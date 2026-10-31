//! Library-level PQ execution inside existing P2SH outputs.
//!
//! The redeem script is `50 02 50 51 01 <version> || body`: OP_RESERVED,
//! a two-byte `PQ` tag, a one-byte push of an execution version, then the
//! ordinary script body. The first four bytes identify the PQ namespace. The
//! whole redeem script, including this header, is committed by the unchanged
//! `OP_HASH160 <20-byte hash> OP_EQUAL` output and existing P2SH address.
//!
//! Authenticate that hash before selecting rules. Version 1 selects SHA2-128f;
//! version 2 selects SHA2-192s, each with its fixed [`signing_context`]. Only the
//! body is executed; the digest callback receives the complete redeem script.
//! OP_RESERVED makes the redeem script fail under legacy execution. Unknown
//! identifiers in the recognized namespace fail without ECDSA fallback.
//!
//! The caller must supply a trusted previous output and a transaction checker
//! bound to that same output, amount and transaction. Invoke this adapter only
//! for network/transaction versions where these PQ rules have been activated.
//! No existing validation entry point calls this adapter automatically.
//! This is a proposed library integration, not node activation or relay policy.
//!
//! HASH160's commitment strength is unchanged: a matching alternative spendable
//! script can bypass the intended signature conditions. This module does not
//! establish category-3 security for the composed authorization scheme.

use alloc::vec::Vec;
use core::fmt;

use zcash_script::{
    interpreter::{CallbackTransactionSignatureChecker, Flags},
    pq,
    script::{self, Code},
};

use crate::util::hash160;

use super::ParameterSet;

/// Fixed Pure SLH-DSA context bound to the committed execution version.
pub const fn signing_context(parameters: ParameterSet) -> &'static [u8] {
    match parameters {
        ParameterSet::Sha2_128f => b"ZCASH/PQ/P2SH\x01",
        ParameterSet::Sha2_192s => b"ZCASH/PQ/P2SH\x02",
    }
}

const NAMESPACE: &[u8] = &[0x50, 0x02, b'P', b'Q'];
const HEADER_BYTES: usize = 6;

/// A rejected P2SH commitment, execution identifier, or script evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// The adapter requires legacy P2SH enforcement, including on fallback paths.
    P2shFlagRequired,
    /// The supplied redeem script does not match the previous output.
    CommitmentMismatch,
    /// A recognized PQ header is truncated or uses a different identifier encoding.
    IdentifierEncoding,
    /// No rules are defined here for this execution identifier.
    UnsupportedIdentifier(u8),
    /// Bounded preliminary parsing or PQ execution rejected the input.
    Pq(pq::Error),
    /// The unchanged legacy evaluator rejected the original serialized scripts.
    Legacy(script::ComponentType, script::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::P2shFlagRequired => f.write_str("P2SH validation must be enabled"),
            Self::CommitmentMismatch => f.write_str("P2SH redeem script commitment mismatch"),
            Self::IdentifierEncoding => f.write_str("invalid PQ execution identifier encoding"),
            Self::UnsupportedIdentifier(id) => {
                write!(f, "unsupported PQ execution identifier {id}")
            }
            Self::Pq(error) => write!(f, "PQ input failed: {error}"),
            Self::Legacy(component, error) => write!(f, "legacy {component:?} failed: {error}"),
        }
    }
}

impl core::error::Error for Error {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::Pq(error) => Some(error),
            Self::Legacy(_, error) => Some(error),
            _ => None,
        }
    }
}

impl From<pq::Error> for Error {
    fn from(error: pq::Error) -> Self {
        Self::Pq(error)
    }
}

/// Prefixes a script body with the execution version for the selected parameter set.
///
/// Construct its ordinary P2SH output/address using HASH160 of the returned
/// bytes. The complete redeem script shares the existing script-size bound.
/// This checks size, not satisfiability, activation or wallet derivation rules.
pub fn redeem_script(parameters: ParameterSet, body: &Code) -> Result<Code, Error> {
    if body.0.len() > pq::MAX_SCRIPT_BYTES - HEADER_BYTES {
        return Err(pq::Error::from(script::Error::ScriptSize(None)).into());
    }
    let mut bytes = Vec::with_capacity(HEADER_BYTES + body.0.len());
    bytes.extend_from_slice(NAMESPACE);
    let version = match parameters {
        ParameterSet::Sha2_128f => 1,
        ParameterSet::Sha2_192s => 2,
    };
    bytes.extend_from_slice(&[0x01, version]);
    bytes.extend_from_slice(&body.0);
    Ok(Code(bytes))
}

/// Authenticates a P2SH redeem script before selecting its PQ execution rules.
///
/// `spend.pub_key` must be the trusted previous output's script; `spend.sig` is
/// the original serialized input. Non-P2SH outputs and ordinary legacy redeem
/// scripts use the existing evaluator with `legacy_flags` and these exact bytes.
/// For ordinary legacy redeem scripts, preliminary parsing can change error
/// reporting but not acceptance.
///
/// PQ mode uses its fixed harness rules (including absolute locktimes and the shared
/// operation-count limit); `legacy_flags` do not define PQ relay-policy rules.
/// The digest callback receives the complete authenticated redeem script, while
/// only its body executes. For v5, the retained digest commits to the previous
/// P2SH scriptPubKey, hence indirectly to the identifier and body through HASH160.
pub fn verify_spend(
    spend: &script::Raw,
    legacy_flags: Flags,
    transaction: &CallbackTransactionSignatureChecker<'_>,
) -> Result<bool, Error> {
    if !legacy_flags.contains(Flags::P2SH) {
        return Err(Error::P2shFlagRequired);
    }
    let legacy = || {
        spend
            .eval(legacy_flags, transaction)
            .map_err(|(part, error)| Error::Legacy(part, error))
    };
    let SpendMode::Pq(selected) = classify_spend(&spend.sig.0, &spend.pub_key)? else {
        return legacy();
    };
    let parameters = selected.parameters;
    let redeem = selected.input.redeem_script();
    let body_bytes = selected.body();
    let arguments = selected.arguments;
    // Copy only authenticated, size-bounded scripts. Keep the full representation
    // for hashing even though the interpreter executes the body after the header.
    let script_code = Code(redeem.to_vec());
    let body = Code(body_bytes.to_vec());
    let sighash = |_: &Code, mode: &zcash_script::signature::HashType| {
        (transaction.sighash)(&script_code, mode)
    };
    let checker = CallbackTransactionSignatureChecker {
        sighash: &sighash,
        lock_time: transaction.lock_time,
        is_final: transaction.is_final,
    };
    super::script::verify_script(
        parameters,
        arguments,
        &body,
        signing_context(parameters),
        &checker,
    )
    .map_err(Error::from)
}

/// Authenticated execution classification. This does not verify signatures or activate PQ.
pub enum SpendMode<'a> {
    /// Use the unchanged legacy evaluator on the original scripts.
    Legacy,
    /// A supported, authenticated PQ script with bounded argument transport.
    Pq(PqSpend<'a>),
}

/// Borrowed PQ script components, constructible only through commitment authentication.
pub struct PqSpend<'a> {
    parameters: ParameterSet,
    input: pq::SpendingInput<'a>,
    arguments: &'a [u8],
}
impl PqSpend<'_> {
    /// Parameter set selected by the authenticated version.
    pub fn parameters(&self) -> ParameterSet {
        self.parameters
    }
    /// Executed body, excluding the committed version header.
    pub fn body(&self) -> &[u8] {
        &self.input.redeem_script()[HEADER_BYTES..]
    }
}

/// Authenticates the final pushed script against a trusted previous output before
/// selecting parameters. Callers supply network/version activation independently.
/// Non-P2SH outputs and ordinary redeem scripts retain legacy evaluation. Recognized
/// malformed or unknown PQ versions reject, never fall back to another verifier.
pub fn classify_spend<'a>(input: &'a [u8], previous_output: &Code) -> Result<SpendMode<'a>, Error> {
    let output = &previous_output.0;
    if output.len() != 23 || output[..2] != [0xa9, 0x14] || output[22] != 0x87 {
        return Ok(SpendMode::Legacy);
    }
    let input = pq::SpendingInput::scan(input)?;
    let redeem = input.redeem_script();
    if hash160::hash(redeem) != output[2..22] {
        return Err(Error::CommitmentMismatch);
    }
    if !redeem.starts_with(NAMESPACE) {
        return Ok(SpendMode::Legacy);
    }
    if redeem.len() < HEADER_BYTES || redeem[4] != 0x01 {
        return Err(Error::IdentifierEncoding);
    }
    let parameters = match redeem[5] {
        1 => ParameterSet::Sha2_128f,
        2 => ParameterSet::Sha2_192s,
        id => return Err(Error::UnsupportedIdentifier(id)),
    };
    let arguments = input.pq_arguments()?;
    Ok(SpendMode::Pq(PqSpend {
        parameters,
        input,
        arguments,
    }))
}

#[cfg(test)]
mod tests;
