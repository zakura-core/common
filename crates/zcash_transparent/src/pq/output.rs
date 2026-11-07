//! A versioned PQ transparent output and the spends that satisfy it.
//!
//! The output is exactly `50 01 vv 14 <commitment>`: `OP_RESERVED`, a one-byte push of a
//! version, and a twenty-byte push of `HASH160(body)`. The body is the script the spending
//! input pushes last, and all of it executes. The version lives in the output and nowhere
//! else, so the committed bytes carry no header of their own, and nothing reads a separate
//! namespace tag.
//!
//! Putting the version in the output is what lets validation reject a payment when it is
//! made: a PQ output is distinguishable from a legacy one on chain, so
//! [`classify_created_output`] can reject a malformed or unknown-version PQ output while
//! the sender still holds the coins, and lets a node refuse to create legacy outputs at
//! all from a chosen height. The version selects the parameter set, the signing context
//! and the commitment, so a later version can replace HASH160 without revisiting the
//! output format. Version 1 selects SHA2-128f and version 2 SHA2-192s, each with the
//! [`signing_context`] for its version and network.
//!
//! `OP_RESERVED` makes the output fail under legacy execution, so a PQ output is
//! unspendable, rather than claimable, wherever these rules are not active. Unknown
//! versions and non-canonical encodings in the namespace are rejected outright; nothing
//! falls back to ECDSA.
//!
//! Because the commitment covers the body alone, the same twenty bytes can appear in an
//! output of either version, or as an ordinary P2SH script hash. Those are separate
//! outputs, separately funded, and the output alone decides which rules spend it, while
//! the signing context and the v5 digest both bind the version a signature was made for.
//! What committing to the body alone gives up is that the committed bytes no longer begin
//! with `OP_RESERVED`, so they are not self-describing and do not fail by construction if
//! some other output commits to them.
//!
//! These rules define PQ outputs and nothing else. [`parse_output`] recognizes one, and
//! every spend check is a method on the recognized output, so an output outside this
//! namespace never reaches this module and keeps whatever rules the caller already
//! applies to it.
//!
//! The caller must supply a trusted previous output and a transaction checker bound to
//! that same output, amount and transaction, and must invoke these rules only for
//! network/transaction versions where they have been activated. No existing validation
//! entry point calls this adapter. These spends assume a v5 or later transaction, whose
//! digest binds the previous output and therefore the version and the commitment; v4
//! binds only the script code it is handed. This is a proposed library integration, not
//! node activation or relay policy.
//!
//! HASH160's commitment strength is unchanged from a P2SH script hash and is the weakest
//! part of this format: a matching alternative spendable script bypasses the intended
//! signature conditions, and this module does not establish category-3 security for the
//! composed authorization scheme. Nor can any output rule check the committed body, which
//! is hidden until the spend: committing to an unsatisfiable or anyone-can-spend body
//! remains possible, and remains the receiver's responsibility.

use alloc::vec::Vec;
use core::fmt;

use zcash_protocol::consensus::NetworkType;
use zcash_script::{
    interpreter::CallbackTransactionSignatureChecker,
    pq,
    script::{self, Code},
};

use crate::util::hash160;

use super::ParameterSet;

/// `OP_RESERVED`, which claims this namespace and fails under legacy execution.
const MARKER: u8 = 0x50;
/// The one-byte push opcode that carries the version.
const VERSION_PUSH: u8 = 0x01;
/// The marker, the version's push opcode, and the version, carried only by the output.
const HEADER_BYTES: usize = 3;
/// The commitment length selected by versions 1 and 2.
const COMMITMENT_BYTES: usize = 20;
/// The complete output: the header, the commitment's push opcode, and the commitment.
const OUTPUT_BYTES: usize = HEADER_BYTES + 1 + COMMITMENT_BYTES;

/// Fixed Pure SLH-DSA context, bound to the output version and to the network.
///
/// Consensus branch identifiers are scoped to a network upgrade rather than to a network,
/// so no transaction digest separates mainnet from testnet; this context does.
///
/// The version is what the context's last byte names, but the parameter set is what selects
/// it, which is sound only while the two are one to one, as [`ParameterSet::version`]
/// describes. A version reusing a parameter set must take the version byte here instead,
/// or two versions would share a context and the v5 digest would be left as the only thing
/// binding a signature to the version it was made for.
pub const fn signing_context(network: NetworkType, parameters: ParameterSet) -> &'static [u8] {
    match (network, parameters) {
        (NetworkType::Main, ParameterSet::Sha2_128f) => b"ZCASH/PQ/OUT/main\x01",
        (NetworkType::Main, ParameterSet::Sha2_192s) => b"ZCASH/PQ/OUT/main\x02",
        (NetworkType::Test, ParameterSet::Sha2_128f) => b"ZCASH/PQ/OUT/test\x01",
        (NetworkType::Test, ParameterSet::Sha2_192s) => b"ZCASH/PQ/OUT/test\x02",
        (NetworkType::Regtest, ParameterSet::Sha2_128f) => b"ZCASH/PQ/OUT/regtest\x01",
        (NetworkType::Regtest, ParameterSet::Sha2_192s) => b"ZCASH/PQ/OUT/regtest\x02",
    }
}

/// A rejected output encoding, version, commitment, or script evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// An output in this namespace is not the canonical encoding for any version.
    OutputEncoding,
    /// No rules are defined here for this output version.
    UnsupportedVersion(u8),
    /// The pushed script does not match the previous output's commitment.
    CommitmentMismatch,
    /// Bounded preliminary parsing or PQ execution rejected the input.
    Pq(pq::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutputEncoding => f.write_str("invalid PQ output encoding"),
            Self::UnsupportedVersion(version) => {
                write!(f, "unsupported PQ output version {version}")
            }
            Self::CommitmentMismatch => f.write_str("PQ output commitment mismatch"),
            Self::Pq(error) => write!(f, "PQ input failed: {error}"),
        }
    }
}

impl core::error::Error for Error {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::Pq(error) => Some(error),
            _ => None,
        }
    }
}

impl From<pq::Error> for Error {
    fn from(error: pq::Error) -> Self {
        Self::Pq(error)
    }
}

/// Builds the complete output that commits to this body under the selected parameter set.
///
/// The body is both what the output commits to and what a spend executes, and it shares
/// the existing script-size bound. This checks size, not satisfiability, activation or
/// wallet derivation rules, and defines no address encoding: the returned bytes are the
/// whole `scriptPubKey`.
///
/// The version written is the one this parameter set selects, so this cannot build an
/// output for a version that reuses a parameter set; see [`ParameterSet::version`].
pub fn output_script(parameters: ParameterSet, body: &Code) -> Result<Code, Error> {
    if body.0.len() > pq::MAX_SCRIPT_BYTES {
        return Err(pq::Error::from(script::Error::ScriptSize(None)).into());
    }
    let mut bytes = Vec::with_capacity(OUTPUT_BYTES);
    bytes.extend_from_slice(&[
        MARKER,
        VERSION_PUSH,
        parameters.version(),
        COMMITMENT_BYTES as u8,
    ]);
    bytes.extend_from_slice(&hash160::hash(&body.0));
    Ok(Code(bytes))
}

/// A structurally valid PQ output. Its source must be authenticated by the caller.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PqOutput {
    parameters: ParameterSet,
    commitment: [u8; COMMITMENT_BYTES],
}

impl PqOutput {
    /// The parameter set this output's version selects.
    pub fn parameters(&self) -> ParameterSet {
        self.parameters
    }

    /// The committed script's hash, under the algorithm this output's version selects.
    pub fn commitment(&self) -> &[u8; COMMITMENT_BYTES] {
        &self.commitment
    }

    /// Authenticates the input's final pushed script against this output's commitment.
    ///
    /// `input` is the original serialized spending input. This is bounded parsing and
    /// authentication, not signature verification or activation. Failed authentication
    /// rejects; nothing falls back to another verifier.
    pub fn authenticate_spend<'a>(&self, input: &'a [u8]) -> Result<PqSpend<'a>, Error> {
        let scanned = pq::SpendingInput::scan(input)?;
        // Apply the script-size and stack-depth bounds before hashing, so an oversized
        // pushed script is rejected without hashing up to the whole input's worth of bytes.
        let arguments = scanned.pq_arguments()?;
        if hash160::hash(scanned.redeem_script()) != self.commitment {
            return Err(Error::CommitmentMismatch);
        }
        Ok(PqSpend {
            parameters: self.parameters,
            input: scanned,
            arguments,
        })
    }

    /// Verifies a spend of this output, authenticating the committed script first.
    ///
    /// `input` is the original serialized spending input, and `transaction` must be bound
    /// to this same output, amount and transaction. PQ execution has fixed rules,
    /// including absolute locktimes, canonical input pushes, a single final stack item and
    /// the shared operation-count limit, so it takes no legacy interpreter flags.
    ///
    /// The digest callback receives the executed script, which is exactly the script this
    /// output commits to. For v5 the retained digest also commits to the previous output,
    /// hence directly to the version and commitment, and through the commitment to the
    /// body.
    pub fn verify_spend(
        &self,
        network: NetworkType,
        input: &[u8],
        transaction: &CallbackTransactionSignatureChecker<'_>,
    ) -> Result<bool, Error> {
        let selected = self.authenticate_spend(input)?;
        let parameters = selected.parameters;
        // Copy only an authenticated, size-bounded script.
        let body = Code(selected.body().to_vec());
        super::script::verify_script(
            parameters,
            selected.arguments,
            &body,
            signing_context(network, parameters),
            transaction,
        )
        .map_err(Error::from)
    }
}

/// Recognizes an output in the PQ namespace, then checks its exact encoding and version.
///
/// An output outside the namespace returns `Ok(None)` and keeps whatever rules the caller
/// already applies to it; an output that claims the namespace returns an error unless it is
/// byte-for-byte the canonical encoding of a defined version. Parsing is not
/// authentication, ownership, or activation.
pub fn parse_output(script: &Code) -> Result<Option<PqOutput>, Error> {
    let bytes = &script.0;
    // `OP_RESERVED` claims the whole namespace: such an output cannot be spent under
    // legacy rules, so there is nothing to keep compatible and no room for near misses.
    if bytes.first() != Some(&MARKER) {
        return Ok(None);
    }
    if bytes.len() != OUTPUT_BYTES
        || bytes[1] != VERSION_PUSH
        || bytes[HEADER_BYTES] != COMMITMENT_BYTES as u8
    {
        return Err(Error::OutputEncoding);
    }
    let version = bytes[2];
    let parameters =
        ParameterSet::from_version(version).ok_or(Error::UnsupportedVersion(version))?;
    let mut commitment = [0; COMMITMENT_BYTES];
    commitment.copy_from_slice(&bytes[HEADER_BYTES + 1..]);
    Ok(Some(PqOutput {
        parameters,
        commitment,
    }))
}

/// What an output being created is, for the rules that apply when a payment is made.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CreatedOutput {
    /// A canonical PQ output of a defined version.
    Pq(ParameterSet),
    /// Any other output, including every ECDSA-spendable legacy template.
    Legacy,
    /// An output claiming the PQ namespace that no version defines.
    Malformed(Error),
}

/// Classifies an output being created, for rules that reject a payment rather than a spend.
///
/// A node activating this format rejects a transaction containing a
/// [`CreatedOutput::Malformed`] output, so a wallet cannot mint an unspendable one. From a
/// later height it can also reject [`CreatedOutput::Legacy`] outputs, which is only
/// decidable here because the version is in the output. Choosing that height, and which
/// outputs to exempt from it, is the node's decision: at minimum coinbase outputs, whose
/// recipients consensus fixes, and null-data outputs, which are unspendable by design.
pub fn classify_created_output(script: &Code) -> CreatedOutput {
    match parse_output(script) {
        Ok(Some(output)) => CreatedOutput::Pq(output.parameters()),
        Ok(None) => CreatedOutput::Legacy,
        Err(error) => CreatedOutput::Malformed(error),
    }
}

/// Borrowed PQ script components, constructible only through commitment authentication.
pub struct PqSpend<'a> {
    parameters: ParameterSet,
    input: pq::SpendingInput<'a>,
    arguments: &'a [u8],
}

impl PqSpend<'_> {
    /// Parameter set selected by the authenticated output version.
    pub fn parameters(&self) -> ParameterSet {
        self.parameters
    }

    /// The authenticated script: what the output commits to, and all that executes.
    pub fn body(&self) -> &[u8] {
        self.input.redeem_script()
    }

    /// Counts signature operations in the committed body, inactive branches included.
    ///
    /// Count this, not the serialized input: a PQ input's signature pushes exceed the
    /// legacy push bound, where legacy counting stops and would report almost none of the
    /// checks the body performs. One SLH-DSA check costs far more than one ECDSA check,
    /// so whoever sets a block budget must weight the two differently; this count does
    /// not distinguish them.
    pub fn sig_op_count(&self, accurate: bool) -> u32 {
        Code(self.body().to_vec()).sig_op_count(accurate)
    }
}

#[cfg(test)]
mod tests;
