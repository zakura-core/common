//! A versioned PQ transparent output and the spends that satisfy it.
//!
//! The output is exactly `00 vv 20 <commitment>`, thirty-five bytes: `OP_0`, the
//! small-integer opcode naming the signature scheme, and a thirty-two-byte push of
//! `SHA-256(body)`. The body is the script the spending input pushes last, and all of it
//! executes. The version lives in the output and nowhere else, so the committed bytes
//! carry no header of their own, and nothing reads a separate namespace tag.
//!
//! The first two bytes are both opcodes rather than pushed data, so each costs one byte
//! rather than the two a pushed byte would. That is not a saving for its own sake: a loose
//! byte is not a field, because the bytes `0x01` through `0x4b` are push opcodes and one in
//! that position would swallow what follows it, leaving the commitment to be read as
//! opcodes. `OP_0` and `OP_1` through `OP_16` are the only single bytes that denote a small
//! number without consuming what comes after, which is what caps each of these two bytes at
//! sixteen or seventeen values.
//!
//! Byte 0 names the *output format* and byte 1 the *signature scheme* within it. This
//! module defines format 0 (`OP_0`) alone, where the commitment is always a thirty-two-byte
//! `SHA-256`, scheme 1 is SHA2-128f and scheme 2 is SHA2-192s. The second byte exists so
//! that adding a scheme does not need a new format, and the first so that a format can
//! later change what the commitment is — a different hash, a different length — without
//! needing a second namespace.
//!
//! Putting the version in the output is what lets validation reject a payment when it is
//! made: a PQ output is distinguishable from a legacy one on chain, so
//! [`classify_created_output`] can reject an undefined-version output while the sender
//! still holds the coins. The version selects the parameter set, the signing context and
//! the commitment, so a later version can replace SHA-256 without revisiting the output
//! format. Version 1 selects SHA2-128f and version 2 SHA2-192s, each with the
//! [`signing_context`] for its version and network.
//!
//! The namespace [`script::is_pq_namespace`] claims is wider than what this module
//! defines: any format opcode, any scheme opcode, and a commitment of any length a single
//! direct push can carry. It has to be, because a shape left outside it would be spendable
//! under the legacy rules and so could not be taken back later without a second consensus
//! change, while a shape inside it is refused from the start and stays available to define.
//! So every shape the namespace holds and this module does not define is *restricted*
//! rather than left to the legacy rules: [`parse_output`] returns
//! [`Error::UnsupportedFormat`], [`Error::UnsupportedCommitmentLength`] or
//! [`Error::UnsupportedVersion`] for it and no spend of it is ever evaluated. Legacy
//! outputs stay creatable and spendable; these rules add a format beside them rather than
//! replacing one, and nothing falls back from PQ to ECDSA.
//!
//! **This format is claimable, not unspendable, wherever these rules are inactive.** The
//! script is three pushes, so under legacy execution it leaves the truthy commitment on
//! top of the stack and is satisfied by an *empty* scriptSig. `OP_RESERVED`, which aborts
//! legacy execution and would have made a PQ output unspendable to any validator lacking
//! these rules, was considered and rejected for the marker; `OP_0` was chosen for the
//! SegWit idiom and because `OP_RESERVED` renders these outputs as invalid or burned in
//! script-aware tooling. What replaces that protection is
//! [`zcash_script::interpreter::Flags::PqOutputs`], which makes the legacy evaluator
//! refuse any script in the namespace once set, as a `scriptPubKey` or as a P2SH redeem
//! script. A caller that activates these rules without setting that flag, or that reaches
//! the legacy evaluator by some path of its own, accepts any spend of a PQ output.
//!
//! Because the commitment covers the body alone, the same thirty-two bytes can appear in
//! an output of either version. Those are separate outputs, separately funded, and the
//! output alone decides which rules spend it, while the signing context and the v5 digest
//! both bind the version a signature was made for. What committing to the body alone gives
//! up is that the committed bytes are not self-describing, and do not fail by construction
//! if some other output commits to them.
//!
//! These rules define PQ outputs and nothing else. [`parse_output`] recognizes one, and
//! every spend check is a method on the recognized output, so an output outside this
//! namespace never reaches this module and keeps whatever rules the caller already
//! applies to it. A near miss — a second byte that is not a scheme opcode, a commitment
//! push that is not the shortest encoding of its payload, a trailing byte after the
//! commitment — is such an output: it is a legacy output and keeps the legacy rules,
//! because unlike under the old marker those scripts really are spendable under them and
//! may already have an owner. A *length* that this format does not fix is not a near miss:
//! it is inside the namespace and restricted.
//!
//! The caller must supply a trusted previous output and a transaction checker bound to
//! that same output, amount and transaction, and must invoke these rules only for
//! network/transaction versions where they have been activated. No existing validation
//! entry point calls this adapter. These spends assume a v5 or later transaction, whose
//! digest binds the previous output and therefore the version and the commitment; v4
//! binds only the script code it is handed. This is a proposed library integration, not
//! node activation or relay policy.
//!
//! No output rule can check the committed body, which is hidden until the spend:
//! committing to an unsatisfiable or anyone-can-spend body remains possible, and remains
//! the receiver's responsibility.

use alloc::vec::Vec;
use core::fmt;

use zcash_protocol::consensus::NetworkType;
use zcash_script::{
    interpreter::CallbackTransactionSignatureChecker,
    pq,
    script::{self, Code},
};

use crate::util::sha256;

use super::ParameterSet;

/// `OP_0`, the only format this module defines. It does not fail under legacy execution.
const FORMAT: u8 = 0x00;
/// The format opcode, the scheme opcode, and the commitment's push opcode.
const HEADER_BYTES: usize = script::PQ_NAMESPACE_HEADER_BYTES;
/// The commitment length format 0 fixes, which is also its push opcode.
const COMMITMENT_BYTES: usize = 32;
/// The complete output: the header and the commitment.
const OUTPUT_BYTES: usize = HEADER_BYTES + COMMITMENT_BYTES;

// What this module encodes and what the legacy evaluator refuses to run must be the same
// set of scripts. [`script::is_pq_namespace`] is the single definition of that set, and
// [`parse_output`] defers to it; these pin the shape the encoder writes to one the predicate
// accepts, so the two cannot drift apart silently. The namespace spans a range of lengths,
// since each format fixes its own, so this is a bound rather than one value.
const _: () = assert!(COMMITMENT_BYTES <= 0x4b);
const _: () = assert!(OUTPUT_BYTES >= script::PQ_NAMESPACE_MIN_BYTES);
const _: () = assert!(OUTPUT_BYTES <= script::PQ_NAMESPACE_MAX_BYTES);

/// Fixed Pure SLH-DSA context, bound to the output format, its version, and the network.
///
/// Consensus branch identifiers are scoped to a network upgrade rather than to a network,
/// so no transaction digest separates mainnet from testnet; this context does.
///
/// The last two bytes are the format and the version within it. Both are here because the
/// version numbering restarts in each format, so two formats will reuse version numbers,
/// and a context that named only the version would let a signature made under one format
/// verify under another.
///
/// The version is what the context's last byte names, but the parameter set is what selects
/// it, which is sound only while the two are one to one, as [`ParameterSet::version`]
/// describes. A version reusing a parameter set must take the version byte here instead,
/// or two versions would share a context and the v5 digest would be left as the only thing
/// binding a signature to the version it was made for.
pub const fn signing_context(network: NetworkType, parameters: ParameterSet) -> &'static [u8] {
    match (network, parameters) {
        (NetworkType::Main, ParameterSet::Sha2_128f) => b"ZCASH/PQ/OUT/main\x00\x01",
        (NetworkType::Main, ParameterSet::Sha2_192s) => b"ZCASH/PQ/OUT/main\x00\x02",
        (NetworkType::Test, ParameterSet::Sha2_128f) => b"ZCASH/PQ/OUT/test\x00\x01",
        (NetworkType::Test, ParameterSet::Sha2_192s) => b"ZCASH/PQ/OUT/test\x00\x02",
        (NetworkType::Regtest, ParameterSet::Sha2_128f) => b"ZCASH/PQ/OUT/regtest\x00\x01",
        (NetworkType::Regtest, ParameterSet::Sha2_192s) => b"ZCASH/PQ/OUT/regtest\x00\x02",
    }
}

/// A rejected output format, version, commitment, or script evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// No rules are defined here for this output format.
    UnsupportedFormat(u8),
    /// No rules are defined here for this output version within format 0.
    UnsupportedVersion(u8),
    /// The commitment is not the length this output's format fixes.
    UnsupportedCommitmentLength(usize),
    /// The pushed script does not match the previous output's commitment.
    CommitmentMismatch,
    /// Bounded preliminary parsing or PQ execution rejected the input.
    Pq(pq::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedFormat(format) => {
                write!(f, "unsupported PQ output format opcode {format:#04x}")
            }
            Self::UnsupportedVersion(version) => {
                write!(f, "unsupported PQ output version {version}")
            }
            Self::UnsupportedCommitmentLength(length) => {
                write!(
                    f,
                    "PQ output commitment is {length} bytes, not {COMMITMENT_BYTES}"
                )
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
    Ok(output_script_from_commitment(
        parameters,
        &sha256::hash(&body.0),
    ))
}

/// Builds the output that commits to `commitment` under the selected parameter set.
///
/// This is [`output_script`] for a payer that was given the commitment rather than the body,
/// which is what a recipient publishes: the body stays with whoever will spend the output.
/// Nothing here can check that a body exists for this commitment, so a wrong commitment makes
/// an output nobody can spend, exactly as a wrong address does today.
pub fn output_script_from_commitment(
    parameters: ParameterSet,
    commitment: &[u8; COMMITMENT_BYTES],
) -> Code {
    let mut bytes = Vec::with_capacity(OUTPUT_BYTES);
    // The commitment's length is also its minimal push opcode, as twenty was before.
    bytes.extend_from_slice(&[FORMAT, parameters.version_opcode(), COMMITMENT_BYTES as u8]);
    bytes.extend_from_slice(commitment);
    Code(bytes)
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
        if sha256::hash(scanned.redeem_script()) != self.commitment {
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

/// Recognizes an output in the PQ namespace, then checks that its version is defined.
///
/// An output outside the namespace returns `Ok(None)` and keeps whatever rules the caller
/// already applies to it. Unlike under the previous marker, a near miss is one of those: an
/// `OP_0`-led script that is not byte-exact really is spendable under the legacy rules and
/// may already have an owner, so it stays a legacy output rather than becoming a malformed
/// PQ one.
///
/// Everything inside the namespace that this module has no rules for is an error rather
/// than a legacy output, which is what restricts those shapes instead of leaving them to be
/// claimed: a format other than 0 gives [`Error::UnsupportedFormat`], a commitment that is
/// not the length format 0 fixes gives [`Error::UnsupportedCommitmentLength`], and a
/// version within format 0 that no parameter set defines gives
/// [`Error::UnsupportedVersion`]. The order matters only for which error a caller sees,
/// since all three are restricted: the format decides everything else, so it is read first.
///
/// Parsing is not authentication, ownership, or activation.
pub fn parse_output(script: &Code) -> Result<Option<PqOutput>, Error> {
    let bytes = &script.0;
    // Defer to the one definition of the namespace, which the legacy evaluator's guard uses
    // too, so that exactly the scripts it refuses to run are the ones parsed here.
    if !script::is_pq_namespace(bytes) {
        return Ok(None);
    }
    // Past this point the script is in the namespace, so it is never a legacy output: it is
    // either an output of the one defined format or a restricted shape.
    if bytes[0] != FORMAT {
        return Err(Error::UnsupportedFormat(bytes[0]));
    }
    if bytes.len() != OUTPUT_BYTES {
        return Err(Error::UnsupportedCommitmentLength(
            bytes.len() - HEADER_BYTES,
        ));
    }
    // `is_pq_namespace` has already accepted byte 1 as a version opcode, so this maps; going
    // back through the conversion keeps the opcode arithmetic in one place.
    let version = ParameterSet::version_from_opcode(bytes[1])
        .expect("the namespace accepts byte 1 only as a version opcode");
    let parameters =
        ParameterSet::from_version(version).ok_or(Error::UnsupportedVersion(version))?;
    let mut commitment = [0; COMMITMENT_BYTES];
    commitment.copy_from_slice(&bytes[HEADER_BYTES..]);
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
    /// Any other output, including every ECDSA-spendable legacy template, and every near
    /// miss of the PQ namespace.
    Legacy,
    /// An output in the PQ namespace that this module has no rules for: an undefined
    /// format, a commitment of the wrong length for its format, or a version within format
    /// 0 that no parameter set defines. Those three are the only things [`Error`] can be
    /// here.
    Malformed(Error),
}

/// Classifies an output being created, for rules that reject a payment rather than a spend.
///
/// A node activating this format rejects a transaction containing a
/// [`CreatedOutput::Malformed`] output, so neither a wallet nor a miner can mint an output
/// in an undefined version, and no such output can appear after activation. Legacy outputs
/// stay valid: this format adds a namespace beside them and bans nothing.
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
