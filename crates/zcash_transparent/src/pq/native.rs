//! Native output envelope and explicit PQ signature checking.
//!
//! The complete output is `OP_RESERVED PUSH3("SLH") PUSH1(version) body`.
//! Its seven-byte prefix is interpreted only by this adapter. The original output,
//! including the prefix, is supplied to the transaction-digest callback. Only the
//! body executes. Every PQ operation uses the output's selected parameter set;
//! ordinary signature operations continue to use ECDSA.
//!
//! The caller supplies the authentic previous output and a transaction checker bound
//! to that output and amount. Parsing is not authentication or network activation.
//! A signature proves approval relative to that binding; the retained transaction
//! digest and arbitrary script alternatives still determine composed security.

use super::ParameterSet;
use alloc::vec::Vec;
use core::fmt;
use zcash_script::{
    interpreter::{self, CallbackTransactionSignatureChecker, Flags, SignatureChecker},
    pq,
    script::Code,
    signature,
};

const PREFIX: &[u8] = b"\x50\x03SLH";
const HEADER_BYTES: usize = 7;

/// A malformed native envelope or failed script execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// The native prefix or version push is malformed.
    Envelope,
    /// The version has no defined execution rules.
    UnsupportedVersion(u8),
    /// Bounded arguments or the shared interpreter rejected execution.
    Execution(pq::Error),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Envelope => f.write_str("invalid native SLH output envelope"),
            Self::UnsupportedVersion(v) => write!(f, "unsupported native SLH version {v}"),
            Self::Execution(e) => write!(f, "native SLH execution failed: {e}"),
        }
    }
}
impl core::error::Error for Error {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::Execution(e) => Some(e),
            _ => None,
        }
    }
}
impl From<pq::Error> for Error {
    fn from(e: pq::Error) -> Self {
        Self::Execution(e)
    }
}

/// Fixed Pure signing context for a native output version.
pub const fn signing_context(parameters: ParameterSet) -> &'static [u8] {
    match parameters {
        ParameterSet::Sha2_128f => b"ZCASH/PQ/NATIVE\x01",
        ParameterSet::Sha2_192s => b"ZCASH/PQ/NATIVE\x02",
    }
}

/// Constructs the complete native output, bounding its header and body together.
/// This does not prove script satisfiability or provide an address encoding.
pub fn output_script(parameters: ParameterSet, body: &Code) -> Result<Code, Error> {
    if body.0.len() > pq::MAX_SCRIPT_BYTES - HEADER_BYTES {
        return Err(pq::Error::Script(zcash_script::script::Error::ScriptSize(None)).into());
    }
    let mut output = Vec::with_capacity(HEADER_BYTES + body.0.len());
    output.extend_from_slice(PREFIX);
    output.extend_from_slice(&[1, parameters.version()]);
    output.extend_from_slice(&body.0);
    Ok(Code(output))
}

/// Borrowed, structurally validated native output. The caller authenticates its source.
pub struct NativeOutput<'a> {
    script: &'a Code,
    parameters: ParameterSet,
}

/// Recognizes the native namespace before checking its version and total size.
/// Unrelated outputs return `None`; recognized invalid envelopes never fall back.
pub fn parse_output(script: &Code) -> Result<Option<NativeOutput<'_>>, Error> {
    if !script.0.starts_with(PREFIX) {
        return Ok(None);
    }
    if script.0.len() < HEADER_BYTES || script.0[5] != 1 {
        return Err(Error::Envelope);
    }
    let parameters = match script.0[6] {
        1 => ParameterSet::Sha2_128f,
        2 => ParameterSet::Sha2_192s,
        v => return Err(Error::UnsupportedVersion(v)),
    };
    if script.0.len() > pq::MAX_SCRIPT_BYTES {
        return Err(pq::Error::Script(zcash_script::script::Error::ScriptSize(None)).into());
    }
    Ok(Some(NativeOutput { script, parameters }))
}

impl NativeOutput<'_> {
    /// The parameter set committed in this output.
    pub fn parameters(&self) -> ParameterSet {
        self.parameters
    }
    /// The exact complete output used for transaction signing.
    pub fn script_code(&self) -> &Code {
        self.script
    }
    /// Executes serialized arguments under this output's native rules.
    ///
    /// The transaction checker must refer to this same trusted previous output.
    /// Native PQ operations and absolute timelocks are enforced independently of
    /// optional policy flags; all other applicable flags are passed through.
    pub fn verify_spend(
        &self,
        input: &[u8],
        flags: Flags,
        transaction: &CallbackTransactionSignatureChecker<'_>,
    ) -> Result<bool, Error> {
        let body = Code(self.script.0[HEADER_BYTES..].to_vec());
        pq::eval(
            input,
            &body,
            self.script,
            flags,
            &Checker {
                parameters: self.parameters,
                transaction,
            },
        )
        .map_err(Error::from)
    }
    /// Counts signature operations in all branches, including ordinary ECDSA checks.
    pub fn sig_op_count(&self, accurate: bool) -> u32 {
        pq::sig_op_count(&Code(self.script.0[HEADER_BYTES..].to_vec()), accurate)
    }
}

struct Checker<'a, 'tx> {
    parameters: ParameterSet,
    transaction: &'a CallbackTransactionSignatureChecker<'tx>,
}
impl SignatureChecker for Checker<'_, '_> {
    fn check_pq_signature(
        &self,
        argument: &[u8],
        public_key: &[u8],
        script_code: &Code,
    ) -> Result<bool, interpreter::Error> {
        if public_key.len() != self.parameters.public_key_bytes() {
            return Err(interpreter::Error::PubKeyType);
        }
        if argument.is_empty() {
            return Ok(false);
        }
        let signature_bytes = self.parameters.signature_bytes();
        if argument.len() != signature_bytes + 1 {
            return Err(interpreter::Error::PqSignatureSize);
        }
        let mode = signature::HashType::from_bits(i32::from(argument[signature_bytes]), true)
            .map_err(|e| interpreter::Error::from(signature::Error::from(e)))?;
        let Some(digest) = (self.transaction.sighash)(script_code, &mode) else {
            return Ok(false);
        };
        Ok(super::verify(
            self.parameters,
            public_key,
            &digest,
            signing_context(self.parameters),
            &argument[..signature_bytes],
        )
        .is_ok())
    }
    fn check_sig(
        &self,
        signature: &signature::Decoded,
        public_key: &[u8],
        script_code: &Code,
    ) -> bool {
        self.transaction
            .check_sig(signature, public_key, script_code)
    }
    fn check_lock_time(&self, lock_time: i64) -> bool {
        self.transaction.check_lock_time(lock_time)
    }
}

#[cfg(test)]
mod tests;
