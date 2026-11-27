//! Library-level PQ script execution under SLH-DSA.
//!
//! The caller authenticates the spending script, selects this path explicitly, and
//! supplies the real transaction digest callback. The context is also caller-supplied:
//! this module deliberately does not freeze a protocol context, marker, or address.
//! All current strict signing-mode selectors are decoded; transaction-dependent rules
//! (including SINGLE's corresponding output) remain the digest callback's responsibility.
//! Use [`super::output::parse_output`] and [`super::output::PqOutput::verify_spend`] to
//! authenticate a script against the output that commits to it before selecting PQ
//! execution and its fixed context.

use zcash_script::{
    interpreter::{CallbackTransactionSignatureChecker, Error, Flags, SignatureChecker},
    pq,
    script::Code,
    signature::{self, HashType},
};

use super::ParameterSet;

// Keep this private: callers enter through verify_script, which selects the
// bounded PQ parser and shared evaluator together.
struct Checker<'a, 'tx> {
    transaction: &'a CallbackTransactionSignatureChecker<'tx>,
    context: &'a [u8],
    parameters: ParameterSet,
}

impl SignatureChecker for Checker<'_, '_> {
    fn check_signature(
        &self,
        argument: &[u8],
        public_key: &[u8],
        _flags: Flags,
        program: &Code,
    ) -> Result<bool, Error> {
        // Encoding errors abort even when the signature is empty. An empty signature
        // with a well-formed key deliberately pushes false without doing cryptography.
        // A false result for a non-empty one, including a missing digest, aborts the
        // spend in the evaluator, which also charges it to the input's budget first.
        // A key of any other length aborts, so no body can mix algorithms: an ECDSA
        // branch parses, then kills the spend if it is ever taken.
        if public_key.len() != self.parameters.public_key_bytes() {
            return Err(Error::PubKeyType);
        }
        if argument.is_empty() {
            return Ok(false);
        }
        if argument.len() != self.parameters.signature_bytes() + 1 {
            return Err(Error::PqSignatureSize);
        }
        let hash_type =
            HashType::from_bits(i32::from(argument[self.parameters.signature_bytes()]), true)
                .map_err(|e| Error::from(signature::Error::from(e)))?;
        let Some(digest) = (self.transaction.sighash)(program, &hash_type) else {
            return Ok(false);
        };
        Ok(super::verify(
            self.parameters,
            public_key,
            &digest,
            self.context,
            &argument[..self.parameters.signature_bytes()],
        )
        .is_ok())
    }

    fn check_sig(&self, _: &signature::Decoded, _: &[u8], _: &Code) -> bool {
        // There is no ECDSA fallback in the PQ path.
        false
    }

    fn check_lock_time(&self, lock_time: i64) -> bool {
        self.transaction.check_lock_time(lock_time)
    }
}

/// Executes a supplied script using SLH-DSA under the PQ script rules.
///
/// This library-only harness parses actual serialized input pushes and runs the script with
/// `CHECKSIG`, `CHECKSIGVERIFY` and `CHECKSIGADD`; multisig opcodes are invalid. It does not
/// authenticate an output commitment or activate PQ transactions. Each check given a
/// non-empty signature costs [`ParameterSet::signature_bytes`] of `input_bytes`, the whole
/// serialized input the arguments came from, revealed script included, and the script fails
/// once its checks cost more. That bounds the checks a block can demand by its size, about
/// one ordinary block's worth whatever the scripts do.
/// The private verifier cannot be passed to a legacy evaluator by callers.
///
/// Malformed signatures, keys, and selectors abort, and so does a non-empty signature
/// that is cryptographically incorrect or has no digest (such as `SIGHASH_SINGLE` without
/// a corresponding output). Only an empty signature with a valid-length key is false.
pub fn verify_script(
    parameters: ParameterSet,
    arguments: &[u8],
    program: &Code,
    context: &[u8],
    transaction: &CallbackTransactionSignatureChecker<'_>,
    input_bytes: usize,
) -> Result<bool, pq::Error> {
    if context.len() > 255 {
        return Err(pq::Error::ContextSize);
    }
    pq::eval_script(
        arguments,
        program,
        &Checker {
            transaction,
            context,
            parameters,
        },
        parameters.check_budget(input_bytes),
    )
}
