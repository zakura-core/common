//! Library-level PQ script execution with existing multisig matching.
//!
//! The caller authenticates the spending script, selects this path explicitly, and
//! supplies the real transaction digest callback. The context is also caller-supplied:
//! this module deliberately does not freeze a protocol context, marker, or address.
//! All current strict signing-mode selectors are decoded; transaction-dependent rules
//! (including SINGLE's corresponding output) remain the digest callback's responsibility.
//! Use [`super::p2sh::verify_spend`] to authenticate a P2SH redeem script before
//! selecting PQ execution and its fixed context.

use zcash_script::{
    interpreter::{CallbackTransactionSignatureChecker, Error, Flags, SignatureChecker},
    pq,
    script::Code,
    signature::{self, HashType},
};

use super::{PUBLIC_KEY_BYTES, SIGNATURE_BYTES};

// Keep this private: callers enter through verify_script, which selects the
// bounded PQ parser and shared evaluator together.
struct Checker<'a, 'tx> {
    transaction: &'a CallbackTransactionSignatureChecker<'tx>,
    context: &'a [u8],
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
        if public_key.len() != PUBLIC_KEY_BYTES {
            return Err(Error::PubKeyType);
        }
        if argument.is_empty() {
            return Ok(false);
        }
        if argument.len() != SIGNATURE_BYTES + 1 {
            return Err(Error::PqSignatureSize);
        }
        let hash_type = HashType::from_bits(i32::from(argument[SIGNATURE_BYTES]), true)
            .map_err(|e| Error::from(signature::Error::from(e)))?;
        let Some(digest) = (self.transaction.sighash)(program, &hash_type) else {
            return Ok(false);
        };
        Ok(super::verify(
            public_key,
            &digest,
            self.context,
            &argument[..SIGNATURE_BYTES],
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

/// Executes a supplied script using SLH-DSA and the shared operation-count limit.
///
/// This library-only harness parses actual serialized input pushes and runs existing
/// script opcodes, including CHECKSIG and CHECKSIGVERIFY. It does not authenticate an
/// output commitment or activate PQ transactions. CHECKSIG consumes an operation;
/// multisig additionally charges its key count before matching, bounding failed
/// matches as well as successful checks. Aggregate transaction/block work limits
/// and relay policy still require qualification.
/// The private verifier cannot be passed to a legacy evaluator by callers.
///
/// Malformed nonempty signatures, keys, and selectors abort. A cryptographically
/// incorrect signature or an empty signature with a valid-length key evaluates false.
pub fn verify_script(
    input: &[u8],
    program: &Code,
    context: &[u8],
    transaction: &CallbackTransactionSignatureChecker<'_>,
) -> Result<bool, pq::Error> {
    if context.len() > 255 {
        return Err(pq::Error::ContextSize);
    }
    pq::eval_script(
        input,
        program,
        &Checker {
            transaction,
            context,
        },
    )
}
