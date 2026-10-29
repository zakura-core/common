//! Library-level single-signer PQ script execution.
//!
//! The caller authenticates the spending script, selects this path explicitly, and
//! supplies the real transaction digest callback. The context is also caller-supplied:
//! this module deliberately does not freeze a protocol context, marker, or address.
//! All current strict signing-mode selectors are decoded; transaction-dependent rules
//! (including SINGLE's corresponding output) remain the digest callback's responsibility.

use core::cell::Cell;

use zcash_script::{
    interpreter::{CallbackTransactionSignatureChecker, Error, Flags, SignatureChecker},
    pq,
    script::Code,
    signature::{self, HashType},
};

use super::{PUBLIC_KEY_BYTES, SIGNATURE_BYTES};

// Keep this private: callers must enter through verify_script, which resets the
// attempt budget and selects the bounded PQ parser and evaluator together.
struct Checker<'a, 'tx> {
    transaction: &'a CallbackTransactionSignatureChecker<'tx>,
    context: &'a [u8],
    attempted: Cell<bool>,
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
        if self.attempted.replace(true) {
            return Err(Error::PqSignatureBudget);
        }
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

/// Executes a supplied script using SLH-DSA and at most one verification attempt.
///
/// This library-only harness parses actual serialized input pushes and runs existing
/// script opcodes, including CHECKSIG and CHECKSIGVERIFY. It does not authenticate an
/// output commitment, activate PQ transactions, or qualify multisig spending. Its
/// one-attempt limit counts unsuccessful checks too, including multisig key matches.
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
            attempted: Cell::new(false),
        },
    )
}
