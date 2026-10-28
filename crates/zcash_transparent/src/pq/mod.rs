//! Standalone SLH-DSA-SHA2-192s primitives, backed by RustCrypto's `slh-dsa`.
//!
//! This experimental module implements deterministic Pure SLH-DSA as specified in
//! [FIPS 205](https://doi.org/10.6028/NIST.FIPS.205). The message and context are supplied
//! by the caller; no transaction digest, wallet derivation, authorization encoding,
//! address format, or script behavior is defined here. This is not HashSLH-DSA.
//!
//! Verification authenticates the message only relative to the supplied public key.
//! The caller must authenticate that key and choose the message and context that bind
//! the signature to its intended use. Contexts may contain at most 255 bytes.

use alloc::vec::Vec;

use slh_dsa::Sha2_192s;

/// A malformed encoding, overlong context, or invalid signature.
pub use slh_dsa::signature::Error;

/// Three 24-byte seeds: `SK.seed`, `SK.prf`, and `PK.seed`, in that order.
pub const SEED_BYTES: usize = 72;
/// The public seed followed by the public root.
pub const PUBLIC_KEY_BYTES: usize = 48;
/// The exact encoded signature size for SLH-DSA-SHA2-192s.
pub const SIGNATURE_BYTES: usize = 16224;

/// An SLH-DSA-SHA2-192s signing key, reusable across messages.
///
/// Secret fields are cleared on drop by the dependency's `zeroize` feature. This wrapper
/// deliberately provides no debug formatting or secret-key export.
pub struct SigningKey(slh_dsa::SigningKey<Sha2_192s>);

impl SigningKey {
    /// Generates a key from the concatenation `SK.seed || SK.prf || PK.seed`.
    ///
    /// The caller must supply 72 cryptographically random bytes, or the output of an
    /// appropriate secret-key derivation construction. Reusing a seed reproduces the
    /// same key. This function neither chooses an entropy source nor derives wallet keys.
    /// The caller remains responsible for protecting and clearing its copy of the seed.
    pub fn from_seed(seed: &[u8; SEED_BYTES]) -> Self {
        Self(slh_dsa::SigningKey::slh_keygen_internal(
            &seed[..24],
            &seed[24..48],
            &seed[48..],
        ))
    }

    /// Returns the canonical 48-byte public-key encoding.
    pub fn public_key(&self) -> [u8; PUBLIC_KEY_BYTES] {
        self.0.as_ref().to_bytes().into()
    }

    /// Signs the message using deterministic Pure SLH-DSA with the supplied context.
    ///
    /// Returns exactly [`SIGNATURE_BYTES`] bytes. Signing the same message and context
    /// with the same key produces the same signature. No additional hashing or
    /// transaction-specific encoding is applied by this wrapper.
    ///
    /// # Errors
    /// Returns an error if the context is longer than 255 bytes.
    pub fn sign(&self, message: &[u8], context: &[u8]) -> Result<Vec<u8>, Error> {
        self.0
            .try_sign_with_context(message, context, None)
            .map(|signature| signature.to_bytes().to_vec())
    }
}

/// Verifies a Pure SLH-DSA signature against a caller-authenticated public key.
///
/// # Errors
/// Rejects public keys other than 48 bytes, signatures other than 16,224 bytes,
/// contexts longer than 255 bytes, and signatures that do not verify. Invalid lengths
/// are rejected before cryptographic verification; trailing bytes are never ignored.
pub fn verify(
    public_key: &[u8],
    message: &[u8],
    context: &[u8],
    signature: &[u8],
) -> Result<(), Error> {
    if public_key.len() != PUBLIC_KEY_BYTES
        || signature.len() != SIGNATURE_BYTES
        || context.len() > 255
    {
        return Err(Error::new());
    }
    let key = slh_dsa::VerifyingKey::<Sha2_192s>::try_from(public_key)?;
    let signature = slh_dsa::Signature::<Sha2_192s>::try_from(signature)?;
    key.try_verify_with_context(message, context, &signature)
}

#[cfg(test)]
mod tests;
