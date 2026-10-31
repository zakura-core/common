//! Standalone SLH-DSA-SHA2-128f and SLH-DSA-SHA2-192s primitives, backed by RustCrypto's `slh-dsa`.
//!
//! This module implements deterministic Pure SLH-DSA as specified in
//! [FIPS 205](https://doi.org/10.6028/NIST.FIPS.205). The message and context are supplied
//! by the caller; no transaction digest, wallet derivation, authorization encoding,
//! or address format is defined by these primitives. The separate [`script`] module
//! provides a library-only script harness, and [`p2sh`] authenticates a proposed PQ
//! execution identifier inside an existing P2SH redeem script. This is not HashSLH-DSA.
//!
//! Verification authenticates the message only relative to the supplied public key.
//! The caller must authenticate that key and choose the message and context that bind
//! the signature to its intended use. Contexts may contain at most 255 bytes.

pub mod p2sh;
pub mod script;

/// A malformed encoding, overlong context, or invalid signature.
pub use slh_dsa::signature::Error;

/// Explicit SLH-DSA parameter selection. Script arguments never select this value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParameterSet {
    /// NIST Category 1, optimized for signing speed.
    Sha2_128f,
    /// NIST Category 3, optimized for signature size.
    Sha2_192s,
}

impl ParameterSet {
    /// Exact public-key encoding length.
    pub const fn public_key_bytes(self) -> usize {
        match self {
            Self::Sha2_128f => sha2_128f::PUBLIC_KEY_BYTES,
            Self::Sha2_192s => sha2_192s::PUBLIC_KEY_BYTES,
        }
    }
    /// Exact signature length, excluding the transaction signing-mode byte.
    pub const fn signature_bytes(self) -> usize {
        match self {
            Self::Sha2_128f => sha2_128f::SIGNATURE_BYTES,
            Self::Sha2_192s => sha2_192s::SIGNATURE_BYTES,
        }
    }
}

// A single implementation keeps exact-length parsing and key encapsulation identical.
macro_rules! parameter_set {
    ($module:ident, $algorithm:ident, $n:literal, $signature:literal, $description:literal) => {
        #[doc = $description]
        pub mod $module {
            use super::Error;
            use alloc::vec::Vec;
            /// Three concatenated seeds: SK.seed, SK.prf and PK.seed.
            pub const SEED_BYTES: usize = 3 * $n;
            /// The public seed followed by the public root.
            pub const PUBLIC_KEY_BYTES: usize = 2 * $n;
            /// Exact standardized signature encoding length.
            pub const SIGNATURE_BYTES: usize = $signature;
            /// Reusable private signing key, with no debug formatting or secret export.
            /// Stored secret seeds are zeroized by the dependency on drop.
            pub struct SigningKey(slh_dsa::SigningKey<slh_dsa::$algorithm>);
            impl SigningKey {
                /// Constructs a key from three concatenated seeds. Callers supply secure
                /// entropy/derivation and remain responsible for clearing their seed copy.
                pub fn from_seed(seed: &[u8; SEED_BYTES]) -> Self {
                    Self(slh_dsa::SigningKey::slh_keygen_internal(
                        &seed[..$n],
                        &seed[$n..2 * $n],
                        &seed[2 * $n..],
                    ))
                }
                /// Returns the canonical encoded public key.
                pub fn public_key(&self) -> [u8; PUBLIC_KEY_BYTES] {
                    self.0.as_ref().to_bytes().into()
                }
                /// Deterministic Pure SLH-DSA signing with a context of at most 255 bytes.
                /// The message is used as supplied, without an additional application hash.
                pub fn sign(&self, message: &[u8], context: &[u8]) -> Result<Vec<u8>, Error> {
                    self.0
                        .try_sign_with_context(message, context, None)
                        .map(|signature| signature.to_bytes().to_vec())
                }
            }
            /// Verifies the exact standardized key/signature encodings using Pure SLH-DSA.
            /// The caller authenticates the key and binds the message and context.
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
                let key = slh_dsa::VerifyingKey::<slh_dsa::$algorithm>::try_from(public_key)?;
                let signature = slh_dsa::Signature::<slh_dsa::$algorithm>::try_from(signature)?;
                key.try_verify_with_context(message, context, &signature)
            }
        }
    };
}
parameter_set!(
    sha2_128f,
    Sha2_128f,
    16,
    17088,
    "SLH-DSA-SHA2-128f with exact typed seeds and public keys."
);
parameter_set!(
    sha2_192s,
    Sha2_192s,
    24,
    16224,
    "SLH-DSA-SHA2-192s with exact typed seeds and public keys."
);

/// Verifies using an explicitly selected parameter set; there is no cross-set fallback.
pub fn verify(
    parameters: ParameterSet,
    public_key: &[u8],
    message: &[u8],
    context: &[u8],
    signature: &[u8],
) -> Result<(), Error> {
    match parameters {
        ParameterSet::Sha2_128f => sha2_128f::verify(public_key, message, context, signature),
        ParameterSet::Sha2_192s => sha2_192s::verify(public_key, message, context, signature),
    }
}

#[cfg(test)]
mod tests;
