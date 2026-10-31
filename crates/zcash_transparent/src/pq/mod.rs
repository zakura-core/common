//! SLH-DSA primitives and native transparent script authorization.
//!
//! Uses the Pure external interface from [FIPS 205](https://doi.org/10.6028/NIST.FIPS.205).
//! These library APIs do not activate network rules or define wallet derivation.

pub mod native;

/// A cryptographic encoding, context or signature verification error.
pub use slh_dsa::signature::Error;

/// The parameter set committed by a native output's version.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParameterSet {
    /// SHA2-128f, NIST Category 1, prioritizing signature-generation speed.
    Sha2_128f,
    /// SHA2-192s, NIST Category 3, prioritizing signature size.
    Sha2_192s,
}

impl ParameterSet {
    /// Native output version byte.
    pub const fn version(self) -> u8 {
        match self {
            Self::Sha2_128f => 1,
            Self::Sha2_192s => 2,
        }
    }
    /// Exact encoded public-key size.
    pub const fn public_key_bytes(self) -> usize {
        match self {
            Self::Sha2_128f => sha2_128f::PUBLIC_KEY_BYTES,
            Self::Sha2_192s => sha2_192s::PUBLIC_KEY_BYTES,
        }
    }
    /// Exact signature size, excluding a transaction signing-mode selector.
    pub const fn signature_bytes(self) -> usize {
        match self {
            Self::Sha2_128f => sha2_128f::SIGNATURE_BYTES,
            Self::Sha2_192s => sha2_192s::SIGNATURE_BYTES,
        }
    }
}

macro_rules! parameter_set {
    ($module:ident, $algorithm:ident, $n:literal, $signature:literal, $doc:literal) => {
        #[doc = $doc]
        pub mod $module {
            use super::Error;
            use alloc::vec::Vec;
            /// Concatenated SK.seed, SK.prf and PK.seed bytes.
            pub const SEED_BYTES: usize = 3 * $n;
            /// Encoded public seed and public root.
            pub const PUBLIC_KEY_BYTES: usize = 2 * $n;
            /// Standardized signature encoding size.
            pub const SIGNATURE_BYTES: usize = $signature;
            /// Private reusable signing key. Secret storage is zeroized on drop.
            /// No secret export or debug formatting is exposed.
            pub struct SigningKey(slh_dsa::SigningKey<slh_dsa::$algorithm>);
            impl SigningKey {
                /// Constructs a key from caller-supplied secure seed material.
                /// The caller is responsible for protecting and clearing its seed copy.
                pub fn from_seed(seed: &[u8; SEED_BYTES]) -> Self {
                    Self(slh_dsa::SigningKey::slh_keygen_internal(
                        &seed[..$n],
                        &seed[$n..2 * $n],
                        &seed[2 * $n..],
                    ))
                }
                /// Returns the canonical public key.
                pub fn public_key(&self) -> [u8; PUBLIC_KEY_BYTES] {
                    self.0.as_ref().to_bytes().into()
                }
                /// Deterministic Pure SLH-DSA signing of the supplied application message.
                /// Contexts are limited to 255 bytes; no additional application hash is added.
                pub fn sign(&self, message: &[u8], context: &[u8]) -> Result<Vec<u8>, Error> {
                    self.0
                        .try_sign_with_context(message, context, None)
                        .map(|sig| sig.to_bytes().to_vec())
                }
            }
            /// Verifies exact key/signature encodings through the Pure external interface.
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
    "SLH-DSA-SHA2-128f signing and verification."
);
parameter_set!(
    sha2_192s,
    Sha2_192s,
    24,
    16224,
    "SLH-DSA-SHA2-192s signing and verification."
);

/// Verifies with an explicit parameter set, without trying alternative algorithms.
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
