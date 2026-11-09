//! Standalone SLH-DSA-SHA2-128f and SLH-DSA-SHA2-192s primitives, backed by RustCrypto's `slh-dsa`.
//!
//! This module implements deterministic Pure SLH-DSA as specified in
//! [FIPS 205](https://doi.org/10.6028/NIST.FIPS.205). The message and context are supplied
//! by the caller; no transaction digest, wallet derivation, authorization encoding,
//! or address format is defined by these primitives. The separate [`script`] module
//! provides a library-only script harness, and [`output`] defines a PQ output carrying a
//! format and a signature scheme, and authenticates the script it commits to. This is not
//! HashSLH-DSA.
//!
//! Verification authenticates the message only relative to the supplied public key.
//! The caller must authenticate that key and choose the message and context that bind
//! the signature to its intended use. Contexts may contain at most 255 bytes.

pub mod output;
pub mod script;
pub mod template;

use zcash_address::unified::PqScheme;

/// A malformed encoding, overlong context, or invalid signature.
pub use slh_dsa::signature::Error;

/// One below `OP_1`, so that adding a scheme in 1..=16 gives the opcode that denotes it.
const SCHEME_OPCODE_BASE: u8 = 0x50;
/// `OP_1`, the opcode for the lowest scheme number the namespace can express.
const SCHEME_OPCODE_FIRST: u8 = SCHEME_OPCODE_BASE + 1;
/// `OP_16`, the opcode for the highest scheme number the namespace can express.
const SCHEME_OPCODE_LAST: u8 = SCHEME_OPCODE_BASE + 16;

/// Explicit SLH-DSA parameter selection. Script arguments never select this value;
/// an authenticated output's scheme does, through [`ParameterSet::from_scheme`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParameterSet {
    /// NIST Category 1, optimized for signing speed.
    Sha2_128f,
    /// NIST Category 3, optimized for signature size.
    Sha2_192s,
}

impl ParameterSet {
    /// The scheme number, within format 0, that selects this parameter set.
    ///
    /// Inside format 0 schemes and parameter sets are one to one, so a parameter set
    /// stands in for a scheme wherever that is convenient: [`output::output_script`] writes
    /// the opcode for the scheme this returns, through [`Self::scheme_opcode`], and
    /// [`output::signing_context`] is keyed on the parameter set rather than on the two
    /// header bytes. A second format ends that, which is the point of having two layers:
    /// the format exists so the commitment can change while the signature schemes stay, so
    /// a later format reusing a parameter set leaves this function with no single answer.
    /// It would need both header bytes carried in [`output::PqOutput`] and the signing
    /// context keyed on both, so that two formats sharing a scheme still get distinct
    /// contexts.
    pub const fn scheme(self) -> u8 {
        match self {
            Self::Sha2_128f => 1,
            Self::Sha2_192s => 2,
        }
    }
    /// The parameter set a format-0 scheme selects, if any scheme does.
    ///
    /// This direction stays correct however the table grows; only [`Self::scheme`] relies
    /// on the mapping being one to one.
    pub const fn from_scheme(scheme: u8) -> Option<Self> {
        match scheme {
            1 => Some(Self::Sha2_128f),
            2 => Some(Self::Sha2_192s),
            _ => None,
        }
    }
    /// The opcode an output writes to carry this scheme.
    ///
    /// An output spells its scheme as the small-integer opcode for that number, so the
    /// scheme costs one byte and the output stays a well-formed script. `OP_1` through
    /// `OP_16` are the only single bytes that denote 1 through 16 without consuming what
    /// follows them, which is what caps each format at sixteen schemes.
    pub const fn scheme_opcode(self) -> u8 {
        SCHEME_OPCODE_BASE + self.scheme()
    }
    /// The scheme number an output's opcode names, for `OP_1` through `OP_16` alone.
    ///
    /// This is the namespace's scheme range, not the set of schemes any parameter set
    /// claims: it answers for all sixteen, so a scheme no parameter set defines is still
    /// recognized as being in the namespace and can be restricted rather than left to the
    /// legacy rules. [`Self::from_scheme`] is what then decides whether it is defined.
    pub const fn scheme_from_opcode(opcode: u8) -> Option<u8> {
        match opcode {
            SCHEME_OPCODE_FIRST..=SCHEME_OPCODE_LAST => Some(opcode - SCHEME_OPCODE_BASE),
            _ => None,
        }
    }
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

    /// The unified-address receiver scheme that names this parameter set.
    ///
    /// The address layer carries its own enumeration, because address encodings live in a crate
    /// that knows nothing about signatures. These two functions are the whole join between
    /// them, and the tests check that it is total in both directions, so neither enumeration can
    /// grow a member the other cannot name.
    pub const fn address_scheme(self) -> PqScheme {
        match self {
            Self::Sha2_128f => PqScheme::Sha2_128f,
            Self::Sha2_192s => PqScheme::Sha2_192s,
        }
    }

    /// The parameter set a unified-address receiver scheme names.
    pub const fn from_address_scheme(scheme: PqScheme) -> Self {
        match scheme {
            PqScheme::Sha2_128f => Self::Sha2_128f,
            PqScheme::Sha2_192s => Self::Sha2_192s,
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
