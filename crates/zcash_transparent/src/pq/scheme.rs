//! The signature scheme that authorizes account spends.
//!
//! The account rules use the scheme only through [`SignatureScheme`], and reach the one in
//! use through [`Scheme`]. Replacing the scheme means implementing the trait in a module of
//! this directory, pointing [`Scheme`] at it, and changing the library dependency; no other
//! file names a scheme library.

use alloc::vec::Vec;
use core::fmt::Debug;

use super::derive::KeySeed;

mod wots_plus;

pub use wots_plus::WotsPlus;

/// The scheme every account uses.
pub type Scheme = WotsPlus;
/// A key that signs one account spend.
pub type SigningKey = <Scheme as SignatureScheme>::SigningKey;
/// The public key an account commits to for one spare.
pub type PublicKey = <Scheme as SignatureScheme>::PublicKey;
/// Why a key could not be derived.
pub type DeriveError = <Scheme as SignatureScheme>::DeriveError;

/// What the account rules need from a signature scheme.
///
/// A spend carries a fixed-size witness: the signature plus whatever else is needed to learn
/// the public key it was made with. Verification recovers that public key from the witness and
/// the signed digest; the account rules then authenticate the key by its commitment in the
/// step's key set. A scheme whose public key cannot be recovered from a signature carries the
/// key in the witness and returns it only if the signature verifies under it.
pub trait SignatureScheme {
    /// Domain separator for committing to one public key in a key set.
    const KEY_DOMAIN: &'static [u8];
    /// Exact size of a witness in bytes.
    const WITNESS_BYTES: usize;
    /// Experimental verification charge per signature; not a production cost model.
    const SIGOPS: u32;

    /// A secret key. One-time and few-time schemes must never sign more than allowed with it.
    type SigningKey;
    /// A public key, compared for equality and committed to by its encoding.
    type PublicKey: Clone + Debug + Eq;
    /// Why a key could not be derived from a seed.
    type DeriveError: Debug;

    /// Derives the key for one account, step and spare.
    fn derive(seed: &KeySeed) -> Result<Self::SigningKey, Self::DeriveError>;

    /// The public key of a secret key.
    fn public_key(key: &Self::SigningKey) -> Self::PublicKey;

    /// The canonical encoding of a public key, which its commitment hashes.
    fn encode_public_key(key: &Self::PublicKey) -> Vec<u8>;

    /// Signs a 32-byte digest, returning a witness of [`Self::WITNESS_BYTES`] bytes. Takes the
    /// key by value so it cannot sign again through this call.
    fn sign(key: Self::SigningKey, digest: &[u8; 32]) -> Vec<u8>;

    /// The public key the witness was made with for `digest`, or `None` if the witness is
    /// malformed or does not verify.
    ///
    /// A key recovered from arbitrary bytes is not authenticated; only matching its
    /// commitment against a trusted key set is.
    fn recover(digest: &[u8; 32], witness: &[u8]) -> Option<Self::PublicKey>;
}
