//! WOTS+ (RFC 8391 with n = 32, w = 16 and SHA-256) as the account signature scheme.
//!
//! This is the only module that uses the `wots-plus` library.

use alloc::vec::Vec;

use wots_plus::{
    MessageDigest, PublicSeed, SIGNATURE_BYTES, SecretSeed, SeedError, Signature, SigningKey,
    VerifyingKey,
};
use zcash_protocol::constants::WOTS_KEY_COMMITMENT_DOMAIN;

use super::{KeySeed, SignatureScheme};

/// One-time WOTS+ keys. A witness is the signature followed by the key's public seed, from
/// which the whole public key is recovered.
#[derive(Clone, Copy, Debug)]
pub enum WotsPlus {}

impl SignatureScheme for WotsPlus {
    const KEY_DOMAIN: &'static [u8] = WOTS_KEY_COMMITMENT_DOMAIN;
    const WITNESS_BYTES: usize = SIGNATURE_BYTES + 32;
    const SIGOPS: u32 = 100;

    type SigningKey = SigningKey;
    type PublicKey = VerifyingKey;
    type DeriveError = SeedError;

    fn derive(seed: &KeySeed) -> Result<SigningKey, SeedError> {
        SigningKey::from_seeds(
            SecretSeed::from_bytes(seed.expand(b"Zcash_WOTS_SK___")),
            PublicSeed::from_bytes(seed.expand(b"Zcash_WOTS_PK___")),
        )
    }

    fn public_key(key: &SigningKey) -> VerifyingKey {
        key.verifying_key()
    }

    /// The public seed followed by the chain endpoints.
    fn encode_public_key(key: &VerifyingKey) -> Vec<u8> {
        key.to_bytes().to_vec()
    }

    fn sign(key: SigningKey, digest: &[u8; 32]) -> Vec<u8> {
        let public_seed = *key.verifying_key().public_seed().as_bytes();
        let signature = key.sign_digest(&MessageDigest::from_bytes(*digest));
        [&signature.to_bytes()[..], &public_seed].concat()
    }

    fn recover(digest: &[u8; 32], witness: &[u8]) -> Option<VerifyingKey> {
        if witness.len() != Self::WITNESS_BYTES {
            return None;
        }
        let (signature, public_seed) = witness.split_at(SIGNATURE_BYTES);
        Some(VerifyingKey::recover_from_signature(
            &MessageDigest::from_bytes(*digest),
            &Signature::from_bytes(signature.try_into().ok()?),
            PublicSeed::from_bytes(public_seed.try_into().ok()?),
        ))
    }
}
