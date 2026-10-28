//! leanSphincs (SHA-256, height 22, pruned to a kept subtree of height 10) as the account
//! signature scheme.
//!
//! This is the only module that uses the `sphincs` library. The scheme is stateless, so a
//! witness carries the public key followed by the signature, and recovery returns that key
//! only if the signature verifies under it.

use alloc::vec::Vec;
use core::convert::Infallible;

use sphincs::{Config, HashFn, N, PUB_KEY_SIZE, PublicKey, SecretKey, Shape, Signature};
use zcash_protocol::constants::SPHINCS_KEY_COMMITMENT_DOMAIN;

use super::{KeySeed, SignatureScheme};

/// Signature size for [`config`]; a test checks it against the library.
const SIGNATURE_BYTES: usize = 4212;

/// The one configuration accounts use. Key generation builds a subtree of `2^10` leaves, about
/// 50 ms in a release build; signing grinds its randomizer into that subtree.
fn config() -> Config {
    Config::new(HashFn::Sha256, 22, Shape::Pruned { b: 10 })
}

/// Stateless leanSphincs keys.
#[derive(Clone, Copy, Debug)]
pub enum Sphincs {}

impl SignatureScheme for Sphincs {
    const KEY_DOMAIN: &'static [u8] = SPHINCS_KEY_COMMITMENT_DOMAIN;
    const WITNESS_BYTES: usize = PUB_KEY_SIZE + SIGNATURE_BYTES;
    const SIGOPS: u32 = 100;

    type SigningKey = SecretKey;
    type PublicKey = PublicKey;
    type DeriveError = Infallible;

    fn derive(seed: &KeySeed) -> Result<SecretKey, Infallible> {
        Ok(sphincs::key_gen(&config(), &seed.expand(b"Zcash_SPHX_SK___")).0)
    }

    fn public_key(key: &SecretKey) -> PublicKey {
        key.public_key()
    }

    /// The root followed by the public parameter.
    fn encode_public_key(key: &PublicKey) -> Vec<u8> {
        key.to_bytes().to_vec()
    }

    fn sign(key: SecretKey, digest: &[u8; 32]) -> Vec<u8> {
        let signature = sphincs::sign(&key, digest).to_bytes();
        [&key.public_key().to_bytes()[..], &signature].concat()
    }

    fn recover(digest: &[u8; 32], witness: &[u8]) -> Option<PublicKey> {
        if witness.len() != Self::WITNESS_BYTES {
            return None;
        }
        let (key, signature) = witness.split_at(PUB_KEY_SIZE);
        let key = PublicKey {
            root: key[..N].try_into().ok()?,
            public_param: key[N..].try_into().ok()?,
        };
        let config = config();
        let signature = Signature::from_bytes(&config, signature)?;
        sphincs::verify(&config, &key, digest, &signature).ok()?;
        Some(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_signature_size_matches_the_library() {
        assert_eq!(SIGNATURE_BYTES, config().sig_size());
        assert_eq!(PUB_KEY_SIZE, 2 * N);
    }
}
