//! SLH-DSA (FIPS 205, the standardized SPHINCS+) as the account signature scheme.
//!
//! This is the only module that uses the `slh-dsa` library. SLH-DSA keys sign any number of
//! times, so an account's spares only cover replacing unconfirmed spends, not key reuse.

use alloc::vec::Vec;
use core::marker::PhantomData;

use slh_dsa::{ParameterSet, Signature, SigningKey, VerifyingKey};
use zcash_protocol::constants::SLH_DSA_KEY_COMMITMENT_DOMAIN;

use super::{KeySeed, SignatureScheme};

/// SLH-DSA context string binding signatures to Zcash account spends.
const CONTEXT: &[u8] = b"Zcash/PQ/spend/v1";

/// The SLH-DSA parameter sets the accounts can be built on, with their encoded sizes.
pub trait Parameters: ParameterSet {
    /// Size of one secret seed, and half the size of a public key.
    const N: usize;
    /// Size of a signature.
    const SIGNATURE_BYTES: usize;
}

impl Parameters for slh_dsa::Sha2_128s {
    const N: usize = 16;
    const SIGNATURE_BYTES: usize = 7856;
}

impl Parameters for slh_dsa::Sha2_128f {
    const N: usize = 16;
    const SIGNATURE_BYTES: usize = 17088;
}

impl Parameters for slh_dsa::Sha2_256s {
    const N: usize = 32;
    const SIGNATURE_BYTES: usize = 29792;
}

/// SLH-DSA keys with parameter set `P`. A witness is the signature followed by the public
/// key, which cannot be recovered from the signature alone.
pub struct SlhDsa<P>(PhantomData<P>);

/// The smallest-signature 128-bit parameter set, the only one whose authorization fits the
/// 10,000-byte script limit.
pub type SlhDsaSha2_128s = SlhDsa<slh_dsa::Sha2_128s>;

impl<P: Parameters> SignatureScheme for SlhDsa<P> {
    const KEY_DOMAIN: &'static [u8] = SLH_DSA_KEY_COMMITMENT_DOMAIN;
    const WITNESS_BYTES: usize = P::SIGNATURE_BYTES + 2 * P::N;
    const SIGOPS: u32 = 100;

    type SigningKey = SigningKey<P>;
    type PublicKey = VerifyingKey<P>;
    type DeriveError = core::convert::Infallible;

    /// FIPS 205 key generation from three seeds expanded from the spare's secret.
    fn derive(seed: &KeySeed) -> Result<SigningKey<P>, Self::DeriveError> {
        Ok(SigningKey::slh_keygen_internal(
            &seed.expand(b"Zcash_SLH_SKSeed")[..P::N],
            &seed.expand(b"Zcash_SLH_SKPrf_")[..P::N],
            &seed.expand(b"Zcash_SLH_PKSeed")[..P::N],
        ))
    }

    fn public_key(key: &SigningKey<P>) -> VerifyingKey<P> {
        key.as_ref().clone()
    }

    /// The public seed followed by the hypertree root.
    fn encode_public_key(key: &VerifyingKey<P>) -> Vec<u8> {
        key.to_vec()
    }

    /// Deterministic signing: the randomizer comes from the key, so re-signing a digest
    /// reproduces the same witness.
    fn sign(key: SigningKey<P>, digest: &[u8; 32]) -> Vec<u8> {
        let signature = key
            .try_sign_with_context(digest, CONTEXT, None)
            .expect("the context is shorter than 256 bytes");
        [signature.to_vec(), key.as_ref().to_vec()].concat()
    }

    fn recover(digest: &[u8; 32], witness: &[u8]) -> Option<VerifyingKey<P>> {
        if witness.len() != Self::WITNESS_BYTES {
            return None;
        }
        let (signature, public_key) = witness.split_at(P::SIGNATURE_BYTES);
        let signature = Signature::<P>::try_from(signature).ok()?;
        let public_key = VerifyingKey::<P>::try_from(public_key).ok()?;
        public_key
            .try_verify_with_context(digest, CONTEXT, &signature)
            .ok()?;
        Some(public_key)
    }
}
