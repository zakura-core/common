//! Prototype key derivation from a wallet seed. To be replaced by a frozen specification
//! before any public network uses it.

use alloc::vec::Vec;

use blake2b_simd::Params;

use super::{AccountScript, KeySet, SPARES, SigningKey};

fn hash(personal: &[u8; 16], key: &[u8], message: &[u8]) -> [u8; 32] {
    Params::new()
        .hash_length(32)
        .personal(personal)
        .key(key)
        .hash(message)
        .as_bytes()
        .try_into()
        .expect("the hash length is 32")
}

/// Derives the key from which every account's spares are derived.
pub fn master_from_seed(seed: &[u8]) -> [u8; 32] {
    hash(b"Zcash_WOTSMaster", &[], seed)
}

/// Derives spare `spare` of step `step` of account index `account`.
///
/// The account index is used rather than the account hash, which depends on the step-0
/// keys. Deriving the same key twice is easy, so callers must record a spare as used
/// before broadcasting anything it signed.
pub fn signing_key(
    master: &[u8; 32],
    account: u32,
    step: u32,
    spare: u8,
) -> Result<SigningKey, wots_plus::SeedError> {
    let mut path = [0; 9];
    path[..4].copy_from_slice(&account.to_le_bytes());
    path[4..8].copy_from_slice(&step.to_le_bytes());
    path[8] = spare;
    SigningKey::from_seeds(
        wots_plus::SecretSeed::from_bytes(hash(b"Zcash_WOTS_SK___", master, &path)),
        wots_plus::PublicSeed::from_bytes(hash(b"Zcash_WOTS_PK___", master, &path)),
    )
}

impl KeySet {
    /// Derives the public keys of every spare of step `step` of account index `account`.
    pub fn derive(
        master: &[u8; 32],
        account: u32,
        step: u32,
    ) -> Result<Self, wots_plus::SeedError> {
        let mut keys = Vec::with_capacity(SPARES);
        for spare in 0..SPARES {
            let spare = u8::try_from(spare).expect("few spares");
            keys.push(signing_key(master, account, step, spare)?.verifying_key());
        }
        Ok(Self::new(keys.try_into().expect("one key per spare")))
    }
}

impl AccountScript {
    /// Derives account index `account`'s redeem script.
    pub fn derive(master: &[u8; 32], account: u32) -> Result<Self, wots_plus::SeedError> {
        Ok(Self::new(KeySet::derive(master, account, 0)?.root()))
    }
}
