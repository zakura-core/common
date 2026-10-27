//! Prototype key derivation from a wallet seed. To be replaced by a frozen specification
//! before any public network uses it.

use alloc::vec::Vec;

use blake2b_simd::Params;

use super::{AccountScript, DeriveError, KeySet, SPARES, Scheme, SignatureScheme, SigningKey};

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
    hash(b"Zcash_PQ_Master_", &[], seed)
}

/// The secret input for one spare of one step of one account, from which the scheme derives
/// that spare's key.
pub struct KeySeed {
    master: [u8; 32],
    path: [u8; 9],
}

impl KeySeed {
    /// The seed of spare `spare` of step `step` of account index `account`.
    ///
    /// The account index is used rather than the account hash, which depends on the step-0
    /// keys.
    pub fn new(master: &[u8; 32], account: u32, step: u32, spare: u8) -> Self {
        let mut path = [0; 9];
        path[..4].copy_from_slice(&account.to_le_bytes());
        path[4..8].copy_from_slice(&step.to_le_bytes());
        path[8] = spare;
        Self {
            master: *master,
            path,
        }
    }

    /// A 32-byte secret for this spare, separated from the scheme's other secrets by `label`.
    pub fn expand(&self, label: &[u8; 16]) -> [u8; 32] {
        hash(label, &self.master, &self.path)
    }
}

/// Derives spare `spare` of step `step` of account index `account`.
///
/// Deriving the same key twice is easy, so callers must record a spare as used before
/// broadcasting anything it signed.
pub fn signing_key(
    master: &[u8; 32],
    account: u32,
    step: u32,
    spare: u8,
) -> Result<SigningKey, DeriveError> {
    Scheme::derive(&KeySeed::new(master, account, step, spare))
}

impl KeySet {
    /// Derives the public keys of every spare of step `step` of account index `account`.
    pub fn derive(master: &[u8; 32], account: u32, step: u32) -> Result<Self, DeriveError> {
        let mut keys = Vec::with_capacity(SPARES);
        for spare in 0..SPARES {
            let spare = u8::try_from(spare).expect("few spares");
            keys.push(Scheme::public_key(&signing_key(
                master, account, step, spare,
            )?));
        }
        Ok(Self::new(keys.try_into().expect("one key per spare")))
    }
}

impl AccountScript {
    /// Derives account index `account`'s redeem script.
    pub fn derive(master: &[u8; 32], account: u32) -> Result<Self, DeriveError> {
        Ok(Self::new(KeySet::derive(master, account, 0)?.root()))
    }
}
