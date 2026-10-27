//! Commitments to one step's spare keys.

use sha2::{Digest, Sha256};
use zcash_protocol::constants::{WOTS_KEY_COMMITMENT_DOMAIN, WOTS_NODE_DOMAIN};

use super::{SPARES, VerifyingKey};

/// Commits to one key's canonical encoding: its public seed followed by its chain endpoints.
pub fn leaf_commit(key: &VerifyingKey) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(WOTS_KEY_COMMITMENT_DOMAIN);
    hash.update(key.to_bytes());
    hash.finalize().into()
}

fn node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(WOTS_NODE_DOMAIN);
    hash.update(left);
    hash.update(right);
    hash.finalize().into()
}

/// Recomputes a step's root from one spare's leaf and its two sibling hashes, ordered from
/// the leaf upwards. Returns `None` for a spare index outside the tree.
pub fn root_from_path(leaf: [u8; 32], spare: u8, path: &[[u8; 32]; 2]) -> Option<[u8; 32]> {
    if usize::from(spare) >= SPARES {
        return None;
    }
    let mut hash = leaf;
    for (level, sibling) in path.iter().enumerate() {
        hash = if spare >> level & 1 == 0 {
            node(&hash, sibling)
        } else {
            node(sibling, &hash)
        };
    }
    Some(hash)
}

/// The public keys of one step's spares and the root committing to them.
#[derive(Clone, Debug)]
pub struct KeySet {
    keys: [VerifyingKey; SPARES],
    leaves: [[u8; 32]; SPARES],
}

impl KeySet {
    /// Commits to the given keys in spare order.
    pub fn new(keys: [VerifyingKey; SPARES]) -> Self {
        let leaves = core::array::from_fn(|index| leaf_commit(&keys[index]));
        Self { keys, leaves }
    }

    /// The public key of one spare.
    pub fn key(&self, spare: u8) -> Option<&VerifyingKey> {
        self.keys.get(usize::from(spare))
    }

    /// The step's key-set root `K(n)`.
    pub fn root(&self) -> [u8; 32] {
        let [a, b, c, d] = &self.leaves;
        node(&node(a, b), &node(c, d))
    }

    /// The sibling hashes proving one spare belongs to [`Self::root`].
    pub fn path(&self, spare: u8) -> Option<[[u8; 32]; 2]> {
        let index = usize::from(spare);
        if index >= SPARES {
            return None;
        }
        let [a, b, c, d] = &self.leaves;
        let upper = if index < 2 { node(c, d) } else { node(a, b) };
        Some([self.leaves[index ^ 1], upper])
    }
}
