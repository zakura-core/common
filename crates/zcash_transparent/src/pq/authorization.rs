//! One spare's signature over a transaction, with its proof of membership in a step.

use alloc::vec::Vec;

use super::{KeySet, Scheme, SignatureScheme, SigningKey, leaf_commit, root_from_path};

/// The witness is split into pushes of at most this size.
const CHUNK: usize = 512;
/// Number of pushes the witness takes.
const WITNESS_PUSHES: usize = Scheme::WITNESS_BYTES.div_ceil(CHUNK);
/// Number of pushes in an authorization: the witness chunks, the spare and the path.
pub(super) const PUSHES: usize = WITNESS_PUSHES + 2;
/// Encoded size of an authorization's pushes.
pub(super) const ENCODED_SIZE: usize = {
    let full = Scheme::WITNESS_BYTES / CHUNK;
    let rest = Scheme::WITNESS_BYTES % CHUNK;
    let rest = if rest == 0 { 0 } else { push_size(rest) };
    full * push_size(CHUNK) + rest + push_size(1) + push_size(64)
};

/// Size of one push of `len` bytes in the encoding [`super::push`] produces.
const fn push_size(len: usize) -> usize {
    match len {
        0..=75 => 1 + len,
        76..=255 => 2 + len,
        _ => 3 + len,
    }
}

/// A signature by one spare of a step, with the spare index and authentication path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Authorization {
    /// The scheme's witness over the transaction digest.
    pub witness: Vec<u8>,
    /// Which of the step's spares signed.
    pub spare: u8,
    /// Sibling hashes from the spare's leaf up to the step's root.
    pub path: [[u8; 32]; 2],
}

impl Authorization {
    /// Signs `digest` with spare `spare` of `keys`, consuming the key so it cannot sign again
    /// through this API. Fails if the key is not that spare.
    pub fn sign(
        key: SigningKey,
        keys: &KeySet,
        spare: u8,
        digest: [u8; 32],
    ) -> Result<Self, &'static str> {
        if keys.key(spare) != Some(&Scheme::public_key(&key)) {
            return Err("the signing key is not that spare of the key set");
        }
        let path = keys.path(spare).expect("the spare exists");
        Ok(Self {
            witness: Scheme::sign(key, &digest),
            spare,
            path,
        })
    }

    /// Recomputes the signing key's root, or `None` for a malformed witness or a spare index
    /// outside the tree.
    ///
    /// Recovery accepts any witness-shaped bytes; only comparing the result with a trusted
    /// root authenticates the signature.
    pub fn recover_root(&self, digest: [u8; 32]) -> Option<[u8; 32]> {
        let key = Scheme::recover(&digest, &self.witness)?;
        root_from_path(leaf_commit(&key), self.spare, &self.path)
    }

    /// Whether this authorization signs `digest` under `root`.
    pub fn verify(&self, digest: [u8; 32], root: &[u8; 32]) -> bool {
        self.recover_root(digest).as_ref() == Some(root)
    }

    /// Appends the authorization's pushes to a script signature.
    pub fn push_into(&self, bytes: &mut Vec<u8>) {
        for chunk in self.witness.chunks(CHUNK) {
            super::push(bytes, chunk);
        }
        super::push(bytes, &[self.spare]);
        super::push(bytes, &[self.path[0], self.path[1]].concat());
    }

    /// Decodes exactly [`PUSHES`] values in the order [`Self::push_into`] writes them.
    pub(super) fn from_pushes(values: &[&[u8]]) -> Option<Self> {
        if values.len() != PUSHES {
            return None;
        }
        let (chunks, rest) = values.split_at(WITNESS_PUSHES);
        let [spare, path] = rest else {
            return None;
        };
        let mut witness = Vec::with_capacity(Scheme::WITNESS_BYTES);
        for chunk in chunks {
            let expected = core::cmp::min(CHUNK, Scheme::WITNESS_BYTES - witness.len());
            if chunk.len() != expected {
                return None;
            }
            witness.extend_from_slice(chunk);
        }
        let [spare]: [u8; 1] = (*spare).try_into().ok()?;
        let path: &[u8; 64] = (*path).try_into().ok()?;
        Some(Self {
            witness,
            spare,
            path: [
                path[..32].try_into().expect("fixed slice"),
                path[32..].try_into().expect("fixed slice"),
            ],
        })
    }
}
