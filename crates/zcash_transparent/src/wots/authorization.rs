//! One spare's signature over a transaction, with its proof of membership in a step.

use alloc::vec::Vec;

use super::{KeySet, MessageDigest, SigningKey, VerifyingKey, leaf_commit, root_from_path};

const SIGNATURE_BYTES: usize = wots_plus::SIGNATURE_BYTES;
/// The signature is split into pushes of at most this size.
const CHUNK: usize = 512;
/// Number of pushes in an authorization: five signature chunks, seed, spare, path.
pub(super) const PUSHES: usize = 8;
/// Encoded size: four PUSHDATA2 and one PUSHDATA1 signature chunks, then direct pushes.
pub(super) const ENCODED_SIZE: usize = 4 * (3 + CHUNK) + (2 + 96) + (1 + 32) + (1 + 1) + (1 + 64);

/// A WOTS+ signature by one spare of a step, with the spare index and authentication path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Authorization {
    /// The WOTS+ signature over the transaction digest.
    pub signature: [u8; SIGNATURE_BYTES],
    /// The signing key's public seed, needed to recover its public key.
    pub public_seed: [u8; 32],
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
        let public_key = key.verifying_key();
        if keys.key(spare) != Some(&public_key) {
            return Err("the signing key is not that spare of the key set");
        }
        let path = keys.path(spare).expect("the spare exists");
        let signature = key
            .sign_digest(&MessageDigest::from_bytes(digest))
            .to_bytes();
        Ok(Self {
            signature,
            public_seed: *public_key.public_seed().as_bytes(),
            spare,
            path,
        })
    }

    /// Recomputes the signing key's root, or `None` for a spare index outside the tree.
    ///
    /// Recovery accepts any signature-shaped bytes; only comparing the result with a
    /// trusted root authenticates the signature.
    pub fn recover_root(&self, digest: [u8; 32]) -> Option<[u8; 32]> {
        let key = VerifyingKey::recover_from_signature(
            &MessageDigest::from_bytes(digest),
            &wots_plus::Signature::from_bytes(&self.signature),
            wots_plus::PublicSeed::from_bytes(self.public_seed),
        );
        root_from_path(leaf_commit(&key), self.spare, &self.path)
    }

    /// Whether this authorization signs `digest` under `root`.
    pub fn verify(&self, digest: [u8; 32], root: &[u8; 32]) -> bool {
        self.recover_root(digest).as_ref() == Some(root)
    }

    /// Appends the authorization's pushes to a script signature.
    pub fn push_into(&self, bytes: &mut Vec<u8>) {
        for chunk in self.signature.chunks(CHUNK) {
            super::push(bytes, chunk);
        }
        super::push(bytes, &self.public_seed);
        super::push(bytes, &[self.spare]);
        super::push(bytes, &[self.path[0], self.path[1]].concat());
    }

    /// Decodes exactly [`PUSHES`] values in the order [`Self::push_into`] writes them.
    pub(super) fn from_pushes(values: &[&[u8]]) -> Option<Self> {
        let [s0, s1, s2, s3, s4, seed, spare, path] = values.try_into().ok()?;
        let mut signature = [0; SIGNATURE_BYTES];
        let mut offset = 0;
        for chunk in [s0, s1, s2, s3, s4] {
            let end = core::cmp::min(offset + CHUNK, SIGNATURE_BYTES);
            if chunk.len() != end - offset {
                return None;
            }
            signature[offset..end].copy_from_slice(chunk);
            offset = end;
        }
        let [spare]: [u8; 1] = (*spare).try_into().ok()?;
        let path: &[u8; 64] = (*path).try_into().ok()?;
        Some(Self {
            signature,
            public_seed: (*seed).try_into().ok()?,
            spare,
            path: [
                path[..32].try_into().expect("fixed slice"),
                path[32..].try_into().expect("fixed slice"),
            ],
        })
    }
}
