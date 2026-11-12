//! SHA-256 hashing utilities.

use sha2::{Digest, Sha256};

/// Computes `SHA-256(input)` in one shot.
pub fn hash(input: &[u8]) -> [u8; 32] {
    Sha256::digest(input).into()
}
