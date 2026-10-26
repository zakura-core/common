//! Sinsemilla generators
use crate::spec::i2lebsp;

pub use sensei::primitives::sinsemilla::K;

/// $\ell^\mathsf{Orchard}_\mathsf{Merkle}$
pub(crate) const L_ORCHARD_MERKLE: usize = 255;

/// SWU hash-to-curve personalization for the Merkle CRH generator
pub const MERKLE_CRH_PERSONALIZATION: &str = "z.cash:Orchard-MerkleCRH";

/// The sequence of K bits in little-endian order representing an integer
/// up to `2^K` - 1.
pub(crate) fn i2lebsp_k(int: usize) -> [bool; K] {
    assert!(int < (1 << K));
    i2lebsp(int as u64)
}

#[cfg(test)]
mod tests {
    use sensei::primitives::pallas;

    #[test]
    // Nodes in the Merkle tree are Pallas base field elements.
    fn l_orchard_merkle() {
        assert_eq!(super::L_ORCHARD_MERKLE, pallas::Base::NUM_BITS as usize);
    }
}
