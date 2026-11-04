//! Constants used in the Orchard protocol.
#[path = "constants/sinsemilla.rs"]
pub mod sinsemilla;
#[path = "constants/util.rs"]
pub mod util;

/// $\mathsf{MerkleDepth^{Orchard}}$
pub const MERKLE_DEPTH_ORCHARD: usize = 32;

/// $\ell^\mathsf{Orchard}_\mathsf{base}$
pub const L_ORCHARD_BASE: usize = 255;

/// $\ell^\mathsf{Orchard}_\mathsf{scalar}$
pub const L_ORCHARD_SCALAR: usize = 255;

/// $\ell_\mathsf{value}$
pub const L_VALUE: usize = 64;

#[cfg(test)]
mod tests {
    use sensei::primitives::pallas;

    #[test]
    // Orchard uses the Pallas base field as its base field.
    fn l_orchard_base() {
        assert_eq!(super::L_ORCHARD_BASE, pallas::Base::NUM_BITS as usize);
    }

    #[test]
    // Orchard uses the Pallas base field as its base field.
    fn l_orchard_scalar() {
        assert_eq!(super::L_ORCHARD_SCALAR, pallas::Scalar::NUM_BITS as usize);
    }
}
