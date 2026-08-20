//! This module contains implementations for the two finite fields of the Pallas
//! and Vesta curves.

pub(crate) mod cm;
mod fp;
mod fq;
// Under `cm-field` the Montgomery parameter sets (and the Montgomery-coupled
// test macro) are compiled but unused outside tests; inversion itself runs
// through the canonical parameter sets in both representations.
#[cfg_attr(feature = "cm-field", allow(dead_code, unused_macros))]
mod modinv62;

// Keep the assembly FFI exception contained within a private module whose
// public interface consists only of safe wrappers. The backend implements
// Montgomery arithmetic, so it is disabled under the experimental `cm-field`
// representation until a CM backend exists.
#[allow(unsafe_code)]
#[cfg(all(
    feature = "aarch64-asm",
    not(feature = "cm-field"),
    target_arch = "aarch64",
    target_vendor = "apple"
))]
mod aarch64_asm;

pub use fp::*;
pub use fq::*;

/// Converts 64-bit little-endian limbs to 32-bit little endian limbs.
#[cfg(feature = "gpu")]
fn u64_to_u32(limbs: &[u64]) -> alloc::vec::Vec<u32> {
    limbs
        .iter()
        .flat_map(|limb| [(limb & 0xFFFF_FFFF) as u32, (limb >> 32) as u32].into_iter())
        .collect()
}

#[cfg(feature = "gpu")]
#[test]
fn test_u64_to_u32() {
    use rand::{Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;

    let mut rng = XorShiftRng::from_seed([0; 16]);
    let u64_limbs: alloc::vec::Vec<u64> = (0..6).map(|_| rng.next_u64()).collect();
    let u32_limbs = crate::fields::u64_to_u32(&u64_limbs);

    let u64_le_bytes: alloc::vec::Vec<u8> = u64_limbs
        .iter()
        .flat_map(|limb| limb.to_le_bytes())
        .collect();
    let u32_le_bytes: alloc::vec::Vec<u8> = u32_limbs
        .iter()
        .flat_map(|limb| limb.to_le_bytes())
        .collect();

    assert_eq!(u64_le_bytes, u32_le_bytes);
}
