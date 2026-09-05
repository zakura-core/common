//! This module contains implementations for the two finite fields of the Pallas
//! and Vesta curves.

#[cfg(feature = "alloc")]
mod fft;
mod fp;
mod fq;
mod modinv62;
mod portable;

use crate::arithmetic::mac;

const MAX_INVERSE_POWER_OF_TWO_EXPONENT: u32 = u64::BITS - 1;
#[cfg(test)]
const INVERSE_POWER_OF_TWO_TEST_EXPONENTS: [u32; 7] =
    [0, 1, 11, 14, 31, 32, MAX_INVERSE_POWER_OF_TWO_EXPONENT];

/// Multiplies a canonical Montgomery representation by `2^-exponent`.
#[inline(always)]
fn mul_by_inverse_power_of_two(
    value: [u64; 4],
    modulus: [u64; 4],
    inv: u64,
    exponent: u32,
) -> [u64; 4] {
    assert!(exponent <= MAX_INVERSE_POWER_OF_TWO_EXPONENT);

    if exponent == 0 {
        return value;
    }

    // Choose q so that value + q * modulus is divisible by 2^exponent.
    // Because q < 2^exponent and value < modulus, the quotient is already
    // canonical.
    let mask = (1u64 << exponent) - 1;
    let q = value[0].wrapping_mul(inv) & mask;
    let (r0, carry) = mac(value[0], q, modulus[0], 0);
    let (r1, carry) = mac(value[1], q, modulus[1], carry);
    let (r2, carry) = mac(value[2], q, modulus[2], carry);
    let (r3, r4) = mac(value[3], q, modulus[3], carry);
    let shift = u64::BITS - exponent;

    debug_assert_eq!(r0 & mask, 0);

    [
        (r0 >> exponent) | (r1 << shift),
        (r1 >> exponent) | (r2 << shift),
        (r2 >> exponent) | (r3 << shift),
        (r3 >> exponent) | (r4 << shift),
    ]
}

// Keep the assembly FFI exception contained within a private module whose
// public interface consists only of safe wrappers.
#[allow(unsafe_code)]
#[cfg(all(
    feature = "aarch64-asm",
    target_arch = "aarch64",
    target_family = "unix"
))]
mod aarch64_asm;

pub use fp::*;
pub use fq::*;

#[cfg(test)]
fn check_equality<F: core::fmt::Debug + PartialEq + subtle::ConstantTimeEq>(values: &[F]) {
    for lhs in values {
        for rhs in values {
            assert_eq!(*lhs == *rhs, bool::from(lhs.ct_eq(rhs)));
        }
    }
}

#[cfg(test)]
#[test]
fn variable_time_equality_matches_constant_time_equality() {
    check_equality(&[Fp::zero(), Fp::one(), Fp::from(2), -Fp::one()]);
    check_equality(&[Fq::zero(), Fq::one(), Fq::from(2), -Fq::one()]);
}

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
