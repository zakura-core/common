//! This module contains implementations for the two finite fields of the Pallas
//! and Vesta curves.

mod fp;
mod fq;
mod modinv62;
mod portable;

// The private IFMA backend serves variable-time GLV reduction and batched
// decoding. Safe wrappers reject unsupported CPUs before any mutation.
#[allow(unsafe_code)]
#[cfg(all(
    feature = "glv",
    feature = "x86_64-asm",
    target_arch = "x86_64",
    target_pointer_width = "64"
))]
mod ifma;

/// Whether eight-lane IFMA arithmetic is available for this concrete field.
#[cfg(feature = "glv")]
pub(crate) fn ifma_available_for<F: ff::Field>() -> bool {
    #[cfg(all(
        feature = "x86_64-asm",
        target_arch = "x86_64",
        target_pointer_width = "64"
    ))]
    {
        ifma::available_for::<F>()
    }
    #[cfg(not(all(
        feature = "x86_64-asm",
        target_arch = "x86_64",
        target_pointer_width = "64"
    )))]
    {
        false
    }
}

/// Multiplies eight lanes, or returns `false` without changing `lhs`.
#[cfg(feature = "glv")]
pub(crate) fn try_mul_assign8<F: ff::Field>(lhs: &mut [F; 8], rhs: &[F; 8]) -> bool {
    #[cfg(all(
        feature = "x86_64-asm",
        target_arch = "x86_64",
        target_pointer_width = "64"
    ))]
    if ifma_available_for::<F>() {
        ifma::mul8(lhs, rhs);
        return true;
    }
    let _ = (lhs, rhs);
    false
}

/// Squares eight lanes, or returns `false` without changing `values`.
#[cfg(feature = "glv")]
pub(crate) fn try_square8<F: ff::Field>(values: &mut [F; 8]) -> bool {
    #[cfg(all(
        feature = "x86_64-asm",
        target_arch = "x86_64",
        target_pointer_width = "64"
    ))]
    if ifma_available_for::<F>() {
        ifma::square8(values);
        return true;
    }
    let _ = values;
    false
}

/// Computes eight square roots, or declines before any field arithmetic.
#[cfg(all(
    feature = "glv",
    feature = "sqrt-table",
    feature = "x86_64-asm",
    target_arch = "x86_64",
    target_pointer_width = "64"
))]
pub(crate) fn try_sqrt8<F: ff::PrimeField>(values: &[F; 8]) -> Option<[subtle::CtOption<F>; 8]> {
    #[cfg(all(
        feature = "x86_64-asm",
        target_arch = "x86_64",
        target_pointer_width = "64"
    ))]
    {
        use core::any::Any;

        if !ifma_available_for::<F>() {
            return None;
        }
        if let Some(values) = (values as &dyn Any).downcast_ref::<[Fp; 8]>() {
            let powers = ifma::pow_t8(values);
            let roots = fp::sqrt_with_t_power8(values, &powers);
            return (&roots as &dyn Any)
                .downcast_ref::<[subtle::CtOption<F>; 8]>()
                .copied();
        }
        if let Some(values) = (values as &dyn Any).downcast_ref::<[Fq; 8]>() {
            let powers = ifma::pow_t8(values);
            let roots = fq::sqrt_with_t_power8(values, &powers);
            return (&roots as &dyn Any)
                .downcast_ref::<[subtle::CtOption<F>; 8]>()
                .copied();
        }
    }
    let _ = values;
    None
}

/// Reduces affine buckets in packed scratch, leaving the source unchanged.
///
/// Returns `None` on unsupported targets or a zero chord denominator. The
/// caller can then retry its unchanged inputs with complete formulas.
#[cfg(all(feature = "glv", any(test, feature = "multicore", feature = "orbits")))]
pub(crate) fn try_reduce_affine_buckets_packed<F: ff::Field>(
    point_count: usize,
    offsets: &[usize],
    point_at: impl Fn(usize) -> (F, F),
) -> Option<alloc::vec::Vec<Option<(F, F)>>> {
    #[cfg(all(
        feature = "x86_64-asm",
        target_arch = "x86_64",
        target_pointer_width = "64"
    ))]
    if ifma_available_for::<F>() {
        return ifma::reduce_affine_buckets(point_count, offsets, point_at);
    }
    let _ = (point_count, offsets, point_at);
    None
}

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
    any(target_family = "unix", target_os = "none"),
    target_pointer_width = "64",
    target_endian = "little"
))]
mod aarch64_asm;

// Keep the build-selected x86-64 inline-assembly exception behind the same
// private boundary.
#[allow(unsafe_code)]
#[cfg(all(
    pasta_curves_x86_64_asm,
    target_arch = "x86_64",
    target_pointer_width = "64"
))]
mod x86_64_asm;

pub use fp::*;
pub use fq::*;

#[cfg(all(test, feature = "glv"))]
mod ifma_tests {
    use super::*;
    use ff::Field;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    fn check_batches<F: Field + From<u64>>() {
        let mut rng = XorShiftRng::from_seed([0xA5; 16]);
        let boundaries = [F::ZERO, F::ONE, -F::ONE, F::from(2), -F::from(2)];
        for iteration in 0..1024 {
            let lhs = core::array::from_fn(|lane| {
                if iteration < boundaries.len() {
                    boundaries[(iteration + lane) % boundaries.len()]
                } else {
                    F::random(&mut rng)
                }
            });
            let rhs = core::array::from_fn(|lane| {
                if iteration < boundaries.len() {
                    boundaries[(iteration * 2 + lane) % boundaries.len()]
                } else {
                    F::random(&mut rng)
                }
            });
            let expected = core::array::from_fn(|lane| lhs[lane] * rhs[lane]);
            let mut actual = lhs;
            let available = try_mul_assign8(&mut actual, &rhs);
            assert_eq!(available, ifma_available_for::<F>());
            assert_eq!(actual, if available { expected } else { lhs });

            let expected = lhs.map(|value| value.square());
            let mut actual = lhs;
            let available = try_square8(&mut actual);
            assert_eq!(available, ifma_available_for::<F>());
            assert_eq!(actual, if available { expected } else { lhs });
        }
    }

    #[test]
    fn ifma_fp_batches_match_scalar_or_leave_inputs_unchanged() {
        check_batches::<Fp>();
    }

    #[test]
    fn ifma_fq_batches_match_scalar_or_leave_inputs_unchanged() {
        check_batches::<Fq>();
    }
}

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
