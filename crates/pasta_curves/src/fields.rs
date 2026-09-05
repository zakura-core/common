//! This module contains implementations for the two finite fields of the Pallas
//! and Vesta curves.

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

// Batched AVX-512 IFMA arithmetic, contained within a private module whose
// public interface consists only of safe wrappers.
#[allow(unsafe_code)]
#[cfg(all(target_arch = "x86_64", feature = "ifma"))]
mod ifma;

#[cfg(all(target_arch = "x86_64", feature = "ifma"))]
const FP_RADIX52: ifma::Radix52Modulus = ifma::Radix52Modulus {
    p52: [
        0xd30ed00000001,
        0xfc094cf91b992,
        0x224698,
        0x0,
        0x400000000000,
    ],
    nprime: 0xd30ecffffffff,
};

#[cfg(all(target_arch = "x86_64", feature = "ifma"))]
const FQ_RADIX52: ifma::Radix52Modulus = ifma::Radix52Modulus {
    p52: [
        0x6eb2100000001,
        0xfc0994a8dd8c4,
        0x224698,
        0x0,
        0x400000000000,
    ],
    nprime: 0x6eb20ffffffff,
};

macro_rules! batch_slice_ops {
    ($field:ident, $modulus:ident, $mul_name:ident, $sqr_name:ident, $scale_name:ident) => {
        /// Elementwise in-place product: `lhs[i] *= rhs[i]`.
        ///
        /// Uses batched AVX-512 IFMA multiplication when available, falling
        /// back to scalar multiplication otherwise.
        pub fn $mul_name(lhs: &mut [$field], rhs: &[$field]) {
            assert!(rhs.len() >= lhs.len());
            #[allow(unused_mut)]
            let mut done = 0;
            #[cfg(all(target_arch = "x86_64", feature = "ifma"))]
            if ifma::ifma_available() {
                // SAFETY: the field type is a `#[repr(transparent)]` wrapper
                // around `[u64; 4]` canonical Montgomery residues, and the
                // required CPU features were just detected.
                #[allow(unsafe_code)]
                {
                    done = unsafe {
                        ifma::mul_slice_raw(
                            lhs.as_mut_ptr() as *mut u64,
                            rhs.as_ptr() as *const u64,
                            lhs.len(),
                            &$modulus,
                        )
                    };
                }
            }
            for (l, r) in lhs[done..].iter_mut().zip(rhs[done..].iter()) {
                *l *= *r;
            }
        }

        /// Elementwise in-place squaring: `x[i] = x[i]^2`.
        ///
        /// Uses batched AVX-512 IFMA multiplication when available, falling
        /// back to scalar squaring otherwise.
        pub fn $sqr_name(x: &mut [$field]) {
            #[allow(unused_mut)]
            let mut done = 0;
            #[cfg(all(target_arch = "x86_64", feature = "ifma"))]
            if ifma::ifma_available() {
                // SAFETY: as in the multiplication wrapper above.
                #[allow(unsafe_code)]
                {
                    done = unsafe {
                        ifma::sqr_slice_raw(x.as_mut_ptr() as *mut u64, x.len(), &$modulus)
                    };
                }
            }
            for v in x[done..].iter_mut() {
                *v = v.square();
            }
        }

        /// Elementwise in-place scaling by one factor: `x[i] *= k`.
        ///
        /// Uses batched AVX-512 IFMA multiplication when available, falling
        /// back to scalar multiplication otherwise.
        pub fn $scale_name(x: &mut [$field], k: &$field) {
            #[allow(unused_mut)]
            let mut done = 0;
            #[cfg(all(target_arch = "x86_64", feature = "ifma"))]
            if ifma::ifma_available() {
                // SAFETY: as in the multiplication wrapper above.
                #[allow(unsafe_code)]
                {
                    done = unsafe {
                        ifma::scale_slice_raw(
                            x.as_mut_ptr() as *mut u64,
                            x.len(),
                            &*(k as *const $field as *const [u64; 4]),
                            &$modulus,
                        )
                    };
                }
            }
            for v in x[done..].iter_mut() {
                *v *= *k;
            }
        }
    };
}

batch_slice_ops!(Fp, FP_RADIX52, fp_mul_slice, fp_sqr_slice, fp_scale_slice);
batch_slice_ops!(Fq, FQ_RADIX52, fq_mul_slice, fq_sqr_slice, fq_scale_slice);

#[cfg(feature = "deferred")]
macro_rules! inner_product_ops {
    ($field:ident, $name:ident) => {
        /// Deferred-reduction inner product `sum_i a[i] * b[i]`.
        ///
        /// Uses the batched AVX-512 IFMA dot-product kernel when available,
        /// falling back to the scalar deferred accumulator otherwise.
        #[cfg_attr(docsrs, doc(cfg(feature = "deferred")))]
        pub fn $name(a: &[$field], b: &[$field]) -> $field {
            use crate::deferred::DeferredField;
            let len = a.len().min(b.len());
            let mut acc = <$field as DeferredField>::Accumulator::default();
            #[allow(unused_mut)]
            let mut done = 0;
            #[cfg(all(target_arch = "x86_64", feature = "ifma"))]
            if ifma::ifma_available() {
                let mut sum = [0u64; 9];
                // SAFETY: the field type is a `#[repr(transparent)]` wrapper
                // around `[u64; 4]` residues, and the required CPU features
                // were just detected.
                #[allow(unsafe_code)]
                {
                    done = unsafe {
                        ifma::dot_slice_raw(
                            a.as_ptr() as *const u64,
                            b.as_ptr() as *const u64,
                            len,
                            &mut sum,
                        )
                    };
                }
                let mut limbs = [0u64; 8];
                limbs.copy_from_slice(&sum[..8]);
                acc = crate::deferred::Product::from_raw(limbs, sum[8]);
            }
            for (x, y) in a[done..len].iter().zip(&b[done..len]) {
                $field::mul_accumulate(&mut acc, x, y);
            }
            <$field as DeferredField>::reduce(acc)
        }
    };
}

#[cfg(feature = "deferred")]
inner_product_ops!(Fp, fp_inner_product);
#[cfg(feature = "deferred")]
inner_product_ops!(Fq, fq_inner_product);

#[cfg(test)]
mod batch_tests {
    use super::*;
    use ff::Field;
    use rand_xorshift::XorShiftRng;

    macro_rules! batch_test {
        ($field:ident, $mul_name:ident, $sqr_name:ident, $scale_name:ident, $test_name:ident) => {
            #[test]
            fn $test_name() {
                use rand::SeedableRng;
                let mut rng = XorShiftRng::from_seed([9; 16]);
                // Cover both the vector body and the scalar tail.
                for len in [0usize, 1, 7, 8, 9, 64, 100] {
                    let mut lhs: std::vec::Vec<$field> =
                        (0..len).map(|_| $field::random(&mut rng)).collect();
                    let rhs: std::vec::Vec<$field> =
                        (0..len).map(|_| $field::random(&mut rng)).collect();
                    let want: std::vec::Vec<$field> =
                        lhs.iter().zip(rhs.iter()).map(|(a, b)| a * b).collect();
                    $mul_name(&mut lhs, &rhs);
                    assert_eq!(lhs, want);

                    let mut x: std::vec::Vec<$field> =
                        (0..len).map(|_| $field::random(&mut rng)).collect();
                    let want: std::vec::Vec<$field> = x.iter().map(|a| a.square()).collect();
                    $sqr_name(&mut x);
                    assert_eq!(x, want);

                    let mut x: std::vec::Vec<$field> =
                        (0..len).map(|_| $field::random(&mut rng)).collect();
                    let k = $field::random(&mut rng);
                    let want: std::vec::Vec<$field> = x.iter().map(|a| a * k).collect();
                    $scale_name(&mut x, &k);
                    assert_eq!(x, want);
                }
            }
        };
    }

    batch_test!(
        Fp,
        fp_mul_slice,
        fp_sqr_slice,
        fp_scale_slice,
        fp_batch_matches_scalar
    );
    batch_test!(
        Fq,
        fq_mul_slice,
        fq_sqr_slice,
        fq_scale_slice,
        fq_batch_matches_scalar
    );

    #[cfg(feature = "deferred")]
    macro_rules! inner_product_test {
        ($field:ident, $name:ident, $test_name:ident) => {
            #[test]
            fn $test_name() {
                use rand::SeedableRng;
                let mut rng = XorShiftRng::from_seed([11; 16]);
                // Cover the vector body, the scalar tail, and lengths that
                // span multiple carry-normalization blocks.
                for len in [0usize, 1, 7, 8, 9, 64, 100, 2048, 2049, 5000] {
                    let a: std::vec::Vec<$field> =
                        (0..len).map(|_| $field::random(&mut rng)).collect();
                    let b: std::vec::Vec<$field> =
                        (0..len).map(|_| $field::random(&mut rng)).collect();
                    let want: $field = a.iter().zip(b.iter()).map(|(x, y)| x * y).sum();
                    assert_eq!($name(&a, &b), want, "mismatch at len={len}");
                }
            }
        };
    }

    #[cfg(feature = "deferred")]
    inner_product_test!(Fp, fp_inner_product, fp_inner_product_matches_scalar);
    #[cfg(feature = "deferred")]
    inner_product_test!(Fq, fq_inner_product, fq_inner_product_matches_scalar);
}
// Keep the assembly FFI exception contained within a private module whose
// public interface consists only of safe wrappers.
#[allow(unsafe_code)]
#[cfg(all(
    feature = "aarch64-asm",
    target_arch = "aarch64",
    target_vendor = "apple"
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
