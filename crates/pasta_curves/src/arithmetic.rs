//! This module provides common utilities, traits and structures for group and
//! field arithmetic.
//!
//! This module is temporary, and the extension traits defined here are expected to be
//! upstreamed into the `ff` and `group` crates after some refactoring.

mod curves;
mod fields;

pub use curves::*;
pub(crate) use fields::*;

/// Multiplies an [`Fp`](crate::Fp) element by `2^-exponent`.
///
/// This is an internal cross-crate bridge for `halo2_proofs`.
#[doc(hidden)]
#[inline]
pub fn mul_fp_by_inverse_power_of_two(value: &crate::Fp, exponent: u32) -> crate::Fp {
    value.mul_by_inverse_power_of_two(exponent)
}

/// Multiplies an [`Fq`](crate::Fq) element by `2^-exponent`.
///
/// This is an internal cross-crate bridge for `halo2_proofs`.
#[doc(hidden)]
#[inline]
pub fn mul_fq_by_inverse_power_of_two(value: &crate::Fq, exponent: u32) -> crate::Fq {
    value.mul_by_inverse_power_of_two(exponent)
}

/// Squares an [`Fp`](crate::Fp) element `count` times.
///
/// This is an internal cross-crate bridge for Halo 2 and Orchard.
#[doc(hidden)]
#[inline]
pub fn square_fp_n(value: &crate::Fp, count: u32) -> crate::Fp {
    if count == 0 {
        *value
    } else {
        SqrtTableHelpers::sqr_n(value, count)
    }
}

/// Squares an [`Fq`](crate::Fq) element `count` times.
///
/// This is an internal cross-crate bridge for Halo 2 and Orchard.
#[doc(hidden)]
#[inline]
pub fn square_fq_n(value: &crate::Fq, count: u32) -> crate::Fq {
    if count == 0 {
        *value
    } else {
        SqrtTableHelpers::sqr_n(value, count)
    }
}

/// The internal Montgomery-form limbs (`a * 2^256 mod p`, little-endian
/// `u64`s) of an [`Fp`](crate::Fp) element.
///
/// This is an internal cross-crate bridge for MSM accelerator backends,
/// which keep their own copy of the Montgomery representation and would
/// otherwise pay a full reduction and re-multiplication per coordinate.
#[doc(hidden)]
#[inline]
pub fn fp_montgomery_limbs(value: &crate::Fp) -> [u64; 4] {
    value.0
}

/// The internal Montgomery-form limbs (`a * 2^256 mod q`, little-endian
/// `u64`s) of an [`Fq`](crate::Fq) element.
///
/// This is an internal cross-crate bridge for MSM accelerator backends;
/// see [`fp_montgomery_limbs`].
#[doc(hidden)]
#[inline]
pub fn fq_montgomery_limbs(value: &crate::Fq) -> [u64; 4] {
    value.0
}

#[cfg(test)]
mod tests {
    use super::{square_fp_n, square_fq_n};
    use crate::{Fp, Fq};

    #[test]
    fn repeated_squaring_bridges_match_field_squaring() {
        let fp = Fp::from(0x9e37_79b9_7f4a_7c15);
        let fq = Fq::from(0x0123_4567_89ab_cdef);

        for count in [0, 1, 2, 11, 64] {
            let expected_fp = (0..count).fold(fp, |value, _| value.square());
            let expected_fq = (0..count).fold(fq, |value, _| value.square());
            assert_eq!(square_fp_n(&fp, count), expected_fp);
            assert_eq!(square_fq_n(&fq, count), expected_fq);
        }
    }
}
