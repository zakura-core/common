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
