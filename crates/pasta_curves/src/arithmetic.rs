//! This module provides common utilities, traits and structures for group and
//! field arithmetic.
//!
//! This module is temporary, and the extension traits defined here are expected to be
//! upstreamed into the `ff` and `group` crates after some refactoring.

#[cfg(all(feature = "sqrt-table", feature = "glv", pasta_curves_avx2))]
pub(crate) mod avx2_chord;
#[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
pub(crate) mod avx2_fft;
#[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
pub(crate) mod avx2_sqrt;
mod curves;
mod fields;
#[cfg(feature = "alloc")]
mod multiexp;

pub use curves::*;
pub(crate) use fields::*;
#[cfg(feature = "glv")]
pub(crate) use multiexp::default_multiexp_window_bits;
// The timing grid in `glv` compares against the generic MSM directly.
#[cfg(all(test, feature = "multicore"))]
pub(crate) use multiexp::signed_booth_multiexp;
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub use multiexp::{best_multiexp_vartime, best_multiexp_vartime_with_parallelism};

/// Radix-2^29 twiddle tables for the AVX2 FFT butterflies of one transform
/// length, or nothing when the kernel is unavailable.
///
/// This is an internal cross-crate bridge for `halo2_proofs`.
#[doc(hidden)]
#[derive(Clone, Debug, Default)]
pub struct FftTwiddles29 {
    #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
    inner: Option<avx2_fft::Twiddles>,
}

impl FftTwiddles29 {
    /// Builds tables from `twiddles[j] = w^j` for `j < n / 2`, if `F` is a
    /// Pasta field and this build runs the AVX2 kernel.
    #[allow(unsafe_code, unused_variables)]
    pub fn new<F: 'static>(twiddles: &[F]) -> Self {
        #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
        {
            use core::any::TypeId;
            let inner = if TypeId::of::<F>() == TypeId::of::<crate::Fp>() {
                // SAFETY: `F` is `Fp`.
                let t = unsafe { &*(twiddles as *const [F] as *const [crate::Fp]) };
                avx2_fft::twiddles_for(t)
            } else if TypeId::of::<F>() == TypeId::of::<crate::Fq>() {
                // SAFETY: `F` is `Fq`.
                let t = unsafe { &*(twiddles as *const [F] as *const [crate::Fq]) };
                avx2_fft::twiddles_for(t)
            } else {
                None
            };
            FftTwiddles29 { inner }
        }
        #[cfg(not(all(feature = "sqrt-table", pasta_curves_avx2)))]
        FftTwiddles29 {}
    }
}

/// Reusable buffer for [`fft_butterflies_avx2`].
///
/// This is an internal cross-crate bridge for `halo2_proofs`.
#[doc(hidden)]
#[derive(Debug, Default)]
pub struct FftScratch29 {
    #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
    inner: avx2_fft::Scratch,
}

/// Runs the radix-2 decimation-in-time butterflies of a node at `level`
/// (length `values.len()`, transform length `values.len() << level`) whose
/// sub-nodes of length `completed` are already transformed, in AVX2.
///
/// Returns `false`, leaving `values` untouched, when the kernel does not apply
/// (not a Pasta field, no AVX2 in this build, tables for another length, or a
/// node shorter than 16); the caller then runs its scalar butterflies.
///
/// This is an internal cross-crate bridge for `halo2_proofs`.
#[doc(hidden)]
#[allow(unsafe_code, unused_variables)]
pub fn fft_butterflies_avx2<F: 'static>(
    values: &mut [F],
    completed: usize,
    level: usize,
    twiddles: &FftTwiddles29,
    scratch: &mut FftScratch29,
) -> bool {
    #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
    {
        use avx2_fft::Avx2FftField;
        use core::any::TypeId;
        let Some(tw) = &twiddles.inner else {
            return false;
        };
        if TypeId::of::<F>() == TypeId::of::<crate::Fp>() {
            // SAFETY: `F` is `Fp`.
            let v = unsafe { &mut *(values as *mut [F] as *mut [crate::Fp]) };
            return crate::Fp::fft_butterflies(v, completed, level, tw, &mut scratch.inner);
        }
        if TypeId::of::<F>() == TypeId::of::<crate::Fq>() {
            // SAFETY: `F` is `Fq`.
            let v = unsafe { &mut *(values as *mut [F] as *mut [crate::Fq]) };
            return crate::Fq::fft_butterflies(v, completed, level, tw, &mut scratch.inner);
        }
    }
    false
}

/// The forward FFT of `values` (`2^log_n` coefficients) zero-padded to the
/// transform length of `twiddles`, in AVX2, matching `halo2_proofs`'
/// `fft_zero_padded_with_twiddles`. On success `values` holds the
/// evaluations; returns `false`, leaving `values` untouched, when the kernel
/// does not apply.
///
/// This is an internal cross-crate bridge for `halo2_proofs`.
#[cfg(feature = "alloc")]
#[doc(hidden)]
// The coefficients are resized in place to the transform length.
#[allow(unsafe_code, unused_variables, clippy::ptr_arg)]
pub fn fft_zero_padded_avx2<F: ff::Field>(
    values: &mut alloc::vec::Vec<F>,
    log_n: u32,
    twiddles: &FftTwiddles29,
    scratch: &mut FftScratch29,
) -> bool {
    #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
    {
        use avx2_fft::Avx2FftField;
        use core::any::TypeId;
        let Some(tw) = &twiddles.inner else {
            return false;
        };
        if values.len() != 1 << log_n || !avx2_fft::zero_padded_applies(log_n, tw) {
            return false;
        }
        if TypeId::of::<F>() == TypeId::of::<crate::Fp>() {
            values.resize(tw.len(), F::ZERO);
            // SAFETY: `F` is `Fp`.
            let v = unsafe { &mut *(values.as_mut_slice() as *mut [F] as *mut [crate::Fp]) };
            crate::Fp::fft_zero_padded(v, log_n, tw, &mut scratch.inner);
            return true;
        }
        if TypeId::of::<F>() == TypeId::of::<crate::Fq>() {
            values.resize(tw.len(), F::ZERO);
            // SAFETY: `F` is `Fq`.
            let v = unsafe { &mut *(values.as_mut_slice() as *mut [F] as *mut [crate::Fq]) };
            crate::Fq::fft_zero_padded(v, log_n, tw, &mut scratch.inner);
            return true;
        }
    }
    false
}

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
