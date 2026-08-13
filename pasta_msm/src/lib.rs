//! Caller-thread, variable-time multiscalar multiplication for the Pasta
//! curves.
//!
//! This crate is an attributed, CPU-only fork of Supranational's
//! `pasta-msm`, Semolina, and Sppark projects. [`pallas_vartime`] and
//! [`vesta_vartime`] provide no constant-time guarantee and should be used
//! only where variable-time behavior is acceptable, such as Halo proof
//! generation.

mod ffi;

use pasta_curves::{pallas, vesta};

/// Computes a variable-time Pallas multiscalar multiplication.
///
/// # Panics
///
/// Panics if `points` and `scalars` have different lengths, or if the native
/// backend cannot complete the operation.
pub fn pallas_vartime(points: &[pallas::Affine], scalars: &[pallas::Scalar]) -> pallas::Point {
    assert_eq!(points.len(), scalars.len(), "length mismatch");
    if points.is_empty() {
        return pallas::Point::default();
    }

    // SAFETY: `pasta_curves` is compiled with `repr-c`; `ffi` checks the
    // corresponding sizes and alignments at compile time. The slices have
    // equal, non-zero lengths and remain alive for the duration of the call.
    unsafe { ffi::pallas_vartime(points, scalars) }
}

/// Computes a variable-time Vesta multiscalar multiplication.
///
/// # Panics
///
/// Panics if `points` and `scalars` have different lengths, or if the native
/// backend cannot complete the operation.
pub fn vesta_vartime(points: &[vesta::Affine], scalars: &[vesta::Scalar]) -> vesta::Point {
    assert_eq!(points.len(), scalars.len(), "length mismatch");
    if points.is_empty() {
        return vesta::Point::default();
    }

    // SAFETY: `pasta_curves` is compiled with `repr-c`; `ffi` checks the
    // corresponding sizes and alignments at compile time. The slices have
    // equal, non-zero lengths and remain alive for the duration of the call.
    unsafe { ffi::vesta_vartime(points, scalars) }
}
