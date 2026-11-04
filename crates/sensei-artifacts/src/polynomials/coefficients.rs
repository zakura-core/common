//! Generators for the fixed- and sigma-polynomial coefficient artifacts.
//!
//! The dense coefficient matrices are not raw inputs: they derive entirely
//! from the compact sources — the Sinsemilla generators, the sparse
//! row-tuple data, the declarative column layout, and the permutation map —
//! through the same `sensei-shared` reconstruction functions the prover runs
//! at load, followed by one inverse transform per column. The prover's
//! cross-check test re-derives both matrices from its own embedded data with
//! its optimized transforms and asserts exact equality, so the two FFT
//! implementations validate each other end to end.

use bento::bytes_of_slice;
use sensei_shared::{FIXED_COLUMNS, N, PERMUTATION_COLUMN_COUNT};
use udon::field::Fp;

use crate::{Error, context::Context, domain, normalize_stored_montgomery};

/// Interpolates each column once and reduces it for deterministic storage.
pub(crate) fn interpolate(mut columns: Vec<[Fp; N]>) -> Result<Vec<[Fp; N]>, Error> {
    let (root_inverse, size_inverse) = domain::inverse_domain(N)?;
    for column in &mut columns {
        udon::fft::reference::inverse_transform(column, &root_inverse, &size_inverse);
        normalize_stored_montgomery(column);
    }
    Ok(columns)
}

fn coefficient_bytes(columns: &[[Fp; N]], expected: usize) -> Result<Vec<u8>, Error> {
    if columns.len() != expected {
        return Err(Error::new("coefficient matrix has unexpected dimensions"));
    }
    Ok(bytes_of_slice(columns).to_vec())
}

/// Generates the exact bytes of the fixed-coefficients artifact.
pub(crate) fn generate_fixed(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    coefficient_bytes(context.fixed_coefficients()?, FIXED_COLUMNS)
}

/// Generates the exact bytes of the sigma-coefficients artifact.
pub(crate) fn generate_sigma(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    coefficient_bytes(context.sigma_coefficients()?, PERMUTATION_COLUMN_COUNT)
}
