//! Generators for the extended-coset artifacts (optional embed dials).
//!
//! The extended cosets are pure functions of the same compact sources the
//! coefficient artifacts derive from: reconstruct the Lagrange columns,
//! interpolate (one inverse transform per column), zero-pad to the extended
//! domain, distribute the coset powers, and run the forward transform. The
//! textbook transforms here reproduce the prover's optimized broadcast-pruned
//! expansion's field values, which the
//! prover's embedded-vs-derived tests and canonical-content digest pin. The
//! sibling `selectors` module evaluates the shared `sensei-shared` selector
//! recipe over these fixed cosets, exactly as the prover's load-time fill.

use bento::bytes_of;
use sensei_shared::{EXTENDED_K, EXTENDED_N, FIXED_COLUMNS, N, PERMUTATION_COLUMN_COUNT};
use udon::field::Fp;

use crate::{Error, context::Context, domain, normalize_stored_montgomery};

/// Expands Lagrange-evaluation columns to their extended-coset forms:
/// interpolate at the base size, zero-pad, distribute `ζ^i` over the
/// coefficients, and evaluate over the extended domain.
pub(super) fn extended_coset_columns(mut columns: Vec<Vec<Fp>>) -> Result<Vec<Vec<Fp>>, Error> {
    let (base_root_inverse, base_size_inverse) = domain::inverse_domain(N)?;
    for column in &mut columns {
        if column.len() != N {
            return Err(Error::new("coset expansion requires base-size columns"));
        }
        udon::fft::reference::inverse_transform(column, &base_root_inverse, &base_size_inverse);
    }
    expand_columns(columns)
}

/// Expands already interpolated columns, preserving shared base-domain work.
pub(crate) fn expand_coefficients<C: AsRef<[Fp]>>(columns: &[C]) -> Result<Vec<Vec<Fp>>, Error> {
    expand_columns(columns.iter().map(|column| column.as_ref().to_vec()))
}

fn expand_columns(columns: impl IntoIterator<Item = Vec<Fp>>) -> Result<Vec<Vec<Fp>>, Error> {
    let extended_root = <Fp>::root_of_unity(EXTENDED_K)
        .ok_or_else(|| Error::new(format!("no 2^{EXTENDED_K} root of unity")))?;
    let zeta = <Fp>::ZETA;
    let zeta_squared = zeta.square();
    // The coset shift has order three, so coefficient scales repeat.
    let scales = [<Fp>::ONE, zeta, zeta_squared];

    columns
        .into_iter()
        .map(|mut column| {
            if column.len() != N {
                return Err(Error::new("coset expansion requires base-size columns"));
            }
            for (index, coefficient) in column.iter_mut().enumerate() {
                *coefficient = coefficient.mul(&scales[index % 3]);
            }
            // Padding stays zero under the coset shift; scale only the N
            // populated coefficients before extending the buffer.
            column.resize(EXTENDED_N, <Fp>::ZERO);
            udon::fft::reference::transform(&mut column, &extended_root);
            normalize_stored_montgomery(&mut column);
            Ok(column)
        })
        .collect()
}

/// Serializes each column in residue-major order, retaining dense context data.
///
/// Context columns remain in natural extended-row order. With `R = EXTENDED_N / N`,
/// the encoder writes one column at a time, then residues `t` in `0..R`, then
/// tile-local indices `k` in `0..N`: natural row `t + R*k` becomes element
/// `t*N + k` of the encoded column. This matches the runtime
/// [`CosetTiles` indexing contract](../../../zakura_sensei/native/polynomial/struct.CosetTiles.html)
/// while the reference transforms above remain independent of its expansion.
fn coset_bytes(cosets: &[Vec<Fp>], expected: usize) -> Result<Vec<u8>, Error> {
    if cosets.len() != expected {
        return Err(Error::new("coset matrix has unexpected dimensions"));
    }
    let mut bytes = Vec::with_capacity(expected * EXTENDED_N * size_of::<Fp>());
    for column in cosets {
        if column.len() != EXTENDED_N {
            return Err(Error::new("coset column has unexpected dimensions"));
        }
        for residue in 0..EXTENDED_N / N {
            for k in 0..N {
                bytes.extend_from_slice(bytes_of(&column[residue + k * (EXTENDED_N / N)]));
            }
        }
    }
    Ok(bytes)
}

/// Generates the exact bytes of the fixed-cosets artifact.
pub(crate) fn generate_fixed(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    coset_bytes(context.fixed_cosets()?, FIXED_COLUMNS)
}

/// Generates the exact bytes of the sigma-cosets artifact.
pub(crate) fn generate_sigma(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    coset_bytes(context.sigma_cosets()?, PERMUTATION_COLUMN_COUNT)
}
