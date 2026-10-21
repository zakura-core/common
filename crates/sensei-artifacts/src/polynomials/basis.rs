//! Lagrange basis artifacts for instance interpolation and boundary checks.
//!
//! A unit vector on base-domain rows defines a Lagrange polynomial. Instance
//! bases store its coefficients, transposed by degree. Boundary artifacts
//! store extended-coset evaluations of `l_0`, `l_last`, and the active mask.

use bento::bytes_of_slice;
use sensei_shared::{EXTENDED_N, INSTANCE_VALUE_COUNT, N, USABLE_ROWS_END};
use udon::field::Fp;

use crate::{Error, context::Context, domain, normalize_stored_montgomery};

use super::cosets::extended_coset_columns;

/// Generates the exact bytes of the instance-bases artifact: the transposed
/// coefficient bases of the Lagrange polynomials at the populated instance
/// rows, one output row per coefficient degree — the values the prover
/// derives at load when the dial is off, produced directly from
/// `L_j(X) = N⁻¹ Σ_k (ω⁻ʲ)^k X^k`.
pub(crate) fn generate_instance_bases(_context: &Context<'_>) -> Result<Vec<u8>, Error> {
    let (root_inverse, size_inverse) = domain::inverse_domain(N)?;
    let mut rows = vec![[<Fp>::ZERO; INSTANCE_VALUE_COUNT]; N];
    let mut step = <Fp>::ONE;
    for basis in 0..INSTANCE_VALUE_COUNT {
        let mut coefficient = size_inverse;
        for row in &mut rows {
            row[basis] = coefficient.reduce().into_loose();
            coefficient = coefficient.mul(&step);
        }
        step = step.mul(&root_inverse);
    }
    Ok(bytes_of_slice(&rows).to_vec())
}

/// Generates the exact bytes of the boundaries artifact: the extended-coset
/// boundary polynomials `l_0` (row 0) and `l_last` (row `USABLE_ROWS_END`)
/// and the active-row mask `1 − (l_last + l_blind)`, in that order — the
/// values the prover transforms at load when the dial is off. The blinding
/// tail is `USABLE_ROWS_END + 1..N`; row `USABLE_ROWS_END` itself belongs
/// to `l_last`, and usable rows are `0..USABLE_ROWS_END`.
pub(crate) fn generate_boundaries(_context: &Context<'_>) -> Result<Vec<u8>, Error> {
    let boundary = |rows: &[usize]| -> Result<Vec<Fp>, Error> {
        let mut values = vec![<Fp>::ZERO; N];
        for &row in rows {
            values[row] = <Fp>::ONE;
        }
        Ok(extended_coset_columns(vec![values])?.remove(0))
    };
    let l_0 = boundary(&[0])?;
    let l_last = boundary(&[USABLE_ROWS_END])?;
    let blind_rows = (USABLE_ROWS_END + 1..N).collect::<Vec<_>>();
    let mut active_rows = boundary(&blind_rows)?;
    for (active, last) in active_rows.iter_mut().zip(&l_last) {
        *active = <Fp>::ONE.sub(&last.add(active));
    }
    let mut bytes = Vec::with_capacity(3 * EXTENDED_N * size_of::<Fp>());
    for mut column in [l_0, l_last, active_rows] {
        normalize_stored_montgomery(&mut column);
        bytes.extend_from_slice(bytes_of_slice(&column));
    }
    Ok(bytes)
}
