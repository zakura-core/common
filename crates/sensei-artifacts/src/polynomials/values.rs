//! Shared reconstruction of fixed and sigma columns on the base domain.
//!
//! Both coefficient and coset encoders start here. Every returned column
//! has `N` evaluations in circuit-row order; the enclosing vector follows
//! fixed-column or permutation-column order from `sensei-shared`.

use sensei_shared::{K, N, fixed_columns::build_fixed_values, permutation::sigma_lagrange_values};
use udon::field::Fp;

use crate::{Error, context::Context};

/// The Lagrange forms of the 29 fixed columns, reconstructed from the raw
/// Sinsemilla table and the source-derived sparse rows.
pub(crate) fn fixed_columns(context: &Context<'_>) -> Result<Vec<[Fp; N]>, Error> {
    let sinsemilla = context.sinsemilla_generators()?;
    let rows = context.sparse_rows()?;
    Ok(build_fixed_values(
        sinsemilla
            .try_into()
            .expect("decode_points checked the generator count"),
        &rows.tuples,
        &rows.assignments,
    ))
}

/// The permutation columns evaluated at each base-domain row.
pub(crate) fn sigma_columns(context: &Context<'_>) -> Result<Vec<[Fp; N]>, Error> {
    let mapping = context.sigma_map()?;
    let omega = <Fp>::root_of_unity(K)
        .ok_or_else(|| Error::new(format!("no 2^{K} root of unity for the base domain")))?;
    let (values, _identities) = sigma_lagrange_values(
        mapping
            .try_into()
            .expect("sigma_map checked the column count"),
        &omega,
        &<Fp>::DELTA,
    );
    Ok(values)
}
