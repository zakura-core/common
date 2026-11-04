//! The shared query and evaluation layer below target preparation, preflight,
//! and proving: validated query resolution over both domains, the explicit
//! rotation rules, and generated expression evaluation.
//!
//! Row addressing is modular over the domain: the base domain has `N` rows
//! and a rotation of `r` moves `r` rows; the extended coset has `EXTENDED_N`
//! rows and the same query rotation moves [`EXTENDED_ROTATION_STRIDE`] rows,
//! because the coset interleaves `EXTENDED_N / N` points between consecutive
//! base points. Both domains are powers of two, so wrapping arithmetic under
//! a mask is exact modular addition for negative rotations too. Nothing here
//! orchestrates commitments or the transcript; the specialized row kernels
//! that need to stay inlined into their callers remain beside them in the
//! prover.

use crate::Error;
use alloc::vec::Vec;

use super::{
    field::Fp,
    target::{EXTENDED_N, FixedTarget, N, Query},
};

#[cfg(test)]
use super::{
    generated_expressions::{self, QueryKind},
    invariant::{self, Invariant},
};

/// Extended-coset rows per unit of query rotation.
pub(super) const EXTENDED_ROTATION_STRIDE: usize = EXTENDED_N / N;

pub(super) fn rotated_query_point(target: &FixedTarget, x: &Fp, rotation: i32) -> Fp {
    if rotation >= 0 {
        rotated_evaluation_point(x, target.domain().omega(), rotation as usize)
    } else {
        rotated_evaluation_point(
            x,
            target.domain().omega_inverse(),
            rotation.unsigned_abs() as usize,
        )
    }
}

pub(super) fn rotated_evaluation_point(x: &Fp, omega: &Fp, rotation: usize) -> Fp {
    x.mul(&omega.pow_u64(rotation as u64))
}

/// The extended rows a gate query frame reads at rotations −1, 0, +1
/// (the `−8`/`+8` neighbours in the extended domain, wrapping). The fold
/// now gathers its rows in blocks; the tests' dense reference still
/// reads through this.
#[cfg(test)]
pub(super) fn gate_query_rows(row: usize) -> [usize; 3] {
    const EXTENDED_MASK: usize = EXTENDED_N - 1;
    debug_assert!(row < EXTENDED_N);
    [
        row.wrapping_sub(EXTENDED_ROTATION_STRIDE) & EXTENDED_MASK,
        row,
        (row + EXTENDED_ROTATION_STRIDE) & EXTENDED_MASK,
    ]
}

/// Every query's column exists among `count` extended-coset records (each of
/// which has the extended length by construction).
pub(super) fn coset_query_columns_exist(queries: &[Query], count: usize) -> bool {
    queries.iter().all(|query| query.column < count)
}

#[cfg(test)]
pub(super) fn evaluate_expression_coset_row<F: core::ops::Index<usize, Output = Fp>>(
    expression: usize,
    target: &FixedTarget,
    advice: &[Vec<Fp>],
    fixed: &[F],
    instance: &[Vec<Fp>],
    row: usize,
) -> Result<Fp, Error> {
    generated_expressions::evaluate(
        &generated_expressions::program_trees(expression)?.tree,
        &mut |kind, index| match kind {
            QueryKind::Fixed => query_coset_value(target.queries().fixed(), index, fixed, row),
            QueryKind::Advice => query_coset_value(target.queries().advice(), index, advice, row),
            QueryKind::Instance => {
                query_coset_value(target.queries().instance(), index, instance, row)
            }
        },
    )
}
#[cfg(test)]
pub(super) fn query_coset_value<C: core::ops::Index<usize, Output = Fp>>(
    queries: &[Query],
    query_index: usize,
    columns: &[C],
    row: usize,
) -> Result<Fp, Error> {
    let query = queries
        .get(query_index)
        .ok_or_else(|| invariant::failed(Invariant::MissingQuery))?;
    let column = columns
        .get(query.column)
        .ok_or_else(|| invariant::failed(Invariant::ColumnShape))?;
    Ok(column[rotated_extended_row(row, query.rotation)])
}

pub(super) fn rotated_extended_row(row: usize, rotation: i32) -> usize {
    // `EXTENDED_N` is a power of two dividing 2^64, so wrapping arithmetic
    // followed by the mask is exact modular addition even for negative
    // rotations (sign-extended through `as usize`).
    row.wrapping_add((rotation as isize as usize).wrapping_mul(EXTENDED_ROTATION_STRIDE))
        & (EXTENDED_N - 1)
}
pub(super) fn evaluate_expression<A: AsRef<[Fp]>>(
    expression: usize,
    target: &FixedTarget,
    advice: &[A],
    instance: &[Fp],
) -> Result<Vec<Fp>, Error> {
    let mut evaluation = super::compiled_expressions::program(expression)?
        .full
        .bind(target.fixed_values(), advice, instance)?;
    Ok((0..N).map(|row| evaluation.evaluate(row)).collect())
}

#[cfg(test)]
pub(super) fn evaluate_expression_at_row<A: AsRef<[Fp]>>(
    expression: usize,
    target: &FixedTarget,
    advice: &[A],
    instance: &[Fp],
    row: usize,
) -> Result<Fp, Error> {
    Ok(super::compiled_expressions::program(expression)?
        .full
        .bind(target.fixed_values(), advice, instance)?
        .evaluate(row))
}

/// Evaluates one ordinary-domain gate expression and reports whether it is
/// zero on every row. An expression with a fixed-only root factor is checked
/// only at the factor's precomputed active rows — the factor is non-zero
/// there, so its dynamic body alone decides zeroness. Missing preparation is
/// an invariant failure: every fixed circuit gate must have active-row metadata.
#[cfg(test)]
pub(super) fn sparse_gate_expression_is_zero<A: AsRef<[Fp]>>(
    expression: usize,
    target: &FixedTarget,
    advice: &[A],
    _instance: &[Fp],
) -> Result<bool, Error> {
    let rows = target
        .gate_active_rows(expression)
        .ok_or(Error::InternalInvariant)?;
    let frame = super::compiled_gates::Frame::resolve(target)?;
    let columns = frame.bind(advice)?;
    super::compiled_gates::check(expression, &columns, rows)
}

/// Source-tree oracle for a fixed-root gate's dynamic body at one row.
#[cfg(test)]
pub(super) fn evaluate_gate_body_at_row<A: AsRef<[Fp]>>(
    expression: usize,
    target: &FixedTarget,
    advice: &[A],
    instance: &[Fp],
    row: usize,
) -> Result<Fp, Error> {
    let body = generated_expressions::program_trees(expression)?
        .dynamic_body()
        .ok_or(Error::InternalInvariant)?;
    generated_expressions::evaluate(body, &mut |kind, index| {
        base_query_value(kind, index, target, advice, instance, row)
    })
}

#[cfg(test)]
pub(super) fn base_query_value<A: AsRef<[Fp]>>(
    kind: QueryKind,
    index: usize,
    target: &FixedTarget,
    advice: &[A],
    instance: &[Fp],
    row: usize,
) -> Result<Fp, Error> {
    match kind {
        QueryKind::Fixed => {
            query_value(target.queries().fixed(), index, target.fixed_values(), row)
        }
        QueryKind::Advice => query_value(target.queries().advice(), index, advice, row),
        QueryKind::Instance => {
            let query = target
                .queries()
                .instance()
                .get(index)
                .filter(|query| query.column == 0 && instance.len() == N)
                .ok_or_else(|| invariant::failed(Invariant::InstanceColumnShape))?;
            Ok(instance[rotated_row(row, query.rotation)])
        }
    }
}

#[cfg(test)]
pub(super) fn query_value<C: AsRef<[Fp]>>(
    queries: &[Query],
    query_index: usize,
    columns: &[C],
    row: usize,
) -> Result<Fp, Error> {
    let query = queries
        .get(query_index)
        .ok_or_else(|| invariant::failed(Invariant::MissingQuery))?;
    let column = columns
        .get(query.column)
        .map(AsRef::as_ref)
        .filter(|column| column.len() == N)
        .ok_or_else(|| invariant::failed(Invariant::ColumnShape))?;
    Ok(column[rotated_row(row, query.rotation)])
}

pub(super) fn rotated_row(row: usize, rotation: i32) -> usize {
    // Same mask-based addressing as `rotated_extended_row`, over the base
    // domain: `N` is a power of two dividing 2^64.
    row.wrapping_add(rotation as isize as usize) & (N - 1)
}
