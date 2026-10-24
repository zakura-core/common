//! Equality checks over the target's prepared nontrivial copy classes.

use crate::Error;
use crate::native::{
    field::Fp,
    prover::AdviceMatrix,
    target::{ColumnKind, FixedTarget, N, PermutationColumn},
};

/// Checks the equality constraints through the prepared copy classes: every
/// member of a nontrivial sigma cycle must equal its class's canonical cell.
/// Fixed points (`sigma == id`) compare a cell with itself for any witness
/// and are structurally satisfied, so no per-cell scan is needed.
pub(super) fn check_copies(
    target: &FixedTarget,
    matrix: &AdviceMatrix,
    instance: &[Fp],
) -> Result<(), Error> {
    for class in target.copy_classes().classes() {
        let (&canonical_cell, rest) = class.split_first().ok_or(Error::InternalInvariant)?;
        let canonical = class_cell_value(target, canonical_cell, matrix, instance)?;
        for &cell in rest {
            if (class_cell_value(target, cell, matrix, instance)?).reduce() != (canonical).reduce()
            {
                return Err(Error::UnsatisfiedWitness);
            }
        }
    }
    Ok(())
}

/// Resolves one column-major permutation cell index to its witness value.
fn class_cell_value<'a>(
    target: &'a FixedTarget,
    cell: u16,
    matrix: &'a AdviceMatrix,
    instance: &'a [Fp],
) -> Result<&'a Fp, Error> {
    let cell = usize::from(cell);
    permutation_value(
        target,
        target.permutation_columns().get(cell / N),
        cell % N,
        matrix,
        instance,
    )
}

fn permutation_value<'a>(
    target: &'a FixedTarget,
    column: Option<&PermutationColumn>,
    row: usize,
    matrix: &'a AdviceMatrix,
    instance: &'a [Fp],
) -> Result<&'a Fp, Error> {
    let column = column.ok_or(Error::InternalInvariant)?;
    match column.kind {
        ColumnKind::Instance if column.index == 0 => instance.get(row),
        ColumnKind::Advice => matrix
            .columns()
            .get(column.index)
            .and_then(|values| values.get(row)),
        ColumnKind::Fixed => target
            .fixed_values()
            .get(column.index)
            .and_then(|values| values.get(row)),
        ColumnKind::Instance => None,
    }
    .ok_or(Error::InternalInvariant)
}
