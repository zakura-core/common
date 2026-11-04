//! Enum-cell witness reference and its separate rational finalizer.
//!
//! The dense writer keeps its shadow hooks; this oracle retains its own
//! assignment representation and denominator-product scan.

use super::AdviceValue;
use crate::Error;
use crate::native::buffer::Buffer;
use crate::native::field::Fp;
use crate::native::target::{ADVICE_COLUMNS, N};
use alloc::vec::Vec;

#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::native::witness) enum AssignmentKind {
    Unassigned,
    AssignedZero,
    Direct,
    Rational,
}

#[cfg(test)]
pub(in crate::native::witness) enum AssignedCell {
    Unassigned,
    AssignedZero,
    Direct(Fp),
    Rational { numerator: Fp, denominator: Fp },
}

#[cfg(test)]
impl AssignedCell {
    pub(in crate::native::witness) fn kind(&self) -> AssignmentKind {
        match self {
            Self::Unassigned => AssignmentKind::Unassigned,
            Self::AssignedZero => AssignmentKind::AssignedZero,
            Self::Direct(_) => AssignmentKind::Direct,
            Self::Rational { .. } => AssignmentKind::Rational,
        }
    }

    pub(in crate::native::witness) fn into_value(self) -> Result<Fp, Error> {
        match self {
            Self::Unassigned | Self::AssignedZero => Ok(<Fp>::ZERO),
            Self::Direct(value) => Ok(value),
            Self::Rational { .. } => Err(Error::InternalInvariant),
        }
    }
}

#[cfg(test)]
struct RationalBatchEntry {
    column: usize,
    row: usize,
    prefix: Fp,
}

/// Finalizes all rational cells with one inversion of their denominator product.
#[cfg(test)]
pub(in crate::native::witness) fn batch_finalize_rationals(
    cells: &mut [Vec<AssignedCell>],
) -> Result<(), Error> {
    let mut product = <Fp>::ONE;
    let mut batch = Vec::new();

    for (column_index, column) in cells.iter().enumerate() {
        for (row, cell) in column.iter().enumerate() {
            if let AssignedCell::Rational { denominator, .. } = cell {
                if denominator.is_zero() {
                    return Err(Error::UnsatisfiedWitness);
                }
                batch.push(RationalBatchEntry {
                    column: column_index,
                    row,
                    prefix: product,
                });
                product = product.mul(denominator);
            }
        }
    }

    if batch.is_empty() {
        return Ok(());
    }
    let mut product_inverse = product.invert().ok_or(Error::InternalInvariant)?;

    for entry in batch.into_iter().rev() {
        let cell = cells
            .get_mut(entry.column)
            .and_then(|column| column.get_mut(entry.row))
            .ok_or(Error::InternalInvariant)?;
        let AssignedCell::Rational {
            numerator,
            denominator,
        } = cell
        else {
            return Err(Error::InternalInvariant);
        };

        let denominator_inverse = product_inverse.mul(&entry.prefix);
        product_inverse = product_inverse.mul(denominator);
        *cell = AssignedCell::Direct(numerator.mul(&denominator_inverse));
    }

    Ok(())
}

/// The former enum-cell staging writer, retained verbatim as the `cfg(test)`
/// oracle for the dense writer: every write and the finalized matrix are
/// asserted identical, including error outcomes. The oracle keeps its own
/// assignment representation and finalization logic.
#[cfg(test)]
pub(super) struct ShadowWriter {
    pub(super) cells: Vec<Vec<AssignedCell>>,
}

#[cfg(test)]
impl ShadowWriter {
    pub(super) fn new() -> Self {
        Self {
            cells: (0..ADVICE_COLUMNS)
                .map(|_| (0..N).map(|_| AssignedCell::Unassigned).collect())
                .collect(),
        }
    }

    pub(super) fn write_advice(
        &mut self,
        column: usize,
        row: usize,
        value: AdviceValue,
    ) -> Result<(), Error> {
        let cell = self
            .cells
            .get_mut(column)
            .and_then(|column| column.get_mut(row))
            .ok_or(Error::InternalInvariant)?;
        if !matches!(cell, AssignedCell::Unassigned) {
            return Err(Error::InternalInvariant);
        }
        *cell = match value {
            AdviceValue::AssignedZero => AssignedCell::AssignedZero,
            AdviceValue::Direct(value) => AssignedCell::Direct(value),
            AdviceValue::Rational {
                numerator,
                denominator,
            } => AssignedCell::Rational {
                numerator,
                denominator,
            },
        };
        Ok(())
    }

    pub(super) fn kind(&self, column: usize, row: usize) -> Option<AssignmentKind> {
        self.cells
            .get(column)
            .and_then(|column| column.get(row))
            .map(AssignedCell::kind)
    }

    pub(super) fn finish(mut self) -> Result<Vec<Buffer<Fp>>, Error> {
        batch_finalize_rationals(&mut self.cells)?;
        self.cells
            .into_iter()
            .map(|column| {
                column
                    .into_iter()
                    .map(AssignedCell::into_value)
                    .collect::<Result<Vec<_>, _>>()
                    .map(Buffer::from)
            })
            .collect()
    }
}
