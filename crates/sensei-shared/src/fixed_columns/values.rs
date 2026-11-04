//! Expansion of the compact fixed-column sources into Lagrange evaluations.

use alloc::vec::Vec;
use udon::{curve::PallasAffine, field::Fp};

use super::{
    FIXED_TUPLE_ASSIGNMENTS, FIXED_TUPLE_COUNT, SINSEMILLA_COORDINATE_COLUMNS,
    SINSEMILLA_TABLE_ROWS, STRUCTURED_FIXED_COLUMN_START, STRUCTURED_FIXED_COLUMNS,
    TUPLE_FIXED_COLUMN_START, TUPLE_FIXED_COLUMNS,
};
use crate::{FIXED_COLUMNS, N, USABLE_ROWS_END, records::RowAssignment};

/// Builds the 29 fixed columns' Lagrange evaluation forms from their compact
/// sources: the row-index and Sinsemilla lookup table (columns 0 through 2),
/// the sparse row-tuple dictionary (columns 3 through 11), and the
/// declarative span layout (columns 12 through 28).
///
/// Columns occupy one contiguous allocation in column-major order.
/// The prover runs this at load over the embedded statics; the coefficient
/// generator runs the same code on the host over the decoded raw inputs.
///
/// Sinsemilla coordinate columns repeat their first table entry after the
/// lookup table through the last usable row. The row-index column stays zero
/// there. All three lookup columns are zero at the boundary row and in the
/// blinding tail. Unassigned tuple rows remain zero; structured columns use
/// their declared defaults and spans.
///
/// # Panics
///
/// Panics if an assignment references a row outside `0..N` or a tuple outside
/// the dictionary. The generator validates the source data before embedding;
/// this expansion assumes those bounds and applies assignments in input order.
pub fn build_fixed_values(
    sinsemilla_generators: &[PallasAffine; SINSEMILLA_TABLE_ROWS],
    tuples: &[[Fp; TUPLE_FIXED_COLUMNS]; FIXED_TUPLE_COUNT],
    assignments: &[RowAssignment; FIXED_TUPLE_ASSIGNMENTS],
) -> Vec<[Fp; N]> {
    let mut fixed_values = alloc::vec![ [<Fp>::ZERO; N]; FIXED_COLUMNS];

    // Column zero is the 10-bit Sinsemilla generator-table index. The unused
    // half of the column, including the blinding rows, remains zero.
    for (row, value) in fixed_values[0][..SINSEMILLA_TABLE_ROWS]
        .iter_mut()
        .enumerate()
    {
        *value = <Fp>::from_u64(row as u64);
    }

    // Expand the generator coordinates into the fixed lookup columns.
    for (row, point) in sinsemilla_generators.iter().enumerate() {
        let (x, y) = point.coordinates();
        fixed_values[1][row] = x.into_loose();
        fixed_values[2][row] = y.into_loose();
    }
    // Halo 2 fills the remaining usable rows with the first table entry; the
    // blinding rows are left zero.
    for column in &mut fixed_values[1..=SINSEMILLA_COORDINATE_COLUMNS] {
        let padding = column[0];
        column[SINSEMILLA_TABLE_ROWS..USABLE_ROWS_END].fill(padding);
    }

    // Columns 3 through 11 are sparse by row and repeat many complete row
    // tuples: each active row copies its dictionary tuple.
    for assignment in assignments {
        let tuple = &tuples[usize::from(assignment.tuple)];
        for (offset, value) in tuple.iter().enumerate() {
            fixed_values[TUPLE_FIXED_COLUMN_START + offset][usize::from(assignment.row)] = *value;
        }
    }

    // Small-valued control and selector columns live in readable Rust data.
    for (index, pattern) in STRUCTURED_FIXED_COLUMNS.iter().enumerate() {
        let column = STRUCTURED_FIXED_COLUMN_START + index;
        debug_assert_eq!(usize::from(pattern.column), column);
        fixed_values[column].fill(<Fp>::from_u64(u64::from(pattern.default)));
        for span in pattern.spans {
            fixed_values[column][usize::from(span.start)..usize::from(span.end)]
                .fill(<Fp>::from_u64(u64::from(span.value)));
        }
    }

    fixed_values
}
