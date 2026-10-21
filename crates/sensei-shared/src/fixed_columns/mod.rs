//! Fixed-column sources, layout, and Lagrange-value reconstruction.
//!
//! The 29 columns are partitioned by their source:
//!
//! | Columns | Source | Expansion |
//! | --- | --- | --- |
//! | 0..=2 | Sinsemilla generator table | Row index and point coordinates. |
//! | 3..=11 | Sparse tuple dictionary | A [`RowAssignment`](crate::records::RowAssignment) selects nine values for one row. |
//! | 12..=28 | [`STRUCTURED_FIXED_COLUMNS`] | Small control and selector values described by row spans. |
//!
//! [`build_fixed_values`] combines these sources into one column-major matrix.
//! The host generator and the prover use the same expansion. The literal span
//! table lives in `patterns.rs`; reconstruction arithmetic lives in `values.rs`.

mod patterns;
mod values;

pub use patterns::STRUCTURED_FIXED_COLUMNS;
pub use values::build_fixed_values;

/// One constant-valued row span of a structured fixed column.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FixedSpan {
    /// Inclusive absolute row, independent of synthesis-region numbering.
    pub start: u16,
    /// Exclusive absolute row.
    pub end: u16,
    /// The small constant every row in the span holds.
    pub value: u8,
}

impl FixedSpan {
    /// Describes rows `start..end` holding `value` without validating bounds.
    ///
    /// The pinned layout uses nonempty spans within the circuit domain;
    /// callers assembling a pattern are responsible for those invariants.
    pub const fn new(start: u16, end: u16, value: u8) -> Self {
        Self { start, end, value }
    }
}

/// The declarative layout of one structured fixed column.
#[derive(Clone, Copy, Debug)]
pub struct FixedColumnPattern {
    /// The absolute fixed-column index the pattern describes.
    pub column: u8,
    /// The value of every row no span covers.
    pub default: u8,
    /// Sorted, non-overlapping spans of non-default rows within `0..crate::N`.
    pub spans: &'static [FixedSpan],
}

/// First fixed column described by [`STRUCTURED_FIXED_COLUMNS`].
pub const STRUCTURED_FIXED_COLUMN_START: usize = 12;
pub use crate::generators::SINSEMILLA_TABLE_ROWS;
/// Fixed columns holding Sinsemilla generator coordinates (columns 1 and 2).
pub const SINSEMILLA_COORDINATE_COLUMNS: usize = 2;
/// First fixed column reconstructed from the sparse row-tuple data.
pub const TUPLE_FIXED_COLUMN_START: usize = 3;
/// Fixed columns reconstructed from the sparse row-tuple data (3 through 11).
pub const TUPLE_FIXED_COLUMNS: usize = 9;
/// Distinct nonzero row tuples of the tuple-reconstructed columns. The
/// all-zero tuple is implicit.
pub const FIXED_TUPLE_COUNT: usize = 525;
/// Number of active rows referencing a tuple. The generator emits assignments
/// in ascending row order and numbers dictionary tuples by their first use.
pub const FIXED_TUPLE_ASSIGNMENTS: usize = 753;
