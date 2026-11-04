use core::ops::Range;

use super::REGION_STARTS;

/// The gadget's region.
pub const REGION: usize = 297;
/// Bits of the incomplete-addition hi chain.
pub const INCOMPLETE_HI_BITS: usize = 125;
/// Bits of the incomplete-addition lo chain.
pub const INCOMPLETE_LO_BITS: usize = 126;
/// Bits handled by complete addition after the incomplete chains.
pub const COMPLETE_BITS: usize = 3;
/// The advice columns holding the input point's `x` (column 0) and `y`
/// (column 1) on every double-and-add row.
pub const COORDINATE_COLUMNS: [usize; 2] = [0, 1];
/// Local rows carrying the repeated input coordinates: the hi chain
/// covers local rows `2..=INCOMPLETE_HI_BITS + 1` and the lo chain
/// `2..=INCOMPLETE_LO_BITS + 1`, with the same two values, so each column
/// holds one run of `INCOMPLETE_LO_BITS` equal cells.
pub const COORDINATE_LOCAL_ROWS: Range<usize> = 2..INCOMPLETE_LO_BITS + 2;

/// The absolute rows of the repeated coordinate run.
pub fn coordinate_rows() -> Range<usize> {
    sensei_shared::commitment_tables::repeated_coordinate_rows()
}

/// The advice column of the hi chain's running sums (and the initial
/// zero, the lo→complete handoff copy, the complete-addition tail and
/// the final sum).
pub const HI_Z_COLUMN: usize = 9;
/// The advice column of the lo chain's running sums (and its hi→lo
/// handoff copy).
pub const LO_Z_COLUMN: usize = 6;

/// Rows of a contiguous incomplete chain or the complete-addition tail.
pub enum ChainRows {
    Contiguous(Range<usize>),
    Tail([usize; COMPLETE_BITS + 2]),
}

impl ChainRows {
    pub fn len(&self) -> usize {
        match self {
            Self::Contiguous(rows) => rows.len(),
            Self::Tail(rows) => rows.len(),
        }
    }

    pub fn row(&self, index: usize) -> usize {
        assert!(index < self.len());
        match self {
            Self::Contiguous(rows) => rows.start + index,
            Self::Tail(rows) => rows[index],
        }
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = usize> + DoubleEndedIterator + '_ {
        (0..self.len()).map(|index| self.row(index))
    }
}

/// The gadget's binary running-sum chains as `(column, absolute rows)`:
/// each chain's first row holds its initial sum and every later row
/// holds `z = 2·z_prev + bit`, so the advice commitment can transpose
/// the chain onto one general term for the initial sum plus one bit
/// term per later row. The three chains are the hi chain (initial zero,
/// 125 bits), the lo chain (initial copy of the hi result, 126 bits),
/// and the complete-addition tail (initial copy of the lo result, three
/// complete bits and the final bit).
pub fn bit_chains() -> [(usize, ChainRows); 3] {
    let start = REGION_STARTS[REGION];
    let tail_start = start + INCOMPLETE_LO_BITS + 3;
    [
        (
            HI_Z_COLUMN,
            ChainRows::Contiguous(start + 1..start + INCOMPLETE_HI_BITS + 2),
        ),
        (
            LO_Z_COLUMN,
            ChainRows::Contiguous(start + 1..start + INCOMPLETE_LO_BITS + 2),
        ),
        (
            HI_Z_COLUMN,
            ChainRows::Tail(core::array::from_fn(|index| {
                tail_start + 2 * index - usize::from(index == COMPLETE_BITS + 1)
            })),
        ),
    ]
}
