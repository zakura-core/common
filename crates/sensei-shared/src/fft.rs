//! Layout of optional prepared FFT artifacts, stored as flat `Fp` arrays.
//!
//! Plans are the base subgroup followed by cosets of sizes N, 2N, 4N, 8N.
//! Each plan stores forward, inverse, then inverse-finish tables, each half
//! its domain size. Expansion scales store the four coset domains in that
//! order, each in Udon's residue-major layout with base size N and coefficient
//! normalization. Offsets below count `Fp` elements from the start of the
//! respective artifact.
//!
//! | Domain | Plan index | Coset index | Table offset | Scale offset |
//! | --- | --- | --- | --- | --- |
//! | Base subgroup (`N`) | 0 | None | 0 | None |
//! | `N` coset | 1 | 0 | `3*N/2` | 0 |
//! | `2N` coset | 2 | 1 | `3*N` | `N` |
//! | `4N` coset | 3 | 2 | `6*N` | `3*N` |
//! | `8N` coset | 4 | 3 | `12*N` | `7*N` |
//!
//! Plan index 0 belongs to the base subgroup, so a coset's plan index is
//! `coset_index + 1`. The subgroup has no expansion-scale entry.

use crate::N;

/// Number of prepared transform plans, including the base subgroup.
pub const PLAN_COUNT: usize = 5;
/// Total field elements in the FFT artifact.
pub const TABLE_LEN: usize = 24 * N;
/// Total field elements in the expansion-scale artifact.
pub const SCALE_LEN: usize = 15 * N;

/// Domain size for plan `index`; panics if the index is outside the layout.
pub const fn plan_size(index: usize) -> usize {
    assert!(index < PLAN_COUNT);
    if index == 0 { N } else { N << (index - 1) }
}

/// Offset of a plan's first table; panics for an invalid plan index.
pub const fn table_offset(index: usize) -> usize {
    assert!(index < PLAN_COUNT);
    if index == 0 {
        0
    } else {
        3 * (N << (index - 1)) / 2
    }
}

/// Offset of a coset's expansion scales; panics for an invalid coset index.
pub const fn scale_offset(index: usize) -> usize {
    assert!(index < PLAN_COUNT - 1);
    ((1 << index) - 1) * N
}
