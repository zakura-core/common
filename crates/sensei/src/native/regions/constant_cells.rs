use alloc::vec::Vec;
use sensei_shared::MERKLE_DEPTH;

use super::{
    REGION_STARTS, roles,
    sinsemilla_hashes::{self, MERKLE_FIRST_REGION, MERKLE_REGIONS_PER_LAYER},
};
use crate::native::field::Fp;

/// The column holding every short-range-check triple.
pub const RANGE_CHECK_COLUMN: usize = 9;
/// Local row of the `2^-b` inverse within a short-range-check region.
pub const RANGE_CHECK_INVERSE_ROW: usize = 2;
/// First regions of the old and new note decompositions.
const OLD_NOTE_DECOMPOSITION: usize = 303;
const NEW_NOTE_DECOMPOSITION: usize = 350;
/// Poseidon initial-state regions whose column 8 holds `2^65`.
const POSEIDON_STATE_REGIONS: [usize; 2] = [271, 272];

/// Short-range-check `(region, width)` pairs outside the Merkle path.
fn range_checks() -> Vec<(usize, usize)> {
    let mut checks = alloc::vec![(284, 4), (285, 5), (288, 9)];
    checks.reserve_exact(22);
    for first in [OLD_NOTE_DECOMPOSITION, NEW_NOTE_DECOMPOSITION] {
        for (offset, width) in [(1, 4), (2, 4), (5, 8), (7, 6), (8, 4), (11, 9), (13, 5)] {
            checks.push((first + offset, width));
        }
        for y_first in [first + 15, first + 20] {
            checks.push((y_first, 9));
            checks.push((y_first + 1, 4));
        }
    }
    checks
}

/// Every nonzero constant cell as `(column, absolute row, value)`.
pub fn nonzero_constants() -> Vec<(usize, usize, Fp)> {
    let mut checks = range_checks();
    checks.reserve_exact(2 * MERKLE_DEPTH);
    for layer in 0..MERKLE_DEPTH {
        let region = MERKLE_FIRST_REGION + layer * MERKLE_REGIONS_PER_LAYER;
        checks.push((region + 2, 5));
        checks.push((region + 3, 5));
    }
    let hashes = sinsemilla_hashes::all();
    // Static census, sized exactly: twelve cross-address ones, the
    // Poseidon initial-state constants, the Merkle layer indices, one
    // inverse per range check, and one coordinate per Sinsemilla hash.
    let mut cells = Vec::with_capacity(
        12 + POSEIDON_STATE_REGIONS.len() + (MERKLE_DEPTH - 1) + checks.len() + hashes.len(),
    );
    // `2^65 = (2^32)^2 · 2`, the Poseidon initial-state constant.
    let two_to_65 = <Fp>::from_u64(1 << 32).square().double();
    for local_row in 0..4 {
        let row = REGION_STARTS[roles::CROSS_ADDRESS_ROWS] + local_row;
        for column in [3, 6, 7] {
            cells.push((column, row, <Fp>::ONE));
        }
    }
    for region in POSEIDON_STATE_REGIONS {
        cells.push((8, REGION_STARTS[region], two_to_65));
    }
    for layer in 1..MERKLE_DEPTH {
        let region = MERKLE_FIRST_REGION + layer * MERKLE_REGIONS_PER_LAYER;
        let column_base = if layer < MERKLE_DEPTH / 2 { 0 } else { 5 };
        cells.push((
            column_base + 4,
            REGION_STARTS[region + 7] + 1,
            <Fp>::from_u64(layer as u64),
        ));
    }
    for (region, width) in checks {
        cells.push((
            RANGE_CHECK_COLUMN,
            REGION_STARTS[region] + RANGE_CHECK_INVERSE_ROW,
            <Fp>::power_of_two_inverse(width as u32),
        ));
    }
    for hash in hashes {
        cells.push((
            hash.column_base,
            hash.start_row(),
            hash.q.coordinates().0.into_loose(),
        ));
    }
    cells
}
