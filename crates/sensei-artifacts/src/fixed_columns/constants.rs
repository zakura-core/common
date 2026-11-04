//! The copy-loaded global constants of the frozen synthesis.
//!
//! Fixed columns 3 and 4 double as Halo 2's constants columns: every value a
//! gadget loads through a copy constraint gets its own fixed cell, and the
//! frozen layout places them in the blocks reconstructed here. Together with
//! the fixed-base window rows
//! ([`fixed_base_window_rows`](super::window_rows::fixed_base_window_rows))
//! these cells are the entire content of fixed columns 3 through 11 — the
//! sparse row tuples the generators bake into the embedded artifacts.
//!
//! The blocks, in construction order (the parent module sorts by row):
//!
//! - **Merkle path** (rows `4l` through `4l + 3` for layer `l`): the two
//!   `2⁻⁵` decomposition shifts, `x_Q` of the Merkle CRH domain, and the
//!   layer index `l` (layer 0's index cell is zero and therefore implicit).
//! - **Commit-ivk canonicity** (rows 131 through 136): `2⁶⁵` and the
//!   `2⁻⁴`/`2⁻⁵`/`2⁻⁹` shifts, then `x_Q` of the commit-ivk domain.
//! - **`y_Q` rows** (row 137 and one row per Merkle layer pair): the two
//!   Sinsemilla chips' fixed `y_Q` cells in columns 3 and 4 — the
//!   note-commitment domain once, the Merkle CRH domain sixteen times.
//! - **Poseidon** (rows 1606 through 1641): the round constants of
//!   [`super::poseidon_constants`] in consumption order, plus `y_Q` of the commit-ivk
//!   domain on the first row's constants column.
//! - **Note-commitment canonicity** (rows 1682 through 1709): one identical
//!   group of inverse-power-of-two shifts and `x_Q` of the note-commitment
//!   domain for each of the old and new note commitments.
//! - **Ones** (rows 1711 through 1725): four groups of three `1` cells.
//!
//! The `x_Q`/`y_Q` values are the coordinates of the pinned `M` generators in
//! [`sensei_shared::generators`] — a Sinsemilla hash's initial point `Q` is its
//! domain's `M` generator.

use super::poseidon_constants::POSEIDON_ROUND_CONSTANTS;
use udon::field::Fp;

use sensei_shared::{
    MERKLE_DEPTH,
    generators::{COMMIT_IVK_M_GENERATOR, MERKLE_CRH_M_GENERATOR, NOTE_COMMIT_M_GENERATOR},
};

/// One copy-loaded constant cell of the frozen synthesis.
#[derive(Clone, Copy, Debug)]
pub(super) struct ConstantCell {
    /// Absolute row.
    pub(super) row: usize,
    /// Absolute fixed column (3 through 10).
    pub(super) column: usize,
    /// The pinned value the cell holds.
    pub(super) value: Fp,
}

/// The inverse of `2^k`: the decomposition-shift constants the canonicity
/// gadgets copy-load.
fn inv_two_pow(k: u32) -> Fp {
    <Fp>::power_of_two_inverse(k)
}

/// Every copy-loaded constant cell of the frozen synthesis, in row order
/// within each block.
pub(super) fn global_constant_cells() -> Vec<ConstantCell> {
    let mut cells = Vec::new();
    let mut put = |row: usize, column: usize, value: Fp| {
        cells.push(ConstantCell { row, column, value });
    };

    let (merkle_x, merkle_y) = MERKLE_CRH_M_GENERATOR.coordinates();
    let (note_x, note_y) = NOTE_COMMIT_M_GENERATOR.coordinates();
    let (ivk_x, ivk_y) = COMMIT_IVK_M_GENERATOR.coordinates();

    // Merkle path: [2⁻⁵, 2⁻⁵, x_Q, l] per layer.
    for layer in 0..MERKLE_DEPTH {
        let base = 4 * layer;
        put(base, 3, inv_two_pow(5));
        put(base + 1, 3, inv_two_pow(5));
        put(base + 2, 3, merkle_x.into_loose());
        if layer > 0 {
            put(base + 3, 3, <Fp>::from_u64(layer as u64));
        }
    }

    // Commit-ivk canonicity block.
    put(131, 3, <Fp>::from_u64(2).pow_u64(65));
    put(133, 3, inv_two_pow(4));
    put(134, 3, inv_two_pow(5));
    put(135, 3, inv_two_pow(9));
    put(136, 3, ivk_x.into_loose());

    // The two note-commitment chips' y_Q, then one Merkle y_Q row per layer
    // pair, both chips loading into their own column.
    put(137, 3, note_y.into_loose());
    put(137, 4, note_y.into_loose());
    for pair in 0..MERKLE_DEPTH / 2 {
        let row = 758 + 53 * pair;
        put(row, 3, merkle_y.into_loose());
        put(row, 4, merkle_y.into_loose());
    }

    // Poseidon: commit-ivk y_Q on the first row's constants column, then the
    // 64 rounds — full rounds one per row, partial rounds two per row.
    put(1606, 3, ivk_y.into_loose());
    let mut rounds = POSEIDON_ROUND_CONSTANTS.iter();
    let mut put_round = |row: usize, columns: [usize; 3], round: &[Fp; 3]| {
        for (column, value) in columns.iter().zip(round) {
            put(row, *column, *value);
        }
    };
    for row in 1606..1610 {
        put_round(row, [5, 6, 7], rounds.next().expect("64 rounds"));
    }
    for row in 1610..1638 {
        put_round(row, [5, 6, 7], rounds.next().expect("64 rounds"));
        put_round(row, [8, 9, 10], rounds.next().expect("64 rounds"));
    }
    for row in 1638..1642 {
        put_round(row, [5, 6, 7], rounds.next().expect("64 rounds"));
    }
    assert!(rounds.next().is_none(), "all 64 rounds are consumed");

    // Note-commitment canonicity: the same shift-and-x_Q group for the old
    // and new note commitments.
    for group_start in [1682, 1696] {
        for (offset, k) in [
            (0, 4),
            (1, 4),
            (2, 8),
            (3, 6),
            (4, 4),
            (5, 9),
            (6, 5),
            (7, 9),
            (8, 4),
            (10, 9),
            (11, 4),
        ] {
            put(group_start + offset, 3, inv_two_pow(k));
        }
        put(group_start + 13, 3, note_x.into_loose());
    }

    // Four groups of three ones.
    for group in 0..4 {
        for offset in 0..3 {
            put(1711 + 4 * group + offset, 3, <Fp>::ONE);
        }
    }

    cells
}
