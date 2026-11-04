use alloc::vec::Vec;
use core::ops::Range;

use sensei_shared::MERKLE_DEPTH;
use sensei_shared::generators::{
    COMMIT_IVK_M_GENERATOR, MERKLE_CRH_M_GENERATOR, NOTE_COMMIT_M_GENERATOR,
};

use super::REGION_STARTS;
use crate::native::curve::PallasAffine;

/// Bits per Sinsemilla message word (the word radix is `2^WORD_BITS`).
pub const WORD_BITS: usize = 10;
/// Offset from a hash's base column to the column holding its running
/// sums `z_i` (one per word, in word order).
pub const RUNNING_SUM_COLUMN_OFFSET: usize = 2;

/// The first Merkle layer's first region.
pub const MERKLE_FIRST_REGION: usize = 8;
/// Regions per Merkle layer.
pub const MERKLE_REGIONS_PER_LAYER: usize = 8;
/// Offset of a Merkle layer's hash region within its regions.
pub const MERKLE_HASH_REGION_OFFSET: usize = 6;
/// Word counts of a Merkle layer hash's message pieces.
pub const MERKLE_PIECES: [usize; 3] = [25, 2, 25];
/// The `commit_ivk` hash region (base column 0).
pub const COMMIT_IVK_REGION: usize = 292;
/// Word counts of the `commit_ivk` hash's message pieces.
pub const COMMIT_IVK_PIECES: [usize; 4] = [25, 1, 24, 1];
/// Word counts of a note commitment hash's message pieces.
pub const NOTE_COMMIT_PIECES: [usize; 8] = [25, 1, 25, 6, 1, 25, 25, 1];
/// The old note's commitment hash region (base column 0).
pub const OLD_NOTE_HASH_REGION: usize = 330;
/// The new note's commitment hash region (base column 5).
pub const NEW_NOTE_HASH_REGION: usize = 377;

/// Hashes per Action.
pub const HASH_COUNT: usize = MERKLE_DEPTH + 3;
/// The advice columns holding running sums: base column 0's and base
/// column 5's, each plus `RUNNING_SUM_COLUMN_OFFSET`.
pub const RUNNING_SUM_COLUMNS: [usize; 2] =
    [RUNNING_SUM_COLUMN_OFFSET, 5 + RUNNING_SUM_COLUMN_OFFSET];
/// Message pieces per Action, across every hash.
pub const PIECE_COUNT: usize =
    MERKLE_DEPTH * MERKLE_PIECES.len() + COMMIT_IVK_PIECES.len() + 2 * NOTE_COMMIT_PIECES.len();
/// Running-sum cells per Action, across every hash.
pub const WORD_COUNT: usize =
    MERKLE_DEPTH * sum(&MERKLE_PIECES) + sum(&COMMIT_IVK_PIECES) + 2 * sum(&NOTE_COMMIT_PIECES);

const fn sum(pieces: &[usize]) -> usize {
    let mut total = 0;
    let mut index = 0;
    while index < pieces.len() {
        total += pieces[index];
        index += 1;
    }
    total
}

/// One hash: its region, base column, and piece word counts. Word `w`
/// of the hash lands at local row `w` of the region; its running sum in
/// column `column_base + RUNNING_SUM_COLUMN_OFFSET`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct HashSchedule {
    pub region: usize,
    pub column_base: usize,
    pub pieces: &'static [usize],
    /// The hash's initial accumulator `Q`; its `x` is the structurally
    /// constant first cell of the base column.
    pub q: PallasAffine,
}

impl HashSchedule {
    /// Words in the hash's message.
    pub const fn words(&self) -> usize {
        sum(self.pieces)
    }

    /// The advice column holding the hash's running sums.
    pub const fn running_sum_column(&self) -> usize {
        self.column_base + RUNNING_SUM_COLUMN_OFFSET
    }

    /// The absolute row of the hash's first word.
    pub fn start_row(&self) -> usize {
        REGION_STARTS[self.region]
    }

    /// The hash's pieces as `(running-sum column, absolute rows)`, in
    /// message order.
    pub fn piece_rows(&self) -> Vec<(usize, Range<usize>)> {
        let start = self.start_row();
        let column = self.running_sum_column();
        let mut offset = 0;
        self.pieces
            .iter()
            .map(|&words| {
                let rows = start + offset..start + offset + words;
                offset += words;
                (column, rows)
            })
            .collect()
    }
}

/// Merkle layer `layer`'s hash: the first half of the path uses base
/// column 0, the second half base column 5.
pub fn merkle_layer(layer: usize) -> HashSchedule {
    HashSchedule {
        region: MERKLE_FIRST_REGION + layer * MERKLE_REGIONS_PER_LAYER + MERKLE_HASH_REGION_OFFSET,
        column_base: if layer < MERKLE_DEPTH / 2 { 0 } else { 5 },
        pieces: &MERKLE_PIECES,
        q: MERKLE_CRH_M_GENERATOR,
    }
}

/// The `commit_ivk` hash.
pub const COMMIT_IVK: HashSchedule = HashSchedule {
    region: COMMIT_IVK_REGION,
    column_base: 0,
    pieces: &COMMIT_IVK_PIECES,
    q: COMMIT_IVK_M_GENERATOR,
};
/// The old note's commitment hash.
pub const OLD_NOTE: HashSchedule = HashSchedule {
    region: OLD_NOTE_HASH_REGION,
    column_base: 0,
    pieces: &NOTE_COMMIT_PIECES,
    q: NOTE_COMMIT_M_GENERATOR,
};
/// The new note's commitment hash.
pub const NEW_NOTE: HashSchedule = HashSchedule {
    region: NEW_NOTE_HASH_REGION,
    column_base: 5,
    pieces: &NOTE_COMMIT_PIECES,
    q: NOTE_COMMIT_M_GENERATOR,
};

/// Every hash of an Action in schedule order: the Merkle layers, then
/// `commit_ivk`, the old note, the new note.
pub fn all() -> Vec<HashSchedule> {
    let hashes = (0..MERKLE_DEPTH)
        .map(merkle_layer)
        .chain([COMMIT_IVK, OLD_NOTE, NEW_NOTE])
        .collect::<Vec<_>>();
    debug_assert_eq!(hashes.len(), HASH_COUNT);
    hashes
}

/// Every piece of an Action as `(running-sum column, absolute rows)`,
/// in schedule order.
pub fn pieces() -> Vec<(usize, Range<usize>)> {
    all().iter().flat_map(HashSchedule::piece_rows).collect()
}
