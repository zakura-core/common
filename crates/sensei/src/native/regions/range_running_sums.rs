use alloc::vec::Vec;
use core::ops::Range;

use super::REGION_STARTS;

/// The advice column of every stream.
pub const COLUMN: usize = 9;
/// Bits per word.
pub const WORD_BITS: usize = 10;
/// First region of the old and new note decompositions.
const OLD_NOTE_DECOMPOSITION: usize = 303;
const NEW_NOTE_DECOMPOSITION: usize = 350;

/// `(region, word count, strict)` of every stream, in writer order.
pub const STREAMS: [(usize, usize, bool); 20] = [
    // Base-field fixed multiplier canonicity (`α₀'`).
    (277, 13, false),
    // Commit-ivk decomposition (`a'`, `b₂c'`).
    (294, 13, false),
    (295, 14, false),
    // Variable-base scalar canonicity (`s`).
    (299, 13, false),
    // Old note: `g_d` and `pk_d` y-canonicity (`j`, `j'`), then the field
    // canonicity of `a'`, `b₃c'`, `e₁f'`, `g₁g₂'`.
    (OLD_NOTE_DECOMPOSITION + 15 + 2, 25, true),
    (OLD_NOTE_DECOMPOSITION + 15 + 3, 13, false),
    (OLD_NOTE_DECOMPOSITION + 20 + 2, 25, true),
    (OLD_NOTE_DECOMPOSITION + 20 + 3, 13, false),
    (OLD_NOTE_DECOMPOSITION + 29, 13, false),
    (OLD_NOTE_DECOMPOSITION + 30, 14, false),
    (OLD_NOTE_DECOMPOSITION + 31, 14, false),
    (OLD_NOTE_DECOMPOSITION + 32, 13, false),
    // New note, likewise.
    (NEW_NOTE_DECOMPOSITION + 15 + 2, 25, true),
    (NEW_NOTE_DECOMPOSITION + 15 + 3, 13, false),
    (NEW_NOTE_DECOMPOSITION + 20 + 2, 25, true),
    (NEW_NOTE_DECOMPOSITION + 20 + 3, 13, false),
    (NEW_NOTE_DECOMPOSITION + 29, 13, false),
    (NEW_NOTE_DECOMPOSITION + 30, 14, false),
    (NEW_NOTE_DECOMPOSITION + 31, 14, false),
    (NEW_NOTE_DECOMPOSITION + 32, 13, false),
];
/// Streams per Action.
pub const PIECE_COUNT: usize = STREAMS.len();
/// Cells per Action across every stream (`n + 1` each).
pub const WORD_COUNT: usize = {
    let mut total = 0;
    let mut index = 0;
    while index < STREAMS.len() {
        total += STREAMS[index].1 + 1;
        index += 1;
    }
    total
};

/// Whether `(column, region, word_bits, num_words, strict)` is one of the
/// scheduled streams.
pub fn is_stream(
    column: usize,
    region: usize,
    word_bits: usize,
    num_words: usize,
    strict: bool,
) -> bool {
    column == COLUMN && word_bits == WORD_BITS && STREAMS.contains(&(region, num_words, strict))
}

/// Every stream as `(column, absolute rows of `z_0..z_n`)`.
pub fn pieces() -> Vec<(usize, Range<usize>)> {
    STREAMS
        .iter()
        .map(|&(region, words, _)| {
            let start = REGION_STARTS[region];
            (COLUMN, start..start + words + 1)
        })
        .collect()
}
