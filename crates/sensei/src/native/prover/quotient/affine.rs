//! Challenge-weighted advice rows shared by rotated affine gate queries.

use super::{ADVICE_COLUMNS, Fp, GATE_QUERY_COUNT, GATE_QUERY_DESCRIPTORS, QueryKind};
use crate::native::generated_expressions::AFFINE_QUERY_SLOTS;
use sensei_shared::queries::ADVICE_QUERIES;

/// The affine frame slots' (neighbour row, advice column) sources. Derive
/// these from the circuit queries rather than maintaining a second rotation
/// table. The gathered block's first advice slots supply unrotated columns.
const SOURCES: [(usize, usize); AFFINE_QUERY_SLOTS.len()] = {
    let mut column = 0;
    while column < ADVICE_COLUMNS {
        let (kind, index) = GATE_QUERY_DESCRIPTORS[column];
        assert!(matches!(kind, QueryKind::Advice));
        assert!(ADVICE_QUERIES[index].column == column);
        assert!(ADVICE_QUERIES[index].rotation == 0);
        column += 1;
    }
    let mut sources = [(0, 0); AFFINE_QUERY_SLOTS.len()];
    let mut i = 0;
    while i < sources.len() {
        let (kind, index) = GATE_QUERY_DESCRIPTORS[AFFINE_QUERY_SLOTS[i]];
        assert!(matches!(kind, QueryKind::Advice));
        let query = ADVICE_QUERIES[index];
        assert!(query.column < ADVICE_COLUMNS);
        assert!(query.rotation >= -1 && query.rotation <= 1);
        sources[i] = ((query.rotation + 1) as usize, query.column);
        i += 1;
    }
    sources
};

/// Three weighted source rows, carried for the lifetime of one fold task.
///
/// Rotation commutes with the Action sum: `sum_a w_a A_a,c(ω^r X)` is the
/// rotation of `sum_a w_a A_a,c(X)`. Consecutive rows of a fold task are one
/// base-domain rotation apart, so only the next row needs new products after
/// seeding. The carry survives the task's gathered-block refills.
pub(super) struct AffineRows {
    rows: [[Fp; ADVICE_COLUMNS]; 3],
}

impl AffineRows {
    pub(super) fn new() -> Self {
        Self {
            rows: [[<Fp>::ZERO; ADVICE_COLUMNS]; 3],
        }
    }

    /// Seeds on the first task row, then advances by one base-domain row.
    /// `value(action, neighbour, column)` reads unrotated gathered advice;
    /// neighbours 0, 1, and 2 are the previous, current, and next rows.
    /// The nonempty Action weights are fixed for this task and end in one.
    #[inline]
    pub(super) fn advance(
        &mut self,
        first: bool,
        weights: &[Fp],
        mut value: impl FnMut(usize, usize, usize) -> Fp,
    ) {
        let (unit, weighted) = weights.split_last().expect("at least one Action");
        debug_assert_eq!(unit.reduce(), <Fp>::ONE.reduce());
        if !first {
            self.rows[0] = self.rows[1];
            self.rows[1] = self.rows[2];
        }
        for r in if first { 0 } else { 2 }..3 {
            for (c, result) in self.rows[r].iter_mut().enumerate() {
                let mut sum = <Fp>::ZERO;
                for (action, weight) in weighted.iter().enumerate() {
                    sum = value(action, r, c).mul_add(weight, &sum);
                }
                *result = sum.add(&value(weighted.len(), r, c));
            }
        }
    }

    #[inline]
    pub(super) fn frame(&self) -> [Fp; GATE_QUERY_COUNT] {
        let mut frame = [<Fp>::ZERO; GATE_QUERY_COUNT];
        for (&slot, (row, column)) in AFFINE_QUERY_SLOTS.iter().zip(SOURCES) {
            frame[slot] = self.rows[row][column];
        }
        frame
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::prover::fold_order::TERMS_PER_ACTION;
    use crate::native::prover::quotient::{FRAME_GROUP_ROWS, FoldWindow, GATHER_WIDTH};
    use crate::native::prover::{EXTENDED_N, FOLD_CHUNK_ROWS, N};

    #[test]
    fn carried_affine_frames_match_independent_rotated_sums() {
        // Dense, full-width field values, with unrelated Actions and columns.
        let columns: Vec<Vec<Vec<Fp>>> = (0..4)
            .map(|action| {
                (0..ADVICE_COLUMNS)
                    .map(|column| {
                        let mut value =
                            <Fp>::from_u64((action * ADVICE_COLUMNS + column + 2) as u64);
                        (0..EXTENDED_N)
                            .map(|_| {
                                value = value.square().add(&<Fp>::ONE);
                                value
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect();
        for action_count in 2..=4 {
            for y in [<Fp>::ZERO, <Fp>::ONE, <Fp>::ONE.neg(), <Fp>::from_u64(31)] {
                let weights: Vec<_> = (0..action_count)
                    .map(|a| y.pow_u64((TERMS_PER_ACTION * (action_count - 1 - a)) as u64))
                    .collect();
                for residue in 0..8 {
                    // Start, interior task boundary, and domain wraparound.
                    for k_offset in [0, FOLD_CHUNK_ROWS, N - FOLD_CHUNK_ROWS] {
                        let window = FoldWindow { residue, k_offset };
                        let mut carry = AffineRows::new();
                        let mut blocks =
                            vec![
                                vec![<Fp>::ZERO; (FRAME_GROUP_ROWS + 2) * GATHER_WIDTH];
                                action_count
                            ];
                        let mut reads = 0;
                        for offset in 0..FOLD_CHUNK_ROWS {
                            let group_offset = offset % FRAME_GROUP_ROWS;
                            if group_offset == 0 {
                                for (a, block) in blocks.iter_mut().enumerate() {
                                    for r in 0..FRAME_GROUP_ROWS + 2 {
                                        let k = (k_offset + offset + N + r - 1) % N;
                                        for c in 0..ADVICE_COLUMNS {
                                            block[r * GATHER_WIDTH + c] =
                                                columns[a][c][residue + 8 * k];
                                        }
                                    }
                                }
                            }
                            carry.advance(offset == 0, &weights, |a, r, c| {
                                reads += 1;
                                blocks[a][(group_offset + r) * GATHER_WIDTH + c]
                            });
                            let actual = carry.frame();
                            for &slot in &AFFINE_QUERY_SLOTS {
                                let (kind, index) = GATE_QUERY_DESCRIPTORS[slot];
                                assert!(matches!(kind, QueryKind::Advice));
                                let query = ADVICE_QUERIES[index];
                                let row = (window.row(offset) as i32 + 8 * query.rotation)
                                    .rem_euclid(EXTENDED_N as i32)
                                    as usize;
                                let values: Vec<_> = columns[..action_count]
                                    .iter()
                                    .map(|columns| columns[query.column][row])
                                    .collect();
                                let expected = <Fp>::sum_of_products_slice(&weights, &values);
                                assert_eq!(
                                    actual[slot].reduce(),
                                    expected.reduce(),
                                    "Actions={action_count}, residue={residue}, task={k_offset}, offset={offset}, slot={slot}"
                                );
                            }
                            for (slot, value) in actual.iter().enumerate() {
                                if !AFFINE_QUERY_SLOTS.contains(&slot) {
                                    assert_eq!(value.reduce(), <Fp>::ZERO.reduce());
                                }
                            }
                        }
                        assert_eq!(reads, action_count * ADVICE_COLUMNS * (FOLD_CHUNK_ROWS + 2));
                    }
                }
            }
        }
    }
}
