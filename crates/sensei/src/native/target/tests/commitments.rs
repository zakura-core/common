//! Structured, batched, and sparse commitments compared with dense commitments.

use alloc::{sync::Arc, vec::Vec};

use crate::native::commitment::normalized;
use crate::native::field::Fp;
use crate::native::polynomial::SharedPoly;
use crate::native::storage::Column;

use super::super::{K, N, TargetError};

/// The grouped same-table window path must return, for
/// every batched Lagrange job, exactly the point the single-job path
/// computes. Deterministic pseudo-random columns exercise dense values,
/// embedded zero runs, and a zero blind.
#[test]
fn grouped_lagrange_batch_matches_single_job_commitments() {
    let target = crate::test_codec::target();
    let columns = (0..12usize)
        .map(|job| {
            SharedPoly::new(
                (0..N)
                    .map(|row| {
                        if (row + job) % 7 == 0 {
                            <Fp>::ZERO
                        } else {
                            <Fp>::from_u64((row * 31 + job * 977 + 5) as u64).square()
                        }
                    })
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    let blinds = (0..12u64).map(<Fp>::from_u64).collect::<Vec<_>>();
    let jobs = columns.iter().zip(&blinds).collect::<Vec<_>>();
    let batched = target
        .parameters()
        .commit_lagrange_batch_projective(
            &jobs,
            &mut crate::native::commitment::MsmWorkspace::new(),
            crate::test_codec::execution(),
        )
        .unwrap();
    let batched = crate::native::commitment::normalized(&batched);
    for ((column, blind), grouped) in jobs.iter().zip(&batched) {
        let single = target
            .parameters()
            .commit_lagrange_projective(
                column,
                blind,
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap();
        let single = crate::native::commitment::normalized(&[single]);
        assert_eq!(single[0], *grouped);
    }
}

/// Every embedded window base is
/// `c(window, digit) · G_row` recomputed from the window tables and the
/// Lagrange bases (and nonidentity) for both coordinate families; a
/// column whose scheduled cells hold table entries commits, through
/// selection, exactly as its dense commitment — with the column's fold
/// run, arbitrary other cells, an unmatched cell (left dense), zero
/// cells, and arbitrary tails and blinds.
#[test]
fn selected_window_coordinate_commitments_match_dense() {
    use crate::native::commitment::normalized;
    use crate::native::curve::VestaAffine;
    use crate::native::regions::fixed_base_windows;
    use sensei_shared::fixed_bases::{FIXED_BASE_REGIONS, FIXED_BASE_TOTAL_WINDOWS};

    let target = crate::test_codec::target();
    let parameters = target.parameters();
    let rows = fixed_base_windows::window_rows();
    assert_eq!(rows.len(), FIXED_BASE_TOTAL_WINDOWS);
    assert_eq!(FIXED_BASE_TOTAL_WINDOWS, 532);
    assert_eq!(parameters.window_selections.len(), 3);

    type Family = (
        usize,
        &'static [VestaAffine],
        fn(&sensei_shared::WindowTableEntry) -> Fp,
    );
    let families: [Family; 3] = [
        (
            fixed_base_windows::X_COLUMN,
            super::super::FIXED_WINDOW_X_BASES,
            |entry| entry.x,
        ),
        (
            fixed_base_windows::Y_COLUMN,
            super::super::FIXED_WINDOW_Y_BASES,
            |entry| entry.y,
        ),
        (
            fixed_base_windows::U_COLUMN,
            super::super::FIXED_WINDOW_U_BASES,
            |entry| entry.u,
        ),
    ];
    let value =
        |seed: usize| <Fp>::from_u64((seed * 6_364_136_223 + 1_442_695_041) as u64).square();
    let fold_rows = parameters.repeated_coordinate_rows();
    for (family, (column_index, bases, coordinate)) in families.into_iter().enumerate() {
        let selection = &parameters.window_selections[family];
        assert_eq!(selection.column, column_index);
        assert_eq!(selection.windows.len(), FIXED_BASE_TOTAL_WINDOWS);

        // Recompute every base.
        let mut expected = Vec::with_capacity(FIXED_BASE_TOTAL_WINDOWS * 8);
        let mut flat = 0;
        for (region, _, window_count) in FIXED_BASE_REGIONS {
            let table = crate::native::witness::fixed_base_window_table(
                crate::test_codec::target().window_tables(),
                region,
            )
            .unwrap();
            assert_eq!(table.len(), window_count);
            for entries in table.iter() {
                let base = parameters.srs.lagrange_generators[rows[flat]].to_affine();
                for entry in entries.iter() {
                    expected.push(base.mul_projective(&coordinate(entry)));
                }
                flat += 1;
            }
        }
        let expected = normalized(&expected);
        for (index, point) in expected.iter().enumerate() {
            assert_eq!(
                point.as_affine().copied().unwrap(),
                bases[index],
                "window base {index} of column {column_index}"
            );
        }

        // Columns with table-selected cells (pseudo-random digits), a
        // constant fold run, one unmatched cell, and arbitrary elsewhere.
        let mut columns = Vec::new();
        for case in 0..3usize {
            let mut column = (0..N)
                .map(|row| value(row * 3 + case + family))
                .collect::<Vec<_>>();
            column[fold_rows.clone()].fill(value(1_000 + case));
            for (window, (row, values, _)) in selection.windows.iter().enumerate() {
                column[*row] = match case {
                    0 => <Fp>::ZERO,
                    _ => values[(window * 7 + case) % 8],
                };
            }
            if case == 2 {
                // One scheduled cell that matches no table entry stays dense.
                column[selection.windows[3].0] = value(77);
            }
            columns.push(SharedPoly::new(column));
        }
        let blinds = [<Fp>::ZERO, <Fp>::from_u64(17), value(99)];
        let dense = normalized(
            &parameters
                .commit_lagrange_batch_projective(
                    &columns.iter().zip(&blinds).collect::<Vec<_>>(),
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        let jobs = columns
            .iter()
            .zip(&blinds)
            .map(|(column, blind)| (column, blind, column_index))
            .collect::<Vec<_>>();
        let selected = normalized(
            &parameters
                .commit_advice_batch_projective(
                    &jobs,
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        assert_eq!(selected, dense);
        assert_eq!(
            parameters.window_selection_count(column_index, &columns[1]),
            532
        );
        assert_eq!(
            parameters.window_selection_count(column_index, &columns[2]),
            531
        );
    }
}

/// The two fixed-base running-sum streams (short and
/// base-field multipliers) cover the pinned cell count on distinct usable
/// rows of column 4, and column 4 committed through the three-bit word
/// transposition equals its dense commitment for: all-zero streams, valid
/// three-bit streams ending in a strict zero, streams with a nonzero
/// remainder, and arbitrary full-width cells — under arbitrary other
/// cells (the digit regions' cells included), tails, and blinds.
#[test]
fn transposed_fixed_base_running_sum_commitments_match_dense() {
    use crate::native::commitment::normalized;
    use crate::native::regions::{fixed_base_running_sums, fixed_base_windows};

    let pieces = fixed_base_running_sums::pieces();
    assert_eq!(pieces.len(), 2);
    assert_eq!(
        pieces.iter().map(|(_, rows)| rows.len()).sum::<usize>(),
        fixed_base_running_sums::WORD_COUNT
    );
    assert_eq!(fixed_base_running_sums::WORD_COUNT, 23 + 86);
    assert!(
        pieces
            .iter()
            .all(|(column, _)| *column == fixed_base_windows::SCALAR_COLUMN)
    );
    assert_eq!(fixed_base_running_sums::WORD_BITS, 3);

    let target = crate::test_codec::target();
    let parameters = target.parameters();
    let column_index = fixed_base_windows::SCALAR_COLUMN;
    let value =
        |seed: usize| <Fp>::from_u64((seed * 6_364_136_223 + 1_442_695_041) as u64).square();
    let radix = <Fp>::from_u64(8);
    let mut columns = Vec::new();
    for case in 0..4usize {
        let mut column = (0..N).map(|row| value(row * 11 + case)).collect::<Vec<_>>();
        for (piece, (_, rows)) in pieces.iter().enumerate() {
            match case {
                0 => column[rows.clone()].fill(<Fp>::ZERO),
                1 | 2 => {
                    let m = rows.len();
                    let word = |j: usize| <Fp>::from_u64(((j * 5 + piece * 3 + case) % 8) as u64);
                    // Case 1: strict zero endpoint (the writer's contract);
                    // case 2: a nonzero remainder past the last cell.
                    let mut z = if case == 2 {
                        <Fp>::from_u64((piece + 2) as u64)
                    } else {
                        <Fp>::ZERO
                    };
                    for j in (0..m).rev() {
                        z = word(j).add(&z.mul(&radix));
                        column[rows.start + j] = z;
                    }
                    if case == 1 {
                        // The final stored cell is the strict zero.
                        column[rows.end - 1] = <Fp>::ZERO;
                        let mut z = <Fp>::ZERO;
                        for j in (0..m - 1).rev() {
                            z = word(j).add(&z.mul(&radix));
                            column[rows.start + j] = z;
                        }
                    }
                }
                _ => {}
            }
        }
        columns.push(SharedPoly::new(column));
    }
    let blinds = [
        <Fp>::ZERO,
        <Fp>::from_u64(17),
        <Fp>::from_u64(23).square(),
        value(99),
    ];
    let dense = normalized(
        &parameters
            .commit_lagrange_batch_projective(
                &columns.iter().zip(&blinds).collect::<Vec<_>>(),
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap(),
    );
    let jobs = columns
        .iter()
        .zip(&blinds)
        .map(|(column, blind)| (column, blind, column_index))
        .collect::<Vec<_>>();
    let transposed = normalized(
        &parameters
            .commit_advice_batch_projective(
                &jobs,
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap(),
    );
    assert_eq!(transposed, dense);
}

/// The writer-derived nonzero constant inventory has the
/// expected size and lands on distinct usable rows; the eligible
/// (already-copied) columns are 0, 4, 5, 6, 7 and 9; and a column holding
/// its constants commits through the offset exactly as its dense
/// commitment, as does one with a mismatched constant cell (kept dense
/// with a correction) and one with every constant cell zero.
#[test]
fn constant_offset_commitments_match_dense() {
    use crate::native::commitment::normalized;
    use crate::native::regions::{constant_cells, variable_base_mul};

    let inventory = constant_cells::nonzero_constants();
    assert_eq!(inventory.len(), 12 + 2 + 31 + 89 + 35);
    let mut columns_seen = inventory
        .iter()
        .map(|(column, _, _)| *column)
        .collect::<Vec<_>>();
    columns_seen.sort_unstable();
    columns_seen.dedup();
    assert_eq!(columns_seen, alloc::vec![0, 3, 4, 5, 6, 7, 8, 9]);

    let target = crate::test_codec::target();
    let parameters = target.parameters();
    let mut eligible = parameters.constant_columns();
    eligible.sort_unstable();
    assert_eq!(
        eligible,
        alloc::vec![(0, 18), (4, 15), (5, 17), (6, 4), (7, 4), (9, 105)]
    );

    let value =
        |seed: usize| <Fp>::from_u64((seed * 6_364_136_223 + 1_442_695_041) as u64).square();
    for (column_index, _) in eligible {
        let cells = inventory
            .iter()
            .filter(|(column, _, _)| *column == column_index)
            .map(|(_, row, constant)| (*row, *constant))
            .collect::<Vec<_>>();
        let mut columns = Vec::new();
        let fold_rows = parameters.repeated_coordinate_rows();
        for case in 0..3usize {
            // Arbitrary elsewhere: the word, bit and selection carve-outs
            // are exact for any values; only the coordinate fold needs
            // its run constant.
            let mut column = (0..N)
                .map(|row| value(row * 23 + case + column_index))
                .collect::<Vec<_>>();
            if variable_base_mul::COORDINATE_COLUMNS.contains(&column_index) {
                column[fold_rows.clone()].fill(value(3_000 + case));
            }
            for &(row, constant) in &cells {
                column[row] = if case == 2 { <Fp>::ZERO } else { constant };
            }
            if case == 1 {
                column[cells[cells.len() / 2].0] = value(4_242);
            }
            columns.push(SharedPoly::new(column));
        }
        assert_eq!(parameters.constant_mismatches(column_index, &columns[0]), 0);
        assert_eq!(parameters.constant_mismatches(column_index, &columns[1]), 1);
        let blinds = [<Fp>::ZERO, <Fp>::from_u64(17), value(99)];
        let dense = normalized(
            &parameters
                .commit_lagrange_batch_projective(
                    &columns.iter().zip(&blinds).collect::<Vec<_>>(),
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        let jobs = columns
            .iter()
            .zip(&blinds)
            .map(|(column, blind)| (column, blind, column_index))
            .collect::<Vec<_>>();
        let folded = normalized(
            &parameters
                .commit_advice_batch_projective(
                    &jobs,
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        assert_eq!(folded, dense, "column {column_index}");
    }
}

/// The variable-base gadget's three binary chains cover 258
/// distinct usable cells of columns 9 and 6, and each column committed
/// through the chain transposition equals its dense commitment for:
/// all-zero chains, valid chains from pseudo-random bits with a zero
/// initial sum, valid chains with arbitrary (copied, full-width) initial
/// sums, and arbitrary full-width cells — under arbitrary other cells
/// (column 9's range streams included), tails, and blinds.
#[test]
fn transposed_variable_base_chain_commitments_match_dense() {
    use crate::native::commitment::normalized;
    use crate::native::regions::variable_base_mul;

    let chains = variable_base_mul::bit_chains();
    assert_eq!(chains.len(), 3);
    assert_eq!(
        chains.iter().map(|(_, rows)| rows.len()).sum::<usize>(),
        258
    );
    assert_eq!(chains[0].1.len(), 126);
    assert_eq!(chains[1].1.len(), 127);
    assert_eq!(chains[2].1.len(), 5);

    let target = crate::test_codec::target();
    let parameters = target.parameters();
    assert_eq!(parameters.bit_columns(), alloc::vec![9, 6]);
    let value =
        |seed: usize| <Fp>::from_u64((seed * 6_364_136_223 + 1_442_695_041) as u64).square();
    for &column_index in &[
        variable_base_mul::HI_Z_COLUMN,
        variable_base_mul::LO_Z_COLUMN,
    ] {
        let column_chains = chains
            .iter()
            .filter(|(column, _)| *column == column_index)
            .map(|(_, rows)| rows.iter().collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let mut columns = Vec::new();
        for case in 0..4usize {
            let mut column = (0..N)
                .map(|row| value(row * 19 + case + column_index))
                .collect::<Vec<_>>();
            for (chain, rows) in column_chains.iter().enumerate() {
                match case {
                    0 => {
                        for &row in rows {
                            column[row] = <Fp>::ZERO;
                        }
                    }
                    1 | 2 => {
                        let mut z = if case == 2 {
                            value(chain + 700)
                        } else {
                            <Fp>::ZERO
                        };
                        column[rows[0]] = z;
                        for (k, &row) in rows.iter().enumerate().skip(1) {
                            let bit = <Fp>::from_u64(((k * 7 + chain * 3 + case) % 2) as u64);
                            z = z.double().add(&bit);
                            column[row] = z;
                        }
                    }
                    _ => {}
                }
            }
            columns.push(SharedPoly::new(column));
        }
        let blinds = [
            <Fp>::ZERO,
            <Fp>::from_u64(17),
            <Fp>::from_u64(23).square(),
            value(99),
        ];
        let dense = normalized(
            &parameters
                .commit_lagrange_batch_projective(
                    &columns.iter().zip(&blinds).collect::<Vec<_>>(),
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        let jobs = columns
            .iter()
            .zip(&blinds)
            .map(|(column, blind)| (column, blind, column_index))
            .collect::<Vec<_>>();
        let transposed = normalized(
            &parameters
                .commit_advice_batch_projective(
                    &jobs,
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        assert_eq!(transposed, dense, "column {column_index}");
    }
}

/// The twenty range-check / canonicity streams cover the
/// pinned cell count on distinct usable rows of column 9, and column 9
/// committed through the ten-bit word transposition equals its dense
/// commitment for: all-zero streams, valid streams with zero final sums,
/// valid streams with large (≈124-bit) non-strict final quotients, and
/// arbitrary full-width cells — under arbitrary other cells, tails, and
/// blinds.
#[test]
fn transposed_range_running_sum_commitments_match_dense() {
    use crate::native::commitment::normalized;
    use crate::native::regions::range_running_sums;

    let pieces = range_running_sums::pieces();
    assert_eq!(pieces.len(), 20);
    assert_eq!(
        pieces.iter().map(|(_, rows)| rows.len()).sum::<usize>(),
        range_running_sums::WORD_COUNT
    );
    assert_eq!(range_running_sums::WORD_COUNT, 333);
    assert!(
        pieces
            .iter()
            .all(|(column, _)| *column == range_running_sums::COLUMN)
    );

    let target = crate::test_codec::target();
    let parameters = target.parameters();
    let column_index = range_running_sums::COLUMN;
    let value =
        |seed: usize| <Fp>::from_u64((seed * 6_364_136_223 + 1_442_695_041) as u64).square();
    let radix = <Fp>::from_u64(1 << range_running_sums::WORD_BITS);
    let mut columns = Vec::new();
    for case in 0..4usize {
        let mut column = (0..N).map(|row| value(row * 17 + case)).collect::<Vec<_>>();
        for (piece, (_, rows)) in pieces.iter().enumerate() {
            match case {
                0 => column[rows.clone()].fill(<Fp>::ZERO),
                1 | 2 => {
                    let m = rows.len();
                    let word = |j: usize| {
                        <Fp>::from_u64(((j * 613 + piece * 97 + case * 11) % 1024) as u64)
                    };
                    // The final stored cell is the stream's final sum
                    // `z_n = t`: zero in case 1, a large (≈124-bit)
                    // non-strict quotient in case 2; the cells before it
                    // are `z_j = d_j + B·z_{j+1}`.
                    let mut t = if case == 2 {
                        <Fp>::from_canonical_uint(value(piece + 500).to_canonical_uint().shr(130))
                            .unwrap()
                    } else {
                        <Fp>::ZERO
                    };
                    column[rows.end - 1] = t;
                    for j in (0..m - 1).rev() {
                        t = word(j).add(&t.mul(&radix));
                        column[rows.start + j] = t;
                    }
                }
                _ => {}
            }
        }
        columns.push(SharedPoly::new(column));
    }
    let blinds = [
        <Fp>::ZERO,
        <Fp>::from_u64(17),
        <Fp>::from_u64(23).square(),
        value(99),
    ];
    let dense = normalized(
        &parameters
            .commit_lagrange_batch_projective(
                &columns.iter().zip(&blinds).collect::<Vec<_>>(),
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap(),
    );
    let jobs = columns
        .iter()
        .zip(&blinds)
        .map(|(column, blind)| (column, blind, column_index))
        .collect::<Vec<_>>();
    let transposed = normalized(
        &parameters
            .commit_advice_batch_projective(
                &jobs,
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap(),
    );
    assert_eq!(transposed, dense);
}

/// The shared hash schedule covers exactly the pinned word
/// count over distinct usable rows of columns 2 and 7, and a word column
/// committed through the transposed word bases equals its dense Lagrange
/// commitment for: an all-zero column, valid ten-bit words with zero
/// remainders, valid words with nonzero remainders, and arbitrary
/// full-width cells (the transform is an identity, not a contract) —
/// each under arbitrary other cells, tails, and blinds, and mixed with
/// folded and dense jobs in one batch.
#[test]
fn transposed_sinsemilla_word_commitments_match_dense() {
    use crate::native::commitment::normalized;
    use crate::native::regions::sinsemilla_hashes;

    let pieces = sinsemilla_hashes::pieces();
    assert_eq!(pieces.len(), sinsemilla_hashes::PIECE_COUNT);
    assert_eq!(pieces.len(), 116);
    assert_eq!(
        pieces.iter().map(|(_, rows)| rows.len()).sum::<usize>(),
        sinsemilla_hashes::WORD_COUNT
    );
    assert_eq!(sinsemilla_hashes::WORD_COUNT, 1_933);
    let mut columns_seen = pieces.iter().map(|(column, _)| *column).collect::<Vec<_>>();
    columns_seen.sort_unstable();
    columns_seen.dedup();
    assert_eq!(
        columns_seen,
        sinsemilla_hashes::RUNNING_SUM_COLUMNS.to_vec()
    );
    assert_eq!(columns_seen, alloc::vec![2, 7]);

    let target = crate::test_codec::target();
    let parameters = target.parameters();
    assert_eq!(parameters.word_columns(), alloc::vec![2, 7, 4, 9]);
    let value =
        |seed: usize| <Fp>::from_u64((seed * 6_364_136_223 + 1_442_695_041) as u64).square();
    let radix = <Fp>::from_u64(1 << sinsemilla_hashes::WORD_BITS);

    for &word_column in &[2usize, 7] {
        let column_pieces = pieces
            .iter()
            .filter(|(column, _)| *column == word_column)
            .map(|(_, rows)| rows.clone())
            .collect::<Vec<_>>();
        // Case 0: all zero. Case 1: valid words, zero remainders.
        // Case 2: valid words, nonzero remainders. Case 3: arbitrary cells.
        let mut columns = Vec::new();
        for case in 0..4usize {
            let mut column = (0..N)
                .map(|row| value(row * 7 + case * 31 + word_column))
                .collect::<Vec<_>>();
            for (piece, rows) in column_pieces.iter().enumerate() {
                match case {
                    0 => column[rows.clone()].fill(<Fp>::ZERO),
                    1 | 2 => {
                        let m = rows.len();
                        let word = |j: usize| {
                            <Fp>::from_u64(((j * 613 + piece * 97 + case * 11) % 1024) as u64)
                        };
                        let mut z = if case == 2 {
                            <Fp>::from_u64((piece * 5 + 1) as u64)
                        } else {
                            <Fp>::ZERO
                        };
                        for j in (0..m).rev() {
                            z = word(j).add(&z.mul(&radix));
                            column[rows.start + j] = z;
                        }
                    }
                    _ => {}
                }
            }
            columns.push(SharedPoly::new(column));
        }
        let blinds = [
            <Fp>::ZERO,
            <Fp>::from_u64(17),
            <Fp>::from_u64(23).square(),
            value(99),
        ];
        let dense_jobs = columns.iter().zip(&blinds).collect::<Vec<_>>();
        let dense = normalized(
            &parameters
                .commit_lagrange_batch_projective(
                    &dense_jobs,
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        let jobs = columns
            .iter()
            .zip(&blinds)
            .map(|(column, blind)| (column, blind, word_column))
            .collect::<Vec<_>>();
        let transposed = normalized(
            &parameters
                .commit_advice_batch_projective(
                    &jobs,
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        assert_eq!(transposed, dense);

        // Mixed batch: the same columns as dense (column 4), folded
        // (column 0, so its coordinate run must be constant), and words.
        let rows = parameters.repeated_coordinate_rows();
        let mut folded_column = columns[3].to_vec();
        folded_column[rows].fill(value(5));
        let folded_column = SharedPoly::new(folded_column);
        let mixed_jobs = alloc::vec![
            (&columns[1], &blinds[1], word_column),
            (&columns[2], &blinds[2], 4usize),
            (&folded_column, &blinds[3], 0usize),
            (&columns[3], &blinds[0], word_column),
        ];
        let mixed = normalized(
            &parameters
                .commit_advice_batch_projective(
                    &mixed_jobs,
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        let mixed_dense = normalized(
            &parameters
                .commit_lagrange_batch_projective(
                    &[
                        (&columns[1], &blinds[1]),
                        (&columns[2], &blinds[2]),
                        (&folded_column, &blinds[3]),
                        (&columns[3], &blinds[0]),
                    ],
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        assert_eq!(mixed, mixed_dense);
    }
}

/// The prepared summed base equals the direct sum of the
/// Lagrange generators over the repeated-coordinate rows and is not the
/// identity; a folded advice column commits exactly as its dense
/// commitment for a zero, one, and arbitrary repeated value under
/// arbitrary other cells, tails, and blinds, alone and mixed with
/// unfolded jobs; a column whose run is not constant is rejected.
#[test]
fn folded_repeated_coordinate_commitments_match_dense() {
    use crate::native::curve::VestaProjective;

    let target = crate::test_codec::target();
    let parameters = target.parameters();
    let rows = parameters.repeated_coordinate_rows();
    assert_eq!(rows.len(), 126);
    let mut direct = VestaProjective::IDENTITY;
    for row in rows.clone() {
        direct = direct.add_mixed(&parameters.srs.lagrange_generators[row].to_affine());
    }
    let direct = normalized(&[direct]);
    let prepared = normalized(&[parameters.repeated_coordinate_base.mul(&<Fp>::ONE)]);
    assert!(direct[0].as_affine().is_some());
    assert_eq!(direct[0], prepared[0]);

    let values = [<Fp>::ZERO, <Fp>::ONE, <Fp>::from_u64(0xdead_beef).square()];
    let columns = values
        .iter()
        .enumerate()
        .map(|(job, value)| {
            let mut column = (0..N)
                .map(|row| <Fp>::from_u64((row * 13 + job * 977 + 3) as u64).square())
                .collect::<Vec<_>>();
            column[rows.clone()].fill(*value);
            SharedPoly::new(column)
        })
        .collect::<Vec<_>>();
    let blinds = [<Fp>::ZERO, <Fp>::from_u64(17), <Fp>::from_u64(23).square()];
    let dense_jobs = columns.iter().zip(&blinds).collect::<Vec<_>>();
    let dense = normalized(
        &parameters
            .commit_lagrange_batch_projective(
                &dense_jobs,
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap(),
    );
    // Columns 0 and 1 fold; column 4 is dense (its run cells commit as is).
    for pattern in [[0usize, 0, 0], [4, 4, 4], [0, 4, 1]] {
        let jobs = columns
            .iter()
            .zip(&blinds)
            .zip(pattern)
            .map(|((column, blind), index)| (column, blind, index))
            .collect::<Vec<_>>();
        let committed = normalized(
            &parameters
                .commit_advice_batch_projective(
                    &jobs,
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution(),
                )
                .unwrap(),
        );
        assert_eq!(committed, dense);
    }

    let mut broken = columns[2].to_vec();
    broken[rows.start + 5] = <Fp>::from_u64(9);
    let broken = SharedPoly::new(broken);
    assert!(
        parameters
            .commit_advice_batch_projective(
                &[(&broken, &blinds[0], 0)],
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution()
            )
            .is_err()
    );
    assert!(
        parameters
            .commit_advice_batch_projective(
                &[(&broken, &blinds[0], 4)],
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution()
            )
            .is_ok()
    );
}

/// A piecewise-constant column committed through the
/// prepared prefix-sum intervals must equal its dense Lagrange
/// commitment. Covers a single full-length run, adjacent equal-value
/// runs (a zero telescoped delta), singleton runs at both usable-prefix
/// boundaries, zero run values, and a zero blind.
#[test]
fn interval_commitments_match_dense_lagrange_commitments() {
    use super::super::{LagrangeCommitScalars, USABLE_ROWS_END};

    let target = crate::test_codec::target();

    let run_sets: Vec<Vec<(u32, Fp)>> = alloc::vec![
        alloc::vec![(0, <Fp>::from_u64(7))],
        alloc::vec![(0, <Fp>::ZERO), (1, <Fp>::from_u64(3)), (2_041, <Fp>::ONE)],
        alloc::vec![
            (0, <Fp>::from_u64(11)),
            (5, <Fp>::from_u64(11)),
            (100, <Fp>::ZERO),
            (700, <Fp>::from_u64(13).square()),
            (701, <Fp>::from_u64(13)),
        ],
    ];
    let columns = run_sets
        .iter()
        .enumerate()
        .map(|(job, runs)| {
            let mut column = alloc::vec![ <Fp>::ZERO; N];
            for (index, (start, value)) in runs.iter().enumerate() {
                let end = runs
                    .get(index + 1)
                    .map_or(USABLE_ROWS_END, |(next, _)| *next as usize);
                column[*start as usize..end].fill(*value);
            }
            for (offset, cell) in column[USABLE_ROWS_END..].iter_mut().enumerate() {
                *cell = <Fp>::from_u64((job * 977 + offset * 31 + 1) as u64).square();
            }
            SharedPoly::new(column)
        })
        .collect::<Vec<_>>();
    let blinds = [<Fp>::ZERO, <Fp>::from_u64(17), <Fp>::from_u64(23).square()];

    let mixed_jobs = run_sets
        .iter()
        .zip(&columns)
        .zip(&blinds)
        .map(|((runs, column), blind)| {
            (
                LagrangeCommitScalars::PiecewiseConstantPrefix {
                    runs: runs.as_slice(),
                    dense: column,
                },
                blind,
            )
        })
        .collect::<Vec<_>>();
    let mixed = target
        .parameters()
        .commit_lagrange_mixed_batch_projective(
            &mixed_jobs,
            &mut crate::native::commitment::MsmWorkspace::new(),
            crate::test_codec::execution(),
        )
        .unwrap();
    let mixed = crate::native::commitment::normalized(&mixed);

    let dense_jobs = columns.iter().zip(&blinds).collect::<Vec<_>>();
    let dense = target
        .parameters()
        .commit_lagrange_batch_projective(
            &dense_jobs,
            &mut crate::native::commitment::MsmWorkspace::new(),
            crate::test_codec::execution(),
        )
        .unwrap();
    let dense = crate::native::commitment::normalized(&dense);

    assert_eq!(mixed, dense);
}

#[test]
fn commitments_reject_the_wrong_polynomial_size() {
    let target = crate::test_codec::target();
    assert!(matches!(
        target.parameters().commit_lagrange_projective(
            &[<Fp>::ZERO],
            &<Fp>::ONE,
            &mut crate::native::commitment::MsmWorkspace::new(),
            crate::test_codec::execution()
        ),
        Err(TargetError::Dimension)
    ));
}

#[test]
fn lagrange_prefix_commitment_matches_zero_padded_commitment() {
    let parameters = crate::test_codec::target().parameters();
    let mut full = alloc::vec![<Fp>::ZERO; N];
    full[N - 1] = <Fp>::from_u64(29);
    let prefixes = [
        SharedPoly::new(Vec::new()),
        SharedPoly::new((1..=10).map(<Fp>::from_u64).collect::<Vec<_>>()),
        SharedPoly::new(full),
    ];
    let mut workspace = crate::native::commitment::MsmWorkspace::new();
    for blind in [<Fp>::ZERO, <Fp>::ONE, <Fp>::from_u64(17)] {
        let commitments = parameters
            .commit_lagrange_prefix_batch_projective(
                &prefixes,
                &blind,
                &mut workspace,
                crate::test_codec::execution(),
            )
            .unwrap();
        assert_eq!(commitments.len(), prefixes.len());
        for (prefix, commitment) in prefixes.iter().zip(commitments) {
            let mut padded = prefix.to_vec();
            padded.resize(N, <Fp>::ZERO);
            let dense = parameters
                .commit_lagrange_projective(
                    &padded,
                    &blind,
                    &mut workspace,
                    crate::test_codec::execution(),
                )
                .unwrap();
            assert_eq!(commitment.to_point(), dense.to_point());
        }
    }
    assert!(
        parameters
            .commit_lagrange_prefix_batch_projective(
                &[] as &[SharedPoly],
                &<Fp>::ONE,
                &mut workspace,
                crate::test_codec::execution(),
            )
            .unwrap()
            .is_empty()
    );

    let oversized = SharedPoly::new(alloc::vec![ <Fp>::ZERO; N + 1]);
    assert!(matches!(
        parameters.commit_lagrange_prefix_batch_projective(
            &[oversized],
            &<Fp>::ONE,
            &mut workspace,
            crate::test_codec::execution()
        ),
        Err(TargetError::Dimension)
    ));
}

/// The IPA mask commitment splits into a challenge-independent part
/// riding a coefficient piece batch (`Σ α_i·G_{2^i} + blind·W`) and a one-term
/// `x_3` correction `c·G_0` on the prepared first coefficient generator; the
/// sum is exactly the sparse commitment of the mask, including `x_3 = 0` and
/// `c = 0`, and the batch's dense outputs are unchanged by the extra job.
/// See [`crate::native::prover::IpaMaskEarly`] for the commitment split.
#[test]
fn hoisted_ipa_mask_parts_reproduce_the_sparse_commitment() {
    let target = crate::test_codec::target();
    let parameters = target.parameters();
    let mut state = 0x1357_9bdf_2468_ace0u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        <Fp>::from_u64(state).square()
    };
    for trial in 0..4 {
        let alphas = (0..K).map(|_| next()).collect::<Vec<_>>();
        let blind = next();
        let x_3 = if trial == 0 { <Fp>::ZERO } else { next() };
        let dense = SharedPoly::new((0..N).map(|_| next()).collect::<Vec<_>>());
        let dense_blind = next();
        let indices = Column::from((0..K).map(|exponent| 1u32 << exponent).collect::<Vec<_>>());
        let scalars = Arc::new(alphas.to_vec());
        let (dense_commitments, early) = parameters
            .commit_coefficients_batch_with_sparse_projective(
                &[(&dense, &dense_blind)],
                indices,
                scalars,
                &blind,
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap();
        assert_eq!(dense_commitments.len(), 1);
        assert_eq!(
            dense_commitments[0].to_point(),
            parameters
                .commit_coefficients_projective(
                    &dense,
                    &dense_blind,
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution()
                )
                .unwrap()
                .to_point()
        );

        let mut constant = <Fp>::ZERO;
        let mut power = x_3;
        let mut mask = Vec::with_capacity(K as usize + 1);
        mask.push((0, <Fp>::ZERO));
        for (exponent, alpha) in alphas.iter().enumerate() {
            constant = constant.sub(&alpha.mul(&power));
            mask.push((1usize << exponent, *alpha));
            power = power.square();
        }
        mask[0].1 = constant;
        let late = parameters
            .prepared_first_coefficient_generator()
            .mul(&constant);
        assert_eq!(
            early.add(&late).to_point(),
            parameters
                .commit_sparse_coefficients(
                    &mask,
                    &blind,
                    &mut crate::native::commitment::MsmWorkspace::new(),
                    crate::test_codec::execution()
                )
                .unwrap()
        );
    }
    // The empty and out-of-range sparse selections are rejected before any
    // arithmetic.
    let empty = Column::from(Vec::<u32>::with_capacity(0));
    let no_scalars = Arc::new(Vec::with_capacity(0));
    assert!(
        parameters
            .commit_coefficients_batch_with_sparse_projective(
                &[],
                empty,
                no_scalars,
                &<Fp>::ONE,
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution()
            )
            .is_err()
    );
    let out_of_range = Column::from(alloc::vec![N as u32]);
    let one_scalar = Arc::new(alloc::vec![<Fp>::ONE]);
    assert!(
        parameters
            .commit_coefficients_batch_with_sparse_projective(
                &[],
                out_of_range,
                one_scalar,
                &<Fp>::ONE,
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution()
            )
            .is_err()
    );
}
