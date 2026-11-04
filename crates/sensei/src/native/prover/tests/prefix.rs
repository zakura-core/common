//! Transcript-prefix determinism and advice commitment equivalence.

use super::{ONE_ACTION_FIXTURE, TWO_ACTION_FIXTURE};
use crate::native::prover::{self, ProverPrefix};
use crate::types::ProvingRequest;
use alloc::vec::Vec;

#[test]
fn fixed_vk_and_instance_prefix_is_deterministic() {
    for fixture in [ONE_ACTION_FIXTURE, TWO_ACTION_FIXTURE] {
        let request = ProvingRequest::decode_iwpr_for_test(fixture).unwrap();
        let mut first_workspace = crate::native::ProverWorkspace::new();
        let mut first = ProverPrefix::initialize(
            crate::test_codec::target(),
            &mut first_workspace,
            crate::test_codec::execution(),
            &request,
            &request.native_statements(),
        )
        .unwrap();
        let mut second_workspace = crate::native::ProverWorkspace::new();
        let mut second = ProverPrefix::initialize(
            crate::test_codec::target(),
            &mut second_workspace,
            crate::test_codec::execution(),
            &request,
            &request.native_statements(),
        )
        .unwrap();
        assert_eq!(first.instance_polynomials.len(), request.action_count());
        assert!(first.transcript().proof().is_empty());
        assert_eq!(
            (first.transcript.squeeze_challenge()).reduce(),
            (second.transcript.squeeze_challenge()).reduce()
        );
    }
}

/// On the real writer output, in every fixture Action,
/// each coordinate column of the variable-base gadget holds one constant
/// run on the shared footprint's rows, every scheduled Sinsemilla
/// running-sum cell is assigned (the transforms' structural premises),
/// and every advice column's planned commitment — folded, transposed, or
/// dense — under arbitrary tail masks and blind equals its dense
/// commitment.
#[test]
fn structured_advice_commitments_match_dense_on_fixtures() {
    use crate::native::regions::{fixed_base_windows, sinsemilla_hashes, variable_base_mul};
    use crate::native::{commitment::normalized, witness};
    use prover::{ADVICE_COLUMNS, ASSIGNED_WORDS_PER_COLUMN, Fp, N, USABLE_ROWS_END};

    let target = crate::test_codec::target();
    let rows = target.parameters().repeated_coordinate_rows();
    assert_eq!(
        rows.len(),
        prover::inventory::advice_stage::FOLDED_RUN_CELLS
    );
    assert!(rows.end <= USABLE_ROWS_END);
    assert_eq!(
        target.parameters().word_columns(),
        sinsemilla_hashes::RUNNING_SUM_COLUMNS
            .iter()
            .copied()
            .chain([
                fixed_base_windows::SCALAR_COLUMN,
                crate::native::regions::range_running_sums::COLUMN,
            ])
            .collect::<Vec<_>>()
    );
    let value =
        |seed: usize| <Fp>::from_u64((seed * 2_862_933_555 + 3_037_000_493) as u64).square();
    for fixture in [ONE_ACTION_FIXTURE, TWO_ACTION_FIXTURE] {
        let request = ProvingRequest::decode_iwpr_for_test(fixture).unwrap();
        let (matrices, _feeds) = witness::build_native_witness_matrices(
            crate::test_codec::target(),
            crate::test_codec::execution(),
            &request,
            &request.native_statements(),
            &crate::native::prover::LookupWorkspace::default(),
        )
        .unwrap();
        for (action, matrix) in matrices.iter().enumerate() {
            for &column_index in &variable_base_mul::COORDINATE_COLUMNS {
                let run = &matrix.columns[column_index][rows.clone()];
                assert!(run.iter().all(|cell| (cell).reduce() == (run[0]).reduce()));
                assert_ne!((run[0]).reduce(), (<Fp>::ZERO).reduce());
            }
            for (column, piece_rows) in sinsemilla_hashes::pieces() {
                for row in piece_rows {
                    let word = matrix.support[column * ASSIGNED_WORDS_PER_COLUMN + row / 64];
                    assert!(word >> (row % 64) & 1 == 1, "unassigned running sum");
                }
            }
            // Every fixed-base window's x and y cells are table entries.
            for column in [
                fixed_base_windows::X_COLUMN,
                fixed_base_windows::Y_COLUMN,
                fixed_base_windows::U_COLUMN,
            ] {
                assert_eq!(
                    target
                        .parameters()
                        .window_selection_count(column, &matrix.columns[column]),
                    532
                );
            }
            for column_index in 0..ADVICE_COLUMNS {
                // Every writer constant holds on the real witness.
                assert_eq!(
                    target
                        .parameters()
                        .constant_mismatches(column_index, &matrix.columns[column_index]),
                    0,
                    "column {column_index}"
                );
                let mut column = matrix.columns[column_index].clone();
                assert_eq!(column.len(), N);
                for (offset, cell) in column[USABLE_ROWS_END..].iter_mut().enumerate() {
                    *cell = value(action * 10_007 + column_index * 977 + offset * 31 + 1);
                }
                let column = prover::SharedPoly::new(column);
                let blind = value(action * 31 + column_index + 5);
                let planned = target
                    .parameters()
                    .commit_advice_batch_projective(
                        &[(&column, &blind, column_index)],
                        &mut crate::native::commitment::MsmWorkspace::new(),
                        crate::test_codec::execution(),
                    )
                    .unwrap();
                let dense = target
                    .parameters()
                    .commit_lagrange_projective(
                        &column,
                        &blind,
                        &mut crate::native::commitment::MsmWorkspace::new(),
                        crate::test_codec::execution(),
                    )
                    .unwrap();
                let mut points = normalized(&[planned[0], dense]).into_iter();
                let planned = points.next().unwrap();
                let dense = points.next().unwrap();
                assert_eq!(planned, dense, "column {column_index}");
            }
        }
    }
}
