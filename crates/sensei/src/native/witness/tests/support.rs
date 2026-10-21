//! Assignment kinds, support masks, serial ordering, and shadow-writer agreement.

use crate::native::test_support::reduced_values;

use alloc::vec::Vec;

use crate::{Error, native::field::Fp};

use super::super::writer::AssignmentKind;
use super::super::{AdviceValue, RowMap, WitnessWriter};

#[test]
fn writer_preserves_assignment_kinds_and_finalizes_rationals() {
    let mut writer = WitnessWriter::with_shadow();
    writer
        .write_region_advice(RowMap::load(), 0, 297, 0, AdviceValue::AssignedZero)
        .unwrap();
    writer
        .write_advice(0, 1, AdviceValue::Direct(<Fp>::from_u64(2)))
        .unwrap();
    writer
        .write_advice(
            0,
            2,
            AdviceValue::Rational {
                numerator: <Fp>::from_u64(6),
                denominator: <Fp>::from_u64(3),
            },
        )
        .unwrap();
    writer
        .write_advice(
            0,
            4,
            AdviceValue::Rational {
                numerator: <Fp>::ZERO,
                denominator: <Fp>::from_u64(5),
            },
        )
        .unwrap();
    writer
        .write_advice(1, 0, AdviceValue::Direct(<Fp>::from_u64(9)))
        .unwrap();
    writer
        .write_advice(
            1,
            1,
            AdviceValue::Rational {
                numerator: <Fp>::from_u64(35),
                denominator: <Fp>::from_u64(7),
            },
        )
        .unwrap();
    assert_eq!(
        writer.assignment_kind(0, 0),
        Some(AssignmentKind::AssignedZero)
    );
    assert_eq!(writer.assignment_kind(0, 1), Some(AssignmentKind::Direct));
    assert_eq!(writer.assignment_kind(0, 2), Some(AssignmentKind::Rational));
    assert_eq!(
        writer.assignment_kind(0, 3),
        Some(AssignmentKind::Unassigned)
    );
    let matrix = writer.finish().unwrap().into_matrix().unwrap();
    assert_eq!((matrix.columns()[0][0]).reduce(), (<Fp>::ZERO).reduce());
    assert_eq!(
        (matrix.columns()[0][1]).reduce(),
        (<Fp>::from_u64(2)).reduce()
    );
    assert_eq!(
        (matrix.columns()[0][2]).reduce(),
        (<Fp>::from_u64(2)).reduce()
    );
    assert_eq!((matrix.columns()[0][3]).reduce(), (<Fp>::ZERO).reduce());
    assert_eq!((matrix.columns()[0][4]).reduce(), (<Fp>::ZERO).reduce());
    assert_eq!(
        (matrix.columns()[1][0]).reduce(),
        (<Fp>::from_u64(9)).reduce()
    );
    assert_eq!(
        (matrix.columns()[1][1]).reduce(),
        (<Fp>::from_u64(5)).reduce()
    );
}

#[test]
fn writer_rejects_bad_assignments() {
    let mut duplicate = WitnessWriter::with_shadow();
    duplicate
        .write_advice(0, 0, AdviceValue::Direct(<Fp>::ZERO))
        .unwrap();
    assert_eq!(
        duplicate.write_advice(0, 0, AdviceValue::AssignedZero),
        Err(Error::InternalInvariant)
    );

    let mut zero_denominator = WitnessWriter::with_shadow();
    zero_denominator
        .write_advice(
            0,
            0,
            AdviceValue::Rational {
                numerator: <Fp>::ONE,
                denominator: <Fp>::ZERO,
            },
        )
        .unwrap();
    assert!(matches!(
        zero_denominator.finish(),
        Err(Error::UnsatisfiedWitness)
    ));
}

#[test]
fn parallel_action_witnesses_match_serial_order() {
    use crate::types::ProvingRequest;

    const FIXTURE: &[u8] = crate::test_codec::FIXTURES[1].request;

    let request = ProvingRequest::decode_iwpr_for_test(FIXTURE).unwrap();
    let serial = request
        .actions()
        .iter()
        .map(|action| {
            super::super::build_native_witness(action)
                .and_then(super::super::NativeWitness::into_matrix)
        })
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let parallel = super::super::build_action_witness_matrices(
        crate::test_codec::target(),
        crate::test_codec::execution(),
        request.actions(),
        &request.native_statements(),
    )
    .unwrap();

    assert_eq!(parallel.len(), serial.len());
    for (parallel, serial) in parallel.iter().zip(&serial) {
        assert_eq!(
            reduced_values(&(parallel.columns())),
            reduced_values(&(serial.columns()))
        );
    }
}

/// Advice structural support derives from the fixed writer
/// schedule. Assignment positions and kinds must be witness-independent —
/// identical for every Action of both fixtures — and no writer assignment
/// may touch the blinding tail.
#[test]
fn advice_structural_support_census() {
    use crate::{
        native::target::{ADVICE_COLUMNS, N, USABLE_ROWS_END},
        types::ProvingRequest,
    };

    const ONE_ACTION: &[u8] = crate::test_codec::FIXTURES[0].request;
    const TWO_ACTION: &[u8] = crate::test_codec::FIXTURES[1].request;

    let mut grids = Vec::new();
    let mut witnesses = Vec::new();
    for fixture in [ONE_ACTION, TWO_ACTION] {
        let request = ProvingRequest::decode_iwpr_for_test(fixture).unwrap();
        for action in request.actions() {
            let writer = super::super::write_native_witness_into(
                action,
                &action.statement.native(),
                WitnessWriter::with_shadow(),
            )
            .unwrap();
            let grid = (0..ADVICE_COLUMNS)
                .map(|column| {
                    (0..N)
                        .map(|row| writer.assignment_kind(column, row).unwrap())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            grids.push(grid);
            witnesses.push(writer.finish().unwrap());
        }
    }
    assert_eq!(grids.len(), 3);

    // Assignment positions are witness-independent: the support mask
    // (which cells are written at all) is identical for every Action.
    // Assignment kinds are not: a cell may be written directly for one
    // witness and rationally for another, so kinds are compared per cell
    // and only their stable portion is censused.
    let mask = |grid: &Vec<Vec<AssignmentKind>>| {
        grid.iter()
            .map(|column| {
                column
                    .iter()
                    .map(|&kind| kind != AssignmentKind::Unassigned)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    };
    let support_mask = mask(&grids[0]);
    for grid in &grids[1..] {
        assert_eq!(mask(grid), support_mask);
    }
    for column in &support_mask {
        for &assigned in &column[USABLE_ROWS_END..] {
            assert!(!assigned);
        }
    }

    // Every witness carries the writer's bitmask as its support
    // mask, bit for bit the shadow-derived structural mask, with exactly one
    // written cell per assigned position (the schedule has no assigned-zero
    // cells, so the support count is the assignment count).
    for witness in &witnesses {
        for (column, mask_column) in support_mask.iter().enumerate() {
            for (row, &assigned) in mask_column.iter().enumerate() {
                assert_eq!(witness.support_bit(column, row), assigned);
            }
        }
        let support = witness
            .support
            .iter()
            .map(|word| word.count_ones() as usize)
            .sum::<usize>();
        assert_eq!(support, 16_077);
    }

    // Per-column counts of (assigned-zero, direct, rational, varying)
    // cells, where "varying" means the three Actions disagree on the
    // kind; the remainder of each column's 2048 rows is unassigned.
    let census = (0..ADVICE_COLUMNS)
        .map(|column| {
            let mut zero = 0usize;
            let mut direct = 0usize;
            let mut rational = 0usize;
            let mut varying = 0usize;
            for row in 0..N {
                let kind = grids[0][column][row];
                if grids[1..].iter().any(|grid| grid[column][row] != kind) {
                    varying += 1;
                } else {
                    match kind {
                        AssignmentKind::Unassigned => {}
                        AssignmentKind::AssignedZero => zero += 1,
                        AssignmentKind::Direct => direct += 1,
                        AssignmentKind::Rational => rational += 1,
                    }
                }
            }
            (zero, direct, rational, varying)
        })
        .collect::<Vec<_>>();
    let support = support_mask
        .iter()
        .map(|column| column.iter().filter(|&&assigned| assigned).count())
        .sum::<usize>();

    assert_eq!(support, 16_077);
    assert_eq!(
        census,
        // Each Sinsemilla hash writes its final word's three cells and
        // its closing y-cell as direct values from the one `z` inverse
        // (18 hashes on columns 0–4, 17 on columns 5–9). Each fixed-base
        // multiplication also reuses its final normalization to write
        // two direct cells (seven pairs on columns 2 and 3). The totals
        // per column are the structural support.
        alloc::vec![
            (0, 783, 974, 0),
            (0, 1_752, 0, 0),
            (0, 1_097, 637, 0),
            (0, 142, 1_610, 0),
            (0, 627, 1_121, 0),
            (0, 659, 1_068, 0),
            (0, 1_281, 20, 1),
            (0, 1_141, 148, 0),
            (0, 191, 1_053, 0),
            (0, 848, 924, 0),
        ]
    );
}

/// Replay both fixtures through the dense writer with the enum-cell shadow
/// attached. Every write and the finalized matrix are asserted identical
/// inside the writer itself; this test drives that comparison over the full
/// fixed schedule, including rational finalization in `finish` and recovery
/// of the dense columns in `into_matrix`.
#[test]
fn event_writer_matches_enum_shadow_on_fixtures() {
    use crate::types::ProvingRequest;

    const ONE_ACTION: &[u8] = crate::test_codec::FIXTURES[0].request;
    const TWO_ACTION: &[u8] = crate::test_codec::FIXTURES[1].request;

    for fixture in [ONE_ACTION, TWO_ACTION] {
        let request = ProvingRequest::decode_iwpr_for_test(fixture).unwrap();
        for action in request.actions() {
            let writer = super::super::write_native_witness_into(
                action,
                &action.statement.native(),
                WitnessWriter::with_shadow(),
            )
            .unwrap();
            writer.finish().unwrap().into_matrix().unwrap();
        }
    }
}
