//! Frozen row-map bounds, assignment footprints, and advice-value census.

use alloc::vec::Vec;
use sensei_shared::regions::FROZEN_REGION_COUNT;

use crate::{Error, native::field::Fp};

use super::super::writer::AssignmentKind;
use super::super::{RowMap, WitnessWriter};

#[test]
fn embedded_row_map_is_canonical_and_bounded() {
    let row_map = RowMap::load();
    assert_eq!(row_map.region_starts().len(), FROZEN_REGION_COUNT);
    assert!(
        row_map
            .region_starts()
            .iter()
            .all(|row| *row < crate::native::target::N)
    );
    assert_eq!(row_map.absolute_row(297, 4).unwrap(), 4);
    assert_eq!(
        row_map.absolute_row(FROZEN_REGION_COUNT, 0),
        Err(Error::InternalInvariant)
    );
    assert_eq!(
        row_map.absolute_row(0, crate::native::target::N),
        Err(Error::InternalInvariant)
    );
}

/// The named layout groups' actual footprints, from the cells the writer
/// assigns (via the shadow oracle), not from adjacent region starts: each
/// top-level input occupies local row 0 of its region in column 0 (points
/// also column 1); the statement row fills columns 0..8 of one row; the
/// cross-address group fills all ten columns of four consecutive rows.
/// Witness-independent, so one Action of one fixture suffices.
#[test]
fn witness_layout_footprints() {
    use crate::native::regions::{REGION_STARTS, roles};
    use crate::{native::target::ADVICE_COLUMNS, types::ProvingRequest};

    const ONE_ACTION: &[u8] = crate::test_codec::FIXTURES[0].request;
    let request = ProvingRequest::decode_iwpr_for_test(ONE_ACTION).unwrap();
    let action = &request.actions()[0];
    let writer = super::super::write_native_witness_into(
        action,
        &action.statement.native(),
        WitnessWriter::with_shadow(),
    )
    .unwrap();
    let assigned = |column: usize, row: usize| {
        writer.assignment_kind(column, row).unwrap() != AssignmentKind::Unassigned
    };

    for (region, columns) in [
        (roles::PSI_OLD, 1),
        (roles::RHO_OLD, 1),
        (roles::CM_OLD, 2),
        (roles::G_D_OLD, 2),
        (roles::AK, 2),
        (roles::NK, 1),
        (roles::V_OLD, 1),
        (roles::V_NEW, 1),
        (roles::PK_D_OLD, 2),
        (roles::G_D_NEW, 2),
        (roles::PK_D_NEW, 2),
        (roles::PSI_NEW, 1),
    ] {
        let row = REGION_STARTS[region];
        for column in 0..columns {
            assert!(assigned(column, row), "region {region} column {column}");
        }
    }
    for region in [roles::VALUE_MAGNITUDE, roles::VALUE_SIGN] {
        assert!(assigned(9, REGION_STARTS[region]), "region {region}");
    }

    let statement_row = REGION_STARTS[roles::STATEMENT_ROW];
    for column in 0..8 {
        assert!(assigned(column, statement_row), "statement column {column}");
    }
    for column in 8..ADVICE_COLUMNS {
        assert!(
            !assigned(column, statement_row),
            "statement column {column}"
        );
    }
    let cross_start = REGION_STARTS[roles::CROSS_ADDRESS_ROWS];
    for local_row in 0..4 {
        for column in 0..ADVICE_COLUMNS {
            assert!(
                assigned(column, cross_start + local_row),
                "cross-address row {local_row} column {column}"
            );
        }
    }
}

/// How much of the advice matrix is
/// witness-independent, i.e. template-eligible?
///
/// The structural audit of the writer schedule finds exactly 22
/// unconditionally constant cells — region 394's four relation rows
/// (columns 1 = 0 and 3, 6, 7 = 1) and the Poseidon initial states in
/// regions 271 and 272 (columns 6, 7 = 0, column 8 = 2^65). Every other
/// written value flows from action data. This test pins that audit
/// (values asserted on every fixture Action) alongside the sampling upper
/// bound and the semantic zero/one densities, which document why
/// classification by sampling would overcount wildly: the fixtures'
/// shared dummy-spend structure makes thousands of witness-dependent
/// cells coincidentally agree.
#[test]
fn advice_value_classification_census() {
    use crate::{
        native::target::{ADVICE_COLUMNS, N},
        types::ProvingRequest,
    };

    const ONE_ACTION: &[u8] = crate::test_codec::FIXTURES[0].request;
    const TWO_ACTION: &[u8] = crate::test_codec::FIXTURES[1].request;

    let mut supports = Vec::new();
    let mut matrices = Vec::new();
    for fixture in [ONE_ACTION, TWO_ACTION] {
        let request = ProvingRequest::decode_iwpr_for_test(fixture).unwrap();
        for action in request.actions() {
            let witness = super::super::build_native_witness(action).unwrap();
            supports.push(
                (0..ADVICE_COLUMNS)
                    .map(|column| {
                        (0..N)
                            .map(|row| witness.support_bit(column, row))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>(),
            );
            matrices.push(witness.into_matrix().unwrap());
        }
    }
    assert_eq!(matrices.len(), 3);
    for support in &supports[1..] {
        assert_eq!(*support, supports[0]);
    }
    let support = &supports[0];

    // The audited writer-schedule constants, verified on every Action.
    let row_map = RowMap::load();
    let mut audited = Vec::new();
    for local_row in 0..4 {
        let row = row_map.absolute_row(394, local_row).unwrap();
        audited.push((1, row, <Fp>::ZERO));
        for column in [3, 6, 7] {
            audited.push((column, row, <Fp>::ONE));
        }
    }
    for region in [271, 272] {
        let row = row_map.absolute_row(region, 0).unwrap();
        audited.push((6, row, <Fp>::ZERO));
        audited.push((7, row, <Fp>::ZERO));
        audited.push((8, row, super::super::power_of_two(65)));
    }
    assert_eq!(audited.len(), 22);
    for &(column, row, expected) in &audited {
        assert!(support[column][row]);
        for matrix in &matrices {
            assert_eq!(
                (matrix.columns()[column][row]).reduce(),
                (expected).reduce()
            );
        }
    }

    // Sampling upper bound and semantic value densities over the support:
    // cells whose values agree across all three fixture Actions, and each
    // Action's zero- and one-valued cell counts. These are properties of
    // the frozen fixtures, not of the circuit — they bound observed
    // agreement without establishing that any unaudited cell is constant.
    let mut sampled_agreement = 0usize;
    let mut zeros = [0usize; 3];
    let mut ones = [0usize; 3];
    for (column, support_column) in support.iter().enumerate() {
        for (row, &assigned) in support_column.iter().enumerate() {
            if !assigned {
                continue;
            }
            let value = matrices[0].columns()[column][row];
            if matrices[1..]
                .iter()
                .all(|matrix| (matrix.columns()[column][row]).reduce() == (value).reduce())
            {
                sampled_agreement += 1;
            }
            for (matrix, counts) in matrices.iter().zip(zeros.iter_mut()) {
                if matrix.columns()[column][row].is_zero() {
                    *counts += 1;
                }
            }
            for (matrix, counts) in matrices.iter().zip(ones.iter_mut()) {
                if (matrix.columns()[column][row]).reduce() == (<Fp>::ONE).reduce() {
                    *counts += 1;
                }
            }
        }
    }
    assert_eq!(
        (sampled_agreement, zeros, ones),
        (908, [300, 300, 318], [117, 117, 101])
    );
}
