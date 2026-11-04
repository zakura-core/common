//! Deferred rational finalization, rejection, and reservation checks.

use alloc::vec::Vec;

use crate::{Error, native::field::Fp};

use super::super::writer::{AssignedCell, batch_finalize_rationals};
use super::super::{AdviceValue, WitnessWriter};

/// The zero-rejecting policy: a zero denominator anywhere rejects the
/// witness before any event is divided, and a log with no rationals is
/// returned unchanged.
#[test]
fn rational_finalize_rejects_zero_denominators_before_modifying_events() {
    let mut writer =
        WitnessWriter::new(crate::test_codec::target(), crate::test_codec::execution());
    writer
        .write_advice(0, 3, AdviceValue::Direct(<Fp>::from_u64(9)))
        .unwrap();
    writer
        .write_advice(
            1,
            4,
            AdviceValue::Rational {
                numerator: <Fp>::from_u64(6),
                denominator: <Fp>::from_u64(3),
            },
        )
        .unwrap();
    writer
        .write_advice(
            2,
            5,
            AdviceValue::Rational {
                numerator: <Fp>::from_u64(1),
                denominator: <Fp>::ZERO,
            },
        )
        .unwrap();
    assert_eq!(writer.finish().err(), Some(Error::UnsatisfiedWitness));

    let mut writer =
        WitnessWriter::new(crate::test_codec::target(), crate::test_codec::execution());
    writer
        .write_advice(0, 3, AdviceValue::Direct(<Fp>::from_u64(9)))
        .unwrap();
    let matrix = writer.finish().unwrap().into_matrix().unwrap();
    assert_eq!(
        (matrix.columns()[0][3]).reduce(),
        (<Fp>::from_u64(9)).reduce()
    );
}

/// A shared-denominator word divides its two slopes by `z` and its
/// x-coordinate by `z²` exactly as three independent rationals would
/// (the shadow oracle checks that per write), and a zero `z` rejects the
/// witness like any zero denominator.
#[test]
fn sinsemilla_word_shares_one_denominator_exactly() {
    let mut writer = WitnessWriter::with_shadow();
    let z = <Fp>::from_u64(0x0f0f_1234_5678);
    let numerators = [<Fp>::from_u64(3), <Fp>::from_u64(5), <Fp>::from_u64(7)];
    writer
        .write_incomplete_double_and_add([(3, 10), (4, 10), (0, 11)], numerators, z)
        .unwrap();
    writer
        .write_advice(
            7,
            20,
            AdviceValue::Rational {
                numerator: <Fp>::from_u64(11),
                denominator: <Fp>::from_u64(13),
            },
        )
        .unwrap();
    let matrix = writer.finish().unwrap().into_matrix().unwrap();
    let z_inverse = z.invert().unwrap();
    assert_eq!(
        (matrix.columns()[3][10]).reduce(),
        (numerators[0].mul(&z_inverse)).reduce()
    );
    assert_eq!(
        (matrix.columns()[4][10]).reduce(),
        (numerators[1].mul(&z_inverse)).reduce()
    );
    assert_eq!(
        (matrix.columns()[0][11]).reduce(),
        (numerators[2].mul(&z_inverse.square())).reduce()
    );
    assert_eq!(
        (matrix.columns()[7][20]).reduce(),
        (<Fp>::from_u64(11).mul(&<Fp>::from_u64(13).invert().unwrap())).reduce()
    );

    let mut writer = WitnessWriter::with_shadow();
    writer
        .write_incomplete_double_and_add([(3, 10), (4, 10), (0, 11)], numerators, <Fp>::ZERO)
        .unwrap();
    assert_eq!(writer.finish().err(), Some(Error::UnsatisfiedWitness));
}

#[test]
fn rational_pair_matches_independent_fractions() {
    let mut writer = WitnessWriter::with_shadow();
    let fractions = [
        (0, 3, <Fp>::ONE),
        (5, 0, <Fp>::ONE.neg()),
        (0, 0, <Fp>::from_u64(7)),
        (11, 13, <Fp>::from_u64(17)),
        (19, 23, <Fp>::from_u64(29)),
    ];
    let mut expected = Vec::new();
    for (row, (first, second, denominator)) in fractions.into_iter().enumerate() {
        let numerators = [<Fp>::from_u64(first), <Fp>::from_u64(second)];
        writer
            .write_rational_pair([(2, row), (3, row)], numerators, denominator)
            .unwrap();
        expected.push(numerators.map(|numerator| numerator.mul(&denominator.invert().unwrap())));
    }
    assert_eq!(writer.rationals.len(), fractions.len());
    writer
        .write_advice(
            7,
            20,
            AdviceValue::Rational {
                numerator: <Fp>::from_u64(31),
                denominator: <Fp>::from_u64(37),
            },
        )
        .unwrap();

    let matrix = writer.finish().unwrap().into_matrix().unwrap();
    for (row, [first, second]) in expected.into_iter().enumerate() {
        assert_eq!(matrix.columns()[2][row].reduce(), first.reduce());
        assert_eq!(matrix.columns()[3][row].reduce(), second.reduce());
    }
    assert_eq!(
        matrix.columns()[7][20].reduce(),
        <Fp>::from_u64(31)
            .mul(&<Fp>::from_u64(37).invert().unwrap())
            .reduce()
    );

    for numerators in [[<Fp>::ONE, <Fp>::ONE], [<Fp>::ZERO, <Fp>::ZERO]] {
        let mut writer = WitnessWriter::with_shadow();
        writer
            .write_rational_pair([(2, 0), (3, 0)], numerators, <Fp>::ZERO)
            .unwrap();
        assert_eq!(writer.finish().err(), Some(Error::UnsatisfiedWitness));
    }
}

#[test]
fn rational_pair_rejects_bad_assignments() {
    for cells in [
        [(2, 0), (2, 0)],
        [(2, 0), (3, crate::native::target::N)],
        [(crate::native::target::ADVICE_COLUMNS, 0), (3, 0)],
    ] {
        let mut writer = WitnessWriter::with_shadow();
        assert_eq!(
            writer.write_rational_pair(cells, [<Fp>::ONE; 2], <Fp>::ONE),
            Err(Error::InternalInvariant)
        );
    }
}

#[test]
fn rational_batch_matches_independent_inversion() {
    let mut writer = WitnessWriter::with_shadow();
    let fractions = [
        (0, 0, 2, 3),
        (0, 17, 5, 7),
        (4, 1024, 0, 11),
        (9, crate::native::target::N - 1, 13, 17),
    ];
    let mut expected = Vec::new();

    for (column, row, numerator, denominator) in fractions {
        let numerator = <Fp>::from_u64(numerator);
        let denominator = <Fp>::from_u64(denominator);
        expected.push((column, row, numerator.mul(&denominator.invert().unwrap())));
        writer
            .write_advice(
                column,
                row,
                AdviceValue::Rational {
                    numerator,
                    denominator,
                },
            )
            .unwrap();
    }

    let matrix = writer.finish().unwrap().into_matrix().unwrap();
    for (column, row, expected) in expected {
        assert_eq!(
            (matrix.columns()[column][row]).reduce(),
            (expected).reduce()
        );
    }
}

#[test]
fn rational_batch_rejects_zero_before_materializing_cells() {
    let mut cells = alloc::vec![
        alloc::vec![AssignedCell::Rational {
            numerator: <Fp>::from_u64(6),
            denominator: <Fp>::from_u64(3),
        }],
        alloc::vec![AssignedCell::Rational {
            numerator: <Fp>::ONE,
            denominator: <Fp>::ZERO,
        }],
    ];

    assert_eq!(
        batch_finalize_rationals(&mut cells),
        Err(Error::UnsatisfiedWitness)
    );
    assert!(matches!(cells[0][0], AssignedCell::Rational { .. }));
    assert!(matches!(cells[1][0], AssignedCell::Rational { .. }));
}

/// The rational-log reservation is derived from the grouped schedule: on
/// both fixtures every Action's log fits without growing and fills more
/// than half of the reservation, so the hint is neither short nor twice
/// the schedule.
#[test]
fn rational_log_reservation_covers_the_grouped_schedule() {
    use crate::types::ProvingRequest;

    for fixture in [
        crate::test_codec::FIXTURES[0].request,
        crate::test_codec::FIXTURES[1].request,
    ] {
        let parsed = ProvingRequest::decode_iwpr_for_test(fixture).unwrap();
        for action in parsed.actions() {
            let writer = super::super::write_native_witness(
                crate::test_codec::target(),
                crate::test_codec::execution(),
                action,
                &action.statement.native(),
            )
            .unwrap();
            let entries = writer.rationals.len();
            assert!(
                entries <= super::super::writer::RATIONAL_CAPACITY
                    && writer.rationals.capacity() == super::super::writer::RATIONAL_CAPACITY,
                "the rational log grew past its reservation: {entries} entries"
            );
            assert!(
                entries > super::super::writer::RATIONAL_CAPACITY / 2,
                "the rational-log reservation is more than twice the schedule: {entries} entries"
            );
        }
    }
}
