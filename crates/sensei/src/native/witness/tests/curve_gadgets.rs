//! Curve gadget checks against scalar, affine, and complete-addition references.

use crate::native::test_support::reduced_values;

use alloc::vec::Vec;

use crate::native::fixed_columns::SINSEMILLA_TABLE_ROWS;
use crate::{
    Error,
    native::{
        curve::{PallasPoint, PallasProjective},
        field::{Fp, Fq},
    },
};

use super::super::fixed_base::FixedWindowAccumulator;
use super::super::variable_base::{
    IncompleteColumns, complete_addition_points, write_chained_complete_addition,
    write_incomplete_double_and_add,
};
use super::super::writer::AssignmentKind;
use super::super::{
    RowMap, SINSEMILLA_TABLE_INDEX_COLUMN, SINSEMILLA_TABLE_X_COLUMN, SINSEMILLA_TABLE_Y_COLUMN,
    WitnessWriter, write_complete_addition,
};

/// The typed generators used by the witness match the fixed lookup columns.
/// Check curve membership once over the table instead of once per hash word.
#[test]
fn sinsemilla_fixed_columns_hold_the_generator_table() {
    let target = crate::test_codec::target();
    let fixed = target.fixed_values();
    let generators = target.sinsemilla_generators();
    assert_eq!(generators.len(), SINSEMILLA_TABLE_ROWS);
    let indexes = &fixed[SINSEMILLA_TABLE_INDEX_COLUMN][..SINSEMILLA_TABLE_ROWS];
    let xs = &fixed[SINSEMILLA_TABLE_X_COLUMN][..SINSEMILLA_TABLE_ROWS];
    let ys = &fixed[SINSEMILLA_TABLE_Y_COLUMN][..SINSEMILLA_TABLE_ROWS];
    for (word, ((index, x), y)) in indexes.iter().zip(xs).zip(ys).enumerate() {
        assert_eq!(
            (*index).reduce(),
            (<Fp>::from_u64(word as u64)).reduce(),
            "generator index column disagrees at word {word}"
        );
        let point = PallasPoint::from_xy(x.reduce(), y.reduce())
            .filter(|point| !point.is_identity())
            .unwrap_or_else(|| panic!("generator at word {word} is not a curve point"));
        assert_eq!(point.as_affine(), Some(&generators[word]));
    }
}

#[test]
fn complete_addition_defers_nonzero_denominators_and_preserves_zero_cases() {
    let row_map = RowMap::load();
    let point = PallasPoint::GENERATOR;
    let (x, y) = point.coordinates().unwrap();
    let mut writer = WitnessWriter::with_shadow();

    assert_eq!(
        write_complete_addition(&mut writer, row_map, 297, &point, &point).unwrap(),
        point.mul_projective(&<Fq>::from_u64(2)).to_point()
    );
    let row = row_map.absolute_row(297, 0).unwrap();
    assert_eq!(
        writer.assignment_kind(4, row),
        Some(AssignmentKind::Rational)
    );
    assert_eq!(writer.assignment_kind(5, row), Some(AssignmentKind::Direct));
    assert_eq!(
        writer.assignment_kind(6, row),
        Some(AssignmentKind::Rational)
    );
    assert_eq!(
        writer.assignment_kind(7, row),
        Some(AssignmentKind::Rational)
    );
    assert_eq!(
        writer.assignment_kind(8, row),
        Some(AssignmentKind::Rational)
    );

    let matrix = writer.finish().unwrap().into_matrix().unwrap();
    let inverse_x = x.invert().unwrap();
    let inverse_two_y = y.double().invert().unwrap();
    assert_eq!(
        (matrix.columns()[4][row]).reduce(),
        (x.square().triple().mul(&inverse_two_y)).reduce()
    );
    assert_eq!((matrix.columns()[5][row]).reduce(), (<Fp>::ZERO).reduce());
    assert_eq!((matrix.columns()[6][row]).reduce(), (inverse_x).reduce());
    assert_eq!((matrix.columns()[7][row]).reduce(), (inverse_x).reduce());
    assert_eq!(
        (matrix.columns()[8][row]).reduce(),
        (inverse_two_y).reduce()
    );

    let inverse = point.neg();
    let mut writer = WitnessWriter::with_shadow();
    write_chained_complete_addition(
        &mut writer,
        row_map,
        297,
        0,
        [&point, &inverse, &PallasPoint::IDENTITY],
        true,
    )
    .unwrap();
    assert_eq!(writer.assignment_kind(5, row), Some(AssignmentKind::Direct));
    assert_eq!(writer.assignment_kind(8, row), Some(AssignmentKind::Direct));
    let matrix = writer.finish().unwrap().into_matrix().unwrap();
    assert_eq!((matrix.columns()[5][row]).reduce(), (<Fp>::ZERO).reduce());
    assert_eq!((matrix.columns()[8][row]).reduce(), (<Fp>::ZERO).reduce());
    assert_eq!(
        (matrix.columns()[2][row + 1]).reduce(),
        (<Fp>::ZERO).reduce()
    );
    assert_eq!(
        (matrix.columns()[3][row + 1]).reduce(),
        (<Fp>::ZERO).reduce()
    );
}

#[test]
fn complete_variable_base_batch_matches_scalar_recurrence() {
    use crate::native::regions::variable_base_mul::COMPLETE_BITS;

    // Include cancellation, doubling, identity inputs, and 2 * accumulator
    // cancelling the selected base. The oracle follows scalar coefficients
    // and multiplies each independently, rather than replaying point additions.
    let half = <Fq>::from_u64(2).invert().unwrap();
    let coefficients = [
        <Fq>::ZERO,
        <Fq>::ONE,
        <Fq>::ONE.neg(),
        <Fq>::from_u64(3),
        <Fq>::from_u64(3).neg(),
        half,
        half.neg(),
        <Fq>::from_u64(0xd6e8_feb8_6659_fd93).square(),
    ];
    for base_scalar in [1, 19] {
        let base = PallasPoint::GENERATOR
            .mul_projective(&<Fq>::from_u64(base_scalar))
            .to_point();
        for coefficient in coefficients {
            for pattern in 0..1 << (COMPLETE_BITS + 1) {
                let bits = core::array::from_fn(|index| pattern & (1 << index) != 0);
                let points = complete_addition_points(
                    base.as_affine().unwrap(),
                    base.double(),
                    base.mul_projective(&coefficient),
                    &bits,
                );
                let mut expected = [<Fq>::ZERO; 2 * COMPLETE_BITS + 3];
                expected[0] = <Fq>::from_u64(2);
                expected[1] = coefficient;
                let mut accumulator = coefficient;
                for (index, bit) in bits[..COMPLETE_BITS].iter().enumerate() {
                    let sign = if *bit { <Fq>::ONE } else { <Fq>::ONE.neg() };
                    expected[2 + 2 * index] = accumulator.add(&sign);
                    accumulator = accumulator.double().add(&sign);
                    expected[3 + 2 * index] = accumulator;
                }
                expected[2 * COMPLETE_BITS + 2] = if bits[COMPLETE_BITS] {
                    accumulator
                } else {
                    accumulator.sub(&<Fq>::ONE)
                };
                for (index, (point, scalar)) in points.iter().zip(expected).enumerate() {
                    assert_eq!(
                        *point,
                        base.mul_projective(&scalar).to_point(),
                        "base {base_scalar}, pattern {pattern}, point {index}"
                    );
                }
            }
        }
    }
}

#[test]
fn incomplete_variable_base_projective_writes_match_affine_reference() {
    let row_map = RowMap::load();
    let base = PallasPoint::GENERATOR;
    let mut reference = base.mul_projective(&<Fq>::from_u64(13)).to_point();
    let bits = [true, false, true, true, false, false, true, false];
    let mut writer = WitnessWriter::with_shadow();
    let mut z = <Fp>::ZERO;
    let result = write_incomplete_double_and_add(
        &mut writer,
        row_map,
        297,
        &base,
        &bits,
        base.mul_projective(&<Fq>::from_u64(13)),
        &mut z,
        IncompleteColumns {
            z: 9,
            x_a: 3,
            lambda_1: 4,
            lambda_2: 5,
        },
    )
    .unwrap();

    for index in 0..bits.len() {
        let row = row_map.absolute_row(297, index + 2).unwrap();
        let next = row_map.absolute_row(297, index + 3).unwrap();
        assert_eq!(
            writer.assignment_kind(4, row),
            Some(AssignmentKind::Rational)
        );
        assert_eq!(
            writer.assignment_kind(5, row),
            Some(AssignmentKind::Rational)
        );
        assert_eq!(
            writer.assignment_kind(3, next),
            Some(AssignmentKind::Rational)
        );
    }

    let matrix = writer.finish().unwrap().into_matrix().unwrap();
    let (base_x, base_y) = base.coordinates().unwrap();
    for (index, bit) in bits.iter().enumerate() {
        let row = index + 2;
        let (x_a, y_a) = reference.coordinates().unwrap();
        let selected_y = if *bit {
            base_y.into_loose()
        } else {
            base_y.neg()
        };
        let lambda_1 = y_a.sub(&selected_y).mul(&x_a.sub(base_x).invert().unwrap());
        let x_r = lambda_1.square().sub(x_a).sub(base_x);
        let lambda_2 = y_a
            .double()
            .mul(&x_a.sub(&x_r).invert().unwrap())
            .sub(&lambda_1);
        let x_new = lambda_2.square().sub(x_a).sub(&x_r);
        let y_new = lambda_2.mul_sub(&x_a.sub(&x_new), y_a);

        assert_eq!((matrix.columns()[4][row]).reduce(), (lambda_1).reduce());
        assert_eq!((matrix.columns()[5][row]).reduce(), (lambda_2).reduce());
        assert_eq!((matrix.columns()[3][row + 1]).reduce(), (x_new).reduce());
        reference = PallasPoint::from_xy(x_new.reduce(), y_new.reduce()).unwrap();
    }
    assert_eq!(
        reduced_values(&(matrix.columns()[4][bits.len() + 2])),
        reduced_values(reference.coordinates().unwrap().1)
    );
    assert_eq!(result.to_point(), reference);
}

#[test]
fn incomplete_variable_base_projective_writes_reject_zero_slope_denominator() {
    let base = PallasPoint::GENERATOR;
    // Equal or opposite inputs fail the first slope; B = -2A fails the
    // second slope even though A + B itself is nonidentity.
    for accumulator in [
        base.to_projective(),
        base.neg().to_projective(),
        base.mul_projective(&<Fq>::from_u64(2).invert().unwrap().neg()),
        PallasProjective::IDENTITY,
    ] {
        let mut writer = WitnessWriter::with_shadow();
        let mut z = <Fp>::ZERO;
        assert!(matches!(
            write_incomplete_double_and_add(
                &mut writer,
                RowMap::load(),
                297,
                &base,
                &[true],
                accumulator,
                &mut z,
                IncompleteColumns {
                    z: 9,
                    x_a: 3,
                    lambda_1: 4,
                    lambda_2: 5,
                },
            ),
            Err(Error::UnsatisfiedWitness)
        ));
    }
}

#[test]
fn fixed_window_coordinates_match_complete_addition() {
    let point = PallasPoint::GENERATOR;
    let added = point.mul_projective(&<Fq>::from_u64(2)).to_point();
    let (point_x, point_y) = point.coordinates().map(|(x, y)| (*x, *y)).unwrap();
    let (added_x, added_y) = added.coordinates().map(|(x, y)| (*x, *y)).unwrap();
    let mut accumulator =
        FixedWindowAccumulator::from_xy(point_x.into_loose(), point_y.into_loose());
    let mut writer = WitnessWriter::with_shadow();
    let mut expected = Vec::new();
    let mut sum = point;
    for row in 0..9 {
        accumulator
            .add_mixed_xy(&added_x.into_loose(), &added_y.into_loose())
            .unwrap();
        writer
            .write_rational_pair(
                [(2, row), (3, row)],
                [accumulator.x.mul(&accumulator.z), accumulator.y],
                accumulator.z_cubed,
            )
            .unwrap();
        sum = sum.add(&added).to_point();
        assert_eq!(accumulator.to_point().unwrap(), sum);
        expected.push(sum);
    }
    let matrix = writer.finish().unwrap().into_matrix().unwrap();
    for (row, point) in expected.iter().enumerate() {
        let (x, y) = point.coordinates().unwrap();
        assert_eq!(matrix.columns()[2][row].reduce(), *x);
        assert_eq!(matrix.columns()[3][row].reduce(), *y);
    }
}
