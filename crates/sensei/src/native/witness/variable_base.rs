//! Variable-base scalar multiplication and its running-sum/overflow witnesses.
//!
//! Incomplete additions keep projective coordinates and emit rational cells for
//! the writer to finalize. Complete-addition points share one normalization
//! batch before their boundary rows are written.

use crate::Error;
use crate::native::curve::{PallasAffine, PallasPoint, PallasProjective, batch_normalize};
use crate::native::field::{CanonicalUint, Fp, Fq};
use crate::native::regions::variable_base_mul::COMPLETE_BITS;

use super::decomposition::write_scheduled_running_sum;
use super::writer::{AdviceValue, RowMap, WitnessWriter};
use super::{
    T_Q, complete_addition_rationals, point_coordinates, point_coordinates_or_zero, power_of_two,
    rational_or_zero, running_sum_at, write_direct, write_region_cells,
};

/// Writes the fixed sequence of incomplete and complete double-and-add rows
/// for a variable base, followed by the scalar overflow witnesses.
pub(super) fn write_variable_base_mul(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    base: &PallasPoint,
    scalar: &Fp,
) -> Result<PallasPoint, Error> {
    use crate::native::regions::variable_base_mul::{
        COORDINATE_COLUMNS, HI_Z_COLUMN, INCOMPLETE_HI_BITS, INCOMPLETE_LO_BITS, LO_Z_COLUMN,
        REGION, bit_chains, coordinate_rows,
    };

    let scalar = <Fq>::from_bytes(scalar.to_bytes()).ok_or(Error::InternalInvariant)?;
    let k = scalar_to_k(&scalar)?;
    let bits = variable_base_bits(k)?;

    let base_affine = base.as_affine().ok_or(Error::InternalInvariant)?;
    // The incomplete chains consume projective coordinates. Their initial
    // affine cells can wait for the same normalization batch as the tail.
    let initial_accumulator = base.double();
    let mut accumulator = initial_accumulator;

    // The shared chain footprint must describe exactly the rows written
    // below: hi chain (initial zero at local row 1, 125 sums), lo chain
    // (handoff copy at local row 1, 126 sums), tail (handoff copy, three
    // complete bits, final bit).
    let chains = bit_chains();
    let start = row_map.absolute_row(REGION, 0)?;
    if chains[0].0 != HI_Z_COLUMN
        || !chains[0]
            .1
            .iter()
            .eq((1..=INCOMPLETE_HI_BITS + 1).map(|row| start + row))
        || chains[1].0 != LO_Z_COLUMN
        || !chains[1]
            .1
            .iter()
            .eq((1..=INCOMPLETE_LO_BITS + 1).map(|row| start + row))
        || chains[2].0 != HI_Z_COLUMN
        || chains[2].1.len() != COMPLETE_BITS + 2
    {
        return Err(Error::InternalInvariant);
    }
    let mut z = <Fp>::ZERO;
    write_direct(writer, row_map, HI_Z_COLUMN, REGION, 1, z)?;

    // Base input coordinates for every double-and-add row. The hi and lo
    // chains cover rows 2..=126 and 2..=127 with the same two values, so each
    // cell is written exactly once here instead of deduplicating overlapping
    // per-chain writes (the former `RegionPlan` map). The rows and columns
    // come from the shared footprint so the advice commitment can fold each
    // run into one term over the summed generators.
    let (base_x, base_y) = point_coordinates(base)?;
    let rows = coordinate_rows();
    if rows.start != row_map.absolute_row(REGION, 2)? {
        return Err(Error::InternalInvariant);
    }
    let [x_column, y_column] = COORDINATE_COLUMNS;
    for row in rows {
        writer.write_advice(x_column, row, AdviceValue::Direct(base_x))?;
        writer.write_advice(y_column, row, AdviceValue::Direct(base_y))?;
    }

    accumulator = write_incomplete_double_and_add(
        writer,
        row_map,
        REGION,
        base,
        &bits[..INCOMPLETE_HI_BITS],
        accumulator,
        &mut z,
        IncompleteColumns {
            z: HI_Z_COLUMN,
            x_a: 3,
            lambda_1: 4,
            lambda_2: 5,
        },
    )?;

    write_direct(writer, row_map, LO_Z_COLUMN, REGION, 1, z)?;
    writer.write_region_advice(row_map, 7, REGION, 2, projective_x(&accumulator)?)?;
    writer.write_region_advice(row_map, 8, REGION, 1, projective_y(&accumulator)?)?;
    accumulator = write_incomplete_double_and_add(
        writer,
        row_map,
        REGION,
        base,
        &bits[INCOMPLETE_HI_BITS..INCOMPLETE_HI_BITS + INCOMPLETE_LO_BITS],
        accumulator,
        &mut z,
        IncompleteColumns {
            z: LO_Z_COLUMN,
            x_a: 7,
            lambda_1: 8,
            lambda_2: 2,
        },
    )?;
    if accumulator.is_identity() {
        return Err(Error::UnsatisfiedWitness);
    }

    let tail_bits: &[bool; COMPLETE_BITS + 1] = bits[INCOMPLETE_HI_BITS + INCOMPLETE_LO_BITS..]
        .try_into()
        .map_err(|_| Error::InternalInvariant)?;
    let points = complete_addition_points(base_affine, initial_accumulator, accumulator, tail_bits);
    let initial_accumulator = points[0];
    let mut accumulator = points[1];
    write_chained_complete_addition(
        writer,
        row_map,
        REGION,
        0,
        [base, base, &initial_accumulator],
        true,
    )?;
    let (x, y) = point_coordinates(&initial_accumulator)?;
    write_direct(writer, row_map, 3, REGION, 2, x)?;
    write_direct(writer, row_map, 4, REGION, 1, y)?;

    let mut offset = INCOMPLETE_LO_BITS + 3;
    if chains[2].1.row(0) != start + offset {
        return Err(Error::InternalInvariant);
    }
    write_direct(writer, row_map, HI_Z_COLUMN, REGION, offset, z)?;
    for (index, bit) in tail_bits[..COMPLETE_BITS].iter().enumerate() {
        let selected_base = if *bit { *base } else { base.neg() };
        write_direct(writer, row_map, 9, REGION, offset + 1, base_y)?;
        // The selected y assignment shares the first addition's `p` input
        // cell (column 1), which the addition writes itself; the accumulator
        // inputs of every addition after the first are the previous
        // addition's result cells and are skipped via `write_q_inputs`.
        let intermediate = points[2 + 2 * index];
        let next = points[3 + 2 * index];
        write_chained_complete_addition(
            writer,
            row_map,
            REGION,
            offset,
            [&selected_base, &accumulator, &intermediate],
            index == 0,
        )?;
        write_chained_complete_addition(
            writer,
            row_map,
            REGION,
            offset + 1,
            [&accumulator, &intermediate, &next],
            false,
        )?;
        accumulator = next;
        z = z.double().add(&<Fp>::from_u64((*bit).into()));
        if chains[2].1.row(index + 1) != start + offset + 2 {
            return Err(Error::InternalInvariant);
        }
        write_direct(writer, row_map, HI_Z_COLUMN, REGION, offset + 2, z)?;
        offset += 2;
    }

    let lsb = bits[254];
    z = z.double().add(&<Fp>::from_u64(lsb.into()));
    if chains[2].1.row(COMPLETE_BITS + 1) != start + offset + 1 {
        return Err(Error::InternalInvariant);
    }
    write_direct(writer, row_map, HI_Z_COLUMN, REGION, offset + 1, z)?;
    write_direct(writer, row_map, 0, REGION, offset + 1, base_x)?;
    write_direct(writer, row_map, 1, REGION, offset + 1, base_y)?;
    let lsb_point = if lsb {
        PallasPoint::IDENTITY
    } else {
        base.neg()
    };
    let result = points[2 * COMPLETE_BITS + 2];
    write_chained_complete_addition(
        writer,
        row_map,
        REGION,
        offset,
        [&lsb_point, &accumulator, &result],
        false,
    )?;

    // Cross-check against a direct scalar multiplication; compiled out of
    // release builds since only a prover bug can trip it.
    debug_assert!(
        base.mul_projective(&scalar).eq(&result.to_projective()),
        "variable-base multiply disagrees with scalar multiplication"
    );
    write_variable_base_overflow(writer, row_map, k, scalar)?;
    Ok(result)
}

/// Returns the initial doubling, tail input, two sums per complete bit, and
/// final low-bit adjustment, all normalized with one shared inversion.
/// The tail's arithmetic needs no affine intermediate; only its witness rows do.
pub(super) fn complete_addition_points(
    base: &PallasAffine,
    initial: PallasProjective,
    mut accumulator: PallasProjective,
    bits: &[bool; COMPLETE_BITS + 1],
) -> [PallasPoint; 2 * COMPLETE_BITS + 3] {
    let mut projective = [PallasProjective::IDENTITY; 2 * COMPLETE_BITS + 3];
    projective[0] = initial;
    projective[1] = accumulator;
    for (index, bit) in bits[..COMPLETE_BITS].iter().enumerate() {
        let selected_base = if *bit { *base } else { base.neg() };
        let intermediate = accumulator.add_mixed(&selected_base);
        accumulator = accumulator.add(&intermediate);
        projective[2 + 2 * index] = intermediate;
        projective[3 + 2 * index] = accumulator;
    }
    projective[2 * COMPLETE_BITS + 2] = if bits[COMPLETE_BITS] {
        accumulator
    } else {
        accumulator.add_mixed(&base.neg())
    };
    let mut points = [PallasPoint::IDENTITY; 2 * COMPLETE_BITS + 3];
    let mut scratch = [<Fp>::ZERO; 2 * COMPLETE_BITS + 3];
    batch_normalize(&projective, &mut points, &mut scratch);
    points
}

/// Advice columns that differ between the high and low incomplete chains.
#[derive(Clone, Copy)]
pub(super) struct IncompleteColumns {
    pub(super) z: usize,
    pub(super) x_a: usize,
    pub(super) lambda_1: usize,
    pub(super) lambda_2: usize,
}

/// Writes one incomplete double-and-add chain. The base input coordinates
/// (columns 0 and 1) are written once by the caller, because the hi and lo
/// chains cover overlapping rows with the same values.
#[allow(clippy::too_many_arguments)] // layout coordinates and chain state have distinct roles
pub(super) fn write_incomplete_double_and_add(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    region: usize,
    base: &PallasPoint,
    bits: &[bool],
    mut accumulator: PallasProjective,
    z: &mut Fp,
    columns: IncompleteColumns,
) -> Result<PallasProjective, Error> {
    let base = base.as_affine().ok_or(Error::InternalInvariant)?;
    let negative_base = base.neg();
    let start = row_map.absolute_row(region, 0)?;
    for (index, bit) in bits.iter().enumerate() {
        let row = start + index + 2;
        *z = z.double().add(&<Fp>::from_u64((*bit).into()));
        writer.write_advice(columns.z, row, AdviceValue::Direct(*z))?;

        let selected_base = if *bit { base } else { &negative_base };
        let step = accumulator
            .incomplete_double_and_add(selected_base)
            .ok_or(Error::UnsatisfiedWitness)?;
        accumulator = step.point;
        let (x, _, denominator) = accumulator.coordinates();
        writer.write_incomplete_double_and_add(
            [
                (columns.lambda_1, row),
                (columns.lambda_2, row),
                (columns.x_a, row + 1),
            ],
            [step.slope_numerators[0], step.slope_numerators[1], *x],
            *denominator,
        )?;
    }
    writer.write_advice(
        columns.lambda_1,
        start + bits.len() + 2,
        projective_y(&accumulator)?,
    )?;
    Ok(accumulator)
}

fn projective_x(point: &PallasProjective) -> Result<AdviceValue, Error> {
    let (x, _, z) = point.coordinates();
    if z.is_zero() {
        return Err(Error::UnsatisfiedWitness);
    }
    Ok(AdviceValue::Rational {
        numerator: *x,
        denominator: z.square(),
    })
}

fn projective_y(point: &PallasProjective) -> Result<AdviceValue, Error> {
    let (_, y, z) = point.coordinates();
    if z.is_zero() {
        return Err(Error::UnsatisfiedWitness);
    }
    Ok(AdviceValue::Rational {
        numerator: *y,
        denominator: z.square().mul(z),
    })
}

/// Writes one complete addition at `row`/`row + 1`. When the addition is
/// chained, its `q` operand is the previous addition's result and the input
/// cells `(2, row)`/`(3, row)` are already written — `write_q_inputs: false`
/// skips them (the values are identical by construction: both come from the
/// same computed point). The caller supplies `[p, q, p + q]` after batch
/// normalization; writing the rows performs no curve arithmetic or inversion.
pub(super) fn write_chained_complete_addition(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    region: usize,
    row: usize,
    [p, q, result]: [&PallasPoint; 3],
    write_q_inputs: bool,
) -> Result<(), Error> {
    let (x_p, y_p) = point_coordinates_or_zero(p);
    let (x_q, y_q) = point_coordinates_or_zero(q);
    let (x_r, y_r) = point_coordinates_or_zero(result);

    let row = row_map.absolute_row(region, row)?;
    writer.write_advice(0, row, AdviceValue::Direct(x_p))?;
    writer.write_advice(1, row, AdviceValue::Direct(y_p))?;
    if write_q_inputs {
        writer.write_advice(2, row, AdviceValue::Direct(x_q))?;
        writer.write_advice(3, row, AdviceValue::Direct(y_q))?;
    }
    for (column, value) in complete_addition_rationals(x_p, y_p, x_q, y_q) {
        writer.write_advice(column, row, value)?;
    }
    writer.write_advice(2, row + 1, AdviceValue::Direct(x_r))?;
    writer.write_advice(3, row + 1, AdviceValue::Direct(y_r))?;
    Ok(())
}

/// Expands the shifted scalar into the most-significant-first circuit schedule.
pub(super) fn variable_base_bits(k: CanonicalUint) -> Result<[bool; 255], Error> {
    if !k.fits_in_bits(255) {
        return Err(Error::InternalInvariant);
    }
    // Most significant bit first, as the incomplete rounds consume them.
    let mut bits = [false; 255];
    for (index, bit) in bits.iter_mut().enumerate() {
        *bit = k.bit(254 - index).ok_or(Error::InternalInvariant)?;
    }
    Ok(bits)
}

/// `k = scalar + t_Q` as a canonical 255-bit integer (an integer sum, not a
/// field addition): the variable-base multiplication witnesses `k`'s bits.
pub(super) fn scalar_to_k(scalar: &Fq) -> Result<CanonicalUint, Error> {
    scalar
        .to_canonical_uint()
        .checked_add_u128(T_Q)
        .ok_or(Error::InternalInvariant)
}

fn write_variable_base_overflow(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    k: CanonicalUint,
    scalar: Fq,
) -> Result<(), Error> {
    let k_254 = <Fp>::from_u64(k.bit(254).ok_or(Error::InternalInvariant)?.into());
    let alpha = <Fp>::from_bytes(scalar.to_bytes()).ok_or(Error::InternalInvariant)?;
    let s = alpha.add(&k_254.mul(&power_of_two(130)));
    write_direct(writer, row_map, 6, 298, 0, s)?;
    // Column 9, region 299: 13 ten-bit words, allowing a nonzero remainder.
    write_scheduled_running_sum(writer, row_map, 9, 299, &s, 10, 13, false)?;

    let z_0 = <Fp>::from_uint_reduced(k);
    let z_130 = <Fp>::from_canonical_uint(k.shr(130)).ok_or(Error::InternalInvariant)?;
    let s_minus_lo_130 = running_sum_at(&s, 13)?;
    write_region_cells(
        writer,
        row_map,
        300,
        [
            (6, 0, z_0),
            (6, 1, z_130),
            (7, 0, k_254),
            (7, 1, alpha),
            (7, 2, s_minus_lo_130),
            (8, 1, s),
        ],
    )?;
    writer.write_region_advice(row_map, 6, 300, 2, rational_or_zero(<Fp>::ONE, z_130))
}
