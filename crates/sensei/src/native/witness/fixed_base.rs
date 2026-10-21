//! Fixed-base multiplication gadgets using embedded circuit window tables.
//!
//! Base-field, short-scalar, and full-scalar gadgets share one window writer.
//! The build-time generator derives the entries with Udon arithmetic.

use sensei_shared::WindowTableEntry;
use sensei_shared::fixed_bases::{
    FIXED_BASE_REGIONS, FIXED_BASE_WINDOW_BITS, FIXED_BASE_WINDOW_SIZE, FULL_SCALAR_WINDOWS,
    FixedBase, SHORT_SCALAR_WINDOWS, fixed_base_window_offset,
};

use crate::Error;
use crate::native::curve::{PallasAffine, PallasPoint};
use crate::native::field::{CanonicalUint, Fp, Fq};

use super::decomposition::{fill_words_and_running_sums, write_scheduled_running_sum};
use super::writer::{AdviceValue, RowMap, WitnessWriter};
use super::{
    T_P, bitrange, point_coordinates_or_zero, power_of_two, running_sum_at,
    write_complete_addition, write_region_cells,
};

/// Writes a fixed-base multiplication by a base-field scalar, including its
/// running sums and canonicity rows. Returns the final affine product.
pub(super) fn write_base_field_fixed_mul(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    incomplete_region: usize,
    final_region: usize,
    fixed_base: FixedBase,
    scalar: &Fp,
) -> Result<PallasPoint, Error> {
    // The running sums land on a scheduled stream the advice commitment
    // transposes onto three-bit word bases.
    if !crate::native::regions::fixed_base_running_sums::is_stream(
        incomplete_region,
        FULL_SCALAR_WINDOWS,
    ) {
        return Err(Error::InternalInvariant);
    }
    let generator = fixed_base.generator();
    let mut digits = [0usize; FULL_SCALAR_WINDOWS];
    let mut running_sums = [<Fp>::ZERO; FULL_SCALAR_WINDOWS + 1];
    fill_words_and_running_sums(
        scalar,
        FIXED_BASE_WINDOW_BITS,
        &mut digits,
        &mut running_sums,
    )?;
    if running_sums.last().is_none_or(|value| !value.is_zero()) {
        return Err(Error::UnsatisfiedWitness);
    }
    let (accumulator, last_window) = write_fixed_incomplete_region(
        writer,
        row_map,
        incomplete_region,
        &generator,
        &digits,
        &running_sums,
    )?;
    let result =
        write_complete_addition(writer, row_map, final_region, &last_window, &accumulator)?;

    // Cross-check the gadget output against a direct scalar multiplication.
    // This only ever fails on a prover bug, so it is compiled out of release
    // builds rather than paying for a full scalar multiplication every call.
    debug_assert!(
        <Fq>::from_bytes(scalar.to_bytes()).is_some_and(|scalar_field| generator
            .mul_projective(&scalar_field)
            .eq(&result.to_projective())),
        "base-field fixed-base multiply disagrees with scalar multiplication"
    );

    let z_43 = running_sums[43];
    let z_44 = running_sums[44];
    let z_84 = running_sums[84];
    let alpha_0 = scalar.sub(&z_84.mul(&power_of_two(252)));
    // Canonicity witness `α₀' = α₀ + 2^130 − t_P`, with `t_P` as a field value.
    let alpha_0_prime = alpha_0
        .add(&power_of_two(130))
        .sub(&<Fp>::from_bytes_reduced(&T_P.to_le_bytes()));
    // Column 9, region 277: 13 ten-bit words, allowing a nonzero remainder.
    write_scheduled_running_sum(writer, row_map, 9, 277, &alpha_0_prime, 10, 13, false)?;
    write_region_cells(
        writer,
        row_map,
        278,
        [
            (6, 0, *scalar),
            (8, 0, z_84),
            (6, 1, alpha_0_prime),
            (7, 1, bitrange(scalar, 252, 254)?),
            (8, 1, bitrange(scalar, 254, 255)?),
            (6, 2, running_sum_at(&alpha_0_prime, 13)?),
            (7, 2, z_44),
            (8, 2, z_43),
        ],
    )?;

    Ok(result)
}

/// Projective window accumulator with cached powers of its denominator.
/// The window writer emits rational coordinates for batched finalization.
pub(super) struct FixedWindowAccumulator {
    pub(super) x: Fp,
    pub(super) y: Fp,
    pub(super) z: Fp,
    pub(super) z_squared: Fp,
    pub(super) z_cubed: Fp,
}

impl FixedWindowAccumulator {
    pub(super) fn from_xy(x: Fp, y: Fp) -> Self {
        Self {
            x,
            y,
            z: <Fp>::ONE,
            z_squared: <Fp>::ONE,
            z_cubed: <Fp>::ONE,
        }
    }

    pub(super) fn add_mixed_xy(&mut self, point_x: &Fp, point_y: &Fp) -> Result<(), Error> {
        let projected_x = point_x.mul(&self.z_squared);
        let projected_y = point_y.mul(&self.z_cubed);
        let h = projected_x.sub(&self.x);
        let r = projected_y.sub(&self.y);
        let h_squared = h.square();
        let h_cubed = h_squared.mul(&h);
        let x_h_squared = self.x.mul(&h_squared);
        let x = r.square().sub(&h_cubed).sub(&x_h_squared.add(&x_h_squared));
        let y = r.mul_sub_product(&x_h_squared.sub(&x), &self.y, &h_cubed);
        let z = self.z.mul(&h);
        let z_squared = z.square();
        let z_cubed = z_squared.mul(&z);
        if z.is_zero() {
            return Err(Error::InternalInvariant);
        }

        *self = Self {
            x,
            y,
            z,
            z_squared,
            z_cubed,
        };
        Ok(())
    }

    pub(super) fn to_point(&self) -> Result<PallasPoint, Error> {
        let z_inverse = self.z.invert().ok_or(Error::InternalInvariant)?;
        let z_inverse_squared = z_inverse.square();
        let x = self.x.mul(&z_inverse_squared);
        let y = self.y.mul(&z_inverse_squared).mul(&z_inverse);
        PallasPoint::from_xy(x.reduce(), y.reduce()).ok_or(Error::InternalInvariant)
    }
}

/// Writes the short-magnitude fixed-base gadget and applies a sign of `1` or
/// `-1` in its final region. The running sums must exhaust the magnitude.
pub(super) fn write_short_fixed_mul(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    incomplete_region: usize,
    final_region: usize,
    fixed_base: FixedBase,
    magnitude: &Fp,
    sign: &Fp,
) -> Result<PallasPoint, Error> {
    // The running sums land on a scheduled stream the advice commitment
    // transposes onto three-bit word bases.
    if !crate::native::regions::fixed_base_running_sums::is_stream(
        incomplete_region,
        SHORT_SCALAR_WINDOWS,
    ) {
        return Err(Error::InternalInvariant);
    }
    let generator = fixed_base.generator();
    let mut digits = [0usize; SHORT_SCALAR_WINDOWS];
    let mut running_sums = [<Fp>::ZERO; SHORT_SCALAR_WINDOWS + 1];
    fill_words_and_running_sums(
        magnitude,
        FIXED_BASE_WINDOW_BITS,
        &mut digits,
        &mut running_sums,
    )?;
    if running_sums.last().is_none_or(|value| !value.is_zero()) {
        return Err(Error::UnsatisfiedWitness);
    }
    let (accumulator, last_window) = write_fixed_incomplete_region(
        writer,
        row_map,
        incomplete_region,
        &generator,
        &digits,
        &running_sums,
    )?;
    let unsigned =
        write_complete_addition(writer, row_map, final_region, &last_window, &accumulator)?;

    let negative_one = <Fp>::ONE.neg();
    if (sign).reduce() != (<Fp>::ONE).reduce() && (sign).reduce() != (negative_one).reduce() {
        return Err(Error::UnsatisfiedWitness);
    }
    let (x, y) = point_coordinates_or_zero(&unsigned);
    let signed_y = if (sign).reduce() == (negative_one).reduce() {
        y.neg()
    } else {
        y
    };
    write_region_cells(
        writer,
        row_map,
        final_region,
        [
            (4, 1, *sign),
            (5, 1, running_sums[SHORT_SCALAR_WINDOWS - 1]),
            (1, 1, signed_y),
        ],
    )?;
    let signed =
        PallasPoint::from_xy(x.reduce(), signed_y.reduce()).ok_or(Error::InternalInvariant)?;

    // Cross-check against a direct scalar multiplication; only a prover bug can
    // trip it, so it is compiled out of release builds (see the base-field
    // fixed-base gadget for the same reasoning).
    debug_assert!(
        <Fq>::from_bytes(magnitude.to_bytes()).is_some_and(|scalar| {
            let expected = generator.mul_projective(&scalar);
            let expected = if (sign).reduce() == (negative_one).reduce() {
                expected.neg()
            } else {
                expected
            };
            expected.eq(&signed.to_projective())
        }),
        "short fixed-base multiply disagrees with scalar multiplication"
    );
    Ok(signed)
}

/// Writes a full-width scalar-field multiplication using three-bit digits.
/// The final complete addition joins the last window to the accumulated prefix.
pub(super) fn write_full_fixed_mul(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    incomplete_region: usize,
    final_region: usize,
    fixed_base: FixedBase,
    scalar: &Fq,
) -> Result<PallasPoint, Error> {
    let generator = fixed_base.generator();
    let digits = scalar_windows::<FULL_SCALAR_WINDOWS>(scalar.to_canonical_uint())?;
    let digit_cells = digits.map(|digit| <Fp>::from_u64(digit as u64));
    let (accumulator, last_window) = write_fixed_incomplete_region(
        writer,
        row_map,
        incomplete_region,
        &generator,
        &digits,
        &digit_cells,
    )?;
    let result =
        write_complete_addition(writer, row_map, final_region, &last_window, &accumulator)?;

    // Cross-check the gadget output against a direct scalar multiplication.
    // The window accumulation above already computes the same product from
    // the shared digit decomposition, so this only ever fails on a prover bug
    // and is compiled out of release builds (see the base-field fixed-base
    // gadget for the same reasoning).
    debug_assert!(
        generator.mul_projective(scalar).eq(&result.to_projective()),
        "full-width fixed-base multiply disagrees with scalar multiplication"
    );
    Ok(result)
}

fn write_fixed_incomplete_region<const WINDOWS: usize>(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    region: usize,
    _generator: &PallasAffine,
    digits: &[usize; WINDOWS],
    scalar_cells: &[Fp],
) -> Result<(PallasPoint, PallasPoint), Error> {
    if WINDOWS < 2 || (scalar_cells.len() != WINDOWS && scalar_cells.len() != WINDOWS + 1) {
        return Err(Error::InternalInvariant);
    }
    use crate::native::regions::fixed_base_windows::{SCALAR_COLUMN, U_COLUMN, X_COLUMN, Y_COLUMN};

    let start = row_map.absolute_row(region, 0)?;
    for (local_row, scalar_cell) in scalar_cells.iter().enumerate() {
        writer.write_advice(
            SCALAR_COLUMN,
            start + local_row,
            AdviceValue::Direct(*scalar_cell),
        )?;
    }

    let window_xy = match fixed_base_window_table(writer.target.window_tables(), region)
        .filter(|table| table.len() == WINDOWS)
    {
        // Precomputed path: one joint selection per window row yields the
        // point coordinates and their interpolation value u — no scalar
        // multiplication, square root, or point revalidation runs here.
        Some(table) => {
            let mut window_xy = [(<Fp>::ZERO, <Fp>::ZERO); WINDOWS];
            for (local_row, (&digit, entries)) in digits.iter().zip(table).enumerate() {
                let &WindowTableEntry { x, y, u } =
                    entries.get(digit).ok_or(Error::InternalInvariant)?;
                writer.write_advice(X_COLUMN, start + local_row, AdviceValue::Direct(x))?;
                writer.write_advice(Y_COLUMN, start + local_row, AdviceValue::Direct(y))?;
                writer.write_advice(U_COLUMN, start + local_row, AdviceValue::Direct(u))?;
                window_xy[local_row] = (x, y);
            }
            window_xy
        }
        None => return Err(Error::InternalInvariant),
    };

    let (first_x, first_y) = window_xy[0];
    let mut projective = FixedWindowAccumulator::from_xy(first_x, first_y);
    writer.write_advice(2, start + 1, AdviceValue::Direct(first_x))?;
    writer.write_advice(3, start + 1, AdviceValue::Direct(first_y))?;

    for (window, &(x, y)) in window_xy.iter().enumerate().take(WINDOWS - 1).skip(1) {
        projective.add_mixed_xy(&x, &y)?;
        if window < WINDOWS - 2 {
            let row = start + window + 1;
            // X/Z² = (X·Z)/Z³ shares the cached Z³ with Y/Z³, so the batch
            // finalizer needs only one denominator entry for both coordinates.
            writer.write_rational_pair(
                [(2, row), (3, row)],
                [projective.x.mul(&projective.z), projective.y],
                projective.z_cubed,
            )?;
        }
    }

    // The next complete-addition gadget needs an affine accumulator. Reuse
    // that normalization for its final witness row instead of deferring it.
    let accumulator = projective.to_point()?;
    if WINDOWS > 2 {
        let (x, y) = point_coordinates_or_zero(&accumulator);
        let row = start + WINDOWS - 1;
        writer.write_advice(2, row, AdviceValue::Direct(x))?;
        writer.write_advice(3, row, AdviceValue::Direct(y))?;
    }

    let &(last_x, last_y) = window_xy.last().ok_or(Error::InternalInvariant)?;
    Ok((
        accumulator,
        PallasPoint::from_xy(last_x.reduce(), last_y.reduce()).ok_or(Error::InternalInvariant)?,
    ))
}

/// One region's precomputed joint `(x, y, u)` window entries, indexed
/// `[window][digit]` with the eight digit entries of a window in one fixed
/// contiguous array. All values are witness-independent, removing a
/// Tonelli–Shanks square root and a scalar multiplication from each window
/// row of every fixed-base multiply; one selection per row jointly yields the
/// three advice cells and the accumulator input coordinates.
type FixedBaseRegionTable = [[WindowTableEntry; FIXED_BASE_WINDOW_SIZE as usize]];

/// Looks up one region's precomputed window table by its position in
/// `FIXED_BASE_REGIONS` — a seven-entry scan over a fixed array instead of a
/// hash-map probe.
pub(crate) fn fixed_base_window_table(
    tables: &[[WindowTableEntry; 8]],
    region: usize,
) -> Option<&FixedBaseRegionTable> {
    let slot = FIXED_BASE_REGIONS
        .iter()
        .position(|&(table_region, ..)| table_region == region)?;
    let start = fixed_base_window_offset(slot);
    let end = start + FIXED_BASE_REGIONS[slot].2;
    tables.get(start..end)
}

pub(super) fn scalar_windows<const COUNT: usize>(
    integer: CanonicalUint,
) -> Result<[usize; COUNT], Error> {
    if COUNT == 0
        || COUNT
            .checked_mul(FIXED_BASE_WINDOW_BITS)
            .is_none_or(|bits| bits > 256)
    {
        return Err(Error::InternalInvariant);
    }
    let mut windows = [0; COUNT];
    for (window, slot) in windows.iter_mut().enumerate() {
        *slot = usize::try_from(
            integer
                .window(window * FIXED_BASE_WINDOW_BITS, FIXED_BASE_WINDOW_BITS)
                .ok_or(Error::InternalInvariant)?,
        )
        .map_err(|_| Error::InternalInvariant)?;
    }
    Ok(windows)
}
