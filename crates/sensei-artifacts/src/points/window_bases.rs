//! Generators for the fixed-window coordinate commitment-base artifacts.
//!
//! For every fixed-base multiplication window (flat in `FIXED_BASE_REGIONS`
//! order) and every one of its eight digit choices, the Vesta point
//! `c(window, digit) · G_row` for the table value `c` (`x`, `y`, or `u`), where
//! `G_row` is the Lagrange SRS base of the window's advice row. An advice
//! commitment can then add the selected point instead of committing the
//! full-width coordinate cell as a general scalar term.
//! A pure function of the pinned SRS, the frozen region layout, and the
//! shared window-table construction; every product must be nonidentity to
//! have an affine record.
//!
//! These are Vesta commitment contributions, distinct from the Pallas window
//! table used during witness generation. Output order is schedule slot, then
//! window within that slot, then digit; the registry stores each family in
//! its own file.

use bento::bytes_of_slice;
use sensei_shared::{
    fixed_bases::{FIXED_BASE_REGIONS, FIXED_BASE_TOTAL_WINDOWS, FIXED_BASE_WINDOW_SIZE},
    regions::REGION_STARTS,
};
use udon::{
    curve::{EisensteinTableBatch, PreparedAffinePoint, Vesta, VestaAffine, VestaProjective},
    exec::{SerialExecutor, TaskBudget},
    field::Fq,
};

use crate::{Error, context::Context};

use super::normalize_points;

/// One compact multiplier per advice-row base, reused by all coordinate families.
pub(crate) struct WindowMultipliers {
    entries: Vec<PreparedAffinePoint<Vesta>>,
}

impl WindowMultipliers {
    pub(crate) fn new(lagrange: &[VestaAffine]) -> Result<Self, Error> {
        let mut bases = Vec::with_capacity(FIXED_BASE_TOTAL_WINDOWS);
        for (region, _, window_count) in FIXED_BASE_REGIONS {
            let start = REGION_STARTS[region];
            for window in 0..window_count {
                let base = lagrange
                    .get(start + window)
                    .ok_or_else(|| Error::new("fixed-base window row outside the SRS"))?;
                bases.push(*base);
            }
        }
        let requirements =
            EisensteinTableBatch::<Vesta, PreparedAffinePoint<Vesta>>::requirements(bases.len())
                .expect("fixed window count fits table storage");
        let mut entries =
            vec![PreparedAffinePoint::from_affine(&bases[0]); requirements.table_entries];
        let mut projective = vec![VestaProjective::IDENTITY; requirements.projective_scratch];
        let mut field = vec![<Fq>::ZERO; requirements.field_scratch];
        EisensteinTableBatch::prepare(
            &bases,
            &mut entries,
            &mut projective,
            &mut field,
            TaskBudget::SERIAL,
            &SerialExecutor,
        );
        Ok(Self { entries })
    }
}

/// Generates the `x`-coordinate artifact.
pub(crate) fn generate_x(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    generate(context, "x", |entry| entry.x)
}

/// Generates the `y`-coordinate artifact.
pub(crate) fn generate_y(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    generate(context, "y", |entry| entry.y)
}

/// Generates the `u`-value artifact, using the table's pinned square-root choice.
pub(crate) fn generate_u(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    generate(context, "u", |entry| entry.u)
}

/// Generates the exact bytes of one coordinate family's artifact in the
/// `mont-u64x4` stored form: `FIXED_BASE_TOTAL_WINDOWS × FIXED_BASE_WINDOW_SIZE`
/// affine records `coordinate(window, digit) · G_row`.
fn generate(
    context: &Context<'_>,
    family: &str,
    coordinate: impl Fn(&sensei_shared::WindowTableEntry) -> udon::field::Fp,
) -> Result<Vec<u8>, Error> {
    let tables = context.window_tables()?;
    let multipliers = context.window_multipliers()?;
    let multipliers = EisensteinTableBatch::bind(&multipliers.entries);
    let window_size = FIXED_BASE_WINDOW_SIZE as usize;
    let mut products = Vec::with_capacity(FIXED_BASE_TOTAL_WINDOWS * window_size);
    for (window, entries) in tables.iter().enumerate() {
        let multiplier = multipliers
            .get(window)
            .expect("one compact table per window");
        for entry in entries {
            products.push(multiplier.mul(&coordinate(entry)));
        }
    }
    let affine = normalize_points(&products)
        .iter()
        .enumerate()
        .map(|(index, point)| {
            point.as_affine().copied().ok_or_else(|| {
                Error::new(format!(
                    "fixed-window {family} base {index} is the identity"
                ))
            })
        })
        .collect::<Result<Vec<VestaAffine>, Error>>()?;
    Ok(bytes_of_slice(&affine).to_vec())
}
