//! Prepared commitment points and coordinate-specific commitment bases.
//!
//! Raw inputs are canonical affine points, 64 bytes each — `x` then `y` as
//! canonical little-endian residues, never the identity — which is the
//! auditable protocol-level form. Preparation applies everything the prover
//! uses embedded: Montgomery limbs and the Lagrange prefix-sum table, with
//! individual bases for the boundary row and blinding tail. Records contain
//! affine `(x, y)` coordinates; warmup derives `ζ·x`. The output is the exact
//! stored bytes of [`SrsPointsFile`] and [`PrimitivePointsFile`], whose layouts
//! are shared with the runtime. [`PreparedPointsFile`] combines both sets in
//! one record. Each encoder prepares only the data its record contains.
//!
//! This module assembles the prepared point records. `srs` derives Lagrange
//! bases, `generators` holds the pinned auxiliary points, and `window_bases`
//! builds the separate x/y/u contribution tables using the same SRS transform.

use bento::bytes_of;
use sensei_shared::{PreparedPointsFile, PrimitivePointsFile, SrsPointsFile, USABLE_ROWS_END};
use udon::curve::{VestaAffine, VestaPoint, VestaProjective, batch_normalize};

use crate::{Error, context::Context};

mod generators;
pub(crate) mod srs;
pub(crate) mod window_bases;

/// Allocates normalized points in input order; identity checks stay with callers.
/// Scratch is allocated after the output and released before returning that output.
fn normalize_points(points: &[VestaProjective]) -> Vec<VestaPoint> {
    let mut output = vec![udon::curve::Point::IDENTITY; points.len()];
    let mut scratch = vec![udon::field::PastaField::ZERO; points.len()];
    batch_normalize(points, &mut output, &mut scratch);
    output
}

/// The prefix-sum table: prepared `P[j] = Σ_{i<j} G_i` for `j` in
/// `1..=USABLE_ROWS_END` at index `j - 1`, then the individual generators for
/// row `USABLE_ROWS_END` and the blinding tail. Every prefix must be
/// nonidentity for the table to have an affine representation; the pinned
/// SRS satisfies this.
fn prefix_sum_table(lagrange: &[VestaAffine]) -> Result<Vec<VestaAffine>, Error> {
    let mut running = VestaProjective::IDENTITY;
    let mut prefixes = Vec::with_capacity(USABLE_ROWS_END);
    for base in &lagrange[..USABLE_ROWS_END] {
        running = running.add_mixed(base);
        prefixes.push(running);
    }
    let mut table = Vec::with_capacity(lagrange.len());
    for (index, point) in normalize_points(&prefixes).iter().enumerate() {
        let affine = point.as_affine().ok_or_else(|| {
            Error::new(format!(
                "lagrange prefix sum P[{}] is the identity",
                index + 1
            ))
        })?;
        table.push(*affine);
    }
    for tail in &lagrange[USABLE_ROWS_END..] {
        table.push(*tail);
    }
    Ok(table)
}

/// Checks a prepared vector's length before installing it in the fixed record.
fn into_array<T, const LEN: usize>(values: Vec<T>, what: &str) -> Result<[T; LEN], Error> {
    let found = values.len();
    values
        .try_into()
        .map_err(|_| Error::new(format!("{what}: expected {LEN} records, found {found}")))
}

/// Constructs the combined SRS and Sinsemilla point record.
pub(crate) fn prepared_points(context: &Context<'_>) -> Result<Box<PreparedPointsFile>, Error> {
    let coefficient = context.coefficient_bases()?;
    let lagrange = context.lagrange_bases()?;
    let sinsemilla = context.sinsemilla_generators()?;
    let lagrange_prefix_sums = prefix_sum_table(lagrange)?;

    Ok(Box::new(PreparedPointsFile {
        coefficient_bases: into_array(coefficient.to_vec(), "coefficient bases")?,
        lagrange_bases: into_array(lagrange.to_vec(), "lagrange bases")?,
        lagrange_prefix_sums: into_array(lagrange_prefix_sums, "lagrange prefix sums")?,
        sinsemilla_generators: sinsemilla
            .try_into()
            .expect("decoded Sinsemilla generator count"),
        blind_generator: generators::BLIND_GENERATOR,
        ipa_generator: generators::IPA_GENERATOR,
    }))
}

/// Generates the exact bytes of the prepared-points artifact in the
/// `mont-u64x4` stored form: the stored representation of a
/// [`PreparedPointsFile`], whose fixed layout makes this encoding
/// host-independent.
pub(crate) fn generate(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    Ok(bytes_of(&*prepared_points(context)?).to_vec())
}

/// Prepares proof commitment points without loading Sinsemilla generators.
pub(crate) fn prepared_srs_points(context: &Context<'_>) -> Result<Box<SrsPointsFile>, Error> {
    let lagrange = context.lagrange_bases()?;
    Ok(Box::new(SrsPointsFile {
        coefficient_bases: into_array(context.coefficient_bases()?.to_vec(), "coefficient bases")?,
        lagrange_bases: into_array(lagrange.to_vec(), "lagrange bases")?,
        lagrange_prefix_sums: into_array(prefix_sum_table(lagrange)?, "lagrange prefix sums")?,
        blind_generator: generators::BLIND_GENERATOR,
        ipa_generator: generators::IPA_GENERATOR,
    }))
}

pub(crate) fn srs_points(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    Ok(bytes_of(&*prepared_srs_points(context)?).to_vec())
}

/// Encodes validated Sinsemilla generators without preparing SRS or circuit data.
pub(crate) fn primitive_points(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    let points = PrimitivePointsFile {
        sinsemilla_generators: context
            .sinsemilla_generators()?
            .try_into()
            .expect("decoded generator count"),
    };
    Ok(bytes_of(&points).to_vec())
}

/// Deduplicates the three pinned keys in stable current/fixed/insecure order.
pub(crate) fn verifier_commitments(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    use crate::raw::points::{VERIFIER_FIXED, VERIFIER_INSECURE, decode_points};
    use sensei_shared::records::{VERIFIER_VERSION_COUNT, VK_COLUMN_COUNT, VerifierCommitments};
    let keys = [
        current_verifier_commitments(context)?,
        decode_points(context.raw, VERIFIER_FIXED, VK_COLUMN_COUNT)?,
        decode_points(context.raw, VERIFIER_INSECURE, VK_COLUMN_COUNT)?,
    ];
    let mut points = Vec::new();
    let mut columns = [[0; VK_COLUMN_COUNT]; VERIFIER_VERSION_COUNT];
    for (key, indices) in keys.iter().zip(&mut columns) {
        for (point, index) in key.iter().zip(indices) {
            *index = match points.iter().position(|p| p == point) {
                Some(index) => index,
                None => {
                    points.push(*point);
                    points.len() - 1
                }
            } as u32;
        }
    }
    let data = VerifierCommitments {
        points: into_array(points, "distinct verifier commitments")?,
        columns,
    };
    Ok(bento::bytes_of(&data).to_vec())
}

/// Halo2 key generation commits each fixed and sigma polynomial with blind one.
fn current_verifier_commitments(context: &Context<'_>) -> Result<Vec<VestaAffine>, Error> {
    use udon::{
        exec::{ExecutionOptions, SerialExecutor},
        field::Fq,
        msm::{Bases, Input, ScalarStorage, Scratch},
    };
    let bases = context.coefficient_bases()?;
    let options = ExecutionOptions::default();
    let mut commitments = Vec::new();
    for polynomial in context
        .fixed_coefficients()?
        .iter()
        .chain(context.sigma_coefficients()?)
    {
        let input = Input::new(Bases::Affine(bases), polynomial);
        let r = input
            .requirements(options)
            .map_err(|e| Error::new(format!("verifier MSM: {e:?}")))?;
        let mut scalars = vec![ScalarStorage::ZERO; r.scalars()];
        let mut digits = vec![0; r.digits()];
        let mut affine = vec![VestaAffine::GENERATOR; r.affine()];
        let mut projective = vec![VestaProjective::IDENTITY; r.projective()];
        let mut field = vec![Fq::ZERO; r.field()];
        let mut indices = vec![0; r.indices()];
        let commitment = input
            .execute(
                options,
                &SerialExecutor,
                Scratch::new(
                    &mut scalars,
                    &mut digits,
                    &mut affine,
                    &mut projective,
                    &mut field,
                    &mut indices,
                ),
            )
            .map_err(|e| Error::new(format!("verifier MSM: {e:?}")))?
            .add_mixed(&generators::BLIND_GENERATOR)
            .to_point();
        commitments.push(
            *commitment
                .as_affine()
                .ok_or_else(|| Error::new("identity verifier commitment"))?,
        );
    }
    Ok(commitments)
}
