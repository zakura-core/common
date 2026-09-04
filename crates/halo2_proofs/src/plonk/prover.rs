use ff::Field;
#[cfg(feature = "batch")]
use ff::PrimeField;
use group::{Curve, Group};
use maybe_rayon::prelude::*;
use rand_core::Rng;
use std::iter;
use std::ops::RangeTo;

use super::{
    ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, ChallengeY, Error, ProvingKey,
    circuit::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Fixed, FloorPlanner, Instance,
        Selector,
    },
    commit_instance,
    evaluation::{EvaluationPoint, EvaluationQuery, PolynomialEvaluator},
    evaluator_schedule::{self, QuotientPoly},
    lookup, permutation, vanishing,
};

#[cfg(test)]
use super::circuit::FloorPlan;
use crate::transcript::{EncodedChallenge, TranscriptWrite};
#[cfg(feature = "batch")]
use crate::{
    InstanceScalarByteOrder, InstanceWindowTable, PREPARED_INSTANCE_BOOLEAN_ROWS,
    PREPARED_INSTANCE_COLUMNS, PREPARED_INSTANCE_DENSE_ROWS, PREPARED_INSTANCE_ROWS,
    PREPARED_INSTANCE_WINDOW_BITS, PREPARED_INSTANCE_WINDOW_MAGNITUDES, PreparedInstanceTable,
};
use crate::{
    arithmetic::{CurveAffine, batch_invert_multi},
    circuit::Value,
    plonk::Assigned,
    poly::{
        self, Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial,
        commitment::{Blind, Params},
        multiopen::{self, ProverQuery},
    },
};

const NO_DENOMINATOR: u32 = u32::MAX;

// These routing thresholds were measured for the prepared no-orbits backend
// at the Ironwood Action circuit's k. For each later circuit, a 256-row
// stratified sample must show that no advice column gains nonzero coefficients,
// while the aggregate removes more than one eighth of its nonzero coefficients
// and at least 256 sampled coefficients. Eight-row per-column prepared-work
// samples then reject adverse recoding and active-window costs, and each
// direct sample must span every prepared main window. Blinds are excluded
// because both routes evaluate one independent blind term.
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
const ADVICE_DELTA_PREPARED_K: u32 = 11;
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
const ADVICE_DELTA_ROUTE_DENOMINATOR: usize = 8;
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
const ADVICE_DELTA_COUNT_SAMPLES: usize = 256;
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
const ADVICE_DELTA_MIN_SAMPLED_SAVINGS: usize = ADVICE_DELTA_COUNT_SAMPLES;
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
const ADVICE_DELTA_WORK_SAMPLES: usize = 8;
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
const ADVICE_DELTA_STRATIFIED_FRACTION: u32 = 0x9e37_79b9;

#[cfg(all(test, feature = "multicore", not(feature = "orbits")))]
static ADVICE_DELTA_ROUTE_HITS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

#[cfg(all(test, feature = "multicore", not(feature = "orbits")))]
fn take_advice_delta_route_hits() -> usize {
    ADVICE_DELTA_ROUTE_HITS.swap(0, std::sync::atomic::Ordering::Relaxed)
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
fn advice_delta_stratified_row(
    polynomial_len: usize,
    sample_rows: usize,
    sample: usize,
) -> Option<usize> {
    if polynomial_len == 0 || sample_rows == 0 || sample >= sample_rows {
        return None;
    }

    let polynomial_len = polynomial_len as u128;
    let sample_rows = sample_rows as u128;
    let sample = sample as u128;
    let start = sample.checked_mul(polynomial_len)? / sample_rows;
    let end = sample.checked_add(1)?.checked_mul(polynomial_len)? / sample_rows;
    let width = end.checked_sub(start)?.max(1);
    // A fractional Weyl sequence chooses a different deterministic offset in
    // each stratum instead of repeatedly sampling the same relative row.
    let sample = u32::try_from(sample).ok()?;
    let fraction = sample
        .wrapping_add(1)
        .wrapping_mul(ADVICE_DELTA_STRATIFIED_FRACTION);
    let offset = (fraction as u128).checked_mul(width)? >> u32::BITS;
    let row = usize::try_from(start.checked_add(offset)?).ok()?;
    (row < usize::try_from(polynomial_len).ok()?).then_some(row)
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
fn sampled_advice_delta_nonzero_counts<F: Field>(
    direct: &[F],
    reference: &[F],
    sample_rows: usize,
) -> Option<(usize, usize)> {
    debug_assert_eq!(direct.len(), reference.len());
    debug_assert!(!direct.is_empty());
    let sample_rows = sample_rows.min(direct.len());
    (0..sample_rows).try_fold((0_usize, 0_usize), |(direct_count, delta_count), sample| {
        let row = advice_delta_stratified_row(direct.len(), sample_rows, sample)?;
        Some((
            direct_count.checked_add(usize::from(!direct[row].is_zero_vartime()))?,
            delta_count.checked_add(usize::from(direct[row] != reference[row]))?,
        ))
    })
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
fn use_sampled_advice_delta_counts(counts: &[(usize, usize)]) -> Option<bool> {
    let every_column_nonincreasing = counts.iter().all(|&(direct, delta)| delta <= direct);
    if !every_column_nonincreasing {
        return Some(false);
    }
    let direct = counts
        .iter()
        .try_fold(0_usize, |total, &(direct, _)| total.checked_add(direct))?;
    let delta = counts
        .iter()
        .try_fold(0_usize, |total, &(_, delta)| total.checked_add(delta))?;
    let saved = direct.checked_sub(delta)?;
    Some(
        every_column_nonincreasing
            && saved >= ADVICE_DELTA_MIN_SAMPLED_SAVINGS
            && saved > direct / ADVICE_DELTA_ROUTE_DENOMINATOR,
    )
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
type AdvicePolynomialsAndBlinds<C> = (
    Vec<Polynomial<<C as CurveAffine>::ScalarExt, LagrangeCoeff>>,
    Vec<Blind<<C as CurveAffine>::ScalarExt>>,
);

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
type AdviceDeltaPlan<C> =
    Vec<Vec<Option<Polynomial<<C as CurveAffine>::ScalarExt, LagrangeCoeff>>>>;

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[inline(never)]
fn plan_advice_deltas<C: CurveAffine>(
    params: &Params<C>,
    domain: &poly::EvaluationDomain<C::Scalar>,
    advice_witnesses: &[AdvicePolynomialsAndBlinds<C>],
) -> Option<AdviceDeltaPlan<C>> {
    if advice_witnesses.len() <= 1 || params.k() != ADVICE_DELTA_PREPARED_K {
        return None;
    }

    let (reference, reference_blinds) = advice_witnesses.first()?;
    let polynomial_len = reference.first()?.len();
    if polynomial_len == 0
        || reference.len() != reference_blinds.len()
        || reference.iter().any(|poly| poly.len() != polynomial_len)
        || advice_witnesses[1..].iter().any(|(advice, blinds)| {
            advice.len() != reference.len()
                || advice.len() != blinds.len()
                || advice.iter().any(|poly| poly.len() != polynomial_len)
        })
    {
        return None;
    }

    // Avoid charging the count scan to unprepared params and worker pools
    // above the prepared backend's measured cap. The prepared handle itself is
    // only acquired after a count candidate survives.
    if !params.prepared_lagrange_commitments_active(polynomial_len) {
        return None;
    }

    // Evaluate each later circuit independently. The count pass only reads
    // sampled coefficients and does not invoke the prepared evaluator.
    let count_candidates = advice_witnesses[1..]
        .par_iter()
        .map(|(advice, _)| {
            let counts = advice
                .iter()
                .zip(reference)
                .map(|(direct, reference)| {
                    sampled_advice_delta_nonzero_counts(
                        direct,
                        reference,
                        ADVICE_DELTA_COUNT_SAMPLES,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            use_sampled_advice_delta_counts(&counts)
        })
        .collect::<Option<Vec<_>>>()?;
    if !count_candidates.iter().any(|&candidate| candidate) {
        return None;
    }

    // Only count-qualified circuits acquire the prepared handle and pay for
    // the per-column work comparison.
    let prepared = params.lagrange_table()?;
    let work_rows = ADVICE_DELTA_WORK_SAMPLES.min(polynomial_len);
    let decisions = advice_witnesses[1..]
        .par_iter()
        .zip(count_candidates.par_iter())
        .map(|((advice, _), &count_candidate)| {
            if !count_candidate {
                return Some(false);
            }

            let mut direct_sample = Vec::with_capacity(work_rows);
            let mut delta_sample = Vec::with_capacity(work_rows);
            for (direct, reference) in advice.iter().zip(reference) {
                direct_sample.clear();
                delta_sample.clear();
                for sample in 0..work_rows {
                    let row = advice_delta_stratified_row(polynomial_len, work_rows, sample)?;
                    direct_sample.push(direct[row]);
                    delta_sample.push(direct[row] - reference[row]);
                }
                if !prepared.scalar_work_is_at_most_vartime(&delta_sample, &direct_sample)? {
                    return Some(false);
                }
            }
            Some(true)
        })
        .collect::<Option<Vec<_>>>()?;
    if !decisions.iter().any(|&route| route) {
        return None;
    }

    Some(
        advice_witnesses[1..]
            .par_iter()
            .zip(decisions.par_iter())
            .map(|((advice, _), &route)| {
                advice
                    .par_iter()
                    .zip(reference.par_iter())
                    .map(|(direct, reference)| {
                        route.then(|| {
                            domain.lagrange_from_vec(
                                direct
                                    .iter()
                                    .zip(reference.iter())
                                    .map(|(&direct, &reference)| direct - reference)
                                    .collect(),
                            )
                        })
                    })
                    .collect()
            })
            .collect(),
    )
}

#[cfg(all(test, feature = "batch"))]
std::thread_local! {
    static PREPARED_INSTANCE_ROUTE_HITS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

#[cfg(all(test, feature = "batch"))]
fn prepared_instance_route_hits() -> usize {
    PREPARED_INSTANCE_ROUTE_HITS.get()
}

#[cfg(feature = "batch")]
fn instance_scalar_bit(bytes: &[u8], bit: usize, byte_order: InstanceScalarByteOrder) -> bool {
    let byte_from_edge = bit / u8::BITS as usize;
    let byte = match byte_order {
        InstanceScalarByteOrder::LittleEndian => bytes[byte_from_edge],
        InstanceScalarByteOrder::BigEndian => bytes[bytes.len() - byte_from_edge - 1],
        InstanceScalarByteOrder::Unsupported => unreachable!("byte order checked by caller"),
    };
    byte & (1 << (bit % u8::BITS as usize)) != 0
}

#[cfg(feature = "batch")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PreparedInstanceDigit {
    magnitude: usize,
    negative: bool,
}

#[cfg(feature = "batch")]
fn instance_scalar_digit(
    bytes: &[u8],
    window: usize,
    scalar_bits: usize,
    byte_order: InstanceScalarByteOrder,
) -> PreparedInstanceDigit {
    let bit_start = window * PREPARED_INSTANCE_WINDOW_BITS;
    debug_assert_eq!(u8::BITS as usize % PREPARED_INSTANCE_WINDOW_BITS, 0);
    let value = if bit_start < scalar_bits {
        let byte_from_edge = bit_start / u8::BITS as usize;
        let byte = match byte_order {
            InstanceScalarByteOrder::LittleEndian => bytes[byte_from_edge],
            InstanceScalarByteOrder::BigEndian => bytes[bytes.len() - byte_from_edge - 1],
            InstanceScalarByteOrder::Unsupported => unreachable!("byte order checked by caller"),
        };
        let bit_offset = bit_start % u8::BITS as usize;
        let live_bits = (scalar_bits - bit_start).min(PREPARED_INSTANCE_WINDOW_BITS);
        let mask = (1 << live_bits) - 1;
        (usize::from(byte) >> bit_offset) & mask
    } else {
        0
    };
    let overlap = if bit_start == 0 {
        0
    } else {
        usize::from(instance_scalar_bit(bytes, bit_start - 1, byte_order))
    };

    // The bit below each window is its carry-in, while the window's high bit
    // is its carry-out. These terms cancel between adjacent windows, leaving a
    // signed digit whose magnitude is at most half the radix.
    let radix = PREPARED_INSTANCE_WINDOW_MAGNITUDES * 2;
    if value < radix / 2 {
        PreparedInstanceDigit {
            magnitude: value + overlap,
            negative: false,
        }
    } else {
        let magnitude = radix - value - overlap;
        PreparedInstanceDigit {
            magnitude,
            negative: magnitude != 0,
        }
    }
}

/// Evaluates independent fixed-base products while splitting their bit ranges
/// across the entire worker pool. Each job accumulates affine table entries
/// locally; only job boundaries require projective-to-projective additions.
#[cfg(feature = "batch")]
fn evaluate_prepared_instance_terms<C: CurveAffine>(
    table: &PreparedInstanceTable<C>,
    terms: &[(usize, C::Scalar)],
) -> Option<Vec<C::Curve>> {
    if matches!(table.byte_order, InstanceScalarByteOrder::Unsupported) {
        return None;
    }
    let representations = terms
        .iter()
        .map(|(_, scalar)| scalar.to_repr())
        .collect::<Vec<_>>();
    if representations
        .iter()
        .zip(terms)
        .any(|(repr, (_, scalar))| {
            let bytes = repr.as_ref();
            let Some(repr_bits) = bytes.len().checked_mul(u8::BITS as usize) else {
                return true;
            };
            if table.scalar_bits > repr_bits
                || (table.scalar_bits..repr_bits)
                    .any(|bit| instance_scalar_bit(bytes, bit, table.byte_order))
            {
                return true;
            }

            // [`PrimeField::Repr`] is opaque. The construction-time probe only
            // selects a candidate order; validate every term before its digits
            // index the positioned table.
            let decoded = match table.byte_order {
                InstanceScalarByteOrder::LittleEndian => {
                    crate::decode_scalar_repr::<C::Scalar>(bytes.iter().rev().copied())
                }
                InstanceScalarByteOrder::BigEndian => {
                    crate::decode_scalar_repr::<C::Scalar>(bytes.iter().copied())
                }
                InstanceScalarByteOrder::Unsupported => unreachable!("checked above"),
            };
            decoded != *scalar
        })
    {
        return None;
    }

    let work = terms.len().checked_mul(table.windows)?;
    if work == 0 {
        return Some(vec![]);
    }
    let worker_count = crate::multicore::current_num_threads().min(work);
    let partials = (0..worker_count)
        .into_par_iter()
        .map(|worker| {
            let start = work * worker / worker_count;
            let end = work * (worker + 1) / worker_count;
            let first_term = start / table.windows;
            let last_term = (end - 1) / table.windows;
            (first_term..=last_term)
                .map(|term_index| {
                    let window_start = if term_index == first_term {
                        start % table.windows
                    } else {
                        0
                    };
                    let window_end = if term_index == last_term {
                        (end - 1) % table.windows + 1
                    } else {
                        table.windows
                    };
                    let (base_index, _) = terms[term_index];
                    let repr = representations[term_index].as_ref();
                    let mut partial = C::Curve::identity();
                    for window in window_start..window_end {
                        let digit = instance_scalar_digit(
                            repr,
                            window,
                            table.scalar_bits,
                            table.byte_order,
                        );
                        if digit.magnitude != 0 {
                            let point = (base_index * table.windows + window)
                                * PREPARED_INSTANCE_WINDOW_MAGNITUDES
                                + digit.magnitude
                                - 1;
                            let point = table.points[point];
                            partial += if digit.negative { -point } else { point };
                        }
                    }
                    (term_index, partial)
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let mut products = vec![None; terms.len()];
    for (term_index, partial) in partials.into_iter().flatten() {
        products[term_index] = Some(match products[term_index].take() {
            Some(product) => product + partial,
            None => partial,
        });
    }
    Some(
        products
            .into_iter()
            .map(|product| product.unwrap_or_else(C::Curve::identity))
            .collect(),
    )
}

#[cfg(feature = "batch")]
fn instance_flag_mask<F: Field>(instance: &[F]) -> Option<usize> {
    let mut mask = 0;
    let flags = &instance[PREPARED_INSTANCE_DENSE_ROWS
        ..PREPARED_INSTANCE_DENSE_ROWS + PREPARED_INSTANCE_BOOLEAN_ROWS];
    for (flag, scalar) in flags.iter().enumerate() {
        if bool::from(scalar.is_zero()) {
            continue;
        }
        if bool::from((*scalar - F::ONE).is_zero()) {
            mask |= 1 << flag;
        } else {
            return None;
        }
    }
    Some(mask)
}

/// Commits the exact one-column Orchard instance shape, sharing any dense row
/// that is equal across every proof. Equality is checked at runtime: generic
/// ten-row circuits are not assumed to share Orchard's anchor or flags.
#[cfg(feature = "batch")]
fn commit_prepared_instances<C: CurveAffine>(
    params: &Params<C>,
    instances: &[&[&[C::Scalar]]],
) -> Option<Vec<Vec<C::Curve>>> {
    if instances.is_empty()
        || instances.iter().any(|columns| {
            columns.len() != PREPARED_INSTANCE_COLUMNS || columns[0].len() != PREPARED_INSTANCE_ROWS
        })
    {
        return None;
    }
    let table = params.prepared_instance_table()?;
    let flag_masks = instances
        .iter()
        .map(|columns| instance_flag_mask(columns[0]))
        .collect::<Option<Vec<_>>>()?;

    let mut terms = Vec::with_capacity(PREPARED_INSTANCE_DENSE_ROWS * instances.len());
    let mut shared_terms = Vec::with_capacity(PREPARED_INSTANCE_DENSE_ROWS);
    let mut proof_terms = (0..instances.len())
        .map(|_| Vec::with_capacity(PREPARED_INSTANCE_DENSE_ROWS))
        .collect::<Vec<_>>();
    for row in 0..PREPARED_INSTANCE_DENSE_ROWS {
        let first = instances[0][0][row];
        if instances
            .iter()
            .skip(1)
            .all(|columns| columns[0][row] == first)
        {
            shared_terms.push(terms.len());
            terms.push((row, first));
        } else {
            for (proof, columns) in instances.iter().enumerate() {
                proof_terms[proof].push(terms.len());
                terms.push((row, columns[0][row]));
            }
        }
    }

    let products = evaluate_prepared_instance_terms(&table, &terms)?;
    let shared = shared_terms
        .into_iter()
        .map(|term| products[term])
        .reduce(|left, right| left + right)
        .unwrap_or_else(C::Curve::identity);
    let shared_offset = flag_masks
        .iter()
        .all(|flag_mask| *flag_mask == flag_masks[0])
        .then(|| table.offsets[flag_masks[0]] + shared);
    Some(
        proof_terms
            .into_par_iter()
            .zip(flag_masks.into_par_iter())
            .map(|(terms, flag_mask)| {
                let mut commitment =
                    shared_offset.unwrap_or_else(|| table.offsets[flag_mask] + shared);
                for term in terms {
                    commitment += products[term];
                }
                vec![commitment]
            })
            .collect(),
    )
}

fn commit_prover_instances<C: CurveAffine>(
    params: &Params<C>,
    instances: &[&[&[C::Scalar]]],
) -> Vec<Vec<C::Curve>> {
    #[cfg(feature = "batch")]
    if let Some(commitments) = commit_prepared_instances(params, instances) {
        #[cfg(test)]
        PREPARED_INSTANCE_ROUTE_HITS.set(PREPARED_INSTANCE_ROUTE_HITS.get() + 1);
        return commitments;
    }

    instances
        .into_par_iter()
        .map(|columns| {
            columns
                .iter()
                .map(|values| {
                    if values.len() <= params.g_lagrange.len() {
                        commit_instance(params, values)
                    } else {
                        // This placeholder is never written to the transcript:
                        // instance preparation returns `InstanceTooLarge` at
                        // the same proof position as the previous path.
                        C::Curve::identity()
                    }
                })
                .collect()
        })
        .collect()
}

fn normalize_prover_instance_commitments<C: CurveAffine>(
    params: &Params<C>,
    instances: &[&[&[C::Scalar]]],
) -> Vec<Vec<C>> {
    let projective = commit_prover_instances(params, instances);
    let column_counts = projective.iter().map(Vec::len).collect::<Vec<_>>();
    let projective = projective.into_iter().flatten().collect::<Vec<_>>();
    let mut affine = vec![C::identity(); projective.len()];
    if !projective.is_empty() {
        C::Curve::batch_normalize(&projective, &mut affine);
    }

    let mut affine = affine.into_iter();
    let commitments = column_counts
        .into_iter()
        .map(|count| affine.by_ref().take(count).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    assert!(affine.next().is_none());
    commitments
}

struct AdviceWitness<F: Field> {
    values: Vec<Polynomial<F, LagrangeCoeff>>,
    denominator_cells: Vec<usize>,
    denominators: Vec<F>,
    denominator_slots: Vec<Vec<u32>>,
    row_count: usize,
}

impl<F: Field> AdviceWitness<F> {
    fn new(values: Vec<Polynomial<F, LagrangeCoeff>>) -> Self {
        let row_count = values.first().map_or(0, |column| column.len());
        assert!(values.iter().all(|column| column.len() == row_count));

        Self {
            denominator_slots: vec![vec![NO_DENOMINATOR; row_count]; values.len()],
            values,
            denominator_cells: Vec::new(),
            denominators: Vec::new(),
            row_count,
        }
    }

    fn assign(&mut self, column: usize, row: usize, assigned: Assigned<F>) -> Result<(), Error> {
        if self
            .values
            .get(column)
            .and_then(|values| values.get(row))
            .is_none()
        {
            return Err(Error::BoundsFailure);
        }

        self.assign_valid(column, row, assigned);
        Ok(())
    }

    fn assign_batch<V>(
        &mut self,
        column: usize,
        row: usize,
        len: usize,
        mut to: V,
    ) -> Result<(), Error>
    where
        V: FnMut(usize) -> Result<Assigned<F>, Error>,
    {
        if len == 0 {
            return Ok(());
        }

        let end = row.checked_add(len).ok_or(Error::BoundsFailure)?;
        if self
            .values
            .get(column)
            .and_then(|values| values.get(row..end))
            .is_none()
        {
            return Err(Error::BoundsFailure);
        }

        for index in 0..len {
            self.assign_valid(column, row + index, to(index)?);
        }
        Ok(())
    }

    fn assign_valid(&mut self, column: usize, row: usize, assigned: Assigned<F>) {
        match assigned {
            Assigned::Zero => {
                self.remove_denominator(column, row);
                self.values[column][row] = F::ZERO;
            }
            Assigned::Trivial(value) => {
                self.remove_denominator(column, row);
                self.values[column][row] = value;
            }
            Assigned::Rational(numerator, denominator) => {
                let slot = self.denominator_slots[column][row];
                if slot == NO_DENOMINATOR {
                    let slot = u32::try_from(self.denominators.len())
                        .expect("the number of advice cells fits into u32");
                    self.denominator_slots[column][row] = slot;
                    self.denominator_cells.push(column * self.row_count + row);
                    self.denominators.push(denominator);
                } else {
                    self.denominators[slot as usize] = denominator;
                }
                self.values[column][row] = numerator;
            }
        }
    }

    fn remove_denominator(&mut self, column: usize, row: usize) {
        let slot = self.denominator_slots[column][row];
        if slot == NO_DENOMINATOR {
            return;
        }

        self.denominator_slots[column][row] = NO_DENOMINATOR;
        let slot = slot as usize;
        self.denominator_cells.swap_remove(slot);
        self.denominators.swap_remove(slot);

        if let Some(&moved_cell) = self.denominator_cells.get(slot) {
            let moved_column = moved_cell / self.row_count;
            let moved_row = moved_cell % self.row_count;
            self.denominator_slots[moved_column][moved_row] = slot as u32;
        }
    }

    fn evaluate(mut self) -> Vec<Polynomial<F, LagrangeCoeff>> {
        batch_invert_multi(&mut self.denominators);
        for (cell, denominator_inverse) in self.denominator_cells.into_iter().zip(self.denominators)
        {
            let column = cell / self.row_count;
            let row = cell % self.row_count;
            self.values[column][row] *= denominator_inverse;
        }
        self.values
    }
}

// Each outer permutation task contains a two-way commitment/transform join.
// Leave capacity for that nested work instead of consuming the whole pool
// with outer tasks.
const PERMUTATION_INNER_WORKER_HEADROOM: usize = 2;
// Bound a top-level estimate of the temporary storage added by preparing more
// than one set at once. Ten scalar-sized buffers cover the current Pasta GLV
// inputs, components, base preparation, product, and transform copies with
// margin; one affine-base buffer is counted separately. Curve backends may use
// opaque scratch that this estimate cannot model.
const PERMUTATION_PARALLEL_ESTIMATED_SCRATCH_BUDGET_BYTES: usize = 8 * 1024 * 1024;
const PERMUTATION_PARALLEL_SCRATCH_SCALAR_EQUIVALENTS: usize = 10;

fn prepare_permutations_in_parallel(task_count: usize, worker_count: usize) -> bool {
    task_count > 1 && worker_count.saturating_sub(task_count) >= PERMUTATION_INNER_WORKER_HEADROOM
}

fn permutation_parallel_scratch_fits<C: CurveAffine>(
    additional_task_count: usize,
    domain_size: usize,
) -> bool {
    let scratch_bytes_per_row = std::mem::size_of::<C>()
        + PERMUTATION_PARALLEL_SCRATCH_SCALAR_EQUIVALENTS * std::mem::size_of::<C::Scalar>();
    additional_task_count
        .checked_mul(domain_size)
        .and_then(|rows| rows.checked_mul(scratch_bytes_per_row))
        .is_some_and(|bytes| bytes <= PERMUTATION_PARALLEL_ESTIMATED_SCRATCH_BUDGET_BYTES)
}

fn prepare_permutation_sets_in_parallel<C: CurveAffine>(
    set_count: usize,
    worker_count: usize,
    domain_size: usize,
) -> bool {
    if !prepare_permutations_in_parallel(set_count, worker_count) {
        return false;
    }

    permutation_parallel_scratch_fits::<C>(set_count.saturating_sub(1), domain_size)
}

fn prepare_nested_permutation_sets_in_parallel<C: CurveAffine>(
    circuit_count: usize,
    set_count: usize,
    worker_count: usize,
    domain_size: usize,
) -> bool {
    circuit_count > 1
        && set_count > 1
        && prepare_permutations_in_parallel(circuit_count, worker_count)
        && permutation_parallel_scratch_fits::<C>(
            circuit_count.saturating_mul(set_count.saturating_sub(1)),
            domain_size,
        )
}

struct WitnessCollection<'a, F: Field> {
    k: u32,
    advice: AdviceWitness<F>,
    instances: &'a [&'a [F]],
    usable_rows: RangeTo<usize>,
    _marker: std::marker::PhantomData<F>,
}

impl<'a, F: Field> Assignment<F> for WitnessCollection<'a, F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // We only care about advice columns here.
        Ok(())
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.instances
            .get(column.index())
            .and_then(|column| column.get(row))
            .map(|v| Value::known(*v))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.advice
            .assign(column.index(), row, to().into_field().assign()?)
    }

    fn assign_advice_batch<V, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        len: usize,
        mut to: V,
    ) -> Result<(), Error>
    where
        V: FnMut(usize) -> Value<Assigned<F>>,
        A: Fn(usize) -> AR,
        AR: Into<String>,
    {
        if len == 0 {
            return Ok(());
        }

        let end = row.checked_add(len).ok_or(Error::BoundsFailure)?;
        if !self.usable_rows.contains(&row) || end > self.usable_rows.end {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.advice
            .assign_batch(column.index(), row, len, |index| to(index).assign())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Fixed>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // We only care about advice columns here.
        Ok(())
    }

    fn copy(&mut self, _: Column<Any>, _: usize, _: Column<Any>, _: usize) -> Result<(), Error> {
        // We only care about advice columns here.
        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
///
/// Every element of `circuits` must have the circuit shape used to generate
/// `pk`.
///
/// The circuit type must be `Sync` and its configuration `Send` so that
/// compatible floor planners can synthesize independent circuit witnesses in
/// parallel.
///
/// # Security
///
/// Proof creation is variable-time in the private witnesses. In particular,
/// prepared batched commitments may expose sparsity and similarity between
/// circuit witnesses through timing. Do not expose proving latency across a
/// boundary where those relationships are sensitive.
pub fn create_proof<
    C: CurveAffine,
    E: EncodedChallenge<C>,
    R: Rng,
    T: TranscriptWrite<C, E>,
    ConcreteCircuit: Circuit<C::ScalarExt> + Sync,
>(
    params: &Params<C>,
    pk: &ProvingKey<C>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[C::Scalar]]],
    mut rng: R,
    transcript: &mut T,
) -> Result<(), Error>
where
    <ConcreteCircuit as Circuit<C::ScalarExt>>::Config: Send,
{
    if circuits.len() != instances.len() {
        return Err(Error::InvalidInstances);
    }

    for instance in instances.iter() {
        if instance.len() != pk.vk.cs.num_instance_columns {
            return Err(Error::InvalidInstances);
        }
    }

    // Hash verification key into transcript
    pk.vk.hash_into(transcript)?;

    let domain = &pk.vk.domain;
    let mut meta = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut meta);

    // Selector optimizations cannot be applied here; use the ConstraintSystem
    // from the verification key.
    let meta = &pk.vk.cs;
    let max_instance_len = params.n as usize - (meta.blinding_factors() + 1);

    let instance_commitments = normalize_prover_instance_commitments(params, instances);
    let instance_values = instances
        .into_par_iter()
        .map(|instance| -> Result<_, Error> {
            instance
                .iter()
                .map(|values| {
                    let mut poly = domain.empty_lagrange();
                    assert_eq!(poly.len(), params.n as usize);
                    if values.len() > max_instance_len {
                        return Err(Error::InstanceTooLarge);
                    }
                    for (poly, value) in poly.iter_mut().zip(values.iter()) {
                        *poly = *value;
                    }
                    Ok(poly)
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Vec<_>>();

    // Preserve circuit and column order while updating the transcript. Keeping
    // each preparation result in order also preserves the transcript prefix
    // before an instance error.
    let mut prepared_instance_values = Vec::with_capacity(instance_values.len());
    for (instance_commitments, instance_values) in
        instance_commitments.into_iter().zip(instance_values)
    {
        let instance_values = instance_values?;
        for commitment in instance_commitments {
            transcript.common_point(commitment)?;
        }
        prepared_instance_values.push(instance_values);
    }

    let unusable_rows_start = params.n as usize - (meta.blinding_factors() + 1);
    let mut witnesses = instances
        .iter()
        .map(|instances| WitnessCollection {
            k: params.k,
            advice: AdviceWitness::new(vec![domain.empty_lagrange(); meta.num_advice_columns]),
            instances,
            // The prover will not be allowed to assign values to advice
            // cells that exist within inactive rows, which include some
            // number of blinding factors and an extra row for use in the
            // permutation argument.
            usable_rows: ..unusable_rows_start,
            _marker: std::marker::PhantomData,
        })
        .collect::<Vec<_>>();

    struct InstanceSingle<C: CurveAffine> {
        pub instance_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
        pub instance_polys: Vec<Polynomial<C::Scalar, Coeff>>,
        pub instance_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    }

    let prepare_instance_polynomials = || {
        prepared_instance_values
            .into_par_iter()
            .map(|instance_values| {
                let instance_polys: Vec<_> = instance_values
                    .iter()
                    .map(|poly| {
                        let lagrange_vec = domain.lagrange_from_vec(poly.to_vec());
                        domain.lagrange_to_coeff_with_twiddles(lagrange_vec, &pk.fft_twiddles)
                    })
                    .collect();

                let instance_cosets: Vec<_> = instance_polys
                    .iter()
                    .map(|poly| {
                        domain.coeff_to_extended_with_twiddles(poly.clone(), &pk.fft_twiddles)
                    })
                    .collect();

                InstanceSingle::<C> {
                    instance_values,
                    instance_polys,
                    instance_cosets,
                }
            })
            .collect::<Vec<_>>()
    };
    let synthesize = || {
        // Synthesize every circuit while allowing its floor planner to share
        // circuit-shape-dependent work across the batch.
        ConcreteCircuit::FloorPlanner::synthesize_batch(
            &mut witnesses,
            circuits,
            config,
            &meta.constants,
            pk.floor_plan.as_ref(),
        )
    };

    // Instance polynomial preparation and witness synthesis are independent.
    // Run them concurrently while preserving the ordered results consumed
    // below.
    let (instance, synthesis_result) = if crate::multicore::current_num_threads() > 1 {
        crate::multicore::join(prepare_instance_polynomials, synthesize)
    } else {
        (prepare_instance_polynomials(), synthesize())
    };
    synthesis_result?;

    struct AdviceSingle<C: CurveAffine> {
        pub advice_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
        pub advice_polys: Vec<Polynomial<C::Scalar, Coeff>>,
        pub advice_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
        pub advice_blinds: Vec<Blind<C::Scalar>>,
    }

    // Rational advice evaluation is independent across circuits. Keep every
    // RNG draw below in circuit order and after successful synthesis.
    let evaluate_in_parallel = witnesses.len() > 1 && crate::multicore::current_num_threads() > 1;
    let advice_values = if evaluate_in_parallel {
        witnesses
            .into_par_iter()
            .map(|witness| witness.advice.evaluate())
            .collect::<Vec<_>>()
    } else {
        witnesses
            .into_iter()
            .map(|witness| witness.advice.evaluate())
            .collect::<Vec<_>>()
    };
    // Consume randomness in circuit order before preparing the independent
    // commitments and polynomial transforms in parallel.
    let advice_witnesses = advice_values
        .into_iter()
        .map(|mut advice| {
            // Add blinding factors to advice columns
            for advice in &mut advice {
                for cell in &mut advice[unusable_rows_start..] {
                    *cell = C::Scalar::random(&mut rng);
                }
            }

            // Compute commitments to advice column polynomials
            let advice_blinds: Vec<_> = advice
                .iter()
                .map(|_| Blind(C::Scalar::random(&mut rng)))
                .collect();
            (advice, advice_blinds)
        })
        .collect::<Vec<_>>();

    let circuit_count = advice_witnesses.len();
    let (prepared_advice, lookup_table_plan) = crate::multicore::join(
        || {
            #[cfg(all(feature = "multicore", not(feature = "orbits")))]
            let delta_plan = plan_advice_deltas(params, domain, &advice_witnesses);
            #[cfg(any(not(feature = "multicore"), feature = "orbits"))]
            let delta_plan: Option<
                Vec<Vec<Option<Polynomial<C::Scalar, LagrangeCoeff>>>>,
            > = None;

            #[cfg(all(test, feature = "multicore", not(feature = "orbits")))]
            if let Some(plan) = &delta_plan {
                ADVICE_DELTA_ROUTE_HITS.fetch_add(
                    plan.iter()
                        .flatten()
                        .filter(|delta| delta.is_some())
                        .count(),
                    std::sync::atomic::Ordering::Relaxed,
                );
            }

            // Preserve the original scheduling and normalization path unless
            // the selected deltas collectively amortize its batch-wide work.
            let Some(delta_plan) = delta_plan else {
                return advice_witnesses
                    .into_par_iter()
                    .map(|(advice, advice_blinds)| {
                        let (advice_commitments, (advice_polys, advice_cosets)) =
                            crate::multicore::join(
                                || {
                                    #[cfg(feature = "multicore")]
                                    let advice_commitments_projective: Vec<_> = advice
                                        .par_iter()
                                        .zip(advice_blinds.par_iter())
                                        .map(|(poly, blind)| {
                                            params.commit_lagrange(poly, *blind)
                                        })
                                        .collect();
                                    #[cfg(not(feature = "multicore"))]
                                    let advice_commitments_projective: Vec<_> = advice
                                        .iter()
                                        .zip(advice_blinds.iter())
                                        .map(|(poly, blind)| {
                                            params.commit_lagrange(poly, *blind)
                                        })
                                        .collect();
                                    let mut advice_commitments =
                                        vec![C::identity(); advice_commitments_projective.len()];
                                    C::Curve::batch_normalize(
                                        &advice_commitments_projective,
                                        &mut advice_commitments,
                                    );
                                    advice_commitments
                                },
                                || {
                                    domain.batch_lagrange_to_coeff_and_extended(
                                        &advice,
                                        &pk.fft_twiddles,
                                    )
                                },
                            );

                        (
                            advice_commitments,
                            AdviceSingle::<C> {
                                advice_values: advice,
                                advice_polys,
                                advice_cosets,
                                advice_blinds,
                            },
                        )
                    })
                    .collect::<Vec<_>>();
            };

            let reference_blinds = &advice_witnesses[0].1;
            // Keep every transform concurrent with the complete routed
            // commitment path, including reconstruction and normalization.
            let (advice_commitments, transforms) = crate::multicore::join(
                || {
                    let candidates = (0..circuit_count)
                        .into_par_iter()
                        .map(|circuit| {
                            let (advice, advice_blinds) = &advice_witnesses[circuit];
                            (0..advice.len())
                                .into_par_iter()
                                .map(|column| {
                                    let direct = &advice[column];
                                    if circuit == 0 {
                                        return (
                                            params.commit_lagrange(direct, advice_blinds[column]),
                                            false,
                                        );
                                    }

                                    let Some(delta) = delta_plan[circuit - 1][column].as_ref()
                                    else {
                                        return (
                                            params.commit_lagrange(direct, advice_blinds[column]),
                                            false,
                                        );
                                    };

                                    // Com(a, r) = Com(a_ref, r_ref)
                                    //     + Com(a - a_ref, r - r_ref).
                                    (
                                        params.commit_lagrange(
                                            delta,
                                            Blind(
                                                advice_blinds[column].0
                                                    - reference_blinds[column].0,
                                            ),
                                        ),
                                        true,
                                    )
                                })
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();

                    let reference = candidates[0]
                        .iter()
                        .map(|(commitment, _)| *commitment)
                        .collect::<Vec<_>>();
                    candidates
                        .into_par_iter()
                        .map(|candidates| {
                            debug_assert_eq!(reference.len(), candidates.len());
                            // Reconstruct in the original circuit and column
                            // order, so later transcript writes remain
                            // unchanged.
                            let projective = reference
                                .iter()
                                .zip(candidates)
                                .map(|(reference, (candidate, use_delta))| {
                                    if use_delta {
                                        *reference + candidate
                                    } else {
                                        candidate
                                    }
                                })
                                .collect::<Vec<_>>();
                            let mut commitments = vec![C::identity(); projective.len()];
                            C::Curve::batch_normalize(&projective, &mut commitments);
                            commitments
                        })
                        .collect::<Vec<_>>()
                },
                || {
                    #[cfg(feature = "multicore")]
                    let advice = advice_witnesses.par_iter();
                    #[cfg(not(feature = "multicore"))]
                    let advice = advice_witnesses.iter();
                    advice
                        .map(|(advice, _)| {
                            domain.batch_lagrange_to_coeff_and_extended(advice, &pk.fft_twiddles)
                        })
                        .collect::<Vec<_>>()
                },
            );

            advice_witnesses
                .into_iter()
                .zip(advice_commitments)
                .zip(transforms)
                .map(
                    |(
                        ((advice, advice_blinds), advice_commitments),
                        (advice_polys, advice_cosets),
                    )| {
                        (
                            advice_commitments,
                            AdviceSingle::<C> {
                                advice_values: advice,
                                advice_polys,
                                advice_cosets,
                                advice_blinds,
                            },
                        )
                    },
                )
                .collect::<Vec<_>>()
        },
        || {
            lookup::prover::prepare_table_plan(
                &pk.vk.cs.lookups,
                circuit_count,
                unusable_rows_start,
            )
        },
    );

    let mut advice = Vec::with_capacity(prepared_advice.len());
    for (advice_commitments, advice_single) in prepared_advice {
        for commitment in advice_commitments {
            transcript.write_point(commitment)?;
        }
        advice.push(advice_single);
    }

    // Create polynomial evaluator context for values.
    let mut value_evaluator = poly::new_evaluator(|| {});

    // Register fixed values with the polynomial evaluator.
    let fixed_values: Vec<_> = pk
        .fixed_values
        .iter()
        .map(|poly| value_evaluator.register_poly_ref(poly))
        .collect();

    // Register advice values with the polynomial evaluator.
    let advice_values: Vec<_> = advice
        .iter()
        .map(|advice| {
            advice
                .advice_values
                .iter()
                .map(|poly| value_evaluator.register_poly_ref(poly))
                .collect::<Vec<_>>()
        })
        .collect();

    // Register instance values with the polynomial evaluator.
    let instance_values: Vec<_> = instance
        .iter()
        .map(|instance| {
            instance
                .instance_values
                .iter()
                .map(|poly| value_evaluator.register_poly_ref(poly))
                .collect::<Vec<_>>()
        })
        .collect();

    // Create polynomial evaluator context for cosets.
    let mut coset_evaluator = poly::new_evaluator(|| {});

    // Register fixed cosets with the polynomial evaluator.
    let fixed_cosets: Vec<_> = pk
        .fixed_cosets
        .iter()
        .enumerate()
        .map(|(column_index, poly)| {
            coset_evaluator
                .register_poly_ref_with_tag(poly, QuotientPoly::Fixed { column_index }.into())
        })
        .collect();

    for (family_index, family) in pk.cached_selector_families.iter().enumerate() {
        let query_and_first_selector = fixed_cosets[family.column_index];
        let combination_len = family.selectors.len() + 1;
        coset_evaluator.register_compressed_selector(
            query_and_first_selector,
            combination_len,
            1,
            query_and_first_selector,
        );
        for (assigned_root, selector) in (2..).zip(family.selectors.iter()) {
            let precomputed = coset_evaluator.register_poly_ref_with_tag(
                selector,
                QuotientPoly::Selector {
                    family_index,
                    assigned_root,
                }
                .into(),
            );
            coset_evaluator.register_compressed_selector(
                query_and_first_selector,
                combination_len,
                assigned_root,
                precomputed,
            );
        }
    }

    // Register advice cosets with the polynomial evaluator.
    let advice_cosets: Vec<_> = advice
        .iter()
        .enumerate()
        .map(|(circuit_index, advice)| {
            advice
                .advice_cosets
                .iter()
                .enumerate()
                .map(|(column_index, poly)| {
                    coset_evaluator.register_poly_ref_with_tag(
                        poly,
                        QuotientPoly::Advice {
                            circuit_index,
                            column_index,
                        }
                        .into(),
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect();

    // Register instance cosets with the polynomial evaluator.
    let instance_cosets: Vec<_> = instance
        .iter()
        .enumerate()
        .map(|(circuit_index, instance)| {
            instance
                .instance_cosets
                .iter()
                .enumerate()
                .map(|(column_index, poly)| {
                    coset_evaluator.register_poly_ref_with_tag(
                        poly,
                        QuotientPoly::Instance {
                            circuit_index,
                            column_index,
                        }
                        .into(),
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect();

    // Register permutation cosets with the polynomial evaluator.
    let permutation_cosets: Vec<_> = pk
        .permutation
        .cosets
        .iter()
        .enumerate()
        .map(|(column_index, poly)| {
            coset_evaluator
                .register_poly_ref_with_tag(poly, QuotientPoly::Permutation { column_index }.into())
        })
        .collect();

    // Register boundary polynomials used in the lookup and permutation arguments.
    let l0 = coset_evaluator.register_poly_ref_with_tag(&pk.l0, QuotientPoly::L0.into());
    let l_blind =
        coset_evaluator.register_poly_ref_with_tag(&pk.l_blind, QuotientPoly::LBlind.into());
    let l_last = coset_evaluator.register_poly_ref_with_tag(&pk.l_last, QuotientPoly::LLast.into());

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();

    // A plan candidate lets lookup preparation omit its symbolic quotient
    // ASTs. Evaluator-shape validation remains deferred until every
    // polynomial has been registered; a rejected candidate reconstructs them
    // on the ordinary compilation path below.
    let circuit_count = instance_values.len();
    let compiled_plan = pk.quotient_plans.get(circuit_count);
    let build_lookup_quotient_asts = compiled_plan.is_none();

    let lookup_count = pk.vk.cs.lookups.len();
    let mut lookup_tasks = Vec::new();
    // Draw all blinding values in circuit-major, lookup-major order before
    // preparing the independent lookup arguments in parallel.
    for circuit_index in 0..instance_values.len() {
        for lookup_index in 0..lookup_count {
            let blinding = lookup::prover::sample_permuted_blinding(pk, &mut rng);
            lookup_tasks.push((circuit_index, lookup_index, blinding));
        }
    }

    let prepared_lookups = lookup::prover::prepare_permuted(
        &pk.vk.cs.lookups,
        lookup_table_plan,
        lookup_tasks,
        pk,
        params,
        domain,
        &value_evaluator,
        theta,
        &advice_values,
        &fixed_values,
        &instance_values,
        &advice_cosets,
        &fixed_cosets,
        &instance_cosets,
        build_lookup_quotient_asts,
    )?;

    let mut prepared_lookups = prepared_lookups.into_iter();
    let lookups: Vec<Vec<lookup::prover::Permuted<C, _>>> = (0..circuit_count)
        .map(|circuit_index| {
            (0..lookup_count)
                .map(|lookup_index| {
                    prepared_lookups
                        .next()
                        .expect("one prepared lookup per task")
                        .finalize(
                            &mut coset_evaluator,
                            transcript,
                            circuit_index,
                            lookup_index,
                        )
                })
                .collect()
        })
        .collect::<Result<Vec<_>, _>>()?;
    debug_assert!(prepared_lookups.next().is_none());

    // Sample beta challenge
    let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();

    // Sample gamma challenge
    let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();

    let permutation_workers = crate::multicore::current_num_threads();
    let permutation_set_count = pk.vk.cs.permutation.set_count(pk.vk.cs_degree);
    let prepare_nested_permutation_sets = prepare_nested_permutation_sets_in_parallel::<C>(
        instance.len(),
        permutation_set_count,
        permutation_workers,
        params.n as usize,
    );
    let permutations: Vec<permutation::prover::Committed<C, _>> = if instance.len() == 1
        && prepare_permutation_sets_in_parallel::<C>(
            permutation_set_count,
            permutation_workers,
            params.n as usize,
        ) {
        // A single circuit cannot use circuit-level permutation parallelism.
        // Prepare its independent sets concurrently, then retain transcript
        // writes in set order.
        let blinding = pk.vk.cs.permutation.sample_blinding(pk, &mut rng);
        let prepared = pk.vk.cs.permutation.prepare_sets_in_parallel(
            params,
            pk,
            &pk.permutation,
            &advice[0].advice_values,
            &pk.fixed_values,
            &instance[0].instance_values,
            beta,
            gamma,
            blinding,
        );
        vec![prepared.commit(&mut coset_evaluator, transcript, 0)?]
    } else if prepare_permutations_in_parallel(instance.len(), permutation_workers) {
        // Draw every permutation's blinding values in circuit and set
        // order before preparing the independent arguments in parallel.
        let permutation_blindings = (0..instance.len())
            .map(|_| pk.vk.cs.permutation.sample_blinding(pk, &mut rng))
            .collect::<Vec<_>>();

        // When the aggregate scratch remains bounded, let each circuit expose
        // its independent set work to the same pool. The per-circuit product
        // prefix and the eventual transcript writes retain their order.
        let prepared_permutations = (0..instance.len())
            .into_par_iter()
            .zip(permutation_blindings.into_par_iter())
            .map(|(circuit_index, blinding)| {
                if prepare_nested_permutation_sets {
                    pk.vk.cs.permutation.prepare_sets_in_parallel(
                        params,
                        pk,
                        &pk.permutation,
                        &advice[circuit_index].advice_values,
                        &pk.fixed_values,
                        &instance[circuit_index].instance_values,
                        beta,
                        gamma,
                        blinding,
                    )
                } else {
                    pk.vk.cs.permutation.prepare(
                        params,
                        pk,
                        &pk.permutation,
                        &advice[circuit_index].advice_values,
                        &pk.fixed_values,
                        &instance[circuit_index].instance_values,
                        beta,
                        gamma,
                        blinding,
                    )
                }
            })
            .collect::<Vec<_>>();

        prepared_permutations
            .into_iter()
            .enumerate()
            .map(|(circuit_index, permutation)| {
                permutation.commit(&mut coset_evaluator, transcript, circuit_index)
            })
            .collect::<Result<Vec<_>, _>>()?
    } else {
        // Keep each circuit's preparation and commitment together on smaller
        // pools to avoid competing for cache across circuits.
        instance
            .iter()
            .zip(advice.iter())
            .enumerate()
            .map(|(circuit_index, (instance, advice))| {
                pk.vk.cs.permutation.commit(
                    params,
                    pk,
                    &pk.permutation,
                    &advice.advice_values,
                    &pk.fixed_values,
                    &instance.instance_values,
                    beta,
                    gamma,
                    circuit_index,
                    &mut coset_evaluator,
                    &mut rng,
                    transcript,
                )
            })
            .collect::<Result<Vec<_>, _>>()?
    };

    debug_assert_eq!(lookups.len(), circuit_count);
    let mut lookup_product_tasks = Vec::with_capacity(circuit_count * lookup_count);
    // Draw all blinding values in circuit-major, lookup-major order before
    // preparing the independent lookup products in parallel.
    for circuit_lookups in lookups {
        debug_assert_eq!(circuit_lookups.len(), lookup_count);
        for lookup in circuit_lookups {
            let blinding = lookup::prover::sample_product_blinding(pk, &mut rng);
            lookup_product_tasks.push((lookup, blinding));
        }
    }

    let prepared_lookup_products = lookup_product_tasks
        .into_par_iter()
        .map(|(lookup, blinding)| lookup.prepare_product(pk, params, beta, gamma, blinding))
        .collect::<Vec<_>>();

    let mut prepared_lookup_products = prepared_lookup_products.into_iter();
    let lookups: Vec<Vec<lookup::prover::Committed<C, _>>> = (0..circuit_count)
        .map(|circuit_index| {
            (0..lookup_count)
                .map(|lookup_index| {
                    prepared_lookup_products
                        .next()
                        .expect("one prepared lookup product per task")
                        .finalize(
                            &mut coset_evaluator,
                            transcript,
                            circuit_index,
                            lookup_index,
                        )
                })
                .collect()
        })
        .collect::<Result<Vec<_>, _>>()?;
    debug_assert!(prepared_lookup_products.next().is_none());

    // Commit to the random polynomial that masks the folded quotient
    // evaluation in the multi-opening argument.
    let vanishing = vanishing::Argument::commit_random_polynomial(params, &mut rng, transcript)?;

    // Obtain challenge for keeping all separate gates linearly independent
    let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();

    // Validate a keygen-prepared plan before using it to bypass every
    // challenge-bound constraint AST allocation. A mismatch takes the full
    // construction path and can replace the retained plan safely.
    let compiled_plan = compiled_plan.filter(|plan| coset_evaluator.accepts_compiled_plan(plan));
    let (permutations, lookups, expressions) = if compiled_plan.is_some() {
        let permutations = permutations
            .into_iter()
            .map(permutation::prover::Committed::into_constructed)
            .collect();
        let lookups = lookups
            .into_iter()
            .map(|lookups| {
                lookups
                    .into_iter()
                    .map(lookup::prover::Committed::into_constructed)
                    .collect()
            })
            .collect();
        (permutations, lookups, vec![])
    } else {
        // Build quotient ASTs only for an unprepared or mismatched shape.
        let (permutations, permutation_expressions): (Vec<_>, Vec<Vec<_>>) = permutations
            .into_iter()
            .zip(advice_cosets.iter())
            .zip(instance_cosets.iter())
            .map(|((permutation, advice), instance)| {
                let (constructed, expressions) = permutation.construct(
                    pk,
                    &pk.vk.cs.permutation,
                    advice,
                    &fixed_cosets,
                    instance,
                    &permutation_cosets,
                    l0,
                    l_blind,
                    l_last,
                );
                (constructed, expressions.collect())
            })
            .unzip();

        let (lookups, lookup_expressions): (Vec<Vec<_>>, Vec<Vec<Vec<_>>>) = lookups
            .into_iter()
            .zip(advice_cosets.iter())
            .zip(instance_cosets.iter())
            .map(|((lookups, advice_cosets), instance_cosets)| {
                lookups
                    .into_iter()
                    .zip(meta.lookups.iter())
                    .map(|(lookup, argument)| {
                        let (constructed, expressions) = lookup.construct(
                            argument,
                            &fixed_cosets,
                            advice_cosets,
                            instance_cosets,
                            l0,
                            l_blind,
                            l_last,
                        );
                        (constructed, expressions.collect())
                    })
                    .unzip()
            })
            .unzip();

        let expressions = advice_cosets
            .iter()
            .zip(instance_cosets.iter())
            .zip(permutation_expressions)
            .zip(lookup_expressions)
            .flat_map(
                |(
                    ((advice_cosets, instance_cosets), permutation_expressions),
                    lookup_expressions,
                )| {
                    let fixed_cosets = &fixed_cosets;
                    iter::empty()
                        .chain(meta.gates.iter().flat_map(move |gate| {
                            gate.polynomials().iter().map(move |expression| {
                                evaluator_schedule::expression_ast(
                                    expression,
                                    fixed_cosets,
                                    advice_cosets,
                                    instance_cosets,
                                )
                            })
                        }))
                        .chain(permutation_expressions)
                        .chain(lookup_expressions.into_iter().flatten())
                },
            )
            .collect();
        (permutations, lookups, expressions)
    };

    // Construct and commit to the quotient polynomial h(X).
    let (vanishing, prepared_plan) = vanishing.construct_quotient(
        params,
        domain,
        &pk.fft_twiddles,
        coset_evaluator,
        expressions.into_iter(),
        theta,
        beta,
        gamma,
        y,
        compiled_plan.as_deref(),
        &mut rng,
        transcript,
    )?;
    if let Some(plan) = prepared_plan {
        pk.quotient_plans.retain(circuit_count, plan);
    }

    let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();
    let xn = super::pow_by_power_of_two(*x, params.k);
    let polynomial_evaluator = PolynomialEvaluator::new(
        [
            *x,
            domain.rotate_omega(*x, poly::Rotation::next()),
            domain.rotate_omega(*x, poly::Rotation::prev()),
            domain.rotate_omega(*x, poly::Rotation(-((meta.blinding_factors() + 1) as i32))),
        ],
        params.n as usize,
        advice.len(),
    );

    // Compute and hash instance evals for each circuit instance
    let instance_queries = instance
        .iter()
        .flat_map(|instance| {
            meta.instance_queries
                .iter()
                .map(move |&(column, rotation)| EvaluationQuery {
                    polynomial: &instance.instance_polys[column.index()],
                    point: EvaluationPoint::from_rotation(
                        rotation,
                        meta.blinding_factors(),
                        || domain.rotate_omega(*x, rotation),
                    ),
                })
        })
        .collect::<Vec<_>>();
    // Collect advice evals for each circuit instance.
    let advice_queries = advice
        .iter()
        .flat_map(|advice| {
            meta.advice_queries
                .iter()
                .map(move |&(column, rotation)| EvaluationQuery {
                    polynomial: &advice.advice_polys[column.index()],
                    point: EvaluationPoint::from_rotation(
                        rotation,
                        meta.blinding_factors(),
                        || domain.rotate_omega(*x, rotation),
                    ),
                })
        })
        .collect::<Vec<_>>();
    // Collect fixed evals, which are shared across all circuit instances.
    let fixed_queries = meta
        .fixed_queries
        .iter()
        .map(|&(column, rotation)| EvaluationQuery {
            polynomial: &pk.fixed_polys[column.index()],
            point: EvaluationPoint::from_rotation(rotation, meta.blinding_factors(), || {
                domain.rotate_omega(*x, rotation)
            }),
        })
        .collect::<Vec<_>>();
    let queries = instance_queries
        .into_iter()
        .chain(advice_queries)
        .chain(fixed_queries)
        .collect::<Vec<_>>();
    let initial_evaluation_count = queries.len();
    let mut queries = queries;
    queries.extend(pk.permutation.evaluation_queries());
    for permutation in &permutations {
        queries.extend(permutation.evaluation_queries());
    }
    for lookups in &lookups {
        for lookup in lookups {
            queries.extend(lookup.evaluation_queries());
        }
    }

    // All evaluations below depend only on x. Evaluate them as one batch so
    // that small argument-local query sets share the same worker wave, then
    // preserve the protocol's transcript order while consuming the results.
    let evaluations = polynomial_evaluator.evaluate(&queries);
    drop(queries);
    let mut evaluations = evaluations.into_iter();
    for _ in 0..initial_evaluation_count {
        let evaluation = evaluations
            .next()
            .expect("one result is returned for every initial evaluation query");
        transcript.write_scalar(evaluation)?;
    }

    let vanishing = vanishing.evaluate(*x, xn, domain, transcript)?;

    // Evaluate common permutation data
    pk.permutation.evaluate(&mut evaluations, transcript)?;

    // Evaluate the permutations, if any, at omega^i x.
    let permutations: Vec<permutation::prover::Evaluated<C>> = permutations
        .into_iter()
        .map(|permutation| -> Result<_, _> { permutation.evaluate(&mut evaluations, transcript) })
        .collect::<Result<Vec<_>, _>>()?;

    // Evaluate the lookups, if any, at omega^i x.
    let lookups: Vec<Vec<lookup::prover::Evaluated<C>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            lookups
                .into_iter()
                .map(|p| p.evaluate(&mut evaluations, transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    assert!(
        evaluations.next().is_none(),
        "one result is consumed for every batched polynomial evaluation query",
    );

    let instances = instance
        .iter()
        .zip(advice.iter())
        .zip(permutations.iter())
        .zip(lookups.iter())
        .flat_map(|(((instance, advice), permutation), lookups)| {
            iter::empty()
                .chain(
                    pk.vk
                        .cs
                        .instance_queries
                        .iter()
                        .map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(*x, at),
                            poly: &instance.instance_polys[column.index()],
                            blind: Blind::default(),
                        }),
                )
                .chain(
                    pk.vk
                        .cs
                        .advice_queries
                        .iter()
                        .map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(*x, at),
                            poly: &advice.advice_polys[column.index()],
                            blind: advice.advice_blinds[column.index()],
                        }),
                )
                .chain(permutation.open(pk, x))
                .chain(lookups.iter().flat_map(move |p| p.open(pk, x)))
        })
        .chain(
            pk.vk
                .cs
                .fixed_queries
                .iter()
                .map(|&(column, at)| ProverQuery {
                    point: domain.rotate_omega(*x, at),
                    poly: &pk.fixed_polys[column.index()],
                    blind: Blind::default(),
                }),
        )
        .chain(pk.permutation.open(x))
        // Keep these last among queries at x: the linear quotient-evaluation
        // mask must have unit coefficient in its point-set fold at x_3.
        .chain(vanishing.open(x));

    multiopen::create_proof(params, rng, transcript, instances).map_err(|_| Error::Opening)
}

#[test]
fn permutation_outer_parallelism_reserves_inner_capacity() {
    for (circuits, workers, expected) in [
        (1, 10, false),
        (2, 2, false),
        (2, 3, false),
        (2, 4, true),
        (3, 4, false),
        (3, 5, true),
        (3, 6, true),
        (3, 10, true),
        (4, 5, false),
        (4, 6, true),
        (4, 10, true),
    ] {
        assert_eq!(
            prepare_permutations_in_parallel(circuits, workers),
            expected
        );
    }
}

#[test]
fn permutation_set_parallelism_limits_scratch() {
    use pasta_curves::EqAffine;

    const SMALL_DOMAIN_SIZE: usize = 1 << 11;
    const LARGE_DOMAIN_SIZE: usize = 1 << 14;

    assert!(prepare_permutation_sets_in_parallel::<EqAffine>(
        3,
        6,
        SMALL_DOMAIN_SIZE,
    ));
    assert!(!prepare_permutation_sets_in_parallel::<EqAffine>(
        3,
        4,
        SMALL_DOMAIN_SIZE,
    ));
    assert!(!prepare_permutation_sets_in_parallel::<EqAffine>(
        3,
        6,
        LARGE_DOMAIN_SIZE,
    ));

    assert!(prepare_nested_permutation_sets_in_parallel::<EqAffine>(
        4,
        3,
        10,
        SMALL_DOMAIN_SIZE,
    ));
    assert!(!prepare_nested_permutation_sets_in_parallel::<EqAffine>(
        1,
        3,
        10,
        SMALL_DOMAIN_SIZE,
    ));
    assert!(!prepare_nested_permutation_sets_in_parallel::<EqAffine>(
        4,
        3,
        5,
        SMALL_DOMAIN_SIZE,
    ));
    assert!(!prepare_nested_permutation_sets_in_parallel::<EqAffine>(
        8,
        3,
        10,
        SMALL_DOMAIN_SIZE,
    ));
    assert!(!prepare_nested_permutation_sets_in_parallel::<EqAffine>(
        4,
        3,
        10,
        LARGE_DOMAIN_SIZE,
    ));
}

#[test]
fn test_commit_instance() {
    use ff::FromUniformBytes;
    use pasta_curves::{EpAffine, EqAffine, Fp, Fq};

    macro_rules! check_curve {
        ($curve:ty, $scalar:ty) => {{
            const K: u32 = 6;

            let params: Params<$curve> = Params::new(K);
            let domain = crate::poly::EvaluationDomain::new(1, K);

            for len in [0, 1, 10, 17, 63] {
                let mut instance = (0..len)
                    .map(|index| {
                        let mut bytes = [0; 64];
                        for (offset, byte) in bytes.iter_mut().enumerate() {
                            *byte = (index as u8)
                                .wrapping_mul(73)
                                .wrapping_add((offset as u8).wrapping_mul(29))
                                .wrapping_add(17);
                        }
                        <$scalar as FromUniformBytes<64>>::from_uniform_bytes(&bytes)
                    })
                    .collect::<Vec<_>>();
                if let Some(value) = instance.get_mut(0) {
                    *value = <$scalar>::ZERO;
                }
                if let Some(value) = instance.get_mut(1) {
                    *value = <$scalar>::ONE;
                }
                if let Some(value) = instance.get_mut(2) {
                    *value = -<$scalar>::ONE;
                }

                let mut poly = domain.empty_lagrange();
                for (coefficient, value) in poly.iter_mut().zip(&instance) {
                    *coefficient = *value;
                }

                assert_eq!(
                    commit_instance(&params, &instance),
                    params.commit_lagrange(&poly, Blind::default())
                );
            }
        }};
    }

    check_curve!(EqAffine, Fp);
    check_curve!(EpAffine, Fq);
}

#[cfg(feature = "batch")]
#[test]
fn prepared_instance_signed_digit_boundaries() {
    let cases = [
        (0x00, 0, 0, false),
        (0x07, 0, 7, false),
        (0x08, 0, 8, true),
        (0x0f, 0, 1, true),
        (0x08, 1, 1, false),
        (0x78, 1, 8, false),
        (0x88, 1, 7, true),
        (0xf8, 1, 0, false),
    ];

    for (byte, window, magnitude, negative) in cases {
        let little = [byte, 0];
        let big = [0, byte];
        let expected = PreparedInstanceDigit {
            magnitude,
            negative,
        };
        assert_eq!(
            instance_scalar_digit(
                &little,
                window,
                u8::BITS as usize * little.len(),
                InstanceScalarByteOrder::LittleEndian,
            ),
            expected,
        );
        assert_eq!(
            instance_scalar_digit(
                &big,
                window,
                u8::BITS as usize * big.len(),
                InstanceScalarByteOrder::BigEndian,
            ),
            expected,
        );
    }

    // A scalar bit length ending on a window boundary needs one carry-only
    // window. The high half of the last data window carries into it.
    assert_eq!(crate::prepared_instance_window_count(8), 3);
    assert_eq!(
        instance_scalar_digit(&[0x80], 2, 8, InstanceScalarByteOrder::LittleEndian),
        PreparedInstanceDigit {
            magnitude: 1,
            negative: false,
        },
    );
}

#[cfg(feature = "batch")]
#[test]
fn prepared_instance_signed_windows_match_native_products() {
    use pasta_curves::{EpAffine, EqAffine, Fp, Fq};

    macro_rules! check_curve {
        ($curve:ty, $scalar:ty) => {{
            const K: u32 = 4;

            let params = Params::<$curve>::new(K);
            assert!(params.prepare_instance_table());
            let table = params.prepared_instance_table().unwrap();
            let mut terms = vec![];
            let mut expected = vec![];
            let mut push = |scalar: $scalar| {
                let base_index = terms.len() % PREPARED_INSTANCE_DENSE_ROWS;
                terms.push((base_index, scalar));
                expected.push(params.g_lagrange[base_index] * scalar);
            };

            let mut power = <$scalar>::ONE;
            for bit in 0..<$scalar as PrimeField>::NUM_BITS as usize {
                if bit >= PREPARED_INSTANCE_WINDOW_BITS - 1
                    && (bit - (PREPARED_INSTANCE_WINDOW_BITS - 1)) % PREPARED_INSTANCE_WINDOW_BITS
                        == 0
                {
                    let below = power - <$scalar>::ONE;
                    let above = power + <$scalar>::ONE;
                    for scalar in [below, power, above, -below, -power, -above] {
                        push(scalar);
                    }
                }
                power = power.double();
            }

            let mut top_bit = <$scalar>::ONE;
            for _ in 1..<$scalar as PrimeField>::NUM_BITS {
                top_bit = top_bit.double();
            }
            for scalar in [
                top_bit - <$scalar>::ONE,
                top_bit,
                top_bit + <$scalar>::ONE,
                -top_bit,
            ] {
                push(scalar);
            }

            assert_eq!(
                evaluate_prepared_instance_terms(&table, &terms)
                    .expect("Pasta scalar representations are supported"),
                expected,
            );
        }};
    }

    check_curve!(EqAffine, Fp);
    check_curve!(EpAffine, Fq);
}

#[cfg(feature = "batch")]
#[test]
fn prepared_instance_commitments_match_generic_msm() {
    use ff::FromUniformBytes;
    use pasta_curves::{EpAffine, EqAffine, Fp, Fq};

    macro_rules! check_curve {
        ($curve:ty, $scalar:ty) => {{
            const K: u32 = 6;

            let params = Params::<$curve>::new(K);
            assert!(params.prepare_instance_table());

            let scalar = |proof: usize, row: usize| {
                let mut bytes = [0; 64];
                for (offset, byte) in bytes.iter_mut().enumerate() {
                    *byte = (proof as u8)
                        .wrapping_mul(97)
                        .wrapping_add((row as u8).wrapping_mul(53))
                        .wrapping_add((offset as u8).wrapping_mul(29))
                        .wrapping_add(11);
                }
                <$scalar as FromUniformBytes<64>>::from_uniform_bytes(&bytes)
            };

            for proofs in [1, 2, 3, 8] {
                let mut owned = (0..proofs)
                    .map(|proof| {
                        let mut instance = (0..PREPARED_INSTANCE_ROWS)
                            .map(|row| scalar(proof, row))
                            .collect::<Vec<_>>();
                        // Exercise runtime sharing of two dense rows. The five
                        // other rows differ whenever the batch has two proofs.
                        instance[0] = scalar(0, 0);
                        instance[3] = scalar(0, 3);
                        for flag in 0..PREPARED_INSTANCE_BOOLEAN_ROWS {
                            instance[PREPARED_INSTANCE_DENSE_ROWS + flag] =
                                <$scalar>::from(((proof >> flag) & 1) as u64);
                        }
                        vec![instance]
                    })
                    .collect::<Vec<_>>();
                // Pin the scalar edge cases used by the signed-window
                // evaluator for every batch size that can contain them.
                owned[0][0][1] = <$scalar>::ZERO;
                if let Some(proof) = owned.get_mut(1) {
                    proof[0][2] = <$scalar>::ONE;
                }
                if let Some(proof) = owned.get_mut(2) {
                    proof[0][4] = -<$scalar>::ONE;
                }

                let column_refs = owned
                    .iter()
                    .map(|columns| columns.iter().map(Vec::as_slice).collect::<Vec<_>>())
                    .collect::<Vec<_>>();
                let instance_refs = column_refs.iter().map(Vec::as_slice).collect::<Vec<_>>();
                let actual = commit_prepared_instances(&params, &instance_refs)
                    .expect("the prepared exact-shape path is armed");

                for (proof, columns) in instance_refs.iter().enumerate() {
                    assert_eq!(actual[proof].len(), PREPARED_INSTANCE_COLUMNS);
                    assert_eq!(actual[proof][0], commit_instance(&params, columns[0]));
                }

                let mut non_boolean = owned[0][0].clone();
                non_boolean[PREPARED_INSTANCE_DENSE_ROWS] = <$scalar>::from(2);
                let non_boolean_columns = [non_boolean.as_slice()];
                let non_boolean_proofs = [&non_boolean_columns[..]];
                assert!(commit_prepared_instances(&params, &non_boolean_proofs).is_none());
            }
        }};
    }

    check_curve!(EqAffine, Fp);
    check_curve!(EpAffine, Fq);
}

#[test]
fn test_create_proof() {
    use crate::{
        circuit::SimpleFloorPlanner,
        plonk::{keygen_pk, keygen_vk},
        transcript::{Blake2bWrite, Challenge255},
    };
    use pasta_curves::EqAffine;
    use rand::rng;

    #[derive(Clone, Copy)]
    struct MyCircuit;

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = ();

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {}

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), Error> {
            Ok(())
        }
    }

    let params: Params<EqAffine> = Params::new(3);
    let vk = keygen_vk(&params, &MyCircuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &MyCircuit).expect("keygen_pk should not fail");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    // Create proof with wrong number of instances
    let proof = create_proof(
        &params,
        &pk,
        &[MyCircuit, MyCircuit],
        &[],
        rng(),
        &mut transcript,
    );
    assert!(matches!(proof.unwrap_err(), Error::InvalidInstances));

    // Create proof with correct number of instances
    create_proof(
        &params,
        &pk,
        &[MyCircuit, MyCircuit],
        &[&[], &[]],
        rng(),
        &mut transcript,
    )
    .expect("proof generation should not fail");
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[test]
fn sampled_advice_delta_counts_require_global_savings() {
    assert_eq!(
        use_sampled_advice_delta_counts(&[(ADVICE_DELTA_MIN_SAMPLED_SAVINGS - 1, 0)]),
        Some(false),
    );
    assert_eq!(
        use_sampled_advice_delta_counts(&[(ADVICE_DELTA_MIN_SAMPLED_SAVINGS, 0)]),
        Some(true),
    );

    // The fractional threshold is strict.
    let direct = ADVICE_DELTA_COUNT_SAMPLES;
    let delta = direct - direct / ADVICE_DELTA_ROUTE_DENOMINATOR;
    let exactly_one_eighth = [(direct, delta); ADVICE_DELTA_ROUTE_DENOMINATOR];
    assert_eq!(
        use_sampled_advice_delta_counts(&exactly_one_eighth),
        Some(false),
    );
    let mut more_than_one_eighth = exactly_one_eighth;
    more_than_one_eighth[0].1 -= 1;
    assert_eq!(
        use_sampled_advice_delta_counts(&more_than_one_eighth),
        Some(true),
    );

    // No individual column may gain sampled nonzero coefficients, even when
    // the aggregate would otherwise pass.
    assert_eq!(
        use_sampled_advice_delta_counts(&[
            (ADVICE_DELTA_COUNT_SAMPLES, 0),
            (ADVICE_DELTA_COUNT_SAMPLES, 0),
            (0, 1),
        ]),
        Some(false),
    );

    // Overflow declines the route instead of wrapping into a decision.
    assert_eq!(
        use_sampled_advice_delta_counts(&[(usize::MAX, usize::MAX), (usize::MAX, usize::MAX),]),
        None,
    );
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[test]
fn advice_delta_samples_one_row_per_stratum() {
    const POLYNOMIAL_LEN: usize = 1 << ADVICE_DELTA_PREPARED_K;

    for sample in 0..ADVICE_DELTA_COUNT_SAMPLES {
        let row = advice_delta_stratified_row(POLYNOMIAL_LEN, ADVICE_DELTA_COUNT_SAMPLES, sample)
            .unwrap();
        let start = sample * POLYNOMIAL_LEN / ADVICE_DELTA_COUNT_SAMPLES;
        let end = (sample + 1) * POLYNOMIAL_LEN / ADVICE_DELTA_COUNT_SAMPLES;
        assert!((start..end).contains(&row));
    }

    assert_eq!(advice_delta_stratified_row(0, 1, 0), None);
    assert_eq!(advice_delta_stratified_row(1, 0, 0), None);
    assert_eq!(advice_delta_stratified_row(1, 1, 1), None);
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[test]
fn advice_delta_sample_counts_zeroes_and_equalities() {
    use pasta_curves::Fp;

    let reference = [Fp::ZERO, Fp::ONE, Fp::from(2), Fp::ZERO];
    let direct = [Fp::ZERO, Fp::ONE, Fp::ZERO, Fp::from(3)];
    assert_eq!(
        sampled_advice_delta_nonzero_counts(&direct, &reference, direct.len()),
        Some((2, 2)),
    );
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[test]
fn malformed_advice_delta_shapes_fall_back() {
    use pasta_curves::{EqAffine, Fp};

    let params = Params::<EqAffine>::new(ADVICE_DELTA_PREPARED_K);
    let domain = poly::EvaluationDomain::<Fp>::new(3, ADVICE_DELTA_PREPARED_K);
    let smaller_domain = poly::EvaluationDomain::<Fp>::new(3, ADVICE_DELTA_PREPARED_K - 1);

    let empty_columns = vec![(Vec::new(), Vec::new()), (Vec::new(), Vec::new())];
    assert!(plan_advice_deltas(&params, &domain, &empty_columns).is_none());

    let mismatched_columns = vec![
        (vec![domain.empty_lagrange()], vec![Blind::<Fp>::default()]),
        (
            vec![domain.empty_lagrange(), domain.empty_lagrange()],
            vec![Blind::<Fp>::default(), Blind::<Fp>::default()],
        ),
    ];
    assert!(plan_advice_deltas(&params, &domain, &mismatched_columns).is_none());

    let mismatched_blinds = vec![
        (vec![domain.empty_lagrange()], vec![Blind::<Fp>::default()]),
        (vec![domain.empty_lagrange()], Vec::new()),
    ];
    assert!(plan_advice_deltas(&params, &domain, &mismatched_blinds).is_none());

    let mismatched_lengths = vec![
        (vec![domain.empty_lagrange()], vec![Blind::<Fp>::default()]),
        (
            vec![smaller_domain.empty_lagrange()],
            vec![Blind::<Fp>::default()],
        ),
    ];
    assert!(plan_advice_deltas(&params, &domain, &mismatched_lengths).is_none());
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
#[test]
fn advice_delta_commitments_preserve_proofs() {
    use crate::{
        circuit::{Layouter, SimpleFloorPlanner},
        plonk::{SingleVerifier, keygen_pk, keygen_vk, verify_proof},
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use ff::{FromUniformBytes, PrimeField};
    use pasta_curves::{EqAffine, Fp};
    use rand::{SeedableRng, rngs::StdRng};

    const ASSIGNED_ROWS: usize = 1100;
    const ADVICE_COLUMNS: usize = 10;
    const MAGNITUDE_SHARED_ROWS: usize = 700;
    const PROOF_SEED: u64 = 0x4144_5649_4345_444c;

    #[derive(Clone, Copy)]
    enum AdviceDeltaProfile {
        Similar,
        MagnitudeInversion,
        HighWindowSparse,
        MissedHighWindow,
    }

    #[derive(Clone, Copy)]
    struct AdviceDeltaCircuit {
        circuit_index: usize,
        shared_columns: usize,
        profile: AdviceDeltaProfile,
    }

    impl AdviceDeltaCircuit {
        fn is_router_sample(row: usize) -> bool {
            static SAMPLE_ROWS: std::sync::OnceLock<Vec<bool>> = std::sync::OnceLock::new();

            SAMPLE_ROWS.get_or_init(|| {
                let polynomial_len = 1_usize << ADVICE_DELTA_PREPARED_K;
                let mut rows = vec![false; polynomial_len];
                for sample_rows in [ADVICE_DELTA_COUNT_SAMPLES, ADVICE_DELTA_WORK_SAMPLES] {
                    for sample in 0..sample_rows {
                        let row = advice_delta_stratified_row(polynomial_len, sample_rows, sample)
                            .unwrap();
                        rows[row] = true;
                    }
                }
                rows
            })[row]
        }

        fn random_value(column: usize, row: usize) -> Fp {
            let mut state = u64::try_from(column * ASSIGNED_ROWS + row)
                .unwrap()
                .wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut bytes = [0_u8; 64];
            for chunk in bytes.chunks_exact_mut(8) {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                chunk.copy_from_slice(&state.to_le_bytes());
            }
            Fp::from_uniform_bytes(&bytes)
        }

        fn value(&self, column: usize, row: usize) -> Fp {
            match self.profile {
                AdviceDeltaProfile::Similar => {
                    let reference = Self::random_value(column, row);
                    if self.circuit_index == 0 || column < self.shared_columns {
                        // This profile models same-wallet witness reuse.
                        reference
                    } else {
                        // Every value at the same position differs from the
                        // reference by a low-work scalar.
                        let delta = self.circuit_index * ASSIGNED_ROWS + row + 1;
                        reference
                            + Fp::from(u64::try_from(delta).expect("test value fits into u64"))
                    }
                }
                AdviceDeltaProfile::MagnitudeInversion => {
                    let direct = Fp::from(u64::try_from(row + 1).unwrap());
                    if self.circuit_index == 0 && row >= MAGNITUDE_SHARED_ROWS {
                        direct - Self::random_value(column, row)
                    } else {
                        direct
                    }
                }
                AdviceDeltaProfile::HighWindowSparse => {
                    let direct = Fp::ONE;
                    if self.circuit_index == 0 && row % 4 != 0 {
                        direct - Fp::from_u128(1_u128 << 119)
                    } else {
                        direct
                    }
                }
                AdviceDeltaProfile::MissedHighWindow => {
                    let direct = Fp::ONE;
                    if self.circuit_index == 0 && !Self::is_router_sample(row) {
                        direct - Fp::from_u128(1_u128 << 119)
                    } else {
                        direct
                    }
                }
            }
        }
    }

    impl Circuit<Fp> for AdviceDeltaCircuit {
        type Config = [Column<Advice>; ADVICE_COLUMNS];
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                circuit_index: 0,
                shared_columns: self.shared_columns,
                profile: self.profile,
            }
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            std::array::from_fn(|_| meta.advice_column())
        }

        fn synthesize(
            &self,
            advice: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "advice delta profiles",
                |mut region| {
                    for (column_index, column) in advice.into_iter().enumerate() {
                        for row in 0..ASSIGNED_ROWS {
                            region.assign_advice(
                                || "value",
                                column,
                                row,
                                || Value::known(self.value(column_index, row)),
                            )?;
                        }
                    }
                    Ok(())
                },
            )
        }
    }

    fn proof(
        params: &Params<EqAffine>,
        pk: &ProvingKey<EqAffine>,
        circuits: &[AdviceDeltaCircuit],
        threads: usize,
        prepared: bool,
    ) -> Vec<u8> {
        let no_columns: &[&[Fp]] = &[];
        let instances = vec![no_columns; circuits.len()];
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap()
            .install(|| {
                assert_eq!(
                    params.prepared_lagrange_commitments_active(1 << ADVICE_DELTA_PREPARED_K),
                    prepared,
                );
                create_proof(
                    params,
                    pk,
                    circuits,
                    &instances,
                    StdRng::seed_from_u64(PROOF_SEED),
                    &mut transcript,
                )
            })
            .expect("proof generation should not fail");
        transcript.finalize()
    }

    fn verify(
        params: &Params<EqAffine>,
        pk: &ProvingKey<EqAffine>,
        circuit_count: usize,
        proof: &[u8],
    ) {
        let no_columns: &[&[Fp]] = &[];
        let instances = vec![no_columns; circuit_count];
        let strategy = SingleVerifier::new(params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof);
        verify_proof(params, pk.get_vk(), strategy, &instances, &mut transcript)
            .expect("proof verification should not fail");
    }

    fn compare_profiles(
        armed: &Params<EqAffine>,
        unarmed: &Params<EqAffine>,
        pk: &ProvingKey<EqAffine>,
        circuits: &[AdviceDeltaCircuit],
        expected_route_hits: usize,
        worker_counts: &[usize],
    ) {
        take_advice_delta_route_hits();
        let expected = proof(unarmed, pk, circuits, 1, false);
        assert_eq!(take_advice_delta_route_hits(), 0);
        verify(unarmed, pk, circuits.len(), &expected);

        for &threads in worker_counts {
            take_advice_delta_route_hits();
            let actual = proof(armed, pk, circuits, threads, true);
            assert_eq!(take_advice_delta_route_hits(), expected_route_hits);
            assert_eq!(actual, expected);
        }
    }

    let unarmed = Params::<EqAffine>::new(ADVICE_DELTA_PREPARED_K);
    let armed = Params::<EqAffine>::new(ADVICE_DELTA_PREPARED_K);
    let keygen_circuit = AdviceDeltaCircuit {
        circuit_index: 0,
        shared_columns: 2,
        profile: AdviceDeltaProfile::Similar,
    };
    let vk = keygen_vk(&unarmed, &keygen_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&unarmed, vk, &keygen_circuit).expect("keygen_pk should not fail");
    assert!(armed.prepare_commitments());

    for (circuit_count, worker_counts) in [(1, &[1][..]), (2, &[1, 4][..]), (4, &[1][..])] {
        let circuits = (0..circuit_count)
            .map(|circuit_index| AdviceDeltaCircuit {
                circuit_index,
                shared_columns: 2,
                profile: AdviceDeltaProfile::Similar,
            })
            .collect::<Vec<_>>();
        compare_profiles(
            &armed,
            &unarmed,
            &pk,
            &circuits,
            ADVICE_COLUMNS * circuit_count.saturating_sub(1),
            worker_counts,
        );
    }

    // A dissimilar second circuit exercises the exact original-schedule
    // fallback after the route scan finds no useful delta.
    let direct_only = [
        keygen_circuit,
        AdviceDeltaCircuit {
            circuit_index: 1,
            shared_columns: 0,
            profile: AdviceDeltaProfile::Similar,
        },
    ];
    compare_profiles(&armed, &unarmed, &pk, &direct_only, 0, &[1]);

    // Routing is independent per later circuit: a useful second circuit can
    // reuse the reference while a dissimilar third circuit commits directly.
    let mixed = [
        keygen_circuit,
        AdviceDeltaCircuit {
            circuit_index: 1,
            shared_columns: 2,
            profile: AdviceDeltaProfile::Similar,
        },
        AdviceDeltaCircuit {
            circuit_index: 2,
            shared_columns: 0,
            profile: AdviceDeltaProfile::Similar,
        },
    ];
    compare_profiles(&armed, &unarmed, &pk, &mixed, ADVICE_COLUMNS, &[1, 4]);

    // One useful column cannot amortize the circuit-wide path, so the sampled
    // aggregate gate retains the fallback.
    let globally_too_small = [
        keygen_circuit,
        AdviceDeltaCircuit {
            circuit_index: 1,
            shared_columns: 1,
            profile: AdviceDeltaProfile::Similar,
        },
    ];
    compare_profiles(&armed, &unarmed, &pk, &globally_too_small, 0, &[1]);

    // Counts alone strongly prefer these deltas, but their few nonzero
    // values are full-width while the direct scalars are small. The sampled
    // prepared-work comparison must retain the exact direct fallback.
    let magnitude_inversion = [
        AdviceDeltaCircuit {
            circuit_index: 0,
            shared_columns: 0,
            profile: AdviceDeltaProfile::MagnitudeInversion,
        },
        AdviceDeltaCircuit {
            circuit_index: 1,
            shared_columns: 0,
            profile: AdviceDeltaProfile::MagnitudeInversion,
        },
    ];
    compare_profiles(&armed, &unarmed, &pk, &magnitude_inversion, 0, &[1, 4]);

    // The count guard prefers a delta with one quarter zeroes over an all-one
    // direct polynomial. Its nonzero terms are 2^119, however, so they activate
    // almost every prepared main window. The per-evaluation work comparison
    // must retain the direct route.
    let direct = (0..(1_usize << ADVICE_DELTA_PREPARED_K))
        .map(|row| {
            if row < ASSIGNED_ROWS {
                Fp::ONE
            } else {
                Fp::ZERO
            }
        })
        .collect::<Vec<_>>();
    let reference = direct
        .iter()
        .enumerate()
        .map(|(row, &direct)| {
            if row < ASSIGNED_ROWS && row % 4 != 0 {
                direct - Fp::from_u128(1_u128 << 119)
            } else {
                direct
            }
        })
        .collect::<Vec<_>>();
    let counts = (0..ADVICE_COLUMNS)
        .map(|_| {
            sampled_advice_delta_nonzero_counts(&direct, &reference, ADVICE_DELTA_COUNT_SAMPLES)
        })
        .collect::<Option<Vec<_>>>()
        .unwrap();
    assert_eq!(use_sampled_advice_delta_counts(&counts), Some(true));

    let high_window_sparse = [
        AdviceDeltaCircuit {
            circuit_index: 0,
            shared_columns: 0,
            profile: AdviceDeltaProfile::HighWindowSparse,
        },
        AdviceDeltaCircuit {
            circuit_index: 1,
            shared_columns: 0,
            profile: AdviceDeltaProfile::HighWindowSparse,
        },
    ];
    compare_profiles(&armed, &unarmed, &pk, &high_window_sparse, 0, &[1, 4]);

    // A fixed work sample could otherwise miss every high-window delta. The
    // direct sample only contains unit scalars and therefore does not span the
    // prepared evaluator's main windows, so the conservative comparison must
    // retain the direct route.
    let direct = (0..(1_usize << ADVICE_DELTA_PREPARED_K))
        .map(|row| {
            if row < ASSIGNED_ROWS {
                Fp::ONE
            } else {
                Fp::ZERO
            }
        })
        .collect::<Vec<_>>();
    let reference = direct
        .iter()
        .enumerate()
        .map(|(row, &direct)| {
            if row < ASSIGNED_ROWS && !AdviceDeltaCircuit::is_router_sample(row) {
                direct - Fp::from_u128(1_u128 << 119)
            } else {
                direct
            }
        })
        .collect::<Vec<_>>();
    let counts = (0..ADVICE_COLUMNS)
        .map(|_| {
            sampled_advice_delta_nonzero_counts(&direct, &reference, ADVICE_DELTA_COUNT_SAMPLES)
        })
        .collect::<Option<Vec<_>>>()
        .unwrap();
    assert_eq!(use_sampled_advice_delta_counts(&counts), Some(true));

    let missed_high_window = [
        AdviceDeltaCircuit {
            circuit_index: 0,
            shared_columns: 0,
            profile: AdviceDeltaProfile::MissedHighWindow,
        },
        AdviceDeltaCircuit {
            circuit_index: 1,
            shared_columns: 0,
            profile: AdviceDeltaProfile::MissedHighWindow,
        },
    ];
    compare_profiles(&armed, &unarmed, &pk, &missed_high_window, 0, &[1, 4]);
}

#[test]
fn advice_witness_evaluates_rationals_and_reassignments() {
    use pasta_curves::Fp;

    let domain = poly::EvaluationDomain::new(3, 3);
    let mut advice = AdviceWitness::new(vec![domain.empty_lagrange(); 2]);

    advice
        .assign(0, 0, Assigned::Rational(Fp::from(6), Fp::from(3)))
        .unwrap();
    advice
        .assign(1, 1, Assigned::Rational(Fp::from(8), Fp::from(2)))
        .unwrap();

    // Removing the first denominator moves the second into its slot. Updating
    // that cell exercises the repaired sparse index after `swap_remove`.
    advice.assign(0, 0, Assigned::Trivial(Fp::from(5))).unwrap();
    advice
        .assign(1, 1, Assigned::Rational(Fp::from(9), Fp::from(3)))
        .unwrap();
    advice
        .assign(0, 2, Assigned::Rational(Fp::from(7), Fp::ZERO))
        .unwrap();
    advice.assign(0, 3, Assigned::Zero).unwrap();
    advice
        .assign(1, 4, Assigned::Trivial(Fp::from(11)))
        .unwrap();
    advice
        .assign(0, 5, Assigned::Rational(Fp::ZERO, Fp::from(7)))
        .unwrap();
    advice
        .assign_batch(0, 6, 2, |index| {
            Ok(match index {
                0 => Assigned::Rational(Fp::from(12), Fp::from(3)),
                1 => Assigned::Trivial(Fp::from(13)),
                _ => unreachable!(),
            })
        })
        .unwrap();
    advice
        .assign_batch(0, 6, 2, |index| {
            Ok(match index {
                0 => Assigned::Trivial(Fp::from(6)),
                1 => Assigned::Rational(Fp::from(14), Fp::from(2)),
                _ => unreachable!(),
            })
        })
        .unwrap();

    assert!(matches!(
        advice.assign(2, 0, Assigned::Zero),
        Err(Error::BoundsFailure)
    ));
    assert!(matches!(
        advice.assign(0, 8, Assigned::Zero),
        Err(Error::BoundsFailure)
    ));
    assert!(
        advice
            .assign_batch(usize::MAX, usize::MAX, 0, |_| unreachable!())
            .is_ok()
    );
    assert!(matches!(
        advice.assign_batch(0, 7, 2, |_| Ok(Assigned::Zero)),
        Err(Error::BoundsFailure)
    ));
    assert!(matches!(
        advice.assign_batch(0, usize::MAX, 2, |_| Ok(Assigned::Zero)),
        Err(Error::BoundsFailure)
    ));

    let advice = advice.evaluate();
    assert_eq!(advice[0][0], Fp::from(5));
    assert_eq!(advice[0][2], Fp::ZERO);
    assert_eq!(advice[0][3], Fp::ZERO);
    assert_eq!(advice[0][5], Fp::ZERO);
    assert_eq!(advice[0][6], Fp::from(6));
    assert_eq!(advice[0][7], Fp::from(7));
    assert_eq!(advice[1][1], Fp::from(3));
    assert_eq!(advice[1][4], Fp::from(11));
}

#[cfg(feature = "multicore")]
#[test]
fn parallel_advice_evaluation_preserves_proof_bytes() {
    use crate::{
        circuit::SimpleFloorPlanner,
        plonk::{keygen_pk, keygen_vk},
        transcript::{Blake2bWrite, Challenge255},
    };
    use pasta_curves::{EqAffine, Fp};
    use rand::{SeedableRng, rngs::StdRng};

    const PROOF_SEED: u64 = 0x5041_5241_4456_4943;
    const WORKER_COUNTS: [usize; 4] = [1, 2, 6, 10];

    #[derive(Clone, Copy)]
    struct RationalCircuit {
        initial: [Assigned<Fp>; 2],
        replacement: [Assigned<Fp>; 2],
    }

    impl Circuit<Fp> for RationalCircuit {
        type Config = Column<Advice>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                initial: [
                    Assigned::Rational(Fp::ZERO, Fp::ONE),
                    Assigned::Rational(Fp::ZERO, Fp::ONE),
                ],
                replacement: [Assigned::Zero, Assigned::Zero],
            }
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            meta.advice_column()
        }

        fn synthesize(
            &self,
            advice: Self::Config,
            mut layouter: impl crate::circuit::Layouter<Fp>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "rational advice",
                |mut region| {
                    for (row, value) in self.initial.into_iter().enumerate() {
                        region.assign_advice(
                            || "initial value",
                            advice,
                            row,
                            || Value::known(value),
                        )?;
                    }
                    for (row, value) in self.replacement.into_iter().enumerate() {
                        region.assign_advice(
                            || "replacement value",
                            advice,
                            row,
                            || Value::known(value),
                        )?;
                    }
                    Ok(())
                },
            )
        }
    }

    let circuits = [
        RationalCircuit {
            initial: [
                Assigned::Rational(Fp::from(2), Fp::from(3)),
                Assigned::Rational(Fp::from(5), Fp::from(7)),
            ],
            replacement: [
                Assigned::Trivial(Fp::from(11)),
                Assigned::Rational(Fp::from(13), Fp::ZERO),
            ],
        },
        RationalCircuit {
            initial: [
                Assigned::Rational(Fp::from(17), Fp::from(19)),
                Assigned::Rational(Fp::from(23), Fp::from(29)),
            ],
            replacement: [
                Assigned::Rational(Fp::ZERO, Fp::from(31)),
                Assigned::Rational(Fp::from(37), Fp::from(41)),
            ],
        },
        RationalCircuit {
            initial: [
                Assigned::Rational(Fp::from(43), Fp::ZERO),
                Assigned::Rational(Fp::from(47), Fp::from(53)),
            ],
            replacement: [
                Assigned::Rational(Fp::from(59), Fp::from(61)),
                Assigned::Zero,
            ],
        },
        RationalCircuit {
            initial: [
                Assigned::Rational(Fp::from(67), Fp::from(71)),
                Assigned::Rational(Fp::from(73), Fp::ZERO),
            ],
            replacement: [
                Assigned::Rational(Fp::from(79), Fp::ZERO),
                Assigned::Trivial(Fp::from(83)),
            ],
        },
    ];
    let params: Params<EqAffine> = Params::new(3);
    let vk = keygen_vk(&params, &circuits[0]).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &circuits[0]).expect("keygen_pk should not fail");
    let instances = [&[][..], &[][..], &[][..], &[][..]];
    let create = |circuit_count, threads| {
        maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap()
            .install(|| {
                let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
                create_proof(
                    &params,
                    &pk,
                    &circuits[..circuit_count],
                    &instances[..circuit_count],
                    StdRng::seed_from_u64(PROOF_SEED),
                    &mut transcript,
                )
                .expect("proof generation should not fail");
                transcript.finalize()
            })
    };

    let expected_single = create(1, 1);
    let expected_batch = create(4, 1);
    for threads in WORKER_COUNTS {
        assert_eq!(create(1, threads), expected_single);
        assert_eq!(create(4, threads), expected_batch);
    }
}

#[test]
fn instance_preparation_preserves_proof_and_error_order() {
    use crate::{
        circuit::SimpleFloorPlanner,
        plonk::{keygen_pk, keygen_vk},
        transcript::{Blake2bWrite, Challenge255, EncodedChallenge, Transcript},
    };
    use pasta_curves::{EqAffine, Fp};
    use rand::{SeedableRng, rngs::StdRng};

    const PROOF_SEED: u64 = 0x494e_5354_414e_4345;

    #[derive(Clone, Copy)]
    struct InstanceCircuit;

    impl<F: Field> Circuit<F> for InstanceCircuit {
        type Config = Column<Instance>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            meta.instance_column()
        }

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), Error> {
            Ok(())
        }
    }

    let params: Params<EqAffine> = Params::new(5);
    let vk = keygen_vk(&params, &InstanceCircuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &InstanceCircuit).expect("keygen_pk should not fail");
    #[cfg(feature = "batch")]
    assert!(params.prepared_instance_table().is_some());
    let circuits = [InstanceCircuit; 4];
    let instance_values = [[Fp::from(1)], [Fp::from(2)], [Fp::from(3)], [Fp::from(4)]];
    let instance_columns = instance_values
        .iter()
        .map(|values| vec![values.as_slice()])
        .collect::<Vec<_>>();
    let instances = instance_columns
        .iter()
        .map(Vec::as_slice)
        .collect::<Vec<_>>();
    let create_seeded_proof = || {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(
            &params,
            &pk,
            &circuits,
            &instances,
            StdRng::seed_from_u64(PROOF_SEED),
            &mut transcript,
        )
        .expect("proof generation should not fail");
        transcript.finalize()
    };

    let expected_proof = create_seeded_proof();
    assert_eq!(create_seeded_proof(), expected_proof);

    let single_circuit = [InstanceCircuit];
    let single_values = [Fp::from(5)];
    let single_columns = [single_values.as_slice()];
    let single_instances = [single_columns.as_slice()];
    let create_single_proof = || {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(
            &params,
            &pk,
            &single_circuit,
            &single_instances,
            StdRng::seed_from_u64(PROOF_SEED),
            &mut transcript,
        )
        .expect("proof generation should not fail");
        transcript.finalize()
    };
    let expected_single_proof = create_single_proof();
    assert_eq!(create_single_proof(), expected_single_proof);

    #[cfg(feature = "multicore")]
    for threads in [1, 4] {
        let proof = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap()
            .install(create_seeded_proof);
        assert_eq!(proof, expected_proof);

        let single_proof = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap()
            .install(create_single_proof);
        assert_eq!(single_proof, expected_single_proof);
    }

    #[cfg(feature = "batch")]
    {
        // Pin both sides of the private Halo2 route contract. These literals
        // intentionally make production-constant drift fail this test.
        assert_eq!(PREPARED_INSTANCE_COLUMNS, 1);
        assert_eq!(PREPARED_INSTANCE_DENSE_ROWS, 7);
        assert_eq!(PREPARED_INSTANCE_BOOLEAN_ROWS, 3);
        assert_eq!(PREPARED_INSTANCE_ROWS, 10);

        let exact_shape_values = (0..circuits.len())
            .map(|proof| {
                let mut values: [Fp; PREPARED_INSTANCE_ROWS] = std::array::from_fn(|row| {
                    Fp::from((proof * PREPARED_INSTANCE_ROWS + row + 1) as u64)
                });
                values[0] = Fp::from(91);
                for flag in 0..PREPARED_INSTANCE_BOOLEAN_ROWS {
                    values[PREPARED_INSTANCE_DENSE_ROWS + flag] =
                        Fp::from(((proof >> flag) & 1) as u64);
                }
                values
            })
            .collect::<Vec<_>>();
        let exact_shape_columns = exact_shape_values
            .iter()
            .map(|values| vec![values.as_slice()])
            .collect::<Vec<_>>();
        let exact_shape_instances = exact_shape_columns
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        let create_exact_shape_proof = |params: &Params<EqAffine>| {
            let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
            create_proof(
                params,
                &pk,
                &circuits,
                &exact_shape_instances,
                StdRng::seed_from_u64(PROOF_SEED),
                &mut transcript,
            )
            .expect("exact-shape proof generation should not fail");
            transcript.finalize()
        };

        let unprepared_params = Params::new(5);
        assert!(unprepared_params.prepared_instance_table().is_none());
        let route_hits = prepared_instance_route_hits();
        let unprepared_proof = create_exact_shape_proof(&unprepared_params);
        assert_eq!(prepared_instance_route_hits(), route_hits);
        let prepared_proof = create_exact_shape_proof(&params);
        assert_eq!(prepared_instance_route_hits(), route_hits + 1);
        assert_eq!(prepared_proof, unprepared_proof);
    }

    let valid = [Fp::from(5)];
    let oversized = vec![Fp::ZERO; params.n as usize];
    let later = [Fp::from(7)];
    let valid_columns = [valid.as_slice()];
    let oversized_columns = [oversized.as_slice()];
    let later_columns = [later.as_slice()];

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    let result = create_proof(
        &params,
        &pk,
        &[InstanceCircuit; 3],
        &[&valid_columns, &oversized_columns, &later_columns],
        StdRng::seed_from_u64(PROOF_SEED),
        &mut transcript,
    );
    assert!(matches!(result, Err(Error::InstanceTooLarge)));
    let actual_prefix = transcript.squeeze_challenge().get_scalar();

    let mut expected = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    pk.vk
        .hash_into(&mut expected)
        .expect("verification-key hashing should not fail");
    expected
        .common_point(commit_instance(&params, &valid).to_affine())
        .expect("valid instance commitment should not fail");
    assert_eq!(actual_prefix, expected.squeeze_challenge().get_scalar());

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    let result = create_proof(
        &params,
        &pk,
        &[InstanceCircuit; 2],
        &[&oversized_columns, &valid_columns],
        StdRng::seed_from_u64(PROOF_SEED),
        &mut transcript,
    );
    assert!(matches!(result, Err(Error::InstanceTooLarge)));
    let actual_prefix = transcript.squeeze_challenge().get_scalar();

    let mut expected = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    pk.vk
        .hash_into(&mut expected)
        .expect("verification-key hashing should not fail");
    assert_eq!(actual_prefix, expected.squeeze_challenge().get_scalar());
}

#[test]
fn instance_failures_do_not_run_synthesis_or_consume_rng() {
    use crate::{
        circuit::SimpleFloorPlanner,
        plonk::{keygen_pk, keygen_vk},
        transcript::{Blake2bWrite, Challenge255, Transcript},
    };
    use pasta_curves::{EqAffine, Fp};
    use rand_core::{Infallible, TryRng};
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };

    #[derive(Clone)]
    struct SideEffectCircuit {
        syntheses: Arc<AtomicUsize>,
        fail: bool,
    }

    impl Circuit<Fp> for SideEffectCircuit {
        type Config = (Column<Instance>, Column<Advice>);
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                syntheses: Arc::clone(&self.syntheses),
                fail: false,
            }
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            (meta.instance_column(), meta.advice_column())
        }

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl crate::circuit::Layouter<Fp>,
        ) -> Result<(), Error> {
            self.syntheses.fetch_add(1, Ordering::SeqCst);
            if self.fail {
                Err(Error::Synthesis)
            } else {
                Ok(())
            }
        }
    }

    struct CountingRng {
        bytes: Arc<AtomicUsize>,
    }

    impl TryRng for CountingRng {
        type Error = Infallible;

        fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
            self.bytes.fetch_add(4, Ordering::SeqCst);
            Ok(0x5a5a_5a5a)
        }

        fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
            self.bytes.fetch_add(8, Ordering::SeqCst);
            Ok(0x5a5a_5a5a_5a5a_5a5a)
        }

        fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
            self.bytes.fetch_add(dst.len(), Ordering::SeqCst);
            dst.fill(0x5a);
            Ok(())
        }
    }

    struct FailOnCommonPoint {
        inner: Blake2bWrite<Vec<u8>, EqAffine, Challenge255<EqAffine>>,
    }

    impl Transcript<EqAffine, Challenge255<EqAffine>> for FailOnCommonPoint {
        fn squeeze_challenge(&mut self) -> Challenge255<EqAffine> {
            self.inner.squeeze_challenge()
        }

        fn common_point(&mut self, _point: EqAffine) -> std::io::Result<()> {
            Err(std::io::Error::other("deliberate common-point failure"))
        }

        fn common_scalar(&mut self, scalar: Fp) -> std::io::Result<()> {
            self.inner.common_scalar(scalar)
        }
    }

    impl TranscriptWrite<EqAffine, Challenge255<EqAffine>> for FailOnCommonPoint {
        fn write_point(&mut self, point: EqAffine) -> std::io::Result<()> {
            self.inner.write_point(point)
        }

        fn write_scalar(&mut self, scalar: Fp) -> std::io::Result<()> {
            self.inner.write_scalar(scalar)
        }
    }

    let syntheses = Arc::new(AtomicUsize::new(0));
    let circuit = SideEffectCircuit {
        syntheses: Arc::clone(&syntheses),
        fail: false,
    };
    let params: Params<EqAffine> = Params::new(5);
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
    syntheses.store(0, Ordering::SeqCst);

    let oversized = vec![Fp::ZERO; params.n as usize];
    let oversized_columns = [oversized.as_slice()];
    let rng_bytes = Arc::new(AtomicUsize::new(0));
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    let result = create_proof(
        &params,
        &pk,
        &[SideEffectCircuit {
            syntheses: Arc::clone(&syntheses),
            fail: true,
        }],
        &[&oversized_columns],
        CountingRng {
            bytes: Arc::clone(&rng_bytes),
        },
        &mut transcript,
    );
    assert!(matches!(result, Err(Error::InstanceTooLarge)));
    let oversized_effects = (
        syntheses.load(Ordering::SeqCst),
        rng_bytes.load(Ordering::SeqCst),
    );

    // A transcript failure for an earlier instance must still precede a later
    // oversized instance.
    let valid = [Fp::ONE];
    let valid_columns = [valid.as_slice()];
    syntheses.store(0, Ordering::SeqCst);
    rng_bytes.store(0, Ordering::SeqCst);
    let mut transcript = FailOnCommonPoint {
        inner: Blake2bWrite::init(vec![]),
    };
    let result = create_proof(
        &params,
        &pk,
        &[circuit.clone(), circuit.clone()],
        &[&valid_columns, &oversized_columns],
        CountingRng {
            bytes: Arc::clone(&rng_bytes),
        },
        &mut transcript,
    );
    assert!(matches!(result, Err(Error::Transcript(_))));
    let transcript_effects = (
        syntheses.load(Ordering::SeqCst),
        rng_bytes.load(Ordering::SeqCst),
    );

    // Synthesis historically precedes the first prover-randomness draw.
    syntheses.store(0, Ordering::SeqCst);
    rng_bytes.store(0, Ordering::SeqCst);
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    let result = create_proof(
        &params,
        &pk,
        &[SideEffectCircuit {
            syntheses: Arc::clone(&syntheses),
            fail: true,
        }],
        &[&valid_columns],
        CountingRng {
            bytes: Arc::clone(&rng_bytes),
        },
        &mut transcript,
    );
    assert!(matches!(result, Err(Error::Synthesis)));
    let synthesis_effects = (
        syntheses.load(Ordering::SeqCst),
        rng_bytes.load(Ordering::SeqCst),
    );
    assert_eq!(
        [oversized_effects, transcript_effects, synthesis_effects],
        [(0, 0), (0, 0), (1, 0)],
    );
}

#[test]
fn v1_proving_key_reuses_floor_plan() {
    use crate::{
        circuit::floor_planner::V1,
        plonk::{SingleVerifier, TableColumn, keygen_pk, keygen_vk, verify_proof},
        poly::Rotation,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use pasta_curves::EqAffine;
    use rand::{SeedableRng, rngs::StdRng};
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    static MEASUREMENTS: AtomicUsize = AtomicUsize::new(0);
    static TABLE_ASSIGNMENTS: AtomicUsize = AtomicUsize::new(0);
    static FAIL_TABLE: AtomicBool = AtomicBool::new(false);
    const PROOF_SEED: u64 = 0x5631_4241_5443_4802;

    #[derive(Clone, Copy)]
    struct MyConfig {
        advice: Column<Advice>,
        table: TableColumn,
    }

    #[derive(Clone, Copy)]
    struct MyCircuit;

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = MyConfig;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            MEASUREMENTS.fetch_add(1, Ordering::Relaxed);
            *self
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = meta.advice_column();
            let table = meta.lookup_table_column();
            meta.lookup(|meta| vec![(meta.query_advice(advice, Rotation::cur()), table)]);
            MyConfig { advice, table }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), Error> {
            layouter.assign_table(
                || "fixed table",
                |mut region| {
                    TABLE_ASSIGNMENTS.fetch_add(1, Ordering::Relaxed);
                    if FAIL_TABLE.load(Ordering::Relaxed) {
                        return Err(Error::Synthesis);
                    }
                    region.assign_cell(|| "zero", config.table, 0, || Value::known(F::ZERO))
                },
            )?;
            layouter.assign_region(
                || "witness",
                |mut region| {
                    region.assign_advice(|| "zero", config.advice, 0, || Value::known(F::ZERO))?;
                    Ok(())
                },
            )
        }
    }

    let params: Params<EqAffine> = Params::new(3);
    TABLE_ASSIGNMENTS.store(0, Ordering::Relaxed);
    let vk = keygen_vk(&params, &MyCircuit).expect("keygen_vk should not fail");
    assert_eq!(TABLE_ASSIGNMENTS.load(Ordering::Relaxed), 1);
    let mut pk = keygen_pk(&params, vk, &MyCircuit).expect("keygen_pk should not fail");
    assert_eq!(TABLE_ASSIGNMENTS.load(Ordering::Relaxed), 2);
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    MEASUREMENTS.store(0, Ordering::Relaxed);
    TABLE_ASSIGNMENTS.store(0, Ordering::Relaxed);
    create_proof(
        &params,
        &pk,
        &[MyCircuit, MyCircuit, MyCircuit],
        &[&[], &[], &[]],
        StdRng::seed_from_u64(PROOF_SEED),
        &mut transcript,
    )
    .expect("proof generation should not fail");
    // The plan cached in the proving key is reused, so proving re-measures
    // nothing. The fixed table values are already part of the proving key,
    // but each circuit's table closure still runs: its side effects and
    // errors are observable behavior.
    assert_eq!(MEASUREMENTS.load(Ordering::Relaxed), 0);
    assert_eq!(TABLE_ASSIGNMENTS.load(Ordering::Relaxed), 3);
    let first_proof = transcript.finalize();
    let strategy = SingleVerifier::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&first_proof[..]);
    verify_proof(
        &params,
        pk.get_vk(),
        strategy,
        &[&[], &[], &[]],
        &mut transcript,
    )
    .expect("proof verification should not fail");

    // A single circuit takes a separate synthesis branch from a batch.
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    TABLE_ASSIGNMENTS.store(0, Ordering::Relaxed);
    create_proof(
        &params,
        &pk,
        &[MyCircuit],
        &[&[]],
        StdRng::seed_from_u64(PROOF_SEED),
        &mut transcript,
    )
    .expect("single proof generation should not fail");
    assert_eq!(TABLE_ASSIGNMENTS.load(Ordering::Relaxed), 1);

    // An error returned by the table closure while the cached plan is reused
    // must propagate out of proving, exactly as when the plan is new.
    FAIL_TABLE.store(true, Ordering::Relaxed);
    TABLE_ASSIGNMENTS.store(0, Ordering::Relaxed);
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    let result = create_proof(
        &params,
        &pk,
        &[MyCircuit],
        &[&[]],
        StdRng::seed_from_u64(PROOF_SEED),
        &mut transcript,
    );
    assert!(matches!(result, Err(Error::Synthesis)));
    assert_eq!(TABLE_ASSIGNMENTS.load(Ordering::Relaxed), 1);
    FAIL_TABLE.store(false, Ordering::Relaxed);

    // The proof bytes must not depend on the parallel schedule: re-create the
    // proof under single- and multi-worker Rayon pools and require identical
    // transcripts.
    #[cfg(feature = "multicore")]
    for threads in [1, 4] {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        MEASUREMENTS.store(0, Ordering::Relaxed);
        TABLE_ASSIGNMENTS.store(0, Ordering::Relaxed);
        maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap()
            .install(|| {
                create_proof(
                    &params,
                    &pk,
                    &[MyCircuit, MyCircuit, MyCircuit],
                    &[&[], &[], &[]],
                    StdRng::seed_from_u64(PROOF_SEED),
                    &mut transcript,
                )
            })
            .expect("proof generation should not fail");
        assert_eq!(MEASUREMENTS.load(Ordering::Relaxed), 0);
        assert_eq!(TABLE_ASSIGNMENTS.load(Ordering::Relaxed), 3);
        assert_eq!(transcript.finalize(), first_proof);
    }

    // A plan produced by another floor planner is ignored safely: the V1
    // planner re-measures once and still produces identical proof bytes.
    pk.floor_plan = Some(FloorPlan::from_arc(std::sync::Arc::new(())));
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    MEASUREMENTS.store(0, Ordering::Relaxed);
    TABLE_ASSIGNMENTS.store(0, Ordering::Relaxed);
    create_proof(
        &params,
        &pk,
        &[MyCircuit, MyCircuit, MyCircuit],
        &[&[], &[], &[]],
        StdRng::seed_from_u64(PROOF_SEED),
        &mut transcript,
    )
    .expect("proof generation with an incompatible plan should not fail");
    assert_eq!(MEASUREMENTS.load(Ordering::Relaxed), 1);
    assert_eq!(TABLE_ASSIGNMENTS.load(Ordering::Relaxed), 3);
    assert_eq!(transcript.finalize(), first_proof);
}

#[test]
fn compressed_selector_cache_preserves_proof() {
    use crate::{
        circuit::{Layouter, SimpleFloorPlanner},
        plonk::{Expression, SingleVerifier, TableColumn, keygen_pk, keygen_vk, verify_proof},
        poly::Rotation,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use pasta_curves::{EqAffine, Fp};
    use rand::{SeedableRng, rngs::StdRng};

    const PROOF_SEED: u64 = 0x5345_4c45_4354_4f52;

    #[derive(Clone, Copy, Debug)]
    struct Config {
        advice: [Column<Advice>; 4],
        selectors: [Selector; crate::MIN_SELECTOR_FAMILY_LEN],
        table: [TableColumn; 2],
    }

    #[derive(Clone, Copy)]
    struct MyCircuit;

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = core::array::from_fn(|_| meta.advice_column());
            let instance = meta.instance_column();
            let selectors = core::array::from_fn(|_| meta.selector());
            let table = [meta.lookup_table_column(), meta.lookup_table_column()];

            for column in advice {
                meta.enable_equality(column);
            }
            meta.enable_equality(instance);

            meta.lookup(|meta| {
                advice[..2]
                    .iter()
                    .zip(table)
                    .map(|(advice, table)| (meta.query_advice(*advice, Rotation::cur()), table))
                    .collect()
            });
            meta.lookup(|meta| {
                advice[2..]
                    .iter()
                    .zip(table)
                    .map(|(advice, table)| (meta.query_advice(*advice, Rotation::cur()), table))
                    .collect()
            });

            for selector in selectors {
                meta.create_gate("selector family", |meta| {
                    let selector = meta.query_selector(selector);
                    let advice = meta.query_advice(advice[0], Rotation::cur());
                    let instance = meta.query_instance(instance, Rotation::cur());
                    vec![
                        selector.clone() * (advice - Expression::Constant(F::ONE)),
                        selector * instance,
                    ]
                });
            }

            // A constraint-system degree one greater than the family length
            // can combine every degree-two selector expression into one fixed
            // column.
            meta.set_minimum_degree(crate::MIN_SELECTOR_FAMILY_LEN + 1);

            Config {
                advice,
                selectors,
                table,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            layouter.assign_table(
                || "two-column lookup table",
                |mut table| {
                    for (row, value) in [F::ZERO, F::ONE].into_iter().enumerate() {
                        for column in config.table {
                            table.assign_cell(|| "value", column, row, || Value::known(value))?;
                        }
                    }
                    Ok(())
                },
            )?;
            layouter.assign_region(
                || "selector family",
                |mut region| {
                    for (row, selector) in config.selectors.iter().enumerate() {
                        selector.enable(&mut region, row)?;
                        for advice in config.advice {
                            region.assign_advice(
                                || "value",
                                advice,
                                row,
                                || Value::known(F::ONE),
                            )?;
                        }
                    }
                    Ok(())
                },
            )
        }
    }

    fn create(
        pk: &ProvingKey<EqAffine>,
        params: &Params<EqAffine>,
        circuit_count: usize,
        seed: u64,
    ) -> Vec<u8> {
        let circuits = [MyCircuit; 4];
        let empty_instance: &[Fp] = &[];
        let instance_columns: &[&[Fp]] = &[empty_instance];
        let instances = [instance_columns; 4];
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(
            params,
            pk,
            &circuits[..circuit_count],
            &instances[..circuit_count],
            StdRng::seed_from_u64(seed),
            &mut transcript,
        )
        .expect("proof generation should not fail");
        transcript.finalize()
    }

    fn verify(
        pk: &ProvingKey<EqAffine>,
        params: &Params<EqAffine>,
        circuit_count: usize,
        proof: &[u8],
    ) {
        let empty_instance: &[Fp] = &[];
        let instance_columns: &[&[Fp]] = &[empty_instance];
        let instances = [instance_columns; 4];
        let strategy = SingleVerifier::new(params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof);
        verify_proof(
            params,
            pk.get_vk(),
            strategy,
            &instances[..circuit_count],
            &mut transcript,
        )
        .expect("proof verification should not fail");
    }
    let params = Params::new(4);
    let create_pk = || {
        let vk = keygen_vk(&params, &MyCircuit).expect("keygen_vk should not fail");
        keygen_pk(&params, vk, &MyCircuit).expect("keygen_pk should not fail")
    };
    let pk = create_pk();
    assert_eq!(pk.cached_selector_families.len(), 1);
    assert_eq!(
        pk.cached_selector_families[0].selectors.len() + 1,
        crate::MIN_SELECTOR_FAMILY_LEN
    );
    assert_eq!(pk.vk.cs.num_instance_columns, 1);
    assert_eq!(pk.vk.cs.lookups.len(), 2);
    assert!(
        pk.vk
            .cs
            .lookups
            .iter()
            .all(|lookup| lookup.input_expressions.len() == 2)
    );
    assert!(pk.vk.cs.permutation.set_count(pk.vk.cs_degree) >= 2);
    assert!(pk.quotient_plans.get(3).is_none());

    // Key generation compiles every retained shape before any proof. The
    // first proof must keep that exact Arc. An empty-plan key provides the
    // byte-for-byte control for 1, 2, and 4 circuits.
    let mut eager_proofs = vec![];
    for circuit_count in [1, 2, 4] {
        let eager_plan = pk
            .quotient_plans
            .get(circuit_count)
            .expect("keygen compiles each retained quotient plan");
        let eager_proof = create(&pk, &params, circuit_count, PROOF_SEED);
        let retained_plan = pk
            .quotient_plans
            .get(circuit_count)
            .expect("the first proof retains its keygen plan");
        assert!(std::sync::Arc::ptr_eq(&eager_plan, &retained_plan));

        let mut lazy_pk = pk.clone();
        lazy_pk.quotient_plans = std::sync::Arc::new(Default::default());
        let lazy_proof = create(&lazy_pk, &params, circuit_count, PROOF_SEED);
        assert_eq!(eager_proof, lazy_proof);
        verify(&pk, &params, circuit_count, &eager_proof);
        eager_proofs.push(eager_proof);
    }

    // A different seed changes commitments before theta is sampled. The
    // symbolic plan binds the resulting challenges, while proof bytes still
    // match a freshly planned control.
    let alternate_seed = PROOF_SEED ^ 0xa11c_e55e_7e57_0001;
    let eager_plan = pk.quotient_plans.get(1).unwrap();
    let alternate_proof = create(&pk, &params, 1, alternate_seed);
    assert_ne!(alternate_proof, eager_proofs[0]);
    assert!(std::sync::Arc::ptr_eq(
        &eager_plan,
        &pk.quotient_plans.get(1).unwrap()
    ));
    let mut alternate_lazy_pk = pk.clone();
    alternate_lazy_pk.quotient_plans = std::sync::Arc::new(Default::default());
    assert_eq!(
        alternate_proof,
        create(&alternate_lazy_pk, &params, 1, alternate_seed)
    );
    verify(&pk, &params, 1, &alternate_proof);

    // A candidate is selected before lookup preparation, so an exact shape
    // mismatch must reconstruct the omitted lookup ASTs before falling back.
    // Removing compressed-selector registration changes the evaluator shape
    // without changing the constraint system or proof bytes.
    let mut mismatched_pk = create_pk();
    let rejected_plan = mismatched_pk.quotient_plans.get(2).unwrap();
    for family in mismatched_pk.cached_selector_families.iter() {
        let column_index = family.column_index;
        mismatched_pk.fixed_cosets[column_index] = mismatched_pk
            .vk
            .domain
            .coeff_to_extended(mismatched_pk.fixed_polys[column_index].clone());
    }
    mismatched_pk.cached_selector_families = Default::default();
    let fallback_proof = create(&mismatched_pk, &params, 2, PROOF_SEED);
    assert_eq!(fallback_proof, eager_proofs[1]);
    assert!(!std::sync::Arc::ptr_eq(
        &rejected_plan,
        &mismatched_pk.quotient_plans.get(2).unwrap()
    ));
    verify(&mismatched_pk, &params, 2, &fallback_proof);

    // Equal polynomial counts and lengths are insufficient. Swap tags across
    // instance/lookup and permutation/lookup-product roles that appear more
    // than once, and require the byte-identical fallback.
    let swapped_tag_pk = create_pk();
    swapped_tag_pk.quotient_plans.swap_polynomial_tags(
        2,
        QuotientPoly::Instance {
            circuit_index: 0,
            column_index: 0,
        },
        QuotientPoly::LookupPermutedTable {
            circuit_index: 1,
            lookup_index: 1,
        },
    );
    swapped_tag_pk.quotient_plans.swap_polynomial_tags(
        2,
        QuotientPoly::PermutationProduct {
            circuit_index: 0,
            set_index: 1,
        },
        QuotientPoly::LookupProduct {
            circuit_index: 1,
            lookup_index: 0,
        },
    );
    let rejected_plan = swapped_tag_pk.quotient_plans.get(2).unwrap();
    let fallback_proof = create(&swapped_tag_pk, &params, 2, PROOF_SEED);
    assert_eq!(fallback_proof, eager_proofs[1]);
    assert!(!std::sync::Arc::ptr_eq(
        &rejected_plan,
        &swapped_tag_pk.quotient_plans.get(2).unwrap()
    ));
    verify(&swapped_tag_pk, &params, 2, &fallback_proof);

    // A family omitted by the cache budget retains its source coset and takes
    // the generic evaluator path. Restore that state for every cached family.
    let mut uncached_pk = pk.clone();
    assert!(std::sync::Arc::ptr_eq(
        &pk.cached_selector_families,
        &uncached_pk.cached_selector_families,
    ));
    for family in pk.cached_selector_families.iter() {
        let column_index = family.column_index;
        uncached_pk.fixed_cosets[column_index] = uncached_pk
            .vk
            .domain
            .coeff_to_extended(uncached_pk.fixed_polys[column_index].clone());
    }
    uncached_pk.cached_selector_families = Default::default();
    uncached_pk.quotient_plans = std::sync::Arc::new(Default::default());

    assert_eq!(
        create(&pk, &params, 2, PROOF_SEED),
        create(&uncached_pk, &params, 2, PROOF_SEED)
    );

    // Concurrent first proofs share the keygen-compiled plan without
    // replacement and preserve deterministic proof bytes.
    let concurrent_pk = create_pk();
    let eager_plan = concurrent_pk.quotient_plans.get(4).unwrap();
    let (first, second) = std::thread::scope(|scope| {
        let first = scope.spawn(|| create(&concurrent_pk, &params, 4, PROOF_SEED));
        let second = scope.spawn(|| create(&concurrent_pk, &params, 4, PROOF_SEED));
        (first.join().unwrap(), second.join().unwrap())
    });
    assert_eq!(first, second);
    assert!(std::sync::Arc::ptr_eq(
        &eager_plan,
        &concurrent_pk.quotient_plans.get(4).unwrap()
    ));

    // Concurrent cold proofs can both miss without racing plan replacement or
    // changing proof bytes.
    let mut cold_pk = create_pk();
    cold_pk.quotient_plans = std::sync::Arc::new(Default::default());
    let barrier = std::sync::Barrier::new(3);
    let (first, second) = std::thread::scope(|scope| {
        let first = scope.spawn(|| {
            barrier.wait();
            create(&cold_pk, &params, 2, PROOF_SEED)
        });
        let second = scope.spawn(|| {
            barrier.wait();
            create(&cold_pk, &params, 2, PROOF_SEED)
        });
        barrier.wait();
        (first.join().unwrap(), second.join().unwrap())
    });
    assert_eq!(first, second);
    assert!(cold_pk.quotient_plans.get(2).is_some());
    verify(&cold_pk, &params, 2, &first);

    #[cfg(feature = "multicore")]
    {
        let single_pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();
        let parallel_pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(4)
            .build()
            .unwrap();
        let single_pk = single_pool.install(create_pk);
        let parallel_pk = parallel_pool.install(create_pk);

        assert_eq!(
            single_pk.cached_selector_families.len(),
            parallel_pk.cached_selector_families.len()
        );
        for (single, parallel) in single_pk
            .cached_selector_families
            .iter()
            .zip(parallel_pk.cached_selector_families.iter())
        {
            assert_eq!(single.column_index, parallel.column_index);
            assert_eq!(
                &single_pk.fixed_cosets[single.column_index][..],
                &parallel_pk.fixed_cosets[parallel.column_index][..]
            );
            assert_eq!(single.selectors.len(), parallel.selectors.len());
            for (single, parallel) in single.selectors.iter().zip(parallel.selectors.iter()) {
                assert_eq!(&single[..], &parallel[..]);
            }
        }

        let single_proof = single_pool.install(|| create(&single_pk, &params, 4, PROOF_SEED));
        let parallel_proof = parallel_pool.install(|| create(&parallel_pk, &params, 4, PROOF_SEED));
        assert_eq!(single_proof, parallel_proof);
    }
}
