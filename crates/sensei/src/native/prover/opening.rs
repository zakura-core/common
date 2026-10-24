//! Polynomial evaluations and the multi-opening collapse.
//!
//! Queries are grouped by their evaluation point sets in protocol order. Dense,
//! embedded, linear, and sparse instance sources retain their representations
//! until the coefficient folds; no transcript write occurs inside a worker task.
//!
//! The dynamic grouping oracle and reference coefficient folds live in
//! `opening/reference.rs`; their test caller paths remain available here.

use alloc::{sync::Arc, vec::Vec};

use crate::Error;
use crate::native::evaluation::{rotated_evaluation_point, rotated_query_point};
use crate::native::field::Fp;
use crate::native::polynomial::SharedPoly;
use crate::native::target::{
    ADVICE_COLUMNS, BLINDING_FACTORS, FixedTarget, INSTANCE_VALUE_COUNT, N, QUOTIENT_PIECES,
};
use crate::native::{buffer::Buffer, worker::Execution};
use crate::types::NativeStatement;
use udon::exec::for_each_chunk_mut;
use udon::polynomial::{divide_linear_in_place, divide_monic_in_place, vanishing_polynomial};

use super::inventory::opening_stage;
use super::opening_schedule::{
    ActionPolynomial, COMMON_OPENING_POINT, FixedPolynomial, OPENING_GROUPS, OPENING_POINTS,
    OPENING_ROTATIONS,
};
use super::{
    COEFFICIENT_CHUNK, EvaluationJob, EvaluationPrefix, EvaluationSource, MultiopenPrefix,
    ProverPrefix, QuotientPiece, QuotientPrefix, VanishingPrefix, parallel_evaluate_polynomials,
};

#[cfg(test)]
mod reference;
#[cfg(test)]
pub(super) use reference::*;

/// A coefficient polynomial borrowed for the duration of a worker wave.
#[derive(Clone)]
pub(super) enum PolySource<'a> {
    #[cfg(test)]
    Arc(SharedPoly),
    Borrowed(&'a [Fp]),
}

impl PolySource<'_> {
    pub(super) fn as_slice(&self) -> &[Fp] {
        match self {
            #[cfg(test)]
            Self::Arc(values) => values,
            Self::Borrowed(values) => values,
        }
    }
}

#[derive(Clone)]
pub(super) enum OpeningSource<'a> {
    Coefficients(PolySource<'a>),
    /// A ten-row Lagrange prefix with a zero tail on the base domain.
    Instance {
        statements: Arc<[NativeStatement]>,
        index: usize,
    },
    QuotientPieces(&'a [QuotientPiece]),
    /// The linear vanishing mask `[r_0, r_1]`, collapsed as two sparse terms
    /// instead of an all-but-two-zeros `N`-coefficient source. Support
    /// contract: coefficient degrees `{0, 1}` only, standing for the dense
    /// `N`-coefficient polynomial with zeros elsewhere; every consumer
    /// (collapse, division, evaluation) must produce the value the dense form
    /// would, and its blind is committed like any other polynomial's.
    Linear([Fp; 2]),
}

impl<'a> ProverPrefix<'a> {
    /// Writes every evaluation in the target's fixed order and squeezes
    /// `x_1` and `x_2` for multi-opening.
    ///
    /// # Transcript contract
    ///
    /// - **Requires** `x` from the [`QuotientPrefix`]; no other challenge.
    /// - **Publishes** scalars only, in the fixed order below (every point is
    ///   `x` rotated by the query's rotation): every Action's instance
    ///   queries, then every Action's advice queries; the fixed queries; the
    ///   vanishing mask at `x`; the sigma columns at `x`; then per Action each
    ///   permutation set at `x` and `x·ω`, plus `x·ω^{-(BLINDING_FACTORS+1)}`
    ///   for every set but the last; then per Action each lookup's product
    ///   at `x` and `x·ω`, permuted input at `x` and `x·ω^{-1}`, and permuted
    ///   table at `x`.
    /// - **Squeezes** `x_1` then `x_2`, the multi-opening challenges, carried
    ///   on the returned [`EvaluationPrefix`].
    /// - **Draws** no randomness.
    ///
    /// The evaluations are computed as one task batch in any order and
    /// written afterwards in the job order above, which is the only
    /// transcript-ordered section. The same fixed schedule, with its
    /// first-appearance grouping, is what the multi-opening stage's
    /// compile-time [`super::opening_schedule`] is derived from.
    ///
    /// # Work and buffer inventory
    ///
    /// Logical counts from [`opening_stage`]: `evaluations(action_count)`
    /// scalars (`EVALUATIONS_FIXED` once plus `EVALUATIONS_PER_ACTION` per
    /// Action), each a dense `N`-coefficient evaluation using cached
    /// rotation-point powers except the linear mask's. No coefficient buffer
    /// is created or retained; the stage reads the quotient stage's coefficient
    /// forms and borrows target-prepared fixed and sigma coefficients; see the
    /// [ownership table](super#stage-buffer-ownership).
    pub(crate) fn write_evaluations(
        &mut self,
        vanishing: &VanishingPrefix,
        quotient: &QuotientPrefix,
    ) -> Result<EvaluationPrefix, Error> {
        let target = self.target;
        let action_count = self.action_count();
        if quotient.permutation_openings.len() != action_count
            || quotient.lookup_product_openings.len() != action_count
            || quotient.pieces.len() != QUOTIENT_PIECES
            || quotient
                .pieces
                .iter()
                .any(|piece| piece.coefficients.len() != N)
            || quotient.advice_coefficients.len() != action_count
            || quotient.permuted_lookup_coefficients.len() != action_count
            || quotient.advice_coefficients.iter().any(|columns| {
                columns.len() != ADVICE_COLUMNS
                    || columns.iter().any(|coefficients| coefficients.len() != N)
            })
            || quotient
                .permuted_lookup_coefficients
                .iter()
                .any(|lookups| lookups.len() != target.lookups().len())
        {
            return Err(Error::InternalInvariant);
        }

        let advice_coefficients = &quotient.advice_coefficients;
        let fixed_coefficients = target.fixed_polynomials().coefficients();
        let sigma_coefficients = target.sigma_polynomials().coefficients();
        let permuted_lookup_coefficients = &quotient.permuted_lookup_coefficients;

        let x = &quotient.x;
        let x_next = rotated_evaluation_point(x, target.domain().omega(), 1);
        let x_previous = rotated_evaluation_point(x, target.domain().omega_inverse(), 1);
        let x_last =
            rotated_evaluation_point(x, target.domain().omega_inverse(), BLINDING_FACTORS + 1);
        let mut evaluation_jobs = Vec::with_capacity(opening_stage::evaluations(action_count));

        fn shared(polynomial: &[Fp], point: Fp) -> EvaluationJob<'_> {
            EvaluationJob {
                coefficients: EvaluationSource::Dense(PolySource::Borrowed(polynomial)),
                point,
            }
        }
        // PreparedInstance handles exact domain nodes as well as other x;
        // errors concern its fixed domain/prefix/scratch sizes, not bad luck in x.
        let instance_weights = target
            .prepared_instance()
            .evaluation_weights(x)
            .map_err(|_| Error::InternalInvariant)?;
        for statement in self.statements.iter() {
            for query in target.queries().instance() {
                if query.column != 0 || query.rotation != 0 {
                    return Err(Error::InternalInvariant);
                }
                evaluation_jobs.push(EvaluationJob {
                    coefficients: EvaluationSource::Value(Fp::sum_of_products(
                        &instance_weights,
                        statement,
                    )),
                    point: *x,
                });
            }
        }
        for action_coefficients in advice_coefficients {
            for query in target.queries().advice() {
                let point = rotated_query_point(target, x, query.rotation);
                evaluation_jobs.push(shared(&action_coefficients[query.column], point));
            }
        }
        for query in target.queries().fixed() {
            let point = rotated_query_point(target, x, query.rotation);
            evaluation_jobs.push(EvaluationJob {
                coefficients: EvaluationSource::Dense(PolySource::Borrowed(
                    &fixed_coefficients[query.column],
                )),
                point,
            });
        }
        evaluation_jobs.push(EvaluationJob {
            coefficients: EvaluationSource::Linear(vanishing.mask),
            point: *x,
        });
        for coefficients in sigma_coefficients {
            evaluation_jobs.push(EvaluationJob {
                coefficients: EvaluationSource::Dense(PolySource::Borrowed(coefficients)),
                point: *x,
            });
        }
        for action_products in &quotient.permutation_openings {
            for (set_index, product) in action_products.iter().enumerate() {
                let coefficients = &product.coefficients;
                evaluation_jobs.push(shared(coefficients, *x));
                evaluation_jobs.push(shared(coefficients, x_next));
                if set_index + 1 < action_products.len() {
                    evaluation_jobs.push(shared(coefficients, x_last));
                }
            }
        }
        for (action_products, action_coefficients) in quotient
            .lookup_product_openings
            .iter()
            .zip(permuted_lookup_coefficients)
        {
            for (product, coefficients) in action_products.iter().zip(action_coefficients) {
                if coefficients.input.len() != N || coefficients.table.len() != N {
                    return Err(Error::InternalInvariant);
                }
                let product_coefficients = &product.coefficients;
                evaluation_jobs.push(shared(product_coefficients, *x));
                evaluation_jobs.push(shared(product_coefficients, x_next));
                evaluation_jobs.push(shared(&coefficients.input, *x));
                evaluation_jobs.push(shared(&coefficients.input, x_previous));
                evaluation_jobs.push(shared(&coefficients.table, *x));
            }
        }

        // Inventory tie: the fixed evaluation schedule's length.
        if evaluation_jobs.len() != opening_stage::evaluations(action_count) {
            return Err(Error::InternalInvariant);
        }
        let evaluations = parallel_evaluate_polynomials(self.execution, evaluation_jobs)?;
        for evaluation in &evaluations {
            self.transcript.write_scalar(evaluation);
        }
        let x_1 = self.transcript.squeeze_challenge();
        let x_2 = self.transcript.squeeze_challenge();

        Ok(EvaluationPrefix { x_1, x_2 })
    }
}

impl<'a> ProverPrefix<'a> {
    /// Builds the target's fixed opening-query list, groups commitments by
    /// identical point sets, collapses each group at `x_1`, and commits to the
    /// `x_2`-collapsed synthetic quotient `Q'` before squeezing `x_3`.
    ///
    /// # Transcript contract
    ///
    /// - **Requires** `x_1` and `x_2` from the [`EvaluationPrefix`] and `x`
    ///   from the [`QuotientPrefix`]; no other challenge.
    /// - **Publishes** one commitment: `Q'`, the `x_2`-fold of every point
    ///   set's `Q_i` divided by its points, in coefficient basis.
    /// - **Squeezes** `x_3`, the multi-opening evaluation point, carried on
    ///   the returned [`MultiopenPrefix`] with the `Q_i` and `Q'`.
    /// - **Draws** no randomness beyond the pre-sampled `Q'` blind: each
    ///   `Q_i` blind is the `x_1`-fold of its group's existing commitment
    ///   blinds.
    ///
    /// Everything before the single write — binding the compile-time
    /// [`super::opening_schedule`] (the fixed opening list's first-appearance
    /// grouping by point set) to this proof's buffers, the `x_1` collapse per
    /// point set, and the synthetic divisions — is preparation, free to run
    /// in any task order; the stage's transcript-ordered section is that one
    /// write followed by the squeeze. The schedule stands for grouping by
    /// exact field-point equality only while the rotated points are pairwise
    /// distinct, so coincident points (`x = 0`) are rejected, as the dynamic
    /// grouping's point-set tie rejected them.
    ///
    /// # Work and buffer inventory
    ///
    /// Logical counts from [`opening_stage`]. The fixed schedule groups the
    /// commitments into `POINT_SETS` point sets; per set one `Q_i` of `N`
    /// coefficients is built as an `x_1`-weighted sum of its group's
    /// coefficient forms (one pass over each), copied once for division by
    /// the monic divisor of its points other than `x`, then folded at `x_2`.
    /// A final division by the common `X - x` produces `Q'` (`N`). One `N`-scalar
    /// coefficient-basis commitment. Alive at return:
    /// `RETAINED_POLYNOMIALS` `N`-coefficient polynomials (the `Q_i` and
    /// `Q'`) and their blinds. This stage consumes the vanishing, quotient,
    /// and evaluation prefixes — nothing after it reads them — so the
    /// quotient stage's coefficient forms are released here, once the `Q_i`
    /// sums have read them and before the divided copies and `Q'` exist.
    pub(crate) fn commit_multiopen_quotient(
        &mut self,
        vanishing: VanishingPrefix,
        quotient: QuotientPrefix,
        evaluations: EvaluationPrefix,
        q_prime_blind: Fp,
    ) -> Result<MultiopenPrefix, Error> {
        let target = self.target;
        let action_count = self.action_count();
        if quotient.advice_coefficients.len() != action_count
            || target.fixed_polynomials().coefficients().len() != target.fixed_values().len()
            || target.sigma_polynomials().coefficients().len() != target.sigma_values().len()
            || quotient.permuted_lookup_coefficients.len() != action_count
            || quotient.advice_blinds.len() != action_count
            || quotient.permutation_openings.len() != action_count
            || quotient.lookup_product_openings.len() != action_count
            || quotient.pieces.len() != QUOTIENT_PIECES
            || quotient
                .pieces
                .iter()
                .any(|piece| piece.coefficients.len() != N)
            || quotient
                .permuted_lookup_coefficients
                .iter()
                .any(|lookups| lookups.len() != target.lookups().len())
        {
            return Err(Error::InternalInvariant);
        }

        let quotient_xn = quotient.x.pow_u64(N as u64);
        let quotient_blind = fold_quotient_blind(&quotient.pieces, &quotient_xn)?;
        // The schedule's points, numbered as the schedule numbers them.
        let points: [Fp; OPENING_POINTS] = core::array::from_fn(|id| {
            rotated_query_point(target, &quotient.x, OPENING_ROTATIONS[id])
        });
        // The compile-time grouping is the first-appearance grouping by field
        // equality exactly when the points are pairwise distinct; coincident
        // points never formed the inventory's point sets.
        if points.iter().enumerate().any(|(id, point)| {
            points[..id]
                .iter()
                .any(|previous| previous.reduce() == point.reduce())
        }) {
            return Err(Error::InternalInvariant);
        }

        let mut group_sources = Vec::with_capacity(OPENING_GROUPS.len());
        let mut q_blinds = Vec::with_capacity(OPENING_GROUPS.len());
        let mut weights = self.execution.buffer(
            OPENING_GROUPS
                .iter()
                .map(|group| group.len(action_count))
                .max()
                .unwrap_or(0),
            false,
        );
        for group in &OPENING_GROUPS {
            let member_count = group.len(action_count);
            let group_weights = &mut weights[..member_count];
            let mut weight = <Fp>::ONE;
            for group_weight in group_weights.iter_mut().rev() {
                *group_weight = weight;
                weight = weight.mul(&evaluations.x_1);
            }
            let extra_piece_capacity = if group.contains_quotient() {
                QUOTIENT_PIECES - 1
            } else {
                0
            };
            let mut weighted = WeightedGroup {
                instance: None,
                dense: Vec::with_capacity(member_count + extra_piece_capacity),
                sparse: Vec::with_capacity(
                    group
                        .fixed()
                        .iter()
                        .filter(|&&polynomial| polynomial == FixedPolynomial::Vanishing)
                        .count()
                        * vanishing.mask.len(),
                ),
            };
            let mut blind = <Fp>::ZERO;
            let mut group_weights = group_weights.iter();
            let mut fold = |source, source_blind: Fp| -> Result<(), Error> {
                let group_weight = group_weights.next().ok_or(Error::InternalInvariant)?;
                push_weighted_source(&mut weighted, source, group_weight, &quotient_xn)?;
                blind = blind.mul_add(&evaluations.x_1, &source_blind);
                Ok(())
            };
            for action_index in 0..action_count {
                for &polynomial in group.per_action() {
                    let (source, source_blind) = bind_action_polynomial(
                        &quotient,
                        &self.statements,
                        action_index,
                        polynomial,
                    )?;
                    fold(source, source_blind)?;
                }
            }
            for &polynomial in group.fixed() {
                let (source, source_blind) = bind_fixed_polynomial(
                    target,
                    &vanishing,
                    &quotient.pieces,
                    &quotient_blind,
                    polynomial,
                )?;
                fold(source, source_blind)?;
            }
            if group_weights.next().is_some() {
                return Err(Error::InternalInvariant);
            }
            group_sources.push(weighted);
            q_blinds.push(blind);
        }
        let q_polynomials = parallel_weighted_sums(
            self.execution,
            group_sources,
            target.prepared_instance().coefficient_rows(),
        )?;
        // The group sums have finished borrowing the quotient coefficients.
        // Release their owners before allocating the divided copies.
        let ipa_mask = quotient.ipa_mask.clone();
        drop(quotient);

        let q_prime_polynomial = SharedPoly::new(parallel_multiopen_quotient(
            self.execution,
            &q_polynomials,
            &points,
            &evaluations.x_2,
        )?);
        // The opening collapse preserves N coefficients; a target commitment
        // error concerns that stage-owned shape.
        let q_prime_commitment = target
            .parameters()
            .commit_coefficients(
                &q_prime_polynomial,
                &q_prime_blind,
                &mut self.workspace.msm,
                self.execution,
            )
            .map_err(|_| Error::InternalInvariant)?;
        // The fresh q_prime blind may yield identity, which cannot be emitted.
        self.transcript
            .write_point(&q_prime_commitment)
            .map_err(|_| Error::RetryRandomness)?;
        let x_3 = self.transcript.squeeze_challenge();

        Ok(MultiopenPrefix {
            q_polynomials,
            q_blinds,
            q_prime_polynomial,
            q_prime_blind,
            x_3,
            ipa_mask,
        })
    }
}

/// Binds one of an Action's scheduled polynomials to this proof's buffer and
/// blind.
fn bind_action_polynomial<'a>(
    quotient: &'a QuotientPrefix,
    statements: &Arc<[NativeStatement]>,
    action_index: usize,
    polynomial: ActionPolynomial,
) -> Result<(OpeningSource<'a>, Fp), Error> {
    let shared =
        |polynomial: &'a SharedPoly| OpeningSource::Coefficients(PolySource::Borrowed(polynomial));
    Ok(match polynomial {
        ActionPolynomial::Instance => {
            statements
                .get(action_index)
                .ok_or(Error::InternalInvariant)?;
            (
                OpeningSource::Instance {
                    statements: Arc::clone(statements),
                    index: action_index,
                },
                <Fp>::ONE,
            )
        }
        ActionPolynomial::Advice(column) => {
            let column = usize::from(column);
            let coefficients = quotient
                .advice_coefficients
                .get(action_index)
                .and_then(|action| action.get(column))
                .ok_or(Error::InternalInvariant)?;
            let blind = *quotient
                .advice_blinds
                .get(action_index)
                .and_then(|action| action.get(column))
                .ok_or(Error::InternalInvariant)?;
            (shared(coefficients), blind)
        }
        ActionPolynomial::Permutation(set_index) => {
            let product = quotient
                .permutation_openings
                .get(action_index)
                .and_then(|action| action.get(usize::from(set_index)))
                .ok_or(Error::InternalInvariant)?;
            (shared(&product.coefficients), product.blind)
        }
        ActionPolynomial::LookupProduct(lookup_index) => {
            let product = quotient
                .lookup_product_openings
                .get(action_index)
                .and_then(|action| action.get(usize::from(lookup_index)))
                .ok_or(Error::InternalInvariant)?;
            (shared(&product.coefficients), product.blind)
        }
        ActionPolynomial::LookupInput(lookup_index) => {
            let coefficients = quotient
                .permuted_lookup_coefficients
                .get(action_index)
                .and_then(|action| action.get(usize::from(lookup_index)))
                .ok_or(Error::InternalInvariant)?;
            (shared(&coefficients.input), coefficients.input_blind)
        }
        ActionPolynomial::LookupTable(lookup_index) => {
            let coefficients = quotient
                .permuted_lookup_coefficients
                .get(action_index)
                .and_then(|action| action.get(usize::from(lookup_index)))
                .ok_or(Error::InternalInvariant)?;
            (shared(&coefficients.table), coefficients.table_blind)
        }
    })
}

/// Binds one of the schedule's once-per-proof polynomials to its source and
/// blind.
fn bind_fixed_polynomial<'a>(
    target: &'a FixedTarget,
    vanishing: &VanishingPrefix,
    piece_polynomials: &'a [QuotientPiece],
    quotient_blind: &Fp,
    polynomial: FixedPolynomial,
) -> Result<(OpeningSource<'a>, Fp), Error> {
    Ok(match polynomial {
        FixedPolynomial::Fixed(column) => {
            let coefficients = target
                .fixed_polynomials()
                .coefficients()
                .get(usize::from(column))
                .map(<[Fp; N]>::as_slice)
                .ok_or(Error::InternalInvariant)?;
            (
                OpeningSource::Coefficients(PolySource::Borrowed(coefficients)),
                <Fp>::ONE,
            )
        }
        FixedPolynomial::Sigma(column) => {
            let coefficients = target
                .sigma_polynomials()
                .coefficients()
                .get(usize::from(column))
                .map(<[Fp; N]>::as_slice)
                .ok_or(Error::InternalInvariant)?;
            (
                OpeningSource::Coefficients(PolySource::Borrowed(coefficients)),
                <Fp>::ONE,
            )
        }
        FixedPolynomial::Quotient => (
            OpeningSource::QuotientPieces(piece_polynomials),
            *quotient_blind,
        ),
        FixedPolynomial::Vanishing => (OpeningSource::Linear(vanishing.mask), vanishing.blind),
    })
}

/// Appends one commitment's `x_1`-weighted source to its group's collapse
/// inputs: a dense source as one weighted term, the quotient as its pieces
/// with the `x^N` Horner weights the folded polynomial would carry, and the
/// linear mask as two weighted sparse terms. Instance sources accumulate into
/// one weighted Lagrange prefix before coefficient expansion.
pub(super) fn push_weighted_source<'a>(
    group: &mut WeightedGroup<'a>,
    source: OpeningSource<'a>,
    weight: &Fp,
    quotient_xn: &Fp,
) -> Result<(), Error> {
    match source {
        OpeningSource::Instance { statements, index } => {
            let statement = statements.get(index).ok_or(Error::InternalInvariant)?;
            let combined = group
                .instance
                .get_or_insert([Fp::ZERO; INSTANCE_VALUE_COUNT]);
            for (value, input) in combined.iter_mut().zip(statement.iter()) {
                *value = input.mul_add(weight, value);
            }
        }
        OpeningSource::Coefficients(coefficients) => {
            if coefficients.as_slice().len() != N {
                return Err(Error::InternalInvariant);
            }
            group.dense.push((coefficients, *weight));
        }
        OpeningSource::QuotientPieces(pieces) => {
            if pieces.len() != QUOTIENT_PIECES
                || pieces.iter().any(|piece| piece.coefficients.len() != N)
            {
                return Err(Error::InternalInvariant);
            }
            let mut piece_weight = *weight;
            for piece in pieces.iter() {
                group
                    .dense
                    .push((PolySource::Borrowed(&piece.coefficients), piece_weight));
                piece_weight = piece_weight.mul(quotient_xn);
            }
        }
        OpeningSource::Linear(mask) => {
            for (index, coefficient) in mask.iter().enumerate() {
                group.sparse.push((index, coefficient.mul(weight)));
            }
        }
    }
    Ok(())
}

pub(super) fn fold_quotient_blind(pieces: &[QuotientPiece], xn: &Fp) -> Result<Fp, Error> {
    if pieces.len() != QUOTIENT_PIECES || pieces.iter().any(|piece| piece.coefficients.len() != N) {
        return Err(Error::InternalInvariant);
    }
    Ok(pieces
        .iter()
        .rev()
        .fold(<Fp>::ZERO, |blind, piece| blind.mul_add(xn, &piece.blind)))
}

/// One opening group's collapse inputs: weighted dense sources summed per
/// coefficient together with one combined instance prefix expanded through
/// its bases, plus already-weighted sparse `(index, value)` terms added to
/// the assembled polynomial afterwards.
pub(super) struct WeightedGroup<'a> {
    pub(super) dense: Vec<(PolySource<'a>, Fp)>,
    pub(super) sparse: Vec<(usize, Fp)>,
    pub(super) instance: Option<[Fp; INSTANCE_VALUE_COUNT]>,
}

/// Collapses every opening group's weighted sources as coefficient-chunk
/// tasks, returning one polynomial per group in group order.
pub(super) fn parallel_weighted_sums(
    execution: Execution<'_>,
    groups: Vec<WeightedGroup>,
    instance_bases: &[[Fp; INSTANCE_VALUE_COUNT]],
) -> Result<Vec<SharedPoly>, Error> {
    if instance_bases.len() != N {
        return Err(Error::InternalInvariant);
    }
    execution
        .map(groups, |group, execution| {
            if group
                .dense
                .iter()
                .any(|(source, _)| source.as_slice().len() != N)
            {
                return Err(Error::InternalInvariant);
            }
            let empty = group.dense.is_empty() && group.instance.is_none();
            let mut polynomial = execution.buffer(N, /* clear sparse-only sums */ empty);
            if !empty {
                for_each_chunk_mut(
                    &mut polynomial,
                    COEFFICIENT_CHUNK,
                    execution.budget,
                    &execution,
                    |chunk, values, _| {
                        for (offset, value) in values.iter_mut().enumerate() {
                            let index = chunk * COEFFICIENT_CHUNK + offset;
                            *value = <Fp>::sum_of_product_pairs(
                                group
                                    .dense
                                    .iter()
                                    .map(|(source, weight)| (&source.as_slice()[index], weight))
                                    .chain(group.instance.iter().flat_map(|prefix| {
                                        instance_bases[index].iter().zip(prefix)
                                    })),
                            );
                        }
                    },
                );
            }
            for (index, value) in group.sparse {
                let coefficient = polynomial.get_mut(index).ok_or(Error::InternalInvariant)?;
                *coefficient = coefficient.add(&value);
            }
            Ok(SharedPoly::new(polynomial))
        })
        .into_iter()
        .collect()
}

/// Folds the opening groups' polynomial quotients with Horner weights.
///
/// Every group's divisor contains `X - x`. Quotient extraction by a fixed
/// monic divisor is linear, and extracting quotients by two monic factors in
/// either order gives the quotient by their product, even with nonzero
/// remainders. Divide by the other factors per group, then by `X - x` once
/// after folding, saving `POINT_SETS - 1` linear divisions. Form each remaining
/// small monic divisor so its factors share one coefficient walk.
pub(super) fn parallel_multiopen_quotient(
    execution: Execution<'_>,
    polynomials: &[SharedPoly],
    points: &[Fp; OPENING_POINTS],
    challenge: &Fp,
) -> Result<Buffer<Fp>, Error> {
    if polynomials.len() != opening_stage::POINT_SETS
        || polynomials.iter().any(|polynomial| polynomial.len() != N)
    {
        return Err(Error::InternalInvariant);
    }
    let jobs = polynomials.iter().enumerate();
    let terms = execution.map(jobs, |(group_index, polynomial), execution| {
        let mut divided = execution.copy(polynomial);
        let mut other_points = [<Fp>::ZERO; OPENING_POINTS - 1];
        let mut point_count = 0;
        for (index, id) in OPENING_GROUPS[group_index]
            .point_ids()
            .filter(|&id| id != COMMON_OPENING_POINT)
            .enumerate()
        {
            other_points[index] = points[id];
            point_count = index + 1;
        }
        let quotient_start = match &other_points[..point_count] {
            [] => 0,
            [point] => divide_linear_in_place(&mut divided, point),
            roots => {
                let mut divisor = [<Fp>::ZERO; OPENING_POINTS];
                let len = vanishing_polynomial(roots, &mut divisor)
                    .expect("one coefficient per point and the monic leading term");
                divide_monic_in_place(&mut divided, &divisor[..len])
                    .expect("a vanishing polynomial is monic")
            }
        };
        (divided, quotient_start)
    });
    let terms: [_; opening_stage::POINT_SETS] =
        terms.try_into().map_err(|_| Error::InternalInvariant)?;
    let [(mut quotient, start), rest @ ..] = terms;
    if start != 0 {
        return Err(Error::InternalInvariant);
    }
    let mut weights = [Fp::ONE; opening_stage::POINT_SETS];
    for index in (0..weights.len() - 1).rev() {
        weights[index] = weights[index + 1].mul(challenge);
    }
    // Read each divided suffix with a virtual zero tail. Group zero has no
    // remaining divisor, so its owned buffer can receive the combined sum.
    for_each_chunk_mut(
        &mut quotient,
        COEFFICIENT_CHUNK,
        execution.budget,
        &execution,
        |chunk, values, _| {
            for (offset, value) in values.iter_mut().enumerate() {
                let index = chunk * COEFFICIENT_CHUNK + offset;
                *value = Fp::sum_of_product_pairs(
                    core::iter::once((&*value, &weights[0])).chain(
                        rest.iter()
                            .zip(&weights[1..])
                            .map(|((polynomial, start), weight)| {
                                (polynomial.get(index + start).unwrap_or(&Fp::ZERO), weight)
                            }),
                    ),
                );
            }
        },
    );
    let quotient_start = divide_linear_in_place(&mut quotient, &points[COMMON_OPENING_POINT]);
    quotient.copy_within(quotient_start.., 0);
    quotient[N - quotient_start..].fill(<Fp>::ZERO);
    Ok(quotient)
}

/// The deferred Horner fold as one pool phase: the accumulator is the leading
/// term, so the result is
/// `accumulator·c^m + p_0·c^(m-1) + … + p_(m-1)`, each output coefficient one
/// product sum with one Montgomery reduction — the same operations per
/// coefficient as the test-only `deferred_horner_polynomial_fold_in_place`.
/// Independent tasks compute `COEFFICIENT_CHUNK` chunks and reassemble them
/// in order, so the result equals the serial walk.
pub(super) fn parallel_deferred_horner_fold(
    execution: Execution<'_>,
    accumulator: SharedPoly,
    polynomials: &[SharedPoly],
    challenge: &Fp,
) -> Result<Buffer<Fp>, Error> {
    if accumulator.len() != N || polynomials.iter().any(|polynomial| polynomial.len() != N) {
        return Err(Error::InternalInvariant);
    }
    let mut weights = execution.buffer(polynomials.len() + 1, false);
    let mut power = <Fp>::ONE;
    for weight in weights.iter_mut().rev() {
        *weight = power;
        power = power.mul(challenge);
    }
    let (leading_weight, weights) = weights.split_first().unwrap();
    let mut folded = accumulator.into_unique().ok_or(Error::InternalInvariant)?;
    for_each_chunk_mut(
        &mut folded,
        COEFFICIENT_CHUNK,
        execution.budget,
        &execution,
        |chunk, values, _| {
            for (offset, value) in values.iter_mut().enumerate() {
                let index = chunk * COEFFICIENT_CHUNK + offset;
                *value = <Fp>::sum_of_product_pairs(
                    core::iter::once((&*value, leading_weight)).chain(
                        polynomials
                            .iter()
                            .zip(weights)
                            .map(|(polynomial, weight)| (&polynomial[index], weight)),
                    ),
                );
            }
        },
    );
    Ok(folded)
}
