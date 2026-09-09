use super::super::{
    Coeff, Polynomial,
    commitment::{self, Blind, Params},
    evaluate_polynomial_with_powers, power_vector,
};
use super::{
    ChallengeX1, ChallengeX2, ChallengeX3, ChallengeX4, ProverQuery, Query,
    construct_intermediate_sets,
};

use crate::arithmetic::CurveAffine;
use crate::multicore;
use crate::transcript::{EncodedChallenge, TranscriptWrite};

use ff::{BatchInvert, Field};
use group::Curve;
use pasta_curves::{deferred::DeferredField, pallas, vesta};
use rand_core::Rng;
use std::any::{Any, TypeId};
use std::hash::Hash;
use std::io;
use std::marker::PhantomData;

// Amortize task scheduling over at least this many field operations per
// worker.
const MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD: usize = 1 << 10;
// Bound the field payload retained for simultaneous point-set quotient terms.
// This excludes `Vec` metadata and allocator rounding.
const MAX_PARALLEL_Q_PRIME_FIELD_BYTES: usize = 8 * 1024 * 1024;
const DEFERRED_FOLD_LANES: usize = 2;

fn fold_polynomial_range<F: Field>(
    values: &mut [F],
    start: usize,
    polynomials: &[&Polynomial<F, Coeff>],
    challenge: F,
) {
    for polynomial in polynomials {
        let common_len = polynomial
            .values
            .len()
            .saturating_sub(start)
            .min(values.len());
        if common_len > 0 {
            for (value, coefficient) in values[..common_len]
                .iter_mut()
                .zip(&polynomial.values[start..start + common_len])
            {
                *value *= challenge;
                *value += coefficient;
            }
        }
        for value in &mut values[common_len..] {
            *value *= challenge;
        }
    }
}

fn fold_polynomial_range_deferred<F: DeferredField>(
    values: &mut [F],
    start: usize,
    polynomials: &[&Polynomial<F, Coeff>],
    powers: &[F],
) {
    debug_assert!(polynomials.len() > 2);
    debug_assert!(powers.len() >= polynomials.len());

    let (last, products) = polynomials
        .split_last()
        .expect("point-set group is nonempty");
    let paired_len = values.len() - values.len() % DEFERRED_FOLD_LANES;
    let (pairs, remainder) = values.split_at_mut(paired_len);
    for (pair_index, pair) in pairs.chunks_exact_mut(DEFERRED_FOLD_LANES).enumerate() {
        let coefficient_index = start + pair_index * DEFERRED_FOLD_LANES;
        // Independent lanes shorten the multiply-accumulate dependency chain
        // while sharing each challenge-power load.
        let mut accumulators = [F::Accumulator::default(); DEFERRED_FOLD_LANES];
        for (polynomial_index, polynomial) in products.iter().enumerate() {
            let exponent = polynomials.len() - 1 - polynomial_index;
            let power = &powers[exponent];
            if let Some(coefficients) = polynomial
                .values
                .get(coefficient_index..coefficient_index + DEFERRED_FOLD_LANES)
            {
                F::mul_accumulate(&mut accumulators[0], &coefficients[0], power);
                F::mul_accumulate(&mut accumulators[1], &coefficients[1], power);
            } else {
                for (lane, accumulator) in accumulators.iter_mut().enumerate() {
                    if let Some(coefficient) = polynomial.values.get(coefficient_index + lane) {
                        F::mul_accumulate(accumulator, coefficient, power);
                    }
                }
            }
        }

        pair[0] = F::reduce(accumulators[0]);
        pair[1] = F::reduce(accumulators[1]);
        if let Some(coefficients) = last
            .values
            .get(coefficient_index..coefficient_index + DEFERRED_FOLD_LANES)
        {
            pair[0] += &coefficients[0];
            pair[1] += &coefficients[1];
        } else {
            for (lane, value) in pair.iter_mut().enumerate() {
                if let Some(coefficient) = last.values.get(coefficient_index + lane) {
                    *value += coefficient;
                }
            }
        }
    }

    if let Some(value) = remainder.first_mut() {
        let coefficient_index = start + paired_len;
        let mut accumulator = F::Accumulator::default();
        for (polynomial_index, polynomial) in products.iter().enumerate() {
            if let Some(coefficient) = polynomial.values.get(coefficient_index) {
                let exponent = polynomials.len() - 1 - polynomial_index;
                F::mul_accumulate(&mut accumulator, coefficient, &powers[exponent]);
            }
        }
        *value = F::reduce(accumulator);
        if let Some(coefficient) = last.values.get(coefficient_index) {
            *value += coefficient;
        }
    }
}

fn collapse_polynomials_with<F: Field>(
    groups: &[Vec<&Polynomial<F, Coeff>>],
    fold_range: impl Fn(&mut [F], usize, &[&Polynomial<F, Coeff>]) + Copy + Send + Sync,
) -> Vec<Polynomial<F, Coeff>> {
    let mut collapsed = groups
        .iter()
        .map(|group| {
            let first = group.first().expect("point-set group is nonempty");
            Polynomial {
                values: first.values.clone(),
                _marker: PhantomData,
            }
        })
        .collect::<Vec<_>>();

    let total_work = collapsed
        .iter()
        .zip(groups)
        .map(|(polynomial, group)| {
            polynomial
                .values
                .len()
                .saturating_mul(group.len().saturating_sub(1))
        })
        .sum::<usize>();
    let thread_count = multicore::current_num_threads();
    if thread_count == 1
        || total_work.div_ceil(thread_count) < MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD
    {
        for (polynomial, group) in collapsed.iter_mut().zip(groups) {
            fold_range(&mut polynomial.values, 0, group);
        }
        return collapsed;
    }
    let work_per_task = total_work.div_ceil(thread_count);

    multicore::scope(|scope| {
        for (polynomial, group) in collapsed.iter_mut().zip(groups) {
            let folds_per_coefficient = group.len().saturating_sub(1);
            if folds_per_coefficient == 0 {
                continue;
            }
            let chunk_size = work_per_task.div_ceil(folds_per_coefficient);
            for (chunk_index, values) in polynomial.values.chunks_mut(chunk_size).enumerate() {
                let start = chunk_index * chunk_size;
                scope.spawn(move |_| fold_range(values, start, group));
            }
        }
    });

    collapsed
}

fn collapse_polynomials_horner<F: Field>(
    groups: &[Vec<&Polynomial<F, Coeff>>],
    challenge: F,
) -> Vec<Polynomial<F, Coeff>> {
    collapse_polynomials_with(groups, |values, start, group| {
        fold_polynomial_range(values, start, &group[1..], challenge);
    })
}

fn collapse_polynomials_deferred<F: DeferredField>(
    groups: &[Vec<&Polynomial<F, Coeff>>],
    challenge: F,
) -> Vec<Polynomial<F, Coeff>> {
    if multicore::current_num_threads() > 1 {
        return collapse_polynomials_horner(groups, challenge);
    }

    let max_group_len = groups.iter().map(Vec::len).max().unwrap_or(0);
    let mut powers = Vec::with_capacity(max_group_len);
    if max_group_len > 0 {
        powers.push(F::ONE);
        for exponent in 1..max_group_len {
            powers.push(powers[exponent - 1] * challenge);
        }
    }

    collapse_polynomials_with(groups, |values, start, group| {
        if group.len() <= 2 {
            fold_polynomial_range(values, start, &group[1..], challenge);
        } else {
            fold_polynomial_range_deferred(values, start, group, &powers);
        }
    })
}

fn collapse_polynomials_pasta<F: Field, T: DeferredField + 'static>(
    groups: &[Vec<&Polynomial<F, Coeff>>],
    challenge: F,
) -> Vec<Polynomial<F, Coeff>> {
    let challenge = *(&challenge as &dyn Any)
        .downcast_ref::<T>()
        .expect("the challenge field was checked before conversion");
    let groups = groups
        .iter()
        .map(|group| {
            group
                .iter()
                .map(|polynomial| {
                    (*polynomial as &dyn Any)
                        .downcast_ref::<Polynomial<T, Coeff>>()
                        .expect("the polynomial field matches the challenge field")
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let collapsed: Box<dyn Any> = Box::new(collapse_polynomials_deferred(&groups, challenge));
    *collapsed
        .downcast::<Vec<Polynomial<F, Coeff>>>()
        .expect("the output polynomial field matches the input field")
}

fn collapse_polynomials<F: Field>(
    groups: &[Vec<&Polynomial<F, Coeff>>],
    challenge: F,
) -> Vec<Polynomial<F, Coeff>> {
    if TypeId::of::<F>() == TypeId::of::<pallas::Base>() {
        collapse_polynomials_pasta::<F, pallas::Base>(groups, challenge)
    } else if TypeId::of::<F>() == TypeId::of::<vesta::Base>() {
        collapse_polynomials_pasta::<F, vesta::Base>(groups, challenge)
    } else {
        collapse_polynomials_horner(groups, challenge)
    }
}

fn kate_division_in_place<F: Field>(polynomial: &mut Vec<F>, point: F) -> F {
    let mut quotient = polynomial
        .pop()
        .expect("a polynomial divided by a linear factor is nonempty");
    for coefficient in polynomial.iter_mut().rev() {
        let remainder = *coefficient + quotient * point;
        *coefficient = quotient;
        quotient = remainder;
    }
    quotient
}

fn prepare_q_prime_term<F: Field>(
    polynomial: &Polynomial<F, Coeff>,
    points: &[F],
    domain_len: usize,
) -> (Polynomial<F, Coeff>, Vec<F>) {
    let mut values = polynomial.values.clone();
    let remainders = points
        .iter()
        .map(|point| kate_division_in_place(&mut values, *point))
        .collect();
    values.resize(domain_len, F::ZERO);
    (
        Polynomial {
            values,
            _marker: PhantomData,
        },
        remainders,
    )
}

struct PreparedQPrime<F> {
    polynomial: Polynomial<F, Coeff>,
    division_remainders: Vec<Vec<F>>,
}

struct QPrimeEvaluationTerm<F> {
    remainder: F,
    vanishing_inverse: F,
}

struct PreparedQPrimeEvaluation<F> {
    terms: Vec<QPrimeEvaluationTerm<F>>,
}

fn prepare_q_prime_evaluation<F: Field>(
    point_sets: &[Vec<F>],
    division_remainders: &[Vec<F>],
    point: F,
) -> Option<PreparedQPrimeEvaluation<F>> {
    assert_eq!(point_sets.len(), division_remainders.len());

    // Successive divisions give
    //
    // Q_i(X) = R_i(X) + Z_i(X) T_i(X),
    //
    // with the scalar remainders forming R_i in Newton basis. Evaluate each
    // small R_i and Z_i, then batch the inversions of the Z_i evaluations.
    let mut terms = point_sets
        .iter()
        .zip(division_remainders)
        .map(|(points, remainders)| {
            assert_eq!(points.len(), remainders.len());
            let (last_remainder, earlier_remainders) = remainders
                .split_last()
                .expect("a point set contains at least one point");
            let remainder = earlier_remainders.iter().zip(points).rev().fold(
                *last_remainder,
                |evaluation, (remainder, query_point)| {
                    *remainder + (point - query_point) * evaluation
                },
            );
            let vanishing_inverse = points.iter().fold(F::ONE, |denominator, query_point| {
                denominator * (point - query_point)
            });
            QPrimeEvaluationTerm {
                remainder,
                vanishing_inverse,
            }
        })
        .collect::<Vec<_>>();
    if terms
        .iter()
        .any(|term| bool::from(term.vanishing_inverse.is_zero()))
    {
        return None;
    }
    terms
        .iter_mut()
        .map(|term| &mut term.vanishing_inverse)
        .batch_invert();

    Some(PreparedQPrimeEvaluation { terms })
}

fn finish_q_prime_evaluation<F: Field>(
    prepared: PreparedQPrimeEvaluation<F>,
    q_evaluations: &[F],
    challenge: F,
) -> F {
    assert_eq!(prepared.terms.len(), q_evaluations.len());

    let mut term_evaluations = q_evaluations
        .iter()
        .zip(prepared.terms)
        .map(|(q_evaluation, term)| (*q_evaluation - term.remainder) * term.vanishing_inverse);
    let first = term_evaluations
        .next()
        .expect("there is at least one multi-opening point set");
    term_evaluations.fold(first, |evaluation, term_evaluation| {
        evaluation * challenge + term_evaluation
    })
}

fn fold_q_prime_range<F: Field>(
    accumulator: &mut [F],
    start: usize,
    terms: &[Polynomial<F, Coeff>],
    challenge: F,
) {
    for (offset, accumulator) in accumulator.iter_mut().enumerate() {
        let coefficient_index = start + offset;
        for term in terms {
            *accumulator *= challenge;
            *accumulator += term.values[coefficient_index];
        }
    }
}

fn parallel_q_prime_terms_fit<F: Field>(
    polynomials: &[Polynomial<F, Coeff>],
    domain_len: usize,
) -> bool {
    polynomials
        .iter()
        .try_fold(0usize, |total, polynomial| {
            polynomial
                .len()
                .max(domain_len)
                .checked_mul(std::mem::size_of::<F>())
                .and_then(|bytes| total.checked_add(bytes))
        })
        .is_some_and(|bytes| bytes <= MAX_PARALLEL_Q_PRIME_FIELD_BYTES)
}

fn prepare_q_prime<F: Field>(
    point_sets: &[Vec<F>],
    polynomials: &[Polynomial<F, Coeff>],
    challenge: F,
    domain_len: usize,
) -> PreparedQPrime<F> {
    debug_assert_eq!(point_sets.len(), polynomials.len());

    let division_work =
        point_sets
            .iter()
            .zip(polynomials)
            .fold(0usize, |total, (points, polynomial)| {
                total.saturating_add(points.len().saturating_mul(polynomial.len()))
            });
    let division_workers = multicore::current_num_threads().min(point_sets.len());
    let prepare_in_parallel = division_workers > 1
        && division_work.div_ceil(division_workers) >= MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD
        && parallel_q_prime_terms_fit(polynomials, domain_len);

    if !prepare_in_parallel {
        let mut accumulator: Option<Polynomial<F, Coeff>> = None;
        let mut division_remainders = Vec::with_capacity(point_sets.len());
        for (points, polynomial) in point_sets.iter().zip(polynomials) {
            let (term, remainders) = prepare_q_prime_term(polynomial, points, domain_len);
            division_remainders.push(remainders);
            if let Some(accumulator) = accumulator.as_mut() {
                fold_q_prime_range(
                    &mut accumulator.values,
                    0,
                    std::slice::from_ref(&term),
                    challenge,
                );
            } else {
                accumulator = Some(term);
            }
        }
        return PreparedQPrime {
            polynomial: accumulator.expect("there is at least one multi-opening point set"),
            division_remainders,
        };
    }

    let mut terms = (0..point_sets.len()).map(|_| None).collect::<Vec<_>>();
    multicore::scope(|scope| {
        for ((points, polynomial), output) in point_sets.iter().zip(polynomials).zip(&mut terms) {
            scope.spawn(move |_| {
                *output = Some(prepare_q_prime_term(polynomial, points, domain_len));
            });
        }
    });
    let (terms, division_remainders): (Vec<_>, Vec<_>) = terms
        .into_iter()
        .map(|term| term.expect("each point-set quotient task completed"))
        .unzip();

    let mut terms = terms.into_iter();
    let mut accumulator = terms
        .next()
        .expect("there is at least one multi-opening point set");
    let terms = terms.as_slice();
    let fold_work = accumulator.len().saturating_mul(terms.len());
    let fold_workers =
        multicore::current_num_threads().min(fold_work / MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD);
    if terms.is_empty() || fold_workers <= 1 {
        fold_q_prime_range(&mut accumulator.values, 0, terms, challenge);
        return PreparedQPrime {
            polynomial: accumulator,
            division_remainders,
        };
    }

    let work_per_task = fold_work.div_ceil(fold_workers);
    let chunk_size = work_per_task.div_ceil(terms.len()).max(1);
    multicore::scope(|scope| {
        for (chunk_index, values) in accumulator.values.chunks_mut(chunk_size).enumerate() {
            let start = chunk_index * chunk_size;
            scope.spawn(move |_| fold_q_prime_range(values, start, terms, challenge));
        }
    });

    PreparedQPrime {
        polynomial: accumulator,
        division_remainders,
    }
}

// A `Vec` is required by `evaluate_polynomial_with_powers` for safe runtime
// downcasting to the Pasta field.
#[allow(clippy::ptr_arg)]
fn evaluate_polynomials_with_side_work<F, R, W>(
    polynomials: &[Polynomial<F, Coeff>],
    powers: &Vec<F>,
    side_work: W,
) -> (Vec<F>, R)
where
    F: Field + 'static,
    R: Send,
    W: FnOnce() -> R + Send,
{
    if polynomials.is_empty() {
        return (Vec::new(), side_work());
    }

    let thread_count = multicore::current_num_threads();
    let worker_count = thread_count.min(polynomials.len());
    let total_work = polynomials.iter().fold(0usize, |total, polynomial| {
        total.saturating_add(polynomial.len())
    });
    if worker_count <= 1
        || total_work.div_ceil(worker_count) < MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD
    {
        let evaluations = polynomials
            .iter()
            .map(|polynomial| evaluate_polynomial_with_powers(polynomial, powers))
            .collect();
        return (evaluations, side_work());
    }

    let mut evaluations = vec![F::ZERO; polynomials.len()];
    let mut side_output = None;
    let polynomials_per_task = polynomials.len().div_ceil(worker_count);
    let evaluation_task_count = polynomials.len().div_ceil(polynomials_per_task);
    let last_task_start = (evaluation_task_count - 1) * polynomials_per_task;
    let (polynomials, last_polynomials) = polynomials.split_at(last_task_start);
    let (regular_evaluations, last_evaluations) = evaluations.split_at_mut(last_task_start);
    // Use an otherwise-idle worker when one is available. If every worker has
    // an evaluation chunk, append the small side job to the shortest chunk to
    // avoid adding another task and its scheduling overhead.
    let separate_side_task = thread_count > evaluation_task_count;
    multicore::scope(|scope| {
        for (polynomials, evaluations) in polynomials
            .chunks(polynomials_per_task)
            .zip(regular_evaluations.chunks_mut(polynomials_per_task))
        {
            scope.spawn(move |_| {
                for (polynomial, evaluation) in polynomials.iter().zip(evaluations) {
                    *evaluation = evaluate_polynomial_with_powers(polynomial, powers);
                }
            });
        }
        let evaluate_last = || {
            for (polynomial, evaluation) in last_polynomials.iter().zip(last_evaluations) {
                *evaluation = evaluate_polynomial_with_powers(polynomial, powers);
            }
        };
        if separate_side_task {
            scope.spawn(|_| evaluate_last());
            scope.spawn(|_| side_output = Some(side_work()));
        } else {
            scope.spawn(|_| {
                evaluate_last();
                side_output = Some(side_work());
            });
        }
    });
    (
        evaluations,
        side_output.expect("the independent side task completed"),
    )
}

fn scale_and_add_polynomial<F: Field>(
    polynomial: Polynomial<F, Coeff>,
    scale: F,
    addend: &Polynomial<F, Coeff>,
) -> Polynomial<F, Coeff> {
    if multicore::current_num_threads() == 1 {
        return polynomial * scale + addend;
    }

    debug_assert_eq!(polynomial.len(), addend.len());
    let mut polynomial = polynomial;
    crate::arithmetic::parallelize(&mut polynomial.values, |values, start| {
        for (value, addend) in values.iter_mut().zip(&addend.values[start..]) {
            *value *= scale;
            *value += addend;
        }
    });
    polynomial
}

/// Create a multi-opening proof.
///
/// # Errors
///
/// Returns [`std::io::ErrorKind::InvalidInput`] if `queries` is empty or
/// contains more than one query for the same commitment at the same point.
pub fn create_proof<
    'a,
    I,
    C: CurveAffine,
    E: EncodedChallenge<C>,
    R: Rng,
    T: TranscriptWrite<C, E>,
>(
    params: &Params<C>,
    mut rng: R,
    transcript: &mut T,
    queries: I,
) -> io::Result<()>
where
    I: IntoIterator<Item = ProverQuery<'a, C>> + Clone,
{
    let x_1: ChallengeX1<_> = transcript.squeeze_challenge_scalar();
    let x_2: ChallengeX2<_> = transcript.squeeze_challenge_scalar();

    let (poly_map, point_sets) = construct_intermediate_sets(queries).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "queries iterator is empty or contains duplicate queries",
        )
    })?;

    // Collapse openings at same point sets together into single openings using
    // x_1 challenge.
    let mut polynomial_groups = vec![vec![]; point_sets.len()];
    let mut q_blinds = vec![Blind(C::Scalar::ZERO); point_sets.len()];
    for commitment_data in poly_map {
        let set_index = commitment_data.set_index;
        polynomial_groups[set_index].push(commitment_data.commitment.poly);
        q_blinds[set_index] *= *x_1;
        q_blinds[set_index] += commitment_data.commitment.blind;
    }
    let mut q_polys = collapse_polynomials(&polynomial_groups, *x_1);
    // Queried polynomials may be constructed in a domain smaller than the
    // parameters; their missing high coefficients are zero.
    for q_poly in &mut q_polys {
        if q_poly.values.len() < params.n as usize {
            q_poly.values.resize(params.n as usize, C::Scalar::ZERO);
        }
    }

    let PreparedQPrime {
        polynomial: q_prime_poly,
        division_remainders,
    } = prepare_q_prime(&point_sets, &q_polys, *x_2, params.n as usize);

    let q_prime_blind = Blind(C::Scalar::random(&mut rng));
    let q_prime_commitment = params.commit(&q_prime_poly, q_prime_blind).to_affine();

    transcript.write_point(q_prime_commitment)?;

    let x_3: ChallengeX3<_> = transcript.squeeze_challenge_scalar();
    let powers = power_vector(*x_3, params.n as usize);

    // The evaluations are independent, but their transcript order is fixed.
    // Prepare the small q' evaluation terms in the same scope so their batch
    // inversion is hidden beneath the domain-sized evaluations.
    let (q_evaluations, prepared_q_prime_evaluation) =
        evaluate_polynomials_with_side_work(&q_polys, &powers, || {
            prepare_q_prime_evaluation(&point_sets, &division_remainders, *x_3)
        });
    for evaluation in &q_evaluations {
        transcript.write_scalar(*evaluation)?;
    }

    // The synthetic divisions used to build q' left one scalar remainder per
    // queried point. Unwind those divisions at x_3 to derive q'(x_3) from the
    // Q_i(x_3) values already required by the transcript. The verifier rejects
    // a collision between x_3 and a queried point; retain the old evaluation
    // path for that negligible event so proof creation remains infallible.
    let q_prime_evaluation = prepared_q_prime_evaluation
        .map(|prepared| finish_q_prime_evaluation(prepared, &q_evaluations, *x_2))
        .unwrap_or_else(|| evaluate_polynomial_with_powers(&q_prime_poly, &powers));

    let x_4: ChallengeX4<_> = transcript.squeeze_challenge_scalar();

    let p_evaluation = q_evaluations
        .iter()
        .fold(q_prime_evaluation, |evaluation, q_evaluation| {
            evaluation * *x_4 + q_evaluation
        });

    let (p_poly, p_poly_blind) = q_polys.into_iter().zip(q_blinds).fold(
        (q_prime_poly, q_prime_blind),
        |(q_prime_poly, q_prime_blind), (poly, blind)| {
            (
                scale_and_add_polynomial(q_prime_poly, *x_4, &poly),
                Blind((q_prime_blind.0 * &(*x_4)) + &blind.0),
            )
        },
    );

    commitment::create_proof_with_powers(
        params,
        rng,
        transcript,
        &p_poly,
        p_poly_blind,
        *x_3,
        powers,
        p_evaluation,
    )
}

#[doc(hidden)]
#[derive(Copy, Clone)]
pub struct PolynomialPointer<'a, C: CurveAffine> {
    poly: &'a Polynomial<C::Scalar, Coeff>,
    blind: commitment::Blind<C::Scalar>,
}

impl<'a, C: CurveAffine> PartialEq for PolynomialPointer<'a, C> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.poly, other.poly)
    }
}

impl<'a, C: CurveAffine> Eq for PolynomialPointer<'a, C> {}

impl<'a, C: CurveAffine> Hash for PolynomialPointer<'a, C> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.poly, state)
    }
}

impl<'a, C: CurveAffine> Query<C::Scalar> for ProverQuery<'a, C> {
    type Commitment = PolynomialPointer<'a, C>;
    type Eval = ();

    fn get_point(&self) -> C::Scalar {
        self.point
    }
    fn get_eval(&self) {}
    fn get_commitment(&self) -> Self::Commitment {
        PolynomialPointer {
            poly: self.poly,
            blind: self.blind,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Coeff, MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD, Polynomial, collapse_polynomials,
        evaluate_polynomials_with_side_work, finish_q_prime_evaluation, kate_division_in_place,
        power_vector, prepare_q_prime, prepare_q_prime_evaluation, scale_and_add_polynomial,
    };
    use crate::arithmetic::{eval_polynomial, kate_division};
    use ff::Field;
    use pasta_curves::{Fp, Fq};
    use std::fmt::Debug;
    use std::marker::PhantomData;

    fn reference_collapse<F: Field>(
        groups: &[Vec<&Polynomial<F, Coeff>>],
        challenge: F,
    ) -> Vec<Polynomial<F, Coeff>> {
        groups
            .iter()
            .map(|group| {
                group[1..]
                    .iter()
                    .fold(group[0].clone(), |accumulator, polynomial| {
                        accumulator * challenge + polynomial
                    })
            })
            .collect()
    }

    fn streaming_collapse_matches_operator_collapse<F>()
    where
        F: Field + From<u64> + Debug,
    {
        let long = MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD * 2 + 1;
        let lengths = [
            vec![long, long - 1, long + 1, long, long],
            vec![3],
            vec![6, 9],
        ];
        let groups = lengths
            .iter()
            .enumerate()
            .map(|(group_index, lengths)| {
                lengths
                    .iter()
                    .enumerate()
                    .map(|(polynomial_index, length)| Polynomial {
                        values: (0..*length)
                            .map(|coefficient_index| {
                                F::from(
                                    100 * group_index as u64
                                        + 10 * polynomial_index as u64
                                        + coefficient_index as u64,
                                )
                            })
                            .collect(),
                        _marker: PhantomData,
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let group_refs = groups
            .iter()
            .map(|group| group.iter().collect::<Vec<_>>())
            .collect::<Vec<_>>();

        for challenge in [F::ZERO, F::ONE, -F::ONE, F::from(17)] {
            let expected = reference_collapse(&group_refs, challenge);
            let check = || {
                let actual = collapse_polynomials(&group_refs, challenge);
                for (expected, actual) in expected.iter().zip(&actual) {
                    assert_eq!(&expected[..], &actual[..]);
                }
            };

            #[cfg(feature = "multicore")]
            for thread_count in [1, 4] {
                maybe_rayon::ThreadPoolBuilder::new()
                    .num_threads(thread_count)
                    .build()
                    .unwrap()
                    .install(&check);
            }
            #[cfg(not(feature = "multicore"))]
            check();
        }
    }

    fn zero_challenge_selects_last_polynomial<F>()
    where
        F: Field + From<u64> + Debug,
    {
        let h = Polynomial {
            values: vec![F::from(2), F::from(3), F::from(5)],
            _marker: PhantomData,
        };
        let r = Polynomial {
            values: vec![F::from(7), F::from(11), F::from(13)],
            _marker: PhantomData,
        };

        let collapsed = collapse_polynomials(&[vec![&h, &r]], F::ZERO);

        assert_eq!(collapsed.len(), 1);
        assert_eq!(collapsed[0].values, r.values);
    }

    fn short_trailing_polynomial_matches_zero_padding<F>()
    where
        F: Field + From<u64> + Debug,
    {
        let len = MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD * 2 + 1;
        let first = Polynomial::from_coefficients(
            (0..len).map(|index| F::from(index as u64 + 1)).collect(),
        );
        let trailing = Polynomial::from_coefficients(vec![F::from(7), F::from(11)]);
        let mut padded = Polynomial::from_coefficients(vec![F::ZERO; len]);
        padded[..][..trailing.len()].copy_from_slice(&trailing);

        for challenge in [F::ZERO, F::ONE, -F::ONE, F::from(17)] {
            let expected = collapse_polynomials(&[vec![&first, &padded]], challenge);
            let check = || {
                let actual = collapse_polynomials(&[vec![&first, &trailing]], challenge);
                assert_eq!(&actual[0][..], &expected[0][..]);
            };

            #[cfg(feature = "multicore")]
            for thread_count in [1, 4] {
                maybe_rayon::ThreadPoolBuilder::new()
                    .num_threads(thread_count)
                    .build()
                    .unwrap()
                    .install(check);
            }
            #[cfg(not(feature = "multicore"))]
            check();
        }
    }

    fn in_place_kate_division_matches_allocating<F>()
    where
        F: Field + From<u64> + Debug,
    {
        for (coefficients, points) in [
            (vec![F::from(9)], vec![F::ZERO]),
            (
                (0..8).map(|value| F::from(value + 1)).collect(),
                vec![F::ZERO, F::ONE, -F::ONE, F::from(7)],
            ),
        ] {
            let mut expected = coefficients.clone();
            let mut expected_remainders = Vec::with_capacity(points.len());
            for point in &points {
                expected_remainders.push(eval_polynomial(&expected, *point));
                expected = kate_division(&expected, *point);
            }

            let mut actual = coefficients;
            let actual_remainders = points
                .iter()
                .map(|point| kate_division_in_place(&mut actual, *point))
                .collect::<Vec<_>>();
            assert_eq!(expected, actual);
            assert_eq!(expected_remainders, actual_remainders);
        }
    }

    fn reference_q_prime<F: Field>(
        point_sets: &[Vec<F>],
        polynomials: &[Polynomial<F, Coeff>],
        challenge: F,
        domain_len: usize,
    ) -> Polynomial<F, Coeff> {
        point_sets
            .iter()
            .zip(polynomials)
            .fold(None, |accumulator, (points, polynomial)| {
                let mut values = points
                    .iter()
                    .fold(polynomial.values.clone(), |values, point| {
                        kate_division(&values, *point)
                    });
                values.resize(domain_len, F::ZERO);
                let term = Polynomial {
                    values,
                    _marker: PhantomData,
                };
                Some(match accumulator {
                    Some(accumulator) => accumulator * challenge + &term,
                    None => term,
                })
            })
            .expect("the test has point sets")
    }

    fn parallel_q_prime_matches_ordered_operator_fold<F>()
    where
        F: Field + From<u64> + Debug,
    {
        // This size crosses both parallel-work thresholds with four workers.
        let domain_len = MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD * 2 + 1;
        let point_sets = vec![
            vec![F::from(2)],
            vec![F::from(3), F::from(5)],
            vec![F::ZERO, -F::ONE, F::from(11)],
        ];
        let polynomials = (0..point_sets.len())
            .map(|polynomial_index| Polynomial {
                values: (0..domain_len)
                    .map(|coefficient_index| {
                        F::from(
                            1 + polynomial_index as u64 * domain_len as u64
                                + coefficient_index as u64,
                        )
                    })
                    .collect(),
                _marker: PhantomData,
            })
            .collect::<Vec<_>>();

        for challenge in [F::ZERO, F::ONE, -F::ONE, F::from(17)] {
            let expected = reference_q_prime(&point_sets, &polynomials, challenge, domain_len);
            let check = || {
                let actual = prepare_q_prime(&point_sets, &polynomials, challenge, domain_len);
                assert_eq!(&actual.polynomial[..], &expected[..]);

                for point in [F::from(13), F::from(19)] {
                    let q_evaluations = polynomials
                        .iter()
                        .map(|polynomial| eval_polynomial(polynomial, point))
                        .collect::<Vec<_>>();
                    let prepared =
                        prepare_q_prime_evaluation(&point_sets, &actual.division_remainders, point)
                            .unwrap();
                    let derived = finish_q_prime_evaluation(prepared, &q_evaluations, challenge);
                    assert_eq!(derived, eval_polynomial(&actual.polynomial, point));
                }

                let collision = point_sets[0][0];
                assert!(
                    prepare_q_prime_evaluation(
                        &point_sets,
                        &actual.division_remainders,
                        collision,
                    )
                    .is_none()
                );
            };

            #[cfg(feature = "multicore")]
            for thread_count in [1, 4] {
                maybe_rayon::ThreadPoolBuilder::new()
                    .num_threads(thread_count)
                    .build()
                    .unwrap()
                    .install(|| check());
            }
            #[cfg(not(feature = "multicore"))]
            check();
        }
    }

    fn parallel_evaluations_match_serial_order<F>()
    where
        F: Field + From<u64> + Debug,
    {
        let empty = Vec::<Polynomial<F, Coeff>>::new();
        let empty_powers = Vec::<F>::new();
        let (empty_evaluations, side_output) =
            evaluate_polynomials_with_side_work(&empty, &empty_powers, || 17);
        assert!(empty_evaluations.is_empty());
        assert_eq!(side_output, 17);

        let polynomial_len = MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD * 2 + 1;
        let polynomials = (0..5)
            .map(|polynomial_index| Polynomial {
                values: (0..polynomial_len)
                    .map(|coefficient_index| {
                        F::from(
                            1 + polynomial_index as u64 * polynomial_len as u64
                                + coefficient_index as u64,
                        )
                    })
                    .collect(),
                _marker: PhantomData,
            })
            .collect::<Vec<_>>();

        for point in [F::ZERO, F::ONE, -F::ONE, F::from(17)] {
            let powers = power_vector(point, polynomial_len);
            let expected = polynomials
                .iter()
                .map(|polynomial| eval_polynomial(polynomial, point))
                .collect::<Vec<_>>();
            let check = || {
                let (actual, side_output) =
                    evaluate_polynomials_with_side_work(&polynomials, &powers, || 19);
                assert_eq!(actual, expected);
                assert_eq!(side_output, 19);
            };

            #[cfg(feature = "multicore")]
            for thread_count in [1, 3, 4, 5, 10] {
                maybe_rayon::ThreadPoolBuilder::new()
                    .num_threads(thread_count)
                    .build()
                    .unwrap()
                    .install(check);
            }
            #[cfg(not(feature = "multicore"))]
            check();
        }
    }

    fn scale_and_add_matches_operators<F>()
    where
        F: Field + From<u64> + Debug,
    {
        let len = MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD * 2 + 1;
        let polynomial = Polynomial {
            values: (0..len).map(|index| F::from(index as u64 + 1)).collect(),
            _marker: PhantomData,
        };
        let addend = Polynomial {
            values: (0..len)
                .map(|index| F::from(index as u64 * 3 + 2))
                .collect(),
            _marker: PhantomData,
        };

        for scale in [F::ZERO, F::ONE, -F::ONE, F::from(17)] {
            let expected = polynomial.clone() * scale + &addend;
            let check = || {
                let actual = scale_and_add_polynomial(polynomial.clone(), scale, &addend);
                assert_eq!(&expected[..], &actual[..]);
            };

            #[cfg(feature = "multicore")]
            for thread_count in [1, 4, 10] {
                maybe_rayon::ThreadPoolBuilder::new()
                    .num_threads(thread_count)
                    .build()
                    .unwrap()
                    .install(check);
            }
            #[cfg(not(feature = "multicore"))]
            check();
        }
    }

    #[test]
    fn streaming_collapse_matches_operator_collapse_fp() {
        streaming_collapse_matches_operator_collapse::<Fp>();
    }

    #[test]
    fn streaming_collapse_matches_operator_collapse_fq() {
        streaming_collapse_matches_operator_collapse::<Fq>();
    }

    #[test]
    fn short_trailing_polynomial_matches_zero_padding_fp() {
        short_trailing_polynomial_matches_zero_padding::<Fp>();
    }

    #[test]
    fn short_trailing_polynomial_matches_zero_padding_fq() {
        short_trailing_polynomial_matches_zero_padding::<Fq>();
    }

    #[test]
    fn zero_challenge_selects_last_polynomial_fp() {
        zero_challenge_selects_last_polynomial::<Fp>();
    }

    #[test]
    fn zero_challenge_selects_last_polynomial_fq() {
        zero_challenge_selects_last_polynomial::<Fq>();
    }

    #[test]
    fn in_place_kate_division_matches_allocating_fp() {
        in_place_kate_division_matches_allocating::<Fp>();
    }

    #[test]
    fn in_place_kate_division_matches_allocating_fq() {
        in_place_kate_division_matches_allocating::<Fq>();
    }

    #[test]
    fn parallel_q_prime_matches_ordered_operator_fold_fp() {
        parallel_q_prime_matches_ordered_operator_fold::<Fp>();
    }

    #[test]
    fn parallel_q_prime_matches_ordered_operator_fold_fq() {
        parallel_q_prime_matches_ordered_operator_fold::<Fq>();
    }

    #[test]
    fn parallel_evaluations_match_serial_order_fp() {
        parallel_evaluations_match_serial_order::<Fp>();
    }

    #[test]
    fn parallel_evaluations_match_serial_order_fq() {
        parallel_evaluations_match_serial_order::<Fq>();
    }

    #[test]
    fn scale_and_add_matches_operators_fp() {
        scale_and_add_matches_operators::<Fp>();
    }

    #[test]
    fn scale_and_add_matches_operators_fq() {
        scale_and_add_matches_operators::<Fq>();
    }
}
