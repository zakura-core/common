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
use std::collections::HashMap;
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
// Two 32-term Comba blocks cover the largest four-action Orchard group with
// one reduction.
#[cfg(any(test, all(feature = "multicore", target_arch = "aarch64")))]
const AARCH64_INNER_PRODUCT_GATHER_SIZE: usize = 64;

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

#[cfg(any(test, all(feature = "multicore", target_arch = "aarch64")))]
fn fold_polynomial_range_blocked_inner_product<F: DeferredField>(
    values: &mut [F],
    start: usize,
    polynomials: &[&Polynomial<F, Coeff>],
    descending_powers: &[F; AARCH64_INNER_PRODUCT_GATHER_SIZE],
) {
    for block in polynomials.chunks(AARCH64_INNER_PRODUCT_GATHER_SIZE) {
        let block_len = block.len();
        let (last, products) = block.split_last().expect("a polynomial block is nonempty");
        // A block continues Horner as
        //
        // A x^k + P_0 x^(k-1) + ... + P_(k-2) x + P_(k-1).
        //
        // Keeping the final addend outside the inner product makes the
        // result the accumulator for the next consecutive block.
        let weights = &descending_powers[AARCH64_INNER_PRODUCT_GATHER_SIZE - block_len..];
        let mut terms = [F::ZERO; AARCH64_INNER_PRODUCT_GATHER_SIZE];
        for (offset, value) in values.iter_mut().enumerate() {
            let coefficient_index = start + offset;
            terms[0] = *value;
            for (term, polynomial) in terms[1..block_len].iter_mut().zip(products) {
                *term = polynomial
                    .values
                    .get(coefficient_index)
                    .copied()
                    .unwrap_or(F::ZERO);
            }
            *value = F::inner_product(&terms[..block_len], weights);
            if let Some(coefficient) = last.values.get(coefficient_index) {
                *value += coefficient;
            }
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

#[cfg(any(test, all(feature = "multicore", target_arch = "aarch64")))]
fn collapse_polynomials_blocked_inner_product<F: DeferredField>(
    groups: &[Vec<&Polynomial<F, Coeff>>],
    challenge: F,
) -> Vec<Polynomial<F, Coeff>> {
    let max_block_len = groups
        .iter()
        .map(|group| group.len().saturating_sub(1))
        .max()
        .unwrap_or(0)
        .min(AARCH64_INNER_PRODUCT_GATHER_SIZE);
    if max_block_len <= DEFERRED_FOLD_LANES {
        return collapse_polynomials_horner(groups, challenge);
    }

    let mut descending_powers = [F::ZERO; AARCH64_INNER_PRODUCT_GATHER_SIZE];
    let mut power = F::ONE;
    for weight in descending_powers[AARCH64_INNER_PRODUCT_GATHER_SIZE - max_block_len..]
        .iter_mut()
        .rev()
    {
        power *= challenge;
        *weight = power;
    }
    collapse_polynomials_with(groups, |values, start, group| {
        // The first polynomial was cloned into `values`; fold exactly the
        // following terms so block boundaries preserve Horner's recurrence.
        let following = &group[1..];
        if following.len() <= DEFERRED_FOLD_LANES {
            // Gathering one or two terms costs more than their direct Horner
            // steps.
            fold_polynomial_range(values, start, following, challenge);
        } else {
            fold_polynomial_range_blocked_inner_product(
                values,
                start,
                following,
                &descending_powers,
            );
        }
    })
}

fn collapse_polynomials_deferred<F: DeferredField>(
    groups: &[Vec<&Polynomial<F, Coeff>>],
    challenge: F,
) -> Vec<Polynomial<F, Coeff>> {
    let thread_count = multicore::current_num_threads();
    #[cfg(all(feature = "multicore", target_arch = "aarch64"))]
    if thread_count > 1 {
        return collapse_polynomials_blocked_inner_product(groups, challenge);
    }
    if thread_count > 1 {
        return collapse_polynomials_horner(groups, challenge);
    }

    let max_group_len = groups.iter().map(Vec::len).max().unwrap_or(0);
    let powers = power_vector(challenge, max_group_len);

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

fn vanishing_polynomial<F: Field>(points: &[F]) -> Vec<F> {
    let Some((first, remaining)) = points.split_first() else {
        return vec![F::ONE];
    };
    let mut coefficients = Vec::with_capacity(points.len() + 1);
    coefficients.extend([-*first, F::ONE]);

    for point in remaining {
        let degree = coefficients.len() - 1;
        coefficients.push(F::ONE);
        // The previous leading coefficient is one, so avoid multiplying it.
        coefficients[degree] = coefficients[degree - 1] - point;
        for coefficient_index in (1..degree).rev() {
            coefficients[coefficient_index] =
                coefficients[coefficient_index - 1] - coefficients[coefficient_index] * point;
        }
        coefficients[0] *= -*point;
    }

    coefficients
}

// For a monic degree-d divisor, each quotient coefficient depends only on the
// corresponding input coefficient and the next d quotient coefficients. The
// degree-two and degree-three cases are the production shapes, so keep those
// higher coefficients in registers instead of revisiting the output vector.
fn divide_by_monic_quadratic<F: Field>(polynomial: &[F], divisor: &[F], quotient: &mut [F]) {
    debug_assert_eq!(divisor.len(), 3);
    let mut higher_1 = F::ZERO;
    let mut higher_2 = F::ZERO;
    for quotient_index in (0..quotient.len()).rev() {
        let mut coefficient = polynomial[quotient_index + 2];
        coefficient -= divisor[1] * higher_1;
        coefficient -= divisor[0] * higher_2;
        quotient[quotient_index] = coefficient;
        higher_2 = higher_1;
        higher_1 = coefficient;
    }
}

fn divide_by_monic_cubic<F: Field>(polynomial: &[F], divisor: &[F], quotient: &mut [F]) {
    debug_assert_eq!(divisor.len(), 4);
    let mut higher_1 = F::ZERO;
    let mut higher_2 = F::ZERO;
    let mut higher_3 = F::ZERO;
    for quotient_index in (0..quotient.len()).rev() {
        let mut coefficient = polynomial[quotient_index + 3];
        coefficient -= divisor[2] * higher_1;
        coefficient -= divisor[1] * higher_2;
        coefficient -= divisor[0] * higher_3;
        quotient[quotient_index] = coefficient;
        higher_3 = higher_2;
        higher_2 = higher_1;
        higher_1 = coefficient;
    }
}

fn divide_by_monic<F: Field>(polynomial: &[F], divisor: &[F], quotient: &mut [F]) {
    let degree = divisor.len() - 1;
    for quotient_index in (0..quotient.len()).rev() {
        let higher_count = degree.min(quotient.len() - 1 - quotient_index);
        let mut coefficient = polynomial[quotient_index + degree];
        for higher_offset in 1..=higher_count {
            coefficient -=
                divisor[degree - higher_offset] * quotient[quotient_index + higher_offset];
        }
        quotient[quotient_index] = coefficient;
    }
}

fn divide_by_vanishing_polynomial<F: Field>(polynomial: &[F], points: &[F]) -> (Vec<F>, Vec<F>) {
    let degree = points.len();
    assert!(
        degree <= polynomial.len(),
        "a polynomial divided by a linear factor is nonempty",
    );
    if degree == 0 {
        return (polynomial.to_vec(), Vec::new());
    }
    if let [point] = points {
        let mut quotient = polynomial.to_vec();
        let remainder = kate_division_in_place(&mut quotient, *point);
        return (quotient, vec![remainder]);
    }

    let divisor = vanishing_polynomial(points);
    let quotient_len = polynomial.len() - degree;
    let mut quotient = Vec::with_capacity(polynomial.len());
    quotient.resize(quotient_len, F::ZERO);
    match degree {
        2 => divide_by_monic_quadratic(polynomial, &divisor, &mut quotient),
        3 => divide_by_monic_cubic(polynomial, &divisor, &mut quotient),
        _ => divide_by_monic(polynomial, &divisor, &mut quotient),
    }

    // Recover the low-degree remainder from the preserved input coefficients.
    let remainder = (0..degree)
        .map(|coefficient_index| {
            let mut coefficient = polynomial[coefficient_index];
            // These indices intentionally move in opposite directions.
            #[allow(clippy::needless_range_loop)]
            for divisor_index in 0..=coefficient_index {
                if let Some(quotient) = quotient.get(coefficient_index - divisor_index) {
                    coefficient -= divisor[divisor_index] * quotient;
                }
            }
            coefficient
        })
        .collect();
    (quotient, remainder)
}

fn prepare_q_prime_term<F: Field>(
    polynomial: &Polynomial<F, Coeff>,
    points: &[F],
    domain_len: usize,
) -> (Polynomial<F, Coeff>, Vec<F>) {
    let (mut values, remainder) = divide_by_vanishing_polynomial(&polynomial.values, points);
    values.resize(domain_len, F::ZERO);
    (
        Polynomial {
            values,
            _marker: PhantomData,
        },
        remainder,
    )
}

struct PreparedQPrime<F> {
    polynomial: Polynomial<F, Coeff>,
    monomial_remainders: Vec<Vec<F>>,
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
    monomial_remainders: &[Vec<F>],
    point: F,
) -> Option<PreparedQPrimeEvaluation<F>> {
    assert_eq!(point_sets.len(), monomial_remainders.len());

    // Direct division gives
    //
    // Q_i(X) = R_i(X) + Z_i(X) T_i(X),
    //
    // with the coefficients of each small R_i stored in monomial order.
    // Evaluate R_i and Z_i, then batch the inversions of the Z_i evaluations.
    let mut terms = point_sets
        .iter()
        .zip(monomial_remainders)
        .map(|(points, remainders)| {
            assert_eq!(points.len(), remainders.len());
            let (last_remainder, earlier_remainders) = remainders
                .split_last()
                .expect("a point set contains at least one point");
            let remainder = earlier_remainders
                .iter()
                .rev()
                .fold(*last_remainder, |evaluation, remainder| {
                    *remainder + point * evaluation
                });
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
        let mut monomial_remainders = Vec::with_capacity(point_sets.len());
        for (points, polynomial) in point_sets.iter().zip(polynomials) {
            let (term, remainders) = prepare_q_prime_term(polynomial, points, domain_len);
            monomial_remainders.push(remainders);
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
            monomial_remainders,
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
    let (terms, monomial_remainders): (Vec<_>, Vec<_>) = terms
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
            monomial_remainders,
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
        monomial_remainders,
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

fn fold_polynomials<F: Field>(
    mut accumulator: Polynomial<F, Coeff>,
    challenge: F,
    polynomials: &[Polynomial<F, Coeff>],
) -> Polynomial<F, Coeff> {
    for polynomial in polynomials {
        debug_assert_eq!(accumulator.len(), polynomial.len());
    }
    if polynomials.is_empty() {
        return accumulator;
    }

    let fold_coefficients = |values: &mut [F], start: usize| {
        let end = start + values.len();
        for polynomial in polynomials {
            for (value, addend) in values.iter_mut().zip(&polynomial.values[start..end]) {
                *value *= challenge;
                *value += addend;
            }
        }
    };

    if multicore::current_num_threads() == 1 {
        fold_coefficients(&mut accumulator.values, 0);
    } else {
        crate::arithmetic::parallelize(&mut accumulator.values, fold_coefficients);
    }
    accumulator
}

const PROVER_POINT_MASK_BITS: usize = usize::BITS as usize;

struct ProverIntermediateSets<'a, C: CurveAffine> {
    commitments: Vec<(PolynomialPointer<'a, C>, usize)>,
    point_sets: Vec<Vec<C::Scalar>>,
}

enum ProverIntermediateSetsResult<'a, C: CurveAffine> {
    Complete(Option<ProverIntermediateSets<'a, C>>),
    TooManyPoints,
}

// The prover normally opens at a handful of challenge rotations. Represent
// each commitment's point set inline, avoiding several tiny vectors and tree
// nodes per commitment. Unusual callers with more points retain the generic
// construction below.
fn construct_prover_intermediate_sets<'a, C, I>(queries: I) -> ProverIntermediateSetsResult<'a, C>
where
    C: CurveAffine,
    I: IntoIterator<Item = ProverQuery<'a, C>> + Clone,
{
    let query_capacity = queries.clone().into_iter().size_hint().0;
    let mut points = Vec::with_capacity(query_capacity.min(PROVER_POINT_MASK_BITS));
    let mut commitments = Vec::with_capacity(query_capacity);
    let mut commitment_indices = HashMap::with_capacity(query_capacity);

    for query in queries {
        let point_index = if let Some(point_index) = points
            .iter()
            .position(|candidate| *candidate == query.point)
        {
            point_index
        } else {
            if points.len() == PROVER_POINT_MASK_BITS {
                return ProverIntermediateSetsResult::TooManyPoints;
            }
            points.push(query.point);
            points.len() - 1
        };

        let commitment = query.get_commitment();
        let commitment_index = *commitment_indices.entry(commitment).or_insert_with(|| {
            commitments.push((commitment, 0_usize));
            commitments.len() - 1
        });
        let point_mask = 1_usize << point_index;
        if commitments[commitment_index].1 & point_mask != 0 {
            return ProverIntermediateSetsResult::Complete(None);
        }
        commitments[commitment_index].1 |= point_mask;
    }

    if commitments.is_empty() {
        return ProverIntermediateSetsResult::Complete(None);
    }

    let mut point_masks = Vec::new();
    for (_, point_mask) in &mut commitments {
        let set_index = point_masks
            .iter()
            .position(|candidate| candidate == point_mask)
            .unwrap_or_else(|| {
                point_masks.push(*point_mask);
                point_masks.len() - 1
            });
        *point_mask = set_index;
    }
    let point_sets = point_masks
        .into_iter()
        .map(|point_mask| {
            points
                .iter()
                .enumerate()
                .filter_map(|(point_index, point)| {
                    ((point_mask >> point_index) & 1 == 1).then_some(*point)
                })
                .collect()
        })
        .collect();

    ProverIntermediateSetsResult::Complete(Some(ProverIntermediateSets {
        commitments,
        point_sets,
    }))
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

    let intermediate_sets = match construct_prover_intermediate_sets(queries.clone()) {
        ProverIntermediateSetsResult::Complete(intermediate_sets) => intermediate_sets,
        ProverIntermediateSetsResult::TooManyPoints => {
            construct_intermediate_sets(queries).map(|(commitments, point_sets)| {
                let commitments = commitments
                    .into_iter()
                    .map(|data| (data.commitment, data.set_index))
                    .collect();
                ProverIntermediateSets {
                    commitments,
                    point_sets,
                }
            })
        }
    };
    let ProverIntermediateSets {
        commitments: poly_map,
        point_sets,
    } = intermediate_sets.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "queries iterator is empty or contains duplicate queries",
        )
    })?;

    // Collapse openings at same point sets together into single openings using
    // x_1 challenge.
    let mut polynomial_groups = vec![vec![]; point_sets.len()];
    let mut q_blinds = vec![Blind(C::Scalar::ZERO); point_sets.len()];
    for (commitment, set_index) in poly_map {
        polynomial_groups[set_index].push(commitment.poly);
        q_blinds[set_index] *= *x_1;
        q_blinds[set_index] += commitment.blind;
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
        monomial_remainders,
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
            prepare_q_prime_evaluation(&point_sets, &monomial_remainders, *x_3)
        });
    for evaluation in &q_evaluations {
        transcript.write_scalar(*evaluation)?;
    }

    // The direct divisions used to build q' left one small monomial-basis
    // remainder per point set. Evaluate those at x_3 to derive q'(x_3) from
    // the Q_i(x_3) values already required by the transcript. The verifier
    // rejects a collision between x_3 and a queried point; retain the old
    // evaluation path for that negligible event so proof creation remains
    // infallible.
    let q_prime_evaluation = prepared_q_prime_evaluation
        .map(|prepared| finish_q_prime_evaluation(prepared, &q_evaluations, *x_2))
        .unwrap_or_else(|| evaluate_polynomial_with_powers(&q_prime_poly, &powers));

    let x_4: ChallengeX4<_> = transcript.squeeze_challenge_scalar();

    let p_evaluation = q_evaluations
        .iter()
        .fold(q_prime_evaluation, |evaluation, q_evaluation| {
            evaluation * *x_4 + q_evaluation
        });

    debug_assert_eq!(q_polys.len(), q_blinds.len());
    let p_poly = fold_polynomials(q_prime_poly, *x_4, &q_polys);
    let p_poly_blind = q_blinds
        .into_iter()
        .fold(q_prime_blind, |accumulator, blind| {
            Blind((accumulator.0 * &(*x_4)) + &blind.0)
        });

    commitment::create_proof_with_powers(
        params,
        rng,
        transcript,
        p_poly,
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
        Blind, Coeff, MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD, Polynomial,
        ProverIntermediateSetsResult, ProverQuery, collapse_polynomials,
        collapse_polynomials_blocked_inner_product, collapse_polynomials_horner,
        construct_intermediate_sets, construct_prover_intermediate_sets,
        divide_by_vanishing_polynomial, evaluate_polynomials_with_side_work,
        finish_q_prime_evaluation, fold_polynomials, kate_division_in_place, power_vector,
        prepare_q_prime, prepare_q_prime_evaluation, vanishing_polynomial,
    };
    use crate::arithmetic::{eval_polynomial, kate_division};
    use ff::Field;
    use pasta_curves::{EqAffine, Fp, Fq};
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

    fn assert_collapsed_eq<F: Field + Debug>(
        actual: &[Polynomial<F, Coeff>],
        expected: &[Polynomial<F, Coeff>],
    ) {
        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.iter().zip(expected) {
            assert_eq!(&actual[..], &expected[..]);
        }
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

    fn blocked_inner_product_boundaries_match_horner<F>()
    where
        F: pasta_curves::deferred::DeferredField + From<u64> + Debug,
    {
        const POLYNOMIAL_LEN: usize = 257;
        const FOLLOWING_LENGTHS: [usize; 5] = [2, 3, 63, 64, 65];

        let groups = FOLLOWING_LENGTHS
            .iter()
            .enumerate()
            .map(|(group_index, following_len)| {
                let group_len = following_len + 1;
                (0..group_len)
                    .map(|polynomial_index| {
                        let len = if group_index + 1 == FOLLOWING_LENGTHS.len()
                            && polynomial_index + 1 == group_len
                        {
                            2
                        } else {
                            POLYNOMIAL_LEN
                        };
                        Polynomial {
                            values: (0..len)
                                .map(|coefficient_index| {
                                    F::from(
                                        1 + (group_index * 1_000_000
                                            + polynomial_index * POLYNOMIAL_LEN
                                            + coefficient_index)
                                            as u64,
                                    )
                                })
                                .collect(),
                            _marker: PhantomData,
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let group_refs = groups
            .iter()
            .map(|group| group.iter().collect::<Vec<_>>())
            .collect::<Vec<_>>();

        for challenge in [F::ZERO, F::ONE, -F::ONE, F::from(17)] {
            let expected = collapse_polynomials_horner(&group_refs, challenge);
            let small_expected = collapse_polynomials_horner(&group_refs[..1], challenge);
            let check = || {
                let actual = collapse_polynomials_blocked_inner_product(&group_refs, challenge);
                assert_collapsed_eq(&actual, &expected);
                let small_actual =
                    collapse_polynomials_blocked_inner_product(&group_refs[..1], challenge);
                assert_collapsed_eq(&small_actual, &small_expected);
            };

            #[cfg(feature = "multicore")]
            for thread_count in [1, 4, 10] {
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

    fn direct_vanishing_division_matches_successive_division<F>()
    where
        F: Field + From<u64> + Debug,
    {
        for coefficients in [Vec::new(), vec![F::from(7), F::from(11)]] {
            let (quotient, remainder) = divide_by_vanishing_polynomial(&coefficients, &[]);
            assert_eq!(quotient, coefficients);
            assert!(remainder.is_empty());
        }

        let point_sets = [
            vec![F::from(2)],
            vec![F::from(3), F::from(5)],
            vec![F::ZERO, -F::ONE, F::from(11)],
            vec![F::from(7), F::from(13), F::from(17), F::from(19)],
        ];

        for points in point_sets {
            let vanishing = vanishing_polynomial(&points);
            assert_eq!(vanishing.len(), points.len() + 1);
            assert_eq!(vanishing.last(), Some(&F::ONE));

            for polynomial_len in [
                points.len(),
                points.len() + 1,
                points.len() + 2,
                points.len() + 3,
                17,
            ] {
                let coefficients = (0..polynomial_len)
                    .map(|index| {
                        if index % 5 == 0 {
                            F::ZERO
                        } else {
                            F::from((index * index + 3 * index + 7) as u64)
                        }
                    })
                    .collect::<Vec<_>>();
                let mut expected = coefficients.clone();
                for point in &points {
                    expected = kate_division(&expected, *point);
                }

                let (actual, remainder) = divide_by_vanishing_polynomial(&coefficients, &points);
                assert_eq!(actual, expected);
                assert_eq!(remainder.len(), points.len());

                for evaluation_point in [F::ZERO, F::ONE, -F::ONE, F::from(23), F::from(29)] {
                    let expected_vanishing = points
                        .iter()
                        .fold(F::ONE, |value, point| value * (evaluation_point - point));
                    assert_eq!(
                        eval_polynomial(&vanishing, evaluation_point),
                        expected_vanishing,
                    );
                    assert_eq!(
                        eval_polynomial(&remainder, evaluation_point),
                        eval_polynomial(&coefficients, evaluation_point)
                            - expected_vanishing * eval_polynomial(&actual, evaluation_point),
                    );
                }
            }
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
        // This is the exact point-set and polynomial-length shape of the
        // Orchard k = 11 prover, and crosses both parallel-work thresholds
        // with four workers.
        let domain_len = 1 << 11;
        let point_sets = vec![
            vec![F::from(2)],
            vec![F::from(3), F::from(5)],
            vec![F::ZERO, -F::ONE, F::from(11)],
            vec![F::from(7), F::from(13), F::from(17)],
            vec![F::from(19), F::from(23)],
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

                for point in [F::from(29), F::from(31)] {
                    let q_evaluations = polynomials
                        .iter()
                        .map(|polynomial| eval_polynomial(polynomial, point))
                        .collect::<Vec<_>>();
                    let prepared =
                        prepare_q_prime_evaluation(&point_sets, &actual.monomial_remainders, point)
                            .unwrap();
                    let derived = finish_q_prime_evaluation(prepared, &q_evaluations, challenge);
                    assert_eq!(derived, eval_polynomial(&actual.polynomial, point));
                }

                let collision = point_sets[0][0];
                assert!(
                    prepare_q_prime_evaluation(
                        &point_sets,
                        &actual.monomial_remainders,
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
                    .install(check);
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

    fn chunk_major_fold_matches_operator_fold<F>()
    where
        F: Field + From<u64> + Debug,
    {
        let len = MIN_PARALLEL_FIELD_OPERATIONS_PER_THREAD * 2 + 1;
        let accumulator = Polynomial {
            values: (0..len).map(|index| F::from(index as u64 + 1)).collect(),
            _marker: PhantomData,
        };
        let polynomials = (0..5)
            .map(|polynomial_index| Polynomial {
                values: (0..len)
                    .map(|index| {
                        F::from(polynomial_index as u64 * len as u64 + index as u64 * 3 + 2)
                    })
                    .collect(),
                _marker: PhantomData,
            })
            .collect::<Vec<_>>();

        for polynomial_count in [0, 1, polynomials.len()] {
            for challenge in [F::ZERO, F::ONE, -F::ONE, F::from(17)] {
                let expected = polynomials[..polynomial_count]
                    .iter()
                    .fold(accumulator.clone(), |accumulator, polynomial| {
                        accumulator * challenge + polynomial
                    });
                let check = || {
                    let actual = fold_polynomials(
                        accumulator.clone(),
                        challenge,
                        &polynomials[..polynomial_count],
                    );
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
    }

    #[test]
    fn prover_point_masks_match_generic_intermediate_sets() {
        let polynomials = (0..4)
            .map(|polynomial_index| {
                Polynomial::from_coefficients(vec![Fp::from(polynomial_index + 1)])
            })
            .collect::<Vec<_>>();
        let points = [Fp::from(5), Fp::from(7), Fp::from(11)];
        let blind = Blind(Fp::from(13));
        let queries = vec![
            ProverQuery::<EqAffine> {
                point: points[2],
                poly: &polynomials[0],
                blind,
            },
            ProverQuery {
                point: points[0],
                poly: &polynomials[0],
                blind,
            },
            ProverQuery {
                point: points[0],
                poly: &polynomials[1],
                blind,
            },
            ProverQuery {
                point: points[2],
                poly: &polynomials[1],
                blind,
            },
            ProverQuery {
                point: points[1],
                poly: &polynomials[2],
                blind,
            },
            ProverQuery {
                point: points[1],
                poly: &polynomials[3],
                blind,
            },
            ProverQuery {
                point: points[2],
                poly: &polynomials[3],
                blind,
            },
        ];

        let (expected_commitments, expected_point_sets) =
            construct_intermediate_sets(queries.clone()).unwrap();
        let (actual_commitments, actual_point_sets) =
            match construct_prover_intermediate_sets(queries) {
                ProverIntermediateSetsResult::Complete(Some(intermediate_sets)) => {
                    (intermediate_sets.commitments, intermediate_sets.point_sets)
                }
                _ => panic!("the supported query set is valid"),
            };

        assert_eq!(actual_point_sets, expected_point_sets);
        assert_eq!(actual_commitments.len(), expected_commitments.len());
        for ((actual_commitment, actual_set_index), expected) in
            actual_commitments.iter().zip(expected_commitments)
        {
            assert!(*actual_commitment == expected.commitment);
            assert_eq!(*actual_set_index, expected.set_index);
        }
    }

    #[test]
    fn prover_point_masks_reject_duplicates() {
        let polynomial = Polynomial::from_coefficients(vec![Fp::ONE]);
        let query = ProverQuery::<EqAffine> {
            point: Fp::from(5),
            poly: &polynomial,
            blind: Blind(Fp::ZERO),
        };

        assert!(matches!(
            construct_prover_intermediate_sets([query.clone(), query]),
            ProverIntermediateSetsResult::Complete(None),
        ));
    }

    #[test]
    fn prover_point_masks_fall_back_above_mask_width() {
        let polynomial = Polynomial::from_coefficients(vec![Fp::ONE]);
        let queries = (0..=super::PROVER_POINT_MASK_BITS)
            .map(|index| ProverQuery::<EqAffine> {
                point: Fp::from(index as u64 + 1),
                poly: &polynomial,
                blind: Blind(Fp::ZERO),
            })
            .collect::<Vec<_>>();

        assert!(construct_intermediate_sets(queries.clone()).is_some());
        assert!(matches!(
            construct_prover_intermediate_sets(queries),
            ProverIntermediateSetsResult::TooManyPoints,
        ));
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
    fn blocked_inner_product_boundaries_match_horner_fp() {
        blocked_inner_product_boundaries_match_horner::<Fp>();
    }

    #[test]
    fn blocked_inner_product_boundaries_match_horner_fq() {
        blocked_inner_product_boundaries_match_horner::<Fq>();
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
    fn direct_vanishing_division_matches_successive_division_fp() {
        direct_vanishing_division_matches_successive_division::<Fp>();
    }

    #[test]
    fn direct_vanishing_division_matches_successive_division_fq() {
        direct_vanishing_division_matches_successive_division::<Fq>();
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
    fn chunk_major_fold_matches_operator_fold_fp() {
        chunk_major_fold_matches_operator_fold::<Fp>();
    }

    #[test]
    fn chunk_major_fold_matches_operator_fold_fq() {
        chunk_major_fold_matches_operator_fold::<Fq>();
    }
}
