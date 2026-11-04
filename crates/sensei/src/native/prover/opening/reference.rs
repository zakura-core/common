//! Test-only dynamic opening grouping and coefficient-fold references.
//!
//! The query plan and grouping reconstruct first-appearance order from actual
//! field points independently of the compile-time protocol schedule. Target
//! query facts and rotation arithmetic remain shared. Reference folds retain
//! their existing algorithms, including the parallel Horner comparison helper.

use alloc::{sync::Arc, vec::Vec};
use core::ops::Range;

use crate::Error;
use crate::native::evaluation::{rotated_evaluation_point, rotated_query_point};
use crate::native::field::Fp;
use crate::native::target::{
    ADVICE_COLUMNS, BLINDING_FACTORS, FixedTarget, N, PERMUTATION_CHUNK_LEN,
};
use crate::native::{buffer::Buffer, worker::Execution};
use udon::exec::for_each_chunk_mut;
use udon::polynomial::fold_weighted;

use super::{COEFFICIENT_CHUNK, OpeningSource, PolySource, opening_stage};

/// A polynomial of the dynamic opening construction, the `cfg(test)` oracle
/// for the compile-time schedule in [`crate::native::protocol::opening`].
#[cfg(test)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::native::prover) enum OpeningPolynomial {
    Instance(usize),
    Advice(usize, usize),
    Permutation(usize, usize),
    LookupProduct(usize, usize),
    LookupInput(usize, usize),
    LookupTable(usize, usize),
    Fixed(usize),
    Sigma(usize),
    Quotient,
    Vanishing,
}

#[cfg(test)]
pub(in crate::native::prover) struct OpeningPlanQuery {
    pub(in crate::native::prover) polynomial: OpeningPolynomial,
    pub(in crate::native::prover) point: Fp,
}

#[cfg(test)]
pub(in crate::native::prover) struct OpeningQuery<'a> {
    pub(in crate::native::prover) polynomial: OpeningPolynomial,
    pub(in crate::native::prover) source: OpeningSource<'a>,
    pub(in crate::native::prover) blind: Fp,
    pub(in crate::native::prover) point: Fp,
}

#[cfg(test)]
pub(in crate::native::prover) struct OpeningCommitment<'a> {
    pub(in crate::native::prover) polynomial: OpeningPolynomial,
    pub(in crate::native::prover) source: OpeningSource<'a>,
    pub(in crate::native::prover) blind: Fp,
    pub(in crate::native::prover) point_indices: Vec<usize>,
}

/// Returns the fixed, circuit-major opening schedule in transcript order.
///
/// The first occurrence of each polynomial and each point set is significant:
/// `group_opening_queries` derives both Horner orderings from this schedule.
/// Together they are the dynamic construction the compile-time
/// [`crate::native::protocol::opening`] is validated against.
#[cfg(test)]
pub(in crate::native::prover) fn opening_query_plan(
    target: &FixedTarget,
    action_count: usize,
    x: &Fp,
) -> Result<Vec<OpeningPlanQuery>, Error> {
    let permutation_set_count = target
        .permutation_columns()
        .len()
        .div_ceil(PERMUTATION_CHUNK_LEN);
    let x_next = rotated_evaluation_point(x, target.domain().omega(), 1);
    let x_previous = rotated_evaluation_point(x, target.domain().omega_inverse(), 1);
    let x_last = rotated_evaluation_point(x, target.domain().omega_inverse(), BLINDING_FACTORS + 1);
    let mut queries = Vec::with_capacity(opening_stage::evaluations(action_count) + 1);

    for action_index in 0..action_count {
        for query in target.queries().instance() {
            if query.column != 0 {
                return Err(Error::InternalInvariant);
            }
            queries.push(OpeningPlanQuery {
                polynomial: OpeningPolynomial::Instance(action_index),
                point: rotated_query_point(target, x, query.rotation),
            });
        }
        for query in target.queries().advice() {
            if query.column >= ADVICE_COLUMNS {
                return Err(Error::InternalInvariant);
            }
            queries.push(OpeningPlanQuery {
                polynomial: OpeningPolynomial::Advice(action_index, query.column),
                point: rotated_query_point(target, x, query.rotation),
            });
        }
        for set_index in 0..permutation_set_count {
            for point in [*x, x_next] {
                queries.push(OpeningPlanQuery {
                    polynomial: OpeningPolynomial::Permutation(action_index, set_index),
                    point,
                });
            }
        }
        for set_index in (0..permutation_set_count).rev().skip(1) {
            queries.push(OpeningPlanQuery {
                polynomial: OpeningPolynomial::Permutation(action_index, set_index),
                point: x_last,
            });
        }
        for lookup_index in 0..target.lookups().len() {
            for (polynomial, point) in [
                (
                    OpeningPolynomial::LookupProduct(action_index, lookup_index),
                    *x,
                ),
                (
                    OpeningPolynomial::LookupInput(action_index, lookup_index),
                    *x,
                ),
                (
                    OpeningPolynomial::LookupTable(action_index, lookup_index),
                    *x,
                ),
                (
                    OpeningPolynomial::LookupInput(action_index, lookup_index),
                    x_previous,
                ),
                (
                    OpeningPolynomial::LookupProduct(action_index, lookup_index),
                    x_next,
                ),
            ] {
                queries.push(OpeningPlanQuery { polynomial, point });
            }
        }
    }
    for query in target.queries().fixed() {
        queries.push(OpeningPlanQuery {
            polynomial: OpeningPolynomial::Fixed(query.column),
            point: rotated_query_point(target, x, query.rotation),
        });
    }
    for sigma_index in 0..target.sigma_polynomials().coefficients().len() {
        queries.push(OpeningPlanQuery {
            polynomial: OpeningPolynomial::Sigma(sigma_index),
            point: *x,
        });
    }
    queries.push(OpeningPlanQuery {
        polynomial: OpeningPolynomial::Quotient,
        point: *x,
    });
    queries.push(OpeningPlanQuery {
        polynomial: OpeningPolynomial::Vanishing,
        point: *x,
    });
    Ok(queries)
}

pub(in crate::native::prover) struct GroupedOpenings<'a> {
    pub(in crate::native::prover) point_sets: Vec<Vec<Fp>>,
    pub(in crate::native::prover) commitments: Vec<OpeningCommitment<'a>>,
    pub(in crate::native::prover) polynomial_groups: Vec<Vec<usize>>,
}

/// Whether two sources name the same buffer (the same polynomial), not merely
/// equal values.
#[cfg(test)]
fn opening_sources_match(left: &OpeningSource, right: &OpeningSource) -> bool {
    match (left, right) {
        (
            OpeningSource::Instance {
                statements: left,
                index: a,
            },
            OpeningSource::Instance {
                statements: right,
                index: b,
            },
        ) => a == b && Arc::ptr_eq(left, right),
        (OpeningSource::Coefficients(left), OpeningSource::Coefficients(right)) => {
            let (left, right) = (left.as_slice(), right.as_slice());
            left.as_ptr() == right.as_ptr() && left.len() == right.len()
        }
        (OpeningSource::QuotientPieces(left), OpeningSource::QuotientPieces(right)) => {
            core::ptr::eq(*left, *right)
        }
        // The mask is one prover-owned pair, so equal values name the same
        // polynomial.
        (OpeningSource::Linear(left), OpeningSource::Linear(right)) => {
            left.map(|value| value.reduce()) == right.map(|value| value.reduce())
        }
        _ => false,
    }
}

#[cfg(test)]
pub(in crate::native::prover) fn group_opening_queries(
    queries: Vec<OpeningQuery>,
) -> Result<GroupedOpenings, Error> {
    let mut points = Vec::<Fp>::with_capacity(queries.len());
    let mut commitments = Vec::<OpeningCommitment>::with_capacity(queries.len());
    for query in queries {
        let point_index = if let Some(index) = points
            .iter()
            .position(|point| (point).reduce() == (query.point).reduce())
        {
            index
        } else {
            points.push(query.point);
            points.len() - 1
        };
        if let Some(commitment) = commitments
            .iter_mut()
            .find(|commitment| commitment.polynomial == query.polynomial)
        {
            if commitment.point_indices.contains(&point_index)
                || !opening_sources_match(&commitment.source, &query.source)
                || (commitment.blind).reduce() != (query.blind).reduce()
            {
                return Err(Error::InternalInvariant);
            }
            commitment.point_indices.reserve(1);
            commitment.point_indices.push(point_index);
        } else {
            commitments.push(OpeningCommitment {
                polynomial: query.polynomial,
                source: query.source,
                blind: query.blind,
                point_indices: alloc::vec![point_index],
            });
        }
    }
    if commitments.is_empty() {
        return Err(Error::InternalInvariant);
    }

    let mut point_index_sets = Vec::<Vec<usize>>::with_capacity(commitments.len());
    let mut polynomial_groups = Vec::<Vec<usize>>::with_capacity(commitments.len());
    for (commitment_index, commitment) in commitments.iter().enumerate() {
        let mut point_index_set = commitment.point_indices.clone();
        point_index_set.sort_unstable();
        let set_index = if let Some(index) = point_index_sets
            .iter()
            .position(|existing| existing == &point_index_set)
        {
            index
        } else {
            point_index_sets.push(point_index_set);
            polynomial_groups.push(Vec::new());
            point_index_sets.len() - 1
        };
        polynomial_groups[set_index].push(commitment_index);
    }
    let point_sets = point_index_sets
        .into_iter()
        .map(|indices| {
            indices
                .into_iter()
                .map(|index| points.get(index).cloned().ok_or(Error::InternalInvariant))
                .collect()
        })
        .collect::<Result<Vec<Vec<_>>, _>>()?;
    Ok(GroupedOpenings {
        point_sets,
        commitments,
        polynomial_groups,
    })
}

/// Sums already-weighted coefficient sources over one coefficient range,
/// paying one Montgomery reduction per output coefficient rather than one per
/// source.
#[cfg(test)]
pub(in crate::native::prover) fn deferred_weighted_polynomial_sum(
    sources: &[(PolySource, Fp)],
    range: Range<usize>,
) -> Result<Vec<Fp>, Error> {
    if sources.is_empty()
        || range.end > N
        || sources
            .iter()
            .any(|(coefficients, _)| coefficients.as_slice().len() != N)
    {
        return Err(Error::InternalInvariant);
    }
    let sources = sources
        .iter()
        .map(|(coefficients, weight)| (coefficients.as_slice(), weight))
        .collect::<Vec<_>>();
    Ok(range
        .map(|index| {
            <Fp>::sum_of_product_pairs(
                sources
                    .iter()
                    .map(|(coefficients, weight)| (&coefficients[index], *weight)),
            )
        })
        .collect())
}

#[cfg(test)]
pub(in crate::native::prover) fn fold_polynomial(
    accumulator: &mut [Fp],
    polynomial: &[Fp],
    challenge: &Fp,
) -> Result<(), Error> {
    if accumulator.len() != polynomial.len() {
        return Err(Error::InternalInvariant);
    }
    for (accumulator, coefficient) in accumulator.iter_mut().zip(polynomial) {
        *accumulator = accumulator.mul_add(challenge, coefficient);
    }
    Ok(())
}

/// Collapses same-length coefficient polynomials with Horner weights.
///
/// Reusing the weights across coefficient chunks makes each output coefficient
/// one product sum. The fixed input count keeps weights and chunk views on the
/// stack.
#[cfg(test)]
pub(in crate::native::prover) fn parallel_horner_polynomial_fold<
    P: AsRef<[Fp]> + Sync,
    const COUNT: usize,
>(
    execution: Execution<'_>,
    polynomials: [P; COUNT],
    challenge: &Fp,
) -> Result<Buffer<Fp>, Error> {
    if COUNT == 0
        || polynomials
            .iter()
            .any(|polynomial| polynomial.as_ref().len() != N)
    {
        return Err(Error::InternalInvariant);
    }
    let mut weights = [<Fp>::ONE; COUNT];
    if COUNT > 1 {
        weights[COUNT - 2] = *challenge;
        for index in (0..COUNT - 2).rev() {
            weights[index] = weights[index + 1].mul(challenge);
        }
    }
    let mut folded = execution.buffer(N, false);
    for_each_chunk_mut(
        &mut folded,
        COEFFICIENT_CHUNK,
        execution.budget,
        &execution,
        |chunk, values, _| {
            let start = chunk * COEFFICIENT_CHUNK;
            let end = start + values.len();
            let inputs = polynomials
                .each_ref()
                .map(|polynomial| &polynomial.as_ref()[start..end]);
            fold_weighted(&inputs, &weights, values)
                .expect("input and output coefficient chunks have matching lengths");
        },
    );
    Ok(folded)
}

/// Collapses coefficient polynomials with Horner weights, paying one
/// Montgomery reduction per output coefficient rather than one per polynomial.
#[cfg(test)]
pub(in crate::native::prover) fn deferred_horner_polynomial_fold(
    polynomials: &[&[Fp]],
    challenge: &Fp,
) -> Result<Vec<Fp>, Error> {
    let (first, rest) = polynomials.split_first().ok_or(Error::InternalInvariant)?;
    if first.len() != N {
        return Err(Error::InternalInvariant);
    }
    let mut accumulator = first.to_vec();
    deferred_horner_polynomial_fold_in_place(&mut accumulator, rest, challenge)?;
    Ok(accumulator)
}

/// Folds `polynomials` into `accumulator` with Horner weights — the
/// accumulator is the leading term, so the result is
/// `accumulator·c^m + p_0·c^(m-1) + … + p_(m-1)` — paying one Montgomery
/// reduction per output coefficient rather than one per polynomial. The
/// serial reference for [`super::parallel_deferred_horner_fold`].
#[cfg(test)]
pub(in crate::native::prover) fn deferred_horner_polynomial_fold_in_place(
    accumulator: &mut [Fp],
    polynomials: &[&[Fp]],
    challenge: &Fp,
) -> Result<(), Error> {
    if accumulator.len() != N || polynomials.iter().any(|polynomial| polynomial.len() != N) {
        return Err(Error::InternalInvariant);
    }
    let mut weights = alloc::vec![ <Fp>::ZERO; polynomials.len() + 1];
    let mut power = <Fp>::ONE;
    for weight in weights.iter_mut().rev() {
        *weight = power;
        power = power.mul(challenge);
    }
    let (leading_weight, weights) = weights
        .split_first()
        .expect("the weight vector has the leading term's entry");
    for (index, coefficient) in accumulator.iter_mut().enumerate() {
        *coefficient = <Fp>::sum_of_product_pairs(
            core::iter::once((&*coefficient, leading_weight)).chain(
                polynomials
                    .iter()
                    .zip(weights)
                    .map(|(polynomial, weight)| (&polynomial[index], weight)),
            ),
        );
    }
    Ok(())
}
