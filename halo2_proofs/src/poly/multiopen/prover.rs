use super::super::{
    commitment::{self, Blind, Params},
    Coeff, Polynomial,
};
use super::{
    construct_intermediate_sets, ChallengeX1, ChallengeX2, ChallengeX3, ChallengeX4, ProverQuery,
    Query,
};

use crate::arithmetic::{eval_polynomial, kate_division, CurveAffine};
use crate::multicore;
use crate::transcript::{EncodedChallenge, TranscriptWrite};

use ff::Field;
use group::Curve;
use rand_core::Rng;
use std::hash::Hash;
use std::io;
use std::marker::PhantomData;

// Amortize task scheduling over at least this many field multiply-adds per
// worker.
const MIN_PARALLEL_FOLDS_PER_THREAD: usize = 1 << 10;

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

fn collapse_polynomials<F: Field>(
    groups: &[Vec<&Polynomial<F, Coeff>>],
    challenge: F,
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
    if thread_count == 1 || total_work.div_ceil(thread_count) < MIN_PARALLEL_FOLDS_PER_THREAD {
        for (polynomial, group) in collapsed.iter_mut().zip(groups) {
            fold_polynomial_range(&mut polynomial.values, 0, &group[1..], challenge);
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
                scope.spawn(move |_| {
                    fold_polynomial_range(values, start, &group[1..], challenge);
                });
            }
        }
    });

    collapsed
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
    let q_polys = collapse_polynomials(&polynomial_groups, *x_1);

    let q_prime_poly = point_sets
        .iter()
        .zip(q_polys.iter())
        .fold(None, |q_prime_poly, (points, poly)| {
            let mut poly = points.iter().fold(poly.clone().values, |poly, point| {
                kate_division(&poly, *point)
            });
            poly.resize(params.n as usize, C::Scalar::ZERO);
            let poly = Polynomial {
                values: poly,
                _marker: PhantomData,
            };

            if q_prime_poly.is_none() {
                Some(poly)
            } else {
                q_prime_poly.map(|q_prime_poly| q_prime_poly * *x_2 + &poly)
            }
        })
        .unwrap();

    let q_prime_blind = Blind(C::Scalar::random(&mut rng));
    let q_prime_commitment = params.commit(&q_prime_poly, q_prime_blind).to_affine();

    transcript.write_point(q_prime_commitment)?;

    let x_3: ChallengeX3<_> = transcript.squeeze_challenge_scalar();

    // Prover sends u_i for all i, which correspond to the evaluation
    // of each Q polynomial commitment at x_3.
    for q_i_poly in &q_polys {
        transcript.write_scalar(eval_polynomial(q_i_poly, *x_3))?;
    }

    let x_4: ChallengeX4<_> = transcript.squeeze_challenge_scalar();

    let (p_poly, p_poly_blind) = q_polys.into_iter().zip(q_blinds).fold(
        (q_prime_poly, q_prime_blind),
        |(q_prime_poly, q_prime_blind), (poly, blind)| {
            (
                q_prime_poly * *x_4 + &poly,
                Blind((q_prime_blind.0 * &(*x_4)) + &blind.0),
            )
        },
    );

    commitment::create_proof(params, rng, transcript, &p_poly, p_poly_blind, *x_3)
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
    use super::{collapse_polynomials, Coeff, Polynomial, MIN_PARALLEL_FOLDS_PER_THREAD};
    use ff::Field;
    use pasta_curves::Fp;
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

    #[test]
    fn streaming_collapse_matches_operator_collapse() {
        let long = MIN_PARALLEL_FOLDS_PER_THREAD * 2;
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
                                Fp::from(
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

        let challenge = Fp::from(17);
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
