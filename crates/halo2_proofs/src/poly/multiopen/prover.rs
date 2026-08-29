use super::super::{
    Coeff, Polynomial,
    commitment::{self, Blind, Params},
};
use super::{
    ChallengeX1, ChallengeX2, ChallengeX3, ChallengeX4, ProverQuery, Query,
    construct_intermediate_sets,
};

use crate::arithmetic::{CurveAffine, eval_polynomial, kate_division};
use crate::multicore;
use crate::transcript::{EncodedChallenge, TranscriptWrite};

use ff::Field;
use group::Curve;
use pasta_curves::{deferred::DeferredField, pallas, vesta};
use rand_core::Rng;
use std::any::{Any, TypeId};
use std::hash::Hash;
use std::io;
use std::marker::PhantomData;

// Amortize task scheduling over at least this many field multiply-adds per
// worker.
const MIN_PARALLEL_FOLDS_PER_THREAD: usize = 1 << 10;
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
    if thread_count == 1 || total_work.div_ceil(thread_count) < MIN_PARALLEL_FOLDS_PER_THREAD {
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

/// Create a multi-opening proof.
///
/// A queried polynomial with fewer coefficients than the parameters' domain
/// size is treated as zero-extended to that size.
///
/// # Errors
///
/// Returns [`std::io::ErrorKind::InvalidInput`] if `queries` is empty,
/// contains more than one query for the same commitment at the same point,
/// or queries a polynomial with more coefficients than the parameters'
/// domain size.
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
        if commitment_data.commitment.poly.num_coeffs() > params.n as usize {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "query polynomial has more coefficients than the parameters' domain size",
            ));
        }
        polynomial_groups[set_index].push(commitment_data.commitment.poly);
        q_blinds[set_index] *= *x_1;
        q_blinds[set_index] += commitment_data.commitment.blind;
    }
    let mut q_polys = collapse_polynomials(&polynomial_groups, *x_1);
    // Each collapsed polynomial keeps its group head's length. Zero-extend to
    // the parameters' length — absent high coefficients read as zero, exactly
    // as the polynomial's commitment treats them — so the final combination
    // below folds equal-length operands.
    for q_poly in &mut q_polys {
        q_poly.values.resize(params.n as usize, C::Scalar::ZERO);
    }

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
    use super::{Coeff, MIN_PARALLEL_FOLDS_PER_THREAD, Polynomial, collapse_polynomials};
    use ff::Field;
    use pasta_curves::{Fp, Fq};
    use std::fmt::Debug;
    use std::marker::PhantomData;

    // A group's collapse keeps the first polynomial's length: shorter group
    // members are zero-extended and longer ones truncated to it, matching
    // `fold_polynomial_range`'s treatment of absent coefficients. Polynomial
    // addition itself requires equal lengths, so fold each coefficient
    // directly.
    fn reference_collapse<F: Field>(
        groups: &[Vec<&Polynomial<F, Coeff>>],
        challenge: F,
    ) -> Vec<Polynomial<F, Coeff>> {
        groups
            .iter()
            .map(|group| Polynomial {
                values: (0..group[0].values.len())
                    .map(|coefficient_index| {
                        group.iter().fold(F::ZERO, |accumulator, polynomial| {
                            accumulator * challenge
                                + polynomial
                                    .values
                                    .get(coefficient_index)
                                    .copied()
                                    .unwrap_or(F::ZERO)
                        })
                    })
                    .collect(),
                _marker: PhantomData,
            })
            .collect()
    }

    fn streaming_collapse_matches_reference<F>()
    where
        F: Field + From<u64> + Debug,
    {
        let long = MIN_PARALLEL_FOLDS_PER_THREAD * 2 + 1;
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

    #[test]
    fn streaming_collapse_matches_reference_fp() {
        streaming_collapse_matches_reference::<Fp>();
    }

    #[test]
    fn streaming_collapse_matches_reference_fq() {
        streaming_collapse_matches_reference::<Fq>();
    }

    #[test]
    fn short_query_polynomial_proves_and_verifies() {
        use crate::arithmetic::eval_polynomial;
        use crate::pasta::EpAffine;
        use crate::poly::commitment::{Blind, Params};
        use crate::poly::multiopen::{ProverQuery, VerifierQuery, create_proof, verify_proof};
        use crate::transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptRead, TranscriptWrite,
        };
        use group::Curve;
        use rand::rng;

        let mut rng = rng();
        let params = Params::<EpAffine>::new(1);

        // A one-coefficient query polynomial is zero-extended to the
        // parameters' length, so its commitment is that of the padded copy.
        let short = Polynomial::<Fq, Coeff> {
            values: vec![Fq::from(5)],
            _marker: PhantomData,
        };
        let padded = Polynomial::<Fq, Coeff> {
            values: vec![Fq::from(5), Fq::ZERO],
            _marker: PhantomData,
        };
        let full = Polynomial::<Fq, Coeff> {
            values: vec![Fq::from(3), Fq::from(4)],
            _marker: PhantomData,
        };
        let short_blind = Blind(Fq::random(&mut rng));
        let full_blind = Blind(Fq::random(&mut rng));
        let short_commitment = params.commit(&padded, short_blind).to_affine();
        let full_commitment = params.commit(&full, full_blind).to_affine();

        let short_point = Fq::from(97);
        let full_point = Fq::from(43);
        let short_eval = eval_polynomial(&short[..], short_point);
        let full_eval = eval_polynomial(&full[..], full_point);

        let mut transcript =
            Blake2bWrite::<Vec<u8>, EpAffine, Challenge255<EpAffine>>::init(vec![]);
        transcript.write_point(short_commitment).unwrap();
        transcript.write_point(full_commitment).unwrap();
        transcript.write_scalar(short_eval).unwrap();
        transcript.write_scalar(full_eval).unwrap();
        create_proof(
            &params,
            rng,
            &mut transcript,
            vec![
                ProverQuery {
                    point: short_point,
                    poly: &short,
                    blind: short_blind,
                },
                ProverQuery {
                    point: full_point,
                    poly: &full,
                    blind: full_blind,
                },
            ],
        )
        .unwrap();
        let proof = transcript.finalize();

        let mut transcript =
            Blake2bRead::<&[u8], EpAffine, Challenge255<EpAffine>>::init(&proof[..]);
        assert_eq!(transcript.read_point().unwrap(), short_commitment);
        assert_eq!(transcript.read_point().unwrap(), full_commitment);
        assert_eq!(transcript.read_scalar().unwrap(), short_eval);
        assert_eq!(transcript.read_scalar().unwrap(), full_eval);
        let guard = verify_proof(
            &params,
            &mut transcript,
            vec![
                VerifierQuery::new_commitment(&short_commitment, short_point, short_eval),
                VerifierQuery::new_commitment(&full_commitment, full_point, full_eval),
            ],
            params.empty_msm(),
        )
        .unwrap();
        assert!(guard.use_challenges().eval());
    }

    #[test]
    fn oversized_query_polynomial_is_rejected() {
        use crate::pasta::EpAffine;
        use crate::poly::commitment::{Blind, Params};
        use crate::poly::multiopen::{ProverQuery, create_proof};
        use crate::transcript::{Blake2bWrite, Challenge255};
        use rand::rng;

        let params = Params::<EpAffine>::new(1);
        let oversized = Polynomial::<Fq, Coeff> {
            values: vec![Fq::ONE; 4],
            _marker: PhantomData,
        };

        let mut transcript =
            Blake2bWrite::<Vec<u8>, EpAffine, Challenge255<EpAffine>>::init(vec![]);
        let result = create_proof(
            &params,
            rng(),
            &mut transcript,
            vec![ProverQuery {
                point: Fq::from(97),
                poly: &oversized,
                blind: Blind(Fq::ZERO),
            }],
        );
        assert_eq!(result.unwrap_err().kind(), std::io::ErrorKind::InvalidInput);
    }
}
