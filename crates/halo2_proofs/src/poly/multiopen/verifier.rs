use ff::{BatchInvert, Field};

use super::super::{
    Error,
    commitment::{Guard, MSM, Params},
};
use super::{
    ChallengeX1, ChallengeX2, ChallengeX3, ChallengeX4, CommitmentReference, Query, VerifierQuery,
    construct_intermediate_sets,
};
use crate::arithmetic::CurveAffine;
use crate::transcript::{EncodedChallenge, TranscriptRead};

/// Computes the expected evaluation of the multi-point quotient at `x_3`.
///
/// Each point set contributes one Lagrange denominator per point and one
/// vanishing denominator. Inverting all of them together reduces this phase to
/// a single field inversion.
fn compute_msm_eval<F: Field>(
    point_sets: &[Vec<F>],
    q_eval_sets: &[Vec<F>],
    proof_evals: &[F],
    x_2: F,
    x_3: F,
) -> Result<F, Error> {
    assert_eq!(point_sets.len(), q_eval_sets.len());
    assert_eq!(point_sets.len(), proof_evals.len());

    let denominator_count = point_sets.iter().map(|points| points.len() + 1).sum();
    let mut denominators = Vec::with_capacity(denominator_count);

    for points in point_sets {
        for (j, x_j) in points.iter().enumerate() {
            let denominator = points
                .iter()
                .enumerate()
                .filter(|(k, _)| *k != j)
                .fold(F::ONE, |denominator, (_, x_k)| denominator * (*x_j - x_k));
            assert!(
                !bool::from(denominator.is_zero()),
                "point sets must contain distinct points"
            );
            denominators.push(denominator);
        }

        let vanishing_denominator = points
            .iter()
            .fold(F::ONE, |denominator, point| denominator * (x_3 - point));
        if bool::from(vanishing_denominator.is_zero()) {
            return Err(Error::OpeningError);
        }
        denominators.push(vanishing_denominator);
    }

    if denominators.is_empty() {
        return Ok(F::ZERO);
    }

    denominators.iter_mut().batch_invert();
    let mut inverse_denominators = denominators.into_iter();

    let msm_eval = point_sets.iter().zip(q_eval_sets).zip(proof_evals).fold(
        F::ZERO,
        |msm_eval, ((points, evals), proof_eval)| {
            assert_eq!(points.len(), evals.len());

            let r_eval =
                points
                    .iter()
                    .enumerate()
                    .zip(evals)
                    .fold(F::ZERO, |r_eval, ((j, _), eval)| {
                        let numerator = points
                            .iter()
                            .enumerate()
                            .filter(|(k, _)| *k != j)
                            .fold(F::ONE, |numerator, (_, point)| numerator * (x_3 - point));
                        let denominator_inv = inverse_denominators
                            .next()
                            .expect("one inverse denominator per interpolation point");

                        r_eval + *eval * numerator * denominator_inv
                    });
            let vanishing_denominator_inv = inverse_denominators
                .next()
                .expect("one inverse vanishing denominator per point set");
            let eval = (*proof_eval - r_eval) * vanishing_denominator_inv;

            msm_eval * x_2 + eval
        },
    );

    debug_assert!(inverse_denominators.next().is_none());
    Ok(msm_eval)
}

/// The most evaluations one commitment keeps inline in
/// [`construct_verifier_sets`]; more fall back to the generic construction.
const INLINE_EVALS: usize = 8;

/// Hashes a commitment reference's address with one multiplication.
#[derive(Default)]
struct AddressHasher(u64);

impl std::hash::Hasher for AddressHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.0 = (self.0.rotate_left(8) ^ u64::from(byte)).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        }
    }
    fn write_usize(&mut self, value: usize) {
        self.0 = (self.0 ^ value as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    }
}

/// One commitment's evaluations, ordered by point index, from either
/// construction.
enum Evals<F> {
    Inline(InlineEvals<F>),
    Heap(Vec<F>),
}

impl<F> Evals<F> {
    fn as_slice(&self) -> &[F] {
        match self {
            Evals::Inline(evals) => &evals.evals[..evals.len],
            Evals::Heap(evals) => evals,
        }
    }
}

/// One commitment's evaluations, ordered by point index.
#[derive(Clone, Copy)]
struct InlineEvals<F> {
    len: usize,
    points: [u8; INLINE_EVALS],
    evals: [F; INLINE_EVALS],
}

/// The verifier's form of `construct_intermediate_sets`: the same commitment
/// order, point sets, set indices and evaluation order, built in one pass
/// with each commitment's point set as a bit mask and its evaluations inline,
/// instead of several small vectors and tree nodes per commitment. Returns
/// `Err(())` for shapes it does not represent (more than `usize::BITS` points
/// or [`INLINE_EVALS`] evaluations per commitment), and `Ok(None)` where the
/// generic construction returns `None`.
#[allow(clippy::type_complexity)]
fn construct_verifier_sets<'r, 'params: 'r, C: CurveAffine, I>(
    queries: I,
) -> Result<
    Option<(
        Vec<(
            CommitmentReference<'r, 'params, C>,
            usize,
            InlineEvals<C::Scalar>,
        )>,
        Vec<Vec<C::Scalar>>,
    )>,
    (),
>
where
    I: IntoIterator<Item = VerifierQuery<'r, 'params, C>>,
{
    let queries = queries.into_iter();
    let capacity = queries.size_hint().0;
    let mut points: Vec<C::Scalar> = Vec::new();
    let mut commitments: Vec<(
        CommitmentReference<'r, 'params, C>,
        usize,
        InlineEvals<C::Scalar>,
    )> = Vec::with_capacity(capacity);
    // Commitment references hash and compare by address.
    #[allow(clippy::mutable_key_type)]
    let mut indices: std::collections::HashMap<
        CommitmentReference<'r, 'params, C>,
        usize,
        std::hash::BuildHasherDefault<AddressHasher>,
    > = std::collections::HashMap::with_capacity_and_hasher(capacity, Default::default());
    for query in queries {
        let point = query.get_point();
        let point_index = match points.iter().position(|p| *p == point) {
            Some(index) => index,
            None => {
                if points.len() == usize::BITS as usize {
                    return Err(());
                }
                points.push(point);
                points.len() - 1
            }
        };
        let commitment = query.get_commitment();
        let index = *indices.entry(commitment).or_insert_with(|| {
            commitments.push((
                commitment,
                0,
                InlineEvals {
                    len: 0,
                    points: [0; INLINE_EVALS],
                    evals: [C::Scalar::ZERO; INLINE_EVALS],
                },
            ));
            commitments.len() - 1
        });
        let (_, mask, evals) = &mut commitments[index];
        let bit = 1usize << point_index;
        if *mask & bit != 0 {
            return Ok(None);
        }
        if evals.len == INLINE_EVALS {
            return Err(());
        }
        *mask |= bit;
        // Insert in point-index order.
        let mut at = evals.len;
        while at > 0 && usize::from(evals.points[at - 1]) > point_index {
            evals.points[at] = evals.points[at - 1];
            evals.evals[at] = evals.evals[at - 1];
            at -= 1;
        }
        evals.points[at] = point_index as u8;
        evals.evals[at] = query.get_eval();
        evals.len += 1;
    }
    if commitments.is_empty() {
        return Ok(None);
    }
    let mut masks: Vec<usize> = Vec::new();
    for (_, mask, _) in commitments.iter_mut() {
        *mask = match masks.iter().position(|m| m == mask) {
            Some(set) => set,
            None => {
                masks.push(*mask);
                masks.len() - 1
            }
        };
    }
    let point_sets = masks
        .into_iter()
        .map(|mask| {
            points
                .iter()
                .enumerate()
                .filter_map(|(i, p)| ((mask >> i) & 1 == 1).then_some(*p))
                .collect()
        })
        .collect();
    Ok(Some((commitments, point_sets)))
}

/// Verify a multi-opening proof.
///
/// # Errors
///
/// Returns [`Error::OpeningError`] if the query set is empty, contains more
/// than one query for the same commitment at the same point, or the verifier
/// challenge is one of the queried points.
pub fn verify_proof<
    'r,
    'params: 'r,
    I,
    C: CurveAffine,
    E: EncodedChallenge<C>,
    T: TranscriptRead<C, E>,
>(
    params: &'params Params<C>,
    transcript: &mut T,
    queries: I,
    mut msm: MSM<'params, C>,
) -> Result<Guard<'params, C, E>, Error>
where
    I: IntoIterator<Item = VerifierQuery<'r, 'params, C>> + Clone,
{
    // Sample x_1 for compressing openings at the same point sets together
    let x_1: ChallengeX1<_> = transcript.squeeze_challenge_scalar();

    // Sample a challenge x_2 for keeping the multi-point quotient
    // polynomial terms linearly independent.
    let x_2: ChallengeX2<_> = transcript.squeeze_challenge_scalar();

    #[allow(clippy::type_complexity)]
    let (commitment_map, point_sets): (Vec<(_, usize, Evals<C::Scalar>)>, _) =
        match construct_verifier_sets(queries.clone()) {
            Ok(sets) => {
                let (map, sets) = sets.ok_or(Error::OpeningError)?;
                (
                    map.into_iter()
                        .map(|(c, set, evals)| (c, set, Evals::Inline(evals)))
                        .collect(),
                    sets,
                )
            }
            Err(()) => {
                let (map, sets) =
                    construct_intermediate_sets(queries).ok_or(Error::OpeningError)?;
                (
                    map.into_iter()
                        .map(|data| (data.commitment, data.set_index, Evals::Heap(data.evals)))
                        .collect(),
                    sets,
                )
            }
        };

    // The final commitment is
    //   [x_4^n] Q' + sum_i [x_4^(n - 1 - i)] Q_i,  Q_i = sum_j [x_1^j] C_ij
    // for the n point sets. Fold each commitment's two powers into one
    // scalar here, instead of scaling every accumulated term again for
    // each later point set; x_4 is sampled only after Q' is read, so the
    // terms are collected first and scaled once x_4 is known.
    let mut q_commitments: Vec<_> = vec![
        (Vec::new(), C::Scalar::ONE); // (commitments with x_1 powers, next x_1 power).
        point_sets.len()];

    // A vec of vecs of evals. The outer vec corresponds to the point set,
    // while the inner vec corresponds to the points in a particular set.
    let mut q_eval_sets = Vec::with_capacity(point_sets.len());
    for point_set in point_sets.iter() {
        q_eval_sets.push(vec![C::Scalar::ZERO; point_set.len()]);
    }

    {
        let mut accumulate = |set_idx: usize, new_commitment, evals: &[C::Scalar]| {
            let (q_commitment, x_1_power) = &mut q_commitments[set_idx];
            q_commitment.push((new_commitment, *x_1_power));
            for (eval, set_eval) in evals.iter().zip(q_eval_sets[set_idx].iter_mut()) {
                *set_eval += (*eval) * (*x_1_power);
            }
            *x_1_power *= *x_1;
        };

        // Each commitment corresponds to evaluations at a set of points.
        // For each set, we collapse each commitment's evals pointwise.
        // Run in order of increasing x_1 powers.
        for (commitment, set_index, evals) in commitment_map.iter().rev() {
            accumulate(*set_index, *commitment, evals.as_slice());
        }
    }

    // Obtain the commitment to the multi-point quotient polynomial f(X).
    let q_prime_commitment = transcript.read_point().map_err(|_| Error::SamplingError)?;

    // Sample a challenge x_3 for checking that f(X) was committed to
    // correctly.
    let x_3: ChallengeX3<_> = transcript.squeeze_challenge_scalar();

    // u is a vector containing the evaluations of the Q polynomial
    // commitments at x_3
    let mut u = Vec::with_capacity(q_eval_sets.len());
    for _ in 0..q_eval_sets.len() {
        u.push(transcript.read_scalar().map_err(|_| Error::SamplingError)?);
    }

    // We can compute the expected msm_eval at x_3 using the u provided
    // by the prover and from x_2
    let msm_eval = compute_msm_eval(&point_sets, &q_eval_sets, &u, *x_2, *x_3)?;

    // Sample a challenge x_4 that we will use to collapse the openings of
    // the various remaining polynomials at x_3 together.
    let x_4: ChallengeX4<_> = transcript.squeeze_challenge_scalar();

    // Compute the final commitment that has to be opened
    let mut x_4_power = C::Scalar::ONE;
    let mut v = msm_eval;
    let mut x_4_powers = Vec::with_capacity(q_commitments.len());
    for _ in u.iter() {
        x_4_powers.push(x_4_power);
        x_4_power *= *x_4;
    }
    for q_eval in u.iter() {
        v = v * &(*x_4) + q_eval;
    }
    msm.scale(x_4_power);
    msm.append_term(x_4_power, q_prime_commitment);
    for ((q_commitment, _), x_4_power) in
        q_commitments.into_iter().zip(x_4_powers.into_iter().rev())
    {
        for (commitment, x_1_power) in q_commitment {
            let scalar = x_1_power * x_4_power;
            match commitment {
                CommitmentReference::Commitment(c) => msm.append_term(scalar, *c),
                CommitmentReference::MSM(inner) => {
                    let mut inner = inner.clone();
                    inner.scale(scalar);
                    msm.add_msm(&inner);
                }
            }
        }
    }

    // Verify the opening proof
    super::commitment::verify_proof(params, msm, transcript, *x_3, v)
}

impl<'a, 'b, C: CurveAffine> Query<C::Scalar> for VerifierQuery<'a, 'b, C> {
    type Commitment = CommitmentReference<'a, 'b, C>;
    type Eval = C::Scalar;

    fn get_point(&self) -> C::Scalar {
        self.point
    }
    fn get_eval(&self) -> C::Scalar {
        self.eval
    }
    fn get_commitment(&self) -> Self::Commitment {
        self.commitment
    }
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;
    use ff::Field;
    use group::CurveAffine;

    use super::{
        ChallengeX1, ChallengeX2, ChallengeX3, Error, Params, VerifierQuery, compute_msm_eval,
        verify_proof,
    };
    use crate::{
        arithmetic::{eval_polynomial, lagrange_interpolate},
        pasta::{EqAffine, Fp},
        transcript::{Blake2bRead, Blake2bWrite, Challenge255, Transcript, TranscriptWrite},
    };

    fn reference_msm_eval(
        point_sets: &[Vec<Fp>],
        q_eval_sets: &[Vec<Fp>],
        proof_evals: &[Fp],
        x_2: Fp,
        x_3: Fp,
    ) -> Fp {
        point_sets.iter().zip(q_eval_sets).zip(proof_evals).fold(
            Fp::ZERO,
            |msm_eval, ((points, evals), proof_eval)| {
                let r_poly = lagrange_interpolate(points, evals);
                let r_eval = eval_polynomial(&r_poly, x_3);
                let eval = points.iter().fold(*proof_eval - r_eval, |eval, point| {
                    eval * (x_3 - point).invert().unwrap()
                });

                msm_eval * x_2 + eval
            },
        )
    }

    #[test]
    fn batched_msm_eval_matches_reference_for_orchard_shapes() {
        assert_eq!(
            compute_msm_eval(&[], &[], &[], Fp::from(2), Fp::from(3))
                .expect("empty input is supported"),
            reference_msm_eval(&[], &[], &[], Fp::from(2), Fp::from(3)),
        );

        for offset in 0_u64..16 {
            let points = [
                Fp::from(11 + offset),
                Fp::from(37 + 2 * offset),
                Fp::from(83 + 3 * offset),
                Fp::from(151 + 5 * offset),
            ];
            // These are the point-set sizes used by the Orchard verifier.
            let point_sets = vec![
                vec![points[0]],
                vec![points[0], points[1]],
                vec![points[0], points[2]],
                vec![points[0], points[1], points[2]],
                vec![points[0], points[1], points[3]],
            ];
            let q_eval_sets: Vec<Vec<_>> = point_sets
                .iter()
                .enumerate()
                .map(|(set, points)| {
                    points
                        .iter()
                        .enumerate()
                        .map(|(point, _)| Fp::from(100 + offset * 20 + set as u64 + point as u64))
                        .collect()
                })
                .collect();
            let proof_evals: Vec<_> = (0..point_sets.len())
                .map(|i| Fp::from(1_000 + offset * 10 + i as u64))
                .collect();
            let x_2 = Fp::from(2_000 + offset);
            let x_3 = Fp::from(3_000 + offset);

            assert_eq!(
                compute_msm_eval(&point_sets, &q_eval_sets, &proof_evals, x_2, x_3)
                    .expect("challenge is distinct from all query points"),
                reference_msm_eval(&point_sets, &q_eval_sets, &proof_evals, x_2, x_3),
            );
        }
    }

    #[test]
    fn verifier_rejects_challenge_in_point_set() {
        let params = Params::<EqAffine>::new(1);
        let commitment = EqAffine::generator();

        // Reproduce the verifier transcript prefix to obtain x_3, then use it
        // as the query point in a fresh verification call.
        let mut transcript =
            Blake2bWrite::<Vec<u8>, EqAffine, Challenge255<EqAffine>>::init(vec![]);
        let _: ChallengeX1<_> = transcript.squeeze_challenge_scalar();
        let _: ChallengeX2<_> = transcript.squeeze_challenge_scalar();
        transcript.write_point(commitment).unwrap();
        let x_3: ChallengeX3<_> = transcript.squeeze_challenge_scalar();
        transcript.write_scalar(Fp::ONE).unwrap();
        let proof = transcript.finalize();

        let mut transcript = Blake2bRead::<&[u8], EqAffine, Challenge255<EqAffine>>::init(&proof);
        let queries = [VerifierQuery::new_commitment(&commitment, *x_3, Fp::ONE)];
        assert_matches!(
            verify_proof(&params, &mut transcript, queries, params.empty_msm(),),
            Err(Error::OpeningError)
        );
    }
}

#[cfg(test)]
mod verifier_sets_tests {
    use super::super::{VerifierQuery, construct_intermediate_sets};
    use super::construct_verifier_sets;
    use crate::pasta::{EqAffine, Fp};
    use ff::Field;
    use group::{Curve, Group};
    use rand::{RngExt, SeedableRng};

    #[test]
    fn verifier_sets_match_generic_construction() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(1);
        let commitments: Vec<EqAffine> = (0..12)
            .map(|_| crate::pasta::Eq::random(&mut rng).to_affine())
            .collect();
        let points: Vec<Fp> = (0..5).map(|_| Fp::random(&mut rng)).collect();
        for _ in 0..200 {
            let mut queries = Vec::new();
            for _ in 0..rng.random_range(1..40) {
                let c = &commitments[rng.random_range(0..commitments.len())];
                let p = points[rng.random_range(0..points.len())];
                queries.push(VerifierQuery::<EqAffine>::new_commitment(
                    c,
                    p,
                    Fp::random(&mut rng),
                ));
            }
            let generic = construct_intermediate_sets(queries.clone());
            let fast = construct_verifier_sets(queries.clone()).expect("shape fits inline");
            match (generic, fast) {
                (None, None) => {}
                (Some((map, sets)), Some((fast_map, fast_sets))) => {
                    assert_eq!(sets, fast_sets);
                    assert_eq!(map.len(), fast_map.len());
                    for (data, (commitment, set, evals)) in map.iter().zip(&fast_map) {
                        assert!(data.commitment == *commitment);
                        assert_eq!(data.set_index, *set);
                        assert_eq!(&data.evals[..], &evals.evals[..evals.len]);
                    }
                }
                (generic, fast) => panic!("{} vs {}", generic.is_some(), fast.is_some()),
            }
        }
    }

    /// Shapes beyond the inline representation (more than `INLINE_EVALS`
    /// evaluations of one commitment, or more than `usize::BITS` points)
    /// take the generic construction, and proofs over them still verify.
    #[test]
    fn verifier_sets_fall_back_beyond_inline_shapes() {
        use super::super::{ProverQuery, create_proof};
        use super::{INLINE_EVALS, verify_proof};
        use crate::arithmetic::eval_polynomial;
        use crate::poly::{
            EvaluationDomain,
            commitment::{Blind, Params},
        };
        use crate::transcript::{Blake2bRead, Blake2bWrite, Challenge255};

        let mut rng = rand::rngs::StdRng::seed_from_u64(2);
        let commitment = crate::pasta::Eq::random(&mut rng).to_affine();
        let many_points = (0..=usize::BITS as u64)
            .map(|i| {
                VerifierQuery::<EqAffine>::new_commitment(&commitment, Fp::from(i + 1), Fp::ONE)
            })
            .collect::<Vec<_>>();
        assert!(construct_verifier_sets(many_points).is_err());

        const K: u32 = 4;
        let params: Params<EqAffine> = Params::new(K);
        let domain = EvaluationDomain::new(1, K);
        let mut poly = domain.empty_coeff();
        for (i, coeff) in poly.iter_mut().enumerate() {
            *coeff = Fp::from(3 + i as u64);
        }
        let blind = Blind(Fp::random(&mut rng));
        let commitment = params.commit(&poly, blind).to_affine();
        let points: Vec<Fp> = (0..=INLINE_EVALS).map(|_| Fp::random(&mut rng)).collect();
        let evals: Vec<Fp> = points.iter().map(|x| eval_polynomial(&poly, *x)).collect();
        let queries = |evals: &[Fp]| {
            points
                .iter()
                .zip(evals)
                .map(|(x, v)| VerifierQuery::new_commitment(&commitment, *x, *v))
                .collect::<Vec<_>>()
        };
        assert!(construct_verifier_sets(queries(&evals)).is_err());

        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(
            &params,
            &mut rng,
            &mut transcript,
            points.iter().map(|x| ProverQuery {
                point: *x,
                poly: &poly,
                blind,
            }),
        )
        .unwrap();
        let proof = transcript.finalize();

        let verify = |evals: &[Fp]| {
            let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
            verify_proof(&params, &mut transcript, queries(evals), params.empty_msm())
                .unwrap()
                .use_challenges()
                .eval()
        };
        assert!(verify(&evals));
        let mut wrong = evals.clone();
        wrong[INLINE_EVALS] += Fp::ONE;
        assert!(!verify(&wrong));
    }
}
