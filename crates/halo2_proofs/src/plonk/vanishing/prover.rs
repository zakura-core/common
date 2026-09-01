use std::{
    any::{Any, TypeId},
    iter,
};

use ff::{Field, WithSmallOrderMulGroup};
use group::Curve;
#[cfg(feature = "multicore")]
use maybe_rayon::prelude::*;
use pasta_curves::{deferred::DeferredField, pallas, vesta};
use rand_core::Rng;

use super::Argument;
use crate::{
    arithmetic::{CurveAffine, best_multiexp, parallelize},
    plonk::{ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, ChallengeY, Error},
    poly::{
        self, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, Polynomial, ProvingKeyTwiddles,
        commitment::{Blind, Params},
        multiopen::ProverQuery,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};

fn fold_quotient_pieces<F: WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    pieces: Vec<Polynomial<F, Coeff>>,
    xn: F,
) -> Polynomial<F, Coeff> {
    if pieces.is_empty() {
        return domain.empty_coeff();
    }

    if TypeId::of::<F>() == TypeId::of::<pallas::Base>() {
        fold_quotient_pieces_pasta::<F, pallas::Base>(pieces, xn)
    } else if TypeId::of::<F>() == TypeId::of::<vesta::Base>() {
        fold_quotient_pieces_pasta::<F, vesta::Base>(pieces, xn)
    } else {
        fold_quotient_pieces_horner(pieces, xn)
    }
}

fn fold_quotient_pieces_horner<F: WithSmallOrderMulGroup<3>>(
    mut pieces: Vec<Polynomial<F, Coeff>>,
    xn: F,
) -> Polynomial<F, Coeff> {
    // Pieces are ordered from least to most significant. Move the highest
    // allocation into the accumulator, then consume the rest in Horner order.
    let mut accumulator = pieces
        .pop()
        .expect("an empty quotient-piece list is handled before folding");

    while let Some(piece) = pieces.pop() {
        debug_assert_eq!(accumulator.len(), piece.len());
        parallelize(&mut accumulator, |accumulator, start| {
            for (accumulator, piece) in accumulator.iter_mut().zip(&piece[start..]) {
                *accumulator = *accumulator * xn + *piece;
            }
        });
    }

    accumulator
}

fn fold_quotient_pieces_deferred<F: DeferredField>(
    mut pieces: Vec<Polynomial<F, Coeff>>,
    xn: F,
) -> Polynomial<F, Coeff> {
    let piece_count = pieces.len();
    let mut output = pieces
        .pop()
        .expect("an empty quotient-piece list is handled before folding");
    if pieces.is_empty() {
        return output;
    }

    let mut powers = Vec::with_capacity(piece_count - 1);
    let mut power = xn;
    powers.push(power);
    for _ in 2..piece_count {
        power *= xn;
        powers.push(power);
    }

    let (constant, intermediate) = pieces
        .split_first()
        .expect("a multi-piece quotient has a constant piece");
    parallelize(&mut output, |output, start| {
        let output_len = output.len();
        let mut products = vec![F::Accumulator::default(); output_len];
        let highest_power = powers
            .last()
            .expect("a multi-piece quotient has a nonconstant power");
        for (product, coefficient) in products.iter_mut().zip(output.iter()) {
            F::mul_accumulate(product, coefficient, highest_power);
        }
        for (piece, power) in intermediate.iter().zip(&powers) {
            for (product, coefficient) in products.iter_mut().zip(&piece[start..][..output_len]) {
                F::mul_accumulate(product, coefficient, power);
            }
        }
        for ((output, product), constant) in output
            .iter_mut()
            .zip(products)
            .zip(&constant[start..][..output_len])
        {
            *output = F::reduce(product) + constant;
        }
    });
    output
}

fn fold_quotient_pieces_pasta<
    F: WithSmallOrderMulGroup<3> + 'static,
    T: DeferredField + 'static,
>(
    pieces: Vec<Polynomial<F, Coeff>>,
    xn: F,
) -> Polynomial<F, Coeff> {
    let xn = *(&xn as &dyn Any)
        .downcast_ref::<T>()
        .expect("the quotient field was checked before conversion");
    let pieces: Box<dyn Any> = Box::new(pieces);
    let pieces = *pieces
        .downcast::<Vec<Polynomial<T, Coeff>>>()
        .expect("the quotient pieces match their checked field");
    let result: Box<dyn Any> = Box::new(fold_quotient_pieces_deferred(pieces, xn));
    *result
        .downcast::<Polynomial<F, Coeff>>()
        .expect("the folded quotient matches its input field")
}

// The random polynomial r(X) masks two evaluations in the multi-opening
// transcript. Its independently blinded commitment R is written before y. The
// prover later reveals r(x), then commits with a fresh blind to the
// multi-opening quotient q'. Only after that commitment does it sample x_3 and
// reveal the Q polynomial for the {x} point-set group at x_3. The vanishing
// queries place r after h in that group, so Horner folding gives it unit
// coefficient:
//
//     Q_x(x_3) = (... + x_1 h(x_3)) + r(x_3).
//
// For r(X) = a + bX + cX^2, the first two columns of the map from (a, b, c) to
// (r(x), r(x_3)) have determinant x_3 - x. The map therefore has rank two
// when the points are distinct, and a one-dimensional kernel. Conditioned on
// the revealed r(x), r(x_3) is uniform, with one random coefficient of excess
// entropy after both evaluations are fixed. The verifier rejects x_3 equal to
// any queried point. The independently Pedersen-blinded group messages hide
// the coefficients before each challenge, while the commitment scheme's
// separate IPA mask hides its final folded scalar. This commitment
// participates in one multi-opening, and the verifier sees only r(x) and its
// single affine contribution r(x_3). Thus three random coefficients give the
// same HVZK masking role as the previous dense polynomial, with one excess
// coefficient beyond the two needed for these evaluations, up to the scheme's
// existing negligible challenge-collision and transcript-abort events.
// Soundness does not depend on an honest prover sampling r from either
// distribution.
const QUOTIENT_EVALUATION_MASK_COEFFICIENTS: usize = 3;

fn sample_quotient_evaluation_mask<F: WithSmallOrderMulGroup<3>, R: Rng>(
    domain: &EvaluationDomain<F>,
    mut rng: R,
) -> Polynomial<F, Coeff> {
    let mut polynomial = domain.empty_coeff();
    assert!(polynomial.len() >= QUOTIENT_EVALUATION_MASK_COEFFICIENTS);
    for coefficient in polynomial
        .iter_mut()
        .take(QUOTIENT_EVALUATION_MASK_COEFFICIENTS)
    {
        *coefficient = F::random(&mut rng);
    }
    polynomial
}

fn commit_quotient_evaluation_mask<C: CurveAffine>(
    params: &Params<C>,
    polynomial: &Polynomial<C::Scalar, Coeff>,
    blind: Blind<C::Scalar>,
) -> C::Curve {
    assert_eq!(polynomial.len(), params.n as usize);
    debug_assert!(
        polynomial[QUOTIENT_EVALUATION_MASK_COEFFICIENTS..]
            .iter()
            .all(|coefficient| *coefficient == C::Scalar::ZERO)
    );

    let scalars = [polynomial[0], polynomial[1], polynomial[2]];
    let bases = [params.g[0], params.g[1], params.g[2]];

    params
        .try_commit_sparse_with_prepared_blind(&scalars, &bases, blind)
        .unwrap_or_else(|| {
            let scalars = [polynomial[0], polynomial[1], polynomial[2], blind.0];
            let bases = [params.g[0], params.g[1], params.g[2], params.w];
            best_multiexp(&scalars, &bases)
        })
}

fn evaluate_quotient_evaluation_mask<F: Field>(polynomial: &Polynomial<F, Coeff>, point: F) -> F {
    assert!(polynomial.len() >= QUOTIENT_EVALUATION_MASK_COEFFICIENTS);
    debug_assert!(
        polynomial[QUOTIENT_EVALUATION_MASK_COEFFICIENTS..]
            .iter()
            .all(|coefficient| *coefficient == F::ZERO)
    );

    polynomial[0] + point * (polynomial[1] + polynomial[2] * point)
}

pub(in crate::plonk) struct CommittedRandomPolynomial<C: CurveAffine> {
    poly: Polynomial<C::Scalar, Coeff>,
    blind: Blind<C::Scalar>,
}

pub(in crate::plonk) struct ConstructedQuotient<C: CurveAffine> {
    h_pieces: Vec<Polynomial<C::Scalar, Coeff>>,
    h_blinds: Vec<Blind<C::Scalar>>,
    random_poly: CommittedRandomPolynomial<C>,
}

pub(in crate::plonk) struct EvaluatedQuotient<C: CurveAffine> {
    h_poly: Polynomial<C::Scalar, Coeff>,
    h_blind: Blind<C::Scalar>,
    random_poly: CommittedRandomPolynomial<C>,
}

impl<C: CurveAffine> Argument<C> {
    /// Commits to the random polynomial that masks the folded quotient
    /// evaluation in the multi-opening argument.
    pub(in crate::plonk) fn commit_random_polynomial<
        E: EncodedChallenge<C>,
        R: Rng,
        T: TranscriptWrite<C, E>,
    >(
        params: &Params<C>,
        domain: &EvaluationDomain<C::Scalar>,
        mut rng: R,
        transcript: &mut T,
    ) -> Result<CommittedRandomPolynomial<C>, Error> {
        // Sample a random quadratic polynomial. If the PLONK and multi-opening
        // evaluation points are distinct, its values at those two points are
        // independent and uniform, with one coefficient of excess entropy.
        // The multi-opening verifier rejects the exceptional point collision,
        // which is the same negligible honest-abort event under the previous
        // dense mask.
        let random_poly = sample_quotient_evaluation_mask(domain, &mut rng);
        // Sample a random blinding factor
        let random_blind = Blind(C::Scalar::random(&mut rng));

        // Commit
        let random_poly_commitment =
            commit_quotient_evaluation_mask(params, &random_poly, random_blind).to_affine();
        transcript.write_point(random_poly_commitment)?;

        Ok(CommittedRandomPolynomial {
            poly: random_poly,
            blind: random_blind,
        })
    }
}

impl<C: CurveAffine> CommittedRandomPolynomial<C> {
    #[allow(clippy::too_many_arguments)]
    /// Constructs and commits to the quotient polynomial pieces.
    pub(in crate::plonk) fn construct_quotient<
        E: EncodedChallenge<C>,
        Ev: Copy + Send + Sync,
        R: Rng,
        T: TranscriptWrite<C, E>,
    >(
        self,
        params: &Params<C>,
        domain: &EvaluationDomain<C::Scalar>,
        fft_twiddles: &ProvingKeyTwiddles<C::Scalar>,
        evaluator: poly::Evaluator<Ev, C::Scalar, ExtendedLagrangeCoeff>,
        expressions: impl Iterator<Item = poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>>,
        theta: ChallengeTheta<C>,
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        y: ChallengeY<C>,
        compiled_plan: Option<&poly::CompiledEvaluationPlan<C::Scalar, ExtendedLagrangeCoeff>>,
        mut rng: R,
        transcript: &mut T,
    ) -> Result<
        (
            ConstructedQuotient<C>,
            Option<poly::CompiledEvaluationPlan<C::Scalar, ExtendedLagrangeCoeff>>,
        ),
        Error,
    > {
        // Fold the constraint expressions into the quotient numerator using
        // the y challenge, then evaluate the numerator.
        let challenges = poly::EvaluationChallenges::new(*theta, *beta, *gamma, *y);
        let (quotient_numerator, prepared_plan) = evaluator.evaluate_quotient_with_compiled_plan(
            expressions,
            domain,
            compiled_plan,
            challenges,
        );

        // Move the numerator to coefficient form, divide by
        // t(X) = X^{params.n} - 1 using its sparse block inverse, and construct
        // the coefficient-form quotient pieces in the same pass.
        let h_pieces =
            domain.quotient_numerator_to_pieces_with_twiddles(quotient_numerator, fft_twiddles);
        debug_assert!(
            h_pieces
                .iter()
                .all(|piece| piece.len() == params.n as usize)
        );
        let h_blinds: Vec<_> = h_pieces
            .iter()
            .map(|_| Blind(C::Scalar::random(&mut rng)))
            .collect();

        // Compute commitments to each h(X) piece
        #[cfg(feature = "multicore")]
        let h_commitments_projective: Vec<_> = h_pieces
            .par_iter()
            .zip(h_blinds.par_iter())
            .map(|(h_piece, blind)| params.commit(h_piece, *blind))
            .collect();
        #[cfg(not(feature = "multicore"))]
        let h_commitments_projective: Vec<_> = h_pieces
            .iter()
            .zip(h_blinds.iter())
            .map(|(h_piece, blind)| params.commit(h_piece, *blind))
            .collect();
        let mut h_commitments = vec![C::identity(); h_commitments_projective.len()];
        C::Curve::batch_normalize(&h_commitments_projective, &mut h_commitments);
        let h_commitments = h_commitments;

        // Hash each h(X) piece
        for c in h_commitments.iter() {
            transcript.write_point(*c)?;
        }

        Ok((
            ConstructedQuotient {
                h_pieces,
                h_blinds,
                random_poly: self,
            },
            prepared_plan,
        ))
    }
}

impl<C: CurveAffine> ConstructedQuotient<C> {
    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        x: C::Scalar,
        xn: C::Scalar,
        domain: &EvaluationDomain<C::Scalar>,
        transcript: &mut T,
    ) -> Result<EvaluatedQuotient<C>, Error> {
        let h_poly = fold_quotient_pieces(domain, self.h_pieces, xn);

        let h_blind = self
            .h_blinds
            .iter()
            .rev()
            .fold(Blind(C::Scalar::ZERO), |acc, eval| acc * Blind(xn) + *eval);

        let random_eval = evaluate_quotient_evaluation_mask(&self.random_poly.poly, x);
        transcript.write_scalar(random_eval)?;

        Ok(EvaluatedQuotient {
            h_poly,
            h_blind,
            random_poly: self.random_poly,
        })
    }
}

impl<C: CurveAffine> EvaluatedQuotient<C> {
    pub(in crate::plonk) fn open(
        &self,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = ProverQuery<'_, C>> + Clone {
        // Keep the random polynomial after h(X). The multi-opening fold gives
        // the last polynomial in a point-set group unit weight, so its later
        // evaluation masks h(x_3) without relying on x_1 being nonzero.
        iter::empty()
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.h_poly,
                blind: self.h_blind,
            }))
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.random_poly.poly,
                blind: self.random_poly.blind,
            }))
    }
}

#[cfg(test)]
mod tests {
    use super::{
        QUOTIENT_EVALUATION_MASK_COEFFICIENTS, commit_quotient_evaluation_mask,
        evaluate_quotient_evaluation_mask, fold_quotient_pieces, sample_quotient_evaluation_mask,
    };
    use crate::{
        arithmetic::{CurveAffine, eval_polynomial},
        plonk::ChallengeX,
        poly::{Coeff, EvaluationDomain, Polynomial, commitment::Blind},
        transcript::{Blake2bWrite, Challenge255, Transcript},
    };
    use ff::{Field, WithSmallOrderMulGroup};
    use pasta_curves::{Fp, Fq, pallas, vesta};
    use rand::{SeedableRng, rngs::StdRng};

    fn allocating_fold<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
        pieces: &[Polynomial<F, Coeff>],
        xn: F,
    ) -> Polynomial<F, Coeff> {
        pieces
            .iter()
            .rev()
            .fold(domain.empty_coeff(), |accumulator, piece| {
                accumulator * xn + piece
            })
    }

    fn check_quotient_piece_fold<F: WithSmallOrderMulGroup<3> + From<u64>>() {
        let domain = EvaluationDomain::new(3, 3);
        let domain_size = domain.empty_coeff().len();

        for piece_count in 0..=8 {
            for xn in [F::ZERO, F::ONE, F::from(7)] {
                let pieces = (0..piece_count)
                    .map(|piece| {
                        domain.coeff_from_vec(
                            (0..domain_size)
                                .map(|coefficient| F::from((piece * 17 + coefficient + 1) as u64))
                                .collect(),
                        )
                    })
                    .collect::<Vec<_>>();
                let highest_allocation = pieces.last().map(|piece| piece.as_ptr());
                let expected = allocating_fold(&domain, &pieces, xn);

                let actual = fold_quotient_pieces(&domain, pieces, xn);

                assert!(actual.iter().eq(expected.iter()));
                if let Some(highest_allocation) = highest_allocation {
                    assert_eq!(actual.as_ptr(), highest_allocation);
                }
            }
        }
    }
    #[test]
    fn quotient_piece_fold_matches_allocating_horner_fold() {
        check_quotient_piece_fold::<Fp>();
        check_quotient_piece_fold::<Fq>();
    }

    fn sparse_commitment_matches_dense<C>()
    where
        C: CurveAffine + core::fmt::Debug,
    {
        let domain = EvaluationDomain::new(1, 3);
        let params = crate::poly::commitment::Params::<C>::new(3);
        let mut rng = StdRng::seed_from_u64(0x7175_6f74_6965_6e74);
        let polynomial = sample_quotient_evaluation_mask(&domain, &mut rng);
        assert!(
            polynomial[QUOTIENT_EVALUATION_MASK_COEFFICIENTS..]
                .iter()
                .all(|coefficient| *coefficient == C::Scalar::ZERO)
        );

        let blind = Blind(C::Scalar::random(&mut rng));
        assert_eq!(
            commit_quotient_evaluation_mask(&params, &polynomial, blind),
            params.commit(&polynomial, blind),
        );

        let point = C::Scalar::random(&mut rng);
        assert_eq!(
            evaluate_quotient_evaluation_mask(&polynomial, point),
            eval_polynomial(&polynomial, point),
        );
    }

    fn quadratic_mask_has_excess_entropy_after_two_evaluations<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64> + core::fmt::Debug,
    {
        let first_point = F::from(5);
        let later_point = F::from(9);
        let first_evaluation = F::from(17);
        let point_difference = later_point - first_point;
        let point_difference_inverse = point_difference.invert().unwrap();
        let squared_difference = later_point.square() - first_point.square();

        // For every desired later evaluation and every quadratic coefficient,
        // there is exactly one choice of the remaining two coefficients. Thus
        // the later evaluation is uniform, and fixing both evaluations leaves
        // one coefficient of entropy.
        for later_evaluation in [F::ZERO, F::ONE, F::from(29)] {
            for quadratic in [F::ZERO, F::ONE, F::from(31)] {
                let linear = (later_evaluation - first_evaluation - quadratic * squared_difference)
                    * point_difference_inverse;
                let constant =
                    first_evaluation - linear * first_point - quadratic * first_point.square();
                let evaluate = |point: F| constant + point * (linear + quadratic * point);
                assert_eq!(evaluate(first_point), first_evaluation);
                assert_eq!(evaluate(later_point), later_evaluation);
            }
        }
    }

    #[test]
    fn quotient_evaluation_mask_is_the_last_vanishing_query() {
        let domain = EvaluationDomain::new(1, 3);
        let mut h_poly = domain.empty_coeff();
        h_poly[0] = pallas::Base::from(3);
        let mut mask_poly = domain.empty_coeff();
        mask_poly[0] = pallas::Base::from(5);

        let evaluated = super::EvaluatedQuotient::<vesta::Affine> {
            h_poly,
            h_blind: Blind(pallas::Base::from(7)),
            random_poly: super::CommittedRandomPolynomial {
                poly: mask_poly,
                blind: Blind(pallas::Base::from(11)),
            },
        };
        type MaskTranscript = Blake2bWrite<Vec<u8>, vesta::Affine, Challenge255<vesta::Affine>>;
        let mut transcript = MaskTranscript::init(Vec::new());
        let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();
        let queries = evaluated.open(x).collect::<Vec<_>>();

        assert_eq!(queries.len(), 2);
        assert!(core::ptr::eq(queries[0].poly, &evaluated.h_poly));
        assert!(core::ptr::eq(queries[1].poly, &evaluated.random_poly.poly));
    }

    #[test]
    fn sparse_commitment_matches_dense_pallas() {
        sparse_commitment_matches_dense::<pallas::Affine>();
    }

    #[test]
    fn sparse_commitment_matches_dense_vesta() {
        sparse_commitment_matches_dense::<vesta::Affine>();
    }

    #[test]
    fn quadratic_mask_has_excess_entropy_after_two_evaluations_fp() {
        quadratic_mask_has_excess_entropy_after_two_evaluations::<pallas::Base>();
    }

    #[test]
    fn quadratic_mask_has_excess_entropy_after_two_evaluations_fq() {
        quadratic_mask_has_excess_entropy_after_two_evaluations::<vesta::Base>();
    }
}
