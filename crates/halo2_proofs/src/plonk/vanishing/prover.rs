use std::iter;

use ff::{Field, WithSmallOrderMulGroup};
use group::Curve;
#[cfg(feature = "multicore")]
use maybe_rayon::prelude::*;
use rand_core::Rng;

use super::Argument;
use crate::{
    arithmetic::{CurveAffine, parallelize},
    plonk::{
        ChallengeX, ChallengeY, Error,
        evaluation::{EvaluationPoint, EvaluationQuery},
    },
    poly::{
        self, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, Polynomial, ProvingKeyTwiddles,
        commitment::{Blind, Params},
        multiopen::ProverQuery,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};

fn fold_quotient_pieces<F: WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    mut pieces: Vec<Polynomial<F, Coeff>>,
    xn: F,
) -> Polynomial<F, Coeff> {
    // Pieces are ordered from least to most significant. Move the highest
    // allocation into the accumulator, then consume the rest in Horner order.
    let Some(mut accumulator) = pieces.pop() else {
        return domain.empty_coeff();
    };

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
    /// evaluation in the multiopening argument.
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
        // Sample a random polynomial of degree n - 1
        let mut random_poly = domain.empty_coeff();
        for coeff in random_poly.iter_mut() {
            *coeff = C::Scalar::random(&mut rng);
        }
        // Sample a random blinding factor
        let random_blind = Blind(C::Scalar::random(&mut rng));

        // Commit
        let random_poly_commitment = params.commit(&random_poly, random_blind).to_affine();
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
        y: ChallengeY<C>,
        mut rng: R,
        transcript: &mut T,
    ) -> Result<ConstructedQuotient<C>, Error> {
        // Fold the constraint expressions into the quotient numerator using
        // the y challenge, then evaluate the numerator.
        let quotient_numerator = poly::Ast::distribute_powers(expressions, *y);
        let quotient_numerator = evaluator.evaluate(&quotient_numerator, domain);

        // Divide by t(X) = X^{params.n} - 1.
        let h_poly = domain.divide_by_vanishing_poly(quotient_numerator);

        // Obtain the quotient polynomial h(X).
        let h_poly = domain.extended_to_coeff_with_twiddles(h_poly, fft_twiddles);

        // Split h(X) up into pieces
        let h_pieces = h_poly
            .chunks_exact(params.n as usize)
            .map(|v| domain.coeff_from_vec(v.to_vec()))
            .collect::<Vec<_>>();
        drop(h_poly);
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

        Ok(ConstructedQuotient {
            h_pieces,
            h_blinds,
            random_poly: self,
        })
    }
}

impl<C: CurveAffine> ConstructedQuotient<C> {
    pub(in crate::plonk) fn evaluation_query(&self) -> EvaluationQuery<'_, C::Scalar> {
        EvaluationQuery {
            polynomial: &self.random_poly.poly,
            point: EvaluationPoint::Current,
        }
    }

    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        xn: C::Scalar,
        domain: &EvaluationDomain<C::Scalar>,
        random_eval: C::Scalar,
        transcript: &mut T,
    ) -> Result<EvaluatedQuotient<C>, Error> {
        let h_poly = fold_quotient_pieces(domain, self.h_pieces, xn);

        let h_blind = self
            .h_blinds
            .iter()
            .rev()
            .fold(Blind(C::Scalar::ZERO), |acc, eval| acc * Blind(xn) + *eval);

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
    use super::fold_quotient_pieces;
    use crate::poly::{Coeff, EvaluationDomain, Polynomial};
    use ff::{Field, WithSmallOrderMulGroup};
    use pasta_curves::Fp;

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

    #[test]
    fn quotient_piece_fold_matches_allocating_horner_fold() {
        let domain = EvaluationDomain::new(3, 3);
        let domain_size = domain.empty_coeff().len();

        for piece_count in 0..=4 {
            for xn in [Fp::ZERO, Fp::ONE, Fp::from(7)] {
                let pieces = (0..piece_count)
                    .map(|piece| {
                        domain.coeff_from_vec(
                            (0..domain_size)
                                .map(|coefficient| Fp::from((piece * 17 + coefficient + 1) as u64))
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
}
