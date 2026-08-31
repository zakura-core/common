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
        cache_layout: Option<&poly::EvaluationCacheLayout>,
        mut rng: R,
        transcript: &mut T,
    ) -> Result<(ConstructedQuotient<C>, Option<poly::EvaluationCacheLayout>), Error> {
        // Fold the constraint expressions into the quotient numerator using
        // the y challenge, then evaluate the numerator.
        let quotient_numerator = poly::Ast::distribute_powers(expressions, *y);
        let (quotient_numerator, prepared_layout) =
            evaluator.evaluate_with_cache_layout(&quotient_numerator, domain, cache_layout);

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
            prepared_layout,
        ))
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
    use ff::WithSmallOrderMulGroup;
    use pasta_curves::{Fp, Fq};

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
}
