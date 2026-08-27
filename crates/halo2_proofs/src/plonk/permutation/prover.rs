use group::{
    Curve,
    ff::{Field, PrimeField},
};
use maybe_rayon::prelude::*;
use rand_core::Rng;
use std::{convert::Infallible, iter};

use super::super::{ChallengeBeta, ChallengeGamma, ChallengeX, circuit::Any};
use super::{Argument, ProvingKey, permutation_chunk_len};
use crate::{
    arithmetic::{CurveAffine, parallelize},
    plonk::{
        self, Error,
        evaluation::{EvaluationPoint, EvaluationQuery},
    },
    poly::{
        self, Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation,
        commitment::{Blind, Params},
        multiopen::ProverQuery,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};

pub struct CommittedSet<C: CurveAffine, Ev> {
    permutation_product_poly: Polynomial<C::Scalar, Coeff>,
    permutation_product_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    permutation_product_blind: Blind<C::Scalar>,
}

pub(crate) struct Committed<C: CurveAffine, Ev> {
    sets: Vec<CommittedSet<C, Ev>>,
}

struct SetBlinding<F: Field> {
    rows: Vec<F>,
    product_blind: Blind<F>,
}

struct PreparedRatios<F: Field> {
    values: Vec<F>,
    blinding: SetBlinding<F>,
}

struct UntransformedSet<F: Field> {
    product: Polynomial<F, LagrangeCoeff>,
    product_blind: Blind<F>,
}

pub(in crate::plonk) struct PermutationBlinding<F: Field> {
    sets: Vec<SetBlinding<F>>,
}

struct PreparedSet<C: CurveAffine> {
    permutation_product_poly: Polynomial<C::Scalar, Coeff>,
    permutation_product_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    permutation_product_commitment: C,
    permutation_product_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) struct Prepared<C: CurveAffine> {
    sets: Vec<PreparedSet<C>>,
}

pub struct ConstructedSet<C: CurveAffine> {
    permutation_product_poly: Polynomial<C::Scalar, Coeff>,
    permutation_product_blind: Blind<C::Scalar>,
}

pub(crate) struct Constructed<C: CurveAffine> {
    sets: Vec<ConstructedSet<C>>,
}

pub(crate) struct Evaluated<C: CurveAffine> {
    constructed: Constructed<C>,
}

impl Argument {
    pub(in crate::plonk) fn sample_blinding<C: CurveAffine, R: Rng>(
        &self,
        pk: &plonk::ProvingKey<C>,
        mut rng: R,
    ) -> PermutationBlinding<C::Scalar> {
        let chunk_len = permutation_chunk_len(pk.vk.cs_degree);
        let blinding_factors = pk.vk.cs.blinding_factors();

        PermutationBlinding {
            sets: self
                .columns
                .chunks(chunk_len)
                .map(|_| SetBlinding {
                    rows: (0..blinding_factors)
                        .map(|_| C::Scalar::random(&mut rng))
                        .collect(),
                    product_blind: Blind(C::Scalar::random(&mut rng)),
                })
                .collect(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn commit<
        C: CurveAffine,
        E: EncodedChallenge<C>,
        Ev: Copy + Send + Sync,
        R: Rng,
        T: TranscriptWrite<C, E>,
    >(
        &self,
        params: &Params<C>,
        pk: &plonk::ProvingKey<C>,
        pkey: &ProvingKey<C>,
        advice: &[Polynomial<C::Scalar, LagrangeCoeff>],
        fixed: &[Polynomial<C::Scalar, LagrangeCoeff>],
        instance: &[Polynomial<C::Scalar, LagrangeCoeff>],
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        evaluator: &mut poly::Evaluator<Ev, C::Scalar, ExtendedLagrangeCoeff>,
        mut rng: R,
        transcript: &mut T,
    ) -> Result<Committed<C, Ev>, Error> {
        let mut sets = vec![];
        self.prepare_sets(
            params,
            pk,
            pkey,
            advice,
            fixed,
            instance,
            beta,
            gamma,
            |rows| {
                for z in rows {
                    *z = C::Scalar::random(&mut rng);
                }
                Blind(C::Scalar::random(&mut rng))
            },
            |set| {
                let permutation_product_coset =
                    evaluator.register_poly(set.permutation_product_coset);

                // Hash the permutation product commitment
                transcript.write_point(set.permutation_product_commitment)?;

                sets.push(CommittedSet {
                    permutation_product_poly: set.permutation_product_poly,
                    permutation_product_coset,
                    permutation_product_blind: set.permutation_product_blind,
                });
                Ok::<(), Error>(())
            },
        )?;

        Ok(Committed { sets })
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn prepare<C: CurveAffine>(
        &self,
        params: &Params<C>,
        pk: &plonk::ProvingKey<C>,
        pkey: &ProvingKey<C>,
        advice: &[Polynomial<C::Scalar, LagrangeCoeff>],
        fixed: &[Polynomial<C::Scalar, LagrangeCoeff>],
        instance: &[Polynomial<C::Scalar, LagrangeCoeff>],
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        blinding: PermutationBlinding<C::Scalar>,
    ) -> Prepared<C> {
        let mut blindings = blinding.sets.into_iter();
        let mut sets = Vec::with_capacity(blindings.len());
        let result: Result<(), Infallible> = self.prepare_sets(
            params,
            pk,
            pkey,
            advice,
            fixed,
            instance,
            beta,
            gamma,
            |rows| {
                let blinding = blindings
                    .next()
                    .expect("one blinding value set is sampled per permutation set");
                rows.copy_from_slice(&blinding.rows);
                blinding.product_blind
            },
            |set| {
                sets.push(set);
                Ok(())
            },
        );
        result.unwrap_or_else(|never| match never {});

        Prepared { sets }
    }

    /// Prepares one circuit's permutation sets concurrently without mutating
    /// the transcript or the shared polynomial evaluator.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn prepare_sets_in_parallel<C: CurveAffine>(
        &self,
        params: &Params<C>,
        pk: &plonk::ProvingKey<C>,
        pkey: &ProvingKey<C>,
        advice: &[Polynomial<C::Scalar, LagrangeCoeff>],
        fixed: &[Polynomial<C::Scalar, LagrangeCoeff>],
        instance: &[Polynomial<C::Scalar, LagrangeCoeff>],
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        blinding: PermutationBlinding<C::Scalar>,
    ) -> Prepared<C> {
        if blinding.sets.len() <= 1 {
            return self.prepare(
                params, pk, pkey, advice, fixed, instance, beta, gamma, blinding,
            );
        }

        let domain = &pk.vk.domain;
        let chunk_len = permutation_chunk_len(pk.vk.cs_degree);
        let blinding_factors = pk.vk.cs.blinding_factors();

        // Record the initial delta power for each set. The numerator ratios
        // are then independent across sets.
        let mut deltaomega = C::Scalar::ONE;
        let set_inputs = self
            .columns
            .chunks(chunk_len)
            .zip(pkey.permutations.chunks(chunk_len))
            .map(|(columns, permutations)| {
                let initial_deltaomega = deltaomega;
                for _ in columns {
                    deltaomega *= &C::Scalar::DELTA;
                }
                (columns, permutations, initial_deltaomega)
            })
            .collect::<Vec<_>>();
        assert_eq!(set_inputs.len(), blinding.sets.len());

        // Indexed collection preserves set order for the dependent prefix
        // chain and eventual transcript writes.
        let prepared_ratios = set_inputs
            .into_par_iter()
            .zip(blinding.sets.into_par_iter())
            .map(
                |((columns, permutations, initial_deltaomega), blinding)| PreparedRatios {
                    values: prepare_ratios(
                        params,
                        domain,
                        columns,
                        permutations,
                        advice,
                        fixed,
                        instance,
                        beta,
                        gamma,
                        initial_deltaomega,
                    )
                    .0,
                    blinding,
                },
            )
            .collect::<Vec<_>>();

        // Each set starts with the preceding set's final product, so this
        // short prefix chain remains serial.
        let mut last_z = C::Scalar::ONE;
        let products = prepared_ratios
            .into_iter()
            .map(|prepared| {
                let blinding = prepared.blinding;
                build_product::<C>(
                    domain,
                    blinding_factors,
                    &mut last_z,
                    prepared.values,
                    |rows| {
                        rows.copy_from_slice(&blinding.rows);
                        blinding.product_blind
                    },
                )
            })
            .collect::<Vec<_>>();

        let sets = products
            .into_par_iter()
            .map(|set| prepare_product(params, pk, set))
            .collect();

        Prepared { sets }
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare_sets<C: CurveAffine, E>(
        &self,
        params: &Params<C>,
        pk: &plonk::ProvingKey<C>,
        pkey: &ProvingKey<C>,
        advice: &[Polynomial<C::Scalar, LagrangeCoeff>],
        fixed: &[Polynomial<C::Scalar, LagrangeCoeff>],
        instance: &[Polynomial<C::Scalar, LagrangeCoeff>],
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        mut set_blinding: impl FnMut(&mut [C::Scalar]) -> Blind<C::Scalar>,
        mut finish_set: impl FnMut(PreparedSet<C>) -> Result<(), E>,
    ) -> Result<(), E> {
        let domain = &pk.vk.domain;

        // How many columns can be included in a single permutation polynomial?
        // We need to multiply by z(X) and (1 - (l_last(X) + l_blind(X))). This
        // will never underflow because of the requirement of at least a degree
        // 3 circuit for the permutation argument.
        let chunk_len = permutation_chunk_len(pk.vk.cs_degree);
        let blinding_factors = pk.vk.cs.blinding_factors();

        // Each column gets its own delta power.
        let mut deltaomega = C::Scalar::ONE;

        // Track the "last" value from the previous column set
        let mut last_z = C::Scalar::ONE;

        for (columns, permutations) in self
            .columns
            .chunks(chunk_len)
            .zip(pkey.permutations.chunks(chunk_len))
        {
            let (ratios, next_deltaomega) = prepare_ratios(
                params,
                domain,
                columns,
                permutations,
                advice,
                fixed,
                instance,
                beta,
                gamma,
                deltaomega,
            );
            deltaomega = next_deltaomega;
            let product =
                build_product::<C>(domain, blinding_factors, &mut last_z, ratios, |rows| {
                    set_blinding(rows)
                });
            finish_set(prepare_product(params, pk, product))?;
        }

        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
fn prepare_ratios<C: CurveAffine>(
    params: &Params<C>,
    domain: &poly::EvaluationDomain<C::Scalar>,
    columns: &[plonk::Column<Any>],
    permutations: &[Polynomial<C::Scalar, LagrangeCoeff>],
    advice: &[Polynomial<C::Scalar, LagrangeCoeff>],
    fixed: &[Polynomial<C::Scalar, LagrangeCoeff>],
    instance: &[Polynomial<C::Scalar, LagrangeCoeff>],
    beta: ChallengeBeta<C>,
    gamma: ChallengeGamma<C>,
    mut deltaomega: C::Scalar,
) -> (Vec<C::Scalar>, C::Scalar) {
    let mut ratios = vec![C::Scalar::ONE; params.n as usize];

    // Compute the product of denominators for this permutation set.
    for (&column, permuted_column_values) in columns.iter().zip(permutations.iter()) {
        let values = match column.column_type() {
            Any::Advice => advice,
            Any::Fixed => fixed,
            Any::Instance => instance,
        };
        parallelize(&mut ratios, |ratios, start| {
            for ((ratio, value), permuted_value) in ratios
                .iter_mut()
                .zip(values[column.index()][start..].iter())
                .zip(permuted_column_values[start..].iter())
            {
                *ratio *= &(*beta * permuted_value + &*gamma + value);
            }
        });
    }

    crate::arithmetic::batch_invert_multi(&mut ratios);

    // Multiply by the product of numerators for this permutation set.
    for &column in columns {
        let omega = domain.get_omega();
        let values = match column.column_type() {
            Any::Advice => advice,
            Any::Fixed => fixed,
            Any::Instance => instance,
        };
        parallelize(&mut ratios, |ratios, start| {
            let mut row_deltaomega = deltaomega * &omega.pow_vartime([start as u64]);
            for (ratio, value) in ratios
                .iter_mut()
                .zip(values[column.index()][start..].iter())
            {
                *ratio *= &(row_deltaomega * &*beta + &*gamma + value);
                row_deltaomega *= &omega;
            }
        });
        deltaomega *= &C::Scalar::DELTA;
    }

    (ratios, deltaomega)
}

fn build_product<C: CurveAffine>(
    domain: &poly::EvaluationDomain<C::Scalar>,
    blinding_factors: usize,
    last_z: &mut C::Scalar,
    mut ratios: Vec<C::Scalar>,
    set_blinding: impl FnOnce(&mut [C::Scalar]) -> Blind<C::Scalar>,
) -> UntransformedSet<C::Scalar> {
    let usable_rows = ratios.len() - blinding_factors;
    let mut state = *last_z;
    let (last, prefix) = ratios[..usable_rows]
        .split_last_mut()
        .expect("the usable evaluation domain is non-empty");
    for value in prefix {
        let current = *value;
        *value = state;
        state *= &current;
    }
    *last = state;

    let mut product = domain.lagrange_from_vec(ratios);
    let product_blind = set_blinding(&mut product[usable_rows..]);
    *last_z = product[usable_rows - 1];

    UntransformedSet {
        product,
        product_blind,
    }
}

fn prepare_product<C: CurveAffine>(
    params: &Params<C>,
    pk: &plonk::ProvingKey<C>,
    set: UntransformedSet<C::Scalar>,
) -> PreparedSet<C> {
    let blind = set.product_blind;
    let z = set.product;
    let (commitment, (polynomial, coset)) = crate::multicore::join(
        || params.commit_lagrange(&z, blind),
        || {
            let polynomial = pk
                .vk
                .domain
                .lagrange_to_coeff_with_twiddles(z.clone(), &pk.fft_twiddles);
            let coset = pk
                .vk
                .domain
                .coeff_to_extended_with_twiddles(polynomial.clone(), &pk.fft_twiddles);
            (polynomial, coset)
        },
    );

    PreparedSet {
        permutation_product_poly: polynomial,
        permutation_product_coset: coset,
        permutation_product_commitment: commitment.to_affine(),
        permutation_product_blind: blind,
    }
}

impl<C: CurveAffine> Prepared<C> {
    pub(in crate::plonk) fn commit<
        E: EncodedChallenge<C>,
        Ev: Copy + Send + Sync,
        T: TranscriptWrite<C, E>,
    >(
        self,
        evaluator: &mut poly::Evaluator<Ev, C::Scalar, ExtendedLagrangeCoeff>,
        transcript: &mut T,
    ) -> Result<Committed<C, Ev>, Error> {
        let mut sets = Vec::with_capacity(self.sets.len());
        for set in self.sets {
            let permutation_product_coset = evaluator.register_poly(set.permutation_product_coset);

            // Hash the permutation product commitment
            transcript.write_point(set.permutation_product_commitment)?;

            sets.push(CommittedSet {
                permutation_product_poly: set.permutation_product_poly,
                permutation_product_coset,
                permutation_product_blind: set.permutation_product_blind,
            });
        }

        Ok(Committed { sets })
    }
}

impl<C: CurveAffine, Ev: Copy + Send + Sync> Committed<C, Ev> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn construct<'a>(
        self,
        pk: &'a plonk::ProvingKey<C>,
        p: &'a Argument,
        advice_cosets: &'a [poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        fixed_cosets: &'a [poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        instance_cosets: &'a [poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        permutation_cosets: &'a [poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        l0: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
        l_blind: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
        l_last: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
    ) -> (
        Constructed<C>,
        impl Iterator<Item = poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>> + 'a,
    ) {
        let chunk_len = permutation_chunk_len(pk.vk.cs_degree);
        let blinding_factors = pk.vk.cs.blinding_factors();
        let last_rotation = Rotation(-((blinding_factors + 1) as i32));

        let constructed = Constructed {
            sets: self
                .sets
                .iter()
                .map(|set| ConstructedSet {
                    permutation_product_poly: set.permutation_product_poly.clone(),
                    permutation_product_blind: set.permutation_product_blind,
                })
                .collect(),
        };

        let expressions = iter::empty()
            // Enforce only for the first set.
            // l_0(X) * (1 - z_0(X)) = 0
            .chain(
                self.sets
                    .first()
                    .map(|first_set| (poly::Ast::one() - first_set.permutation_product_coset) * l0),
            )
            // Enforce only for the last set.
            // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
            .chain(self.sets.last().map(|last_set| {
                ((poly::Ast::from(last_set.permutation_product_coset)
                    * last_set.permutation_product_coset)
                    - last_set.permutation_product_coset)
                    * l_last
            }))
            // Except for the first set, enforce.
            // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
            .chain(
                self.sets
                    .iter()
                    .skip(1)
                    .zip(self.sets.iter())
                    .map(|(set, last_set)| {
                        (poly::Ast::from(set.permutation_product_coset)
                            - last_set
                                .permutation_product_coset
                                .with_rotation(last_rotation))
                            * l0
                    })
                    .collect::<Vec<_>>(),
            )
            // And for all the sets we enforce:
            // (1 - (l_last(X) + l_blind(X))) * (
            //   z_i(\omega X) \prod_j (p(X) + \beta s_j(X) + \gamma)
            // - z_i(X) \prod_j (p(X) + \delta^j \beta X + \gamma)
            // )
            .chain(
                self.sets
                    .into_iter()
                    .zip(p.columns.chunks(chunk_len))
                    .zip(permutation_cosets.chunks(chunk_len))
                    .enumerate()
                    .map(move |(chunk_index, ((set, columns), cosets))| {
                        let mut left = poly::Ast::<_, C::Scalar, _>::from(
                            set.permutation_product_coset
                                .with_rotation(Rotation::next()),
                        );
                        for (values, permutation) in columns
                            .iter()
                            .map(|&column| match column.column_type() {
                                Any::Advice => &advice_cosets[column.index()],
                                Any::Fixed => &fixed_cosets[column.index()],
                                Any::Instance => &instance_cosets[column.index()],
                            })
                            .zip(cosets.iter())
                        {
                            left *= poly::Ast::<_, C::Scalar, _>::from(*values)
                                + (poly::Ast::ConstantTerm(*beta) * poly::Ast::from(*permutation))
                                + poly::Ast::ConstantTerm(*gamma);
                        }

                        let mut right = poly::Ast::from(set.permutation_product_coset);
                        let mut current_delta = *beta
                            * &(C::Scalar::DELTA.pow_vartime([(chunk_index * chunk_len) as u64]));
                        for values in columns.iter().map(|&column| match column.column_type() {
                            Any::Advice => &advice_cosets[column.index()],
                            Any::Fixed => &fixed_cosets[column.index()],
                            Any::Instance => &instance_cosets[column.index()],
                        }) {
                            right *= poly::Ast::from(*values)
                                + poly::Ast::LinearTerm(current_delta)
                                + poly::Ast::ConstantTerm(*gamma);
                            current_delta *= &C::Scalar::DELTA;
                        }

                        (left - right) * (poly::Ast::one() - (poly::Ast::from(l_last) + l_blind))
                    }),
            );

        (constructed, expressions)
    }
}

impl<C: CurveAffine> super::ProvingKey<C> {
    pub(in crate::plonk) fn open(
        &self,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = ProverQuery<'_, C>> + Clone {
        self.polys.iter().map(move |poly| ProverQuery {
            point: *x,
            poly,
            blind: Blind::default(),
        })
    }

    pub(in crate::plonk) fn evaluation_queries(
        &self,
    ) -> impl Iterator<Item = EvaluationQuery<'_, C::Scalar>> {
        self.polys.iter().map(|polynomial| EvaluationQuery {
            polynomial,
            point: EvaluationPoint::Current,
        })
    }

    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        &self,
        evaluations: &mut impl Iterator<Item = C::Scalar>,
        transcript: &mut T,
    ) -> Result<(), Error> {
        // Hash permutation evals
        for _ in &self.polys {
            let eval = evaluations
                .next()
                .expect("one result is returned for every permutation-key evaluation query");
            transcript.write_scalar(eval)?;
        }

        Ok(())
    }
}

impl<C: CurveAffine> Constructed<C> {
    pub(in crate::plonk) fn evaluation_queries(
        &self,
    ) -> impl Iterator<Item = EvaluationQuery<'_, C::Scalar>> {
        self.sets.iter().enumerate().flat_map(|(index, set)| {
            [
                Some(EvaluationQuery {
                    polynomial: &set.permutation_product_poly,
                    point: EvaluationPoint::Current,
                }),
                Some(EvaluationQuery {
                    polynomial: &set.permutation_product_poly,
                    point: EvaluationPoint::Next,
                }),
                (index + 1 < self.sets.len()).then_some(EvaluationQuery {
                    polynomial: &set.permutation_product_poly,
                    point: EvaluationPoint::Last,
                }),
            ]
            .into_iter()
            .flatten()
        })
    }

    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        evaluations: &mut impl Iterator<Item = C::Scalar>,
        transcript: &mut T,
    ) -> Result<Evaluated<C>, Error> {
        let evaluation_count = self.evaluation_queries().count();
        for _ in 0..evaluation_count {
            let evaluation = evaluations
                .next()
                .expect("one result is returned for every permutation evaluation query");
            transcript.write_scalar(evaluation)?;
        }

        Ok(Evaluated { constructed: self })
    }
}

impl<C: CurveAffine> Evaluated<C> {
    pub(in crate::plonk) fn open<'a>(
        &'a self,
        pk: &'a plonk::ProvingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = ProverQuery<'a, C>> + Clone {
        let blinding_factors = pk.vk.cs.blinding_factors();
        let x_next = pk.vk.domain.rotate_omega(*x, Rotation::next());
        let x_last = pk
            .vk
            .domain
            .rotate_omega(*x, Rotation(-((blinding_factors + 1) as i32)));

        iter::empty()
            .chain(self.constructed.sets.iter().flat_map(move |set| {
                iter::empty()
                    // Open permutation product commitments at x and \omega x
                    .chain(Some(ProverQuery {
                        point: *x,
                        poly: &set.permutation_product_poly,
                        blind: set.permutation_product_blind,
                    }))
                    .chain(Some(ProverQuery {
                        point: x_next,
                        poly: &set.permutation_product_poly,
                        blind: set.permutation_product_blind,
                    }))
            }))
            // Open it at \omega^{last} x for all but the last set. This rotation is only
            // sensical for the first row, but we only use this rotation in a constraint
            // that is gated on l_0.
            .chain(
                self.constructed
                    .sets
                    .iter()
                    .rev()
                    .skip(1)
                    .flat_map(move |set| {
                        Some(ProverQuery {
                            point: x_last,
                            poly: &set.permutation_product_poly,
                            blind: set.permutation_product_blind,
                        })
                    }),
            )
    }
}

#[cfg(all(test, feature = "multicore"))]
mod tests {
    use super::permutation_chunk_len;
    use crate::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error, create_proof, keygen_pk, keygen_vk,
        },
        poly::commitment::Params,
        transcript::{Blake2bWrite, Challenge255},
    };
    use pasta_curves::{EqAffine, Fp};
    use rand::{SeedableRng, rngs::StdRng};

    const EQUALITY_COLUMNS: usize = 3;
    const MAX_PROOF_CIRCUITS: usize = 4;
    const PROOF_CIRCUIT_COUNTS: [usize; 3] = [1, 2, MAX_PROOF_CIRCUITS];
    const PROOF_THREAD_COUNTS: [usize; 2] = [6, 10];
    const PROOF_SEED: u64 = 0x5045_524d_5554_4508;

    #[derive(Clone, Copy)]
    struct PermutationConfig {
        columns: [Column<Advice>; EQUALITY_COLUMNS],
    }

    #[derive(Clone, Copy)]
    struct PermutationCircuit {
        value: Fp,
    }

    impl Circuit<Fp> for PermutationCircuit {
        type Config = PermutationConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self { value: Fp::from(0) }
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            let columns = std::array::from_fn(|_| meta.advice_column());
            for column in columns.iter().copied() {
                meta.enable_equality(column);
            }
            PermutationConfig { columns }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "permutation copies",
                |mut region| {
                    let mut cells = Vec::with_capacity(EQUALITY_COLUMNS);
                    for (offset, column) in config.columns.iter().enumerate() {
                        cells.push(
                            region
                                .assign_advice(
                                    || "value",
                                    *column,
                                    offset,
                                    || Value::known(self.value),
                                )?
                                .cell(),
                        );
                    }
                    for cells in cells.windows(2) {
                        region.constrain_equal(cells[0], cells[1])?;
                    }
                    Ok(())
                },
            )
        }
    }

    #[test]
    fn proof_bytes_match_across_permutation_preparation_schedules() {
        let params: Params<EqAffine> = Params::new(4);
        let circuit = PermutationCircuit { value: Fp::from(0) };
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");

        let columns = pk.vk.cs.permutation.get_columns();
        assert_eq!(columns.len(), EQUALITY_COLUMNS);
        assert!(
            columns
                .chunks(permutation_chunk_len(pk.vk.cs_degree))
                .count()
                > 1
        );

        let circuits: [PermutationCircuit; MAX_PROOF_CIRCUITS] =
            std::array::from_fn(|index| PermutationCircuit {
                value: Fp::from(index as u64 + 1),
            });
        let no_instance_columns: &[&[Fp]] = &[];
        let instances = [no_instance_columns; MAX_PROOF_CIRCUITS];

        let prove = |circuit_count, threads| {
            let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
            maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap()
                .install(|| {
                    create_proof(
                        &params,
                        &pk,
                        &circuits[..circuit_count],
                        &instances[..circuit_count],
                        StdRng::seed_from_u64(PROOF_SEED),
                        &mut transcript,
                    )
                })
                .expect("proof generation should not fail");
            transcript.finalize()
        };

        for circuit_count in PROOF_CIRCUIT_COUNTS {
            let serial = prove(circuit_count, 1);
            for threads in PROOF_THREAD_COUNTS {
                assert_eq!(serial, prove(circuit_count, threads));
            }
        }
    }
}
