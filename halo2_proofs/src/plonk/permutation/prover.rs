use group::{
    ff::{Field, PrimeField},
    Curve,
};
use rand_core::Rng;
use std::{convert::Infallible, iter};

use super::super::{circuit::Any, ChallengeBeta, ChallengeGamma, ChallengeX};
use super::{permutation_chunk_len, Argument, ProvingKey};
use crate::{
    arithmetic::{parallelize, CurveAffine},
    plonk::{
        self,
        evaluation::{EvaluationPoint, EvaluationQuery, PolynomialEvaluator},
        Error,
    },
    poly::{
        self,
        commitment::{Blind, Params},
        multiopen::ProverQuery,
        Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation,
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
            // Goal is to compute the products of fractions
            //
            // (p_j(\omega^i) + \delta^j \omega^i \beta + \gamma) /
            // (p_j(\omega^i) + \beta s_j(\omega^i) + \gamma)
            //
            // where p_j(X) is the jth column in this permutation,
            // and i is the ith row of the column.

            let mut modified_values = vec![C::Scalar::ONE; params.n as usize];

            // Iterate over each column of the permutation
            for (&column, permuted_column_values) in columns.iter().zip(permutations.iter()) {
                let values = match column.column_type() {
                    Any::Advice => advice,
                    Any::Fixed => fixed,
                    Any::Instance => instance,
                };
                parallelize(&mut modified_values, |modified_values, start| {
                    for ((modified_values, value), permuted_value) in modified_values
                        .iter_mut()
                        .zip(values[column.index()][start..].iter())
                        .zip(permuted_column_values[start..].iter())
                    {
                        *modified_values *= &(*beta * permuted_value + &*gamma + value);
                    }
                });
            }

            // Invert to obtain the denominator for the permutation product polynomial
            crate::arithmetic::batch_invert_multi(&mut modified_values);

            // Iterate over each column again, this time finishing the computation
            // of the entire fraction by computing the numerators
            for &column in columns.iter() {
                let omega = domain.get_omega();
                let values = match column.column_type() {
                    Any::Advice => advice,
                    Any::Fixed => fixed,
                    Any::Instance => instance,
                };
                parallelize(&mut modified_values, |modified_values, start| {
                    let mut deltaomega = deltaomega * &omega.pow_vartime([start as u64]);
                    for (modified_values, value) in modified_values
                        .iter_mut()
                        .zip(values[column.index()][start..].iter())
                    {
                        // Multiply by p_j(\omega^i) + \delta^j \omega^i \beta
                        *modified_values *= &(deltaomega * &*beta + &*gamma + value);
                        deltaomega *= &omega;
                    }
                });
                deltaomega *= &C::Scalar::DELTA;
            }

            // The modified_values vector is a vector of products of fractions
            // of the form
            //
            // (p_j(\omega^i) + \delta^j \omega^i \beta + \gamma) /
            // (p_j(\omega^i) + \beta s_j(\omega^i) + \gamma)
            //
            // where i is the index into modified_values, for the jth column in
            // the permutation

            // Compute the evaluations of the permutation product polynomial
            // over our domain, starting with z[0] = 1
            let mut z = vec![last_z];
            for row in 1..(params.n as usize) {
                let mut tmp = z[row - 1];

                tmp *= &modified_values[row - 1];
                z.push(tmp);
            }
            let mut z = domain.lagrange_from_vec(z);
            // Set blinding factors
            let blind = set_blinding(&mut z[params.n as usize - blinding_factors..]);
            // Set new last_z
            last_z = z[params.n as usize - (blinding_factors + 1)];

            let (permutation_product_commitment_projective, (permutation_product_poly, coset)) =
                crate::multicore::join(
                    || params.commit_lagrange(&z, blind),
                    || {
                        let z = domain.lagrange_to_coeff_with_twiddles(z.clone(), &pk.fft_twiddles);
                        let coset =
                            domain.coeff_to_extended_with_twiddles(z.clone(), &pk.fft_twiddles);
                        (z, coset)
                    },
                );
            let permutation_product_blind = blind;
            let permutation_product_commitment =
                permutation_product_commitment_projective.to_affine();

            finish_set(PreparedSet {
                permutation_product_poly,
                permutation_product_coset: coset,
                permutation_product_commitment,
                permutation_product_blind,
            })?;
        }

        Ok(())
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

    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        &self,
        evaluator: &PolynomialEvaluator<C::Scalar>,
        transcript: &mut T,
    ) -> Result<(), Error> {
        // Hash permutation evals
        let queries = self
            .polys
            .iter()
            .map(|polynomial| EvaluationQuery {
                polynomial,
                point: EvaluationPoint::Current,
            })
            .collect::<Vec<_>>();
        for eval in evaluator.evaluate(&queries) {
            transcript.write_scalar(eval)?;
        }

        Ok(())
    }
}

impl<C: CurveAffine> Constructed<C> {
    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        evaluator: &PolynomialEvaluator<C::Scalar>,
        transcript: &mut T,
    ) -> Result<Evaluated<C>, Error> {
        let mut queries = Vec::with_capacity(self.sets.len() * 3);
        for (index, set) in self.sets.iter().enumerate() {
            queries.push(EvaluationQuery {
                polynomial: &set.permutation_product_poly,
                point: EvaluationPoint::Current,
            });
            queries.push(EvaluationQuery {
                polynomial: &set.permutation_product_poly,
                point: EvaluationPoint::Next,
            });
            if index + 1 < self.sets.len() {
                queries.push(EvaluationQuery {
                    polynomial: &set.permutation_product_poly,
                    point: EvaluationPoint::Last,
                });
            }
        }
        for evaluation in evaluator.evaluate(&queries) {
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
            create_proof, keygen_pk, keygen_vk, Advice, Circuit, Column, ConstraintSystem, Error,
        },
        poly::commitment::Params,
        transcript::{Blake2bWrite, Challenge255},
    };
    use pasta_curves::{EqAffine, Fp};
    use rand::{rngs::StdRng, SeedableRng};

    const EQUALITY_COLUMNS: usize = 3;
    const PROOF_CIRCUITS: usize = 4;
    const PARALLEL_THREADS: usize = 8;
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

        let circuits: [PermutationCircuit; PROOF_CIRCUITS] =
            std::array::from_fn(|index| PermutationCircuit {
                value: Fp::from(index as u64 + 1),
            });
        let no_instance_columns: &[&[Fp]] = &[];
        let instances = [no_instance_columns; PROOF_CIRCUITS];

        let prove = |threads| {
            let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
            maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap()
                .install(|| {
                    create_proof(
                        &params,
                        &pk,
                        &circuits,
                        &instances,
                        StdRng::seed_from_u64(PROOF_SEED),
                        &mut transcript,
                    )
                })
                .expect("proof generation should not fail");
            transcript.finalize()
        };

        assert_eq!(prove(1), prove(PARALLEL_THREADS));
    }
}
