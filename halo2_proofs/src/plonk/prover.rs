use ff::Field;
use group::Curve;
use rand_core::Rng;
use std::iter;
use std::ops::RangeTo;

use super::{
    circuit::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Fixed, FloorPlanner, Instance,
        Selector,
    },
    commit_instance,
    evaluation::{EvaluationPoint, EvaluationQuery, PolynomialEvaluator},
    lookup, permutation, vanishing, ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX,
    ChallengeY, Error, ProvingKey,
};
use crate::{
    arithmetic::CurveAffine,
    circuit::Value,
    plonk::Assigned,
    poly::{
        self,
        commitment::{Blind, Params},
        multiopen::{self, ProverQuery},
        Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial,
    },
};
use crate::{
    poly::batch_invert_assigned,
    transcript::{EncodedChallenge, TranscriptWrite},
};

struct WitnessCollection<'a, F: Field> {
    k: u32,
    advice: Vec<Polynomial<Assigned<F>, LagrangeCoeff>>,
    instances: &'a [&'a [F]],
    usable_rows: RangeTo<usize>,
    _marker: std::marker::PhantomData<F>,
}

impl<'a, F: Field> Assignment<F> for WitnessCollection<'a, F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // We only care about advice columns here.
        Ok(())
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.instances
            .get(column.index())
            .and_then(|column| column.get(row))
            .map(|v| Value::known(*v))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        *self
            .advice
            .get_mut(column.index())
            .and_then(|values| values.get_mut(row))
            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Fixed>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // We only care about advice columns here.
        Ok(())
    }

    fn copy(&mut self, _: Column<Any>, _: usize, _: Column<Any>, _: usize) -> Result<(), Error> {
        // We only care about advice columns here.
        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
///
/// Every element of `circuits` must have the circuit shape used to generate
/// `pk`.
pub fn create_proof<
    C: CurveAffine,
    E: EncodedChallenge<C>,
    R: Rng,
    T: TranscriptWrite<C, E>,
    ConcreteCircuit: Circuit<C::Scalar>,
>(
    params: &Params<C>,
    pk: &ProvingKey<C>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[C::Scalar]]],
    mut rng: R,
    transcript: &mut T,
) -> Result<(), Error> {
    if circuits.len() != instances.len() {
        return Err(Error::InvalidInstances);
    }

    for instance in instances.iter() {
        if instance.len() != pk.vk.cs.num_instance_columns {
            return Err(Error::InvalidInstances);
        }
    }

    // Hash verification key into transcript
    pk.vk.hash_into(transcript)?;

    let domain = &pk.vk.domain;
    let mut meta = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut meta);

    // Selector optimizations cannot be applied here; use the ConstraintSystem
    // from the verification key.
    let meta = &pk.vk.cs;

    struct InstanceSingle<C: CurveAffine> {
        pub instance_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
        pub instance_polys: Vec<Polynomial<C::Scalar, Coeff>>,
        pub instance_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    }

    let instance: Vec<InstanceSingle<C>> = instances
        .iter()
        .map(|instance| -> Result<InstanceSingle<C>, Error> {
            let instance_values = instance
                .iter()
                .map(|values| {
                    let mut poly = domain.empty_lagrange();
                    assert_eq!(poly.len(), params.n as usize);
                    if values.len() > (poly.len() - (meta.blinding_factors() + 1)) {
                        return Err(Error::InstanceTooLarge);
                    }
                    for (poly, value) in poly.iter_mut().zip(values.iter()) {
                        *poly = *value;
                    }
                    Ok(poly)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let instance_commitments_projective: Vec<_> = instance
                .iter()
                .map(|values| commit_instance(params, values))
                .collect();
            let mut instance_commitments =
                vec![C::identity(); instance_commitments_projective.len()];
            C::Curve::batch_normalize(&instance_commitments_projective, &mut instance_commitments);
            let instance_commitments = instance_commitments;
            drop(instance_commitments_projective);

            for commitment in &instance_commitments {
                transcript.common_point(*commitment)?;
            }

            let instance_polys: Vec<_> = instance_values
                .iter()
                .map(|poly| {
                    let lagrange_vec = domain.lagrange_from_vec(poly.to_vec());
                    domain.lagrange_to_coeff_with_twiddles(lagrange_vec, &pk.fft_twiddles)
                })
                .collect();

            let instance_cosets: Vec<_> = instance_polys
                .iter()
                .map(|poly| domain.coeff_to_extended_with_twiddles(poly.clone(), &pk.fft_twiddles))
                .collect();

            Ok(InstanceSingle {
                instance_values,
                instance_polys,
                instance_cosets,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    struct AdviceSingle<C: CurveAffine> {
        pub advice_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
        pub advice_polys: Vec<Polynomial<C::Scalar, Coeff>>,
        pub advice_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
        pub advice_blinds: Vec<Blind<C::Scalar>>,
    }

    let unusable_rows_start = params.n as usize - (meta.blinding_factors() + 1);
    let mut witnesses = instances
        .iter()
        .map(|instances| WitnessCollection {
            k: params.k,
            advice: vec![domain.empty_lagrange_assigned(); meta.num_advice_columns],
            instances,
            // The prover will not be allowed to assign values to advice
            // cells that exist within inactive rows, which include some
            // number of blinding factors and an extra row for use in the
            // permutation argument.
            usable_rows: ..unusable_rows_start,
            _marker: std::marker::PhantomData,
        })
        .collect::<Vec<_>>();

    // Synthesize every circuit while allowing its floor planner to share
    // circuit-shape-dependent work across the batch.
    ConcreteCircuit::FloorPlanner::synthesize_batch(
        &mut witnesses,
        circuits,
        config,
        meta.constants.clone(),
    )?;

    let advice: Vec<AdviceSingle<C>> = witnesses
        .into_iter()
        .map(|witness| -> Result<AdviceSingle<C>, Error> {
            let mut advice = batch_invert_assigned(witness.advice);

            // Add blinding factors to advice columns
            for advice in &mut advice {
                for cell in &mut advice[unusable_rows_start..] {
                    *cell = C::Scalar::random(&mut rng);
                }
            }

            // Compute commitments to advice column polynomials
            let advice_blinds: Vec<_> = advice
                .iter()
                .map(|_| Blind(C::Scalar::random(&mut rng)))
                .collect();
            let advice_commitments_projective: Vec<_> = advice
                .iter()
                .zip(advice_blinds.iter())
                .map(|(poly, blind)| params.commit_lagrange(poly, *blind))
                .collect();
            let mut advice_commitments = vec![C::identity(); advice_commitments_projective.len()];
            C::Curve::batch_normalize(&advice_commitments_projective, &mut advice_commitments);
            let advice_commitments = advice_commitments;
            drop(advice_commitments_projective);

            for commitment in &advice_commitments {
                transcript.write_point(*commitment)?;
            }

            let (advice_polys, advice_cosets) =
                domain.batch_lagrange_to_coeff_and_extended(&advice, &pk.fft_twiddles);

            Ok(AdviceSingle {
                advice_values: advice,
                advice_polys,
                advice_cosets,
                advice_blinds,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Create polynomial evaluator context for values.
    let mut value_evaluator = poly::new_evaluator(|| {});

    // Register fixed values with the polynomial evaluator.
    let fixed_values: Vec<_> = pk
        .fixed_values
        .iter()
        .map(|poly| value_evaluator.register_poly(poly.clone()))
        .collect();

    // Register advice values with the polynomial evaluator.
    let advice_values: Vec<_> = advice
        .iter()
        .map(|advice| {
            advice
                .advice_values
                .iter()
                .map(|poly| value_evaluator.register_poly(poly.clone()))
                .collect::<Vec<_>>()
        })
        .collect();

    // Register instance values with the polynomial evaluator.
    let instance_values: Vec<_> = instance
        .iter()
        .map(|instance| {
            instance
                .instance_values
                .iter()
                .map(|poly| value_evaluator.register_poly(poly.clone()))
                .collect::<Vec<_>>()
        })
        .collect();

    // Create polynomial evaluator context for cosets.
    let mut coset_evaluator = poly::new_evaluator(|| {});

    // Register fixed cosets with the polynomial evaluator.
    let fixed_cosets: Vec<_> = pk
        .fixed_cosets
        .iter()
        .map(|poly| coset_evaluator.register_poly(poly.clone()))
        .collect();

    // Register advice cosets with the polynomial evaluator.
    let advice_cosets: Vec<_> = advice
        .iter()
        .map(|advice| {
            advice
                .advice_cosets
                .iter()
                .map(|poly| coset_evaluator.register_poly(poly.clone()))
                .collect::<Vec<_>>()
        })
        .collect();

    // Register instance cosets with the polynomial evaluator.
    let instance_cosets: Vec<_> = instance
        .iter()
        .map(|instance| {
            instance
                .instance_cosets
                .iter()
                .map(|poly| coset_evaluator.register_poly(poly.clone()))
                .collect::<Vec<_>>()
        })
        .collect();

    // Register permutation cosets with the polynomial evaluator.
    let permutation_cosets: Vec<_> = pk
        .permutation
        .cosets
        .iter()
        .map(|poly| coset_evaluator.register_poly(poly.clone()))
        .collect();

    // Register boundary polynomials used in the lookup and permutation arguments.
    let l0 = coset_evaluator.register_poly(pk.l0.clone());
    let l_blind = coset_evaluator.register_poly(pk.l_blind.clone());
    let l_last = coset_evaluator.register_poly(pk.l_last.clone());

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();

    let lookups: Vec<Vec<lookup::prover::Permuted<C, _>>> = instance_values
        .iter()
        .zip(instance_cosets.iter())
        .zip(advice_values.iter())
        .zip(advice_cosets.iter())
        .map(|(((instance_values, instance_cosets), advice_values), advice_cosets)| -> Result<Vec<_>, Error> {
            // Construct and commit to permuted values for each lookup
            pk.vk
                .cs
                .lookups
                .iter()
                .map(|lookup| {
                    lookup.commit_permuted(
                        pk,
                        params,
                        domain,
                        &value_evaluator,
                        &mut coset_evaluator,
                        theta,
                        advice_values,
                        &fixed_values,
                        instance_values,
                        advice_cosets,
                        &fixed_cosets,
                        instance_cosets,
                        &mut rng,
                        transcript,
                    )
                })
                .collect()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Sample beta challenge
    let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();

    // Sample gamma challenge
    let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();

    // Commit to permutations.
    let permutations: Vec<permutation::prover::Committed<C, _>> = instance
        .iter()
        .zip(advice.iter())
        .map(|(instance, advice)| {
            pk.vk.cs.permutation.commit(
                params,
                pk,
                &pk.permutation,
                &advice.advice_values,
                &pk.fixed_values,
                &instance.instance_values,
                beta,
                gamma,
                &mut coset_evaluator,
                &mut rng,
                transcript,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    let lookups: Vec<Vec<lookup::prover::Committed<C, _>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            // Construct and commit to products for each lookup
            lookups
                .into_iter()
                .map(|lookup| {
                    lookup.commit_product(
                        pk,
                        params,
                        beta,
                        gamma,
                        &mut coset_evaluator,
                        &mut rng,
                        transcript,
                    )
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Commit to the random polynomial that masks the folded quotient
    // evaluation in the multiopening argument.
    let vanishing =
        vanishing::Argument::commit_random_polynomial(params, domain, &mut rng, transcript)?;

    // Obtain challenge for keeping all separate gates linearly independent
    let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();

    // Evaluate the h(X) polynomial's constraint system expressions for the permutation constraints.
    let (permutations, permutation_expressions): (Vec<_>, Vec<_>) = permutations
        .into_iter()
        .zip(advice_cosets.iter())
        .zip(instance_cosets.iter())
        .map(|((permutation, advice), instance)| {
            permutation.construct(
                pk,
                &pk.vk.cs.permutation,
                advice,
                &fixed_cosets,
                instance,
                &permutation_cosets,
                l0,
                l_blind,
                l_last,
                beta,
                gamma,
            )
        })
        .unzip();

    let (lookups, lookup_expressions): (Vec<Vec<_>>, Vec<Vec<_>>) = lookups
        .into_iter()
        .map(|lookups| {
            // Evaluate the h(X) polynomial's constraint system expressions for the lookup constraints, if any.
            lookups
                .into_iter()
                .map(|p| p.construct(beta, gamma, l0, l_blind, l_last))
                .unzip()
        })
        .unzip();

    let expressions = advice_cosets
        .iter()
        .zip(instance_cosets.iter())
        .zip(permutation_expressions)
        .zip(lookup_expressions)
        .flat_map(
            |(((advice_cosets, instance_cosets), permutation_expressions), lookup_expressions)| {
                let fixed_cosets = &fixed_cosets;
                iter::empty()
                    // Custom constraints
                    .chain(meta.gates.iter().flat_map(move |gate| {
                        gate.polynomials().iter().map(move |expr| {
                            expr.evaluate(
                                &poly::Ast::ConstantTerm,
                                &|_| panic!("virtual selectors are removed during optimization"),
                                &|query| {
                                    fixed_cosets[query.column_index]
                                        .with_rotation(query.rotation)
                                        .into()
                                },
                                &|query| {
                                    advice_cosets[query.column_index]
                                        .with_rotation(query.rotation)
                                        .into()
                                },
                                &|query| {
                                    instance_cosets[query.column_index]
                                        .with_rotation(query.rotation)
                                        .into()
                                },
                                &|a| -a,
                                &|a, b| a + b,
                                &|a, b| a * b,
                                &|a, scalar| a * scalar,
                            )
                        })
                    }))
                    // Permutation constraints, if any.
                    .chain(permutation_expressions)
                    // Lookup constraints, if any.
                    .chain(lookup_expressions.into_iter().flatten())
            },
        );

    // Construct and commit to the quotient polynomial h(X).
    let vanishing = vanishing.construct_quotient(
        params,
        domain,
        &pk.fft_twiddles,
        coset_evaluator,
        expressions,
        y,
        &mut rng,
        transcript,
    )?;

    let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();
    let xn = x.pow([params.n, 0, 0, 0]);
    let polynomial_evaluator = PolynomialEvaluator::new(
        [
            *x,
            domain.rotate_omega(*x, poly::Rotation::next()),
            domain.rotate_omega(*x, poly::Rotation::prev()),
            domain.rotate_omega(*x, poly::Rotation(-((meta.blinding_factors() + 1) as i32))),
        ],
        params.n as usize,
        advice.len(),
    );

    // Compute and hash instance evals for each circuit instance
    let instance_queries = instance
        .iter()
        .flat_map(|instance| {
            meta.instance_queries
                .iter()
                .map(move |&(column, rotation)| EvaluationQuery {
                    polynomial: &instance.instance_polys[column.index()],
                    point: EvaluationPoint::from_rotation(
                        rotation,
                        meta.blinding_factors(),
                        || domain.rotate_omega(*x, rotation),
                    ),
                })
        })
        .collect::<Vec<_>>();
    for evaluation in polynomial_evaluator.evaluate(&instance_queries) {
        transcript.write_scalar(evaluation)?;
    }

    // Compute and hash advice evals for each circuit instance
    let advice_queries = advice
        .iter()
        .flat_map(|advice| {
            meta.advice_queries
                .iter()
                .map(move |&(column, rotation)| EvaluationQuery {
                    polynomial: &advice.advice_polys[column.index()],
                    point: EvaluationPoint::from_rotation(
                        rotation,
                        meta.blinding_factors(),
                        || domain.rotate_omega(*x, rotation),
                    ),
                })
        })
        .collect::<Vec<_>>();
    for evaluation in polynomial_evaluator.evaluate(&advice_queries) {
        transcript.write_scalar(evaluation)?;
    }

    // Compute and hash fixed evals (shared across all circuit instances)
    let fixed_queries = meta
        .fixed_queries
        .iter()
        .map(|&(column, rotation)| EvaluationQuery {
            polynomial: &pk.fixed_polys[column.index()],
            point: EvaluationPoint::from_rotation(rotation, meta.blinding_factors(), || {
                domain.rotate_omega(*x, rotation)
            }),
        })
        .collect::<Vec<_>>();
    for evaluation in polynomial_evaluator.evaluate(&fixed_queries) {
        transcript.write_scalar(evaluation)?;
    }

    let vanishing = vanishing.evaluate(xn, domain, &polynomial_evaluator, transcript)?;

    // Evaluate common permutation data
    pk.permutation.evaluate(&polynomial_evaluator, transcript)?;

    // Evaluate the permutations, if any, at omega^i x.
    let permutations: Vec<permutation::prover::Evaluated<C>> = permutations
        .into_iter()
        .map(|permutation| -> Result<_, _> {
            permutation.evaluate(&polynomial_evaluator, transcript)
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Evaluate the lookups, if any, at omega^i x.
    let lookups: Vec<Vec<lookup::prover::Evaluated<C>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            lookups
                .into_iter()
                .map(|p| p.evaluate(&polynomial_evaluator, transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    let instances = instance
        .iter()
        .zip(advice.iter())
        .zip(permutations.iter())
        .zip(lookups.iter())
        .flat_map(|(((instance, advice), permutation), lookups)| {
            iter::empty()
                .chain(
                    pk.vk
                        .cs
                        .instance_queries
                        .iter()
                        .map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(*x, at),
                            poly: &instance.instance_polys[column.index()],
                            blind: Blind::default(),
                        }),
                )
                .chain(
                    pk.vk
                        .cs
                        .advice_queries
                        .iter()
                        .map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(*x, at),
                            poly: &advice.advice_polys[column.index()],
                            blind: advice.advice_blinds[column.index()],
                        }),
                )
                .chain(permutation.open(pk, x))
                .chain(lookups.iter().flat_map(move |p| p.open(pk, x)))
        })
        .chain(
            pk.vk
                .cs
                .fixed_queries
                .iter()
                .map(|&(column, at)| ProverQuery {
                    point: domain.rotate_omega(*x, at),
                    poly: &pk.fixed_polys[column.index()],
                    blind: Blind::default(),
                }),
        )
        .chain(pk.permutation.open(x))
        // We query the h(X) polynomial at x
        .chain(vanishing.open(x));

    multiopen::create_proof(params, rng, transcript, instances).map_err(|_| Error::Opening)
}

#[test]
fn test_commit_instance() {
    use ff::FromUniformBytes;
    use pasta_curves::{EpAffine, EqAffine, Fp, Fq};

    macro_rules! check_curve {
        ($curve:ty, $scalar:ty) => {{
            const K: u32 = 6;

            let params: Params<$curve> = Params::new(K);
            let domain = crate::poly::EvaluationDomain::new(1, K);

            for len in [0, 1, 10, 17, 63] {
                let mut instance = (0..len)
                    .map(|index| {
                        let mut bytes = [0; 64];
                        for (offset, byte) in bytes.iter_mut().enumerate() {
                            *byte = (index as u8)
                                .wrapping_mul(73)
                                .wrapping_add((offset as u8).wrapping_mul(29))
                                .wrapping_add(17);
                        }
                        <$scalar as FromUniformBytes<64>>::from_uniform_bytes(&bytes)
                    })
                    .collect::<Vec<_>>();
                if let Some(value) = instance.get_mut(0) {
                    *value = <$scalar>::ZERO;
                }
                if let Some(value) = instance.get_mut(1) {
                    *value = <$scalar>::ONE;
                }
                if let Some(value) = instance.get_mut(2) {
                    *value = -<$scalar>::ONE;
                }

                let mut poly = domain.empty_lagrange();
                for (coefficient, value) in poly.iter_mut().zip(&instance) {
                    *coefficient = *value;
                }

                assert_eq!(
                    commit_instance(&params, &instance),
                    params.commit_lagrange(&poly, Blind::default())
                );
            }
        }};
    }

    check_curve!(EqAffine, Fp);
    check_curve!(EpAffine, Fq);
}

#[test]
fn test_create_proof() {
    use crate::{
        circuit::SimpleFloorPlanner,
        plonk::{keygen_pk, keygen_vk},
        transcript::{Blake2bWrite, Challenge255},
    };
    use pasta_curves::EqAffine;
    use rand::rng;

    #[derive(Clone, Copy)]
    struct MyCircuit;

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = ();

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {}

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), Error> {
            Ok(())
        }
    }

    let params: Params<EqAffine> = Params::new(3);
    let vk = keygen_vk(&params, &MyCircuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &MyCircuit).expect("keygen_pk should not fail");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    // Create proof with wrong number of instances
    let proof = create_proof(
        &params,
        &pk,
        &[MyCircuit, MyCircuit],
        &[],
        rng(),
        &mut transcript,
    );
    assert!(matches!(proof.unwrap_err(), Error::InvalidInstances));

    // Create proof with correct number of instances
    create_proof(
        &params,
        &pk,
        &[MyCircuit, MyCircuit],
        &[&[], &[]],
        rng(),
        &mut transcript,
    )
    .expect("proof generation should not fail");
}

#[test]
fn v1_batch_reuses_measurement() {
    use crate::{
        circuit::floor_planner::V1,
        plonk::{keygen_pk, keygen_vk},
        transcript::{Blake2bWrite, Challenge255},
    };
    use pasta_curves::EqAffine;
    use rand::rng;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static MEASUREMENTS: AtomicUsize = AtomicUsize::new(0);

    #[derive(Clone, Copy)]
    struct MyCircuit;

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = ();
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            MEASUREMENTS.fetch_add(1, Ordering::Relaxed);
            *self
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {}

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), Error> {
            Ok(())
        }
    }

    let params: Params<EqAffine> = Params::new(3);
    let vk = keygen_vk(&params, &MyCircuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &MyCircuit).expect("keygen_pk should not fail");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    MEASUREMENTS.store(0, Ordering::Relaxed);
    create_proof(
        &params,
        &pk,
        &[MyCircuit, MyCircuit, MyCircuit],
        &[&[], &[], &[]],
        rng(),
        &mut transcript,
    )
    .expect("proof generation should not fail");
    assert_eq!(MEASUREMENTS.load(Ordering::Relaxed), 1);
}
