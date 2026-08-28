use ff::Field;
use group::Curve;
use maybe_rayon::prelude::*;
use rand_core::Rng;
use std::iter;
use std::ops::RangeTo;

use super::{
    ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, ChallengeY, Error, ProvingKey,
    circuit::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Fixed, FloorPlanner, Instance,
        Selector,
    },
    commit_instance,
    evaluation::{EvaluationPoint, EvaluationQuery, PolynomialEvaluator},
    lookup, permutation, vanishing,
};

#[cfg(test)]
use super::circuit::FloorPlan;
use crate::transcript::{EncodedChallenge, TranscriptWrite};
use crate::{
    arithmetic::{CurveAffine, batch_invert_multi},
    circuit::Value,
    plonk::Assigned,
    poly::{
        self, Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial,
        commitment::{Blind, Params},
        multiopen::{self, ProverQuery},
    },
};

const NO_DENOMINATOR: u32 = u32::MAX;

struct AdviceWitness<F: Field> {
    values: Vec<Polynomial<F, LagrangeCoeff>>,
    denominator_cells: Vec<usize>,
    denominators: Vec<F>,
    denominator_slots: Vec<Vec<u32>>,
    row_count: usize,
}

impl<F: Field> AdviceWitness<F> {
    fn new(values: Vec<Polynomial<F, LagrangeCoeff>>) -> Self {
        let row_count = values.first().map_or(0, |column| column.len());
        assert!(values.iter().all(|column| column.len() == row_count));

        Self {
            denominator_slots: vec![vec![NO_DENOMINATOR; row_count]; values.len()],
            values,
            denominator_cells: Vec::new(),
            denominators: Vec::new(),
            row_count,
        }
    }

    fn assign(&mut self, column: usize, row: usize, assigned: Assigned<F>) -> Result<(), Error> {
        if self
            .values
            .get(column)
            .and_then(|values| values.get(row))
            .is_none()
        {
            return Err(Error::BoundsFailure);
        }

        match assigned {
            Assigned::Zero => {
                self.remove_denominator(column, row);
                self.values[column][row] = F::ZERO;
            }
            Assigned::Trivial(value) => {
                self.remove_denominator(column, row);
                self.values[column][row] = value;
            }
            Assigned::Rational(numerator, denominator) => {
                let slot = self.denominator_slots[column][row];
                if slot == NO_DENOMINATOR {
                    let slot = u32::try_from(self.denominators.len())
                        .expect("the number of advice cells fits into u32");
                    self.denominator_slots[column][row] = slot;
                    self.denominator_cells.push(column * self.row_count + row);
                    self.denominators.push(denominator);
                } else {
                    self.denominators[slot as usize] = denominator;
                }
                self.values[column][row] = numerator;
            }
        }

        Ok(())
    }

    fn remove_denominator(&mut self, column: usize, row: usize) {
        let slot = self.denominator_slots[column][row];
        if slot == NO_DENOMINATOR {
            return;
        }

        self.denominator_slots[column][row] = NO_DENOMINATOR;
        let slot = slot as usize;
        self.denominator_cells.swap_remove(slot);
        self.denominators.swap_remove(slot);

        if let Some(&moved_cell) = self.denominator_cells.get(slot) {
            let moved_column = moved_cell / self.row_count;
            let moved_row = moved_cell % self.row_count;
            self.denominator_slots[moved_column][moved_row] = slot as u32;
        }
    }

    fn evaluate(mut self) -> Vec<Polynomial<F, LagrangeCoeff>> {
        batch_invert_multi(&mut self.denominators);
        for (cell, denominator_inverse) in self.denominator_cells.into_iter().zip(self.denominators)
        {
            let column = cell / self.row_count;
            let row = cell % self.row_count;
            self.values[column][row] *= denominator_inverse;
        }
        self.values
    }
}

// Each outer circuit task contains a two-way commitment/transform join. Leave
// capacity for that nested work instead of consuming the whole pool with
// circuit tasks.
const PERMUTATION_INNER_WORKER_HEADROOM: usize = 2;

fn prepare_permutations_in_parallel(circuit_count: usize, worker_count: usize) -> bool {
    circuit_count > 1
        && worker_count.saturating_sub(circuit_count) >= PERMUTATION_INNER_WORKER_HEADROOM
}

struct WitnessCollection<'a, F: Field> {
    k: u32,
    advice: AdviceWitness<F>,
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

        self.advice
            .assign(column.index(), row, to().into_field().assign()?)
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
///
/// The circuit type must be `Sync` and its configuration `Send` so that
/// compatible floor planners can synthesize independent circuit witnesses in
/// parallel.
pub fn create_proof<
    C: CurveAffine,
    E: EncodedChallenge<C>,
    R: Rng,
    T: TranscriptWrite<C, E>,
    ConcreteCircuit: Circuit<C::ScalarExt> + Sync,
>(
    params: &Params<C>,
    pk: &ProvingKey<C>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[C::Scalar]]],
    mut rng: R,
    transcript: &mut T,
) -> Result<(), Error>
where
    <ConcreteCircuit as Circuit<C::ScalarExt>>::Config: Send,
{
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

    let prepared_instances = instances
        .into_par_iter()
        .map(|instance| -> Result<_, Error> {
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

            Ok((
                instance_commitments,
                InstanceSingle::<C> {
                    instance_values,
                    instance_polys,
                    instance_cosets,
                },
            ))
        })
        .collect::<Vec<_>>();

    // Prepare each circuit independently, then preserve circuit and column
    // order while updating the transcript. Keeping each preparation result in
    // order also preserves the transcript prefix before an instance error.
    let mut instance = Vec::with_capacity(prepared_instances.len());
    for prepared in prepared_instances {
        let (instance_commitments, instance_single) = prepared?;
        for commitment in instance_commitments {
            transcript.common_point(commitment)?;
        }
        instance.push(instance_single);
    }

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
            advice: AdviceWitness::new(vec![domain.empty_lagrange(); meta.num_advice_columns]),
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
        &meta.constants,
        pk.floor_plan.as_ref(),
    )?;

    // Consume randomness in circuit order before preparing the independent
    // commitments and polynomial transforms in parallel.
    let advice_witnesses = witnesses
        .into_iter()
        .map(|witness| -> Result<_, Error> {
            let mut advice = witness.advice.evaluate();

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
            Ok((advice, advice_blinds))
        })
        .collect::<Result<Vec<_>, _>>()?;

    let prepared_advice = advice_witnesses
        .into_par_iter()
        .map(|(advice, advice_blinds)| {
            let (advice_commitments, (advice_polys, advice_cosets)) = crate::multicore::join(
                || {
                    #[cfg(feature = "multicore")]
                    let advice_commitments_projective: Vec<_> = advice
                        .par_iter()
                        .zip(advice_blinds.par_iter())
                        .map(|(poly, blind)| params.commit_lagrange(poly, *blind))
                        .collect();
                    #[cfg(not(feature = "multicore"))]
                    let advice_commitments_projective: Vec<_> = advice
                        .iter()
                        .zip(advice_blinds.iter())
                        .map(|(poly, blind)| params.commit_lagrange(poly, *blind))
                        .collect();
                    let mut advice_commitments =
                        vec![C::identity(); advice_commitments_projective.len()];
                    C::Curve::batch_normalize(
                        &advice_commitments_projective,
                        &mut advice_commitments,
                    );
                    advice_commitments
                },
                || domain.batch_lagrange_to_coeff_and_extended(&advice, &pk.fft_twiddles),
            );

            (
                advice_commitments,
                AdviceSingle::<C> {
                    advice_values: advice,
                    advice_polys,
                    advice_cosets,
                    advice_blinds,
                },
            )
        })
        .collect::<Vec<_>>();

    let mut advice = Vec::with_capacity(prepared_advice.len());
    for (advice_commitments, advice_single) in prepared_advice {
        for commitment in advice_commitments {
            transcript.write_point(commitment)?;
        }
        advice.push(advice_single);
    }

    // Create polynomial evaluator context for values.
    let mut value_evaluator = poly::new_evaluator(|| {});

    // Register fixed values with the polynomial evaluator.
    let fixed_values: Vec<_> = pk
        .fixed_values
        .iter()
        .map(|poly| value_evaluator.register_poly_ref(poly))
        .collect();

    // Register advice values with the polynomial evaluator.
    let advice_values: Vec<_> = advice
        .iter()
        .map(|advice| {
            advice
                .advice_values
                .iter()
                .map(|poly| value_evaluator.register_poly_ref(poly))
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
                .map(|poly| value_evaluator.register_poly_ref(poly))
                .collect::<Vec<_>>()
        })
        .collect();

    // Create polynomial evaluator context for cosets.
    let mut coset_evaluator = poly::new_evaluator(|| {});

    // Register fixed cosets with the polynomial evaluator.
    let fixed_cosets: Vec<_> = pk
        .fixed_cosets
        .iter()
        .map(|poly| coset_evaluator.register_poly_ref(poly))
        .collect();

    for family in pk.cached_selector_families.iter() {
        let query_and_first_selector = fixed_cosets[family.column_index];
        let combination_len = family.selectors.len() + 1;
        coset_evaluator.register_compressed_selector(
            query_and_first_selector,
            combination_len,
            1,
            query_and_first_selector,
        );
        for (assigned_root, selector) in (2..).zip(family.selectors.iter()) {
            let precomputed = coset_evaluator.register_poly_ref(selector);
            coset_evaluator.register_compressed_selector(
                query_and_first_selector,
                combination_len,
                assigned_root,
                precomputed,
            );
        }
    }

    // Register advice cosets with the polynomial evaluator.
    let advice_cosets: Vec<_> = advice
        .iter()
        .map(|advice| {
            advice
                .advice_cosets
                .iter()
                .map(|poly| coset_evaluator.register_poly_ref(poly))
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
                .map(|poly| coset_evaluator.register_poly_ref(poly))
                .collect::<Vec<_>>()
        })
        .collect();

    // Register permutation cosets with the polynomial evaluator.
    let permutation_cosets: Vec<_> = pk
        .permutation
        .cosets
        .iter()
        .map(|poly| coset_evaluator.register_poly_ref(poly))
        .collect();

    // Register boundary polynomials used in the lookup and permutation arguments.
    let l0 = coset_evaluator.register_poly_ref(&pk.l0);
    let l_blind = coset_evaluator.register_poly_ref(&pk.l_blind);
    let l_last = coset_evaluator.register_poly_ref(&pk.l_last);

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();

    let lookup_count = pk.vk.cs.lookups.len();
    let mut lookup_tasks = Vec::new();
    // Draw all blinding values in circuit-major, lookup-major order before
    // preparing the independent lookup arguments in parallel.
    for circuit_index in 0..instance_values.len() {
        for lookup_index in 0..lookup_count {
            let blinding = lookup::prover::sample_permuted_blinding(pk, &mut rng);
            lookup_tasks.push((circuit_index, lookup_index, blinding));
        }
    }

    let prepared_lookups = lookup_tasks
        .into_par_iter()
        .map(|(circuit_index, lookup_index, blinding)| {
            pk.vk.cs.lookups[lookup_index].prepare_permuted(
                pk,
                params,
                domain,
                &value_evaluator,
                theta,
                &advice_values[circuit_index],
                &fixed_values,
                &instance_values[circuit_index],
                &advice_cosets[circuit_index],
                &fixed_cosets,
                &instance_cosets[circuit_index],
                blinding,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    let mut prepared_lookups = prepared_lookups.into_iter();
    let lookups: Vec<Vec<lookup::prover::Permuted<C, _>>> = (0..instance_values.len())
        .map(|_| {
            (0..lookup_count)
                .map(|_| {
                    prepared_lookups
                        .next()
                        .expect("one prepared lookup per task")
                        .finalize(&mut coset_evaluator, transcript)
                })
                .collect()
        })
        .collect::<Result<Vec<_>, _>>()?;
    debug_assert!(prepared_lookups.next().is_none());

    // Sample beta challenge
    let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();

    // Sample gamma challenge
    let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();

    let permutations: Vec<permutation::prover::Committed<C, _>> =
        if prepare_permutations_in_parallel(instance.len(), crate::multicore::current_num_threads())
        {
            // Draw every permutation's blinding values in circuit and set
            // order before preparing the independent arguments in parallel.
            let permutation_blindings = (0..instance.len())
                .map(|_| pk.vk.cs.permutation.sample_blinding(pk, &mut rng))
                .collect::<Vec<_>>();

            let prepared_permutations = (0..instance.len())
                .into_par_iter()
                .zip(permutation_blindings.into_par_iter())
                .map(|(circuit_index, blinding)| {
                    pk.vk.cs.permutation.prepare(
                        params,
                        pk,
                        &pk.permutation,
                        &advice[circuit_index].advice_values,
                        &pk.fixed_values,
                        &instance[circuit_index].instance_values,
                        beta,
                        gamma,
                        blinding,
                    )
                })
                .collect::<Vec<_>>();

            prepared_permutations
                .into_iter()
                .map(|permutation| permutation.commit(&mut coset_evaluator, transcript))
                .collect::<Result<Vec<_>, _>>()?
        } else {
            // Keep each circuit's preparation and commitment together on
            // smaller pools to avoid competing for cache across circuits.
            instance
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
                .collect::<Result<Vec<_>, _>>()?
        };

    let circuit_count = lookups.len();
    let mut lookup_product_tasks = Vec::with_capacity(circuit_count * lookup_count);
    // Draw all blinding values in circuit-major, lookup-major order before
    // preparing the independent lookup products in parallel.
    for circuit_lookups in lookups {
        debug_assert_eq!(circuit_lookups.len(), lookup_count);
        for lookup in circuit_lookups {
            let blinding = lookup::prover::sample_product_blinding(pk, &mut rng);
            lookup_product_tasks.push((lookup, blinding));
        }
    }

    let prepared_lookup_products = lookup_product_tasks
        .into_par_iter()
        .map(|(lookup, blinding)| lookup.prepare_product(pk, params, beta, gamma, blinding))
        .collect::<Vec<_>>();

    let mut prepared_lookup_products = prepared_lookup_products.into_iter();
    let lookups: Vec<Vec<lookup::prover::Committed<C, _>>> = (0..circuit_count)
        .map(|_| {
            (0..lookup_count)
                .map(|_| {
                    prepared_lookup_products
                        .next()
                        .expect("one prepared lookup product per task")
                        .finalize(&mut coset_evaluator, transcript)
                })
                .collect()
        })
        .collect::<Result<Vec<_>, _>>()?;
    debug_assert!(prepared_lookup_products.next().is_none());

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
    // Collect advice evals for each circuit instance.
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
    // Collect fixed evals, which are shared across all circuit instances.
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
    // Evaluate all transcript-adjacent queries in one batch so that the
    // parallel evaluator does not encounter an artificial barrier between
    // instance, advice, and fixed polynomials.
    let queries = instance_queries
        .into_iter()
        .chain(advice_queries)
        .chain(fixed_queries)
        .collect::<Vec<_>>();
    for evaluation in polynomial_evaluator.evaluate(&queries) {
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
fn permutation_outer_parallelism_reserves_inner_capacity() {
    for (circuits, workers, expected) in [
        (1, 10, false),
        (2, 2, false),
        (2, 3, false),
        (2, 4, true),
        (4, 5, false),
        (4, 6, true),
        (4, 10, true),
    ] {
        assert_eq!(
            prepare_permutations_in_parallel(circuits, workers),
            expected
        );
    }
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
fn advice_witness_evaluates_rationals_and_reassignments() {
    use pasta_curves::Fp;

    let domain = poly::EvaluationDomain::new(3, 3);
    let mut advice = AdviceWitness::new(vec![domain.empty_lagrange(); 2]);

    advice
        .assign(0, 0, Assigned::Rational(Fp::from(6), Fp::from(3)))
        .unwrap();
    advice
        .assign(1, 1, Assigned::Rational(Fp::from(8), Fp::from(2)))
        .unwrap();

    // Removing the first denominator moves the second into its slot. Updating
    // that cell exercises the repaired sparse index after `swap_remove`.
    advice.assign(0, 0, Assigned::Trivial(Fp::from(5))).unwrap();
    advice
        .assign(1, 1, Assigned::Rational(Fp::from(9), Fp::from(3)))
        .unwrap();
    advice
        .assign(0, 2, Assigned::Rational(Fp::from(7), Fp::ZERO))
        .unwrap();
    advice.assign(0, 3, Assigned::Zero).unwrap();
    advice
        .assign(1, 4, Assigned::Trivial(Fp::from(11)))
        .unwrap();
    advice
        .assign(0, 5, Assigned::Rational(Fp::ZERO, Fp::from(7)))
        .unwrap();

    assert!(matches!(
        advice.assign(2, 0, Assigned::Zero),
        Err(Error::BoundsFailure)
    ));
    assert!(matches!(
        advice.assign(0, 8, Assigned::Zero),
        Err(Error::BoundsFailure)
    ));

    let advice = advice.evaluate();
    assert_eq!(advice[0][0], Fp::from(5));
    assert_eq!(advice[0][2], Fp::ZERO);
    assert_eq!(advice[0][3], Fp::ZERO);
    assert_eq!(advice[0][5], Fp::ZERO);
    assert_eq!(advice[1][1], Fp::from(3));
    assert_eq!(advice[1][4], Fp::from(11));
}

#[test]
fn instance_preparation_preserves_proof_and_error_order() {
    use crate::{
        circuit::SimpleFloorPlanner,
        plonk::{keygen_pk, keygen_vk},
        transcript::{Blake2bWrite, Challenge255, EncodedChallenge, Transcript},
    };
    use pasta_curves::{EqAffine, Fp};
    use rand::{SeedableRng, rngs::StdRng};

    const PROOF_SEED: u64 = 0x494e_5354_414e_4345;

    #[derive(Clone, Copy)]
    struct InstanceCircuit;

    impl<F: Field> Circuit<F> for InstanceCircuit {
        type Config = Column<Instance>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            meta.instance_column()
        }

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), Error> {
            Ok(())
        }
    }

    let params: Params<EqAffine> = Params::new(3);
    let vk = keygen_vk(&params, &InstanceCircuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &InstanceCircuit).expect("keygen_pk should not fail");
    let circuits = [InstanceCircuit; 4];
    let instance_values = [[Fp::from(1)], [Fp::from(2)], [Fp::from(3)], [Fp::from(4)]];
    let instance_columns = instance_values
        .iter()
        .map(|values| vec![values.as_slice()])
        .collect::<Vec<_>>();
    let instances = instance_columns
        .iter()
        .map(Vec::as_slice)
        .collect::<Vec<_>>();
    let create_seeded_proof = || {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(
            &params,
            &pk,
            &circuits,
            &instances,
            StdRng::seed_from_u64(PROOF_SEED),
            &mut transcript,
        )
        .expect("proof generation should not fail");
        transcript.finalize()
    };

    let expected_proof = create_seeded_proof();
    assert_eq!(create_seeded_proof(), expected_proof);

    #[cfg(feature = "multicore")]
    for threads in [1, 4] {
        let proof = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap()
            .install(create_seeded_proof);
        assert_eq!(proof, expected_proof);
    }

    let valid = [Fp::from(5)];
    let oversized = vec![Fp::ZERO; params.n as usize];
    let later = [Fp::from(7)];
    let valid_columns = [valid.as_slice()];
    let oversized_columns = [oversized.as_slice()];
    let later_columns = [later.as_slice()];

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    let result = create_proof(
        &params,
        &pk,
        &[InstanceCircuit; 3],
        &[&valid_columns, &oversized_columns, &later_columns],
        StdRng::seed_from_u64(PROOF_SEED),
        &mut transcript,
    );
    assert!(matches!(result, Err(Error::InstanceTooLarge)));
    let actual_prefix = transcript.squeeze_challenge().get_scalar();

    let mut expected = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    pk.vk
        .hash_into(&mut expected)
        .expect("verification-key hashing should not fail");
    expected
        .common_point(commit_instance(&params, &valid).to_affine())
        .expect("valid instance commitment should not fail");
    assert_eq!(actual_prefix, expected.squeeze_challenge().get_scalar());

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    let result = create_proof(
        &params,
        &pk,
        &[InstanceCircuit; 2],
        &[&oversized_columns, &valid_columns],
        StdRng::seed_from_u64(PROOF_SEED),
        &mut transcript,
    );
    assert!(matches!(result, Err(Error::InstanceTooLarge)));
    let actual_prefix = transcript.squeeze_challenge().get_scalar();

    let mut expected = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    pk.vk
        .hash_into(&mut expected)
        .expect("verification-key hashing should not fail");
    assert_eq!(actual_prefix, expected.squeeze_challenge().get_scalar());
}

#[test]
fn v1_proving_key_reuses_floor_plan() {
    use crate::{
        circuit::floor_planner::V1,
        plonk::{keygen_pk, keygen_vk},
        transcript::{Blake2bWrite, Challenge255},
    };
    use pasta_curves::EqAffine;
    use rand::{SeedableRng, rngs::StdRng};
    use std::sync::atomic::{AtomicUsize, Ordering};

    static MEASUREMENTS: AtomicUsize = AtomicUsize::new(0);
    const PROOF_SEED: u64 = 0x5631_4241_5443_4802;

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
    let mut pk = keygen_pk(&params, vk, &MyCircuit).expect("keygen_pk should not fail");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    MEASUREMENTS.store(0, Ordering::Relaxed);
    create_proof(
        &params,
        &pk,
        &[MyCircuit, MyCircuit, MyCircuit],
        &[&[], &[], &[]],
        StdRng::seed_from_u64(PROOF_SEED),
        &mut transcript,
    )
    .expect("proof generation should not fail");
    // The plan cached in the proving key is reused, so proving re-measures
    // nothing.
    assert_eq!(MEASUREMENTS.load(Ordering::Relaxed), 0);
    let first_proof = transcript.finalize();

    // The proof bytes must not depend on the parallel schedule: re-create the
    // proof under single- and multi-worker Rayon pools and require identical
    // transcripts.
    #[cfg(feature = "multicore")]
    for threads in [1, 4] {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        MEASUREMENTS.store(0, Ordering::Relaxed);
        maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .unwrap()
            .install(|| {
                create_proof(
                    &params,
                    &pk,
                    &[MyCircuit, MyCircuit, MyCircuit],
                    &[&[], &[], &[]],
                    StdRng::seed_from_u64(PROOF_SEED),
                    &mut transcript,
                )
            })
            .expect("proof generation should not fail");
        assert_eq!(MEASUREMENTS.load(Ordering::Relaxed), 0);
        assert_eq!(transcript.finalize(), first_proof);
    }

    // A plan produced by another floor planner is ignored safely: the V1
    // planner re-measures once and still produces identical proof bytes.
    pk.floor_plan = Some(FloorPlan::from_arc(std::sync::Arc::new(())));
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    MEASUREMENTS.store(0, Ordering::Relaxed);
    create_proof(
        &params,
        &pk,
        &[MyCircuit, MyCircuit, MyCircuit],
        &[&[], &[], &[]],
        StdRng::seed_from_u64(PROOF_SEED),
        &mut transcript,
    )
    .expect("proof generation with an incompatible plan should not fail");
    assert_eq!(MEASUREMENTS.load(Ordering::Relaxed), 1);
    assert_eq!(transcript.finalize(), first_proof);
}

#[test]
fn compressed_selector_cache_preserves_proof() {
    use crate::{
        circuit::{Layouter, SimpleFloorPlanner},
        plonk::{Expression, keygen_pk, keygen_vk},
        poly::Rotation,
        transcript::{Blake2bWrite, Challenge255},
    };
    use pasta_curves::EqAffine;
    use rand::{SeedableRng, rngs::StdRng};

    const PROOF_SEED: u64 = 0x5345_4c45_4354_4f52;

    #[derive(Clone, Copy, Debug)]
    struct Config {
        advice: Column<Advice>,
        selectors: [Selector; crate::MIN_SELECTOR_FAMILY_LEN],
    }

    #[derive(Clone, Copy)]
    struct MyCircuit;

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = meta.advice_column();
            let selectors = core::array::from_fn(|_| meta.selector());

            for selector in selectors {
                meta.create_gate("selector family", |meta| {
                    let selector = meta.query_selector(selector);
                    let advice = meta.query_advice(advice, Rotation::cur());
                    vec![selector * (advice - Expression::Constant(F::ONE))]
                });
            }

            // A constraint-system degree one greater than the family length
            // can combine every degree-two selector expression into one fixed
            // column.
            meta.set_minimum_degree(crate::MIN_SELECTOR_FAMILY_LEN + 1);

            Config { advice, selectors }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "selector family",
                |mut region| {
                    for (row, selector) in config.selectors.iter().enumerate() {
                        selector.enable(&mut region, row)?;
                        region.assign_advice(
                            || "value",
                            config.advice,
                            row,
                            || Value::known(F::ONE),
                        )?;
                    }
                    Ok(())
                },
            )
        }
    }

    fn create(pk: &ProvingKey<EqAffine>, params: &Params<EqAffine>) -> Vec<u8> {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(
            params,
            pk,
            &[MyCircuit, MyCircuit],
            &[&[], &[]],
            StdRng::seed_from_u64(PROOF_SEED),
            &mut transcript,
        )
        .expect("proof generation should not fail");
        transcript.finalize()
    }

    let params = Params::new(4);
    let create_pk = || {
        let vk = keygen_vk(&params, &MyCircuit).expect("keygen_vk should not fail");
        keygen_pk(&params, vk, &MyCircuit).expect("keygen_pk should not fail")
    };
    let pk = create_pk();
    assert_eq!(pk.cached_selector_families.len(), 1);
    assert_eq!(
        pk.cached_selector_families[0].selectors.len() + 1,
        crate::MIN_SELECTOR_FAMILY_LEN
    );

    // A family omitted by the cache budget retains its source coset and takes
    // the generic evaluator path. Restore that state for every cached family.
    let mut uncached_pk = pk.clone();
    assert!(std::sync::Arc::ptr_eq(
        &pk.cached_selector_families,
        &uncached_pk.cached_selector_families,
    ));
    for family in pk.cached_selector_families.iter() {
        let column_index = family.column_index;
        uncached_pk.fixed_cosets[column_index] = uncached_pk
            .vk
            .domain
            .coeff_to_extended(uncached_pk.fixed_polys[column_index].clone());
    }
    uncached_pk.cached_selector_families = Default::default();

    assert_eq!(create(&pk, &params), create(&uncached_pk, &params));

    #[cfg(feature = "multicore")]
    {
        let single_pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();
        let parallel_pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(4)
            .build()
            .unwrap();
        let single_pk = single_pool.install(create_pk);
        let parallel_pk = parallel_pool.install(create_pk);

        assert_eq!(
            single_pk.cached_selector_families.len(),
            parallel_pk.cached_selector_families.len()
        );
        for (single, parallel) in single_pk
            .cached_selector_families
            .iter()
            .zip(parallel_pk.cached_selector_families.iter())
        {
            assert_eq!(single.column_index, parallel.column_index);
            assert_eq!(
                &single_pk.fixed_cosets[single.column_index][..],
                &parallel_pk.fixed_cosets[parallel.column_index][..]
            );
            assert_eq!(single.selectors.len(), parallel.selectors.len());
            for (single, parallel) in single.selectors.iter().zip(parallel.selectors.iter()) {
                assert_eq!(&single[..], &parallel[..]);
            }
        }

        let single_proof = single_pool.install(|| create(&single_pk, &params));
        let parallel_proof = parallel_pool.install(|| create(&parallel_pk, &params));
        assert_eq!(single_proof, parallel_proof);
    }
}
