use std::{
    fmt,
    sync::{Arc, Mutex},
};

use ff::{Field, WithSmallOrderMulGroup};
use maybe_rayon::prelude::*;

use super::{ProvingKey, circuit::Expression, lookup, permutation};
use crate::{
    arithmetic::CurveAffine,
    poly::{
        self, Ast, AstLeaf, CompiledEvaluationPlan, EvaluationCacheLayout, ExtendedLagrangeCoeff,
    },
};

const RETAINED_QUOTIENT_CIRCUIT_COUNTS: [usize; 3] = [1, 2, 4];
const MAX_RETAINED_QUOTIENT_CACHE_LAYOUT_BYTES: usize = 64 * 1024;
const MAX_RETAINED_COMPILED_PLAN_BYTES: usize = 2 * 1024 * 1024;

struct LookupTopology<E, F: WithSmallOrderMulGroup<3>> {
    compressed_input: Ast<E, F, ExtendedLagrangeCoeff>,
    permuted_input: AstLeaf<E, ExtendedLagrangeCoeff>,
    compressed_table: Ast<E, F, ExtendedLagrangeCoeff>,
    permuted_table: AstLeaf<E, ExtendedLagrangeCoeff>,
}

fn expression_ast<E: Copy, F: WithSmallOrderMulGroup<3>>(
    expression: &Expression<F>,
    fixed: &[AstLeaf<E, ExtendedLagrangeCoeff>],
    advice: &[AstLeaf<E, ExtendedLagrangeCoeff>],
    instance: &[AstLeaf<E, ExtendedLagrangeCoeff>],
) -> Ast<E, F, ExtendedLagrangeCoeff> {
    expression.evaluate(
        &Ast::ConstantTerm,
        &|_| panic!("virtual selectors are removed during optimization"),
        &|query| {
            fixed[query.column_index]
                .with_rotation(query.rotation)
                .into()
        },
        &|query| {
            advice[query.column_index]
                .with_rotation(query.rotation)
                .into()
        },
        &|query| {
            instance[query.column_index]
                .with_rotation(query.rotation)
                .into()
        },
        &|a| -a,
        &|a, b| a + b,
        &|a, b| a * b,
        &|a, scalar| a * scalar,
    )
}

pub(super) struct QuotientCacheLayouts<F: Field> {
    layouts: Mutex<[Option<Arc<EvaluationCacheLayout>>; RETAINED_QUOTIENT_CIRCUIT_COUNTS.len()]>,
    compiled_plans: Mutex<
        [Option<Arc<CompiledEvaluationPlan<F, ExtendedLagrangeCoeff>>>;
            RETAINED_QUOTIENT_CIRCUIT_COUNTS.len()],
    >,
}

impl<F: Field> Default for QuotientCacheLayouts<F> {
    fn default() -> Self {
        Self {
            layouts: Mutex::new(std::array::from_fn(|_| None)),
            compiled_plans: Mutex::new(std::array::from_fn(|_| None)),
        }
    }
}

impl<F: Field> fmt::Debug for QuotientCacheLayouts<F> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("QuotientCacheLayouts")
            .finish_non_exhaustive()
    }
}

impl<F: Field> QuotientCacheLayouts<F> {
    fn index(circuit_count: usize) -> Option<usize> {
        RETAINED_QUOTIENT_CIRCUIT_COUNTS
            .iter()
            .position(|count| *count == circuit_count)
    }

    pub(super) fn get(&self, circuit_count: usize) -> Option<Arc<EvaluationCacheLayout>> {
        let index = Self::index(circuit_count)?;
        self.layouts
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())[index]
            .clone()
    }

    pub(super) fn get_compiled_plan(
        &self,
        circuit_count: usize,
    ) -> Option<Arc<CompiledEvaluationPlan<F, ExtendedLagrangeCoeff>>> {
        let index = Self::index(circuit_count)?;
        self.compiled_plans
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())[index]
            .clone()
    }

    pub(super) fn retain(&self, circuit_count: usize, layout: EvaluationCacheLayout) {
        let Some(index) = Self::index(circuit_count) else {
            return;
        };
        let mut layouts = self
            .layouts
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let existing_bytes = layouts
            .iter()
            .enumerate()
            .filter(|(candidate, _)| *candidate != index)
            .filter_map(|(_, layout)| layout.as_ref())
            .map(|layout| layout.payload_bytes())
            .sum::<usize>();
        if existing_bytes.saturating_add(layout.payload_bytes())
            <= MAX_RETAINED_QUOTIENT_CACHE_LAYOUT_BYTES
        {
            layouts[index] = Some(Arc::new(layout));
        }
    }

    pub(super) fn retain_compiled_plan(
        &self,
        circuit_count: usize,
        plan: CompiledEvaluationPlan<F, ExtendedLagrangeCoeff>,
    ) {
        let Some(index) = Self::index(circuit_count) else {
            return;
        };
        let mut plans = self
            .compiled_plans
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let existing_bytes = plans
            .iter()
            .enumerate()
            .filter(|(candidate, _)| *candidate != index)
            .filter_map(|(_, plan)| plan.as_ref())
            .map(|plan| plan.payload_bytes())
            .sum::<usize>();
        if existing_bytes.saturating_add(plan.payload_bytes()) <= MAX_RETAINED_COMPILED_PLAN_BYTES {
            plans[index] = Some(Arc::new(plan));
        }
    }
}

/// Prepares bounded quotient schedules from proving-key topology alone.
pub(super) fn prepare_quotient_cache_layouts<C: CurveAffine>(pk: &ProvingKey<C>) {
    let cs = &pk.vk.cs;
    let permutation_set_count = cs.permutation.set_count(pk.vk.cs_degree);

    let plans = RETAINED_QUOTIENT_CIRCUIT_COUNTS
        .into_par_iter()
        .map(|circuit_count| {
            let mut evaluator = poly::new_virtual_evaluator(|| {});

            // Keep this registration order synchronized with quotient setup in
            // `create_proof`. Exact validation fails closed if the order drifts.
            let fixed = (0..pk.fixed_cosets.len())
                .map(|_| evaluator.register_virtual_poly())
                .collect::<Vec<_>>();
            for family in pk.cached_selector_families.iter() {
                let query_and_first_selector = fixed[family.column_index];
                let combination_len = family.selectors.len() + 1;
                evaluator.register_compressed_selector(
                    query_and_first_selector,
                    combination_len,
                    1,
                    query_and_first_selector,
                );
                for assigned_root in 2..=combination_len {
                    let selector = evaluator.register_virtual_poly();
                    evaluator.register_compressed_selector(
                        query_and_first_selector,
                        combination_len,
                        assigned_root,
                        selector,
                    );
                }
            }

            let advice = (0..circuit_count)
                .map(|_| {
                    (0..cs.num_advice_columns)
                        .map(|_| evaluator.register_virtual_poly())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let instance = (0..circuit_count)
                .map(|_| {
                    (0..cs.num_instance_columns)
                        .map(|_| evaluator.register_virtual_poly())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let permutation_cosets = (0..pk.permutation.cosets.len())
                .map(|_| evaluator.register_virtual_poly())
                .collect::<Vec<_>>();
            let l0 = evaluator.register_virtual_poly();
            let l_blind = evaluator.register_virtual_poly();
            let l_last = evaluator.register_virtual_poly();

            let lookup_topologies = (0..circuit_count)
                .map(|circuit_index| {
                    cs.lookups
                        .iter()
                        .map(|lookup| {
                            let compressed_input = lookup::prover::compress_expressions_coset(
                                &lookup.input_expressions,
                                &fixed,
                                &advice[circuit_index],
                                &instance[circuit_index],
                            );
                            let compressed_table = lookup::prover::compress_expressions_coset(
                                &lookup.table_expressions,
                                &fixed,
                                &advice[circuit_index],
                                &instance[circuit_index],
                            );
                            let permuted_input = evaluator.register_virtual_poly();
                            let permuted_table = evaluator.register_virtual_poly();
                            LookupTopology {
                                compressed_input,
                                permuted_input,
                                compressed_table,
                                permuted_table,
                            }
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let permutation_products = (0..circuit_count)
                .map(|_| {
                    (0..permutation_set_count)
                        .map(|_| evaluator.register_virtual_poly())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let lookup_products = (0..circuit_count)
                .map(|_| {
                    (0..cs.lookups.len())
                        .map(|_| evaluator.register_virtual_poly())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();

            let mut expressions = vec![];
            for (circuit_index, ((lookups, permutation_products), lookup_products)) in
                lookup_topologies
                    .into_iter()
                    .zip(permutation_products.iter())
                    .zip(lookup_products)
                    .enumerate()
            {
                expressions.extend(cs.gates.iter().flat_map(|gate| {
                    gate.polynomials().iter().map(|expression| {
                        expression_ast(
                            expression,
                            &fixed,
                            &advice[circuit_index],
                            &instance[circuit_index],
                        )
                    })
                }));
                expressions.extend(permutation::prover::construct_constraints(
                    &cs.permutation,
                    pk.vk.cs_degree,
                    cs.blinding_factors(),
                    permutation_products,
                    &advice[circuit_index],
                    &fixed,
                    &instance[circuit_index],
                    &permutation_cosets,
                    l0,
                    l_blind,
                    l_last,
                ));
                for (lookup, product) in lookups.into_iter().zip(lookup_products) {
                    expressions.extend(lookup::prover::construct_constraints(
                        lookup.compressed_input,
                        lookup.permuted_input,
                        lookup.compressed_table,
                        lookup.permuted_table,
                        product,
                        l0,
                        l_blind,
                        l_last,
                    ));
                }
            }

            let quotient_numerator =
                Ast::distribute_challenge_powers(expressions, poly::EvaluationChallenge::Y);
            let plan = evaluator
                .prepare_compiled_quotient_plan(&quotient_numerator, pk.vk.domain.extended_len());
            (circuit_count, plan)
        })
        .collect::<Vec<_>>();
    // Retain in circuit-count order even though construction is parallel.
    for (circuit_count, plan) in plans {
        pk.quotient_cache_layouts
            .retain_compiled_plan(circuit_count, plan);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_counts_are_bounded() {
        assert_eq!(RETAINED_QUOTIENT_CIRCUIT_COUNTS, [1, 2, 4]);
        assert_eq!(MAX_RETAINED_QUOTIENT_CACHE_LAYOUT_BYTES, 64 * 1024);
        assert_eq!(MAX_RETAINED_COMPILED_PLAN_BYTES, 2 * 1024 * 1024);
    }
}
