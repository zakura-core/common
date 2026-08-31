use std::{
    fmt,
    sync::{Arc, Mutex},
};

use ff::{Field, WithSmallOrderMulGroup};
use maybe_rayon::prelude::*;

use super::{ProvingKey, circuit::Expression, lookup, permutation};
use crate::{
    arithmetic::CurveAffine,
    poly::{self, Ast, AstLeaf, CompiledEvaluationPlan, ExtendedLagrangeCoeff},
};

const RETAINED_QUOTIENT_CIRCUIT_COUNTS: [usize; 3] = [1, 2, 4];
// This bounds payload kept by the proving key after parallel keygen planning;
// it is not a bound on transient keygen allocations.
const MAX_RETAINED_QUOTIENT_PLAN_BYTES: usize = 1024 * 1024;

fn replacement_fits_payload_cap(
    existing_payloads: impl IntoIterator<Item = (usize, usize)>,
    replacement_index: usize,
    replacement_bytes: usize,
) -> bool {
    existing_payloads
        .into_iter()
        .filter(|(index, _)| *index != replacement_index)
        .map(|(_, bytes)| bytes)
        .fold(replacement_bytes, usize::saturating_add)
        <= MAX_RETAINED_QUOTIENT_PLAN_BYTES
}

#[derive(Clone, Copy)]
#[repr(usize)]
enum QuotientPolyRole {
    Fixed,
    Selector,
    Advice,
    Instance,
    Permutation,
    L0,
    LBlind,
    LLast,
    LookupPermutedInput,
    LookupPermutedTable,
    PermutationProduct,
    LookupProduct,
}

/// Semantic role of one polynomial in a compiled quotient plan.
#[derive(Clone, Copy)]
pub(in crate::plonk) enum QuotientPoly {
    Fixed {
        column_index: usize,
    },
    Selector {
        family_index: usize,
        assigned_root: usize,
    },
    Advice {
        circuit_index: usize,
        column_index: usize,
    },
    Instance {
        circuit_index: usize,
        column_index: usize,
    },
    Permutation {
        column_index: usize,
    },
    L0,
    LBlind,
    LLast,
    LookupPermutedInput {
        circuit_index: usize,
        lookup_index: usize,
    },
    LookupPermutedTable {
        circuit_index: usize,
        lookup_index: usize,
    },
    PermutationProduct {
        circuit_index: usize,
        set_index: usize,
    },
    LookupProduct {
        circuit_index: usize,
        lookup_index: usize,
    },
}

impl From<QuotientPoly> for poly::EvaluationPolyTag {
    fn from(tag: QuotientPoly) -> Self {
        let (role, first, second) = match tag {
            QuotientPoly::Fixed { column_index } => (QuotientPolyRole::Fixed, column_index, 0),
            QuotientPoly::Selector {
                family_index,
                assigned_root,
            } => (QuotientPolyRole::Selector, family_index, assigned_root),
            QuotientPoly::Advice {
                circuit_index,
                column_index,
            } => (QuotientPolyRole::Advice, circuit_index, column_index),
            QuotientPoly::Instance {
                circuit_index,
                column_index,
            } => (QuotientPolyRole::Instance, circuit_index, column_index),
            QuotientPoly::Permutation { column_index } => {
                (QuotientPolyRole::Permutation, column_index, 0)
            }
            QuotientPoly::L0 => (QuotientPolyRole::L0, 0, 0),
            QuotientPoly::LBlind => (QuotientPolyRole::LBlind, 0, 0),
            QuotientPoly::LLast => (QuotientPolyRole::LLast, 0, 0),
            QuotientPoly::LookupPermutedInput {
                circuit_index,
                lookup_index,
            } => (
                QuotientPolyRole::LookupPermutedInput,
                circuit_index,
                lookup_index,
            ),
            QuotientPoly::LookupPermutedTable {
                circuit_index,
                lookup_index,
            } => (
                QuotientPolyRole::LookupPermutedTable,
                circuit_index,
                lookup_index,
            ),
            QuotientPoly::PermutationProduct {
                circuit_index,
                set_index,
            } => (
                QuotientPolyRole::PermutationProduct,
                circuit_index,
                set_index,
            ),
            QuotientPoly::LookupProduct {
                circuit_index,
                lookup_index,
            } => (QuotientPolyRole::LookupProduct, circuit_index, lookup_index),
        };
        poly::EvaluationPolyTag::new(role as usize, first, second)
    }
}

struct LookupTopology<E, F: WithSmallOrderMulGroup<3>> {
    compressed_input: Ast<E, F, ExtendedLagrangeCoeff>,
    permuted_input: AstLeaf<E, ExtendedLagrangeCoeff>,
    compressed_table: Ast<E, F, ExtendedLagrangeCoeff>,
    permuted_table: AstLeaf<E, ExtendedLagrangeCoeff>,
}

pub(in crate::plonk) fn expression_ast<E: Copy, F: WithSmallOrderMulGroup<3>>(
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

pub(super) struct QuotientPlans<F: Field> {
    plans: Mutex<
        [Option<Arc<CompiledEvaluationPlan<F, ExtendedLagrangeCoeff>>>;
            RETAINED_QUOTIENT_CIRCUIT_COUNTS.len()],
    >,
}

impl<F: Field> Default for QuotientPlans<F> {
    fn default() -> Self {
        Self {
            plans: Mutex::new(std::array::from_fn(|_| None)),
        }
    }
}

impl<F: Field> fmt::Debug for QuotientPlans<F> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("QuotientPlans")
            .finish_non_exhaustive()
    }
}

impl<F: Field> QuotientPlans<F> {
    fn index(circuit_count: usize) -> Option<usize> {
        RETAINED_QUOTIENT_CIRCUIT_COUNTS
            .iter()
            .position(|count| *count == circuit_count)
    }

    pub(super) fn get(
        &self,
        circuit_count: usize,
    ) -> Option<Arc<CompiledEvaluationPlan<F, ExtendedLagrangeCoeff>>> {
        let index = Self::index(circuit_count)?;
        self.plans
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())[index]
            .clone()
    }

    pub(super) fn retain(
        &self,
        circuit_count: usize,
        plan: CompiledEvaluationPlan<F, ExtendedLagrangeCoeff>,
    ) {
        let Some(index) = Self::index(circuit_count) else {
            return;
        };
        let mut plans = self
            .plans
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let existing_payloads = plans
            .iter()
            .enumerate()
            .filter_map(|(index, plan)| plan.as_ref().map(|plan| (index, plan.payload_bytes())));
        if replacement_fits_payload_cap(existing_payloads, index, plan.payload_bytes()) {
            plans[index] = Some(Arc::new(plan));
        }
    }

    #[cfg(test)]
    pub(super) fn swap_polynomial_tags(
        &self,
        circuit_count: usize,
        lhs: QuotientPoly,
        rhs: QuotientPoly,
    ) {
        let index = Self::index(circuit_count).expect("the circuit count is retained");
        let mut plans = self
            .plans
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let plan = Arc::get_mut(plans[index].as_mut().expect("the plan is retained"))
            .expect("the retained plan has no external references");
        plan.swap_polynomial_tags(lhs.into(), rhs.into());
    }
}

/// Prepares bounded compiled quotient plans from proving-key topology alone.
pub(super) fn prepare_quotient_plans<C: CurveAffine>(pk: &ProvingKey<C>) {
    let cs = &pk.vk.cs;
    let permutation_set_count = cs.permutation.set_count(pk.vk.cs_degree);

    let plans = RETAINED_QUOTIENT_CIRCUIT_COUNTS
        .into_par_iter()
        .map(|circuit_count| {
            let mut evaluator = poly::new_virtual_evaluator(|| {});

            // Keep this registration order synchronized with quotient setup in
            // `create_proof`. Exact validation fails closed if the order drifts.
            let fixed = (0..pk.fixed_cosets.len())
                .map(|column_index| {
                    evaluator
                        .register_virtual_poly_with_tag(QuotientPoly::Fixed { column_index }.into())
                })
                .collect::<Vec<_>>();
            for (family_index, family) in pk.cached_selector_families.iter().enumerate() {
                let query_and_first_selector = fixed[family.column_index];
                let combination_len = family.selectors.len() + 1;
                evaluator.register_compressed_selector(
                    query_and_first_selector,
                    combination_len,
                    1,
                    query_and_first_selector,
                );
                for assigned_root in 2..=combination_len {
                    let selector = evaluator.register_virtual_poly_with_tag(
                        QuotientPoly::Selector {
                            family_index,
                            assigned_root,
                        }
                        .into(),
                    );
                    evaluator.register_compressed_selector(
                        query_and_first_selector,
                        combination_len,
                        assigned_root,
                        selector,
                    );
                }
            }

            let advice = (0..circuit_count)
                .map(|circuit_index| {
                    (0..cs.num_advice_columns)
                        .map(|column_index| {
                            evaluator.register_virtual_poly_with_tag(
                                QuotientPoly::Advice {
                                    circuit_index,
                                    column_index,
                                }
                                .into(),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let instance = (0..circuit_count)
                .map(|circuit_index| {
                    (0..cs.num_instance_columns)
                        .map(|column_index| {
                            evaluator.register_virtual_poly_with_tag(
                                QuotientPoly::Instance {
                                    circuit_index,
                                    column_index,
                                }
                                .into(),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let permutation_cosets = (0..pk.permutation.cosets.len())
                .map(|column_index| {
                    evaluator.register_virtual_poly_with_tag(
                        QuotientPoly::Permutation { column_index }.into(),
                    )
                })
                .collect::<Vec<_>>();
            let l0 = evaluator.register_virtual_poly_with_tag(QuotientPoly::L0.into());
            let l_blind = evaluator.register_virtual_poly_with_tag(QuotientPoly::LBlind.into());
            let l_last = evaluator.register_virtual_poly_with_tag(QuotientPoly::LLast.into());

            let lookup_topologies = (0..circuit_count)
                .map(|circuit_index| {
                    cs.lookups
                        .iter()
                        .enumerate()
                        .map(|(lookup_index, lookup)| {
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
                            let permuted_input = evaluator.register_virtual_poly_with_tag(
                                QuotientPoly::LookupPermutedInput {
                                    circuit_index,
                                    lookup_index,
                                }
                                .into(),
                            );
                            let permuted_table = evaluator.register_virtual_poly_with_tag(
                                QuotientPoly::LookupPermutedTable {
                                    circuit_index,
                                    lookup_index,
                                }
                                .into(),
                            );
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
                .map(|circuit_index| {
                    (0..permutation_set_count)
                        .map(|set_index| {
                            evaluator.register_virtual_poly_with_tag(
                                QuotientPoly::PermutationProduct {
                                    circuit_index,
                                    set_index,
                                }
                                .into(),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let lookup_products = (0..circuit_count)
                .map(|circuit_index| {
                    (0..cs.lookups.len())
                        .map(|lookup_index| {
                            evaluator.register_virtual_poly_with_tag(
                                QuotientPoly::LookupProduct {
                                    circuit_index,
                                    lookup_index,
                                }
                                .into(),
                            )
                        })
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
        pk.quotient_plans.retain(circuit_count, plan);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_counts_are_bounded() {
        assert_eq!(RETAINED_QUOTIENT_CIRCUIT_COUNTS, [1, 2, 4]);
        assert_eq!(MAX_RETAINED_QUOTIENT_PLAN_BYTES, 1024 * 1024);
    }

    #[test]
    fn retained_payload_cap_is_aggregate_and_replacement_aware() {
        let cap = MAX_RETAINED_QUOTIENT_PLAN_BYTES;
        assert!(replacement_fits_payload_cap(
            [(0, cap), (1, cap / 2)],
            0,
            cap / 2,
        ));
        assert!(replacement_fits_payload_cap([(1, cap - 1)], 0, 1,));
        assert!(!replacement_fits_payload_cap(
            [(0, cap), (1, cap / 2)],
            0,
            cap / 2 + 1,
        ));
        assert!(!replacement_fits_payload_cap(
            [(0, usize::MAX), (1, usize::MAX)],
            2,
            1,
        ));
    }
}
