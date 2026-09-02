use super::super::{
    ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, Error, ProvingKey,
    circuit::Expression, evaluator_schedule::QuotientPoly,
};
use super::Argument;
use crate::{
    arithmetic::{CurveAffine, parallelize},
    plonk::evaluation::{EvaluationPoint, EvaluationQuery},
    poly::{
        self, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation,
        commitment::{Blind, Params},
        multiopen::ProverQuery,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};
use ff::{PrimeField, WithSmallOrderMulGroup};
use group::{Curve, ff::Field};
use maybe_rayon::prelude::*;
use rand_core::Rng;
use std::{
    any::{Any, TypeId},
    cmp::Ordering,
    iter,
    ops::{Mul, MulAssign},
    sync::{Arc, Mutex},
};

#[derive(Debug)]
pub(in crate::plonk) struct Permuted<C: CurveAffine, Ev> {
    compressed_input_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_input_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    compressed_input_coset: Option<poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>>,
    permuted_input_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    permuted_input_blind: Blind<C::Scalar>,
    compressed_table_expression: Arc<Polynomial<C::Scalar, LagrangeCoeff>>,
    compressed_table_coset: Option<poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>>,
    permuted_table_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_table_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    permuted_table_blind: Blind<C::Scalar>,
}

#[derive(Debug)]
pub(in crate::plonk) struct Committed<C: CurveAffine, Ev> {
    compressed_input_coset: Option<poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>>,
    permuted_input_poly: Polynomial<C::Scalar, Coeff>,
    permuted_input_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    permuted_input_blind: Blind<C::Scalar>,
    compressed_table_coset: Option<poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>>,
    permuted_table_poly: Polynomial<C::Scalar, Coeff>,
    permuted_table_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    permuted_table_blind: Blind<C::Scalar>,
    product_poly: Polynomial<C::Scalar, Coeff>,
    product_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    product_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) struct Constructed<C: CurveAffine> {
    permuted_input_poly: Polynomial<C::Scalar, Coeff>,
    permuted_input_blind: Blind<C::Scalar>,
    permuted_table_poly: Polynomial<C::Scalar, Coeff>,
    permuted_table_blind: Blind<C::Scalar>,
    product_poly: Polynomial<C::Scalar, Coeff>,
    product_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) struct Evaluated<C: CurveAffine> {
    constructed: Constructed<C>,
}

pub(in crate::plonk) struct PermutedBlinding<F: Field> {
    input_rows: Vec<F>,
    table_rows: Vec<F>,
    input_blind: Blind<F>,
    table_blind: Blind<F>,
}

pub(in crate::plonk) struct PreparedPermuted<C: CurveAffine, Ev> {
    compressed_input_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_input_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    compressed_input_coset: Option<poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>>,
    permuted_input_commitment: C,
    permuted_input_blind: Blind<C::Scalar>,
    compressed_table_expression: Arc<Polynomial<C::Scalar, LagrangeCoeff>>,
    compressed_table_coset: Option<poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>>,
    permuted_table_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_table_commitment: C,
    permuted_table_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) struct ProductBlinding<F: Field> {
    rows: Vec<F>,
    product_blind: Blind<F>,
}

struct PreparedTable<F: Field, Ev> {
    compressed_expression: Arc<Polynomial<F, LagrangeCoeff>>,
    compressed_coset: Option<poly::Ast<Ev, F, ExtendedLagrangeCoeff>>,
    sorted_values: Vec<F>,
    sorted_keys: Vec<PastaSortKey>,
}

struct PreparedInput<F: Field, Ev> {
    compressed_expression: Polynomial<F, LagrangeCoeff>,
    compressed_coset: Option<poly::Ast<Ev, F, ExtendedLagrangeCoeff>>,
    sorted_values: Vec<F>,
    sorted_keys: Vec<PastaSortKey>,
}

struct PendingLookup<C: CurveAffine, Ev> {
    task_index: usize,
    lookup_index: usize,
    input: PreparedInput<C::Scalar, Ev>,
    blinding: PermutedBlinding<C::Scalar>,
}

struct TableState<C: CurveAffine, Ev> {
    table: Option<Arc<PreparedTable<C::Scalar, Ev>>>,
    pending: Vec<PendingLookup<C, Ev>>,
}

const PASTA_REPR_BYTES: usize = 32;
const PASTA_LIMB_BYTES: usize = std::mem::size_of::<u64>();
const PASTA_REPR_LIMBS: usize = PASTA_REPR_BYTES / PASTA_LIMB_BYTES;

#[derive(Clone, Copy)]
struct PastaSortKey {
    limbs: [u64; PASTA_REPR_LIMBS],
    source: usize,
}

impl PastaSortKey {
    const EMPTY: Self = Self {
        limbs: [0; PASTA_REPR_LIMBS],
        source: 0,
    };
}

impl PartialEq for PastaSortKey {
    fn eq(&self, other: &Self) -> bool {
        self.limbs == other.limbs
    }
}

impl Eq for PastaSortKey {}

impl PartialOrd for PastaSortKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PastaSortKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.limbs.iter().rev().cmp(other.limbs.iter().rev())
    }
}

fn pasta_sort_limbs(repr: [u8; PASTA_REPR_BYTES]) -> [u64; PASTA_REPR_LIMBS] {
    let (limbs, remainder) = repr.as_chunks::<PASTA_LIMB_BYTES>();
    assert!(remainder.is_empty());
    std::array::from_fn(|index| u64::from_le_bytes(limbs[index]))
}

fn uses_pasta_sort_keys<F: Field>() -> bool {
    TypeId::of::<F>() == TypeId::of::<crate::pasta::Fp>()
        || TypeId::of::<F>() == TypeId::of::<crate::pasta::Fq>()
}

pub(in crate::plonk) struct TablePlan {
    representatives: Vec<usize>,
    groups: Vec<usize>,
    table_sort_scratch: Vec<Vec<PastaSortKey>>,
    input_sort_scratch: Vec<Vec<PastaSortKey>>,
}

fn sort_pasta_values<F: PrimeField<Repr = [u8; PASTA_REPR_BYTES]>>(
    values: &mut [F],
    scratch: &mut [PastaSortKey],
) {
    assert_eq!(values.len(), scratch.len());
    for (source, (value, entry)) in values.iter().zip(scratch.iter_mut()).enumerate() {
        *entry = PastaSortKey {
            limbs: pasta_sort_limbs(value.to_repr()),
            source,
        };
    }
    scratch.sort_unstable();

    // Equal canonical encodings represent equal field elements, so their
    // relative input positions do not affect the lookup output.
    for destination in 0..values.len() {
        if scratch[destination].source == destination {
            continue;
        }

        let displaced = values[destination];
        let mut position = destination;
        loop {
            let source = scratch[position].source;
            scratch[position].source = position;
            if source == destination {
                values[position] = displaced;
                break;
            }
            values[position] = values[source];
            position = source;
        }
    }
}

// A `Vec` is required here for safe runtime specialization through `Any`.
#[allow(clippy::ptr_arg)]
fn sort_lookup_values<F: Field + Ord>(values: &mut Vec<F>, scratch: &mut [PastaSortKey]) {
    let dynamic_values = values as &mut dyn Any;
    if let Some(values) = dynamic_values.downcast_mut::<Vec<crate::pasta::Fp>>() {
        sort_pasta_values(values, scratch);
        return;
    }
    if let Some(values) = dynamic_values.downcast_mut::<Vec<crate::pasta::Fq>>() {
        sort_pasta_values(values, scratch);
        return;
    }

    values.sort_unstable();
}

pub(in crate::plonk) struct PreparedProduct<C: CurveAffine, Ev> {
    compressed_input_coset: Option<poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>>,
    permuted_input_poly: Polynomial<C::Scalar, Coeff>,
    permuted_input_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    permuted_input_coset_values: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    permuted_input_blind: Blind<C::Scalar>,
    compressed_table_coset: Option<poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>>,
    permuted_table_poly: Polynomial<C::Scalar, Coeff>,
    permuted_table_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    permuted_table_coset_values: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    permuted_table_blind: Blind<C::Scalar>,
    product_poly: Polynomial<C::Scalar, Coeff>,
    product_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    product_commitment: C,
    product_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) fn sample_permuted_blinding<C: CurveAffine, R: Rng>(
    pk: &ProvingKey<C>,
    mut rng: R,
) -> PermutedBlinding<C::Scalar> {
    let blind_rows = pk.vk.cs.blinding_factors() + 1;
    PermutedBlinding {
        input_rows: (0..blind_rows)
            .map(|_| C::Scalar::random(&mut rng))
            .collect(),
        table_rows: (0..blind_rows)
            .map(|_| C::Scalar::random(&mut rng))
            .collect(),
        input_blind: Blind(C::Scalar::random(&mut rng)),
        table_blind: Blind(C::Scalar::random(&mut rng)),
    }
}

pub(in crate::plonk) fn sample_product_blinding<C: CurveAffine, R: Rng>(
    pk: &ProvingKey<C>,
    mut rng: R,
) -> ProductBlinding<C::Scalar> {
    ProductBlinding {
        rows: (0..pk.vk.cs.blinding_factors())
            .map(|_| C::Scalar::random(&mut rng))
            .collect(),
        product_blind: Blind(C::Scalar::random(&mut rng)),
    }
}

/// Builds the coset-basis AST for one theta-compressed lookup side.
///
/// Every [`Expression`] must have had its virtual selectors removed.
pub(in crate::plonk) fn compress_expressions_coset<E: Copy, F: Field>(
    expressions: &[Expression<F>],
    fixed_cosets: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
    advice_cosets: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
    instance_cosets: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
) -> poly::Ast<E, F, ExtendedLagrangeCoeff> {
    expressions
        .iter()
        .map(|expression| {
            expression.evaluate(
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
        .reduce(|acc, expression| {
            acc * poly::Ast::ChallengeTerm(poly::EvaluationChallenge::Theta) + expression
        })
        .unwrap_or(poly::Ast::ConstantTerm(F::ZERO))
}

impl<F: Field> Argument<F> {
    fn has_same_table(&self, other: &Self) -> bool {
        self.table_expressions.len() == other.table_expressions.len()
            && self
                .table_expressions
                .iter()
                .zip(other.table_expressions.iter())
                .all(|(left, right)| match (left, right) {
                    (Expression::Fixed(left), Expression::Fixed(right)) => {
                        left.index == right.index
                            && left.column_index == right.column_index
                            && left.rotation == right.rotation
                    }
                    _ => false,
                })
    }
}

/// Plans fixed-table sharing and allocates lookup sort workspace.
pub(in crate::plonk) fn prepare_table_plan<F: Field>(
    lookup_arguments: &[Argument<F>],
    circuit_count: usize,
    usable_rows: usize,
) -> TablePlan {
    let mut representatives = Vec::<usize>::new();
    let groups = lookup_arguments
        .iter()
        .enumerate()
        .map(|(lookup_index, argument)| {
            representatives
                .iter()
                .position(|representative| {
                    argument.has_same_table(&lookup_arguments[*representative])
                })
                .unwrap_or_else(|| {
                    representatives.push(lookup_index);
                    representatives.len() - 1
                })
        })
        .collect::<Vec<_>>();

    let scratch_len = if uses_pasta_sort_keys::<F>() {
        usable_rows
    } else {
        0
    };
    let table_sort_scratch = representatives
        .iter()
        .map(|_| vec![PastaSortKey::EMPTY; scratch_len])
        .collect();
    let input_sort_scratch = (0..circuit_count)
        .flat_map(|_| {
            lookup_arguments
                .iter()
                .map(|_| vec![PastaSortKey::EMPTY; scratch_len])
        })
        .collect();

    TablePlan {
        representatives,
        groups,
        table_sort_scratch,
        input_sort_scratch,
    }
}

impl<F: WithSmallOrderMulGroup<3> + Ord> Argument<F> {
    #[allow(clippy::too_many_arguments)]
    fn prepare_table<Ev: Copy + Send + Sync, Ec: Copy + Send + Sync>(
        &self,
        domain: &EvaluationDomain<F>,
        value_evaluator: &poly::Evaluator<Ev, F, LagrangeCoeff>,
        theta: F,
        fixed_values: &[poly::AstLeaf<Ev, LagrangeCoeff>],
        fixed_cosets: &[poly::AstLeaf<Ec, ExtendedLagrangeCoeff>],
        usable_rows: usize,
        build_quotient_asts: bool,
        mut sort_scratch: Vec<PastaSortKey>,
    ) -> PreparedTable<F, Ec> {
        let unpermuted_expressions = self.table_expressions.iter().map(|expression| {
            let Expression::Fixed(query) = expression else {
                unreachable!("lookup table expressions are fixed queries")
            };
            fixed_values[query.column_index]
                .with_rotation(query.rotation)
                .into()
        });
        let compressed_expression = unpermuted_expressions
            .reduce(|acc, expression| acc * theta + expression)
            .unwrap_or(poly::Ast::ConstantTerm(F::ZERO));
        let compressed_coset = build_quotient_asts.then(|| {
            self.table_expressions
                .iter()
                .map(|expression| {
                    let Expression::Fixed(query) = expression else {
                        unreachable!("lookup table expressions are fixed queries")
                    };
                    fixed_cosets[query.column_index]
                        .with_rotation(query.rotation)
                        .into()
                })
                .reduce(|acc, expression| {
                    acc * poly::Ast::ChallengeTerm(poly::EvaluationChallenge::Theta) + expression
                })
                .unwrap_or(poly::Ast::ConstantTerm(F::ZERO))
        });
        let compressed_expression = value_evaluator.evaluate(&compressed_expression, domain);
        let mut sorted_values = compressed_expression
            .iter()
            .take(usable_rows)
            .copied()
            .collect::<Vec<_>>();
        sort_lookup_values(&mut sorted_values, &mut sort_scratch);

        PreparedTable {
            compressed_expression: Arc::new(compressed_expression),
            compressed_coset,
            sorted_values,
            sorted_keys: sort_scratch,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare_input<Ev: Copy + Send + Sync, Ec: Copy + Send + Sync>(
        &self,
        domain: &EvaluationDomain<F>,
        value_evaluator: &poly::Evaluator<Ev, F, LagrangeCoeff>,
        theta: F,
        advice_values: &[poly::AstLeaf<Ev, LagrangeCoeff>],
        fixed_values: &[poly::AstLeaf<Ev, LagrangeCoeff>],
        instance_values: &[poly::AstLeaf<Ev, LagrangeCoeff>],
        advice_cosets: &[poly::AstLeaf<Ec, ExtendedLagrangeCoeff>],
        fixed_cosets: &[poly::AstLeaf<Ec, ExtendedLagrangeCoeff>],
        instance_cosets: &[poly::AstLeaf<Ec, ExtendedLagrangeCoeff>],
        usable_rows: usize,
        build_quotient_asts: bool,
        mut sort_scratch: Vec<PastaSortKey>,
    ) -> PreparedInput<F, Ec> {
        let unpermuted_expressions = self.input_expressions.iter().map(|expression| {
            expression.evaluate(
                &|scalar| poly::Ast::ConstantTerm(scalar),
                &|_| panic!("virtual selectors are removed during optimization"),
                &|query| {
                    fixed_values[query.column_index]
                        .with_rotation(query.rotation)
                        .into()
                },
                &|query| {
                    advice_values[query.column_index]
                        .with_rotation(query.rotation)
                        .into()
                },
                &|query| {
                    instance_values[query.column_index]
                        .with_rotation(query.rotation)
                        .into()
                },
                &|a| -a,
                &|a, b| a + b,
                &|a, b| a * b,
                &|a, scalar| a * scalar,
            )
        });
        let compressed_expression = unpermuted_expressions
            .reduce(|acc, expression| acc * theta + expression)
            .unwrap_or(poly::Ast::ConstantTerm(F::ZERO));
        let compressed_coset = build_quotient_asts.then(|| {
            self.input_expressions
                .iter()
                .map(|expression| {
                    expression.evaluate(
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
                .reduce(|acc, expression| {
                    acc * poly::Ast::ChallengeTerm(poly::EvaluationChallenge::Theta) + expression
                })
                .unwrap_or(poly::Ast::ConstantTerm(F::ZERO))
        });
        let compressed_expression = value_evaluator.evaluate(&compressed_expression, domain);
        let mut sorted_values = compressed_expression
            .iter()
            .take(usable_rows)
            .copied()
            .collect::<Vec<_>>();
        sort_lookup_values(&mut sorted_values, &mut sort_scratch);

        PreparedInput {
            compressed_expression,
            compressed_coset,
            sorted_values,
            sorted_keys: sort_scratch,
        }
    }

    fn finish_permuted<C, Ec: Copy + Send + Sync>(
        &self,
        pk: &ProvingKey<C>,
        params: &Params<C>,
        domain: &EvaluationDomain<C::Scalar>,
        input: PreparedInput<C::Scalar, Ec>,
        table: &PreparedTable<C::Scalar, Ec>,
        blinding: PermutedBlinding<C::Scalar>,
    ) -> Result<PreparedPermuted<C, Ec>, Error>
    where
        C: CurveAffine<ScalarExt = F>,
        C::Curve: Mul<F, Output = C::Curve> + MulAssign<F>,
    {
        let PreparedInput {
            compressed_expression: compressed_input_expression,
            compressed_coset: compressed_input_coset,
            sorted_values: sorted_input_values,
            sorted_keys: sorted_input_keys,
        } = input;
        let (mut permuted_input_values, mut permuted_table_values) = permute_sorted_values(
            sorted_input_values,
            &sorted_input_keys,
            &table.sorted_values,
            &table.sorted_keys,
        )?;

        let blind_rows = pk.vk.cs.blinding_factors() + 1;
        assert_eq!(blinding.input_rows.len(), blind_rows);
        assert_eq!(blinding.table_rows.len(), blind_rows);
        permuted_input_values.extend_from_slice(&blinding.input_rows);
        permuted_table_values.extend_from_slice(&blinding.table_rows);
        assert_eq!(permuted_input_values.len(), params.n as usize);
        assert_eq!(permuted_table_values.len(), params.n as usize);

        #[cfg(feature = "sanity-checks")]
        {
            let mut last = None;
            for (input, table) in permuted_input_values
                .iter()
                .zip(permuted_table_values.iter())
                .take(table.sorted_values.len())
            {
                if input != table {
                    assert_eq!(*input, last.unwrap());
                }
                last = Some(*input);
            }
        }

        let permuted_input_expression = domain.lagrange_from_vec(permuted_input_values);
        let permuted_table_expression = domain.lagrange_from_vec(permuted_table_values);

        let permuted_input_blind = blinding.input_blind;
        let permuted_table_blind = blinding.table_blind;

        // These Lagrange values remain live until the lookup product is built.
        // Commit now, then consume them in the basis transforms after that
        // final use instead of cloning both base-domain buffers here.
        let (permuted_input_commitment, permuted_table_commitment) = crate::multicore::join(
            || {
                params
                    .commit_lagrange(&permuted_input_expression, permuted_input_blind)
                    .to_affine()
            },
            || {
                params
                    .commit_lagrange(&permuted_table_expression, permuted_table_blind)
                    .to_affine()
            },
        );

        Ok(PreparedPermuted {
            compressed_input_expression,
            compressed_input_coset,
            permuted_input_expression,
            permuted_input_commitment,
            permuted_input_blind,
            compressed_table_expression: Arc::clone(&table.compressed_expression),
            compressed_table_coset: table.compressed_coset.clone(),
            permuted_table_expression,
            permuted_table_commitment,
            permuted_table_blind,
        })
    }
}

/// Prepares lookup arguments while sharing fixed-table work across circuits.
///
/// Each tuple in `lookup_tasks` is `(circuit index, lookup index, blinding)`.
/// The returned values retain that task order so transcript writes remain in
/// circuit-major, lookup-major order.
#[allow(clippy::too_many_arguments)]
pub(in crate::plonk) fn prepare_permuted<C, Ev: Copy + Send + Sync, Ec: Copy + Send + Sync>(
    lookup_arguments: &[Argument<C::Scalar>],
    table_plan: TablePlan,
    lookup_tasks: Vec<(usize, usize, PermutedBlinding<C::Scalar>)>,
    pk: &ProvingKey<C>,
    params: &Params<C>,
    domain: &EvaluationDomain<C::Scalar>,
    value_evaluator: &poly::Evaluator<Ev, C::Scalar, LagrangeCoeff>,
    theta: ChallengeTheta<C>,
    advice_values: &[Vec<poly::AstLeaf<Ev, LagrangeCoeff>>],
    fixed_values: &[poly::AstLeaf<Ev, LagrangeCoeff>],
    instance_values: &[Vec<poly::AstLeaf<Ev, LagrangeCoeff>>],
    advice_cosets: &[Vec<poly::AstLeaf<Ec, ExtendedLagrangeCoeff>>],
    fixed_cosets: &[poly::AstLeaf<Ec, ExtendedLagrangeCoeff>],
    instance_cosets: &[Vec<poly::AstLeaf<Ec, ExtendedLagrangeCoeff>>],
    build_quotient_asts: bool,
) -> Result<Vec<PreparedPermuted<C, Ec>>, Error>
where
    C: CurveAffine,
    C::Scalar: WithSmallOrderMulGroup<3> + Ord,
    C::Curve: Mul<C::Scalar, Output = C::Curve> + MulAssign<C::Scalar>,
{
    let TablePlan {
        representatives: table_representatives,
        groups: table_groups,
        table_sort_scratch,
        input_sort_scratch,
    } = table_plan;
    assert_eq!(lookup_tasks.len(), input_sort_scratch.len());

    let usable_rows = params.n as usize - (pk.vk.cs.blinding_factors() + 1);

    // With one worker, direct table preparation avoids continuation overhead.
    if crate::multicore::current_num_threads() == 1 {
        let prepared_tables = table_representatives
            .into_par_iter()
            .zip(table_sort_scratch.into_par_iter())
            .map(|(lookup_index, sort_scratch)| {
                lookup_arguments[lookup_index].prepare_table(
                    domain,
                    value_evaluator,
                    *theta,
                    fixed_values,
                    fixed_cosets,
                    usable_rows,
                    build_quotient_asts,
                    sort_scratch,
                )
            })
            .collect::<Vec<_>>();

        return lookup_tasks
            .into_par_iter()
            .zip(input_sort_scratch.into_par_iter())
            .map(|((circuit_index, lookup_index, blinding), sort_scratch)| {
                let input = lookup_arguments[lookup_index].prepare_input(
                    domain,
                    value_evaluator,
                    *theta,
                    &advice_values[circuit_index],
                    fixed_values,
                    &instance_values[circuit_index],
                    &advice_cosets[circuit_index],
                    fixed_cosets,
                    &instance_cosets[circuit_index],
                    usable_rows,
                    build_quotient_asts,
                    sort_scratch,
                );
                lookup_arguments[lookup_index].finish_permuted(
                    pk,
                    params,
                    domain,
                    input,
                    &prepared_tables[table_groups[lookup_index]],
                    blinding,
                )
            })
            .collect();
    }

    let table_states = (0..table_representatives.len())
        .map(|_| {
            Mutex::new(TableState::<C, Ec> {
                table: None,
                pending: Vec::new(),
            })
        })
        .collect::<Vec<_>>();
    let prepared = Mutex::new(
        (0..lookup_tasks.len())
            .map(|_| None)
            .collect::<Vec<Option<Result<PreparedPermuted<C, Ec>, Error>>>>(),
    );

    // Inputs and tables become ready independently. A completed input either
    // continues immediately or moves into its table's pending queue; no worker
    // blocks waiting for the other side. Results use task-indexed slots so the
    // caller retains circuit-major transcript order.
    crate::multicore::scope(|scope| {
        for (task_index, ((circuit_index, lookup_index, blinding), sort_scratch)) in
            lookup_tasks.into_iter().zip(input_sort_scratch).enumerate()
        {
            let state = &table_states[table_groups[lookup_index]];
            let prepared = &prepared;
            scope.spawn(move |_| {
                let input = lookup_arguments[lookup_index].prepare_input(
                    domain,
                    value_evaluator,
                    *theta,
                    &advice_values[circuit_index],
                    fixed_values,
                    &instance_values[circuit_index],
                    &advice_cosets[circuit_index],
                    fixed_cosets,
                    &instance_cosets[circuit_index],
                    usable_rows,
                    build_quotient_asts,
                    sort_scratch,
                );

                let mut pending = Some(PendingLookup {
                    task_index,
                    lookup_index,
                    input,
                    blinding,
                });
                let table = {
                    let mut state = state.lock().expect("table state is not poisoned");
                    if let Some(table) = &state.table {
                        Some(Arc::clone(table))
                    } else {
                        state
                            .pending
                            .push(pending.take().expect("the lookup task is available"));
                        None
                    }
                };

                if let Some(table) = table {
                    let pending = pending.expect("the lookup task is available");
                    let result = lookup_arguments[lookup_index].finish_permuted(
                        pk,
                        params,
                        domain,
                        pending.input,
                        &table,
                        pending.blinding,
                    );
                    prepared.lock().expect("results are not poisoned")[task_index] = Some(result);
                }
            });
        }

        for ((representative, sort_scratch), state) in table_representatives
            .into_iter()
            .zip(table_sort_scratch)
            .zip(&table_states)
        {
            let prepared = &prepared;
            scope.spawn(move |_| {
                let table = Arc::new(lookup_arguments[representative].prepare_table(
                    domain,
                    value_evaluator,
                    *theta,
                    fixed_values,
                    fixed_cosets,
                    usable_rows,
                    build_quotient_asts,
                    sort_scratch,
                ));
                let pending = {
                    let mut state = state.lock().expect("table state is not poisoned");
                    state.table = Some(Arc::clone(&table));
                    std::mem::take(&mut state.pending)
                };

                pending.into_par_iter().for_each(|pending| {
                    let result = lookup_arguments[pending.lookup_index].finish_permuted(
                        pk,
                        params,
                        domain,
                        pending.input,
                        &table,
                        pending.blinding,
                    );
                    prepared.lock().expect("results are not poisoned")[pending.task_index] =
                        Some(result);
                });
            });
        }
    });

    prepared
        .into_inner()
        .expect("results are not poisoned")
        .into_iter()
        .map(|result| result.expect("every lookup task produces one result"))
        .collect()
}

impl<C: CurveAffine, Ev: Copy + Send + Sync> PreparedPermuted<C, Ev> {
    /// Writes commitments and reserves coset leaves in circuit order.
    pub(in crate::plonk) fn finalize<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        evaluator: &mut poly::Evaluator<Ev, C::Scalar, ExtendedLagrangeCoeff>,
        transcript: &mut T,
        circuit_index: usize,
        lookup_index: usize,
    ) -> Result<Permuted<C, Ev>, Error> {
        transcript.write_point(self.permuted_input_commitment)?;
        transcript.write_point(self.permuted_table_commitment)?;

        let permuted_input_coset = evaluator.register_deferred_poly_with_tag(
            QuotientPoly::LookupPermutedInput {
                circuit_index,
                lookup_index,
            }
            .into(),
        );
        let permuted_table_coset = evaluator.register_deferred_poly_with_tag(
            QuotientPoly::LookupPermutedTable {
                circuit_index,
                lookup_index,
            }
            .into(),
        );

        Ok(Permuted {
            compressed_input_expression: self.compressed_input_expression,
            permuted_input_expression: self.permuted_input_expression,
            compressed_input_coset: self.compressed_input_coset,
            permuted_input_coset,
            permuted_input_blind: self.permuted_input_blind,
            compressed_table_expression: self.compressed_table_expression,
            compressed_table_coset: self.compressed_table_coset,
            permuted_table_expression: self.permuted_table_expression,
            permuted_table_coset,
            permuted_table_blind: self.permuted_table_blind,
        })
    }
}

impl<C: CurveAffine, Ev: Copy + Send + Sync> Permuted<C, Ev> {
    /// Constructs the grand product polynomial for this lookup.
    pub(in crate::plonk) fn prepare_product(
        self,
        pk: &ProvingKey<C>,
        params: &Params<C>,
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        blinding: ProductBlinding<C::Scalar>,
    ) -> PreparedProduct<C, Ev> {
        let blinding_factors = pk.vk.cs.blinding_factors();
        assert_eq!(blinding.rows.len(), blinding_factors);
        // Goal is to compute the products of fractions
        //
        // Numerator: (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        //            * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        // Denominator: (a'(\omega^i) + \beta) (s'(\omega^i) + \gamma)
        //
        // where a_j(X) is the jth input expression in this lookup,
        // where a'(X) is the compression of the permuted input expressions,
        // s_j(X) is the jth table expression in this lookup,
        // s'(X) is the compression of the permuted table expressions,
        // and i is the ith row of the expression.
        let mut lookup_product = vec![C::Scalar::ZERO; params.n as usize];
        // Denominator uses the permuted input expression and permuted table expression
        parallelize(&mut lookup_product, |lookup_product, start| {
            for ((lookup_product, permuted_input_value), permuted_table_value) in lookup_product
                .iter_mut()
                .zip(self.permuted_input_expression[start..].iter())
                .zip(self.permuted_table_expression[start..].iter())
            {
                *lookup_product = (*beta + permuted_input_value) * &(*gamma + permuted_table_value);
            }
        });

        // Batch invert to obtain the denominators for the lookup product
        // polynomials
        crate::arithmetic::batch_invert_multi(&mut lookup_product);

        // Finish the computation of the entire fraction by computing the numerators
        // (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        // * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        parallelize(&mut lookup_product, |product, start| {
            for ((product, &input_term), &table_term) in product
                .iter_mut()
                .zip(self.compressed_input_expression[start..].iter())
                .zip(self.compressed_table_expression[start..].iter())
            {
                *product *= &(input_term + &*beta);
                *product *= &(table_term + &*gamma);
            }
        });

        // The product vector is a vector of products of fractions of the form
        //
        // Numerator: (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        //            * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        // Denominator: (a'(\omega^i) + \beta) (s'(\omega^i) + \gamma)
        //
        // where there are m input expressions and m table expressions,
        // a_j(\omega^i) is the jth input expression in this lookup,
        // a'j(\omega^i) is the permuted input expression,
        // s_j(\omega^i) is the jth table expression in this lookup,
        // s'(\omega^i) is the permuted table expression,
        // and i is the ith row of the expression.

        // Compute the evaluations of the lookup product polynomial
        // over our domain, starting with z[0] = 1
        // Reuse the fraction vector for z instead of allocating a second
        // domain-sized vector. This includes the "last" row, which should be
        // a boolean (and ideally 1, else soundness is broken).
        let usable_rows = params.n as usize - blinding_factors;
        let mut state = C::Scalar::ONE;
        for product in lookup_product.iter_mut().take(usable_rows) {
            let current = *product;
            *product = state;
            state *= &current;
        }
        lookup_product.truncate(usable_rows);
        lookup_product.extend(blinding.rows);
        assert_eq!(lookup_product.len(), params.n as usize);
        let z = pk.vk.domain.lagrange_from_vec(lookup_product);

        #[cfg(feature = "sanity-checks")]
        // This test works only with intermediate representations in this method.
        // It can be used for debugging purposes.
        {
            // While in Lagrange basis, check that product is correctly constructed
            let u = (params.n as usize) - (blinding_factors + 1);

            // l_0(X) * (1 - z(X)) = 0
            assert_eq!(z[0], C::Scalar::ONE);

            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            // - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
            for i in 0..u {
                let mut left = z[i + 1];
                let permuted_input_value = &self.permuted_input_expression[i];

                let permuted_table_value = &self.permuted_table_expression[i];

                left *= &(*beta + permuted_input_value);
                left *= &(*gamma + permuted_table_value);

                let mut right = z[i];
                let mut input_term = self.compressed_input_expression[i];

                let mut table_term = self.compressed_table_expression[i];

                input_term += &(*beta);
                table_term += &(*gamma);
                right *= &(input_term * &table_term);

                assert_eq!(left, right);
            }

            // l_last(X) * (z(X)^2 - z(X)) = 0
            // Assertion will fail only when soundness is broken, in which
            // case this z[u] value will be zero. (bad!)
            assert_eq!(z[u], C::Scalar::ONE);
        }

        let Permuted {
            compressed_input_expression: _,
            permuted_input_expression,
            compressed_input_coset,
            permuted_input_coset,
            permuted_input_blind,
            compressed_table_expression: _,
            compressed_table_coset,
            permuted_table_expression,
            permuted_table_coset,
            permuted_table_blind,
        } = self;
        let transform_permuted = |values| {
            let polynomial = pk
                .vk
                .domain
                .lagrange_to_coeff_with_twiddles(values, &pk.fft_twiddles);
            let coset = pk
                .vk
                .domain
                .coeff_to_extended_with_twiddles(polynomial.clone(), &pk.fft_twiddles);
            (polynomial, coset)
        };

        let product_blind = blinding.product_blind;
        let (
            (
                (permuted_input_poly, permuted_input_coset_values),
                (permuted_table_poly, permuted_table_coset_values),
            ),
            (product_commitment, (z, product_coset)),
        ) = crate::multicore::join(
            || {
                crate::multicore::join(
                    || transform_permuted(permuted_input_expression),
                    || transform_permuted(permuted_table_expression),
                )
            },
            || {
                crate::multicore::join(
                    || params.commit_lagrange(&z, product_blind).to_affine(),
                    || {
                        let z = pk
                            .vk
                            .domain
                            .lagrange_to_coeff_with_twiddles(z.clone(), &pk.fft_twiddles);
                        let coset = pk
                            .vk
                            .domain
                            .coeff_to_extended_with_twiddles(z.clone(), &pk.fft_twiddles);
                        (z, coset)
                    },
                )
            },
        );

        PreparedProduct {
            compressed_input_coset,
            permuted_input_poly,
            permuted_input_coset,
            permuted_input_coset_values,
            permuted_input_blind,
            compressed_table_coset,
            permuted_table_poly,
            permuted_table_coset,
            permuted_table_coset_values,
            permuted_table_blind,
            product_poly: z,
            product_coset,
            product_commitment,
            product_blind,
        }
    }
}

impl<C: CurveAffine, Ev: Copy + Send + Sync> PreparedProduct<C, Ev> {
    /// Writes the product commitment and registers its coset in circuit order.
    pub(in crate::plonk) fn finalize<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        evaluator: &mut poly::Evaluator<Ev, C::Scalar, ExtendedLagrangeCoeff>,
        transcript: &mut T,
        circuit_index: usize,
        lookup_index: usize,
    ) -> Result<Committed<C, Ev>, Error> {
        evaluator.fill_deferred_poly(self.permuted_input_coset, self.permuted_input_coset_values);
        evaluator.fill_deferred_poly(self.permuted_table_coset, self.permuted_table_coset_values);
        let product_coset = evaluator.register_poly_with_tag(
            self.product_coset,
            QuotientPoly::LookupProduct {
                circuit_index,
                lookup_index,
            }
            .into(),
        );

        // Hash product commitment.
        transcript.write_point(self.product_commitment)?;

        Ok(Committed {
            compressed_input_coset: self.compressed_input_coset,
            permuted_input_poly: self.permuted_input_poly,
            permuted_input_coset: self.permuted_input_coset,
            permuted_input_blind: self.permuted_input_blind,
            compressed_table_coset: self.compressed_table_coset,
            permuted_table_poly: self.permuted_table_poly,
            permuted_table_coset: self.permuted_table_coset,
            permuted_table_blind: self.permuted_table_blind,
            product_poly: self.product_poly,
            product_coset,
            product_blind: self.product_blind,
        })
    }
}

/// Builds the lookup constraint ASTs without evaluating polynomial rows.
pub(in crate::plonk) fn construct_constraints<E: Copy, F: Field>(
    compressed_input: poly::Ast<E, F, ExtendedLagrangeCoeff>,
    permuted_input: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    compressed_table: poly::Ast<E, F, ExtendedLagrangeCoeff>,
    permuted_table: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    product: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    l0: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    l_blind: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    l_last: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
) -> impl Iterator<Item = poly::Ast<E, F, ExtendedLagrangeCoeff>> {
    let active_rows = poly::Ast::one() - (poly::Ast::from(l_last) + l_blind);
    let beta = poly::Ast::ChallengeTerm(poly::EvaluationChallenge::Beta);
    let gamma = poly::Ast::ChallengeTerm(poly::EvaluationChallenge::Gamma);

    iter::empty()
        // l_0(X) * (1 - z(X)) = 0
        .chain(Some((poly::Ast::one() - product) * l0))
        // l_last(X) * (z(X)^2 - z(X)) = 0
        .chain(Some(
            (poly::Ast::from(product) * product - product) * l_last,
        ))
        // (1 - (l_last(X) + l_blind(X))) * (
        //   z(omega X) (a'(X) + beta) (s'(X) + gamma)
        //   - z(X) (compressed_input(X) + beta)
        //     (compressed_table(X) + gamma)
        // ) = 0
        .chain({
            let left: poly::Ast<_, _, _> =
                poly::Ast::<_, F, _>::from(product.with_rotation(Rotation::next()))
                    * (poly::Ast::from(permuted_input) + beta.clone())
                    * (poly::Ast::from(permuted_table) + gamma.clone());

            let right: poly::Ast<_, _, _> =
                poly::Ast::from(product) * (compressed_input + beta) * (compressed_table + gamma);

            Some((left - right) * active_rows.clone())
        })
        // l_0(X) * (a'(X) - s'(X)) = 0
        .chain(Some(
            (poly::Ast::from(permuted_input) - permuted_table) * l0,
        ))
        // (1 - (l_last + l_blind)) *
        // (a'(X) - s'(X)) * (a'(X) - a'(omega^-1 X)) = 0
        .chain(Some(
            (poly::Ast::<_, F, _>::from(permuted_input) - permuted_table)
                * (poly::Ast::from(permuted_input)
                    - permuted_input.with_rotation(Rotation::prev()))
                * active_rows,
        ))
}

impl<'a, C: CurveAffine, Ev: Copy + Send + Sync + 'a> Committed<C, Ev> {
    /// Finishes the lookup argument without rebuilding its quotient ASTs.
    pub(in crate::plonk) fn into_constructed(self) -> Constructed<C> {
        Constructed {
            permuted_input_poly: self.permuted_input_poly,
            permuted_input_blind: self.permuted_input_blind,
            permuted_table_poly: self.permuted_table_poly,
            permuted_table_blind: self.permuted_table_blind,
            product_poly: self.product_poly,
            product_blind: self.product_blind,
        }
    }

    /// Given a Lookup with input expressions, table expressions, permuted input
    /// expression, permuted table expression, and grand product polynomial, this
    /// method constructs constraints that must hold between these values.
    /// This method returns the constraints as a vector of ASTs for polynomials in
    /// the extended evaluation domain.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn construct(
        self,
        argument: &Argument<C::Scalar>,
        fixed_cosets: &[poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        advice_cosets: &[poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        instance_cosets: &[poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        l0: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
        l_blind: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
        l_last: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    ) -> (
        Constructed<C>,
        impl Iterator<Item = poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>> + 'a,
    ) {
        let compressed_input_coset = self.compressed_input_coset.unwrap_or_else(|| {
            compress_expressions_coset(
                &argument.input_expressions,
                fixed_cosets,
                advice_cosets,
                instance_cosets,
            )
        });
        let compressed_table_coset = self.compressed_table_coset.unwrap_or_else(|| {
            compress_expressions_coset(
                &argument.table_expressions,
                fixed_cosets,
                advice_cosets,
                instance_cosets,
            )
        });
        let expressions = construct_constraints(
            compressed_input_coset,
            self.permuted_input_coset,
            compressed_table_coset,
            self.permuted_table_coset,
            self.product_coset,
            l0,
            l_blind,
            l_last,
        );

        (
            Constructed {
                permuted_input_poly: self.permuted_input_poly,
                permuted_input_blind: self.permuted_input_blind,
                permuted_table_poly: self.permuted_table_poly,
                permuted_table_blind: self.permuted_table_blind,
                product_poly: self.product_poly,
                product_blind: self.product_blind,
            },
            expressions,
        )
    }
}

impl<C: CurveAffine> Constructed<C> {
    pub(in crate::plonk) fn evaluation_queries(&self) -> [EvaluationQuery<'_, C::Scalar>; 5] {
        [
            EvaluationQuery {
                polynomial: &self.product_poly,
                point: EvaluationPoint::Current,
            },
            EvaluationQuery {
                polynomial: &self.product_poly,
                point: EvaluationPoint::Next,
            },
            EvaluationQuery {
                polynomial: &self.permuted_input_poly,
                point: EvaluationPoint::Current,
            },
            EvaluationQuery {
                polynomial: &self.permuted_input_poly,
                point: EvaluationPoint::Previous,
            },
            EvaluationQuery {
                polynomial: &self.permuted_table_poly,
                point: EvaluationPoint::Current,
            },
        ]
    }

    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        evaluations: &mut impl Iterator<Item = C::Scalar>,
        transcript: &mut T,
    ) -> Result<Evaluated<C>, Error> {
        // Hash each advice evaluation.
        for _ in 0..self.evaluation_queries().len() {
            let evaluation = evaluations
                .next()
                .expect("one result is returned for every lookup evaluation query");
            transcript.write_scalar(evaluation)?;
        }

        Ok(Evaluated { constructed: self })
    }
}

impl<C: CurveAffine> Evaluated<C> {
    pub(in crate::plonk) fn open<'a>(
        &'a self,
        pk: &'a ProvingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = ProverQuery<'a, C>> + Clone {
        let x_inv = pk.vk.domain.rotate_omega(*x, Rotation::prev());
        let x_next = pk.vk.domain.rotate_omega(*x, Rotation::next());

        iter::empty()
            // Open lookup product commitments at x
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.product_poly,
                blind: self.constructed.product_blind,
            }))
            // Open lookup input commitments at x
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.permuted_input_poly,
                blind: self.constructed.permuted_input_blind,
            }))
            // Open lookup table commitments at x
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.permuted_table_poly,
                blind: self.constructed.permuted_table_blind,
            }))
            // Open lookup input commitments at x_inv
            .chain(Some(ProverQuery {
                point: x_inv,
                poly: &self.constructed.permuted_input_poly,
                blind: self.constructed.permuted_input_blind,
            }))
            // Open lookup product commitments at x_next
            .chain(Some(ProverQuery {
                point: x_next,
                poly: &self.constructed.product_poly,
                blind: self.constructed.product_blind,
            }))
    }
}

#[cfg(test)]
fn permute_usable_values<F: Field + Ord>(
    mut input_values: Vec<F>,
    mut table_values: Vec<F>,
) -> Result<(Vec<F>, Vec<F>), Error> {
    assert_eq!(input_values.len(), table_values.len());

    let scratch_len = if uses_pasta_sort_keys::<F>() {
        input_values.len()
    } else {
        0
    };
    let mut input_keys = vec![PastaSortKey::EMPTY; scratch_len];
    let mut table_keys = vec![PastaSortKey::EMPTY; scratch_len];
    crate::multicore::join(
        || sort_lookup_values(&mut input_values, &mut input_keys),
        || sort_lookup_values(&mut table_values, &mut table_keys),
    );

    permute_sorted_values(input_values, &input_keys, &table_values, &table_keys)
}

fn permute_sorted_values<F: Field + Ord>(
    input_values: Vec<F>,
    input_keys: &[PastaSortKey],
    table_values: &[F],
    table_keys: &[PastaSortKey],
) -> Result<(Vec<F>, Vec<F>), Error> {
    assert_eq!(input_values.len(), table_values.len());
    assert_eq!(input_keys.is_empty(), table_keys.is_empty());
    if input_keys.is_empty() {
        debug_assert!(input_values.windows(2).all(|pair| pair[0] <= pair[1]));
        debug_assert!(table_values.windows(2).all(|pair| pair[0] <= pair[1]));
        let permuted_table_values = permute_sorted_values_by(
            &input_values,
            table_values,
            |row| input_values[row] == input_values[row - 1],
            |table_row, input_row| table_values[table_row] < input_values[input_row],
            |table_row, input_row| table_values[table_row] == input_values[input_row],
        )?;
        return Ok((input_values, permuted_table_values));
    }

    assert_eq!(input_values.len(), input_keys.len());
    assert_eq!(table_values.len(), table_keys.len());
    debug_assert!(input_keys.windows(2).all(|pair| pair[0] <= pair[1]));
    debug_assert!(table_keys.windows(2).all(|pair| pair[0] <= pair[1]));
    let permuted_table_values = permute_sorted_values_by(
        &input_values,
        table_values,
        |row| input_keys[row] == input_keys[row - 1],
        |table_row, input_row| table_keys[table_row] < input_keys[input_row],
        |table_row, input_row| table_keys[table_row] == input_keys[input_row],
    )?;
    Ok((input_values, permuted_table_values))
}

fn permute_sorted_values_by<F: Field, SameInput, TableLess, TableSame>(
    input_values: &[F],
    table_values: &[F],
    same_input: SameInput,
    table_less: TableLess,
    table_same: TableSame,
) -> Result<Vec<F>, Error>
where
    SameInput: Fn(usize) -> bool,
    TableLess: Fn(usize, usize) -> bool,
    TableSame: Fn(usize, usize) -> bool,
{
    let usable_rows = input_values.len();
    let mut permuted_table_values = vec![F::ZERO; usable_rows];
    let mut consumed_table_rows = Vec::new();
    let mut table_row = 0;

    let mut repeated_input_rows = input_values
        .iter()
        .zip(permuted_table_values.iter_mut())
        .enumerate()
        .filter_map(|(row, (input_value, table_value))| {
            if row == 0 || !same_input(row) {
                *table_value = *input_value;
                while table_row < usable_rows && table_less(table_row, row) {
                    table_row += 1;
                }
                if table_row < usable_rows && table_same(table_row, row) {
                    consumed_table_rows.push(table_row);
                    table_row += 1;
                    None
                } else {
                    Some(Err(Error::ConstraintSystemFailure))
                }
            } else {
                Some(Ok(row))
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    let mut consumed_table_rows = consumed_table_rows.into_iter().peekable();
    for (row, value) in table_values.iter().copied().enumerate() {
        if consumed_table_rows.peek() == Some(&row) {
            consumed_table_rows.next();
        } else {
            permuted_table_values[repeated_input_rows.pop().unwrap()] = value;
        }
    }
    assert!(consumed_table_rows.next().is_none());
    assert!(repeated_input_rows.is_empty());

    Ok(permuted_table_values)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use pasta_curves::pallas;

    use super::*;
    use crate::plonk::circuit::FixedQuery;

    const TEST_ALPHABET_SIZE: usize = 3;

    // This is the previous BTreeMap implementation, retained as an oracle for
    // exact output ordering and error behavior.
    fn reference_permutation<F: Field + Ord>(
        mut input_values: Vec<F>,
        table_values: Vec<F>,
    ) -> Result<(Vec<F>, Vec<F>), Error> {
        input_values.sort();
        let mut leftovers = table_values
            .into_iter()
            .fold(BTreeMap::new(), |mut counts, value| {
                *counts.entry(value).or_insert(0_u32) += 1;
                counts
            });
        let mut permuted_table_values = vec![F::ZERO; input_values.len()];
        let mut repeated_input_rows = input_values
            .iter()
            .zip(permuted_table_values.iter_mut())
            .enumerate()
            .filter_map(|(row, (input_value, table_value))| {
                if row == 0 || *input_value != input_values[row - 1] {
                    *table_value = *input_value;
                    if let Some(count) = leftovers.get_mut(input_value) {
                        assert!(*count > 0);
                        *count -= 1;
                        None
                    } else {
                        Some(Err(Error::ConstraintSystemFailure))
                    }
                } else {
                    Some(Ok(row))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        for (value, count) in leftovers {
            for _ in 0..count {
                permuted_table_values[repeated_input_rows.pop().unwrap()] = value;
            }
        }
        assert!(repeated_input_rows.is_empty());

        Ok((input_values, permuted_table_values))
    }

    fn values(values: &[u64]) -> Vec<pallas::Scalar> {
        values.iter().copied().map(pallas::Scalar::from).collect()
    }

    fn check_table_sort<F: PrimeField<Repr = [u8; PASTA_REPR_BYTES]> + Ord>() {
        let mut expected = (0..1024_u64)
            .flat_map(|value| {
                let value = F::from(value.wrapping_mul(0x9e37_79b9));
                [value, -value, value]
            })
            .collect::<Vec<_>>();
        let mut actual = expected.clone();
        expected.sort_unstable();
        let mut scratch = vec![PastaSortKey::EMPTY; actual.len()];
        sort_lookup_values(&mut actual, &mut scratch);
        assert_eq!(actual, expected);

        actual.reverse();
        sort_lookup_values(&mut actual, &mut scratch);
        assert_eq!(actual, expected);
    }

    #[test]
    fn table_sort_matches_field_order() {
        check_table_sort::<pallas::Base>();
        check_table_sort::<pallas::Scalar>();
    }

    fn small_vectors<F: PrimeField>(len: usize) -> Vec<Vec<F>> {
        (0..TEST_ALPHABET_SIZE.pow(u32::try_from(len).expect("test length fits in u32")))
            .map(|mut encoded| {
                (0..len)
                    .map(|_| {
                        let value = u64::try_from(encoded % TEST_ALPHABET_SIZE)
                            .expect("test alphabet values fit in u64");
                        encoded /= TEST_ALPHABET_SIZE;
                        F::from(value)
                    })
                    .collect()
            })
            .collect()
    }

    fn lookup_with_table(queries: &[(usize, usize, i32)]) -> Argument<pallas::Scalar> {
        Argument {
            input_expressions: Vec::new(),
            table_expressions: queries
                .iter()
                .map(|(index, column_index, rotation)| {
                    Expression::Fixed(FixedQuery {
                        index: *index,
                        column_index: *column_index,
                        rotation: Rotation(*rotation),
                    })
                })
                .collect(),
        }
    }

    #[test]
    fn identical_fixed_table_queries_share_preparation() {
        let table = lookup_with_table(&[(1, 0, 0), (3, 2, -1)]);
        assert!(table.has_same_table(&lookup_with_table(&[(1, 0, 0), (3, 2, -1)])));
        assert!(!table.has_same_table(&lookup_with_table(&[(1, 0, 0)])));
        assert!(!table.has_same_table(&lookup_with_table(&[(1, 0, 0), (4, 2, -1)])));
        assert!(!table.has_same_table(&lookup_with_table(&[(3, 2, -1), (1, 0, 0)])));

        let plan = prepare_table_plan(
            &[
                table,
                lookup_with_table(&[(1, 0, 0), (3, 2, -1)]),
                lookup_with_table(&[(1, 0, 0)]),
            ],
            2,
            17,
        );
        assert_eq!(plan.representatives, [0, 2]);
        assert_eq!(plan.groups, [0, 0, 1]);
        assert_eq!(plan.table_sort_scratch.len(), 2);
        assert!(
            plan.table_sort_scratch
                .iter()
                .all(|scratch| scratch.len() == 17)
        );
        assert_eq!(plan.input_sort_scratch.len(), 6);
        assert!(
            plan.input_sort_scratch
                .iter()
                .all(|scratch| scratch.len() == 17)
        );
    }

    fn check_lookup_permutation_exhaustively<F>()
    where
        F: PrimeField<Repr = [u8; PASTA_REPR_BYTES]> + Ord,
    {
        for len in 0..=4 {
            let vectors = small_vectors::<F>(len);
            for input in &vectors {
                for table in &vectors {
                    let actual = permute_usable_values(input.clone(), table.clone());
                    match reference_permutation(input.clone(), table.clone()) {
                        Ok(expected) => assert_eq!(actual.unwrap(), expected),
                        Err(Error::ConstraintSystemFailure) => {
                            assert!(matches!(actual, Err(Error::ConstraintSystemFailure)))
                        }
                        Err(_) => panic!("reference returned an unexpected error"),
                    }
                }
            }
        }
    }

    #[test]
    fn sorted_lookup_permutation_matches_reference_exhaustively() {
        check_lookup_permutation_exhaustively::<pallas::Base>();
        check_lookup_permutation_exhaustively::<pallas::Scalar>();
    }

    #[test]
    fn sorted_lookup_permutation_preserves_output_order() {
        let input = values(&[2, 2, 5, 1, 7, 2, 6, 4]);
        let table = values(&[5, 1, 2, 3, 2, 4, 6, 7]);

        assert_eq!(
            permute_usable_values(input, table).unwrap(),
            (
                values(&[1, 2, 2, 2, 4, 5, 6, 7]),
                values(&[1, 2, 3, 2, 4, 5, 6, 7]),
            )
        );
    }

    #[test]
    fn sorted_lookup_permutation_rejects_missing_value() {
        let input = values(&[1, 2, 2, 7]);
        let table = values(&[1, 2, 3, 4]);

        assert!(matches!(
            permute_usable_values(input.clone(), table.clone()),
            Err(Error::ConstraintSystemFailure)
        ));
        assert!(matches!(
            reference_permutation(input, table),
            Err(Error::ConstraintSystemFailure)
        ));
    }
}
