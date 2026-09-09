use super::super::{
    ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, Error, ProvingKey,
    circuit::Expression, evaluator_schedule::QuotientPoly,
};
use super::Argument;
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
use crate::PERMUTED_U10_TABLE_SUFFIX_TERMS;
#[cfg(feature = "multicore")]
use crate::{
    PREPARED_SORTED_U10_COMMITMENT_K, PreparedLookupCommitments, SORTED_U10_SUFFIX_MULTIPLES,
    arithmetic::best_multiexp,
};
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
#[cfg(feature = "multicore")]
use group::Group;
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
    sinsemilla_q_0: Option<(F, usize)>,
    #[cfg(feature = "multicore")]
    sorted_u10_range: bool,
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

/// Require factoring to remove at least one quarter of the usable terms.
/// This also guards the structural Sinsemilla marker against unrelated tables
/// that happen to have the same lookup shape.
const SINSEMILLA_Q_0_MIN_REPETITION_FRACTION_DENOMINATOR: usize = 4;

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

#[cfg(feature = "multicore")]
const SORTED_U10_BITS: usize = 10;
#[cfg(feature = "multicore")]
const SORTED_U10_MAX_VALUE: u16 = (1 << SORTED_U10_BITS) - 1;
/// Upper bound on the independently blinded tail handled by this route.
/// This covers Orchard's current blind rows while keeping the tail on-stack.
#[cfg(feature = "multicore")]
const SORTED_U10_MAX_SUFFIX: usize = 8;

#[cfg(feature = "multicore")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SortedU10Transition {
    row: u16,
    delta: u16,
}

#[cfg(feature = "multicore")]
struct SortedU10 {
    transitions: Vec<SortedU10Transition>,
    first: u16,
    last: u16,
}

#[cfg(feature = "multicore")]
fn pasta_u10(key: &PastaSortKey) -> Option<u16> {
    if key.limbs[1..].iter().any(|&limb| limb != 0)
        || key.limbs[0] > u64::from(SORTED_U10_MAX_VALUE)
    {
        return None;
    }
    u16::try_from(key.limbs[0]).ok()
}

#[cfg(feature = "multicore")]
impl SortedU10 {
    fn new(first_key: &PastaSortKey) -> Option<Self> {
        let first = pasta_u10(first_key)?;
        Some(Self {
            transitions: Vec::with_capacity(usize::from(SORTED_U10_MAX_VALUE)),
            first,
            last: first,
        })
    }

    fn push_distinct(&mut self, row: usize, key: &PastaSortKey) -> Option<()> {
        let value = pasta_u10(key)?;
        let delta = value.checked_sub(self.last)?;
        if delta == 0 {
            return None;
        }
        self.transitions.push(SortedU10Transition {
            row: u16::try_from(row).ok()?,
            delta,
        });
        self.last = value;
        Some(())
    }
}

#[cfg(feature = "multicore")]
fn prepared_sorted_u10_suffix_multiples<C: CurveAffine>(
    params: &Params<C>,
    sorted_u10_range: bool,
    usable_rows: usize,
    input_len: usize,
) -> Option<&[C]> {
    if !sorted_u10_range
        || usable_rows == 0
        || usable_rows > params.n as usize
        || input_len != usable_rows
        || params.n as usize - usable_rows > SORTED_U10_MAX_SUFFIX
    {
        return None;
    }
    let suffix_multiples = params.prepared_lagrange_suffix_multiples()?;
    if suffix_multiples.len() != params.g_lagrange.len() * SORTED_U10_SUFFIX_MULTIPLES {
        return None;
    }
    Some(suffix_multiples)
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
    table_kinds: Vec<PreparedTableKind>,
    table_sort_scratch: Vec<Vec<PastaSortKey>>,
    input_sort_scratch: Vec<Vec<PastaSortKey>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PreparedTableKind {
    Generic,
    Sinsemilla,
    #[cfg(feature = "multicore")]
    SortedU10Range,
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

fn factorable_sinsemilla_q_0<F: Field + Ord>(sorted_values: &[F], q_0: F) -> Option<(F, usize)> {
    debug_assert!(sorted_values.windows(2).all(|pair| pair[0] <= pair[1]));
    if sorted_values.is_empty() || bool::from(q_0.is_zero()) {
        return None;
    }

    let q_0_terms = sorted_values.iter().filter(|&&value| value == q_0).count();
    (q_0_terms
        >= sorted_values
            .len()
            .div_ceil(SINSEMILLA_Q_0_MIN_REPETITION_FRACTION_DENOMINATOR))
    .then_some((q_0, q_0_terms))
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
    fn has_same_fixed_query(left: &Expression<F>, right: &Expression<F>) -> bool {
        match (left, right) {
            (Expression::Fixed(left), Expression::Fixed(right)) => {
                left.index == right.index
                    && left.column_index == right.column_index
                    && left.rotation == right.rotation
            }
            _ => false,
        }
    }

    fn has_same_table(&self, other: &Self) -> bool {
        self.table_expressions.len() == other.table_expressions.len()
            && self
                .table_expressions
                .iter()
                .zip(other.table_expressions.iter())
                .all(|(left, right)| Self::has_same_fixed_query(left, right))
    }

    fn has_sinsemilla_table_shape(&self, arguments: &[Self], uses: usize) -> bool {
        let [
            Expression::Fixed(index),
            Expression::Fixed(x),
            Expression::Fixed(y),
        ] = self.table_expressions.as_slice()
        else {
            return false;
        };
        let current_rotation = Rotation::cur();
        uses > 1
            && [index, x, y]
                .iter()
                .all(|query| query.rotation == current_rotation)
            && index.column_index != x.column_index
            && index.column_index != y.column_index
            && x.column_index != y.column_index
            && arguments.iter().any(|argument| {
                argument.table_expressions.len() == 1
                    && Self::has_same_fixed_query(
                        &self.table_expressions[0],
                        &argument.table_expressions[0],
                    )
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
    let mut group_uses = vec![0usize; representatives.len()];
    for &group in &groups {
        group_uses[group] += 1;
    }
    // Orchard's Sinsemilla table is the reused three-column generator lookup
    // whose index column is also used by the 10-bit range check. This private
    // structural marker avoids adding a circuit-configuration hint to the
    // public API. The q_0 repetition threshold below guards lookalike tables.
    let sinsemilla_tables = representatives
        .iter()
        .enumerate()
        .map(|(group, &representative)| {
            lookup_arguments[representative]
                .has_sinsemilla_table_shape(lookup_arguments, group_uses[group])
        })
        .collect::<Vec<_>>();
    let table_kinds = representatives
        .iter()
        .enumerate()
        .map(|(group, &_representative)| {
            if sinsemilla_tables[group] {
                return PreparedTableKind::Sinsemilla;
            }
            // The 10-bit range-check table is the one-column view of the index
            // column in the structurally identified Sinsemilla generator
            // table. This only hints at routing; the sorted input must still
            // validate as an exact u10 profile.
            #[cfg(feature = "multicore")]
            if let [range_expression] = lookup_arguments[_representative]
                .table_expressions
                .as_slice()
                && representatives.iter().zip(&sinsemilla_tables).any(
                    |(&sinsemilla_representative, &is_sinsemilla)| {
                        is_sinsemilla
                            && Argument::has_same_fixed_query(
                                range_expression,
                                &lookup_arguments[sinsemilla_representative].table_expressions[0],
                            )
                    },
                )
            {
                return PreparedTableKind::SortedU10Range;
            }
            PreparedTableKind::Generic
        })
        .collect::<Vec<_>>();
    #[cfg(all(feature = "multicore", debug_assertions))]
    if sinsemilla_tables.iter().any(|&is_sinsemilla| is_sinsemilla) {
        debug_assert!(table_kinds.contains(&PreparedTableKind::SortedU10Range));
    }

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
        table_kinds,
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
        table_kind: PreparedTableKind,
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
        let q_0 = compressed_expression[0];
        let mut sorted_values = compressed_expression
            .iter()
            .take(usable_rows)
            .copied()
            .collect::<Vec<_>>();
        sort_lookup_values(&mut sorted_values, &mut sort_scratch);
        // The Sinsemilla generator lookup is padded with its first tuple. Its
        // theta-compressed value is therefore repeated over roughly half of
        // the table commitment. Keep this specialization at the table-MSM
        // boundary instead of changing generic MSM routing.
        let sinsemilla_q_0 = (table_kind == PreparedTableKind::Sinsemilla)
            .then(|| factorable_sinsemilla_q_0(&sorted_values, q_0))
            .flatten();

        PreparedTable {
            compressed_expression: Arc::new(compressed_expression),
            compressed_coset,
            sorted_values,
            sorted_keys: sort_scratch,
            sinsemilla_q_0,
            #[cfg(feature = "multicore")]
            sorted_u10_range: table_kind == PreparedTableKind::SortedU10Range,
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
        // These values gain blind rows in `finish_permuted`, as does the
        // table permutation derived from them. Retain full-domain capacity
        // for both vectors.
        let mut sorted_values = Vec::with_capacity(compressed_expression.len());
        sorted_values.extend(compressed_expression.iter().take(usable_rows).copied());
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
        table: &PreparedTable<F, Ec>,
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
        #[cfg(feature = "multicore")]
        let sorted_u10_suffix_multiples = prepared_sorted_u10_suffix_multiples(
            params,
            table.sorted_u10_range,
            table.sorted_values.len(),
            sorted_input_keys.len(),
        );
        #[cfg(feature = "multicore")]
        let (mut permuted_input_values, mut permuted_table_values, sorted_u10) =
            if sorted_u10_suffix_multiples.is_some() {
                permute_sorted_values_with_sorted_u10(
                    sorted_input_values,
                    &sorted_input_keys,
                    &table.sorted_values,
                    &table.sorted_keys,
                )?
            } else {
                let (input, table) = permute_sorted_values(
                    sorted_input_values,
                    &sorted_input_keys,
                    &table.sorted_values,
                    &table.sorted_keys,
                )?;
                (input, table, None)
            };
        #[cfg(not(feature = "multicore"))]
        let (mut permuted_input_values, mut permuted_table_values) = permute_sorted_values(
            sorted_input_values,
            &sorted_input_keys,
            &table.sorted_values,
            &table.sorted_keys,
        )?;
        debug_assert_eq!(permuted_table_values.len(), table.sorted_values.len());

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

        #[cfg(all(feature = "multicore", debug_assertions))]
        if let Some(profile) = &sorted_u10 {
            let mut current = profile.first;
            let mut transitions = profile.transitions.iter().peekable();
            for (row, scalar) in permuted_input_expression
                .iter()
                .take(table.sorted_values.len())
                .enumerate()
            {
                if transitions
                    .peek()
                    .is_some_and(|transition| usize::from(transition.row) == row)
                {
                    current += transitions.next().unwrap().delta;
                }
                debug_assert_eq!(*scalar, F::from(u64::from(current)));
            }
            debug_assert!(transitions.next().is_none());
            debug_assert_eq!(current, profile.last);
        }

        let permuted_input_blind = blinding.input_blind;
        let permuted_table_blind = blinding.table_blind;

        // These Lagrange values remain live until the lookup product is built.
        // Commit now, then consume them in the basis transforms after that
        // final use instead of cloning both base-domain buffers here.
        let (permuted_input_commitment, permuted_table_commitment) = commit_permuted_pair(
            params,
            domain,
            &permuted_input_expression,
            permuted_input_blind,
            &permuted_table_expression,
            permuted_table_blind,
            table.sinsemilla_q_0,
            table.sorted_values.len(),
            #[cfg(feature = "multicore")]
            sorted_u10.as_ref().zip(sorted_u10_suffix_multiples),
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

#[cfg(feature = "multicore")]
fn commit_sorted_u10<C: CurveAffine>(
    params: &Params<C>,
    poly: &Polynomial<C::Scalar, LagrangeCoeff>,
    blind: Blind<C::Scalar>,
    usable_rows: usize,
    profile: &SortedU10,
    suffix_multiples: &[C],
) -> Option<C::Curve> {
    if params.k != PREPARED_SORTED_U10_COMMITMENT_K
        || poly.len() != params.n as usize
        || usable_rows == 0
        || usable_rows > poly.len()
        || poly.len() - usable_rows > SORTED_U10_MAX_SUFFIX
        || profile.first > profile.last
        || profile.last > SORTED_U10_MAX_VALUE
        || suffix_multiples.len() != params.g_lagrange.len() * SORTED_U10_SUFFIX_MULTIPLES
    {
        return None;
    }

    let mut previous_row = 0;
    let mut total_delta = 0u16;
    for transition in &profile.transitions {
        let row = usize::from(transition.row);
        if row == 0
            || row >= usable_rows
            || row <= previous_row
            || transition.delta == 0
            || total_delta.checked_add(transition.delta)? > profile.last - profile.first
        {
            return None;
        }
        previous_row = row;
        total_delta += transition.delta;
    }
    if total_delta != profile.last - profile.first {
        return None;
    }

    // Abel summation over full-domain suffix sums H_i:
    // x_0 H_0 + sum (x_i - x_{i - 1}) H_i
    //   = sum_{i < usable} x_i G_i + x_last H_usable.
    // Subtract x_last from every suffix scalar to cancel the final term.
    // Two independent projective chains expose instruction-level parallelism;
    // the outer scheduler supplies lookup- and Action-level concurrency.
    let mut prefix = [C::Curve::identity(); 2];
    let mut lane = 0;
    let mut add_multiple = |row: usize, scalar: u16| {
        let offset = row * SORTED_U10_SUFFIX_MULTIPLES;
        for _ in 0..scalar / 4 {
            prefix[lane] += suffix_multiples[offset + 2];
            lane ^= 1;
        }
        let remainder = scalar % 4;
        if remainder >= 2 {
            prefix[lane] += suffix_multiples[offset + 1];
            lane ^= 1;
        }
        if remainder & 1 != 0 {
            prefix[lane] += suffix_multiples[offset];
            lane ^= 1;
        }
    };
    add_multiple(0, profile.first);
    for transition in &profile.transitions {
        add_multiple(usize::from(transition.row), transition.delta);
    }
    let prefix = prefix[0] + prefix[1];

    let suffix_len = poly.len() - usable_rows;
    let term_len = suffix_len + 1;
    let correction = C::Scalar::from(u64::from(profile.last));
    let mut scalars = [C::Scalar::ZERO; SORTED_U10_MAX_SUFFIX + 1];
    for (scalar, value) in scalars[..suffix_len].iter_mut().zip(&poly[usable_rows..]) {
        *scalar = *value - correction;
    }
    scalars[suffix_len] = blind.0;
    let mut bases = [C::identity(); SORTED_U10_MAX_SUFFIX + 1];
    bases[..suffix_len].copy_from_slice(&params.g_lagrange[usable_rows..]);
    bases[suffix_len] = params.w;

    Some(prefix + best_multiexp::<C>(&scalars[..term_len], &bases[..term_len]))
}

#[cfg(all(feature = "multicore", not(feature = "orbits")))]
fn try_commit_permuted_u10_table<C: CurveAffine>(
    params: &Params<C>,
    poly: &Polynomial<C::Scalar, LagrangeCoeff>,
    blind: Blind<C::Scalar>,
    usable_rows: usize,
) -> Option<C::Curve> {
    if params.k != PREPARED_SORTED_U10_COMMITMENT_K
        || poly.len() != params.n as usize
        || usable_rows.checked_add(PERMUTED_U10_TABLE_SUFFIX_TERMS)? != poly.len()
    {
        return None;
    }
    let values: &[C::Scalar] = poly;
    params.commit_permuted_u10_table(&values[..usable_rows], &values[usable_rows..], blind)
}

#[allow(clippy::too_many_arguments)]
fn commit_permuted_pair<C: CurveAffine>(
    params: &Params<C>,
    domain: &EvaluationDomain<C::Scalar>,
    input: &Polynomial<C::Scalar, LagrangeCoeff>,
    input_blind: Blind<C::Scalar>,
    table: &Polynomial<C::Scalar, LagrangeCoeff>,
    table_blind: Blind<C::Scalar>,
    sinsemilla_q_0: Option<(C::Scalar, usize)>,
    usable_rows: usize,
    #[cfg(feature = "multicore")] sorted_u10: Option<(&SortedU10, &[C])>,
) -> (C, C) {
    // The 10-bit range-check input stays sorted, so its prefix can use cached
    // Lagrange suffix sums. Other inputs use linearity:
    // C(input, r_i) = C(table, r_t) + C(input - table, r_i - r_t).
    // The lookup construction makes that delta sparse.
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    let permuted_u10_table = sorted_u10.is_some();
    let (table_commitment, (input_or_difference, direct_input)) = crate::multicore::join(
        || {
            #[cfg(all(feature = "multicore", not(feature = "orbits")))]
            if permuted_u10_table
                && let Some(commitment) =
                    try_commit_permuted_u10_table(params, table, table_blind, usable_rows)
            {
                return commitment;
            }
            commit_sinsemilla_table(params, table, table_blind, sinsemilla_q_0, usable_rows)
        },
        || {
            #[cfg(feature = "multicore")]
            let direct_input = sorted_u10.and_then(|(profile, suffix_multiples)| {
                commit_sorted_u10(
                    params,
                    input,
                    input_blind,
                    usable_rows,
                    profile,
                    suffix_multiples,
                )
            });
            #[cfg(not(feature = "multicore"))]
            let direct_input: Option<C::Curve> = None;

            if let Some(commitment) = direct_input {
                (commitment, true)
            } else {
                (
                    commit_lagrange_difference(
                        params,
                        domain,
                        input,
                        table,
                        Blind(input_blind.0 - table_blind.0),
                    ),
                    false,
                )
            }
        },
    );
    let input_commitment = if direct_input {
        input_or_difference
    } else {
        table_commitment + input_or_difference
    };
    let projective = [input_commitment, table_commitment];
    let mut affine = [C::identity(); 2];
    C::Curve::batch_normalize(&projective, &mut affine);
    (affine[0], affine[1])
}

fn commit_sinsemilla_table<C: CurveAffine>(
    params: &Params<C>,
    polynomial: &Polynomial<C::Scalar, LagrangeCoeff>,
    blind: Blind<C::Scalar>,
    sinsemilla_q_0: Option<(C::Scalar, usize)>,
    usable_rows: usize,
) -> C::Curve {
    let Some((q_0, q_0_count)) = sinsemilla_q_0 else {
        return params.commit_lagrange(polynomial, blind);
    };

    // Factor the Sinsemilla table's repeated q_0 without changing any other
    // scalar. The dedicated prepared-table path sums the selected Lagrange
    // bases into S_U, then adds [q_0] S_U. Existing zero and low-magnitude
    // behavior is therefore preserved for every remaining coefficient.
    params
        .try_commit_sinsemilla_table(polynomial, blind, q_0, q_0_count, usable_rows)
        .unwrap_or_else(|| params.commit_lagrange(polynomial, blind))
}

fn commit_lagrange_difference<C: CurveAffine>(
    params: &Params<C>,
    domain: &EvaluationDomain<C::Scalar>,
    lhs: &Polynomial<C::Scalar, LagrangeCoeff>,
    rhs: &Polynomial<C::Scalar, LagrangeCoeff>,
    blind: Blind<C::Scalar>,
) -> C::Curve {
    assert_eq!(lhs.len(), rhs.len());
    assert_eq!(lhs.len(), params.g_lagrange.len());

    let difference = lhs
        .iter()
        .zip(rhs.iter())
        .map(|(&lhs, &rhs)| lhs - rhs)
        .collect();
    params.commit_lagrange(&domain.lagrange_from_vec(difference), blind)
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
        table_kinds,
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
            .zip(table_kinds.into_par_iter())
            .map(|((lookup_index, sort_scratch), table_kind)| {
                lookup_arguments[lookup_index].prepare_table(
                    domain,
                    value_evaluator,
                    *theta,
                    fixed_values,
                    fixed_cosets,
                    usable_rows,
                    build_quotient_asts,
                    table_kind,
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

        for (((representative, sort_scratch), table_kind), state) in table_representatives
            .into_iter()
            .zip(table_sort_scratch)
            .zip(table_kinds)
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
                    table_kind,
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
        let fraction_rows = params.n as usize - (blinding_factors + 1);
        let mut denominators = vec![C::Scalar::ZERO; params.n as usize];
        // Denominator uses the permuted input expression and permuted table expression
        parallelize(&mut denominators[..fraction_rows], |denominators, start| {
            for ((denominator, permuted_input_value), permuted_table_value) in denominators
                .iter_mut()
                .zip(self.permuted_input_expression[start..].iter())
                .zip(self.permuted_table_expression[start..].iter())
            {
                *denominator = (*beta + permuted_input_value) * &(*gamma + permuted_table_value);
            }
        });

        // Compute the numerators for the lookup product polynomial.
        // (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        // * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        let mut numerators = vec![C::Scalar::ZERO; params.n as usize];
        parallelize(&mut numerators[..fraction_rows], |numerators, start| {
            for ((numerator, &input_term), &table_term) in numerators
                .iter_mut()
                .zip(self.compressed_input_expression[start..].iter())
                .zip(self.compressed_table_expression[start..].iter())
            {
                *numerator = (input_term + &*beta) * &(table_term + &*gamma);
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

        // Compute the evaluations of the lookup product polynomial over our
        // domain, starting with z[0] = 1. Reuse the numerator vector for z
        // instead of allocating a third domain-sized vector.
        let usable_rows = params.n as usize - blinding_factors;
        let mut lookup_product = super::super::prefix_products_of_fractions(
            numerators,
            denominators,
            fraction_rows,
            C::Scalar::ONE,
        );
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
    let output_capacity = input_values.capacity();
    if input_keys.is_empty() {
        debug_assert!(input_values.windows(2).all(|pair| pair[0] <= pair[1]));
        debug_assert!(table_values.windows(2).all(|pair| pair[0] <= pair[1]));
        let permuted_table_values = permute_sorted_values_by(
            &input_values,
            table_values,
            output_capacity,
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
        output_capacity,
        |row| input_keys[row] == input_keys[row - 1],
        |table_row, input_row| table_keys[table_row] < input_keys[input_row],
        |table_row, input_row| table_keys[table_row] == input_keys[input_row],
    )?;
    Ok((input_values, permuted_table_values))
}

#[cfg(feature = "multicore")]
fn permute_sorted_values_with_sorted_u10<F: Field + Ord>(
    input_values: Vec<F>,
    input_keys: &[PastaSortKey],
    table_values: &[F],
    table_keys: &[PastaSortKey],
) -> Result<(Vec<F>, Vec<F>, Option<SortedU10>), Error> {
    assert_eq!(input_values.len(), table_values.len());
    assert_eq!(input_keys.is_empty(), table_keys.is_empty());
    if input_keys.is_empty() {
        return permute_sorted_values(input_values, input_keys, table_values, table_keys)
            .map(|(input, table)| (input, table, None));
    }

    assert_eq!(input_values.len(), input_keys.len());
    assert_eq!(table_values.len(), table_keys.len());
    debug_assert!(input_keys.windows(2).all(|pair| pair[0] <= pair[1]));
    debug_assert!(table_keys.windows(2).all(|pair| pair[0] <= pair[1]));
    let output_capacity = input_values.capacity();
    let mut sorted_u10 = input_keys.first().and_then(SortedU10::new);
    let permuted_table_values = permute_sorted_values_by(
        &input_values,
        table_values,
        output_capacity,
        |row| {
            let same = input_keys[row] == input_keys[row - 1];
            if !same
                && let Some(profile) = &mut sorted_u10
                && profile.push_distinct(row, &input_keys[row]).is_none()
            {
                sorted_u10 = None;
            }
            same
        },
        |table_row, input_row| table_keys[table_row] < input_keys[input_row],
        |table_row, input_row| table_keys[table_row] == input_keys[input_row],
    )?;
    Ok((input_values, permuted_table_values, sorted_u10))
}

fn permute_sorted_values_by<F: Field, SameInput, TableLess, TableSame>(
    input_values: &[F],
    table_values: &[F],
    output_capacity: usize,
    mut same_input: SameInput,
    table_less: TableLess,
    table_same: TableSame,
) -> Result<Vec<F>, Error>
where
    SameInput: FnMut(usize) -> bool,
    TableLess: Fn(usize, usize) -> bool,
    TableSame: Fn(usize, usize) -> bool,
{
    let usable_rows = input_values.len();
    let mut permuted_table_values = Vec::with_capacity(output_capacity);
    permuted_table_values.resize(usable_rows, F::ZERO);
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

    use pasta_curves::{pallas, vesta};

    use super::*;
    use crate::plonk::circuit::FixedQuery;

    const TEST_ALPHABET_SIZE: usize = 3;
    #[cfg(feature = "multicore")]
    const OVER_PREPARED_ROUTE_THREADS: usize = 11;

    #[cfg(feature = "multicore")]
    fn pasta_key(value: u64) -> PastaSortKey {
        PastaSortKey {
            limbs: [value, 0, 0, 0],
            source: 0,
        }
    }

    #[cfg(feature = "multicore")]
    fn test_sorted_u10(keys: &[PastaSortKey]) -> Option<SortedU10> {
        let first_key = keys.first()?;
        let mut profile = SortedU10::new(first_key)?;
        for row in 1..keys.len() {
            if keys[row] != keys[row - 1] {
                profile.push_distinct(row, &keys[row])?;
            }
        }
        Some(profile)
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn collects_sorted_u10_range_profile_during_permutation() {
        let input_values = [0, 0, 2, 2, 7, u64::from(SORTED_U10_MAX_VALUE)];
        let input_keys = input_values.into_iter().map(pasta_key).collect::<Vec<_>>();
        let maximum = u64::from(SORTED_U10_MAX_VALUE);
        let table_values = [0, 0, 2, 7, maximum, maximum];
        let table_keys = table_values.map(pasta_key);
        let (fused_input, fused_table, profile) = permute_sorted_values_with_sorted_u10(
            input_values.map(pallas::Scalar::from).to_vec(),
            &input_keys,
            &table_values.map(pallas::Scalar::from),
            &table_keys,
        )
        .unwrap();
        let profile = profile.unwrap();
        assert_eq!(profile.first, 0);
        assert_eq!(profile.last, SORTED_U10_MAX_VALUE);
        assert_eq!(
            profile.transitions,
            [
                SortedU10Transition { row: 2, delta: 2 },
                SortedU10Transition { row: 4, delta: 5 },
                SortedU10Transition {
                    row: 5,
                    delta: SORTED_U10_MAX_VALUE - 7,
                },
            ]
        );

        let (plain_input, plain_table) = permute_sorted_values(
            input_values.map(pallas::Scalar::from).to_vec(),
            &input_keys,
            &table_values.map(pallas::Scalar::from),
            &table_keys,
        )
        .unwrap();
        assert_eq!(fused_input, plain_input);
        assert_eq!(fused_table, plain_table);

        let outside_u10 = maximum + 1;
        let non_u10 = [pallas::Scalar::from(outside_u10); 2];
        let non_u10_keys = [pasta_key(outside_u10); 2];
        let (_, _, profile) = permute_sorted_values_with_sorted_u10(
            non_u10.to_vec(),
            &non_u10_keys,
            &non_u10,
            &non_u10_keys,
        )
        .unwrap();
        assert!(profile.is_none());

        assert!(test_sorted_u10(&[pasta_key(2), pasta_key(1)]).is_none());
        assert!(test_sorted_u10(&[pasta_key(outside_u10)]).is_none());
        assert_eq!(std::mem::size_of::<SortedU10Transition>(), 4);
    }

    #[cfg(feature = "multicore")]
    fn check_sorted_u10_commitments<C>()
    where
        C: CurveAffine + core::fmt::Debug,
        C::Curve: core::fmt::Debug,
    {
        use rand::{SeedableRng, rngs::StdRng};

        const K: u32 = PREPARED_SORTED_U10_COMMITMENT_K;

        let params = Params::<C>::new(K);
        let domain = EvaluationDomain::<C::Scalar>::new(1, K);
        let domain_len = 1usize << K;
        let eligibility_keys = vec![pasta_key(0); domain_len - SORTED_U10_MAX_SUFFIX];

        // An eligible-looking input must not enable profiling unless
        // preparation has built the suffix cache.
        assert!(
            prepared_sorted_u10_suffix_multiples(
                &params,
                true,
                eligibility_keys.len(),
                eligibility_keys.len(),
            )
            .is_none()
        );
        assert!(params.prepare_commitments());
        let suffix_multiples = params.prepared_lagrange_suffix_multiples().unwrap();
        let wide_pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(OVER_PREPARED_ROUTE_THREADS)
            .build()
            .unwrap();
        assert!(
            wide_pool
                .install(|| {
                    prepared_sorted_u10_suffix_multiples(
                        &params,
                        true,
                        eligibility_keys.len(),
                        eligibility_keys.len(),
                    )
                })
                .is_none()
        );
        let constant_profile = test_sorted_u10(&eligibility_keys).unwrap();
        let prepared_suffix_multiples = prepared_sorted_u10_suffix_multiples(
            &params,
            true,
            eligibility_keys.len(),
            eligibility_keys.len(),
        )
        .unwrap();
        assert_eq!((constant_profile.first, constant_profile.last), (0, 0));
        assert!(constant_profile.transitions.is_empty());
        assert!(std::ptr::eq(suffix_multiples, prepared_suffix_multiples));
        let cloned_params = params.clone();
        let cloned_suffix_multiples = cloned_params
            .prepared_lagrange_suffix_multiples()
            .expect("cloned params share their prepared suffix multiples");
        assert!(std::ptr::eq(suffix_multiples, cloned_suffix_multiples));

        let mut encoded = Vec::new();
        params.write(&mut encoded).unwrap();
        let decoded = Params::<C>::read(&mut encoded.as_slice()).unwrap();
        assert!(decoded.prepared_lagrange_suffix_multiples().is_none());

        assert!(
            prepared_sorted_u10_suffix_multiples(
                &params,
                false,
                eligibility_keys.len(),
                eligibility_keys.len(),
            )
            .is_none()
        );
        assert!(
            prepared_sorted_u10_suffix_multiples(
                &params,
                true,
                domain_len - SORTED_U10_MAX_SUFFIX - 1,
                eligibility_keys.len(),
            )
            .is_none()
        );
        assert!(
            prepared_sorted_u10_suffix_multiples(
                &params,
                true,
                domain_len - SORTED_U10_MAX_SUFFIX - 1,
                domain_len - SORTED_U10_MAX_SUFFIX - 1,
            )
            .is_none()
        );
        let mut invalid_keys = eligibility_keys.clone();
        invalid_keys[0] = pasta_key(u64::from(SORTED_U10_MAX_VALUE) + 1);
        assert!(test_sorted_u10(&invalid_keys).is_none());
        let wrong_k = Params::<C>::new(K - 1);
        assert!(wrong_k.prepare_commitments());
        let wrong_k_usable = (1usize << (K - 1)) - SORTED_U10_MAX_SUFFIX;
        assert!(
            prepared_sorted_u10_suffix_multiples(&wrong_k, true, wrong_k_usable, wrong_k_usable,)
                .is_none()
        );

        let mut rng = StdRng::seed_from_u64(0x7531_302d_6c6f_6f6b);
        let cases = [
            (
                0usize,
                (0..domain_len)
                    .map(|row| ((row / 7) * 3).min(usize::from(SORTED_U10_MAX_VALUE)) as u16)
                    .collect::<Vec<_>>(),
            ),
            (
                6usize,
                (0..domain_len - 6)
                    .map(|row| (5 + (row / 9) * 4).min(usize::from(SORTED_U10_MAX_VALUE)) as u16)
                    .collect::<Vec<_>>(),
            ),
            (
                SORTED_U10_MAX_SUFFIX,
                (0..domain_len - SORTED_U10_MAX_SUFFIX)
                    .map(|row| {
                        if row + 1 == domain_len - SORTED_U10_MAX_SUFFIX {
                            SORTED_U10_MAX_VALUE
                        } else {
                            0
                        }
                    })
                    .collect::<Vec<_>>(),
            ),
        ];

        for (suffix_len, prefix_values) in cases {
            let usable_rows = domain_len - suffix_len;
            let keys = prefix_values
                .iter()
                .map(|&value| pasta_key(u64::from(value)))
                .collect::<Vec<_>>();
            let profile = test_sorted_u10(&keys).unwrap();
            let mut values = prefix_values
                .iter()
                .map(|&value| C::Scalar::from(u64::from(value)))
                .collect::<Vec<_>>();
            values.extend((0..suffix_len).map(|_| C::Scalar::random(&mut rng)));
            let polynomial = domain.lagrange_from_vec(values);
            let blind = loop {
                let candidate = C::Scalar::random(&mut rng);
                if !bool::from(candidate.is_zero()) {
                    break Blind(candidate);
                }
            };

            assert_eq!(keys.len(), usable_rows);
            assert_eq!(
                commit_sorted_u10(
                    &params,
                    &polynomial,
                    blind,
                    usable_rows,
                    &profile,
                    suffix_multiples,
                )
                .unwrap(),
                params.commit_lagrange(&polynomial, blind),
            );
        }

        #[cfg(not(feature = "orbits"))]
        {
            let usable_rows = domain_len - PERMUTED_U10_TABLE_SUFFIX_TERMS;
            let mut values = vec![C::Scalar::ZERO; usable_rows];
            for (value, scalar) in (1..=u64::from(SORTED_U10_MAX_VALUE)).zip(&mut values) {
                *scalar = C::Scalar::from(value);
            }
            let mut state = 0x7065_726d_2d75_3130u64;
            for end in (1..values.len()).rev() {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                values.swap(end, state as usize % (end + 1));
            }
            values
                .extend((0..PERMUTED_U10_TABLE_SUFFIX_TERMS).map(|_| C::Scalar::random(&mut rng)));
            let mut malformed_values = values.clone();
            malformed_values[0] = C::Scalar::from(u64::from(SORTED_U10_MAX_VALUE) + 1);
            let polynomial = domain.lagrange_from_vec(values);
            let malformed = domain.lagrange_from_vec(malformed_values);
            let blind = Blind(C::Scalar::random(&mut rng));

            assert_eq!(
                try_commit_permuted_u10_table(&params, &polynomial, blind, usable_rows),
                Some(params.commit_lagrange(&polynomial, blind)),
            );
            // An out-of-range prefix value makes direct recoding decline; the
            // prepared evaluator must still return the exact commitment.
            assert_eq!(
                try_commit_permuted_u10_table(&params, &malformed, blind, usable_rows),
                Some(params.commit_lagrange(&malformed, blind)),
            );
            assert!(
                try_commit_permuted_u10_table(&params, &polynomial, blind, usable_rows - 1)
                    .is_none()
            );
            assert!(
                wide_pool
                    .install(|| {
                        try_commit_permuted_u10_table(&params, &polynomial, blind, usable_rows)
                    })
                    .is_none()
            );
            assert!(
                try_commit_permuted_u10_table(&decoded, &polynomial, blind, usable_rows).is_none()
            );
        }

        let usable_rows = domain_len - SORTED_U10_MAX_SUFFIX;
        let zero = domain.lagrange_from_vec(vec![C::Scalar::ZERO; domain_len]);
        let malformed = SortedU10 {
            transitions: vec![SortedU10Transition { row: 1, delta: 1 }],
            first: 0,
            last: 2,
        };
        assert!(
            commit_sorted_u10(
                &params,
                &zero,
                Blind(C::Scalar::ONE),
                usable_rows,
                &malformed,
                suffix_multiples,
            )
            .is_none()
        );
        assert!(
            commit_sorted_u10(
                &params,
                &zero,
                Blind(C::Scalar::ONE),
                usable_rows,
                &SortedU10 {
                    transitions: vec![SortedU10Transition { row: 0, delta: 2 }],
                    first: 0,
                    last: 2,
                },
                suffix_multiples,
            )
            .is_none()
        );
        assert!(
            commit_sorted_u10(
                &params,
                &zero,
                Blind(C::Scalar::ONE),
                usable_rows,
                &SortedU10 {
                    transitions: Vec::new(),
                    first: 0,
                    last: 0,
                },
                &suffix_multiples[..suffix_multiples.len() - 1],
            )
            .is_none()
        );

        let input_blind = Blind(C::Scalar::ONE);
        let table_blind = Blind(C::Scalar::from(2));
        assert_eq!(
            commit_permuted_pair(
                &params,
                &domain,
                &zero,
                input_blind,
                &zero,
                table_blind,
                None,
                usable_rows,
                Some((&malformed, suffix_multiples)),
            ),
            (
                params.commit_lagrange(&zero, input_blind).to_affine(),
                params.commit_lagrange(&zero, table_blind).to_affine(),
            ),
        );
    }

    #[cfg(feature = "multicore")]
    fn run_sorted_u10_commitment_check<C>()
    where
        C: CurveAffine + core::fmt::Debug,
        C::Curve: core::fmt::Debug,
    {
        maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap()
            .install(check_sorted_u10_commitments::<C>);
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn sorted_u10_commitment_matches_lagrange_pallas() {
        run_sorted_u10_commitment_check::<pallas::Affine>();
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn sorted_u10_commitment_matches_lagrange_vesta() {
        run_sorted_u10_commitment_check::<vesta::Affine>();
    }

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

    fn check_permuted_pair_commitments<C>()
    where
        C: CurveAffine + core::fmt::Debug,
        C::Curve: core::fmt::Debug,
    {
        const K: u32 = 4;

        let params = Params::<C>::new(K);
        #[cfg(any(feature = "multicore", feature = "orbits"))]
        assert!(params.prepare_commitments());
        #[cfg(feature = "multicore")]
        let prepared_pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();
        let domain = EvaluationDomain::<C::Scalar>::new(1, K);
        let zero = domain.lagrange_from_vec(vec![C::Scalar::ZERO; 1 << K]);
        assert_eq!(
            commit_permuted_pair(
                &params,
                &domain,
                &zero,
                Blind(C::Scalar::ZERO),
                &zero,
                Blind(C::Scalar::ZERO),
                None,
                0,
                #[cfg(feature = "multicore")]
                None,
            ),
            (C::identity(), C::identity()),
        );

        let q_0 = C::Scalar::from(29);
        let table_values = (0..1_usize << K)
            .map(|index| {
                if (index < 15 && index % 2 == 0) || index == (1 << K) - 1 {
                    q_0
                } else {
                    C::Scalar::from(index as u64 + 1)
                }
            })
            .collect::<Vec<_>>();

        let identical = table_values.clone();
        let full_difference = table_values
            .iter()
            .map(|value| *value + C::Scalar::ONE)
            .collect::<Vec<_>>();
        let sparse_difference = table_values
            .iter()
            .enumerate()
            .map(|(index, value)| {
                if index % 3 == 0 {
                    *value + C::Scalar::from(index as u64 + 2)
                } else {
                    *value
                }
            })
            .collect::<Vec<_>>();

        for (input_values, input_blind, table_blind) in [
            (
                identical.clone(),
                Blind(C::Scalar::from(7)),
                Blind(C::Scalar::from(7)),
            ),
            (
                identical,
                Blind(C::Scalar::from(11)),
                Blind(C::Scalar::from(13)),
            ),
            (
                full_difference,
                Blind(C::Scalar::from(17)),
                Blind(C::Scalar::from(17)),
            ),
            (
                sparse_difference,
                Blind(C::Scalar::from(19)),
                Blind(C::Scalar::from(23)),
            ),
        ] {
            let input = domain.lagrange_from_vec(input_values);
            let table = domain.lagrange_from_vec(table_values.clone());
            let expected = (
                params.commit_lagrange(&input, input_blind).to_affine(),
                params.commit_lagrange(&table, table_blind).to_affine(),
            );
            // Model noncontiguous witness-dependent positions and a random
            // blind-tail row that happens to equal q_0.
            #[cfg(feature = "multicore")]
            let routed_table = prepared_pool
                .install(|| params.try_commit_sinsemilla_table(&table, table_blind, q_0, 8, 15));
            #[cfg(all(not(feature = "multicore"), feature = "orbits"))]
            let routed_table = params.try_commit_sinsemilla_table(&table, table_blind, q_0, 8, 15);
            #[cfg(any(feature = "multicore", feature = "orbits"))]
            assert_eq!(
                routed_table.map(|point| point.to_affine()),
                Some(expected.1)
            );

            for sinsemilla_q_0 in [None, Some((q_0, 8))] {
                assert_eq!(
                    commit_permuted_pair(
                        &params,
                        &domain,
                        &input,
                        input_blind,
                        &table,
                        table_blind,
                        sinsemilla_q_0,
                        15,
                        #[cfg(feature = "multicore")]
                        None,
                    ),
                    expected,
                );
            }
        }

        let constant = domain.lagrange_from_vec(vec![q_0; 1usize << K]);
        let expected_constant = params.commit_lagrange(&constant, Blind(C::Scalar::ZERO));
        assert_eq!(
            commit_sinsemilla_table(
                &params,
                &constant,
                Blind(C::Scalar::ZERO),
                Some((q_0, 1 << K)),
                1 << K,
            ),
            expected_constant,
        );

        #[cfg(any(feature = "multicore", feature = "orbits"))]
        {
            #[cfg(feature = "multicore")]
            let routed = prepared_pool.install(|| {
                params.try_commit_sinsemilla_table(
                    &constant,
                    Blind(C::Scalar::ZERO),
                    q_0,
                    1 << K,
                    1 << K,
                )
            });
            #[cfg(not(feature = "multicore"))]
            let routed = params.try_commit_sinsemilla_table(
                &constant,
                Blind(C::Scalar::ZERO),
                q_0,
                1 << K,
                1 << K,
            );
            assert_eq!(routed, Some(expected_constant));

            assert!(
                params
                    .try_commit_sinsemilla_table(
                        &constant,
                        Blind(C::Scalar::ZERO),
                        C::Scalar::ZERO,
                        1 << K,
                        1 << K,
                    )
                    .is_none()
            );
            assert!(
                params
                    .try_commit_sinsemilla_table(
                        &constant,
                        Blind(C::Scalar::ZERO),
                        q_0,
                        (1 << K) - 1,
                        1 << K,
                    )
                    .is_none()
            );
            assert!(
                params
                    .try_commit_sinsemilla_table(
                        &constant,
                        Blind(C::Scalar::ZERO),
                        q_0,
                        (1 << K) + 1,
                        1 << K,
                    )
                    .is_none()
            );
            assert!(
                params
                    .try_commit_sinsemilla_table(
                        &constant,
                        Blind(C::Scalar::ZERO),
                        q_0,
                        1 << K,
                        (1 << K) + 1,
                    )
                    .is_none()
            );

            let unprepared = Params::<C>::new(K);
            assert!(
                unprepared
                    .try_commit_sinsemilla_table(
                        &constant,
                        Blind(C::Scalar::ZERO),
                        q_0,
                        1 << K,
                        1 << K,
                    )
                    .is_none()
            );
        }
    }

    #[test]
    fn permuted_pair_commitments_reuse_table_pallas() {
        check_permuted_pair_commitments::<pallas::Affine>();
    }

    #[test]
    fn permuted_pair_commitments_reuse_table_vesta() {
        check_permuted_pair_commitments::<vesta::Affine>();
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

    fn sorted_values_with_counts(counts: &[(u64, usize)]) -> Vec<pallas::Scalar> {
        let mut values = counts
            .iter()
            .flat_map(|&(value, count)| iter::repeat(pallas::Scalar::from(value)).take(count))
            .collect::<Vec<_>>();
        values.sort_unstable();
        values
    }

    fn sorted_values_with_mode(mode_count: usize, len: usize) -> Vec<pallas::Scalar> {
        sorted_values_with_zeroes_and_mode(0, mode_count, len)
    }

    fn sorted_values_with_zeroes_and_mode(
        zero_count: usize,
        mode_count: usize,
        len: usize,
    ) -> Vec<pallas::Scalar> {
        let unique_count = len
            .checked_sub(zero_count)
            .and_then(|remaining| remaining.checked_sub(mode_count))
            .expect("zeroes and mode fit within the test vector");
        let mut values = iter::repeat(pallas::Scalar::ZERO)
            .take(zero_count)
            .chain(iter::repeat(pallas::Scalar::ONE).take(mode_count))
            .chain((0..unique_count).map(|index| {
                pallas::Scalar::from(u64::try_from(index).expect("test index fits in u64") + 2)
            }))
            .collect::<Vec<_>>();
        values.sort_unstable();
        values
    }

    #[test]
    fn sinsemilla_q_0_requires_a_strong_nonzero_repetition() {
        let len = 16usize;
        let threshold = len.div_ceil(SINSEMILLA_Q_0_MIN_REPETITION_FRACTION_DENOMINATOR);
        let exact = sorted_values_with_mode(threshold, len);
        assert_eq!(
            factorable_sinsemilla_q_0(&exact, pallas::Scalar::ONE),
            Some((pallas::Scalar::ONE, threshold)),
        );

        let below = sorted_values_with_mode(threshold - 1, len);
        assert_eq!(factorable_sinsemilla_q_0(&below, pallas::Scalar::ONE), None,);
        assert_eq!(
            factorable_sinsemilla_q_0::<pallas::Scalar>(&[], pallas::Scalar::ONE),
            None,
        );
        assert_eq!(
            factorable_sinsemilla_q_0(
                &sorted_values_with_counts(&[(0, 8), (1, 4), (2, 4)]),
                pallas::Scalar::ZERO,
            ),
            None,
        );
    }

    #[test]
    fn sinsemilla_factoring_uses_q_0_instead_of_the_mode() {
        let longer_other_run = sorted_values_with_counts(&[(1, 4), (2, 8), (3, 4)]);
        assert_eq!(
            factorable_sinsemilla_q_0(&longer_other_run, pallas::Scalar::ONE),
            Some((pallas::Scalar::ONE, 4)),
        );

        let weak_q_0 = sorted_values_with_counts(&[(1, 3), (2, 8), (3, 5)]);
        assert_eq!(
            factorable_sinsemilla_q_0(&weak_q_0, pallas::Scalar::ONE),
            None,
        );

        // Existing zeroes remain zero after factoring, so they do not reduce
        // the number of q_0 terms saved by the dedicated MSM.
        let zero_dominant = sorted_values_with_counts(&[(0, 8), (1, 4), (2, 4)]);
        assert_eq!(
            factorable_sinsemilla_q_0(&zero_dominant, pallas::Scalar::ONE),
            Some((pallas::Scalar::ONE, 4)),
        );
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
        assert_eq!(
            plan.table_kinds,
            [PreparedTableKind::Generic, PreparedTableKind::Generic]
        );
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

    #[test]
    fn reused_indexed_triple_matches_sinsemilla_shape() {
        let index = lookup_with_table(&[(1, 0, 0)]);
        let triple = lookup_with_table(&[(1, 0, 0), (11, 1, 0), (12, 2, 0)]);
        let plan = prepare_table_plan(
            &[
                index,
                triple,
                lookup_with_table(&[(1, 0, 0), (11, 1, 0), (12, 2, 0)]),
            ],
            2,
            17,
        );
        assert_eq!(plan.representatives, [0, 1]);
        assert_eq!(plan.groups, [0, 1, 1]);
        #[cfg(feature = "multicore")]
        assert_eq!(
            plan.table_kinds,
            [
                PreparedTableKind::SortedU10Range,
                PreparedTableKind::Sinsemilla,
            ]
        );
        #[cfg(not(feature = "multicore"))]
        assert_eq!(
            plan.table_kinds,
            [PreparedTableKind::Generic, PreparedTableKind::Sinsemilla]
        );

        let one_off = prepare_table_plan(
            &[
                lookup_with_table(&[(1, 0, 0)]),
                lookup_with_table(&[(1, 0, 0), (11, 1, 0), (12, 2, 0)]),
            ],
            1,
            17,
        );
        assert_eq!(
            one_off.table_kinds,
            [PreparedTableKind::Generic, PreparedTableKind::Generic]
        );

        let no_index_lookup = prepare_table_plan(
            &[
                lookup_with_table(&[(1, 0, 0), (11, 1, 0), (12, 2, 0)]),
                lookup_with_table(&[(1, 0, 0), (11, 1, 0), (12, 2, 0)]),
            ],
            1,
            17,
        );
        assert_eq!(no_index_lookup.table_kinds, [PreparedTableKind::Generic]);

        let rotated = prepare_table_plan(
            &[
                lookup_with_table(&[(1, 0, 0)]),
                lookup_with_table(&[(1, 0, 0), (11, 1, 1), (12, 2, 0)]),
                lookup_with_table(&[(1, 0, 0), (11, 1, 1), (12, 2, 0)]),
            ],
            1,
            17,
        );
        assert_eq!(
            rotated.table_kinds,
            [PreparedTableKind::Generic, PreparedTableKind::Generic]
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
