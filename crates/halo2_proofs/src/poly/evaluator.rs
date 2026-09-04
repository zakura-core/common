use std::{
    any::{Any, TypeId},
    borrow::Cow,
    collections::{HashMap, hash_map::DefaultHasher},
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::{Add, Mul, MulAssign, Neg, Sub},
    sync::Arc,
};

use ff::WithSmallOrderMulGroup;
use group::ff::Field;
use pasta_curves::{deferred::DeferredField, pallas, vesta};

use super::{
    Basis, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation,
};
use crate::multicore;

const EVALUATOR_CHUNKS_PER_THREAD: usize = 8;

// Repeated linear terms save an evaluation-domain walk, but every additional
// physical cache slot retains one field element per polynomial row. Bound both
// the number of logical entries and the payload of physical slots that cannot
// reuse gaps in the existing cache lifetimes.
const MAX_LINEAR_TERM_CACHE_ENTRIES: usize = 16;
const MAX_ADDITIONAL_LINEAR_TERM_CACHE_BYTES: usize = 4 * 1024 * 1024;

/// Returns `(chunk_size, num_chunks)` suitable for processing the given
/// polynomial length in the current parallelization environment.
fn get_chunk_params(poly_len: usize) -> (usize, usize) {
    // Check the level of parallelization we have available.
    let num_threads = multicore::current_num_threads();
    // We scale the number of chunks by a constant factor, to ensure that if not
    // all threads are available, we can achieve more uniform throughput and
    // don't end up waiting on a couple of threads to process the last chunks.
    let num_chunks = num_threads * EVALUATOR_CHUNKS_PER_THREAD;
    // Calculate the ideal chunk size for the desired throughput. We use ceiling
    // division to ensure the minimum chunk size is 1.
    //     chunk_size = ceil(poly_len / num_chunks)
    let chunk_size = (poly_len + num_chunks - 1) / num_chunks;
    // Now re-calculate num_chunks from the actual chunk size.
    //     num_chunks = ceil(poly_len / chunk_size)
    let num_chunks = (poly_len + chunk_size - 1) / chunk_size;

    (chunk_size, num_chunks)
}

#[derive(Clone, Copy, Default)]
struct LinearTermCacheBudget {
    max_entries: usize,
    max_additional_slots: usize,
}

fn linear_term_cache_budget<F: Field, B: BasisOps>(poly_len: usize) -> LinearTermCacheBudget {
    if !B::CACHE_REPEATED_LINEAR_TERMS {
        return LinearTermCacheBudget::default();
    }

    let max_additional_slots = poly_len
        .checked_mul(std::mem::size_of::<F>())
        .filter(|bytes_per_slot| *bytes_per_slot != 0)
        .map(|bytes_per_slot| {
            (MAX_ADDITIONAL_LINEAR_TERM_CACHE_BYTES / bytes_per_slot)
                .min(MAX_LINEAR_TERM_CACHE_ENTRIES)
        })
        .unwrap_or(0);
    LinearTermCacheBudget {
        max_entries: MAX_LINEAR_TERM_CACHE_ENTRIES,
        max_additional_slots,
    }
}

/// A reference to a polynomial registered with an [`Evaluator`].
#[derive(Clone, Copy)]
pub(crate) struct AstLeaf<E, B: Basis> {
    index: usize,
    rotation: Rotation,
    _evaluator: PhantomData<(E, B)>,
}

impl<E, B: Basis> fmt::Debug for AstLeaf<E, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AstLeaf")
            .field("index", &self.index)
            .field("rotation", &self.rotation)
            .finish()
    }
}

impl<E, B: Basis> PartialEq for AstLeaf<E, B> {
    fn eq(&self, rhs: &Self) -> bool {
        // We compare rotations by offset, which doesn't account for equivalent rotations.
        self.index.eq(&rhs.index) && self.rotation.0.eq(&rhs.rotation.0)
    }
}

impl<E, B: Basis> Eq for AstLeaf<E, B> {}

impl<E, B: Basis> Hash for AstLeaf<E, B> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self.rotation.0.hash(state);
    }
}

impl<E, B: Basis> AstLeaf<E, B> {
    /// Produces a new `AstLeaf` node corresponding to the underlying polynomial at a
    /// _new_ rotation. Existing rotations applied to this leaf node are ignored and the
    /// returned polynomial is not rotated _relative_ to the previous structure.
    pub(crate) fn with_rotation(&self, rotation: Rotation) -> Self {
        AstLeaf {
            index: self.index,
            rotation,
            _evaluator: PhantomData,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct IndexedLeaf {
    index: usize,
    rotation: Rotation,
}

impl Hash for IndexedLeaf {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self.rotation.0.hash(state);
    }
}

impl<E, B: Basis> From<AstLeaf<E, B>> for IndexedLeaf {
    fn from(leaf: AstLeaf<E, B>) -> Self {
        Self {
            index: leaf.index,
            rotation: leaf.rotation,
        }
    }
}

impl<E, B: Basis> From<&AstLeaf<E, B>> for IndexedLeaf {
    fn from(leaf: &AstLeaf<E, B>) -> Self {
        Self {
            index: leaf.index,
            rotation: leaf.rotation,
        }
    }
}

/// Transcript challenges used by the quotient evaluator's symbolic plan.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EvaluationChallenge {
    Theta,
    Beta,
    Gamma,
    Y,
}

/// Opaque, exact semantic identity for one registered polynomial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct EvaluationPolyTag([usize; 3]);

impl EvaluationPolyTag {
    /// Creates a collision-free tag from an exact role and two role-specific
    /// indices.
    pub(crate) const fn new(role: usize, first: usize, second: usize) -> Self {
        Self([role, first, second])
    }
}

const EVALUATION_CHALLENGE_COUNT: usize = 4;

/// Current-proof values for [`EvaluationChallenge`] operands.
#[derive(Clone, Copy, Debug)]
pub(crate) struct EvaluationChallenges<F> {
    theta: F,
    beta: F,
    gamma: F,
    y: F,
}

impl<F> EvaluationChallenges<F> {
    pub(crate) fn new(theta: F, beta: F, gamma: F, y: F) -> Self {
        Self {
            theta,
            beta,
            gamma,
            y,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum PlanScalar<F> {
    // Variants are assigned from protocol provenance at AST construction;
    // challenge operands are never inferred from concrete field equality.
    Literal(F),
    Challenge(EvaluationChallenge),
    ScaledChallenge {
        challenge: EvaluationChallenge,
        factor: F,
    },
    ChallengePower {
        challenge: EvaluationChallenge,
        exponent: u32,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct ScalarId<F>(u32, PhantomData<fn() -> F>);

impl<F> ScalarId<F> {
    fn from_index(index: usize) -> Option<Self> {
        Some(Self(index.try_into().ok()?, PhantomData))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

impl<F> Hash for ScalarId<F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

struct PlanScalarInterner<F> {
    descriptors: Vec<PlanScalar<F>>,
    literals: Vec<(F, ScalarId<F>)>,
    challenges: [Option<ScalarId<F>>; EVALUATION_CHALLENGE_COUNT],
    scaled_challenges: [Vec<(F, ScalarId<F>)>; EVALUATION_CHALLENGE_COUNT],
    challenge_powers: [Vec<Option<ScalarId<F>>>; EVALUATION_CHALLENGE_COUNT],
}

impl<F: Field> PlanScalarInterner<F> {
    fn new() -> Self {
        Self {
            descriptors: vec![],
            literals: vec![],
            challenges: [None; EVALUATION_CHALLENGE_COUNT],
            scaled_challenges: std::array::from_fn(|_| vec![]),
            challenge_powers: std::array::from_fn(|_| vec![]),
        }
    }

    fn push(&mut self, descriptor: PlanScalar<F>) -> ScalarId<F> {
        let id = ScalarId::from_index(self.descriptors.len())
            .expect("a quotient plan has fewer than 2^32 scalar descriptors");
        self.descriptors.push(descriptor);
        id
    }

    fn intern(&mut self, descriptor: PlanScalar<F>) -> ScalarId<F> {
        match descriptor {
            PlanScalar::Literal(value) => {
                if let Some((_, id)) = self
                    .literals
                    .iter()
                    .find(|(candidate, _)| *candidate == value)
                {
                    return *id;
                }
                let id = self.push(descriptor);
                self.literals.push((value, id));
                id
            }
            PlanScalar::Challenge(challenge) => {
                let index = challenge.index();
                if let Some(id) = self.challenges[index] {
                    return id;
                }
                let id = self.push(descriptor);
                self.challenges[index] = Some(id);
                id
            }
            PlanScalar::ScaledChallenge { challenge, factor } => {
                let index = challenge.index();
                if let Some((_, id)) = self.scaled_challenges[index]
                    .iter()
                    .find(|(candidate, _)| *candidate == factor)
                {
                    return *id;
                }
                let id = self.push(descriptor);
                self.scaled_challenges[index].push((factor, id));
                id
            }
            PlanScalar::ChallengePower {
                challenge,
                exponent,
            } => {
                let powers = &mut self.challenge_powers[challenge.index()];
                let exponent_index = exponent as usize;
                if powers.len() <= exponent_index {
                    powers.resize(exponent_index + 1, None);
                }
                if let Some(id) = powers[exponent_index] {
                    return id;
                }
                let id = self.push(descriptor);
                self.challenge_powers[challenge.index()][exponent_index] = Some(id);
                id
            }
        }
    }

    fn finish(self) -> Box<[PlanScalar<F>]> {
        self.descriptors.into_boxed_slice()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CompressedSelectorShape {
    query: IndexedLeaf,
    combination_len: usize,
    assigned_root: usize,
    selector: IndexedLeaf,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct EvaluatorShape {
    polynomial_lengths: Box<[usize]>,
    // `None` exists only for ephemeral plans used by the generic evaluator.
    // A retained compiled quotient plan never matches without complete tags.
    polynomial_tags: Option<Box<[EvaluationPolyTag]>>,
    compressed_selectors: Box<[CompressedSelectorShape]>,
    reused_compressed_selector_sources: Box<[usize]>,
}

impl<F: PartialEq> PartialEq for PlanScalar<F> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Literal(lhs), Self::Literal(rhs)) => lhs == rhs,
            (Self::Challenge(lhs), Self::Challenge(rhs)) => lhs == rhs,
            (
                Self::ScaledChallenge {
                    challenge: lhs_challenge,
                    factor: lhs_factor,
                },
                Self::ScaledChallenge {
                    challenge: rhs_challenge,
                    factor: rhs_factor,
                },
            ) => lhs_challenge == rhs_challenge && lhs_factor == rhs_factor,
            (
                Self::ChallengePower {
                    challenge: lhs_challenge,
                    exponent: lhs_exponent,
                },
                Self::ChallengePower {
                    challenge: rhs_challenge,
                    exponent: rhs_exponent,
                },
            ) => lhs_challenge == rhs_challenge && lhs_exponent == rhs_exponent,
            _ => false,
        }
    }
}

impl<F: Eq> Eq for PlanScalar<F> {}

impl EvaluationChallenge {
    fn index(self) -> usize {
        match self {
            Self::Theta => 0,
            Self::Beta => 1,
            Self::Gamma => 2,
            Self::Y => 3,
        }
    }

    fn value<F: Copy>(self, challenges: &EvaluationChallenges<F>) -> F {
        match self {
            Self::Theta => challenges.theta,
            Self::Beta => challenges.beta,
            Self::Gamma => challenges.gamma,
            Self::Y => challenges.y,
        }
    }
}

struct BoundEvaluationChallenges<F> {
    values: EvaluationChallenges<F>,
    powers: [Vec<F>; EVALUATION_CHALLENGE_COUNT],
}

#[derive(Clone, Copy)]
enum ScaleKind {
    MinusOne,
    One,
    Two,
    Other,
}

struct BoundPlanScalars<F> {
    values: Box<[F]>,
    scale_kinds: Box<[ScaleKind]>,
}

impl<F: Copy> BoundPlanScalars<F> {
    fn get(&self, id: ScalarId<F>) -> F {
        self.values[id.index()]
    }

    fn scale(&self, id: ScalarId<F>) -> (F, ScaleKind) {
        (self.values[id.index()], self.scale_kinds[id.index()])
    }
}

impl<F: Field> BoundEvaluationChallenges<F> {
    fn new(
        values: EvaluationChallenges<F>,
        max_exponents: [u32; EVALUATION_CHALLENGE_COUNT],
    ) -> Self {
        let powers = std::array::from_fn(|index| {
            let max_exponent = max_exponents[index] as usize;
            let challenge = match index {
                0 => values.theta,
                1 => values.beta,
                2 => values.gamma,
                3 => values.y,
                _ => unreachable!(),
            };
            let mut powers = Vec::with_capacity(max_exponent + 1);
            powers.push(F::ONE);
            for exponent in 1..=max_exponent {
                powers.push(powers[exponent - 1] * challenge);
            }
            powers
        });
        Self { values, powers }
    }
}

impl<F: Field> PlanScalar<F> {
    fn resolve(self, challenges: &BoundEvaluationChallenges<F>) -> F {
        match self {
            Self::Literal(value) => value,
            Self::Challenge(challenge) => challenge.value(&challenges.values),
            Self::ScaledChallenge { challenge, factor } => {
                challenge.value(&challenges.values) * factor
            }
            Self::ChallengePower {
                challenge,
                exponent,
            } => challenges.powers[challenge.index()][exponent as usize],
        }
    }

    fn record_max_exponent(self, max_exponents: &mut [u32; EVALUATION_CHALLENGE_COUNT]) {
        if let Self::ChallengePower {
            challenge,
            exponent,
        } = self
        {
            max_exponents[challenge.index()] = max_exponents[challenge.index()].max(exponent);
        }
    }
}

impl<F: Field> BoundPlanScalars<F> {
    fn new(
        descriptors: &[PlanScalar<F>],
        challenges: EvaluationChallenges<F>,
        max_exponents: [u32; EVALUATION_CHALLENGE_COUNT],
    ) -> Self {
        let challenges = BoundEvaluationChallenges::new(challenges, max_exponents);
        let values = descriptors
            .iter()
            .map(|descriptor| descriptor.resolve(&challenges))
            .collect::<Box<[_]>>();
        let minus_one = -F::ONE;
        let two = F::ONE.double();
        let scale_kinds = values
            .iter()
            .map(|value| {
                if *value == minus_one {
                    ScaleKind::MinusOne
                } else if *value == F::ONE {
                    ScaleKind::One
                } else if *value == two {
                    ScaleKind::Two
                } else {
                    ScaleKind::Other
                }
            })
            .collect();
        Self {
            values,
            scale_kinds,
        }
    }
}

/// An evaluation context for polynomial operations.
///
/// This context enables us to de-duplicate queries of circuit columns (and the rotations
/// they might require), by storing a list of all the underlying polynomials involved in
/// any query (which are almost certainly column polynomials). We use the context like so:
///
/// - We register each underlying polynomial with the evaluator, which returns a reference
///   to it as a [`AstLeaf`].
/// - The references are then used to build up a [`Ast`] that represents the overall
///   operations to be applied to the polynomials.
/// - Finally, we call [`Evaluator::evaluate`] passing in the [`Ast`].
///
/// Polynomials registered with [`Evaluator::register_poly`] are owned by the
/// evaluator. Polynomials registered with [`Evaluator::register_poly_ref`] are
/// borrowed and must outlive it.
pub(crate) struct Evaluator<'poly, E, F: Field, B: Basis> {
    polys: Vec<Cow<'poly, Polynomial<F, B>>>,
    virtual_poly_count: Option<usize>,
    // Registration is all-or-none: `Some` always contains one tag per
    // registered polynomial. [`Evaluator::record_polynomial_tag`] enforces the
    // invariant at every registration site.
    polynomial_tags: Option<Vec<EvaluationPolyTag>>,
    compressed_selectors: Vec<CompressedSelectorLeaf<E, B>>,
    reused_compressed_selector_sources: Vec<usize>,
    _context: E,
}

struct CompressedSelectorLeaf<E, B: Basis> {
    query: AstLeaf<E, B>,
    combination_len: usize,
    assigned_root: usize,
    selector: AstLeaf<E, B>,
}

/// Constructs a new `Evaluator`.
///
/// The `context` parameter is used to provide type safety for evaluators. It ensures that
/// an evaluator will only be used to evaluate [`Ast`]s containing [`AstLeaf`]s obtained
/// from itself. It should be set to the empty closure `|| {}`, because anonymous closures
/// all have unique types.
pub(crate) fn new_evaluator<'poly, E: Fn() + Clone, F: Field, B: Basis>(
    context: E,
) -> Evaluator<'poly, E, F, B> {
    Evaluator {
        polys: vec![],
        virtual_poly_count: None,
        polynomial_tags: None,
        compressed_selectors: vec![],
        reused_compressed_selector_sources: vec![],
        _context: context,
    }
}

/// Constructs an [`Evaluator`] that registers polynomial topology without
/// retaining polynomial values. The returned evaluator accepts only virtual
/// leaves and cannot evaluate rows.
pub(crate) fn new_virtual_evaluator<E: Fn() + Clone, F: Field, B: Basis>(
    context: E,
) -> Evaluator<'static, E, F, B> {
    Evaluator {
        polys: vec![],
        virtual_poly_count: Some(0),
        polynomial_tags: None,
        compressed_selectors: vec![],
        reused_compressed_selector_sources: vec![],
        _context: context,
    }
}

fn same_ast<E, F: Field, B: Basis>(lhs: &Ast<E, F, B>, rhs: &Ast<E, F, B>) -> bool {
    match (lhs, rhs) {
        (Ast::Poly(lhs), Ast::Poly(rhs)) => lhs == rhs,
        (Ast::Add(lhs_a, lhs_b), Ast::Add(rhs_a, rhs_b)) => {
            same_ast(lhs_a, rhs_a) && same_ast(lhs_b, rhs_b)
        }
        (Ast::Mul(AstMul(lhs_a, lhs_b)), Ast::Mul(AstMul(rhs_a, rhs_b))) => {
            same_ast(lhs_a, rhs_a) && same_ast(lhs_b, rhs_b)
        }
        (Ast::Scale(lhs, lhs_scalar), Ast::Scale(rhs, rhs_scalar)) => {
            lhs_scalar == rhs_scalar && same_ast(lhs, rhs)
        }
        (Ast::DistributePowers(lhs, lhs_base), Ast::DistributePowers(rhs, rhs_base)) => {
            lhs_base == rhs_base
                && lhs.len() == rhs.len()
                && lhs
                    .iter()
                    .zip(rhs.iter())
                    .all(|(lhs, rhs)| same_ast(lhs, rhs))
        }
        (
            Ast::DistributeChallengePowers(lhs, lhs_base),
            Ast::DistributeChallengePowers(rhs, rhs_base),
        ) => {
            lhs_base == rhs_base
                && lhs.len() == rhs.len()
                && lhs
                    .iter()
                    .zip(rhs.iter())
                    .all(|(lhs, rhs)| same_ast(lhs, rhs))
        }
        (Ast::LinearTerm(lhs), Ast::LinearTerm(rhs))
        | (Ast::ConstantTerm(lhs), Ast::ConstantTerm(rhs)) => lhs == rhs,
        (
            Ast::LinearChallengeTerm {
                challenge: lhs_challenge,
                factor: lhs_factor,
            },
            Ast::LinearChallengeTerm {
                challenge: rhs_challenge,
                factor: rhs_factor,
            },
        ) => lhs_challenge == rhs_challenge && lhs_factor == rhs_factor,
        (Ast::ChallengeTerm(lhs), Ast::ChallengeTerm(rhs)) => lhs == rhs,
        _ => false,
    }
}

type AstProduct<'a, E, F, B> = (&'a Ast<E, F, B>, &'a Ast<E, F, B>);

fn mul_terms<E, F: Field, B: Basis>(term: &Ast<E, F, B>) -> Option<AstProduct<'_, E, F, B>> {
    match term {
        Ast::Mul(AstMul(lhs, rhs)) => Some((lhs, rhs)),
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum FactorSide {
    Left,
    Right,
}

fn factor_terms<E, F: Field, B: Basis>(
    term: &Ast<E, F, B>,
    side: FactorSide,
) -> Option<AstProduct<'_, E, F, B>> {
    let (lhs, rhs) = mul_terms(term)?;
    Some(match side {
        FactorSide::Left => (lhs, rhs),
        FactorSide::Right => (rhs, lhs),
    })
}

struct FactorGroup<'a, E, F: Field, B: Basis> {
    factor: &'a Ast<E, F, B>,
    terms: Vec<(usize, &'a Ast<E, F, B>)>,
}

// Partitions product terms into repeated left factors, followed by repeated
// right factors among terms that were not claimed by a left-factor group.
fn factor_groups<'a, E, F: Field, B: Basis>(
    terms: &[&'a Ast<E, F, B>],
) -> Vec<FactorGroup<'a, E, F, B>> {
    let mut claimed = vec![false; terms.len()];
    let mut groups = vec![];

    for side in [FactorSide::Left, FactorSide::Right] {
        for index in 0..terms.len() {
            if claimed[index] {
                continue;
            }
            let factor = match factor_terms(terms[index], side) {
                Some((factor, _)) => factor,
                None => continue,
            };

            let matching = (index..terms.len())
                .filter(|candidate| !claimed[*candidate])
                .filter(|candidate| {
                    factor_terms(terms[*candidate], side)
                        .is_some_and(|(candidate, _)| same_ast(factor, candidate))
                })
                .collect::<Vec<_>>();
            if matching.len() < 2 {
                continue;
            }

            let terms = matching
                .into_iter()
                .map(|position| {
                    claimed[position] = true;
                    let (_, term) = factor_terms(terms[position], side)
                        .expect("a factor group only contains product terms");
                    (position, term)
                })
                .collect();
            groups.push(FactorGroup { factor, terms });
        }
    }

    groups
}

struct SelectorRunMatch {
    assigned_root: usize,
    start: usize,
    end: usize,
    side: FactorSide,
}

struct SelectorFamilyMatch<E, B: Basis> {
    query: AstLeaf<E, B>,
    combination_len: usize,
    runs: Vec<SelectorRunMatch>,
}

fn selector_difference<E, F: Field, B: Basis>(
    ast: &Ast<E, F, B>,
    minus_one: F,
) -> Option<(F, &AstLeaf<E, B>)> {
    match ast {
        Ast::Add(constant, negated_query) => match (constant.as_ref(), negated_query.as_ref()) {
            (Ast::ConstantTerm(root), Ast::Scale(query, scalar)) if *scalar == minus_one => {
                match query.as_ref() {
                    Ast::Poly(query) => Some((*root, query)),
                    _ => None,
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// Recognizes the exact expression emitted for a compressed selector.
fn compressed_selector<E, F: Field, B: Basis>(
    ast: &Ast<E, F, B>,
    minus_one: F,
) -> Option<(&AstLeaf<E, B>, usize, usize)> {
    let mut prefix = ast;
    let mut query = None;
    let mut roots = vec![];
    while let Ast::Mul(AstMul(lhs, rhs)) = prefix {
        let (root, candidate_query) = selector_difference(rhs, minus_one)?;
        match query {
            Some(query) if query != candidate_query => return None,
            Some(_) => {}
            None => query = Some(candidate_query),
        }
        roots.push(root);
        prefix = lhs;
    }

    let prefix_query = match prefix {
        Ast::Poly(query) => query,
        _ => return None,
    };
    if query.is_some_and(|query| query != prefix_query) {
        return None;
    }

    let combination_len = roots.len() + 1;
    if combination_len < crate::MIN_SELECTOR_FAMILY_LEN {
        return None;
    }

    // Roots are appended in ascending order, but peeling the left-nested
    // product above encounters them in reverse.
    roots.reverse();
    let mut roots = roots.iter().peekable();
    let mut expected = F::ONE;
    let mut assigned_root = None;
    for root_index in 1..=combination_len {
        if roots.peek().is_some_and(|root| **root == expected) {
            roots.next();
        } else if assigned_root.is_none() {
            assigned_root = Some(root_index);
        } else {
            return None;
        }
        expected += F::ONE;
    }
    if roots.next().is_some() {
        return None;
    }

    Some((prefix_query, combination_len, assigned_root?))
}

fn selector_family_matches<E: Copy, F: Field, B: Basis>(
    terms: &[Ast<E, F, B>],
    minus_one: F,
) -> Vec<SelectorFamilyMatch<E, B>> {
    let mut families: Vec<SelectorFamilyMatch<E, B>> = vec![];
    let mut start = 0;
    while start < terms.len() {
        let candidate = [FactorSide::Left, FactorSide::Right]
            .into_iter()
            .find_map(|side| {
                let (factor, _) = factor_terms(&terms[start], side)?;
                let (query, combination_len, assigned_root) =
                    compressed_selector(factor, minus_one)?;
                Some((side, factor, *query, combination_len, assigned_root))
            });

        if let Some((side, factor, query, combination_len, assigned_root)) = candidate {
            let mut end = start + 1;
            while end < terms.len()
                && factor_terms(&terms[end], side)
                    .is_some_and(|(candidate, _)| same_ast(factor, candidate))
            {
                end += 1;
            }
            let run = SelectorRunMatch {
                assigned_root,
                start,
                end,
                side,
            };
            match families
                .iter_mut()
                .find(|family| family.combination_len == combination_len && family.query == query)
            {
                Some(family) => family.runs.push(run),
                None => families.push(SelectorFamilyMatch {
                    query,
                    combination_len,
                    runs: vec![run],
                }),
            }
            start = end;
        } else {
            start += 1;
        }
    }

    families.retain_mut(|family| {
        family.runs.sort_by_key(|run| run.assigned_root);
        family.runs.len() == family.combination_len
            && family
                .runs
                .iter()
                .enumerate()
                .all(|(index, run)| run.assigned_root == index + 1)
    });
    families
}

// A private evaluation plan compiled once before parallel chunk evaluation.
// Structural AST matching and challenge-power calculation happen only while
// constructing this plan.
enum EvaluationPlan<F: Field> {
    Poly(IndexedLeaf),
    Add(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Square(Box<Self>),
    Scale(Box<Self>, ScalarId<F>),
    Horner {
        base: Box<Self>,
        coefficients: Box<[IndexedLeaf]>,
    },
    DistributePowers {
        work: Vec<DistributionWork<F>>,
        base: ScalarId<F>,
    },
    CacheStore {
        slot: usize,
        inner: Box<Self>,
    },
    CacheLoad {
        slot: usize,
    },
    LinearTerm(ScalarId<F>),
    ConstantTerm(ScalarId<F>),
}

enum DistributionWork<F: Field> {
    Term {
        term: EvaluationPlan<F>,
        power: ScalarId<F>,
    },
    WeightedSharedFactor {
        factor: EvaluationPlan<F>,
        terms: Vec<WeightedTerm<F>>,
    },
    SelectorFamily {
        query: IndexedLeaf,
        runs: Vec<SelectorFamilyRun<F>>,
    },
}

struct SelectorFamilyRun<F: Field> {
    bodies: FactorBodyPlan<F>,
    power: ScalarId<F>,
}

enum FactorBodyPlan<F: Field> {
    Sequential(Vec<EvaluationPlan<F>>),
    Factored(Vec<FactorBodyWork<F>>),
}

enum FactorBodyWork<F: Field> {
    Term(WeightedTerm<F>),
    SharedFactor {
        factor: EvaluationPlan<F>,
        terms: Vec<WeightedTerm<F>>,
    },
}

struct WeightedTerm<F: Field> {
    term: EvaluationPlan<F>,
    power: ScalarId<F>,
}

/// A challenge-independent compiled quotient plan retained by a proving key.
pub(crate) struct CompiledEvaluationPlan<F: Field, B: Basis> {
    plan: EvaluationPlan<F>,
    scalar_descriptors: Box<[PlanScalar<F>]>,
    evaluator_shape: EvaluatorShape,
    cache_slots: usize,
    scratch_slots: usize,
    max_challenge_exponents: [u32; EVALUATION_CHALLENGE_COUNT],
    _basis: PhantomData<B>,
}

impl<F: Field, B: Basis> CompiledEvaluationPlan<F, B> {
    pub(crate) fn payload_bytes(&self) -> usize {
        size_of::<Self>()
            + self.plan.heap_payload_bytes()
            + self.scalar_descriptors.len() * size_of::<PlanScalar<F>>()
            + self.evaluator_shape.polynomial_lengths.len() * size_of::<usize>()
            + self
                .evaluator_shape
                .polynomial_tags
                .as_ref()
                .map_or(0, |tags| tags.len() * size_of::<EvaluationPolyTag>())
            + self.evaluator_shape.compressed_selectors.len() * size_of::<CompressedSelectorShape>()
            + self
                .evaluator_shape
                .reused_compressed_selector_sources
                .len()
                * size_of::<usize>()
    }

    /// Returns whether every polynomial in this plan has an exact semantic
    /// tag. Only such plans are safe to retain across prover calls.
    pub(crate) fn has_exact_polynomial_tags(&self) -> bool {
        self.evaluator_shape
            .polynomial_tags
            .as_ref()
            .is_some_and(|tags| tags.len() == self.evaluator_shape.polynomial_lengths.len())
    }

    #[cfg(test)]
    pub(crate) fn swap_polynomial_tags(&mut self, lhs: EvaluationPolyTag, rhs: EvaluationPolyTag) {
        let tags = self
            .evaluator_shape
            .polynomial_tags
            .as_mut()
            .expect("the plan has exact polynomial tags");
        let lhs_index = tags
            .iter()
            .position(|tag| *tag == lhs)
            .expect("the left polynomial tag is present");
        let rhs_index = tags
            .iter()
            .position(|tag| *tag == rhs)
            .expect("the right polynomial tag is present");
        tags.swap(lhs_index, rhs_index);
    }
}

const MIN_HORNER_COEFFICIENTS: usize = 4;

fn field_from_small_usize<F: Field>(value: usize) -> F {
    (0..value).fold(F::ZERO, |accumulator, _| accumulator + F::ONE)
}

struct ExpandedPolynomial<'a, E, F: Field, B: Basis> {
    base: &'a Ast<E, F, B>,
    coefficients: Box<[AstLeaf<E, B>]>,
}

// Recognizes a polynomial assembled from independently constructed powers:
//
// `0 + 1 * c_0 + (1 * x) * c_1 + ((1 * x) * x) * c_2 + ...`.
//
// This exact shape is emitted by fixed-base coordinate interpolation
// constraints. The compiled plan evaluates it with Horner's method while the
// constraint expression remains unchanged.
fn expanded_polynomial<E: Copy, F: Field, B: Basis>(
    ast: &Ast<E, F, B>,
) -> Option<ExpandedPolynomial<'_, E, F, B>> {
    let mut terms = vec![];
    let mut prefix = ast;
    while let Ast::Add(lhs, rhs) = prefix {
        terms.push(rhs.as_ref());
        prefix = lhs.as_ref();
    }
    if !matches!(prefix, Ast::ConstantTerm(constant) if *constant == F::ZERO) {
        return None;
    }
    terms.reverse();

    // Small polynomials do not recover the recognition and evaluation
    // overhead.
    if terms.len() < MIN_HORNER_COEFFICIENTS {
        return None;
    }

    let mut base = None;
    let mut previous_power = None;
    let mut coefficients = Vec::with_capacity(terms.len());
    for (degree, term) in terms.into_iter().enumerate() {
        let (power, coefficient) = mul_terms(term)?;
        let coefficient = match coefficient {
            Ast::Poly(coefficient) => *coefficient,
            _ => return None,
        };

        if degree == 0 {
            if !matches!(power, Ast::ConstantTerm(constant) if *constant == F::ONE) {
                return None;
            }
        } else {
            let (power_prefix, candidate_base) = mul_terms(power)?;
            if !same_ast(power_prefix, previous_power?) {
                return None;
            }
            match base {
                Some(base) if !same_ast(base, candidate_base) => return None,
                Some(_) => {}
                None => base = Some(candidate_base),
            }
        }

        previous_power = Some(power);
        coefficients.push(coefficient);
    }

    Some(ExpandedPolynomial {
        base: base?,
        coefficients: coefficients.into_boxed_slice(),
    })
}

// Accumulates a polynomial expression against precomputed powers. Pasta
// fields use their wide product accumulator. Other fields retain ordinary
// field arithmetic, without adding a bound to the public prover API.
enum PowerFold<'a, F: Field> {
    Eager {
        accumulators: Vec<F>,
        terms: &'a mut [F],
        factors: Option<Vec<F>>,
    },
    Pallas {
        accumulators: Vec<<pallas::Base as DeferredField>::Accumulator>,
        terms: Vec<F>,
        factors: Option<Vec<F>>,
        addends: Option<Vec<F>>,
        output: &'a mut [F],
    },
    Vesta {
        accumulators: Vec<<vesta::Base as DeferredField>::Accumulator>,
        terms: Vec<F>,
        factors: Option<Vec<F>>,
        addends: Option<Vec<F>>,
        output: &'a mut [F],
    },
}

impl<'a, F: Field> PowerFold<'a, F> {
    fn new(output: &'a mut [F]) -> Self {
        if TypeId::of::<F>() == TypeId::of::<pallas::Base>() {
            Self::Pallas {
                accumulators: vec![Default::default(); output.len()],
                terms: vec![F::ZERO; output.len()],
                factors: None,
                addends: None,
                output,
            }
        } else if TypeId::of::<F>() == TypeId::of::<vesta::Base>() {
            Self::Vesta {
                accumulators: vec![Default::default(); output.len()],
                terms: vec![F::ZERO; output.len()],
                factors: None,
                addends: None,
                output,
            }
        } else {
            Self::Eager {
                accumulators: vec![F::ZERO; output.len()],
                terms: output,
                factors: None,
            }
        }
    }

    fn terms(&mut self) -> &mut [F] {
        match self {
            Self::Eager { terms, .. } => terms,
            Self::Pallas { terms, .. } => terms,
            Self::Vesta { terms, .. } => terms,
        }
    }

    fn factors(&mut self) -> &mut [F] {
        let (factors, len) = match self {
            Self::Eager { terms, factors, .. } => (factors, terms.len()),
            Self::Pallas { terms, factors, .. } => (factors, terms.len()),
            Self::Vesta { terms, factors, .. } => (factors, terms.len()),
        };
        factors
            .get_or_insert_with(|| vec![F::ZERO; len])
            .as_mut_slice()
    }

    fn accumulate(&mut self, power: F) {
        if power == F::ONE {
            self.accumulate_addends();
            return;
        }

        match self {
            Self::Eager {
                accumulators,
                terms,
                ..
            } => {
                for (accumulator, term) in accumulators.iter_mut().zip(terms.iter()) {
                    *accumulator += *term * power;
                }
            }
            Self::Pallas {
                accumulators,
                terms,
                ..
            } => accumulate_deferred::<pallas::Base>(accumulators, &*terms, &power),
            Self::Vesta {
                accumulators,
                terms,
                ..
            } => accumulate_deferred::<vesta::Base>(accumulators, &*terms, &power),
        }
    }

    fn accumulate_addends(&mut self) {
        match self {
            Self::Eager {
                accumulators,
                terms,
                ..
            } => {
                for (accumulator, term) in accumulators.iter_mut().zip(terms.iter()) {
                    *accumulator += term;
                }
            }
            Self::Pallas { addends, terms, .. } | Self::Vesta { addends, terms, .. } => {
                match addends {
                    Some(addends) => {
                        for (addend, term) in addends.iter_mut().zip(terms.iter()) {
                            *addend += term;
                        }
                    }
                    None => *addends = Some(terms.clone()),
                }
            }
        }
    }

    fn accumulate_products(&mut self) {
        match self {
            Self::Eager {
                accumulators,
                terms,
                factors,
            } => {
                let factors = factors
                    .as_ref()
                    .expect("factor values are evaluated before accumulation");
                for ((accumulator, term), factor) in
                    accumulators.iter_mut().zip(terms.iter()).zip(factors)
                {
                    *accumulator += *term * factor;
                }
            }
            Self::Pallas {
                accumulators,
                terms,
                factors,
                ..
            } => accumulate_deferred_products::<pallas::Base>(
                accumulators,
                &*terms,
                factors
                    .as_ref()
                    .expect("factor values are evaluated before accumulation"),
            ),
            Self::Vesta {
                accumulators,
                terms,
                factors,
                ..
            } => accumulate_deferred_products::<vesta::Base>(
                accumulators,
                &*terms,
                factors
                    .as_ref()
                    .expect("factor values are evaluated before accumulation"),
            ),
        }
    }

    fn finish(self) {
        match self {
            Self::Eager {
                accumulators,
                terms,
                ..
            } => terms.copy_from_slice(&accumulators),
            Self::Pallas {
                accumulators,
                addends,
                output,
                ..
            } => {
                let mut result = reduce_deferred::<pallas::Base, _>(accumulators);
                if let Some(addends) = addends {
                    for (result, addend) in result.iter_mut().zip(addends) {
                        *result += addend;
                    }
                }
                output.copy_from_slice(&result);
            }
            Self::Vesta {
                accumulators,
                addends,
                output,
                ..
            } => {
                let mut result = reduce_deferred::<vesta::Base, _>(accumulators);
                if let Some(addends) = addends {
                    for (result, addend) in result.iter_mut().zip(addends) {
                        *result += addend;
                    }
                }
                output.copy_from_slice(&result);
            }
        }
    }
}

// Reuses the buffers for consecutive weighted folds within one distribution
// and one Rayon chunk. A reset makes prior contents unreachable: terms are
// overwritten before accumulation, and the flags guard addends and products
// until their buffers have been initialized for the current fold.
struct DeferredPowerFold<T: DeferredField, F: Field> {
    accumulators: Vec<T::Accumulator>,
    terms: Vec<F>,
    addends: Vec<F>,
    reduced: Vec<F>,
    has_products: bool,
    has_addends: bool,
}

impl<T: DeferredField + 'static, F: Field> DeferredPowerFold<T, F> {
    fn new(len: usize) -> Self {
        Self {
            accumulators: vec![Default::default(); len],
            terms: vec![F::ZERO; len],
            addends: vec![F::ZERO; len],
            reduced: vec![F::ZERO; len],
            has_products: false,
            has_addends: false,
        }
    }

    fn reset(&mut self) {
        self.has_products = false;
        self.has_addends = false;
    }

    fn accumulate(&mut self, power: F) {
        if power == F::ONE {
            if self.has_addends {
                for (addend, term) in self.addends.iter_mut().zip(&self.terms) {
                    *addend += term;
                }
            } else {
                self.addends.copy_from_slice(&self.terms);
                self.has_addends = true;
            }
        } else if self.has_products {
            accumulate_deferred::<T>(&mut self.accumulators, &self.terms, &power);
        } else {
            initialize_deferred::<T>(&mut self.accumulators, &self.terms, &power);
            self.has_products = true;
        }
    }

    fn finish_into(&mut self, output: &mut [F]) {
        if self.has_products {
            reduce_deferred_into::<T, F>(&self.accumulators, &mut self.reduced);
        } else {
            self.reduced.fill(F::ZERO);
        }
        if self.has_addends {
            for (result, addend) in self.reduced.iter_mut().zip(&self.addends) {
                *result += addend;
            }
        }
        output.copy_from_slice(&self.reduced);
    }
}

enum ReusablePowerFold<F: Field> {
    Eager { accumulators: Vec<F>, terms: Vec<F> },
    Pallas(DeferredPowerFold<pallas::Base, F>),
    Vesta(DeferredPowerFold<vesta::Base, F>),
}

impl<F: Field> ReusablePowerFold<F> {
    fn new(len: usize) -> Self {
        if TypeId::of::<F>() == TypeId::of::<pallas::Base>() {
            Self::Pallas(DeferredPowerFold::new(len))
        } else if TypeId::of::<F>() == TypeId::of::<vesta::Base>() {
            Self::Vesta(DeferredPowerFold::new(len))
        } else {
            Self::Eager {
                accumulators: vec![F::ZERO; len],
                terms: vec![F::ZERO; len],
            }
        }
    }

    fn reset(&mut self) {
        match self {
            Self::Eager { accumulators, .. } => accumulators.fill(F::ZERO),
            Self::Pallas(fold) => fold.reset(),
            Self::Vesta(fold) => fold.reset(),
        }
    }

    fn terms(&mut self) -> &mut [F] {
        match self {
            Self::Eager { terms, .. } => terms,
            Self::Pallas(fold) => &mut fold.terms,
            Self::Vesta(fold) => &mut fold.terms,
        }
    }

    fn accumulate(&mut self, power: F) {
        match self {
            Self::Eager {
                accumulators,
                terms,
            } => {
                if power == F::ONE {
                    for (accumulator, term) in accumulators.iter_mut().zip(terms) {
                        *accumulator += *term;
                    }
                } else {
                    for (accumulator, term) in accumulators.iter_mut().zip(terms) {
                        *accumulator += *term * power;
                    }
                }
            }
            Self::Pallas(fold) => fold.accumulate(power),
            Self::Vesta(fold) => fold.accumulate(power),
        }
    }

    fn finish_into(&mut self, output: &mut [F]) {
        match self {
            Self::Eager { accumulators, .. } => output.copy_from_slice(accumulators),
            Self::Pallas(fold) => fold.finish_into(output),
            Self::Vesta(fold) => fold.finish_into(output),
        }
    }
}

fn initialize_deferred<T: DeferredField + 'static>(
    accumulators: &mut [T::Accumulator],
    terms: &dyn Any,
    power: &dyn Any,
) {
    let terms = terms
        .downcast_ref::<Vec<T>>()
        .expect("term buffer matches the deferred field")
        .as_slice();
    let power = power
        .downcast_ref::<T>()
        .expect("power matches the deferred field");
    for (accumulator, term) in accumulators.iter_mut().zip(terms) {
        let mut initialized = T::Accumulator::default();
        T::mul_accumulate(&mut initialized, term, power);
        *accumulator = initialized;
    }
}

fn accumulate_deferred<T: DeferredField + 'static>(
    accumulators: &mut [T::Accumulator],
    terms: &dyn Any,
    power: &dyn Any,
) {
    let terms = terms
        .downcast_ref::<Vec<T>>()
        .expect("term buffer matches the deferred field")
        .as_slice();
    let power = power
        .downcast_ref::<T>()
        .expect("power matches the deferred field");
    for (accumulator, term) in accumulators.iter_mut().zip(terms) {
        T::mul_accumulate(accumulator, term, power);
    }
}

fn accumulate_deferred_products<T: DeferredField + 'static>(
    accumulators: &mut [T::Accumulator],
    terms: &dyn Any,
    factors: &dyn Any,
) {
    let terms = terms
        .downcast_ref::<Vec<T>>()
        .expect("term buffer matches the deferred field");
    let factors = factors
        .downcast_ref::<Vec<T>>()
        .expect("factor buffer matches the deferred field");
    for ((accumulator, term), factor) in accumulators.iter_mut().zip(terms).zip(factors) {
        T::mul_accumulate(accumulator, term, factor);
    }
}

fn reduce_deferred<T: DeferredField + 'static, F: Field>(
    accumulators: Vec<T::Accumulator>,
) -> Vec<F> {
    let values: Box<dyn Any> =
        Box::new(accumulators.into_iter().map(T::reduce).collect::<Vec<_>>());
    match values.downcast::<Vec<F>>() {
        Ok(values) => *values,
        Err(_) => unreachable!("field type was checked before accumulation"),
    }
}

fn reduce_deferred_into<T: DeferredField + 'static, F: Field>(
    accumulators: &[T::Accumulator],
    values: &mut Vec<F>,
) {
    let values = (values as &mut dyn Any)
        .downcast_mut::<Vec<T>>()
        .expect("output buffer matches the deferred field");
    for (value, accumulator) in values.iter_mut().zip(accumulators) {
        *value = T::reduce(*accumulator);
    }
}

#[derive(Clone, Copy)]
enum PowerBase<F> {
    Literal(F),
    Challenge(EvaluationChallenge),
}

impl<F: Field> PowerBase<F> {
    fn scalar(self) -> PlanScalar<F> {
        match self {
            Self::Literal(value) => PlanScalar::Literal(value),
            Self::Challenge(challenge) => PlanScalar::Challenge(challenge),
        }
    }

    fn powers(self, len: usize) -> Vec<PlanScalar<F>> {
        match self {
            Self::Literal(base) => {
                let mut power = F::ONE;
                (0..len)
                    .map(|_| {
                        let current = power;
                        power *= base;
                        PlanScalar::Literal(current)
                    })
                    .collect()
            }
            Self::Challenge(challenge) => (0..len)
                .map(|exponent| PlanScalar::ChallengePower {
                    challenge,
                    exponent: exponent
                        .try_into()
                        .expect("a quotient expression count fits in u32"),
                })
                .collect(),
        }
    }
}

impl<F: Field> EvaluationPlan<F> {
    fn compile<E: Copy, B: Basis>(ast: &Ast<E, F, B>, scalars: &mut PlanScalarInterner<F>) -> Self {
        if let Ast::Add(_, _) = ast
            && let Some(polynomial) = expanded_polynomial(ast)
        {
            return Self::Horner {
                base: Box::new(Self::compile(polynomial.base, scalars)),
                coefficients: polynomial
                    .coefficients
                    .iter()
                    .copied()
                    .map(IndexedLeaf::from)
                    .collect(),
            };
        }

        match ast {
            Ast::Poly(leaf) => Self::Poly((*leaf).into()),
            Ast::Add(lhs, rhs) => Self::Add(
                Box::new(Self::compile(lhs, scalars)),
                Box::new(Self::compile(rhs, scalars)),
            ),
            Ast::Mul(AstMul(lhs, rhs)) if same_ast(lhs, rhs) => {
                Self::Square(Box::new(Self::compile(lhs, scalars)))
            }
            Ast::Mul(AstMul(lhs, rhs)) => Self::Mul(
                Box::new(Self::compile(lhs, scalars)),
                Box::new(Self::compile(rhs, scalars)),
            ),
            Ast::Scale(inner, scalar) => Self::Scale(
                Box::new(Self::compile(inner, scalars)),
                scalars.intern(PlanScalar::Literal(*scalar)),
            ),
            Ast::DistributePowers(terms, base) => {
                Self::compile_distribute_powers(terms, PowerBase::Literal(*base), scalars)
            }
            Ast::DistributeChallengePowers(terms, challenge) => {
                Self::compile_distribute_powers(terms, PowerBase::Challenge(*challenge), scalars)
            }
            Ast::LinearTerm(scalar) => {
                Self::LinearTerm(scalars.intern(PlanScalar::Literal(*scalar)))
            }
            Ast::LinearChallengeTerm { challenge, factor } => {
                Self::LinearTerm(scalars.intern(PlanScalar::ScaledChallenge {
                    challenge: *challenge,
                    factor: *factor,
                }))
            }
            Ast::ConstantTerm(scalar) => {
                Self::ConstantTerm(scalars.intern(PlanScalar::Literal(*scalar)))
            }
            Ast::ChallengeTerm(challenge) => {
                Self::ConstantTerm(scalars.intern(PlanScalar::Challenge(*challenge)))
            }
        }
    }

    fn compile_distribute_powers<E: Copy, B: Basis>(
        terms: &[Ast<E, F, B>],
        base: PowerBase<F>,
        scalars: &mut PlanScalarInterner<F>,
    ) -> Self {
        match terms {
            [] => Self::ConstantTerm(scalars.intern(PlanScalar::Literal(F::ZERO))),
            [term] => Self::compile(term, scalars),
            terms => {
                let mut work = Vec::with_capacity(terms.len());
                let powers = base.powers(terms.len());

                let selector_families = selector_family_matches(terms, -F::ONE);
                let mut claimed = vec![false; terms.len()];
                for family in selector_families {
                    let runs = family
                        .runs
                        .into_iter()
                        .map(|run| {
                            debug_assert!(claimed[run.start..run.end].iter().all(|value| !value));
                            claimed[run.start..run.end].fill(true);
                            let bodies = terms[run.start..run.end]
                                .iter()
                                .map(|term| {
                                    let (_, body) = factor_terms(term, run.side)
                                        .expect("a selector-family run only contains products");
                                    body
                                })
                                .collect::<Vec<_>>();
                            SelectorFamilyRun {
                                bodies: FactorBodyPlan::compile(&bodies, base, scalars),
                                power: scalars.intern(powers[terms.len() - run.end]),
                            }
                        })
                        .collect();
                    work.push(DistributionWork::SelectorFamily {
                        query: family.query.into(),
                        runs,
                    });
                }

                // Group matching factors even when other constraint terms
                // separate them. Retaining each body's absolute challenge
                // power preserves the original transcript-defined ordering.
                let available_positions = claimed
                    .iter()
                    .enumerate()
                    .filter_map(|(position, claimed)| (!claimed).then_some(position))
                    .collect::<Vec<_>>();
                let available_terms = available_positions
                    .iter()
                    .map(|position| &terms[*position])
                    .collect::<Vec<_>>();
                for group in factor_groups(&available_terms) {
                    let terms = group
                        .terms
                        .into_iter()
                        .map(|(available_position, term)| {
                            let position = available_positions[available_position];
                            claimed[position] = true;
                            WeightedTerm {
                                term: EvaluationPlan::compile(term, scalars),
                                power: scalars.intern(powers[terms.len() - 1 - position]),
                            }
                        })
                        .collect();
                    work.push(DistributionWork::WeightedSharedFactor {
                        factor: Self::compile(group.factor, scalars),
                        terms,
                    });
                }

                // Every repeated factor was claimed above, so append the
                // remaining independent terms from the lowest original
                // challenge power to the highest.
                for position in (0..terms.len()).rev() {
                    if !claimed[position] {
                        work.push(DistributionWork::Term {
                            term: Self::compile(&terms[position], scalars),
                            power: scalars.intern(powers[terms.len() - 1 - position]),
                        });
                    }
                }

                Self::DistributePowers {
                    work,
                    base: scalars.intern(base.scalar()),
                }
            }
        }
    }

    fn required_scratch_slots(&self) -> usize {
        match self {
            Self::Poly(_) | Self::LinearTerm(_) | Self::ConstantTerm(_) => 0,
            Self::Add(lhs, rhs) | Self::Mul(lhs, rhs) => lhs
                .required_scratch_slots()
                .max(1 + rhs.required_scratch_slots()),
            Self::Square(inner) | Self::Scale(inner, _) => inner.required_scratch_slots(),
            Self::Horner { base, .. } => 1 + base.required_scratch_slots().max(1),
            Self::DistributePowers { work, .. } => work
                .iter()
                .map(DistributionWork::required_scratch_slots)
                .max()
                .unwrap_or(0),
            Self::CacheStore { inner, .. } => inner.required_scratch_slots(),
            Self::CacheLoad { .. } => 0,
        }
    }

    // Counts retained allocation payloads exactly, excluding allocator and
    // [`Arc`] headers and rounding.
    fn heap_payload_bytes(&self) -> usize {
        match self {
            Self::Add(lhs, rhs) | Self::Mul(lhs, rhs) => {
                2 * size_of::<Self>() + lhs.heap_payload_bytes() + rhs.heap_payload_bytes()
            }
            Self::Square(inner) | Self::Scale(inner, _) | Self::CacheStore { inner, .. } => {
                size_of::<Self>() + inner.heap_payload_bytes()
            }
            Self::Horner { base, coefficients } => {
                size_of::<Self>()
                    + base.heap_payload_bytes()
                    + coefficients.len() * size_of::<IndexedLeaf>()
            }
            Self::DistributePowers { work, .. } => {
                work.capacity() * size_of::<DistributionWork<F>>()
                    + work
                        .iter()
                        .map(DistributionWork::heap_payload_bytes)
                        .sum::<usize>()
            }
            Self::Poly(_)
            | Self::CacheLoad { .. }
            | Self::LinearTerm(_)
            | Self::ConstantTerm(_) => 0,
        }
    }
}

impl<F: Field> DistributionWork<F> {
    fn heap_payload_bytes(&self) -> usize {
        match self {
            Self::Term { term, .. } => term.heap_payload_bytes(),
            Self::WeightedSharedFactor { factor, terms } => {
                factor.heap_payload_bytes()
                    + terms.capacity() * size_of::<WeightedTerm<F>>()
                    + terms
                        .iter()
                        .map(|term| term.term.heap_payload_bytes())
                        .sum::<usize>()
            }
            Self::SelectorFamily { runs, .. } => {
                runs.capacity() * size_of::<SelectorFamilyRun<F>>()
                    + runs
                        .iter()
                        .map(|run| run.bodies.heap_payload_bytes())
                        .sum::<usize>()
            }
        }
    }
}

impl<F: Field> FactorBodyPlan<F> {
    fn heap_payload_bytes(&self) -> usize {
        match self {
            Self::Sequential(plans) => {
                plans.capacity() * size_of::<EvaluationPlan<F>>()
                    + plans
                        .iter()
                        .map(EvaluationPlan::heap_payload_bytes)
                        .sum::<usize>()
            }
            Self::Factored(work) => {
                work.capacity() * size_of::<FactorBodyWork<F>>()
                    + work
                        .iter()
                        .map(FactorBodyWork::heap_payload_bytes)
                        .sum::<usize>()
            }
        }
    }
}

impl<F: Field> FactorBodyWork<F> {
    fn heap_payload_bytes(&self) -> usize {
        match self {
            Self::Term(term) => term.term.heap_payload_bytes(),
            Self::SharedFactor { factor, terms } => {
                factor.heap_payload_bytes()
                    + terms.capacity() * size_of::<WeightedTerm<F>>()
                    + terms
                        .iter()
                        .map(|term| term.term.heap_payload_bytes())
                        .sum::<usize>()
            }
        }
    }
}

fn max_challenge_exponents<F: Field>(
    descriptors: &[PlanScalar<F>],
) -> [u32; EVALUATION_CHALLENGE_COUNT] {
    let mut max_exponents = [0; EVALUATION_CHALLENGE_COUNT];
    for descriptor in descriptors {
        descriptor.record_max_exponent(&mut max_exponents);
    }
    max_exponents
}

fn same_plan<F: Field>(lhs: &EvaluationPlan<F>, rhs: &EvaluationPlan<F>) -> bool {
    match (lhs, rhs) {
        (EvaluationPlan::Poly(lhs), EvaluationPlan::Poly(rhs)) => lhs == rhs,
        (EvaluationPlan::Add(lhs_a, lhs_b), EvaluationPlan::Add(rhs_a, rhs_b))
        | (EvaluationPlan::Mul(lhs_a, lhs_b), EvaluationPlan::Mul(rhs_a, rhs_b)) => {
            same_plan(lhs_a, rhs_a) && same_plan(lhs_b, rhs_b)
        }
        (EvaluationPlan::Square(lhs), EvaluationPlan::Square(rhs)) => same_plan(lhs, rhs),
        (EvaluationPlan::Scale(lhs, lhs_scalar), EvaluationPlan::Scale(rhs, rhs_scalar)) => {
            lhs_scalar == rhs_scalar && same_plan(lhs, rhs)
        }
        (
            EvaluationPlan::Horner {
                base: lhs_base,
                coefficients: lhs_coefficients,
            },
            EvaluationPlan::Horner {
                base: rhs_base,
                coefficients: rhs_coefficients,
            },
        ) => {
            same_plan(lhs_base, rhs_base)
                && lhs_coefficients.len() == rhs_coefficients.len()
                && lhs_coefficients
                    .iter()
                    .zip(rhs_coefficients.iter())
                    .all(|(lhs, rhs)| lhs == rhs)
        }
        (EvaluationPlan::LinearTerm(lhs), EvaluationPlan::LinearTerm(rhs))
        | (EvaluationPlan::ConstantTerm(lhs), EvaluationPlan::ConstantTerm(rhs)) => lhs == rhs,
        (EvaluationPlan::CacheStore { .. }, _)
        | (EvaluationPlan::CacheLoad { .. }, _)
        | (_, EvaluationPlan::CacheStore { .. })
        | (_, EvaluationPlan::CacheLoad { .. }) => {
            unreachable!("common-subexpression planning runs once")
        }
        _ => false,
    }
}

struct PlanOccurrence<'a, F: Field> {
    plan: &'a EvaluationPlan<F>,
    end: usize,
    fingerprint: u64,
}

fn fingerprint<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn collect_plan_occurrences<'a, F: Field>(
    plan: &'a EvaluationPlan<F>,
    nodes: &mut Vec<PlanOccurrence<'a, F>>,
) -> u64 {
    let index = nodes.len();
    nodes.push(PlanOccurrence {
        plan,
        end: usize::MAX,
        fingerprint: 0,
    });
    let plan_fingerprint = match plan {
        EvaluationPlan::Add(lhs, rhs) | EvaluationPlan::Mul(lhs, rhs) => {
            let lhs = collect_plan_occurrences(lhs, nodes);
            let rhs = collect_plan_occurrences(rhs, nodes);
            let tag = usize::from(matches!(plan, EvaluationPlan::Mul(_, _)));
            fingerprint(&(tag, lhs, rhs))
        }
        EvaluationPlan::Square(inner) => {
            let inner = collect_plan_occurrences(inner, nodes);
            fingerprint(&(2usize, inner))
        }
        EvaluationPlan::Scale(inner, scalar) => {
            let inner = collect_plan_occurrences(inner, nodes);
            fingerprint(&(3usize, inner, scalar))
        }
        EvaluationPlan::Horner { base, coefficients } => {
            let base = collect_plan_occurrences(base, nodes);
            fingerprint(&(4usize, base, coefficients.as_ref()))
        }
        EvaluationPlan::DistributePowers { work, .. } => {
            for work in work {
                match work {
                    DistributionWork::Term { term, .. } => {
                        collect_plan_occurrences(term, nodes);
                    }
                    DistributionWork::WeightedSharedFactor { factor, terms } => {
                        collect_plan_occurrences(factor, nodes);
                        for term in terms {
                            collect_plan_occurrences(&term.term, nodes);
                        }
                    }
                    DistributionWork::SelectorFamily { runs, .. } => {
                        for run in runs.iter().rev() {
                            collect_factor_body_occurrences(&run.bodies, nodes);
                        }
                    }
                }
            }
            // Distribution plans are never themselves cache candidates.
            fingerprint(&(5usize, index))
        }
        EvaluationPlan::Poly(leaf) => fingerprint(&(6usize, leaf)),
        EvaluationPlan::LinearTerm(scalar) => fingerprint(&(7usize, scalar)),
        EvaluationPlan::ConstantTerm(scalar) => fingerprint(&(8usize, scalar)),
        EvaluationPlan::CacheStore { .. } | EvaluationPlan::CacheLoad { .. } => {
            unreachable!("common-subexpression planning runs once")
        }
    };
    nodes[index].end = nodes.len();
    nodes[index].fingerprint = plan_fingerprint;
    plan_fingerprint
}

fn collect_factor_body_occurrences<'a, F: Field>(
    plan: &'a FactorBodyPlan<F>,
    nodes: &mut Vec<PlanOccurrence<'a, F>>,
) {
    match plan {
        FactorBodyPlan::Sequential(bodies) => {
            for body in bodies {
                collect_plan_occurrences(body, nodes);
            }
        }
        FactorBodyPlan::Factored(work) => {
            for work in work {
                match work {
                    FactorBodyWork::Term(term) => {
                        collect_plan_occurrences(&term.term, nodes);
                    }
                    FactorBodyWork::SharedFactor { factor, terms } => {
                        collect_plan_occurrences(factor, nodes);
                        for term in terms {
                            collect_plan_occurrences(&term.term, nodes);
                        }
                    }
                }
            }
        }
    }
}

fn plan_cost<F: Field>(
    plan: &EvaluationPlan<F>,
    two: F,
    scalars: &[PlanScalar<F>],
) -> (usize, usize) {
    match plan {
        EvaluationPlan::Poly(_)
        | EvaluationPlan::LinearTerm(_)
        | EvaluationPlan::ConstantTerm(_) => (0, 1),
        EvaluationPlan::Add(lhs, rhs) => {
            let lhs = plan_cost(lhs, two, scalars);
            let rhs = plan_cost(rhs, two, scalars);
            (lhs.0 + rhs.0, 1 + lhs.1 + rhs.1)
        }
        EvaluationPlan::Mul(lhs, rhs) => {
            let lhs = plan_cost(lhs, two, scalars);
            let rhs = plan_cost(rhs, two, scalars);
            (1 + lhs.0 + rhs.0, 1 + lhs.1 + rhs.1)
        }
        EvaluationPlan::Square(inner) => {
            let inner = plan_cost(inner, two, scalars);
            (1 + inner.0, 1 + inner.1)
        }
        EvaluationPlan::Scale(inner, scalar) => {
            let inner = plan_cost(inner, two, scalars);
            let multiplication = match scalars[scalar.index()] {
                PlanScalar::Literal(scalar) => {
                    usize::from(scalar != -F::ONE && scalar != F::ONE && scalar != two)
                }
                PlanScalar::Challenge(_)
                | PlanScalar::ScaledChallenge { .. }
                | PlanScalar::ChallengePower { .. } => 1,
            };
            (multiplication + inner.0, 1 + inner.1)
        }
        EvaluationPlan::Horner { base, coefficients } => {
            let base = plan_cost(base, two, scalars);
            (
                base.0 + coefficients.len() - 1,
                1 + base.1 + coefficients.len(),
            )
        }
        EvaluationPlan::DistributePowers { .. } => (0, 1),
        EvaluationPlan::CacheStore { .. } | EvaluationPlan::CacheLoad { .. } => {
            unreachable!("common-subexpression planning runs once")
        }
    }
}

// Each cached polynomial occupies one chunk-sized buffer. One avoided field
// multiplication amortizes storing and loading that buffer; copy-only shapes
// remain uncached.
const MIN_CSE_SAVED_MULTIPLICATIONS: usize = 1;

#[derive(Clone, Copy)]
struct CacheAction {
    slot: usize,
    store: bool,
    end: usize,
}

const CACHE_EVENT_LOAD: u8 = 0;
const CACHE_EVENT_STORE: u8 = 1;

#[derive(Clone, Copy, Debug)]
struct CacheEvent {
    occurrence: u32,
    end: u32,
    slot: u16,
    kind: u8,
    reserved: u8,
}

/// A sparse, circuit-count-specific evaluator cache schedule.
struct EvaluationCacheLayout {
    events: Box<[CacheEvent]>,
    occurrence_count: u32,
    cache_slots: u16,
}

impl EvaluationCacheLayout {
    fn from_actions(actions: &[Option<CacheAction>], cache_slots: usize) -> Option<Self> {
        let occurrence_count = actions.len().try_into().ok()?;
        let cache_slots = cache_slots.try_into().ok()?;
        let events = actions
            .iter()
            .enumerate()
            .filter_map(|(occurrence, action)| action.map(|action| (occurrence, action)))
            .map(|(occurrence, action)| {
                Some(CacheEvent {
                    occurrence: occurrence.try_into().ok()?,
                    end: action.end.try_into().ok()?,
                    slot: action.slot.try_into().ok()?,
                    kind: if action.store {
                        CACHE_EVENT_STORE
                    } else {
                        CACHE_EVENT_LOAD
                    },
                    reserved: 0,
                })
            })
            .collect::<Option<Box<[_]>>>()?;
        Some(Self {
            events,
            occurrence_count,
            cache_slots,
        })
    }

    fn is_valid_for<F: Field>(&self, plan: &EvaluationPlan<F>) -> bool {
        validate_cache_events(plan, self)
    }
}

fn cache_slot_intervals(
    actions: &[Option<CacheAction>],
    cache_slots: usize,
) -> Vec<(usize, usize)> {
    let mut intervals = vec![(usize::MAX, 0); cache_slots];
    for (occurrence, action) in actions.iter().enumerate() {
        if let Some(action) = action {
            let interval = &mut intervals[action.slot];
            if action.store {
                interval.0 = occurrence;
            }
            interval.1 = occurrence;
        }
    }
    debug_assert!(intervals.iter().all(|(start, _)| *start != usize::MAX));
    intervals
}

// Reuses physical cache buffers whose traversal-order lifetimes do not
// overlap. Cache stores and loads remain unchanged.
fn reuse_cache_slots(actions: &mut [Option<CacheAction>], cache_slots: usize) -> usize {
    let intervals = cache_slot_intervals(actions, cache_slots);
    let mut order = (0..cache_slots).collect::<Vec<_>>();
    order.sort_unstable_by_key(|slot| intervals[*slot].0);
    let mut remap = vec![0; cache_slots];
    let mut active = Vec::<(usize, usize)>::new();
    let mut free = vec![];
    let mut next_slot = 0;
    for old_slot in order {
        let (start, end) = intervals[old_slot];
        let mut index = 0;
        while index < active.len() {
            if active[index].0 < start {
                free.push(active.swap_remove(index).1);
            } else {
                index += 1;
            }
        }

        let new_slot = free.pop().unwrap_or_else(|| {
            let slot = next_slot;
            next_slot += 1;
            slot
        });
        remap[old_slot] = new_slot;
        active.push((end, new_slot));
    }

    for action in actions.iter_mut().flatten() {
        action.slot = remap[action.slot];
    }
    next_slot
}

struct LinearTermCacheOccupancy {
    active_slots: Vec<usize>,
    max_allowed_slots: usize,
    remaining_entries: usize,
}

impl LinearTermCacheOccupancy {
    fn new(
        actions: &[Option<CacheAction>],
        cache_slots: usize,
        budget: LinearTermCacheBudget,
    ) -> Self {
        let mut starts = vec![0usize; actions.len()];
        let mut ends = vec![0usize; actions.len() + 1];
        for (start, end) in cache_slot_intervals(actions, cache_slots) {
            starts[start] += 1;
            ends[end + 1] += 1;
        }

        let mut active = 0usize;
        let active_slots = starts
            .into_iter()
            .zip(ends)
            .map(|(starting, ending)| {
                active -= ending;
                active += starting;
                active
            })
            .collect::<Vec<_>>();
        let baseline_max = active_slots.iter().copied().max().unwrap_or(0);

        Self {
            active_slots,
            max_allowed_slots: baseline_max.saturating_add(budget.max_additional_slots),
            remaining_entries: budget.max_entries,
        }
    }

    fn try_reserve(&mut self, start: usize, end: usize) -> bool {
        if self.remaining_entries == 0
            || self.active_slots[start..=end]
                .iter()
                .any(|active| *active >= self.max_allowed_slots)
        {
            return false;
        }

        for active in &mut self.active_slots[start..=end] {
            *active += 1;
        }
        self.remaining_entries -= 1;
        true
    }
}

struct RepeatShape {
    saved_multiplications: usize,
    saved_visits: usize,
    first_occurrence: usize,
    occurrences: Vec<usize>,
}

impl<F: Field> EvaluationPlan<F> {
    fn cache_common_subexpression_actions(
        &self,
        linear_term_budget: LinearTermCacheBudget,
        scalars: &[PlanScalar<F>],
    ) -> (Vec<Option<CacheAction>>, usize) {
        let (actions, cache_slots) = {
            let mut occurrences = vec![];
            collect_plan_occurrences(self, &mut occurrences);
            let mut fingerprint_groups: HashMap<u64, Vec<usize>> = HashMap::new();
            for (index, occurrence) in occurrences.iter().enumerate() {
                fingerprint_groups
                    .entry(occurrence.fingerprint)
                    .or_default()
                    .push(index);
            }
            let mut grouped = vec![false; occurrences.len()];
            let mut shapes = vec![];
            let two = F::ONE.double();

            for index in 0..occurrences.len() {
                if grouped[index] {
                    continue;
                }
                let matching = fingerprint_groups[&occurrences[index].fingerprint]
                    .iter()
                    .copied()
                    .filter(|candidate| {
                        // A fingerprint collision can only add candidates to
                        // this exact structural comparison.
                        !grouped[*candidate]
                            && same_plan(occurrences[index].plan, occurrences[*candidate].plan)
                    })
                    .collect::<Vec<_>>();
                if matching.len() > 1 {
                    for candidate in &matching {
                        grouped[*candidate] = true;
                    }
                    let cost = plan_cost(occurrences[index].plan, two, scalars);
                    shapes.push(RepeatShape {
                        saved_multiplications: (matching.len() - 1) * cost.0,
                        saved_visits: (matching.len() - 1) * cost.1,
                        first_occurrence: index,
                        occurrences: matching,
                    });
                }
            }

            shapes.sort_unstable_by(|lhs, rhs| {
                rhs.saved_multiplications
                    .cmp(&lhs.saved_multiplications)
                    .then_with(|| rhs.saved_visits.cmp(&lhs.saved_visits))
                    .then_with(|| lhs.first_occurrence.cmp(&rhs.first_occurrence))
            });

            let mut actions = vec![None; occurrences.len()];
            let mut covered = vec![false; occurrences.len()];
            let mut cache_slots = 0;
            let mut linear_term_occupancy = None;
            for shape in shapes {
                let matching = shape
                    .occurrences
                    .into_iter()
                    .filter(|candidate| {
                        !covered[*candidate..occurrences[*candidate].end]
                            .iter()
                            .any(|value| *value)
                    })
                    .collect::<Vec<_>>();
                if matching.len() < 2 {
                    continue;
                }

                let cost = plan_cost(occurrences[matching[0]].plan, two, scalars);
                let is_linear_term =
                    matches!(occurrences[matching[0]].plan, EvaluationPlan::LinearTerm(_));
                if is_linear_term {
                    // Cacheable arithmetic shapes have positive multiplication
                    // cost and sort before linear terms, so this occupancy
                    // includes every existing CSE lifetime.
                    let occupancy = linear_term_occupancy.get_or_insert_with(|| {
                        LinearTermCacheOccupancy::new(&actions, cache_slots, linear_term_budget)
                    });
                    if !occupancy.try_reserve(matching[0], *matching.last().unwrap()) {
                        continue;
                    }
                } else if (matching.len() - 1) * cost.0 < MIN_CSE_SAVED_MULTIPLICATIONS {
                    continue;
                } else {
                    debug_assert!(linear_term_occupancy.is_none());
                }

                let slot = cache_slots;
                cache_slots += 1;
                for (index, occurrence) in matching.into_iter().enumerate() {
                    actions[occurrence] = Some(CacheAction {
                        slot,
                        store: index == 0,
                        end: occurrences[occurrence].end,
                    });
                    covered[occurrence..occurrences[occurrence].end].fill(true);
                }
            }
            let cache_slots = reuse_cache_slots(&mut actions, cache_slots);
            (actions, cache_slots)
        };

        (actions, cache_slots)
    }

    #[cfg(test)]
    fn cache_common_subexpressions(
        &mut self,
        linear_term_budget: LinearTermCacheBudget,
        scalars: &[PlanScalar<F>],
    ) -> usize {
        let (actions, cache_slots) =
            self.cache_common_subexpression_actions(linear_term_budget, scalars);
        let mut occurrence = 0;
        apply_cache_actions(self, &actions, &mut occurrence);
        debug_assert_eq!(occurrence, actions.len());
        cache_slots
    }

    fn cache_with_layout(
        &mut self,
        linear_term_budget: LinearTermCacheBudget,
        cached: Option<&EvaluationCacheLayout>,
        retain_layout: bool,
        scalars: &[PlanScalar<F>],
    ) -> (usize, Option<EvaluationCacheLayout>) {
        if let Some(cached) = cached
            && cached.is_valid_for(self)
        {
            apply_cache_events(self, cached);
            return (cached.cache_slots.into(), None);
        }

        let (actions, cache_slots) =
            self.cache_common_subexpression_actions(linear_term_budget, scalars);
        let layout = retain_layout
            .then(|| EvaluationCacheLayout::from_actions(&actions, cache_slots))
            .flatten();
        let mut occurrence = 0;
        apply_cache_actions(self, &actions, &mut occurrence);
        debug_assert_eq!(occurrence, actions.len());
        (cache_slots, layout)
    }
}

fn validate_cache_events<F: Field>(
    plan: &EvaluationPlan<F>,
    layout: &EvaluationCacheLayout,
) -> bool {
    fn validate_factor_body<'a, F: Field>(
        body: &'a FactorBodyPlan<F>,
        layout: &EvaluationCacheLayout,
        event_index: &mut usize,
        occurrence: &mut u32,
        stores: &mut [Option<&'a EvaluationPlan<F>>],
    ) -> bool {
        match body {
            FactorBodyPlan::Sequential(terms) => terms.iter().fold(true, |valid, term| {
                validate_plan(term, layout, event_index, occurrence, stores) & valid
            }),
            FactorBodyPlan::Factored(work) => work.iter().fold(true, |valid, work| {
                let work_valid = match work {
                    FactorBodyWork::Term(term) => {
                        validate_plan(&term.term, layout, event_index, occurrence, stores)
                    }
                    FactorBodyWork::SharedFactor { factor, terms } => {
                        let factor_valid =
                            validate_plan(factor, layout, event_index, occurrence, stores);
                        terms.iter().fold(factor_valid, |valid, term| {
                            validate_plan(&term.term, layout, event_index, occurrence, stores)
                                & valid
                        })
                    }
                };
                work_valid & valid
            }),
        }
    }

    fn validate_plan<'a, F: Field>(
        plan: &'a EvaluationPlan<F>,
        layout: &EvaluationCacheLayout,
        event_index: &mut usize,
        occurrence: &mut u32,
        stores: &mut [Option<&'a EvaluationPlan<F>>],
    ) -> bool {
        let start = *occurrence;
        let event = match layout.events.get(*event_index) {
            Some(event) if event.occurrence < start => return false,
            Some(event) if event.occurrence == start => {
                *event_index += 1;
                Some(event)
            }
            _ => None,
        };
        let Some(next_occurrence) = occurrence.checked_add(1) else {
            return false;
        };
        *occurrence = next_occurrence;
        if let Some(event) = event
            && (event.reserved != 0
                || event.kind > CACHE_EVENT_STORE
                || event.slot >= layout.cache_slots
                || event.end > layout.occurrence_count
                || layout
                    .events
                    .get(*event_index)
                    .is_some_and(|next| next.occurrence < event.end))
        {
            return false;
        }

        let children_valid = match plan {
            EvaluationPlan::Add(lhs, rhs) | EvaluationPlan::Mul(lhs, rhs) => {
                let lhs = validate_plan(lhs, layout, event_index, occurrence, stores);
                let rhs = validate_plan(rhs, layout, event_index, occurrence, stores);
                lhs & rhs
            }
            EvaluationPlan::Square(inner) | EvaluationPlan::Scale(inner, _) => {
                validate_plan(inner, layout, event_index, occurrence, stores)
            }
            EvaluationPlan::Horner { base, .. } => {
                validate_plan(base, layout, event_index, occurrence, stores)
            }
            EvaluationPlan::DistributePowers { work, .. } => {
                work.iter().fold(true, |valid, work| {
                    let work_valid = match work {
                        DistributionWork::Term { term, .. } => {
                            validate_plan(term, layout, event_index, occurrence, stores)
                        }
                        DistributionWork::WeightedSharedFactor { factor, terms } => {
                            let factor =
                                validate_plan(factor, layout, event_index, occurrence, stores);
                            terms.iter().fold(factor, |valid, term| {
                                validate_plan(&term.term, layout, event_index, occurrence, stores)
                                    & valid
                            })
                        }
                        DistributionWork::SelectorFamily { runs, .. } => {
                            runs.iter().rev().fold(true, |valid, run| {
                                validate_factor_body(
                                    &run.bodies,
                                    layout,
                                    event_index,
                                    occurrence,
                                    stores,
                                ) & valid
                            })
                        }
                    };
                    work_valid & valid
                })
            }
            EvaluationPlan::Poly(_)
            | EvaluationPlan::LinearTerm(_)
            | EvaluationPlan::ConstantTerm(_) => true,
            EvaluationPlan::CacheStore { .. } | EvaluationPlan::CacheLoad { .. } => false,
        };

        let event_valid = event.is_none_or(|event| {
            if event.end != *occurrence {
                return false;
            }
            let slot = usize::from(event.slot);
            if event.kind == CACHE_EVENT_STORE {
                stores[slot] = Some(plan);
                true
            } else {
                // The retained layout contains no trusted fingerprint. A load
                // is reusable only when it exactly matches the store in this
                // proof's challenge-bound plan.
                stores[slot].is_some_and(|stored| same_plan(stored, plan))
            }
        });
        children_valid & event_valid
    }

    let mut event_index = 0;
    let mut occurrence = 0;
    let mut stores = vec![None; usize::from(layout.cache_slots)];
    validate_plan(plan, layout, &mut event_index, &mut occurrence, &mut stores)
        && event_index == layout.events.len()
        && occurrence == layout.occurrence_count
}

fn apply_cache_events<F: Field>(plan: &mut EvaluationPlan<F>, layout: &EvaluationCacheLayout) {
    fn apply_factor_body<F: Field>(
        body: &mut FactorBodyPlan<F>,
        layout: &EvaluationCacheLayout,
        event_index: &mut usize,
        occurrence: &mut u32,
    ) {
        match body {
            FactorBodyPlan::Sequential(terms) => {
                for term in terms {
                    apply_plan(term, layout, event_index, occurrence);
                }
            }
            FactorBodyPlan::Factored(work) => {
                for work in work {
                    match work {
                        FactorBodyWork::Term(term) => {
                            apply_plan(&mut term.term, layout, event_index, occurrence)
                        }
                        FactorBodyWork::SharedFactor { factor, terms } => {
                            apply_plan(factor, layout, event_index, occurrence);
                            for term in terms {
                                apply_plan(&mut term.term, layout, event_index, occurrence);
                            }
                        }
                    }
                }
            }
        }
    }

    fn apply_plan<F: Field>(
        plan: &mut EvaluationPlan<F>,
        layout: &EvaluationCacheLayout,
        event_index: &mut usize,
        occurrence: &mut u32,
    ) {
        let event = layout
            .events
            .get(*event_index)
            .filter(|event| event.occurrence == *occurrence)
            .copied();
        if event.is_some() {
            *event_index += 1;
        }
        *occurrence += 1;
        if let Some(event) = event
            && event.kind == CACHE_EVENT_LOAD
        {
            *plan = EvaluationPlan::CacheLoad {
                slot: event.slot.into(),
            };
            *occurrence = event.end;
            return;
        }

        match plan {
            EvaluationPlan::Add(lhs, rhs) | EvaluationPlan::Mul(lhs, rhs) => {
                apply_plan(lhs, layout, event_index, occurrence);
                apply_plan(rhs, layout, event_index, occurrence);
            }
            EvaluationPlan::Square(inner) | EvaluationPlan::Scale(inner, _) => {
                apply_plan(inner, layout, event_index, occurrence)
            }
            EvaluationPlan::Horner { base, .. } => {
                apply_plan(base, layout, event_index, occurrence)
            }
            EvaluationPlan::DistributePowers { work, .. } => {
                for work in work {
                    match work {
                        DistributionWork::Term { term, .. } => {
                            apply_plan(term, layout, event_index, occurrence)
                        }
                        DistributionWork::WeightedSharedFactor { factor, terms } => {
                            apply_plan(factor, layout, event_index, occurrence);
                            for term in terms {
                                apply_plan(&mut term.term, layout, event_index, occurrence);
                            }
                        }
                        DistributionWork::SelectorFamily { runs, .. } => {
                            for run in runs.iter_mut().rev() {
                                apply_factor_body(&mut run.bodies, layout, event_index, occurrence);
                            }
                        }
                    }
                }
            }
            EvaluationPlan::Poly(_)
            | EvaluationPlan::LinearTerm(_)
            | EvaluationPlan::ConstantTerm(_) => {}
            EvaluationPlan::CacheStore { .. } | EvaluationPlan::CacheLoad { .. } => {
                unreachable!("a retained layout is applied to an uncached plan")
            }
        }

        if let Some(event) = event {
            let inner = std::mem::replace(
                plan,
                EvaluationPlan::CacheLoad {
                    slot: event.slot.into(),
                },
            );
            *plan = EvaluationPlan::CacheStore {
                slot: event.slot.into(),
                inner: Box::new(inner),
            };
        }
    }

    let mut event_index = 0;
    let mut occurrence = 0;
    apply_plan(plan, layout, &mut event_index, &mut occurrence);
    debug_assert_eq!(event_index, layout.events.len());
    debug_assert_eq!(occurrence, layout.occurrence_count);
}

fn apply_cache_actions<F: Field>(
    plan: &mut EvaluationPlan<F>,
    actions: &[Option<CacheAction>],
    occurrence: &mut usize,
) {
    let action = actions[*occurrence];
    *occurrence += 1;
    if let Some(action) = action
        && !action.store
    {
        *plan = EvaluationPlan::CacheLoad { slot: action.slot };
        *occurrence = action.end;
        return;
    }

    match plan {
        EvaluationPlan::Add(lhs, rhs) | EvaluationPlan::Mul(lhs, rhs) => {
            apply_cache_actions(lhs, actions, occurrence);
            apply_cache_actions(rhs, actions, occurrence);
        }
        EvaluationPlan::Square(inner) | EvaluationPlan::Scale(inner, _) => {
            apply_cache_actions(inner, actions, occurrence)
        }
        EvaluationPlan::Horner { base, .. } => apply_cache_actions(base, actions, occurrence),
        EvaluationPlan::DistributePowers { work, .. } => {
            for work in work {
                match work {
                    DistributionWork::Term { term, .. } => {
                        apply_cache_actions(term, actions, occurrence)
                    }
                    DistributionWork::WeightedSharedFactor { factor, terms } => {
                        apply_cache_actions(factor, actions, occurrence);
                        for term in terms {
                            apply_cache_actions(&mut term.term, actions, occurrence);
                        }
                    }
                    DistributionWork::SelectorFamily { runs, .. } => {
                        for run in runs.iter_mut().rev() {
                            apply_factor_body_cache_actions(&mut run.bodies, actions, occurrence);
                        }
                    }
                }
            }
        }
        EvaluationPlan::Poly(_)
        | EvaluationPlan::LinearTerm(_)
        | EvaluationPlan::ConstantTerm(_) => {}
        EvaluationPlan::CacheStore { .. } | EvaluationPlan::CacheLoad { .. } => {
            unreachable!("common-subexpression planning runs once")
        }
    }

    if let Some(action) = action {
        let inner = std::mem::replace(plan, EvaluationPlan::CacheLoad { slot: action.slot });
        *plan = EvaluationPlan::CacheStore {
            slot: action.slot,
            inner: Box::new(inner),
        };
    }
}

fn apply_factor_body_cache_actions<F: Field>(
    plan: &mut FactorBodyPlan<F>,
    actions: &[Option<CacheAction>],
    occurrence: &mut usize,
) {
    match plan {
        FactorBodyPlan::Sequential(bodies) => {
            for body in bodies {
                apply_cache_actions(body, actions, occurrence);
            }
        }
        FactorBodyPlan::Factored(work) => {
            for work in work {
                match work {
                    FactorBodyWork::Term(term) => {
                        apply_cache_actions(&mut term.term, actions, occurrence)
                    }
                    FactorBodyWork::SharedFactor { factor, terms } => {
                        apply_cache_actions(factor, actions, occurrence);
                        for term in terms {
                            apply_cache_actions(&mut term.term, actions, occurrence);
                        }
                    }
                }
            }
        }
    }
}

impl<F: Field> FactorBodyPlan<F> {
    fn compile<E: Copy, B: Basis>(
        terms: &[&Ast<E, F, B>],
        base: PowerBase<F>,
        scalars: &mut PlanScalarInterner<F>,
    ) -> Self {
        let groups = factor_groups(terms);
        if groups.is_empty() {
            return Self::Sequential(
                terms
                    .iter()
                    .map(|term| EvaluationPlan::compile(term, scalars))
                    .collect(),
            );
        }

        // Retain each body's original challenge power even when a factor
        // group spans non-consecutive terms.
        let mut powers = base.powers(terms.len());
        powers.reverse();

        let mut claimed = vec![false; terms.len()];
        let mut work = Vec::with_capacity(groups.len() + terms.len());
        for group in groups {
            let terms = group
                .terms
                .into_iter()
                .map(|(position, term)| {
                    claimed[position] = true;
                    WeightedTerm {
                        term: EvaluationPlan::compile(term, scalars),
                        power: scalars.intern(powers[position]),
                    }
                })
                .collect();
            work.push(FactorBodyWork::SharedFactor {
                factor: EvaluationPlan::compile(group.factor, scalars),
                terms,
            });
        }
        for (position, term) in terms.iter().enumerate() {
            if !claimed[position] {
                work.push(FactorBodyWork::Term(WeightedTerm {
                    term: EvaluationPlan::compile(term, scalars),
                    power: scalars.intern(powers[position]),
                }));
            }
        }

        Self::Factored(work)
    }

    fn required_scratch_slots(&self) -> usize {
        match self {
            Self::Sequential(bodies) => {
                1 + bodies
                    .iter()
                    .map(EvaluationPlan::required_scratch_slots)
                    .max()
                    .unwrap_or(0)
            }
            Self::Factored(work) => work
                .iter()
                .map(FactorBodyWork::required_scratch_slots)
                .max()
                .unwrap_or(0),
        }
    }
}

impl<F: Field> FactorBodyWork<F> {
    fn required_scratch_slots(&self) -> usize {
        match self {
            Self::Term(term) => term.term.required_scratch_slots(),
            Self::SharedFactor { factor, terms } => factor.required_scratch_slots().max(
                terms
                    .iter()
                    .map(|term| term.term.required_scratch_slots())
                    .max()
                    .unwrap_or(0),
            ),
        }
    }
}

impl<F: Field> DistributionWork<F> {
    fn required_scratch_slots(&self) -> usize {
        match self {
            Self::Term { term, .. } => term.required_scratch_slots(),
            Self::WeightedSharedFactor { factor, terms } => factor.required_scratch_slots().max(
                terms
                    .iter()
                    .map(|term| term.term.required_scratch_slots())
                    .max()
                    .unwrap_or(0),
            ),
            Self::SelectorFamily { runs, .. } => {
                // The selector product tree occupies at most one more slot
                // than its leaves.
                runs.len()
                    + 1
                    + runs
                        .iter()
                        .map(|run| run.bodies.required_scratch_slots())
                        .max()
                        .unwrap_or(0)
            }
        }
    }
}

impl<'poly, E, F: Field, B: Basis> Evaluator<'poly, E, F, B> {
    fn has_complete_polynomial_tags(&self) -> bool {
        let polynomial_count = self.virtual_poly_count.unwrap_or(self.polys.len());
        self.polynomial_tags
            .as_ref()
            .is_some_and(|tags| tags.len() == polynomial_count)
    }

    fn shape_with_virtual_poly_len(&self, virtual_poly_len: Option<usize>) -> EvaluatorShape {
        let polynomial_lengths = match self.virtual_poly_count {
            Some(count) => {
                let poly_len = virtual_poly_len
                    .expect("a virtual evaluator shape requires a polynomial length");
                vec![poly_len; count].into_boxed_slice()
            }
            None => {
                assert!(
                    virtual_poly_len.is_none(),
                    "a concrete evaluator derives its polynomial lengths"
                );
                self.polys
                    .iter()
                    .map(|polynomial| polynomial.len())
                    .collect()
            }
        };
        EvaluatorShape {
            polynomial_lengths,
            polynomial_tags: self.polynomial_tags.clone().map(Vec::into_boxed_slice),
            compressed_selectors: self
                .compressed_selectors
                .iter()
                .map(|selector| CompressedSelectorShape {
                    query: (&selector.query).into(),
                    combination_len: selector.combination_len,
                    assigned_root: selector.assigned_root,
                    selector: (&selector.selector).into(),
                })
                .collect(),
            reused_compressed_selector_sources: self
                .reused_compressed_selector_sources
                .clone()
                .into_boxed_slice(),
        }
    }

    fn matches_shape(&self, shape: &EvaluatorShape) -> bool {
        let (Some(polynomial_tags), Some(expected_tags)) = (
            self.polynomial_tags.as_deref(),
            shape.polynomial_tags.as_deref(),
        ) else {
            // Untagged shapes are valid only for an evaluator's ephemeral
            // within-call plan; they can never authorize a retained hit.
            return false;
        };
        self.polys.len() == shape.polynomial_lengths.len()
            && self
                .polys
                .iter()
                .zip(shape.polynomial_lengths.iter())
                .all(|(polynomial, expected)| polynomial.len() == *expected)
            && polynomial_tags == expected_tags
            && self.compressed_selectors.len() == shape.compressed_selectors.len()
            && self
                .compressed_selectors
                .iter()
                .zip(shape.compressed_selectors.iter())
                .all(|(selector, expected)| {
                    IndexedLeaf::from(&selector.query) == expected.query
                        && selector.combination_len == expected.combination_len
                        && selector.assigned_root == expected.assigned_root
                        && IndexedLeaf::from(&selector.selector) == expected.selector
                })
            && self.reused_compressed_selector_sources.as_slice()
                == shape.reused_compressed_selector_sources.as_ref()
    }

    /// Returns whether this evaluator can execute a retained quotient plan.
    pub(crate) fn accepts_compiled_plan(&self, plan: &CompiledEvaluationPlan<F, B>) -> bool {
        self.matches_shape(&plan.evaluator_shape)
    }

    fn compile_quotient_plan(
        &self,
        ast: &Ast<E, F, B>,
        poly_len: usize,
        cache_layout: Option<&EvaluationCacheLayout>,
        retain_layout: bool,
    ) -> (CompiledEvaluationPlan<F, B>, Option<EvaluationCacheLayout>)
    where
        E: Copy,
        B: BasisOps,
    {
        let ast = self
            .replace_compressed_selectors(ast)
            .unwrap_or_else(|| ast.clone());
        let mut scalar_interner = PlanScalarInterner::new();
        let mut plan = EvaluationPlan::compile(&ast, &mut scalar_interner);
        let scalar_descriptors = scalar_interner.finish();
        let (cache_slots, layout) = plan.cache_with_layout(
            linear_term_cache_budget::<F, B>(poly_len),
            cache_layout,
            retain_layout,
            &scalar_descriptors,
        );
        let scratch_slots = plan.required_scratch_slots();
        let max_challenge_exponents = max_challenge_exponents(&scalar_descriptors);
        let evaluator_shape =
            self.shape_with_virtual_poly_len(self.virtual_poly_count.map(|_| poly_len));
        (
            CompiledEvaluationPlan {
                plan,
                scalar_descriptors,
                evaluator_shape,
                cache_slots,
                scratch_slots,
                max_challenge_exponents,
                _basis: PhantomData,
            },
            layout,
        )
    }

    /// Registers the given polynomial for use in this evaluation context.
    ///
    /// This API treats each registered polynomial as unique, even if the same polynomial
    /// is added multiple times.
    #[cfg(test)]
    pub(crate) fn register_poly(&mut self, poly: Polynomial<F, B>) -> AstLeaf<E, B> {
        assert!(
            self.virtual_poly_count.is_none(),
            "a virtual evaluator cannot retain polynomial values"
        );
        let index = self.polys.len();
        self.record_polynomial_tag(index, None);
        self.polys.push(Cow::Owned(poly));

        Self::leaf(index)
    }

    /// Registers an owned polynomial with an exact semantic tag.
    pub(crate) fn register_poly_with_tag(
        &mut self,
        poly: Polynomial<F, B>,
        tag: EvaluationPolyTag,
    ) -> AstLeaf<E, B> {
        assert!(
            self.virtual_poly_count.is_none(),
            "a virtual evaluator cannot retain polynomial values"
        );
        let index = self.polys.len();
        self.record_polynomial_tag(index, Some(tag));
        self.polys.push(Cow::Owned(poly));

        Self::leaf(index)
    }

    /// Reserves a tagged owned-polynomial slot whose values will be supplied
    /// before evaluation. This preserves semantic leaf ordering across work
    /// that is deliberately deferred past transcript-adjacent phases.
    pub(crate) fn register_deferred_poly_with_tag(
        &mut self,
        tag: EvaluationPolyTag,
    ) -> AstLeaf<E, B> {
        assert!(
            self.virtual_poly_count.is_none(),
            "a virtual evaluator cannot retain polynomial values"
        );
        let index = self.polys.len();
        self.record_polynomial_tag(index, Some(tag));
        self.polys.push(Cow::Owned(Polynomial {
            values: Vec::new(),
            _marker: PhantomData,
        }));

        Self::leaf(index)
    }

    /// Supplies the values for a slot from
    /// [`Self::register_deferred_poly_with_tag`].
    pub(crate) fn fill_deferred_poly(&mut self, leaf: AstLeaf<E, B>, poly: Polynomial<F, B>) {
        assert!(
            self.virtual_poly_count.is_none(),
            "a virtual evaluator cannot retain polynomial values"
        );
        let slot = self
            .polys
            .get_mut(leaf.index)
            .expect("a deferred polynomial leaf belongs to this evaluator");
        assert!(slot.is_empty(), "a deferred polynomial is filled once");
        *slot = Cow::Owned(poly);
    }

    /// Registers a borrowed polynomial for use in this evaluation context.
    ///
    /// This API treats each registered polynomial as unique, even if the same
    /// polynomial is added multiple times.
    pub(crate) fn register_poly_ref(&mut self, poly: &'poly Polynomial<F, B>) -> AstLeaf<E, B> {
        assert!(
            self.virtual_poly_count.is_none(),
            "a virtual evaluator cannot retain polynomial values"
        );
        let index = self.polys.len();
        self.record_polynomial_tag(index, None);
        self.polys.push(Cow::Borrowed(poly));

        Self::leaf(index)
    }

    /// Registers a borrowed polynomial with an exact semantic tag.
    pub(crate) fn register_poly_ref_with_tag(
        &mut self,
        poly: &'poly Polynomial<F, B>,
        tag: EvaluationPolyTag,
    ) -> AstLeaf<E, B> {
        assert!(
            self.virtual_poly_count.is_none(),
            "a virtual evaluator cannot retain polynomial values"
        );
        let index = self.polys.len();
        self.record_polynomial_tag(index, Some(tag));
        self.polys.push(Cow::Borrowed(poly));

        Self::leaf(index)
    }

    /// Registers a distinct polynomial leaf without retaining its row values.
    ///
    /// This requires an evaluator constructed by [`new_virtual_evaluator`].
    #[cfg(test)]
    pub(crate) fn register_virtual_poly(&mut self) -> AstLeaf<E, B> {
        let index = self
            .virtual_poly_count
            .as_mut()
            .expect("virtual leaves require a virtual evaluator");
        let leaf_index = *index;
        *index += 1;
        self.record_polynomial_tag(leaf_index, None);
        Self::leaf(leaf_index)
    }

    /// Registers a virtual polynomial with an exact semantic tag.
    pub(crate) fn register_virtual_poly_with_tag(
        &mut self,
        tag: EvaluationPolyTag,
    ) -> AstLeaf<E, B> {
        let index = self
            .virtual_poly_count
            .as_mut()
            .expect("virtual leaves require a virtual evaluator");
        let leaf_index = *index;
        *index += 1;
        self.record_polynomial_tag(leaf_index, Some(tag));
        Self::leaf(leaf_index)
    }

    fn leaf(index: usize) -> AstLeaf<E, B> {
        AstLeaf {
            index,
            rotation: Rotation::cur(),
            _evaluator: PhantomData,
        }
    }

    fn record_polynomial_tag(&mut self, index: usize, tag: Option<EvaluationPolyTag>) {
        // Starting tagged registration requires the first polynomial, and
        // every later registration must remain tagged. Untagged registration
        // likewise cannot opt into tags after the first polynomial.
        match (&mut self.polynomial_tags, tag) {
            (None, None) => {}
            (None, Some(tag)) => {
                assert_eq!(index, 0, "tag every polynomial or tag none of them");
                self.polynomial_tags = Some(vec![tag]);
            }
            (Some(tags), Some(tag)) => {
                assert_eq!(tags.len(), index);
                tags.push(tag);
            }
            (Some(_), None) => panic!("tag every polynomial or tag none of them"),
        }
    }

    pub(crate) fn register_compressed_selector(
        &mut self,
        query: AstLeaf<E, B>,
        combination_len: usize,
        assigned_root: usize,
        selector: AstLeaf<E, B>,
    ) {
        if query.index == selector.index
            && !self
                .reused_compressed_selector_sources
                .contains(&query.index)
        {
            self.reused_compressed_selector_sources.push(query.index);
        }
        self.compressed_selectors.push(CompressedSelectorLeaf {
            query,
            combination_len,
            assigned_root,
            selector,
        });
    }

    // Returns `None` when this subtree needs no replacement, so its parent can
    // retain the existing `Arc` instead of rebuilding it.
    fn replace_compressed_selectors(&self, ast: &Ast<E, F, B>) -> Option<Ast<E, F, B>>
    where
        E: Copy,
    {
        if let Some((query, combination_len, assigned_root)) = compressed_selector(ast, -F::ONE) {
            if let Some(selector) = self.compressed_selectors.iter().find(|selector| {
                selector.query == *query
                    && selector.combination_len == combination_len
                    && selector.assigned_root == assigned_root
            }) {
                return Some(Ast::Poly(selector.selector));
            }
        }

        match ast {
            Ast::Poly(query) => {
                // A selector family may reuse its source polynomial as the
                // first precomputed selector. Reaching that source outside a
                // recognized selector subtree would evaluate the wrong
                // polynomial, so fail closed if the matcher ever misses one.
                assert!(
                    !self
                        .reused_compressed_selector_sources
                        .contains(&query.index),
                    "reused compressed-selector source was not replaced"
                );
                None
            }
            Ast::LinearTerm(_)
            | Ast::LinearChallengeTerm { .. }
            | Ast::ConstantTerm(_)
            | Ast::ChallengeTerm(_) => None,
            Ast::Add(lhs, rhs) => {
                let replaced_lhs = self.replace_compressed_selectors(lhs);
                let replaced_rhs = self.replace_compressed_selectors(rhs);
                if replaced_lhs.is_none() && replaced_rhs.is_none() {
                    None
                } else {
                    Some(Ast::Add(
                        replaced_lhs
                            .map(Arc::new)
                            .unwrap_or_else(|| Arc::clone(lhs)),
                        replaced_rhs
                            .map(Arc::new)
                            .unwrap_or_else(|| Arc::clone(rhs)),
                    ))
                }
            }
            Ast::Mul(AstMul(lhs, rhs)) => {
                let replaced_lhs = self.replace_compressed_selectors(lhs);
                let replaced_rhs = self.replace_compressed_selectors(rhs);
                if replaced_lhs.is_none() && replaced_rhs.is_none() {
                    None
                } else {
                    Some(Ast::Mul(AstMul(
                        replaced_lhs
                            .map(Arc::new)
                            .unwrap_or_else(|| Arc::clone(lhs)),
                        replaced_rhs
                            .map(Arc::new)
                            .unwrap_or_else(|| Arc::clone(rhs)),
                    )))
                }
            }
            Ast::Scale(inner, scalar) => self
                .replace_compressed_selectors(inner)
                .map(|inner| Ast::Scale(Arc::new(inner), *scalar)),
            Ast::DistributePowers(terms, base) => {
                let mut replaced_terms = None;
                for (index, term) in terms.iter().enumerate() {
                    match (
                        replaced_terms.as_mut(),
                        self.replace_compressed_selectors(term),
                    ) {
                        (None, None) => {}
                        (None, Some(replacement)) => {
                            let mut output = Vec::with_capacity(terms.len());
                            output.extend_from_slice(&terms[..index]);
                            output.push(replacement);
                            replaced_terms = Some(output);
                        }
                        (Some(output), None) => output.push(term.clone()),
                        (Some(output), Some(replacement)) => output.push(replacement),
                    }
                }
                replaced_terms.map(|terms| Ast::DistributePowers(Arc::new(terms), *base))
            }
            Ast::DistributeChallengePowers(terms, challenge) => {
                let mut replaced_terms = None;
                for (index, term) in terms.iter().enumerate() {
                    match (
                        replaced_terms.as_mut(),
                        self.replace_compressed_selectors(term),
                    ) {
                        (None, None) => {}
                        (None, Some(replacement)) => {
                            let mut output = Vec::with_capacity(terms.len());
                            output.extend_from_slice(&terms[..index]);
                            output.push(replacement);
                            replaced_terms = Some(output);
                        }
                        (Some(output), None) => output.push(term.clone()),
                        (Some(output), Some(replacement)) => output.push(replacement),
                    }
                }
                replaced_terms
                    .map(|terms| Ast::DistributeChallengePowers(Arc::new(terms), *challenge))
            }
        }
    }

    /// Evaluates the given polynomial operation against this context.
    pub(crate) fn evaluate(
        &self,
        ast: &Ast<E, F, B>,
        domain: &EvaluationDomain<F>,
    ) -> Polynomial<F, B>
    where
        E: Copy + Send + Sync,
        F: WithSmallOrderMulGroup<3>,
        B: BasisOps,
    {
        self.evaluate_inner(
            Some(ast),
            domain,
            None,
            false,
            None,
            false,
            EvaluationChallenges {
                theta: F::ZERO,
                beta: F::ZERO,
                gamma: F::ZERO,
                y: F::ZERO,
            },
        )
        .0
    }

    #[cfg(test)]
    fn evaluate_with_cache_layout(
        &self,
        ast: &Ast<E, F, B>,
        domain: &EvaluationDomain<F>,
        cache_layout: Option<&EvaluationCacheLayout>,
    ) -> (Polynomial<F, B>, Option<EvaluationCacheLayout>)
    where
        E: Copy + Send + Sync,
        F: WithSmallOrderMulGroup<3>,
        B: BasisOps,
    {
        let (polynomial, layout, _) = self.evaluate_inner(
            Some(ast),
            domain,
            cache_layout,
            true,
            None,
            false,
            EvaluationChallenges {
                theta: F::ZERO,
                beta: F::ZERO,
                gamma: F::ZERO,
                y: F::ZERO,
            },
        );
        (polynomial, layout)
    }

    pub(crate) fn evaluate_quotient_with_compiled_plan<I>(
        &self,
        expressions: I,
        domain: &EvaluationDomain<F>,
        compiled_plan: Option<&CompiledEvaluationPlan<F, B>>,
        challenges: EvaluationChallenges<F>,
    ) -> (Polynomial<F, B>, Option<CompiledEvaluationPlan<F, B>>)
    where
        E: Copy + Send + Sync,
        F: WithSmallOrderMulGroup<3>,
        B: BasisOps,
        I: IntoIterator<Item = Ast<E, F, B>>,
    {
        let compiled_plan = compiled_plan.filter(|plan| self.matches_shape(&plan.evaluator_shape));
        if let Some(compiled_plan) = compiled_plan {
            return (
                self.evaluate_inner(
                    None,
                    domain,
                    None,
                    false,
                    Some(compiled_plan),
                    false,
                    challenges,
                )
                .0,
                None,
            );
        }

        let ast = Ast::distribute_challenge_powers(expressions, EvaluationChallenge::Y);
        let (polynomial, _, plan) = self.evaluate_inner(
            Some(&ast),
            domain,
            None,
            false,
            None,
            self.has_complete_polynomial_tags(),
            challenges,
        );
        (polynomial, plan)
    }

    /// Plans a cache layout without evaluating any polynomial rows.
    ///
    /// This requires an evaluator constructed by [`new_virtual_evaluator`].
    #[cfg(test)]
    fn prepare_cache_layout(
        &self,
        ast: &Ast<E, F, B>,
        poly_len: usize,
    ) -> Option<EvaluationCacheLayout>
    where
        E: Copy,
        B: BasisOps,
    {
        assert!(
            self.virtual_poly_count.is_some(),
            "topology-only planning requires a virtual evaluator"
        );
        self.compile_quotient_plan(ast, poly_len, None, true).1
    }

    /// Compiles a challenge-independent quotient plan without evaluating
    /// polynomial rows.
    ///
    /// This requires an evaluator constructed by [`new_virtual_evaluator`].
    pub(crate) fn prepare_compiled_quotient_plan(
        &self,
        ast: &Ast<E, F, B>,
        poly_len: usize,
    ) -> CompiledEvaluationPlan<F, B>
    where
        E: Copy,
        B: BasisOps,
    {
        assert!(
            self.virtual_poly_count.is_some(),
            "topology-only planning requires a virtual evaluator"
        );
        assert!(
            self.has_complete_polynomial_tags(),
            "a retained quotient plan requires one semantic tag per polynomial"
        );
        self.compile_quotient_plan(ast, poly_len, None, false).0
    }

    fn evaluate_inner(
        &self,
        ast: Option<&Ast<E, F, B>>,
        domain: &EvaluationDomain<F>,
        cache_layout: Option<&EvaluationCacheLayout>,
        retain_layout: bool,
        compiled_plan: Option<&CompiledEvaluationPlan<F, B>>,
        retain_compiled_plan: bool,
        challenges: EvaluationChallenges<F>,
    ) -> (
        Polynomial<F, B>,
        Option<EvaluationCacheLayout>,
        Option<CompiledEvaluationPlan<F, B>>,
    )
    where
        E: Copy + Send + Sync,
        F: WithSmallOrderMulGroup<3>,
        B: BasisOps,
    {
        assert!(
            self.virtual_poly_count.is_none(),
            "a virtual evaluator cannot evaluate polynomial rows"
        );
        // We're working in a single basis, so all polynomials are the same length.
        let poly_len = self.polys.first().unwrap().len();
        let (chunk_size, _num_chunks) = get_chunk_params(poly_len);

        struct AstContext<'a, F: Field, B: Basis> {
            domain: &'a EvaluationDomain<F>,
            chunk_size: usize,
            chunk_index: usize,
            polys: &'a [Cow<'a, Polynomial<F, B>>],
            scalars: &'a BoundPlanScalars<F>,
        }

        fn recurse_weighted_terms<F: WithSmallOrderMulGroup<3>, B: BasisOps>(
            terms: &[WeightedTerm<F>],
            ctx: &AstContext<'_, F, B>,
            output: &mut [F],
            cache: &mut [F],
            scratch: &mut [F],
            fold: &mut ReusablePowerFold<F>,
        ) {
            fold.reset();
            for term in terms {
                recurse_into(&term.term, ctx, fold.terms(), cache, scratch);
                fold.accumulate(ctx.scalars.get(term.power));
            }
            fold.finish_into(output);
        }

        // `scratch` is preallocated per-chunk workspace whose size is derived
        // from the compiled plan.
        fn recurse_factor_body<F: WithSmallOrderMulGroup<3>, B: BasisOps>(
            plan: &FactorBodyPlan<F>,
            base: F,
            ctx: &AstContext<'_, F, B>,
            output: &mut [F],
            cache: &mut [F],
            scratch: &mut [F],
        ) {
            match plan {
                FactorBodyPlan::Sequential(bodies) => {
                    let (first, remaining) = bodies
                        .split_first()
                        .expect("a compiled factor body has at least one term");
                    recurse_into(first, ctx, output, cache, scratch);

                    if !remaining.is_empty() {
                        let (term_values, recurse_scratch) = scratch.split_at_mut(output.len());
                        for body in remaining {
                            recurse_into(body, ctx, term_values, cache, recurse_scratch);
                            for (group, term) in output.iter_mut().zip(term_values.iter()) {
                                *group *= base;
                                *group += term;
                            }
                        }
                    }
                }
                FactorBodyPlan::Factored(work) => {
                    let mut fold = PowerFold::new(output);
                    let mut reusable_weighted_fold = None;
                    for work in work {
                        match work {
                            FactorBodyWork::Term(term) => {
                                recurse_into(&term.term, ctx, fold.terms(), cache, scratch);
                                fold.accumulate(ctx.scalars.get(term.power));
                            }
                            FactorBodyWork::SharedFactor { factor, terms } => {
                                recurse_into(factor, ctx, fold.factors(), cache, scratch);
                                {
                                    let body_values = fold.terms();
                                    let reusable_weighted_fold = reusable_weighted_fold
                                        .get_or_insert_with(|| {
                                            ReusablePowerFold::new(body_values.len())
                                        });
                                    recurse_weighted_terms(
                                        terms,
                                        ctx,
                                        body_values,
                                        cache,
                                        scratch,
                                        reusable_weighted_fold,
                                    );
                                }
                                fold.accumulate_products();
                            }
                        }
                    }
                    fold.finish();
                }
            }
        }

        fn accumulate_selector_family<F: WithSmallOrderMulGroup<3>, B: BasisOps>(
            query: &IndexedLeaf,
            runs: &[SelectorFamilyRun<F>],
            base: ScalarId<F>,
            ctx: &AstContext<'_, F, B>,
            scratch: &mut [F],
            cache: &mut [F],
            fold: &mut PowerFold<'_, F>,
        ) {
            let chunk_len = fold.terms().len();
            let base = ctx.scalars.get(base);
            let tree_slots = runs.len() + 1;
            let (tree, body_scratch) = scratch.split_at_mut(tree_slots * chunk_len);

            // Preserve the compiled cache traversal while placing each
            // weighted body in selector-root order.
            for run_index in (0..runs.len()).rev() {
                let run = &runs[run_index];
                let body_start = run_index * chunk_len;
                let body = &mut tree[body_start..body_start + chunk_len];
                recurse_factor_body(&run.bodies, base, ctx, body, cache, body_scratch);
                let power = ctx.scalars.get(run.power);
                for body in body.iter_mut() {
                    *body *= power;
                }
            }

            let query = leaf_chunk(query, ctx, chunk_len);
            let paired_leaves = runs.len() / 2;
            for pair in 0..paired_leaves {
                let left_slot = pair * 2;
                let right_slot = left_slot + 1;
                let left_root = field_from_small_usize::<F>(left_slot + 1);
                let right_root = field_from_small_usize::<F>(right_slot + 1);
                let left_start = left_slot * chunk_len;
                let right_start = right_slot * chunk_len;
                let (left, right) = tree.split_at_mut(right_start);
                let left = &mut left[left_start..left_start + chunk_len];
                let right = &mut right[..chunk_len];
                for ((product, sum), query) in
                    left.iter_mut().zip(right.iter_mut()).zip(query.iter())
                {
                    let left_sum = *product;
                    let right_sum = *sum;
                    let left_factor = left_root - query;
                    let right_factor = right_root - query;
                    *product = left_factor * right_factor;
                    *sum = left_sum * right_factor + right_sum * left_factor;
                }
            }

            let mut active_nodes = paired_leaves;
            if runs.len() % 2 == 1 {
                let leaf_slot = runs.len() - 1;
                let sum_slot = runs.len();
                let leaf_start = leaf_slot * chunk_len;
                let sum_start = sum_slot * chunk_len;
                let (leaf, sum) = tree.split_at_mut(sum_start);
                let leaf = &mut leaf[leaf_start..leaf_start + chunk_len];
                let sum = &mut sum[..chunk_len];
                let root = field_from_small_usize::<F>(runs.len());
                for ((product, sum), query) in leaf.iter_mut().zip(sum.iter_mut()).zip(query.iter())
                {
                    *sum = *product;
                    *product = root - query;
                }
                active_nodes += 1;
            }

            while active_nodes > 1 {
                if active_nodes == 2 {
                    for row in 0..chunk_len {
                        let left_product = tree[row];
                        let left_sum = tree[chunk_len + row];
                        let right_product = tree[2 * chunk_len + row];
                        let right_sum = tree[3 * chunk_len + row];
                        tree[chunk_len + row] = left_sum * right_product + right_sum * left_product;
                    }
                    break;
                }

                let paired_nodes = active_nodes / 2;
                for pair in 0..paired_nodes {
                    let left_start = pair * 4 * chunk_len;
                    let right_start = left_start + 2 * chunk_len;
                    let output_start = pair * 2 * chunk_len;
                    for row in 0..chunk_len {
                        let left_product = tree[left_start + row];
                        let left_sum = tree[left_start + chunk_len + row];
                        let right_product = tree[right_start + row];
                        let right_sum = tree[right_start + chunk_len + row];
                        tree[output_start + row] = left_product * right_product;
                        tree[output_start + chunk_len + row] =
                            left_sum * right_product + right_sum * left_product;
                    }
                }

                let mut next_nodes = paired_nodes;
                if active_nodes % 2 == 1 {
                    let input_start = (active_nodes - 1) * 2 * chunk_len;
                    let output_start = paired_nodes * 2 * chunk_len;
                    tree.copy_within(input_start..input_start + 2 * chunk_len, output_start);
                    next_nodes += 1;
                }
                active_nodes = next_nodes;
            }

            let terms = fold.terms();
            let sum = &tree[chunk_len..2 * chunk_len];
            for ((term, sum), query) in terms.iter_mut().zip(sum.iter()).zip(query.iter()) {
                *term = *sum * query;
            }
            fold.accumulate_addends();
        }

        fn leaf_chunk<'a, F: WithSmallOrderMulGroup<3>, B: BasisOps>(
            leaf: &IndexedLeaf,
            ctx: &'a AstContext<'_, F, B>,
            chunk_len: usize,
        ) -> RotatedChunk<'a, F> {
            let (first, second) = B::rotated_chunk(
                ctx.domain,
                ctx.chunk_size,
                ctx.chunk_index,
                &ctx.polys[leaf.index],
                leaf.rotation,
                chunk_len,
            );
            RotatedChunk { first, second }
        }

        fn add_scaled<F: Field>(sums: &mut [F], values: &[F], scalar: F, kind: ScaleKind) {
            debug_assert_eq!(sums.len(), values.len());
            match kind {
                ScaleKind::MinusOne => {
                    for (sum, value) in sums.iter_mut().zip(values) {
                        *sum -= value;
                    }
                }
                ScaleKind::One => {
                    for (sum, value) in sums.iter_mut().zip(values) {
                        *sum += value;
                    }
                }
                ScaleKind::Two => {
                    for (sum, value) in sums.iter_mut().zip(values) {
                        *sum += value.double();
                    }
                }
                ScaleKind::Other => {
                    let mut sum_blocks = sums.chunks_exact_mut(4);
                    let mut value_blocks = values.chunks_exact(4);
                    for (sums, values) in (&mut sum_blocks).zip(&mut value_blocks) {
                        // Expose four independent multiplications before their
                        // dependent additions.
                        let product_0 = values[0] * scalar;
                        let product_1 = values[1] * scalar;
                        let product_2 = values[2] * scalar;
                        let product_3 = values[3] * scalar;
                        sums[0] += product_0;
                        sums[1] += product_1;
                        sums[2] += product_2;
                        sums[3] += product_3;
                    }
                    for (sum, value) in sum_blocks
                        .into_remainder()
                        .iter_mut()
                        .zip(value_blocks.remainder())
                    {
                        *sum += *value * scalar;
                    }
                }
            }
        }

        fn scale_value<F: Field>(value: F, scalar: F, kind: ScaleKind) -> F {
            match kind {
                ScaleKind::MinusOne => -value,
                ScaleKind::One => value,
                ScaleKind::Two => value.double(),
                ScaleKind::Other => value * scalar,
            }
        }

        fn recurse_into<F: WithSmallOrderMulGroup<3>, B: BasisOps>(
            plan: &EvaluationPlan<F>,
            ctx: &AstContext<'_, F, B>,
            output: &mut [F],
            cache: &mut [F],
            scratch: &mut [F],
        ) {
            match plan {
                EvaluationPlan::Poly(leaf) => B::copy_rotated_chunk(
                    ctx.domain,
                    ctx.chunk_size,
                    ctx.chunk_index,
                    &ctx.polys[leaf.index],
                    leaf.rotation,
                    output,
                ),
                EvaluationPlan::Add(a, b) => {
                    if let EvaluationPlan::ConstantTerm(scalar) = a.as_ref() {
                        // A constant leaf has no cache event, so evaluating its
                        // sibling directly preserves the plan's cache order.
                        let scalar = ctx.scalars.get(*scalar);
                        if let EvaluationPlan::Scale(scaled_rhs, factor) = b.as_ref() {
                            let (factor, kind) = ctx.scalars.scale(*factor);
                            if let EvaluationPlan::ConstantTerm(rhs) = scaled_rhs.as_ref() {
                                let rhs = scale_value(ctx.scalars.get(*rhs), factor, kind);
                                B::fill_constant(ctx.chunk_index, scalar + rhs, output);
                                return;
                            }
                            recurse_into(scaled_rhs, ctx, output, cache, scratch);
                            match kind {
                                ScaleKind::MinusOne => B::combine_constant(
                                    ctx.chunk_index,
                                    scalar,
                                    output,
                                    |value, constant| constant - value,
                                ),
                                ScaleKind::One => B::combine_constant(
                                    ctx.chunk_index,
                                    scalar,
                                    output,
                                    |value, constant| constant + value,
                                ),
                                ScaleKind::Two => B::combine_constant(
                                    ctx.chunk_index,
                                    scalar,
                                    output,
                                    |value, constant| constant + value.double(),
                                ),
                                ScaleKind::Other => B::combine_constant(
                                    ctx.chunk_index,
                                    scalar,
                                    output,
                                    |value, constant| constant + value * factor,
                                ),
                            }
                            return;
                        }

                        recurse_into(b, ctx, output, cache, scratch);
                        B::combine_constant(ctx.chunk_index, scalar, output, |value, constant| {
                            value + constant
                        });
                        return;
                    }

                    recurse_into(a, ctx, output, cache, scratch);
                    if let EvaluationPlan::Scale(scaled_rhs, scalar) = b.as_ref() {
                        let (scalar, kind) = ctx.scalars.scale(*scalar);
                        if let EvaluationPlan::ConstantTerm(constant) = scaled_rhs.as_ref() {
                            let constant = scale_value(ctx.scalars.get(*constant), scalar, kind);
                            B::combine_constant(
                                ctx.chunk_index,
                                constant,
                                output,
                                |value, constant| value + constant,
                            );
                        } else if let EvaluationPlan::Poly(leaf) = scaled_rhs.as_ref() {
                            let chunk = leaf_chunk(leaf, ctx, output.len());
                            let (first, second) = chunk.into_slices();
                            let (first_output, second_output) = output.split_at_mut(first.len());
                            add_scaled(first_output, first, scalar, kind);
                            if !second.is_empty() {
                                add_scaled(second_output, second, scalar, kind);
                            }
                        } else {
                            let (rhs_values, rhs_scratch) = scratch.split_at_mut(output.len());
                            recurse_into(scaled_rhs, ctx, rhs_values, cache, rhs_scratch);
                            add_scaled(output, rhs_values, scalar, kind);
                        }
                        return;
                    }

                    if let EvaluationPlan::ConstantTerm(scalar) = b.as_ref() {
                        B::combine_constant(
                            ctx.chunk_index,
                            ctx.scalars.get(*scalar),
                            output,
                            |value, constant| value + constant,
                        );
                        return;
                    }

                    if let EvaluationPlan::Poly(leaf) = b.as_ref() {
                        let chunk = leaf_chunk(leaf, ctx, output.len());
                        for (lhs, rhs) in output.iter_mut().zip(chunk.iter()) {
                            *lhs += *rhs;
                        }
                        return;
                    }

                    let (rhs_values, rhs_scratch) = scratch.split_at_mut(output.len());
                    recurse_into(b, ctx, rhs_values, cache, rhs_scratch);
                    for (lhs, rhs) in output.iter_mut().zip(rhs_values.iter()) {
                        *lhs += *rhs;
                    }
                }
                EvaluationPlan::Mul(a, b) => {
                    if let (EvaluationPlan::ConstantTerm(lhs), EvaluationPlan::ConstantTerm(rhs)) =
                        (a.as_ref(), b.as_ref())
                    {
                        B::fill_constant(
                            ctx.chunk_index,
                            ctx.scalars.get(*lhs) * ctx.scalars.get(*rhs),
                            output,
                        );
                        return;
                    }

                    // Preserve the multiplication shape while avoiding a
                    // constant vector for every scalar value.
                    if let EvaluationPlan::ConstantTerm(scalar) = a.as_ref() {
                        let (scalar, kind) = ctx.scalars.scale(*scalar);
                        recurse_scaled_into(b, scalar, kind, ctx, output, cache, scratch);
                        return;
                    }
                    if let EvaluationPlan::ConstantTerm(scalar) = b.as_ref() {
                        let (scalar, kind) = ctx.scalars.scale(*scalar);
                        recurse_scaled_into(a, scalar, kind, ctx, output, cache, scratch);
                        return;
                    }

                    if let (EvaluationPlan::Poly(lhs), EvaluationPlan::Poly(rhs)) =
                        (a.as_ref(), b.as_ref())
                    {
                        let lhs = leaf_chunk(lhs, ctx, output.len());
                        let rhs = leaf_chunk(rhs, ctx, output.len());
                        for ((output, lhs), rhs) in
                            output.iter_mut().zip(lhs.iter()).zip(rhs.iter())
                        {
                            *output = *lhs * rhs;
                        }
                        return;
                    }
                    if let EvaluationPlan::Poly(rhs) = b.as_ref() {
                        recurse_into(a, ctx, output, cache, scratch);
                        let rhs = leaf_chunk(rhs, ctx, output.len());
                        for (lhs, rhs) in output.iter_mut().zip(rhs.iter()) {
                            *lhs *= rhs;
                        }
                        return;
                    }
                    if let EvaluationPlan::Poly(lhs) = a.as_ref() {
                        recurse_into(b, ctx, output, cache, scratch);
                        let lhs = leaf_chunk(lhs, ctx, output.len());
                        for (rhs, lhs) in output.iter_mut().zip(lhs.iter()) {
                            *rhs *= lhs;
                        }
                        return;
                    }

                    recurse_into(a, ctx, output, cache, scratch);
                    let (rhs, rhs_scratch) = scratch.split_at_mut(output.len());
                    recurse_into(b, ctx, rhs, cache, rhs_scratch);
                    for (lhs, rhs) in output.iter_mut().zip(rhs.iter()) {
                        *lhs *= *rhs;
                    }
                }
                EvaluationPlan::Square(inner) => {
                    if let EvaluationPlan::Poly(leaf) = inner.as_ref() {
                        let chunk = leaf_chunk(leaf, ctx, output.len());
                        for (output, value) in output.iter_mut().zip(chunk.iter()) {
                            *output = value.square();
                        }
                        return;
                    }
                    recurse_into(inner, ctx, output, cache, scratch);
                    for value in output.iter_mut() {
                        *value = value.square();
                    }
                }
                EvaluationPlan::Scale(a, scalar) => {
                    let (scalar, kind) = ctx.scalars.scale(*scalar);
                    recurse_scaled_into(a, scalar, kind, ctx, output, cache, scratch);
                }
                EvaluationPlan::Horner { base, coefficients } => {
                    let (highest, remaining) = coefficients
                        .split_last()
                        .expect("a Horner plan has at least four coefficients");
                    B::copy_rotated_chunk(
                        ctx.domain,
                        ctx.chunk_size,
                        ctx.chunk_index,
                        &ctx.polys[highest.index],
                        highest.rotation,
                        output,
                    );

                    let (base_values, scratch) = scratch.split_at_mut(output.len());
                    recurse_into(base, ctx, base_values, cache, scratch);
                    for coefficient in remaining.iter().rev() {
                        for (value, base) in output.iter_mut().zip(base_values.iter()) {
                            *value *= base;
                        }
                        let coefficient = leaf_chunk(coefficient, ctx, output.len());
                        for (value, coefficient) in output.iter_mut().zip(coefficient.iter()) {
                            *value += coefficient;
                        }
                    }
                }
                EvaluationPlan::DistributePowers { work, base } => {
                    let mut fold = PowerFold::new(output);
                    let mut reusable_weighted_fold = None;
                    for work in work {
                        match work {
                            DistributionWork::Term { term, power } => {
                                recurse_into(term, ctx, fold.terms(), cache, scratch);
                                fold.accumulate(ctx.scalars.get(*power));
                            }
                            DistributionWork::WeightedSharedFactor { factor, terms } => {
                                recurse_into(factor, ctx, fold.factors(), cache, scratch);
                                {
                                    let body_values = fold.terms();
                                    let reusable_weighted_fold = reusable_weighted_fold
                                        .get_or_insert_with(|| {
                                            ReusablePowerFold::new(body_values.len())
                                        });
                                    recurse_weighted_terms(
                                        terms,
                                        ctx,
                                        body_values,
                                        cache,
                                        scratch,
                                        reusable_weighted_fold,
                                    );
                                }
                                fold.accumulate_products();
                            }
                            DistributionWork::SelectorFamily { query, runs } => {
                                accumulate_selector_family(
                                    query, runs, *base, ctx, scratch, cache, &mut fold,
                                );
                            }
                        }
                    }

                    fold.finish();
                }
                EvaluationPlan::CacheStore { slot, inner } => {
                    recurse_into(inner, ctx, output, cache, scratch);
                    let start = slot * output.len();
                    cache[start..start + output.len()].copy_from_slice(output);
                }
                EvaluationPlan::CacheLoad { slot } => {
                    let start = slot * output.len();
                    output.copy_from_slice(&cache[start..start + output.len()]);
                }
                EvaluationPlan::LinearTerm(scalar) => B::fill_linear(
                    ctx.domain,
                    ctx.chunk_size,
                    ctx.chunk_index,
                    ctx.scalars.get(*scalar),
                    output,
                ),
                EvaluationPlan::ConstantTerm(scalar) => {
                    B::fill_constant(ctx.chunk_index, ctx.scalars.get(*scalar), output)
                }
            }
        }

        fn recurse_scaled_into<F: WithSmallOrderMulGroup<3>, B: BasisOps>(
            plan: &EvaluationPlan<F>,
            scalar: F,
            kind: ScaleKind,
            ctx: &AstContext<'_, F, B>,
            output: &mut [F],
            cache: &mut [F],
            scratch: &mut [F],
        ) {
            if let EvaluationPlan::Poly(leaf) = plan {
                let chunk = leaf_chunk(leaf, ctx, output.len());
                match kind {
                    ScaleKind::MinusOne => {
                        for (output, value) in output.iter_mut().zip(chunk.iter()) {
                            *output = -*value;
                        }
                    }
                    ScaleKind::One => {
                        for (output, value) in output.iter_mut().zip(chunk.iter()) {
                            *output = *value;
                        }
                    }
                    ScaleKind::Two => {
                        for (output, value) in output.iter_mut().zip(chunk.iter()) {
                            *output = value.double();
                        }
                    }
                    ScaleKind::Other => {
                        for (output, value) in output.iter_mut().zip(chunk.iter()) {
                            *output = *value * scalar;
                        }
                    }
                }
                return;
            }

            recurse_into(plan, ctx, output, cache, scratch);
            match kind {
                ScaleKind::MinusOne => {
                    for value in output.iter_mut() {
                        *value = -*value;
                    }
                }
                ScaleKind::One => {}
                ScaleKind::Two => {
                    for value in output.iter_mut() {
                        *value = value.double();
                    }
                }
                ScaleKind::Other => {
                    for value in output.iter_mut() {
                        *value *= scalar;
                    }
                }
            }
        }

        // Apply `ast` to each chunk in parallel, writing the result into an output
        // polynomial.
        let mut owned_plan = None;
        let mut prepared_layout = None;
        let (plan, scalar_descriptors, cache_slots, scratch_slots, max_challenge_exponents) =
            match compiled_plan {
                Some(compiled_plan) => (
                    &compiled_plan.plan,
                    compiled_plan.scalar_descriptors.as_ref(),
                    compiled_plan.cache_slots,
                    compiled_plan.scratch_slots,
                    compiled_plan.max_challenge_exponents,
                ),
                None => {
                    let ast = ast.expect("an uncached evaluation has an AST");
                    let (plan, layout) =
                        self.compile_quotient_plan(ast, poly_len, cache_layout, retain_layout);
                    prepared_layout = layout;
                    owned_plan = Some(plan);
                    let owned_plan = owned_plan.as_ref().unwrap();
                    (
                        &owned_plan.plan,
                        owned_plan.scalar_descriptors.as_ref(),
                        owned_plan.cache_slots,
                        owned_plan.scratch_slots,
                        owned_plan.max_challenge_exponents,
                    )
                }
            };
        let mut result = B::empty_poly(domain);
        let bound_scalars =
            BoundPlanScalars::new(scalar_descriptors, challenges, max_challenge_exponents);
        multicore::scope(|scope| {
            let bound_scalars = &bound_scalars;
            for (chunk_index, out) in result.chunks_mut(chunk_size).enumerate() {
                let plan = &plan;
                scope.spawn(move |_| {
                    let ctx = AstContext {
                        domain,
                        chunk_size,
                        chunk_index,
                        polys: &self.polys,
                        scalars: bound_scalars,
                    };
                    let mut storage = vec![F::ZERO; (cache_slots + scratch_slots) * out.len()];
                    let (cache, scratch) = storage.split_at_mut(cache_slots * out.len());
                    recurse_into(plan, &ctx, out, cache, scratch);
                });
            }
        });
        let prepared_plan = retain_compiled_plan.then(|| owned_plan.take()).flatten();
        (result, prepared_layout, prepared_plan)
    }
}

/// Struct representing the [`Ast::Mul`] case.
///
/// This struct exists to make the internals of this case private so that we don't
/// accidentally construct this case directly, because it can only be implemented for the
/// [`ExtendedLagrangeCoeff`] basis.
#[derive(Clone)]
pub(crate) struct AstMul<E, F: Field, B: Basis>(Arc<Ast<E, F, B>>, Arc<Ast<E, F, B>>);

impl<E, F: Field, B: Basis> fmt::Debug for AstMul<E, F, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("AstMul")
            .field(&self.0)
            .field(&self.1)
            .finish()
    }
}

/// A polynomial operation backed by an [`Evaluator`].
#[derive(Clone)]
pub(crate) enum Ast<E, F: Field, B: Basis> {
    Poly(AstLeaf<E, B>),
    Add(Arc<Ast<E, F, B>>, Arc<Ast<E, F, B>>),
    Mul(AstMul<E, F, B>),
    Scale(Arc<Ast<E, F, B>>, F),
    /// Represents a linear combination of a vector of nodes and the powers of a
    /// field element, where the nodes are ordered from highest to lowest degree
    /// terms.
    #[allow(dead_code)]
    DistributePowers(Arc<Vec<Ast<E, F, B>>>, F),
    /// As [`Ast::DistributePowers`], with a proof challenge as the base.
    DistributeChallengePowers(Arc<Vec<Ast<E, F, B>>>, EvaluationChallenge),
    /// The degree-1 term of a polynomial.
    ///
    /// The field element is the coefficient of the term in the standard basis, not the
    /// coefficient basis.
    #[allow(dead_code)]
    LinearTerm(F),
    /// A degree-1 term scaled by a proof challenge and a static factor.
    LinearChallengeTerm {
        challenge: EvaluationChallenge,
        factor: F,
    },
    /// The degree-0 term of a polynomial.
    ///
    /// The field element is the same in both the standard and evaluation bases.
    ConstantTerm(F),
    /// A proof challenge represented as a constant polynomial.
    ChallengeTerm(EvaluationChallenge),
}

impl<E, F: Field, B: Basis> Ast<E, F, B> {
    #[allow(dead_code)]
    pub fn distribute_powers<I: IntoIterator<Item = Self>>(i: I, base: F) -> Self {
        Ast::DistributePowers(Arc::new(i.into_iter().collect()), base)
    }

    pub(crate) fn distribute_challenge_powers<I: IntoIterator<Item = Self>>(
        i: I,
        challenge: EvaluationChallenge,
    ) -> Self {
        Ast::DistributeChallengePowers(Arc::new(i.into_iter().collect()), challenge)
    }
}

impl<E, F: Field, B: Basis> fmt::Debug for Ast<E, F, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Poly(leaf) => f.debug_tuple("Poly").field(leaf).finish(),
            Self::Add(lhs, rhs) => f.debug_tuple("Add").field(lhs).field(rhs).finish(),
            Self::Mul(x) => f.debug_tuple("Mul").field(x).finish(),
            Self::Scale(base, scalar) => f.debug_tuple("Scale").field(base).field(scalar).finish(),
            Self::DistributePowers(terms, base) => f
                .debug_tuple("DistributePowers")
                .field(terms)
                .field(base)
                .finish(),
            Self::DistributeChallengePowers(terms, challenge) => f
                .debug_tuple("DistributeChallengePowers")
                .field(terms)
                .field(challenge)
                .finish(),
            Self::LinearTerm(x) => f.debug_tuple("LinearTerm").field(x).finish(),
            Self::LinearChallengeTerm { challenge, factor } => f
                .debug_struct("LinearChallengeTerm")
                .field("challenge", challenge)
                .field("factor", factor)
                .finish(),
            Self::ConstantTerm(x) => f.debug_tuple("ConstantTerm").field(x).finish(),
            Self::ChallengeTerm(challenge) => {
                f.debug_tuple("ChallengeTerm").field(challenge).finish()
            }
        }
    }
}

impl<E, F: Field, B: Basis> From<AstLeaf<E, B>> for Ast<E, F, B> {
    fn from(leaf: AstLeaf<E, B>) -> Self {
        Ast::Poly(leaf)
    }
}

impl<E, F: Field, B: Basis> Ast<E, F, B> {
    pub(crate) fn one() -> Self {
        Self::ConstantTerm(F::ONE)
    }
}

impl<E, F: Field, B: Basis> Neg for Ast<E, F, B> {
    type Output = Ast<E, F, B>;

    fn neg(self) -> Self::Output {
        Ast::Scale(Arc::new(self), -F::ONE)
    }
}

impl<E: Clone, F: Field, B: Basis> Neg for &Ast<E, F, B> {
    type Output = Ast<E, F, B>;

    fn neg(self) -> Self::Output {
        -(self.clone())
    }
}

impl<E, F: Field, B: Basis> Add for Ast<E, F, B> {
    type Output = Ast<E, F, B>;

    fn add(self, other: Self) -> Self::Output {
        Ast::Add(Arc::new(self), Arc::new(other))
    }
}

impl<'a, E: Clone, F: Field, B: Basis> Add<&'a Ast<E, F, B>> for &'a Ast<E, F, B> {
    type Output = Ast<E, F, B>;

    fn add(self, other: &'a Ast<E, F, B>) -> Self::Output {
        self.clone() + other.clone()
    }
}

impl<E, F: Field, B: Basis> Add<AstLeaf<E, B>> for Ast<E, F, B> {
    type Output = Ast<E, F, B>;

    fn add(self, other: AstLeaf<E, B>) -> Self::Output {
        Ast::Add(Arc::new(self), Arc::new(other.into()))
    }
}

impl<E, F: Field, B: Basis> Sub for Ast<E, F, B> {
    type Output = Ast<E, F, B>;

    fn sub(self, other: Self) -> Self::Output {
        self + (-other)
    }
}

impl<'a, E: Clone, F: Field, B: Basis> Sub<&'a Ast<E, F, B>> for &'a Ast<E, F, B> {
    type Output = Ast<E, F, B>;

    fn sub(self, other: &'a Ast<E, F, B>) -> Self::Output {
        self + &(-other)
    }
}

impl<E, F: Field, B: Basis> Sub<AstLeaf<E, B>> for Ast<E, F, B> {
    type Output = Ast<E, F, B>;

    fn sub(self, other: AstLeaf<E, B>) -> Self::Output {
        self + (-Ast::from(other))
    }
}

impl<E, F: Field> Mul for Ast<E, F, LagrangeCoeff> {
    type Output = Ast<E, F, LagrangeCoeff>;

    fn mul(self, other: Self) -> Self::Output {
        Ast::Mul(AstMul(Arc::new(self), Arc::new(other)))
    }
}

impl<'a, E: Clone, F: Field> Mul<&'a Ast<E, F, LagrangeCoeff>> for &'a Ast<E, F, LagrangeCoeff> {
    type Output = Ast<E, F, LagrangeCoeff>;

    fn mul(self, other: &'a Ast<E, F, LagrangeCoeff>) -> Self::Output {
        self.clone() * other.clone()
    }
}

impl<E, F: Field> Mul<AstLeaf<E, LagrangeCoeff>> for Ast<E, F, LagrangeCoeff> {
    type Output = Ast<E, F, LagrangeCoeff>;

    fn mul(self, other: AstLeaf<E, LagrangeCoeff>) -> Self::Output {
        Ast::Mul(AstMul(Arc::new(self), Arc::new(other.into())))
    }
}

impl<E, F: Field> Mul for Ast<E, F, ExtendedLagrangeCoeff> {
    type Output = Ast<E, F, ExtendedLagrangeCoeff>;

    fn mul(self, other: Self) -> Self::Output {
        Ast::Mul(AstMul(Arc::new(self), Arc::new(other)))
    }
}

impl<'a, E: Clone, F: Field> Mul<&'a Ast<E, F, ExtendedLagrangeCoeff>>
    for &'a Ast<E, F, ExtendedLagrangeCoeff>
{
    type Output = Ast<E, F, ExtendedLagrangeCoeff>;

    fn mul(self, other: &'a Ast<E, F, ExtendedLagrangeCoeff>) -> Self::Output {
        self.clone() * other.clone()
    }
}

impl<E, F: Field> Mul<AstLeaf<E, ExtendedLagrangeCoeff>> for Ast<E, F, ExtendedLagrangeCoeff> {
    type Output = Ast<E, F, ExtendedLagrangeCoeff>;

    fn mul(self, other: AstLeaf<E, ExtendedLagrangeCoeff>) -> Self::Output {
        Ast::Mul(AstMul(Arc::new(self), Arc::new(other.into())))
    }
}

impl<E, F: Field, B: Basis> Mul<F> for Ast<E, F, B> {
    type Output = Ast<E, F, B>;

    fn mul(self, other: F) -> Self::Output {
        Ast::Scale(Arc::new(self), other)
    }
}

impl<E: Clone, F: Field, B: Basis> Mul<F> for &Ast<E, F, B> {
    type Output = Ast<E, F, B>;

    fn mul(self, other: F) -> Self::Output {
        Ast::Scale(Arc::new(self.clone()), other)
    }
}

impl<E: Clone, F: Field> MulAssign for Ast<E, F, ExtendedLagrangeCoeff> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone().mul(rhs)
    }
}

/// Operations which can be performed over a given basis.
pub(crate) trait BasisOps: Basis {
    /// Whether repeated dense evaluations of [`Ast::LinearTerm`] are worth
    /// retaining in the evaluator's bounded cache.
    const CACHE_REPEATED_LINEAR_TERMS: bool;

    fn empty_poly<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
    ) -> Polynomial<F, Self>;
    fn fill_constant<F: Field>(chunk_index: usize, scalar: F, output: &mut [F]);
    /// Combines `output` with the basis representation of `scalar` in place.
    ///
    /// `combine` receives the existing output value first and the corresponding
    /// coefficient or evaluation of the constant polynomial second.
    fn combine_constant<F: Field>(
        chunk_index: usize,
        scalar: F,
        output: &mut [F],
        combine: impl FnMut(F, F) -> F,
    );
    fn fill_linear<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
        chunk_size: usize,
        chunk_index: usize,
        scalar: F,
        output: &mut [F],
    );
    fn copy_rotated_chunk<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
        chunk_size: usize,
        chunk_index: usize,
        poly: &Polynomial<F, Self>,
        rotation: Rotation,
        output: &mut [F],
    ) {
        let (first_values, second_values) = Self::rotated_chunk(
            domain,
            chunk_size,
            chunk_index,
            poly,
            rotation,
            output.len(),
        );
        let (first, second) = output.split_at_mut(first_values.len());
        first.copy_from_slice(first_values);
        second.copy_from_slice(second_values);
    }
    fn rotated_chunk<'a, F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
        chunk_size: usize,
        chunk_index: usize,
        poly: &'a Polynomial<F, Self>,
        rotation: Rotation,
        chunk_len: usize,
    ) -> (&'a [F], &'a [F]);
}

struct RotatedChunk<'a, F> {
    first: &'a [F],
    second: &'a [F],
}

impl<'a, F: Copy> RotatedChunk<'a, F> {
    fn new(
        values: &'a [F],
        rotation_is_negative: bool,
        rotation_abs: usize,
        chunk_size: usize,
        chunk_index: usize,
        chunk_len: usize,
    ) -> Self {
        assert!(rotation_abs <= values.len());

        let mid = if rotation_is_negative {
            values.len() - rotation_abs
        } else {
            rotation_abs
        };
        let unwrapped_start = mid + chunk_size * chunk_index;
        let source_start = if unwrapped_start >= values.len() {
            unwrapped_start - values.len()
        } else {
            unwrapped_start
        };

        let first_len = chunk_len.min(values.len() - source_start);
        Self {
            first: &values[source_start..source_start + first_len],
            second: &values[..chunk_len - first_len],
        }
    }

    fn iter(&self) -> impl Iterator<Item = &'a F> + use<'a, F> {
        self.first.iter().chain(self.second)
    }

    fn into_slices(self) -> (&'a [F], &'a [F]) {
        (self.first, self.second)
    }
}

impl BasisOps for Coeff {
    const CACHE_REPEATED_LINEAR_TERMS: bool = false;

    fn empty_poly<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
    ) -> Polynomial<F, Self> {
        domain.empty_coeff()
    }

    fn fill_constant<F: Field>(chunk_index: usize, scalar: F, output: &mut [F]) {
        output.fill(F::ZERO);
        if chunk_index == 0 {
            output[0] = scalar;
        }
    }

    fn combine_constant<F: Field>(
        chunk_index: usize,
        scalar: F,
        output: &mut [F],
        mut combine: impl FnMut(F, F) -> F,
    ) {
        for (index, value) in output.iter_mut().enumerate() {
            let constant = if chunk_index == 0 && index == 0 {
                scalar
            } else {
                F::ZERO
            };
            *value = combine(*value, constant);
        }
    }

    fn fill_linear<F: WithSmallOrderMulGroup<3>>(
        _: &EvaluationDomain<F>,
        chunk_size: usize,
        chunk_index: usize,
        scalar: F,
        output: &mut [F],
    ) {
        output.fill(F::ZERO);
        // If the chunk size is 1 (e.g. if we have a small k and many threads), then the
        // linear coefficient is the second chunk. Otherwise, the chunk size is greater
        // than one, and the linear coefficient is the second element of the first chunk.
        // Note that we check against the original chunk size, not the potentially-short
        // actual size of the current chunk, because we want to know whether the size of
        // the previous chunk was 1.
        if chunk_size == 1 {
            if chunk_index == 1 {
                output[0] = scalar;
            }
        } else if chunk_index == 0 {
            output[1] = scalar;
        }
    }

    fn rotated_chunk<'a, F: WithSmallOrderMulGroup<3>>(
        _: &EvaluationDomain<F>,
        _: usize,
        _: usize,
        _: &'a Polynomial<F, Self>,
        _: Rotation,
        _: usize,
    ) -> (&'a [F], &'a [F]) {
        panic!("Can't rotate polynomials in the standard basis")
    }
}

impl BasisOps for LagrangeCoeff {
    const CACHE_REPEATED_LINEAR_TERMS: bool = true;

    fn empty_poly<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
    ) -> Polynomial<F, Self> {
        domain.empty_lagrange()
    }

    fn fill_constant<F: Field>(_: usize, scalar: F, output: &mut [F]) {
        output.fill(scalar);
    }

    fn combine_constant<F: Field>(
        _: usize,
        scalar: F,
        output: &mut [F],
        mut combine: impl FnMut(F, F) -> F,
    ) {
        for value in output {
            *value = combine(*value, scalar);
        }
    }

    fn fill_linear<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
        chunk_size: usize,
        chunk_index: usize,
        scalar: F,
        output: &mut [F],
    ) {
        // Take every power of omega within the chunk, and multiply by scalar.
        let omega = domain.get_omega();
        let start = chunk_size * chunk_index;
        let mut value = omega.pow_vartime([start as u64]) * scalar;
        for output in output.iter_mut() {
            *output = value;
            value *= omega;
        }
    }

    fn rotated_chunk<'a, F: WithSmallOrderMulGroup<3>>(
        _: &EvaluationDomain<F>,
        chunk_size: usize,
        chunk_index: usize,
        poly: &'a Polynomial<F, Self>,
        rotation: Rotation,
        chunk_len: usize,
    ) -> (&'a [F], &'a [F]) {
        RotatedChunk::new(
            &poly.values,
            rotation.0 < 0,
            rotation.0.unsigned_abs() as usize,
            chunk_size,
            chunk_index,
            chunk_len,
        )
        .into_slices()
    }
}

impl BasisOps for ExtendedLagrangeCoeff {
    const CACHE_REPEATED_LINEAR_TERMS: bool = true;

    fn empty_poly<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
    ) -> Polynomial<F, Self> {
        domain.empty_extended()
    }

    fn fill_constant<F: Field>(_: usize, scalar: F, output: &mut [F]) {
        output.fill(scalar);
    }

    fn combine_constant<F: Field>(
        _: usize,
        scalar: F,
        output: &mut [F],
        mut combine: impl FnMut(F, F) -> F,
    ) {
        for value in output {
            *value = combine(*value, scalar);
        }
    }

    fn fill_linear<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
        chunk_size: usize,
        chunk_index: usize,
        scalar: F,
        output: &mut [F],
    ) {
        // Take every power of the extended omega within the chunk, and multiply by scalar.
        let omega = domain.get_extended_omega();
        let start = chunk_size * chunk_index;
        let mut value = omega.pow_vartime([start as u64]) * F::ZETA * scalar;
        for output in output.iter_mut() {
            *output = value;
            value *= omega;
        }
    }

    fn rotated_chunk<'a, F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
        chunk_size: usize,
        chunk_index: usize,
        poly: &'a Polynomial<F, Self>,
        rotation: Rotation,
        chunk_len: usize,
    ) -> (&'a [F], &'a [F]) {
        let rotation_scale = domain.get_quotient_poly_degree().next_power_of_two();
        debug_assert_eq!(poly.len() % rotation_scale, 0);
        let rotation_period = poly.len() / rotation_scale;
        let rotation_abs = (usize::try_from(rotation.0.unsigned_abs())
            .expect("rotation magnitude fits in usize")
            % rotation_period)
            * rotation_scale;
        RotatedChunk::new(
            &poly.values,
            rotation.0 < 0,
            rotation_abs,
            chunk_size,
            chunk_index,
            chunk_len,
        )
        .into_slices()
    }
}

#[cfg(test)]
mod tests {
    use std::{borrow::Cow, sync::Arc};

    use group::ff::{Field, WithSmallOrderMulGroup};
    use pasta_curves::{pallas, vesta};

    use super::{
        Ast, AstLeaf, AstMul, BasisOps, BoundPlanScalars, CacheAction, DistributionWork,
        EvaluationChallenge, EvaluationChallenges, EvaluationPlan, EvaluationPolyTag, Evaluator,
        FactorBodyPlan, FactorSide, LinearTermCacheBudget, LinearTermCacheOccupancy,
        MAX_ADDITIONAL_LINEAR_TERM_CACHE_BYTES, MAX_LINEAR_TERM_CACHE_ENTRIES, PlanScalar,
        PlanScalarInterner, ReusablePowerFold, ScalarId, compressed_selector, get_chunk_params,
        linear_term_cache_budget, new_evaluator, new_virtual_evaluator, reuse_cache_slots,
        selector_family_matches,
    };
    use crate::poly::{
        Basis, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation,
    };

    fn check_reusable_power_fold<F: Field + From<u64>>() {
        let terms = |seed: u64| {
            (0..7)
                .map(|offset| F::from(seed + offset))
                .collect::<Vec<_>>()
        };
        let cases = [
            vec![(terms(2), F::from(3)), (terms(11), F::from(5))],
            vec![(terms(17), F::ONE)],
            vec![(terms(23), F::ONE), (terms(31), F::from(7))],
            vec![(terms(41), F::from(11)), (terms(47), F::ONE)],
            vec![(terms(53), F::ONE), (terms(61), F::ONE)],
        ];
        let mut fold = ReusablePowerFold::<F>::new(7);
        for case in cases {
            fold.reset();
            let mut expected = vec![F::ZERO; 7];
            for (terms, power) in case {
                fold.terms().copy_from_slice(&terms);
                fold.accumulate(power);
                for (expected, term) in expected.iter_mut().zip(terms) {
                    *expected += term * power;
                }
            }
            let mut actual = vec![F::ZERO; 7];
            fold.finish_into(&mut actual);
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn reusable_power_fold_resets_every_buffer() {
        check_reusable_power_fold::<pallas::Base>();
        check_reusable_power_fold::<vesta::Base>();
    }

    fn compile_plan<E: Copy, F: Field, B: Basis>(
        ast: &Ast<E, F, B>,
    ) -> (EvaluationPlan<F>, Box<[PlanScalar<F>]>) {
        let mut scalars = PlanScalarInterner::new();
        let plan = EvaluationPlan::compile(ast, &mut scalars);
        (plan, scalars.finish())
    }

    fn compile_plan_only<E: Copy, F: Field, B: Basis>(ast: &Ast<E, F, B>) -> EvaluationPlan<F> {
        compile_plan(ast).0
    }

    fn plan_scalar<F: Field>(scalars: &[PlanScalar<F>], id: ScalarId<F>) -> PlanScalar<F> {
        scalars[id.index()]
    }

    #[test]
    fn plan_scalars_are_exactly_interned_and_bound_once() {
        type F = pallas::Base;

        let descriptors = [
            PlanScalar::Literal(F::from(3)),
            PlanScalar::Challenge(EvaluationChallenge::Theta),
            PlanScalar::Challenge(EvaluationChallenge::Beta),
            PlanScalar::Challenge(EvaluationChallenge::Gamma),
            PlanScalar::ScaledChallenge {
                challenge: EvaluationChallenge::Beta,
                factor: F::from(5),
            },
            PlanScalar::ChallengePower {
                challenge: EvaluationChallenge::Y,
                exponent: 3,
            },
        ];
        let mut interner = PlanScalarInterner::new();
        let ids = descriptors.map(|descriptor| interner.intern(descriptor));
        assert_eq!(
            descriptors.map(|descriptor| interner.intern(descriptor)),
            ids
        );
        assert!(ids.windows(2).all(|pair| pair[0] != pair[1]));

        let stored = interner.finish();
        assert_eq!(&*stored, &descriptors);
        let bound = BoundPlanScalars::new(
            &stored,
            EvaluationChallenges {
                // Equal challenge values must not coalesce their symbolic IDs.
                theta: F::from(7),
                beta: F::from(7),
                gamma: F::from(7),
                y: F::from(11),
            },
            super::max_challenge_exponents(&stored),
        );
        let expected = [
            F::from(3),
            F::from(7),
            F::from(7),
            F::from(7),
            F::from(35),
            F::from(11).pow_vartime([3]),
        ];
        assert_eq!(ids.map(|id| bound.get(id)), expected);

        assert!(ScalarId::<F>::from_index(u32::MAX as usize).is_some());
        if usize::BITS > u32::BITS {
            assert!(ScalarId::<F>::from_index(u32::MAX as usize + 1).is_none());
        }
    }

    #[test]
    fn short_chunk_regression_test() {
        // Pick the smallest polynomial length that is guaranteed to produce a short chunk
        // on this machine.
        let k = match (1..16)
            .map(|k| (k, get_chunk_params(1 << k)))
            .find(|(k, (chunk_size, num_chunks))| (1 << k) < chunk_size * num_chunks)
            .map(|(k, _)| k)
        {
            Some(k) => k,
            None => {
                // We are on a machine with a power-of-two number of threads, and cannot
                // trigger the bug.
                eprintln!(
                    "can't find a polynomial length for short_chunk_regression_test; skipping"
                );
                return;
            }
        };
        eprintln!("Testing short-chunk regression with k = {}", k);

        fn test_case<E: Copy + Send + Sync, B: BasisOps>(
            k: u32,
            mut evaluator: Evaluator<E, pallas::Base, B>,
        ) {
            // Instantiate the evaluator with a trivial polynomial.
            let domain = EvaluationDomain::new(1, k);
            evaluator.register_poly(B::empty_poly(&domain));

            // With the bug present, these will panic.
            let _ = evaluator.evaluate(&Ast::ConstantTerm(pallas::Base::ZERO), &domain);
            let _ = evaluator.evaluate(&Ast::LinearTerm(pallas::Base::ZERO), &domain);
        }

        test_case(k, new_evaluator::<_, _, Coeff>(|| {}));
        test_case(k, new_evaluator::<_, _, LagrangeCoeff>(|| {}));
        test_case(k, new_evaluator::<_, _, ExtendedLagrangeCoeff>(|| {}));
    }

    #[test]
    fn borrowed_and_owned_polynomials_evaluate_together() {
        const K: u32 = 4;

        let domain = EvaluationDomain::new(1, K);
        let poly = domain.lagrange_from_vec(
            (0..1 << K)
                .map(|value| pallas::Base::from(value as u64))
                .collect(),
        );

        let mut evaluator = new_evaluator(|| {});
        let borrowed_leaf = evaluator.register_poly_ref(&poly);
        assert!(matches!(
            &evaluator.polys[borrowed_leaf.index],
            Cow::Borrowed(stored) if std::ptr::eq(*stored, &poly)
        ));

        let owned_leaf = evaluator.register_poly(poly.clone());
        assert!(matches!(&evaluator.polys[owned_leaf.index], Cow::Owned(_)));

        let mixed = evaluator.evaluate(&(Ast::from(borrowed_leaf) + owned_leaf), &domain);
        let expected = domain.lagrange_from_vec(poly.iter().map(|value| value.double()).collect());

        assert!(expected.iter().eq(mixed.iter()));
    }

    #[test]
    fn scale_by_small_values() {
        let domain = EvaluationDomain::new(1, 4);
        let mut evaluator = new_evaluator::<_, _, ExtendedLagrangeCoeff>(|| {});
        evaluator.register_poly(ExtendedLagrangeCoeff::empty_poly(&domain));

        let value = pallas::Base::from(42);
        for (scalar, expected) in [
            (pallas::Base::ONE, value),
            (-pallas::Base::ONE, -value),
            (pallas::Base::ONE.double(), value.double()),
        ] {
            let result = evaluator.evaluate(&(Ast::ConstantTerm(value) * scalar), &domain);
            assert!(result.iter().all(|result| *result == expected));
        }
    }

    #[test]
    fn scale_polynomials_by_small_values() {
        fn check<B: BasisOps>() {
            fn context() {}

            let domain = EvaluationDomain::new(1, 4);
            let mut poly = B::empty_poly(&domain);
            for (index, value) in poly.iter_mut().enumerate() {
                *value = pallas::Base::from(index as u64 + 7);
            }
            let mut evaluator = new_evaluator::<fn(), _, B>(context);
            let leaf = evaluator.register_poly(poly);

            for rotation in [Rotation::cur(), Rotation::prev(), Rotation::next()] {
                let leaf = leaf.with_rotation(rotation);
                let expected = evaluator.evaluate(&Ast::from(leaf), &domain);
                for scalar in [
                    -pallas::Base::ONE,
                    pallas::Base::ONE,
                    pallas::Base::ONE.double(),
                    pallas::Base::from(7),
                ] {
                    let ast = Ast::from(leaf) * scalar;
                    assert!(matches!(
                        compile_plan_only(&ast),
                        EvaluationPlan::Scale(inner, _)
                            if matches!(inner.as_ref(), EvaluationPlan::Poly(_))
                    ));

                    let result = evaluator.evaluate(&ast, &domain);
                    assert!(
                        result
                            .iter()
                            .zip(expected.iter())
                            .all(|(result, value)| *result == *value * scalar)
                    );
                }
            }
        }

        check::<LagrangeCoeff>();
        check::<ExtendedLagrangeCoeff>();
    }

    #[test]
    fn multiply_by_constant_terms() {
        fn check<B: BasisOps>()
        where
            Ast<fn(), pallas::Base, B>: std::ops::Mul<Output = Ast<fn(), pallas::Base, B>>,
        {
            fn context() {}

            let domain = EvaluationDomain::new(1, 4);
            let mut poly = B::empty_poly(&domain);
            for (index, value) in poly.iter_mut().enumerate() {
                *value = pallas::Base::from(index as u64 + 7);
            }
            let expected = poly.clone();

            let mut evaluator = new_evaluator::<fn(), _, B>(context);
            let leaf = evaluator.register_poly(poly);
            let two = pallas::Base::ONE.double();

            for scalar in [
                -pallas::Base::ONE,
                pallas::Base::ONE,
                two,
                pallas::Base::from(7),
            ] {
                let constant = Ast::ConstantTerm(scalar);
                let expression = Ast::from(leaf);
                let constant_lhs = constant.clone() * expression.clone();
                let constant_rhs = expression * constant;

                for ast in [constant_lhs, constant_rhs] {
                    assert!(matches!(&ast, Ast::Mul(_)));

                    let result = evaluator.evaluate(&ast, &domain);
                    assert!(
                        result
                            .iter()
                            .zip(expected.iter())
                            .all(|(result, value)| *result == *value * scalar)
                    );
                }
            }
        }

        check::<LagrangeCoeff>();
        check::<ExtendedLagrangeCoeff>();
    }

    #[test]
    fn multiply_two_constant_terms() {
        fn check<B: BasisOps>()
        where
            Ast<fn(), pallas::Base, B>: std::ops::Mul<Output = Ast<fn(), pallas::Base, B>>,
        {
            type F = pallas::Base;

            fn context() {}

            let domain = EvaluationDomain::new(3, 4);
            let mut evaluator = new_evaluator::<fn(), _, B>(context);
            evaluator
                .register_poly_with_tag(B::empty_poly(&domain), EvaluationPolyTag::new(0, 0, 0));

            for (lhs, rhs) in [
                (-F::ONE, F::from(7)),
                (F::ZERO, F::from(11)),
                (F::ONE, F::from(13)),
                (F::from(2), F::from(17)),
            ] {
                let expected = lhs * rhs;
                let ast = Ast::ConstantTerm(lhs) * Ast::ConstantTerm(rhs);
                assert!(matches!(
                    compile_plan_only(&ast),
                    EvaluationPlan::Mul(lhs, rhs)
                        if matches!(lhs.as_ref(), EvaluationPlan::ConstantTerm(_))
                            && matches!(rhs.as_ref(), EvaluationPlan::ConstantTerm(_))
                ));
                let actual = evaluator.evaluate(&ast, &domain);
                assert!(actual.iter().all(|value| *value == expected));
            }

            let ast = Ast::ChallengeTerm(EvaluationChallenge::Theta)
                * Ast::ChallengeTerm(EvaluationChallenge::Beta);
            let challenge_pairs = [
                (-F::ONE, F::from(7)),
                (F::ZERO, F::from(11)),
                (F::ONE, F::from(13)),
                (F::from(2), F::from(17)),
            ];
            let first = challenge_pairs[0];
            let (actual, plan) = evaluator.evaluate_quotient_with_compiled_plan(
                std::iter::once(ast),
                &domain,
                None,
                EvaluationChallenges::new(first.0, first.1, F::from(19), F::from(23)),
            );
            assert!(actual.iter().all(|value| *value == first.0 * first.1));
            let plan = plan.expect("a tagged evaluation returns a retained plan");
            assert!(matches!(
                &plan.plan,
                EvaluationPlan::Mul(lhs, rhs)
                    if matches!(lhs.as_ref(), EvaluationPlan::ConstantTerm(_))
                        && matches!(rhs.as_ref(), EvaluationPlan::ConstantTerm(_))
            ));

            for (lhs, rhs) in &challenge_pairs[1..] {
                let (actual, replacement) = evaluator.evaluate_quotient_with_compiled_plan(
                    std::iter::empty(),
                    &domain,
                    Some(&plan),
                    EvaluationChallenges::new(*lhs, *rhs, F::from(29), F::from(31)),
                );
                assert!(replacement.is_none());
                assert!(actual.iter().all(|value| *value == *lhs * rhs));
            }
        }

        check::<LagrangeCoeff>();
        check::<ExtendedLagrangeCoeff>();
    }

    fn assert_constant_add_sub_values<B: BasisOps>() {
        type F = pallas::Base;

        fn context() {}

        fn assert_operation<B: BasisOps>(
            operation: usize,
            actual: &Polynomial<F, B>,
            value: &Polynomial<F, B>,
            constant: &Polynomial<F, B>,
        ) {
            assert!(actual.iter().zip(value.iter().zip(constant.iter())).all(
                |(actual, (value, constant))| {
                    *actual
                        == match operation {
                            0 | 1 => *value + constant,
                            2 => *constant - value,
                            3 => *value - constant,
                            _ => unreachable!(),
                        }
                }
            ));
        }

        let domain = EvaluationDomain::new(3, 4);
        let mut evaluator = new_evaluator::<fn(), _, B>(context);
        evaluator.register_poly_with_tag(B::empty_poly(&domain), EvaluationPolyTag::new(0, 0, 0));
        let value = Ast::LinearTerm(F::from(11));
        let expected_value = evaluator.evaluate(&value, &domain);
        let scalars = [-F::ONE, F::ZERO, F::ONE, F::from(2), F::from(7)];

        for scalar in scalars {
            let constant = Ast::ConstantTerm(scalar);
            let operations = [
                constant.clone() + value.clone(),
                value.clone() + constant.clone(),
                constant.clone() - value.clone(),
                value.clone() - constant,
            ];
            let expected_constant = evaluator.evaluate(&Ast::ConstantTerm(scalar), &domain);
            for (operation, ast) in operations.iter().enumerate() {
                let actual = evaluator.evaluate(ast, &domain);
                assert_operation(operation, &actual, &expected_value, &expected_constant);
            }

            // In the coefficient basis, multiplication by a constant is
            // represented by `Scale`, because pointwise `Mul` is only defined
            // for evaluation bases.
            let scaled = value.clone() * scalar;
            let actual = evaluator.evaluate(&scaled, &domain);
            assert!(
                actual
                    .iter()
                    .zip(expected_value.iter())
                    .all(|(actual, value)| *actual == *value * scalar)
            );
        }

        for operation in 0..4 {
            let constant = Ast::ChallengeTerm(EvaluationChallenge::Theta);
            let ast = match operation {
                0 => constant.clone() + value.clone(),
                1 => value.clone() + constant.clone(),
                2 => constant.clone() - value.clone(),
                3 => value.clone() - constant,
                _ => unreachable!(),
            };
            let first_scalar = scalars[0];
            let first_challenges =
                EvaluationChallenges::new(first_scalar, F::from(13), F::from(17), F::from(19));
            let (first, plan) = evaluator.evaluate_quotient_with_compiled_plan(
                std::iter::once(ast),
                &domain,
                None,
                first_challenges,
            );
            let plan = plan.expect("a tagged evaluation returns a retained plan");
            let expected_constant = evaluator.evaluate(&Ast::ConstantTerm(first_scalar), &domain);
            assert_operation(operation, &first, &expected_value, &expected_constant);

            for scalar in &scalars[1..] {
                let challenges =
                    EvaluationChallenges::new(*scalar, F::from(23), F::from(29), F::from(31));
                let (actual, replacement) = evaluator.evaluate_quotient_with_compiled_plan(
                    std::iter::empty(),
                    &domain,
                    Some(&plan),
                    challenges,
                );
                assert!(replacement.is_none());
                let expected_constant = evaluator.evaluate(&Ast::ConstantTerm(*scalar), &domain);
                assert_operation(operation, &actual, &expected_value, &expected_constant);
            }
        }
    }

    #[test]
    fn constant_add_sub_consumers_match_all_bases() {
        assert_constant_add_sub_values::<Coeff>();
        assert_constant_add_sub_values::<LagrangeCoeff>();
        assert_constant_add_sub_values::<ExtendedLagrangeCoeff>();
    }

    fn assert_cached_constant_consumers<B: BasisOps>()
    where
        Ast<fn(), pallas::Base, B>: std::ops::Mul<Output = Ast<fn(), pallas::Base, B>>,
    {
        type F = pallas::Base;

        fn context() {}

        fn expression<B>(
            operation: usize,
            constant: Ast<fn(), F, B>,
            value: Ast<fn(), F, B>,
        ) -> Ast<fn(), F, B>
        where
            B: BasisOps,
            Ast<fn(), F, B>: std::ops::Mul<Output = Ast<fn(), F, B>>,
        {
            match operation {
                0 => constant + value,
                1 => value + constant,
                2 => constant - value,
                3 => value - constant,
                4 => constant * value,
                5 => value * constant,
                _ => unreachable!(),
            }
        }

        fn expected(operation: usize, value: F, constant: F) -> F {
            match operation {
                0 | 1 => value + constant,
                2 => constant - value,
                3 => value - constant,
                4 | 5 => value * constant,
                _ => unreachable!(),
            }
        }

        fn assert_values<B: Basis>(
            operation: usize,
            actual: &Polynomial<F, B>,
            value: &Polynomial<F, B>,
            scalar: F,
        ) {
            assert!(
                actual
                    .iter()
                    .zip(value.iter())
                    .all(|(actual, value)| *actual == expected(operation, *value, scalar))
            );
        }

        let domain = EvaluationDomain::new(3, 4);
        let mut values = B::empty_poly(&domain);
        for (index, value) in values.iter_mut().enumerate() {
            *value = F::from(index as u64 + 3);
        }
        let mut evaluator = new_evaluator::<fn(), _, B>(context);
        let leaf = evaluator.register_poly_with_tag(values, EvaluationPolyTag::new(0, 0, 0));
        let value = Ast::from(leaf);
        let square = value.clone() * value;
        let cached_value = square.clone() + square;
        let expected_value = evaluator.evaluate(&cached_value, &domain);
        let scalars = [-F::ONE, F::ZERO, F::ONE, F::from(2), F::from(7)];

        for scalar in scalars {
            // Keep the AST operand non-trivial while compiling it to a
            // `ConstantTerm`, so `Mul` retains its original plan shape.
            let constant = Ast::ConstantTerm(scalar) + Ast::ConstantTerm(F::ZERO);
            for operation in 0..6 {
                let ast = expression(operation, constant.clone(), cached_value.clone());
                let (actual, plan) = evaluator.evaluate_quotient_with_compiled_plan(
                    std::iter::once(ast),
                    &domain,
                    None,
                    EvaluationChallenges::new(F::from(11), F::from(13), F::from(17), F::from(19)),
                );
                let plan = plan.expect("a tagged evaluation returns a retained plan");
                assert!(
                    plan.cache_slots > 0,
                    "the child is evaluated through the cache"
                );
                assert_values(operation, &actual, &expected_value, scalar);
            }
        }

        for operation in 0..6 {
            let ast = expression(
                operation,
                Ast::ChallengeTerm(EvaluationChallenge::Theta),
                cached_value.clone(),
            );
            let first_scalar = scalars[0];
            let (first, plan) = evaluator.evaluate_quotient_with_compiled_plan(
                std::iter::once(ast),
                &domain,
                None,
                EvaluationChallenges::new(first_scalar, F::from(13), F::from(17), F::from(19)),
            );
            let plan = plan.expect("a tagged evaluation returns a retained plan");
            assert!(
                plan.cache_slots > 0,
                "the child is evaluated through the cache"
            );
            assert_values(operation, &first, &expected_value, first_scalar);

            for scalar in &scalars[1..] {
                let (actual, replacement) = evaluator.evaluate_quotient_with_compiled_plan(
                    std::iter::empty(),
                    &domain,
                    Some(&plan),
                    EvaluationChallenges::new(*scalar, F::from(23), F::from(29), F::from(31)),
                );
                assert!(replacement.is_none());
                assert_values(operation, &actual, &expected_value, *scalar);
            }
        }
    }

    #[test]
    fn cached_constant_consumers_match_pointwise_bases() {
        assert_cached_constant_consumers::<LagrangeCoeff>();
        assert_cached_constant_consumers::<ExtendedLagrangeCoeff>();
    }

    #[test]
    fn subtract_polynomials() {
        let domain = EvaluationDomain::new(1, 4);
        let mut evaluator = new_evaluator::<_, _, ExtendedLagrangeCoeff>(|| {});
        evaluator.register_poly(ExtendedLagrangeCoeff::empty_poly(&domain));

        let lhs = pallas::Base::from(42);
        let rhs = pallas::Base::from(17);
        let result =
            evaluator.evaluate(&(Ast::ConstantTerm(lhs) - Ast::ConstantTerm(rhs)), &domain);
        assert!(result.iter().all(|result| *result == lhs - rhs));
    }

    fn check_scaled_addends<F, B>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
        B: BasisOps,
    {
        let domain = EvaluationDomain::<F>::new(3, 4);
        let mut evaluator = new_evaluator::<_, F, B>(|| {});
        let leaves = (0..3)
            .map(|poly_index| {
                let mut poly = B::empty_poly(&domain);
                let poly_len = poly.len();
                for (row, value) in poly.iter_mut().enumerate() {
                    *value = F::from((poly_index * poly_len + row + 1) as u64);
                }
                evaluator.register_poly(poly)
            })
            .collect::<Vec<_>>();

        let lhs = Ast::from(leaves[0]);
        for rhs in [
            Ast::from(leaves[1]),
            Ast::from(leaves[1]) + Ast::from(leaves[2]),
        ] {
            for scalar in [-F::ONE, F::ONE, F::ONE.double(), F::from(7)] {
                let ast = lhs.clone() + rhs.clone() * scalar;
                assert!(matches!(
                    compile_plan_only(&ast),
                    EvaluationPlan::Add(_, addend)
                        if matches!(addend.as_ref(), EvaluationPlan::Scale(_, _))
                ));

                let lhs_values = evaluator.evaluate(&lhs, &domain);
                let rhs_values = evaluator.evaluate(&rhs, &domain);
                let actual = evaluator.evaluate(&ast, &domain);
                assert!(
                    actual
                        .iter()
                        .zip(lhs_values.iter().zip(rhs_values.iter()))
                        .all(|(actual, (lhs, rhs))| *actual == *lhs + *rhs * scalar)
                );
            }
        }
    }

    fn check_coefficient_scaled_addends<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
    {
        let domain = EvaluationDomain::<F>::new(3, 4);
        let mut evaluator = new_evaluator::<fn(), F, Coeff>(|| {});
        evaluator.register_poly(domain.empty_coeff());

        let lhs = Ast::ConstantTerm(F::from(3));
        let rhs = Ast::ConstantTerm(F::from(5)) + Ast::LinearTerm(F::from(7));
        for scalar in [-F::ONE, F::ONE, F::ONE.double(), F::from(11)] {
            let ast = lhs.clone() + rhs.clone() * scalar;
            let lhs_values = evaluator.evaluate(&lhs, &domain);
            let rhs_values = evaluator.evaluate(&rhs, &domain);
            let actual = evaluator.evaluate(&ast, &domain);
            assert!(
                actual
                    .iter()
                    .zip(lhs_values.iter().zip(rhs_values.iter()))
                    .all(|(actual, (lhs, rhs))| *actual == *lhs + *rhs * scalar)
            );
        }
    }

    #[test]
    fn scaled_addends_are_accumulated_in_place() {
        check_coefficient_scaled_addends::<pallas::Base>();
        check_scaled_addends::<pallas::Base, LagrangeCoeff>();
        check_scaled_addends::<pallas::Base, ExtendedLagrangeCoeff>();
        check_coefficient_scaled_addends::<vesta::Base>();
        check_scaled_addends::<vesta::Base, LagrangeCoeff>();
        check_scaled_addends::<vesta::Base, ExtendedLagrangeCoeff>();
    }

    #[test]
    fn in_place_terms_match_basis_values() {
        let domain = EvaluationDomain::new(3, 4);
        let scalar = pallas::Base::from(17);

        let mut coeff_evaluator = new_evaluator::<_, _, Coeff>(|| {});
        coeff_evaluator.register_poly(domain.empty_coeff());
        let mut expected = vec![pallas::Base::ZERO; 1 << 4];
        expected[0] = scalar;
        let actual = coeff_evaluator.evaluate(&Ast::ConstantTerm(scalar), &domain);
        assert_eq!(&actual[..], &expected);
        expected[0] = pallas::Base::ZERO;
        expected[1] = scalar;
        let actual = coeff_evaluator.evaluate(&Ast::LinearTerm(scalar), &domain);
        assert_eq!(&actual[..], &expected);

        let mut lagrange_evaluator = new_evaluator::<_, _, LagrangeCoeff>(|| {});
        lagrange_evaluator.register_poly(domain.empty_lagrange());
        assert!(
            lagrange_evaluator
                .evaluate(&Ast::ConstantTerm(scalar), &domain)
                .iter()
                .all(|value| *value == scalar)
        );
        let mut value = scalar;
        let expected = (0..1 << 4)
            .map(|_| {
                let current = value;
                value *= domain.get_omega();
                current
            })
            .collect::<Vec<_>>();
        let actual = lagrange_evaluator.evaluate(&Ast::LinearTerm(scalar), &domain);
        assert_eq!(&actual[..], &expected);

        let mut extended_evaluator = new_evaluator::<_, _, ExtendedLagrangeCoeff>(|| {});
        extended_evaluator.register_poly(domain.empty_extended());
        assert!(
            extended_evaluator
                .evaluate(&Ast::ConstantTerm(scalar), &domain)
                .iter()
                .all(|value| *value == scalar)
        );
        let mut value = scalar * pallas::Base::ZETA;
        let expected = (0..domain.extended_len())
            .map(|_| {
                let current = value;
                value *= domain.get_extended_omega();
                current
            })
            .collect::<Vec<_>>();
        let actual = extended_evaluator.evaluate(&Ast::LinearTerm(scalar), &domain);
        assert_eq!(&actual[..], &expected);
    }

    #[test]
    fn empty_and_singleton_distribute_powers_match_direct_evaluation() {
        fn check<B: BasisOps>() {
            fn context() {}

            let domain = EvaluationDomain::new(3, 4);
            let mut evaluator = new_evaluator::<fn(), _, B>(context);
            evaluator.register_poly(B::empty_poly(&domain));
            let base = pallas::Base::from(11);

            let empty = Ast::<fn(), pallas::Base, B>::distribute_powers([], base);
            let actual = evaluator.evaluate(&empty, &domain);
            assert!(actual.iter().all(|value| *value == pallas::Base::ZERO));

            let term =
                Ast::ConstantTerm(pallas::Base::from(17)) + Ast::LinearTerm(pallas::Base::from(19));
            let expected = evaluator.evaluate(&term, &domain);
            let singleton = Ast::distribute_powers([term], base);
            let actual = evaluator.evaluate(&singleton, &domain);
            assert_eq!(&actual[..], &expected[..]);
        }

        check::<Coeff>();
        check::<LagrangeCoeff>();
        check::<ExtendedLagrangeCoeff>();
    }

    #[test]
    fn in_place_rotation_matches_existing_chunk_helpers() {
        let domain = EvaluationDomain::new(5, 4);
        let lagrange = domain.lagrange_from_vec(
            (0..16)
                .map(|value| pallas::Base::from(value as u64))
                .collect(),
        );
        let mut extended = domain.empty_extended();
        for (index, value) in extended.iter_mut().enumerate() {
            *value = pallas::Base::from(index as u64);
        }

        for rotation in [
            Rotation(-16),
            Rotation(-6),
            Rotation::prev(),
            Rotation::cur(),
            Rotation::next(),
            Rotation(12),
            Rotation(16),
        ] {
            for chunk_size in [1, 3, 7, 16] {
                let num_chunks = lagrange.len().div_ceil(chunk_size);
                for chunk_index in 0..num_chunks {
                    let expected = lagrange
                        .rotate(rotation)
                        .chunks(chunk_size)
                        .nth(chunk_index)
                        .unwrap()
                        .to_vec();
                    let mut actual = vec![pallas::Base::ZERO; expected.len()];
                    lagrange.copy_rotated_chunk(rotation, chunk_size, chunk_index, &mut actual);
                    assert_eq!(actual, expected);
                }
            }

            let rotation_scale = domain.get_quotient_poly_degree().next_power_of_two();
            for chunk_size in [1, 3, 7, 16, 64] {
                let num_chunks = extended.len().div_ceil(chunk_size);
                for chunk_index in 0..num_chunks {
                    let expected = domain
                        .rotate_extended(&extended, rotation)
                        .chunks(chunk_size)
                        .nth(chunk_index)
                        .unwrap()
                        .to_vec();
                    let mut actual = vec![pallas::Base::ZERO; expected.len()];
                    extended.copy_rotated_chunk_helper(
                        rotation.0 < 0,
                        rotation.0.unsigned_abs() as usize * rotation_scale,
                        chunk_size,
                        chunk_index,
                        &mut actual,
                    );
                    assert_eq!(actual, expected);
                }
            }
        }
    }

    #[test]
    fn large_extended_rotations_are_cyclic() {
        let domain = EvaluationDomain::new(5, 4);
        let mut extended = domain.empty_extended();
        for (index, value) in extended.iter_mut().enumerate() {
            *value = pallas::Base::from(index as u64);
        }

        let rotation_scale = domain.get_quotient_poly_degree().next_power_of_two();
        assert_eq!(rotation_scale, 4);
        assert_eq!(extended.len(), 64);
        let rotation_period = i32::try_from(extended.len() / rotation_scale)
            .expect("test rotation period fits in i32");

        for rotation in [
            Rotation(1_073_741_825),
            Rotation(-1_073_741_825),
            Rotation(i32::MIN),
            Rotation(i32::MAX),
        ] {
            let offset = usize::try_from(rotation.0.rem_euclid(rotation_period))
                .expect("non-negative rotation fits in usize")
                * rotation_scale;
            let extended_values = &extended[..];
            let expected = extended_values[offset..]
                .iter()
                .chain(&extended_values[..offset])
                .copied()
                .collect::<Vec<_>>();
            let mut actual = vec![pallas::Base::ZERO; extended.len()];
            for (chunk_index, output) in actual.chunks_mut(7).enumerate() {
                ExtendedLagrangeCoeff::copy_rotated_chunk(
                    &domain,
                    7,
                    chunk_index,
                    &extended,
                    rotation,
                    output,
                );
            }
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn scratch_evaluation_matches_rowwise_expression() {
        let domain = EvaluationDomain::new(5, 4);
        let mut lhs_poly = domain.empty_extended();
        let mut rhs_poly = domain.empty_extended();
        for (index, (lhs, rhs)) in lhs_poly.iter_mut().zip(rhs_poly.iter_mut()).enumerate() {
            *lhs = pallas::Base::from((index + 1) as u64);
            *rhs = pallas::Base::from((2 * index + 3) as u64);
        }

        let lhs_cur = lhs_poly.clone();
        let lhs_prev = domain.rotate_extended(&lhs_poly, Rotation::prev());
        let rhs_prev = domain.rotate_extended(&rhs_poly, Rotation::prev());
        let rhs_next = domain.rotate_extended(&rhs_poly, Rotation::next());

        let mut evaluator = new_evaluator::<_, _, ExtendedLagrangeCoeff>(|| {});
        let lhs = evaluator.register_poly(lhs_poly);
        let rhs = evaluator.register_poly(rhs_poly);
        let product = (Ast::from(lhs.with_rotation(Rotation::prev()))
            + rhs.with_rotation(Rotation::next()))
            * (Ast::from(lhs) - rhs.with_rotation(Rotation::prev()));
        let scaled = Ast::from(lhs) * pallas::Base::from(3);
        let constant = Ast::ConstantTerm(pallas::Base::from(7));
        let base = pallas::Base::from(11);
        let ast = Ast::distribute_powers([product, scaled, constant], base);

        let actual = evaluator.evaluate(&ast, &domain);
        for index in 0..actual.len() {
            let product = (lhs_prev[index] + rhs_next[index]) * (lhs_cur[index] - rhs_prev[index]);
            let scaled = lhs_cur[index] * pallas::Base::from(3);
            let expected = (product * base + scaled) * base + pallas::Base::from(7);
            assert_eq!(actual[index], expected);
        }
    }

    fn expanded_polynomial_expression<E: Copy, F: Field>(
        base: Ast<E, F, ExtendedLagrangeCoeff>,
        coefficients: &[AstLeaf<E, ExtendedLagrangeCoeff>],
        prefix: F,
    ) -> Ast<E, F, ExtendedLagrangeCoeff> {
        let mut polynomial = Ast::ConstantTerm(prefix);
        let mut power = Ast::ConstantTerm(F::ONE);
        for coefficient in coefficients {
            polynomial = polynomial + power.clone() * Ast::from(*coefficient);
            power = power * base.clone();
        }
        polynomial
    }

    fn polynomial_expression_from_powers<E: Copy, F: Field>(
        powers: &[Ast<E, F, ExtendedLagrangeCoeff>],
        coefficients: &[AstLeaf<E, ExtendedLagrangeCoeff>],
    ) -> Ast<E, F, ExtendedLagrangeCoeff> {
        powers.iter().zip(coefficients).fold(
            Ast::ConstantTerm(F::ZERO),
            |polynomial, (power, coefficient)| polynomial + power.clone() * Ast::from(*coefficient),
        )
    }

    fn check_expanded_polynomials_use_horner<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
    {
        const INTERPOLATION_WIDTH: u64 = 8;

        fn context() {}

        let domain = EvaluationDomain::new(3, 3);
        let to_extended = |values| {
            domain.coeff_to_extended(domain.lagrange_to_coeff(domain.lagrange_from_vec(values)))
        };

        let direct_base_values = (0..INTERPOLATION_WIDTH)
            .map(|row| F::from(row + 3))
            .collect::<Vec<_>>();
        let left_base_values = (0..INTERPOLATION_WIDTH)
            .map(|row| F::from(2 * row + 5))
            .collect::<Vec<_>>();
        let right_base_values = (0..INTERPOLATION_WIDTH)
            .map(|row| F::from(3 * row + 1))
            .collect::<Vec<_>>();
        let coefficient_values = (0..INTERPOLATION_WIDTH)
            .map(|degree| {
                (0..INTERPOLATION_WIDTH)
                    .map(|row| F::from((degree + 2) * (row + 7) + 1))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let direct_target_values = (0..INTERPOLATION_WIDTH)
            .map(|row| F::from(5 * row + 11))
            .collect::<Vec<_>>();
        let compound_target_values = (0..INTERPOLATION_WIDTH)
            .map(|row| F::from(7 * row + 13))
            .collect::<Vec<_>>();
        let selector_values = (0..INTERPOLATION_WIDTH)
            .map(|row| F::from(row + 17))
            .collect::<Vec<_>>();

        let direct_base = to_extended(direct_base_values);
        let left_base = to_extended(left_base_values);
        let right_base = to_extended(right_base_values);
        let coefficient_polys = coefficient_values
            .into_iter()
            .map(to_extended)
            .collect::<Vec<_>>();
        let direct_target = to_extended(direct_target_values);
        let compound_target = to_extended(compound_target_values);
        let selector = to_extended(selector_values);

        let direct_base_values = direct_base.to_vec();
        let left_base_values = left_base.to_vec();
        let right_base_values = right_base.to_vec();
        let coefficient_values = coefficient_polys
            .iter()
            .map(|coefficient| coefficient.to_vec())
            .collect::<Vec<_>>();
        let direct_target_values = direct_target.to_vec();
        let compound_target_values = compound_target.to_vec();
        let selector_values = selector.to_vec();

        let mut evaluator = new_evaluator::<fn(), F, ExtendedLagrangeCoeff>(context);
        let direct_base = evaluator.register_poly(direct_base);
        let left_base = evaluator.register_poly(left_base);
        let right_base = evaluator.register_poly(right_base);
        let coefficients = coefficient_polys
            .into_iter()
            .map(|coefficient| evaluator.register_poly(coefficient))
            .collect::<Vec<_>>();
        let direct_target = evaluator.register_poly(direct_target);
        let compound_target = evaluator.register_poly(compound_target);
        let selector = evaluator.register_poly(selector);

        let direct_base = Ast::from(direct_base);
        let scale = F::from(INTERPOLATION_WIDTH);
        let compound_base = Ast::from(left_base) - Ast::from(right_base) * scale;
        let direct = expanded_polynomial_expression(direct_base.clone(), &coefficients, F::ZERO)
            - direct_target;
        let compound =
            expanded_polynomial_expression(compound_base.clone(), &coefficients, F::ZERO)
                - compound_target;

        let challenge = F::from(19);
        let selector = Ast::from(selector);
        let expression =
            Ast::distribute_powers([selector.clone() * direct, selector * compound], challenge);
        let actual = evaluator.evaluate(&expression, &domain);
        for row in 0..actual.len() {
            let evaluate = |base| {
                coefficient_values
                    .iter()
                    .rev()
                    .fold(F::ZERO, |accumulator, coefficient| {
                        accumulator * base + coefficient[row]
                    })
            };
            let direct = evaluate(direct_base_values[row]) - direct_target_values[row];
            let compound_base = left_base_values[row] - right_base_values[row] * scale;
            let compound = evaluate(compound_base) - compound_target_values[row];
            let expected = selector_values[row] * (direct * challenge + compound);
            assert_eq!(actual[row], expected);
        }

        let direct_polynomial =
            expanded_polynomial_expression(direct_base.clone(), &coefficients, F::ZERO);
        assert!(matches!(
            compile_plan_only(&direct_polynomial),
            EvaluationPlan::Horner { .. }
        ));

        let nonzero_prefix =
            expanded_polynomial_expression(direct_base.clone(), &coefficients, F::ONE);
        assert!(super::expanded_polynomial(&nonzero_prefix).is_none());
        assert!(
            super::expanded_polynomial(&expanded_polynomial_expression(
                direct_base.clone(),
                &coefficients[..3],
                F::ZERO,
            ))
            .is_none()
        );

        let mut powers = vec![];
        let mut power = Ast::ConstantTerm(F::ONE);
        for _ in &coefficients {
            powers.push(power.clone());
            power = power * compound_base.clone();
        }

        let mut broken_powers = powers.clone();
        broken_powers[4] = powers[2].clone();
        assert!(
            super::expanded_polynomial(&polynomial_expression_from_powers(
                &broken_powers,
                &coefficients,
            ))
            .is_none()
        );

        let mut changed_base = powers;
        changed_base[4] = changed_base[3].clone() * direct_base;
        assert!(
            super::expanded_polynomial(&polynomial_expression_from_powers(
                &changed_base,
                &coefficients,
            ))
            .is_none()
        );
    }

    #[test]
    fn expanded_polynomials_use_horner() {
        check_expanded_polynomials_use_horner::<pallas::Base>();
        check_expanded_polynomials_use_horner::<vesta::Base>();
    }

    fn check_repeated_subexpressions_use_squares<F, B>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
        B: BasisOps,
        Ast<fn(), F, B>: std::ops::Mul<Output = Ast<fn(), F, B>>,
    {
        fn context() {}

        let domain = EvaluationDomain::new(3, 4);
        let mut values = B::empty_poly(&domain);
        for (index, value) in values.iter_mut().enumerate() {
            *value = F::from(index as u64 + 3);
        }

        let mut evaluator = new_evaluator::<fn(), _, B>(context);
        let leaf = evaluator.register_poly(values);
        let repeated =
            Ast::from(leaf.with_rotation(Rotation::prev())) + Ast::ConstantTerm(F::from(7));
        let inner_square = repeated.clone() * repeated.clone();
        let nested_square = inner_square.clone() * inner_square;
        let plan = compile_plan_only(&nested_square);
        match &plan {
            EvaluationPlan::Square(inner) => {
                assert!(matches!(inner.as_ref(), EvaluationPlan::Square(_)));
            }
            _ => panic!("nested repeated operands compile to nested squares"),
        }

        let expected = evaluator.evaluate(&repeated, &domain);
        let actual = evaluator.evaluate(&nested_square, &domain);
        assert!(
            actual
                .iter()
                .zip(expected.iter())
                .all(|(actual, expected)| *actual == expected.square().square())
        );

        let lhs = Ast::from(leaf.with_rotation(Rotation::prev()));
        let rhs = Ast::from(leaf.with_rotation(Rotation::next()));
        let product = lhs.clone() * rhs.clone();
        assert!(matches!(
            compile_plan_only(&product),
            EvaluationPlan::Mul(_, _)
        ));

        let expected_lhs = evaluator.evaluate(&lhs, &domain);
        let expected_rhs = evaluator.evaluate(&rhs, &domain);
        let actual = evaluator.evaluate(&product, &domain);
        assert!(
            actual
                .iter()
                .zip(expected_lhs.iter().zip(expected_rhs.iter()))
                .all(|(actual, (lhs, rhs))| *actual == *lhs * rhs)
        );
    }

    #[test]
    fn repeated_subexpressions_use_squares() {
        check_repeated_subexpressions_use_squares::<pallas::Base, LagrangeCoeff>();
        check_repeated_subexpressions_use_squares::<pallas::Base, ExtendedLagrangeCoeff>();
        check_repeated_subexpressions_use_squares::<vesta::Base, LagrangeCoeff>();
        check_repeated_subexpressions_use_squares::<vesta::Base, ExtendedLagrangeCoeff>();
    }

    fn check_repeated_squares_are_cached<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
    {
        let domain = EvaluationDomain::new(3, 4);
        let mut values = domain.empty_extended();
        for (index, value) in values.iter_mut().enumerate() {
            *value = F::from(index as u64 + 3);
        }

        let mut evaluator = new_evaluator::<_, _, ExtendedLagrangeCoeff>(|| {});
        let leaf = evaluator.register_poly(values.clone());
        let value = Ast::from(leaf);
        let square = value.clone() * value;
        let ast = square.clone() + square;

        let (mut plan, scalars) = compile_plan(&ast);
        assert_eq!(
            plan.cache_common_subexpressions(LinearTermCacheBudget::default(), &scalars),
            1
        );
        match plan {
            EvaluationPlan::Add(lhs, rhs) => match (*lhs, *rhs) {
                (
                    EvaluationPlan::CacheStore { slot, inner },
                    EvaluationPlan::CacheLoad { slot: loaded },
                ) => {
                    assert_eq!(slot, loaded);
                    assert!(matches!(*inner, EvaluationPlan::Square(_)));
                }
                _ => panic!("repeated square uses one cache store and one cache load"),
            },
            _ => panic!("repeated square preserves the addition plan"),
        }

        let actual = evaluator.evaluate(&ast, &domain);
        assert!(
            actual
                .iter()
                .zip(values.iter())
                .all(|(actual, value)| *actual == value.square().double())
        );
    }

    #[test]
    fn repeated_squares_are_cached() {
        check_repeated_squares_are_cached::<pallas::Base>();
        check_repeated_squares_are_cached::<vesta::Base>();
    }

    #[test]
    fn retained_cache_layout_is_validated_against_the_current_plan() {
        let domain = EvaluationDomain::new(3, 4);
        let mut values = domain.empty_extended();
        for (index, value) in values.iter_mut().enumerate() {
            *value = pallas::Base::from(index as u64 + 3);
        }

        let mut evaluator = new_evaluator::<_, _, ExtendedLagrangeCoeff>(|| {});
        let leaf = evaluator.register_poly(values);
        let repeated = |constant| {
            let value = Ast::from(leaf) + Ast::ConstantTerm(pallas::Base::from(constant));
            value.clone() * value
        };
        let original = repeated(7) + repeated(7);

        let mut planner = new_virtual_evaluator::<_, pallas::Base, ExtendedLagrangeCoeff>(|| {});
        let virtual_leaf = planner.register_virtual_poly();
        let virtual_repeated = |constant| {
            let value = Ast::from(virtual_leaf) + Ast::ConstantTerm(pallas::Base::from(constant));
            value.clone() * value
        };
        let virtual_original = virtual_repeated(7) + virtual_repeated(7);
        let eager_layout = planner
            .prepare_cache_layout(&virtual_original, domain.extended_len())
            .expect("topology-only planning prepares a layout");
        let expected = evaluator.evaluate(&original, &domain);
        let (actual, replacement) =
            evaluator.evaluate_with_cache_layout(&original, &domain, Some(&eager_layout));
        assert_eq!(&actual[..], &expected[..]);
        assert!(replacement.is_none());

        let (_, layout) = evaluator.evaluate_with_cache_layout(&original, &domain, None);
        let layout = layout.expect("the cold evaluation prepares a layout");
        assert!(!layout.events.is_empty());

        // Challenge-bound scalar values may differ between proofs. The
        // retained events remain valid because their current-plan store and
        // load shapes still compare exactly.
        let matching = repeated(11) + repeated(11);
        let expected = evaluator.evaluate(&matching, &domain);
        let (actual, replacement) =
            evaluator.evaluate_with_cache_layout(&matching, &domain, Some(&layout));
        assert_eq!(&actual[..], &expected[..]);
        assert!(replacement.is_none());

        // The same occurrence count is insufficient: a different load shape
        // invalidates the retained layout and safely falls back to planning.
        let mismatched = repeated(13) + repeated(17);
        let expected = evaluator.evaluate(&mismatched, &domain);
        let (actual, replacement) =
            evaluator.evaluate_with_cache_layout(&mismatched, &domain, Some(&layout));
        assert_eq!(&actual[..], &expected[..]);
        assert!(replacement.is_some());
    }

    #[test]
    fn compiled_plan_rebinds_challenges_and_rejects_a_shape_mismatch() {
        type F = pallas::Base;

        fn context() {}

        fn expressions(
            leaf: AstLeaf<fn(), ExtendedLagrangeCoeff>,
        ) -> Vec<Ast<fn(), F, ExtendedLagrangeCoeff>> {
            vec![
                Ast::from(leaf) * Ast::ChallengeTerm(EvaluationChallenge::Theta)
                    + Ast::ChallengeTerm(EvaluationChallenge::Beta),
                Ast::LinearChallengeTerm {
                    challenge: EvaluationChallenge::Beta,
                    factor: F::from(3),
                } + Ast::ChallengeTerm(EvaluationChallenge::Gamma),
            ]
        }

        fn expected(
            evaluator: &Evaluator<'_, fn(), F, ExtendedLagrangeCoeff>,
            domain: &EvaluationDomain<F>,
            leaf: AstLeaf<fn(), ExtendedLagrangeCoeff>,
            challenges: EvaluationChallenges<F>,
        ) -> Polynomial<F, ExtendedLagrangeCoeff> {
            evaluator.evaluate(
                &Ast::distribute_powers(
                    [
                        Ast::from(leaf) * Ast::ConstantTerm(challenges.theta)
                            + Ast::ConstantTerm(challenges.beta),
                        Ast::LinearTerm(challenges.beta * F::from(3))
                            + Ast::ConstantTerm(challenges.gamma),
                    ],
                    challenges.y,
                ),
                domain,
            )
        }

        let domain = EvaluationDomain::new(3, 4);
        let mut values = domain.empty_extended();
        for (index, value) in values.iter_mut().enumerate() {
            *value = F::from(index as u64 + 11);
        }

        let value_tag = EvaluationPolyTag::new(0, 0, 0);
        let mut evaluator = new_evaluator::<fn(), _, ExtendedLagrangeCoeff>(context);
        let leaf = evaluator.register_poly_with_tag(values.clone(), value_tag);
        // Deliberately collide the concrete challenge values. The compiled
        // plan must retain their distinct symbolic provenance.
        let first_challenges = EvaluationChallenges {
            theta: F::from(7),
            beta: F::from(7),
            gamma: F::from(7),
            y: F::from(7),
        };
        let (first, plan) = evaluator.evaluate_quotient_with_compiled_plan(
            expressions(leaf),
            &domain,
            None,
            first_challenges,
        );
        assert_eq!(
            &first[..],
            &expected(&evaluator, &domain, leaf, first_challenges)[..]
        );
        let plan = plan.expect("the cold evaluation returns a compiled plan");

        let second_challenges = EvaluationChallenges {
            theta: F::from(11),
            beta: F::from(13),
            gamma: F::from(17),
            y: F::from(19),
        };
        let (second, replacement) = evaluator.evaluate_quotient_with_compiled_plan(
            std::iter::empty(),
            &domain,
            Some(&plan),
            second_challenges,
        );
        assert_eq!(
            &second[..],
            &expected(&evaluator, &domain, leaf, second_challenges)[..]
        );
        assert_ne!(&second[..], &first[..]);
        assert!(replacement.is_none());

        for value in [F::ZERO, F::ONE, F::from(2), -F::ONE] {
            let colliding_challenges = EvaluationChallenges {
                theta: value,
                beta: value,
                gamma: value,
                y: value,
            };
            let (actual, replacement) = evaluator.evaluate_quotient_with_compiled_plan(
                std::iter::empty(),
                &domain,
                Some(&plan),
                colliding_challenges,
            );
            assert_eq!(
                &actual[..],
                &expected(&evaluator, &domain, leaf, colliding_challenges)[..]
            );
            assert!(replacement.is_none());
        }

        let third_challenges = EvaluationChallenges {
            theta: F::from(23),
            beta: F::from(29),
            gamma: F::from(31),
            y: F::from(37),
        };
        let (concurrent_second, concurrent_third) = std::thread::scope(|scope| {
            let second = scope.spawn(|| {
                evaluator
                    .evaluate_quotient_with_compiled_plan(
                        std::iter::empty(),
                        &domain,
                        Some(&plan),
                        second_challenges,
                    )
                    .0
            });
            let third = scope.spawn(|| {
                evaluator
                    .evaluate_quotient_with_compiled_plan(
                        std::iter::empty(),
                        &domain,
                        Some(&plan),
                        third_challenges,
                    )
                    .0
            });
            (second.join().unwrap(), third.join().unwrap())
        });
        assert_eq!(&concurrent_second[..], &second[..]);
        assert_eq!(
            &concurrent_third[..],
            &expected(&evaluator, &domain, leaf, third_challenges)[..]
        );

        let mut mismatched = new_evaluator::<fn(), _, ExtendedLagrangeCoeff>(context);
        let mismatched_leaf = mismatched.register_poly_with_tag(values.clone(), value_tag);
        mismatched.register_poly_with_tag(values, EvaluationPolyTag::new(1, 0, 0));
        let (actual, replacement) = mismatched.evaluate_quotient_with_compiled_plan(
            expressions(mismatched_leaf),
            &domain,
            Some(&plan),
            second_challenges,
        );
        assert_eq!(
            &actual[..],
            &expected(&mismatched, &domain, mismatched_leaf, second_challenges,)[..]
        );
        assert!(replacement.is_some());
    }

    #[test]
    fn compiled_plan_rejects_swapped_polynomial_tags() {
        type F = pallas::Base;

        fn context() {}

        fn expressions(
            lhs: AstLeaf<fn(), ExtendedLagrangeCoeff>,
            rhs: AstLeaf<fn(), ExtendedLagrangeCoeff>,
        ) -> [Ast<fn(), F, ExtendedLagrangeCoeff>; 1] {
            [Ast::from(lhs) * rhs + lhs]
        }

        let domain = EvaluationDomain::new(3, 4);
        let mut lhs_values = domain.empty_extended();
        let mut rhs_values = domain.empty_extended();
        for (index, (lhs, rhs)) in lhs_values.iter_mut().zip(rhs_values.iter_mut()).enumerate() {
            *lhs = F::from(index as u64 + 3);
            *rhs = F::from(index as u64 + 41);
        }
        let lhs_tag = EvaluationPolyTag::new(0, 0, 0);
        let rhs_tag = EvaluationPolyTag::new(1, 0, 0);
        let challenges =
            EvaluationChallenges::new(F::from(5), F::from(7), F::from(11), F::from(13));

        let mut original = new_evaluator::<fn(), _, ExtendedLagrangeCoeff>(context);
        let lhs = original.register_poly_with_tag(lhs_values.clone(), lhs_tag);
        let rhs = original.register_poly_with_tag(rhs_values.clone(), rhs_tag);
        let (_, plan) = original.evaluate_quotient_with_compiled_plan(
            expressions(lhs, rhs),
            &domain,
            None,
            challenges,
        );
        let plan = plan.expect("the cold evaluation returns a compiled plan");

        let mut swapped = new_evaluator::<fn(), _, ExtendedLagrangeCoeff>(context);
        let lhs = swapped.register_poly_with_tag(lhs_values.clone(), rhs_tag);
        let rhs = swapped.register_poly_with_tag(rhs_values.clone(), lhs_tag);
        let (expected, _) = swapped.evaluate_quotient_with_compiled_plan(
            expressions(lhs, rhs),
            &domain,
            None,
            challenges,
        );
        let (actual, replacement) = swapped.evaluate_quotient_with_compiled_plan(
            expressions(lhs, rhs),
            &domain,
            Some(&plan),
            challenges,
        );
        assert_eq!(&actual[..], &expected[..]);
        assert!(replacement.is_some());

        let mut untagged = new_evaluator::<fn(), _, ExtendedLagrangeCoeff>(context);
        let untagged_lhs = untagged.register_poly(lhs_values);
        let untagged_rhs = untagged.register_poly(rhs_values);
        assert!(!untagged.accepts_compiled_plan(&plan));
        let (_, replacement) = untagged.evaluate_quotient_with_compiled_plan(
            expressions(untagged_lhs, untagged_rhs),
            &domain,
            Some(&plan),
            challenges,
        );
        assert!(replacement.is_none());
    }

    #[test]
    fn compiled_plan_rejects_a_compressed_selector_shape_mismatch() {
        type F = pallas::Base;
        const ORIGINAL_COMBINATION_LEN: usize = 4;
        const MISMATCHED_COMBINATION_LEN: usize = 5;

        fn context() {}

        let domain = EvaluationDomain::new(3, 4);
        let mut query_values = domain.empty_extended();
        let mut selector_values = domain.empty_extended();
        for (index, (query, selector)) in query_values
            .iter_mut()
            .zip(selector_values.iter_mut())
            .enumerate()
        {
            *query = F::from(index as u64 + 3);
            *selector = F::from(index as u64 + 37);
        }

        let challenges = EvaluationChallenges {
            theta: F::from(3),
            beta: F::from(5),
            gamma: F::from(7),
            y: F::from(11),
        };
        let query_tag = EvaluationPolyTag::new(0, 0, 0);
        let selector_tag = EvaluationPolyTag::new(1, 0, 0);
        let mut original = new_evaluator::<fn(), _, ExtendedLagrangeCoeff>(context);
        let original_query = original.register_poly_with_tag(query_values.clone(), query_tag);
        let original_selector =
            original.register_poly_with_tag(selector_values.clone(), selector_tag);
        original.register_compressed_selector(
            original_query,
            ORIGINAL_COMBINATION_LEN,
            1,
            original_selector,
        );
        let (_, plan) = original.evaluate_quotient_with_compiled_plan(
            [compressed_selector_expression(
                original_query,
                ORIGINAL_COMBINATION_LEN,
                1,
            )],
            &domain,
            None,
            challenges,
        );
        let plan = plan.expect("the cold evaluation returns a compiled plan");

        // Keep polynomial count and lengths identical while changing only the
        // compressed-selector mapping retained by the evaluator.
        let mut mismatched = new_evaluator::<fn(), _, ExtendedLagrangeCoeff>(context);
        let mismatched_query = mismatched.register_poly_with_tag(query_values, query_tag);
        let mismatched_selector = mismatched.register_poly_with_tag(selector_values, selector_tag);
        mismatched.register_compressed_selector(
            mismatched_query,
            MISMATCHED_COMBINATION_LEN,
            1,
            mismatched_selector,
        );
        let (actual, replacement) = mismatched.evaluate_quotient_with_compiled_plan(
            [compressed_selector_expression(
                mismatched_query,
                MISMATCHED_COMBINATION_LEN,
                1,
            )],
            &domain,
            Some(&plan),
            challenges,
        );
        let expected = mismatched.evaluate(&Ast::from(mismatched_selector), &domain);
        assert_eq!(&actual[..], &expected[..]);
        assert!(replacement.is_some());
    }

    fn check_nested_arithmetic_and_linear_common_subexpressions_are_cached<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
    {
        let domain = EvaluationDomain::new(3, 4);
        let mut evaluator = new_evaluator::<_, _, ExtendedLagrangeCoeff>(|| {});
        let mut values = vec![];
        let leaves = (0..4)
            .map(|poly_index| {
                let mut poly = domain.empty_extended();
                let poly_len = poly.len();
                for (row, value) in poly.iter_mut().enumerate() {
                    *value = F::from((poly_index * poly_len + row + 1) as u64);
                }
                values.push(poly.clone());
                evaluator.register_poly(poly)
            })
            .collect::<Vec<_>>();

        let repeated = (Ast::from(leaves[0]) + leaves[1]) * (Ast::from(leaves[2]) + leaves[3]);
        let linear_scalar = F::from(13);
        let terms = (5..9)
            .map(|constant| {
                repeated.clone()
                    + Ast::ConstantTerm(F::from(constant))
                    + Ast::LinearTerm(linear_scalar)
            })
            .collect::<Vec<_>>();
        let base = F::from(11);
        let ast = Ast::distribute_powers(terms.clone(), base);

        let (mut plan, scalars) = compile_plan(&ast);
        assert_eq!(
            plan.cache_common_subexpressions(
                linear_term_cache_budget::<F, ExtendedLagrangeCoeff>(values[0].len()),
                &scalars
            ),
            2
        );

        let (mut single_saved_multiplication, single_scalars) =
            compile_plan(&Ast::distribute_powers(terms.into_iter().take(2), base));
        assert_eq!(
            single_saved_multiplication
                .cache_common_subexpressions(LinearTermCacheBudget::default(), &single_scalars),
            1
        );

        let repeated_copy = Ast::from(leaves[0]);
        let (mut copy_only, copy_scalars) = compile_plan(&Ast::distribute_powers(
            [repeated_copy.clone(), repeated_copy],
            base,
        ));
        assert_eq!(
            copy_only.cache_common_subexpressions(LinearTermCacheBudget::default(), &copy_scalars,),
            0
        );

        let actual = evaluator.evaluate(&ast, &domain);
        let mut linear_value = linear_scalar * F::ZETA;
        for row in 0..actual.len() {
            let repeated = (values[0][row] + values[1][row]) * (values[2][row] + values[3][row]);
            let expected = (5..9).fold(F::ZERO, |accumulator, constant| {
                accumulator * base + repeated + F::from(constant) + linear_value
            });
            assert_eq!(actual[row], expected);
            linear_value *= domain.get_extended_omega();
        }
    }

    #[test]
    fn nested_arithmetic_and_linear_common_subexpressions_are_cached() {
        check_nested_arithmetic_and_linear_common_subexpressions_are_cached::<pallas::Base>();
        check_nested_arithmetic_and_linear_common_subexpressions_are_cached::<vesta::Base>();
    }

    #[test]
    fn repeated_linear_terms_respect_cache_limits() {
        fn repeated_terms() -> Ast<fn(), pallas::Base, ExtendedLagrangeCoeff> {
            let scalars = [2, 3, 5].map(pallas::Base::from);
            Ast::distribute_powers(
                scalars.into_iter().chain(scalars).map(Ast::LinearTerm),
                pallas::Base::from(7),
            )
        }

        for (limit, expected_slots) in [(0, 0), (1, 1), (2, 2), (3, 3), (8, 3)] {
            let (mut plan, scalars) = compile_plan(&repeated_terms());
            assert_eq!(
                plan.cache_common_subexpressions(
                    LinearTermCacheBudget {
                        max_entries: limit,
                        max_additional_slots: limit,
                    },
                    &scalars
                ),
                expected_slots
            );
        }
    }

    #[test]
    fn repeated_linear_terms_prefer_more_reuse() {
        let less_reused = pallas::Base::from(2);
        let more_reused = pallas::Base::from(3);
        let ast: Ast<fn(), _, ExtendedLagrangeCoeff> = Ast::distribute_powers(
            [
                less_reused,
                more_reused,
                more_reused,
                less_reused,
                more_reused,
            ]
            .map(Ast::LinearTerm),
            pallas::Base::from(5),
        );
        let (mut plan, scalars) = compile_plan(&ast);
        assert_eq!(
            plan.cache_common_subexpressions(
                LinearTermCacheBudget {
                    max_entries: 1,
                    max_additional_slots: 1,
                },
                &scalars
            ),
            1
        );

        let stored_scalar = match plan {
            EvaluationPlan::DistributePowers { work, .. } => work.into_iter().find_map(|work| {
                if let DistributionWork::Term {
                    term: EvaluationPlan::CacheStore { inner, .. },
                    ..
                } = work
                {
                    if let EvaluationPlan::LinearTerm(scalar) = *inner {
                        return Some(scalar);
                    }
                }
                None
            }),
            _ => None,
        };
        assert_eq!(
            stored_scalar.map(|scalar| plan_scalar(&scalars, scalar)),
            Some(PlanScalar::Literal(more_reused))
        );
    }

    fn check_repeated_linear_term_evaluation<F, B>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
        B: BasisOps,
    {
        fn context() {}

        let domain = EvaluationDomain::new(3, 4);
        let mut evaluator = new_evaluator::<fn(), F, B>(context);
        evaluator.register_poly(B::empty_poly(&domain));

        let second = F::from(3);
        let base = F::from(5);
        for first in [F::ZERO, F::from(2)] {
            let scalars = [first, second, first, second];
            let ast = Ast::distribute_powers(scalars.map(Ast::LinearTerm), base);
            let actual = evaluator.evaluate(&ast, &domain);
            let direct =
                [first, second].map(|scalar| evaluator.evaluate(&Ast::LinearTerm(scalar), &domain));

            for (row, actual) in actual.iter().enumerate() {
                let expected = scalars.iter().fold(F::ZERO, |accumulator, scalar| {
                    let direct = if *scalar == first {
                        direct[0][row]
                    } else {
                        direct[1][row]
                    };
                    accumulator * base + direct
                });
                assert_eq!(*actual, expected);
            }
        }
    }

    #[test]
    fn repeated_linear_term_evaluation_matches_direct_values() {
        check_repeated_linear_term_evaluation::<pallas::Base, LagrangeCoeff>();
        check_repeated_linear_term_evaluation::<pallas::Base, ExtendedLagrangeCoeff>();
        check_repeated_linear_term_evaluation::<vesta::Base, LagrangeCoeff>();
        check_repeated_linear_term_evaluation::<vesta::Base, ExtendedLagrangeCoeff>();
    }

    #[test]
    fn linear_term_cache_budget_is_bounded_to_evaluation_bases() {
        // Orchard's k = 11 quotient evaluation uses a 2^14-row extended
        // domain, so each Pasta-field slot retains 512 KiB.
        let poly_len = 1 << 14;
        let bytes_per_slot = poly_len * std::mem::size_of::<pallas::Base>();
        let expected_additional_slots = (MAX_ADDITIONAL_LINEAR_TERM_CACHE_BYTES / bytes_per_slot)
            .min(MAX_LINEAR_TERM_CACHE_ENTRIES);
        assert_eq!(expected_additional_slots, 8);

        assert_eq!(
            linear_term_cache_budget::<pallas::Base, Coeff>(poly_len).max_entries,
            0,
        );
        for budget in [
            linear_term_cache_budget::<pallas::Base, LagrangeCoeff>(poly_len),
            linear_term_cache_budget::<pallas::Base, ExtendedLagrangeCoeff>(poly_len),
        ] {
            assert_eq!(budget.max_entries, MAX_LINEAR_TERM_CACHE_ENTRIES);
            assert_eq!(budget.max_additional_slots, expected_additional_slots);
            assert!(
                budget.max_additional_slots * bytes_per_slot
                    <= MAX_ADDITIONAL_LINEAR_TERM_CACHE_BYTES
            );
        }

        let overflow = linear_term_cache_budget::<pallas::Base, ExtendedLagrangeCoeff>(usize::MAX);
        assert_eq!(overflow.max_entries, MAX_LINEAR_TERM_CACHE_ENTRIES);
        assert_eq!(overflow.max_additional_slots, 0);
    }

    #[test]
    fn cache_slots_are_reused_after_their_last_load() {
        let mut actions = vec![None; 6];
        actions[0] = Some(CacheAction {
            slot: 0,
            store: true,
            end: 1,
        });
        actions[1] = Some(CacheAction {
            slot: 1,
            store: true,
            end: 2,
        });
        actions[2] = Some(CacheAction {
            slot: 0,
            store: false,
            end: 3,
        });
        actions[3] = Some(CacheAction {
            slot: 2,
            store: true,
            end: 4,
        });
        actions[4] = Some(CacheAction {
            slot: 2,
            store: false,
            end: 5,
        });
        actions[5] = Some(CacheAction {
            slot: 1,
            store: false,
            end: 6,
        });

        assert_eq!(reuse_cache_slots(&mut actions, 3), 2);
        assert_eq!(actions[0].unwrap().slot, actions[2].unwrap().slot);
        assert_eq!(actions[3].unwrap().slot, actions[4].unwrap().slot);
        assert_eq!(actions[0].unwrap().slot, actions[3].unwrap().slot);
        assert_ne!(actions[0].unwrap().slot, actions[1].unwrap().slot);
    }

    #[test]
    fn linear_term_cache_reuses_free_lifetime_gaps() {
        let mut actions = vec![None; 8];
        actions[0] = Some(CacheAction {
            slot: 0,
            store: true,
            end: 1,
        });
        actions[7] = Some(CacheAction {
            slot: 0,
            store: false,
            end: 8,
        });
        actions[2] = Some(CacheAction {
            slot: 1,
            store: true,
            end: 3,
        });
        actions[3] = Some(CacheAction {
            slot: 1,
            store: false,
            end: 4,
        });

        let mut occupancy = LinearTermCacheOccupancy::new(
            &actions,
            2,
            LinearTermCacheBudget {
                max_entries: 2,
                max_additional_slots: 0,
            },
        );
        assert!(occupancy.try_reserve(4, 5));
        assert!(!occupancy.try_reserve(5, 6));
    }

    #[test]
    fn linear_term_cache_prunes_physical_slots_beyond_byte_budget() {
        let bytes_per_slot = MAX_ADDITIONAL_LINEAR_TERM_CACHE_BYTES / 2;
        let poly_len = bytes_per_slot / std::mem::size_of::<pallas::Base>();
        let budget = linear_term_cache_budget::<pallas::Base, ExtendedLagrangeCoeff>(poly_len);
        assert_eq!(budget.max_additional_slots, 2);

        let mut occupancy = LinearTermCacheOccupancy::new(&[None; 5], 0, budget);
        assert!(occupancy.try_reserve(0, 4));
        assert!(occupancy.try_reserve(1, 3));
        assert!(!occupancy.try_reserve(2, 2));
    }

    #[test]
    fn extended_shared_factors_support_nested_rotated_bodies() {
        let domain = EvaluationDomain::new(5, 4);
        let mut polys = (0..4)
            .map(|poly_index| {
                let mut poly = domain.empty_extended();
                let poly_len = poly.len();
                for (row, value) in poly.iter_mut().enumerate() {
                    *value = pallas::Base::from((poly_index * poly_len + row + 1) as u64);
                }
                poly
            })
            .collect::<Vec<_>>();

        let a_prev = domain.rotate_extended(&polys[0], Rotation::prev());
        let b_next = domain.rotate_extended(&polys[1], Rotation::next());
        let c_cur = polys[2].clone();
        let c_prev = domain.rotate_extended(&polys[2], Rotation::prev());
        let c_next = domain.rotate_extended(&polys[2], Rotation::next());
        let d_cur = polys[3].clone();
        let d_prev = domain.rotate_extended(&polys[3], Rotation::prev());
        let d_next = domain.rotate_extended(&polys[3], Rotation::next());

        let mut evaluator = new_evaluator::<_, _, ExtendedLagrangeCoeff>(|| {});
        let a = evaluator.register_poly(polys.remove(0));
        let b = evaluator.register_poly(polys.remove(0));
        let c = evaluator.register_poly(polys.remove(0));
        let d = evaluator.register_poly(polys.remove(0));

        let factor =
            Ast::from(a.with_rotation(Rotation::prev())) + b.with_rotation(Rotation::next());
        let body_a = (Ast::from(c.with_rotation(Rotation::prev()))
            + d.with_rotation(Rotation::next()))
            * (Ast::from(c.with_rotation(Rotation::next())) - d.with_rotation(Rotation::prev()));
        let body_base = pallas::Base::from(13);
        let body_b = Ast::distribute_powers(
            [
                Ast::from(c) * d,
                Ast::from(c.with_rotation(Rotation::prev())) + d.with_rotation(Rotation::next()),
                Ast::ConstantTerm(pallas::Base::from(7)),
            ],
            body_base,
        );
        let outer_base = pallas::Base::from(19);
        let left = Ast::distribute_powers(
            [
                factor.clone() * body_a.clone(),
                factor.clone() * body_b.clone(),
            ],
            outer_base,
        );
        let right = Ast::distribute_powers([body_a * factor.clone(), body_b * factor], outer_base);

        let actual_left = evaluator.evaluate(&left, &domain);
        let actual_right = evaluator.evaluate(&right, &domain);
        for row in 0..actual_left.len() {
            let factor = a_prev[row] + b_next[row];
            let body_a = (c_prev[row] + d_next[row]) * (c_next[row] - d_prev[row]);
            let body_b = (c_cur[row] * d_cur[row] * body_base + c_prev[row] + d_next[row])
                * body_base
                + pallas::Base::from(7);
            let expected = factor * body_a * outer_base + factor * body_b;
            assert_eq!(actual_left[row], expected);
            assert_eq!(actual_right[row], expected);
        }
    }

    fn check_shared_factor_groups<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
    {
        let domain = EvaluationDomain::new(1, 3);
        let factor_a_values = [2_u64, 3, 5, 7, 11, 13, 17, 19].map(F::from);
        let factor_b_values = [23_u64, 29, 31, 37, 41, 43, 47, 53].map(F::from);
        let body_values = [
            [59_u64, 61, 67, 71, 73, 79, 83, 89],
            [97, 101, 103, 107, 109, 113, 127, 131],
            [137, 139, 149, 151, 157, 163, 167, 173],
            [179, 181, 191, 193, 197, 199, 211, 223],
            [227, 229, 233, 239, 241, 251, 257, 263],
            [269, 271, 277, 281, 283, 293, 307, 311],
        ]
        .map(|values| values.map(F::from));

        let mut evaluator = new_evaluator::<_, _, LagrangeCoeff>(|| {});
        let factor_a = evaluator.register_poly(domain.lagrange_from_vec(factor_a_values.to_vec()));
        let factor_b = evaluator.register_poly(domain.lagrange_from_vec(factor_b_values.to_vec()));
        let bodies = body_values
            .iter()
            .map(|values| evaluator.register_poly(domain.lagrange_from_vec(values.to_vec())))
            .collect::<Vec<_>>();

        let common_factor =
            Ast::from(factor_a) * (Ast::ConstantTerm(F::from(2)) - Ast::from(factor_b));
        let terms = vec![
            common_factor.clone() * Ast::from(bodies[0]),
            common_factor.clone() * Ast::from(bodies[1]),
            Ast::from(factor_b) * Ast::from(bodies[2]),
            common_factor.clone() * Ast::from(bodies[3]),
            common_factor.clone() * Ast::from(bodies[4]),
            common_factor.clone() * Ast::from(bodies[5]),
        ];

        let right_terms = bodies
            .iter()
            .take(4)
            .map(|body| Ast::from(*body) * common_factor.clone())
            .collect::<Vec<_>>();

        let base = F::from(9);
        let planned_ast = Ast::distribute_powers(terms.clone(), base);
        let (plan, scalars) = compile_plan(&planned_ast);
        let work = match plan {
            EvaluationPlan::DistributePowers { work, .. } => work,
            _ => panic!("multiple terms compile to distributed work"),
        };
        match work.as_slice() {
            [
                DistributionWork::WeightedSharedFactor { terms, .. },
                DistributionWork::Term {
                    power: middle_power,
                    ..
                },
            ] => {
                assert_eq!(terms.len(), 5);
                assert_eq!(
                    plan_scalar(&scalars, terms[0].power),
                    PlanScalar::Literal(base.pow_vartime([5]))
                );
                assert_eq!(
                    plan_scalar(&scalars, terms[1].power),
                    PlanScalar::Literal(base.pow_vartime([4]))
                );
                assert_eq!(
                    plan_scalar(&scalars, terms[2].power),
                    PlanScalar::Literal(base.square())
                );
                assert_eq!(
                    plan_scalar(&scalars, terms[3].power),
                    PlanScalar::Literal(base)
                );
                assert_eq!(
                    plan_scalar(&scalars, terms[4].power),
                    PlanScalar::Literal(F::ONE)
                );
                assert_eq!(
                    plan_scalar(&scalars, *middle_power),
                    PlanScalar::Literal(base * base * base)
                );
            }
            _ => panic!("disjoint runs sharing a factor compile to shared work"),
        }

        for base in [F::ZERO, F::ONE, F::from(9)] {
            let actual = evaluator.evaluate(&Ast::distribute_powers(terms.clone(), base), &domain);
            let actual_right =
                evaluator.evaluate(&Ast::distribute_powers(right_terms.clone(), base), &domain);
            for row in 0..actual.len() {
                let common_factor = factor_a_values[row] * (F::from(2) - factor_b_values[row]);
                let factors = [
                    common_factor,
                    common_factor,
                    factor_b_values[row],
                    common_factor,
                    common_factor,
                    common_factor,
                ];
                let expected = factors
                    .iter()
                    .zip(body_values.iter())
                    .fold(F::ZERO, |accumulator, (factor, body)| {
                        accumulator * base + *factor * body[row]
                    });
                assert_eq!(actual[row], expected);

                let expected_right = body_values[..4].iter().fold(F::ZERO, |accumulator, body| {
                    accumulator * base + body[row] * common_factor
                });
                assert_eq!(actual_right[row], expected_right);
            }
        }
    }

    #[test]
    fn shared_factor_groups_match_generic_evaluation() {
        check_shared_factor_groups::<pallas::Base>();
        check_shared_factor_groups::<vesta::Base>();
    }

    fn check_nested_shared_factor_groups<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
    {
        let domain = EvaluationDomain::new(1, 3);
        let raw_values = (0..10)
            .map(|column| {
                (0..8)
                    .map(|row| F::from((column + 2) * (row + 3) + 1))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut evaluator = new_evaluator::<_, F, LagrangeCoeff>(|| {});
        let leaves = raw_values
            .iter()
            .map(|values| evaluator.register_poly(domain.lagrange_from_vec(values.clone())))
            .collect::<Vec<_>>();

        let selector = Ast::from(leaves[0]);
        let left_factor = (Ast::from(leaves[1]) + Ast::from(leaves[2])) * Ast::from(leaves[3]);
        let right_factor = Ast::from(leaves[8]) * (Ast::from(leaves[9]) + Ast::from(leaves[7]));
        let bodies = vec![
            left_factor.clone() * Ast::from(leaves[5]),
            left_factor.clone() * Ast::from(leaves[6]),
            Ast::from(leaves[2]) * Ast::from(leaves[7]),
            left_factor * Ast::from(leaves[8]),
            Ast::from(leaves[3]) * right_factor.clone(),
            Ast::from(leaves[4]) * right_factor,
        ];
        let terms = bodies
            .iter()
            .map(|body| selector.clone() * body.clone())
            .collect::<Vec<_>>();

        let base = F::from(13);
        let (plan, scalars) = compile_plan(&Ast::distribute_powers(terms.clone(), base));
        let weighted_terms = match &plan {
            EvaluationPlan::DistributePowers { work, .. } => match work.as_slice() {
                [DistributionWork::WeightedSharedFactor { terms, .. }] => terms,
                _ => panic!("the common outer factor should be planned"),
            },
            _ => panic!("multiple terms compile to distributed work"),
        };
        assert_eq!(weighted_terms.len(), 6);
        for (index, term) in weighted_terms.iter().enumerate() {
            assert_eq!(
                plan_scalar(&scalars, term.power),
                PlanScalar::Literal(base.pow_vartime([(5 - index) as u64]))
            );
        }

        for base in [F::ZERO, F::ONE, F::from(13)] {
            let actual = evaluator.evaluate(&Ast::distribute_powers(terms.clone(), base), &domain);
            for row in 0..actual.len() {
                let left_factor_value =
                    (raw_values[1][row] + raw_values[2][row]) * raw_values[3][row];
                let right_factor_value =
                    raw_values[8][row] * (raw_values[9][row] + raw_values[7][row]);
                let body_values = [
                    left_factor_value * raw_values[5][row],
                    left_factor_value * raw_values[6][row],
                    raw_values[2][row] * raw_values[7][row],
                    left_factor_value * raw_values[8][row],
                    raw_values[3][row] * right_factor_value,
                    raw_values[4][row] * right_factor_value,
                ];
                let expected = body_values.iter().fold(F::ZERO, |accumulator, body| {
                    accumulator * base + raw_values[0][row] * *body
                });
                assert_eq!(actual[row], expected);
            }
        }
    }

    #[test]
    fn nested_shared_factor_groups_preserve_challenge_powers() {
        check_nested_shared_factor_groups::<pallas::Base>();
        check_nested_shared_factor_groups::<vesta::Base>();
    }

    fn compressed_selector_expression<E: Copy, F: Field>(
        query: AstLeaf<E, ExtendedLagrangeCoeff>,
        combination_len: usize,
        assigned_root: usize,
    ) -> Ast<E, F, ExtendedLagrangeCoeff> {
        let mut expression = Ast::from(query);
        let mut root = F::ONE;
        for root_index in 1..=combination_len {
            if root_index != assigned_root {
                expression = expression * (Ast::ConstantTerm(root) - Ast::from(query));
            }
            root += F::ONE;
        }
        expression
    }

    #[test]
    fn compressed_selector_replacement_reuses_unchanged_subtrees() {
        const COMBINATION_LEN: usize = 4;

        let domain = EvaluationDomain::new(3, 3);
        let mut evaluator = new_evaluator::<_, pallas::Base, ExtendedLagrangeCoeff>(|| {});
        let query = evaluator.register_poly(domain.empty_extended());
        let selector = evaluator.register_poly(domain.empty_extended());
        let unrelated = evaluator.register_poly(domain.empty_extended());
        evaluator.register_compressed_selector(query, COMBINATION_LEN, 1, selector);

        let unchanged = Arc::new(Ast::from(unrelated) + Ast::ConstantTerm(pallas::Base::ONE));
        assert!(
            evaluator
                .replace_compressed_selectors(unchanged.as_ref())
                .is_none()
        );

        let ast = Ast::Add(
            Arc::new(compressed_selector_expression(query, COMBINATION_LEN, 1)),
            Arc::clone(&unchanged),
        );
        let replaced = evaluator
            .replace_compressed_selectors(&ast)
            .expect("the compressed selector should be replaced");

        match replaced {
            Ast::Add(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Ast::Poly(leaf) if *leaf == selector));
                assert!(Arc::ptr_eq(&rhs, &unchanged));
            }
            _ => panic!("the replacement should preserve the root addition"),
        }
    }

    #[test]
    fn compressed_selector_replacement_handles_every_ast_container() {
        const COMBINATION_LEN: usize = 4;

        let domain = EvaluationDomain::new(3, 3);
        let mut evaluator = new_evaluator::<_, pallas::Base, ExtendedLagrangeCoeff>(|| {});
        let query_and_first_selector = evaluator.register_poly(domain.empty_extended());
        let unrelated = evaluator.register_poly(domain.empty_extended());
        evaluator.register_compressed_selector(
            query_and_first_selector,
            COMBINATION_LEN,
            1,
            query_and_first_selector,
        );

        let compressed =
            || compressed_selector_expression(query_and_first_selector, COMBINATION_LEN, 1);
        let unrelated = || Ast::from(unrelated);
        let cases = [
            compressed(),
            Ast::Add(Arc::new(compressed()), Arc::new(unrelated())),
            Ast::Add(Arc::new(unrelated()), Arc::new(compressed())),
            Ast::Mul(AstMul(Arc::new(compressed()), Arc::new(unrelated()))),
            Ast::Mul(AstMul(Arc::new(unrelated()), Arc::new(compressed()))),
            Ast::Scale(Arc::new(compressed()), pallas::Base::from(5)),
            Ast::DistributePowers(
                Arc::new(vec![unrelated(), compressed()]),
                pallas::Base::from(7),
            ),
            Ast::DistributePowers(
                Arc::new(vec![compressed(), unrelated()]),
                pallas::Base::from(11),
            ),
        ];

        for case in cases {
            assert!(evaluator.replace_compressed_selectors(&case).is_some());
        }
    }

    #[test]
    #[should_panic(expected = "reused compressed-selector source was not replaced")]
    fn compressed_selector_replacement_rejects_unmatched_reused_source() {
        const COMBINATION_LEN: usize = 4;

        let domain = EvaluationDomain::new(3, 3);
        let mut evaluator = new_evaluator::<_, pallas::Base, ExtendedLagrangeCoeff>(|| {});
        let query_and_first_selector = evaluator.register_poly(domain.empty_extended());
        let unrelated = evaluator.register_poly(domain.empty_extended());
        evaluator.register_compressed_selector(
            query_and_first_selector,
            COMBINATION_LEN,
            1,
            query_and_first_selector,
        );

        evaluator.replace_compressed_selectors(&Ast::Add(
            Arc::new(Ast::from(unrelated)),
            Arc::new(Ast::from(
                query_and_first_selector.with_rotation(Rotation::next()),
            )),
        ));
    }

    fn compressed_selector_value<F: Field>(
        query: F,
        combination_len: usize,
        assigned_root: usize,
    ) -> F {
        let mut value = query;
        let mut root = F::ONE;
        for root_index in 1..=combination_len {
            if root_index != assigned_root {
                value *= root - query;
            }
            root += F::ONE;
        }
        value
    }

    fn check_compressed_selector_families<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
    {
        const COMBINATION_LEN: usize = 5;

        let domain = EvaluationDomain::new(3, 3);
        let mut query_poly = domain.empty_extended();
        for (row, value) in query_poly.iter_mut().enumerate() {
            *value = F::from((row % 11 + 1) as u64);
        }
        let query_values = domain
            .rotate_extended(&query_poly, Rotation::next())
            .to_vec();

        let mut body_polys = vec![];
        for body_index in 0..=COMBINATION_LEN {
            let mut body = domain.empty_extended();
            for (row, value) in body.iter_mut().enumerate() {
                *value = F::from((body_index * 17 + row * 3 + 2) as u64);
            }
            body_polys.push(body);
        }
        let body_values = body_polys
            .iter()
            .map(|body| body.to_vec())
            .collect::<Vec<_>>();

        let mut evaluator = new_evaluator::<_, F, ExtendedLagrangeCoeff>(|| {});
        let query = evaluator
            .register_poly(query_poly)
            .with_rotation(Rotation::next());
        let bodies = body_polys
            .into_iter()
            .map(|body| evaluator.register_poly(body))
            .collect::<Vec<_>>();

        for assigned_root in 1..=COMBINATION_LEN {
            let mut selector = domain.empty_extended();
            for (selector, query) in selector.iter_mut().zip(&query_values) {
                *selector = compressed_selector_value(*query, COMBINATION_LEN, assigned_root);
            }
            let selector = evaluator.register_poly(selector);
            evaluator.register_compressed_selector(query, COMBINATION_LEN, assigned_root, selector);
        }

        let mut terms = vec![];
        let mut control_terms = vec![];
        let mut term_inputs = vec![];
        for assigned_root in 1..=COMBINATION_LEN {
            let selector = compressed_selector_expression(query, COMBINATION_LEN, assigned_root);
            let parsed = compressed_selector(&selector, -F::ONE)
                .expect("the exact compressed-selector shape should be recognized");
            assert_eq!(parsed.1, COMBINATION_LEN);
            assert_eq!(parsed.2, assigned_root);

            let repetitions = if assigned_root == 2 { 2 } else { 1 };
            for repetition in 0..repetitions {
                let body_index = if repetition == 0 {
                    assigned_root - 1
                } else {
                    COMBINATION_LEN
                };
                let body = if repetition == 0 {
                    Ast::from(bodies[body_index])
                } else {
                    let inner = Ast::from(bodies[body_index]) + Ast::from(bodies[0]);
                    inner.clone() * inner
                };
                terms.push(selector.clone() * body.clone());
                control_terms.push((selector.clone() * Ast::ConstantTerm(F::ONE)) * body);
                term_inputs.push(Some((assigned_root, body_index, repetition != 0)));
            }
        }

        // Keep one unrelated term after the planned family to ensure that
        // every original challenge power is retained.
        terms.push(Ast::from(bodies[0]) + Ast::from(bodies[COMBINATION_LEN - 1]));
        control_terms.push(Ast::from(bodies[0]) + Ast::from(bodies[COMBINATION_LEN - 1]));
        term_inputs.push(None);

        let families = selector_family_matches(&terms, -F::ONE);
        assert_eq!(families.len(), 1);
        assert_eq!(families[0].combination_len, COMBINATION_LEN);
        assert_eq!(families[0].runs.len(), COMBINATION_LEN);
        assert_eq!(families[0].runs[1].end - families[0].runs[1].start, 2);
        assert!(selector_family_matches(&control_terms, -F::ONE).is_empty());

        let base = F::from(19);
        let planned_ast = Ast::distribute_powers(terms.clone(), base);
        let (plan, scalars) = compile_plan(&planned_ast);
        let work = match plan {
            EvaluationPlan::DistributePowers { work, .. } => work,
            _ => panic!("multiple terms compile to distributed work"),
        };
        assert_eq!(work.len(), 2);
        let runs = work
            .iter()
            .find_map(|work| match work {
                DistributionWork::SelectorFamily {
                    query: planned,
                    runs,
                } => {
                    assert_eq!(*planned, query.into());
                    Some(runs)
                }
                _ => None,
            })
            .expect("the complete selector family is planned");
        assert_eq!(runs.len(), COMBINATION_LEN);
        match &runs[1].bodies {
            FactorBodyPlan::Sequential(bodies) => {
                assert_eq!(bodies.len(), 2);
                assert!(matches!(&bodies[1], EvaluationPlan::Square(_)));
            }
            FactorBodyPlan::Factored(_) => panic!("unrelated bodies remain sequential"),
        }
        assert_eq!(
            plan_scalar(&scalars, runs[4].power),
            PlanScalar::Literal(base)
        );

        for base in [F::ZERO, F::ONE, F::from(19)] {
            let actual = evaluator.evaluate(&Ast::distribute_powers(terms.clone(), base), &domain);
            let control = evaluator.evaluate(
                &Ast::distribute_powers(control_terms.clone(), base),
                &domain,
            );
            assert_eq!(&actual[..], &control[..]);

            for row in 0..actual.len() {
                let expected = term_inputs.iter().fold(F::ZERO, |accumulator, input| {
                    let term = match input {
                        Some((assigned_root, body_index, squared)) => {
                            let mut body = body_values[*body_index][row];
                            if *squared {
                                body = (body + body_values[0][row]).square();
                            }
                            compressed_selector_value(
                                query_values[row],
                                COMBINATION_LEN,
                                *assigned_root,
                            ) * body
                        }
                        None => body_values[0][row] + body_values[COMBINATION_LEN - 1][row],
                    };
                    accumulator * base + term
                });
                assert_eq!(actual[row], expected);
            }
        }

        let nested_base = F::from(19);
        let outer_base = F::from(23);
        let factor = Ast::from(bodies[0]) + Ast::ConstantTerm(F::from(3));
        let nested = Ast::distribute_powers(terms.clone(), nested_base);
        let nested_control = Ast::distribute_powers(control_terms.clone(), nested_base);
        let candidate = Ast::distribute_powers(
            [
                factor.clone() * nested,
                factor.clone() * Ast::from(bodies[1]),
            ],
            outer_base,
        );
        let control = Ast::distribute_powers(
            [
                factor.clone() * nested_control,
                factor * Ast::from(bodies[1]),
            ],
            outer_base,
        );

        let (nested_plan, scalars) = compile_plan(&candidate);
        let shared_terms = match &nested_plan {
            EvaluationPlan::DistributePowers { work, .. } => work
                .iter()
                .find_map(|work| match work {
                    DistributionWork::WeightedSharedFactor { terms, .. } => Some(terms),
                    _ => None,
                })
                .expect("the outer shared factor is planned"),
            _ => panic!("the outer terms compile to distributed work"),
        };
        assert_eq!(shared_terms.len(), 2);
        assert_eq!(
            plan_scalar(&scalars, shared_terms[0].power),
            PlanScalar::Literal(outer_base)
        );
        assert_eq!(
            plan_scalar(&scalars, shared_terms[1].power),
            PlanScalar::Literal(F::ONE)
        );
        let nested_work = match &shared_terms[0].term {
            EvaluationPlan::DistributePowers { work, .. } => work,
            _ => panic!("the first shared-factor body is distributed work"),
        };
        assert!(
            nested_work
                .iter()
                .any(|work| matches!(work, DistributionWork::SelectorFamily { .. }))
        );
        // Five selector runs need eight slots. The outer shared factor uses
        // the distribution fold's buffers without adding scratch slots.
        assert_eq!(nested_plan.required_scratch_slots(), COMBINATION_LEN + 3);

        let actual = evaluator.evaluate(&candidate, &domain);
        let generic = evaluator.evaluate(&control, &domain);
        assert_eq!(&actual[..], &generic[..]);

        let incomplete = terms[..terms.len() - 2].to_vec();
        assert!(selector_family_matches(&incomplete, -F::ONE).is_empty());

        let right_hand = (1..=COMBINATION_LEN)
            .map(|assigned_root| {
                Ast::from(bodies[assigned_root - 1])
                    * compressed_selector_expression(query, COMBINATION_LEN, assigned_root)
            })
            .collect::<Vec<_>>();
        let right_hand_control = (1..=COMBINATION_LEN)
            .map(|assigned_root| {
                Ast::from(bodies[assigned_root - 1])
                    * (compressed_selector_expression(query, COMBINATION_LEN, assigned_root)
                        * Ast::ConstantTerm(F::ONE))
            })
            .collect::<Vec<_>>();
        let right_hand_families = selector_family_matches(&right_hand, -F::ONE);
        assert_eq!(right_hand_families.len(), 1);
        assert!(
            right_hand_families[0]
                .runs
                .iter()
                .all(|run| matches!(run.side, FactorSide::Right))
        );

        // Reverse the roots and put the unrelated term before the family to
        // exercise non-root run order and leading unclaimed terms.
        let reversed = terms.iter().cloned().rev().collect::<Vec<_>>();
        let reversed_control = control_terms.iter().cloned().rev().collect::<Vec<_>>();
        assert_eq!(selector_family_matches(&reversed, -F::ONE).len(), 1);
        for (candidate, control) in [
            (right_hand, right_hand_control),
            (reversed, reversed_control),
        ] {
            for base in [F::ZERO, F::ONE, F::from(19)] {
                let candidate =
                    evaluator.evaluate(&Ast::distribute_powers(candidate.clone(), base), &domain);
                let control =
                    evaluator.evaluate(&Ast::distribute_powers(control.clone(), base), &domain);
                assert_eq!(&candidate[..], &control[..]);
            }
        }

        let overlapping = (1..=COMBINATION_LEN)
            .map(|assigned_root| {
                compressed_selector_expression(query, COMBINATION_LEN, assigned_root)
                    * compressed_selector_expression(bodies[0], COMBINATION_LEN, assigned_root)
            })
            .collect::<Vec<_>>();
        // Both factors form complete families, but each term can be claimed
        // only once. Deterministically preferring the left family is safe.
        let overlapping_families = selector_family_matches(&overlapping, -F::ONE);
        assert_eq!(overlapping_families.len(), 1);
        assert_eq!(overlapping_families[0].query, query);

        let mut repeated_run = terms.clone();
        repeated_run
            .push(compressed_selector_expression(query, COMBINATION_LEN, 1) * Ast::from(bodies[0]));
        assert!(selector_family_matches(&repeated_run, -F::ONE).is_empty());

        let non_selector =
            Ast::from(query) * (Ast::ConstantTerm(F::ONE) + Ast::<_, F, _>::from(query));
        assert!(compressed_selector(&non_selector, -F::ONE).is_none());
    }

    fn check_orchard_selector_family_lengths<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64>,
    {
        let domain = EvaluationDomain::new(3, 3);
        let mut query_poly = domain.empty_extended();
        let mut body_poly = domain.empty_extended();
        for (row, (query, body)) in query_poly.iter_mut().zip(body_poly.iter_mut()).enumerate() {
            *query = F::from((row % 11 + 1) as u64);
            *body = F::from((row * 7 + 3) as u64);
        }

        let mut evaluator = new_evaluator::<_, F, ExtendedLagrangeCoeff>(|| {});
        let query = evaluator.register_poly(query_poly);
        let body = evaluator.register_poly(body_poly);

        // Orchard has compressed-selector families of lengths 4, 5, 6,
        // and 7. Exercise every product-tree shape used by the circuit.
        for combination_len in 4..=7 {
            let terms = (1..=combination_len)
                .map(|assigned_root| {
                    compressed_selector_expression(query, combination_len, assigned_root)
                        * Ast::from(body)
                })
                .collect::<Vec<_>>();
            let control_terms = (1..=combination_len)
                .map(|assigned_root| {
                    (compressed_selector_expression(query, combination_len, assigned_root)
                        * Ast::ConstantTerm(F::ONE))
                        * Ast::from(body)
                })
                .collect::<Vec<_>>();

            let families = selector_family_matches(&terms, -F::ONE);
            assert_eq!(families.len(), 1);
            assert_eq!(families[0].combination_len, combination_len);
            assert!(selector_family_matches(&control_terms, -F::ONE).is_empty());

            for base in [F::ZERO, F::ONE, F::from(19)] {
                let candidate =
                    evaluator.evaluate(&Ast::distribute_powers(terms.clone(), base), &domain);
                let control = evaluator.evaluate(
                    &Ast::distribute_powers(control_terms.clone(), base),
                    &domain,
                );
                assert_eq!(&candidate[..], &control[..]);
            }
        }
    }

    #[test]
    fn compressed_selector_families_match_generic_evaluation() {
        check_compressed_selector_families::<pallas::Base>();
        check_compressed_selector_families::<vesta::Base>();
        check_orchard_selector_family_lengths::<pallas::Base>();
        check_orchard_selector_family_lengths::<vesta::Base>();
    }
}
