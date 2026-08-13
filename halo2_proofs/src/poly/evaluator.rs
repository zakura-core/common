use std::{
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::{Add, Mul, MulAssign, Neg, Sub},
    sync::Arc,
};

use ff::WithSmallOrderMulGroup;
use group::ff::Field;

use super::{
    Basis, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation,
};
use crate::multicore;

/// Returns `(chunk_size, num_chunks)` suitable for processing the given polynomial length
/// in the current parallelization environment.
fn get_chunk_params(poly_len: usize) -> (usize, usize) {
    // Check the level of parallelization we have available.
    let num_threads = multicore::current_num_threads();
    // We scale the number of chunks by a constant factor, to ensure that if not all
    // threads are available, we can achieve more uniform throughput and don't end up
    // waiting on a couple of threads to process the last chunks.
    let num_chunks = num_threads * 4;
    // Calculate the ideal chunk size for the desired throughput. We use ceiling
    // division to ensure the minimum chunk size is 1.
    //     chunk_size = ceil(poly_len / num_chunks)
    let chunk_size = (poly_len + num_chunks - 1) / num_chunks;
    // Now re-calculate num_chunks from the actual chunk size.
    //     num_chunks = ceil(poly_len / chunk_size)
    let num_chunks = (poly_len + chunk_size - 1) / chunk_size;

    (chunk_size, num_chunks)
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
pub(crate) struct Evaluator<E, F: Field, B: Basis> {
    polys: Vec<Polynomial<F, B>>,
    _context: E,
}

/// Constructs a new `Evaluator`.
///
/// The `context` parameter is used to provide type safety for evaluators. It ensures that
/// an evaluator will only be used to evaluate [`Ast`]s containing [`AstLeaf`]s obtained
/// from itself. It should be set to the empty closure `|| {}`, because anonymous closures
/// all have unique types.
pub(crate) fn new_evaluator<E: Fn() + Clone, F: Field, B: Basis>(context: E) -> Evaluator<E, F, B> {
    Evaluator {
        polys: vec![],
        _context: context,
    }
}

fn required_scratch_slots<E, F: Field, B: Basis>(ast: &Ast<E, F, B>) -> usize {
    match ast {
        Ast::Poly(_) | Ast::LinearTerm(_) | Ast::ConstantTerm(_) => 0,
        Ast::Add(lhs, rhs) | Ast::Mul(AstMul(lhs, rhs)) => {
            required_scratch_slots(lhs).max(1 + required_scratch_slots(rhs))
        }
        Ast::Scale(inner, _) => required_scratch_slots(inner),
        Ast::DistributePowers(terms, _) => {
            let term_slots = terms.iter().map(required_scratch_slots).max().unwrap_or(0);
            if has_shared_factor_run(terms) {
                // One slot retains the factor, and one evaluates subsequent
                // bodies while the first body remains in `output`.
                2 + term_slots
            } else {
                term_slots
            }
        }
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
        (Ast::LinearTerm(lhs), Ast::LinearTerm(rhs))
        | (Ast::ConstantTerm(lhs), Ast::ConstantTerm(rhs)) => lhs == rhs,
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

fn shared_factor_run<E, F: Field, B: Basis>(
    terms: &[Ast<E, F, B>],
    end: usize,
) -> Option<(usize, &Ast<E, F, B>, FactorSide)> {
    for side in [FactorSide::Left, FactorSide::Right] {
        let (factor, _) = factor_terms(&terms[end - 1], side)?;
        let mut start = end - 1;
        while start > 0 {
            match factor_terms(&terms[start - 1], side) {
                Some((candidate, _)) if same_ast(factor, candidate) => start -= 1,
                _ => break,
            }
        }

        if end - start > 1 {
            return Some((start, factor, side));
        }
    }

    None
}

fn has_shared_factor_run<E, F: Field, B: Basis>(terms: &[Ast<E, F, B>]) -> bool {
    terms.windows(2).any(|terms| {
        [FactorSide::Left, FactorSide::Right]
            .into_iter()
            .any(|side| {
                matches!(
                    (
                        factor_terms(&terms[0], side),
                        factor_terms(&terms[1], side),
                    ),
                    (Some((lhs, _)), Some((rhs, _))) if same_ast(lhs, rhs)
                )
            })
    })
}

struct SelectorRun {
    assigned_root: usize,
    start: usize,
    end: usize,
    side: FactorSide,
}

struct SelectorFamilyPlan<'a, E, B: Basis> {
    query: &'a AstLeaf<E, B>,
    combination_len: usize,
    runs: Vec<SelectorRun>,
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

    // Tiny combinations do not recover the planning and scratch traffic.
    // Orchard's useful compressed-selector families have size 4..=7.
    let combination_len = roots.len() + 1;
    if combination_len < 4 {
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

fn selector_family_plans<'a, E, F: Field, B: Basis>(
    terms: &'a [Ast<E, F, B>],
    minus_one: F,
) -> Vec<SelectorFamilyPlan<'a, E, B>> {
    let mut families: Vec<SelectorFamilyPlan<'_, E, B>> = vec![];
    let mut start = 0;
    while start < terms.len() {
        let candidate = [FactorSide::Left, FactorSide::Right]
            .into_iter()
            .find_map(|side| {
                let (factor, _) = factor_terms(&terms[start], side)?;
                let (query, combination_len, assigned_root) =
                    compressed_selector(factor, minus_one)?;
                Some((side, factor, query, combination_len, assigned_root))
            });

        if let Some((side, factor, query, combination_len, assigned_root)) = candidate {
            let mut end = start + 1;
            while end < terms.len()
                && factor_terms(&terms[end], side)
                    .is_some_and(|(candidate, _)| same_ast(factor, candidate))
            {
                end += 1;
            }
            let run = SelectorRun {
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
                None => families.push(SelectorFamilyPlan {
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

fn collect_square_nodes<E, F: Field, B: Basis>(ast: &Ast<E, F, B>, square_nodes: &mut Vec<usize>) {
    match ast {
        Ast::Poly(_) | Ast::LinearTerm(_) | Ast::ConstantTerm(_) => {}
        Ast::Add(lhs, rhs) => {
            collect_square_nodes(lhs, square_nodes);
            collect_square_nodes(rhs, square_nodes);
        }
        Ast::Mul(AstMul(lhs, rhs)) => {
            if same_ast(lhs, rhs) {
                square_nodes.push(ast as *const Ast<E, F, B> as usize);
                // Only `lhs` is evaluated for a recognized square.
                collect_square_nodes(lhs, square_nodes);
            } else {
                collect_square_nodes(lhs, square_nodes);
                collect_square_nodes(rhs, square_nodes);
            }
        }
        Ast::Scale(inner, _) => collect_square_nodes(inner, square_nodes),
        Ast::DistributePowers(terms, _) => {
            for term in terms.iter() {
                collect_square_nodes(term, square_nodes);
            }
        }
    }
}

impl<E, F: Field, B: Basis> Evaluator<E, F, B> {
    /// Registers the given polynomial for use in this evaluation context.
    ///
    /// This API treats each registered polynomial as unique, even if the same polynomial
    /// is added multiple times.
    pub(crate) fn register_poly(&mut self, poly: Polynomial<F, B>) -> AstLeaf<E, B> {
        let index = self.polys.len();
        self.polys.push(poly);

        AstLeaf {
            index,
            rotation: Rotation::cur(),
            _evaluator: PhantomData,
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
        // We're working in a single basis, so all polynomials are the same length.
        let poly_len = self.polys.first().unwrap().len();
        let (chunk_size, _num_chunks) = get_chunk_params(poly_len);

        struct AstContext<'a, E, F: Field, B: Basis> {
            domain: &'a EvaluationDomain<F>,
            chunk_size: usize,
            chunk_index: usize,
            polys: &'a [Polynomial<F, B>],
            selector_family_root: &'a Ast<E, F, B>,
            selector_families: &'a [SelectorFamilyPlan<'a, E, B>],
            square_nodes: &'a [usize],
            minus_one: F,
            two: F,
        }

        struct SelectorFamilyBuffers<'a, F> {
            output: &'a mut [F],
            scratch: &'a mut [F],
            selectors: &'a mut [F],
            accumulators: &'a mut [F],
        }

        fn recurse_factor_body<E, F: WithSmallOrderMulGroup<3>, B: BasisOps>(
            terms: &[Ast<E, F, B>],
            run: std::ops::Range<usize>,
            side: FactorSide,
            base: F,
            ctx: &AstContext<'_, E, F, B>,
            output: &mut [F],
            scratch: &mut [F],
        ) {
            let (_, first) = factor_terms(&terms[run.start], side)
                .expect("a shared-factor run only contains products");
            recurse_into(first, ctx, output, scratch);

            if run.len() > 1 {
                let (term_values, recurse_scratch) = scratch.split_at_mut(output.len());
                for term in &terms[run.start + 1..run.end] {
                    let (_, term) = factor_terms(term, side)
                        .expect("a shared-factor run only contains products");
                    recurse_into(term, ctx, term_values, recurse_scratch);
                    for (group, term) in output.iter_mut().zip(term_values.iter()) {
                        *group *= base;
                        *group += term;
                    }
                }
            }
        }

        fn accumulate_selector_family<E, F: WithSmallOrderMulGroup<3>, B: BasisOps>(
            family: &SelectorFamilyPlan<'_, E, B>,
            terms: &[Ast<E, F, B>],
            base: F,
            ctx: &AstContext<'_, E, F, B>,
            buffers: SelectorFamilyBuffers<'_, F>,
        ) {
            let SelectorFamilyBuffers {
                output,
                scratch,
                selectors: selector_scratch,
                accumulators,
            } = buffers;
            let chunk_len = output.len();
            let prefix_len = family.combination_len * chunk_len;
            let (prefixes, suffix) = selector_scratch.split_at_mut(prefix_len);
            let suffix = &mut suffix[..chunk_len];
            B::copy_rotated_chunk(
                ctx.domain,
                ctx.chunk_size,
                ctx.chunk_index,
                &ctx.polys[family.query.index],
                family.query.rotation,
                &mut prefixes[..chunk_len],
            );

            let mut root = F::ONE;
            // Prefix `r` is q * product(i - q) for roots i below r.
            for index in 1..family.combination_len {
                let (previous, current) = prefixes.split_at_mut(index * chunk_len);
                let query = &previous[..chunk_len];
                let previous = &previous[previous.len() - chunk_len..];
                let current = &mut current[..chunk_len];
                for ((current, previous), query) in
                    current.iter_mut().zip(previous.iter()).zip(query.iter())
                {
                    *current = *previous * (root - query);
                }
                root += F::ONE;
            }

            let mut has_suffix = false;
            for index in (0..family.combination_len).rev() {
                {
                    let selector = &mut prefixes[index * chunk_len..(index + 1) * chunk_len];
                    if has_suffix {
                        for (selector, suffix) in selector.iter_mut().zip(suffix.iter()) {
                            *selector *= *suffix;
                        }
                    }

                    let run = &family.runs[index];
                    recurse_factor_body(
                        terms,
                        run.start..run.end,
                        run.side,
                        base,
                        ctx,
                        output,
                        scratch,
                    );
                    let exponent = terms.len() - run.end;
                    let global_power = base.pow_vartime([exponent as u64]);
                    for ((accumulator, selector), body) in accumulators
                        .iter_mut()
                        .zip(selector.iter())
                        .zip(output.iter())
                    {
                        *accumulator += *selector * body * global_power;
                    }
                }

                if index > 0 {
                    let query = &prefixes[..chunk_len];
                    if has_suffix {
                        for (suffix, query) in suffix.iter_mut().zip(query.iter()) {
                            *suffix *= root - query;
                        }
                    } else {
                        for (suffix, query) in suffix.iter_mut().zip(query.iter()) {
                            *suffix = root - query;
                        }
                        has_suffix = true;
                    }
                    root -= F::ONE;
                }
            }
        }

        fn recurse_into<E, F: WithSmallOrderMulGroup<3>, B: BasisOps>(
            ast: &Ast<E, F, B>,
            ctx: &AstContext<'_, E, F, B>,
            output: &mut [F],
            scratch: &mut [F],
        ) {
            match ast {
                Ast::Poly(leaf) => B::copy_rotated_chunk(
                    ctx.domain,
                    ctx.chunk_size,
                    ctx.chunk_index,
                    &ctx.polys[leaf.index],
                    leaf.rotation,
                    output,
                ),
                Ast::Add(a, b) => {
                    recurse_into(a, ctx, output, scratch);
                    let (rhs_values, rhs_scratch) = scratch.split_at_mut(output.len());
                    if let Ast::Scale(negated_rhs, scalar) = b.as_ref() {
                        if *scalar == ctx.minus_one {
                            recurse_into(negated_rhs, ctx, rhs_values, rhs_scratch);
                            for (lhs, rhs) in output.iter_mut().zip(rhs_values.iter()) {
                                *lhs -= *rhs;
                            }
                            return;
                        }
                    }

                    recurse_into(b, ctx, rhs_values, rhs_scratch);
                    for (lhs, rhs) in output.iter_mut().zip(rhs_values.iter()) {
                        *lhs += *rhs;
                    }
                }
                Ast::Mul(AstMul(a, b)) => {
                    // Preserve the multiplication shape while avoiding a
                    // constant vector for scalars with cheap field operations.
                    if let Ast::ConstantTerm(scalar) = a.as_ref() {
                        if recurse_small_scale_into(b, *scalar, ctx, output, scratch) {
                            return;
                        }
                    }
                    if let Ast::ConstantTerm(scalar) = b.as_ref() {
                        if recurse_small_scale_into(a, *scalar, ctx, output, scratch) {
                            return;
                        }
                    }

                    let node = ast as *const Ast<E, F, B> as usize;
                    if ctx.square_nodes.binary_search(&node).is_ok() {
                        recurse_into(a, ctx, output, scratch);
                        for value in output.iter_mut() {
                            *value = value.square();
                        }
                        return;
                    }

                    recurse_into(a, ctx, output, scratch);
                    let (rhs, rhs_scratch) = scratch.split_at_mut(output.len());
                    recurse_into(b, ctx, rhs, rhs_scratch);
                    for (lhs, rhs) in output.iter_mut().zip(rhs.iter()) {
                        *lhs *= *rhs;
                    }
                }
                Ast::Scale(a, scalar) => {
                    if !recurse_small_scale_into(a, *scalar, ctx, output, scratch) {
                        recurse_into(a, ctx, output, scratch);
                        for lhs in output.iter_mut() {
                            *lhs *= scalar;
                        }
                    }
                }
                Ast::DistributePowers(terms, base) => match terms.as_slice() {
                    [] => B::fill_constant(ctx.chunk_index, F::ZERO, output),
                    [term] => recurse_into(term, ctx, output, scratch),
                    terms => {
                        let mut accumulators = vec![F::ZERO; output.len()];
                        let selector_families = (std::ptr::eq(ast, ctx.selector_family_root)
                            && !ctx.selector_families.is_empty())
                        .then_some(ctx.selector_families);
                        let mut claimed = selector_families.map(|_| vec![false; terms.len()]);
                        if let Some(selector_families) = selector_families {
                            let max_combination_len = selector_families
                                .iter()
                                .map(|family| family.combination_len)
                                .max()
                                .expect("selector-family plans are non-empty");
                            let mut selector_scratch =
                                vec![F::ZERO; (max_combination_len + 1) * output.len()];
                            for family in selector_families {
                                for run in &family.runs {
                                    claimed.as_mut().expect("claimed terms are allocated")
                                        [run.start..run.end]
                                        .fill(true);
                                }
                                accumulate_selector_family(
                                    family,
                                    terms,
                                    *base,
                                    ctx,
                                    SelectorFamilyBuffers {
                                        output,
                                        scratch,
                                        selectors: &mut selector_scratch,
                                        accumulators: &mut accumulators,
                                    },
                                );
                            }
                        }
                        let mut power = F::ONE;
                        let mut processed = 0;
                        let mut end = terms.len();

                        // Traverse from the lowest original challenge power to
                        // the highest, preserving every term's exact weight.
                        while end > 0 {
                            if claimed.as_ref().is_some_and(|claimed| claimed[end - 1]) {
                                processed += 1;
                                if processed < terms.len() {
                                    power *= base;
                                }
                                end -= 1;
                                continue;
                            }

                            let unclaimed_start = claimed
                                .as_ref()
                                .and_then(|claimed| claimed[..end].iter().rposition(|value| *value))
                                .map(|position| position + 1)
                                .unwrap_or(0);
                            let shared_run = shared_factor_run(
                                &terms[unclaimed_start..end],
                                end - unclaimed_start,
                            )
                            .map(|(start, factor, side)| (unclaimed_start + start, factor, side));
                            if let Some((start, factor, side)) = shared_run {
                                let (factor_values, body_scratch) =
                                    scratch.split_at_mut(output.len());
                                recurse_into(factor, ctx, factor_values, body_scratch);
                                recurse_factor_body(
                                    terms,
                                    start..end,
                                    side,
                                    *base,
                                    ctx,
                                    output,
                                    body_scratch,
                                );

                                for ((accumulator, factor), group) in accumulators
                                    .iter_mut()
                                    .zip(factor_values.iter())
                                    .zip(output.iter())
                                {
                                    *accumulator += *factor * group * power;
                                }

                                for _ in start..end {
                                    processed += 1;
                                    if processed < terms.len() {
                                        power *= base;
                                    }
                                }
                                end = start;
                            } else {
                                recurse_into(&terms[end - 1], ctx, output, scratch);
                                for (accumulator, term) in
                                    accumulators.iter_mut().zip(output.iter())
                                {
                                    *accumulator += *term * power;
                                }

                                processed += 1;
                                if processed < terms.len() {
                                    power *= base;
                                }
                                end -= 1;
                            }
                        }

                        output.copy_from_slice(&accumulators);
                    }
                },
                Ast::LinearTerm(scalar) => {
                    B::fill_linear(ctx.domain, ctx.chunk_size, ctx.chunk_index, *scalar, output)
                }
                Ast::ConstantTerm(scalar) => B::fill_constant(ctx.chunk_index, *scalar, output),
            }
        }

        fn recurse_small_scale_into<E, F: WithSmallOrderMulGroup<3>, B: BasisOps>(
            ast: &Ast<E, F, B>,
            scalar: F,
            ctx: &AstContext<'_, E, F, B>,
            output: &mut [F],
            scratch: &mut [F],
        ) -> bool {
            if scalar == ctx.minus_one {
                recurse_into(ast, ctx, output, scratch);
                for value in output.iter_mut() {
                    *value = -*value;
                }
                true
            } else if scalar == F::ONE {
                recurse_into(ast, ctx, output, scratch);
                true
            } else if scalar == ctx.two {
                recurse_into(ast, ctx, output, scratch);
                for value in output.iter_mut() {
                    *value = value.double();
                }
                true
            } else {
                false
            }
        }

        // Apply `ast` to each chunk in parallel, writing the result into an output
        // polynomial.
        let minus_one = -F::ONE;
        let two = F::ONE.double();
        let mut result = B::empty_poly(domain);
        let scratch_slots = required_scratch_slots(ast);
        let selector_families = match ast {
            Ast::DistributePowers(terms, _) => selector_family_plans(terms, minus_one),
            _ => vec![],
        };
        let mut square_nodes = vec![];
        collect_square_nodes(ast, &mut square_nodes);
        square_nodes.sort_unstable();
        square_nodes.dedup();
        multicore::scope(|scope| {
            let selector_families = &selector_families;
            let square_nodes = &square_nodes;
            for (chunk_index, out) in result.chunks_mut(chunk_size).enumerate() {
                scope.spawn(move |_| {
                    let ctx = AstContext {
                        domain,
                        chunk_size,
                        chunk_index,
                        polys: &self.polys,
                        selector_family_root: ast,
                        selector_families,
                        square_nodes,
                        minus_one,
                        two,
                    };
                    let mut scratch = vec![F::ZERO; scratch_slots * out.len()];
                    recurse_into(ast, &ctx, out, &mut scratch);
                });
            }
        });
        result
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
    DistributePowers(Arc<Vec<Ast<E, F, B>>>, F),
    /// The degree-1 term of a polynomial.
    ///
    /// The field element is the coefficient of the term in the standard basis, not the
    /// coefficient basis.
    LinearTerm(F),
    /// The degree-0 term of a polynomial.
    ///
    /// The field element is the same in both the standard and evaluation bases.
    ConstantTerm(F),
}

impl<E, F: Field, B: Basis> Ast<E, F, B> {
    pub fn distribute_powers<I: IntoIterator<Item = Self>>(i: I, base: F) -> Self {
        Ast::DistributePowers(Arc::new(i.into_iter().collect()), base)
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
            Self::LinearTerm(x) => f.debug_tuple("LinearTerm").field(x).finish(),
            Self::ConstantTerm(x) => f.debug_tuple("ConstantTerm").field(x).finish(),
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
    fn empty_poly<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
    ) -> Polynomial<F, Self>;
    fn fill_constant<F: Field>(chunk_index: usize, scalar: F, output: &mut [F]);
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
    );
}

impl BasisOps for Coeff {
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

    fn copy_rotated_chunk<F: WithSmallOrderMulGroup<3>>(
        _: &EvaluationDomain<F>,
        _: usize,
        _: usize,
        _: &Polynomial<F, Self>,
        _: Rotation,
        _: &mut [F],
    ) {
        panic!("Can't rotate polynomials in the standard basis")
    }
}

impl BasisOps for LagrangeCoeff {
    fn empty_poly<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
    ) -> Polynomial<F, Self> {
        domain.empty_lagrange()
    }

    fn fill_constant<F: Field>(_: usize, scalar: F, output: &mut [F]) {
        output.fill(scalar);
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

    fn copy_rotated_chunk<F: WithSmallOrderMulGroup<3>>(
        _: &EvaluationDomain<F>,
        chunk_size: usize,
        chunk_index: usize,
        poly: &Polynomial<F, Self>,
        rotation: Rotation,
        output: &mut [F],
    ) {
        poly.copy_rotated_chunk(rotation, chunk_size, chunk_index, output)
    }
}

impl BasisOps for ExtendedLagrangeCoeff {
    fn empty_poly<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
    ) -> Polynomial<F, Self> {
        domain.empty_extended()
    }

    fn fill_constant<F: Field>(_: usize, scalar: F, output: &mut [F]) {
        output.fill(scalar);
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

    fn copy_rotated_chunk<F: WithSmallOrderMulGroup<3>>(
        domain: &EvaluationDomain<F>,
        chunk_size: usize,
        chunk_index: usize,
        poly: &Polynomial<F, Self>,
        rotation: Rotation,
        output: &mut [F],
    ) {
        let rotation_abs = (rotation.0.unsigned_abs() as usize)
            .checked_mul(domain.get_quotient_poly_degree().next_power_of_two())
            .expect("scaled rotation fits in usize");
        poly.copy_rotated_chunk_helper(
            rotation.0 < 0,
            rotation_abs,
            chunk_size,
            chunk_index,
            output,
        )
    }
}

#[cfg(test)]
mod tests {
    use group::ff::{Field, WithSmallOrderMulGroup};
    use pasta_curves::{pallas, vesta};

    use super::{
        collect_square_nodes, compressed_selector, get_chunk_params, new_evaluator,
        selector_family_plans, Ast, AstLeaf, BasisOps, Evaluator, FactorSide,
    };
    use crate::poly::{Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, Rotation};

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
                    assert!(result
                        .iter()
                        .zip(expected.iter())
                        .all(|(result, value)| *result == *value * scalar));
                }
            }
        }

        check::<LagrangeCoeff>();
        check::<ExtendedLagrangeCoeff>();
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
        assert!(lagrange_evaluator
            .evaluate(&Ast::ConstantTerm(scalar), &domain)
            .iter()
            .all(|value| *value == scalar));
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
        assert!(extended_evaluator
            .evaluate(&Ast::ConstantTerm(scalar), &domain)
            .iter()
            .all(|value| *value == scalar));
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
        let mut square_nodes = vec![];
        collect_square_nodes(&nested_square, &mut square_nodes);
        assert_eq!(square_nodes.len(), 2);

        let expected = evaluator.evaluate(&repeated, &domain);
        let actual = evaluator.evaluate(&nested_square, &domain);
        assert!(actual
            .iter()
            .zip(expected.iter())
            .all(|(actual, expected)| *actual == expected.square().square()));

        let lhs = Ast::from(leaf.with_rotation(Rotation::prev()));
        let rhs = Ast::from(leaf.with_rotation(Rotation::next()));
        let product = lhs.clone() * rhs.clone();
        square_nodes.clear();
        collect_square_nodes(&product, &mut square_nodes);
        assert!(square_nodes.is_empty());

        let expected_lhs = evaluator.evaluate(&lhs, &domain);
        let expected_rhs = evaluator.evaluate(&rhs, &domain);
        let actual = evaluator.evaluate(&product, &domain);
        assert!(actual
            .iter()
            .zip(expected_lhs.iter().zip(expected_rhs.iter()))
            .all(|(actual, (lhs, rhs))| *actual == *lhs * rhs));
    }

    #[test]
    fn repeated_subexpressions_use_squares() {
        check_repeated_subexpressions_use_squares::<pallas::Base, LagrangeCoeff>();
        check_repeated_subexpressions_use_squares::<pallas::Base, ExtendedLagrangeCoeff>();
        check_repeated_subexpressions_use_squares::<vesta::Base, LagrangeCoeff>();
        check_repeated_subexpressions_use_squares::<vesta::Base, ExtendedLagrangeCoeff>();
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

    fn check_shared_factor_runs<F>()
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

        assert!(matches!(
            super::shared_factor_run(&terms, terms.len()),
            Some((3, _, FactorSide::Left))
        ));
        assert!(super::shared_factor_run(&terms, 3).is_none());
        assert!(matches!(
            super::shared_factor_run(&terms, 2),
            Some((0, _, FactorSide::Left))
        ));

        let right_terms = bodies
            .iter()
            .take(4)
            .map(|body| Ast::from(*body) * common_factor.clone())
            .collect::<Vec<_>>();
        assert!(matches!(
            super::shared_factor_run(&right_terms, right_terms.len()),
            Some((0, _, FactorSide::Right))
        ));

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
    fn shared_factor_runs_match_generic_evaluation() {
        check_shared_factor_runs::<pallas::Base>();
        check_shared_factor_runs::<vesta::Base>();
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
                terms.push(selector.clone() * Ast::from(bodies[body_index]));
                control_terms.push(
                    (selector.clone() * Ast::ConstantTerm(F::ONE)) * Ast::from(bodies[body_index]),
                );
                term_inputs.push(Some((assigned_root, body_index)));
            }
        }

        // Keep one unrelated term after the planned family to ensure that
        // every original challenge power is retained.
        terms.push(Ast::from(bodies[0]) + Ast::from(bodies[COMBINATION_LEN - 1]));
        control_terms.push(Ast::from(bodies[0]) + Ast::from(bodies[COMBINATION_LEN - 1]));
        term_inputs.push(None);

        let plans = selector_family_plans(&terms, -F::ONE);
        assert_eq!(plans.len(), 1);
        assert_eq!(plans[0].combination_len, COMBINATION_LEN);
        assert_eq!(plans[0].runs.len(), COMBINATION_LEN);
        assert_eq!(plans[0].runs[1].end - plans[0].runs[1].start, 2);
        assert!(selector_family_plans(&control_terms, -F::ONE).is_empty());

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
                        Some((assigned_root, body_index)) => {
                            compressed_selector_value(
                                query_values[row],
                                COMBINATION_LEN,
                                *assigned_root,
                            ) * body_values[*body_index][row]
                        }
                        None => body_values[0][row] + body_values[COMBINATION_LEN - 1][row],
                    };
                    accumulator * base + term
                });
                assert_eq!(actual[row], expected);
            }
        }

        let incomplete = terms[..terms.len() - 2].to_vec();
        assert!(selector_family_plans(&incomplete, -F::ONE).is_empty());

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
        let right_hand_plans = selector_family_plans(&right_hand, -F::ONE);
        assert_eq!(right_hand_plans.len(), 1);
        assert!(right_hand_plans[0]
            .runs
            .iter()
            .all(|run| matches!(run.side, FactorSide::Right)));

        // Reverse the roots and put the unrelated term before the family to
        // exercise non-root run order and leading unclaimed terms.
        let reversed = terms.iter().cloned().rev().collect::<Vec<_>>();
        let reversed_control = control_terms.iter().cloned().rev().collect::<Vec<_>>();
        let reversed_plans = selector_family_plans(&reversed, -F::ONE);
        assert_eq!(reversed_plans.len(), 1);
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
        let overlapping_plans = selector_family_plans(&overlapping, -F::ONE);
        assert_eq!(overlapping_plans.len(), 1);
        assert_eq!(overlapping_plans[0].query, &query);

        let mut repeated_run = terms.clone();
        repeated_run
            .push(compressed_selector_expression(query, COMBINATION_LEN, 1) * Ast::from(bodies[0]));
        assert!(selector_family_plans(&repeated_run, -F::ONE).is_empty());

        let non_selector =
            Ast::from(query) * (Ast::ConstantTerm(F::ONE) + Ast::<_, F, _>::from(query));
        assert!(compressed_selector(&non_selector, -F::ONE).is_none());
    }

    #[test]
    fn compressed_selector_families_match_generic_evaluation() {
        check_compressed_selector_families::<pallas::Base>();
        check_compressed_selector_families::<vesta::Base>();
    }
}
