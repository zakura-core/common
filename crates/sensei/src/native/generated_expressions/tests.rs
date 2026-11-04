use crate::native::test_support::reduced_values;
/// Gate 14's folded scale is exactly the product of the two pool
/// constants it replaced.
#[test]
fn folded_gate_14_scale_matches_constant_product() {
    assert_eq!(
        (super::TWO_POW_130).reduce(),
        (super::constant(8).mul(&super::constant(9))).reduce()
    );
    assert_eq!(
        super::TWO_POW_130.to_canonical_uint().highest_set_bit(),
        Some(130)
    );
}

use std::{hint::black_box, time::Instant};

use crate::Error;
use crate::native::expressions::Expression;

#[test]
fn tree_evaluation_preserves_query_order_and_errors() {
    use crate::native::expressions::{advice, constant, fixed, instance};
    let tree = advice(0)
        .add(instance(1).multiply_constant(0))
        .mul(fixed(2).neg())
        .add(constant(5));
    let mut reads = Vec::new();
    let value = super::evaluate(&tree, &mut |kind, index| {
        reads.push((kind, index));
        Ok(<Fp>::from_u64(index as u64 + 3))
    })
    .unwrap();
    assert_eq!(
        reads,
        [
            (QueryKind::Advice, 0),
            (QueryKind::Instance, 1),
            (QueryKind::Fixed, 2)
        ]
    );
    assert_eq!((value).reduce(), (<Fp>::from_u64(54).neg()).reduce()); // (3 + 4 * 2) * -5 + 1
    for fail_at in 0..reads.len() {
        let mut visited = Vec::new();
        let result = super::evaluate(&tree, &mut |kind, index| {
            visited.push((kind, index));
            if visited.len() == fail_at + 1 {
                Err(Error::InternalInvariant)
            } else {
                Ok(<Fp>::ZERO)
            }
        });
        assert_eq!(reduced_values(&(result)), Err(Error::InternalInvariant));
        assert_eq!(visited, reads[..=fail_at]);
    }
}

#[test]
fn cached_tree_splits_borrow_the_original_operands() {
    use crate::native::expressions::{advice, fixed};
    let mut programs = alloc::vec![
        super::ProgramTrees::new(advice(0).mul(fixed(0))),
        super::ProgramTrees::new(fixed(0).mul(advice(0))),
        super::ProgramTrees::new(fixed(0).mul(fixed(1))),
        super::ProgramTrees::new(advice(0).mul(advice(1))),
    ];
    programs.reserve_exact(crate::native::programs::expression_programs().len());
    programs.extend(
        crate::native::programs::expression_programs()
            .into_iter()
            .map(super::ProgramTrees::new),
    );
    for program in programs {
        let expected = program.tree.fixed_root_split();
        assert_eq!(program.fixed_factor(), expected.map(|(factor, _)| factor));
        assert_eq!(program.dynamic_body(), expected.map(|(_, body)| body));
        if let Some((factor, body)) = expected {
            assert!(std::ptr::eq(program.fixed_factor().unwrap(), factor));
            assert!(std::ptr::eq(program.dynamic_body().unwrap(), body));
        }
    }
    assert!(super::program_trees(super::PROGRAM_COUNT).is_err());
}

/// Pin the reviewed reassociation and independently recover the exact
/// historical container by undoing only the two curve root splits.
#[test]
fn tree_spec_matches_historical_container_digest() {
    use sha2::{Digest, Sha256};
    let mut programs = crate::native::programs::expression_programs();
    let digest = |programs: &[Expression]| {
        hex::encode(Sha256::digest(
            crate::native::expressions::encode_container(programs).unwrap(),
        ))
    };
    let reassociated = digest(&programs);
    for program in &mut programs[6..8] {
        let Expression::Product(selector, body) = program.clone() else {
            panic!("curve selector root")
        };
        let Expression::Product(coordinate, relation) = *body else {
            panic!("curve body")
        };
        *program = selector.mul(*coordinate).mul(*relation);
    }
    assert_eq!(
        digest(&programs),
        "6ce3e5193ab6b36d0fd977509ee5d7774c8ebdabab39af9f5363b6d91bc66663"
    );
    assert_eq!(
        reassociated,
        "76e6d2442230a70f6aec4559d54417b7ce6f6c5ab4507ae3e4f6f71ea00d48e0"
    );
}

use super::{
    AFFINE_QUERY_SLOTS, BILINEAR_BLOCK_LEN, FACTOR_GROUPS, Fp, GATE_6_BILINEAR_FIRST,
    GATE_25_PROGRAMS, GATE_CONSTRAINT_COUNT, GATE_PROGRAMS_2N, GATE_PROGRAMS_4N, GATE_QUERY_COUNT,
    GATE_QUERY_DESCRIPTORS, GATES, Gate4NCoefficients, Gate25BodyKernel, GateChallengeCoefficients,
    GateKernel, GateRowCoefficients, LOOKUPS, LookupInputKernel, MAX_GATE_CONSTRAINTS,
    PREPARED_GATE_SELECTOR_COUNT, PREPARED_GATE_SELECTOR_FIXED_QUERY, QueryKind,
    ROW_COEFFICIENT_QUERY_SLOTS, RangeCheckInputKernel, RowSum, SINSEMILLA_INPUT_LOOKUPS,
    SinsemillaCubics, SinsemillaInputKernel, TREES, constant, evaluate, evaluate_affine_gates,
    evaluate_affine_gates_4n, evaluate_gates, evaluate_gates_2n, evaluate_gates_4n,
    first_curve_relation, prepare_gate_selectors, weighted_bilinear_kernel_13,
    weighted_factor_kernel_67, weighted_factor_kernel_105, weighted_factor_kernel_106,
    weighted_factor_kernel_186,
};

mod kernel_metadata {
    use std::{cell::RefCell, collections::BTreeSet};

    use crate::native::{
        expressions::QueryDependencies,
        queries::{ADVICE_QUERIES, FIXED_QUERIES, INSTANCE_QUERIES},
    };

    use super::{
        Fp, GATE_CONSTRAINT_COUNT, GATE_PROGRAMS_2N, GATE_PROGRAMS_4N, GATE_QUERY_DESCRIPTORS,
        Gate4NCoefficients, GateKernel, PREPARED_GATE_SELECTOR_COUNT, QueryKind, TREES,
        evaluate_gates_2n, evaluate_gates_4n, query_value,
    };

    /// The dependency set of every program a kernel implements.
    fn kernel_dependencies(kernel: GateKernel) -> QueryDependencies {
        let programs = &*TREES;
        (0..GATE_CONSTRAINT_COUNT)
            .filter(|&program| kernel.implements(program))
            .map(|program| programs[program].tree.query_dependencies())
            .fold(QueryDependencies::default(), QueryDependencies::union)
    }

    /// Maps recorded frame indices to the (kind, query) set they denote.
    fn frame_reads_to_dependencies(frames: &BTreeSet<usize>) -> QueryDependencies {
        frames
            .iter()
            .map(|&frame| {
                let (kind, index) = GATE_QUERY_DESCRIPTORS[frame];
                let bit = 1u32 << index;
                match kind {
                    QueryKind::Fixed => QueryDependencies {
                        fixed: bit,
                        ..Default::default()
                    },
                    QueryKind::Advice => QueryDependencies {
                        advice: bit,
                        ..Default::default()
                    },
                    QueryKind::Instance => QueryDependencies {
                        instance: bit,
                        ..Default::default()
                    },
                }
            })
            .fold(QueryDependencies::default(), QueryDependencies::union)
    }

    #[test]
    fn kernels_partition_the_gate_programs() {
        for program in 0..GATE_CONSTRAINT_COUNT {
            let owners = GateKernel::ALL
                .iter()
                .filter(|kernel| kernel.implements(program))
                .count();
            assert_eq!(owners, 1, "program {program}");
        }
        assert!(GATE_PROGRAMS_2N.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(GATE_PROGRAMS_4N.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(
            GATE_PROGRAMS_2N
                .iter()
                .all(|program| !GATE_PROGRAMS_4N.contains(program))
        );
    }

    #[test]
    fn every_program_depends_only_on_existing_queries() {
        let programs = &*TREES;
        let in_range = |bits: u32, table_len: usize| bits >> table_len == 0;
        for (index, program) in programs.iter().enumerate() {
            let dependencies = program.tree.query_dependencies();
            assert!(
                in_range(dependencies.fixed, FIXED_QUERIES.len()),
                "program {index}"
            );
            assert!(
                in_range(dependencies.advice, ADVICE_QUERIES.len()),
                "program {index}"
            );
            assert!(
                in_range(dependencies.instance, INSTANCE_QUERIES.len()),
                "program {index}"
            );
            if let Some(factor) = program.fixed_factor() {
                assert!(
                    factor.query_dependencies().is_fixed_only(),
                    "program {index}: the root factor must read only fixed queries"
                );
            }
        }
    }

    /// A class kernel's actual frame reads, recorded through its query
    /// closure, must lie within the declared dependencies of the programs
    /// it implements.
    #[test]
    fn class_kernels_read_only_their_programs_queries() {
        let queries: alloc::vec::Vec<Fp> = GATE_QUERY_DESCRIPTORS
            .iter()
            .map(|&(kind, index)| query_value(kind, index))
            .collect();
        let reads = RefCell::new(BTreeSet::new());
        let query = |frame: usize| {
            reads.borrow_mut().insert(frame);
            queries[frame]
        };

        let mut accumulator = <Fp>::ZERO;
        evaluate_gates_2n(
            &query,
            &[<Fp>::ONE; GATE_PROGRAMS_2N.len()],
            &mut accumulator,
        );
        let read_2n = frame_reads_to_dependencies(&reads.borrow());
        assert!(!read_2n.is_fixed_only() || read_2n.fixed != 0);
        assert!(
            read_2n.is_subset_of(kernel_dependencies(GateKernel::Class2N)),
            "2N kernel reads outside its programs' dependencies: {read_2n:?}"
        );

        reads.borrow_mut().clear();
        evaluate_gates_4n(
            &query,
            &[<Fp>::ONE; PREPARED_GATE_SELECTOR_COUNT],
            &Gate4NCoefficients::new([<Fp>::ONE; GATE_PROGRAMS_4N.len()]),
            &mut accumulator,
        );
        let read_4n = frame_reads_to_dependencies(&reads.borrow());
        assert!(
            read_4n.is_subset_of(kernel_dependencies(GateKernel::Class4N)),
            "4N kernel reads outside its programs' dependencies: {read_4n:?}"
        );
    }
}

fn query_value(kind: QueryKind, index: usize) -> Fp {
    let kind_offset = match kind {
        QueryKind::Fixed => 0x1000,
        QueryKind::Advice => 0x2000,
        QueryKind::Instance => 0x3000,
    };
    <Fp>::from_u64(kind_offset + index as u64 * 0x101 + 7)
}

#[test]
fn shared_preflight_bodies_match_tree_reference() {
    use super::{interpolation_body, poseidon_full_round_bodies};
    let target = crate::test_codec::target();
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        <Fp>::from_u64(state)
            .square()
            .square()
            .add(&<Fp>::from_u64(state >> 3))
    };
    let advice = (0..super::super::target::ADVICE_COLUMNS)
        .map(|_| {
            (0..super::super::target::N)
                .map(|_| next())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    // Every base row includes both sides of the rotation wraparound.
    for row in 0..super::super::target::N {
        let mut query = |kind, index| {
            super::super::evaluation::base_query_value(kind, index, target, &advice, &[], row)
        };
        let poseidon = poseidon_full_round_bodies(&mut query).unwrap();
        for (program, value) in (75..78).zip(poseidon).chain(
            [56, 59].map(|program| (program, interpolation_body(program, &mut query).unwrap())),
        ) {
            let body = super::program_trees(program)
                .unwrap()
                .dynamic_body()
                .unwrap();
            assert_eq!(
                (value).reduce(),
                (evaluate(body, &mut query).unwrap()).reduce(),
                "program {program}, row {row}"
            );
        }
    }
    // Also vary the fixed coefficients independently of the target data.
    for _ in 0..128 {
        let queries = GATE_QUERY_DESCRIPTORS.map(|_| next());
        let mut query = |kind, index| {
            Ok(queries[GATE_QUERY_DESCRIPTORS
                .iter()
                .position(|descriptor| *descriptor == (kind, index))
                .unwrap()])
        };
        let poseidon = poseidon_full_round_bodies(&mut query).unwrap();
        for (program, value) in (75..78).zip(poseidon).chain(
            [56, 59].map(|program| (program, interpolation_body(program, &mut query).unwrap())),
        ) {
            assert_eq!(
                (value).reduce(),
                (evaluate(
                    super::program_trees(program)
                        .unwrap()
                        .dynamic_body()
                        .unwrap(),
                    &mut query
                )
                .unwrap())
                .reduce()
            );
        }
    }
    for program in [56, 59] {
        assert_eq!(
            reduced_values(
                &(interpolation_body(program, &mut |_, _| Err(Error::InternalInvariant)))
            ),
            Err(Error::InternalInvariant)
        );
    }
    assert_eq!(
        reduced_values(&(poseidon_full_round_bodies(&mut |_, _| Err(Error::InternalInvariant)))),
        Err(Error::InternalInvariant)
    );
}

#[test]
fn reassociated_curve_gates_use_sparse_reference_checks() {
    use super::super::{
        evaluation::{evaluate_expression_at_row, sparse_gate_expression_is_zero},
        target::{ADVICE_COLUMNS, N},
    };
    let target = crate::test_codec::target();
    for program in [6, 7] {
        let rows = target.gate_active_rows(program).unwrap();
        assert!(!rows.is_empty() && rows.len() < N);
        let mut advice = alloc::vec![ alloc::vec![ <Fp>::from_u64(7); N]; ADVICE_COLUMNS];
        let column = target.queries().advice()[program - 6].column;
        for &row in rows {
            advice[column][usize::from(row)] = <Fp>::ZERO;
        }
        for expected in [true, false] {
            assert_eq!(
                sparse_gate_expression_is_zero(program, target, &advice, &[]),
                Ok(expected)
            );
            assert_eq!(
                (0..N).all(
                    |row| evaluate_expression_at_row(program, target, &advice, &[], row)
                        .unwrap()
                        .is_zero()
                ),
                expected
            );
            advice[column][usize::from(rows[0])] = <Fp>::ONE;
        }
    }
}

/// The gate 25 body kernel computes exactly the two programs' dynamic
/// bodies on every row of random columns, and resolves only for them.
#[test]
fn gate_25_body_kernel_matches_tree_reference() {
    let target = crate::test_codec::target();
    let n = super::super::target::N;
    assert!(Gate25BodyKernel::resolve(target, 6).is_none());
    let mut state = 0x7f4a_7c15_9e37_79b9u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        <Fp>::from_u64(state)
            .square()
            .add(&<Fp>::from_u64(state >> 13))
    };
    let advice_columns = target
        .queries()
        .advice()
        .iter()
        .map(|query| query.column)
        .max()
        .unwrap()
        + 1;
    let random = (0..advice_columns)
        .map(|_| (0..n).map(|_| next()).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let instance = alloc::vec![ <Fp>::ZERO; n];
    for program in GATE_25_PROGRAMS {
        let kernel = Gate25BodyKernel::resolve(target, program).unwrap();
        assert!(kernel.accepts(&random));
        for row in 0..n {
            let expected = super::super::evaluation::evaluate_gate_body_at_row(
                program, target, &random, &instance, row,
            )
            .unwrap();
            assert_eq!(
                (kernel.row(&random, target.fixed_values(), row)).reduce(),
                (expected).reduce(),
                "program {program} row {row}"
            );
        }
    }
}

/// The base-domain Sinsemilla input kernel computes exactly its three
/// programs on every row, for random columns as well as the fixtures'
/// witnesses (checked in preflight's tests), and resolves only for the two
/// Sinsemilla lookups.
#[test]
fn sinsemilla_input_kernel_matches_tree_reference() {
    let target = crate::test_codec::target();
    let n = super::super::target::N;
    assert!(SinsemillaInputKernel::resolve(target, 0).is_none());
    assert!(SinsemillaInputKernel::resolve(target, 3).is_none());
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        <Fp>::from_u64(state)
            .square()
            .add(&<Fp>::from_u64(state >> 5))
    };
    let advice_columns = target
        .queries()
        .advice()
        .iter()
        .map(|query| query.column)
        .max()
        .unwrap()
        + 1;
    let random = (0..advice_columns)
        .map(|_| (0..n).map(|_| next()).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let instance = alloc::vec![ <Fp>::ZERO; n];
    for frame in SINSEMILLA_INPUT_LOOKUPS {
        let kernel = SinsemillaInputKernel::resolve(target, frame.lookup).unwrap();
        assert!(kernel.accepts(&random));
        let programs = target.lookups()[frame.lookup].inputs();
        assert_eq!(programs.start, frame.first_program);
        let expected = programs
            .indices()
            .map(|program| {
                super::super::evaluation::evaluate_expression(program, target, &random, &instance)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let expected_rows = (0..n)
            .map(|row| [expected[0][row], expected[1][row], expected[2][row]])
            .collect::<Vec<_>>();
        for (row, expected) in expected_rows.iter().enumerate() {
            assert_eq!(
                reduced_values(&(kernel.row(&random, target.fixed_values(), row))),
                reduced_values(expected),
                "lookup {} row {row}",
                frame.lookup
            );
        }
    }
    // The range-check kernel: lookup 0's single program, row by row.
    let range = RangeCheckInputKernel::resolve(target, 0).unwrap();
    assert!(range.accepts(&random));
    let programs = target.lookups()[0].inputs();
    assert_eq!((programs.start, programs.len()), (193, 1));
    let expected =
        super::super::evaluation::evaluate_expression(programs.start, target, &random, &instance)
            .unwrap();
    for (row, expected) in expected.iter().enumerate() {
        assert_eq!(
            (range.row(&random, target.fixed_values(), row)).reduce(),
            (*expected).reduce(),
            "row {row}"
        );
    }
    assert!(RangeCheckInputKernel::resolve(target, 1).is_none());
    for lookup_index in 0..target.lookups().len() {
        let kernel = LookupInputKernel::resolve(target, lookup_index).unwrap();
        assert_eq!(
            kernel.components(),
            target.lookups()[lookup_index].inputs().len()
        );
    }
    assert!(LookupInputKernel::resolve(target, 3).is_none());

    let mut short = random.clone();
    short[0].pop();
    assert!(
        !SinsemillaInputKernel::resolve(target, 1)
            .unwrap()
            .accepts(&short)
    );
}

#[test]
fn gate_programs_classify_fixed_root_factors() {
    let programs = &*TREES;
    let full = programs[..193]
        .iter()
        .enumerate()
        .filter_map(|(index, program)| program.fixed_factor().is_none().then_some(index))
        .collect::<Vec<_>>();
    assert!(full.is_empty());
}

/// Visits every source node in post-order for the structural censuses.
fn for_each_node(tree: &Expression, mut visit: impl FnMut(&Expression)) {
    fn walk(tree: &Expression, visit: &mut impl FnMut(&Expression)) {
        match tree {
            Expression::Sum(left, right) | Expression::Product(left, right) => {
                walk(left, visit);
                walk(right, visit);
            }
            Expression::Negated(inner) | Expression::ConstantScaled(inner, _) => walk(inner, visit),
            _ => {}
        }
        visit(tree);
    }
    walk(tree, &mut visit);
}

fn multiplication_count(tree: &Expression) -> usize {
    let mut count = 0;
    for_each_node(tree, |node| {
        if matches!(
            node,
            Expression::Product(..) | Expression::ConstantScaled(..)
        ) {
            count += 1;
        }
    });
    count
}

/// A hash-consed expression node for the value-numbering census.
/// Commutative operands are stored sorted so `a·b` and `b·a` intern to
/// one node; everything else is structural (no algebraic rewriting), so
/// the census *under*-counts the sharing an algebraic optimizer could
/// reach and its floor is conservative.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ValueNode {
    Fixed(u8),
    Advice(u8),
    Instance(u8),
    Constant(u8),
    Neg(u32),
    Add(u32, u32),
    Mul(u32, u32),
    MulConst(u32, u8),
}

/// Nodes interned and visited, split into
/// products/scalings and sums/negations.
#[derive(Default, PartialEq, Eq, Debug)]
struct OpCounts {
    executed_muls: usize,
    distinct_muls: usize,
    executed_adds: usize,
    distinct_adds: usize,
}

/// Interns a tree and counts arithmetic nodes, both visited and newly
/// created, preserving the census independently of the field evaluator.
fn value_number_program(
    tree: &Expression,
    interner: &mut std::collections::HashMap<ValueNode, u32>,
    counts: &mut OpCounts,
) -> u32 {
    let node = match tree {
        Expression::Fixed(index) => ValueNode::Fixed(*index),
        Expression::Advice(index) => ValueNode::Advice(*index),
        Expression::Instance(index) => ValueNode::Instance(*index),
        Expression::Constant(index) => ValueNode::Constant(*index),
        Expression::Sum(left, right) | Expression::Product(left, right) => {
            let left = value_number_program(left, interner, counts);
            let right = value_number_program(right, interner, counts);
            let (low, high) = (left.min(right), left.max(right));
            if matches!(tree, Expression::Sum(..)) {
                ValueNode::Add(low, high)
            } else {
                ValueNode::Mul(low, high)
            }
        }
        Expression::Negated(inner) => ValueNode::Neg(value_number_program(inner, interner, counts)),
        Expression::ConstantScaled(inner, index) => {
            ValueNode::MulConst(value_number_program(inner, interner, counts), *index)
        }
    };
    let next = interner.len() as u32;
    let mut created = false;
    let id = *interner.entry(node).or_insert_with(|| {
        created = true;
        next
    });
    match node {
        ValueNode::Add(..) | ValueNode::Neg(_) => {
            counts.executed_adds += 1;
            counts.distinct_adds += usize::from(created);
        }
        ValueNode::Mul(..) | ValueNode::MulConst(..) => {
            counts.executed_muls += 1;
            counts.distinct_muls += usize::from(created);
        }
        _ => {}
    }
    id
}

/// Excludes the prepared selector factor and its root multiplication.
fn gate_body(program: &super::ProgramTrees) -> &Expression {
    program.dynamic_body().unwrap_or(&program.tree)
}

/// Structural global value numbering over the 193 gate
/// program bodies — the per-row dynamic work of the quotient's gate fold
/// (prepared selector factors excluded) — and, separately, the seven
/// lookup input programs the θ-compression evaluates on the extended
/// coset. Three columns per op class: executed (each body evaluated
/// independently, the tree evaluator's cost), per-program distinct
/// (sharing within one body), and global distinct (sharing across all
/// bodies). The per-program→global gap bounds what cross-gate common
/// subexpression elimination can remove beyond a per-gate evaluator; the
/// hand-written fused kernel statically contains ≈252 multiply/mul_add
/// calls plus folder and product-sum fusion (≈480 mul-equivalents per
/// row), sitting between the executed and per-program columns.
#[test]
fn gate_body_value_numbering_census() {
    let programs = &*TREES;

    let census = |bodies: &[&Expression]| {
        let mut executed = OpCounts::default();
        for body in bodies {
            let mut fresh = std::collections::HashMap::new();
            let mut counts = OpCounts::default();
            value_number_program(body, &mut fresh, &mut counts);
            executed.executed_muls += counts.executed_muls;
            executed.executed_adds += counts.executed_adds;
            executed.distinct_muls += counts.distinct_muls;
            executed.distinct_adds += counts.distinct_adds;
        }
        let mut shared = std::collections::HashMap::new();
        let mut global = OpCounts::default();
        for body in bodies {
            value_number_program(body, &mut shared, &mut global);
        }
        (
            executed.executed_muls,
            executed.distinct_muls,
            global.distinct_muls,
            executed.executed_adds,
            executed.distinct_adds,
            global.distinct_adds,
        )
    };

    let gate_bodies = programs[..193].iter().map(gate_body).collect::<Vec<_>>();
    let lookup_inputs = LOOKUPS
        .iter()
        .flat_map(|lookup| lookup.inputs().indices())
        .map(|index| &programs[index].tree)
        .collect::<Vec<_>>();

    // Extracting the curve selectors removes their work from the body
    // census. These tree operation counts do not model the hot kernel's
    // algebraic sharing, selector reconstruction, or product-sum fusion.
    assert_eq!(census(&gate_bodies), (561, 450, 265, 1039, 854, 412));
    // The seven lookup input programs share nothing at any level —
    // global numbering removes not a single multiplication — so
    // precompression has no repeated combination to hoist there either.
    assert_eq!(census(&lookup_inputs), (28, 28, 28, 51, 49, 44));
}

/// Points of the smallest sub-coset determining a total-degree-`degree`
/// term's quotient contribution, as a multiple of `N`:
/// `M_d = N·2^⌈log₂(d−1)⌉`, with degree ≤ 2 needing only the base domain.
/// Dividing a vanishing constraint of degree at most `d·(N−1)` by
/// `X^N − 1` leaves degree below `(d−1)·N`, hence this power-of-two bound.
fn class_multiple(degree: usize) -> usize {
    match degree {
        0..=2 => 1,
        3 => 2,
        4..=5 => 4,
        6..=9 => 8,
        _ => panic!("no quotient term has degree {degree}"),
    }
}

/// Per-program total degree over the expression trees,
/// split into prepared-selector factor and body via the validated fixed
/// root factor. Pins the degree-class structure the quotient split relies
/// on: 180 of 193 gate programs need the full 8N
/// extended coset, exactly 13 drop to 2N/4N, and no program queries the
/// instance column at all.
#[test]
fn quotient_degree_class_census() {
    use alloc::collections::BTreeMap;

    let programs = &*TREES;

    let mut degree_histogram = BTreeMap::new();
    let mut selector_histogram = BTreeMap::new();
    let mut body_histogram = BTreeMap::new();
    let mut class_2n = Vec::new();
    let mut class_4n = Vec::new();
    let mut class_8n = 0usize;
    for (index, program) in programs[..193].iter().enumerate() {
        let degree = program.tree.degree();
        // The factor is one operand of the program's root multiplication
        // (validated by `fixed_root_split`), so total degree splits as
        // selector degree + body degree.
        let selector_degree = program.fixed_factor().map_or(0, Expression::degree);
        assert!(selector_degree <= degree);
        *degree_histogram.entry(degree).or_insert(0usize) += 1;
        *selector_histogram.entry(selector_degree).or_insert(0usize) += 1;
        *body_histogram
            .entry(degree - selector_degree)
            .or_insert(0usize) += 1;
        match class_multiple(degree) {
            2 => class_2n.push(index),
            4 => class_4n.push(index),
            8 => class_8n += 1,
            multiple => panic!("unexpected gate class {multiple}N"),
        }
    }
    assert_eq!(
        degree_histogram.into_iter().collect::<Vec<_>>(),
        [(3, 4), (4, 2), (5, 7), (6, 21), (7, 35), (8, 65), (9, 59)]
    );
    // The complex fixed selectors `q·∏(cᵢ−q)` alone contribute degree
    // 4–7; twelve programs carry a plain degree-1 selector. The two
    // reassociated curve programs now expose their degree-4 selectors.
    assert_eq!(
        selector_histogram.into_iter().collect::<Vec<_>>(),
        [(1, 12), (4, 46), (5, 18), (6, 43), (7, 74)]
    );
    assert_eq!(
        body_histogram.into_iter().collect::<Vec<_>>(),
        [(1, 62), (2, 87), (3, 24), (4, 5), (5, 11), (8, 4)]
    );
    assert_eq!(class_2n, super::GATE_PROGRAMS_2N);
    assert_eq!(class_4n, super::GATE_PROGRAMS_4N);
    assert_eq!(class_8n, 180);

    // Lookup expressions: input compressions have degree 3–4, every
    // table form is a bare fixed query.
    let lookup_degrees = LOOKUPS
        .iter()
        .map(|lookup| {
            let degrees = |range: super::ExpressionRange| {
                range
                    .indices()
                    .map(|index| programs[index].tree.degree())
                    .collect::<Vec<_>>()
            };
            (degrees(lookup.inputs()), degrees(lookup.tables()))
        })
        .collect::<Vec<_>>();
    assert_eq!(
        lookup_degrees,
        [
            (alloc::vec![3], alloc::vec![1]),
            (alloc::vec![4, 2, 4], alloc::vec![1, 1, 1]),
            (alloc::vec![4, 2, 4], alloc::vec![1, 1, 1]),
        ]
    );

    // Instance appears in no gate or lookup program: its only quotient
    // consumer is permutation set 0.
    let instance_operations: usize = programs
        .iter()
        .map(|program| {
            let mut count = 0;
            for_each_node(&program.tree, |node| {
                if matches!(node, Expression::Instance(_)) {
                    count += 1;
                }
            });
            count
        })
        .sum();
    assert_eq!(instance_operations, 0);
}

/// The per-family degree-class map and the class pinning each column.
/// A column is pinned at the largest class among the terms that read it:
/// gate programs via their
/// queries, lookup product rules via their compression expressions, and
/// permutation set rules via their member columns. Result: every advice
/// column and 28 of 29 fixed columns are pinned at 8N — per-column LDE
/// right-sizing is dead as a pure win for this circuit.
#[test]
fn quotient_family_class_and_column_pinning_census() {
    use alloc::collections::BTreeSet;

    use crate::native::queries::{
        ADVICE_QUERIES, FIXED_QUERIES, INSTANCE_QUERIES, PERMUTATION_COLUMNS,
    };
    use crate::native::target::{
        ADVICE_COLUMNS, BLINDING_FACTORS, ColumnKind, FIXED_COLUMNS, PERMUTATION_CHUNK_LEN,
    };

    let programs = &*TREES;

    // Pin events: (kind, column, class multiple).
    let mut events: Vec<(QueryKind, usize, usize)> = Vec::new();
    let mut fixed_11_programs = Vec::new();

    for (index, program) in programs[..193].iter().enumerate() {
        let multiple = class_multiple(program.tree.degree());
        for_each_node(&program.tree, |node| match node {
            Expression::Advice(query) => events.push((
                QueryKind::Advice,
                ADVICE_QUERIES[usize::from(*query)].column,
                multiple,
            )),
            Expression::Fixed(query) => {
                let column = FIXED_QUERIES[usize::from(*query)].column;
                if column == 11 {
                    fixed_11_programs.push(index);
                }
                events.push((QueryKind::Fixed, column, multiple));
            }
            Expression::Instance(query) => events.push((
                QueryKind::Instance,
                INSTANCE_QUERIES[usize::from(*query)].column,
                multiple,
            )),
            _ => {}
        });
    }
    // Fixed column 11 is read only by the two 2N gate programs — the one
    // column whose extended form a class split could shrink.
    fixed_11_programs.dedup();
    assert_eq!(fixed_11_programs, [57, 60]);

    // Lookup product rules: z(ω)·(a′+β)(s′+γ) − z·(input+β)(table+γ),
    // times the active-rows mask — degree 1 + compression degrees + 1,
    // floored by the degree-3 permuted branch. The compressions pin
    // every column their expressions query at the rule class.
    let mut rule_degrees = Vec::new();
    for lookup in LOOKUPS {
        let compression_degree = |range: super::ExpressionRange| {
            range
                .indices()
                .map(|index| programs[index].tree.degree())
                .max()
                .unwrap()
        };
        let degree =
            (1 + compression_degree(lookup.inputs()) + compression_degree(lookup.tables())).max(3)
                + 1;
        rule_degrees.push(degree);
        let multiple = class_multiple(degree);
        for expression in lookup.inputs().indices().chain(lookup.tables().indices()) {
            for_each_node(&programs[expression].tree, |node| match node {
                Expression::Advice(query) => events.push((
                    QueryKind::Advice,
                    ADVICE_QUERIES[usize::from(*query)].column,
                    multiple,
                )),
                Expression::Fixed(query) => events.push((
                    QueryKind::Fixed,
                    FIXED_QUERIES[usize::from(*query)].column,
                    multiple,
                )),
                Expression::Instance(query) => events.push((
                    QueryKind::Instance,
                    INSTANCE_QUERIES[usize::from(*query)].column,
                    multiple,
                )),
                _ => {}
            });
        }
    }
    assert_eq!(rule_degrees, [6, 7, 7]);

    // Permutation set rules: z(ω)·∏(v+βσ+γ) − z·∏(v+βδⁱX+γ), times the
    // active-rows mask — degree = member columns + 2. Sets 0 and 1 carry
    // seven columns (degree 9, 8N); set 2 is fixed column 10 alone
    // (degree 3, 2N).
    let mut set_shapes = Vec::new();
    for chunk in PERMUTATION_COLUMNS.chunks(PERMUTATION_CHUNK_LEN) {
        let degree = chunk.len() + 2;
        let multiple = class_multiple(degree);
        set_shapes.push((chunk.len(), degree, multiple));
        for column in chunk {
            let kind = match column.kind {
                ColumnKind::Advice => QueryKind::Advice,
                ColumnKind::Fixed => QueryKind::Fixed,
                ColumnKind::Instance => QueryKind::Instance,
            };
            events.push((kind, column.index, multiple));
        }
    }
    assert_eq!(set_shapes, [(7, 9, 8), (7, 9, 8), (1, 3, 2)]);

    // The boundary and continuity terms (`l_0`/`l_last` rules and the
    // lookup permuted-column rules, degree 2–3) read only
    // argument-internal columns and pin no circuit column; their masses
    // are censused in `quotient_class_fold_work_census`.

    let mut advice_pins = [0usize; ADVICE_COLUMNS];
    let mut fixed_pins = [0usize; FIXED_COLUMNS];
    let mut instance_pin = 0usize;
    for (kind, column, multiple) in events {
        let slot = match kind {
            QueryKind::Advice => &mut advice_pins[column],
            QueryKind::Fixed => &mut fixed_pins[column],
            QueryKind::Instance => &mut instance_pin,
        };
        *slot = (*slot).max(multiple);
    }
    assert_eq!(advice_pins, [8; ADVICE_COLUMNS]);
    let mut expected_fixed = [8usize; FIXED_COLUMNS];
    expected_fixed[11] = 2;
    assert_eq!(fixed_pins, expected_fixed);
    // Pinned at 8N solely through permutation set 0.
    assert_eq!(instance_pin, 8);

    // Every rotation used anywhere is a whole number of base rows —
    // multiples of ROTATION_SCALE = 8 extended rows — so the stride-8
    // sub-cosets are rotation-closed and class folds read strided views
    // of existing arrays.
    let mut rotations: BTreeSet<i32> = ADVICE_QUERIES
        .iter()
        .chain(FIXED_QUERIES.iter())
        .chain(INSTANCE_QUERIES.iter())
        .map(|query| query.rotation)
        .collect();
    rotations.insert(1); // permutation and lookup product steps
    rotations.insert(-1); // lookup permuted-input continuity
    rotations.insert(-(BLINDING_FACTORS as i32 + 1)); // permutation last-row jump
    assert_eq!(rotations.into_iter().collect::<Vec<_>>(), [-6, -1, 0, 1]);
}

/// Fold-work mass per degree class — the attribution for evaluating
/// lower-degree terms on smaller sub-cosets. Mass = per-row multiplication
/// estimate × folded rows (one Action). The estimate counts tree body
/// multiplications plus one prepared-selector application and one y-fold
/// per gate program, and hand-counts of the fold closures in
/// `prover/quotient.rs` for the permutation and lookup argument terms.
/// These are structural operation counts, not measurements of quotient
/// substage time.
#[test]
fn quotient_class_fold_work_census() {
    use alloc::collections::BTreeMap;

    use crate::native::queries::PERMUTATION_COLUMNS;
    use crate::native::target::{EXTENDED_N, N, PERMUTATION_CHUNK_LEN};

    let programs = &*TREES;

    // (per-row multiplications, class multiple) per folded term.
    let gate_terms: Vec<(usize, usize)> = programs[..193]
        .iter()
        .map(|program| {
            let multiple = class_multiple(program.tree.degree());
            // Body multiplications exclude the prepared factor's own
            // muls and the root mul that applies it; add one selector
            // application and one y-fold back.
            let muls = match program.fixed_factor() {
                Some(factor) => {
                    multiplication_count(&program.tree) - multiplication_count(factor) + 1
                }
                None => multiplication_count(&program.tree) + 1,
            };
            (muls, multiple)
        })
        .collect();

    let permutation_terms: Vec<(usize, usize)> = {
        let chunks: Vec<_> = PERMUTATION_COLUMNS.chunks(PERMUTATION_CHUNK_LEN).collect();
        let mut terms = alloc::vec![(2, 1), (3, 2)]; // l_0 rule; l_last rule
        terms.reserve_exact(2 * chunks.len() - 1);
        terms.extend(core::iter::repeat_n((2, 1), chunks.len() - 1)); // continuity per later set
        for chunk in &chunks {
            // Per member column: β·σ, ×left, β·δⁱ·X, ×right — four muls —
            // plus the active-rows mask and the y-fold.
            terms.push((4 * chunk.len() + 2, class_multiple(chunk.len() + 2)));
        }
        terms
    };

    let lookup_terms: Vec<(usize, usize)> = LOOKUPS
        .iter()
        .flat_map(|lookup| {
            let compression_degree = |range: super::ExpressionRange| {
                range
                    .indices()
                    .map(|index| programs[index].tree.degree())
                    .max()
                    .unwrap()
            };
            let rule = class_multiple(
                (1 + compression_degree(lookup.inputs()) + compression_degree(lookup.tables()))
                    .max(3)
                    + 1,
            );
            // l_0; l_last; product rule; permuted boundary; permuted
            // continuity.
            [(2, 1), (3, 2), (6, rule), (2, 1), (3, 2)]
        })
        .collect();

    let mass = |terms: &[(usize, usize)]| {
        let dense: usize = terms.iter().map(|(muls, _)| muls * EXTENDED_N).sum();
        let classed: usize = terms
            .iter()
            .map(|(muls, multiple)| muls * multiple * N)
            .sum();
        (dense, classed)
    };
    // Gates: −483,328 of 15,515,648 (3.1% of the family's fold mass).
    assert_eq!(mass(&gate_terms), (15_515_648, 15_032_320));
    // Permutation: −196,608 of 1,228,800 (16.0%).
    assert_eq!(mass(&permutation_terms), (1_228_800, 1_032_192));
    // Lookups: −393,216 of 786,432 (50.0%).
    assert_eq!(mass(&lookup_terms), (786_432, 393_216));

    // Term census per class multiple (one Action): 30 of 215 folded
    // terms leave the 8N fold.
    let mut per_class = BTreeMap::new();
    for &(_, multiple) in gate_terms
        .iter()
        .chain(&permutation_terms)
        .chain(&lookup_terms)
    {
        *per_class.entry(multiple).or_insert(0usize) += 1;
    }
    assert_eq!(
        per_class.into_iter().collect::<Vec<_>>(),
        [(1, 9), (2, 12), (4, 9), (8, 185)]
    );
}

fn direct_gate_selectors(queries: &[Fp; super::GATE_QUERY_COUNT]) -> [Fp; 46] {
    [
        selector!(queries[38], 0, 1, 2, 3, 4),
        selector!(queries[38], 5, 1, 2, 3, 4),
        selector!(queries[38], 5, 0, 2, 3, 4),
        selector!(queries[39], 0, 1, 2),
        selector!(queries[39], 5, 1, 2),
        selector!(queries[39], 5, 0, 2),
        selector!(queries[39], 5, 0, 1),
        selector!(queries[38], 5, 0, 1, 3, 4),
        selector!(queries[38], 5, 0, 1, 2, 4),
        selector!(queries[38], 5, 0, 1, 2, 3),
        selector!(queries[40], 0, 1, 2, 3),
        selector!(queries[40], 5, 1, 2, 3),
        selector!(queries[40], 5, 0, 2, 3),
        selector!(queries[40], 5, 0, 1, 3),
        selector!(queries[40], 5, 0, 1, 2),
        selector!(queries[41], 0, 1, 2),
        selector!(queries[41], 5, 1, 2),
        selector!(queries[41], 5, 0, 2),
        selector!(queries[41], 5, 0, 1),
        selector!(queries[44], 0, 1, 2),
        selector!(queries[44], 5, 1, 2),
        selector!(queries[44], 5, 0, 2),
        selector!(queries[44], 5, 0, 1),
        selector!(queries[45], 0, 1, 2, 3, 4),
        selector!(queries[45], 5, 1, 2, 3, 4),
        selector!(queries[46], 0, 1, 2, 3, 4, 12),
        selector!(queries[46], 5, 1, 2, 3, 4, 12),
        selector!(queries[45], 5, 0, 2, 3, 4),
        selector!(queries[45], 5, 0, 1, 3, 4),
        selector!(queries[45], 5, 0, 1, 2, 4),
        selector!(queries[45], 5, 0, 1, 2, 3),
        selector!(queries[46], 5, 0, 2, 3, 4, 12),
        selector!(queries[47], 0, 1, 2, 3, 4, 12),
        selector!(queries[47], 5, 1, 2, 3, 4, 12),
        selector!(queries[47], 5, 0, 2, 3, 4, 12),
        selector!(queries[47], 5, 0, 1, 3, 4, 12),
        selector!(queries[47], 5, 0, 1, 2, 4, 12),
        selector!(queries[47], 5, 0, 1, 2, 3, 12),
        selector!(queries[47], 5, 0, 1, 2, 3, 4),
        selector!(queries[48], 0, 1, 2, 3, 4, 12),
        selector!(queries[48], 5, 1, 2, 3, 4, 12),
        selector!(queries[48], 5, 0, 2, 3, 4, 12),
        selector!(queries[48], 5, 0, 1, 3, 4, 12),
        selector!(queries[48], 5, 0, 1, 2, 4, 12),
        selector!(queries[48], 5, 0, 1, 2, 3, 12),
        selector!(queries[48], 5, 0, 1, 2, 3, 4),
    ]
}

#[test]
fn shared_selector_preparation_matches_independent_chains() {
    let mut state = 0xd38b_3c45_81d2_76f1u64;
    for _ in 0..128 {
        let queries = GATE_QUERY_DESCRIPTORS.map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            <Fp>::from_u64(state).square().square()
        });
        let prepared = prepare_gate_selectors(&queries);
        let direct = direct_gate_selectors(&queries);
        assert_eq!(
            reduced_values(&(&prepared[..35])),
            reduced_values(&(&direct[..35]))
        );
        assert_eq!(
            reduced_values(&(&prepared[35..38])),
            reduced_values(&(&direct[39..42]))
        );
        for (bank, query) in [46, 47, 48].into_iter().enumerate() {
            for omit in 4..=7 {
                let expected = (1..=7)
                    .filter(|root| *root != omit)
                    .fold(queries[query], |acc, root| {
                        acc.mul(&<Fp>::from_u64(root).sub(&queries[query]))
                    });
                assert_eq!(
                    prepared[38 + bank * 4 + omit as usize - 4].reduce(),
                    expected.reduce()
                );
            }
        }
    }
}

/// The generated bilinear kernel's factor pair reproduces the source
/// sum `Σ body_i · P[i]` over gate 6's programs 13..17 on broad frames
/// and degenerate challenges, including `y = 0`; the block's programs
/// all carry gate 6's selector, which the kernel leaves to the fold.
#[test]
fn generated_bilinear_kernel_matches_source_body_sum() {
    let selector = super::program_trees(GATES[6].start)
        .unwrap()
        .fixed_factor()
        .unwrap();
    let bodies: [&Expression; BILINEAR_BLOCK_LEN] = core::array::from_fn(|offset| {
        let trees = super::program_trees(GATE_6_BILINEAR_FIRST + offset).unwrap();
        assert_eq!(trees.fixed_factor(), Some(selector));
        trees.dynamic_body().unwrap()
    });
    let base = GATE_QUERY_DESCRIPTORS.map(|(kind, index)| query_value(kind, index));
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        <Fp>::from_u64(state).square()
    };
    let mut frames = [
        base,
        [<Fp>::ZERO; GATE_QUERY_COUNT],
        [<Fp>::ONE; GATE_QUERY_COUNT],
    ]
    .to_vec();
    frames.reserve_exact(32);
    for _ in 0..32 {
        frames.push(core::array::from_fn(|_| next()));
    }
    let mut checked = 0;
    for queries in &frames {
        for y in [<Fp>::ZERO, <Fp>::ONE, <Fp>::from_u64(2), next()] {
            let powers: [Fp; GATE_CONSTRAINT_COUNT] =
                core::array::from_fn(|slot| y.pow_u64((GATE_CONSTRAINT_COUNT - 1 - slot) as u64));
            let (left, right) = weighted_bilinear_kernel_13(queries, &y, &powers);
            let mut expected = <Fp>::ZERO;
            for (offset, body) in bodies.iter().enumerate() {
                let value = evaluate(body, &mut |kind, index| {
                    GATE_QUERY_DESCRIPTORS
                        .iter()
                        .position(|descriptor| *descriptor == (kind, index))
                        .map(|frame_index| queries[frame_index])
                        .ok_or(crate::Error::InternalInvariant)
                })
                .unwrap();
                expected = value.mul_add(&powers[GATE_6_BILINEAR_FIRST + offset], &expected);
            }
            assert_eq!((left.mul(&right)).reduce(), (expected).reduce());
            checked += 1;
        }
    }
    assert_eq!(checked, 35 * 4);
}

/// Every generated shared-factor kernel's `factor · weighted` reproduces
/// the source sum `Σ body_i · P[i]` over its programs on broad frames and
/// degenerate challenges, its programs all lie in one gate under that
/// gate's selector, and the kernel list matches `FACTOR_GROUPS`.
#[test]
fn generated_factor_kernels_match_source_body_sums() {
    type Kernel = fn(&[Fp; GATE_QUERY_COUNT], &[Fp; GATE_CONSTRAINT_COUNT]) -> (Fp, Fp);
    let kernels: [Kernel; 4] = [
        weighted_factor_kernel_67,
        weighted_factor_kernel_105,
        weighted_factor_kernel_106,
        weighted_factor_kernel_186,
    ];
    let base = GATE_QUERY_DESCRIPTORS.map(|(kind, index)| query_value(kind, index));
    let mut state = 0x2f6e_2b1a_5c3d_9e87u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        <Fp>::from_u64(state).square()
    };
    let mut frames = [
        base,
        [<Fp>::ZERO; GATE_QUERY_COUNT],
        [<Fp>::ONE; GATE_QUERY_COUNT],
    ]
    .to_vec();
    frames.reserve_exact(16);
    for _ in 0..16 {
        frames.push(core::array::from_fn(|_| next()));
    }
    for (programs, kernel) in FACTOR_GROUPS.iter().zip(kernels) {
        let gate = GATES
            .iter()
            .find(|gate| gate.indices().contains(&programs[0]))
            .expect("group programs are gate constraints");
        let selector = super::program_trees(gate.start)
            .unwrap()
            .fixed_factor()
            .unwrap();
        for &program in programs.iter() {
            assert!(gate.indices().contains(&program));
            assert_eq!(
                super::program_trees(program).unwrap().fixed_factor(),
                Some(selector)
            );
        }
        for queries in &frames {
            for y in [<Fp>::ZERO, <Fp>::ONE, <Fp>::from_u64(2), next()] {
                let powers: [Fp; GATE_CONSTRAINT_COUNT] = core::array::from_fn(|slot| {
                    y.pow_u64((GATE_CONSTRAINT_COUNT - 1 - slot) as u64)
                });
                let (factor, weighted) = kernel(queries, &powers);
                let mut expected = <Fp>::ZERO;
                for &program in programs.iter() {
                    let body = super::program_trees(program)
                        .unwrap()
                        .dynamic_body()
                        .unwrap();
                    let value = evaluate(body, &mut |kind, index| {
                        GATE_QUERY_DESCRIPTORS
                            .iter()
                            .position(|descriptor| *descriptor == (kind, index))
                            .map(|frame_index| queries[frame_index])
                            .ok_or(crate::Error::InternalInvariant)
                    })
                    .unwrap();
                    expected = value.mul_add(&powers[program], &expected);
                }
                assert_eq!(
                    (factor.mul(&weighted)).reduce(),
                    (expected).reduce(),
                    "group {programs:?}"
                );
            }
        }
    }
}

/// The distributed complementary-control forms equal the direct
/// `v·x + (1 − v)·x'` products they replace, for controls inside and
/// far outside `{0, 1}` and arbitrary operands.
#[test]
fn complementary_control_identities_match_direct_products() {
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        <Fp>::from_u64(state).square().square()
    };
    let mut controls = [
        <Fp>::ZERO,
        <Fp>::ONE,
        <Fp>::ONE.neg(),
        <Fp>::from_u64(2),
        <Fp>::from_u64(2).neg(),
        <Fp>::from_u64(0xffff_ffff_ffff_ffff),
    ]
    .to_vec();
    controls.reserve_exact(32);
    for _ in 0..32 {
        controls.push(next());
    }
    for &v in controls.iter() {
        let w = <Fp>::ONE.sub(&v);
        for _ in 0..4 {
            let (a, b, c, d) = (next(), next(), next(), next());
            assert_eq!(
                (super::complementary_blend(&v, &a, &b)).reduce(),
                (v.mul(&a.sub(&b)).add(&w.mul(&a.add(&b)))).reduce()
            );
            // Gate 15's pair: `v·a + w·(a − b)` and `v·c + w·(c + d)`.
            assert_eq!(
                (a.sub(&w.mul(&b))).reduce(),
                (v.mul(&a).add(&w.mul(&a.sub(&b)))).reduce()
            );
            assert_eq!(
                (c.add(&w.mul(&d))).reduce(),
                (v.mul(&c).add(&w.mul(&c.add(&d)))).reduce()
            );
            let (select_0, select_1) = super::complementary_select(&v, &a, &b, &c, &d);
            assert_eq!(
                (select_0).reduce(),
                (c.sub(&v.mul(&b).add(&w.mul(&a)))).reduce()
            );
            assert_eq!(
                (select_1).reduce(),
                (d.sub(&v.mul(&a).add(&w.mul(&b)))).reduce()
            );
        }
    }
}

/// The combined digit/range evaluations equal independently weighted
/// power sums and direct root products on arbitrary off-domain frames,
/// every digit, and zero/unit/negative-unit challenges. Fixed row
/// preparation must not depend on the Action's advice queries.
#[test]
fn combined_digit_polynomials_match_separate_constraints() {
    use crate::native::prover::fold_order::TERMS_PER_ACTION;

    let mut state = 0x6a09_e667_f3bc_c909u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        <Fp>::from_u64(state).square().square()
    };
    let power_sum = |t: &Fp, q: &[Fp; super::GATE_QUERY_COUNT]| {
        let mut power = <Fp>::ONE;
        let mut sum = q[25];
        for coefficient in &q[27..=33] {
            power = power.mul(t);
            sum = sum.add(&coefficient.mul(&power));
        }
        sum.sub(&q[0])
    };
    let mut frames = [[<Fp>::ZERO; GATE_QUERY_COUNT]; 40];
    for (index, frame) in frames.iter_mut().enumerate() {
        if index > 0 {
            for value in frame.iter_mut() {
                *value = next();
            }
        }
    }
    for y in [<Fp>::ZERO, <Fp>::ONE, <Fp>::ONE.neg(), next(), next()] {
        let powers = core::array::from_fn(|slot| y.pow_u64((TERMS_PER_ACTION - 1 - slot) as u64));
        let y_powers = core::array::from_fn(|power| y.pow_u64(power as u64));
        let challenge = GateChallengeCoefficients::new(&powers, y.pow_u64(37), y);
        for frame in &frames {
            let prepared = prepare_gate_selectors(frame);
            let selectors = &prepared;
            let coefficients = GateRowCoefficients::for_row(
                selectors,
                ROW_COEFFICIENT_QUERY_SLOTS.map(|slot| frame[slot]),
                &powers,
                &y_powers,
                &challenge,
                true,
            );
            let digits = coefficients.digits.as_ref().unwrap();
            let inputs = (0..8).map(<Fp>::from_u64).chain([
                <Fp>::ONE.neg(),
                frame[4],
                frame[4].sub(&frame[14].mul_by_8()),
                next(),
            ]);
            for t in inputs {
                let range = selector!(t, 5, 0, 1, 2, 3, 4, 12);
                let digit = power_sum(&t, frame);
                assert_eq!(super::digit_polynomial(&t, frame).reduce(), digit.reduce());
                for (bank, (digit_slot, range_slot, selector_slot)) in
                    [(56, 55, 42), (59, 62, 43)].into_iter().enumerate()
                {
                    let expected = digit
                        .mul(&powers[digit_slot])
                        .add(&range.mul(&powers[range_slot]))
                        .mul(&frame[selector_slot]);
                    let combined =
                        super::combined_digit_polynomial(&t, &digits.polynomials[bank], &frame[0])
                            .mul(&digits.weights[bank]);
                    assert_eq!(combined.reduce(), expected.reduce());
                }
            }
        }
    }
}

/// The MDS-carried weights reproduce gate 21's selector-weighted
/// fold of its three original bodies for arbitrary selector, slot powers,
/// fifth powers and next-state values, including zero and unit weights.
#[test]
fn mds_weights_match_row_fold() {
    let mut state = 0x3c6e_f372_fe94_f82bu64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        <Fp>::from_u64(state).square()
    };
    for selector in [<Fp>::ZERO, <Fp>::ONE, <Fp>::ONE.neg(), next(), next()] {
        for _ in 0..8 {
            let slot_powers = [next(), next(), next()];
            let fifth_powers = [next(), next(), next()];
            let next_state = [next(), next(), next()];
            let mut powers = [<Fp>::ZERO; GATE_CONSTRAINT_COUNT];
            powers[75..78].copy_from_slice(&slot_powers);
            let mut selectors = [<Fp>::ZERO; PREPARED_GATE_SELECTOR_COUNT];
            selectors[18] = selector;
            let challenge = GateChallengeCoefficients::new(&powers, <Fp>::ONE, <Fp>::ONE);
            let coefficients = GateRowCoefficients::for_row(
                &selectors,
                [<Fp>::ZERO; ROW_COEFFICIENT_QUERY_SLOTS.len()],
                &powers,
                &[<Fp>::ONE; MAX_GATE_CONSTRAINTS + 1],
                &challenge,
                false,
            );
            let mut folded = RowSum::new();
            for (power, weight) in fifth_powers.iter().zip(&coefficients.mds_21) {
                folded.add_product(power, weight);
            }
            for (value, weight) in next_state.iter().zip(&coefficients.negated_weights_21) {
                folded.add_product(value, weight);
            }

            let mut expected = <Fp>::ZERO;
            for (row, (slot_power, value)) in slot_powers.iter().zip(&next_state).enumerate() {
                let body =
                    <Fp>::sum_of_products(&fifth_powers, &super::POSEIDON_MDS[row]).sub(value);
                expected = expected.add(&selector.mul(slot_power).mul(&body));
            }
            assert_eq!((folded.finish()).reduce(), (expected).reduce());
        }
    }
}

/// The paired-root forms equal their direct products on and away from
/// the roots, including their pair-product constants.
#[test]
fn paired_root_range_polynomials_match_direct_products() {
    assert_eq!((super::TWELVE).reduce(), (<Fp>::from_u64(12)).reduce());
    assert_eq!((super::SIXTY).reduce(), (<Fp>::from_u64(60)).reduce());
    let mut inputs = (0..=16u64).map(<Fp>::from_u64).collect::<Vec<_>>();
    inputs.reserve_exact(64 + 6);
    inputs.push(<Fp>::ONE.neg());
    inputs.push(<Fp>::from_u64(2).neg());
    inputs.push(<Fp>::from_u64(7).neg());
    inputs.push(super::TWELVE);
    inputs.push(super::SIXTY);
    inputs.push(<Fp>::from_u64(0xffff_ffff_ffff_ffff));
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    for _ in 0..64 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        inputs.push(<Fp>::from_u64(state).square().square());
    }
    for &x in inputs.iter() {
        assert_eq!(
            (super::range_8(&x)).reduce(),
            (selector!(x, 5, 0, 1, 2, 3, 4, 12)).reduce()
        );
        assert_eq!(
            (super::range_4(&x)).reduce(),
            (selector!(x, 5, 0, 1)).reduce()
        );
    }
    for root in 0..8u64 {
        assert!(super::range_8(&<Fp>::from_u64(root)).is_zero());
    }
    for root in 0..4u64 {
        assert!(super::range_4(&<Fp>::from_u64(root)).is_zero());
    }
    assert!(!super::range_8(&<Fp>::from_u64(8)).is_zero());
    assert!(!super::range_4(&<Fp>::from_u64(4)).is_zero());
}

#[test]
fn fused_gate_kernel_matches_tree_reference() {
    assert!(matches!(
        GATE_QUERY_DESCRIPTORS[46],
        (QueryKind::Fixed, PREPARED_GATE_SELECTOR_FIXED_QUERY)
    ));
    // The row coefficients are shared across Actions, so every frame
    // slot they read must be a fixed (Action-independent) query.
    for slot in ROW_COEFFICIENT_QUERY_SLOTS {
        assert!(matches!(
            GATE_QUERY_DESCRIPTORS[slot],
            (QueryKind::Fixed, _)
        ));
    }
    for (index, descriptor) in GATE_QUERY_DESCRIPTORS.iter().enumerate() {
        assert!(!GATE_QUERY_DESCRIPTORS[..index].contains(descriptor));
    }

    let expression_indices = GATES
        .iter()
        .flat_map(|gate| gate.indices())
        .collect::<Vec<_>>();
    assert_eq!(expression_indices, (0..193).collect::<Vec<_>>());

    let base_queries = GATE_QUERY_DESCRIPTORS.map(|(kind, index)| query_value(kind, index));
    let mut frames = [
        <Fp>::ZERO,
        <Fp>::ONE,
        constant(0),
        constant(1),
        constant(2),
        constant(3),
        constant(4),
        constant(12),
        <Fp>::from_u64(0x1234_5678_9abc_def0),
    ]
    .map(|selector_value| {
        let mut queries = base_queries;
        for index in [38, 39, 40, 41, 44, 45, 46, 47, 48] {
            queries[index] = selector_value;
        }
        queries
    })
    .to_vec();
    // Vary each family independently too: using one value everywhere
    // would miss an accidental swap of the reconstructed tail queries.
    frames.reserve_exact(64);
    let mut state = 0xc648_a7db_8302_e951u64;
    for _ in 0..64 {
        frames.push(GATE_QUERY_DESCRIPTORS.map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            <Fp>::from_u64(state).square().square()
        }));
    }
    // Also use the upper half of the loose Montgomery range. These
    // represent the same fields but stress bounded product-sum carries.
    let modulus = <udon::field::PallasBase as udon::field::PrimeModulus>::MODULUS;
    let loose = frames
        .iter()
        .map(|frame| {
            frame.map(|value| {
                let mut limbs = value.reduce().montgomery_limbs();
                let mut carry = 0u128;
                for (limb, p) in limbs.iter_mut().zip(modulus) {
                    let sum = u128::from(*limb) + u128::from(p) + carry;
                    *limb = sum as u64;
                    carry = sum >> 64;
                }
                Fp::from_montgomery_limbs(limbs)
            })
        })
        .collect::<Vec<_>>();
    frames.extend(loose);
    for queries in frames {
        let prepared_row = prepare_gate_selectors(&queries);
        let prepared_selectors: [Fp; PREPARED_GATE_SELECTOR_COUNT] = prepared_row
            [..PREPARED_GATE_SELECTOR_COUNT]
            .try_into()
            .unwrap();
        let direct = direct_gate_selectors(&queries);
        assert_eq!(
            reduced_values(&(&prepared_selectors[..35])),
            reduced_values(&(&direct[..35]))
        );
        assert_eq!(
            reduced_values(&(&prepared_selectors[35..38])),
            reduced_values(&(&direct[39..42]))
        );
        for y in [
            <Fp>::ZERO,
            <Fp>::ONE,
            <Fp>::ONE.neg(),
            <Fp>::from_u64(2),
            <Fp>::from_u64(0x1234_5678_9abc_def0),
        ] {
            let mut y_powers = [<Fp>::ONE; MAX_GATE_CONSTRAINTS + 1];
            for exponent in 1..y_powers.len() {
                y_powers[exponent] = y_powers[exponent - 1].mul(&y);
            }
            // The absolute power of every gate slot in a 193-slot block
            // (the prover's table also carries its rule-block offset).
            let slot_power =
                |program: usize| y.pow_u64((expression_indices.len() - 1 - program) as u64);
            let powers: [Fp; GATE_CONSTRAINT_COUNT] = core::array::from_fn(slot_power);

            // `y^37` is formed independently here; the prover derives it
            // from its y-power table.
            let challenge = GateChallengeCoefficients::new(&powers, y.pow_u64(37), y);
            let coefficients = GateRowCoefficients::for_row(
                &prepared_selectors,
                ROW_COEFFICIENT_QUERY_SLOTS.map(|slot| queries[slot]),
                &powers,
                &y_powers,
                &challenge,
                true,
            );
            let mut row = RowSum::new();
            evaluate_gates::<false>(
                &queries,
                &SinsemillaCubics::from_frame(&queries),
                &prepared_selectors,
                &coefficients,
                &powers,
                &mut row,
            );
            let mut fused = row.finish();
            // Exercise the combined nonlinear weights on the same
            // arbitrary off-domain frames as the tree oracle. Restoring
            // the affine bodies must reproduce the complete 8N kernel.
            let mut shared = RowSum::new();
            evaluate_gates::<true>(
                &queries,
                &SinsemillaCubics::from_frame(&queries),
                &prepared_selectors,
                &coefficients,
                &powers,
                &mut shared,
            );
            let affine = evaluate_affine_gates::<true>(
                &queries,
                &<Fp>::ONE,
                &prepared_selectors,
                &coefficients,
                &powers,
            );
            assert_eq!(shared.finish().add(&affine).reduce(), fused.reduce());
            // The fused kernel skips the carved small-class slots;
            // adding their class kernels under the slots' absolute
            // y-powers must reproduce the full interpreted stream.
            evaluate_gates_2n(
                &|frame_index| queries[frame_index],
                &GATE_PROGRAMS_2N.map(slot_power),
                &mut fused,
            );
            evaluate_gates_4n(
                &|frame_index| queries[frame_index],
                &prepared_selectors,
                &Gate4NCoefficients::new(GATE_PROGRAMS_4N.map(slot_power)),
                &mut fused,
            );

            let mut interpreted = <Fp>::ZERO;
            for &expression in &expression_indices {
                let value = evaluate(
                    &super::program_trees(expression).unwrap().tree,
                    &mut |kind, index| {
                        GATE_QUERY_DESCRIPTORS
                            .iter()
                            .position(|descriptor| *descriptor == (kind, index))
                            .map(|frame_index| queries[frame_index])
                            .ok_or(crate::Error::InternalInvariant)
                    },
                )
                .unwrap();
                interpreted = interpreted.mul_add(&y, &value);
            }

            assert_eq!((fused).reduce(), (interpreted).reduce());
        }
    }
}

/// Per Action, the kernel with the affine bodies skipped, plus one
/// evaluation of the affine family on the challenge-weighted aggregated
/// frame, reproduces the complete fused kernel exactly — for one to four
/// Actions sharing their fixed queries, under degenerate and arbitrary
/// challenges. Both the 8N and 4N passes read advice only through
/// `AFFINE_QUERY_SLOTS`; the 4N pass also reads weighted fixed constants.
#[test]
fn shared_affine_pass_matches_fused_kernel() {
    use crate::native::prover::fold_order::TERMS_PER_ACTION;

    let base = GATE_QUERY_DESCRIPTORS.map(|(kind, index)| query_value(kind, index));
    let mut state = 0x5eed_1234_abcd_0001u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let value = <Fp>::from_u64(state).square();
        if state & 1 == 0 {
            value
        } else {
            // Mix reduced and upper loose representatives across Actions.
            let modulus = <udon::field::PallasBase as udon::field::PrimeModulus>::MODULUS;
            let mut limbs = value.reduce().montgomery_limbs();
            let mut carry = 0u128;
            for (limb, p) in limbs.iter_mut().zip(modulus) {
                carry += u128::from(*limb) + u128::from(p);
                *limb = carry as u64;
                carry >>= 64;
            }
            Fp::from_montgomery_limbs(limbs)
        }
    };
    let prepared_row = prepare_gate_selectors(&base);
    let prepared_selectors: [Fp; PREPARED_GATE_SELECTOR_COUNT] = prepared_row
        [..PREPARED_GATE_SELECTOR_COUNT]
        .try_into()
        .unwrap();
    for action_count in 1..=4usize {
        for y in [
            <Fp>::ZERO,
            <Fp>::ONE,
            <Fp>::ONE.neg(),
            <Fp>::from_u64(0x1234_5678_9abc_def0),
            next(),
        ] {
            let mut y_powers = [<Fp>::ONE; MAX_GATE_CONSTRAINTS + 1];
            for exponent in 1..y_powers.len() {
                y_powers[exponent] = y_powers[exponent - 1].mul(&y);
            }
            let powers: [Fp; GATE_CONSTRAINT_COUNT] =
                core::array::from_fn(|index| y.pow_u64((TERMS_PER_ACTION - 1 - index) as u64));
            let challenge = GateChallengeCoefficients::new(&powers, y.pow_u64(37), y);
            let coefficients = GateRowCoefficients::for_row(
                &prepared_selectors,
                ROW_COEFFICIENT_QUERY_SLOTS.map(|slot| base[slot]),
                &powers,
                &y_powers,
                &challenge,
                true,
            );
            let weights = (0..action_count)
                .map(|action| y.pow_u64((TERMS_PER_ACTION * (action_count - 1 - action)) as u64))
                .collect::<Vec<_>>();
            let weight_sum = weights
                .iter()
                .fold(<Fp>::ZERO, |sum, weight| sum.add(weight));
            let frames = (0..action_count)
                .map(|_| {
                    let mut frame = base;
                    for value in frame.iter_mut().take(25) {
                        *value = next();
                    }
                    frame
                })
                .collect::<Vec<_>>();

            let mut fused = <Fp>::ZERO;
            let mut split = <Fp>::ZERO;
            let mut aggregated = [<Fp>::ZERO; GATE_QUERY_COUNT];
            for (frame, weight) in frames.iter().zip(&weights) {
                let mut complete = RowSum::new();
                evaluate_gates::<false>(
                    frame,
                    &SinsemillaCubics::from_frame(frame),
                    &prepared_selectors,
                    &coefficients,
                    &powers,
                    &mut complete,
                );
                fused = fused.add(&complete.finish().mul(weight));
                let mut skipped = RowSum::new();
                evaluate_gates::<true>(
                    frame,
                    &SinsemillaCubics::from_frame(frame),
                    &prepared_selectors,
                    &coefficients,
                    &powers,
                    &mut skipped,
                );
                split = split.add(&skipped.finish().mul(weight));
                for slot in 0..GATE_QUERY_COUNT {
                    aggregated[slot] = aggregated[slot].add(&frame[slot].mul(weight));
                }
            }
            let affine = evaluate_affine_gates::<true>(
                &aggregated,
                &weight_sum,
                &prepared_selectors,
                &coefficients,
                &powers,
            );
            assert_eq!(
                (fused).reduce(),
                (split.add(&affine)).reduce(),
                "actions {action_count}"
            );

            let class_coefficients =
                Gate4NCoefficients::new(GATE_PROGRAMS_4N.map(|slot| powers[slot]));
            let mut complete_4n = Fp::ZERO;
            let mut shared_4n = RowSum::new();
            for (frame, weight) in frames.iter().zip(&weights) {
                let mut value = Fp::ZERO;
                evaluate_gates_4n(
                    &|slot| frame[slot],
                    &prepared_selectors,
                    &class_coefficients,
                    &mut value,
                );
                complete_4n = complete_4n.add(&value.mul(weight));
                let curve_weight = Fp::sum_of_products(
                    &[frame[42], frame[43]],
                    &[powers[58].mul(weight), powers[61].mul(weight)],
                );
                shared_4n.add_product(&first_curve_relation(&|slot| frame[slot]), &curve_weight);
            }
            evaluate_affine_gates_4n::<true>(
                &|slot| {
                    assert!(slot >= 25 || AFFINE_QUERY_SLOTS.contains(&slot));
                    aggregated[slot]
                },
                &weight_sum,
                &prepared_selectors,
                &class_coefficients,
                &mut shared_4n,
            );
            assert_eq!(
                shared_4n.finish().reduce(),
                complete_4n.reduce(),
                "4N actions {action_count}"
            );

            let mut perturbed = aggregated;
            for (slot, value) in perturbed.iter_mut().enumerate() {
                if !AFFINE_QUERY_SLOTS.contains(&slot) {
                    *value = next();
                }
            }
            assert_eq!(
                (evaluate_affine_gates::<true>(
                    &perturbed,
                    &weight_sum,
                    &prepared_selectors,
                    &coefficients,
                    &powers,
                ))
                .reduce(),
                (affine).reduce()
            );
        }
    }
}

#[test]
#[ignore = "manual generated-gate row benchmark"]
fn measure_gate_row_kernel() {
    const ROWS: usize = 1 << 12;

    let queries = GATE_QUERY_DESCRIPTORS.map(|(kind, index)| query_value(kind, index));
    let prepared_row = prepare_gate_selectors(&queries);
    let prepared_selectors: [Fp; PREPARED_GATE_SELECTOR_COUNT] = prepared_row
        [..PREPARED_GATE_SELECTOR_COUNT]
        .try_into()
        .unwrap();
    let y = <Fp>::from_u64(0x1234_5678_9abc_def0);
    let y_37 = y.pow_u64(37);
    let mut y_powers = [<Fp>::ONE; MAX_GATE_CONSTRAINTS + 1];
    for exponent in 1..y_powers.len() {
        y_powers[exponent] = y_powers[exponent - 1].mul(&y);
    }
    let powers: [Fp; GATE_CONSTRAINT_COUNT] =
        core::array::from_fn(|index| y.pow_u64((GATE_CONSTRAINT_COUNT - 1 - index) as u64));
    let powers_2n = GATE_PROGRAMS_2N.map(|program| powers[program]);
    let coefficients_4n = Gate4NCoefficients::new(GATE_PROGRAMS_4N.map(|program| powers[program]));
    let challenge_coefficients = GateChallengeCoefficients::new(&powers, y_37, y);
    let repetitions = std::env::var("SENSEI_BENCH_REPETITIONS")
        .map(|value| value.parse::<usize>().unwrap())
        .unwrap_or(20);

    // Match the relative class sizes of one Action's gate fold, including
    // its shared row-coefficient preparation. Black-box the frame so the
    // repeated input cannot move row arithmetic outside the timed loop.
    for _ in 0..repetitions {
        let mut accumulator = <Fp>::ZERO;
        let started = Instant::now();
        for index in 0..ROWS {
            let queries = black_box(&queries);
            let selectors = black_box(&prepared_selectors);
            let coefficients = GateRowCoefficients::for_row(
                selectors,
                ROW_COEFFICIENT_QUERY_SLOTS.map(|slot| queries[slot]),
                &powers,
                &y_powers,
                &challenge_coefficients,
                false,
            );
            let mut row = RowSum::new();
            evaluate_gates::<false>(
                queries,
                &SinsemillaCubics::from_frame(queries),
                selectors,
                &coefficients,
                &powers,
                &mut row,
            );
            accumulator = accumulator.add(&row.finish());
            if index % 2 == 0 {
                evaluate_gates_4n(
                    &|slot| queries[slot],
                    selectors,
                    &coefficients_4n,
                    &mut accumulator,
                );
            }
            if index % 4 == 0 {
                evaluate_gates_2n(&|slot| queries[slot], &powers_2n, &mut accumulator);
            }
        }
        let elapsed = started.elapsed();
        black_box(accumulator);
        eprintln!("SENSEI_GATE_ROW_NS={}", elapsed.as_nanos());
    }
}

#[test]
#[ignore = "manual generated-gate fold benchmark"]
fn measure_gate_fold_kernel() {
    const ROWS: usize = 1 << 15;

    let queries = GATE_QUERY_DESCRIPTORS.map(|(kind, index)| query_value(kind, index));
    let prepared_row = prepare_gate_selectors(&queries);
    let prepared_selectors: [Fp; PREPARED_GATE_SELECTOR_COUNT] = prepared_row
        [..PREPARED_GATE_SELECTOR_COUNT]
        .try_into()
        .unwrap();
    let y = <Fp>::from_u64(0x1234_5678_9abc_def0);
    let mut y_powers = [<Fp>::ONE; MAX_GATE_CONSTRAINTS + 1];
    for exponent in 1..y_powers.len() {
        y_powers[exponent] = y_powers[exponent - 1].mul(&y);
    }
    let powers: [Fp; GATE_CONSTRAINT_COUNT] =
        core::array::from_fn(|index| y.pow_u64((GATE_CONSTRAINT_COUNT - 1 - index) as u64));
    let challenge = GateChallengeCoefficients::new(&powers, y.pow_u64(37), y);
    let coefficients = GateRowCoefficients::for_row(
        &prepared_selectors,
        ROW_COEFFICIENT_QUERY_SLOTS.map(|slot| queries[slot]),
        &powers,
        &y_powers,
        &challenge,
        false,
    );
    let mut accumulator = <Fp>::from_u64(0xfedc_ba98_7654_3210);

    let started = Instant::now();
    for _ in 0..ROWS {
        let mut row = RowSum::new();
        evaluate_gates::<false>(
            black_box(&queries),
            &SinsemillaCubics::from_frame(black_box(&queries)),
            black_box(&prepared_selectors),
            black_box(&coefficients),
            black_box(&powers),
            &mut row,
        );
        accumulator = accumulator.add(&row.finish());
    }
    let elapsed = started.elapsed();

    black_box(accumulator);
    eprintln!("SENSEI_GATE_FOLD_NS={}", elapsed.as_nanos());
}
