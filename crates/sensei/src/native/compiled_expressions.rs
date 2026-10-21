//! Compact expression schedules generated from the shared circuit recipes.
//!
//! `sensei-macros` validates and interns trees on the host, then emits a
//! topological instruction table for each entry's reachable DAG. A single
//! non-generic loop evaluates each distinct node once per row. Binding borrows
//! and validates the required columns once; row reads use those slices and
//! pre-normalized rotations directly. Scratch is local to the binding and
//! overwritten on every evaluation, including when rows are revisited.
//!
//! Structural IDs and fixed-factor splits remain compiled metadata. Local
//! value numbers address compact scratch; they do not define tree equality.

use crate::Error;
use alloc::boxed::Box;

use super::{
    field::Fp,
    generated_expressions::{QueryKind, constant, scale},
    invariant::{self, Invariant},
    target::N,
};

#[derive(Clone, Copy)]
pub(crate) struct CompiledExpression {
    id: usize,
    fixed_only: bool,
    schedule: &'static ExpressionSchedule,
}

impl PartialEq for CompiledExpression {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for CompiledExpression {}

impl CompiledExpression {
    pub(crate) fn is_fixed_only(self) -> bool {
        self.fixed_only
    }

    /// Resolves only this entry's queries. A fixed-only expression needs no
    /// advice or instance columns. Shape failures are reported here, before
    /// any row arithmetic, in first-use query order with repeats removed.
    /// Only this small binding step is generic over column storage; the
    /// evaluator and its arithmetic are shared by all callers.
    pub(crate) fn bind<'a, A: AsRef<[Fp]>>(
        self,
        fixed: &'a [[Fp; N]],
        advice: &'a [A],
        instance: &'a [Fp],
    ) -> Result<Evaluation<'a>, Error> {
        let queries = self
            .schedule
            .queries
            .iter()
            .map(|query| {
                let column = match query.kind {
                    QueryKind::Fixed => fixed
                        .get(query.column)
                        .ok_or_else(|| invariant::failed(Invariant::ColumnShape))?,
                    QueryKind::Advice => advice
                        .get(query.column)
                        .and_then(|column| column.as_ref().try_into().ok())
                        .ok_or_else(|| invariant::failed(Invariant::ColumnShape))?,
                    QueryKind::Instance => {
                        if query.column != 0 {
                            return Err(invariant::failed(Invariant::InstanceColumnShape));
                        }
                        instance
                            .try_into()
                            .map_err(|_| invariant::failed(Invariant::InstanceColumnShape))?
                    }
                };
                Ok(ResolvedQuery {
                    column,
                    rotation: query.rotation,
                })
            })
            .collect::<Result<Box<[_]>, Error>>()?;
        Ok(Evaluation {
            instructions: self.schedule.instructions,
            queries,
            values: alloc::vec![ <Fp>::ZERO; self.schedule.instructions.len()].into_boxed_slice(),
        })
    }

    pub(crate) fn bind_fixed(self, fixed: &[[Fp; N]]) -> Result<Evaluation<'_>, Error> {
        self.bind(fixed, &[] as &[&[Fp]], &[])
    }
}

/// Six bytes per instruction; u16 operands are validated during expansion.
/// The destination is the instruction's position, and every source precedes
/// it. Constant and query operands address separate immutable pools.
#[derive(Clone, Copy)]
#[repr(u8)]
enum Instruction {
    Query(u16),
    Constant(u16),
    Sum(u16, u16),
    Product(u16, u16),
    Negated(u16),
    ConstantScaled(u16, u16),
}

const _: () = assert!(core::mem::size_of::<Instruction>() == 6);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ExpressionQuery {
    kind: QueryKind,
    column: usize,
    rotation: usize,
}

struct ExpressionSchedule {
    instructions: &'static [Instruction],
    queries: &'static [ExpressionQuery],
}

struct ResolvedQuery<'a> {
    column: &'a [Fp; N],
    rotation: usize,
}

/// A concrete evaluation context borrowing one set of columns. Each worker
/// owns its scratch, which is reused for an entire row pass. Nothing is
/// cached across bindings, witnesses, or blinding updates.
pub(crate) struct Evaluation<'a> {
    instructions: &'static [Instruction],
    queries: Box<[ResolvedQuery<'a>]>,
    values: Box<[Fp]>,
}

impl Evaluation<'_> {
    // One machine-code loop for every entry and every column representation.
    // Field operations inline here instead of crossing per-node ABI boundaries.
    #[inline(never)]
    pub(crate) fn evaluate(&mut self, row: usize) -> Fp {
        let values = &mut self.values;
        for (slot, instruction) in self.instructions.iter().enumerate() {
            values[slot] = match *instruction {
                Instruction::Query(index) => {
                    let query = &self.queries[usize::from(index)];
                    query.column[row.wrapping_add(query.rotation) & (N - 1)]
                }
                Instruction::Constant(index) => constant(usize::from(index)),
                Instruction::Sum(left, right) => {
                    values[usize::from(left)].add(&values[usize::from(right)])
                }
                Instruction::Product(left, right) => {
                    values[usize::from(left)].mul(&values[usize::from(right)])
                }
                Instruction::Negated(inner) => values[usize::from(inner)].neg(),
                Instruction::ConstantScaled(inner, index) => {
                    scale(&values[usize::from(inner)], usize::from(index))
                }
            };
        }
        values[self.instructions.len() - 1]
    }
}

#[derive(Clone, Copy)]
pub(crate) struct CompiledProgram {
    pub(crate) full: CompiledExpression,
    split: Option<(CompiledExpression, CompiledExpression)>,
}

impl CompiledProgram {
    pub(crate) fn fixed_factor(&self) -> Option<CompiledExpression> {
        self.split.map(|(factor, _)| factor)
    }

    #[cfg(test)]
    pub(crate) fn dynamic_body(&self) -> Option<CompiledExpression> {
        self.split.map(|(_, body)| body)
    }
}

sensei_macros::expression_programs!();

pub(crate) fn program(index: usize) -> Result<CompiledProgram, Error> {
    PROGRAMS.get(index).copied().ok_or(Error::InternalInvariant)
}

#[cfg(test)]
mod tests {
    use super::super::{
        evaluation::query_value,
        generated_expressions::{evaluate, program_trees},
        queries::{ADVICE_QUERIES, FIXED_QUERIES, INSTANCE_QUERIES},
        target::{ADVICE_COLUMNS, FIXED_COLUMNS},
    };
    use super::*;
    use sensei_shared::expressions::{Expression, PROGRAM_COUNT};
    use std::prelude::v1::*;

    fn entries(index: usize) -> impl Iterator<Item = (CompiledExpression, &'static Expression)> {
        let tree = program_trees(index).unwrap();
        let compiled = program(index).unwrap();
        core::iter::once((compiled.full, &tree.tree))
            .chain(compiled.fixed_factor().zip(tree.fixed_factor()))
            .chain(compiled.dynamic_body().zip(tree.dynamic_body()))
    }

    fn sample(tag: usize, column: usize, row: usize) -> Fp {
        if row < 8 {
            <Fp>::from_u64(row as u64)
        } else {
            <Fp>::from_bytes_reduced(&core::array::from_fn::<_, 64, _>(|byte| {
                (row * 131 + column * 37 + tag * 17 + byte * 53) as u8
            }))
        }
    }

    #[test]
    fn compiled_programs_match_source_trees_and_splits() {
        let fixed = (0..FIXED_COLUMNS)
            .map(|column| core::array::from_fn(|row| sample(1, column, row)))
            .collect::<Vec<_>>();
        let advice = (0..ADVICE_COLUMNS)
            .map(|column| (0..N).map(|row| sample(2, column, row)).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let instance = (0..N).map(|row| sample(3, 0, row)).collect::<Vec<_>>();
        // Revisit rows and cross both wrap boundaries. Scratch must always be
        // overwritten, even for constants or previously evaluated entries.
        let rows = (0..32).chain([N - 1, N - 2, N / 2, 0, N - 1, 7, N, usize::MAX]);
        for index in 0..PROGRAM_COUNT {
            let tree = program_trees(index).unwrap();
            let compiled = program(index).unwrap();
            assert_eq!(compiled.full.is_fixed_only(), tree.tree.is_fixed_only());
            assert_eq!(
                compiled.fixed_factor().is_some(),
                tree.fixed_factor().is_some()
            );
            for (compiled, tree) in entries(index) {
                let mut bound = compiled.bind(&fixed, &advice, &instance).unwrap();
                for row in rows.clone() {
                    let expected = evaluate(tree, &mut |kind, index| match kind {
                        QueryKind::Fixed => query_value(&FIXED_QUERIES, index, &fixed, row),
                        QueryKind::Advice => query_value(&ADVICE_QUERIES, index, &advice, row),
                        QueryKind::Instance => {
                            query_value(&INSTANCE_QUERIES, index, &[&instance], row)
                        }
                    })
                    .unwrap();
                    assert_eq!(
                        (bound.evaluate(row)).reduce(),
                        (expected).reduce(),
                        "program {index}, row {row}"
                    );
                }
                if compiled.is_fixed_only() {
                    assert_eq!(
                        (compiled.bind_fixed(&fixed).unwrap().evaluate(0)).reduce(),
                        (bound.evaluate(0)).reduce()
                    );
                }
            }
        }
        assert!(program(PROGRAM_COUNT).is_err());
    }

    /// Query callbacks no longer exist. Their former order/multiplicity and
    /// injected-error semantics are deliberately replaced: each reachable
    /// interned node executes once, and each required column is bound before
    /// row evaluation. This census is independent of the macro's interner.
    #[test]
    fn schedules_evaluate_each_distinct_node_and_query_once() {
        fn visit<'a>(tree: &'a Expression, nodes: &mut Vec<&'a Expression>) {
            if nodes.contains(&tree) {
                return;
            }
            match tree {
                Expression::Sum(left, right) | Expression::Product(left, right) => {
                    visit(left, nodes);
                    visit(right, nodes);
                }
                Expression::Negated(inner) | Expression::ConstantScaled(inner, _) => {
                    visit(inner, nodes)
                }
                _ => {}
            }
            nodes.push(tree);
        }
        for index in 0..PROGRAM_COUNT {
            for (compiled, tree) in entries(index) {
                let mut nodes = Vec::new();
                visit(tree, &mut nodes);
                assert_eq!(compiled.schedule.instructions.len(), nodes.len());
                let queries = nodes
                    .iter()
                    .filter_map(|node| {
                        let (kind, query) = match node {
                            Expression::Fixed(index) => {
                                (QueryKind::Fixed, FIXED_QUERIES[usize::from(*index)])
                            }
                            Expression::Advice(index) => {
                                (QueryKind::Advice, ADVICE_QUERIES[usize::from(*index)])
                            }
                            Expression::Instance(index) => {
                                (QueryKind::Instance, INSTANCE_QUERIES[usize::from(*index)])
                            }
                            _ => return None,
                        };
                        Some(ExpressionQuery {
                            kind,
                            column: query.column,
                            rotation: (query.rotation as isize as usize) & (N - 1),
                        })
                    })
                    .collect::<Vec<_>>();
                assert_eq!(compiled.schedule.queries, queries);
                let slots = compiled
                    .schedule
                    .instructions
                    .iter()
                    .filter_map(|instruction| {
                        if let Instruction::Query(index) = instruction {
                            Some(usize::from(*index))
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();
                assert_eq!(slots, (0..queries.len()).collect::<Vec<_>>());
            }
        }
    }

    #[test]
    fn bindings_validate_required_columns_before_evaluation() {
        let fixed = alloc::vec![ [<Fp>::ZERO; N]; FIXED_COLUMNS];
        let advice = alloc::vec![ alloc::vec![ <Fp>::ZERO; N]; ADVICE_COLUMNS];
        let instance = alloc::vec![ <Fp>::ZERO; N];
        for index in 0..PROGRAM_COUNT {
            for (compiled, _) in entries(index) {
                for query in compiled.schedule.queries {
                    match query.kind {
                        QueryKind::Fixed => assert!(
                            compiled
                                .bind(&fixed[..query.column], &advice, &instance)
                                .is_err()
                        ),
                        QueryKind::Advice => {
                            assert!(
                                compiled
                                    .bind(&fixed, &advice[..query.column], &instance)
                                    .is_err()
                            );
                            for length in [0, N - 1, N + 1] {
                                let mut columns = advice.clone();
                                columns[query.column].resize(length, <Fp>::ZERO);
                                assert!(compiled.bind(&fixed, &columns, &instance).is_err());
                            }
                        }
                        QueryKind::Instance => {
                            for length in [0, N - 1, N + 1] {
                                assert!(
                                    compiled
                                        .bind(&fixed, &advice, &alloc::vec![ <Fp>::ZERO; length])
                                        .is_err()
                                );
                            }
                        }
                    }
                }
                // Unreferenced columns are neither accessed nor validated.
                let mut columns = advice.iter().map(Vec::as_slice).collect::<Vec<_>>();
                for (column, values) in columns.iter_mut().enumerate() {
                    if !compiled
                        .schedule
                        .queries
                        .iter()
                        .any(|query| query.kind == QueryKind::Advice && query.column == column)
                    {
                        *values = &[];
                    }
                }
                let instance = if compiled
                    .schedule
                    .queries
                    .iter()
                    .any(|query| query.kind == QueryKind::Instance)
                {
                    instance.as_slice()
                } else {
                    &[]
                };
                assert!(compiled.bind(&fixed, &columns, instance).is_ok());
            }
        }
    }

    #[test]
    fn compiled_identity_matches_structural_equality() {
        let expressions = (0..PROGRAM_COUNT).flat_map(entries).collect::<Vec<_>>();
        for (index, (compiled, tree)) in expressions.iter().enumerate() {
            for (other_compiled, other_tree) in &expressions[..index] {
                assert_eq!(compiled == other_compiled, tree == other_tree);
            }
        }
    }
}
