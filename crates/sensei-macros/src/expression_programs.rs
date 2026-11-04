//! Lower source trees to compact, value-numbered schedules on the host.

use std::collections::BTreeMap;

use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use sensei_shared::{
    N,
    expressions::{CONSTANT_COUNT, Expression, PROGRAM_COUNT},
    programs::expression_programs,
    queries::{ADVICE_QUERIES, FIXED_QUERIES, INSTANCE_QUERIES},
};
use syn::{Error, Result};

pub(crate) fn evaluate() -> Result<TokenStream> {
    let trees = expression_programs();
    if trees.len() != PROGRAM_COUNT {
        return Err(Error::new(Span::call_site(), "wrong circuit program count"));
    }
    emit_programs(&trees)
}

/// Child IDs make structural interning independent of tree size. Operand
/// order, wrappers, and constants remain part of identity. These global IDs
/// preserve equality across full expressions and their split operands; the
/// smaller, entry-local value numbers are only scratch-buffer addresses.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Fixed(usize),
    Advice(usize),
    Instance(usize),
    Constant(usize),
    Sum(usize, usize),
    Product(usize, usize),
    Negated(usize),
    ConstantScaled(usize, usize),
}

impl Node {
    fn children(self) -> impl Iterator<Item = usize> {
        match self {
            Self::Sum(left, right) | Self::Product(left, right) => [Some(left), Some(right)],
            Self::Negated(inner) | Self::ConstantScaled(inner, _) => [Some(inner), None],
            _ => [None, None],
        }
        .into_iter()
        .flatten()
    }
}

struct ExpressionNode {
    node: Node,
    fixed_only: bool,
    entry: bool,
}

#[derive(Default)]
struct Expressions {
    nodes: Vec<ExpressionNode>,
    indices: BTreeMap<Node, usize>,
}

impl Expressions {
    fn intern(&mut self, tree: &Expression) -> Result<usize> {
        let node = match tree {
            Expression::Fixed(index) => {
                Node::Fixed(checked_index(*index, FIXED_QUERIES.len(), "fixed query")?)
            }
            Expression::Advice(index) => {
                Node::Advice(checked_index(*index, ADVICE_QUERIES.len(), "advice query")?)
            }
            Expression::Instance(index) => Node::Instance(checked_index(
                *index,
                INSTANCE_QUERIES.len(),
                "instance query",
            )?),
            Expression::Constant(index) => {
                Node::Constant(checked_index(*index, CONSTANT_COUNT, "constant")?)
            }
            Expression::Sum(left, right) => Node::Sum(self.intern(left)?, self.intern(right)?),
            Expression::Product(left, right) => {
                Node::Product(self.intern(left)?, self.intern(right)?)
            }
            Expression::Negated(inner) => Node::Negated(self.intern(inner)?),
            Expression::ConstantScaled(inner, index) => Node::ConstantScaled(
                self.intern(inner)?,
                checked_index(*index, CONSTANT_COUNT, "constant")?,
            ),
        };
        if let Some(&id) = self.indices.get(&node) {
            return Ok(id);
        }
        let fixed_only = match node {
            Node::Fixed(_) | Node::Constant(_) => true,
            Node::Advice(_) | Node::Instance(_) => false,
            _ => node.children().all(|id| self.nodes[id].fixed_only),
        };
        let id = self.nodes.len();
        self.nodes.push(ExpressionNode {
            node,
            fixed_only,
            entry: false,
        });
        self.indices.insert(node, id);
        Ok(id)
    }

    fn entry(&mut self, tree: &Expression) -> Result<TokenStream> {
        let id = self.intern(tree)?;
        self.nodes[id].entry = true;
        let fixed_only = self.nodes[id].fixed_only;
        let schedule = format_ident!("SCHEDULE_{id}");
        Ok(quote!(CompiledExpression { id: #id, fixed_only: #fixed_only, schedule: &#schedule }))
    }

    /// Left-first postorder, skipping nodes already reached. This is done
    /// only during expansion: the target never walks trees, discovers live
    /// nodes, or checks cache generations. Every operand precedes its user.
    fn schedule(&self, root: usize) -> Vec<usize> {
        fn visit(expressions: &Expressions, id: usize, seen: &mut [bool], out: &mut Vec<usize>) {
            if seen[id] {
                return;
            }
            seen[id] = true;
            for child in expressions.nodes[id].node.children() {
                visit(expressions, child, seen, out);
            }
            out.push(id);
        }
        let mut out = Vec::new();
        visit(self, root, &mut vec![false; self.nodes.len()], &mut out);
        out
    }

    fn emit_schedule(&self, root: usize) -> Result<TokenStream> {
        let mut instruction_slots = BTreeMap::new();
        let mut instructions = Vec::new();
        let mut queries = Vec::new();
        for node_id in self.schedule(root) {
            let node = self.nodes[node_id].node;
            let instruction = match node {
                Node::Fixed(index) | Node::Advice(index) | Node::Instance(index) => {
                    // Query metadata belongs to the fixed circuit. Resolve its
                    // descriptor here; binding only checks and borrows columns.
                    let (kind, query) = match node {
                        Node::Fixed(_) => (quote!(QueryKind::Fixed), FIXED_QUERIES[index]),
                        Node::Advice(_) => (quote!(QueryKind::Advice), ADVICE_QUERIES[index]),
                        Node::Instance(_) => (quote!(QueryKind::Instance), INSTANCE_QUERIES[index]),
                        _ => unreachable!(),
                    };
                    let column = query.column;
                    let rotation = (query.rotation as isize as usize) & (N - 1);
                    let query_slot = compact_index(queries.len())?;
                    queries.push(quote!(ExpressionQuery { kind: #kind, column: #column, rotation: #rotation }));
                    quote!(Instruction::Query(#query_slot))
                }
                Node::Constant(index) => {
                    let index = compact_index(index)?;
                    quote!(Instruction::Constant(#index))
                }
                Node::Sum(left, right) | Node::Product(left, right) => {
                    let left = instruction_slots[&left];
                    let right = instruction_slots[&right];
                    if matches!(node, Node::Sum(..)) {
                        quote!(Instruction::Sum(#left, #right))
                    } else {
                        quote!(Instruction::Product(#left, #right))
                    }
                }
                Node::Negated(inner) => {
                    let inner = instruction_slots[&inner];
                    quote!(Instruction::Negated(#inner))
                }
                Node::ConstantScaled(inner, index) => {
                    let inner = instruction_slots[&inner];
                    let index = compact_index(index)?;
                    quote!(Instruction::ConstantScaled(#inner, #index))
                }
            };
            instruction_slots.insert(node_id, compact_index(instructions.len())?);
            instructions.push(instruction);
        }
        let name = format_ident!("SCHEDULE_{root}");
        Ok(quote! {
            const #name: ExpressionSchedule = ExpressionSchedule {
                instructions: &[#(#instructions),*],
                queries: &[#(#queries),*],
            };
        })
    }
}

fn emit_programs(trees: &[Expression]) -> Result<TokenStream> {
    let mut expressions = Expressions::default();
    let programs = trees
        .iter()
        .map(|tree| {
            let full = expressions.entry(tree)?;
            let split = match tree.fixed_root_split() {
                Some((factor, body)) => {
                    let factor = expressions.entry(factor)?;
                    let body = expressions.entry(body)?;
                    quote!(Some((#factor, #body)))
                }
                None => quote!(None),
            };
            Ok(quote!(CompiledProgram { full: #full, split: #split }))
        })
        .collect::<Result<Vec<_>>>()?;
    let schedules = expressions
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| node.entry)
        .map(|(id, _)| expressions.emit_schedule(id))
        .collect::<Result<Vec<_>>>()?;
    let count = trees.len();
    Ok(quote! {
        const PROGRAMS: [CompiledProgram; #count] = [#(#programs),*];
        #(#schedules)*
    })
}

fn checked_index(index: u8, count: usize, kind: &str) -> Result<usize> {
    let index = usize::from(index);
    if index < count {
        Ok(index)
    } else {
        Err(Error::new(
            Span::call_site(),
            format!("{kind} index {index} is out of bounds ({count})"),
        ))
    }
}

fn compact_index(index: usize) -> Result<u16> {
    u16::try_from(index)
        .map_err(|_| Error::new(Span::call_site(), "expression schedule exceeds u16"))
}

#[cfg(test)]
mod tests {
    use sensei_shared::expressions::{advice, constant, fixed, instance};

    use super::*;

    #[test]
    fn rejects_every_kind_of_out_of_bounds_operand() {
        for tree in [
            fixed(FIXED_QUERIES.len() as u8),
            advice(ADVICE_QUERIES.len() as u8),
            instance(INSTANCE_QUERIES.len() as u8),
            constant(CONSTANT_COUNT as u8),
            advice(0).multiply_constant(CONSTANT_COUNT as u8),
        ] {
            assert!(
                emit_programs(&[tree])
                    .unwrap_err()
                    .to_string()
                    .contains("out of bounds")
            );
        }
        assert!(compact_index(usize::from(u16::MAX)).is_ok());
        assert!(compact_index(usize::from(u16::MAX) + 1).is_err());
        assert!(evaluate().is_ok());
    }

    #[test]
    fn interning_preserves_tree_identity() {
        let trees = [
            fixed(0).mul(advice(0)),
            fixed(0).mul(advice(0)),
            advice(0).mul(fixed(0)),
            fixed(0).mul(advice(0)).neg(),
            fixed(0).mul(advice(0)).multiply_constant(5),
        ];
        let mut expressions = Expressions::default();
        let descriptors: Vec<_> = trees
            .iter()
            .map(|tree| expressions.entry(tree).unwrap().to_string())
            .collect();
        assert_eq!(descriptors[0], descriptors[1]);
        for descriptor in &descriptors[2..] {
            assert_ne!(&descriptors[0], descriptor);
        }
        assert_eq!(
            expressions.nodes.iter().filter(|node| node.entry).count(),
            4
        );
    }

    #[test]
    fn schedules_visit_shared_nodes_once_and_only_after_their_operands() {
        let child = advice(0).add(constant(5));
        let parent = child.clone().mul(advice(1));
        let tree = parent.clone().add(parent.clone()).add(child.clone().neg());
        let mut expressions = Expressions::default();
        // Unrelated earlier IDs must not leak into an entry's schedule.
        expressions.entry(&instance(0).mul(fixed(0))).unwrap();
        let root = expressions.intern(&tree).unwrap();
        let schedule = expressions.schedule(root);
        assert_eq!(schedule.len(), 8);
        assert_eq!(schedule.last(), Some(&root));
        for (slot, &id) in schedule.iter().enumerate() {
            assert!(!schedule[..slot].contains(&id));
            for child in expressions.nodes[id].node.children() {
                assert!(schedule[..slot].contains(&child));
            }
        }
        assert_eq!(
            schedule
                .iter()
                .filter(|&&id| id == expressions.indices[&Node::Advice(0)])
                .count(),
            1
        );
        let count = expressions.nodes.len();
        expressions.entry(&parent).unwrap();
        assert_eq!(expressions.nodes.len(), count);
        assert_eq!(expressions.schedule(root), schedule);
    }
}
