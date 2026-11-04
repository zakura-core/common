//! Independent source-tree arithmetic oracle, compiled only for tests.
//!
//! `TREES` holds `crate::native::programs::expression_programs()` once per
//! test process. `evaluate` recursively evaluates those shared source trees
//! using [`sensei_shared::constants::CONSTANTS`]. The parent module retains
//! the caller paths; its sibling `tests` module owns the structural censuses
//! and historical digest pin. See the
//! [expression execution map](crate::native#expression-execution-paths) for
//! the reference's independence boundary.

use std::sync::LazyLock;

use crate::{Error, native::expressions::Expression};

use super::{Fp, PROGRAM_COUNT, QueryKind, constant};

// The source trees and their shape constants live in sensei-shared.
#[cfg(test)]
use sensei_shared::expressions::CONSTANT_COUNT;

/// An owned source tree with its fixed-root split cached as an operand side.
/// Borrowing the children on access avoids self-references or duplicate trees.
#[cfg(test)]
pub(crate) struct ProgramTrees {
    pub(crate) tree: Expression,
    fixed_on_left: Option<bool>,
}

#[cfg(test)]
impl ProgramTrees {
    pub(super) fn new(tree: Expression) -> Self {
        fn validate_constants(tree: &Expression) {
            match tree {
                Expression::Constant(index) => assert!(usize::from(*index) < CONSTANT_COUNT),
                Expression::ConstantScaled(inner, index) => {
                    assert!(usize::from(*index) < CONSTANT_COUNT);
                    validate_constants(inner);
                }
                Expression::Sum(left, right) | Expression::Product(left, right) => {
                    validate_constants(left);
                    validate_constants(right);
                }
                Expression::Negated(inner) => validate_constants(inner),
                Expression::Fixed(_) | Expression::Advice(_) | Expression::Instance(_) => {}
            }
        }
        validate_constants(&tree);
        let fixed_on_left = tree.fixed_root_split().map(|_| {
            let Expression::Product(left, _) = &tree else {
                unreachable!("only root products split");
            };
            left.is_fixed_only()
        });
        Self {
            tree,
            fixed_on_left,
        }
    }

    fn split(&self) -> Option<(&Expression, &Expression)> {
        let fixed_on_left = self.fixed_on_left?;
        let Expression::Product(left, right) = &self.tree else {
            unreachable!("only root products split");
        };
        Some(if fixed_on_left {
            (left, right)
        } else {
            (right, left)
        })
    }

    pub(crate) fn fixed_factor(&self) -> Option<&Expression> {
        self.split().map(|(factor, _)| factor)
    }

    pub(crate) fn dynamic_body(&self) -> Option<&Expression> {
        self.split().map(|(_, body)| body)
    }
}

/// Source trees retained only as the tests' independent arithmetic oracle.
#[cfg(test)]
pub(super) static TREES: LazyLock<[ProgramTrees; PROGRAM_COUNT]> = LazyLock::new(|| {
    let trees: [Expression; PROGRAM_COUNT] = crate::native::programs::expression_programs()
        .try_into()
        .expect("the circuit must contain PROGRAM_COUNT expressions");
    trees.map(ProgramTrees::new)
});

#[cfg(test)]
pub(crate) fn program_trees(expression: usize) -> Result<&'static ProgramTrees, Error> {
    TREES.get(expression).ok_or(Error::InternalInvariant)
}

/// Evaluates the source tree in operand order, propagating query errors.
/// Constants are checked when the process-lifetime program table is built.
#[cfg(test)]
pub(crate) fn evaluate(
    expression: &Expression,
    query: &mut dyn FnMut(QueryKind, usize) -> Result<Fp, Error>,
) -> Result<Fp, Error> {
    Ok(match expression {
        Expression::Fixed(index) => query(QueryKind::Fixed, usize::from(*index))?,
        Expression::Advice(index) => query(QueryKind::Advice, usize::from(*index))?,
        Expression::Instance(index) => query(QueryKind::Instance, usize::from(*index))?,
        Expression::Constant(index) => constant(usize::from(*index)),
        Expression::Sum(left, right) => evaluate(left, query)?.add(&evaluate(right, query)?),
        Expression::Product(left, right) => evaluate(left, query)?.mul(&evaluate(right, query)?),
        Expression::Negated(inner) => evaluate(inner, query)?.neg(),
        Expression::ConstantScaled(inner, index) => {
            evaluate(inner, query)?.mul(&constant(usize::from(*index)))
        }
    })
}
