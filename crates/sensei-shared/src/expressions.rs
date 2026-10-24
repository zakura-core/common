//! Gate and lookup expression trees and their structural analyses.
//!
//! The source of record is [`super::programs::expression_programs`]. The
//! macros expand these trees into executable Rust during compilation.
//! Tests retain trees as the independent reference for every evaluator. The
//! historical encoder remains solely for the frozen-spec digest test; no
//! artifact is generated from it and no runtime consumer decodes or executes
//! its output.

use alloc::boxed::Box;
/// Number of gate and lookup expression programs, in protocol order.
pub const PROGRAM_COUNT: usize = 207;

/// Number of shared field constants, validated during macro expansion.
pub const CONSTANT_COUNT: usize = 49;

/// One gate or lookup expression as an owned tree, defined in [`super::programs`].
///
/// Analyze a fixed factor times a dynamic body. Leaf indices refer to the
/// corresponding kind's [query table](crate::queries), while constants use the
/// shared pool:
///
/// ```
/// use zakura_sensei_shared::expressions::{advice, constant, fixed};
///
/// let gate = fixed(0).mul(advice(1).add(constant(0)));
/// assert_eq!(gate.degree(), 2);
/// assert_eq!(gate.query_dependencies().advice, 1 << 1);
///
/// let (factor, body) = gate.fixed_root_split().unwrap();
/// assert!(factor.is_fixed_only());
/// assert!(!body.is_fixed_only());
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expression {
    /// A fixed-column query leaf.
    Fixed(u8),
    /// An advice-column query leaf.
    Advice(u8),
    /// An instance-column query leaf.
    Instance(u8),
    /// A shared-pool constant leaf.
    Constant(u8),
    /// The sum of two expressions.
    Sum(Box<Expression>, Box<Expression>),
    /// The product of two expressions.
    Product(Box<Expression>, Box<Expression>),
    /// The negation of an expression.
    Negated(Box<Expression>),
    /// The expression times pool constant `index`.
    ConstantScaled(Box<Expression>, u8),
}

/// A fixed-column query leaf.
pub fn fixed(index: u8) -> Expression {
    Expression::Fixed(index)
}

/// An advice-column query leaf.
pub fn advice(index: u8) -> Expression {
    Expression::Advice(index)
}

/// An instance-column query leaf.
pub fn instance(index: u8) -> Expression {
    Expression::Instance(index)
}

/// A shared-pool constant leaf.
pub fn constant(index: u8) -> Expression {
    Expression::Constant(index)
}

impl Expression {
    /// Whether every query in this tree is fixed (constants are fixed-only).
    pub fn is_fixed_only(&self) -> bool {
        match self {
            Self::Fixed(_) | Self::Constant(_) => true,
            Self::Advice(_) | Self::Instance(_) => false,
            Self::Sum(left, right) | Self::Product(left, right) => {
                left.is_fixed_only() && right.is_fixed_only()
            }
            Self::Negated(inner) | Self::ConstantScaled(inner, _) => inner.is_fixed_only(),
        }
    }

    /// The fixed factor and dynamic body of a root product with exactly one
    /// fixed-only operand. Wrappers around the root product prevent a split.
    pub fn fixed_root_split(&self) -> Option<(&Self, &Self)> {
        let Self::Product(left, right) = self else {
            return None;
        };
        match (left.is_fixed_only(), right.is_fixed_only()) {
            (true, false) => Some((left, right)),
            (false, true) => Some((right, left)),
            _ => None,
        }
    }

    /// Total degree under the semiring: queries have degree one, constants
    /// zero, sums take the maximum, and products add degrees. Negation and
    /// constant scaling preserve degree, including scaling by zero.
    pub fn degree(&self) -> usize {
        match self {
            Self::Fixed(_) | Self::Advice(_) | Self::Instance(_) => 1,
            Self::Constant(_) => 0,
            Self::Sum(left, right) => left.degree().max(right.degree()),
            Self::Product(left, right) => left.degree() + right.degree(),
            Self::Negated(inner) | Self::ConstantScaled(inner, _) => inner.degree(),
        }
    }

    /// The query indices read by this tree, grouped by query kind.
    ///
    /// # Panics
    /// Panics for query indices at or above 32, outside the bitset's range.
    pub fn query_dependencies(&self) -> QueryDependencies {
        let mut dependencies = QueryDependencies::default();
        match self {
            Self::Fixed(index) | Self::Advice(index) | Self::Instance(index) => {
                assert!(*index < 32, "query index exceeds dependency bitset");
                let bit = 1u32 << index;
                match self {
                    Self::Fixed(_) => dependencies.fixed = bit,
                    Self::Advice(_) => dependencies.advice = bit,
                    _ => dependencies.instance = bit,
                }
            }
            Self::Constant(_) => {}
            Self::Sum(left, right) | Self::Product(left, right) => {
                dependencies = left.query_dependencies().union(right.query_dependencies());
            }
            Self::Negated(inner) | Self::ConstantScaled(inner, _) => {
                dependencies = inner.query_dependencies();
            }
        }
        dependencies
    }

    /// The sum `self + rhs`, named like the field type's own `add` for
    /// consistency across the workspace's arithmetic call sites.
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, rhs: Self) -> Self {
        Self::Sum(Box::new(self), Box::new(rhs))
    }

    /// The product `self · rhs`.
    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, rhs: Self) -> Self {
        Self::Product(Box::new(self), Box::new(rhs))
    }

    /// The negation `-self`.
    #[allow(clippy::should_implement_trait)]
    pub fn neg(self) -> Self {
        Self::Negated(Box::new(self))
    }

    /// The product of `self` and pool constant `index`.
    pub fn multiply_constant(self, index: u8) -> Self {
        Self::ConstantScaled(Box::new(self), index)
    }
}

/// The query indices one program reads, per query kind, as bitsets over the
/// query tables (`bit i` set when query `i` of that kind is read). Every
/// table has fewer than 32 entries, which [`Expression::query_dependencies`] enforces.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct QueryDependencies {
    /// Fixed-column queries read.
    pub fixed: u32,
    /// Advice-column queries read.
    pub advice: u32,
    /// Instance-column queries read.
    pub instance: u32,
}

impl QueryDependencies {
    /// The union of two dependency sets.
    pub const fn union(self, other: Self) -> Self {
        Self {
            fixed: self.fixed | other.fixed,
            advice: self.advice | other.advice,
            instance: self.instance | other.instance,
        }
    }

    /// Whether every query in `self` is also in `other`.
    pub const fn is_subset_of(self, other: Self) -> bool {
        self.fixed & !other.fixed == 0
            && self.advice & !other.advice == 0
            && self.instance & !other.instance == 0
    }

    /// Whether the set reads only fixed columns.
    pub const fn is_fixed_only(self) -> bool {
        self.advice == 0 && self.instance == 0
    }
}

#[cfg(test)]
mod tests {
    use super::{QueryDependencies, advice, constant, fixed, instance};

    #[test]
    fn root_split_requires_exactly_one_fixed_operand() {
        let factor = fixed(3).add(constant(0)).neg().multiply_constant(1);
        let body = advice(2).mul(instance(1)).neg().multiply_constant(0);
        assert!(factor.is_fixed_only());
        assert!(!body.is_fixed_only());
        for tree in [
            factor.clone().mul(body.clone()),
            body.clone().mul(factor.clone()),
        ] {
            assert_eq!(tree.fixed_root_split(), Some((&factor, &body)));
            assert!(tree.clone().neg().fixed_root_split().is_none());
            assert!(tree.multiply_constant(0).fixed_root_split().is_none());
        }
        for tree in [
            factor.clone().mul(factor.clone()),
            body.clone().mul(body.clone()),
            factor.add(body),
            fixed(0),
            constant(0),
        ] {
            assert!(tree.fixed_root_split().is_none());
        }
    }

    #[test]
    fn analyses_preserve_semiring_degree_and_union_dependencies() {
        let tree = fixed(31)
            .add(advice(2).mul(advice(2)))
            .mul(instance(1).neg().multiply_constant(0))
            .add(constant(1));
        assert_eq!(constant(0).degree(), 0);
        assert_eq!(tree.degree(), 3);
        assert_eq!(
            tree.query_dependencies(),
            QueryDependencies {
                fixed: 1 << 31,
                advice: 1 << 2,
                instance: 1 << 1
            },
        );
    }
}
