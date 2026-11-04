//! Ordered expression-tree adapter and complete protocol inventory.

use alloc::vec::Vec;

use crate::expressions::{Expression, PROGRAM_COUNT};

use super::{Algebra, Value, expression};

struct Trees;

impl Algebra for Trees {
    type Value = Expression;
    fn fixed(&self, index: u8) -> Expression {
        crate::expressions::fixed(index)
    }
    fn advice(&self, index: u8) -> Expression {
        crate::expressions::advice(index)
    }
    fn gated(&self, factor: impl FnOnce() -> Expression, body: Expression) -> Expression {
        factor().mul(body)
    }
}

impl Value for Expression {
    fn constant(index: u8) -> Self {
        crate::expressions::constant(index)
    }
    fn add(self, rhs: Self) -> Self {
        self.add(rhs)
    }
    fn mul(self, rhs: Self) -> Self {
        self.mul(rhs)
    }
    fn neg(self) -> Self {
        self.neg()
    }
    fn multiply_constant(self, index: u8) -> Self {
        self.multiply_constant(index)
    }
}

/// Every expression in protocol order (the historical container order).
#[allow(
    clippy::disallowed_types,
    reason = "host/test expression builder; prohibited from proving by the allocation audit"
)]
pub fn expression_programs() -> Vec<Expression> {
    (0..PROGRAM_COUNT)
        .map(|index| expression(&Trees, index))
        .collect()
}
