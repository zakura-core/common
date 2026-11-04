//! Specialized field arithmetic for direct recipe evaluation.

use udon::field::Fp;

use crate::constants::constant;

use super::Value;

impl Value for Fp {
    #[inline(always)]
    fn constant(index: u8) -> Self {
        constant(usize::from(index))
    }

    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        <Fp>::add(&self, &rhs)
    }

    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        <Fp>::mul(&self, &rhs)
    }

    #[inline(always)]
    fn neg(self) -> Self {
        <Fp>::neg(&self)
    }

    #[inline(always)]
    fn multiply_constant(self, index: u8) -> Self {
        crate::constants::scale(&self, usize::from(index))
    }

    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        <Fp>::sub(&self, &rhs)
    }

    #[inline(always)]
    fn square(self) -> Self {
        <Fp>::square(&self)
    }

    #[inline(always)]
    fn mix(values: [Self; 3], coefficient: u8) -> Self {
        let coefficient = usize::from(coefficient);
        <Fp>::sum_of_products(
            &values,
            &[
                constant(coefficient),
                constant(coefficient + 1),
                constant(coefficient + 2),
            ],
        )
    }
}
