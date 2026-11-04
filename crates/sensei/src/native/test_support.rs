//! Reduced Montgomery values for comparing nested arithmetic results in tests.
//!
//! This normalization shares production field arithmetic; it is not an oracle.
//! See the [oracle-independence map](crate::native#oracle-independence) before
//! consolidating the independent references that use it.

use super::buffer::Buffer;
use udon::field::{PastaField, PrimeModulus, Reduced, ReductionState};

pub(crate) fn reduced_values<T: ReducedValues + ?Sized>(value: &T) -> T::Output {
    value.reduced_values()
}

pub(crate) trait ReducedValues {
    type Output;
    fn reduced_values(&self) -> Self::Output;
}

impl<M: PrimeModulus, S: ReductionState> ReducedValues for PastaField<M, S> {
    type Output = PastaField<M, Reduced>;
    fn reduced_values(&self) -> Self::Output {
        self.reduce()
    }
}

impl<T: ReducedValues + ?Sized> ReducedValues for &T {
    type Output = T::Output;
    fn reduced_values(&self) -> Self::Output {
        reduced_values(*self)
    }
}

impl<T: ReducedValues> ReducedValues for [T] {
    type Output = Vec<T::Output>;
    fn reduced_values(&self) -> Self::Output {
        self.iter().map(reduced_values).collect()
    }
}

impl<T: ReducedValues, const N: usize> ReducedValues for [T; N] {
    type Output = Vec<T::Output>;
    fn reduced_values(&self) -> Self::Output {
        reduced_values(self.as_slice())
    }
}

impl<T: ReducedValues> ReducedValues for Vec<T> {
    type Output = Vec<T::Output>;
    fn reduced_values(&self) -> Self::Output {
        reduced_values(self.as_slice())
    }
}

impl<T: ReducedValues> ReducedValues for Buffer<T> {
    type Output = Vec<T::Output>;
    fn reduced_values(&self) -> Self::Output {
        reduced_values(&self[..])
    }
}

impl<T: ReducedValues> ReducedValues for Option<T> {
    type Output = Option<T::Output>;
    fn reduced_values(&self) -> Self::Output {
        self.as_ref().map(reduced_values)
    }
}

impl<T: ReducedValues, E: Clone> ReducedValues for Result<T, E> {
    type Output = Result<T::Output, E>;
    fn reduced_values(&self) -> Self::Output {
        self.as_ref().map(reduced_values).map_err(Clone::clone)
    }
}

impl<A: ReducedValues, B: ReducedValues> ReducedValues for (A, B) {
    type Output = (A::Output, B::Output);
    fn reduced_values(&self) -> Self::Output {
        (reduced_values(&self.0), reduced_values(&self.1))
    }
}

impl ReducedValues for u32 {
    type Output = Self;
    fn reduced_values(&self) -> Self {
        *self
    }
}
