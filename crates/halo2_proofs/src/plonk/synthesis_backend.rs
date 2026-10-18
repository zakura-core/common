//! The single [`Assignment`] type that key generation and proving synthesize
//! circuits against.
//!
//! A circuit's synthesis code (its chips, gadgets, and region closures) is
//! monomorphized once per assignment backend. Routing both production
//! backends through this enum compiles that code once instead of twice,
//! while each backend operation stays statically dispatched: a predictable
//! branch on the variant, with both arms available for inlining.

use ff::Field;

use super::{
    Advice, Any, Assigned, Assignment, Column, Error, Fixed, Instance, Selector, keygen::Assembly,
    prover::WitnessCollection,
};
use crate::circuit::Value;

/// Key-generation or proving assignment backend.
pub(super) enum SynthesisBackend<'b, 'w, F: Field> {
    Keygen(&'b mut Assembly<F>),
    Prove(&'b mut WitnessCollection<'w, F>),
}

/// Calls `$method` on whichever backend `$self` holds.
macro_rules! dispatch {
    ($self:ident.$method:ident($($arg:expr),*)) => {
        match $self {
            SynthesisBackend::Keygen(backend) => backend.$method($($arg),*),
            SynthesisBackend::Prove(backend) => backend.$method($($arg),*),
        }
    };
}

impl<F: Field> Assignment<F> for SynthesisBackend<'_, '_, F> {
    #[inline]
    fn enter_region<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        dispatch!(self.enter_region(name_fn))
    }

    #[inline]
    fn exit_region(&mut self) {
        dispatch!(self.exit_region())
    }

    #[inline]
    fn enable_selector<A, AR>(
        &mut self,
        annotation: A,
        selector: &Selector,
        row: usize,
    ) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        dispatch!(self.enable_selector(annotation, selector, row))
    }

    #[inline]
    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        dispatch!(self.query_instance(column, row))
    }

    #[inline]
    fn assign_advice<V, VR, A, AR>(
        &mut self,
        annotation: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        dispatch!(self.assign_advice(annotation, column, row, to))
    }

    #[inline]
    fn assign_advice_batch<V, A, AR>(
        &mut self,
        annotation: A,
        column: Column<Advice>,
        row: usize,
        len: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnMut(usize) -> Value<Assigned<F>>,
        A: Fn(usize) -> AR,
        AR: Into<String>,
    {
        dispatch!(self.assign_advice_batch(annotation, column, row, len, to))
    }

    #[inline]
    fn assign_advice_batch_with_previous_denominator<V, A, AR>(
        &mut self,
        annotation: A,
        column: Column<Advice>,
        row: usize,
        len: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnMut(usize) -> Value<Assigned<F>>,
        A: Fn(usize) -> AR,
        AR: Into<String>,
    {
        dispatch!(
            self.assign_advice_batch_with_previous_denominator(annotation, column, row, len, to)
        )
    }

    #[inline]
    fn assign_advice_batch_with_previous_denominator_squared<V, A, AR>(
        &mut self,
        annotation: A,
        column: Column<Advice>,
        row: usize,
        len: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnMut(usize) -> Value<Assigned<F>>,
        A: Fn(usize) -> AR,
        AR: Into<String>,
    {
        dispatch!(self.assign_advice_batch_with_previous_denominator_squared(
            annotation, column, row, len, to
        ))
    }

    #[inline]
    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        annotation: A,
        column: Column<Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        dispatch!(self.assign_fixed(annotation, column, row, to))
    }

    #[inline]
    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        dispatch!(self.copy(left_column, left_row, right_column, right_row))
    }

    #[inline]
    fn fill_from_row(
        &mut self,
        column: Column<Fixed>,
        row: usize,
        to: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        dispatch!(self.fill_from_row(column, row, to))
    }

    #[inline]
    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        dispatch!(self.push_namespace(name_fn))
    }

    #[inline]
    fn pop_namespace(&mut self, gadget_name: Option<String>) {
        dispatch!(self.pop_namespace(gadget_name))
    }
}
