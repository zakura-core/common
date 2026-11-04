//! Scoped execution borrowed from the caller.
#[cfg(feature = "prover")]
use super::{
    buffer::{Buffer, BufferPool},
    field::Fp,
};
use alloc::vec::Vec;
use udon::exec::{Executor, TaskBudget};

pub(crate) mod run;

trait Dispatch: Sync {
    fn join(&self, left: &mut (dyn FnMut() + Send), right: &mut (dyn FnMut() + Send));
}
impl<E: Executor> Dispatch for E {
    fn join(&self, left: &mut (dyn FnMut() + Send), right: &mut (dyn FnMut() + Send)) {
        Executor::join(self, left, right);
    }
}
/// Borrows an executor without imposing its concrete type on circuit records.
#[derive(Clone, Copy)]
pub(crate) struct Execution<'a> {
    dispatch: &'a dyn Dispatch,
    pub(crate) budget: TaskBudget,
    #[cfg(feature = "prover")]
    buffers: Option<&'a BufferPool<Fp>>,
}
impl<'a> Execution<'a> {
    pub(crate) fn new<E: Executor>(executor: &'a E, budget: TaskBudget) -> Self {
        Self {
            dispatch: executor,
            budget,
            #[cfg(feature = "prover")]
            buffers: None,
        }
    }
    #[cfg(feature = "prover")]
    pub(crate) fn with_buffers<'b>(self, buffers: &'b BufferPool<Fp>) -> Execution<'b>
    where
        'a: 'b,
    {
        Execution {
            dispatch: self.dispatch,
            budget: self.budget,
            buffers: Some(buffers),
        }
    }
    #[cfg(feature = "prover")]
    pub(crate) fn buffer(self, len: usize, clear: bool) -> Buffer<Fp> {
        self.buffers.map_or_else(
            || alloc::vec![<Fp>::ZERO; len].into(),
            |pool| pool.take(len, <Fp>::ZERO, clear),
        )
    }
    #[cfg(feature = "prover")]
    pub(crate) fn provision(self, len: usize, count: usize) {
        if let Some(buffers) = self.buffers {
            buffers.provision(len, count, <Fp>::ZERO);
        }
    }
    #[cfg(feature = "prover")]
    pub(crate) fn copy(self, values: &[Fp]) -> Buffer<Fp> {
        let mut buffer = self.buffer(values.len(), false);
        buffer.copy_from_slice(values);
        buffer
    }
    pub(crate) fn serial(self) -> Self {
        Self {
            budget: TaskBudget::SERIAL,
            ..self
        }
    }
    pub(crate) fn map<I, R: Send>(self, items: I, job: impl Fn(I::Item, Self) -> R + Sync) -> Vec<R>
    where
        I: IntoIterator,
        I::Item: Send,
        I::IntoIter: ExactSizeIterator + Send,
    {
        let items = items.into_iter();
        let job = |item| job(item, self);
        if self.budget == TaskBudget::SERIAL {
            return items.map(job).collect();
        }
        let mut map = run::Map::new(items, &job);
        run::drive(&mut map, self.budget, &self);
        map.results()
    }
}
impl Executor for Execution<'_> {
    fn join<L, R, A, B>(&self, left: L, right: R) -> (A, B)
    where
        L: FnOnce() -> A + Send,
        R: FnOnce() -> B + Send,
        A: Send,
        B: Send,
    {
        if self.budget == TaskBudget::SERIAL {
            return (left(), right());
        }
        let (mut left, mut right) = (Some(left), Some(right));
        let (mut a, mut b) = (None, None);
        self.dispatch
            .join(&mut || a = Some(left.take().unwrap()()), &mut || {
                b = Some(right.take().unwrap()())
            });
        (a.unwrap(), b.unwrap())
    }
}
