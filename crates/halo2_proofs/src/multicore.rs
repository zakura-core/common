//! An interface for dealing with the kinds of parallel computations involved in
//! `halo2`. It's currently just a (very!) thin wrapper around `rayon` but may
//! be extended in the future to allow for various parallelism strategies.

#[cfg(all(
    feature = "multicore",
    target_arch = "wasm32",
    not(target_feature = "atomics")
))]
compile_error!(
    "The multicore feature flag is not supported on wasm32 architectures without atomics"
);

pub use maybe_rayon::{
    iter::{IntoParallelIterator, ParallelIterator},
    scope,
};

/// Runs `a` and `b`, potentially in parallel, and returns both results, like
/// `rayon::join`.
///
/// The tasks are called through `&mut dyn FnMut`, so rayon's join machinery is
/// compiled once for all callers, rather than once per pair of closure types. That
/// costs two indirect calls per join, which is negligible for the coarse tasks halo2
/// joins: whole polynomials, columns, and FFT halves above a fixed recursion depth.
pub fn join<A, B, RA, RB>(a: A, b: B) -> (RA, RB)
where
    A: FnOnce() -> RA + Send,
    B: FnOnce() -> RB + Send,
    RA: Send,
    RB: Send,
{
    let (mut a, mut a_result) = (Some(a), None);
    let (mut b, mut b_result) = (Some(b), None);
    join_dyn(&mut || a_result = a.take().map(|a| a()), &mut || {
        b_result = b.take().map(|b| b())
    });
    (
        a_result.expect("join_dyn runs each task once, or propagates its panic"),
        b_result.expect("join_dyn runs each task once, or propagates its panic"),
    )
}

fn join_dyn(a: &mut (dyn FnMut() + Send), b: &mut (dyn FnMut() + Send)) {
    maybe_rayon::join(a, b);
}

#[cfg(feature = "multicore")]
pub use maybe_rayon::{current_num_threads, iter::IndexedParallelIterator};

#[cfg(not(feature = "multicore"))]
pub fn current_num_threads() -> usize {
    1
}

pub trait TryFoldAndReduce<T, E> {
    /// Implements `iter.try_fold().try_reduce()` for `rayon::iter::ParallelIterator`,
    /// falling back on `Iterator::try_fold` when the `multicore` feature flag is
    /// disabled.
    /// The `try_fold_and_reduce` function can only be called by a iter with
    /// `Result<T, E>` item type because the `fold_op` must meet the trait
    /// bounds of both `try_fold` and `try_reduce` from rayon.   
    fn try_fold_and_reduce(
        self,
        identity: impl Fn() -> T + Send + Sync,
        fold_op: impl Fn(T, Result<T, E>) -> Result<T, E> + Send + Sync,
    ) -> Result<T, E>;
}

#[cfg(feature = "multicore")]
impl<T, E, I> TryFoldAndReduce<T, E> for I
where
    T: Send + Sync,
    E: Send + Sync,
    I: maybe_rayon::iter::ParallelIterator<Item = Result<T, E>>,
{
    fn try_fold_and_reduce(
        self,
        identity: impl Fn() -> T + Send + Sync,
        fold_op: impl Fn(T, Result<T, E>) -> Result<T, E> + Send + Sync,
    ) -> Result<T, E> {
        self.try_fold(&identity, &fold_op)
            .try_reduce(&identity, |a, b| fold_op(a, Ok(b)))
    }
}

#[cfg(not(feature = "multicore"))]
impl<T, E, I> TryFoldAndReduce<T, E> for I
where
    I: std::iter::Iterator<Item = Result<T, E>>,
{
    fn try_fold_and_reduce(
        mut self,
        identity: impl Fn() -> T + Send + Sync,
        fold_op: impl Fn(T, Result<T, E>) -> Result<T, E> + Send + Sync,
    ) -> Result<T, E> {
        self.try_fold(identity(), fold_op)
    }
}

pub(crate) trait TheBestReduce {
    type Item;

    /// Combines the best of `std::iter` and `rayon` reductions.
    fn the_best_reduce(
        self,
        identity: impl Fn() -> Self::Item + Send + Sync,
        op: impl Fn(Self::Item, Self::Item) -> Self::Item + Send + Sync,
    ) -> Option<Self::Item>;
}

#[cfg(feature = "multicore")]
impl<I> TheBestReduce for I
where
    I: maybe_rayon::iter::ParallelIterator,
{
    type Item = <Self as maybe_rayon::iter::ParallelIterator>::Item;

    fn the_best_reduce(
        self,
        identity: impl Fn() -> Self::Item + Send + Sync,
        op: impl Fn(Self::Item, Self::Item) -> Self::Item + Send + Sync,
    ) -> Option<Self::Item> {
        Some(self.reduce(identity, op))
    }
}

#[cfg(not(feature = "multicore"))]
impl<I> TheBestReduce for I
where
    I: std::iter::Iterator,
{
    type Item = <Self as std::iter::Iterator>::Item;

    fn the_best_reduce(
        self,
        _: impl Fn() -> Self::Item + Send + Sync,
        f: impl Fn(Self::Item, Self::Item) -> Self::Item + Send + Sync,
    ) -> Option<Self::Item> {
        self.reduce(f)
    }
}
