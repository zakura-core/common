//! Primitive caches with pointer atomics, owned values elsewhere.
//!
//! The [public ownership account](crate::primitives#lazy-data-and-ownership)
//! lists the consumers. With `target_has_atomic = "ptr"`, [`Cache`] is
//! `once_cell::race::OnceBox` and [`Cached`] is a static borrow. Concurrent
//! first accesses may run multiple initializers: one boxed result is published,
//! the others are dropped, and all successful callers borrow the published
//! value. The static caches retain it for the process lifetime. A panicking
//! initializer publishes nothing and does not prevent a later initialization.
//!
//! Without pointer atomics, `Cache` stores no value and `Cached` is an owned
//! `Box`. Every `get_or_init` invokes its initializer; the caller drops the value
//! after use. Sinsemilla's `OnceTable` uses this same ownership split but a
//! different initialization claim on atomic targets; it is not a `Cache` alias.
//!
//! The uncached path keeps signature primitives available on targets such as
//! Cortex-M0 without requiring an interrupt policy or a critical-section hook.

#[cfg(target_has_atomic = "ptr")]
pub(crate) use once_cell::race::OnceBox as Cache;
#[cfg(target_has_atomic = "ptr")]
pub(crate) type Cached<T> = &'static T;

#[cfg(not(target_has_atomic = "ptr"))]
pub(crate) type Cached<T> = alloc::boxed::Box<T>;

#[cfg(not(target_has_atomic = "ptr"))]
pub(crate) struct Cache<T>(core::marker::PhantomData<fn() -> T>);

#[cfg(not(target_has_atomic = "ptr"))]
impl<T> Cache<T> {
    pub(crate) const fn new() -> Self {
        Self(core::marker::PhantomData)
    }

    pub(crate) fn get_or_init(&self, init: impl FnOnce() -> Cached<T>) -> Cached<T> {
        init()
    }
}
