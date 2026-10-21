//! Target-dependent ownership for the lazy Sinsemilla affine generator vector.
//!
//! See the [public cache account](crate::primitives#lazy-data-and-ownership).
//! With pointer atomics, the static cell retains the published vector for the
//! process lifetime; without them, each access returns a fresh owned value.

use alloc::boxed::Box;
#[cfg(target_has_atomic = "ptr")]
use core::sync::atomic::{AtomicBool, Ordering};

#[cfg(target_has_atomic = "ptr")]
use once_cell::race::OnceBox;

/// A lazily-initialized cell whose initializer runs at most once, even under
/// concurrent first use.
///
/// `OnceBox::get_or_init` alone lets every racing thread run the initializer
/// and discards all but one result, which is wasteful for the large tables
/// stored here. The claim flag instead makes losing callers spin until the
/// winner stores the value. There is no claim reset or poison recovery; this
/// requires an initializer that returns without panicking or reentering the
/// same cell. It must not be interrupted by a caller that waits on this cell.
#[cfg(target_has_atomic = "ptr")]
pub(crate) struct OnceTable<T> {
    claimed: AtomicBool,
    cell: OnceBox<T>,
}

#[cfg(target_has_atomic = "ptr")]
impl<T> OnceTable<T> {
    pub(crate) const fn new() -> Self {
        OnceTable {
            claimed: AtomicBool::new(false),
            cell: OnceBox::new(),
        }
    }

    /// Gets the contents of the cell, initializing it with `f` if the cell was
    /// empty.
    ///
    /// `f` runs at most once across all threads. It must not panic: a panicked
    /// initializer leaves the cell permanently claimed-but-empty, and any
    /// later access will spin forever. Reentering this cell during initialization
    /// also spins without allowing the initializer to finish.
    pub(crate) fn get_or_init(&self, f: impl FnOnce() -> T) -> &T {
        if let Some(value) = self.cell.get() {
            return value;
        }
        if !self.claimed.swap(true, Ordering::AcqRel) {
            // We won the claim, so we run the initializer; `set` cannot fail.
            let _ = self.cell.set(Box::new(f()));
        }
        loop {
            if let Some(value) = self.cell.get() {
                return value;
            }
            core::hint::spin_loop();
        }
    }
}

/// Without pointer atomics, retain no shared state or interrupt assumptions.
/// Each access runs its initializer and returns an owned box, released by the
/// caller; there is no at-most-once guarantee on this target.
#[cfg(not(target_has_atomic = "ptr"))]
pub(crate) struct OnceTable<T>(core::marker::PhantomData<fn() -> T>);

#[cfg(not(target_has_atomic = "ptr"))]
impl<T> OnceTable<T> {
    pub(crate) const fn new() -> Self {
        Self(core::marker::PhantomData)
    }

    pub(crate) fn get_or_init(&self, init: impl FnOnce() -> T) -> Box<T> {
        Box::new(init())
    }
}
