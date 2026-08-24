//! An exactly-once lazy cell for expensive lookup tables.

use alloc::boxed::Box;
use core::sync::atomic::{AtomicBool, Ordering};

use once_cell::race::OnceBox;

/// A lazily-initialized cell whose initializer runs at most once, even under
/// concurrent first use.
///
/// `OnceBox::get_or_init` alone lets every racing thread run the initializer
/// and discards all but one result, which is wasteful for the large tables
/// stored here. The claim flag instead makes losing threads spin until the
/// winner stores the value. On the single-threaded no_std targets this crate
/// supports there is nothing to race with, so the spin path is unreachable
/// there; with OS threads the spin is bounded by the winner's initialization
/// time, matching the spin-lock behavior of the `lazy_static` (`spin_no_std`)
/// this replaces.
pub(crate) struct OnceTable<T> {
    claimed: AtomicBool,
    cell: OnceBox<T>,
}

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
    /// other thread touching it will spin forever.
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
