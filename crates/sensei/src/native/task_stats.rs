//! Test-only task timing accumulators shared by the verification stage
//! attribution and the final-MSM batch probes.
//!
//! Pool threads record through a shared reference into relaxed atomics, so
//! no thread-local state travels to workers. A disabled accumulator costs one
//! branch per task and records nothing.

use std::{
    sync::atomic::{AtomicU64, AtomicUsize, Ordering},
    time::Instant,
};

/// Count, total, and maximum duration of one class of tasks.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct TaskSummary {
    pub(crate) count: usize,
    pub(crate) sum_ns: u64,
    pub(crate) max_ns: u64,
}

/// Accumulates a [`TaskSummary`] from any thread.
#[derive(Debug, Default)]
pub(crate) struct TaskStats {
    enabled: bool,
    count: AtomicUsize,
    sum_ns: AtomicU64,
    max_ns: AtomicU64,
}

impl TaskStats {
    pub(crate) fn new(enabled: bool) -> Self {
        Self {
            enabled,
            ..Self::default()
        }
    }

    /// Starts timing one task when enabled.
    #[inline]
    pub(crate) fn start(&self) -> Option<Instant> {
        self.enabled.then(Instant::now)
    }

    /// Records the interval since `started`.
    #[inline]
    pub(crate) fn record(&self, started: Option<Instant>) {
        if let Some(started) = started {
            let elapsed = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
            self.count.fetch_add(1, Ordering::Relaxed);
            self.sum_ns.fetch_add(elapsed, Ordering::Relaxed);
            self.max_ns.fetch_max(elapsed, Ordering::Relaxed);
        }
    }

    pub(crate) fn snapshot(&self) -> TaskSummary {
        TaskSummary {
            count: self.count.load(Ordering::Relaxed),
            sum_ns: self.sum_ns.load(Ordering::Relaxed),
            max_ns: self.max_ns.load(Ordering::Relaxed),
        }
    }
}
