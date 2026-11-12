//! Opt-in test-only verification-stage attribution.
//!
//! Wall intervals are marked on the calling thread between pipeline
//! milestones. Fold, point-prefetch, and final-MSM task durations accumulate
//! from pool threads through [`TaskStats`], so no thread-local state travels
//! to workers (the executor's `run` enters the pool, where the caller's
//! thread-locals are invisible). Enable on the calling thread with [`enable`]
//! before `verify_proofs`, then read the result with [`take`].

use crate::native::task_stats::{TaskStats, TaskSummary};
use std::{
    cell::{Cell, RefCell},
    time::Instant,
};

/// The recorded stages, in pipeline order. Each interval runs from the
/// previous mark (or from [`Recorder::begin`]) to its own mark.
#[derive(Clone, Copy)]
#[repr(usize)]
pub(crate) enum Stage {
    /// `weights`: batch weight sampling, runtime acquisition, and chunking.
    Weights = 0,
    /// `fold`: proof folding into chunk equations, serial or pooled.
    Fold,
    /// `merge`: merging chunk equations and returning their shells.
    Merge,
    /// `msm_prepare`: final-MSM planning and workspace growth.
    MsmPrepare,
    /// `msm_execute`: final-MSM execution.
    MsmExecute,
    /// `finish`: the fixed-generator sum, the identity check, and leaving
    /// the pool.
    Finish,
    /// `return`: returning the combined equation and workspace to the pools.
    Return,
}

impl Stage {
    /// Every stage, in recorded order.
    pub(crate) const ALL: [Self; 7] = [
        Self::Weights,
        Self::Fold,
        Self::Merge,
        Self::MsmPrepare,
        Self::MsmExecute,
        Self::Finish,
        Self::Return,
    ];

    /// The stage's stable output token.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::Weights => "weights",
            Self::Fold => "fold",
            Self::Merge => "merge",
            Self::MsmPrepare => "msm_prepare",
            Self::MsmExecute => "msm_execute",
            Self::Finish => "finish",
            Self::Return => "return",
        }
    }
}

/// Stable stage names in recorded order; the discriminants are checked to be
/// the recorded positions.
pub(crate) const NAMES: [&str; Stage::ALL.len()] = {
    let mut names = [""; Stage::ALL.len()];
    let mut index = 0;
    while index < names.len() {
        assert!(Stage::ALL[index] as usize == index);
        names[index] = Stage::ALL[index].name();
        index += 1;
    }
    names
};

/// Final-MSM task classes probed per input group: preparation (scalar
/// recoding into retained records), window accumulation, and reduction.
pub(crate) const MSM_TASK_KINDS: [&str; 3] = ["prepare", "window", "reduce"];

/// Scheduling facts recorded alongside the intervals.
#[derive(Clone, Debug, Default)]
pub(crate) struct Facts {
    /// Fold chunks the batch cut.
    pub(crate) fold_jobs: usize,
    /// Proofs per fold chunk (zero on the serial path).
    pub(crate) fold_chunk: usize,
    /// Final-MSM task budget requested.
    pub(crate) msm_budget: usize,
    /// Final-MSM work bundles actually prepared.
    pub(crate) msm_workers: usize,
    /// Per final-MSM input group: `(partitions, output slots, grain)`.
    pub(crate) msm_groups: Vec<(usize, usize, usize)>,
    /// Retained bytes of the leased workspace before and after the batch.
    pub(crate) workspace_before: usize,
    pub(crate) workspace_after: usize,
}

/// One verification call's attribution.
pub(crate) struct VerifyTimings {
    /// Per-stage elapsed nanoseconds, in [`NAMES`] order.
    pub(crate) elapsed_ns: [u128; NAMES.len()],
    /// Fold tasks (one per chunk; on the serial path, the single fold).
    pub(crate) fold: TaskSummary,
    /// Point prefetch (batch decoding) per proof.
    pub(crate) prefetch: TaskSummary,
    /// Final-MSM tasks per input group, in [`MSM_TASK_KINDS`] order.
    pub(crate) msm: Vec<[TaskSummary; 3]>,
    pub(crate) facts: Facts,
}

thread_local! {
    static ENABLED: Cell<bool> = const { Cell::new(false) };
    static LAST: RefCell<Option<VerifyTimings>> = const { RefCell::new(None) };
}

/// Enables attribution for the next verification on this thread.
pub(crate) fn enable() {
    LAST.with(|last| assert!(last.borrow().is_none()));
    ENABLED.with(|enabled| enabled.set(true));
}

/// Disables attribution and returns the last completed verification's timings.
pub(crate) fn take() -> Option<VerifyTimings> {
    ENABLED.with(|enabled| enabled.set(false));
    LAST.with(|last| last.borrow_mut().take())
}

/// Collects one call's attribution; a disabled recorder does nothing.
pub(crate) struct Recorder {
    last: Option<Instant>,
    elapsed_ns: [u128; NAMES.len()],
    pub(crate) fold: TaskStats,
    pub(crate) prefetch: TaskStats,
    pub(crate) msm: Vec<[TaskStats; 3]>,
    pub(crate) facts: Facts,
}

impl Recorder {
    /// Starts recording if attribution is enabled on this thread.
    pub(crate) fn begin() -> Self {
        Self::with(ENABLED.with(Cell::get))
    }

    /// A recorder that records nothing, for entry points outside `verify`.
    pub(crate) fn disabled() -> Self {
        Self::with(false)
    }

    fn with(enabled: bool) -> Self {
        Self {
            last: enabled.then(Instant::now),
            elapsed_ns: [0; NAMES.len()],
            fold: TaskStats::new(enabled),
            prefetch: TaskStats::new(enabled),
            msm: Vec::new(),
            facts: Facts::default(),
        }
    }

    /// Closes the interval that began at the previous mark (or at `begin`)
    /// and attributes it to `stage`.
    pub(crate) fn mark(&mut self, stage: Stage) {
        if let Some(last) = self.last {
            let now = Instant::now();
            self.elapsed_ns[stage as usize] += now.duration_since(last).as_nanos();
            self.last = Some(now);
        }
    }

    /// Provisions one probe set per final-MSM input group.
    pub(crate) fn msm_inputs(&mut self, groups: usize) {
        if self.last.is_some() {
            self.msm = (0..groups)
                .map(|_| core::array::from_fn(|_| TaskStats::new(true)))
                .collect();
        }
    }

    pub(crate) fn finish(self) {
        if self.last.is_some() {
            LAST.with(|last| {
                *last.borrow_mut() = Some(VerifyTimings {
                    elapsed_ns: self.elapsed_ns,
                    fold: self.fold.snapshot(),
                    prefetch: self.prefetch.snapshot(),
                    msm: self
                        .msm
                        .iter()
                        .map(|kinds| kinds.each_ref().map(TaskStats::snapshot))
                        .collect(),
                    facts: self.facts,
                });
            });
        }
    }
}
