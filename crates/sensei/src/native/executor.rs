//! Shared execution resources, independent of either proof role.
//!
//! [`PoolExecutor::get`] owns one process-lifetime executor; both runtimes keep
//! a shared reference to it as described in [`super::srs`]. With `multicore`,
//! it attempts to create a private Rayon pool when more than one worker is
//! available. A single worker or pool-construction failure uses the serial
//! path; without `multicore`, execution is always serial.
//!
//! [`PoolExecutor::run`] enters the selected pool, or runs on its caller for the
//! serial path. Its [`PoolContext`] scopes nested joins to that choice without
//! selecting Rayon's global pool. The executor owns neither circuit data nor
//! request scratch and receives no caller RNG: proof APIs sample on the calling
//! thread before entering it for proof work.
use std::sync::OnceLock;
use udon::exec::{Executor, SerialExecutor, TaskBudget};
pub(super) struct PoolExecutor {
    #[cfg(feature = "multicore")]
    pool: Option<rayon::ThreadPool>,
}

impl PoolExecutor {
    /// Shared workers without initializing either the prover or verifier state.
    pub(super) fn get() -> &'static Self {
        static EXECUTOR: OnceLock<PoolExecutor> = OnceLock::new();
        EXECUTOR.get_or_init(Self::new)
    }

    fn new() -> Self {
        #[cfg(feature = "multicore")]
        {
            let workers = std::thread::available_parallelism().map_or(1, usize::from);
            #[cfg(test)]
            let workers = std::env::var("SENSEI_BENCH_WORKERS")
                .ok()
                .map(|value| value.parse::<usize>().expect("positive worker count"))
                .unwrap_or(workers);
            assert!(workers > 0);
            // Worker creation is an optimization; failure keeps a serial path.
            let pool = (workers > 1)
                .then(|| {
                    rayon::ThreadPoolBuilder::new()
                        .num_threads(workers)
                        .build()
                        .ok()
                })
                .flatten();
            Self { pool }
        }
        #[cfg(not(feature = "multicore"))]
        Self {}
    }

    pub(super) fn budget(&self) -> TaskBudget {
        #[cfg(feature = "multicore")]
        if let Some(pool) = &self.pool {
            return TaskBudget::new(pool.current_num_threads()).expect("nonempty pool");
        }
        TaskBudget::SERIAL
    }
}

impl PoolExecutor {
    pub(super) fn run<R: Send>(&self, work: impl FnOnce(&PoolContext) -> R + Send) -> R {
        #[cfg(feature = "multicore")]
        if let Some(pool) = &self.pool {
            return pool.install(|| work(&PoolContext { parallel: true }));
        }
        work(&PoolContext {
            #[cfg(feature = "multicore")]
            parallel: false,
        })
    }
}

// Only constructed inside the selected pool (or for the serial fallback).
// Nested joins never re-enter a pool or select Rayon's global pool.
pub(super) struct PoolContext {
    #[cfg(feature = "multicore")]
    parallel: bool,
}
impl Executor for PoolContext {
    fn join<L, R, A, B>(&self, left: L, right: R) -> (A, B)
    where
        L: FnOnce() -> A + Send,
        R: FnOnce() -> B + Send,
        A: Send,
        B: Send,
    {
        #[cfg(feature = "multicore")]
        let parallel = self.parallel;
        #[cfg(not(feature = "multicore"))]
        let parallel = false;
        let (mut left, mut right) = (Some(left), Some(right));
        let (mut left_result, mut right_result) = (None, None);
        join_dyn(
            parallel,
            &mut || left_result = Some(left.take().expect("left job runs once")()),
            &mut || right_result = Some(right.take().expect("right job runs once")()),
        );
        (
            left_result.expect("left job ran"),
            right_result.expect("right job ran"),
        )
    }
}

// The only join the backends instantiate: every generic `Executor::join` call
// funnels through these two closure types, so Rayon's work-splitting machinery
// is compiled once instead of once per call site and closure pair.
fn join_dyn(parallel: bool, left: &mut (dyn FnMut() + Send), right: &mut (dyn FnMut() + Send)) {
    #[cfg(feature = "multicore")]
    if parallel {
        rayon::join(|| left(), || right());
        return;
    }
    let _ = parallel;
    // Delegating keeps the serial contract: the right job runs even when the
    // left one unwinds.
    SerialExecutor.join(|| left(), || right());
}

#[cfg(all(test, feature = "multicore"))]
mod tests {
    use super::*;
    #[test]
    fn join_runs_the_right_job_when_the_left_unwinds() {
        let ran = std::sync::atomic::AtomicBool::new(false);
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            PoolExecutor { pool: None }.run(|context| {
                context.join(
                    || panic!("left job"),
                    || ran.store(true, std::sync::atomic::Ordering::Relaxed),
                );
            });
        }));
        assert!(unwound.is_err());
        assert!(ran.load(std::sync::atomic::Ordering::Relaxed));
    }

    #[test]
    fn pool_context_uses_selected_workers_and_serial_fallback() {
        let caller = std::thread::current().id();
        let serial = PoolExecutor { pool: None };
        serial.run(|context| {
            assert_eq!(
                context.join(|| std::thread::current().id(), || 2),
                (caller, 2)
            );
        });
        for workers in [1, 2, 4] {
            let executor = PoolExecutor {
                pool: Some(
                    rayon::ThreadPoolBuilder::new()
                        .num_threads(workers)
                        .build()
                        .unwrap(),
                ),
            };
            executor.run(|context| {
                let check = || {
                    assert_eq!(rayon::current_num_threads(), workers);
                    assert_ne!(std::thread::current().id(), caller);
                };
                context.join(check, || context.join(check, check));
            });
        }
    }
}
