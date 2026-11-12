//! Shared execution resources, independent of either proof role.
//!
//! [`PoolExecutor::get`] owns one process-lifetime executor; both runtimes keep
//! a shared reference to it as described in [`super::srs`]. With `multicore`,
//! it attempts to create a private Rayon pool when more than one worker is
//! available. A single worker or pool-construction failure uses the serial
//! path; without `multicore`, execution is always serial.
//!
//! The pool's worker budget follows Rayon-consistent precedence: an explicit
//! [`configure`] budget wins, a positive integer `RAYON_NUM_THREADS` is the
//! default when unconfigured, and the detected available parallelism is the
//! fallback. The pool stays private to Sensei: the environment variable never
//! selects or resizes Rayon's global pool here. [`configure`] and
//! initialization serialize on one configuration state, so a configuration
//! either takes effect or is reported as lost — never silently ignored.
//!
//! [`PoolExecutor::run`] enters the selected pool, or runs on its caller for the
//! serial path. Its [`PoolContext`] scopes nested joins to that choice without
//! selecting Rayon's global pool. The executor owns neither circuit data nor
//! request scratch and receives no caller RNG: proof APIs sample on the calling
//! thread before entering it for proof work.
use crate::WorkersConfigError;
use std::sync::{Mutex, MutexGuard, OnceLock};
use udon::exec::{Executor, SerialExecutor, TaskBudget};

pub(crate) struct PoolExecutor {
    #[cfg(feature = "multicore")]
    pool: Option<rayon::ThreadPool>,
}

static EXECUTOR: OnceLock<PoolExecutor> = OnceLock::new();

// One shared configuration state makes `configure` and initialization
// race-free: whichever locks first decides whether the explicit budget is
// observed, and a late `configure` reports `AlreadyInitialized` instead of
// storing a value initialization will never read.
struct Config {
    workers: Option<usize>,
    initialized: bool,
}
static CONFIG: Mutex<Config> = Mutex::new(Config {
    workers: None,
    initialized: false,
});

fn lock(mutex: &Mutex<Config>) -> MutexGuard<'_, Config> {
    mutex
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Stores the worker budget read by executor initialization. The public
/// [`crate::configure_workers`] contract documents the precedence and errors.
pub(crate) fn configure(workers: usize) -> Result<(), WorkersConfigError> {
    if workers == 0 {
        return Err(WorkersConfigError::Zero);
    }
    let mut config = lock(&CONFIG);
    if config.initialized {
        return Err(WorkersConfigError::AlreadyInitialized);
    }
    if config.workers.is_some() {
        return Err(WorkersConfigError::AlreadyConfigured);
    }
    config.workers = Some(workers);
    Ok(())
}

/// The pool's worker count, initializing the shared workers if needed.
pub(crate) fn worker_budget() -> usize {
    PoolExecutor::get().budget().get()
}

/// Rayon-consistent worker-budget precedence: the explicit budget wins,
/// `RAYON_NUM_THREADS` is the default when unconfigured, and the detected
/// parallelism is the fallback. A zero or unparseable environment value is
/// ignored rather than clamped.
#[cfg(feature = "multicore")]
fn resolve_workers(configured: Option<usize>, env: Option<&str>, detected: usize) -> usize {
    configured
        .or_else(|| {
            env.and_then(|value| value.parse().ok())
                .filter(|&workers| workers != 0)
        })
        .unwrap_or(detected)
}

impl PoolExecutor {
    /// Shared workers without initializing either the prover or verifier state.
    pub(crate) fn get() -> &'static Self {
        EXECUTOR.get_or_init(Self::new)
    }

    fn new() -> Self {
        let configured = {
            let mut config = lock(&CONFIG);
            config.initialized = true;
            config.workers
        };
        #[cfg(feature = "multicore")]
        {
            let detected = std::thread::available_parallelism().map_or(1, usize::from);
            let workers = resolve_workers(
                configured,
                std::env::var("RAYON_NUM_THREADS").ok().as_deref(),
                detected,
            );
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
        {
            let _ = configured;
            Self {}
        }
    }

    pub(crate) fn budget(&self) -> TaskBudget {
        #[cfg(feature = "multicore")]
        if let Some(pool) = &self.pool {
            return TaskBudget::new(pool.current_num_threads()).expect("nonempty pool");
        }
        TaskBudget::SERIAL
    }
}

impl PoolExecutor {
    pub(crate) fn run<R: Send>(&self, work: impl FnOnce(&PoolContext) -> R + Send) -> R {
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
pub(crate) struct PoolContext {
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
        rayon::join(left, right);
        return;
    }
    let _ = parallel;
    // Delegating keeps the serial contract: the right job runs even when the
    // left one unwinds.
    SerialExecutor.join(left, right);
}

#[cfg(all(test, feature = "multicore"))]
mod tests {
    use super::*;

    #[test]
    fn worker_resolution_prefers_explicit_then_env_then_detected() {
        // The explicit budget wins over everything.
        assert_eq!(resolve_workers(Some(4), Some("8"), 16), 4);
        assert_eq!(resolve_workers(Some(1), None, 16), 1);
        // RAYON_NUM_THREADS is the default when unconfigured.
        assert_eq!(resolve_workers(None, Some("8"), 16), 8);
        // Zero and unparseable environment values fall through to detection.
        assert_eq!(resolve_workers(None, Some("0"), 16), 16);
        assert_eq!(resolve_workers(None, Some("eight"), 16), 16);
        assert_eq!(resolve_workers(None, Some(""), 16), 16);
        assert_eq!(resolve_workers(None, Some("-2"), 16), 16);
        assert_eq!(resolve_workers(None, None, 16), 16);
    }

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
