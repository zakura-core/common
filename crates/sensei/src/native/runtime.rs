//! Process-owned preparation, execution, and reusable proof scratch.
//!
//! See [`super::srs`] for the shared runtime owners and workspace retention
//! policy. [`runtime`] obtains the SRS, then the shared executor, then prepares
//! [`PreparedProver`] inside that executor. Its `OnceLock<Result<ProverRuntime,
//! Error>>` retains both successful preparation and returned errors; the public
//! [`crate::warm_up_prover`] contract describes how cached errors are reported.
//!
//! [`prove`] finishes runtime initialization before sampling randomness on the
//! calling thread. Only the sampled values enter the worker pool: the borrowed
//! [`RandomSource`] needs neither `Send` nor `Sync` and is never stored in the
//! runtime. Sampling precedes workspace acquisition and proof execution, so
//! callbacks may reenter proof or warmup APIs without holding the idle-slot
//! mutex. [`WorkspaceCache`] lends the call's workspace to the pipeline and
//! applies the common retention policy after it returns. Warmup initializes
//! preparation and workers without acquiring a proof workspace.

use super::{
    PreparedProver, ProverWorkspace, randomness::ProvingRandomness, srs::PreparedSrs,
    worker::Execution,
};
use crate::{
    Error, ProvingRequest, RandomSource,
    tuning::{self, WorkspaceRetention},
};
use std::sync::{Mutex, MutexGuard, OnceLock};

struct ProverRuntime {
    prepared: PreparedProver,
    executor: &'static PoolExecutor,
    workspace: WorkspaceCache,
}

static RUNTIME: OnceLock<Result<ProverRuntime, Error>> = OnceLock::new();

#[derive(Default)]
struct WorkspaceCache(Mutex<Option<ProverWorkspace>>);

impl WorkspaceCache {
    fn with<R>(&self, work: impl FnOnce(&mut ProverWorkspace) -> R) -> R {
        self.with_policy(tuning::WORKSPACE, work)
    }

    fn with_policy<R>(
        &self,
        policy: WorkspaceRetention,
        work: impl FnOnce(&mut ProverWorkspace) -> R,
    ) -> R {
        if policy == WorkspaceRetention::Discard {
            let mut workspace = ProverWorkspace::default();
            let result = work(&mut workspace);
            #[cfg(all(test, feature = "verifier"))]
            LAST_WORKSPACE.set(Some(WorkspaceResources::capture(&workspace)));
            return result;
        }
        let mut workspace = lock(&self.0).take().unwrap_or_default();
        let result = work(&mut workspace);
        #[cfg(all(test, feature = "verifier"))]
        LAST_WORKSPACE.set(Some(WorkspaceResources::capture(&workspace)));
        // Retain one idle workspace. Concurrent calls remain independent, but
        // a transient burst cannot permanently grow the scratch cache. Normal
        // errors return storage; unwinding discards the active workspace.
        let mut idle = lock(&self.0);
        if idle.is_none() {
            *idle = Some(workspace);
        }
        result
    }
}

use super::executor::{PoolContext, PoolExecutor};

fn runtime() -> Result<&'static ProverRuntime, Error> {
    RUNTIME
        .get_or_init(|| {
            let srs = PreparedSrs::shared();
            let executor = PoolExecutor::get();
            let prepared =
                executor.run(|context| PreparedProver::new(srs, context, executor.budget()))?;
            Ok(ProverRuntime {
                prepared,
                executor,
                workspace: WorkspaceCache::default(),
            })
        })
        .as_ref()
        .map_err(|&error| error)
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

pub(crate) fn warm_up_prover() {
    let _ = runtime();
}

#[cfg(all(test, feature = "verifier"))]
pub(super) fn prepared_srs_for_test() -> Option<&'static std::sync::Arc<PreparedSrs>> {
    RUNTIME.get().map(|result| {
        result
            .as_ref()
            .unwrap()
            .prepared
            .target
            .parameters()
            .shared_srs()
    })
}

#[cfg(all(test, feature = "verifier"))]
#[derive(Clone, Copy)]
struct WorkspaceResources {
    allocations: usize,
    buffers: usize,
    polynomial: usize,
    lookup: usize,
    lookup_buffers: usize,
    lookup_allocations: usize,
    msm: usize,
    fft: usize,
    ipa: usize,
}
#[cfg(all(test, feature = "verifier"))]
impl WorkspaceResources {
    fn capture(workspace: &ProverWorkspace) -> Self {
        let polynomial = workspace.buffers.inventory();
        let lookup = workspace.lookup.inventory();
        Self {
            allocations: polynomial.allocations,
            buffers: polynomial.buffers,
            polynomial: polynomial.bytes,
            lookup: lookup.bytes,
            lookup_buffers: lookup.buffers,
            lookup_allocations: lookup.allocations,
            msm: workspace.msm.retained_bytes(),
            fft: workspace.fft.retained_bytes(),
            ipa: workspace.ipa.retained_bytes(),
        }
    }
}
#[cfg(all(test, feature = "verifier"))]
std::thread_local! {
    static LAST_WORKSPACE: std::cell::Cell<Option<WorkspaceResources>> = const { std::cell::Cell::new(None) };
}

#[cfg(all(test, feature = "verifier"))]
pub(crate) fn benchmark_resources() {
    let runtime = runtime().unwrap();
    let resources = LAST_WORKSPACE
        .get()
        .expect("benchmark primes a proof on this thread");
    let idle = lock(&runtime.workspace.0);
    let idle_bytes = idle.as_ref().map_or(0, |workspace| {
        let r = WorkspaceResources::capture(workspace);
        r.polynomial + r.lookup + r.msm + r.fft + r.ipa
    });
    eprintln!(
        "SENSEI_RESOURCES workers={} msm_bytes={} fft_bytes={} ipa_bytes={} polynomial_bytes={} polynomial_buffers={} polynomial_allocations={} lookup_bytes={} lookup_buffers={} lookup_allocations={} idle_workspace_bytes={} retention={:?}",
        runtime.executor.budget().get(),
        resources.msm,
        resources.fft,
        resources.ipa,
        resources.polynomial,
        resources.buffers,
        resources.allocations,
        resources.lookup,
        resources.lookup_buffers,
        resources.lookup_allocations,
        idle_bytes,
        tuning::WORKSPACE,
    );
}

pub(crate) fn prove(
    request: &ProvingRequest,
    randomness: &mut dyn RandomSource,
) -> Result<Vec<u8>, Error> {
    let runtime = runtime()?;
    #[cfg(test)]
    let timing = super::stage_timing::Recorder::begin();
    // The RNG need not be Send and may reenter proving. Sample on its caller
    // before borrowing a workspace or entering the worker pool.
    let randomness = ProvingRandomness::sample(randomness, request.action_count())?;
    runtime.workspace.with(|workspace| {
        let run = |context: &PoolContext| {
            runtime.prepared.create_proof_sampled(
                request,
                randomness,
                workspace,
                Execution::new(context, runtime.executor.budget()),
                #[cfg(test)]
                timing,
            )
        };
        #[cfg(test)]
        {
            super::stage_timing::Context::transfer(|timings| {
                runtime
                    .executor
                    .run(|context| timings.enter(|| run(context)))
            })
        }
        #[cfg(not(test))]
        runtime.executor.run(run)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::buffer::BufferInventory;
    use udon::field::Fp;

    #[test]
    fn cache_retains_one_workspace_returns_errors_and_discards_panics() {
        let cache = WorkspaceCache::default();
        let failure: Result<(), ()> =
            cache.with_policy(WorkspaceRetention::RetainOne, |workspace| {
                drop(workspace.buffers.take(64, <Fp>::ONE, true));
                Err(())
            });
        assert_eq!(failure, Err(()));
        assert_eq!(
            lock(&cache.0).as_ref().unwrap().buffers.inventory(),
            BufferInventory {
                allocations: 1,
                buffers: 1,
                bytes: 2048,
            }
        );
        cache.with_policy(WorkspaceRetention::RetainOne, |outer| {
            assert_eq!(
                outer.buffers.inventory(),
                BufferInventory {
                    allocations: 1,
                    buffers: 1,
                    bytes: 2048,
                }
            );
            // A second caller can finish while the first still owns its lease.
            cache.with_policy(WorkspaceRetention::RetainOne, |inner| {
                assert_eq!(
                    inner.buffers.inventory(),
                    BufferInventory {
                        allocations: 0,
                        buffers: 0,
                        bytes: 0,
                    }
                );
                drop(inner.buffers.take(128, <Fp>::ONE, true));
            });
        });
        assert_eq!(
            lock(&cache.0).as_ref().unwrap().buffers.inventory(),
            BufferInventory {
                allocations: 1,
                buffers: 1,
                bytes: 4096,
            }
        );
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            cache.with_policy(WorkspaceRetention::RetainOne, |workspace| {
                let _buffer = workspace.buffers.take(128, <Fp>::ZERO, true);
                panic!("pipeline failure");
            });
        }));
        assert!(panic.is_err());
        assert!(lock(&cache.0).is_none());
        cache.with_policy(WorkspaceRetention::RetainOne, |workspace| {
            assert_eq!(
                workspace.buffers.inventory(),
                BufferInventory {
                    allocations: 0,
                    buffers: 0,
                    bytes: 0,
                }
            )
        });
    }

    #[test]
    fn discard_releases_workspace_on_success_error_and_panic() {
        let cache = WorkspaceCache::default();
        for fail in [false, true] {
            let result = cache.with_policy(WorkspaceRetention::Discard, |workspace| {
                assert_eq!(
                    workspace.buffers.inventory(),
                    BufferInventory {
                        allocations: 0,
                        buffers: 0,
                        bytes: 0,
                    }
                );
                drop(workspace.buffers.take(64, <Fp>::ONE, true));
                cache.with_policy(WorkspaceRetention::Discard, |other| {
                    assert_eq!(
                        other.buffers.inventory(),
                        BufferInventory {
                            allocations: 0,
                            buffers: 0,
                            bytes: 0,
                        }
                    );
                    drop(other.buffers.take(128, <Fp>::ONE, true));
                });
                if fail { Err(()) } else { Ok(()) }
            });
            assert_eq!(result.is_err(), fail);
            assert!(lock(&cache.0).is_none());
        }
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            cache.with_policy(WorkspaceRetention::Discard, |workspace| {
                let _buffer = workspace.buffers.take(128, <Fp>::ZERO, true);
                panic!("pipeline failure");
            });
        }));
        assert!(panic.is_err());
        assert!(lock(&cache.0).is_none());
    }
}
