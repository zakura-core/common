//! `RAYON_NUM_THREADS` sizes the unconfigured pool in production builds.
//!
//! This target links the library without `cfg(test)`, so no bench override
//! applies: a positive integer `RAYON_NUM_THREADS` must constrain the workers
//! exactly, with no configuration call and no source patch.

use zakura_sensei as sensei;

#[test]
fn unconfigured_pool_honors_rayon_num_threads() {
    let env = std::env::var("RAYON_NUM_THREADS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|&workers| workers != 0);
    let budget = sensei::worker_budget();
    match env {
        Some(workers) if cfg!(feature = "multicore") => assert_eq!(budget, workers),
        _ if cfg!(feature = "multicore") => assert!(budget >= 1),
        _ => assert_eq!(budget, 1),
    }
    // The pool is final once read; late configuration reports that.
    assert_eq!(
        sensei::configure_workers(budget),
        Err(sensei::WorkersConfigError::AlreadyInitialized)
    );
}
