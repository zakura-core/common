//! Worker-budget configuration lifecycle against the real process-wide
//! executor. One test function: the budget is read once at initialization, so
//! the orderings under test need a process where nothing has run yet.

use zakura_sensei as sensei;

#[test]
fn configuration_is_honored_once_and_final() {
    assert_eq!(
        sensei::configure_workers(0),
        Err(sensei::WorkersConfigError::Zero)
    );
    assert_eq!(sensei::configure_workers(3), Ok(()));
    assert_eq!(
        sensei::configure_workers(5),
        Err(sensei::WorkersConfigError::AlreadyConfigured)
    );
    // The first worker-budget read initializes the executor with the
    // configured value — even with RAYON_NUM_THREADS exported by a harness.
    let expected = if cfg!(feature = "multicore") { 3 } else { 1 };
    assert_eq!(sensei::worker_budget(), expected);
    assert_eq!(
        sensei::configure_workers(5),
        Err(sensei::WorkersConfigError::AlreadyInitialized)
    );
    // Warmup and verification reuse the already-initialized pool.
    sensei::warm_up_verifier();
    assert_eq!(sensei::worker_budget(), expected);
}
