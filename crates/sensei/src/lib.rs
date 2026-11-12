//! Sensei creates post-NU6.3 Ironwood Action proofs and verifies all three
//! pinned Orchard Action circuit versions through one safe Rust interface.
//!
//! Construct canonical field elements and points with their `from_bytes`
//! constructors, assemble each `Action` from a `PublicStatement` and a
//! `PrivateWitness`, then pass the actions to `ProvingRequest::new`. Call
//! `create_proof` with the request and a caller-owned [`RandomSource`].
//!
//! Canonical constructors validate encodings; request construction checks
//! public points and representable storage dimensions. Proving checks the
//! witness relations and returns the proof's
//! verifier-facing bytes. `warm_up_prover` optionally prepares the process-wide
//! proving state ahead of the first proof. Arithmetic is variable-time.
//!
//! Verify with `VerificationRequest::new` and `verify_proofs`, borrowing the
//! proof and its ordered public statements. Verification supports any nonempty
//! Action count with representable storage, as does proving. Verification
//! shares prepared SRS tables, codebooks, and workers with
//! proving, and never initializes the prover's circuit state. The first nonempty
//! `verify_proofs` call prepares the verifier on demand; `warm_up_verifier`
//! can do this eagerly, and `warm_up_verifier_scratch` can additionally
//! provision verification scratch for an expected batch shape, reporting what
//! it provisioned in a `VerificationPlan`. Warming either role prepares the
//! shared SRS once; warming the other then prepares only its remaining state.
//! `warm_up` warms both roles.
//! Each verification request selects its `CircuitVersion`; batches may mix
//! versions and share one final verification equation. Keys are embedded.
//!
//! `configure_workers` optionally bounds the shared worker pool before the
//! first proof, verification, or warm-up call; `worker_budget` reports the
//! pool's final budget. Unconfigured processes honor a positive integer
//! `RAYON_NUM_THREADS` before falling back to the detected parallelism.
//!
//! [`redpallas`] provides signing, spend-key randomization, and individual or
//! batch signature verification. Its generator preparation is independent of
//! proof workers, SRS tables, and circuit state. See its
//! [caller requirements](redpallas#caller-requirements) for timing and randomness
//! assumptions.
//!
//! With default features disabled, Sensei provides `no_std` + `alloc`
//! arithmetic, protocol primitives, and RedPallas signature operations.
//! `prover` and `verifier` independently enable proof creation and verification
//! (each requires `std`). `multicore` optionally adds Rayon execution. The default
//! configuration enables both proof roles and multicore execution.
//!
//! # Crate map
//!
//! Start with the documentation that owns each part of the implementation:
//!
//! | Area | Entry point |
//! | --- | --- |
//! | Standalone field, point, and protocol operations | [`primitives`] |
//! | Standalone signatures and key randomization | [`redpallas`] |
//! | Circuit facts, recipes, and stored record layouts | [`sensei_shared`] |
//! | Host-generated embedded data and the `build.rs` pipeline | [`sensei-artifacts`](../zakura_sensei_artifacts/index.html) |
//! | Host macro expansion into prover code | [`sensei-macros`](../zakura_sensei_macros/index.html) |
//!
//! Sensei uses `sensei-shared` at runtime and in its build script. The build
//! script calls `sensei-artifacts`; enabling `prover` also makes the compiler
//! run `sensei-macros`. Those host generators depend on `sensei-shared`, never
//! on Sensei: their output bytes and emitted Rust flow into the target build,
//! while the generator crates themselves stay on the host.
//!
//! The private `src/native/mod.rs` owns proof preparation, witness synthesis,
//! runtime kernels, and transcript stages. Its module docs are available with
//! `--document-private-items` when either proof role is enabled. Within that
//! runtime, `native::generated_expressions::{TREES, evaluate}` is the
//! `cfg(test)`-only tree-evaluation reference for optimized expression paths.
//! It shares the [`sensei_shared::programs`] recipes, so agreement establishes
//! evaluator consistency rather than an independent circuit specification.
//!
//! # Proof ownership
//!
//! These compile-only workflows enable both `prover` and `verifier` and take
//! caller-supplied Actions and randomness. Collect the public statements in
//! Action order before moving the Actions into `ProvingRequest`. The request
//! owns the witnesses; verification borrows the retained statements and proof
//! bytes for the duration of `verify_proofs`.
//!
//! One proving request produces one proof covering all of its Actions. Even
//! with several Actions, this is a singleton verification batch:
//!
//! ```no_run
//! # #[cfg(all(feature = "prover", feature = "verifier"))] {
//! use zakura_sensei::{
//!     Action, CircuitVersion, Error, ProvingRequest, RandomSource,
//!     VerificationRequest, create_proof, verify_proofs,
//! };
//!
//! fn prove_and_verify(actions: Vec<Action>, rng: &mut dyn RandomSource) -> Result<(), Error> {
//!     let statements: Vec<_> = actions.iter().map(|action| action.statement.clone()).collect();
//!     let proving = ProvingRequest::new(actions)?;
//!     let proof = create_proof(&proving, rng)?;
//!     let verification = VerificationRequest::new(
//!         CircuitVersion::PostNu6_3, &statements, &proof,
//!     )?;
//!     verify_proofs(&[verification], rng)
//! }
//! # }
//! ```
//!
//! To verify several proofs together, keep each proof's statements and bytes
//! alive, then borrow them into separate verification requests. Each inner
//! `Vec<Action>` below produces one proof; the outer vector determines the
//! number of proofs in the verification batch. The batch may contain proofs
//! with different Action counts. Batches with more than one proof consume
//! fresh verification randomness as described by [`RandomSource`].
//!
//! ```no_run
//! # #[cfg(all(feature = "prover", feature = "verifier"))] {
//! use zakura_sensei::{
//!     Action, CircuitVersion, Error, ProvingRequest, RandomSource,
//!     VerificationRequest, create_proof, verify_proofs, warm_up_prover,
//! };
//!
//! fn prove_and_verify_batch(
//!     action_groups: Vec<Vec<Action>>,
//!     rng: &mut dyn RandomSource,
//! ) -> Result<(), Error> {
//!     // Optional: prepare the prover before the first proof.
//!     warm_up_prover();
//!     let mut proofs = Vec::with_capacity(action_groups.len());
//!     for actions in action_groups {
//!         let statements: Vec<_> = actions.iter().map(|action| action.statement.clone()).collect();
//!         let proving = ProvingRequest::new(actions)?;
//!         let proof = create_proof(&proving, rng)?;
//!         proofs.push((statements, proof));
//!     }
//!     let requests = proofs.iter().map(|(statements, proof)| {
//!         VerificationRequest::new(CircuitVersion::PostNu6_3, statements, proof)
//!     }).collect::<Result<Vec<_>, _>>()?;
//!     verify_proofs(&requests, rng)
//! }
//! # }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
// Preserve the imported `chunks_exact` code, as in Udon. The pinned
// toolchain's Clippy predates this lint (introduced in 1.98).
#![allow(unknown_lints)]
#![allow(clippy::chunks_exact_to_as_chunks)]
extern crate alloc;
#[cfg(test)]
extern crate self as zakura_sensei;
#[cfg(all(test, not(feature = "std")))]
extern crate std;

// The `artifact_path!` macro: generated into `OUT_DIR` by `build.rs` from the
// `sensei-artifacts` registry, mapping each embedded artifact's identifier to its
// exact output path. Included ahead of the modules so the embedding
// declarations can use it; the registry alone spells stems, stored-form
// descriptors, and extensions.
include!(concat!(env!("OUT_DIR"), "/artifact-paths.rs"));

#[cfg(test)]
#[path = "../artifact_selection.rs"]
#[cfg(all(feature = "prover", feature = "verifier"))]
mod artifact_selection;
mod error;
#[cfg(any(feature = "prover", feature = "verifier"))]
mod native;
pub mod primitives;
#[cfg(any(feature = "prover", feature = "verifier"))]
mod public_input;
pub mod redpallas;
mod rng;
#[cfg(feature = "prover")]
mod selector_preparation;
#[cfg(feature = "prover")]
mod sizing;
mod static_data;
#[cfg(test)]
#[cfg(feature = "prover")]
mod test_codec;
#[cfg(any(feature = "prover", feature = "verifier"))]
mod tuning;
#[cfg(any(feature = "prover", feature = "verifier"))]
mod types;
#[cfg(test)]
#[path = "../tests/support/verification.rs"]
#[cfg(feature = "verifier")]
mod verification_corpus;

pub use error::Error;
#[cfg(any(feature = "prover", feature = "verifier"))]
pub use error::WorkersConfigError;
pub use primitives::{Fp, Fq, Fr, NonIdentityPallasPoint, PallasPoint, SpendValidatingKey};
pub use rng::{RandomSource, RandomnessError};
#[cfg(any(feature = "prover", feature = "verifier"))]
pub use types::{CircuitVersion, PublicStatement};
#[cfg(feature = "verifier")]
pub use types::{VerificationPlan, VerificationRequest};

#[cfg(feature = "prover")]
pub use types::{Action, PrivateWitness, ProvingRequest};

/// Creates an Ironwood Action proof using caller-supplied proving randomness.
///
/// The returned bytes can be passed to an Ironwood proof verifier. See
/// [`RandomSource`] for the security requirements on `randomness`.
///
/// After runtime preparation succeeds, the entire proving randomness schedule
/// is sampled before checking statement/witness relations or circuit
/// satisfaction. A source failure interrupts sampling; otherwise even an
/// invalid witness consumes the full schedule. Failures never restore the
/// caller's RNG state.
///
/// Randomness callbacks run on the calling thread before borrowing proof
/// scratch or entering the worker pool, so they may reenter proof or warmup
/// APIs. The source is borrowed and needs neither [`Send`] nor [`Sync`].
///
/// # Errors
///
/// [`ProvingRequest::new`] checks shape and public-point validity. Proving rejects
/// mismatched statement/witness relations with [`Error::InvalidStatement`] and
/// unsatisfied circuit constraints with [`Error::UnsatisfiedWitness`]. A source
/// error returns [`Error::RngFailure`]. On [`Error::RetryRandomness`], retry the
/// same request with fresh draws. [`Error::InternalInvariant`] reports an
/// internal failure, including a cached preparation error; see [`warm_up_prover`].
///
/// # Panics
///
/// Panics from the randomness callback propagate to the caller.
#[cfg(feature = "prover")]
pub fn create_proof(
    request: &ProvingRequest,
    randomness: &mut dyn RandomSource,
) -> Result<Vec<u8>, Error> {
    native::prove(request, randomness)
}

/// Warms the prover and then the verifier, combining [`warm_up_prover`] and
/// [`warm_up_verifier`] and reusing their shared SRS and execution resources.
#[cfg(all(feature = "prover", feature = "verifier"))]
pub fn warm_up() {
    warm_up_prover();
    warm_up_verifier();
}

/// Sets the worker budget for the process-wide pool shared by proving,
/// verification, and pooled RedPallas batch verification.
///
/// Call this before the first proving, verification, or warm-up API call in
/// the process: the budget is read once when the shared executor initializes
/// and is final afterwards. Precedence is Rayon-consistent: this explicit
/// budget wins; otherwise a positive integer `RAYON_NUM_THREADS` sizes the
/// pool (a zero or unparseable value is ignored), and the detected available
/// parallelism is the fallback. That fallback counts every logical CPU,
/// efficiency cores and SMT siblings included, and is not always the fastest
/// size, so measure the deployment's own workload before choosing a budget.
/// The pool is private to Sensei, so neither
/// this budget nor the environment variable selects or resizes Rayon's global
/// pool. Without the `multicore` feature execution is serial and an accepted
/// budget has no effect.
///
/// # Errors
///
/// Returns [`WorkersConfigError::Zero`] for a zero budget,
/// [`WorkersConfigError::AlreadyConfigured`] for a repeated call, and
/// [`WorkersConfigError::AlreadyInitialized`] once the shared executor
/// exists, in which case the running pool keeps its workers.
#[cfg(any(feature = "prover", feature = "verifier"))]
pub fn configure_workers(workers: usize) -> Result<(), WorkersConfigError> {
    native::executor::configure(workers)
}

/// Returns the shared pool's worker budget, initializing the shared workers —
/// but neither proof role's preparation — if needed.
///
/// After this returns, [`configure_workers`] reports
/// [`WorkersConfigError::AlreadyInitialized`]. This is the private pool's
/// size (one if the pool could not be built), not a limit on the process's
/// other threads. Without the `multicore` feature this is always one.
#[cfg(any(feature = "prover", feature = "verifier"))]
pub fn worker_budget() -> usize {
    native::executor::worker_budget()
}

/// Eagerly builds the shared SRS and per-process proving state that the first
/// [`create_proof`] call would otherwise build on demand.
///
/// Calling this is optional, idempotent, and safe concurrently with either
/// warmup or proof API. Proving is identical with or without it; subsequent
/// calls are nearly free. Shared SRS preparation is reused by verification,
/// including the complete coefficient/Lagrange banks and W/U tables.
/// Use it to pay the one-time initialization cost at a moment of the
/// caller's choosing.
///
/// Initializes shared execution resources and prover preparation without
/// consuming randomness, acquiring a proof workspace, or preparing verifier
/// keys. Request-sized scratch is allocated when proving needs it.
///
/// A returned initialization error is cached for the rest of the process.
/// This function does not report it; every subsequent [`create_proof`] call
/// returns that error without retrying preparation or consuming randomness.
/// This is also the behavior when the first proof call initializes the prover.
#[cfg(feature = "prover")]
pub fn warm_up_prover() {
    native::warm_up_prover();
}

/// Eagerly builds the shared SRS and per-process verification state that the
/// first nonempty [`verify_proofs`] call would otherwise build on demand.
///
/// Calling this is optional, idempotent, and safe concurrently with either
/// warmup or proof API. It consumes no randomness and does not initialize the
/// prover's circuit state. Shared coefficient/Lagrange banks and W/U tables are
/// prepared once and reused by proving; later calls are nearly free.
/// Verifier initialization retains successfully prepared state and has no
/// cached initialization-error result.
/// Shared execution resources and verifier keys are prepared here; per-batch
/// scratch is allocated only when verification needs it.
#[cfg(feature = "verifier")]
pub fn warm_up_verifier() {
    native::verifier::warm_up_verifier();
}

/// Optionally provisions bounded verification scratch for an expected batch of
/// `proofs` proofs totalling `actions` Actions, on top of [`warm_up_verifier`]
/// (which it performs first and which allocates no batch scratch itself), and
/// reports the shape's [`VerificationPlan`].
///
/// The first large batch otherwise pays for growing per-chunk equation scratch
/// and the final-MSM workspace. This prepares one batch's worth — one
/// final-MSM workspace and one equation entry per proof-folding chunk,
/// assuming the Actions are spread uniformly across the proofs — and offers
/// it to the idle scratch cache that `verify_proofs` leases from, bringing
/// the next such call near its steady-state latency. Provisioning is
/// capacity-only: a real batch still plans its own work and grows any
/// shortfall, including the one equation entry that merging a multi-chunk
/// batch grows to hold all of its transcript points. A shape exceeding the
/// cache's retention checks is provisioned and then dropped (the plan
/// reports `retention_eligible: false`). Calling again with a larger shape
/// grows the same idle entries; calling repeatedly does not prepare
/// additional workspaces, so only one batch's scratch is ever warmed.
/// `proofs` of zero only warms the verifier and reports a plan with zero
/// provisioned bytes. Consumes no randomness.
///
/// The plan is computed under the pool's final worker budget, so call
/// [`configure_workers`] first. Warm-up is an optimization for the first
/// call, not a reservation. Later calls can still allocate or grow scratch:
/// a call that finds no idle entry allocates one, and returns it to the
/// cache afterwards if it passes the retention checks and a slot is free.
/// Calls lease a workspace only for their final MSM, so more calls than
/// `workspace_slots` can overlap while sharing cached workspaces. The slot
/// count and `max_idle_bytes` describe the idle cache only; neither limits
/// concurrent verification nor bounds the process's peak memory.
#[cfg(feature = "verifier")]
pub fn warm_up_verifier_scratch(proofs: usize, actions: usize) -> VerificationPlan {
    native::verifier::warm_up_verifier_scratch(proofs, actions)
}

/// Verifies a batch of Action proofs for their selected circuit versions and
/// ordered statements. Versions may be mixed in a batch.
///
/// A singleton needs no randomness. An empty batch succeeds without initialization
/// or randomness. Larger batches require fresh cryptographically secure randomness
/// independent of the proofs; see [`RandomSource`]. Every proof is weighted once
/// in one combined verification equation. No Action-count limit is imposed.
///
/// Batch weights are sampled before verifier initialization, scratch acquisition,
/// or reading proof contents. A source failure or zero weight stops sampling
/// immediately. Callbacks run on the calling thread and may reenter proof or
/// warmup APIs. The source is borrowed and needs neither [`Send`] nor [`Sync`];
/// failures never restore its state.
///
/// # Errors
///
/// Returns [`Error::InvalidProof`] for malformed proof contents or a failed
/// verification equation, [`Error::RngFailure`] if the source fails, or
/// [`Error::InternalInvariant`] for an unexpected internal failure.
/// [`Error::RetryRandomness`] means a batch weight was zero: retry the same
/// batch with fresh weights, without regenerating its proofs. Request validation
/// can return [`Error::InvalidInput`] from [`VerificationRequest::new`].
///
/// # Panics
///
/// Panics from the randomness callback propagate to the caller.
#[cfg(feature = "verifier")]
pub fn verify_proofs(
    requests: &[VerificationRequest<'_>],
    randomness: &mut dyn RandomSource,
) -> Result<(), Error> {
    native::verifier::verify(requests, randomness)
}

#[cfg(test)]
#[cfg(all(feature = "prover", feature = "verifier"))]
mod benchmark_tests;

#[cfg(test)]
#[cfg(feature = "prover")]
mod resource_tests;
