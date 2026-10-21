//! Shared ownership and preparation policy for the pinned SRS.
//!
//! # Runtime ownership
//!
//! Both proof roles use this SRS and [`PoolExecutor`](super::executor::PoolExecutor),
//! but keep their circuit preparation and scratch separate. Paths in the table
//! are relative to `native`; `runtime` requires `prover`, and `verifier` requires
//! `verifier`.
//!
//! | Resource | Owner and lifetime |
//! | --- | --- |
//! | Shared SRS | [`SRS`] retains an `Arc<PreparedSrs>` for the process lifetime. The prover's target parameters and verifier runtime each hold a clone of that `Arc`, sharing the coefficient/Lagrange banks and W/U tables. |
//! | Workers | `executor::PoolExecutor::get` retains one executor for the process lifetime. Both runtimes borrow it; initializing the executor does not initialize either role. |
//! | Prover preparation | `runtime::RUNTIME` owns `PreparedProver`, including circuit and polynomial preparation selected by `tuning`. It does not prepare verifier keys. |
//! | Verifier preparation | `verifier::RUNTIME` owns the expanded verifying-key bank and version-index lists. It does not construct the prover's circuit state. Equal-width SRS and verifier banks share residue codebooks from [`Codebooks`]. |
//! | Scratch | Each active call owns its workspace and lends it mutably to computation. Prover scratch covers the proof pipeline; verifier retention applies only to the final combined MSM, not its worker-local equation scratch. |
//!
//! Each role obtains [`PreparedSrs::shared`] before entering the executor for
//! its own preparation. SRS initialization uses serial loaders and does not
//! wait for pool work or initialize either role. The SRS cell retains a
//! successful value; a panicking initializer leaves it uninitialized. Codebook
//! cells likewise initialize each requested width once on success.
//!
//! Warming one role initializes the shared owners and that role's preparation.
//! Warming the other reuses the shared owners; `crate::warm_up` (when both
//! features are enabled) warms the prover and then the verifier. Warmup consumes
//! no randomness and does not acquire or pre-size request workspaces. The
//! role-specific modules describe sampling order and link the public warmup
//! contracts, including their different initialization-error behavior.
//!
//! # Workspace retention
//!
//! [`tuning::WORKSPACE`](crate::tuning::WORKSPACE) currently selects `Discard`:
//! workspaces are created per call and released on return or unwinding, while
//! preparation and workers remain alive. Under `RetainOne`, each role instead
//! has one idle slot. A call takes that slot under a mutex, or creates a fresh
//! workspace if it is empty, then releases the lock before doing work. On
//! normal return, including an error, it restores its workspace only if the
//! slot is still empty; concurrent calls can therefore use independent scratch
//! without retaining a workspace per caller. Unwinding drops the active
//! workspace without returning it to the slot. Allocators may retain freed
//! pages under either policy.
//!
//! Both runtime caches recover a poisoned idle-slot mutex with `into_inner`.
//! This permits reuse of the slot; it does not turn a panicking computation
//! into a successful one. Worker coordination keeps its separate, strict lock
//! handling. No workspace lock is held during RNG callbacks or pool execution.

use alloc::{sync::Arc, vec::Vec};
use sensei_shared::{SrsPointsFile, commitment_tables::Codebook};
use std::sync::OnceLock;
use udon::{
    curve::{PreparedAffinePoint, Vesta},
    msm::Bases,
};

use super::commitment::{FixedGenerator, SrsGenerators};

crate::static_data::embed_struct! {
    /// Affine coefficient/Lagrange SRS, prefix sums, and auxiliary generators
    /// in Montgomery storage. The generator validates the points; embedding
    /// preserves their representation without checking curve membership.
    pub(in crate::native) static PREPARED_POINTS: SrsPointsFile =
        artifact_path!(srs_points);
}

/// One residue codebook per width, including banks prepared by the verifier.
#[derive(Default)]
struct Codebooks([OnceLock<Arc<Codebook>>; 3]);

impl Codebooks {
    fn get(&self, width: u8) -> Arc<Codebook> {
        assert!((5..=7).contains(&width), "supported alpha width");
        self.0[usize::from(width - 5)]
            .get_or_init(|| Arc::new(Codebook::new(width)))
            .clone()
    }
}

/// Immutable SRS caches shared by prepared provers and verifiers. Circuit
/// derivations and the verifier's fixed polynomial commitments live elsewhere.
pub(crate) struct PreparedSrs {
    pub(crate) coefficient_generators: Vec<PreparedAffinePoint<Vesta>>,
    pub(crate) lagrange_generators: Vec<PreparedAffinePoint<Vesta>>,
    coefficient_tables: SrsGenerators,
    lagrange_tables: SrsGenerators,
    pub(crate) blind_generator: FixedGenerator,
    pub(crate) ipa_generator: FixedGenerator,
    #[cfg(feature = "verifier")]
    codebooks: Codebooks,
}

static SRS: OnceLock<Arc<PreparedSrs>> = OnceLock::new();

impl PreparedSrs {
    /// Obtain shared preparation before entering either role's worker pool.
    /// Initialization uses the serial bank loaders and never waits on pool work.
    pub(crate) fn shared() -> Arc<Self> {
        SRS.get_or_init(|| Arc::new(Self::new())).clone()
    }

    #[cfg(all(test, feature = "prover"))]
    pub(crate) fn fresh_for_test() -> Arc<Self> {
        Arc::new(Self::new())
    }

    fn new() -> Self {
        let points = PREPARED_POINTS;
        let codebooks = Codebooks::default();
        let book = |section: usize| {
            let width = crate::tuning::COMMITMENT_TABLES.srs[section]
                .table
                .alpha_width();
            (width != 0).then(|| codebooks.get(width))
        };
        Self {
            coefficient_generators: points
                .coefficient_bases
                .iter()
                .map(PreparedAffinePoint::from_affine)
                .collect(),
            lagrange_generators: points
                .lagrange_bases
                .iter()
                .map(PreparedAffinePoint::from_affine)
                .collect(),
            coefficient_tables: SrsGenerators::new(&points.coefficient_bases, 0, book(0)),
            lagrange_tables: SrsGenerators::new(&points.lagrange_bases, 1, book(1)),
            blind_generator: FixedGenerator::configured(&points.blind_generator, 2),
            ipa_generator: FixedGenerator::configured(&points.ipa_generator, 3),
            #[cfg(feature = "verifier")]
            codebooks,
        }
    }

    pub(crate) fn coefficient_bases(&self) -> Bases<'_, Vesta> {
        self.coefficient_tables.bases(&self.coefficient_generators)
    }

    pub(crate) fn lagrange_bases(&self) -> Bases<'_, Vesta> {
        self.lagrange_tables.bases(&self.lagrange_generators)
    }

    #[cfg(feature = "verifier")]
    pub(crate) fn codebook(&self, width: u8) -> Arc<Codebook> {
        self.codebooks.get(width)
    }
}

#[cfg(all(test, feature = "prover", feature = "verifier"))]
mod tests;
