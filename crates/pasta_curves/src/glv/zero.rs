//! Fixed-base multiscalar **zero-checks**: is $\sum_i \[k_i\] P_i$ the
//! identity, for bases $P_i$ that are fixed across many checks?
//!
//! This is the verifier-shaped workload of recursive/IPA proof systems
//! (halo2's `MSM::eval` reduces to exactly this): a few thousand bases,
//! almost all fixed in advance (the SRS generators), scalars uniformly
//! random and public, and only the Boolean identity outcome needed. Fixed
//! bases change the optimization problem for the Eisenstein-orbit MSM
//! backend: instead of treating only the six units
//! $U_6 = \{\pm 1, \pm\omega, \pm\omega^2\}$ as free actions on a stored
//! point, a whole subgroup $G = \langle U_6, \alpha, \beta^k \rangle$ of
//! the residue units of $\mathbf{Z}[\omega]/2^c$ becomes free by
//! **preparation**: one transformed point $[\eta_a]P_i$ is precomputed per
//! $U_6$-coset of $G$ (the `prepared` submodule), every radix-$2^c$ digit
//! factors as $d = u\,\eta_a\,\delta_j$ through a static residue codebook
//! (the `codebook` submodule), and a window then needs one bucket per
//! $G$-orbit —
//! $B/2$ for the α-only subgroup instead of the $(B^2 + 2)/6$ unit orbits.
//! Fewer, cheaper buckets buy a much wider radix at the same reducer cost,
//! which cuts the dominant per-window point visits.
//!
//! The recoding is fixed-length with a small residual tail (the prepared
//! digit set is not a canonical number system); residuals are tiny and are
//! finished by the existing unprepared orbit machinery over the trivial
//! $\eta = 1$ layer. The evaluation is an exact MSM throughout — the
//! zero-check condition is exploited only in the API shape (no point is
//! returned, preparation is amortized across checks, and several
//! same-bases checks can be probabilistically batched with
//! [`combine_equations`]).
//!
//! # Soundness
//!
//! [`PreparedZeroMsm::is_zero_vartime`] is exact: it accepts iff the sum
//! is the identity. [`combine_equations`] is the standard random-linear-
//! combination reduction and is *probabilistic*: if any input equation is
//! false, the combined equation accepts with probability at most
//! $(m - 1)/r$ over the challenge, which must be sampled (or
//! Fiat–Shamir-derived) only after every equation is fixed.
//! [`PreparedZeroMsm::is_zero_batch_vartime`] enforces that ordering by
//! construction — it derives the challenge by hashing the prepared-bases
//! digest and every equation — while
//! [`PreparedZeroMsm::is_zero_batch_with_challenge_vartime`] leaves the
//! obligation with the caller's transcript.
//!
//! Prepared tables are built in-process from the caller's bases; there is
//! deliberately no deserialization path for them — a corrupted table would
//! make the check unsound. Should serialization ever be added, it must
//! bind the table to the curve, the preparation-time bases digest (already
//! computed and used by the batch challenge), the codebook mode and exact
//! variant lifts, and the implementation version — and even then,
//! rebuilding from the bases is the only trust story that needs no
//! separate soundness argument.
//!
//! Everything here is variable-time in scalars and points; all inputs must
//! be public.
//!
//! # Deferred by measurement
//!
//! Scalar-dependent CSE (reusing repeated transformed-point pairs across
//! windows) stays out on counting grounds for this workload: with
//! uniformly random scalars a base repeats its full digit label across a
//! window pair with probability $B^{-2}$, and an *addition* is saved only
//! when both members of a bucket-adjacent pair repeat and are paired
//! together again — expected well below 0.1% of the additions at any
//! supported width, less than the sort-and-match bookkeeping would cost.
//! Revisit only for workloads with structured or repeated scalars.
//!
//! Richer codebook geometry is measured out at the 2,048-base scale
//! (2026-08-24 sweep, this module's harness): every ≤ 96 MiB mode —
//! subgroup or [`CodebookMode::ExponentBox`] cover, 6 to 256 buckets,
//! 15 to 22 windows — lands within ~5% of β7^8, because bucket-count
//! and program-size trades no longer bind once integration is hybrid
//! batch-affine and the per-window fills dominate. In particular β8^32
//! (the subgroup with the box's variant count) trails β7^8 by 1–3% and
//! the c = 8 boxes tie it within noise without ever beating the
//! frontier, so the assessment's late-α factorization (β8^16's cosets
//! paired under an online degree-3 map: the same fill count as β8^32
//! plus a doubled coefficient program) and a late-β analogue are
//! counted out without implementation — an online endomorphism plane
//! can only reach frontier points the measured modes already bracket.
//! Compact 64-byte prepared points and base-major layouts stay out on
//! the phase-contention measurements (the reduce phase, not table
//! traffic, is ~3/4 of the runtime, and the small-table α6 mode inflates
//! under contention exactly as the 48 MiB modes do).
//!
//! Every ranking here (mode preferences, tail widths, the planner list)
//! was measured on one 32-core x86-64 host with the portable field
//! backend. Re-fit on other targets — in particular aarch64 with the
//! assembly backend, whose inversion/multiplication ratio differs — by
//! rerunning the two ignored harnesses in this module's tests
//! (`zero_check_timings`, `zero_check_phase_timings`) and the parent
//! module's `msm_backend_timings`.

use alloc::vec::Vec;

use ff::{Field, FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use group::CurveAffine as _;
#[cfg(feature = "multicore")]
use maybe_rayon::prelude::*;

use super::orbit;
use super::{
    AffinePoint, GlvParams, SignedMagnitude, checked_signed_magnitudes, current_num_threads,
    decompose, private, reduce_affine_buckets, reduce_affine_buckets_in_place,
};

mod codebook;
mod isogeny;
mod prepared;
/// The fixed subset-table baseline, kept test-gated: it exists to be
/// raced against the prepared codebook by the benchmark harness (an
/// in-crate ignored test), not to be shipped.
#[cfg(test)]
pub(crate) mod subset;

pub use codebook::CodebookMode;
use codebook::{Codebook, CoeffAdd, Recoded, unpack_code};
use prepared::{VariantTable, unit_coords};

/// Widths the tail MSM chooses between. Only the residuals ride the tail
/// (extra terms run as their own MSM), and residuals are tiny, so the
/// small orbit wedges win; width 5 is kept for headroom.
const TAIL_WIDTHS: [usize; 3] = [3, 4, 5];

/// Extra-term count from which the extras MSM goes through the planned
/// GLV backends ([`super::try_multiexp`]); below it, a per-term
/// multiplication loop is cheaper than any bucket method's fixed
/// per-window costs.
const EXTRAS_PLANNED_MIN: usize = super::MIN_GLV_MULTIEXP_TERMS;

/// Default per-table ceiling for the large allocations accounted by
/// [`PreparedZeroMsm::prepared_bytes`]. A 13 MiB ceiling selects the α7
/// mode for an Orchard-sized SRS; its two prover tables account for about
/// 24.8 MiB in total, plus small metadata and allocator overhead.
const DEFAULT_TABLE_FOOTPRINT_BUDGET: usize = 13 << 20;

/// A prepared fixed-base zero-check: reusable tables for testing
/// $\sum_i \[k_i\] P_i \stackrel{?}{=} \mathcal{O}$ against the bases given
/// at preparation, with per-check extra terms for the non-fixed remainder
/// of a verifier equation.
///
/// Preparation cost and memory scale with the mode's variant count (see
/// [`CodebookMode`]); [`Self::prepared_bytes`] reports the footprint. The
/// check itself is exact — see the module docs for the soundness story —
/// and variable-time in everything, so all inputs must be public.
pub struct PreparedZeroMsm<C: GlvParams> {
    codebook: Codebook,
    table: VariantTable<C>,
    /// Bases that participate: nonidentity and not merged into another
    /// base by the preparation-time relation scan.
    live: Vec<bool>,
    /// `(source, target, µ)`: base `source` satisfied
    /// $P_{\text{source}} = \[\mu\] P_{\text{target}}$, so its scalar folds
    /// into the target's before recoding. Sources are never targets.
    merges: Vec<(usize, usize, C::ScalarExt)>,
    /// The η = 1 layer in the unprepared backend's rotated form, for the
    /// tail MSM and the (unreachable-in-practice) naive fallback.
    tail_bases: Vec<orbit::RotatedBase<C::Base>>,
    /// Prebuilt tail wedge parameters for [`TAIL_WIDTHS`].
    tail_params: [orbit::OrbitParams; TAIL_WIDTHS.len()],
    /// Index into [`TAIL_WIDTHS`]/`tail_params` of the width chosen for the
    /// residual tail (a pure function of the live count and the codebook's
    /// tail bound, so it is fixed at preparation).
    tail_width: usize,
    /// BLAKE2b-256 over the prepared bases, mixed into
    /// [`Self::is_zero_batch_vartime`]'s derived challenge (and available
    /// to any future table-trust story).
    bases_digest: [u8; 32],
}

impl<C: GlvParams> core::fmt::Debug for PreparedZeroMsm<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PreparedZeroMsm")
            .field("mode", &self.codebook.mode())
            .field("terms", &self.live.len())
            .field("prepared_bytes", &self.prepared_bytes())
            .field("merged_bases", &self.merges.len())
            .finish()
    }
}

impl<C: GlvParams> PreparedZeroMsm<C> {
    /// Prepares zero-checks against `bases`, choosing the codebook mode by
    /// the operation model at the current thread-pool width, within a
    /// 13 MiB per-table accounted-footprint budget — or `None` when even
    /// the smallest mode would exceed that budget (from roughly $2^{13}$
    /// Pasta bases), declining rather than silently allocating past it. Use
    /// [`Self::prepare_with_mode`] to pin a mode explicitly and accept its
    /// memory regardless of the budget.
    pub fn prepare(bases: &[C::AffineExt]) -> Option<Self> {
        plan_mode::<C>(
            bases.len(),
            current_num_threads(),
            DEFAULT_TABLE_FOOTPRINT_BUDGET,
        )
        .map(|mode| Self::prepare_with_mode(bases, mode))
    }

    /// Prepares zero-checks against `bases` with an explicit codebook mode.
    ///
    /// Preparation scans the bases for exact $u$, $u\alpha$, $u\beta$
    /// relations ($u \in U_6$) and merges any related bases into one table
    /// slot (their scalars are folded per check); random independent bases
    /// essentially never match, but protocol-defined bases may contain
    /// deliberate duplicates or endomorphic images.
    pub fn prepare_with_mode(bases: &[C::AffineExt], mode: CodebookMode) -> Self {
        let num_threads = current_num_threads();
        let codebook = Codebook::new(mode);
        let mut live: Vec<bool> = bases
            .iter()
            .map(|base| !bool::from(base.is_identity()))
            .collect();
        let merges = scan_relations::<C>(bases, &mut live);
        let table = VariantTable::<C>::build(bases, &live, codebook.variants(), num_threads);

        // The η = 1 layer, re-expressed with the ζ²x rotation materialized
        // for the unprepared tail machinery.
        let unit_variant = codebook.unit_variant();
        let tail_bases: Vec<orbit::RotatedBase<C::Base>> = (0..bases.len())
            .map(|index| {
                let point = table.get(unit_variant, index);
                orbit::RotatedBase {
                    xs: [point.x, point.zeta_x, -point.x - point.zeta_x],
                    y: point.y,
                }
            })
            .collect();
        let tail_params = TAIL_WIDTHS.map(orbit::OrbitParams::new);
        let live_count = live.iter().filter(|&&l| l).count();
        let tail_width = tail_width_index(live_count, codebook.tail_bound());

        let mut digest = blake2b_simd::Params::new()
            .hash_length(32)
            .personal(b"zakura-zero-base")
            .to_state();
        digest.update(&(bases.len() as u64).to_le_bytes());
        for base in bases {
            let (x, y) = C::affine_xy(base);
            digest.update(x.to_repr().as_ref());
            digest.update(y.to_repr().as_ref());
        }
        let mut bases_digest = [0u8; 32];
        bases_digest.copy_from_slice(digest.finalize().as_bytes());

        PreparedZeroMsm {
            codebook,
            table,
            live,
            merges,
            tail_bases,
            tail_params,
            tail_width,
            bases_digest,
        }
    }

    /// The codebook mode this preparation uses.
    pub fn mode(&self) -> CodebookMode {
        self.codebook.mode()
    }

    /// The number of fixed bases this preparation covers.
    pub fn terms(&self) -> usize {
        self.live.len()
    }

    /// Accounted table footprint in bytes: the variant table, tail bases,
    /// residue entries, and codebook lifts. This intentionally excludes
    /// small live/merge vectors, the coefficient program, object and
    /// allocator overhead, and transient setup scratch; it is an estimate
    /// of the dominant retained payload rather than a heap or RSS total.
    pub fn prepared_bytes(&self) -> usize {
        self.table.bytes()
            + self.tail_bases.len() * core::mem::size_of::<orbit::RotatedBase<C::Base>>()
            + self.codebook.table_bytes()
    }

    /// Whether $\sum_i \[k_i\] P_i$ is the identity, for the prepared bases.
    ///
    /// # Panics
    ///
    /// Panics if `scalars.len()` differs from the prepared base count.
    pub fn is_zero_vartime(&self, scalars: &[C::ScalarExt]) -> bool {
        self.is_zero_with_terms_vartime(scalars, &[])
    }

    /// Whether $\sum_i \[k_i\] P_i + \sum_j \[s_j\] Q_j$ is the identity: the
    /// prepared bases with their scalars, plus per-check `extra`
    /// (scalar, point) terms for the non-fixed part of a verifier equation
    /// (e.g. the proof's own commitments). The extras run as their own
    /// multiscalar multiplication — per-term below
    /// [`EXTRAS_PLANNED_MIN`] terms, the planned GLV backends above it —
    /// concurrent with the prepared windows under parallelism, so they
    /// never widen the fixed residual tail.
    ///
    /// # Panics
    ///
    /// Panics if `scalars.len()` differs from the prepared base count.
    pub fn is_zero_with_terms_vartime(
        &self,
        scalars: &[C::ScalarExt],
        extra: &[(C::ScalarExt, C::AffineExt)],
    ) -> bool {
        bool::from(
            self.multiexp_with_terms_vartime(scalars, extra)
                .is_identity(),
        )
    }

    /// The exact multiscalar multiplication
    /// $\sum_i \[k_i\] P_i + \sum_j \[s_j\] Q_j$ over the prepared bases
    /// and per-call `extra` terms — the same evaluation the zero-checks run,
    /// with the group element returned instead of compared against the
    /// identity. This is the prover-shaped entry point: a polynomial
    /// commitment over a fixed SRS is exactly this call with the
    /// coefficients as the fixed scalars (and, in halo2's layout, the
    /// blinding factor riding one of the trailing fixed bases).
    ///
    /// Variable-time in everything; all inputs must be public or the timing
    /// leak accepted by the caller (halo2's prover already evaluates its
    /// commitments through a variable-time multiexp).
    ///
    /// # Panics
    ///
    /// Panics if `scalars.len()` differs from the prepared base count.
    pub fn multiexp_with_terms_vartime(
        &self,
        scalars: &[C::ScalarExt],
        extra: &[(C::ScalarExt, C::AffineExt)],
    ) -> C {
        assert_eq!(
            scalars.len(),
            self.live.len(),
            "one scalar per prepared base"
        );
        let num_threads = current_num_threads();

        // Fold merged bases' scalars into their targets (rare; scan-found).
        let folded: Vec<C::ScalarExt>;
        let scalars = if self.merges.is_empty() {
            scalars
        } else {
            let mut owned = scalars.to_vec();
            for &(source, target, mu) in &self.merges {
                let contribution = owned[source] * mu;
                owned[target] += contribution;
                owned[source] = C::ScalarExt::ZERO;
            }
            folded = owned;
            &folded
        };

        // Dead rows (identity bases, merge sources) contribute nothing;
        // force their recoding rows and residuals to zero. A decomposition
        // half out of bound is unreachable (`decompose` guarantees the
        // strict 2^127 bound), but rather than trust that with a panic the
        // whole check degrades to the exact naive evaluation, matching
        // `try_multiexp`'s posture toward the same guard.
        let decompose_checked = |(index, k): (usize, &C::ScalarExt)| {
            if !self.live[index] {
                let zero = SignedMagnitude {
                    negative: false,
                    magnitude: 0,
                };
                return Some((zero, zero));
            }
            checked_signed_magnitudes(decompose::<C>(k))
        };
        #[cfg(not(feature = "multicore"))]
        let components: Option<Vec<_>> =
            scalars.iter().enumerate().map(decompose_checked).collect();
        #[cfg(feature = "multicore")]
        let components: Option<Vec<_>> = if num_threads > 1 {
            scalars
                .par_iter()
                .enumerate()
                .map(decompose_checked)
                .collect()
        } else {
            scalars.iter().enumerate().map(decompose_checked).collect()
        };
        let Some(components) = components else {
            return self.naive_multiexp(scalars, extra);
        };

        let recoded = codebook::recode(&self.codebook, &components, num_threads);

        // Extras with zero scalars or identity points contribute nothing.
        let extras: Vec<(C::ScalarExt, C::AffineExt)> = extra
            .iter()
            .filter(|(scalar, point)| {
                !bool::from(point.is_identity()) && !bool::from(scalar.is_zero())
            })
            .copied()
            .collect();
        match self.evaluate(&recoded, &extras, num_threads) {
            Some(sum) => sum,
            // Unreachable for valid curve points (the batched-affine
            // reduction's inversions cannot actually hit zero), but never
            // trust that with the result's correctness: fall back to a
            // naive exact evaluation.
            None => self.naive_multiexp(scalars, extra),
        }
    }

    /// Checks several equations over the prepared bases at once through a
    /// random linear combination, deriving the combining challenge itself:
    /// $\rho$ = BLAKE2b(prepared-bases digest, every equation's scalars),
    /// mapped uniformly into the scalar field. Because $\rho$ is a hash of
    /// the complete equation set, it cannot be known before the equations
    /// are fixed, so the $(m - 1)/r$ false-accept bound of
    /// [`combine_equations`] holds by construction (in the random-oracle
    /// model; defeating it means grinding ~$r/(m-1)$ hashes).
    ///
    /// Protocols that already own a transcript should instead squeeze
    /// their own challenge — *after absorbing every equation* — and call
    /// [`Self::is_zero_batch_with_challenge_vartime`].
    pub fn is_zero_batch_vartime(&self, equations: &[&[C::ScalarExt]]) -> bool
    where
        C::ScalarExt: ff::FromUniformBytes<64>,
    {
        if equations.is_empty() {
            return true;
        }
        let mut state = blake2b_simd::Params::new()
            .hash_length(64)
            .personal(b"zakura-zero-rho\0")
            .to_state();
        state.update(&self.bases_digest);
        state.update(&(equations.len() as u64).to_le_bytes());
        for equation in equations {
            for scalar in equation.iter() {
                state.update(scalar.to_repr().as_ref());
            }
        }
        let mut wide = [0u8; 64];
        wide.copy_from_slice(state.finalize().as_bytes());
        let challenge = C::ScalarExt::from_uniform_bytes(&wide);
        self.is_zero_batch_with_challenge_vartime(equations, challenge)
    }

    /// [`Self::is_zero_batch_vartime`] with a caller-supplied challenge.
    ///
    /// # Soundness
    ///
    /// The $(m - 1)/r$ bound holds **only** if `challenge` was sampled or
    /// Fiat–Shamir-derived *after every equation was fixed* and is never
    /// reused across batches whose equations it did not absorb. A
    /// challenge known in advance lets a prover construct false equations
    /// that cancel in the combination. Prefer the self-deriving variant
    /// unless a protocol transcript owns the challenge.
    pub fn is_zero_batch_with_challenge_vartime(
        &self,
        equations: &[&[C::ScalarExt]],
        challenge: C::ScalarExt,
    ) -> bool {
        if equations.is_empty() {
            return true;
        }
        self.is_zero_vartime(&combine_equations::<C>(equations, challenge))
    }

    /// $\sum_w B^w C_w + B^L T + E$: the main prepared windows, the shifted
    /// residual tail, and the extra terms' own MSM.
    fn evaluate(
        &self,
        recoded: &Recoded,
        extras: &[(C::ScalarExt, C::AffineExt)],
        num_threads: usize,
    ) -> Option<C> {
        let window_bits = self.codebook.window_bits();
        let main_windows = self.codebook.main_windows();
        let active = recoded.active_windows;

        #[cfg(not(feature = "multicore"))]
        let _ = num_threads;
        #[cfg(feature = "multicore")]
        if num_threads > 1 {
            // The main windows run through the shared paired-window
            // schedule ([`super::paired_windows_sum`]). The residual tail
            // and the extras MSM run concurrently with them: with many
            // extra terms (batch verification accumulates thousands of
            // per-proof commitments) the extras are a substantial MSM of
            // their own, and running the phases back to back would add
            // their latency instead of overlapping it.
            let (extras_part, (windows_part, tail)) = maybe_rayon::join(
                || self.extras_sum(extras),
                || {
                    maybe_rayon::join(
                        || {
                            super::paired_windows_sum::<C>(active, window_bits, |window| {
                                self.window_sum(recoded, window)
                            })
                        },
                        || self.tail_sum(&recoded.residuals, num_threads),
                    )
                },
            );
            let windows_part = windows_part?;
            let mut tail = tail?;
            if !bool::from(tail.is_identity()) {
                for _ in 0..window_bits * main_windows {
                    tail = tail.double();
                }
            }
            return Some(windows_part + tail + extras_part?);
        }

        let mut acc = self.tail_sum(&recoded.residuals, num_threads)?;
        if !bool::from(acc.is_identity()) {
            for _ in 0..window_bits * (main_windows - active) {
                acc = acc.double();
            }
        }
        for window in (0..active).rev() {
            for _ in 0..window_bits {
                acc = acc.double();
            }
            acc += self.window_sum(recoded, window)?;
        }
        Some(acc + self.extras_sum(extras)?)
    }

    /// One main window: stage the unit-rotated prepared points by bucket,
    /// reduce each bucket batch-affine, and run the static coefficient
    /// program over the bucket sums.
    fn window_sum(&self, recoded: &Recoded, window: usize) -> Option<C> {
        let (points, offsets) = self.stage_window(recoded, window);
        let buckets = reduce_affine_buckets_in_place(points, offsets).or_else(|| {
            let (points, offsets) = self.stage_window(recoded, window);
            reduce_affine_buckets(points, offsets)
        })?;
        integrate_coefficients::<C>(self.codebook.program(), &buckets)
    }

    /// Places one window's nonzero digits into per-bucket point ranges,
    /// fetching each digit's prepared point and applying its unit. The
    /// bucket histogram was produced during recoding and the codes are
    /// window-major, so this is a single contiguous pass.
    fn stage_window(
        &self,
        recoded: &Recoded,
        window: usize,
    ) -> (Vec<AffinePoint<C::Base>>, Vec<usize>) {
        let terms = recoded.terms;
        let bucket_count = self.codebook.bucket_count();
        let counts = &recoded.counts[window * bucket_count..][..bucket_count];
        let codes = &recoded.codes[window * terms..][..terms];

        let mut offsets = Vec::with_capacity(bucket_count + 1);
        offsets.push(0usize);
        for &count in counts {
            offsets.push(offsets.last().copied().unwrap() + count as usize);
        }

        let mut positions = offsets[..bucket_count].to_vec();
        let mut points = alloc::vec![
            AffinePoint {
                x: C::Base::ZERO,
                y: C::Base::ZERO,
            };
            *offsets.last().unwrap()
        ];
        for (base, &code) in codes.iter().enumerate() {
            if code == 0 {
                continue;
            }
            let (bucket, variant, unit) = unpack_code(code);
            let (x, y) = unit_coords(self.table.get(variant, base), unit);
            let position = positions[bucket];
            points[position] = AffinePoint { x, y };
            positions[bucket] = position + 1;
        }

        (points, offsets)
    }

    /// The tail MSM $T = \sum_i \[\tau_i\] P_i$ over the (tiny) residuals,
    /// via the unprepared orbit machinery at the width fixed at
    /// preparation.
    fn tail_sum(
        &self,
        residuals: &[(SignedMagnitude, SignedMagnitude)],
        num_threads: usize,
    ) -> Option<C> {
        let params = &self.tail_params[self.tail_width];
        tail_multiexp::<C>(params, residuals, &self.tail_bases, num_threads)
    }

    /// $E = \sum_j \[s_j\] Q_j$ over the per-check extra terms (already
    /// filtered of zero scalars and identity points), as an independent
    /// MSM: the planned GLV backends from [`EXTRAS_PLANNED_MIN`] terms up,
    /// otherwise the Signed-Booth backend at a width matched to the small
    /// count. Riding the extras in the residual tail — the previous
    /// design — forced its tiny wedge from the residuals' 3–4 windows to
    /// a full-width sweep over every row, which measured ~+1 ms per 48
    /// extras; a dedicated small MSM prices only the extras, and large
    /// extra sets (batch verification accumulates thousands) get a real
    /// planner instead of a tail width.
    fn extras_sum(&self, extras: &[(C::ScalarExt, C::AffineExt)]) -> Option<C> {
        if extras.is_empty() {
            return Some(C::identity());
        }
        let scalars: Vec<C::ScalarExt> = extras.iter().map(|(s, _)| *s).collect();
        let points: Vec<C::AffineExt> = extras.iter().map(|(_, q)| *q).collect();
        if extras.len() >= EXTRAS_PLANNED_MIN
            && let Some(sum) = super::try_multiexp::<C>(&scalars, &points)
        {
            return Some(sum);
        }
        // The planner declining (or an arithmetic guard failing) is
        // unreachable for full-width verifier extras at these counts,
        // but the paths below stay exact regardless.
        // Small counts: Signed-Booth at a width from the bucket/visit
        // balance (per-window bucket work dominates until the visit count
        // catches up), run serially — this whole job is sub-millisecond
        // and already overlaps the main windows inside its own join arm,
        // so splitting its 30–40 tiny window tasks into a saturated pool
        // costs more in scheduling than it recovers (measured −25% on the
        // 32-worker single-bundle Ironwood cell). The constant-time
        // per-term ladder is the exact fallback of last resort.
        if let Some(components) = scalars
            .iter()
            .map(decompose::<C>)
            .map(checked_signed_magnitudes)
            .collect::<Option<Vec<_>>>()
        {
            let window_bits = match extras.len() {
                ..=24 => 3,
                25..=80 => 4,
                81..=192 => 5,
                _ => 6,
            };
            let booth_bases = super::multiexp_bases::<C>(&points);
            if let Some(sum) = super::multiexp::<C>(&components, &booth_bases, window_bits, 1) {
                return Some(sum);
            }
        }
        let mut acc = C::identity();
        for (scalar, point) in extras {
            acc += C::from(*point) * scalar;
        }
        Some(acc)
    }

    /// Exact fallback evaluation (never taken in practice; see the caller).
    fn naive_multiexp(
        &self,
        scalars: &[C::ScalarExt],
        extra: &[(C::ScalarExt, C::AffineExt)],
    ) -> C {
        let mut acc = C::identity();
        for (index, scalar) in scalars.iter().enumerate() {
            if !self.live[index] || bool::from(scalar.is_zero()) {
                continue;
            }
            let base = &self.tail_bases[index];
            let point = C::from(C::affine_unchecked(
                base.xs[0],
                base.y,
                private::CrateToken(()),
            ));
            acc += point * scalar;
        }
        for (scalar, point) in extra {
            acc += C::from(*point) * scalar;
        }
        acc
    }
}

/// The object-safe surface [`crate::arithmetic::CurveExt::try_prepare_zero_check`]
/// hands to generic callers (halo2's verifier reaches the prepared check
/// through this, with the SRS as the fixed bases and the proof's own
/// commitments as the extra terms).
impl<C: GlvParams> crate::arithmetic::PreparedZeroCheck<C> for PreparedZeroMsm<C> {
    fn terms(&self) -> usize {
        PreparedZeroMsm::terms(self)
    }

    fn is_zero_with_terms_vartime(
        &self,
        scalars: &[C::ScalarExt],
        extra: &[(C::ScalarExt, C::AffineExt)],
    ) -> bool {
        PreparedZeroMsm::is_zero_with_terms_vartime(self, scalars, extra)
    }

    fn multiexp_with_terms_vartime(
        &self,
        scalars: &[C::ScalarExt],
        extra: &[(C::ScalarExt, C::AffineExt)],
    ) -> C {
        PreparedZeroMsm::multiexp_with_terms_vartime(self, scalars, extra)
    }
}

/// Picks the residual tail's orbit width: residuals are `tail_bound`-sized,
/// so only their few low windows run, and the wedge reducer runs once per
/// window any row reaches. Same cost units as the orbit backend's model.
fn tail_width_index(live: usize, tail_bound: i64) -> usize {
    let bound_bits = 64 - tail_bound.unsigned_abs().leading_zeros() as usize;
    let mut best = (usize::MAX, 0);
    for (index, &width) in TAIL_WIDTHS.iter().enumerate() {
        let residual_windows = bound_bits.div_ceil(width) + 1;
        let buckets = ((1usize << (2 * width)) + 2) / 6;
        let visits = live * residual_windows * 27 / 32;
        let units = visits + 3 * (buckets - 1) * residual_windows;
        if units < best.0 {
            best = (units, index);
        }
    }
    best.1
}

/// The unprepared orbit MSM over already-rotated bases. The caller
/// guarantees rows of dead bases carry zero components (this recodes rows
/// unconditionally).
fn tail_multiexp<C: GlvParams>(
    params: &orbit::OrbitParams,
    components: &[(SignedMagnitude, SignedMagnitude)],
    rotated: &[orbit::RotatedBase<C::Base>],
    num_threads: usize,
) -> Option<C> {
    debug_assert_eq!(components.len(), rotated.len());
    let width = params.window_stride();
    let mut digits = alloc::vec![0u16; components.len() * width];

    #[cfg(not(feature = "multicore"))]
    let _ = num_threads;
    #[cfg(feature = "multicore")]
    if num_threads > 1 {
        let active = digits
            .par_chunks_mut(width)
            .zip(components.par_iter())
            .map(|(row, &(first, second))| orbit::recode_row(params, first, second, row))
            .max()
            .unwrap_or(0);
        return super::paired_windows_sum::<C>(active, params.width(), |window| {
            orbit::windows_sum::<C>(params, &digits, rotated, window..window + 1)
        });
    }

    let mut active = 0;
    for (row, &(first, second)) in digits.chunks_exact_mut(width).zip(components) {
        active = active.max(orbit::recode_row(params, first, second, row));
    }
    orbit::windows_sum::<C>(params, &digits, rotated, 0..active)
}

/// Scans the fixed bases for exact relations $P_j = \[\mu\] P_i$ with
/// $\mu \in U_6 \cdot \{1, \alpha, \beta\}$ (as scalars:
/// $\pm\lambda^e \cdot \{1, 1 - \lambda, 2 - \lambda\}$). Every found
/// relation kills the later base (`live[j] = false`) and records the fold;
/// sources are never targets, so folds apply in any order.
fn scan_relations<C: GlvParams>(
    bases: &[C::AffineExt],
    live: &mut [bool],
) -> Vec<(usize, usize, C::ScalarExt)> {
    use alloc::collections::BTreeMap;

    let mut by_x: BTreeMap<Vec<u8>, Vec<(usize, C::Base)>> = BTreeMap::new();
    for (index, base) in bases.iter().enumerate() {
        if live[index] {
            let (x, y) = C::affine_xy(base);
            by_x.entry(x.to_repr().as_ref().to_vec())
                .or_default()
                .push((index, y));
        }
    }
    // No possible relations without an x-collision somewhere: x-coordinates
    // are preserved only up to the ζ rotations and the maps, but any
    // relation forces the *image's* x to collide with a stored base's x.
    // (The map is cheap; the α/β images are only computed when scanning.)

    let live_indices: Vec<usize> = (0..bases.len()).filter(|&i| live[i]).collect();
    let live_affine: Vec<C::AffineExt> = live_indices.iter().map(|&i| bases[i]).collect();
    let alphas = isogeny::alpha_affine_batch::<C>(&live_affine);
    let betas = isogeny::beta_affine_batch_from_alphas::<C>(&live_affine, &alphas);

    let zeta = <C::Base as WithSmallOrderMulGroup<3>>::ZETA;
    let lambda = <C::ScalarExt as WithSmallOrderMulGroup<3>>::ZETA;
    let mut merges: Vec<(usize, usize, C::ScalarExt)> = Vec::new();
    let mut merged = alloc::vec![false; bases.len()];

    for (position, &i) in live_indices.iter().enumerate() {
        if merged[i] {
            continue;
        }
        let mut images: Vec<(C::Base, C::Base, C::ScalarExt)> = Vec::with_capacity(18);
        let mut push_images = |point: &C::AffineExt, eigen: C::ScalarExt| {
            let (x, y) = C::affine_xy(point);
            let zx = x * zeta;
            let xs = [x, zx, -x - zx];
            let mut rotation = C::ScalarExt::ONE;
            for &ux in xs.iter() {
                images.push((ux, y, eigen * rotation));
                images.push((ux, -y, -eigen * rotation));
                rotation *= lambda;
            }
        };
        push_images(&bases[i], C::ScalarExt::ONE);
        push_images(&alphas[position], C::ScalarExt::ONE - lambda);
        push_images(&betas[position], C::ScalarExt::from(2) - lambda);

        for (x, y, mu) in images {
            if let Some(candidates) = by_x.get(x.to_repr().as_ref()) {
                for &(j, candidate_y) in candidates {
                    if j > i && !merged[j] && candidate_y == y {
                        // P_j = [µ] P_i, so [k_j]P_j = [k_j µ] P_i.
                        merged[j] = true;
                        live[j] = false;
                        merges.push((j, i, mu));
                    }
                }
            }
        }
    }
    merges
}

/// Folds `m` same-bases equations into one with the challenge $\rho$:
/// $K_i = \sum_j \rho^j k_{j,i}$, so checking $\sum_i \[K_i\]P_i = \mathcal O$
/// checks all $\sum_i \[k_{j,i}\]P_i = \mathcal O$ at once.
///
/// # Soundness
///
/// If at least one input equation is false, the combined equation still
/// accepts with probability at most $(m - 1)/r$ over a uniform challenge.
/// The challenge **must** be sampled or Fiat–Shamir-derived only after all
/// equations are fixed; a challenge known in advance voids the bound.
///
/// # Panics
///
/// Panics if the equations have differing lengths.
pub fn combine_equations<C: GlvParams>(
    equations: &[&[C::ScalarExt]],
    challenge: C::ScalarExt,
) -> Vec<C::ScalarExt> {
    let Some(first) = equations.first() else {
        return Vec::new();
    };
    let mut combined = first.to_vec();
    let mut power = C::ScalarExt::ONE;
    for equation in &equations[1..] {
        assert_eq!(
            equation.len(),
            combined.len(),
            "equations over one base set"
        );
        power *= challenge;
        for (accumulated, k) in combined.iter_mut().zip(equation.iter()) {
            *accumulated += power * k;
        }
    }
    combined
}

/// Operand count from which [`integrate_coefficients`] sums each binary
/// position through the batched-affine tree. Below it, the tree's per-level
/// batch inversions dominate (they amortize over too few additions) and the
/// straight-line projective form is cheaper — measured on the phase
/// harness: β7^8's 57-addition program lost ~0.1 ms/check batched, α7's
/// ~130-addition program gained ~0.1 ms.
const BATCH_INTEGRATE_MIN_ADDS: usize = 112;

/// Runs the static coefficient program over one window's bucket sums:
/// $\sum_j [\delta_j] Q_j$ with unit digits applied per operand as an
/// x-rotation (one multiplication for $\zeta x$, plus an addition for
/// $\zeta^2 x = -x - \zeta x$) and a y-negation; empty buckets skipped.
///
/// The program is position-major. Large programs (wide modes have hundreds
/// of operands) sum each position's operands through the shared
/// batched-affine reduction tree — the same reducer and per-addition cost
/// as the bucket fills — and Horner-fold $\sum_t 2^t S_t$ over the
/// ~⌈log₂ B⌉ position sums; small programs run straight-line, one
/// projective mixed addition per operand, which beats the tree until its
/// batch inversions amortize (see [`BATCH_INTEGRATE_MIN_ADDS`]).
fn integrate_coefficients<C: GlvParams>(
    program: &[Vec<CoeffAdd>],
    buckets: &[Option<AffinePoint<C::Base>>],
) -> Option<C> {
    let zeta = <C::Base as WithSmallOrderMulGroup<3>>::ZETA;
    let additions: usize = program.iter().map(Vec::len).sum();

    if additions < BATCH_INTEGRATE_MIN_ADDS {
        let mut acc = C::identity();
        for ops in program.iter().rev() {
            acc = acc.double();
            for op in ops {
                if let Some(point) = &buckets[usize::from(op.bucket)] {
                    let x = match op.rotation {
                        0 => point.x,
                        1 => point.x * zeta,
                        _ => -point.x - point.x * zeta,
                    };
                    let y = if op.negate { -point.y } else { point.y };
                    acc += C::affine_unchecked(x, y, private::CrateToken(()));
                }
            }
        }
        return Some(acc);
    }

    // ζx once per nonempty bucket; repeated rotated references share it.
    let zeta_xs: Vec<C::Base> = buckets
        .iter()
        .map(|bucket| bucket.as_ref().map_or(C::Base::ZERO, |p| p.x * zeta))
        .collect();

    let mut points = Vec::with_capacity(additions);
    let mut offsets = Vec::with_capacity(program.len() + 1);
    offsets.push(0usize);
    for ops in program {
        for op in ops {
            if let Some(point) = &buckets[usize::from(op.bucket)] {
                let x = match op.rotation {
                    0 => point.x,
                    1 => zeta_xs[usize::from(op.bucket)],
                    _ => -point.x - zeta_xs[usize::from(op.bucket)],
                };
                let y = if op.negate { -point.y } else { point.y };
                points.push(AffinePoint { x, y });
            }
        }
        offsets.push(points.len());
    }

    let position_sums = reduce_affine_buckets(points, offsets)?;
    let mut acc = C::identity();
    for sum in position_sums.iter().rev() {
        acc = acc.double();
        if let Some(point) = sum {
            acc += C::affine_unchecked(point.x, point.y, private::CrateToken(()));
        }
    }
    Some(acc)
}

/// Chooses a default codebook mode: an ordered preference list within
/// `table_footprint_budget` bytes as reported by
/// [`PreparedZeroMsm::prepared_bytes`], fit to the `zero_check_timings`
/// measurements on 32-core x86-64 (portable field backend, Vesta,
/// 2026-08-24; medians of interleaved rounds against the unprepared
/// `try_multiexp` control on true zero relations):
///
/// - `β7^8` (⟨U₆, α, β⁸⟩ at B = 128; 256 variants, 32 buckets, ~24 KiB of
///   table per base) was the best or within noise of the best serial *and*
///   parallel mode at 1,024 and 2,048 terms — +56..+60% over the control
///   serially and +47..+87% at 2–16 workers — and still +55% at 8,192
///   terms on 32 workers.
/// - `β6^4` (B = 64; 128 variants, 16 buckets, half the memory) matches it
///   at 8+ workers and was the best 32-worker mode at 2,048 terms; wide
///   pools prefer its 22 windows over β7^8's 19.
/// - The α-only widths trail the β modes by 5–15% at these sizes (their
///   larger coefficient alphabets cost more integration than the extra
///   variants cost in cache) but need 2–4× less memory: `α7` gave +47%
///   serial at 2,048 terms in 12 MiB, `α6` +36% in 6 MiB.
/// - At 8,192 terms the wider radixes win serially (`β8^16`/`α8`/`α9`,
///   +42..+51%), but every measured mode exceeds the current 13 MiB default.
///   Default preparation therefore declines at that size; explicit
///   [`PreparedZeroMsm::prepare_with_mode`] remains available to callers that
///   accept the larger footprint.
/// - The subset-table baseline — given the same batched-affine tree
///   reduction as everything else — beats the unprepared control from
///   t = 12 up but still trails the codebook by 18–31% at comparable or
///   larger memory (t = 12, 43 MiB: 11.7 ms and t = 14, 147 MiB: 10.3 ms,
///   against β7^8's 8.9 ms in 48 MiB, serial at 2,048 terms), with no
///   parallel path; it is not a candidate.
/// - In the 2026-08-24 48 MiB sweep, wider c = 8 codebooks — `β8^32` and
///   the 16×16 exponent box (256 variants against 96/47 buckets) — measured
///   0–3% behind `β7^8` at 2,048 terms serially and inside the parallel
///   noise band, never ahead of it. They therefore are not candidates under
///   the tighter default; see the module docs for why richer geometry no
///   longer pays.
///
/// Returns `None` when even the smallest candidate would exceed
/// `table_footprint_budget` (large base sets — at the default budget, from
/// roughly 2^13 Pasta bases up), so the caller declines to prepare instead of
/// silently allocating past the budget.
///
/// Benchmarks can pin any mode via [`PreparedZeroMsm::prepare_with_mode`].
#[derive(Clone, Copy)]
struct ModeCandidate {
    mode: CodebookMode,
    variants: usize,
    buckets: usize,
}

const BETA_SEVEN_POWER_EIGHT: ModeCandidate = ModeCandidate {
    mode: CodebookMode::Subgroup {
        window_bits: 7,
        beta_power: Some(8),
    },
    variants: 256,
    buckets: 32,
};
const BETA_SIX_POWER_FOUR: ModeCandidate = ModeCandidate {
    mode: CodebookMode::Subgroup {
        window_bits: 6,
        beta_power: Some(4),
    },
    variants: 128,
    buckets: 16,
};
const ALPHA_SEVEN: ModeCandidate = ModeCandidate {
    mode: CodebookMode::alpha_only(7),
    variants: 64,
    buckets: 64,
};
const ALPHA_SIX: ModeCandidate = ModeCandidate {
    mode: CodebookMode::alpha_only(6),
    variants: 32,
    buckets: 32,
};
const ALPHA_FIVE: ModeCandidate = ModeCandidate {
    mode: CodebookMode::alpha_only(5),
    variants: 16,
    buckets: 16,
};

const DEFAULT_MODE_CANDIDATES: [ModeCandidate; 5] = [
    BETA_SEVEN_POWER_EIGHT,
    BETA_SIX_POWER_FOUR,
    ALPHA_SEVEN,
    ALPHA_SIX,
    ALPHA_FIVE,
];
const WIDE_MODE_CANDIDATES: [ModeCandidate; 5] = [
    BETA_SIX_POWER_FOUR,
    BETA_SEVEN_POWER_EIGHT,
    ALPHA_SEVEN,
    ALPHA_SIX,
    ALPHA_FIVE,
];

fn plan_mode<C: GlvParams>(
    terms: usize,
    num_threads: usize,
    table_footprint_budget: usize,
) -> Option<CodebookMode> {
    // These counts come from the derived §6.3 handoff table (re-asserted
    // by `subgroup_table_matches_handoff`), not a closed formula.
    let candidates = if num_threads >= 16 {
        // Wide worker pools: more windows beat fewer visits (and β6⁴
        // needs half β7⁸'s memory, so the reordering never loses a fit).
        &WIDE_MODE_CANDIDATES
    } else {
        &DEFAULT_MODE_CANDIDATES
    };
    candidates
        .iter()
        .find(|candidate| {
            estimated_table_footprint::<C>(
                terms,
                candidate.mode.window_bits(),
                candidate.variants,
                candidate.buckets,
            )
            .is_some_and(|bytes| bytes <= table_footprint_budget)
        })
        .map(|candidate| candidate.mode)
}

/// Computes the allocation classes included by
/// [`PreparedZeroMsm::prepared_bytes`] without first building the table.
fn estimated_table_footprint<C: GlvParams>(
    terms: usize,
    window_bits: usize,
    variants: usize,
    buckets: usize,
) -> Option<usize> {
    let variant_table = terms
        .checked_mul(variants)?
        .checked_mul(core::mem::size_of::<prepared::PreparedPoint<C::Base>>())?;
    let tail_bases = terms.checked_mul(core::mem::size_of::<orbit::RotatedBase<C::Base>>())?;
    let residue_entries =
        (1usize << (2 * window_bits)).checked_mul(core::mem::size_of::<codebook::CodeEntry>())?;
    let lifts = variants
        .checked_add(buckets)?
        .checked_mul(core::mem::size_of::<codebook::Eis>())?;
    variant_table
        .checked_add(tail_bases)?
        .checked_add(residue_entries)?
        .checked_add(lifts)
}

#[cfg(test)]
pub(crate) mod testutil {
    use super::*;

    /// Deterministic full-width nonzero discrete logs.
    fn dl<C: GlvParams>(seed: u64, index: u64) -> C::ScalarExt {
        let base = C::ScalarExt::from(0x9E37_79B9_7F4A_7C15u64 ^ seed);
        (base + C::ScalarExt::from(index)).square().square() + C::ScalarExt::from(index + 1)
    }

    /// Builds `terms` bases with known discrete logs — including identity,
    /// duplicate, negated, and endomorphic entries — plus `count` scalar
    /// vectors over those bases, each an **exact zero relation** (§23.4):
    /// random full-width scalars with the last live scalar solved so that
    /// $\sum_i k_i g_i = 0$.
    pub(crate) fn zero_relations<C: GlvParams>(
        terms: usize,
        seed: u64,
        count: usize,
    ) -> (Vec<Vec<C::ScalarExt>>, Vec<C::AffineExt>) {
        assert!(terms >= 8);
        let generator = C::generator();
        let mut dls = Vec::with_capacity(terms);
        for index in 0..terms {
            let value = match index % 32 {
                0 => C::ScalarExt::ZERO,                    // identity base
                2 => dl::<C>(seed, 1),                      // duplicate of 1
                3 => -dl::<C>(seed, 1),                     // negation of 1
                4 => dl::<C>(seed, 1) * C::ScalarExt::ZETA, // endomorphic image
                _ => dl::<C>(seed, index as u64),
            };
            dls.push(value);
        }
        let bases: Vec<C::AffineExt> = dls
            .iter()
            .map(|value| {
                if bool::from(value.is_zero()) {
                    C::AffineExt::identity()
                } else {
                    (generator * value).to_affine()
                }
            })
            .collect();

        let equations = (0..count)
            .map(|equation| {
                let scalar_seed = seed.wrapping_add(0xABCD + 1_000 * equation as u64);
                let mut scalars: Vec<C::ScalarExt> = (0..terms)
                    .map(|index| dl::<C>(scalar_seed, index as u64 + 7))
                    .collect();
                // Sparsity mixed in: some zero scalars and small scalars.
                for index in (0..terms).step_by(13) {
                    scalars[index] = C::ScalarExt::ZERO;
                }
                for index in (5..terms).step_by(17) {
                    scalars[index] = C::ScalarExt::from(index as u64);
                }
                let solve = terms - 1;
                assert!(!bool::from(dls[solve].is_zero()));
                let mut sum = C::ScalarExt::ZERO;
                for index in 0..terms {
                    if index != solve {
                        sum += scalars[index] * dls[index];
                    }
                }
                scalars[solve] = -sum * dls[solve].invert().unwrap();
                assert_eq!(
                    dls.iter()
                        .zip(&scalars)
                        .fold(C::ScalarExt::ZERO, |acc, (g, k)| acc + *g * k),
                    C::ScalarExt::ZERO
                );
                scalars
            })
            .collect();
        (equations, bases)
    }

    /// One-equation convenience form of [`zero_relations`].
    pub(crate) fn zero_relation<C: GlvParams>(
        terms: usize,
        seed: u64,
    ) -> (Vec<C::ScalarExt>, Vec<C::AffineExt>) {
        let (mut equations, bases) = zero_relations::<C>(terms, seed, 1);
        (equations.pop().unwrap(), bases)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{pallas, vesta};

    fn modes_under_test() -> Vec<CodebookMode> {
        vec![
            CodebookMode::alpha_only(6),
            CodebookMode::alpha_only(7),
            CodebookMode::alpha_only(8),
            CodebookMode::alpha_only(9),
            CodebookMode::Subgroup {
                window_bits: 6,
                beta_power: Some(4),
            },
            CodebookMode::Subgroup {
                window_bits: 6,
                beta_power: Some(1),
            },
            CodebookMode::ExponentBox {
                window_bits: 6,
                alpha_extent: 8,
                beta_extent: 8,
            },
            CodebookMode::ExponentBox {
                window_bits: 8,
                alpha_extent: 16,
                beta_extent: 16,
            },
        ]
    }

    /// Exact zero relations verify; one-bit perturbations, all-zero
    /// scalars, and single-term inputs behave per §23.4 — at every mode.
    fn zero_checks_across_modes<C: GlvParams>() {
        let terms = 600;
        let (scalars, bases) = testutil::zero_relation::<C>(terms, 42);
        for mode in modes_under_test() {
            let prepared = PreparedZeroMsm::<C>::prepare_with_mode(&bases, mode);
            assert!(
                prepared.is_zero_vartime(&scalars),
                "true relation rejected ({mode:?})"
            );

            let mut perturbed = scalars.clone();
            perturbed[10] += C::ScalarExt::ONE;
            assert!(
                !prepared.is_zero_vartime(&perturbed),
                "perturbed relation accepted ({mode:?})"
            );

            let zeros = alloc::vec![C::ScalarExt::ZERO; terms];
            assert!(prepared.is_zero_vartime(&zeros));

            let mut single = zeros.clone();
            single[1] = C::ScalarExt::from(123);
            assert!(!prepared.is_zero_vartime(&single));
        }
    }

    /// The prepared check agrees with the generic MSM on random (nonzero)
    /// inputs and on the same inputs with extra terms carved out.
    fn matches_generic_msm<C: GlvParams>() {
        let (scalars, bases, expected) = super::super::testutil::verifier_multiexp_inputs::<C>(700);
        let prepared = PreparedZeroMsm::<C>::prepare_with_mode(&bases, CodebookMode::alpha_only(6));
        assert_eq!(
            prepared.is_zero_vartime(&scalars),
            bool::from(expected.is_identity())
        );

        // Cancel the expected value through an extra term: the check with
        // extras must accept exactly then.
        let extra = [(-C::ScalarExt::ONE, expected.to_affine())];
        assert!(prepared.is_zero_with_terms_vartime(&scalars, &extra));
        let wrong = [(C::ScalarExt::ONE, expected.to_affine())];
        assert_eq!(
            prepared.is_zero_with_terms_vartime(&scalars, &wrong),
            bool::from(expected.is_identity())
        );

        // The point-returning evaluation is the same computation with the
        // group element handed back: it must equal the generic MSM exactly,
        // with and without extra terms.
        assert_eq!(
            prepared.multiexp_with_terms_vartime(&scalars, &[]),
            expected
        );
        assert!(bool::from(
            prepared
                .multiexp_with_terms_vartime(&scalars, &extra)
                .is_identity()
        ));
        let generator = C::generator().to_affine();
        assert_eq!(
            prepared.multiexp_with_terms_vartime(&scalars, &[(C::ScalarExt::from(41), generator)]),
            expected + C::generator() * C::ScalarExt::from(41)
        );
    }

    /// Splitting terms between the prepared set and the extras never
    /// changes the verdict.
    fn extras_match_inline_terms<C: GlvParams>() {
        let (scalars, bases) = testutil::zero_relation::<C>(80, 7);
        let split = 64;
        let prepared =
            PreparedZeroMsm::<C>::prepare_with_mode(&bases[..split], CodebookMode::alpha_only(6));
        let extra: Vec<(C::ScalarExt, C::AffineExt)> = scalars[split..]
            .iter()
            .cloned()
            .zip(bases[split..].iter().cloned())
            .collect();
        assert!(prepared.is_zero_with_terms_vartime(&scalars[..split], &extra));
        let mut broken = extra.clone();
        // Index 64 is an identity base in the corpus; perturb a live one.
        broken[2].0 += C::ScalarExt::ONE;
        assert!(!prepared.is_zero_with_terms_vartime(&scalars[..split], &broken));
    }

    /// Probabilistic batching: all-true batches accept; any false member
    /// rejects (failure needs a challenge collision of probability ~1/r),
    /// through both the self-deriving and explicit-challenge APIs.
    fn batch_combination<C: GlvParams>()
    where
        C::ScalarExt: ff::FromUniformBytes<64>,
    {
        let (mut equations, bases) = testutil::zero_relations::<C>(120, 1, 2);
        let scalars_b = equations.pop().unwrap();
        let scalars_a = equations.pop().unwrap();
        let prepared = PreparedZeroMsm::<C>::prepare_with_mode(&bases, CodebookMode::alpha_only(6));
        assert!(prepared.is_zero_batch_vartime(&[&scalars_a, &scalars_b]));
        assert!(prepared.is_zero_batch_vartime(&[]));
        let mut broken = scalars_b.clone();
        broken[3] += C::ScalarExt::ONE;
        assert!(!prepared.is_zero_batch_vartime(&[&scalars_a, &broken]));

        let challenge = C::ScalarExt::from(0xDEAD_BEEFu64).square() + C::ScalarExt::ONE;
        assert!(
            prepared.is_zero_batch_with_challenge_vartime(&[&scalars_a, &scalars_b], challenge)
        );
        assert!(!prepared.is_zero_batch_with_challenge_vartime(&[&scalars_a, &broken], challenge));
        // An empty batch is vacuously true through both entry points.
        assert!(prepared.is_zero_batch_with_challenge_vartime(&[], challenge));
    }

    /// The α and β merges fold with the exact eigenvalues: bases planted
    /// as $[\mu]P$ for $\mu \in \{1-\lambda,\, 2-\lambda,\, -\lambda(1-\lambda),\,
    /// \lambda^2(2-\lambda)\}$ merge away, exact relations over them
    /// verify, and perturbing a merged base's scalar rejects — a wrong
    /// fold eigenvalue flips one of these verdicts. (The shared corpus
    /// plants only unit-type relations, covered by `relation_scan_merges`
    /// below; this closes the α/β leg end to end.)
    fn relation_scan_alpha_beta_merges<C: GlvParams>() {
        let generator = C::generator();
        let lambda = <C::ScalarExt as WithSmallOrderMulGroup<3>>::ZETA;
        let alpha = C::ScalarExt::ONE - lambda;
        let beta = C::ScalarExt::from(2) - lambda;
        let anchor = C::ScalarExt::from(0x1234_5678_9ABC_DEF1u64).square() + C::ScalarExt::ONE;
        let mut dls: Vec<C::ScalarExt> = (0..40u64)
            .map(|i| C::ScalarExt::from(0x9E37_79B9u64 + i).square() + C::ScalarExt::from(i))
            .collect();
        dls[7] = anchor;
        dls[11] = anchor * alpha; // [α]P₇
        dls[13] = anchor * beta; // [β]P₇
        dls[17] = -(anchor * alpha * lambda); // [−λα]P₇
        dls[19] = anchor * beta * lambda.square(); // [λ²β]P₇
        let bases: Vec<C::AffineExt> = dls.iter().map(|d| (generator * d).to_affine()).collect();

        let prepared = PreparedZeroMsm::<C>::prepare_with_mode(&bases, CodebookMode::alpha_only(6));
        assert!(prepared.merges.len() >= 4);
        for planted in [11usize, 13, 17, 19] {
            assert!(
                !prepared.live[planted],
                "planted index {planted} must merge away"
            );
        }

        // An exact zero relation, solved on the anchor base.
        let mut scalars: Vec<C::ScalarExt> = (0..40u64)
            .map(|i| C::ScalarExt::from(0xABCD_EF01u64 + i).square() + C::ScalarExt::from(i + 3))
            .collect();
        let mut sum = C::ScalarExt::ZERO;
        for (index, (scalar, dl)) in scalars.iter().zip(&dls).enumerate() {
            if index != 7 {
                sum += *scalar * dl;
            }
        }
        scalars[7] = -sum * anchor.invert().unwrap();
        assert!(prepared.is_zero_vartime(&scalars));

        // A merged base's scalar reaches the sum only through its fold, so
        // each perturbation must still flip the verdict.
        for planted in [11usize, 13, 17, 19] {
            let mut perturbed = scalars.clone();
            perturbed[planted] += C::ScalarExt::ONE;
            assert!(
                !prepared.is_zero_vartime(&perturbed),
                "perturbing merged index {planted} must reject"
            );
        }
    }

    /// The relation scan finds duplicates, negations, and endomorphic
    /// images planted by the corpus, and folded evaluation stays exact.
    fn relation_scan_merges<C: GlvParams>() {
        let (scalars, bases) = testutil::zero_relation::<C>(200, 3);
        let prepared = PreparedZeroMsm::<C>::prepare_with_mode(&bases, CodebookMode::alpha_only(6));
        // The corpus plants duplicate/negated/endomorphic bases every 32
        // indices; at 200 terms the scan must find some.
        assert!(
            !prepared.merges.is_empty(),
            "planted relations must be found"
        );
        assert!(prepared.is_zero_vartime(&scalars));
        let mut perturbed = scalars;
        perturbed[2] += C::ScalarExt::ONE;
        assert!(!prepared.is_zero_vartime(&perturbed));
    }

    /// The default planner produces a working preparation.
    fn planned_mode_works<C: GlvParams>() {
        let (scalars, bases) = testutil::zero_relation::<C>(600, 11);
        let prepared =
            PreparedZeroMsm::<C>::prepare(&bases).expect("600 bases fit the default budget");
        assert!(prepared.is_zero_vartime(&scalars));
        let estimate = estimated_table_footprint::<C>(
            bases.len(),
            prepared.mode().window_bits(),
            prepared.codebook.variants().len(),
            prepared.codebook.bucket_count(),
        )
        .expect("the table-footprint estimate fits usize");
        assert_eq!(estimate, prepared.prepared_bytes());
    }

    /// The default mode planner stays within its table-footprint budget and
    /// declines (rather than over-allocating) when no candidate fits.
    #[test]
    fn plan_mode_respects_budget() {
        for threads in [1usize, 32] {
            let mode = plan_mode::<pallas::Point>(2_050, threads, DEFAULT_TABLE_FOOTPRINT_BUDGET);
            assert_eq!(mode, Some(CodebookMode::alpha_only(7)));
            let bytes = estimated_table_footprint::<pallas::Point>(
                2_050,
                ALPHA_SEVEN.mode.window_bits(),
                ALPHA_SEVEN.variants,
                ALPHA_SEVEN.buckets,
            )
            .expect("the Orchard-sized estimate fits usize");
            assert!(bytes <= DEFAULT_TABLE_FOOTPRINT_BUDGET);

            let fixed = estimated_table_footprint::<pallas::Point>(
                0,
                ALPHA_FIVE.mode.window_bits(),
                ALPHA_FIVE.variants,
                ALPHA_FIVE.buckets,
            )
            .unwrap();
            let one = estimated_table_footprint::<pallas::Point>(
                1,
                ALPHA_FIVE.mode.window_bits(),
                ALPHA_FIVE.variants,
                ALPHA_FIVE.buckets,
            )
            .unwrap();
            let largest = (DEFAULT_TABLE_FOOTPRINT_BUDGET - fixed) / (one - fixed);
            let fits = plan_mode::<pallas::Point>(largest, threads, DEFAULT_TABLE_FOOTPRINT_BUDGET);
            let too_large =
                plan_mode::<pallas::Point>(largest + 1, threads, DEFAULT_TABLE_FOOTPRINT_BUDGET);
            assert!(fits.is_some());
            assert_eq!(too_large, None);
        }
    }

    /// Planner metadata stays synchronized with constructed codebooks.
    #[test]
    fn default_candidate_shapes_match_codebooks() {
        for candidate in DEFAULT_MODE_CANDIDATES {
            let codebook = Codebook::new(candidate.mode);
            assert_eq!(candidate.variants, codebook.variants().len());
            assert_eq!(candidate.buckets, codebook.bucket_count());
        }
    }

    #[cfg(feature = "multicore")]
    fn zero_checks_at_thread_counts<C: GlvParams>() {
        for num_threads in [2, 3, 8] {
            maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(num_threads)
                .build()
                .expect("test thread pool must build")
                .install(|| {
                    let (scalars, bases) = testutil::zero_relation::<C>(600, 5);
                    let prepared = PreparedZeroMsm::<C>::prepare_with_mode(
                        &bases,
                        CodebookMode::alpha_only(7),
                    );
                    assert!(prepared.is_zero_vartime(&scalars));
                    let mut perturbed = scalars;
                    perturbed[10] += C::ScalarExt::ONE;
                    assert!(!prepared.is_zero_vartime(&perturbed));
                });
        }
    }

    /// The coefficient program computes Σ [δ_j] Q_j (§23.1), on real
    /// bucket sums of every occupancy pattern. The mode list covers both
    /// integration strategies: α6 and β6^1 run straight-line, α8's
    /// 320-addition program crosses [`BATCH_INTEGRATE_MIN_ADDS`] into the
    /// batched-affine tree.
    fn coefficient_program_matches_naive<C: GlvParams>() {
        let generator = C::generator();
        for mode in [
            CodebookMode::alpha_only(6),
            CodebookMode::alpha_only(8),
            CodebookMode::Subgroup {
                window_bits: 6,
                beta_power: Some(1),
            },
        ] {
            let codebook = Codebook::new(mode);
            let m = codebook.bucket_count();
            for pattern in 0..3u64 {
                let buckets: Vec<Option<AffinePoint<C::Base>>> = (0..m)
                    .map(|k| {
                        let keep = match pattern {
                            0 => true,
                            1 => k % 3 == 1,
                            _ => k == 0,
                        };
                        keep.then(|| {
                            let point = generator
                                * (C::ScalarExt::from(k as u64 + 2).square()
                                    + C::ScalarExt::from(pattern + 1));
                            let affine = point.to_affine();
                            let (x, y) = C::affine_xy(&affine);
                            AffinePoint { x, y }
                        })
                    })
                    .collect();
                let mut expected = C::identity();
                let signed = |v: i64| {
                    let m = C::ScalarExt::from(v.unsigned_abs());
                    if v < 0 { -m } else { m }
                };
                for (&delta, bucket) in codebook.coefficients().iter().zip(&buckets) {
                    if let Some(point) = bucket {
                        let weight = signed(delta.a)
                            + signed(delta.b) * <C::ScalarExt as WithSmallOrderMulGroup<3>>::ZETA;
                        expected += C::from(C::affine_unchecked(
                            point.x,
                            point.y,
                            private::CrateToken(()),
                        )) * weight;
                    }
                }
                assert_eq!(
                    integrate_coefficients::<C>(codebook.program(), &buckets)
                        .expect("valid bucket sums"),
                    expected,
                    "coefficient program mismatch ({mode:?}, pattern {pattern})"
                );
            }
        }
    }

    macro_rules! zero_tests {
        ($mod_name:ident, $curve:ty) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn across_modes() {
                    zero_checks_across_modes::<$curve>();
                }
                #[test]
                fn generic_agreement() {
                    matches_generic_msm::<$curve>();
                }
                #[test]
                fn extras() {
                    extras_match_inline_terms::<$curve>();
                }
                #[test]
                fn batching() {
                    batch_combination::<$curve>();
                }
                #[test]
                fn relation_scan() {
                    relation_scan_merges::<$curve>();
                }
                #[test]
                fn relation_scan_alpha_beta() {
                    relation_scan_alpha_beta_merges::<$curve>();
                }
                #[test]
                fn planned_mode() {
                    planned_mode_works::<$curve>();
                }
                #[test]
                fn coefficient_program() {
                    coefficient_program_matches_naive::<$curve>();
                }
                #[cfg(feature = "multicore")]
                #[test]
                fn thread_counts() {
                    zero_checks_at_thread_counts::<$curve>();
                }
            }
        };
    }

    /// Manual per-phase timing of the serial prepared path (§24's phase
    /// breakdown): decomposition, recoding, window staging, batched-affine
    /// reduction, coefficient integration, the tail MSM, and the Horner
    /// doublings, plus the extra-terms overhead of a halo2-shaped check.
    ///
    /// ```text
    /// cargo test --release --features multicore,orbits --lib -- \
    ///     --ignored zero_check_phase_timings --nocapture
    /// ```
    #[test]
    #[ignore = "manual timing harness; see the doc comment"]
    fn zero_check_phase_timings() {
        use group::Group as _;
        use std::time::Instant;
        use std::vec::Vec;

        type C = vesta::Point;

        let terms = 2_048;
        let (scalars, bases) = testutil::zero_relation::<C>(terms, 99);
        #[cfg(feature = "multicore")]
        let pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .expect("bench thread pool must build");

        let body = || {
            for mode in [
                CodebookMode::Subgroup {
                    window_bits: 7,
                    beta_power: Some(8),
                },
                CodebookMode::alpha_only(7),
            ] {
                let prepared = PreparedZeroMsm::<C>::prepare_with_mode(&bases, mode);
                let iters = 15;
                let mut phases = [0.0f64; 7];
                let mut extras_delta = [0.0f64; 2];
                const EXTRAS_COUNTS: [usize; 2] = [48, 512];
                // The scan finds the corpus's planted relations; fold them
                // as the production path does (timed within "decompose").
                let mut folded = scalars.clone();
                for &(source, target, mu) in &prepared.merges {
                    let contribution = folded[source] * mu;
                    folded[target] += contribution;
                    folded[source] = <C as crate::arithmetic::CurveExt>::ScalarExt::ZERO;
                }
                for _ in 0..iters {
                    let mut mark = Instant::now();
                    let mut lap = |slot: &mut f64| {
                        let now = Instant::now();
                        *slot += (now - mark).as_secs_f64() * 1e3;
                        mark = now;
                    };
                    let components: Vec<_> = folded
                        .iter()
                        .enumerate()
                        .map(|(index, k)| {
                            if !prepared.live[index] {
                                let zero = SignedMagnitude {
                                    negative: false,
                                    magnitude: 0,
                                };
                                return (zero, zero);
                            }
                            checked_signed_magnitudes(decompose::<C>(k)).expect("bounded")
                        })
                        .collect();
                    lap(&mut phases[0]); // decompose
                    let recoded = codebook::recode(&prepared.codebook, &components, 1);
                    lap(&mut phases[1]); // recode
                    let mut window_sums = Vec::with_capacity(recoded.active_windows);
                    for window in 0..recoded.active_windows {
                        let (points, offsets) = prepared.stage_window(&recoded, window);
                        lap(&mut phases[2]); // stage (fetch + placement)
                        let buckets = reduce_affine_buckets(points, offsets).expect("valid points");
                        lap(&mut phases[3]); // batched-affine reduction
                        window_sums.push(
                            integrate_coefficients::<C>(prepared.codebook.program(), &buckets)
                                .expect("valid points"),
                        );
                        lap(&mut phases[4]); // coefficient integration
                    }
                    let tail = prepared
                        .tail_sum(&recoded.residuals, 1)
                        .expect("valid points");
                    lap(&mut phases[5]); // tail MSM
                    let window_bits = prepared.codebook.window_bits();
                    let main_windows = prepared.codebook.main_windows();
                    let mut acc = tail;
                    if !bool::from(acc.is_identity()) {
                        for _ in 0..window_bits * (main_windows - recoded.active_windows) {
                            acc = acc.double();
                        }
                    }
                    for sum in window_sums.into_iter().rev() {
                        for _ in 0..window_bits {
                            acc = acc.double();
                        }
                        acc += sum;
                    }
                    lap(&mut phases[6]); // Horner recombination
                    assert!(bool::from(acc.is_identity()));

                    // Extra-terms overhead: a halo2-shaped check carries a
                    // few dozen per-proof commitments per proof (hundreds
                    // under batch verification).
                    for (count, delta) in EXTRAS_COUNTS.iter().zip(&mut extras_delta) {
                        let extra: Vec<_> = scalars[..*count]
                            .iter()
                            .cloned()
                            .zip(bases[..*count].iter().cloned())
                            .collect();
                        let start = Instant::now();
                        let with_extras = prepared.is_zero_with_terms_vartime(&scalars, &extra);
                        let with_ms = start.elapsed().as_secs_f64() * 1e3;
                        let start = Instant::now();
                        let without = prepared.is_zero_vartime(&scalars);
                        let without_ms = start.elapsed().as_secs_f64() * 1e3;
                        assert!(!with_extras || without); // perturbed sums differ
                        *delta += with_ms - without_ms;
                    }
                }
                let total: f64 = phases.iter().sum();
                let labels = [
                    "decompose",
                    "recode",
                    "stage",
                    "reduce",
                    "integrate",
                    "tail",
                    "horner",
                ];
                let mut report = std::string::String::new();
                for (label, ms) in labels.iter().zip(phases) {
                    report.push_str(&format!(
                        "{label}={:.3}ms({:.0}%) ",
                        ms / iters as f64,
                        100.0 * ms / total
                    ));
                }
                println!(
                    "vesta terms={terms} serial {mode:?}: {report}total={:.3}ms \
                     extras48-delta={:+.3}ms extras512-delta={:+.3}ms",
                    total / iters as f64,
                    extras_delta[0] / iters as f64,
                    extras_delta[1] / iters as f64,
                );
            }
        };
        #[cfg(feature = "multicore")]
        pool.install(body);
        #[cfg(not(feature = "multicore"))]
        body();

        // The same phase split under contention: per-window stage/reduce/
        // integrate accumulated across parallel window tasks (CPU time
        // summed over workers, so a phase whose *sum* grows with the
        // worker count is losing to shared-cache contention). Contrasts a
        // small table (α6, 12 MiB at 2,048 terms) against a large one
        // (β7^8, 48 MiB).
        #[cfg(feature = "multicore")]
        for threads in [8usize, 32] {
            let pool = maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .expect("bench thread pool must build");
            pool.install(|| {
                use std::sync::atomic::{AtomicU64, Ordering};
                for mode in [
                    CodebookMode::Subgroup {
                        window_bits: 7,
                        beta_power: Some(8),
                    },
                    CodebookMode::alpha_only(6),
                ] {
                    let prepared = PreparedZeroMsm::<C>::prepare_with_mode(&bases, mode);
                    let mut folded = scalars.clone();
                    for &(source, target, mu) in &prepared.merges {
                        let contribution = folded[source] * mu;
                        folded[target] += contribution;
                        folded[source] = <C as crate::arithmetic::CurveExt>::ScalarExt::ZERO;
                    }
                    let iters = 15;
                    let stage_ns = AtomicU64::new(0);
                    let reduce_ns = AtomicU64::new(0);
                    let integrate_ns = AtomicU64::new(0);
                    let mut wall = 0.0f64;
                    for _ in 0..iters {
                        let components: Vec<_> = folded
                            .iter()
                            .enumerate()
                            .map(|(index, k)| {
                                if !prepared.live[index] {
                                    let zero = SignedMagnitude {
                                        negative: false,
                                        magnitude: 0,
                                    };
                                    return (zero, zero);
                                }
                                checked_signed_magnitudes(decompose::<C>(k)).expect("bounded")
                            })
                            .collect();
                        let recoded = codebook::recode(&prepared.codebook, &components, threads);
                        let window_bits = prepared.codebook.window_bits();
                        let start = Instant::now();
                        let windows_part = (0..recoded.active_windows)
                            .into_par_iter()
                            .map(|window| {
                                let mark = Instant::now();
                                let (points, offsets) = prepared.stage_window(&recoded, window);
                                stage_ns
                                    .fetch_add(mark.elapsed().as_nanos() as u64, Ordering::Relaxed);
                                let mark = Instant::now();
                                let buckets = reduce_affine_buckets(points, offsets)?;
                                reduce_ns
                                    .fetch_add(mark.elapsed().as_nanos() as u64, Ordering::Relaxed);
                                let mark = Instant::now();
                                let mut sum = integrate_coefficients::<C>(
                                    prepared.codebook.program(),
                                    &buckets,
                                )?;
                                for _ in 0..window_bits * window {
                                    sum = sum.double();
                                }
                                integrate_ns
                                    .fetch_add(mark.elapsed().as_nanos() as u64, Ordering::Relaxed);
                                Some(sum)
                            })
                            .try_reduce(C::identity, |mut left, right| {
                                left += right;
                                Some(left)
                            })
                            .expect("valid points");
                        wall += start.elapsed().as_secs_f64() * 1e3;
                        let mut tail = prepared
                            .tail_sum(&recoded.residuals, threads)
                            .expect("valid points");
                        if !bool::from(tail.is_identity()) {
                            for _ in 0..window_bits * prepared.codebook.main_windows() {
                                tail = tail.double();
                            }
                        }
                        assert!(bool::from((windows_part + tail).is_identity()));
                    }
                    let per_iter =
                        |ns: &AtomicU64| ns.load(Ordering::Relaxed) as f64 / 1e6 / iters as f64;
                    println!(
                        "vesta terms={terms} threads={threads} {mode:?}: \
                         windows-wall={:.3}ms cpu-sums: stage={:.3}ms reduce={:.3}ms \
                         integrate+shift={:.3}ms",
                        wall / iters as f64,
                        per_iter(&stage_ns),
                        per_iter(&reduce_ns),
                        per_iter(&integrate_ns),
                    );
                }
            });
        }
    }

    /// Manual timing harness for the fixed-base zero-check candidates; used
    /// to pick the default prepared mode and calibrate [`plan_mode`]. Not
    /// part of the automated suite.
    ///
    /// ```text
    /// cargo test --release --features multicore,orbits --lib -- \
    ///     --ignored zero_check_timings --nocapture
    /// ```
    ///
    /// Candidates per cell, all timed in interleaved rounds (one sample of
    /// every candidate per round, medians reported) against the production
    /// unprepared control (`try_multiexp` + identity test):
    /// prepared α-only widths 6..=9, selected β-subgroup modes, and the
    /// fixed subset-table baseline.
    #[test]
    #[ignore = "manual timing harness; see the doc comment"]
    fn zero_check_timings() {
        use group::Group as _;
        use std::string::String;
        use std::time::Instant;
        use std::vec::Vec;

        type C = vesta::Point;

        fn median(mut samples: Vec<f64>) -> f64 {
            samples.sort_by(f64::total_cmp);
            samples[samples.len() / 2]
        }

        const SIZES: [usize; 5] = [512, 1_024, 2_048, 4_096, 8_192];
        const THREADS: [usize; 6] = [1, 2, 4, 8, 16, 32];

        for terms in SIZES {
            let (scalars, bases) = testutil::zero_relation::<C>(terms, 99);
            let mut wrong = scalars.clone();
            wrong[10] += <C as crate::arithmetic::CurveExt>::ScalarExt::ONE;

            let mut modes = alloc::vec![
                CodebookMode::alpha_only(6),
                CodebookMode::alpha_only(7),
                CodebookMode::alpha_only(8),
                CodebookMode::alpha_only(9),
                CodebookMode::Subgroup {
                    window_bits: 6,
                    beta_power: Some(4),
                },
                CodebookMode::Subgroup {
                    window_bits: 7,
                    beta_power: Some(8),
                },
                CodebookMode::Subgroup {
                    window_bits: 8,
                    beta_power: Some(16),
                },
            ];
            if terms <= 2_048 {
                // The wider-geometry candidates (only affordable small):
                // full units at B = 64 (512 variants), the box-cardinality
                // subgroup β8^32, and the two most instructive exponent
                // boxes — the assessment's 16×16 at c = 8 and the
                // half-memory β7^8 analogue at c = 7.
                modes.extend([
                    CodebookMode::Subgroup {
                        window_bits: 6,
                        beta_power: Some(1),
                    },
                    CodebookMode::Subgroup {
                        window_bits: 8,
                        beta_power: Some(32),
                    },
                    CodebookMode::ExponentBox {
                        window_bits: 8,
                        alpha_extent: 16,
                        beta_extent: 16,
                    },
                    CodebookMode::ExponentBox {
                        window_bits: 7,
                        alpha_extent: 16,
                        beta_extent: 8,
                    },
                ]);
            }

            let mut prepared_list: Vec<(String, PreparedZeroMsm<C>)> = Vec::new();
            for mode in modes {
                let start = Instant::now();
                let prepared = PreparedZeroMsm::<C>::prepare_with_mode(&bases, mode);
                let prep_ms = start.elapsed().as_secs_f64() * 1e3;
                assert!(prepared.is_zero_vartime(&scalars));
                assert!(!prepared.is_zero_vartime(&wrong));
                let label = match mode {
                    CodebookMode::Subgroup {
                        window_bits,
                        beta_power: None,
                    } => format!("a{window_bits}"),
                    CodebookMode::Subgroup {
                        window_bits,
                        beta_power: Some(k),
                    } => format!("b{window_bits}^{k}"),
                    CodebookMode::ExponentBox {
                        window_bits,
                        alpha_extent,
                        beta_extent,
                    } => format!("x{window_bits}_{alpha_extent}x{beta_extent}"),
                };
                println!(
                    "vesta terms={terms:>5} prepare {label:>6}: {prep_ms:>8.1}ms \
                     {:>7.1}MiB windows={} buckets={} program={:?} tail_bound={}",
                    prepared.prepared_bytes() as f64 / (1 << 20) as f64,
                    prepared.codebook.main_windows(),
                    prepared.codebook.bucket_count(),
                    prepared.codebook.program_cost(),
                    prepared.codebook.tail_bound(),
                );
                prepared_list.push((label, prepared));
            }

            let mut subset_list: Vec<(String, subset::SubsetTable<C>)> = Vec::new();
            for block_bits in [10usize, 12, 14] {
                if (terms > 2_048 && block_bits > 10) || (terms != 2_048 && block_bits > 12) {
                    continue; // hundreds of MiB; not a useful tier
                }
                let start = Instant::now();
                let table = subset::SubsetTable::<C>::prepare(&bases, block_bits);
                let prep_ms = start.elapsed().as_secs_f64() * 1e3;
                assert!(table.is_zero_vartime(&scalars));
                assert!(!table.is_zero_vartime(&wrong));
                println!(
                    "vesta terms={terms:>5} prepare  t={block_bits:>2}: {prep_ms:>8.1}ms \
                     {:>7.1}MiB",
                    table.bytes() as f64 / (1 << 20) as f64,
                );
                subset_list.push((format!("t{block_bits}"), table));
            }

            for threads in THREADS {
                #[cfg(feature = "multicore")]
                let pool = maybe_rayon::ThreadPoolBuilder::new()
                    .num_threads(threads)
                    .build()
                    .expect("bench thread pool must build");
                #[cfg(not(feature = "multicore"))]
                if threads != 1 {
                    continue;
                }

                let iters = (1_200_000 / terms).clamp(5, 31) | 1;
                let body = || {
                    let mut main_samples = Vec::new();
                    let mut control_samples = Vec::new();
                    let mut prepared_samples = alloc::vec![Vec::new(); prepared_list.len()];
                    let mut subset_samples = alloc::vec![Vec::new(); subset_list.len()];
                    for _ in 0..iters {
                        // What upstream main's verifier runs for this check:
                        // its Booth-only try_multiexp (the code below is
                        // byte-identical to main's) plus the identity test.
                        // At cells where main's model refuses GLV entirely
                        // (running the generic MSM, which this harness does
                        // not reimplement), the column is skipped.
                        if let Some(window_bits) =
                            super::super::glv_multiexp_window_bits::<C>(scalars.len(), threads)
                        {
                            let start = Instant::now();
                            let components = scalars
                                .iter()
                                .map(super::super::decompose::<C>)
                                .map(super::super::checked_signed_magnitudes)
                                .collect::<Option<Vec<_>>>()
                                .expect("bounded halves");
                            let booth_bases = super::super::multiexp_bases::<C>(&bases);
                            let main_equivalent = super::super::multiexp::<C>(
                                &components,
                                &booth_bases,
                                window_bits,
                                threads,
                            );
                            main_samples.push(start.elapsed().as_secs_f64() * 1e3);
                            assert!(bool::from(
                                main_equivalent.expect("Booth runs").is_identity()
                            ));
                        }

                        let start = Instant::now();
                        let control = super::super::try_multiexp::<C>(&scalars, &bases);
                        control_samples.push(start.elapsed().as_secs_f64() * 1e3);
                        assert!(bool::from(
                            control.expect("control plans a GLV backend").is_identity()
                        ));
                        for ((_, prepared), samples) in
                            prepared_list.iter().zip(&mut prepared_samples)
                        {
                            let start = Instant::now();
                            let ok = prepared.is_zero_vartime(&scalars);
                            samples.push(start.elapsed().as_secs_f64() * 1e3);
                            assert!(ok);
                        }
                        for ((_, table), samples) in subset_list.iter().zip(&mut subset_samples) {
                            let start = Instant::now();
                            let ok = table.is_zero_vartime(&scalars);
                            samples.push(start.elapsed().as_secs_f64() * 1e3);
                            assert!(ok);
                        }
                    }
                    let main_ms = (!main_samples.is_empty()).then(|| median(main_samples));
                    let control = median(control_samples);
                    let mut report = match main_ms {
                        Some(main_ms) => format!(
                            "vesta terms={terms:>5} threads={threads:>2} main={main_ms:>7.3}ms \
                             control={control:>7.3}ms "
                        ),
                        None => format!(
                            "vesta terms={terms:>5} threads={threads:>2} main=generic \
                             control={control:>7.3}ms "
                        ),
                    };
                    let mut best: Option<(&str, f64)> = None;
                    for ((label, _), samples) in prepared_list
                        .iter()
                        .zip(prepared_samples)
                        .map(|((l, p), s)| ((l.as_str(), p), s))
                    {
                        let ms = median(samples);
                        report.push_str(&format!("{label}={ms:.3} "));
                        if best.is_none_or(|(_, b)| ms < b) {
                            best = Some((label, ms));
                        }
                    }
                    for ((label, _), samples) in subset_list.iter().zip(subset_samples) {
                        let ms = median(samples);
                        report.push_str(&format!("{label}={ms:.3} "));
                    }
                    let (best_label, best_ms) = best.expect("some prepared mode ran");
                    let vs_main = match main_ms {
                        Some(main_ms) => format!("{:+.1}%", (main_ms / best_ms - 1.0) * 100.0),
                        None => alloc::string::String::from("n/a"),
                    };
                    println!(
                        "{report}| best={best_label} vs-main={vs_main} vs-control={:+.1}%",
                        (control / best_ms - 1.0) * 100.0
                    );
                };
                #[cfg(feature = "multicore")]
                pool.install(body);
                #[cfg(not(feature = "multicore"))]
                body();
            }
        }
    }

    zero_tests!(pallas_zero, pallas::Point);
    zero_tests!(vesta_zero, vesta::Point);
}
