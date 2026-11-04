//! The staged native proving pipeline over the fixed target.
//!
//! [`ProverPrefix`] carries the transcript through the frozen stage order:
//! advice commitments, lookup permutations, grand products, the vanishing
//! polynomial, quotient construction, evaluations, the multi-opening
//! collapse, and the recursive IPA. Every stage is deterministic: the random
//! values it spends arrive pre-sampled and labeled by use site in
//! [`super::randomness::ProvingRandomness`], which draws the reference
//! schedule the committed RNG tapes pin.
//!
//! This module holds the shared stage records and their representation checks.
//! Stage methods live in [`advice`], [`lookup`], [`products`], [`quotient`],
//! [`opening`], and [`ipa`], in execution order. They remain methods of the same
//! transcript owner, so moving between stages adds no dispatch or wrapper layer.
//! [`evaluation`] caches point powers within each opening or IPA worker wave.
//! [`inventory`] describes their work and retained buffers; [`fold_order`]
//! names the constraint slots whose positions determine challenge powers.
//!
//! Lower-level target, polynomial, and MSM errors become
//! [`Error::InternalInvariant`] when the inputs are prepared circuit data or
//! stage-owned shapes that must meet fixed circuit dimensions and internal
//! size relationships. Witness
//! relation and satisfaction errors instead propagate from [`super::witness`]
//! and [`super::preflight`]; see [`super::invariant`] for that distinction.
//! A randomized proof commitment may be the identity, which the transcript
//! cannot encode; its write reports [`Error::RetryRandomness`]. A zero IPA
//! challenge uses the same retry policy in [`ipa::invert_ipa_challenge`]. The
//! fixed-blind common instance commitments in [`ProverPrefix::initialize_checked`]
//! are deterministic for the statement and retain their separate internal-error
//! classification. See [`Error`] for caller recovery.
//!
//! # Stage-buffer ownership
//!
//! The table follows successful production execution. A [`Buffer`] owns its
//! storage exclusively; proof-created [`SharedPoly`] values normally wrap it
//! in an `Arc`. Cloning that handle shares storage, whereas cloning a `Buffer`
//! copies its contents. `into_unique` recovers the buffer only from its sole
//! owner, without copying. Moving a buffer into a transform or the next prefix
//! does not return it to a pool.
//!
//! A pooled buffer returns to its originating workspace pool on its last
//! owning drop, making its allocation reusable; borrowed views do not own a
//! lease. Buffers made from ordinary vectors or by execution without a pool
//! free normally instead. Static slices are never pooled. The same drop rules
//! apply on early returns, without implying later stages ran. Scalar blinds,
//! challenges, commitments, and fixed-size masks travel by value.
//!
//! | Record / storage | Creator | Shared readers | Consuming transition | Pool return / release |
//! | --- | --- | --- | --- | --- |
//! | [`ProverPrefix::statements`] | Proof pipeline: one `Arc<[NativeStatement]>` | Witness/preflight and the instance commitment borrow; sparse quotient jobs and instance opening sources clone the Arc. | Remains on the prover; opening binding folds statement values into an inline prefix. | Ordinary shared allocation, released by its last Arc; the prover keeps its owner until [`ProverPrefix::into_proof`]. |
//! | [`ProverPrefix::instance_polynomials`] | Preflight builds dense `SharedPoly` rows and passes them to [`ProverPrefix::initialize_checked`]. | Preflight, lookup compression, and permutation products borrow the rows. The instance commitment instead borrows `statements`. | [`ProverPrefix::commit_product_arguments`] clears the vector after its last value readers finish. | Last column owners drop at that clear; later stages use the sparse statements. |
//! | [`AdviceMatrix`] → [`AdvicePrefix::values`] | Witness construction; [`ProverPrefix::commit_advice`] unwraps each matrix after preflight, masks the columns, and wraps them as `SharedPoly` (matrix clone fallback if still shared). | Preflight reads the matrix; advice commitments, lookup compression, and product construction borrow the masked columns. | [`ProverPrefix::construct_quotient`] recovers each window's unique columns and moves them into inverse transforms. | No return at this move: the same buffers survive as opening coefficients. |
//! | [`PermutedLookup::compressed_input`] and [`LookupPrefix::compressed_tables`] | [`ProverPrefix::commit_lookup_permutations`]; equal table recipes share handles across lookups and every Action reads those tables. | Lookup permutation preparation and product construction borrow the compressed columns. | Quotient construction discards these base-domain inputs; its table cosets are computed separately. | Inputs drop while their window is staged. Table handles drop at single-window return, or explicitly before the multi-window loop. Last owners return any pooled storage. |
//! | [`PermutedLookup::permuted_input`] / [`PermutedLookup::permuted_table`] | Lookup permutation preparation, followed by tail masking and `SharedPoly` wrapping | Lookup commitments and products borrow both columns. | Quotient staging recovers unique buffers and moves them into the 4N form transforms; blinds move alongside the resulting coefficients. | Buffers survive as opening coefficients. Separate lookup interval-run buffers return after the lookup commitment batch. |
//! | [`ProductForms`] in [`PermutationPrefix`] / [`LookupProductPrefix`] | [`ProverPrefix::commit_product_arguments`] stages Lagrange rows; commitment side jobs transform a copy into coefficients and a ready or deferred [`ProductCoset`]. | The commitment batch borrows staged rows; quotient expansion borrows retained coefficients when a coset was deferred. | [`ProductForms::install`] replaces staged rows; [`split_product_openings`] later moves coefficients/blinds into [`ProductOpening`] and cosets into the window fold. | Staged rows drop on installation after the batch; permutation interval-run vectors are freed after the batch. Retained coefficients and cosets follow their rows below. |
//! | Proof-specific cosets: [`ProductCoset`], [`LookupCosets`], instance/advice forms | Product stage for a single-window proof; otherwise product expansion at window entry. Quotient jobs create the other cosets. | Residue fold plans share tiled storage; compressed table cosets additionally share an Arc across Actions and equal lookup recipes. | Each window's quotient coordinator consumes forms into fold plans; no proof-specific coset enters [`QuotientPrefix`]. | Residue/product storage returns after its final plan/task owner drops. Compressed tables also have a coordinator owner until the window's run ends. See the coordinator table below for per-job lifetimes. |
//! | Target fixed/sigma coefficients and cosets | [`FixedTarget`] preparation; the current coefficient and coset policies in [`crate::tuning`] are `WarmUp`, retaining heap storage. `Embed` variants borrow statics. | Quotient folds borrow coset views; evaluations and opening sums borrow coefficients. | No stage consumes target storage. | No proof-stage pool return; heap data follows the target's lifetime, and embedded data is static. |
//! | [`QuotientPrefix`] coefficients: advice, permuted lookups, [`ProductOpening`], [`QuotientPiece`] | Quotient transforms retain advice/lookup buffers, move product coefficients, and interpolate pieces; multiple windows combine pieces before commitment. | Piece commitments and expansions share temporary readers; [`ProverPrefix::write_evaluations`] and opening group sums borrow the retained coefficients. | [`ProverPrefix::commit_multiopen_quotient`] consumes the prefix, builds all `Q_i`, then explicitly drops it before divided copies and `Q′` are built. | Retained coefficient leases return at that drop. Intermediate window pieces return after their weighted addition to the combined pieces. |
//! | [`EvaluationSource`] / [`opening::OpeningSource`] | Evaluation job creation and opening-schedule binding | Dense production sources and quotient pieces borrow their owners; instance sources hold an Arc to statements; linear masks and evaluated values are inline. | Evaluation jobs consume descriptors; opening binding turns them into weighted borrowed sources, an inline instance prefix, or sparse terms for the group sums. | No new coefficient lease in these descriptors. Borrows end with the worker wave; instance-source Arcs drop after binding. Evaluation power-cache buffers drop after the evaluation wave. |
//! | [`MultiopenPrefix`] (`Q_i`, `Q′`) | [`ProverPrefix::commit_multiopen_quotient`] builds `Q_i` sums; divided copies produce `Q′` by reusing the first copy. | `Q′` commitment, `Q_i` evaluations, and the final Horner fold borrow coefficients. | [`ProverPrefix::commit_ipa_mask`] consumes the prefix, recovers unique `Q′` storage, and folds `Q_i` into it as [`IpaMaskPrefix::polynomial`]. | Other divided copies drop after `Q′` construction; `Q_i` drop immediately after the final fold. `Q′` storage moves on without returning. |
//! | [`IpaMaskPrefix::polynomial`] | Final opening fold, reusing `Q′` | IPA round preparation shares its current round state and borrows its polynomial. | [`ProverPrefix::finish_ipa`] moves the buffer into masking and the recursive rounds, which reuse it. | The polynomial and evaluation-power buffers drop when the round driver returns. Reusable workspace banks remain with the caller. |
//!
//! The [quotient coordinator table](quotient/run/struct.Quotient.html) details residue,
//! class, and piece publication/release. The
//! [MSM lease lifecycle](super::commitment::msm) details task receipts, reader
//! drainage, and workspace scratch. Those task lifecycles sit inside the stage
//! boundaries above.

mod advice;
mod evaluation;
pub(crate) mod fold_order;
mod inventory;
mod ipa;
mod lookup;
mod opening;
mod products;
mod quotient;

pub(crate) use ipa::IpaWorkspace;
pub(super) use lookup::prepared_lookup_table_tuples;
pub(crate) use lookup::{LookupPreparation, LookupWorkspace};

use super::buffer::Buffer;
use super::commitment::normalized;
use super::curve::{VestaPoint, VestaProjective};
use super::field::Fp;
#[cfg(test)]
use super::generated_expressions;
use super::invariant;
use super::invariant::Invariant;
use super::polynomial::{FpClass2NTiles, FpCosetTiles, SharedPoly};
use super::protocol::opening as opening_schedule;
use super::randomness::LOOKUPS_PER_ACTION;
use super::target::{
    ADVICE_COLUMNS, EXTENDED_N, FixedTarget, N, PERMUTATION_SETS, USABLE_ROWS_END,
};
use super::transcript::Transcript;
use super::witness::ASSIGNED_WORDS_PER_COLUMN;
use crate::Error;
use crate::types::{NativeStatement, ProvingRequest};
use alloc::{sync::Arc, vec::Vec};
#[cfg(test)]
use evaluation::EvaluationPowerCache;
use evaluation::{EvaluationJob, EvaluationSource, parallel_evaluate_polynomials};
#[cfg(test)]
use opening::PolySource;

/// Rows per quotient-fold task: 128 tasks over the extended domain, each
/// owning the stride views of every class accumulator its rows cover.
///
/// Kernel shape: a multiple of 8 dividing `EXTENDED_N` (asserted where the
/// tasks are cut), because each task's 4N/2N/N class chunks are its rows
/// divided by 2, 4, and 8. Dependents: `quotient_stage::FOLD_TASKS` and the
/// class chunk lengths.
const FOLD_CHUNK_ROWS: usize = 128;

/// Rows per lookup-compression task.
///
/// Tuning knob: any divisor of `EXTENDED_N`; the only dependent is the
/// compression task count.
const COMPRESSION_CHUNK_ROWS: usize = EXTENDED_N / 8;

/// Coefficients per task in the multi-opening collapse and Horner folds.
///
/// Tuning knob: any positive value; the only dependents are those task
/// counts (results are order-independent field sums).
const COEFFICIENT_CHUNK: usize = 128;

/// Native state after the fixed VK and instance transcript prefix is absorbed.
pub(crate) struct ProverPrefix<'a> {
    target: &'a FixedTarget,
    workspace: &'a mut super::ProverWorkspace,
    execution: super::worker::Execution<'a>,
    /// Each Action's dense `N`-row instance column; see the
    /// [ownership table](self#stage-buffer-ownership) for readers and release.
    /// Later stages obtain the Action count from [`Self::action_count`].
    instance_polynomials: Vec<SharedPoly>,
    /// The Actions' decoded native statement records in one shared allocation;
    /// see the [ownership table](self#stage-buffer-ownership).
    statements: Arc<[NativeStatement]>,
    transcript: Transcript,
}

/// One finalized, unblinded advice matrix at the native protocol boundary,
/// with its assignment support.
///
/// # Support contract
///
/// `support` is the witness writer's assignment bitmask
/// (`ASSIGNED_WORDS_PER_COLUMN` words per column; bit `row % 64` of word
/// `column * ASSIGNED_WORDS_PER_COLUMN + row / 64` is set when the cell was
/// assigned, zero included). It describes *positions*, and for the fixed
/// writer schedule it is the same for every valid witness and never covers
/// the blinding tail `USABLE_ROWS_END..N` (pinned by
/// `advice_structural_support_census`; re-checked where the tail masks are
/// installed, in [`ProverPrefix::commit_advice`]). A commitment path may omit
/// unsupported cells, whose dense value is zero, but must include every
/// supported cell and every tail row once the masks are installed.
#[derive(Clone)]
pub(crate) struct AdviceMatrix {
    columns: [Buffer<Fp>; ADVICE_COLUMNS],
    support: [u64; ADVICE_COLUMNS * ASSIGNED_WORDS_PER_COLUMN],
}

/// Native state through the first prover challenge.
pub(crate) struct AdvicePrefix {
    /// Masked Lagrange columns; see the [ownership table](self#stage-buffer-ownership).
    values: Vec<Vec<SharedPoly>>,
    blinds: Vec<[Fp; ADVICE_COLUMNS]>,
    theta: Fp,
}

/// One lookup's compressed input and permuted columns in Lagrange form. The
/// compressed table side is witness-independent and shared across actions in
/// [`LookupPrefix::compressed_tables`].
#[derive(Clone)]
pub(crate) struct PermutedLookup {
    compressed_input: SharedPoly,
    permuted_input: SharedPoly,
    permuted_table: SharedPoly,
    input_blind: Fp,
    table_blind: Fp,
    input_commitment: VestaPoint,
    table_commitment: VestaPoint,
}

/// Native state through the lookup-permutation commitments and challenges.
pub(crate) struct LookupPrefix {
    lookups: Vec<[PermutedLookup; LOOKUPS_PER_ACTION]>,
    /// One θ-compressed table handle per lookup; see the
    /// [ownership table](self#stage-buffer-ownership) for sharing and release.
    compressed_tables: [SharedPoly; LOOKUPS_PER_ACTION],
    beta: Fp,
    gamma: Fp,
}

/// A base-domain column in evaluation (Lagrange) form: exactly `N` rows,
/// validated at construction. Dereferences to the shared buffer so consumers
/// read it like any polynomial, without a bare length-`N` vector standing in
/// for either of the two base forms.
struct LagrangeColumn(SharedPoly);

impl LagrangeColumn {
    fn new(values: SharedPoly) -> Result<Self, Error> {
        if values.len() != N {
            return Err(invariant::failed(Invariant::BaseDomainLength));
        }
        Ok(Self(values))
    }
}

impl core::ops::Deref for LagrangeColumn {
    type Target = SharedPoly;
    fn deref(&self) -> &SharedPoly {
        &self.0
    }
}

/// A base-domain polynomial in coefficient form: exactly `N` coefficients,
/// validated at construction.
struct BaseCoefficients(SharedPoly);

impl BaseCoefficients {
    fn new(coefficients: SharedPoly) -> Result<Self, Error> {
        if coefficients.len() != N {
            return Err(invariant::failed(Invariant::BaseDomainLength));
        }
        Ok(Self(coefficients))
    }
}

impl core::ops::Deref for BaseCoefficients {
    type Target = SharedPoly;
    fn deref(&self) -> &SharedPoly {
        &self.0
    }
}

/// Evaluations over the extended coset: exactly `EXTENDED_N` values as the
/// forward transform's finished tiles (eight base-domain rows blocks), valid
/// by construction. Readers index rows through the record or its borrowed
/// [`super::polynomial::FpCosetView`].
type ExtendedCoset = FpCosetTiles;

/// Evaluations over the 2N class coset — the extended coset's stride-4 rows
/// — as the forward transform's two finished tiles. The form of a
/// polynomial whose every quotient consumer folds on the 2N or N class.
type Class2NCoset = FpClass2NTiles;

/// A grand product's ready or deferred coset on its largest required class.
///
/// [`fold_order::permutation_product_class`] selects the extended coset for
/// full-width permutation sets, and 2N for the singleton set. Lookup products
/// use the extended coset. Deferred variants record only this class until
/// their quotient window needs the evaluations.
enum ProductCoset {
    Extended(ExtendedCoset),
    Class2N(Class2NCoset),
    /// Expand the retained coefficients only when their quotient window runs.
    /// Keeping every Action's cosets alive would defeat the window memory bound.
    Deferred(fold_order::DegreeClass),
}

impl ProductCoset {
    fn expand(
        self,
        coefficients: &[Fp],
        fft: &super::polynomial::PreparedFft,
        execution: super::worker::Execution<'_>,
    ) -> Result<Self, Error> {
        match self {
            Self::Deferred(class) => product_coset(coefficients, class, fft, execution),
            ready => Ok(ready),
        }
    }

    /// Takes a ready extended coset; deferred or differently sized cosets fail.
    fn into_extended(self) -> Result<ExtendedCoset, Error> {
        match self {
            Self::Extended(coset) => Ok(coset),
            Self::Class2N(_) | Self::Deferred(_) => Err(Error::InternalInvariant),
        }
    }

    /// Takes a ready 2N coset; deferred or differently sized cosets fail.
    fn into_class_2n(self) -> Result<Class2NCoset, Error> {
        match self {
            Self::Class2N(coset) => Ok(coset),
            Self::Extended(_) | Self::Deferred(_) => Err(Error::InternalInvariant),
        }
    }
}

/// A grand product's `N` coefficients and its ready or deferred class coset.
struct ProductPolynomialForms {
    coefficients: Buffer<Fp>,
    coset: ProductCoset,
}

/// The tests' bridge from a dense row-major vector to the residue-major
/// record, recording the length invariant it enforces.
#[cfg(test)]
fn extended_coset_from_dense_rows(values: Vec<Fp>) -> Result<ExtendedCoset, Error> {
    ExtendedCoset::from_dense_rows(&values)
        .ok_or_else(|| invariant::failed(Invariant::ExtendedDomainLength))
}

/// A grand product's checked staged/retained state; see the
/// [ownership table](self#stage-buffer-ownership) for transitions and release.
enum ProductForms {
    Staged(LagrangeColumn),
    Retained {
        coefficients: BaseCoefficients,
        coset: ProductCoset,
    },
}

/// What a committed grand product leaves for the openings once the quotient
/// fold has consumed its coset: the coefficient form and the blind.
pub(crate) struct ProductOpening {
    coefficients: BaseCoefficients,
    blind: Fp,
}

impl ProductForms {
    fn staged_rows(rows: impl Into<Buffer<Fp>>) -> Result<Self, Error> {
        Ok(Self::Staged(LagrangeColumn::new(SharedPoly::new(rows))?))
    }

    /// The staged Lagrange rows (before the forms are installed).
    fn staged(&self) -> Result<&LagrangeColumn, Error> {
        match self {
            Self::Staged(rows) => Ok(rows),
            Self::Retained { .. } => Err(Error::InternalInvariant),
        }
    }

    /// Replaces the staged rows with the transformed forms (once).
    fn install(&mut self, forms: ProductPolynomialForms) -> Result<(), Error> {
        match self {
            Self::Staged(_) => {
                *self = Self::Retained {
                    coefficients: BaseCoefficients::new(SharedPoly::new(forms.coefficients))?,
                    coset: forms.coset,
                };
                Ok(())
            }
            Self::Retained { .. } => Err(Error::InternalInvariant),
        }
    }

    /// The retained coefficient form (production readers receive it as a
    /// [`ProductOpening`] once the quotient stage has consumed the record).
    #[cfg(test)]
    fn coefficients(&self) -> Result<&BaseCoefficients, Error> {
        match self {
            Self::Retained { coefficients, .. } => Ok(coefficients),
            Self::Staged(_) => Err(Error::InternalInvariant),
        }
    }

    /// Splits retained forms into opening coefficients and a coset state.
    ///
    /// The quotient window must expand a deferred state before folding it.
    /// Coefficients and `blind` survive as opening data. Staged rows cannot split.
    fn into_opening(self, blind: Fp) -> Result<(ProductOpening, ProductCoset), Error> {
        match self {
            Self::Retained {
                coefficients,
                coset,
            } => Ok((
                ProductOpening {
                    coefficients,
                    blind,
                },
                coset,
            )),
            Self::Staged(_) => Err(Error::InternalInvariant),
        }
    }

    /// The retained coset as dense extended-coset rows: the extended record
    /// flattened, or a 2N/deferred product expanded from its coefficients
    /// (the dense reference every class form must agree with).
    #[cfg(test)]
    fn dense_coset(&self) -> Result<Vec<Fp>, Error> {
        match self {
            Self::Retained {
                coset: ProductCoset::Extended(coset),
                ..
            } => Ok(coset.to_dense_rows()),
            Self::Retained {
                coset: ProductCoset::Class2N(_) | ProductCoset::Deferred(_),
                coefficients,
            } => super::polynomial::base_coefficients_to_extended_coset(coefficients)
                .ok_or(Error::InternalInvariant),
            Self::Staged(_) => Err(Error::InternalInvariant),
        }
    }
}

/// Every Action's product openings, Action-major.
type ProductOpenings<const PER_ACTION: usize> = Vec<[ProductOpening; PER_ACTION]>;

/// Every Action's product cosets, Action-major, as the fold consumes them.
type ProductCosets<const PER_ACTION: usize> = Vec<[ProductCoset; PER_ACTION]>;

/// Splits every product of every Action into its opening data and its coset,
/// Action-major, consuming the stage records.
fn split_product_openings<P, const PER_ACTION: usize>(
    actions: Vec<[P; PER_ACTION]>,
    into_parts: impl Fn(P) -> Result<(ProductOpening, ProductCoset), Error>,
) -> Result<(ProductOpenings<PER_ACTION>, ProductCosets<PER_ACTION>), Error> {
    let mut openings = Vec::with_capacity(actions.len());
    let mut cosets = Vec::with_capacity(actions.len());
    for products in actions {
        // The validated prefixes carry exactly `PER_ACTION` products per
        // Action, so each Action's openings and cosets are fixed records.
        let mut action_openings: [Option<ProductOpening>; PER_ACTION] =
            core::array::from_fn(|_| None);
        let mut action_cosets: [Option<ProductCoset>; PER_ACTION] = core::array::from_fn(|_| None);
        for ((opening_slot, coset_slot), product) in action_openings
            .iter_mut()
            .zip(action_cosets.iter_mut())
            .zip(products)
        {
            let (opening, coset) = into_parts(product)?;
            *opening_slot = Some(opening);
            *coset_slot = Some(coset);
        }
        openings.push(action_openings.map(|slot| slot.expect("every product was split above")));
        cosets.push(action_cosets.map(|slot| slot.expect("every product was split above")));
    }
    Ok((openings, cosets))
}

/// One permutation chunk's grand-product polynomial and commitment.
pub(crate) struct PermutationProduct {
    forms: ProductForms,
    blind: Fp,
    commitment: VestaPoint,
    /// Interval description of the staged Lagrange rows for the commitment
    /// batch: the scan's ascending `(start row, value)` runs over the usable
    /// prefix (one per active row plus the trailing stretch), chain-scaled.
    /// The commitment reads one prefix-sum term per run plus the dense tail;
    /// an empty vector selects the dense fallback. See the
    /// [ownership table](self#stage-buffer-ownership) for release.
    interval_runs: Vec<(u32, Fp)>,
}

/// Native state through the permutation grand-product commitments: one
/// product per permutation set per Action.
pub(crate) struct PermutationPrefix {
    products: Vec<[PermutationProduct; PERMUTATION_SETS]>,
}

impl PermutationPrefix {
    fn new(products: Vec<[PermutationProduct; PERMUTATION_SETS]>) -> Self {
        Self { products }
    }
}

/// One lookup's grand-product polynomial and commitment.
pub(crate) struct LookupProduct {
    forms: ProductForms,
    blind: Fp,
    commitment: VestaPoint,
}

/// Native state through the lookup grand-product commitments: one product per
/// lookup per Action.
pub(crate) struct LookupProductPrefix {
    products: Vec<[LookupProduct; LOOKUPS_PER_ACTION]>,
}

impl LookupProductPrefix {
    fn new(products: Vec<[LookupProduct; LOOKUPS_PER_ACTION]>) -> Self {
        Self { products }
    }
}

/// Native state through the random vanishing-polynomial commitment and `y`.
pub(crate) struct VanishingPrefix {
    /// The linear mask `r(X) = r_0 + r_1·X` as `[r_0, r_1]`; every consumer
    /// treats it as the `N`-coefficient polynomial with a zero tail.
    mask: [Fp; 2],
    blind: Fp,
    y: Fp,
}

/// One quotient piece and its independently blinded commitment.
pub(crate) struct QuotientPiece {
    coefficients: SharedPoly,
    blind: Fp,
    commitment: VestaPoint,
}

/// Native state through quotient construction, commitments, and `x`.
///
/// Coefficient forms and opening blinds follow the
/// [ownership table](self#stage-buffer-ownership).
pub(crate) struct QuotientPrefix {
    pieces: Vec<QuotientPiece>,
    advice_coefficients: Vec<Vec<SharedPoly>>,
    advice_blinds: Vec<[Fp; ADVICE_COLUMNS]>,
    permuted_lookup_coefficients: Vec<[PermutedLookupCoefficients; LOOKUPS_PER_ACTION]>,
    /// The permutation grand products' openings, Action-major and
    /// set-ascending; see the [ownership table](self#stage-buffer-ownership).
    permutation_openings: ProductOpenings<{ fold_order::PERMUTATION_SET_COUNT }>,
    /// The lookup grand products' openings, Action-major and lookup-ascending.
    lookup_product_openings: ProductOpenings<{ fold_order::LOOKUP_COUNT }>,
    /// The IPA mask commitment's challenge-independent part, formed in this
    /// stage's piece batch and carried to `commit_ipa_mask`.
    ipa_mask: IpaMaskEarly,
    x: Fp,
}

/// Native state after every public polynomial evaluation is written and the
/// two multi-opening compression challenges are squeezed.
pub(crate) struct EvaluationPrefix {
    x_1: Fp,
    x_2: Fp,
}

struct PermutedLookupCoefficients {
    input: SharedPoly,
    table: SharedPoly,
    input_blind: Fp,
    table_blind: Fp,
}

/// Native state through the deterministic multi-opening collapse and `Q'`
/// commitment.
pub(crate) struct MultiopenPrefix {
    q_polynomials: Vec<SharedPoly>,
    q_blinds: Vec<Fp>,
    q_prime_polynomial: SharedPoly,
    q_prime_blind: Fp,
    x_3: Fp,
    ipa_mask: IpaMaskEarly,
}

/// The IPA mask commitment's challenge-independent part: the sparse
/// mask `s(X) = c + Σ_i α_i X^{2^i}` commits as
/// `Σ_i α_i·G_{2^i} + blind·W + c·G_0`, and only the constant
/// `c = −Σ_i α_i x_3^{2^i}` needs `x_3`, making `s(x_3) = 0`.
/// The first two terms are one small index-selected job in the
/// quotient stage's piece-commitment batch (its pre-sampled `α_i` and blind
/// travel with it); [`ProverPrefix::commit_ipa_mask`] adds `c·G_0` as one
/// prepared fixed-base multiplication. The transcript, RNG schedule, and the
/// point written are unchanged.
#[derive(Clone)]
pub(crate) struct IpaMaskEarly {
    commitment: VestaProjective,
    alphas: [Fp; crate::native::randomness::IPA_ROUNDS],
    blind: Fp,
}

/// Native state through the final multi-opening fold and sparse IPA mask
/// commitment, immediately before the recursive IPA rounds.
pub(crate) struct IpaMaskPrefix {
    x_3: Fp,
    polynomial: Buffer<Fp>,
    blind: Fp,
    mask: [(usize, Fp); super::target::K as usize + 1],
    mask_blind: Fp,
    xi: Fp,
    z: Fp,
}

/// One Action's lookup cosets the fold reads. The compressed input is not
/// among them: the fold evaluates it at each row from the Action's
/// advice cosets through the row's shared input-kernel coefficients.
#[derive(Clone)]
struct LookupCosets {
    /// Action-invariant because table expressions query only fixed columns
    /// and θ is common; sharing and release follow the
    /// [ownership table](self#stage-buffer-ownership).
    compressed_table: Arc<ExtendedCoset>,
    // Only even extended residues are produced: these columns' largest
    // consumer is the separate 4N lookup branch.
    permuted_input: ExtendedCoset,
    permuted_table: ExtendedCoset,
}

/// Dense coefficient and coset pair used by the independent test transforms.
#[cfg(test)]
struct PolynomialForms {
    coefficients: Buffer<Fp>,
    coset: ExtendedCoset,
}

#[cfg(test)]
impl PolynomialForms {
    /// Pairs `N` coefficients with their `EXTENDED_N` coset evaluations.
    fn new(coefficients: impl Into<Buffer<Fp>>, coset: ExtendedCoset) -> Result<Self, Error> {
        let coefficients = coefficients.into();
        if coefficients.len() != N {
            return Err(invariant::failed(Invariant::BaseDomainLength));
        }
        Ok(Self {
            coefficients,
            coset,
        })
    }
}

enum LagrangeFormInput {
    Dense(Buffer<Fp>),
    /// Lookup permuted columns, whose quotient consumers need only 4N.
    Dense4N(Buffer<Fp>),
    /// One Action's ten-field instance prefix, read from the prover's shared
    /// statement records.
    SparseInstance {
        statements: Arc<[NativeStatement]>,
        index: usize,
    },
}

impl<'a> ProverPrefix<'a> {
    /// The proof's Action count: the validated statement collection's length,
    /// fixed at initialization and independent of which stage payloads are
    /// still alive.
    fn action_count(&self) -> usize {
        self.statements.len()
    }

    #[cfg(test)]
    pub(crate) fn initialize(
        target: &'a FixedTarget,
        workspace: &'a mut super::ProverWorkspace,
        execution: super::worker::Execution<'a>,
        request: &ProvingRequest,
        statements: &[NativeStatement],
    ) -> Result<Self, Error> {
        let instances = statements
            .iter()
            .map(|statement| {
                let mut column = execution.buffer(N, true);
                column[..statement.len()].copy_from_slice(&statement[..]);
                SharedPoly::new(column)
            })
            .collect();
        Self::initialize_checked(
            target,
            workspace,
            execution,
            request,
            Arc::from(statements),
            instances,
        )
    }

    /// Accepts the statement records and N-row instances produced by witness
    /// construction/preflight. Shape mismatches here break that internal handoff;
    /// public/private relation failures have already been checked there.
    pub(crate) fn initialize_checked(
        target: &'a FixedTarget,
        workspace: &'a mut super::ProverWorkspace,
        execution: super::worker::Execution<'a>,
        request: &ProvingRequest,
        statements: Arc<[NativeStatement]>,
        instance_polynomials: Vec<SharedPoly>,
    ) -> Result<Self, Error> {
        if statements.len() != request.action_count()
            || instance_polynomials.len() != statements.len()
            || instance_polynomials.iter().any(|column| column.len() != N)
        {
            return Err(Error::InternalInvariant);
        }
        let proof_capacity = request.shape.proof_bytes;
        let mut transcript = Transcript::with_proof_capacity(proof_capacity);
        transcript.common_scalar(target.vk_representative());

        // The ten-field prefix handles exist for the prefix commitment alone
        // and end with it.
        let instance_prefixes = statements
            .iter()
            .map(|statement| &statement[..])
            .collect::<Vec<_>>();
        // NativeStatement fixes the prefix width; the prepared Lagrange bank
        // must accept these internally assembled commitment inputs.
        let pending_commitments = target
            .parameters()
            .commit_lagrange_prefix_batch_projective(
                &instance_prefixes,
                &<Fp>::ONE,
                &mut workspace.msm,
                execution,
            )
            .map_err(|_| Error::InternalInvariant)?;
        let instance_commitments = normalized(&pending_commitments);
        // The blind above is fixed at one. An identity here is classified as
        // an internal failure; fresh prover draws cannot change this common input.
        for commitment in &instance_commitments {
            transcript
                .common_point(commitment)
                .map_err(|_| Error::InternalInvariant)?;
        }

        Ok(Self {
            target,
            workspace,
            execution,
            instance_polynomials,
            statements,
            transcript,
        })
    }

    /// Consumes the prover, returning the completed proof bytes uncopied.
    pub(crate) fn into_proof(self) -> Vec<u8> {
        self.transcript.into_proof()
    }

    #[cfg(test)]
    pub(crate) fn transcript(&self) -> &Transcript {
        &self.transcript
    }
}

impl AdviceMatrix {
    /// Pairs dense columns with their assignment support, enforcing the
    /// support's shape (its exclusion of the blinding tail is a property of
    /// the fixed schedule, checked at the commitment boundary).
    pub(super) fn from_columns_with_support(
        columns: impl TryInto<[Buffer<Fp>; ADVICE_COLUMNS]>,
        support: impl TryInto<[u64; ADVICE_COLUMNS * ASSIGNED_WORDS_PER_COLUMN]>,
    ) -> Result<Self, Error> {
        let columns = columns.try_into().map_err(|_| Error::InternalInvariant)?;
        let support = support.try_into().map_err(|_| Error::InternalInvariant)?;
        if columns.iter().any(|column| column.len() != N) {
            return Err(Error::InternalInvariant);
        }
        Ok(Self { columns, support })
    }

    pub(crate) fn columns(&self) -> &[Buffer<Fp>] {
        &self.columns
    }

    /// The assignment support words, column-major (`ASSIGNED_WORDS_PER_COLUMN`
    /// per column), for a path that gathers supported cells.
    #[cfg(test)]
    pub(crate) fn support_words(&self) -> &[u64] {
        &self.support
    }
}

/// The support contract's shape check: `ADVICE_COLUMNS` columns of
/// `ASSIGNED_WORDS_PER_COLUMN` words with no bit set in the blinding tail
/// `USABLE_ROWS_END..N`.
fn support_excludes_tail(support: &[u64]) -> bool {
    support.len() == ADVICE_COLUMNS * ASSIGNED_WORDS_PER_COLUMN
        && support
            .chunks_exact(ASSIGNED_WORDS_PER_COLUMN)
            .all(|words| (USABLE_ROWS_END..N).all(|row| words[row / 64] >> (row % 64) & 1 == 0))
}

#[cfg(test)]
fn lagrange_to_forms(values: &[Fp]) -> Result<PolynomialForms, Error> {
    owned_lagrange_to_forms(
        values.to_vec(),
        crate::test_codec::target().fft(),
        crate::test_codec::execution(),
    )
}

#[cfg(test)]
fn owned_lagrange_to_forms(
    values: impl Into<Buffer<Fp>>,
    fft: &super::polynomial::PreparedFft,
    execution: super::worker::Execution<'_>,
) -> Result<PolynomialForms, Error> {
    let mut values = values.into();
    if values.len() != N || !fft.ifft(&mut values) {
        return Err(Error::InternalInvariant);
    }
    let coset = fft
        .coefficients::<8>(&values, execution.serial())
        .ok_or(Error::InternalInvariant)?;
    PolynomialForms::new(values, coset)
}

/// Converts one grand product's Lagrange rows to its retained forms: the `N`
/// coefficients and the coset on the class its consumers require — the
/// extended coset, or the 2N class coset for the singleton permutation set
/// ([`fold_order::permutation_product_class`]).
fn owned_lagrange_to_product_forms(
    (mut values, class): (Buffer<Fp>, fold_order::DegreeClass),
    fft: &super::polynomial::PreparedFft,
    execution: super::worker::Execution<'_>,
) -> Result<ProductPolynomialForms, Error> {
    if values.len() != N || !fft.ifft(&mut values) {
        return Err(Error::InternalInvariant);
    }
    let coset = product_coset(&values, class, fft, execution)?;
    Ok(ProductPolynomialForms {
        coefficients: values,
        coset,
    })
}

fn product_coset(
    values: &[Fp],
    class: fold_order::DegreeClass,
    fft: &super::polynomial::PreparedFft,
    execution: super::worker::Execution<'_>,
) -> Result<ProductCoset, Error> {
    match class {
        fold_order::DegreeClass::Extended => fft
            .coefficients::<8>(values, execution)
            .map(ProductCoset::Extended)
            .ok_or(Error::InternalInvariant),
        fold_order::DegreeClass::Class2N => fft
            .coefficients::<2>(values, execution)
            .map(ProductCoset::Class2N)
            .ok_or(Error::InternalInvariant),
        _ => Err(Error::InternalInvariant),
    }
}

/// The test compression oracle's coset columns, shared by Arc between tasks.
/// Advice columns are tiled records; `F` can own test vectors or borrow target
/// coset views. Target storage follows the
/// [ownership table](self#stage-buffer-ownership), including the current
/// `WarmUp` preparation policy.
#[cfg(test)]
struct CosetStack<F> {
    advice: Vec<Vec<ExtendedCoset>>,
    fixed: Vec<F>,
}

#[cfg(test)]
mod tests;
