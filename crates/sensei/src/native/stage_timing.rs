//! Opt-in test-only proof-stage attribution.

use std::{
    cell::{Cell, RefCell},
    time::Instant,
};

/// The proof's recorded stages, in pipeline order. Each variant documents
/// the work its interval actually covers: an interval runs from the previous
/// mark (or from `Recorder::begin`, taken after prover warmup) to its own
/// mark, so the first stage includes the upfront randomness sampling and the
/// last covers proof extraction and size validation. The token each variant
/// emits is the historical name the research parser and record read; the
/// tokens are stable, the descriptions are the truth.
#[derive(Clone, Copy)]
#[repr(usize)]
pub(crate) enum Stage {
    /// `witness`: drawing the whole randomness schedule, building every
    /// Action's advice matrix, and the preflight gate, copy, and lookup checks
    /// (see [`WitnessStage`] for the split).
    Witness = 0,
    /// `initialize`: the transcript and instance-polynomial commitments.
    Initialize,
    /// `advice`: advice column forms and commitments, θ.
    Advice,
    /// `lookup_permutations`: lookup compression, permutation construction,
    /// and the permuted-column commitments, β and γ.
    LookupPermutations,
    /// `product_arguments`: permutation and lookup grand products with their
    /// commitments (the preparation waves are also reported separately as
    /// `product_arguments.prepare`).
    ProductArguments,
    /// `vanishing`: the random vanishing polynomial's commitment, y.
    Vanishing,
    /// `quotient`: quotient construction through the piece commitments, x
    /// (see [`QuotientStage`] for the split).
    Quotient,
    /// `evaluations`: every opening evaluation written to the transcript.
    Evaluations,
    /// `multiopen_quotient`: the multiopen quotient commitment, x₃.
    MultiopenQuotient,
    /// `ipa_mask`: the IPA mask commitment and its challenges.
    IpaMask,
    /// `ipa_finish`: the eleven IPA rounds and the final scalars.
    IpaFinish,
    /// `proof_copy`: proof extraction from the transcript and the size
    /// validation — no copy is mandatory; the historical token is kept.
    ProofCopy,
}

impl Stage {
    /// Every stage, in recorded order.
    pub(crate) const ALL: [Self; 12] = [
        Self::Witness,
        Self::Initialize,
        Self::Advice,
        Self::LookupPermutations,
        Self::ProductArguments,
        Self::Vanishing,
        Self::Quotient,
        Self::Evaluations,
        Self::MultiopenQuotient,
        Self::IpaMask,
        Self::IpaFinish,
        Self::ProofCopy,
    ];

    /// The stage's stable output token.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::Witness => "witness",
            Self::Initialize => "initialize",
            Self::Advice => "advice",
            Self::LookupPermutations => "lookup_permutations",
            Self::ProductArguments => "product_arguments",
            Self::Vanishing => "vanishing",
            Self::Quotient => "quotient",
            Self::Evaluations => "evaluations",
            Self::MultiopenQuotient => "multiopen_quotient",
            Self::IpaMask => "ipa_mask",
            Self::IpaFinish => "ipa_finish",
            Self::ProofCopy => "proof_copy",
        }
    }
}

/// Stable caller-stage names in recorded order, derived from [`Stage`]; the
/// discriminants are checked to be the recorded positions.
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

thread_local! {
    static ENABLED: Cell<bool> = const { Cell::new(false) };
    static LAST: RefCell<Option<StageTimings>> = const { RefCell::new(None) };
    static LAST_QUOTIENT: RefCell<Option<QuotientTimings>> = const { RefCell::new(None) };
    static WITNESS: RefCell<Option<WitnessTimings>> = const { RefCell::new(None) };
    static PRODUCT_PREPARE_NS: Cell<u128> = const { Cell::new(0) };
    static IPA_NS: Cell<[u128; IPA_PHASE_COUNT]> = const { Cell::new([0; IPA_PHASE_COUNT]) };
    static IPA_EARLY_ROUNDS: Cell<usize> = const { Cell::new(0) };
}

/// The IPA finish's attributed round phases, reported as
/// `ipa_finish.<phase>` tokens of the stage line and summed over the eleven
/// rounds. `prepare` ends at the last field-preparation completion; MSM
/// work can already run during this interval. `batch` is the remaining tail
/// until the round's commitments are ready. `rounds` covers the shared scope,
/// including transcript challenges and round transitions. `generators` covers
/// materialization between scopes. These are wall-time intervals between
/// milestones, not exclusive arithmetic timings.
#[derive(Clone, Copy)]
#[repr(usize)]
pub(crate) enum IpaPhase {
    Prepare = 0,
    Batch,
    Rounds,
    Generators,
}

/// Number of [`IpaPhase`] tokens.
pub(crate) const IPA_PHASE_COUNT: usize = 4;

/// The IPA phase tokens, in [`IpaPhase`] order.
#[cfg_attr(
    not(feature = "verifier"),
    expect(
        dead_code,
        reason = "Timing reports are consumed by the full-feature benchmark harness."
    )
)]
pub(crate) const IPA_PHASE_NAMES: [&str; IPA_PHASE_COUNT] = [
    "ipa_finish.prepare",
    "ipa_finish.batch",
    "ipa_finish.rounds",
    "ipa_finish.generators",
];

/// Starts timing one IPA phase when attribution is enabled.
#[inline]
pub(crate) fn ipa_phase_start() -> Option<Instant> {
    ENABLED.with(Cell::get).then(Instant::now)
}

/// Attributes the interval since `started` to `phase`.
#[inline]
pub(crate) fn ipa_phase_finish(phase: IpaPhase, started: Option<Instant>) {
    if let Some(started) = started {
        let elapsed_ns = started.elapsed().as_nanos();
        IPA_NS.with(|elapsed| {
            let mut values = elapsed.get();
            values[phase as usize] += elapsed_ns;
            elapsed.set(values);
        });
    }
}

/// Adds intervals measured by a shared coordinator to the caller's recorder.
pub(crate) fn ipa_phase_add(phase: IpaPhase, ns: u128) {
    IPA_NS.with(|elapsed| {
        let mut values = elapsed.get();
        values[phase as usize] += ns;
        elapsed.set(values);
    });
}

/// Records rounds that admitted an MSM window before their final field task.
pub(crate) fn ipa_early_rounds(rounds: usize) {
    IPA_EARLY_ROUNDS.with(|value| value.set(rounds));
}

/// The quotient stage's recorded substages, in order. (Fusing the gate,
/// permutation, lookup, and class folds into one classed row pass and
/// replacing the telescope conversion with tiled interpolation changed the
/// former `gate_constraints`/`permutation_constraints`/`lookup_constraints`
/// substages to `constraint_fold` and `numerator_conversion` to
/// `interpolation`.)
#[derive(Clone, Copy)]
#[repr(usize)]
pub(crate) enum QuotientStage {
    /// `forms`: through the last column expansion and table compression;
    /// residue folds and smaller class inverses can already run here.
    Forms = 0,
    /// `lookup_forms`: the immediate mark after `forms`; table compression
    /// participates in that shared interval.
    LookupForms,
    /// `constraint_fold`: the remaining tail through the last residue scatter.
    ConstraintFold,
    /// `interpolation`: the remaining tail through the last coefficient lift;
    /// completed pieces can already enter their MSMs.
    Interpolation,
    /// `piece_commitments`: the piece commitments and their transcript
    /// writes.
    PieceCommitments,
}

impl QuotientStage {
    /// Every substage, in recorded order.
    pub(crate) const ALL: [Self; 5] = [
        Self::Forms,
        Self::LookupForms,
        Self::ConstraintFold,
        Self::Interpolation,
        Self::PieceCommitments,
    ];

    /// The substage's stable output token.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::Forms => "forms",
            Self::LookupForms => "lookup_forms",
            Self::ConstraintFold => "constraint_fold",
            Self::Interpolation => "interpolation",
            Self::PieceCommitments => "piece_commitments",
        }
    }
}

/// Quotient substage names in recorded order, derived from
/// [`QuotientStage`].
pub(crate) const QUOTIENT_NAMES: [&str; QuotientStage::ALL.len()] = {
    let mut names = [""; QuotientStage::ALL.len()];
    let mut index = 0;
    while index < names.len() {
        assert!(QuotientStage::ALL[index] as usize == index);
        names[index] = QuotientStage::ALL[index].name();
        index += 1;
    }
    names
};

/// The witness stage's recorded substages, in order, each summed over the
/// Actions. (`fixed_setup` was retired because preflight setup is now a
/// warm static deref whose duration quantizes to zero and would poison
/// geometric means.)
#[derive(Clone, Copy)]
#[repr(usize)]
pub(crate) enum WitnessStage {
    /// `construction`: the witness writers and matrix finalization for every
    /// Action (one pool task per Action).
    Construction = 0,
    /// `action_setup`: the native instance column per Action.
    ActionSetup,
    /// `gates`: the sparse gate checks.
    Gates,
    /// `copies`: the equality-constraint checks.
    Copies,
    /// `lookups`: lookup input evaluation with membership checking.
    Lookups,
}

impl WitnessStage {
    /// Every substage, in recorded order.
    pub(crate) const ALL: [Self; 5] = [
        Self::Construction,
        Self::ActionSetup,
        Self::Gates,
        Self::Copies,
        Self::Lookups,
    ];

    /// The substage's stable output token.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::Construction => "construction",
            Self::ActionSetup => "action_setup",
            Self::Gates => "gates",
            Self::Copies => "copies",
            Self::Lookups => "lookups",
        }
    }
}

/// Witness and preflight substage names in recorded order, derived from
/// [`WitnessStage`].
pub(crate) const WITNESS_NAMES: [&str; WitnessStage::ALL.len()] = {
    let mut names = [""; WitnessStage::ALL.len()];
    let mut index = 0;
    while index < names.len() {
        assert!(WitnessStage::ALL[index] as usize == index);
        names[index] = WitnessStage::ALL[index].name();
        index += 1;
    }
    names
};

/// Durations for one successful native proof, in [`NAMES`] order.
#[cfg_attr(
    not(feature = "verifier"),
    expect(
        dead_code,
        reason = "Timing reports are consumed by the full-feature benchmark harness."
    )
)]
pub(crate) struct StageTimings {
    /// Per-stage elapsed nanoseconds.
    pub(crate) elapsed_ns: [u128; NAMES.len()],
    /// Elapsed nanoseconds of the product-argument preparation waves (the
    /// permutation grand products ahead of the first commitment batch),
    /// reported as the `product_arguments.prepare` token of the stage line.
    pub(crate) product_prepare_ns: u128,
    /// Elapsed nanoseconds of the IPA round phases, in [`IpaPhase`] order,
    /// reported as the [`IPA_PHASE_NAMES`] tokens of the stage line.
    pub(crate) ipa_ns: [u128; IPA_PHASE_COUNT],
    /// Rounds admitting an MSM window before all field preparation completed.
    pub(crate) ipa_early_rounds: usize,
}

/// Timings for one quotient construction.
#[cfg_attr(
    not(feature = "verifier"),
    expect(
        dead_code,
        reason = "Timing reports are consumed by the full-feature benchmark harness."
    )
)]
pub(crate) struct QuotientTimings {
    /// Sum of complete fold-task durations, including work overlapping forms.
    pub(crate) fold_work_ns: u128,
    /// Per-substage elapsed nanoseconds.
    pub(crate) elapsed_ns: [u128; QUOTIENT_NAMES.len()],
    /// Fold, inverse, and piece-MSM tasks admitted before the preceding
    /// operation finished all of its independent outputs.
    pub(crate) early_consumers: [usize; 3],
}

/// Timings for one witness construction and preflight pass.
pub(crate) struct WitnessTimings {
    /// Per-substage elapsed nanoseconds.
    pub(crate) elapsed_ns: [u128; WITNESS_NAMES.len()],
}

/// Enables attribution for the next proof on this thread.
pub(crate) fn enable() {
    LAST.with(|last| assert!(last.borrow().is_none()));
    LAST_QUOTIENT.with(|last| assert!(last.borrow().is_none()));
    WITNESS.with(|timings| {
        let mut timings = timings.borrow_mut();
        assert!(timings.is_none());
        *timings = Some(WitnessTimings {
            elapsed_ns: [0; WITNESS_NAMES.len()],
        });
    });
    PRODUCT_PREPARE_NS.with(|elapsed| elapsed.set(0));
    IPA_NS.with(|elapsed| elapsed.set([0; IPA_PHASE_COUNT]));
    IPA_EARLY_ROUNDS.with(|value| value.set(0));
    ENABLED.with(|enabled| enabled.set(true));
}

/// Disables attribution and returns the last successful proof's timings.
pub(crate) fn take() -> Option<StageTimings> {
    ENABLED.with(|enabled| enabled.set(false));
    LAST.with(|last| last.borrow_mut().take())
}

/// Returns the last successful proof's quotient attribution.
pub(crate) fn take_quotient() -> Option<QuotientTimings> {
    LAST_QUOTIENT.with(|last| last.borrow_mut().take())
}

/// Returns the last successful proof's witness attribution.
pub(crate) fn take_witness() -> Option<WitnessTimings> {
    WITNESS.with(|timings| timings.borrow_mut().take())
}

/// Measures one complete witness substage when attribution is enabled.
pub(crate) fn measure_witness<T>(stage: WitnessStage, operation: impl FnOnce() -> T) -> T {
    let started = ENABLED.with(Cell::get).then(Instant::now);
    let result = operation();
    if let Some(started) = started {
        let elapsed_ns = started.elapsed().as_nanos();
        WITNESS.with(|timings| {
            let mut timings = timings.borrow_mut();
            let timings = timings
                .as_mut()
                .expect("enabled proof must have witness timings");
            timings.elapsed_ns[stage as usize] += elapsed_ns;
        });
    }
    result
}

/// Measures the product-argument preparation when attribution is enabled.
pub(crate) fn measure_product_prepare<T>(operation: impl FnOnce() -> T) -> T {
    let started = ENABLED.with(Cell::get).then(Instant::now);
    let result = operation();
    if let Some(started) = started {
        let elapsed_ns = started.elapsed().as_nanos();
        PRODUCT_PREPARE_NS.with(|elapsed| elapsed.set(elapsed.get() + elapsed_ns));
    }
    result
}

pub(super) struct Recorder {
    last: Option<Instant>,
    elapsed_ns: [u128; NAMES.len()],
}

impl Recorder {
    pub(super) fn begin() -> Self {
        Self {
            last: ENABLED.with(Cell::get).then(Instant::now),
            elapsed_ns: [0; NAMES.len()],
        }
    }

    /// Closes the interval that began at the previous mark (or at `begin`)
    /// and attributes it to `stage`.
    pub(super) fn mark(&mut self, stage: Stage) {
        if let Some(last) = self.last {
            let now = Instant::now();
            self.elapsed_ns[stage as usize] += now.duration_since(last).as_nanos();
            self.last = Some(now);
        }
    }

    pub(super) fn finish(self) {
        if self.last.is_some() {
            LAST.with(|last| {
                *last.borrow_mut() = Some(StageTimings {
                    elapsed_ns: self.elapsed_ns,
                    product_prepare_ns: PRODUCT_PREPARE_NS.with(|elapsed| elapsed.replace(0)),
                    ipa_ns: IPA_NS.with(|elapsed| elapsed.replace([0; IPA_PHASE_COUNT])),
                    ipa_early_rounds: IPA_EARLY_ROUNDS.with(|value| value.replace(0)),
                });
            });
        }
    }
}

pub(super) struct QuotientRecorder {
    pub(super) fold_work_ns: u128,
    last: Option<Instant>,
    elapsed_ns: [u128; QUOTIENT_NAMES.len()],
    pub(super) early_consumers: [usize; 3],
}

impl QuotientRecorder {
    pub(super) fn begin() -> Self {
        Self {
            fold_work_ns: 0,
            last: ENABLED.with(Cell::get).then(Instant::now),
            elapsed_ns: [0; QUOTIENT_NAMES.len()],
            early_consumers: [0; 3],
        }
    }

    /// Closes the interval that began at the previous mark (or at `begin`)
    /// and attributes it to `stage`.
    pub(super) fn mark(&mut self, stage: QuotientStage) {
        if let Some(last) = self.last {
            let now = Instant::now();
            self.elapsed_ns[stage as usize] += now.duration_since(last).as_nanos();
            self.last = Some(now);
        }
    }

    pub(super) fn finish(self) {
        if self.last.is_some() {
            LAST_QUOTIENT.with(|last| {
                *last.borrow_mut() = Some(QuotientTimings {
                    fold_work_ns: self.fold_work_ns,
                    elapsed_ns: self.elapsed_ns,
                    early_consumers: self.early_consumers,
                });
            });
        }
    }
}

/// Moves attribution with a proof while preserving a worker's previous state.
#[derive(Default)]
pub(super) struct Context {
    enabled: bool,
    last: Option<StageTimings>,
    quotient: Option<QuotientTimings>,
    witness: Option<WitnessTimings>,
    product: u128,
    ipa: [u128; IPA_PHASE_COUNT],
    ipa_early: usize,
}

impl Context {
    fn take() -> Self {
        Self {
            enabled: ENABLED.with(|value| value.replace(false)),
            last: LAST.with(|value| value.take()),
            quotient: LAST_QUOTIENT.with(|value| value.take()),
            witness: WITNESS.with(|value| value.take()),
            product: PRODUCT_PREPARE_NS.with(|value| value.replace(0)),
            ipa: IPA_NS.with(|value| value.replace([0; IPA_PHASE_COUNT])),
            ipa_early: IPA_EARLY_ROUNDS.with(|value| value.replace(0)),
        }
    }

    fn apply(self) {
        ENABLED.with(|value| value.set(self.enabled));
        LAST.with(|value| *value.borrow_mut() = self.last);
        LAST_QUOTIENT.with(|value| *value.borrow_mut() = self.quotient);
        WITNESS.with(|value| *value.borrow_mut() = self.witness);
        PRODUCT_PREPARE_NS.with(|value| value.set(self.product));
        IPA_NS.with(|value| value.set(self.ipa));
        IPA_EARLY_ROUNDS.with(|value| value.set(self.ipa_early));
    }

    pub(super) fn transfer<R>(work: impl FnOnce(&mut Self) -> R) -> R {
        struct Restore(Context);
        impl Drop for Restore {
            fn drop(&mut self) {
                std::mem::take(&mut self.0).apply();
            }
        }
        let mut restore = Restore(Self::take());
        work(&mut restore.0)
    }

    pub(super) fn enter<R>(&mut self, work: impl FnOnce() -> R) -> R {
        struct Restore<'a> {
            output: &'a mut Context,
            previous: Context,
        }
        impl Drop for Restore<'_> {
            fn drop(&mut self) {
                *self.output = Context::take();
                std::mem::take(&mut self.previous).apply();
            }
        }
        let previous = Self::take();
        std::mem::take(self).apply();
        let _restore = Restore {
            output: self,
            previous,
        };
        work()
    }
}
