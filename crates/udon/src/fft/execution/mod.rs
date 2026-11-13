//! Transform plans for scoped execution or incremental task scheduling.
//!
//! [`FftPlan::execute`], [`ExpansionPlan::execute`], and
//! [`InterpolationPlan::execute`] drive contiguous buffers on a caller's
//! [`Executor`](crate::exec::Executor). Their corresponding run types expose
//! individual tasks over exclusively leased field fragments.
//!
//! Tasks operate on local tiles, pairs of tiles, or explicitly sized column
//! panels. Stage barriers belong to a single run, so a small transform does not
//! wait for other transforms. Fields preserve their loose representation bound
//! throughout execution, including on unwind. Reordering uses a retained
//! snapshot with bounded copy and gather tasks, or bounded swaps when the
//! provider can lease a contiguous bank.

use core::{num::NonZeroUsize, ops::Range};

use super::{
    Codelet, Direction, Domain, ElementOrder, FftError, InputStorage, InputSupport, InverseScale,
    PastaField, PrimeModulus, Transform, TransformRequest, TwiddleTable, bit_reverse,
    factors::ForwardShift,
    stages::{StageKernel, twiddle_table},
};
use crate::exec::{
    SerialExecutor,
    execution::{
        Completion, Frontier, Identity, Kernel, Outcome, ReadView, Task, TaskError, TaskKey,
        TaskStorage,
    },
};

mod expansion;
pub use expansion::{
    ExpansionBank, ExpansionPlan, ExpansionPublished, ExpansionRequest, ExpansionRun,
};
mod interpolation;
pub use interpolation::{
    AdditionKernel, AdditionRequest, InterpolationPlan, InterpolationPublished, InterpolationRun,
};
mod driver;

/// Worker-independent tile geometry and transform semantics.
///
/// Use [`Self::execute`] for one contiguous transform, [`Self::execute_batch`]
/// for consecutive polynomials, or [`FftRun`] for incremental scheduling.
/// Plans borrow tables for `'t` and can be reused with new working buffers.
/// The underlying [`Transform`] binds the domain and tables; this plan adds storage,
/// ordering, normalization, and task geometry. An [`FftRun`] binds one invocation
/// to frontier storage; it does not extend the lifetime of borrowed tables.
#[derive(Clone, Copy, Debug)]
pub struct FftPlan<'t, M: PrimeModulus> {
    plan: Transform<'t, M>,
    request: TransformRequest,
    tile: usize,
    codelet: Codelet,
    twiddles: Option<TwiddleTable<'t, M>>,
    input_scale: PastaField<M>,
    shift: ForwardShift<M>,
    residue_scales: Option<&'t [PastaField<M>]>,
    columns: Option<(usize, usize)>,
    contiguous_permutation: bool,
    scatter_input: bool,
    resume: Option<(usize, ElementOrder)>,
    budget: crate::exec::TaskBudget,
    memory_limit: Option<usize>,
}

impl<'t, M: PrimeModulus> FftPlan<'t, M> {
    /// Resolves a transform using its mathematical request and available storage.
    ///
    /// Udon selects kernels, subdivisions, and intermediate storage. The plan
    /// borrows tables, binds no working buffers, and fixes the workspace reported
    /// by [`Self::retained_fields`]. Execution requires that workspace even when
    /// another implementation could use less.
    ///
    /// Prefix lengths range from zero through the domain size; larger prefixes
    /// return [`FftError::InvalidPrefix`]. Bit-reversed prefix input, an unscaled
    /// forward request, or a non-power-of-two fragment length returns
    /// [`FftError::InvalidExecution`]. Fragment lengths are clamped to the domain
    /// size after validation. Required workspace exceeding the byte ceiling
    /// returns [`FftError::MemoryLimit`]. Construction does not write storage.
    pub fn new(
        plan: Transform<'t, M>,
        request: TransformRequest,
        storage: super::StorageLayout,
        options: crate::exec::ExecutionOptions,
    ) -> Result<Self, FftError> {
        let size = plan.domain().size();
        let (tile, whole_bank) = match storage {
            super::StorageLayout::Contiguous => (
                super::Strategy::select(size, options, usize::MAX)
                    .tile_len
                    .min(size),
                true,
            ),
            super::StorageLayout::Fragments { length, whole_bank } => {
                if !length.is_power_of_two() {
                    return Err(FftError::InvalidExecution);
                }
                (length.get().min(size), whole_bank)
            }
        };
        let mut result = Self::with_strategy(
            plan,
            request,
            NonZeroUsize::new(tile).unwrap(),
            Codelet::Radix2,
        )?;
        result.budget = options.task_budget();
        result.memory_limit = options.memory_limit();
        result.contiguous_permutation = whole_bank;
        // Panels change the native order as well as scratch use. Compare complete
        // layouts so an order conversion cannot escape the workspace ceiling.
        if result.fragments() > 1
            && let Some((columns, panels)) =
                super::Strategy::columns(tile, result.fragments(), options, usize::MAX)
        {
            let candidate = result.with_columns(
                NonZeroUsize::new(columns).unwrap(),
                NonZeroUsize::new(panels).unwrap(),
            )?;
            if options.memory_limit().is_none_or(|limit| {
                candidate.retained_fields() <= limit / core::mem::size_of::<PastaField<M>>()
            }) {
                result = candidate;
            }
        }
        if let Some(limit) = options.memory_limit() {
            let required = result.retained_fields() * core::mem::size_of::<PastaField<M>>();
            if required > limit {
                return Err(FftError::MemoryLimit { required, limit });
            }
        }
        Ok(result)
    }

    /// Validates the mathematical request and power-of-two tile size.
    ///
    /// The request selects in-place or preserved separate input. `tile` must
    /// be a power of two and is clamped to the domain size. It limits local
    /// transforms and half the fields in a paired stage task.
    ///
    /// Prefix lengths may range from zero through the domain size; larger
    /// prefixes return [`FftError::InvalidPrefix`]. A bit-reversed prefix,
    /// unscaled forward transform, or non-power-of-two tile returns
    /// [`FftError::InvalidExecution`]. No storage is bound or modified. Tables in
    /// `plan` remain borrowed across runs.
    pub(in crate::fft) fn with_strategy(
        plan: Transform<'t, M>,
        request: TransformRequest,
        tile: NonZeroUsize,
        codelet: Codelet,
    ) -> Result<Self, FftError> {
        let size = plan.domain().size();
        let input = request.input_len(size);
        if input > size {
            return Err(FftError::InvalidPrefix {
                min: 0,
                max: size,
                actual: input,
            });
        }
        if !tile.is_power_of_two()
            || (matches!(request.support, InputSupport::Prefix(_))
                && request.input_order == ElementOrder::BitReversed)
            || (request.direction == Direction::Forward
                && request.inverse_scale == InverseScale::Unscaled)
        {
            return Err(FftError::InvalidExecution);
        }
        Ok(Self {
            plan,
            request,
            tile: tile.get().min(plan.domain().size()),
            codelet,
            twiddles: None,
            input_scale: PastaField::ONE,
            shift: ForwardShift::for_domain(plan.domain()),
            residue_scales: None,
            columns: None,
            contiguous_permutation: false,
            scatter_input: false,
            resume: None,
            budget: crate::exec::TaskBudget::SERIAL,
            memory_limit: None,
        })
    }

    pub(in crate::fft) fn resume(mut self, first: usize, input_order: ElementOrder) -> Self {
        self.resume = Some((first, input_order));
        self.request.input_order = input_order;
        self
    }

    /// Selects an already bound dense or stage-packed twiddle table.
    ///
    /// Either root direction supplies both transform directions. A smaller table
    /// covers local stages; larger stages compute their powers. Without this
    /// override, tasks use `plan`'s tables or computed recurrence.
    pub fn with_twiddles(mut self, table: TwiddleTable<'t, M>) -> Self {
        self.twiddles = Some(table);
        self
    }

    /// Multiplies forward coefficients by a common factor before transforming.
    ///
    /// This supports retained unscaled inverse coefficients without a separate
    /// normalization pass. Panics for an inverse transform.
    pub fn with_input_scale(mut self, scale: PastaField<M>) -> Self {
        assert!(
            !self.inverse(),
            "input scaling requires a forward transform"
        );
        self.input_scale = scale;
        self
    }

    pub(in crate::fft) fn with_residue_scales(
        mut self,
        expansion: super::Expansion<'t, M>,
        residue: usize,
        mut scale: PastaField<M>,
    ) -> Self {
        self.shift = expansion.residue_shift(residue);
        self.residue_scales = expansion
            .scales
            .map(|scales| &scales[residue * self.size()..(residue + 1) * self.size()]);
        if self.residue_scales.is_some()
            && expansion.normalization == super::ExpansionScaleNormalization::UnscaledInverse
        {
            // The table already divides by the base size. Cancel that factor
            // here so the input's own normalization is applied exactly once.
            scale = scale.mul(&PastaField::<M>::from_u64(self.size() as u64));
        }
        self.with_input_scale(scale)
    }

    /// Selects bounded column panels after local transforms.
    ///
    /// `columns` is clamped to the local tile; a final panel may be shorter.
    /// `panels` bounds retained results, independently of worker count, and is
    /// clamped to the number of panels in that tile. Each task gathers and
    /// transforms at most `columns * fragments()` fields. A band scatters only
    /// after its readers finish; other runs remain independently schedulable.
    ///
    /// Returns [`FftError::SizeOverflow`] if the retained field count overflows
    /// `usize` or its field slice would exceed `isize::MAX` bytes.
    /// A single-fragment transform keeps its local kernel without panels.
    pub(in crate::fft) fn with_columns(
        mut self,
        columns: NonZeroUsize,
        panels: NonZeroUsize,
    ) -> Result<Self, FftError> {
        let columns = columns.get().min(self.tile);
        let panels = panels.get().min(self.tile.div_ceil(columns));
        let fields = columns
            .checked_mul(panels)
            .and_then(|n| n.checked_mul(self.fragments()))
            .ok_or(FftError::SizeOverflow)?;
        super::check_field_count(fields)?;
        if self.fragments() > 1 {
            self.columns = Some((columns, panels));
        }
        Ok(self)
    }

    /// Converts physical order by swapping indices within a contiguous bank.
    ///
    /// Each task leases the whole values bank exclusively. This avoids a full
    /// retained snapshot, at the cost of serializing permutation tasks for this run.
    /// Other phases still use bounded fragment leases.
    pub(in crate::fft) fn with_contiguous_permutation(mut self) -> Self {
        self.contiguous_permutation = true;
        self
    }

    /// Visits separate input in consecutive tiles and scatters to working order.
    ///
    /// Each initialization task reads at most [`Self::tile`] input positions
    /// and exclusively leases the whole contiguous destination bank. This
    /// serializes initialization for this run, while other runs remain ready.
    /// Sparse initialization retains its fused broadcast optimization. In-place
    /// execution is unchanged. Without this option, tasks gather into disjoint
    /// destination tiles.
    #[cfg(test)]
    pub(in crate::fft) fn with_scatter_initialization(mut self) -> Self {
        self.scatter_input = true;
        self
    }

    /// Size of each writable fragment; it divides the transform size.
    pub fn tile(&self) -> usize {
        self.tile
    }

    /// Number of writable fragments.
    pub fn fragments(&self) -> usize {
        self.size() / self.tile
    }

    /// Transform size in field elements.
    pub fn size(&self) -> usize {
        self.plan.domain().size()
    }

    /// Additional fields for order conversion and column-panel results.
    ///
    /// These phases reuse the same storage. [`Self::execute`] requires at least
    /// this many scratch entries. Incremental scheduling must retain this bank
    /// across tasks; admission also counts the full provisioned capacity, run,
    /// guard, and frontier metadata, and any intermediate transform values.
    pub fn retained_fields(&self) -> usize {
        if self.fragments() == 1 {
            return 0;
        }
        let snapshot = if !self.contiguous_permutation
            && ((!self.separate() && self.pre_reverse()) || self.post_reverse())
        {
            self.size()
        } else {
            0
        };
        snapshot.max(
            self.columns
                .map_or(0, |(columns, panels)| columns * panels * self.fragments()),
        )
    }

    fn separate(&self) -> bool {
        self.request.input_storage == InputStorage::Preserve
    }

    fn inverse(&self) -> bool {
        self.request.direction == Direction::Inverse
    }
    fn native_input(&self) -> ElementOrder {
        if let Some((_, order)) = self.resume {
            return order;
        }
        if self.inverse()
            || self.columns.is_some()
            || self.fragments() == 1 && self.request.output_order == ElementOrder::Natural
            || self.separate()
                && matches!(self.request.support, InputSupport::Prefix(n) if n <= self.size() / 16)
        {
            ElementOrder::BitReversed
        } else {
            ElementOrder::Natural
        }
    }
    fn native_output(&self) -> ElementOrder {
        if self.native_input() == ElementOrder::BitReversed {
            ElementOrder::Natural
        } else {
            ElementOrder::BitReversed
        }
    }
    fn pre_reverse(&self) -> bool {
        self.request.input_order != self.native_input()
    }
    fn post_reverse(&self) -> bool {
        self.request.output_order != self.native_output()
    }
    fn column_normalized(&self) -> bool {
        self.columns.is_some()
            && self.inverse()
            && self.first() <= self.size()
            && self.request.inverse_scale == InverseScale::Normalized
    }
    fn sparse(&self) -> bool {
        self.separate()
            && matches!(self.request.support, InputSupport::Prefix(_))
            && self.native_input() == ElementOrder::BitReversed
    }
    fn first(&self) -> usize {
        if let Some((first, _)) = self.resume {
            return first;
        }
        if self.sparse() {
            self.size()
                / self
                    .request
                    .input_len(self.size())
                    .max(1)
                    .next_power_of_two()
                * 2
        } else {
            2
        }
    }
    fn twist(&self) -> bool {
        self.resume.is_none()
            && !self.inverse()
            && (!self.shift.is_identity()
                || self.input_scale.reduce() != PastaField::<M>::ONE.reduce()
                || self.residue_scales.is_some())
    }
    fn twist_before_permute(&self) -> bool {
        !self.separate() && self.pre_reverse() && self.twist()
    }
    fn permutation(&self) -> WorkKind {
        if self.contiguous_permutation {
            WorkKind::Permute
        } else {
            WorkKind::Snapshot
        }
    }

    fn initial(&self) -> (WorkKind, usize) {
        if self.fragments() == 1 {
            (WorkKind::Fused, 0)
        } else if self.resume.is_some() {
            if self.first() > self.size() {
                (WorkKind::Finish, 0)
            } else if self.native_input() == ElementOrder::BitReversed {
                (WorkKind::Local, 0)
            } else {
                (WorkKind::Pair, self.size())
            }
        } else if self.separate() || matches!(self.request.support, InputSupport::Prefix(_)) {
            (
                if self.separate() && self.scatter_input && !self.sparse() {
                    WorkKind::InitializeScatter
                } else {
                    WorkKind::Initialize
                },
                0,
            )
        } else if self.twist_before_permute() {
            (WorkKind::Twist, 0)
        } else if self.pre_reverse() {
            (self.permutation(), 0)
        } else if self.twist() {
            (WorkKind::Twist, 0)
        } else if self.inverse() || self.columns.is_some() || self.fragments() == 1 {
            (WorkKind::Local, 0)
        } else {
            (WorkKind::Pair, self.size())
        }
    }
}

/// A physical bank named by an FFT resource request.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Bank {
    /// Original shared input, present only for separate-output execution.
    Input,
    /// Writable transform fragments.
    Values,
    /// Retained snapshot used for order conversion.
    Snapshot,
}

/// A bounded FFT kernel family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum WorkKind {
    /// Complete a transform that fits one local tile, fusing its phases.
    Fused,
    /// Initialize a destination tile, zeroing unsupported input positions.
    Initialize,
    /// Scatter one input tile while exclusively leasing the whole destination.
    InitializeScatter,
    /// Copy a tile into a retained snapshot.
    Snapshot,
    /// Gather a bit-reversed tile from the completed snapshot.
    Reorder,
    /// Swap a bounded set of bit-reversed indices in a whole-bank lease.
    Permute,
    /// Apply forward coset powers to one tile.
    Twist,
    /// Perform a local transform, including the selected small codelets.
    Local,
    /// Perform one stage on a pair of tiles.
    Pair,
    /// Gather and transform a bounded column-major retained panel.
    Column,
    /// Scatter one row fragment from a completed panel band.
    Scatter,
    /// Apply inverse normalization and coset powers, or a terminal product.
    Finish,
}

/// One ready task and its entire field-access bundle.
#[derive(Clone, Debug)]
pub struct Request<'a> {
    /// Nonforgeable claim identity.
    pub key: TaskKey<'a>,
    #[cfg(test)]
    kind: WorkKind,
    /// Bank and global range of the first exclusive output fragment.
    pub write: (Bank, Range<usize>),
    /// Second exclusive fragment for a butterfly pair.
    pub pair: Option<Range<usize>>,
    /// Shared input bank and required global range, if any.
    pub read: Option<(Bank, Range<usize>)>,
    /// Shared terminal product input in requested physical output order.
    pub factor: Option<Range<usize>>,
}

/// Transient kernel views, indexed relative to the requested ranges.
///
/// The direct [`Resources`] implementation supports local task execution.
/// Erased [`ReadView`] references need not be `Sync`, so this bundle is not a
/// transferable owner. To send a task to a worker, own typed borrowed slices or
/// movable guards and construct these views in [`Resources::buffers`] there.
pub struct Buffers<'a, M: PrimeModulus> {
    /// Exclusive first fragment, exactly the requested range length.
    pub values: &'a mut [PastaField<M>],
    /// Exclusive paired fragment, empty for single-fragment work.
    pub pair: &'a mut [PastaField<M>],
    /// Shared input view for the request's read range.
    pub source: &'a dyn ReadView<PastaField<M>>,
    /// Shared terminal product view for the requested factor range.
    pub factor: &'a dyn ReadView<PastaField<M>>,
}

/// Owned safe fragments or movable application lease guards.
///
/// Views must name the initialized banks and ranges in the claimed request.
/// Violations can panic or invalidate arithmetic but cannot violate memory safety.
pub trait Resources<M: PrimeModulus> {
    /// Borrows this task's complete bundle until the bounded kernel returns.
    fn buffers(&mut self) -> Buffers<'_, M>;
}

impl<M: PrimeModulus> Resources<M> for Buffers<'_, M> {
    fn buffers(&mut self) -> Buffers<'_, M> {
        Buffers {
            values: self.values,
            pair: self.pair,
            source: self.source,
            factor: self.factor,
        }
    }
}

/// Detached FFT arithmetic, constructed by [`FftRun::try_claim`].
pub struct FftKernel<'t, M: PrimeModulus> {
    plan: FftPlan<'t, M>,
    kind: WorkKind,
    start: usize,
    block: usize,
    product: bool,
    column: usize,
    band: usize,
}

impl<M: PrimeModulus> FftKernel<'_, M> {
    fn run(&self, buffers: Buffers<'_, M>) {
        let Buffers {
            values,
            pair,
            source,
            factor,
        } = buffers;
        let plan = self.plan;
        let tile = plan.tile;
        let fields = match self.kind {
            WorkKind::Permute | WorkKind::InitializeScatter => plan.size(),
            WorkKind::Column => plan.columns.unwrap().0.min(tile - self.column) * plan.fragments(),
            WorkKind::Scatter => self.band,
            _ => tile,
        };
        super::assert_length("task fragment", fields, values.len());
        super::assert_length(
            "paired fragment",
            if self.kind == WorkKind::Pair { tile } else { 0 },
            pair.len(),
        );
        let required = match self.kind {
            WorkKind::Snapshot => tile,
            WorkKind::Reorder => plan.size(),
            WorkKind::Initialize | WorkKind::InitializeScatter | WorkKind::Fused
                if plan.separate() =>
            {
                plan.request.input_len(plan.size())
            }
            WorkKind::Column => plan.size(),
            WorkKind::Scatter => self.band * plan.fragments(),
            _ => 0,
        };
        super::assert_length("task source", required, source.len());
        super::assert_length(
            "task factor",
            if matches!(self.kind, WorkKind::Finish | WorkKind::Fused) && self.product {
                tile
            } else {
                0
            },
            factor.len(),
        );
        match self.kind {
            WorkKind::Fused => {
                // Full inputs also benefit from visiting coefficients in
                // degree order: copy, scaling, and bit reversal share a pass.
                let input = (plan.separate()
                    && plan.resume.is_none()
                    && plan.request.input_order == ElementOrder::Natural
                    && plan.native_input() == ElementOrder::BitReversed)
                    .then(|| source.contiguous(0..source.len()))
                    .flatten();
                if let Some(input) = input {
                    plan.plan.fill_prefix(
                        input,
                        values,
                        if plan.inverse() {
                            ForwardShift::Domain(super::factors::Shift::Subgroup)
                        } else {
                            plan.shift
                        },
                        plan.residue_scales,
                        plan.input_scale,
                    );
                } else if plan.sparse() {
                    self.initialize_prefix(values, source);
                } else if plan.separate() && plan.scatter_input {
                    self.initialize_scatter(values, source);
                } else if plan.separate() {
                    for (index, value) in values.iter_mut().enumerate() {
                        let logical = if plan.native_input() == ElementOrder::Natural {
                            index
                        } else {
                            bit_reverse(index, plan.size().ilog2())
                        };
                        let physical = if plan.request.input_order == ElementOrder::Natural {
                            logical
                        } else {
                            bit_reverse(logical, plan.size().ilog2())
                        };
                        *value = source.get(physical).copied().unwrap_or(PastaField::ZERO);
                    }
                } else {
                    values[plan.request.input_len(plan.size())..].fill(PastaField::ZERO);
                    if plan.twist_before_permute() {
                        self.twist(values, plan.request.input_order);
                    }
                    if plan.pre_reverse() {
                        plan.plan.permute(values);
                    }
                }
                if plan.twist() && !plan.twist_before_permute() && !plan.sparse() && input.is_none()
                {
                    self.twist(values, plan.native_input());
                }
                if plan.first() <= plan.size()
                    && plan.native_input() == ElementOrder::BitReversed
                    && plan.request.output_order == ElementOrder::Natural
                    && plan.request.inverse_scale == InverseScale::Normalized
                    && plan.twiddles.is_none()
                    && plan.codelet == Codelet::Radix2
                {
                    plan.plan.local(values, plan.inverse(), plan.first());
                } else {
                    StageKernel {
                        plan: plan.plan,
                        inverse: plan.inverse(),
                        dif: plan.native_input() == ElementOrder::Natural,
                        scale: plan.request.inverse_scale,
                        codelet: plan.codelet,
                        twiddles: plan.twiddles,
                        output_order: plan.request.output_order,
                        factor: None,
                    }
                    .run(values, plan.first(), 1, &SerialExecutor);
                }
                if self.product {
                    for (index, value) in values.iter_mut().enumerate() {
                        *value = value.mul(factor.get(index).expect("invalid product view"));
                    }
                }
            }
            WorkKind::Initialize => {
                if plan.sparse() {
                    self.initialize_prefix(values, source);
                    return;
                }
                let support = plan.request.input_len(plan.size());
                for (offset, value) in values.iter_mut().enumerate() {
                    let index = self.start + offset;
                    if plan.separate() {
                        let logical = if plan.native_input() == ElementOrder::Natural {
                            index
                        } else {
                            bit_reverse(index, plan.size().ilog2())
                        };
                        *value = if logical >= support {
                            PastaField::ZERO
                        } else {
                            let physical = if plan.request.input_order == ElementOrder::Natural {
                                logical
                            } else {
                                bit_reverse(logical, plan.size().ilog2())
                            };
                            *source.get(physical).expect("invalid input view")
                        };
                    } else if index >= support {
                        *value = PastaField::ZERO;
                    }
                }
            }
            WorkKind::InitializeScatter => self.initialize_scatter(values, source),
            WorkKind::Snapshot => {
                for (index, value) in values.iter_mut().enumerate() {
                    *value = *source.get(index).expect("invalid snapshot source");
                }
            }
            WorkKind::Reorder => {
                for (offset, value) in values.iter_mut().enumerate() {
                    *value = *source
                        .get(bit_reverse(self.start + offset, plan.size().ilog2()))
                        .expect("invalid reorder source");
                }
            }
            WorkKind::Permute => {
                for index in self.start..self.start + tile {
                    let other = bit_reverse(index, plan.size().ilog2());
                    if index < other {
                        values.swap(index, other);
                    }
                }
            }
            WorkKind::Twist => {
                self.twist(
                    values,
                    if plan.twist_before_permute() {
                        plan.request.input_order
                    } else {
                        plan.native_input()
                    },
                );
            }
            WorkKind::Local => {
                if (plan.native_input() == ElementOrder::BitReversed)
                    && plan.twiddles.is_none()
                    && plan.codelet == Codelet::Radix2
                {
                    plan.plan.local(values, plan.inverse(), plan.first());
                } else {
                    StageKernel {
                        plan: Transform::new(
                            Domain::for_size(tile)
                                .expect("validated tile domain")
                                .subgroup(),
                        ),
                        inverse: plan.inverse(),
                        dif: plan.native_input() == ElementOrder::Natural,
                        scale: InverseScale::Unscaled,
                        codelet: plan.codelet,
                        twiddles: twiddle_table(plan.plan, plan.twiddles, plan.inverse(), tile),
                        output_order: plan.native_output(),
                        factor: None,
                    }
                    .run(values, plan.first(), 1, &SerialExecutor);
                }
            }
            WorkKind::Pair => {
                StageKernel {
                    plan: plan.plan,
                    inverse: plan.inverse(),
                    dif: plan.native_input() == ElementOrder::Natural,
                    scale: InverseScale::Unscaled,
                    codelet: plan.codelet,
                    twiddles: plan.twiddles,
                    output_order: plan.native_output(),
                    factor: None,
                }
                .pair(values, pair, self.start % (self.block / 2), self.block);
            }
            WorkKind::Column => {
                let rows = plan.fragments();
                let columns = values.len() / rows;
                for row_start in (0..rows).step_by(8) {
                    for column_start in (0..columns).step_by(8) {
                        let width = (columns - column_start).min(8);
                        for row in row_start..(row_start + 8).min(rows) {
                            let first = row * tile + self.column + column_start;
                            if let Some(span) = source.contiguous(first..first + width) {
                                for (offset, value) in span.iter().enumerate() {
                                    values[(column_start + offset) * rows + row] = *value;
                                }
                            } else {
                                for offset in 0..width {
                                    values[(column_start + offset) * rows + row] =
                                        *source.get(first + offset).expect("invalid column source");
                                }
                            }
                        }
                    }
                }
                if plan.twiddles.is_some() {
                    StageKernel {
                        plan: plan.plan,
                        inverse: plan.inverse(),
                        dif: false,
                        scale: plan.request.inverse_scale,
                        codelet: plan.codelet,
                        twiddles: plan.twiddles,
                        output_order: plan.native_output(),
                        factor: None,
                    }
                    .columns(values, self.column, tile, plan.first());
                } else {
                    plan.plan.columns(
                        values,
                        self.column,
                        tile,
                        plan.inverse(),
                        plan.column_normalized(),
                        plan.first(),
                    );
                }
            }
            WorkKind::Scatter => {
                if let Some(panel) = source.contiguous(0..source.len()) {
                    for (column, value) in values.iter_mut().enumerate() {
                        *value = panel[column * plan.fragments() + self.start / tile];
                    }
                } else {
                    for (column, value) in values.iter_mut().enumerate() {
                        *value = *source
                            .get(column * plan.fragments() + self.start / tile)
                            .expect("invalid panel source");
                    }
                }
            }
            WorkKind::Finish => {
                let inverse = plan.inverse() && !plan.column_normalized();
                let normalized = plan.request.inverse_scale == InverseScale::Normalized;
                let subgroup = plan.plan.domain().is_subgroup();
                let factors = if !inverse || subgroup {
                    super::factors::Factors::Identity
                } else if normalized {
                    super::factors::Factors::normalized(plan.plan.domain())
                } else {
                    super::factors::Factors::untwist(plan.plan.domain())
                };
                for (offset, value) in values.iter_mut().enumerate() {
                    let physical = self.start + offset;
                    let logical = if plan.request.output_order == ElementOrder::Natural {
                        physical
                    } else {
                        bit_reverse(physical, plan.size().ilog2())
                    };
                    if inverse {
                        if normalized {
                            *value = if subgroup {
                                crate::field::pasta::butterfly::divide_by_power_of_two(
                                    *value,
                                    plan.size().ilog2(),
                                )
                            } else {
                                factors.apply_normalized(*value, logical, plan.size().ilog2())
                            };
                        } else if !subgroup && !logical.is_multiple_of(3) {
                            *value = value.mul(&factors.at(logical));
                        }
                    }
                    if self.product {
                        *value = value.mul(factor.get(offset).expect("invalid product view"));
                    }
                }
            }
        }
    }

    fn initialize_scatter(
        &self,
        values: &mut [PastaField<M>],
        source: &dyn ReadView<PastaField<M>>,
    ) {
        let plan = self.plan;
        let log_size = plan.size().ilog2();
        let support = plan.request.input_len(plan.size());
        for physical in self.start..self.start + plan.tile {
            let logical = if plan.request.input_order == ElementOrder::Natural {
                physical
            } else {
                bit_reverse(physical, log_size)
            };
            let destination = if plan.native_input() == ElementOrder::Natural {
                logical
            } else {
                bit_reverse(logical, log_size)
            };
            values[destination] = if logical < support {
                *source.get(physical).expect("invalid input view")
            } else {
                PastaField::ZERO
            };
        }
    }

    fn initialize_prefix(
        &self,
        values: &mut [PastaField<M>],
        source: &dyn ReadView<PastaField<M>>,
    ) {
        let plan = self.plan;
        let repeat = plan.first() / 2;
        let width = plan.size() / repeat;
        let twist = plan.twist();
        let scale = !plan.input_scale.is_one();
        // Amortize progression setup across at least 32 distinct powers. Tiny
        // regions retain direct exponentiation, including fragmented repeats.
        let powers = if twist && plan.residue_scales.is_none() && values.len() / repeat >= 32 {
            match plan.shift {
                ForwardShift::Residue { shift, inverse } => Some(
                    super::factors::BitReversedPowers::new(shift, inverse, width.ilog2()),
                ),
                _ => None,
            }
        } else {
            None
        };
        let mut power = powers.as_ref().map(|powers| powers.at(self.start / repeat));
        let mut offset = 0;
        while offset < values.len() {
            let index = self.start + offset;
            let degree = bit_reverse(index / repeat, width.ilog2());
            let mut value = source.get(degree).copied().unwrap_or(PastaField::ZERO);
            if degree < source.len() && twist {
                if let Some(scales) = plan.residue_scales {
                    value = value.mul(&scales[degree]);
                } else if !(plan.shift.is_identity()
                    || plan.shift.cycle().is_some() && degree.is_multiple_of(3))
                {
                    value = value.mul(&power.unwrap_or_else(|| plan.shift.at(degree)));
                }
                if scale {
                    value = value.mul(&plan.input_scale);
                }
            }
            let len = (repeat - index % repeat).min(values.len() - offset);
            values[offset..offset + len].fill(value);
            offset += len;
            if offset < values.len()
                && let Some(powers) = &powers
            {
                power = Some(powers.next(index / repeat, power.unwrap()));
            }
        }
    }

    fn twist(&self, values: &mut [PastaField<M>], order: ElementOrder) {
        let plan = self.plan;
        let scale = !plan.input_scale.is_one();
        if let Some(scales) = plan.residue_scales {
            for (offset, value) in values.iter_mut().enumerate() {
                let index = if order == ElementOrder::Natural {
                    self.start + offset
                } else {
                    bit_reverse(self.start + offset, plan.size().ilog2())
                };
                *value = value.mul(&scales[index]);
                if scale {
                    *value = value.mul(&plan.input_scale);
                }
            }
        } else if let Some(cycle) = plan.shift.cycle() {
            if !scale && plan.shift.is_identity() {
                return;
            }
            let cycle = if scale {
                cycle.scaled(plan.input_scale)
            } else {
                cycle
            };
            for (offset, value) in values.iter_mut().enumerate() {
                let degree = if order == ElementOrder::Natural {
                    self.start + offset
                } else {
                    bit_reverse(self.start + offset, plan.size().ilog2())
                };
                if scale || !degree.is_multiple_of(3) {
                    *value = value.mul(&cycle.at(degree));
                }
            }
        } else {
            let ForwardShift::Residue { shift, inverse } = plan.shift else {
                unreachable!()
            };
            if order == ElementOrder::Natural {
                let mut power = shift.pow_u64(self.start as u64).mul(&plan.input_scale);
                let len = values.len();
                for (index, value) in values.iter_mut().enumerate() {
                    *value = value.mul(&power);
                    if index + 1 < len {
                        power = power.mul(&shift);
                    }
                }
            } else {
                let powers =
                    super::factors::BitReversedPowers::new(shift, inverse, plan.size().ilog2());
                let mut power = powers.at(self.start).mul(&plan.input_scale);
                let len = values.len();
                for (offset, value) in values.iter_mut().enumerate() {
                    *value = value.mul(&power);
                    if offset + 1 < len {
                        power = powers.next(self.start + offset, power);
                    }
                }
            }
        }
    }
}

impl<M: PrimeModulus, R: Resources<M>> Kernel<R> for FftKernel<'_, M> {
    type Output = ();
    fn execute(&mut self, resources: &mut R) -> Self::Output {
        self.run(resources.buffers())
    }
}

/// Leases and arithmetic status returned after publishing one task.
pub struct Published<R> {
    /// Entire resource envelope for immediate release.
    pub resources: R,
    /// Scheduler transition error, which poisons this run.
    pub error: Option<TaskError>,
    /// Execution status, including cancellation or unwind.
    pub outcome: Outcome,
    /// Whether this receipt finishes the transform and readies consumers.
    pub complete: bool,
}

/// Compact phase state for one transform; no eagerly materialized task graph.
pub struct FftRun<'a, 't, M: PrimeModulus> {
    plan: FftPlan<'t, M>,
    frontier: Frontier<'a>,
    kind: WorkKind,
    block: usize,
    post: bool,
    product: bool,
    complete: bool,
    failed: bool,
    column: usize,
}

impl<'a, 't, M: PrimeModulus> FftRun<'a, 't, M> {
    fn empty(
        plan: FftPlan<'t, M>,
        identity: &'a mut Identity,
        slots: &'a mut [TaskStorage],
    ) -> Self {
        Self {
            plan,
            frontier: Frontier::new(identity, slots, 0),
            kind: WorkKind::Finish,
            block: 0,
            post: false,
            product: false,
            complete: true,
            failed: false,
            column: 0,
        }
    }
    /// Binds exclusive metadata.
    ///
    /// `product` adds a terminal elementwise factor in requested output order.
    /// Arithmetic buffers are bound only by claims. Panics if frontier storage
    /// is empty.
    pub fn new(
        plan: FftPlan<'t, M>,
        product: bool,
        identity: &'a mut Identity,
        slots: &'a mut [TaskStorage],
    ) -> Self {
        let (kind, block) = plan.initial();
        let complete =
            kind == WorkKind::Finish && (!plan.inverse() || plan.column_normalized()) && !product;
        let total = if complete {
            0
        } else if kind == WorkKind::Pair {
            plan.fragments() / 2
        } else {
            plan.fragments()
        };
        Self {
            plan,
            frontier: Frontier::new(identity, slots, total),
            kind,
            block,
            post: false,
            product,
            complete,
            failed: false,
            column: 0,
        }
    }

    fn band(&self) -> usize {
        self.plan.columns.map_or(0, |(columns, panels)| {
            (self.plan.tile - self.column).min(columns * panels)
        })
    }

    fn task_count(&self) -> usize {
        if self.complete {
            0
        } else if self.kind == WorkKind::Pair {
            self.plan.fragments() / 2
        } else if self.kind == WorkKind::Column {
            self.band().div_ceil(self.plan.columns.unwrap().0)
        } else {
            self.plan.fragments()
        }
    }

    fn request(&self, key: TaskKey<'a>) -> Request<'a> {
        let tile = self.plan.tile;
        let index = key.index();
        let start = if self.kind == WorkKind::Pair {
            let half_tiles = self.block / 2 / tile;
            (index / half_tiles * 2 * half_tiles + index % half_tiles) * tile
        } else {
            index * tile
        };
        let range = match self.kind {
            WorkKind::Permute | WorkKind::InitializeScatter => 0..self.plan.size(),
            WorkKind::Column => {
                let columns = self.plan.columns.unwrap().0;
                let first = index * columns;
                first * self.plan.fragments()
                    ..(first + columns).min(self.band()) * self.plan.fragments()
            }
            WorkKind::Scatter => start + self.column..start + self.column + self.band(),
            _ => start..start + tile,
        };
        Request {
            key,
            #[cfg(test)]
            kind: self.kind,
            write: (
                if matches!(self.kind, WorkKind::Snapshot | WorkKind::Column) {
                    Bank::Snapshot
                } else {
                    Bank::Values
                },
                range.clone(),
            ),
            pair: (self.kind == WorkKind::Pair)
                .then_some(start + self.block / 2..start + self.block / 2 + tile),
            read: match self.kind {
                WorkKind::Snapshot => Some((Bank::Values, range.clone())),
                WorkKind::Reorder => Some((Bank::Snapshot, 0..self.plan.size())),
                WorkKind::Initialize | WorkKind::InitializeScatter | WorkKind::Fused
                    if self.plan.separate() =>
                {
                    Some((
                        Bank::Input,
                        0..self.plan.request.input_len(self.plan.size()),
                    ))
                }
                WorkKind::Column => Some((Bank::Values, 0..self.plan.size())),
                WorkKind::Scatter => Some((Bank::Snapshot, 0..self.band() * self.plan.fragments())),
                _ => None,
            },
            factor: (matches!(self.kind, WorkKind::Finish | WorkKind::Fused) && self.product)
                .then_some(range.clone()),
        }
    }

    /// Writes at most the supplied request capacity, without claiming work.
    pub fn ready(&self, output: &mut [Option<Request<'a>>]) -> usize {
        self.ready_from(0, output)
    }

    /// Continues readiness enumeration at a task index in this epoch. This
    /// allows a small request buffer to inspect every compatible task. Pass
    /// one past the last returned key's index; restart at zero after publishing
    /// a receipt because the run may have exposed a new stage.
    pub fn ready_from(&self, start: usize, output: &mut [Option<Request<'a>>]) -> usize {
        if self.complete || self.failed {
            return 0;
        }
        let mut written = 0;
        for key in self
            .frontier
            .tasks()
            .filter(|key| key.index() >= start)
            .take(output.len())
        {
            output[written] = Some(self.request(key));
            written += 1;
        }
        written
    }

    /// Acquires the complete bundle atomically before detaching bounded work.
    pub fn try_claim<R: Resources<M>>(
        &mut self,
        request: Request<'a>,
        acquire: impl FnOnce() -> Option<R>,
    ) -> Result<Option<Task<'a, FftKernel<'t, M>, R>>, TaskError> {
        if self.failed {
            return Err(TaskError::Failed);
        }
        self.frontier.check_key(request.key)?;
        let actual = self.request(request.key);
        let kernel = FftKernel {
            plan: self.plan,
            kind: self.kind,
            start: if matches!(
                self.kind,
                WorkKind::Permute | WorkKind::Scatter | WorkKind::InitializeScatter
            ) {
                request.key.index() * self.plan.tile
            } else {
                actual.write.1.start
            },
            block: self.block,
            product: self.product,
            column: self.column
                + if self.kind == WorkKind::Column {
                    request.key.index() * self.plan.columns.unwrap().0
                } else {
                    0
                },
            band: self.band(),
        };
        self.frontier.try_claim(request.key, kernel, acquire)
    }

    fn arithmetic(&mut self) {
        if self.plan.first() > self.plan.size() {
            self.finish();
        } else if self.plan.native_input() == ElementOrder::BitReversed {
            self.kind = WorkKind::Local;
        } else {
            self.kind = WorkKind::Pair;
            self.block = self.plan.size();
        }
    }

    fn finish(&mut self) {
        self.post = true;
        self.kind = if self.plan.post_reverse() {
            self.plan.permutation()
        } else {
            WorkKind::Finish
        };
        if !self.plan.post_reverse()
            && (!self.plan.inverse() || self.plan.column_normalized())
            && !self.product
        {
            self.complete = true;
        }
    }

    fn after_input(&mut self) {
        if self.plan.twist() && !self.plan.twist_before_permute() && !self.plan.sparse() {
            self.kind = WorkKind::Twist;
        } else {
            self.arithmetic();
        }
    }

    /// Publishes a receipt and exposes this run's next stage immediately.
    /// A failed run accepts outstanding receipts for draining but exposes no
    /// new work. Foreign receipts are returned intact.
    pub fn complete<R>(
        &mut self,
        receipt: Completion<'a, R, ()>,
    ) -> Result<Published<R>, crate::exec::execution::PublishError<'a, R, ()>> {
        let completed = self.frontier.complete(receipt)?;
        let mut error = None;
        self.failed |= completed.outcome != Outcome::Success;
        if !self.failed && self.frontier.is_complete() {
            match self.kind {
                WorkKind::Initialize | WorkKind::InitializeScatter => {
                    if self.plan.twist_before_permute() {
                        self.kind = WorkKind::Twist;
                    } else if !self.plan.separate() && self.plan.pre_reverse() {
                        self.kind = self.plan.permutation();
                    } else {
                        self.after_input();
                    }
                }
                WorkKind::Snapshot => self.kind = WorkKind::Reorder,
                WorkKind::Reorder | WorkKind::Permute => {
                    if self.post {
                        self.kind = WorkKind::Finish;
                        if (!self.plan.inverse() || self.plan.column_normalized()) && !self.product
                        {
                            self.complete = true;
                        }
                    } else {
                        self.after_input();
                    }
                }
                WorkKind::Twist => {
                    if self.plan.twist_before_permute() {
                        self.kind = self.plan.permutation();
                    } else {
                        self.arithmetic();
                    }
                }
                WorkKind::Local => {
                    if self.plan.columns.is_some() {
                        self.kind = WorkKind::Column;
                    } else if self.plan.native_input() == ElementOrder::BitReversed
                        && self.plan.fragments() > 1
                    {
                        self.kind = WorkKind::Pair;
                        self.block = (self.plan.tile * 2).max(self.plan.first());
                    } else {
                        self.finish();
                    }
                }
                WorkKind::Pair => {
                    if self.plan.native_input() == ElementOrder::BitReversed {
                        if self.block == self.plan.size() {
                            self.finish();
                        } else {
                            self.block *= 2;
                        }
                    } else {
                        self.block /= 2;
                        if self.block == self.plan.tile {
                            self.kind = WorkKind::Local;
                        }
                    }
                }
                WorkKind::Finish | WorkKind::Fused => self.complete = true,
                WorkKind::Column => self.kind = WorkKind::Scatter,
                WorkKind::Scatter => {
                    self.column += self.band();
                    if self.column == self.plan.tile {
                        self.finish();
                    } else {
                        self.kind = WorkKind::Column;
                    }
                }
            }
            if let Err(transition) = self.frontier.restart(self.task_count()) {
                self.failed = true;
                error = Some(transition);
            }
        }
        Ok(Published {
            resources: completed.resources,
            error,
            outcome: completed.outcome,
            complete: self.complete && !self.failed,
        })
    }

    /// Whether all tasks succeeded and their receipts were published.
    pub fn is_complete(&self) -> bool {
        self.complete && !self.failed
    }

    /// Whether a task failed, was cancelled, or returned invalid resources.
    pub fn is_failed(&self) -> bool {
        self.failed
    }

    /// Outstanding receipts that must be published or drained.
    pub fn inflight(&self) -> usize {
        self.frontier.inflight()
    }

    /// Rebinds completed metadata for another transform without reconstructing
    /// task storage or resetting its identity. Stale receipts remain invalid.
    /// The application must finish consumers before reusing their field banks.
    /// Returns [`TaskError::Busy`] until this run completes, or
    /// [`TaskError::Failed`] after failure; errors leave the run unchanged.
    pub fn rebind(&mut self, plan: FftPlan<'t, M>, product: bool) -> Result<(), TaskError> {
        if self.failed {
            return Err(TaskError::Failed);
        }
        if !self.complete {
            return Err(TaskError::Busy);
        }
        let (kind, block) = plan.initial();
        self.frontier.restart(if kind == WorkKind::Pair {
            plan.fragments() / 2
        } else {
            plan.fragments()
        })?;
        self.plan = plan;
        self.product = product;
        self.kind = kind;
        self.block = block;
        self.post = false;
        self.complete = false;
        self.column = 0;
        Ok(())
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
pub(crate) mod test_buffers;

#[cfg(test)]
pub(crate) mod test_pipeline;
