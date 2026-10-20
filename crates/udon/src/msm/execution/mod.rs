//! Bounded MSM preparation, window, and reduction tasks.
//!
//! [`BatchPlan`] drives contiguous input batches on a caller's scoped executor.
//! For application-controlled scheduling, use the incremental types below.
//!
//! [`MsmPlan`] fixes legal term subdivisions independently of worker count.
//! [`MsmRun`] binds one invocation and incrementally exposes [`Request`]s. The
//! application acquires the requested typed leases, claims a task, executes it
//! on any worker, and publishes its completion. Preparation and window storage
//! are retained until their consumers finish; arithmetic scratch belongs to
//! each executing task and can serve other operations between tasks.

use core::{marker::PhantomData, num::NonZeroUsize};

use super::{
    ArithmeticOptions, Bases, CurveError, Input, PastaCurve, ProjectivePoint, Requirements,
    ScalarStorage, Scalars, Scratch, assert_scratch, kernels, prepared,
    recode::{self, Geometry, Shape},
    schedule,
};
use crate::exec::ExecutionOptions;
use crate::exec::execution::{
    Completion, Frontier, Identity, Kernel, Outcome, ReadView, Task, TaskError, TaskKey,
    TaskStorage,
};

pub(super) mod batch;
mod chunks;
mod driver;
mod fragmented;
pub use super::schedule::JobStorage;
pub use batch::{BatchPlan, WorkerStorage};
pub use chunks::{ChunkRequest, ParallelMsmRun};

/// Base metadata for scalar rows supplied by producer tasks after binding.
///
/// Each claimed task leases its own source range through [`SourceBuffers`].
/// This avoids borrowing a complete scalar or index array while producers
/// still own disjoint writable fragments. The provider keeps requests ready
/// by declining acquisition until their complete source range is published.
#[derive(Clone, Copy, Debug)]
pub struct ProducedInput<'i, C: PastaCurve> {
    bases: Bases<'i, C>,
    terms: usize,
    indexed: bool,
}
impl<'i, C: PastaCurve> ProducedInput<'i, C> {
    /// Selects every base in storage order; producers supply field scalars.
    pub fn dense(bases: Bases<'i, C>) -> Self {
        Self {
            bases,
            terms: bases.len(),
            indexed: false,
        }
    }
    /// Producers supply field scalars and indices for `terms` selected bases.
    /// Indices are checked by each consuming kernel before arithmetic writes.
    pub fn indexed(bases: Bases<'i, C>, terms: usize) -> Self {
        Self {
            bases,
            terms,
            indexed: true,
        }
    }
    /// Number of logical terms, independent of source storage availability.
    pub fn len(&self) -> usize {
        self.terms
    }
    /// Whether this input contributes no terms.
    pub fn is_empty(&self) -> bool {
        self.terms == 0
    }
    fn metadata(self) -> Input<'i, C> {
        Input {
            bases: self.bases,
            scalars: Scalars::Raw(&[]),
            indices: None,
        }
    }
}

/// Published source fragments local to a claimed request's term range.
///
/// Preparation reads `Request::terms` scalars starting at logical index zero.
/// Indexed preparation and windows read that many indices. Other tasks need
/// neither source. Scalar residues and base records obey [`Input`]'s arithmetic
/// invariants. Published sources must remain unchanged until their consumers
/// release them; lengths and index bounds are checked before writes.
pub struct SourceBuffers<'a, C: PastaCurve> {
    /// Raw field scalars, possibly spanning several producer fragments.
    pub scalars: &'a dyn ReadView<crate::field::PastaField<C::Scalar>>,
    /// Base indices for an indexed produced input.
    pub indices: &'a dyn ReadView<u32>,
}

/// Resolved arithmetic and storage requirements for bounded MSM tasks.
///
/// Construction selects recoding, subdivisions, and accumulation from input
/// facts and resource constraints. The caller supplies storage and schedules
/// the resulting resource requests; the implementation choice remains private.
#[derive(Clone, Copy, Debug)]
pub struct MsmPlan<C: PastaCurve> {
    terms: usize,
    cap: usize,
    options: ArithmeticOptions,
    // Large incremental grains keep their planned Booth geometry. Batch
    // execution can specialize after preparation unless memory adaptation
    // already resolved a narrower width. This is independent of the request.
    specialize_short: bool,
    job: schedule::JobStorage,
    retained: Requirements,
    memory_limit: Option<usize>,
    marker: PhantomData<C>,
}

impl<C: PastaCurve> MsmPlan<C> {
    /// Resolves a reusable plan from the term count and resource constraints.
    ///
    /// This conservative plan accepts any scalar row and the original bases of
    /// any supported bank of the stated length. Use [`Self::for_input`] to account
    /// for retained preparation.
    /// No storage is allocated or written; impossible sizes or workspace limits
    /// return [`CurveError::SizeOverflow`] or [`CurveError::MemoryLimit`].
    pub fn new(terms: usize, options: ExecutionOptions) -> Result<Self, CurveError> {
        let (job, arithmetic) = schedule::unbound::<C>(terms, options, None, None)?;
        Ok(Self::from_job(
            terms,
            arithmetic,
            job,
            true,
            options.memory_limit(),
        ))
    }

    /// Resolves a plan using this input's scalar shape and retained preparation.
    ///
    /// A retained [`AlphaTable`](super::AlphaTable) is an optional accelerator.
    /// Its [size heuristic](super::AlphaDescription::amortized) is considered
    /// alongside scalar shape and the resolved resource limits.
    ///
    /// The input is not borrowed by the plan. Execution checks the term count
    /// and preparation before writing. Requirements are fixed: if planning
    /// omits scalar preparation or digit storage, later inputs must supply the
    /// corresponding retained records or matching cache. A plan specialized
    /// for short scalars requires prepared scalars with no larger bit width;
    /// a plan relying on compact bases requires compact bases again. An α plan
    /// requires an α bank with the same codebook width. Changing task resources
    /// after planning does not change its geometry. After retaining a digit
    /// cache, construct a new plan to remove temporary recoding storage.
    /// Use [`Self::new`] for reuse across arbitrary scalar rows and bases.
    ///
    /// Construction does not write storage. Size and workspace errors follow
    /// [`Self::new`]. Retained preparation is separate from the workspace ceiling.
    pub fn for_input(input: &Input<'_, C>, options: ExecutionOptions) -> Result<Self, CurveError> {
        let plan = schedule::Plan::new(core::slice::from_ref(input), options.into())?;
        let job = schedule::job(input, plan.options)?;
        Ok(Self::from_job(
            input.len(),
            plan.options.arithmetic,
            job,
            false,
            options.memory_limit(),
        ))
    }

    /// Plans sources published in independently available fragments.
    ///
    /// `source_fragment` is the maximum consecutive source range the provider
    /// can lease. Udon chooses preparation and arithmetic subdivisions within it.
    /// A supplied [`AlphaTable`](super::AlphaTable) is considered using each
    /// subdivision's size and task allowance, rather than the full row length;
    /// see [`AlphaDescription::amortized`](super::AlphaDescription::amortized).
    /// The plan retains no source borrow. Construction writes no storage and
    /// has the size and workspace errors of [`Self::new`].
    pub fn for_produced(
        input: ProducedInput<'_, C>,
        source_fragment: NonZeroUsize,
        options: ExecutionOptions,
    ) -> Result<Self, CurveError> {
        let (job, arithmetic) = schedule::unbound::<C>(
            input.len(),
            options,
            Some(source_fragment),
            input.bases.alpha().map(|c| c.description()),
        )?;
        Ok(Self::from_job(
            input.len(),
            arithmetic,
            job,
            true,
            options.memory_limit(),
        ))
    }

    pub(super) fn cache_geometry(&self, terms: usize) -> Option<Geometry> {
        self.complete_cache_geometry(terms)
            .filter(|geometry| !matches!(geometry, Geometry::Alpha(_)))
    }

    pub(super) fn alpha_cache_geometry(&self, terms: usize) -> Option<Geometry> {
        self.complete_cache_geometry(terms)
            .filter(|geometry| matches!(geometry, Geometry::Alpha(_)))
    }

    fn complete_cache_geometry(&self, terms: usize) -> Option<Geometry> {
        (self.terms == terms && terms != 0 && terms <= self.cap && !self.options.streaming())
            .then_some(self.job.geometry)
    }

    /// Plans bounded tasks without binding inputs or allocating storage.
    ///
    /// The effective grain is the smaller of `grain`, the arithmetic chunk cap,
    /// and the term count. Scheduling capacity and memory admission belong to
    /// the caller. Use [`Self::retained_for_slots`] and [`Self::temporary`] to
    /// size retained chunks and each simultaneous scratch bundle separately;
    /// also account for metadata, queues, unused provider capacity, and alignment.
    /// Returns [`CurveError::SizeOverflow`] for unrepresentable storage counts
    /// or bytes, before binding or writing any storage.
    #[cfg(test)]
    fn new_with(
        terms: usize,
        mut options: ArithmeticOptions,
        grain: NonZeroUsize,
    ) -> Result<Self, CurveError> {
        let cap = terms.min(grain.get()).min(options.chunk_cap());
        options.chunk_size = NonZeroUsize::new(cap.max(1));
        let geometry = Geometry::select(
            cap,
            Shape {
                bits: 255,
                weight: 0,
            },
            options,
            crate::exec::TaskBudget::SERIAL,
        );
        let job = schedule::fixed_geometry::<C>(cap, geometry, options)?;
        let retained = Requirements {
            scalars: cap,
            digits: geometry.storage_len(cap)?,
            projective: if terms == 0 {
                0
            } else {
                geometry
                    .windows()
                    .checked_mul(if options.streaming() {
                        geometry.buckets() + 1
                    } else {
                        1
                    })
                    .ok_or(CurveError::SizeOverflow)?
            },
            ..Requirements::default()
        };
        let temporary = if options.streaming() {
            Requirements::default()
        } else {
            job.work
        };
        retained.plus(temporary)?.times::<C>(1)?.bytes::<C>()?;
        Ok(Self {
            terms,
            cap,
            options,
            specialize_short: cap < 4096,
            job,
            retained,
            memory_limit: None,
            marker: PhantomData,
        })
    }

    fn from_job(
        terms: usize,
        options: ArithmeticOptions,
        job: schedule::JobStorage,
        specialize_short: bool,
        memory_limit: Option<usize>,
    ) -> Self {
        let retained = Requirements {
            scalars: job.requirements.scalars,
            digits: job.requirements.digits,
            projective: if terms == 0 {
                0
            } else {
                job.geometry.windows()
                    + if options.streaming() {
                        job.work.projective
                    } else {
                        0
                    }
            },
            ..Requirements::default()
        };
        Self {
            terms,
            cap: job.cap,
            options,
            specialize_short,
            job,
            retained,
            memory_limit,
            marker: PhantomData,
        }
    }

    /// Upper bounds on typed storage retained by one active term chunk.
    ///
    /// Plans made with [`Self::for_input`] account for retained scalar records
    /// and matching digit caches. Execution requires compatible preparation.
    /// These counts exclude run metadata and executing tasks' temporary scratch.
    pub fn retained(&self) -> Requirements {
        self.retained
    }

    /// Upper bounds on retained storage for `slots` independent term chunks.
    ///
    /// Each slot owns preparation and one partial per window. The shared
    /// temporary bundles are counted separately, once per simultaneous lease.
    /// Metadata, queues, idle provider capacity, and alignment still belong in
    /// application admission accounting. Streaming
    /// uses [`MsmRun`] with one complete set of retained window buckets.
    /// Returns [`CurveError::SizeOverflow`] if the requested slice counts or
    /// their total bytes are unrepresentable, or [`CurveError::MemoryLimit`]
    /// if these slots and the plan's simultaneous temporary bundles exceed its
    /// workspace ceiling.
    pub fn retained_for_slots(&self, slots: NonZeroUsize) -> Result<Requirements, CurveError> {
        let r = self.retained.times::<C>(slots.get())?;
        let tasks = self.output_slots().min(self.job.budget.get()).min(32);
        let required = r.plus(self.temporary().times::<C>(tasks)?)?.bytes::<C>()?;
        if let Some(limit) = self.memory_limit
            && required > limit
        {
            return Err(CurveError::MemoryLimit { required, limit });
        }
        Ok(r)
    }

    /// Upper bounds on one executing task's temporary arithmetic bundle.
    ///
    /// Each simultaneously executing task needs its own bundle. These counts
    /// exclude retained chunks and metadata; they do not bound total admission.
    pub fn temporary(&self) -> Requirements {
        if self.options.streaming() {
            Requirements::default()
        } else {
            self.job.work
        }
    }

    /// Maximum terms in a task; zero only for an empty operation.
    pub fn grain(&self) -> usize {
        self.cap
    }

    /// Maximum terms written by one preparation request. Providers can reserve
    /// disjoint retained fragments of this size before binding an input.
    pub fn preparation_terms(&self) -> usize {
        self.cap.min(recode::CHUNK)
    }

    /// Reduces the term grain while preserving this plan's recoding geometry.
    ///
    /// Unlike replanning a shorter input, this keeps its window width and
    /// kernel family. Independent partitions can therefore add scheduling
    /// slack without implicitly selecting a different recoder. Extra window
    /// collapses and retained slots still belong in the caller's cost model.
    #[cfg(test)]
    fn with_grain(mut self, grain: NonZeroUsize) -> Result<Self, CurveError> {
        self.cap = self.cap.min(grain.get());
        self.options.chunk_size = NonZeroUsize::new(self.cap.max(1));
        self.job = schedule::fixed_geometry::<C>(self.cap, self.job.geometry, self.options)?;
        self.retained.scalars = self.cap;
        self.retained.digits = self.job.geometry.storage_len(self.cap)?;
        self.retained_for_slots(NonZeroUsize::MIN)?;
        Ok(self)
    }

    /// Number of retained projective result slots per active input chunk.
    pub fn output_slots(&self) -> usize {
        if self.terms == 0 {
            0
        } else {
            self.job.geometry.windows()
        }
    }

    // Reusing scalar records is independent of digit geometry. A digit cache
    // remains valid only for the complete, unsplit input and selected geometry.
    fn cached<'i>(&self, input: Input<'i, C>, geometry: Geometry) -> Option<&'i [u8]> {
        if self.options.streaming() || input.len() > self.cap {
            return None;
        }
        match input.scalars {
            Scalars::Prepared(s) => s.cached_digits(geometry),
            _ => None,
        }
    }

    fn accepts(&self, input: Input<'_, C>) -> bool {
        if let Geometry::Alpha(width) = self.job.geometry
            && input
                .bases
                .alpha()
                .is_none_or(|c| c.description().window_bits() != width)
        {
            return false;
        }
        if input.is_empty() {
            return true;
        }
        let prepared = match input.scalars {
            Scalars::Prepared(s) => Some(s),
            _ => None,
        };
        if self.job.requirements.scalars == 0 && prepared.is_none() {
            return false;
        }
        if self.job.requirements.digits == 0
            && self.job.geometry.stride() != 0
            && self.cached(input, self.job.geometry).is_none()
        {
            return false;
        }
        if let Geometry::Short(bits) = self.job.geometry
            && prepared.is_none_or(|s| s.shape.bits > bits)
        {
            return false;
        }
        self.job.geometry != Geometry::Joint
            || self.job.work.affine != 0
            || matches!(input.bases, Bases::Compact(_) | Bases::CompactPrepared(_))
    }

    fn initial_geometry(&self, input: Input<'_, C>) -> Geometry {
        if self.cached(input, self.job.geometry).is_none()
            && !self.options.streaming()
            && self.specialize_short
            && let Scalars::Prepared(s) = input.scalars
        {
            let actual = Geometry::for_shape(input.len(), s.shape, self.options);
            if matches!(actual, Geometry::Short(_)) {
                return actual;
            }
        }
        self.job.geometry
    }
}

/// Work kind with distinct storage lifetime requirements.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum WorkKind {
    /// Writes one retained scalar and recoding chunk.
    Prepare,
    /// Reads a prepared chunk and computes or deposits one window.
    Window,
    /// Collapses one retained streaming bucket array.
    Collapse,
    /// Recombines completed windows in a bounded ordered reduction.
    Reduce,
}

/// One ready MSM task and the complete resource bundle it requires.
#[derive(Clone, Copy, Debug)]
pub struct Request<'a> {
    /// Claim identity, valid only for this run and dependency epoch.
    pub key: TaskKey<'a>,
    #[cfg(test)]
    kind: WorkKind,
    /// First input term processed by this task.
    pub offset: usize,
    /// Terms in this chunk.
    pub terms: usize,
    /// First retained scalar written during preparation, relative to the chunk.
    pub scalar_start: usize,
    /// First retained recoding byte written during preparation.
    pub digit_start: usize,
    /// Window index, or zero for preparation and reduction.
    window: usize,
    /// Exclusive task scratch. During preparation its scalar and digit fields
    /// describe writes into retained storage, not additional temporary blocks.
    pub scratch: Requirements,
    /// Shared retained scalar prefix for a window task.
    pub read_scalars: usize,
    /// Shared retained digit prefix for a window task.
    pub read_digits: usize,
    /// First retained bucket requested by this task.
    pub bucket_start: usize,
    /// Exclusive retained projective bucket count.
    pub buckets: usize,
    /// Logical output slot, when this task writes a partial result.
    pub output_slot: Option<usize>,
    /// Number of produced source scalars read starting at `offset`.
    pub source_scalars: usize,
    /// Number of produced source indices read starting at `offset`.
    pub source_indices: usize,
    /// Number of shared logical partials read by a reduction task.
    pub read_partials: usize,
}

/// Transient kernel views obtained from an owned task resource bundle.
///
/// The direct [`Resources`] implementation supports local task execution.
/// Erased [`ReadView`] references need not be `Sync`. For worker dispatch, own
/// typed borrowed slices or movable guards and construct these views on the
/// worker in [`Resources::buffers`].
pub struct Buffers<'a, C: PastaCurve> {
    /// Shared prepared scalar records; empty for a preparation task.
    pub records: &'a dyn ReadView<ScalarStorage<C>>,
    /// Shared recoding bytes; empty for a preparation task.
    pub digits: &'a dyn ReadView<u8>,
    /// Exclusive typed scratch or preparation destination prefixes.
    pub scratch: Scratch<'a, C>,
    /// Exclusive retained buckets for one streaming window.
    pub buckets: &'a mut [ProjectivePoint<C>],
    /// One exclusive logical result slot for a window or collapse task.
    pub output: &'a mut [ProjectivePoint<C>],
    /// Fragmented shared results for the reduction task.
    pub partials: &'a dyn ReadView<ProjectivePoint<C>>,
}

/// An owned bundle of safe fragments or application-provided lease guards.
///
/// The views must represent the prefixes and window named by the claimed [`Request`].
/// Incorrect capacities panic before writes; semantic slot identity and initialized
/// retained contents belong to the application provider's contract. Incorrect contents
/// can produce incorrect arithmetic but cannot violate Rust memory safety. Guards
/// remain owned by the task through unwinding.
pub trait Resources<C: PastaCurve> {
    /// Borrows all disjoint mutable and shared views for this bounded kernel.
    fn buffers(&mut self) -> Buffers<'_, C>;

    /// Borrows source fragments together with disjoint arithmetic destinations.
    /// Existing borrowed inputs do not need sources and use this default.
    fn with_source<O>(
        &mut self,
        use_buffers: impl FnOnce(Buffers<'_, C>, SourceBuffers<'_, C>) -> O,
    ) -> O
    where
        Self: Sized,
    {
        use_buffers(
            self.buffers(),
            SourceBuffers {
                scalars: &[],
                indices: &[],
            },
        )
    }
}

impl<C: PastaCurve> Resources<C> for Buffers<'_, C> {
    fn buffers(&mut self) -> Buffers<'_, C> {
        Buffers {
            records: self.records,
            digits: self.digits,
            scratch: self.scratch.reborrow(),
            buckets: self.buckets,
            output: self.output,
            partials: self.partials,
        }
    }
}

/// Detached arithmetic for one request; constructed only by [`MsmRun`].
pub struct MsmKernel<'i, C: PastaCurve> {
    input: Input<'i, C>,
    produced: Option<ProducedInput<'i, C>>,
    plan: MsmPlan<C>,
    kind: WorkKind,
    offset: usize,
    terms: usize,
    window: usize,
    geometry: Geometry,
    first_chunk: bool,
    scalar_bits: u8,
}

/// Opaque kernel output, published through [`MsmRun::complete`].
pub struct MsmOutput<C: PastaCurve>(Result<(Shape, ProjectivePoint<C>), CurveError>);

impl<C: PastaCurve> MsmKernel<'_, C> {
    fn run(
        &self,
        buffers: Buffers<'_, C>,
        source: SourceBuffers<'_, C>,
    ) -> Result<(Shape, ProjectivePoint<C>), CurveError> {
        let Buffers {
            records: buffers_records,
            digits,
            scratch,
            buckets,
            output,
            partials,
        } = buffers;
        let geometry = self.geometry;
        let mut shape = Shape { bits: 0, weight: 0 };
        let mut result = ProjectivePoint::IDENTITY;
        if let Some(input) = self.produced {
            if self.kind == WorkKind::Prepare {
                assert_scratch("source scalars", self.terms, source.scalars.len());
            }
            if input.indexed && matches!(self.kind, WorkKind::Prepare | WorkKind::Window) {
                assert_scratch("source indices", self.terms, source.indices.len());
                let mut first = 0;
                while first < self.terms {
                    let indices = source
                        .indices
                        .contiguous_prefix(first..self.terms)
                        .filter(|s| !s.is_empty())
                        .unwrap_or_else(|| {
                            core::slice::from_ref(
                                source.indices.get(first).expect("invalid source view"),
                            )
                        });
                    for (position, &index) in indices.iter().enumerate() {
                        if u64::from(index) >= input.bases.len() as u64 {
                            return Err(CurveError::BaseIndexOutOfBounds {
                                position: self.offset + first + position,
                                index,
                                bases: input.bases.len(),
                            });
                        }
                    }
                    first += indices.len();
                }
            }
        }
        match self.kind {
            WorkKind::Prepare => {
                let digit_len = self.plan.cached(self.input, geometry).is_none().then(|| {
                    let len = geometry
                        .storage_len(self.terms)
                        .expect("bounded plan geometry");
                    assert_scratch("digits", len, scratch.digits.len());
                    len
                });
                let records = if self.produced.is_some() {
                    assert_scratch("scalars", self.terms, scratch.scalars.len());
                    let records = &mut scratch.scalars[..self.terms];
                    let mut first = 0;
                    while first < self.terms {
                        if let Some(values) = source
                            .scalars
                            .contiguous_prefix(first..self.terms)
                            .filter(|s| !s.is_empty())
                        {
                            prepared::prepare_chunk(
                                Scalars::Raw(values),
                                &mut records[first..first + values.len()],
                            );
                            first += values.len();
                        } else {
                            records[first] = ScalarStorage::field(
                                source.scalars.get(first).expect("invalid source view"),
                            );
                            first += 1;
                        }
                    }
                    records as &[_]
                } else {
                    let source = self
                        .input
                        .scalars
                        .slice(self.offset..self.offset + self.terms);
                    match source {
                        Scalars::Prepared(s) => s.records,
                        _ => {
                            assert_scratch("scalars", self.terms, scratch.scalars.len());
                            let records = &mut scratch.scalars[..self.terms];
                            prepared::prepare_chunk(source, records);
                            records
                        }
                    }
                };
                shape = Shape::of(records);
                if let Some(len) = digit_len {
                    recode::write_bases(
                        records,
                        geometry,
                        &mut scratch.digits[..len],
                        self.input.bases,
                    );
                }
            }
            WorkKind::Window => {
                let records = match self.input.scalars {
                    Scalars::Prepared(s) => Some(&s.records[self.offset..self.offset + self.terms]),
                    _ => None,
                };
                let records: &dyn ReadView<ScalarStorage<C>> = records
                    .as_ref()
                    .map_or(buffers_records, |r| r as &dyn ReadView<_>);
                let cache = self.plan.cached(self.input, geometry);
                let digits: &dyn ReadView<u8> =
                    cache.as_ref().map_or(digits, |d| d as &dyn ReadView<_>);
                assert_scratch("scalars", self.terms, records.len());
                let digit_len = geometry
                    .storage_len(self.terms)
                    .expect("bounded plan geometry");
                assert_scratch("digits", digit_len, digits.len());
                let task = kernels::Task {
                    offset: self.offset,
                    window: self.window,
                    pass: self.plan.job.pass.min(self.terms),
                    geometry,
                    accumulation: self.plan.job.accumulation,
                };
                if self.plan.options.streaming() {
                    assert_scratch("projective", geometry.buckets(), buckets.len());
                    let buckets = &mut buckets[..geometry.buckets()];
                    if self.first_chunk {
                        buckets.fill(ProjectivePoint::IDENTITY);
                    }
                    if let Some(input) = self.produced {
                        kernels::stream_selected(
                            &kernels::BaseView {
                                bases: input.bases,
                                indices: input.indexed.then_some(kernels::Indices::Fragment {
                                    view: source.indices,
                                    offset: self.offset,
                                }),
                            },
                            self.terms,
                            fragmented::Fragmented::new(digits, digit_len),
                            task,
                            buckets,
                        );
                    } else if let Some(digits) = digits.contiguous(0..digit_len) {
                        kernels::stream(&self.input, self.terms, digits, task, buckets);
                    } else {
                        kernels::stream_view(
                            &self.input,
                            self.terms,
                            fragmented::Fragmented::new(digits, digit_len),
                            task,
                            buckets,
                        );
                    }
                } else {
                    assert_scratch("partial output", 1, output.len());
                    let scratch = scratch.checked(self.plan.temporary());
                    let work = &mut kernels::Work {
                        affine: scratch.affine,
                        projective: scratch.projective,
                        field: scratch.field,
                        indices: scratch.indices,
                    };
                    output[0] = if matches!(geometry, Geometry::Booth(_))
                        && self.scalar_bits <= 64
                        && (self.scalar_bits == 0
                            || self.window * geometry.width() > usize::from(self.scalar_bits) + 1)
                    {
                        // A centered carry can reach a window starting at bits + 1.
                        // Prepare's completed maximum bounds both signed halves
                        // only through 64 bits; keep every original partial slot.
                        ProjectivePoint::IDENTITY
                    } else if let Some(input) = self.produced {
                        kernels::run_selected(
                            &kernels::BaseView {
                                bases: input.bases,
                                indices: input.indexed.then_some(kernels::Indices::Fragment {
                                    view: source.indices,
                                    offset: self.offset,
                                }),
                            },
                            fragmented::Fragmented::new(records, self.terms),
                            fragmented::Fragmented::new(digits, digit_len),
                            task,
                            work,
                        )
                    } else {
                        match (
                            records.contiguous(0..self.terms),
                            digits.contiguous(0..digit_len),
                        ) {
                            (Some(records), Some(digits)) => {
                                kernels::run(&self.input, records, digits, task, work)
                            }
                            _ => kernels::run_view(
                                &self.input,
                                fragmented::Fragmented::new(records, self.terms),
                                fragmented::Fragmented::new(digits, digit_len),
                                task,
                                work,
                            ),
                        }
                    };
                }
            }
            WorkKind::Collapse => {
                assert_scratch("projective", geometry.buckets(), buckets.len());
                assert_scratch("partial output", 1, output.len());
                output[0] = kernels::collapse_projective(&buckets[..geometry.buckets()]);
            }
            WorkKind::Reduce => {
                assert_scratch("partial inputs", geometry.windows(), partials.len());
                for window in (0..geometry.windows()).rev() {
                    let partial = partials
                        .get(window)
                        .expect("invalid fragmented partial view");
                    for _ in 0..geometry.width() {
                        result = result.double();
                    }
                    result = result.add(partial);
                }
            }
        }
        Ok((shape, result))
    }
}

impl<C: PastaCurve, R: Resources<C>> Kernel<R> for MsmKernel<'_, C> {
    type Output = MsmOutput<C>;
    fn execute(&mut self, resources: &mut R) -> Self::Output {
        resources.with_source(|buffers, source| MsmOutput(self.run(buffers, source)))
    }
}

/// Returned leases and operation publication after one task completes.
pub struct Published<C: PastaCurve, R> {
    /// All task resources, ready for provider release or retained handoff.
    pub resources: R,
    /// Arithmetic validation error, if any; the run is then failed.
    pub error: Option<CurveError>,
    /// Kernel execution status, including panic or cancellation.
    pub outcome: Outcome,
    /// Final result, present only on the completion that finishes this MSM.
    pub result: Option<ProjectivePoint<C>>,
}

/// One bound MSM invocation with incremental local dependencies.
///
/// Caller-owned frontier storage bounds detached tasks. Its size controls
/// dispatch capacity, not geometry or scratch provisioning. Preparation readies
/// this input's windows immediately, and its final reduction releases a result
/// without waiting for other operations. Retained chunk storage can be reused
/// after every window consuming it has completed. Streaming bucket storage
/// remains retained through the final collapse.
pub struct MsmRun<'a, 'i, C: PastaCurve> {
    input: Input<'i, C>,
    produced: Option<ProducedInput<'i, C>>,
    plan: MsmPlan<C>,
    frontier: Frontier<'a>,
    kind: WorkKind,
    offset: usize,
    start: usize,
    end: usize,
    geometry: Geometry,
    shape: Shape,
    result: ProjectivePoint<C>,
    complete: bool,
    failed: bool,
}

impl<'a, 'i, C: PastaCurve> MsmRun<'a, 'i, C> {
    /// Binds an input and exclusive run metadata without touching arithmetic buffers.
    ///
    /// The input must satisfy the plan's requirements (see [`MsmPlan::for_input`]),
    /// and frontier storage must be nonempty. Panics for incompatible input or
    /// empty frontier storage.
    pub fn new(
        plan: MsmPlan<C>,
        input: Input<'i, C>,
        identity: &'a mut Identity,
        storage: &'a mut [TaskStorage],
    ) -> Self {
        assert_eq!(input.len(), plan.terms, "input must match the plan");
        Self::bind_range(plan, input, 0..input.len(), identity, storage)
    }

    /// Binds an independently scheduled partition of a validated input.
    ///
    /// The plan describes the full input and fixes geometry; `range` selects the terms
    /// contributed by this run. Partition results can be reduced outside the scheduler.
    /// Each live partition needs its own retained storage and metadata. Nonempty
    /// partial ranges discard a whole-input digit cache; plans that require that cache
    /// cannot bind those ranges. Empty ranges complete with the identity. Scalar
    /// records remain reusable. Panics if the range is reversed or outside the input.
    /// Input and frontier requirements follow [`Self::new`].
    pub fn new_partition(
        plan: MsmPlan<C>,
        input: Input<'i, C>,
        range: core::ops::Range<usize>,
        identity: &'a mut Identity,
        storage: &'a mut [TaskStorage],
    ) -> Self {
        assert_eq!(input.len(), plan.terms, "input must match the plan");
        assert!(
            range.start <= range.end && range.end <= input.len(),
            "invalid partition"
        );
        Self::bind_range(plan, input, range, identity, storage)
    }

    /// Binds source metadata before producer tasks have filled scalar rows.
    ///
    /// Source availability is enforced by the provider at `try_claim`. Plan
    /// compatibility and frontier requirements follow [`Self::new`].
    pub fn new_produced(
        plan: MsmPlan<C>,
        input: ProducedInput<'i, C>,
        identity: &'a mut Identity,
        storage: &'a mut [TaskStorage],
    ) -> Self {
        Self::new_produced_partition(plan, input, 0..input.len(), identity, storage)
    }

    /// Binds an independent partition whose sources arrive from producers.
    ///
    /// Plan compatibility, range, and frontier requirements follow
    /// [`Self::new_partition`]. No resources are acquired here.
    pub fn new_produced_partition(
        plan: MsmPlan<C>,
        input: ProducedInput<'i, C>,
        range: core::ops::Range<usize>,
        identity: &'a mut Identity,
        storage: &'a mut [TaskStorage],
    ) -> Self {
        assert_eq!(input.len(), plan.terms, "input must match the plan");
        assert!(
            range.start <= range.end && range.end <= input.len(),
            "invalid partition"
        );
        let mut run = Self::bind_range(plan, input.metadata(), range, identity, storage);
        run.produced = Some(input);
        run
    }

    fn bind_range(
        plan: MsmPlan<C>,
        mut input: Input<'i, C>,
        range: core::ops::Range<usize>,
        identity: &'a mut Identity,
        storage: &'a mut [TaskStorage],
    ) -> Self {
        // Empty parallel slots do no arithmetic and can retain a required cache.
        if !range.is_empty()
            && range != (0..input.len())
            && let Scalars::Prepared(ref mut prepared) = input.scalars
        {
            *prepared = prepared.without_cache();
        }
        assert!(
            plan.accepts(input),
            "input must match the plan's preparation"
        );
        let complete = range.is_empty();
        let frontier = Frontier::new(
            identity,
            storage,
            range.len().min(plan.cap).div_ceil(recode::CHUNK),
        );
        Self {
            input,
            produced: None,
            plan,
            frontier,
            kind: WorkKind::Prepare,
            offset: range.start,
            start: range.start,
            end: range.end,
            geometry: plan.initial_geometry(input),
            shape: Shape { bits: 0, weight: 0 },
            result: ProjectivePoint::IDENTITY,
            complete,
            failed: false,
        }
    }

    /// Writes a bounded number of ready requests, with no task allocation.
    pub fn ready(&self, output: &mut [Option<Request<'a>>]) -> usize {
        self.ready_from(0, output)
    }

    /// Continues a bounded readiness scan at a task index in the current
    /// epoch. Pass one past the last returned key's index to inspect later
    /// requests when the output buffer is smaller than the frontier. Restart
    /// at zero after publishing a completion, which may change dependencies.
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
            let chunk_terms = self.plan.cap.min(self.end - self.offset);
            let scalar_start = if self.kind == WorkKind::Prepare {
                key.index() * recode::CHUNK
            } else {
                0
            };
            let digit_start = scalar_start * self.geometry.stride();
            let terms = if self.kind == WorkKind::Prepare {
                (chunk_terms - scalar_start).min(recode::CHUNK)
            } else {
                chunk_terms
            };
            let mut scratch = Requirements::default();
            let mut read_scalars = 0;
            let mut read_digits = 0;
            let mut buckets = 0;
            match self.kind {
                WorkKind::Prepare => {
                    if !matches!(self.input.scalars, Scalars::Prepared(_)) {
                        scratch.scalars = terms;
                    }
                    if self.plan.cached(self.input, self.geometry).is_none() {
                        scratch.digits = self.geometry.storage_len(terms).unwrap();
                    }
                }
                WorkKind::Window => {
                    if !matches!(self.input.scalars, Scalars::Prepared(_)) {
                        read_scalars = terms;
                    }
                    if self.plan.cached(self.input, self.geometry).is_none() {
                        read_digits = self.geometry.storage_len(terms).unwrap();
                    }
                    scratch = self.plan.temporary();
                    if self.plan.options.streaming() {
                        buckets = self.geometry.buckets();
                    }
                }
                WorkKind::Collapse => buckets = self.geometry.buckets(),
                WorkKind::Reduce => {}
            }
            output[written] = Some(Request {
                key,
                #[cfg(test)]
                kind: self.kind,
                offset: self.offset + scalar_start,
                terms,
                scalar_start,
                digit_start,
                window: key.index(),
                bucket_start: key.index()
                    * if self.plan.options.streaming() {
                        self.geometry.buckets()
                    } else {
                        0
                    },
                output_slot: (self.kind == WorkKind::Collapse
                    || self.kind == WorkKind::Window && !self.plan.options.streaming())
                .then_some(key.index()),
                scratch,
                read_scalars,
                read_digits,
                buckets,
                source_scalars: if self.produced.is_some() && self.kind == WorkKind::Prepare {
                    terms
                } else {
                    0
                },
                source_indices: if self.produced.is_some_and(|input| input.indexed)
                    && matches!(self.kind, WorkKind::Prepare | WorkKind::Window)
                {
                    terms
                } else {
                    0
                },
                read_partials: if self.kind == WorkKind::Reduce {
                    self.geometry.windows()
                } else {
                    0
                },
            });
            written += 1;
        }
        written
    }

    /// Detaches a task after atomic acquisition of its complete resource bundle.
    /// Failed acquisition leaves the request ready. Use only requests obtained
    /// from this run; stale and duplicate keys are rejected before acquisition.
    pub fn try_claim<R: Resources<C>>(
        &mut self,
        request: Request<'a>,
        acquire: impl FnOnce() -> Option<R>,
    ) -> Result<Option<Task<'a, MsmKernel<'i, C>, R>>, TaskError> {
        let kernel = self.kernel(request)?;
        self.frontier.try_claim(request.key, kernel, acquire)
    }

    fn kernel(&self, request: Request<'a>) -> Result<MsmKernel<'i, C>, TaskError> {
        if self.failed {
            return Err(TaskError::Failed);
        }
        self.frontier.check_key(request.key)?;
        let start = if self.kind == WorkKind::Prepare {
            request.key.index() * recode::CHUNK
        } else {
            0
        };
        let terms = self.plan.cap.min(self.end - self.offset) - start;
        let terms = if self.kind == WorkKind::Prepare {
            terms.min(recode::CHUNK)
        } else {
            terms
        };
        Ok(MsmKernel {
            input: self.input,
            produced: self.produced,
            plan: self.plan,
            kind: self.kind,
            offset: self.offset + start,
            terms,
            window: request.key.index(),
            geometry: self.geometry,
            first_chunk: self.offset == self.start,
            scalar_bits: self.shape.bits,
        })
    }

    /// Publishes completion, returns owned leases, and readies local successors.
    ///
    /// Failed or foreign receipts follow the [`crate::exec::execution`] completion
    /// protocol. Resource validation failure poisons the run and publishes no
    /// arithmetic result.
    #[expect(
        clippy::result_large_err,
        reason = "return owned receipts without allocation"
    )]
    pub fn complete<R>(
        &mut self,
        completion: Completion<'a, R, MsmOutput<C>>,
    ) -> Result<Published<C, R>, crate::exec::execution::PublishError<'a, R, MsmOutput<C>>> {
        let completed = self.frontier.complete(completion)?;
        let mut error = None;
        self.failed |= completed.outcome != Outcome::Success;
        if let Some(MsmOutput(output)) = completed.output {
            match output {
                Ok((shape, partial)) => {
                    if self.kind == WorkKind::Prepare {
                        self.shape.bits = self.shape.bits.max(shape.bits);
                        self.shape.weight = self.shape.weight.saturating_add(shape.weight);
                    } else if self.kind == WorkKind::Reduce {
                        self.result = self.result.add(&partial);
                    }
                }
                Err(e) => {
                    self.failed = true;
                    error = Some(e);
                }
            }
        }
        if !self.failed && self.frontier.is_complete() {
            let total = match self.kind {
                WorkKind::Prepare => {
                    if !self.plan.options.streaming()
                        && self.plan.specialize_short
                        && self.plan.cached(self.input, self.geometry).is_none()
                    {
                        let actual = Geometry::for_shape(
                            self.plan.cap.min(self.end - self.offset),
                            self.shape,
                            self.plan.options,
                        );
                        if matches!(actual, Geometry::Short(_)) {
                            self.geometry = actual;
                        }
                    }
                    self.kind = WorkKind::Window;
                    self.geometry.windows()
                }
                WorkKind::Window if !self.plan.options.streaming() => {
                    self.kind = WorkKind::Reduce;
                    1
                }
                WorkKind::Window => {
                    if self.end - self.offset > self.plan.cap {
                        self.offset += self.plan.cap;
                        self.kind = WorkKind::Prepare;
                        self.shape = Shape { bits: 0, weight: 0 };
                        self.plan
                            .cap
                            .min(self.end - self.offset)
                            .div_ceil(recode::CHUNK)
                    } else {
                        self.kind = WorkKind::Collapse;
                        self.geometry.windows()
                    }
                }
                WorkKind::Collapse => {
                    self.kind = WorkKind::Reduce;
                    1
                }
                WorkKind::Reduce => {
                    if !self.plan.options.streaming() && self.end - self.offset > self.plan.cap {
                        self.offset += self.plan.cap;
                        self.geometry = self.plan.initial_geometry(self.input);
                        self.kind = WorkKind::Prepare;
                        self.shape = Shape { bits: 0, weight: 0 };
                        self.plan
                            .cap
                            .min(self.end - self.offset)
                            .div_ceil(recode::CHUNK)
                    } else {
                        self.complete = true;
                        0
                    }
                }
            };
            if self.frontier.restart(total).is_err() {
                self.failed = true;
                error = Some(CurveError::SizeOverflow);
            }
        }
        Ok(Published {
            resources: completed.resources,
            error,
            outcome: completed.outcome,
            result: self.result(),
        })
    }

    /// Final result, including identity for an empty input; absent on failure.
    pub fn result(&self) -> Option<ProjectivePoint<C>> {
        (self.complete && !self.failed).then_some(self.result)
    }

    /// Whether a failed kernel or invalid resource bundle poisoned this run.
    pub fn is_failed(&self) -> bool {
        self.failed
    }

    /// Number of detached tasks still requiring publication or draining.
    pub fn inflight(&self) -> usize {
        self.frontier.inflight()
    }

    /// Rebinds completed metadata to another planned invocation.
    ///
    /// Epochs are preserved so old task keys remain stale. Consumers must release
    /// retained buffers before the application reuses their storage. The input
    /// must satisfy the plan's requirements, as for [`Self::new`].
    ///
    /// Returns [`TaskError::Busy`] before completion, [`TaskError::Failed`] on failure,
    /// or [`TaskError::Overflow`] if the epoch cannot advance.
    pub fn rebind(&mut self, plan: MsmPlan<C>, input: Input<'i, C>) -> Result<(), TaskError> {
        assert_eq!(input.len(), plan.terms, "input must match the plan");
        self.rebind_range(plan, input, 0..input.len())
    }

    /// Reuses completed metadata for another produced scalar row.
    ///
    /// The old row's consumers must have released their source leases.
    /// Input, error, and panic contracts match [`Self::rebind`].
    pub fn rebind_produced(
        &mut self,
        plan: MsmPlan<C>,
        input: ProducedInput<'i, C>,
    ) -> Result<(), TaskError> {
        self.rebind_produced_partition(plan, input, 0..input.len())
    }

    /// Reuses a completed partition while preserving stale-key detection.
    ///
    /// The range must be ordered and contained in the input; violations panic.
    /// Input and lifecycle contracts follow [`Self::rebind`].
    pub fn rebind_produced_partition(
        &mut self,
        plan: MsmPlan<C>,
        input: ProducedInput<'i, C>,
        range: core::ops::Range<usize>,
    ) -> Result<(), TaskError> {
        assert_eq!(input.len(), plan.terms, "input must match the plan");
        assert!(
            range.start <= range.end && range.end <= input.len(),
            "partition must lie within the input"
        );
        self.rebind_range(plan, input.metadata(), range)?;
        self.produced = Some(input);
        Ok(())
    }

    fn rebind_range(
        &mut self,
        plan: MsmPlan<C>,
        mut input: Input<'i, C>,
        range: core::ops::Range<usize>,
    ) -> Result<(), TaskError> {
        if self.failed {
            return Err(TaskError::Failed);
        }
        if !self.complete {
            return Err(TaskError::Busy);
        }
        let complete = range.is_empty();
        if !complete
            && range != (0..input.len())
            && let Scalars::Prepared(ref mut prepared) = input.scalars
        {
            *prepared = prepared.without_cache();
        }
        assert!(plan.accepts(input), "input preparation must match the plan");
        self.frontier
            .restart(range.len().min(plan.cap).div_ceil(recode::CHUNK))?;
        self.input = input;
        self.produced = None;
        self.plan = plan;
        self.geometry = plan.initial_geometry(input);
        self.shape = Shape { bits: 0, weight: 0 };
        self.offset = range.start;
        self.start = range.start;
        self.end = range.end;
        self.kind = WorkKind::Prepare;
        self.result = ProjectivePoint::IDENTITY;
        self.complete = complete;
        Ok(())
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
pub(crate) mod test_buffers;
