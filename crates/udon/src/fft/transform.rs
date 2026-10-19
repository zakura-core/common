use super::factors::{Factors, InverseFinish};
use super::planning::Geometry;
use super::{
    CoefficientView, CosetDomain, Executor, FftError, PastaField, PrimeModulus, Strategy, Tables,
    bit_reverse,
};
#[cfg(test)]
use super::{assert_length, check_prefix};
use crate::exec::{TaskBudget, for_each_chunk_mut};
use crate::field::pasta::butterfly::{butterfly, divide_by_power_of_two, scale as scale_loose};

/// Reusable transform metadata borrowing caller-prepared tables.
///
/// For size `n`, root `w`, and shift `s` from [`Self::domain`], the forward
/// transform maps coefficients `c[i]` to `sum(c[i] * (s * w^j)^i, i = 0..n)`
/// at evaluation index `j`. The inverse recovers the coefficients, including
/// division by `n` and removal of the shift, unless an explicit
/// [`super::InverseScale`] selects an unscaled inverse. Natural order means
/// increasing degree for coefficients and increasing `j` for evaluations;
/// methods accepting other orders document them. A singleton transform preserves
/// its sole value.
///
/// Transforms can be shared across executions with independent mutable buffers. Every
/// full input and output slice must contain exactly `n` fields. [`Self::execute`]
/// accepts shorter coefficient or evaluation inputs through
/// [`super::TransformRequest`]. Direct transforms adapt to scratch capacity;
/// [`Self::scratch_requirements`] reports the preferred size under the given resource
/// limits. [`super::execution::FftPlan::retained_fields`] sizes the fixed workspace of a
/// resolved plan. Direct transforms accept empty scratch. Resolved plans require their
/// declared workspace. Buffer contract violations panic before writes; request
/// validation follows [`Self::execute`].
///
/// Table contents follow [`Tables`]' validity contract. The module's
/// [validation and working-storage rules](super) apply to all executions,
/// including errors and panics.
#[derive(Clone, Copy)]
pub struct Transform<'a, M: PrimeModulus> {
    pub(super) domain: CosetDomain<M>,
    pub(super) tables: Tables<'a, M>,
}

impl<M: PrimeModulus> core::fmt::Debug for Transform<'_, M> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Transform")
            .field("domain", &self.domain)
            .field("tables", &self.tables)
            .finish()
    }
}

impl<'a, M: PrimeModulus> Transform<'a, M> {
    // A detached column task has already gathered its complete panel. It
    // never joins or obtains scratch while executing this bounded kernel.
    pub(super) fn columns(
        self,
        values: &mut [PastaField<M>],
        first_column: usize,
        tile_len: usize,
        inverse: bool,
        normalized: bool,
        first: usize,
    ) {
        let geometry = Geometry {
            tile_len,
            tiles: self.domain.size() / tile_len,
            columns: values.len() / (self.domain.size() / tile_len),
            jobs: 1,
        };
        let mut run = if normalized {
            Run::inverse(&[])
        } else if inverse {
            Run::INVERSE_UNSCALED
        } else {
            Run::forward(2)
        };
        run.set_first(first);
        let finish = if normalized {
            InverseFinish::select(self.domain, self.tables.inverse_finish.is_some())
        } else {
            InverseFinish::Outputs(Factors::Identity)
        };
        Kernel {
            plan: self,
            run,
            finish,
        }
        .cross(values, first_column, &geometry);
    }
    // The complete transform fits the planner's bounded local grain.
    pub(super) fn local(self, values: &mut [PastaField<M>], inverse: bool, first: usize) {
        let mut run = if inverse {
            Run::inverse(&[])
        } else {
            Run::forward(first)
        };
        run.set_first(first);
        let finish = if inverse {
            InverseFinish::select(self.domain, self.tables.inverse_finish.is_some())
        } else {
            InverseFinish::Outputs(Factors::Identity)
        };
        Kernel {
            plan: self,
            run,
            finish,
        }
        .local(values);
    }
    /// Constructs a transform that computes powers and permutations as needed.
    pub fn new(domain: CosetDomain<M>) -> Self {
        Self {
            domain,
            tables: Tables::default(),
        }
    }

    /// The evaluation domain, including its coset shift.
    pub const fn domain(self) -> CosetDomain<M> {
        self.domain
    }

    /// Preferred scratch field count for either full in-place transform direction.
    ///
    /// Counts initialized field elements. Direct execution can use smaller storage
    /// and select another implementation. The query does not allocate or reserve
    /// storage; it resolves a contiguous transform through
    /// [`super::execution::FftPlan::new`], with its planning errors.
    pub fn scratch_requirements(
        self,
        options: crate::exec::ExecutionOptions,
    ) -> Result<usize, FftError> {
        Ok(super::execution::FftPlan::new(
            self,
            super::TransformRequest::new(super::Direction::Forward),
            super::StorageLayout::Contiguous,
            options,
        )?
        .retained_fields())
    }

    /// Replaces natural-order coefficients with coset evaluations in natural order.
    ///
    /// `values` must have the domain's size. Resource limits, errors, and buffer
    /// state follow [`Self::execute`] with a full in-place forward request.
    pub fn forward<E: Executor>(
        self,
        values: &mut [PastaField<M>],
        options: crate::exec::ExecutionOptions,
        executor: &E,
        scratch: &mut [PastaField<M>],
    ) -> Result<(), FftError> {
        self.execute(
            super::TransformRequest::new(super::Direction::Forward),
            None,
            values,
            options,
            executor,
            scratch,
        )
    }

    /// Replaces natural-order evaluations with normalized natural coefficients.
    ///
    /// `values` must have the domain's size. Resource limits, errors, and buffer
    /// state follow [`Self::execute`] with a full in-place inverse request.
    pub fn inverse<E: Executor>(
        self,
        values: &mut [PastaField<M>],
        options: crate::exec::ExecutionOptions,
        executor: &E,
        scratch: &mut [PastaField<M>],
    ) -> Result<(), FftError> {
        self.execute(
            super::TransformRequest::new(super::Direction::Inverse),
            None,
            values,
            options,
            executor,
            scratch,
        )
    }

    /// Executes a mathematical request within the supplied resource constraints.
    ///
    /// `values` must have the domain's size. Supply `input` exactly when
    /// [`super::InputStorage::Preserve`] is requested, with the full domain size
    /// or the declared prefix length. Forward initialization applies its
    /// [`CoefficientView::normalization_factor`]; inverse input must have factor
    /// one. In-place prefixes ignore and overwrite the remaining values.
    /// Scratch, including an empty slice, limits the implementation selected for
    /// this call; unused scratch tails are untouched.
    ///
    /// Request errors follow [`super::execution::FftPlan::new`]. Violating the input or
    /// buffer requirements panics. These checks and returned errors precede writes. An
    /// executor panic may partially change data; the module's [working-storage
    /// rules](super) describe validity during unwinding.
    pub fn execute<E: Executor>(
        self,
        request: super::TransformRequest,
        input: Option<CoefficientView<'_, M>>,
        values: &mut [PastaField<M>],
        options: crate::exec::ExecutionOptions,
        executor: &E,
        scratch: &mut [PastaField<M>],
    ) -> Result<(), FftError> {
        let options = options.for_scratch::<PastaField<M>>(scratch.len());
        let mut plan = super::execution::FftPlan::new(
            self,
            request,
            super::StorageLayout::Contiguous,
            options,
        )?;
        if let Some(input) = input {
            if request.direction == super::Direction::Forward {
                plan = plan.with_input_scale(input.normalization_factor());
            } else {
                assert_eq!(
                    input.normalization_factor().reduce(),
                    PastaField::<M>::ONE.reduce(),
                    "inverse input must be normalized"
                );
            }
        }
        plan.execute(
            input.map(|view| view.as_slice()),
            values,
            None,
            scratch,
            executor,
        );
        Ok(())
    }

    /// Required scratch field count for either transform direction.
    ///
    /// Delegates to [`Strategy::requirements`] with this domain's size.
    /// That query also sizes arrays in const contexts without constructing a plan.
    ///
    /// Returns [`FftError::InvalidExecution`] for invalid [`Strategy`],
    /// or [`FftError::SizeOverflow`] if the scratch field slice would exceed
    /// `isize::MAX` bytes or its element count overflows `usize`.
    pub(super) const fn scratch_requirements_with(
        self,
        options: Strategy,
    ) -> Result<usize, FftError> {
        options.requirements(self.domain.size())
    }

    #[cfg(test)]
    fn check(
        self,
        buffer: &'static str,
        len: usize,
        options: Strategy,
        scratch_len: usize,
    ) -> Result<usize, FftError> {
        assert_length(buffer, self.domain.size(), len);
        let required = self.scratch_requirements_with(options)?;
        super::check_scratch(required, scratch_len);
        Ok(required)
    }

    /// Replaces natural-order coefficients with natural-order coset evaluations.
    ///
    /// Buffer lengths, errors, and the evaluation formula are defined by [`Transform`].
    #[cfg(test)]
    pub(in crate::fft) fn forward_with<E: Executor>(
        self,
        values: &mut [PastaField<M>],
        options: Strategy,
        executor: &E,
        scratch: &mut [PastaField<M>],
    ) -> Result<(), FftError> {
        let required = self.check("values", values.len(), options, scratch.len())?;
        self.bounded(
            options,
            super::TransformRequest::new(super::Direction::Forward),
            false,
        )?
        .execute_with(
            None,
            values,
            None,
            &mut scratch[..required],
            core::num::NonZeroUsize::new(options.max_tasks).unwrap(),
            executor,
        );
        Ok(())
    }

    /// Replaces natural-order evaluations with normalized polynomial coefficients.
    ///
    /// Both sides use the ordering, lengths, and error contract of [`Transform`].
    #[cfg(test)]
    pub(in crate::fft) fn inverse_with<E: Executor>(
        self,
        values: &mut [PastaField<M>],
        options: Strategy,
        executor: &E,
        scratch: &mut [PastaField<M>],
    ) -> Result<(), FftError> {
        let required = self.check("values", values.len(), options, scratch.len())?;
        self.bounded(
            options,
            super::TransformRequest::new(super::Direction::Inverse),
            false,
        )?
        .execute_with(
            None,
            values,
            None,
            &mut scratch[..required],
            core::num::NonZeroUsize::new(options.max_tasks).unwrap(),
            executor,
        );
        Ok(())
    }

    /// Interpolates evaluations already stored in bit-reversed order.
    ///
    /// This avoids a permutation when a caller scatters evaluations directly
    /// into their working positions. Evaluation
    /// row `j` must be stored at the reversal of its low `log2(n)` bits, where
    /// `n` is the domain size. Output coefficients are in increasing degree
    /// order, with the same normalization, lengths, and errors as [`Self::inverse`].
    #[cfg(test)]
    pub(in crate::fft) fn inverse_bit_reversed_with<E: Executor>(
        self,
        values: &mut [PastaField<M>],
        options: Strategy,
        executor: &E,
        scratch: &mut [PastaField<M>],
    ) -> Result<(), FftError> {
        let required = self.check("values", values.len(), options, scratch.len())?;
        let mut request = super::TransformRequest::new(super::Direction::Inverse);
        request.input_order = super::ElementOrder::BitReversed;
        self.bounded(options, request, false)?.execute_with(
            None,
            values,
            None,
            &mut scratch[..required],
            core::num::NonZeroUsize::new(options.max_tasks).unwrap(),
            executor,
        );
        Ok(())
    }

    /// Preserves the coefficients and writes their transform into `output`.
    ///
    /// Accepts ordinary coefficients or a [`CoefficientView`], whose scale is
    /// folded into output initialization.
    /// Both input and output must have the domain size. Ordering, scratch
    /// requirements, and errors are the same as for [`Self::forward`].
    #[cfg(test)]
    pub(in crate::fft) fn forward_into_with<'input, E: Executor>(
        self,
        input: impl Into<CoefficientView<'input, M>>,
        output: &mut [PastaField<M>],
        options: Strategy,
        executor: &E,
        scratch: &mut [PastaField<M>],
    ) -> Result<(), FftError> {
        let input = input.into();
        let extra = input.normalization_factor();
        let input = input.as_slice();
        assert_length("input", self.domain.size(), input.len());
        let required = self.check("output", output.len(), options, scratch.len())?;
        self.bounded(
            options,
            super::TransformRequest::new(super::Direction::Forward),
            true,
        )?
        .with_input_scale(extra)
        .execute_with(
            Some(input),
            output,
            None,
            &mut scratch[..required],
            core::num::NonZeroUsize::new(options.max_tasks).unwrap(),
            executor,
        );
        Ok(())
    }

    /// Preserves the evaluations and writes their interpolation into `output`.
    ///
    /// Both slices must have the domain size. Ordering, scratch requirements,
    /// and errors are the same as for [`Self::inverse`].
    #[cfg(test)]
    pub(in crate::fft) fn inverse_into_with<E: Executor>(
        self,
        input: &[PastaField<M>],
        output: &mut [PastaField<M>],
        options: Strategy,
        executor: &E,
        scratch: &mut [PastaField<M>],
    ) -> Result<(), FftError> {
        assert_length("input", self.domain.size(), input.len());
        let required = self.check("output", output.len(), options, scratch.len())?;
        self.bounded(
            options,
            super::TransformRequest::new(super::Direction::Inverse),
            true,
        )?
        .execute_with(
            Some(input),
            output,
            None,
            &mut scratch[..required],
            core::num::NonZeroUsize::new(options.max_tasks).unwrap(),
            executor,
        );
        Ok(())
    }

    /// Evaluates a coefficient prefix, treating the remaining coefficients as zero.
    ///
    /// Input uses increasing degree order. Accepts ordinary coefficients or a
    /// [`CoefficientView`], including one retained by a smaller expansion; its
    /// scale is folded into initialization.
    ///
    /// An empty prefix produces the zero polynomial; a prefix longer than the
    /// domain returns [`FftError::InvalidPrefix`]. Output uses natural evaluation
    /// order and must have the full domain size. Scratch requirements and other
    /// errors are those of [`Self::forward`], even for an empty prefix.
    #[cfg(test)]
    pub(in crate::fft) fn forward_prefix_with<'input, E: Executor>(
        self,
        coefficients: impl Into<CoefficientView<'input, M>>,
        output: &mut [PastaField<M>],
        options: Strategy,
        executor: &E,
        scratch: &mut [PastaField<M>],
    ) -> Result<(), FftError> {
        let coefficients = coefficients.into();
        let extra = coefficients.normalization_factor();
        let coefficients = coefficients.as_slice();
        let required = self.check("output", output.len(), options, scratch.len())?;
        check_prefix(coefficients.len(), 0, self.domain.size())?;
        let mut request = super::TransformRequest::new(super::Direction::Forward);
        request.support = super::InputSupport::Prefix(coefficients.len());
        self.bounded(options, request, true)?
            .with_input_scale(extra)
            .execute_with(
                Some(coefficients),
                output,
                None,
                &mut scratch[..required],
                core::num::NonZeroUsize::new(options.max_tasks).unwrap(),
                executor,
            );
        Ok(())
    }

    fn bounded(
        self,
        options: Strategy,
        request: super::TransformRequest,
        separate: bool,
    ) -> Result<super::execution::FftPlan<'a, M>, FftError> {
        let nz = |n| core::num::NonZeroUsize::new(n).unwrap();
        super::execution::FftPlan::with_strategy(
            self,
            crate::fft::TransformRequest {
                input_storage: if separate {
                    crate::fft::InputStorage::Preserve
                } else {
                    crate::fft::InputStorage::InPlace
                },
                ..request
            },
            nz(options.tile_len),
            super::Codelet::Radix2,
        )?
        .with_contiguous_permutation()
        .with_columns(nz(options.columns_per_task), nz(options.max_tasks))
    }

    #[cfg(test)]
    pub(super) fn scatter(self, input: &[PastaField<M>], output: &mut [PastaField<M>]) {
        for (index, &value) in input.iter().enumerate() {
            output[self.reversed(index)] = value;
        }
    }

    pub(super) fn permute(self, values: &mut [PastaField<M>]) {
        for index in 0..values.len() {
            let destination = self.reversed(index);
            if index < destination {
                values.swap(index, destination);
            }
        }
    }

    pub(super) fn reversed(self, index: usize) -> usize {
        bit_reverse(index, self.domain.domain().log_size())
    }

    #[cfg(test)]
    pub(super) fn scale_coefficients(self, values: &mut [PastaField<M>], extra: PastaField<M>) {
        let shift = self.domain.shift();
        if shift.reduce() == PastaField::<M>::ONE.reduce()
            && extra.reduce() == PastaField::<M>::ONE.reduce()
        {
            return;
        }
        let cycle = [extra, extra.mul(&shift), extra.mul(&shift.square())];
        for (index, value) in values.iter_mut().enumerate() {
            if index % 3 != 0 || extra.reduce() != PastaField::<M>::ONE.reduce() {
                *value = value.mul(&cycle[index % 3]);
            }
        }
    }

    // Also used by residue expansion: each residue has a different scaling base
    // but shares this plan's subgroup twiddles and bit-reversal permutation.
    pub(super) fn fill_prefix(
        self,
        coefficients: &[PastaField<M>],
        output: &mut [PastaField<M>],
        shift: super::factors::ForwardShift<M>,
        scales: Option<&[PastaField<M>]>,
        extra: PastaField<M>,
    ) -> usize {
        if coefficients.is_empty() {
            output.fill(PastaField::ZERO);
            return output.len() * 2;
        }
        let width = coefficients.len().next_power_of_two();
        let chunk_len = output.len() / width;
        // After bit reversal, each chunk starts with one coefficient and a
        // zero suffix. Its first log2(chunk_len) butterfly rounds only copy
        // that coefficient, so broadcasting skips those rounds. Visiting the
        // coefficients in degree order also permits a scaling progression.
        let mut scale = extra;
        let normalized = extra.reduce() != PastaField::<M>::ONE.reduce();
        let identity = shift.is_identity();
        let cycle = shift.cycle().map(|cycle| cycle.scaled(extra));
        for (index, value) in coefficients.iter().enumerate() {
            let value = if let Some(table) = scales {
                let scale = if normalized {
                    table[index].mul(&extra)
                } else {
                    table[index]
                };
                value.mul(&scale)
            } else if identity {
                if normalized {
                    value.mul(&extra)
                } else {
                    *value
                }
            } else if let Some(cycle) = cycle {
                if index % 3 == 0 && !normalized {
                    *value
                } else {
                    value.mul(&cycle.at(index))
                }
            } else {
                let value = value.mul(&scale);
                if index + 1 < coefficients.len() {
                    scale = scale.mul(&shift.shift());
                }
                value
            };
            let destination = self.reversed(index);
            output[destination..destination + chunk_len].fill(value);
        }
        for index in coefficients.len()..width {
            let destination = self.reversed(index);
            output[destination..destination + chunk_len].fill(PastaField::ZERO);
        }
        chunk_len * 2
    }

    pub(super) fn run<E: Executor>(
        self,
        values: &mut [PastaField<M>],
        options: Strategy,
        executor: &E,
        scratch: &mut [PastaField<M>],
        run: Run<'_, '_, M>,
    ) {
        let mut plan = self;
        if run.inverse && !run.normalized {
            plan.domain = self.domain.domain().subgroup();
        }
        let mut request = super::TransformRequest::new(if run.inverse {
            super::Direction::Inverse
        } else {
            super::Direction::Forward
        });
        if run.inverse && !run.normalized {
            request.inverse_scale = super::InverseScale::Unscaled;
        }
        plan.bounded(options, request, false)
            .expect("validated transform geometry")
            .resume(run.first, super::ElementOrder::BitReversed)
            .execute_with(
                None,
                values,
                run.factor,
                scratch,
                core::num::NonZeroUsize::new(options.max_tasks).unwrap(),
                executor,
            );
        for lift in run.lifts {
            for_each_chunk_mut(
                values,
                options.tile_len.min(values.len()),
                TaskBudget::new(options.max_tasks).unwrap(),
                executor,
                |chunk, output, _| {
                    let start = chunk * options.tile_len.min(self.domain.size());
                    for (value, coefficient) in output
                        .iter_mut()
                        .zip(lift.values.get(start..).unwrap_or(&[]))
                    {
                        *value = value.add(coefficient);
                    }
                },
            );
        }
    }
}

pub(super) struct Run<'a, 'b, M: PrimeModulus> {
    inverse: bool,
    normalized: bool,
    first: usize,
    lifts: &'a [super::Class<'b, M>],
    factor: Option<&'a [PastaField<M>]>,
}

impl<'a, 'b, M: PrimeModulus> Run<'a, 'b, M> {
    fn set_first(&mut self, first: usize) {
        self.first = first;
    }
    pub(super) fn forward(first: usize) -> Self {
        Self {
            inverse: false,
            normalized: false,
            first,
            lifts: &[],
            factor: None,
        }
    }
    pub(super) fn inverse(lifts: &'a [super::Class<'b, M>]) -> Self {
        Self {
            inverse: true,
            normalized: true,
            first: 2,
            lifts,
            factor: None,
        }
    }
    /// An inverse run that leaves domain-size and coset scaling to the caller.
    pub(super) const INVERSE_UNSCALED: Self = Self {
        inverse: true,
        normalized: false,
        first: 2,
        lifts: &[],
        factor: None,
    };
    #[cfg(test)]
    pub(super) fn forward_product(first: usize, factor: &'a [PastaField<M>]) -> Self {
        Self {
            factor: Some(factor),
            ..Self::forward(first)
        }
    }
}

struct Kernel<'a, 'b, 'c, M: PrimeModulus> {
    plan: Transform<'a, M>,
    run: Run<'b, 'c, M>,
    finish: InverseFinish<M>,
}

impl<M: PrimeModulus> Kernel<'_, '_, '_, M> {
    fn root(&self) -> PastaField<M> {
        if self.run.inverse {
            self.plan.domain.domain().inverse_root()
        } else {
            self.plan.domain.domain().root()
        }
    }

    // Canonical roots are nested: the root of order 2^k is the full
    // domain root raised to size / 2^k. The field already stores this ladder.
    fn stage_root(&self, log_size: u32) -> PastaField<M> {
        if self.run.inverse {
            PastaField::root_of_unity_inverse(log_size).unwrap()
        } else {
            PastaField::root_of_unity(log_size).unwrap()
        }
    }

    fn twiddles(&self) -> Option<&[PastaField<M>]> {
        if self.run.inverse {
            self.plan.tables.inverse
        } else {
            self.plan.tables.forward
        }
    }

    fn needs_finish_twiddles(&self) -> bool {
        self.run.normalized
            && self.plan.tables.inverse.is_none()
            && (!matches!(self.finish, InverseFinish::ScaledInputs(_))
                || self.plan.tables.inverse_finish.is_none())
    }

    #[inline(never)]
    fn local(&self, values: &mut [PastaField<M>]) {
        let whole_inverse = self.run.normalized && values.len() == self.plan.domain.size();
        let whole_forward = !self.run.inverse && values.len() == self.plan.domain.size();
        let last = if whole_inverse {
            values.len() / 2
        } else {
            values.len()
        };
        let local_len = values.len();
        let mut block = self.run.first;
        while block <= last {
            let stride = self.plan.domain.size() / block;
            let step = if self.twiddles().is_some() {
                PastaField::ONE
            } else {
                self.stage_root(block.trailing_zeros())
            };
            for chunk in values.chunks_exact_mut(block) {
                let (left, right) = chunk.split_at_mut(block / 2);
                // Separate prepared forward multiplies from the add/sub pass.
                // Keep terminal stores and inverse finishing in their original loop.
                if !self.run.inverse
                    && block < local_len
                    && let Some(table) = self.twiddles()
                {
                    for (index, value) in right.iter_mut().enumerate().skip(1) {
                        *value = scale_loose(*value, &table[index * stride]);
                    }
                    for (left, right) in left.iter_mut().zip(right) {
                        butterfly(left, right, None);
                    }
                    continue;
                }
                let mut power = PastaField::ONE;
                for (index, (left, right)) in left.iter_mut().zip(right).enumerate() {
                    if index == 0 {
                        butterfly(left, right, None);
                    } else {
                        if self.twiddles().is_none() {
                            power = power.mul(&step);
                        }
                        let twiddle = self.twiddles().map_or(power, |table| table[index * stride]);
                        butterfly(left, right, Some(&twiddle));
                    }
                    if whole_forward && block == self.plan.domain.size() {
                        *left = self.forward_store(*left, index);
                        *right = self.forward_store(*right, index + block / 2);
                    }
                }
            }
            block *= 2;
        }
        if whole_inverse {
            let (left, right) = values.split_at_mut(self.plan.domain.size() / 2);
            let mut twiddle = PastaField::ONE;
            let right_scale = self.right_scale();
            for (index, (left, right)) in left.iter_mut().zip(right).enumerate() {
                self.finish(left, right, index, twiddle, right_scale);
                if index + 1 < self.plan.domain.size() / 2 && self.needs_finish_twiddles() {
                    twiddle = twiddle.mul(&self.root());
                }
            }
        }
    }

    fn forward_store(&self, value: PastaField<M>, index: usize) -> PastaField<M> {
        self.run
            .factor
            .map_or_else(|| value, |factor| scale_loose(value, &factor[index]))
    }

    fn finish(
        &self,
        left: &mut PastaField<M>,
        right: &mut PastaField<M>,
        index: usize,
        twiddle: PastaField<M>,
        right_scale: PastaField<M>,
    ) {
        if let InverseFinish::ScaledInputs(factors) = self.finish {
            self.finish_scaled(left, right, index, factors.at(index), right_scale);
        } else {
            let twiddle = self
                .plan
                .tables
                .inverse
                .map_or(twiddle, |table| table[index]);
            butterfly(left, right, (index != 0).then_some(&twiddle));
            let log_size = self.plan.domain.domain().log_size();
            *left = divide_by_power_of_two(*left, log_size);
            *right = divide_by_power_of_two(*right, log_size);
            if let InverseFinish::Outputs(factors @ Factors::Periodic(_)) = self.finish {
                for (value, degree) in [
                    (&mut *left, index),
                    (&mut *right, index + self.plan.domain.size() / 2),
                ] {
                    if degree % 3 != 0 {
                        *value = value.mul(&factors.at(degree));
                    }
                }
            }
        }
        // Add coefficients only after inverse scaling and untwisting.
        // Equal-size lifts also contribute to the upper terminal store.
        for lift in self.run.lifts {
            if let Some(coefficient) = lift.values.get(index) {
                *left = left.add(coefficient);
            }
            if let Some(coefficient) = lift.values.get(index + self.plan.domain.size() / 2) {
                *right = right.add(coefficient);
            }
        }
    }

    fn finish_scaled(
        &self,
        left: &mut PastaField<M>,
        right: &mut PastaField<M>,
        index: usize,
        scale: PastaField<M>,
        right_scale: PastaField<M>,
    ) {
        // The finish table combines the normalized factor with the twiddle.
        // The upper output also needs the untwisting factor at degree n/2.
        let high_scale = self.plan.tables.inverse_finish.unwrap()[index];
        let low = scale_loose(*left, &scale);
        let high = scale_loose(*right, &high_scale);
        *left = low.add(&high);
        let difference = low.sub(&high);
        *right = if right_scale.reduce() == PastaField::<M>::ONE.reduce() {
            difference
        } else {
            difference.mul(&right_scale)
        };
    }

    fn right_scale(&self) -> PastaField<M> {
        if self.run.normalized && matches!(self.finish, InverseFinish::ScaledInputs(_)) {
            Factors::untwist(self.plan.domain).at(self.plan.domain.size() / 2)
        } else {
            PastaField::ONE
        }
    }

    fn cross(&self, values: &mut [PastaField<M>], first_column: usize, geometry: &Geometry) {
        let finish_twiddles = self.needs_finish_twiddles();
        let mut column_twiddle = if finish_twiddles {
            self.root().pow_u64(first_column as u64)
        } else {
            PastaField::ONE
        };
        let tile_twiddle = if finish_twiddles {
            self.stage_root(geometry.tiles.trailing_zeros())
        } else {
            PastaField::ONE
        };
        let right_scale = self.right_scale();
        // One seed per active stage and column block, then a recurrence
        // across columns. Pasta domains have at most 32 radix-2 stages.
        // Each tuple holds the column seed, column step, and tile step.
        let mut stages = [(PastaField::ONE, PastaField::ONE, PastaField::ONE); 32];
        if self.twiddles().is_none() {
            for (stage, state) in stages[..geometry.tiles.trailing_zeros() as usize]
                .iter_mut()
                .enumerate()
            {
                let block = (2 << stage) * geometry.tile_len;
                if block >= self.run.first
                    && !(self.run.normalized && block == self.plan.domain.size())
                {
                    let column_step = self.stage_root(block.trailing_zeros());
                    *state = (
                        column_step.pow_u64(first_column as u64),
                        column_step,
                        self.stage_root(stage as u32 + 1),
                    );
                }
            }
        }
        let columns = values.len() / geometry.tiles;
        for (offset, lane) in values.chunks_exact_mut(geometry.tiles).enumerate() {
            let column = first_column + offset;
            let mut distance = 1;
            while distance < geometry.tiles {
                let stride = geometry.tiles / (2 * distance);
                if 2 * distance * geometry.tile_len >= self.run.first {
                    if self.run.normalized && distance == geometry.tiles / 2 {
                        let (left, right) = lane.split_at_mut(distance);
                        let mut twiddle = column_twiddle;
                        for (tile, (left, right)) in left.iter_mut().zip(right).enumerate() {
                            self.finish(
                                left,
                                right,
                                tile * geometry.tile_len + column,
                                twiddle,
                                right_scale,
                            );
                            if tile + 1 < distance && finish_twiddles {
                                twiddle = twiddle.mul(&tile_twiddle);
                            }
                        }
                    } else {
                        let (first, column_step, step) = stages[distance.trailing_zeros() as usize];
                        for group in lane.chunks_exact_mut(distance * 2) {
                            let (left, right) = group.split_at_mut(distance);
                            let mut power = first;
                            for (tile, (left, right)) in left.iter_mut().zip(right).enumerate() {
                                let index = (tile * geometry.tile_len + column) * stride;
                                if index == 0 {
                                    butterfly(left, right, None);
                                } else {
                                    let twiddle =
                                        self.twiddles().map_or(power, |table| table[index]);
                                    butterfly(left, right, Some(&twiddle));
                                }
                                if !self.run.inverse && distance == geometry.tiles / 2 {
                                    let index = tile * geometry.tile_len + column;
                                    *left = self.forward_store(*left, index);
                                    *right = self
                                        .forward_store(*right, index + self.plan.domain.size() / 2);
                                }
                                if self.twiddles().is_none() && tile + 1 < distance {
                                    power = power.mul(&step);
                                }
                            }
                        }
                        if self.twiddles().is_none() && offset + 1 < columns {
                            stages[distance.trailing_zeros() as usize].0 = first.mul(&column_step);
                        }
                    }
                }
                distance *= 2;
            }
            if offset + 1 < columns && finish_twiddles {
                column_twiddle = column_twiddle.mul(&self.root());
            }
        }
    }
}
