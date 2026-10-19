//! Monomorphic base access and arithmetic for one complete chunk or window.

use super::storage::Storage;
use crate::curve::pasta::reduce::{collapse, collapse_with_scratch, reduce};
use crate::exec::execution::ReadView;

use super::{
    Accumulation, Bases, Input, ScalarStorage,
    recode::{self, Geometry},
};
use crate::{
    curve::{
        AffinePoint, CurveTableEntry, EisensteinTableBatch, PastaCurve, Point, PreparedAffinePoint,
        ProjectivePoint,
        pasta::{eisenstein, eisenstein_batch},
    },
    exec::SerialExecutor,
    field::PastaField,
};

pub(super) struct Work<'a, C: PastaCurve> {
    pub(super) affine: &'a mut [AffinePoint<C>],
    pub(super) projective: &'a mut [ProjectivePoint<C>],
    pub(super) field: &'a mut [PastaField<C::Base>],
    pub(super) indices: &'a mut [usize],
}
#[derive(Clone, Copy)]
pub(super) struct Task {
    pub(super) offset: usize,
    pub(super) window: usize,
    pub(super) pass: usize,
    pub(super) geometry: Geometry,
    pub(super) accumulation: Accumulation,
}
trait Base<C: PastaCurve>: Copy + Sync {
    fn point(self, rotation: usize) -> Option<AffinePoint<C>>;
}
impl<C: PastaCurve> Base<C> for AffinePoint<C> {
    fn point(self, rotation: usize) -> Option<AffinePoint<C>> {
        Some(self.rotated(rotation))
    }
}
impl<C: PastaCurve> Base<C> for PreparedAffinePoint<C> {
    fn point(self, rotation: usize) -> Option<AffinePoint<C>> {
        Some(self.rotated(rotation))
    }
}
impl<C: PastaCurve> Base<C> for Point<C> {
    fn point(self, rotation: usize) -> Option<AffinePoint<C>> {
        self.as_affine().map(|p| p.rotated(rotation))
    }
}
#[derive(Clone, Copy)]
pub(super) enum Indices<'a> {
    Slice(&'a [u32]),
    Strided {
        offset: usize,
        stride: usize,
    },
    Fragment {
        view: &'a dyn ReadView<u32>,
        offset: usize,
    },
}
impl Indices<'_> {
    #[inline]
    fn get(self, index: usize) -> usize {
        match self {
            Self::Slice(values) => values[index] as usize,
            Self::Strided { offset, stride } => offset + index * stride,
            Self::Fragment { view, offset } => {
                *view.get(index - offset).expect("validated index fragment") as usize
            }
        }
    }
}
pub(super) struct BaseView<'a, C: PastaCurve> {
    pub(super) bases: Bases<'a, C>,
    pub(super) indices: Option<Indices<'a>>,
}
struct View<'a, B, const INDEXED: bool> {
    bases: &'a [B],
    indices: Indices<'a>,
    offset: usize,
    stride: usize,
}
impl<B: Copy, const INDEXED: bool> View<'_, B, INDEXED> {
    #[inline]
    fn index(&self, term: usize) -> usize {
        let i = self.offset + term;
        if INDEXED { self.indices.get(i) } else { i }
    }
    #[inline]
    fn at(&self, term: usize) -> B {
        self.bases[self.index(term) * self.stride]
    }
}

pub(super) fn run<C: PastaCurve>(
    input: &Input<'_, C>,
    records: &[ScalarStorage<C>],
    digits: &[u8],
    task: Task,
    work: &mut Work<'_, C>,
) -> ProjectivePoint<C> {
    run_view(input, records, digits, task, work)
}

pub(super) fn run_view<C: PastaCurve>(
    input: &Input<'_, C>,
    records: impl Storage<ScalarStorage<C>>,
    digits: impl Storage<u8>,
    task: Task,
    work: &mut Work<'_, C>,
) -> ProjectivePoint<C> {
    run_selected(
        &BaseView {
            bases: input.bases,
            indices: input.indices.map(Indices::Slice),
        },
        records,
        digits,
        task,
        work,
    )
}

pub(super) fn run_selected<C: PastaCurve>(
    input: &BaseView<'_, C>,
    records: impl Storage<ScalarStorage<C>>,
    digits: impl Storage<u8>,
    task: Task,
    work: &mut Work<'_, C>,
) -> ProjectivePoint<C> {
    match input.bases {
        Bases::Affine(b) => access(input, b, records, digits, task, work, 1),
        Bases::Prepared(b) => access(input, b, records, digits, task, work, 1),
        Bases::Points(b) => access(input, b, records, digits, task, work, 1),
        Bases::Compact(b) => compact(input, b.as_slice(), records, digits, task, work),
        Bases::CompactPrepared(b) => compact(input, b.as_slice(), records, digits, task, work),
        Bases::Odd(b) => access(input, b.originals(), records, digits, task, work, 1),
        Bases::OddPrepared(b) => access(input, b.originals(), records, digits, task, work, 1),
        Bases::Alpha(b) => alpha(input, b, records, digits, task, work),
        Bases::AlphaPrepared(b) => alpha(input, b, records, digits, task, work),
    }
}

fn compact<C: PastaCurve, B: Base<C> + CurveTableEntry<C>>(
    input: &BaseView<'_, C>,
    bases: &[B],
    records: impl Storage<ScalarStorage<C>>,
    digits: impl Storage<u8>,
    task: Task,
    work: &mut Work<'_, C>,
) -> ProjectivePoint<C> {
    if task.geometry != Geometry::Joint {
        return access(input, bases, records, digits, task, work, 8);
    }
    let top = digits
        .chunks_exact(recode::JOINT_STRIDE)
        .map(|r| usize::from(r.get(eisenstein::MAX_DIGITS)))
        .max()
        .unwrap_or(0);
    let mut sum = ProjectivePoint::IDENTITY;
    for column in (0..top).rev() {
        sum = sum.double();
        for (i, row) in digits.chunks_exact(recode::JOINT_STRIDE).enumerate() {
            let code = row.get(column);
            if code != 0 {
                let j = input
                    .indices
                    .map_or(task.offset + i, |indices| indices.get(task.offset + i));
                sum = sum.add_mixed(&eisenstein::digit_point(&bases[8 * j..8 * j + 8], code));
            }
        }
    }
    sum
}

fn access<C: PastaCurve, B: Base<C>>(
    input: &BaseView<'_, C>,
    bases: &[B],
    records: impl Storage<ScalarStorage<C>>,
    digits: impl Storage<u8>,
    task: Task,
    work: &mut Work<'_, C>,
    stride: usize,
) -> ProjectivePoint<C> {
    match input.indices {
        Some(indices) => execute(
            View::<_, true> {
                bases,
                indices,
                offset: task.offset,
                stride,
            },
            records,
            digits,
            task,
            work,
        ),
        None => execute(
            View::<_, false> {
                bases,
                indices: Indices::Slice(&[]),
                offset: task.offset,
                stride,
            },
            records,
            digits,
            task,
            work,
        ),
    }
}
fn execute<C: PastaCurve, B: Base<C>, const INDEXED: bool>(
    view: View<'_, B, INDEXED>,
    records: impl Storage<ScalarStorage<C>>,
    digits: impl Storage<u8>,
    task: Task,
    work: &mut Work<'_, C>,
) -> ProjectivePoint<C> {
    #[cfg(test)]
    super::test_support::record_kernel(task.geometry);
    match task.geometry {
        Geometry::Alpha(_) => unreachable!("α geometry uses prepared layers"),
        Geometry::Short(bits) => short(view, records, bits, work),
        Geometry::Joint => joint(view, records, digits, task.pass, work),
        Geometry::Booth(_) if digits.is_empty() => {
            window::<C, B, INDEXED, true>(view, records, digits, task, work)
        }
        Geometry::Booth(_) => window::<C, B, INDEXED, false>(view, records, digits, task, work),
    }
}
fn short<C: PastaCurve, B: Base<C>, const INDEXED: bool>(
    view: View<'_, B, INDEXED>,
    records: impl Storage<ScalarStorage<C>>,
    bits: u8,
    work: &mut Work<'_, C>,
) -> ProjectivePoint<C> {
    let mut sum = ProjectivePoint::IDENTITY;
    // Zero, Boolean, and signed-unit rows execute at every input length without
    // GLV tables, inversions, or a full-width doubling ladder.
    if bits <= 1 || records.len() < 32 {
        for bit in (0..bits).rev() {
            sum = sum.double();
            for (i, record) in records.iter().enumerate() {
                if record.magnitude & (1 << bit) != 0
                    && let Some(p) = view.at(i).point(0)
                {
                    sum = sum.add_mixed(&if record.negative { p.neg() } else { p });
                }
            }
        }
    } else {
        let buckets = &mut work.projective[..16];
        for window in (0..usize::from(bits).div_ceil(4)).rev() {
            for _ in 0..4 {
                sum = sum.double();
            }
            buckets.fill(ProjectivePoint::IDENTITY);
            for (i, record) in records.iter().enumerate() {
                let digit = ((record.magnitude >> (4 * window)) & 15) as usize;
                if digit != 0
                    && let Some(p) = view.at(i).point(0)
                {
                    buckets[digit] =
                        buckets[digit].add_mixed(&if record.negative { p.neg() } else { p });
                }
            }
            let mut running = ProjectivePoint::IDENTITY;
            for bucket in buckets[1..].iter().rev() {
                running = running.add(bucket);
                sum = sum.add(&running);
            }
        }
    }
    sum
}
fn joint<C: PastaCurve, B: Base<C>, const INDEXED: bool>(
    view: View<'_, B, INDEXED>,
    records: impl Storage<ScalarStorage<C>>,
    digits: impl Storage<u8>,
    pass: usize,
    work: &mut Work<'_, C>,
) -> ProjectivePoint<C> {
    let mut sum = ProjectivePoint::IDENTITY;
    for first in (0..records.len()).step_by(pass) {
        let end = records.len().min(first + pass);
        let (tables, bases) = work.affine.split_at_mut(8 * (end - first));
        let mut active = 0;
        let mut top = 0;
        for i in first..end {
            let len = usize::from(digits.get(i * recode::JOINT_STRIDE + eisenstein::MAX_DIGITS));
            if len != 0
                && let Some(p) = view.at(i).point(0)
            {
                bases[active] = p;
                work.indices[active] = i;
                active += 1;
                top = top.max(len);
            }
        }
        if active == 0 {
            continue;
        }
        let r = EisensteinTableBatch::<C>::requirements(active).unwrap();
        eisenstein_batch::prepare_inner(
            &bases[..active],
            &mut tables[..8 * active],
            &mut work.projective[..r.projective_scratch],
            &mut work.field[..r.field_scratch],
            1,
            &SerialExecutor,
        );
        let mut partial = ProjectivePoint::IDENTITY;
        for column in (0..top).rev() {
            partial = partial.double();
            for (i, &term) in work.indices[..active].iter().enumerate() {
                let code = digits.get(term * recode::JOINT_STRIDE + column);
                if code != 0 {
                    partial = partial
                        .add_mixed(&eisenstein::digit_point(&tables[8 * i..8 * i + 8], code));
                }
            }
        }
        sum = sum.add(&partial);
    }
    sum
}
pub(super) fn collapse_projective<C: PastaCurve>(
    buckets: &[ProjectivePoint<C>],
) -> ProjectivePoint<C> {
    let mut running = ProjectivePoint::IDENTITY;
    let mut sum = ProjectivePoint::IDENTITY;
    for bucket in buckets.iter().rev() {
        running = running.add(bucket);
        sum = sum.add(&running);
    }
    sum
}
#[inline]
fn accumulate_projective<C: PastaCurve, B: Base<C>, const INDEXED: bool, const DIRECT: bool>(
    view: &View<'_, B, INDEXED>,
    records: impl Storage<ScalarStorage<C>>,
    digits: impl Storage<u8>,
    terms: core::ops::Range<usize>,
    task: Task,
    sums: &mut [ProjectivePoint<C>],
) {
    recode::window_views::<C, DIRECT>(
        records,
        digits,
        terms,
        task.geometry,
        task.window,
        &mut |term, a: i16, b: i16| {
            for (half, digit) in [a, b].into_iter().enumerate() {
                if digit != 0
                    && let Some(p) = view.at(term).point(half)
                {
                    let i = usize::from(digit.unsigned_abs()) - 1;
                    sums[i] = sums[i].add_mixed(&if digit < 0 { p.neg() } else { p });
                }
            }
        },
    );
}

fn window<C: PastaCurve, B: Base<C>, const INDEXED: bool, const DIRECT: bool>(
    view: View<'_, B, INDEXED>,
    records: impl Storage<ScalarStorage<C>>,
    digits: impl Storage<u8>,
    task: Task,
    work: &mut Work<'_, C>,
) -> ProjectivePoint<C> {
    let terms = records.len();
    let buckets = task.geometry.buckets();
    if task.accumulation == Accumulation::Projective {
        let sums = &mut work.projective[..buckets];
        sums.fill(ProjectivePoint::IDENTITY);
        accumulate_projective::<C, B, INDEXED, DIRECT>(
            &view,
            records,
            digits,
            0..terms,
            task,
            sums,
        );
        return collapse_projective(sums);
    }
    let pass = task.pass.min(terms);
    let (points, survivors) = work.affine.split_at_mut(2 * pass + buckets);
    let survivors = &mut survivors[..buckets];
    let (starts, indices) = work.indices.split_at_mut(buckets);
    let (lens, cursors) = indices.split_at_mut(buckets);
    let cursors = &mut cursors[..buckets];
    lens.fill(0);
    for first in (0..terms).step_by(pass) {
        let end = terms.min(first + pass);
        if task.accumulation == Accumulation::Hybrid && end == terms {
            let sums = &mut work.projective[..buckets];
            for i in 0..buckets {
                sums[i] = if lens[i] == 0 {
                    ProjectivePoint::IDENTITY
                } else {
                    survivors[i].to_projective()
                };
            }
            accumulate_projective::<C, B, INDEXED, DIRECT>(
                &view,
                records,
                digits,
                first..end,
                task,
                sums,
            );
            return collapse_projective(sums);
        }
        cursors.copy_from_slice(lens);
        recode::window_views::<C, DIRECT>(
            records,
            digits,
            first..end,
            task.geometry,
            task.window,
            &mut |term, a: i16, b: i16| {
                if view.at(term).point(0).is_some() {
                    for digit in [a, b] {
                        if digit != 0 {
                            cursors[usize::from(digit.unsigned_abs()) - 1] += 1;
                        }
                    }
                }
            },
        );
        let mut total = 0;
        for i in 0..buckets {
            starts[i] = total;
            total += cursors[i];
            if lens[i] != 0 {
                points[starts[i]] = survivors[i];
            }
            let cursor = starts[i] + lens[i];
            lens[i] = cursors[i];
            cursors[i] = cursor;
        }
        recode::window_views::<C, DIRECT>(
            records,
            digits,
            first..end,
            task.geometry,
            task.window,
            &mut |term, a: i16, b: i16| {
                for (half, digit) in [a, b].into_iter().enumerate() {
                    if digit != 0
                        && let Some(p) = view.at(term).point(half)
                    {
                        let i = usize::from(digit.unsigned_abs()) - 1;
                        points[cursors[i]] = if digit < 0 { p.neg() } else { p };
                        cursors[i] += 1;
                    }
                }
            },
        );
        reduce(&mut points[..total], starts, lens, work.field, cursors);
        for i in 0..buckets {
            if lens[i] != 0 {
                survivors[i] = points[starts[i]];
            }
        }
    }
    if task.geometry == Geometry::Booth(8) && task.accumulation == Accumulation::Affine {
        // Deposit buffers and bucket metadata are dead after the final pass.
        // Other geometries/accumulation paths retain their existing collapse.
        collapse_with_scratch(survivors, lens, points, work.field, starts, cursors)
    } else {
        collapse(survivors, lens)
    }
}

pub(super) fn stream<C: PastaCurve>(
    input: &Input<'_, C>,
    terms: usize,
    digits: &[u8],
    task: Task,
    sums: &mut [ProjectivePoint<C>],
) {
    stream_view(input, terms, digits, task, sums)
}

pub(super) fn stream_view<C: PastaCurve>(
    input: &Input<'_, C>,
    terms: usize,
    digits: impl Storage<u8>,
    task: Task,
    sums: &mut [ProjectivePoint<C>],
) {
    stream_selected(
        &BaseView {
            bases: input.bases,
            indices: input.indices.map(Indices::Slice),
        },
        terms,
        digits,
        task,
        sums,
    )
}

pub(super) fn stream_selected<C: PastaCurve>(
    input: &BaseView<'_, C>,
    terms: usize,
    digits: impl Storage<u8>,
    task: Task,
    sums: &mut [ProjectivePoint<C>],
) {
    fn deposit<C: PastaCurve, B: Base<C>, const INDEXED: bool>(
        view: View<'_, B, INDEXED>,
        terms: usize,
        digits: impl Storage<u8>,
        task: Task,
        sums: &mut [ProjectivePoint<C>],
    ) {
        #[cfg(test)]
        super::test_support::record_kernel(task.geometry);
        recode::rows_view(
            digits,
            terms,
            0..terms,
            task.geometry,
            task.window,
            |term, a, b| {
                for (half, digit) in [a, b].into_iter().enumerate() {
                    if digit != 0
                        && let Some(p) = view.at(term).point(half)
                    {
                        let i = usize::from(digit.unsigned_abs()) - 1;
                        sums[i] = sums[i].add_mixed(&if digit < 0 { p.neg() } else { p });
                    }
                }
            },
        );
    }
    macro_rules! access {
        ($bases:expr, $stride:expr) => {
            match input.indices {
                Some(indices) => deposit(
                    View::<_, true> {
                        bases: $bases,
                        indices,
                        offset: task.offset,
                        stride: $stride,
                    },
                    terms,
                    digits,
                    task,
                    sums,
                ),
                None => deposit(
                    View::<_, false> {
                        bases: $bases,
                        indices: Indices::Slice(&[]),
                        offset: task.offset,
                        stride: $stride,
                    },
                    terms,
                    digits,
                    task,
                    sums,
                ),
            }
        };
    }
    match input.bases {
        Bases::Affine(b) => access!(b, 1),
        Bases::Prepared(b) => access!(b, 1),
        Bases::Points(b) => access!(b, 1),
        Bases::Compact(b) => access!(b.as_slice(), 8),
        Bases::CompactPrepared(b) => access!(b.as_slice(), 8),
        Bases::Odd(b) => access!(b.originals(), 1),
        Bases::OddPrepared(b) => access!(b.originals(), 1),
        Bases::Alpha(b) => access!(b.originals(), 1),
        Bases::AlphaPrepared(b) => access!(b.originals(), 1),
    }
}

/// Visits short scalar digits across adjacent output lanes; full-width tiles
/// reuse the selected single-output kernel.
#[expect(
    clippy::too_many_arguments,
    reason = "A checked matrix supplies two strides and a bounded output tile."
)]
pub(super) fn shared<C: PastaCurve>(
    bases: Bases<'_, C>,
    output_offset: usize,
    output_stride: usize,
    term_stride: usize,
    records: &[ScalarStorage<C>],
    digits: &[u8],
    task: Task,
    work: &mut Work<'_, C>,
    output: &mut [ProjectivePoint<C>],
) {
    if output.len() == 1 {
        output[0] = run_selected(
            &BaseView {
                bases,
                indices: Some(Indices::Strided {
                    offset: output_offset,
                    stride: term_stride,
                }),
            },
            records,
            digits,
            task,
            work,
        );
        return;
    }
    #[expect(
        clippy::too_many_arguments,
        reason = "Monomorphic matrix access preserves the borrowed base layout."
    )]
    fn interleaved<C: PastaCurve, B: Base<C>>(
        bases: &[B],
        entry_stride: usize,
        output_offset: usize,
        output_stride: usize,
        term_stride: usize,
        records: &[ScalarStorage<C>],
        task: Task,
        work: &mut Work<'_, C>,
        output: &mut [ProjectivePoint<C>],
    ) {
        #[cfg(test)]
        super::test_support::record_kernel(task.geometry);
        let lanes = output.len();
        let point = |term: usize, lane: usize, rotation: usize| {
            bases[(output_offset + lane * output_stride + (task.offset + term) * term_stride)
                * entry_stride]
                .point(rotation)
        };
        output.fill(ProjectivePoint::IDENTITY);
        if let Geometry::Short(bits) = task.geometry {
            if bits <= 1 || records.len() < 32 {
                for bit in (0..bits).rev() {
                    for sum in output.iter_mut() {
                        *sum = sum.double();
                    }
                    for (term, record) in records.iter().enumerate() {
                        if record.magnitude & (1 << bit) != 0 {
                            for (lane, sum) in output.iter_mut().enumerate() {
                                if let Some(p) = point(term, lane, 0) {
                                    *sum =
                                        sum.add_mixed(&if record.negative { p.neg() } else { p });
                                }
                            }
                        }
                    }
                }
            } else {
                let buckets = &mut work.projective[..16 * lanes];
                for window in (0..usize::from(bits).div_ceil(4)).rev() {
                    for sum in output.iter_mut() {
                        for _ in 0..4 {
                            *sum = sum.double();
                        }
                    }
                    buckets.fill(ProjectivePoint::IDENTITY);
                    for (term, record) in records.iter().enumerate() {
                        let digit = ((record.magnitude >> (4 * window)) & 15) as usize;
                        if digit != 0 {
                            for lane in 0..lanes {
                                if let Some(p) = point(term, lane, 0) {
                                    let sum = &mut buckets[digit * lanes + lane];
                                    *sum =
                                        sum.add_mixed(&if record.negative { p.neg() } else { p });
                                }
                            }
                        }
                    }
                    for (lane, sum) in output.iter_mut().enumerate() {
                        let mut running = ProjectivePoint::IDENTITY;
                        for bucket in (1..16).rev() {
                            running = running.add(&buckets[bucket * lanes + lane]);
                            *sum = sum.add(&running);
                        }
                    }
                }
            }
        } else {
            unreachable!("multiple output lanes require short scalars");
        }
    }
    macro_rules! access {
        ($bases:expr, $stride:expr) => {
            interleaved(
                $bases,
                $stride,
                output_offset,
                output_stride,
                term_stride,
                records,
                task,
                work,
                output,
            )
        };
    }
    match bases {
        Bases::Affine(b) => access!(b, 1),
        Bases::Prepared(b) => access!(b, 1),
        Bases::Points(b) => access!(b, 1),
        Bases::Compact(b) => access!(b.as_slice(), 8),
        Bases::CompactPrepared(b) => access!(b.as_slice(), 8),
        Bases::Odd(b) => access!(b.originals(), 1),
        Bases::OddPrepared(b) => access!(b.originals(), 1),
        Bases::Alpha(b) => access!(b.originals(), 1),
        Bases::AlphaPrepared(b) => access!(b.originals(), 1),
    }
}

// Keep the residual kernel separate: its bucket bookkeeping otherwise bloats
// the main-window function and increases register spills in point staging.
#[inline(never)]
fn alpha_tail<C: PastaCurve, E: Base<C> + CurveTableEntry<C>>(
    input: &BaseView<'_, C>,
    table: super::AlphaTable<'_, C, E>,
    digits: impl Storage<u8>,
    terms: usize,
    task: Task,
    work: &mut Work<'_, C>,
) -> ProjectivePoint<C> {
    let description = table.codebook().description();
    let stride = task.geometry.stride();
    let index = |term| {
        input
            .indices
            .map_or(task.offset + term, |i| i.get(task.offset + term))
    };
    let code = |term| {
        let start = term * stride + task.window * 4;
        u32::from_le_bytes(match digits.slice(start..start + 4).contiguous() {
            Some(bytes) => bytes.try_into().expect("one alpha code"),
            None => core::array::from_fn(|i| digits.get(start + i)),
        })
    };
    // The last row contains two signed residuals, not residue codes. Keeping
    // it as a separate window lets the ordinary reduction apply B^windows.
    let mut sum = ProjectivePoint::IDENTITY;
    let mut top = 0;
    let mut max_odd = 0;
    for term in 0..terms {
        let c = code(term);
        for value in [c as u16 as i16, (c >> 16) as u16 as i16] {
            let m = value.unsigned_abs();
            if m != 0 {
                max_odd = max_odd.max(m >> m.trailing_zeros());
            }
        }
        top = top
            .max((c as u16 as i16).unsigned_abs())
            .max(((c >> 16) as u16 as i16).unsigned_abs());
    }
    let bits = 16 - top.leading_zeros();
    // Even-numbered alpha layers contain odd multiples of P. Factor each
    // component as 2^bit * odd, then reduce all bit positions together to
    // share their inversions. Larger odd parts use the binary fallback.
    if task.accumulation != Accumulation::Projective && usize::from(max_odd) < description.layers()
    {
        let points = &mut work.affine[..task.pass.min(terms) + description.layers()];
        let (starts, rest) = work.indices.split_at_mut(16);
        let (lens, cursors) = rest.split_at_mut(16);
        let cursors = &mut cursors[..16];
        let sums = &mut work.projective[..16];
        sums.fill(ProjectivePoint::IDENTITY);
        let mut first = 0;
        while first < terms {
            let mut end = first;
            let mut deposits = 0;
            lens.fill(0);
            // Each term can deposit both GLV components. Bound the pass by
            // occupied point slots as well as the caller's term limit.
            while end < terms && end - first < task.pass && points.len() - deposits >= 2 {
                let c = code(end);
                for value in [c as u16 as i16, (c >> 16) as u16 as i16] {
                    if value != 0 {
                        lens[value.unsigned_abs().trailing_zeros() as usize] += 1;
                        deposits += 1;
                    }
                }
                end += 1;
            }
            let mut total = 0;
            for bit in 0..16 {
                starts[bit] = total;
                total += lens[bit];
                cursors[bit] = starts[bit];
            }
            for term in first..end {
                let c = code(term);
                for (rotation, value) in [c as u16 as i16, (c >> 16) as u16 as i16]
                    .into_iter()
                    .enumerate()
                {
                    if value != 0 {
                        let magnitude = value.unsigned_abs();
                        let bit = magnitude.trailing_zeros() as usize;
                        let layer = usize::from(magnitude >> bit) - 1;
                        let p = table.entry(layer, index(term)).rotated(rotation);
                        points[cursors[bit]] = if value < 0 { p.neg() } else { p };
                        cursors[bit] += 1;
                    }
                }
            }
            reduce(&mut points[..total], starts, lens, work.field, cursors);
            for bit in 0..16 {
                if lens[bit] != 0 {
                    sums[bit] = sums[bit].add_mixed(&points[starts[bit]]);
                }
            }
            first = end;
        }
        for bit in (0..bits as usize).rev() {
            sum = sum.double().add(&sums[bit]);
        }
        return sum;
    }
    for bit in (0..bits).rev() {
        sum = sum.double();
        for term in 0..terms {
            let c = code(term);
            for (rotation, value) in [c as u16 as i16, (c >> 16) as u16 as i16]
                .into_iter()
                .enumerate()
            {
                if value.unsigned_abs() & (1 << bit) != 0 {
                    let p = table.entry(0, index(term)).rotated(rotation);
                    sum = sum.add_mixed(&if value < 0 { p.neg() } else { p });
                }
            }
        }
    }
    sum
}

fn alpha<C: PastaCurve, E: Base<C> + CurveTableEntry<C>>(
    input: &BaseView<'_, C>,
    table: super::AlphaTable<'_, C, E>,
    records: impl Storage<ScalarStorage<C>>,
    digits: impl Storage<u8>,
    task: Task,
    work: &mut Work<'_, C>,
) -> ProjectivePoint<C> {
    if !matches!(task.geometry, Geometry::Alpha(_)) {
        return access(input, table.originals(), records, digits, task, work, 1);
    }
    #[cfg(test)]
    super::test_support::record_kernel(task.geometry);
    let description = table.codebook().description();
    let terms = records.len();
    let stride = task.geometry.stride();
    let index = |term| {
        input
            .indices
            .map_or(task.offset + term, |i| i.get(task.offset + term))
    };
    let code = |term| {
        let start = term * stride + task.window * 4;
        u32::from_le_bytes(match digits.slice(start..start + 4).contiguous() {
            Some(bytes) => bytes.try_into().expect("one alpha code"),
            None => core::array::from_fn(|i| digits.get(start + i)),
        })
    };
    if task.window == description.main_windows() {
        return alpha_tail(input, table, digits, terms, task, work);
    }
    let count = description.layers();
    let point = |term, c: super::alpha::Code| {
        let p = table.entry(c.layer(), index(term)).rotated(c.rotation());
        if c.negative() { p.neg() } else { p }
    };
    let integrate_projective = |sums: &[ProjectivePoint<C>]| {
        let mut sum = ProjectivePoint::IDENTITY;
        for position in (0..8).rev() {
            sum = sum.double();
            for (bucket, coefficient) in table.codebook().coefficients().iter().enumerate() {
                let digit = coefficient.digits[position];
                if digit != 0 {
                    let unit = digit - 1;
                    let mut p = sums[bucket];
                    for _ in 0..unit / 2 {
                        p = p.endomorphism();
                    }
                    sum = sum.add(&if unit & 1 != 0 { p.neg() } else { p });
                }
            }
        }
        sum
    };
    if task.accumulation == Accumulation::Projective {
        let sums = &mut work.projective[..count];
        sums.fill(ProjectivePoint::IDENTITY);
        for term in 0..terms {
            let c = super::alpha::Code::from_bits(code(term));
            if c.present() {
                let bucket = c.bucket();
                sums[bucket] = sums[bucket].add_mixed(&point(term, c));
            }
        }
        return integrate_projective(sums);
    }
    let pass = task.pass.min(terms);
    let (points, survivors) = work.affine.split_at_mut(pass + count);
    let survivors = &mut survivors[..count];
    let (starts, rest) = work.indices.split_at_mut(count);
    let (lens, cursors) = rest.split_at_mut(count);
    let cursors = &mut cursors[..count];
    lens.fill(0);
    for first in (0..terms).step_by(pass) {
        let end = terms.min(first + pass);
        cursors.copy_from_slice(lens);
        for term in first..end {
            let c = super::alpha::Code::from_bits(code(term));
            if c.present() {
                cursors[c.bucket()] += 1;
            }
        }
        let mut total = 0;
        for bucket in 0..count {
            starts[bucket] = total;
            total += cursors[bucket];
            if lens[bucket] != 0 {
                points[starts[bucket]] = survivors[bucket];
            }
            let cursor = starts[bucket] + lens[bucket];
            lens[bucket] = cursors[bucket];
            cursors[bucket] = cursor;
        }
        // Give the scatter loop direct slice arguments and its own register
        // allocation, independent of the reducer and integration bookkeeping.
        #[inline(never)]
        fn scatter<C: PastaCurve, E: Base<C> + CurveTableEntry<C>>(
            input: &BaseView<'_, C>,
            table: super::AlphaTable<'_, C, E>,
            digits: impl Storage<u8>,
            task: Task,
            range: core::ops::Range<usize>,
            points: &mut [AffinePoint<C>],
            cursors: &mut [usize],
        ) {
            let stride = task.geometry.stride();
            for term in range {
                let start = term * stride + task.window * 4;
                let c = super::alpha::Code::from_bits(u32::from_le_bytes(
                    match digits.slice(start..start + 4).contiguous() {
                        Some(bytes) => bytes.try_into().expect("one alpha code"),
                        None => core::array::from_fn(|i| digits.get(start + i)),
                    },
                ));
                if c.present() {
                    let term = task.offset + term;
                    let base = input.indices.map_or(term, |indices| indices.get(term));
                    let p = table.entry(c.layer(), base).rotated(c.rotation());
                    let bucket = c.bucket();
                    points[cursors[bucket]] = if c.negative() { p.neg() } else { p };
                    cursors[bucket] += 1;
                }
            }
        }
        scatter(input, table, digits, task, first..end, points, cursors);
        reduce(&mut points[..total], starts, lens, work.field, cursors);
        for bucket in 0..count {
            if lens[bucket] != 0 {
                survivors[bucket] = points[starts[bucket]];
            }
        }
    }
    let additions = table
        .codebook()
        .coefficients()
        .iter()
        .map(|coefficient| {
            coefficient
                .digits
                .iter()
                .filter(|&&digit| digit != 0)
                .count()
        })
        .sum::<usize>();
    // Match the prepared reference's crossover: large coefficient programs
    // amortize a shared inversion tree across the eight binary positions.
    // Reuse existing scratch; small passes retain mixed projective additions.
    if additions >= 112 && points.len() >= additions && work.field.len() >= 2 * additions + 16 {
        let mut position_starts = [0; 8];
        let mut position_lens = [0; 8];
        let mut total = 0;
        for position in 0..8 {
            position_starts[position] = total;
            for (bucket, coefficient) in table.codebook().coefficients().iter().enumerate() {
                let digit = coefficient.digits[position];
                if lens[bucket] != 0 && digit != 0 {
                    let unit = digit - 1;
                    let p = survivors[bucket].rotated(usize::from(unit / 2));
                    points[total] = if unit & 1 != 0 { p.neg() } else { p };
                    total += 1;
                    position_lens[position] += 1;
                }
            }
        }
        reduce(
            &mut points[..total],
            &position_starts,
            &mut position_lens,
            work.field,
            &mut [0; 8],
        );
        let mut sum = ProjectivePoint::IDENTITY;
        for position in (0..8).rev() {
            sum = sum.double();
            if position_lens[position] != 0 {
                sum = sum.add_mixed(&points[position_starts[position]]);
            }
        }
        return sum;
    }
    let mut sum = ProjectivePoint::IDENTITY;
    for position in (0..8).rev() {
        sum = sum.double();
        for (bucket, coefficient) in table.codebook().coefficients().iter().enumerate() {
            let digit = coefficient.digits[position];
            if lens[bucket] != 0 && digit != 0 {
                let unit = digit - 1;
                let p = survivors[bucket].rotated(usize::from(unit / 2));
                sum = sum.add_mixed(&if unit & 1 != 0 { p.neg() } else { p });
            }
        }
    }
    sum
}
