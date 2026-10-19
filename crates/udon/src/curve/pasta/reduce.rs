//! Affine bucket reduction with one shared inversion per pair-tree level.

use core::marker::PhantomData;

use crate::field::invert_nonzero;

use super::{AffinePoint, PastaCurve, ProjectivePoint};
use crate::field::PastaField;

/// Sums one bounded batch, sharing inversions until the final small layer.
///
/// The caller supplies at least one field per input point. Cancelled pairs
/// disappear; no identity is ever stored as a nonidentity affine point.
pub(super) fn sum<C: PastaCurve>(
    points: &mut [AffinePoint<C>],
    fields: &mut [PastaField<C::Base>],
) -> ProjectivePoint<C> {
    let mut lens = [points.len()];
    // Small layers cannot amortize another inversion. Finish projectively
    // without imposing a normalization inversion on the returned sum.
    while lens[0] > 16 {
        let count = lens[0];
        reduce_fused::<C, true>(&mut points[..count], &[0], &mut lens, fields);
    }
    let mut sum = ProjectivePoint::IDENTITY;
    for point in &points[..lens[0]] {
        sum = sum.add_mixed(point);
    }
    sum
}

/// Reduces disjoint buckets to zero or one affine point, updating their lengths.
///
/// Bucket `i` occupies `points[starts[i]..starts[i] + lens[i]]`. The caller
/// reserves disjoint ranges, one start per length, `fields` sized as described
/// below, and one `loose_starts` entry per bucket. Survivors end up at their
/// bucket's start.
///
/// The first level stages chord denominators and numerators from the deposits in
/// `points`; every sum is written loose into the tail of `fields`, and each
/// level also writes the next level's chords from the sums it has just
/// formed, so later levels read every pair once. Survivors are reduced back
/// into `points` once. `fields` holds `points.len() / 2` denominators, as
/// many scaled numerators, and `2 * (points.len() / 2 + starts.len())` loose
/// coordinates; `loose_starts` has one entry per bucket. A zero chord
/// denominator falls back to one complete level on reduced points, as
/// [`reduce_level`] documents.
pub(crate) fn reduce<C: PastaCurve>(
    points: &mut [AffinePoint<C>],
    starts: &[usize],
    lens: &mut [usize],
    fields: &mut [PastaField<C::Base>],
    loose_starts: &mut [usize],
) {
    let cap = points.len() / 2;
    let mut in_points = true;
    let mut staged = 0;
    while lens.iter().any(|&n| n > 1) {
        let next = {
            let (denom, rest) = fields.split_at_mut(cap);
            let (numerators, loose) = rest.split_at_mut(cap);
            if in_points {
                let mut offset = 0;
                for (loose_start, &len) in loose_starts.iter_mut().zip(lens.iter()) {
                    *loose_start = offset;
                    offset += len.div_ceil(2);
                }
                assert!(2 * offset <= loose.len(), "loose reduction scratch");
                staged = stage::<C>(points, starts, lens, denom, numerators);
                level::<C, true>(
                    points,
                    loose,
                    starts,
                    loose_starts,
                    lens,
                    denom,
                    numerators,
                    staged,
                )
            } else {
                level::<C, false>(
                    points,
                    loose,
                    starts,
                    loose_starts,
                    lens,
                    denom,
                    numerators,
                    staged,
                )
            }
        };
        match next {
            Some(next) => {
                in_points = false;
                staged = next;
            }
            None => {
                if !in_points {
                    materialize(points, &fields[2 * cap..], starts, loose_starts, lens);
                }
                reduce_level::<C, false>(points, starts, lens, fields);
                in_points = true;
            }
        }
    }
    if !in_points {
        materialize(points, &fields[2 * cap..], starts, loose_starts, lens);
    }
}

/// Writes the chord denominators and numerators of every pair of deposits.
fn stage<C: PastaCurve>(
    points: &[AffinePoint<C>],
    starts: &[usize],
    lens: &[usize],
    denom: &mut [PastaField<C::Base>],
    numerators: &mut [PastaField<C::Base>],
) -> usize {
    let mut staged = 0;
    for (&start, &len) in starts.iter().zip(lens) {
        for pair in points[start..start + len].chunks_exact(2) {
            denom[staged] = pair[1].x.sub(&pair[0].x);
            numerators[staged] = pair[1].y.sub(&pair[0].y);
            staged += 1;
        }
    }
    staged
}

/// Reduces every bucket's live loose points into `points`.
fn materialize<C: PastaCurve>(
    points: &mut [AffinePoint<C>],
    loose: &[PastaField<C::Base>],
    starts: &[usize],
    loose_starts: &[usize],
    lens: &[usize],
) {
    for ((&start, &loose_start), &len) in starts.iter().zip(loose_starts).zip(lens) {
        let live = &loose[2 * loose_start..2 * (loose_start + len)];
        for (slot, pair) in points[start..start + len]
            .iter_mut()
            .zip(live.chunks_exact(2))
        {
            *slot = AffinePoint {
                x: pair[0].reduce(),
                y: pair[1].reduce(),
                marker: PhantomData,
            };
        }
    }
}

/// One incomplete level over `staged` pairs whose denominators are in
/// `denom`, reading reduced deposits from `points` when `FROM_POINTS` and
/// loose pairs otherwise. Sums are written loose, and the chords of the
/// next level's pairs replace the consumed scratch entries. Returns the
/// next level's pair count, or `None`, before changing `lens` or `loose`,
/// when the product of the denominators is zero.
#[inline(always)]
#[expect(
    clippy::too_many_arguments,
    reason = "One level takes both point layouts, the bucket tables, and its scratch lanes."
)]
fn level<C: PastaCurve, const FROM_POINTS: bool>(
    points: &[AffinePoint<C>],
    loose: &mut [PastaField<C::Base>],
    starts: &[usize],
    loose_starts: &[usize],
    lens: &mut [usize],
    denom: &mut [PastaField<C::Base>],
    numerators: &mut [PastaField<C::Base>],
    staged: usize,
) -> Option<usize> {
    let mut inverses = [PastaField::ONE; 2];
    if staged != 0 {
        let mut products = [PastaField::ONE; 2];
        products[(staged - 1) & 1] = denom[staged - 1];
        if staged > 1 {
            products[(staged - 2) & 1] = denom[staged - 2];
        }
        // Pre-scale each numerator by the later denominators in its lane.
        // Recovering the slope then needs one multiplication before squaring,
        // instead of recovering the denominator inverse first. This keeps the
        // multiplication count and scratch size unchanged.
        for i in (0..staged.saturating_sub(2)).rev() {
            numerators[i] = numerators[i].mul(&products[i & 1]);
            products[i & 1] = products[i & 1].mul(&denom[i]);
        }
        let product = if staged == 1 {
            products[0]
        } else {
            products[0].mul(&products[1])
        };
        let inverse = product.invert()?;
        inverses = if staged == 1 {
            [inverse, PastaField::ONE]
        } else {
            [inverse.mul(&products[1]), inverse.mul(&products[0])]
        };
    }
    let mut read = 0;
    let mut next = 0;
    for ((&start, &loose_start), len) in starts.iter().zip(loose_starts).zip(lens.iter_mut()) {
        let old = *len;
        // The first level's output region holds one point per pair plus an
        // odd survivor; later levels rewrite their input region in place.
        let span = if FROM_POINTS { old.div_ceil(2) } else { old };
        let out = &mut loose[2 * loose_start..2 * (loose_start + span)];
        let mut emitter = Emitter {
            written: 0,
            previous_x: PastaField::ZERO,
            previous_y: PastaField::ZERO,
        };
        let mut i = 0;
        // Finish two independent chords together so their multiplication and
        // squaring chains can overlap. Each pair of outputs also supplies the
        // next level's chord without separate emitter bookkeeping.
        while i + 3 < old {
            let (px, py, qx, rx, ry, sx) = if FROM_POINTS {
                let pair = &points[start + i..start + i + 4];
                (
                    pair[0].x.into_loose(),
                    pair[0].y.into_loose(),
                    pair[1].x.into_loose(),
                    pair[2].x.into_loose(),
                    pair[2].y.into_loose(),
                    pair[3].x.into_loose(),
                )
            } else {
                let pair = &out[2 * i..2 * i + 8];
                (pair[0], pair[1], pair[2], pair[4], pair[5], pair[6])
            };
            let first_sum = px.add(&qx);
            let second_sum = rx.add(&sx);
            let first = inverses[read & 1].mul(&numerators[read]);
            let second = inverses[(read + 1) & 1].mul(&numerators[read + 1]);
            if read < staged.saturating_sub(2) {
                inverses[read & 1] = inverses[read & 1].mul(&denom[read]);
            }
            if read + 1 < staged.saturating_sub(2) {
                inverses[(read + 1) & 1] = inverses[(read + 1) & 1].mul(&denom[read + 1]);
            }
            read += 2;
            let first_x = first.square().sub(&first_sum);
            let second_x = second.square().sub(&second_sum);
            let first_y = first.mul(&px.sub(&first_x)).sub(&py);
            let second_y = second.mul(&rx.sub(&second_x)).sub(&ry);
            let output = &mut out[2 * emitter.written..2 * emitter.written + 4];
            output.copy_from_slice(&[first_x, first_y, second_x, second_y]);
            denom[next] = second_x.sub(&first_x);
            numerators[next] = second_y.sub(&first_y);
            next += 1;
            emitter.written += 2;
            i += 4;
        }
        while i + 1 < old {
            let (px, py, qx) = if FROM_POINTS {
                let (p, q) = (points[start + i], points[start + i + 1]);
                (p.x.into_loose(), p.y.into_loose(), q.x.into_loose())
            } else {
                let pair = &out[2 * i..2 * i + 4];
                (pair[0], pair[1], pair[2])
            };
            let slope = inverses[read & 1].mul(&numerators[read]);
            if read < staged.saturating_sub(2) {
                inverses[read & 1] = inverses[read & 1].mul(&denom[read]);
            }
            read += 1;
            let (x, y) = AffinePoint::<C>::slope_coordinates(&px, &py, &qx, &slope);
            emitter.emit(out, denom, numerators, &mut next, x, y);
            i += 2;
        }
        if old & 1 != 0 {
            let (x, y) = if FROM_POINTS {
                let p = points[start + old - 1];
                (p.x.into_loose(), p.y.into_loose())
            } else {
                (out[2 * (old - 1)], out[2 * (old - 1) + 1])
            };
            emitter.emit(out, denom, numerators, &mut next, x, y);
        }
        *len = emitter.written;
    }
    debug_assert_eq!(read, staged);
    Some(next)
}

/// Writes one bucket's sums and survivors in order, and the next level's
/// chord denominator and numerator each time a pair completes.
struct Emitter<M: crate::field::PrimeModulus> {
    written: usize,
    previous_x: PastaField<M>,
    previous_y: PastaField<M>,
}

impl<M: crate::field::PrimeModulus> Emitter<M> {
    /// Sums land at or before the pair they replace, and the next level's
    /// pair index never passes the current one, so both slabs are updated in
    /// place.
    #[inline(always)]
    fn emit(
        &mut self,
        out: &mut [PastaField<M>],
        denom: &mut [PastaField<M>],
        numerators: &mut [PastaField<M>],
        next: &mut usize,
        x: PastaField<M>,
        y: PastaField<M>,
    ) {
        out[2 * self.written] = x;
        out[2 * self.written + 1] = y;
        if self.written & 1 != 0 {
            denom[*next] = x.sub(&self.previous_x);
            numerators[*next] = y.sub(&self.previous_y);
            *next += 1;
        }
        self.previous_x = x;
        self.previous_y = y;
        self.written += 1;
    }
}

#[inline(always)]
fn reduce_fused<C: PastaCurve, const INCOMPLETE: bool>(
    points: &mut [AffinePoint<C>],
    starts: &[usize],
    lens: &mut [usize],
    fields: &mut [PastaField<C::Base>],
) -> usize {
    let (denom, suffix) = fields.split_at_mut(points.len() / 2);
    let mut staged = 0;
    for (&start, &len) in starts.iter().zip(lens.iter()) {
        for pair in points[start..start + len].chunks_exact(2) {
            let (p, q) = (pair[0], pair[1]);
            if !INCOMPLETE && p.x == q.x && p.y != q.y {
                continue;
            }
            denom[staged] = if !INCOMPLETE && p.x == q.x {
                p.y.double()
            } else {
                q.x.sub(&p.x)
            };
            staged += 1;
        }
    }
    let mut inverses = [PastaField::ONE; 2];
    if staged != 0 {
        // Even and odd denominators form independent multiplication chains.
        // suffix[i] excludes denom[i] and contains later factors in that lane.
        // Seeding each lane with its last denominator avoids multiplying by one;
        // its endpoint needs no suffix entry during inverse recovery.
        let mut products = [PastaField::ONE; 2];
        products[(staged - 1) & 1] = denom[staged - 1];
        if staged > 1 {
            products[(staged - 2) & 1] = denom[staged - 2];
        }
        for i in (0..staged.saturating_sub(2)).rev() {
            suffix[i] = products[i & 1];
            products[i & 1] = products[i & 1].mul(&denom[i]);
        }
        let product = if staged == 1 {
            products[0]
        } else {
            products[0].mul(&products[1])
        };
        let Some(inverse) = product.invert() else {
            // Neither destinations nor lengths have been touched. Recompute
            // the denominators, handling doubles and cancelling pairs.
            return reduce_level::<C, false>(points, starts, lens, fields);
        };
        inverses = if staged == 1 {
            [inverse, PastaField::ONE]
        } else {
            [inverse.mul(&products[1]), inverse.mul(&products[0])]
        };
    }
    // Forward inverse recovery lets each pair be read before writing its sum.
    // Within a bucket, pair j reads positions 2j and 2j+1 before writing at most
    // position j. Odd survivors and later pairs therefore remain intact until
    // needed, even when cancellations reduce the number of outputs.
    let mut read = 0;
    for (&start, len) in starts.iter().zip(lens.iter_mut()) {
        let old = *len;
        let mut written = 0;
        for i in (0..old.saturating_sub(1)).step_by(2) {
            let (p, q) = (points[start + i], points[start + i + 1]);
            if !INCOMPLETE && p.x == q.x && p.y != q.y {
                continue;
            }
            let inverse = if read < staged.saturating_sub(2) {
                let result = inverses[read & 1].mul(&suffix[read]);
                inverses[read & 1] = inverses[read & 1].mul(&denom[read]);
                result
            } else {
                inverses[read & 1]
            };
            read += 1;
            let numerator = if !INCOMPLETE && p.x == q.x {
                p.tangent_numerator()
            } else {
                q.y.sub(&p.y)
            };
            let slope = numerator.mul(&inverse);
            points[start + written] = AffinePoint::from_slope(&p.x, &p.y, &q.x, &slope);
            written += 1;
        }
        if old & 1 != 0 {
            points[start + written] = points[start + old - 1];
            written += 1;
        }
        *len = written;
    }
    debug_assert_eq!(read, staged);
    staged
}

#[cfg(test)]
pub(crate) fn reduce_with<C: PastaCurve, const FUSED: bool>(
    points: &mut [AffinePoint<C>],
    starts: &[usize],
    lens: &mut [usize],
    fields: &mut [PastaField<C::Base>],
    mut level: impl FnMut(usize, usize),
) {
    while lens.iter().any(|&n| n > 1) {
        let terms = lens.iter().sum();
        let staged = reduce_level::<C, FUSED>(points, starts, lens, fields);
        level(staged, terms);
    }
}

/// Reduces one pair-tree level and returns the number of staged denominators.
///
/// Storage follows [`reduce`]. This complete path handles the exceptional pairs
/// detected by [`reduce_fused`]. `FUSED` selects a `mul_sub` expression for the
/// output's y-coordinate in timing controls; it does not fuse inverse recovery.
#[inline(always)]
pub(crate) fn reduce_level<C: PastaCurve, const FUSED: bool>(
    points: &mut [AffinePoint<C>],
    starts: &[usize],
    lens: &mut [usize],
    fields: &mut [PastaField<C::Base>],
) -> usize {
    let (denom, prefix) = fields.split_at_mut(points.len() / 2);
    let mut staged = 0;
    for (&start, &len) in starts.iter().zip(lens.iter()) {
        for pair in points[start..start + len].chunks_exact(2) {
            let (p, q) = (pair[0], pair[1]);
            if p.x == q.x && p.y != q.y {
                continue;
            }
            denom[staged] = if p.x == q.x {
                p.y.double()
            } else {
                q.x.sub(&p.x)
            };
            staged += 1;
        }
    }
    invert_nonzero(&mut denom[..staged], prefix);
    // Even when every pair cancels, this pass must compact odd survivors
    // and publish the new lengths. Pair j reads positions 2j and 2j+1 before
    // writing at most position j; it cannot overwrite a later unread pair.
    let mut read = 0;
    for (&start, len) in starts.iter().zip(lens.iter_mut()) {
        let old = *len;
        let mut written = 0;
        for i in (0..old.saturating_sub(1)).step_by(2) {
            let (p, q) = (points[start + i], points[start + i + 1]);
            if p.x == q.x && p.y != q.y {
                continue;
            }
            let numerator = if p.x == q.x {
                p.tangent_numerator()
            } else {
                q.y.sub(&p.y)
            };
            let slope = numerator.mul(&denom[read]);
            read += 1;
            points[start + written] = if FUSED {
                AffinePoint::from_slope_fused(&p.x, &p.y, &q.x, &slope)
            } else {
                AffinePoint::from_slope(&p.x, &p.y, &q.x, &slope)
            };
            written += 1;
        }
        if old & 1 != 0 {
            points[start + written] = points[start + old - 1];
            written += 1;
        }
        *len = written;
    }
    debug_assert_eq!(read, staged);
    staged
}

/// Retained native benchmark control with the original six-field staging layout.
#[cfg(test)]
pub(crate) fn reduce_original<C: PastaCurve>(
    points: &mut [AffinePoint<C>],
    starts: &[usize],
    lens: &mut [usize],
    fields: &mut [PastaField<C::Base>],
    writes: &mut [usize],
) {
    let capacity = points.len() / 2;
    let (x1, fields) = fields.split_at_mut(capacity);
    let (y1, fields) = fields.split_at_mut(capacity);
    let (x2, fields) = fields.split_at_mut(capacity);
    let (numerator, fields) = fields.split_at_mut(capacity);
    let (denom, prefix) = fields.split_at_mut(capacity);
    loop {
        // Read every pair's operands before completing additions in place.
        // Compacting odd survivors cannot overwrite an unread pair; cancelled
        // pairs disappear without needing an inverse or an identity encoding.
        let mut staged = 0;
        for (&start, len) in starts.iter().zip(lens.iter_mut()) {
            let old = *len;
            *len = 0;
            for i in (0..old.saturating_sub(1)).step_by(2) {
                let p = points[start + i];
                let q = points[start + i + 1];
                if p.x == q.x && p.y != q.y {
                    continue;
                }
                x1[staged] = p.x.into_loose();
                y1[staged] = p.y.into_loose();
                x2[staged] = q.x.into_loose();
                if p.x == q.x {
                    numerator[staged] = p.tangent_numerator();
                    denom[staged] = p.y.double();
                } else {
                    numerator[staged] = q.y.sub(&p.y);
                    denom[staged] = q.x.sub(&p.x);
                }
                writes[staged] = start + *len;
                *len += 1;
                staged += 1;
            }
            if old & 1 != 0 {
                points[start + *len] = points[start + old - 1];
                *len += 1;
            }
        }
        if staged == 0 {
            break;
        }
        invert_nonzero(&mut denom[..staged], prefix);
        for i in 0..staged {
            let slope = numerator[i].mul(&denom[i]);
            points[writes[i]] = AffinePoint::from_slope(&x1[i], &y1[i], &x2[i], &slope);
        }
        if lens.iter().all(|&n| n <= 1) {
            break;
        }
    }
}

/// Weights survivor `i` by `i + 1`, skipping points whose occupancy is zero.
pub(crate) fn collapse<C: PastaCurve>(
    points: &[AffinePoint<C>],
    occupied: &[usize],
) -> ProjectivePoint<C> {
    let Some(last) = occupied.iter().rposition(|&n| n != 0) else {
        return ProjectivePoint::IDENTITY;
    };
    let mut running = ProjectivePoint::IDENTITY;
    let mut sum = ProjectivePoint::IDENTITY;
    for (point, &len) in points[..=last].iter().zip(&occupied[..=last]).rev() {
        if len != 0 {
            running = running.add_mixed(point);
        }
        sum = sum.add(&running);
    }
    sum
}

/// Weights 128 affine survivors through four shared-inversion fronts.
///
/// Reuses dead deposit scratch: 448 affine points, 576 fields, and 96 entries
/// in each index lane. `occupied` is disposable after entry. Other sizes or
/// smaller workspaces retain the ordinary collapse. Logical bucket positions
/// are preserved even when intermediate additions cancel.
pub(crate) fn collapse_with_scratch<C: PastaCurve>(
    points: &[AffinePoint<C>],
    occupied: &mut [usize],
    scratch: &mut [AffinePoint<C>],
    fields: &mut [PastaField<C::Base>],
    starts: &mut [usize],
    loose_starts: &mut [usize],
) -> ProjectivePoint<C> {
    const BUCKETS: usize = 128;
    const GROUPS: usize = 96;
    if points.len() != BUCKETS
        || occupied.len() != BUCKETS
        || scratch.len() < 2 * BUCKETS + 2 * GROUPS
        || fields.len() < 6 * GROUPS
        || starts.len() < GROUPS
        || loose_starts.len() < GROUPS
    {
        return collapse(points, occupied);
    }
    if occupied.iter().all(|&len| len == 0) {
        return ProjectivePoint::IDENTITY;
    }

    // Snapshot occupancy before recycling its usize lane for pair lengths.
    // Byte flags add only 256 bounded stack bytes; no workspace growth.
    let mut flags_storage = [[0_u8; BUCKETS]; 2];
    let (first_flags, second_flags) = flags_storage.split_at_mut(1);
    let (mut flags, mut next_flags) = (&mut first_flags[0], &mut second_flags[0]);
    for (flag, &len) in flags.iter_mut().zip(occupied.iter()) {
        *flag = u8::from(len != 0);
    }
    let (mut front, rest) = scratch.split_at_mut(BUCKETS);
    let (mut next, pairs) = rest.split_at_mut(BUCKETS);
    let pairs = &mut pairs[..2 * GROUPS];
    front.copy_from_slice(points);
    for (group, start) in starts[..GROUPS].iter_mut().enumerate() {
        *start = 2 * group;
    }

    let mut main_len = BUCKETS;
    for depth in 0..4 {
        let mut groups = 0;
        {
            let mut stage = |a: usize, b: usize| {
                let mut len = 0;
                for source in [a, b] {
                    if flags[source] != 0 {
                        pairs[2 * groups + len] = front[source];
                        len += 1;
                    }
                }
                occupied[groups] = len;
                groups += 1;
            };
            for pair in 0..main_len / 2 {
                stage(2 * pair, 2 * pair + 1);
            }
            // Existing odd-sum trees each occupy main_len/2 logical slots.
            for odd in 0..depth {
                let start = main_len + odd * (main_len / 2);
                for pair in 0..main_len / 4 {
                    stage(start + 2 * pair, start + 2 * pair + 1);
                }
            }
            // New odd tree: one-based entries 1,3,5,... of the main list.
            for pair in 0..main_len / 4 {
                stage(4 * pair, 4 * pair + 2);
            }
        }
        debug_assert_eq!(groups, [96, 64, 40, 24][depth]);
        // Each disjoint group contains zero, one or two live nonidentity
        // points. The existing complete fallback handles doubles and inverses.
        reduce(
            &mut pairs[..2 * groups],
            &starts[..groups],
            &mut occupied[..groups],
            &mut fields[..6 * groups],
            &mut loose_starts[..groups],
        );
        for group in 0..groups {
            debug_assert!(occupied[group] <= 1);
            next_flags[group] = occupied[group] as u8;
            if occupied[group] != 0 {
                next[group] = pairs[2 * group];
            }
        }
        core::mem::swap(&mut front, &mut next);
        core::mem::swap(&mut flags, &mut next_flags);
        main_len /= 2;
    }

    // Q(P1,...,P2m) = 2 Q(P1+P2,...) - sum(P1,P3,...).
    // The remaining main list has eight points; four odd trees have four each.
    for i in 0..8 {
        occupied[i] = usize::from(flags[i]);
    }
    let mut result = collapse(&front[..8], &occupied[..8]);
    for odd in (0..4).rev() {
        let mut odd_sum = ProjectivePoint::IDENTITY;
        for i in 8 + odd * 4..12 + odd * 4 {
            if flags[i] != 0 {
                odd_sum = odd_sum.add_mixed(&front[i]);
            }
        }
        result = result.double().add(&odd_sum.neg());
    }
    result
}

#[cfg(test)]
#[path = "tests/reduce.rs"]
mod tests;
