//! Temporary Eisenstein tables and Jacobian ladders on isomorphic curves.

use super::CurveError;
use super::{
    PastaCurve, ProjectivePoint,
    eisenstein::{Digit, EisensteinScalar},
};
use crate::exec::{Executor, TaskBudget};
use crate::field::{CanonicalUint, PastaField};
use core::marker::PhantomData;

// 25 table fields (24 coordinates and their omitted denominator), two
// accumulator coordinates, and five shared-inversion ladder fields per base.
const BATCH_FIELDS: usize = 32;
const AFFINE_MIN: usize = 32;

/// Preferred field scratch for [`batch_mul_same_scalar`], in elements.
///
/// Also applies to [`batch_mul_same_scalar_prepared`]. The count depends only
/// on `points`, not the scalar or task budget. It may be zero. Smaller scratch
/// is accepted and can require additional passes or more projective work;
/// supplying this capacity does not guarantee a particular execution strategy.
/// Returns [`CurveError::SizeOverflow`] if the preferred field buffer exceeds
/// Rust's slice size limits.
pub const fn same_scalar_scratch<C: PastaCurve>(points: usize) -> Result<usize, CurveError> {
    super::checked_count::<PastaField<C::Base>>(
        points,
        if points < AFFINE_MIN { 0 } else { BATCH_FIELDS },
    )
}

/// Multiplies projective points in place by the same scalar, including identities.
///
/// Each output replaces the input at the same index. Empty batches are accepted;
/// a zero scalar sets every output to identity. Inputs must satisfy
/// [`ProjectivePoint`]'s mathematical invariants. Outputs represent the products
/// without promising a particular Jacobian scaling. Use
/// [`super::batch_normalize`] when affine outputs are required.
///
/// The operation allocates no storage of its own and does not normalize inputs.
/// Caller-owned `field` scratch can be sized with [`same_scalar_scratch`];
/// shorter or empty scratch is accepted. Initial scratch contents do not
/// matter, and scratch beyond the reported capacity is untouched. Execution
/// is variable-time with respect to both points and the scalar; use only where
/// their timing and memory access patterns need not be secret.
///
/// # Panics
///
/// An executor panic can leave some points multiplied and others unchanged,
/// and scratch partially written. [`Executor`] requires all scoped jobs to
/// finish or unwind before the panic propagates. Scratch can be reused without
/// clearing it; restore the original points before retrying the multiplication.
///
/// ```
/// use zakura_udon::{
///     curve::{batch_mul_same_scalar, same_scalar_scratch, Pallas, PallasProjective},
///     exec::{SerialExecutor, TaskBudget},
///     field::{Fp, Fq},
/// };
///
/// let base = PallasProjective::GENERATOR;
/// let mut points = [base, PallasProjective::IDENTITY];
/// let mut scratch = vec![Fp::ZERO; same_scalar_scratch::<Pallas>(points.len())?];
/// batch_mul_same_scalar(
///     &mut points, &Fq::from_u64(2), &mut scratch,
///     TaskBudget::SERIAL, &SerialExecutor,
/// );
/// assert_eq!(points, [base.double(), PallasProjective::IDENTITY]);
/// # Ok::<(), zakura_udon::curve::CurveError>(())
/// ```
pub fn batch_mul_same_scalar<C: PastaCurve, X: Executor>(
    points: &mut [ProjectivePoint<C>],
    scalar: &PastaField<C::Scalar>,
    field: &mut [PastaField<C::Base>],
    budget: TaskBudget,
    executor: &X,
) {
    batch_mul_same_scalar_prepared(
        points,
        &EisensteinScalar::new(scalar),
        field,
        budget,
        executor,
    );
}

/// Multiplies projective points in place using a prepared [`EisensteinScalar`].
///
/// Reuses scalar preparation across calls. Has the input, scratch, timing, and
/// panic contracts of [`batch_mul_same_scalar`]; borrows no inputs after return.
pub fn batch_mul_same_scalar_prepared<C: PastaCurve, X: Executor>(
    points: &mut [ProjectivePoint<C>],
    scalar: &EisensteinScalar<C>,
    field: &mut [PastaField<C::Base>],
    budget: TaskBudget,
    executor: &X,
) {
    if scalar.digits().is_empty() {
        points.fill(ProjectivePoint::IDENTITY);
        return;
    }
    let batch = points.len().min(field.len() / BATCH_FIELDS);
    if batch < AFFINE_MIN {
        complete_batch(points, scalar, budget.get(), executor);
    } else {
        for points in points.chunks_mut(batch) {
            effective_batch(
                points,
                scalar,
                &mut field[..points.len() * BATCH_FIELDS],
                budget.get(),
                executor,
            );
        }
    }
}

fn complete_batch<C: PastaCurve, X: Executor>(
    points: &mut [ProjectivePoint<C>],
    scalar: &EisensteinScalar<C>,
    tasks: usize,
    executor: &X,
) {
    let tasks = tasks.min(points.len().div_ceil(AFFINE_MIN).max(1));
    if tasks > 1 {
        let (left, right) = points.split_at_mut(points.len() / 2);
        executor.join(
            || complete_batch(left, scalar, tasks / 2, executor),
            || complete_batch(right, scalar, tasks - tasks / 2, executor),
        );
    } else {
        for point in points {
            *point = multiply_prepared(point, scalar);
        }
    }
}

fn effective_batch<C: PastaCurve, X: Executor>(
    points: &mut [ProjectivePoint<C>],
    scalar: &EisensteinScalar<C>,
    field: &mut [PastaField<C::Base>],
    tasks: usize,
    executor: &X,
) {
    let n = points.len();
    let tasks = tasks.min((n / AFFINE_MIN).max(1));
    if tasks > 1 {
        let left_tasks = tasks / 2;
        let mid = n / tasks * left_tasks;
        let (left, right) = points.split_at_mut(mid);
        let (a, b) = field.split_at_mut(mid * BATCH_FIELDS);
        executor.join(
            || effective_batch(left, scalar, a, left_tasks, executor),
            || effective_batch(right, scalar, b, tasks - left_tasks, executor),
        );
        return;
    }
    let (tables, rest) = field.split_at_mut(n * 25);
    for (point, table) in points.iter().zip(tables.chunks_exact_mut(25)) {
        // Identity lanes use a valid temporary curve for the shared inversion;
        // their zero restoration denominator reinstates identity at the end.
        let identity = point.is_identity();
        let base = if identity {
            &ProjectivePoint::GENERATOR
        } else {
            point
        };
        let denominator = EffectiveTable::prepare(base, &mut table[..24]).denominator;
        table[24] = if identity {
            PastaField::ZERO
        } else {
            denominator
        };
    }
    let table = |index: usize| {
        let fields = &tables[index * 25..(index + 1) * 25];
        EffectiveTable::<C> {
            coordinates: &fields[..16],
            endomorphism_x: &fields[16..24],
            denominator: fields[24],
        }
    };
    let (xs, rest) = rest.split_at_mut(n);
    let (ys, rest) = rest.split_at_mut(n);
    let (denom, rest) = rest.split_at_mut(n);
    let (prefix, rest) = rest.split_at_mut(n);
    let (hs, rest) = rest.split_at_mut(n);
    let (rs, h2s) = rest.split_at_mut(n);
    let (&top, digits) = scalar.digits().split_last().unwrap();
    for i in 0..n {
        let xy = table(i).digit(top);
        xs[i] = xy.x;
        ys[i] = xy.y;
    }
    // A lane's private coordinates lie on E_d: y² = x³ + 5*d⁶, where d is
    // its omitted denominator. They are not AffinePoint or POD entries.
    // The nonexceptional ladder argument at eisenstein_batch::multiply_inner
    // survives the isomorphism; each lane may have a different nonzero d.
    for &digit in digits.iter().rev() {
        if digit.is_zero() {
            for i in 0..n {
                denom[i] = ys[i].double();
            }
            crate::field::invert_nonzero(denom, prefix);
            for i in 0..n {
                let slope = xs[i].square().triple().mul(&denom[i]);
                let x = slope.square().sub(&xs[i].double());
                ys[i] = slope.mul(&xs[i].sub(&x)).sub(&ys[i]);
                xs[i] = x;
            }
        } else {
            for i in 0..n {
                let d = table(i).digit(digit);
                hs[i] = d.x.sub(&xs[i]);
                rs[i] = d.y.sub(&ys[i]);
                h2s[i] = hs[i].square();
                denom[i] = h2s[i].mul(&xs[i].double().add(&d.x)).sub(&rs[i].square());
                xs[i] = d.x;
            }
            crate::field::invert_nonzero(denom, prefix);
            for i in 0..n {
                let a = ys[i].mul(&denom[i]);
                let b = a.mul(&hs[i]);
                let c = b.mul(&h2s[i]);
                let lambda = c.sub(&rs[i]);
                xs[i] = xs[i].add(&b.mul(&lambda).double().double());
                ys[i] = ys[i].neg().sub(
                    &PastaField::<C::Base>::ONE
                        .add(&a.mul(&lambda).double().double())
                        .mul(&lambda.add(&c)),
                );
            }
        }
    }
    for (i, point) in points.iter_mut().enumerate() {
        *point = ProjectivePoint {
            x: xs[i],
            y: ys[i],
            z: table(i).denominator,
            marker: PhantomData,
        };
    }
}

/// Multiplies a nonidentity base by a canonical scalar without inversion.
///
/// Table entries and the ladder stay on y²=x³+5*d⁶. Restoring d in the final
/// Jacobian denominator yields an ordinary point. The private scratch types
/// cannot be confused with affine points or retained POD tables.
pub(super) fn multiply<C: PastaCurve>(
    base: &ProjectivePoint<C>,
    scalar: CanonicalUint,
) -> ProjectivePoint<C> {
    multiply_prepared(base, &EisensteinScalar::<C>::from_canonical(scalar))
}

fn multiply_prepared<C: PastaCurve>(
    base: &ProjectivePoint<C>,
    prepared: &EisensteinScalar<C>,
) -> ProjectivePoint<C> {
    if base.is_identity() {
        return ProjectivePoint::IDENTITY;
    }
    let Some((&top, digits)) = prepared.digits().split_last() else {
        return ProjectivePoint::IDENTITY;
    };
    let mut storage = [PastaField::ZERO; 24];
    let table = EffectiveTable::prepare(base, &mut storage);
    let mut result = Jacobian {
        xy: table.digit(top),
        z: PastaField::ONE,
    };
    for &code in digits.iter().rev() {
        result = result.double();
        if !code.is_zero() {
            result = result.add(table.digit(code));
        }
    }
    ProjectivePoint {
        x: result.xy.x,
        y: result.xy.y,
        z: result.z.mul(&table.denominator),
        marker: PhantomData,
    }
}

// Scratch on E_d; it never implements an ordinary point or POD interface.
#[derive(Clone, Copy)]
struct Jacobian<C: PastaCurve> {
    xy: Coordinates<C>,
    z: PastaField<C::Base>,
}

impl<C: PastaCurve> Jacobian<C> {
    fn double(self) -> Self {
        // The a=0 formulas do not use the curve's constant term. A zero z
        // remains zero, including for the private identity representation.
        let b = self.xy.y.square();
        let c = b.square();
        let d = self.xy.x.mul(&b);
        let e = self.xy.x.square().triple().half();
        let x = e.square().sub(&d.double());
        Self {
            xy: Coordinates {
                x,
                y: e.mul_sub(&d.sub(&x), &c),
            },
            z: self.z.mul(&self.xy.y),
        }
    }

    fn add(self, rhs: Coordinates<C>) -> Self {
        if self.z.is_zero() {
            return Self {
                xy: rhs,
                z: PastaField::ONE,
            };
        }
        let zz = self.z.square();
        let u = rhs.x.mul(&zz);
        let s = rhs.y.mul(&zz).mul(&self.z);
        let h = u.sub(&self.xy.x);
        let r = s.sub(&self.xy.y);
        if h.is_zero() {
            // Scalar schedules may encounter equal or inverse points. Keep
            // the ladder complete even though table construction is incomplete.
            return if r.is_zero() {
                self.double()
            } else {
                Self {
                    xy: rhs,
                    z: PastaField::ZERO,
                }
            };
        }
        let hh = h.square();
        let hhh = h.mul(&hh);
        let v = self.xy.x.mul(&hh);
        let x = r.square().sub(&hhh).sub(&v.double());
        Self {
            xy: Coordinates {
                x,
                y: r.mul_sub_product(&v.sub(&x), &self.xy.y, &hhh),
            },
            z: self.z.mul(&h),
        }
    }
}

// These coordinates satisfy y² = x³ + 5*d^6 for a separately retained d.
// They are deliberately neither AffinePoint nor CurveTableEntry: treating them
// as ordinary affine/POD values would lose the omitted denominator.
#[derive(Clone, Copy)]
struct Coordinates<C: PastaCurve> {
    x: PastaField<C::Base>,
    y: PastaField<C::Base>,
}

impl<C: PastaCurve> Coordinates<C> {
    fn transform(mut self, rotation: usize, negative: bool) -> Self {
        self.x = match rotation {
            0 => self.x,
            1 => self.x.mul(&PastaField::<C::Base>::ZETA),
            2 => self.x.mul(&PastaField::<C::Base>::ZETA_INVERSE),
            _ => unreachable!("three rotations"),
        };
        if negative {
            self.y = self.y.neg();
        }
        self
    }

    fn rescale(self, ratio: &PastaField<C::Base>) -> Self {
        let square = ratio.square();
        Self {
            x: self.x.mul(&square),
            y: self.y.mul(&square).mul(ratio),
        }
    }
}

struct EffectiveTable<'a, C: PastaCurve> {
    coordinates: &'a [PastaField<C::Base>],
    endomorphism_x: &'a [PastaField<C::Base>],
    denominator: PastaField<C::Base>,
}

impl<'a, C: PastaCurve> EffectiveTable<'a, C> {
    fn prepare(base: &ProjectivePoint<C>, storage: &'a mut [PastaField<C::Base>]) -> Self {
        debug_assert!(!base.is_identity());
        debug_assert_eq!(storage.len(), 24);
        let (storage, rotations) = storage.split_at_mut(16);
        // D=2P has denominator d=P.z*P.y. Its raw x/y lie on E_d, with
        // equation y²=x³+5*d^6. Map P onto E_d by scaling its raw x/y by
        // P.y²/P.y³. This uses no inverse, even for projectively scaled input.
        let yy = base.y.square();
        let yyyy = yy.square();
        let xyy = base.x.mul(&yy);
        let e = base.x.square().triple().half();
        let dx = e.square().sub(&xyy.double());
        let double = ProjectivePoint::<C> {
            x: dx,
            y: e.mul_sub(&xyy.sub(&dx), &yyyy),
            z: base.z.mul(&base.y),
            marker: PhantomData,
        };
        let operand = Coordinates::<C> {
            x: double.x,
            y: double.y,
        };
        let mut current = Coordinates::<C> { x: xyy, y: yyyy };
        let mut z = PastaField::ONE;
        storage[0] = current.x;
        storage[1] = current.y;
        // Each tuple transforms the previous representative, adds 2P, then
        // transforms the result into the next representative. Coefficients use
        // phi(a,b)=(-b,a-b), with REPRESENTATIVES' order for storage.
        const CHAIN: [(usize, usize, bool, usize, bool); 7] = [
            (4, 0, false, 0, false),
            (7, 1, true, 0, false),
            (2, 2, false, 1, false),
            (6, 1, true, 0, false),
            (5, 1, true, 2, true),
            (1, 0, true, 0, true),
            (3, 1, true, 0, false),
        ];
        let mut ratios = [PastaField::ONE; 7];
        for (step, &(index, before, negate_before, after, negate_after)) in CHAIN.iter().enumerate()
        {
            current = current.transform(before, negate_before);
            let zz = z.square();
            let h = operand.x.mul(&zz).sub(&current.x);
            let r = operand.y.mul(&zz).mul(&z).sub(&current.y);
            // No transformed representative equals +/-2P: the corresponding
            // nonzero Eisenstein differences have norm below the prime order.
            // Hence all h and z stay nonzero for every nonidentity base.
            debug_assert!(!h.is_zero());
            let hh = h.square();
            let hhh = hh.mul(&h);
            let v = current.x.mul(&hh);
            let x = r.square().sub(&hhh).sub(&v.double());
            let y = r.mul_sub_product(&v.sub(&x), &current.y, &hhh);
            current = Coordinates { x, y }.transform(after, negate_after);
            z = z.mul(&h);
            ratios[step] = h;
            storage[2 * index] = current.x;
            storage[2 * index + 1] = current.y;
        }
        // z_i divides z_final through the recorded ratios. Multiplying each
        // entry by the suffix ratio squared/cubed puts all entries on E_(d*z).
        // The reverse products recover these ratios without division.
        let mut suffix = PastaField::ONE;
        for step in (0..7).rev() {
            suffix = suffix.mul(&ratios[step]);
            let index = if step == 0 { 0 } else { CHAIN[step - 1].0 };
            let entry = Coordinates::<C> {
                x: storage[2 * index],
                y: storage[2 * index + 1],
            }
            .rescale(&suffix);
            storage[2 * index] = entry.x;
            storage[2 * index + 1] = entry.y;
        }
        for (rotation, xy) in rotations.iter_mut().zip(storage.chunks_exact(2)) {
            *rotation = xy[0].mul(&PastaField::<C::Base>::ZETA);
        }
        Self {
            coordinates: storage,
            endomorphism_x: rotations,
            denominator: double.z.mul(&z),
        }
    }

    fn digit(&self, code: Digit) -> Coordinates<C> {
        let index = usize::from(code.entry);
        let x = self.coordinates[2 * index];
        let rotated = self.endomorphism_x[index];
        let y = self.coordinates[2 * index + 1];
        Coordinates {
            x: match code.rotation {
                0 => x,
                1 => rotated,
                _ => x.add(&rotated).neg(),
            },
            y: if code.negative { y.neg() } else { y },
        }
    }
}

#[cfg(test)]
#[path = "tests/effective.rs"]
mod tests;
