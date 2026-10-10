//! Shared-inversion compact tables and same-scalar ladders.

use crate::field::invert_nonzero;
use core::marker::PhantomData;

use super::{
    AffinePoint, CurveError, CurveTableEntry, CurveTableRequirements, EisensteinScalar,
    EisensteinTable, PastaCurve, ProjectivePoint, assert_length, assert_scratch, checked_count,
    eisenstein,
};
use crate::{
    exec::{Executor, TaskBudget},
    field::PastaField,
};

const TABLE_AFFINE_MIN: usize = 8;
const LADDER_AFFINE_MIN: usize = 64;

// Either layout borrows entries without copying or rebuilding retained tables.
#[derive(Clone, Copy)]
enum Tables<'a, C: PastaCurve, E: CurveTableEntry<C>> {
    Flat(&'a [E]),
    Borrowed(&'a [&'a EisensteinTable<'a, C, E>]),
}
impl<'a, C: PastaCurve, E: CurveTableEntry<C>> Tables<'a, C, E> {
    fn len(self) -> usize {
        match self {
            Self::Flat(entries) => entries.len() / 8,
            Self::Borrowed(tables) => tables.len(),
        }
    }
    fn group(self, index: usize) -> &'a [E] {
        match self {
            Self::Flat(entries) => &entries[8 * index..8 * (index + 1)],
            Self::Borrowed(tables) => tables[index].as_slice(),
        }
    }
    fn range(self, range: core::ops::Range<usize>) -> Self {
        match self {
            Self::Flat(entries) => Self::Flat(&entries[range.start * 8..range.end * 8]),
            Self::Borrowed(tables) => Self::Borrowed(&tables[range]),
        }
    }
}

/// Borrowed compact tables, stored as consecutive groups of eight entries.
///
/// Each group has [`EisensteinTable`]'s order, with its base in entry zero.
/// Batch preparation and same-scalar multiplication can share inversions across
/// bases. Callers supply storage and scoped execution; the table operations
/// allocate no storage of their own. All [`CurveTableEntry`] representations
/// are supported, and empty batches are accepted. Timing and memory access
/// patterns can depend on the bases and scalar; these operations assume those
/// patterns need not be secret.
///
/// ```
/// use zakura_udon::{
///     curve::{
///         CurveTableRequirements, EisensteinScalar, EisensteinTableBatch,
///         Pallas, PallasAffine, PallasProjective,
///     },
///     exec::{SerialExecutor, TaskBudget},
///     field::{Fp, Fq},
/// };
///
/// const N: usize = 64;
/// const R: CurveTableRequirements = match EisensteinTableBatch::<Pallas>::requirements(N) {
///     Ok(r) => r,
///     Err(_) => panic!("batch is too large"),
/// };
/// const MUL: usize = match EisensteinTableBatch::<Pallas>::multiplication_scratch(N) {
///     Ok(n) => n,
///     Err(_) => panic!("batch is too large"),
/// };
/// const FIELD: usize = if MUL > R.field_scratch {
///     MUL
/// } else {
///     R.field_scratch
/// };
/// let bases = [PallasAffine::GENERATOR; N];
/// let mut entries = [PallasAffine::GENERATOR; R.table_entries];
/// let mut projective = [PallasProjective::IDENTITY; R.projective_scratch];
/// let mut field = [Fp::ZERO; FIELD];
/// let tables = EisensteinTableBatch::prepare(
///     &bases,
///     &mut entries,
///     &mut projective,
///     &mut field,
///     TaskBudget::SERIAL,
///     &SerialExecutor,
/// );
/// let scalar = EisensteinScalar::new(&Fq::from_u64(42));
/// let mut output = [PallasProjective::IDENTITY; N];
/// tables.mul_prepared(
///     &scalar,
///     &mut output,
///     &mut field,
///     TaskBudget::SERIAL,
///     &SerialExecutor,
/// );
/// for (i, product) in output.iter().enumerate() {
///     assert_eq!(*product, tables.get(i).unwrap().mul_prepared(&scalar));
/// }
/// # Ok::<(), zakura_udon::curve::CurveError>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct EisensteinTableBatch<'a, C: PastaCurve, E: CurveTableEntry<C> = AffinePoint<C>> {
    entries: &'a [E],
    marker: PhantomData<C>,
}

impl<'a, C: PastaCurve, E: CurveTableEntry<C>> EisensteinTableBatch<'a, C, E> {
    /// Returns exact entry and minimum scratch counts for batch preparation.
    ///
    /// Counts depend on the number of `bases`, independently of the task budget.
    /// Returns [`CurveError::SizeOverflow`] if a buffer exceeds slice limits.
    pub const fn requirements(bases: usize) -> Result<CurveTableRequirements, CurveError> {
        let table_entries = match checked_count::<E>(bases, 8) {
            Ok(n) => n,
            Err(e) => return Err(e),
        };
        let projective_scratch = if bases < TABLE_AFFINE_MIN {
            match checked_count::<ProjectivePoint<C>>(bases, 8) {
                Ok(n) => n,
                Err(e) => return Err(e),
            }
        } else {
            0
        };
        let field_scratch = match checked_count::<PastaField<C::Base>>(
            bases,
            if bases < TABLE_AFFINE_MIN { 8 } else { 4 },
        ) {
            Ok(n) => n,
            Err(e) => return Err(e),
        };
        Ok(CurveTableRequirements {
            table_entries,
            projective_scratch,
            field_scratch,
        })
    }

    /// Prepares one table per base in caller-selected entry storage.
    ///
    /// Size buffers with [`Self::requirements`] for `bases.len()`. `entries`
    /// must have the exact reported length; scratch may be larger, with unused
    /// tails left untouched. Initial contents do not matter. The returned view
    /// borrows only `entries`, leaving scratch available for other work.
    ///
    /// # Panics
    ///
    /// Incorrect buffer lengths panic before writes. An executor panic may leave
    /// buffers partially written. All scoped jobs finish or unwind before it
    /// propagates, as required by [`Executor`].
    pub fn prepare<B: CurveTableEntry<C>, X: Executor>(
        bases: &[B],
        entries: &'a mut [E],
        projective: &mut [ProjectivePoint<C>],
        field: &mut [PastaField<C::Base>],
        budget: TaskBudget,
        executor: &X,
    ) -> Self {
        assert_eq!(entries.len() / 8, bases.len(), "one table per base");
        assert!(
            entries.len().is_multiple_of(8),
            "incomplete Eisenstein table"
        );
        let r = Self::requirements(bases.len()).expect("entry storage bounds preparation scratch");
        assert_length("entries", r.table_entries, entries.len());
        assert_scratch("projective", r.projective_scratch, projective.len());
        assert_scratch("field", r.field_scratch, field.len());
        prepare_inner(
            bases,
            entries,
            &mut projective[..r.projective_scratch],
            &mut field[..r.field_scratch],
            budget.get(),
            executor,
        );
        Self {
            entries,
            marker: PhantomData,
        }
    }

    /// Borrows trusted tables in consecutive groups of eight entries.
    ///
    /// Each group must have been prepared in [`EisensteinTable`]'s order.
    /// Panics unless the storage contains complete groups. Binding performs no
    /// field or curve arithmetic and does not inspect entries.
    pub const fn bind(entries: &'a [E]) -> Self {
        assert!(
            entries.len().is_multiple_of(8),
            "incomplete Eisenstein table"
        );
        Self {
            entries,
            marker: PhantomData,
        }
    }

    /// Returns the number of bases.
    pub const fn len(&self) -> usize {
        self.entries.len() / 8
    }

    /// Returns whether there are no tables.
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Borrows the flat table storage.
    pub const fn as_slice(&self) -> &'a [E] {
        self.entries
    }

    /// Borrows an individual table, or returns `None` for an out-of-range index.
    ///
    /// The table inherits this batch's entry contract without revalidation.
    pub fn get(&self, index: usize) -> Option<EisensteinTable<'a, C, E>> {
        if index >= self.len() {
            return None;
        }
        let entries = &self.entries[index * 8..(index + 1) * 8];
        Some(EisensteinTable::bind(
            &entries[0].affine(),
            entries.try_into().expect("one complete table"),
        ))
    }

    /// Returns the field capacity for a single batch multiplication pass.
    ///
    /// Pass the number of tables as `bases`. Counts are independent of the scalar
    /// and task budget and apply to all multiplication methods, including
    /// [`Self::mul_borrowed_prepared`].
    /// This is a preferred capacity, not a minimum: smaller or empty scratch is
    /// accepted, as described by [`Self::mul_prepared`].
    /// Returns [`CurveError::SizeOverflow`] if the buffer exceeds slice limits.
    pub const fn multiplication_scratch(bases: usize) -> Result<usize, CurveError> {
        checked_count::<PastaField<C::Base>>(bases, if bases < LADDER_AFFINE_MIN { 0 } else { 5 })
    }

    /// Multiplies every base by the same scalar, in table order.
    ///
    /// Has the mathematical result and buffer and panic contracts of
    /// [`Self::mul_prepared`]. Retain an [`EisensteinScalar`] to reuse scalar
    /// preparation across calls.
    pub fn mul<X: Executor>(
        &self,
        scalar: &PastaField<C::Scalar>,
        output: &mut [ProjectivePoint<C>],
        field: &mut [PastaField<C::Base>],
        budget: TaskBudget,
        executor: &X,
    ) {
        self.mul_prepared(
            &EisensteinScalar::new(scalar),
            output,
            field,
            budget,
            executor,
        )
    }

    /// Multiplies bases in table order using reusable scalar digits.
    ///
    /// Size field scratch with [`Self::multiplication_scratch`] for `self.len()`.
    /// Initial buffer contents do not matter; scratch beyond the reported count
    /// is untouched. A zero scalar writes identities. Entries must satisfy the
    /// mathematical contract of [`EisensteinTable::mul`].
    /// Smaller scratch uses bounded batches or complete projective arithmetic.
    ///
    /// # Panics
    ///
    /// Panics before writes unless `output.len() == self.len()`.
    ///
    /// An executor panic may leave output and scratch partially written. All
    /// scoped jobs finish or unwind before it propagates, as required by
    /// [`Executor`]. The buffers can then be reused without clearing them.
    pub fn mul_prepared<X: Executor>(
        &self,
        scalar: &EisensteinScalar<C>,
        output: &mut [ProjectivePoint<C>],
        field: &mut [PastaField<C::Base>],
        budget: TaskBudget,
        executor: &X,
    ) {
        multiply_batch(
            Tables::Flat(self.entries),
            scalar,
            output,
            field,
            budget,
            executor,
        );
    }

    /// Multiplies independently retained, borrowed tables by one scalar.
    ///
    /// Prepares the scalar once per call. See [`Self::mul_borrowed_prepared`]
    /// for the input, scratch, timing, and panic contracts and for reuse of a
    /// prepared scalar across calls.
    pub fn mul_borrowed<X: Executor>(
        tables: &[&EisensteinTable<'_, C, E>],
        scalar: &PastaField<C::Scalar>,
        output: &mut [ProjectivePoint<C>],
        field: &mut [PastaField<C::Base>],
        budget: TaskBudget,
        executor: &X,
    ) {
        Self::mul_borrowed_prepared(
            tables,
            &EisensteinScalar::new(scalar),
            output,
            field,
            budget,
            executor,
        );
    }

    /// Multiplies independently retained tables with a reusable scalar schedule.
    ///
    /// Writes one product per table in slice order. Repeated references and an
    /// empty slice are accepted; a zero scalar writes identities. Tables may
    /// borrow disjoint storage. Their entries are neither copied nor rebuilt,
    /// and must satisfy [`EisensteinTable::mul`]'s mathematical contract, which
    /// is assumed without revalidation.
    ///
    /// Size `field` with [`Self::multiplication_scratch`] for `tables.len()`.
    /// Smaller or empty scratch is accepted; initial contents do not matter,
    /// and scratch beyond the reported capacity is untouched. This method
    /// allocates no storage of its own and retains no borrows after return.
    /// Timing and memory access patterns can depend on the tables and scalar.
    ///
    /// # Panics
    ///
    /// Panics before any output or scratch writes unless
    /// `output.len() == tables.len()`. An executor panic can leave output and
    /// scratch partially written. All jobs finish or unwind before propagation,
    /// as required by [`Executor`]; the buffers can then be reused without
    /// clearing them.
    ///
    /// ```
    /// use zakura_udon::{
    ///     curve::{EisensteinScalar, EisensteinTable, EisensteinTableBatch,
    ///             PallasAffine, PallasProjective, RotatedAffinePoint},
    ///     exec::{SerialExecutor, TaskBudget},
    ///     field::{Fp, Fq},
    /// };
    ///
    /// let base = PallasAffine::GENERATOR;
    /// let mut first = [RotatedAffinePoint::from_affine(&base); 8];
    /// let mut second = first;
    /// let mut projective = [PallasProjective::IDENTITY; 8];
    /// let mut field = [Fp::ZERO; 8];
    /// let a = EisensteinTable::prepare(&base, &mut first, &mut projective, &mut field);
    /// let b = EisensteinTable::prepare(&base.neg(), &mut second, &mut projective, &mut field);
    /// let scalar = EisensteinScalar::new(&Fq::from_u64(7));
    /// let mut output = [PallasProjective::IDENTITY; 3];
    /// EisensteinTableBatch::mul_borrowed_prepared(
    ///     &[&b, &a, &b], &scalar, &mut output, &mut [],
    ///     TaskBudget::SERIAL, &SerialExecutor,
    /// );
    /// let product = a.mul_prepared(&scalar);
    /// assert_eq!(output, [product.neg(), product, product.neg()]);
    /// ```
    pub fn mul_borrowed_prepared<X: Executor>(
        tables: &[&EisensteinTable<'_, C, E>],
        scalar: &EisensteinScalar<C>,
        output: &mut [ProjectivePoint<C>],
        field: &mut [PastaField<C::Base>],
        budget: TaskBudget,
        executor: &X,
    ) {
        multiply_batch(
            Tables::Borrowed(tables),
            scalar,
            output,
            field,
            budget,
            executor,
        );
    }
}

fn multiply_batch<C: PastaCurve, E: CurveTableEntry<C>, X: Executor>(
    tables: Tables<'_, C, E>,
    scalar: &EisensteinScalar<C>,
    output: &mut [ProjectivePoint<C>],
    field: &mut [PastaField<C::Base>],
    budget: TaskBudget,
    executor: &X,
) {
    let n = tables.len();
    assert_length("output", n, output.len());
    let digits = scalar.digits();
    let batch = n.min(field.len() / 5);
    if batch >= LADDER_AFFINE_MIN && !digits.is_empty() {
        for (index, output) in output.chunks_mut(batch).enumerate() {
            let start = index * batch;
            multiply_inner(
                tables.range(start..start + output.len()),
                digits,
                output,
                &mut field[..output.len() * 5],
                true,
                budget.get(),
                executor,
            );
        }
    } else {
        multiply_inner(
            tables,
            digits,
            output,
            &mut [],
            false,
            budget.get(),
            executor,
        );
    }
}

pub(crate) fn prepare_inner<
    C: PastaCurve,
    B: CurveTableEntry<C>,
    E: CurveTableEntry<C>,
    X: Executor,
>(
    bases: &[B],
    entries: &mut [E],
    projective: &mut [ProjectivePoint<C>],
    field: &mut [PastaField<C::Base>],
    tasks: usize,
    executor: &X,
) {
    let n = bases.len();
    let tasks = tasks.min((n / TABLE_AFFINE_MIN).max(1));
    if tasks > 1 {
        let left_tasks = tasks / 2;
        let mid = n / tasks * left_tasks;
        let (a, b) = entries.split_at_mut(mid * 8);
        let (fa, fb) = field.split_at_mut(mid * 4);
        executor.join(
            || prepare_inner(&bases[..mid], a, &mut [], fa, left_tasks, executor),
            || prepare_inner(&bases[mid..], b, &mut [], fb, tasks - left_tasks, executor),
        );
    } else if n < TABLE_AFFINE_MIN {
        for (base, points) in bases.iter().zip(projective.chunks_exact_mut(8)) {
            points.copy_from_slice(&eisenstein::representatives_affine(&base.affine()));
        }
        eisenstein::normalize(projective, field, entries);
    } else {
        prepare_affine(bases, entries, field);
    }
}

// Every chord below has distinct x coordinates: equality would make one of
// the small nonzero Eisenstein coefficient differences or sums vanish. Their
// norms are far below either prime group order. No exceptional-point branches
// or projective intermediates are needed for these nonidentity inputs.
fn prepare_affine<C: PastaCurve, B: CurveTableEntry<C>, E: CurveTableEntry<C>>(
    bases: &[B],
    entries: &mut [E],
    field: &mut [PastaField<C::Base>],
) {
    let n = bases.len();
    let (denom, prefix) = field.split_at_mut(2 * n);
    for (i, base) in bases.iter().enumerate() {
        let p = base.affine();
        entries[8 * i] = E::from_affine(&p);
        denom[i] = base.rotated(1).x.sub(&p.x);
    }
    invert_nonzero(&mut denom[..n], prefix);
    for (i, group) in entries.chunks_exact_mut(8).enumerate() {
        let p = group[0].affine();
        let d = p.chord_with_inverse(&group[0].rotated(1).neg(), &denom[i]);
        group[1] = E::from_affine(&d);
        denom[i] = group[1].rotated(1).x.sub(&d.x);
    }
    invert_nonzero(&mut denom[..n], prefix);
    for (i, group) in entries.chunks_exact_mut(8).enumerate() {
        let d = group[1].affine();
        let b = d.chord_with_inverse(&group[1].rotated(1).neg(), &denom[i]);
        let minus_three = b.rotated(2);
        group[4] = E::from_affine(&minus_three.neg());
    }
    for (i, group) in entries.chunks_exact(8).enumerate() {
        let minus_three = group[4].affine().neg();
        let phi = group[0].rotated(1);
        denom[2 * i] = minus_three.x.sub(&phi.x);
        denom[2 * i + 1] = group[4].rotated(2).neg().x.sub(&phi.x);
    }
    // Each +/- pair shares a chord denominator, so four additions per base
    // need just two inverse entries and one inversion phase.
    invert_nonzero(denom, prefix);
    for (i, group) in entries.chunks_exact_mut(8).enumerate() {
        let phi = group[0].rotated(1);
        let minus_three = group[4].affine().neg();
        let b_phi = group[4].rotated(2).neg();
        group[5] = E::from_affine(&phi.chord_with_inverse(&minus_three, &denom[2 * i]).neg());
        group[3] = E::from_affine(
            &phi.chord_with_inverse(&minus_three.neg(), &denom[2 * i])
                .endomorphism()
                .neg(),
        );
        group[2] = E::from_affine(
            &phi.chord_with_inverse(&b_phi.neg(), &denom[2 * i + 1])
                .endomorphism(),
        );
        let four_b = phi.chord_with_inverse(&b_phi, &denom[2 * i + 1]);
        group[6] = E::from_affine(&four_b.rotated(2));
    }
    for (i, group) in entries.chunks_exact(8).enumerate() {
        denom[i] = group[6].rotated(1).x.sub(&group[0].rotated(1).x);
    }
    invert_nonzero(&mut denom[..n], prefix);
    for (i, group) in entries.chunks_exact_mut(8).enumerate() {
        let p = group[0]
            .rotated(1)
            .chord_with_inverse(&group[6].rotated(1), &denom[i]);
        group[7] = E::from_affine(&p.rotated(2));
    }
}

fn multiply_inner<C: PastaCurve, E: CurveTableEntry<C>, X: Executor>(
    entries: Tables<'_, C, E>,
    digits: &[eisenstein::Digit],
    output: &mut [ProjectivePoint<C>],
    field: &mut [PastaField<C::Base>],
    affine: bool,
    tasks: usize,
    executor: &X,
) {
    let n = output.len();
    let tasks = tasks.min((n / LADDER_AFFINE_MIN).max(1));
    if tasks > 1 {
        let left_tasks = tasks / 2;
        let mid = n / tasks * left_tasks;
        let (a, b) = output.split_at_mut(mid);
        let (fa, fb) = field.split_at_mut(if affine { mid * 5 } else { 0 });
        executor.join(
            || {
                multiply_inner(
                    entries.range(0..mid),
                    digits,
                    a,
                    fa,
                    affine,
                    left_tasks,
                    executor,
                )
            },
            || {
                multiply_inner(
                    entries.range(mid..n),
                    digits,
                    b,
                    fb,
                    affine,
                    tasks - left_tasks,
                    executor,
                )
            },
        );
    } else if affine {
        affine_ladder(entries, digits, output, field);
    } else {
        for (index, result) in output.iter_mut().enumerate() {
            let group = entries.group(index);
            *result = eisenstein::multiply(group, digits);
        }
    }
}

// Nonempty digits from EisensteinScalar admit this affine ladder for every
// nonidentity base B; no per-scalar exceptional-case check is needed.
//
// Let q > 2^254 be the prime group order and lambda² + lambda + 1 = 0 mod q.
// An integer pair (a,b) represents a + b*lambda, and its norm
// N(a,b) = a² - ab + b² equals (a+b*lambda)(a+b*lambda²) mod q. If the pair
// represents zero, q divides its norm. Thus a nonzero pair of norm < q
// cannot vanish modulo q, and its multiple of B cannot be identity.
//
// GLV starts with r_0 whose coordinates have magnitude < 2^127. Recoding
// selects digits d_j with coordinates of magnitude <= 5 and leaves residuals
// r_(j+1) = (r_j - d_j)/2. After the first step, each coordinate has magnitude
// <= 2^126 + 2; later steps preserve the looser bound < 2^126 + 5. Recoding
// stops at the first zero pair, so every recorded proper residual is nonzero.
// Its norm is < 3*(2^126 + 5)² < q. The initial r_0 represents the original
// scalar, which is nonzero: GLV maps zero to (0,0) and hence empty digits.
//
// The high-to-low ladder reconstructs these residuals. Before processing d_j
// below the top digit, P = [r_(j+1)]B and D = [d_j]B. All accumulator states
// are nonidentity. Odd prime order rules out y(P)=0, so doubling is defined.
// For a nonzero digit, the fused 2P+D step has two possible exceptions:
//
// * D=P: the selector matches r_j modulo 8, making r_(j+1) divisible by 4
//   coordinatewise, whereas d_j has an odd coordinate. Their difference is
//   nonzero with coordinates of magnitude < 2^126 + 10. Its norm is below
//   3*(2^126 + 10)² < 2^254 < q, so equality modulo q is impossible.
// * D=-2P: 2r_(j+1)+d_j = r_j. A proper residual cannot vanish modulo q by
//   the norm bound; at j=0 it is the original nonzero scalar.
//
// These arguments require the GLV bounds, selector congruences, and canonical
// treatment of zero. Arbitrary injected digit strings need not satisfy them.
fn affine_ladder<C: PastaCurve, E: CurveTableEntry<C>>(
    entries: Tables<'_, C, E>,
    digits: &[eisenstein::Digit],
    output: &mut [ProjectivePoint<C>],
    field: &mut [PastaField<C::Base>],
) {
    let n = output.len();
    let (denom, rest) = field.split_at_mut(n);
    let (prefix, rest) = rest.split_at_mut(n);
    let (hs, rest) = rest.split_at_mut(n);
    let (rs, h2s) = rest.split_at_mut(n);
    let (&top, digits) = digits.split_last().unwrap();
    for (index, result) in output.iter_mut().enumerate() {
        let group = entries.group(index);
        *result = eisenstein::decoded_point(group, top).to_projective();
    }
    for &code in digits.iter().rev() {
        if code.is_zero() {
            for (d, p) in denom.iter_mut().zip(output.iter()) {
                *d = p.y.double();
            }
            invert_nonzero(denom, prefix);
            for (p, d) in output.iter_mut().zip(denom.iter()) {
                let xx = p.x.square();
                let slope = xx.double().add(&xx).mul(d);
                let x = slope.square().sub(&p.x.double());
                p.y = slope.mul(&p.x.sub(&x)).sub(&p.y);
                p.x = x;
            }
        } else {
            // Fuse 2P + D for P=(x,y), D=(u,v). Put h=u-x, r=v-y and
            // den=h²(2x+u)-r². With a=y/den, b=a*h and c=b*h²,
            // lambda=c-r gives x'=u+4b*lambda and
            // y'=-y-(1+4a*lambda)(lambda+c). These are the two chord
            // additions with their intermediate denominator eliminated.
            // Only den needs inversion; h=0 is allowed when D=-P.
            // The curve equations give den=2yr-3x²h, which vanishes when D
            // lies on P's tangent: D=P or D=-2P. The proof above excludes both.
            for (i, p) in output.iter_mut().enumerate() {
                let group = entries.group(i);
                let d = eisenstein::decoded_point(group, code);
                hs[i] = d.x.sub(&p.x);
                rs[i] = d.y.sub(&p.y);
                h2s[i] = hs[i].square();
                denom[i] = h2s[i].mul(&p.x.double().add(&d.x)).sub(&rs[i].square());
                // The finish needs the digit x and the original y only.
                p.x = d.x.into_loose();
            }
            invert_nonzero(denom, prefix);
            for (i, p) in output.iter_mut().enumerate() {
                let a = p.y.mul(&denom[i]);
                let b = a.mul(&hs[i]);
                let c = b.mul(&h2s[i]);
                let lambda = c.sub(&rs[i]);
                p.x = p.x.add(&b.mul(&lambda).double().double());
                p.y = p.y.neg().sub(
                    &PastaField::<C::Base>::ONE
                        .add(&a.mul(&lambda).double().double())
                        .mul(&lambda.add(&c)),
                );
            }
        }
    }
}
