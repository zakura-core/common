//! Joint width-three recoding in the Eisenstein integers.
//!
//! A pair `(a, b)` represents `a + b*lambda`, with `lambda² + lambda + 1 = 0`.
//! Multiplication by `lambda` rotates a pair to `(-b, a - b)`; signs and the
//! three rotations give six units. Evaluating `lambda` at the scalar field's
//! cube root of unity maps these integer pairs to scalars.

use super::{
    AffinePoint, CurveTableEntry, CurveTableRequirements, PastaCurve, ProjectivePoint,
    assert_scratch, batch,
};
use crate::field::{CanonicalUint, PastaField};
use core::marker::PhantomData;

pub(crate) const MAX_DIGITS: usize = 132;

/// A scalar decomposed and recoded for joint Eisenstein multiplication.
///
/// Prepare once for [`EisensteinTable::mul_prepared`] or
/// [`EisensteinTableBatch::mul_prepared`](super::EisensteinTableBatch::mul_prepared)
/// or [`batch_mul_same_scalar_prepared`](super::batch_mul_same_scalar_prepared)
/// when the same scalar acts on several bases. This fixed-size, allocation-free
/// value is specific to its curve and borrows neither the scalar nor a table.
/// Preparation and multiplication expose scalar-dependent timing and memory
/// access patterns; the representation does not provide constant-time lookup.
#[derive(Clone, Copy, Debug)]
pub struct EisensteinScalar<C: PastaCurve> {
    digits: [Digit; MAX_DIGITS],
    len: usize,
    marker: PhantomData<C>,
}

impl<C: PastaCurve> EisensteinScalar<C> {
    /// Records joint doubling-ladder digits for reuse across tables and batches.
    ///
    /// Preparation is variable-time and requires no allocation. The scalar uses
    /// [`PastaField`]'s loose representation.
    pub fn new(scalar: &PastaField<C::Scalar>) -> Self {
        Self::from_canonical(scalar.to_canonical_uint())
    }

    /// Recodes a canonical scalar integer into signed Eisenstein digits.
    ///
    /// The caller must establish that `scalar` is below `C::Scalar`'s modulus;
    /// [`CanonicalUint`] alone does not establish that bound.
    pub(super) fn from_canonical(scalar: CanonicalUint) -> Self {
        let (a, b) = super::glv::decompose_canonical::<C>(scalar);
        let (digits, len) = recode(a, b);
        Self {
            digits: digits.map(Digit::from_code),
            len,
            marker: PhantomData,
        }
    }

    pub(crate) fn digits(&self) -> &[Digit] {
        &self.digits[..self.len]
    }
}

/// A signed table index and endomorphism rotation, or the zero-digit sentinel.
///
/// Decoding when preparing the scalar avoids division and remainder in every
/// base's ladder. Entry 8 denotes zero and must never reach table lookup;
/// nonzero entries are in `0..8`, with rotations in `0..3`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Digit {
    pub(super) entry: u8,
    pub(super) rotation: u8,
    pub(super) negative: bool,
}

impl Digit {
    pub(super) fn from_code(code: u8) -> Self {
        if code == 0 {
            Self {
                entry: 8,
                rotation: 0,
                negative: false,
            }
        } else {
            let value = code - 1;
            Self {
                entry: value / 6,
                rotation: (value % 6) / 2,
                negative: value & 1 != 0,
            }
        }
    }
    pub(super) fn is_zero(self) -> bool {
        self.entry == 8
    }
}

/// Coefficients `a + b*lambda`, in retained table order.
pub(super) const REPRESENTATIVES: [(i8, i8); 8] = [
    (1, 0),
    (1, -1),
    (2, -1),
    (1, -2),
    (3, 0),
    (3, -1),
    (1, -3),
    (2, -3),
];

// All 48 signed unit rotations cover precisely the residue pairs modulo 8
// that are not both even. Subtracting the selected digit makes both residual
// coordinates divisible by 8, so the next two ladder digits are zero.
// The affine ladder proof in eisenstein_batch relies on this spacing and the
// digit-coordinate bound of 5.
// Generating the selector keeps its codes tied to the retained table order.
const SELECTOR: [(i8, i8, u8); 64] = {
    let mut table = [(0, 0, 0); 64];
    let mut representative = 0;
    while representative < 8 {
        let (mut a, mut b) = REPRESENTATIVES[representative];
        let mut rotation = 0;
        while rotation < 3 {
            let mut negative = 0;
            while negative < 2 {
                let (a, b) = if negative == 0 { (a, b) } else { (-a, -b) };
                assert!(a.unsigned_abs() <= 5 && b.unsigned_abs() <= 5);
                let index = (((a & 7) << 3) | (b & 7)) as usize;
                assert!(table[index].2 == 0);
                table[index] = (
                    a,
                    b,
                    (representative * 6 + rotation * 2 + negative + 1) as u8,
                );
                negative += 1;
            }
            (a, b) = (-b, a - b);
            rotation += 1;
        }
        representative += 1;
    }
    let mut index = 0;
    while index < 64 {
        assert!((table[index].2 == 0) == (index & 9 == 0));
        index += 1;
    }
    table
};

// Each digit coordinate has magnitude at most 5. Dividing by two after
// subtraction takes 127-bit inputs to magnitude <= 5 in 127 steps; the
// remaining small pairs terminate within five further steps.
pub(crate) fn recode(mut a: i128, mut b: i128) -> ([u8; MAX_DIGITS], usize) {
    debug_assert!(a != i128::MIN && b != i128::MIN);
    let mut digits = [0; MAX_DIGITS];
    let mut len = 0;
    while a != 0 || b != 0 {
        let (digit_a, digit_b, code) = SELECTOR[(((a & 7) << 3) | (b & 7)) as usize];
        digits[len] = code;
        // Equal parity makes this exact, without overflowing on a - digit_a.
        a = (a >> 1) - (i128::from(digit_a) >> 1);
        b = (b >> 1) - (i128::from(digit_b) >> 1);
        len += 1;
    }
    (digits, len)
}

pub(super) fn representatives_affine<C: PastaCurve>(
    base: &AffinePoint<C>,
) -> [ProjectivePoint<C>; 8] {
    // Use the same coefficient identities as representatives, keeping phi(base)
    // affine. Commuting sums and negating the projective operand in differences
    // makes six of the seven additions mixed; intermediates need no inversion.
    let phi = base.endomorphism();
    let difference = base.to_projective().add_mixed(&phi.neg());
    let b = difference.sub(&difference.endomorphism());
    let b_phi = b.endomorphism();
    let minus_three = b_phi.endomorphism();
    let three_a = minus_three.add_mixed(&phi);
    let three_b = minus_three.neg().add_mixed(&phi);
    let four_a = b_phi.neg().add_mixed(&phi);
    let four_b = b_phi.add_mixed(&phi);
    let nineteen = four_b.add_mixed(&phi);
    [
        base.to_projective(),
        difference,
        four_a.endomorphism(),
        three_b.endomorphism().neg(),
        minus_three.neg(),
        three_a.neg(),
        four_b.endomorphism().endomorphism(),
        nineteen.endomorphism().endomorphism(),
    ]
}

/// Eight borrowed representatives for repeated multiplication of one base.
///
/// Write `[a] P` for multiplication of point `P` by a signed integer `a`.
/// Entry order is `[a] base + [b] base.endomorphism()` for coefficient pairs
/// `(1,0), (1,-1), (2,-1), (1,-2), (3,0), (3,-1), (1,-3), (2,-3)`.
/// Each entry supplies six points by applying [`AffinePoint::endomorphism`]
/// zero, one, or two times, with either sign. These 48 points serve as digits
/// in a doubling ladder over the two halves from
/// [`glv_decompose`](super::glv_decompose).
///
/// The default [`AffinePoint`] entries occupy 512 bytes; choose
/// [`PreparedAffinePoint`](super::PreparedAffinePoint) entries for 768 bytes and
/// cheaper rotations.
/// These sizes exclude the base and table handle. Preparation
/// and multiplication are allocation-free and provide no constant-time
/// guarantee for secret bases, scalars, or table contents.
/// The entry count is encoded in the borrowed array type.
#[derive(Clone, Copy)]
pub struct EisensteinTable<'a, C: PastaCurve, E: CurveTableEntry<C> = AffinePoint<C>> {
    base: AffinePoint<C>,
    entries: &'a [E; 8],
}

impl<C: PastaCurve, E: CurveTableEntry<C>> core::fmt::Debug for EisensteinTable<'_, C, E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("EisensteinTable")
            .field("base", &self.base)
            .field("entries", &self.entries)
            .finish()
    }
}

impl<'a, C: PastaCurve, E: CurveTableEntry<C>> EisensteinTable<'a, C, E> {
    /// Exact entry count and minimum preparation scratch lengths.
    pub const REQUIREMENTS: CurveTableRequirements = CurveTableRequirements {
        table_entries: 8,
        projective_scratch: 8,
        field_scratch: 8,
    };

    /// Prepares eight entries in caller-owned storage using one inversion.
    ///
    /// Both scratch buffers must have at least eight elements; shorter buffers panic
    /// before any writes. Initial contents do not matter. Scratch tails are untouched
    /// and scratch can be reused as soon as this returns.
    ///
    /// The returned view borrows only `entries`.
    ///
    /// ```
    /// use zakura_udon::{
    ///     curve::{
    ///         EisensteinTable, Pallas, PallasAffine, PallasProjective,
    ///         PreparedAffinePoint,
    ///     },
    ///     field::{Fp, Fq},
    /// };
    /// let base = PallasAffine::GENERATOR;
    /// let mut entries = [PreparedAffinePoint::from_affine(&base); 8];
    /// let mut projective = [PallasProjective::IDENTITY; 8];
    /// let mut field = [Fp::ZERO; 8];
    /// let table = EisensteinTable::<Pallas, PreparedAffinePoint<Pallas>>::prepare(
    ///     &base, &mut entries, &mut projective, &mut field,
    /// );
    /// let scalar = Fq::from_u64(42);
    /// assert_eq!(table.mul(&scalar), base.mul_projective(&scalar));
    /// ```
    pub fn prepare(
        base: &AffinePoint<C>,
        entries: &'a mut [E; 8],
        projective_scratch: &mut [ProjectivePoint<C>],
        field_scratch: &mut [PastaField<C::Base>],
    ) -> Self {
        assert_scratch("projective", 8, projective_scratch.len());
        assert_scratch("field", 8, field_scratch.len());
        projective_scratch[..8].copy_from_slice(&representatives_affine(base));
        normalize(&projective_scratch[..8], &mut field_scratch[..8], entries);
        Self {
            base: *base,
            entries,
        }
    }

    /// Borrows trusted entries in the representative order documented on this type.
    ///
    /// `entries` must have been prepared for `base`. Binding preserves the stored
    /// representation and performs no field or curve arithmetic.
    pub const fn bind(base: &AffinePoint<C>, entries: &'a [E; 8]) -> Self {
        Self {
            base: *base,
            entries,
        }
    }

    /// Borrows the nonidentity base.
    pub const fn base(&self) -> &AffinePoint<C> {
        &self.base
    }

    /// Borrows entries in the representative order documented on this type.
    pub const fn as_slice(&self) -> &'a [E] {
        self.entries
    }

    /// Borrows the eight entries in the representative order documented on this type.
    pub const fn as_array(&self) -> &'a [E; 8] {
        self.entries
    }

    /// Multiplies by a scalar; zero returns identity.
    ///
    /// Uses bounded stack storage without caller scratch or
    /// allocation. Execution is variable-time.
    pub fn mul(&self, scalar: &PastaField<C::Scalar>) -> ProjectivePoint<C> {
        self.mul_prepared(&EisensteinScalar::new(scalar))
    }

    /// Multiplies using digits that can be reused across tables and batches.
    ///
    /// Has the same entry requirements as [`Self::mul`], and requires no
    /// scratch or allocation. A zero scalar returns identity.
    pub fn mul_prepared(&self, scalar: &EisensteinScalar<C>) -> ProjectivePoint<C> {
        multiply(self.entries, scalar.digits())
    }
}

pub(super) fn normalize<C: PastaCurve, E: CurveTableEntry<C>>(
    points: &[ProjectivePoint<C>],
    field: &mut [PastaField<C::Base>],
    entries: &mut [E],
) {
    batch::normalize(points, field, |index, point| {
        // None of the eight small Eisenstein representatives vanishes modulo
        // the prime scalar modulus, so their nonidentity multiples stay so.
        entries[index] = E::from_affine(point.as_affine().expect("nonidentity representative"));
    });
}

pub(crate) fn decoded_point<C: PastaCurve, E: CurveTableEntry<C>>(
    entries: &[E],
    code: Digit,
) -> AffinePoint<C> {
    let entry = entries[usize::from(code.entry)].rotated(usize::from(code.rotation));
    if code.negative { entry.neg() } else { entry }
}

pub(super) fn multiply<C: PastaCurve, E: CurveTableEntry<C>>(
    entries: &[E],
    digits: &[Digit],
) -> ProjectivePoint<C> {
    let mut result = ProjectivePoint::IDENTITY;
    for &code in digits.iter().rev() {
        result = result.double();
        if !code.is_zero() {
            result = result.add_mixed(&decoded_point(entries, code));
        }
    }
    result
}

pub(crate) fn digit_point<C: PastaCurve, E: CurveTableEntry<C>>(
    entries: &[E],
    code: u8,
) -> AffinePoint<C> {
    decoded_point(entries, Digit::from_code(code))
}
