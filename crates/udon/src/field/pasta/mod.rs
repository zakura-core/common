//! Pasta representations, parameters, and optimized field kernels.

#![forbid(unsafe_code)]

use core::{fmt, marker::PhantomData};

mod algorithms;
mod batch;
pub(crate) mod butterfly;
mod constant_prefix;
mod encoding;
mod fractions;
mod inversion;
mod montgomery;
mod parameters;
mod powers;
mod products;
mod representation;
mod safegcd;
mod small;
mod sqrt;
mod stored_form;
mod uint;
pub(crate) mod word;

#[cfg(feature = "traits")]
pub(crate) use batch::invert_groups;
pub use batch::{
    BatchInversionError, batch_invert, batch_invert_groups, batch_invert_groups_scaled,
    batch_invert_scaled, try_batch_invert_by, try_batch_invert_scaled_by,
};
pub(crate) use batch::{NonzeroInversionLanes, invert_nonzero};
pub use constant_prefix::{ConstantPrefix, ConstantPrefixError};
pub use encoding::{low_u64, random};
pub use fractions::{FractionPrefixError, fraction_prefixes, fraction_prefixes_in_place};
#[cfg(test)]
pub(crate) use inversion::count_inversions;
pub use parameters::{PallasBase, PallasScalar, PrimeModulus};
pub(crate) use powers::fill_powers;
#[cfg(test)]
pub(crate) use products::count_slice_sums;
pub use products::{ProductSum, dot, dot_iter};
pub use representation::{Loose, Reduced, ReductionState};
pub use stored_form::STORED_FORM;
pub use uint::CanonicalUint;
pub(crate) const TWO_ADICITY: u32 = parameters::TWO_ADICITY;

use montgomery::{montgomery_multiply_loose, montgomery_square, reduce_once};
use word::adc;

#[cfg(test)]
pub(crate) mod test_support;
#[cfg(test)]
mod tests;

const ENCODED_SIZE: usize = 32;

/// An element of a Pasta prime field stored as four Montgomery limbs.
///
/// The representation state `S` carries the bound on the stored Montgomery
/// integer: [`Loose`] permits `[0, 2p)` and [`Reduced`] permits `[0, p)`.
/// Arithmetic returns loose values. [`reduce`](Self::reduce) produces the
/// unique representative required by equality, ordering, and square roots.
/// Only reduced values implement equality, comparing their limbs directly.
/// Comparing loose field values requires an explicit reduction of both sides.
/// The exact loose limbs of an arithmetic result are not guaranteed; equivalent
/// computations can produce different representatives within the bound.
/// Ordering and debug output use the canonical field integer.
///
/// Arithmetic uses explicit methods, including when the unstable `traits`
/// feature is enabled. Consumer code can wrap loose values in
/// `field::FieldAdapter` to use operators and the `field::Field` interface.
///
/// Implements [`bento::Pod`] so a constructed value can be written as bytes
/// and embedded with its exact limbs and representation state. Stored values
/// are trusted to uphold their type's invariant and are used directly.
/// [`from_montgomery_limbs`](Self::from_montgomery_limbs) constructs a new value
/// from raw limbs, checking the bound selected by `S`.
///
/// [`crate::stored_form!`] identifies the stored representation of both fields.
/// Use [`to_bytes`](Self::to_bytes) for canonical protocol encoding.
///
/// ```
/// use zakura_udon::field::Fp;
/// static ZERO: &Fp = bento::AlignedBytes([0; 32]).as_value();
/// assert_eq!(ZERO.add(&<Fp>::ONE).reduce(), <Fp>::ONE.reduce());
/// ```
// SAFETY: The derive checks the integer array and marker layout. All limb bit
// patterns are valid to read and share. The state's bound is required for
// mathematical results, not memory safety. Assembly kernels use registers or
// fixed-size limb accesses; arbitrary limb bits cannot affect memory validity.
#[derive(Clone, Copy, bento::Pod)]
#[repr(transparent)]
pub struct PastaField<M: PrimeModulus, S: ReductionState = Loose> {
    limbs: [u64; 4],
    marker: PhantomData<(M, S)>,
}

/// The Pallas coordinate field and Vesta scalar field.
pub type Fp<S = Loose> = PastaField<PallasBase, S>;
/// The Vesta coordinate field and Pallas scalar field.
pub type Fq<S = Loose> = PastaField<PallasScalar, S>;

impl<M: PrimeModulus> PartialEq for PastaField<M, Reduced> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.limbs == other.limbs
    }
}

impl<M: PrimeModulus> Eq for PastaField<M, Reduced> {}

impl<M: PrimeModulus> Ord for PastaField<M, Reduced> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        // Multiplication by R preserves equality, but not integer ordering.
        self.to_canonical_uint().cmp(&other.to_canonical_uint())
    }
}

impl<M: PrimeModulus> PartialOrd for PastaField<M, Reduced> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<M: PrimeModulus, S: ReductionState> fmt::Debug for PastaField<M, S> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let limbs = self.canonical_limbs();
        write!(
            formatter,
            "0x{:016x}{:016x}{:016x}{:016x}",
            limbs[3], limbs[2], limbs[1], limbs[0]
        )
    }
}

impl<M: PrimeModulus, S: ReductionState> Default for PastaField<M, S> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<M: PrimeModulus, S: ReductionState> PastaField<M, S> {
    /// The additive identity in stored Montgomery form.
    pub const ZERO: Self = Self {
        limbs: [0; 4],
        marker: PhantomData,
    };
    /// The multiplicative identity, whose stored limbs are `R mod p`.
    pub const ONE: Self = Self {
        limbs: M::R,
        marker: PhantomData,
    };

    #[inline]
    const fn from_montgomery(limbs: [u64; 4]) -> Self {
        debug_assert!(word::compare_limbs(&limbs, &Self::BOUND).is_lt());
        Self {
            limbs,
            marker: PhantomData,
        }
    }

    // Constructors select their result state statically; arithmetic itself
    // always returns Loose. This is not an import or stored-value validator.
    const BOUND: [u64; 4] = if S::REDUCED {
        M::MODULUS
    } else {
        M::TWICE_MODULUS
    };

    #[inline]
    const fn from_loose(limbs: [u64; 4]) -> Self {
        Self::from_montgomery(if S::REDUCED {
            reduce_once::<M>(limbs)
        } else {
            limbs
        })
    }

    /// Returns the unique representative in `[0, p)`.
    ///
    /// Loose values pay for one conditional subtraction. Reduced values are
    /// returned unchanged; no runtime representation flag is stored or tested.
    #[inline]
    pub const fn reduce(self) -> PastaField<M, Reduced> {
        PastaField {
            limbs: if S::REDUCED {
                self.limbs
            } else {
                reduce_once::<M>(self.limbs)
            },
            marker: PhantomData,
        }
    }

    /// Widens the representation bound without changing any limbs.
    #[inline]
    pub const fn into_loose(self) -> PastaField<M> {
        PastaField {
            limbs: self.limbs,
            marker: PhantomData,
        }
    }

    /// Embeds an unsigned 64-bit integer; every such integer is below both moduli.
    pub fn from_u64(value: u64) -> Self {
        Self::from_canonical_limbs([value, 0, 0, 0])
    }

    /// Embeds an unsigned 128-bit integer; every such integer is below both moduli.
    pub fn from_u128(value: u128) -> Self {
        Self::from_canonical_limbs([value as u64, (value >> 64) as u64, 0, 0])
    }

    /// Returns whether this value is zero, recognizing both `0` and `p`
    /// in the loose representation.
    #[inline]
    pub const fn is_zero(&self) -> bool {
        let limbs = self.limbs;
        (limbs[0] == 0 && limbs[1] == 0 && limbs[2] == 0 && limbs[3] == 0)
            || (!S::REDUCED
                && limbs[0] == M::MODULUS[0]
                && limbs[1] == M::MODULUS[1]
                && limbs[2] == M::MODULUS[2]
                && limbs[3] == M::MODULUS[3])
    }

    /// Returns whether this value is one, recognizing both `R mod p` and
    /// `(R mod p) + p` in the loose Montgomery representation.
    #[inline]
    pub const fn is_one(&self) -> bool {
        let limbs = self.limbs;
        let loose_one = const { word::add_limbs(&M::R, &M::MODULUS).0 };
        (limbs[0] == M::R[0] && limbs[1] == M::R[1] && limbs[2] == M::R[2] && limbs[3] == M::R[3])
            || (!S::REDUCED
                && limbs[0] == loose_one[0]
                && limbs[1] == loose_one[1]
                && limbs[2] == loose_one[2]
                && limbs[3] == loose_one[3])
    }

    /// Returns `self + rhs`.
    #[inline]
    pub fn add<T: ReductionState>(&self, rhs: &PastaField<M, T>) -> PastaField<M> {
        PastaField::from_montgomery(montgomery::add_twice_modulus::<M>(&self.limbs, &rhs.limbs))
    }

    /// Returns `self - rhs`.
    #[inline]
    pub fn sub<T: ReductionState>(&self, rhs: &PastaField<M, T>) -> PastaField<M> {
        PastaField::from_montgomery(montgomery::sub_twice_modulus::<M>(&self.limbs, &rhs.limbs))
    }

    /// Returns the additive inverse.
    #[inline]
    pub fn neg(&self) -> PastaField<M> {
        // Only the AArch64 backend's flag-carried subtraction beats the
        // portable masked form; x86-64 compiles that form into fewer
        // instructions than a call through the backend's memory operands.
        #[cfg(all(udon_aarch64_asm, not(miri)))]
        {
            PastaField::from_montgomery(montgomery::sub_twice_modulus::<M>(&[0; 4], &self.limbs))
        }
        #[cfg(not(all(udon_aarch64_asm, not(miri))))]
        {
            // 2p - a masked to zero for a = 0: the zero test becomes mask
            // arithmetic instead of a branch on the operand value.
            let (limbs, borrow) = word::subtract_limbs(&M::TWICE_MODULUS, &self.limbs);
            debug_assert_eq!(borrow, 0);
            let nonzero = self.limbs[0] | self.limbs[1] | self.limbs[2] | self.limbs[3];
            let mask = u64::from(nonzero != 0).wrapping_neg();
            PastaField::from_montgomery([
                limbs[0] & mask,
                limbs[1] & mask,
                limbs[2] & mask,
                limbs[3] & mask,
            ])
        }
    }

    /// Returns `self * rhs`.
    #[inline]
    pub fn mul<T: ReductionState>(&self, rhs: &PastaField<M, T>) -> PastaField<M> {
        PastaField::from_montgomery(montgomery_multiply_loose::<M>(&self.limbs, &rhs.limbs))
    }

    /// Returns `self * self`.
    #[inline(always)]
    pub fn square(&self) -> PastaField<M> {
        PastaField::from_montgomery(montgomery_square::<M>(&self.limbs))
    }

    /// Returns `2 * self`.
    #[inline(always)]
    pub fn double(&self) -> PastaField<M> {
        // As for `neg`, only AArch64 routes doubling through the backend.
        #[cfg(all(udon_aarch64_asm, not(miri)))]
        {
            PastaField::from_montgomery(montgomery::add_twice_modulus::<M>(
                &self.limbs,
                &self.limbs,
            ))
        }
        #[cfg(not(all(udon_aarch64_asm, not(miri))))]
        {
            // 4p exceeds the radix, so preserve the high carry before reducing
            // modulo 2p.
            let limbs = [
                self.limbs[0] << 1,
                (self.limbs[1] << 1) | (self.limbs[0] >> 63),
                (self.limbs[2] << 1) | (self.limbs[1] >> 63),
                (self.limbs[3] << 1) | (self.limbs[2] >> 63),
            ];
            PastaField::from_montgomery(montgomery::reduce_twice_modulus::<M>(
                limbs,
                self.limbs[3] >> 63,
            ))
        }
    }

    /// Returns `self / 2`, preserving the representation bound.
    #[inline]
    pub(crate) fn half(&self) -> Self {
        // Stored parity can differ from canonical parity. For residue a and
        // odd modulus p, adding p when a is odd makes the integer even without
        // changing its field value. Since a < 2p and 3p < R, a + p fits.
        // Halving also preserves the tighter bound when a < p.
        let mask = (self.limbs[0] & 1).wrapping_neg();
        let mut limbs = self.limbs;
        let mut carry = 0;
        for (limb, modulus) in limbs.iter_mut().zip(M::MODULUS) {
            (*limb, carry) = adc(*limb, modulus & mask, carry);
        }
        debug_assert_eq!(carry, 0);
        Self::from_montgomery([
            (limbs[0] >> 1) | (limbs[1] << 63),
            (limbs[1] >> 1) | (limbs[2] << 63),
            (limbs[2] >> 1) | (limbs[3] << 63),
            limbs[3] >> 1,
        ])
    }

    /// Returns `3 * self`.
    #[inline]
    pub fn triple(&self) -> PastaField<M> {
        small::multiply::<M, 3>(self.limbs)
    }

    /// Returns `4 * self`.
    #[inline]
    pub fn mul_by_4(&self) -> PastaField<M> {
        small::multiply::<M, 4>(self.limbs)
    }

    /// Returns `8 * self`.
    #[inline]
    pub fn mul_by_8(&self) -> PastaField<M> {
        small::multiply::<M, 8>(self.limbs)
    }

    /// Returns `self * multiplier + addend`.
    #[inline]
    pub fn mul_add<T: ReductionState, U: ReductionState>(
        &self,
        multiplier: &PastaField<M, T>,
        addend: &PastaField<M, U>,
    ) -> PastaField<M> {
        #[cfg(all(test, feature = "traits"))]
        test_support::record_mul_add();
        self.mul(multiplier).add(addend)
    }

    /// Returns `self * multiplier - subtrahend`.
    #[inline]
    pub fn mul_sub<T: ReductionState, U: ReductionState>(
        &self,
        multiplier: &PastaField<M, T>,
        subtrahend: &PastaField<M, U>,
    ) -> PastaField<M> {
        self.mul(multiplier).sub(subtrahend)
    }

    /// Raises this value to an unsigned exponent; exponent zero returns one.
    ///
    /// The multiplication schedule depends on the exponent.
    pub fn pow_u64(&self, exponent: u64) -> PastaField<M> {
        crate::field::pasta::algorithms::pow_u64(&self.into_loose(), exponent)
    }

    /// Embeds a signed 64-bit integer, including `i64::MIN`.
    #[inline]
    pub fn from_i64(coefficient: i64) -> Self {
        let value = Self::from_u64(coefficient.unsigned_abs());
        if coefficient < 0 {
            Self::from_loose(value.neg().limbs)
        } else {
            value
        }
    }
}

// Inline arithmetic wrappers so generic exponentiation uses the specialized kernels.
impl<M: PrimeModulus> PastaField<M, Reduced> {
    /// Subtracts canonical residues without passing through the loose range.
    #[inline(always)]
    pub(crate) fn sub_reduced(&self, rhs: &Self) -> Self {
        #[cfg(all(udon_asm, not(miri)))]
        let limbs = crate::field::asm::sub_loose(&self.limbs, &rhs.limbs, &M::MODULUS);
        #[cfg(not(all(udon_asm, not(miri))))]
        let limbs = {
            let (difference, borrow) = word::borrow_sub_limbs(&self.limbs, &rhs.limbs);
            let mask = (borrow as u64).wrapping_neg();
            let restore = M::MODULUS.map(|limb| limb & mask);
            word::carry_add_limbs(&difference, &restore).0
        };
        Self::from_montgomery(limbs)
    }

    /// Returns the additive inverse of a nonzero value, reduced.
    ///
    /// `p - a` is canonical for `0 < a < p`. Curve code uses this for
    /// coordinates that cannot be zero, avoiding the `2p` restoration and
    /// conditional reduction of [`Self::neg`]. A zero input, which no valid
    /// nonidentity point coordinate can be, would yield `p`; the debug
    /// assertion rejects it, and only trusted storage can present one.
    #[inline]
    pub(crate) fn negate_nonzero(&self) -> Self {
        debug_assert!(!self.is_zero());
        #[cfg(all(udon_asm, not(miri)))]
        let limbs = crate::field::asm::subtract_wrapping(&M::MODULUS, &self.limbs);
        #[cfg(not(all(udon_asm, not(miri))))]
        let limbs = word::subtract_limbs(&M::MODULUS, &self.limbs).0;
        PastaField::from_montgomery(limbs)
    }
}

impl<M: PrimeModulus> crate::field::pasta::algorithms::Field for PastaField<M> {
    const ONE: Self = Self::ONE;
    #[inline(always)]
    fn mul(&self, rhs: &Self) -> Self {
        self.mul(rhs)
    }
    #[inline(always)]
    fn square(&self) -> Self {
        self.square()
    }
}

#[cfg(any(test, not(feature = "sqrt-table-large")))]
impl<M: PrimeModulus> algorithms::SqrtField for PastaField<M> {
    const ZERO: Self = Self::ZERO;
    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.is_zero()
    }
    #[inline(always)]
    fn is_one(&self) -> bool {
        self.is_one()
    }
}
