//! Inherent field operations; no RustCrypto field or group traits are required.
use super::{Fp, Fq};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

macro_rules! field {
    ($field:ident, $native:ident, $modulus:ident) => {
        impl $field {
            /// The additive identity.
            pub const ZERO: Self = Self(udon::field::$native::ZERO);
            /// The multiplicative identity.
            pub const ONE: Self = Self(udon::field::$native::ONE);
            /// Number of bits in a canonical field element.
            pub const NUM_BITS: u32 = 255;
            /// The additive identity.
            pub const fn zero() -> Self {
                Self::ZERO
            }
            /// The multiplicative identity.
            pub const fn one() -> Self {
                Self::ONE
            }
            /// Reduces a four-limb little-endian integer modulo the field order.
            ///
            /// Accepts every 256-bit integer. The limbs encode an ordinary integer;
            /// use [`Self::from_native`] to wrap a typed native field value and
            /// [`Self::from_bytes`] for canonical byte decoding.
            pub fn from_raw(limbs: [u64; 4]) -> Self {
                Self::from_native(udon::field::$native::from_uint_reduced(
                    udon::field::CanonicalUint::from_limbs(limbs),
                ))
            }
            /// Embeds a 128-bit unsigned integer in the field.
            pub fn from_u128(value: u128) -> Self {
                Self::from_raw([value as u64, (value >> 64) as u64, 0, 0])
            }
            /// Decodes a canonical little-endian integer, without reducing it.
            ///
            /// Uses [`Self::from_bytes`]'s validation, returning an empty
            /// [`CtOption`] on rejection.
            pub fn from_repr(bytes: [u8; 32]) -> CtOption<Self> {
                let value = Self::from_bytes(bytes);
                CtOption::new(
                    value.unwrap_or(Self::zero()),
                    Choice::from(value.is_ok() as u8),
                )
            }
            /// Returns the canonical little-endian integer.
            pub fn to_repr(self) -> [u8; 32] {
                self.to_bytes()
            }
            /// Reduces a wide little-endian integer modulo the field order.
            ///
            /// Accepts every 64-byte input. Use [`Self::from_bytes`] for canonical
            /// byte decoding.
            pub fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
                Self::from_native(udon::field::$native::from_wide_bytes_reduced(bytes))
            }
            /// Samples by reducing eight random little-endian words.
            pub fn random(mut rng: impl rand::Rng) -> Self {
                let mut bytes = [0; 64];
                for chunk in bytes.chunks_exact_mut(8) {
                    chunk.copy_from_slice(&rng.next_u64().to_le_bytes());
                }
                Self::from_uniform_bytes(&bytes)
            }
            /// Returns the canonical integer's little-endian bits.
            pub fn to_le_bits(self) -> bitvec::array::BitArray<[u8; 32], bitvec::order::Lsb0> {
                self.to_bytes().into()
            }
            /// Returns whether this element is zero.
            pub const fn is_zero(&self) -> bool {
                self.0.is_zero()
            }
            /// Returns whether this element is zero using variable-time comparison.
            pub fn is_zero_vartime(&self) -> bool {
                self.0.is_zero()
            }
            /// Returns whether two field elements are equal.
            pub fn eq_vartime(&self, rhs: &Self) -> bool {
                self == rhs
            }
            /// Returns whether the canonical integer is odd.
            pub fn is_odd(&self) -> Choice {
                Choice::from(self.0.is_odd() as u8)
            }
            /// Returns twice this element.
            pub fn double(&self) -> Self {
                Self::from_native(self.0.double())
            }
            /// Returns the square of this element.
            pub fn square(&self) -> Self {
                Self::from_native(self.0.square())
            }
            /// Returns the multiplicative inverse, or none for zero.
            pub fn invert(&self) -> CtOption<Self> {
                let value = self.0.invert();
                CtOption::new(
                    Self::from_native(value.unwrap_or(udon::field::$native::ZERO)),
                    Choice::from(value.is_some() as u8),
                )
            }
            /// Returns a square root, or none for a nonsquare.
            pub fn sqrt(&self) -> CtOption<Self> {
                let value = self.0.reduce().sqrt();
                CtOption::new(
                    Self(value.unwrap_or(udon::field::$native::ZERO).into_loose()),
                    Choice::from(value.is_some() as u8),
                )
            }
            /// Raises this element to a little-endian sequence of exponent limbs.
            pub fn pow_vartime(&self, exponent: impl AsRef<[u64]>) -> Self {
                let mut result = Self::ONE;
                for limb in exponent.as_ref().iter().rev() {
                    for bit in (0..64).rev() {
                        result = result.square();
                        if (limb >> bit) & 1 != 0 {
                            result *= self;
                        }
                    }
                }
                result
            }
        }
        impl Default for $field {
            fn default() -> Self {
                Self::zero()
            }
        }
        impl From<u64> for $field {
            fn from(value: u64) -> Self {
                Self::from_native(udon::field::$native::from_u64(value))
            }
        }
        impl From<bool> for $field {
            fn from(value: bool) -> Self {
                Self::from(u64::from(value))
            }
        }
        impl PartialEq for $field {
            fn eq(&self, rhs: &Self) -> bool {
                self.0.reduce() == rhs.0.reduce()
            }
        }
        impl Eq for $field {}
        impl Ord for $field {
            fn cmp(&self, rhs: &Self) -> core::cmp::Ordering {
                self.0.reduce().cmp(&rhs.0.reduce())
            }
        }
        impl PartialOrd for $field {
            fn partial_cmp(&self, rhs: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(rhs))
            }
        }
        impl ConstantTimeEq for $field {
            fn ct_eq(&self, rhs: &Self) -> Choice {
                self.0
                    .reduce()
                    .montgomery_limbs()
                    .ct_eq(&rhs.0.reduce().montgomery_limbs())
            }
        }
        impl ConditionallySelectable for $field {
            fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                let a = a.0.montgomery_limbs();
                let b = b.0.montgomery_limbs();
                Self(udon::field::$native::from_montgomery_limbs(
                    core::array::from_fn(|i| u64::conditional_select(&a[i], &b[i], choice)),
                ))
            }
        }
        impl Neg for $field {
            type Output = Self;
            fn neg(self) -> Self {
                Self::from_native(self.0.neg())
            }
        }
        impl Neg for &$field {
            type Output = $field;
            fn neg(self) -> $field {
                -*self
            }
        }
        field_op!($field, Add, add, AddAssign, add_assign);
        field_op!($field, Sub, sub, SubAssign, sub_assign);
        field_op!($field, Mul, mul, MulAssign, mul_assign);
        impl core::iter::Sum for $field {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::zero(), |a, b| a + b)
            }
        }
        impl<'a> core::iter::Sum<&'a Self> for $field {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.copied().sum()
            }
        }
    };
}
macro_rules! field_op {
    ($field:ident, $trait:ident, $op:ident, $assign:ident, $assign_op:ident) => {
        impl $trait for $field {
            type Output = Self;
            fn $op(self, rhs: Self) -> Self {
                Self::from_native(self.0.$op(&rhs.0))
            }
        }
        impl $trait<&$field> for $field {
            type Output = Self;
            fn $op(self, rhs: &Self) -> Self {
                self.$op(*rhs)
            }
        }
        impl $trait<$field> for &$field {
            type Output = $field;
            fn $op(self, rhs: $field) -> $field {
                (*self).$op(rhs)
            }
        }
        impl $trait<&$field> for &$field {
            type Output = $field;
            fn $op(self, rhs: &$field) -> $field {
                (*self).$op(*rhs)
            }
        }
        impl $assign for $field {
            fn $assign_op(&mut self, rhs: Self) {
                *self = self.$op(rhs);
            }
        }
        impl $assign<&$field> for $field {
            fn $assign_op(&mut self, rhs: &Self) {
                *self = self.$op(*rhs);
            }
        }
    };
}
field!(Fp, Fp, PallasBase);
field!(Fq, Fq, PallasScalar);

#[cfg(test)]
mod tests {
    use super::*;
    use udon::field::{PallasBase, PallasScalar, PrimeModulus};
    #[test]
    fn loose_residues_have_canonical_equality_and_encoding() {
        let zero_p = Fp::from_native(udon::field::Fp::from_montgomery_limbs(PallasBase::MODULUS));
        let zero_q = Fq::from_native(udon::field::Fq::from_montgomery_limbs(
            PallasScalar::MODULUS,
        ));
        assert_eq!(zero_p, Fp::ZERO);
        assert_eq!(zero_q, Fq::ZERO);
        assert!(bool::from(zero_p.ct_eq(&Fp::ZERO)));
        assert!(bool::from(zero_q.ct_eq(&Fq::ZERO)));
        assert_eq!(zero_p.cmp(&Fp::ZERO), core::cmp::Ordering::Equal);
        assert_eq!(zero_q.cmp(&Fq::ZERO), core::cmp::Ordering::Equal);
        assert_eq!(zero_p.to_bytes(), [0; 32]);
        assert_eq!(zero_q.to_bytes(), [0; 32]);
        assert_eq!(zero_p + Fp::ONE, Fp::ONE);
        assert_eq!(zero_q + Fq::ONE, Fq::ONE);
        assert!(zero_p.is_zero() && zero_q.is_zero());
    }
}
