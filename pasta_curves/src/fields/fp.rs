use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};

use ff::{Field, FromUniformBytes, PrimeField, WithSmallOrderMulGroup};
use rand::TryRng;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "sqrt-table")]
use lazy_static::lazy_static;

#[cfg(feature = "bits")]
use ff::{FieldBits, PrimeFieldBits};

use crate::arithmetic::{sbb, SqrtTableHelpers};
#[cfg(not(feature = "cm-field"))]
use crate::arithmetic::{adc, mac};
#[cfg(feature = "cm-field")]
use super::cm;
#[cfg(feature = "deferred")]
use crate::deferred::DeferredField;
#[cfg(all(feature = "deferred", not(feature = "cm-field")))]
use crate::deferred::Product;
#[cfg(all(feature = "deferred", feature = "cm-field"))]
use crate::deferred::CmProduct;

/// The per-field CM parameter set (see `fields/cm.rs`).
#[cfg(feature = "cm-field")]
type CmP = cm::FpParams;

#[cfg(feature = "sqrt-table")]
use crate::arithmetic::SqrtTables;

/// This represents an element of $\mathbb{F}_p$ where
///
/// `p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001`
///
/// is the base field of the Pallas curve.
// The internal representation of this type is four 64-bit unsigned
// integers in little-endian order. By default `Fp` values are in
// Montgomery form; i.e., Fp(a) = aR mod p, with R = 2^256. Under the
// experimental `cm-field` feature the same four words instead pack two
// two's-complement `i128` coefficients (a, b) representing the element
// (a + b*sigma)/2^131 modulo the CM generator (see `fields/cm.rs`).
#[derive(Clone, Copy, Eq)]
#[repr(transparent)]
pub struct Fp(pub(crate) [u64; 4]);

// The 32-byte, u64-aligned storage shape is a crate-level contract
// (serialization, GPU code generation, and point layouts build on it);
// pin it independently of the internal representation.
static_assertions::assert_eq_size!(Fp, [u64; 4]);
static_assertions::assert_eq_align!(Fp, u64);

impl fmt::Debug for Fp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_repr();
        write!(f, "0x")?;
        for &b in tmp.iter().rev() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl From<bool> for Fp {
    fn from(bit: bool) -> Fp {
        if bit {
            Fp::one()
        } else {
            Fp::zero()
        }
    }
}

#[cfg(not(feature = "cm-field"))]
impl From<u64> for Fp {
    fn from(val: u64) -> Fp {
        Fp([val, 0, 0, 0]) * R2
    }
}

#[cfg(feature = "cm-field")]
impl From<u64> for Fp {
    fn from(val: u64) -> Fp {
        Fp(cm::pack(cm::from_u64::<CmP>(val)))
    }
}

// Montgomery residues are unique, so structural limb equality is field
// equality.
#[cfg(not(feature = "cm-field"))]
impl ConstantTimeEq for Fp {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0[0].ct_eq(&other.0[0])
            & self.0[1].ct_eq(&other.0[1])
            & self.0[2].ct_eq(&other.0[2])
            & self.0[3].ct_eq(&other.0[3])
    }
}

// The CM representation is redundant (representatives can differ by
// small lattice vectors), so equality must NOT compare stored words:
// normalize the difference and test the raw coefficients for zero.
#[cfg(feature = "cm-field")]
impl ConstantTimeEq for Fp {
    fn ct_eq(&self, other: &Self) -> Choice {
        cm::ct_eq::<CmP>(cm::unpack(&self.0), cm::unpack(&other.0))
    }
}

impl PartialEq for Fp {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).unwrap_u8() == 1
    }
}

impl core::cmp::Ord for Fp {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let left = self.to_repr();
        let right = other.to_repr();
        left.iter()
            .zip(right.iter())
            .rev()
            .find_map(|(left_byte, right_byte)| match left_byte.cmp(right_byte) {
                core::cmp::Ordering::Equal => None,
                res => Some(res),
            })
            .unwrap_or(core::cmp::Ordering::Equal)
    }
}

impl core::cmp::PartialOrd for Fp {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl ConditionallySelectable for Fp {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp([
            u64::conditional_select(&a.0[0], &b.0[0], choice),
            u64::conditional_select(&a.0[1], &b.0[1], choice),
            u64::conditional_select(&a.0[2], &b.0[2], choice),
            u64::conditional_select(&a.0[3], &b.0[3], choice),
        ])
    }
}

/// Constant representing the modulus
/// p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
const MODULUS_LIMBS: [u64; 4] = [
    0x992d30ed00000001,
    0x224698fc094cf91b,
    0x0000000000000000,
    0x4000000000000000,
];

/// The modulus as u32 limbs.
#[cfg(not(target_pointer_width = "64"))]
const MODULUS_LIMBS_32: [u32; 8] = [
    0x0000_0001,
    0x992d_30ed,
    0x094c_f91b,
    0x2246_98fc,
    0x0000_0000,
    0x0000_0000,
    0x0000_0000,
    0x4000_0000,
];

impl<'a> Neg for &'a Fp {
    type Output = Fp;

    #[inline]
    fn neg(self) -> Fp {
        self.neg()
    }
}

impl Neg for Fp {
    type Output = Fp;

    #[inline]
    fn neg(self) -> Fp {
        -&self
    }
}

impl<'a, 'b> Sub<&'b Fp> for &'a Fp {
    type Output = Fp;

    #[inline]
    fn sub(self, rhs: &'b Fp) -> Fp {
        self.sub(rhs)
    }
}

impl<'a, 'b> Add<&'b Fp> for &'a Fp {
    type Output = Fp;

    #[inline]
    fn add(self, rhs: &'b Fp) -> Fp {
        self.add(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fp> for &'a Fp {
    type Output = Fp;

    #[inline]
    fn mul(self, rhs: &'b Fp) -> Fp {
        self.mul_runtime(rhs)
    }
}

impl_binops_additive!(Fp, Fp);
impl_binops_multiplicative!(Fp, Fp);

impl<T: ::core::borrow::Borrow<Fp>> ::core::iter::Sum<T> for Fp {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, item| acc + item.borrow())
    }
}

impl<T: ::core::borrow::Borrow<Fp>> ::core::iter::Product<T> for Fp {
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, item| acc * item.borrow())
    }
}

/// INV = -(p^{-1} mod 2^64) mod 2^64
#[cfg(not(feature = "cm-field"))]
const INV: u64 = 0x992d30ecffffffff;

/// R = 2^256 mod p (limbs; published to GPU kernels verbatim).
#[cfg_attr(feature = "cm-field", allow(dead_code))] // GPU-contract constant
const MONT_R_LIMBS: [u64; 4] = [
    0x34786d38fffffffd,
    0x992c350be41914ad,
    0xffffffffffffffff,
    0x3fffffffffffffff,
];

/// R as a field element (Montgomery form of 1).
#[cfg(not(feature = "cm-field"))]
const R: Fp = Fp(MONT_R_LIMBS);

/// R^2 = 2^512 mod p (limbs; published to GPU kernels verbatim).
#[cfg_attr(feature = "cm-field", allow(dead_code))] // GPU-contract constant
const MONT_R2_LIMBS: [u64; 4] = [
    0x8c78ecb30000000f,
    0xd7d30dbd8b0de0e7,
    0x7797a99bc3c95d18,
    0x096d41af7b9cb714,
];

/// R^2 as a field element (converts integers into Montgomery form).
#[cfg(not(feature = "cm-field"))]
const R2: Fp = Fp(MONT_R2_LIMBS);

/// R^3 = 2^768 mod p
#[cfg(not(feature = "cm-field"))]
const R3: Fp = Fp([
    0xf185a5993a9e10f9,
    0xf6a68f3b6ac5b1d1,
    0xdf8d1014353fd42c,
    0x2ae309222d2d9910,
]);

/// `GENERATOR = 5 mod p` is a generator of the `p - 1` order multiplicative
/// subgroup, or in other words a primitive root of the field.
const GENERATOR: Fp = Fp::from_raw([
    0x0000_0000_0000_0005,
    0x0000_0000_0000_0000,
    0x0000_0000_0000_0000,
    0x0000_0000_0000_0000,
]);

const S: u32 = 32;

/// GENERATOR^t where t * 2^s + 1 = p
/// with t odd. In other words, this
/// is a 2^s root of unity.
const ROOT_OF_UNITY: Fp = Fp::from_raw([
    0xbdad6fabd87ea32f,
    0xea322bf2b7bb7584,
    0x362120830561f81a,
    0x2bce74deac30ebda,
]);

/// GENERATOR^{2^s} where t * 2^s + 1 = p
/// with t odd. In other words, this
/// is a t root of unity.
const DELTA: Fp = Fp::from_raw([
    0x6a6ccd20dd7b9ba2,
    0xf5e4f3f13eee5636,
    0xbd455b7112a5049d,
    0x0a757d0f0006ab6c,
]);

/// `(t - 1) // 2` where t * 2^s + 1 = p with t odd.
#[cfg(any(test, not(feature = "sqrt-table")))]
const T_MINUS1_OVER2: [u64; 4] = [
    0x04a6_7c8d_cc96_9876,
    0x0000_0000_1123_4c7e,
    0x0000_0000_0000_0000,
    0x0000_0000_2000_0000,
];

impl Default for Fp {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl Fp {
    /// Returns zero, the additive identity.
    #[inline]
    pub const fn zero() -> Fp {
        Fp([0, 0, 0, 0])
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    #[cfg(not(feature = "cm-field"))]
    pub const fn one() -> Fp {
        R
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    #[cfg(feature = "cm-field")]
    pub const fn one() -> Fp {
        Fp(cm::pack(<CmP as cm::CmParams>::ONE))
    }

    /// Doubles this field element.
    #[inline]
    pub const fn double(&self) -> Fp {
        // TODO: This can be achieved more efficiently with a bitshift.
        self.add(self)
    }

    #[cfg(feature = "cm-field")]
    fn from_u512(limbs: [u64; 8]) -> Fp {
        Fp(cm::pack(cm::from_u512::<CmP>(&limbs)))
    }

    #[cfg(not(feature = "cm-field"))]
    fn from_u512(limbs: [u64; 8]) -> Fp {
        // We reduce an arbitrary 512-bit number by decomposing it into two 256-bit digits
        // with the higher bits multiplied by 2^256. Thus, we perform two reductions
        //
        // 1. the lower bits are multiplied by R^2, as normal
        // 2. the upper bits are multiplied by R^2 * 2^256 = R^3
        //
        // and computing their sum in the field. It remains to see that arbitrary 256-bit
        // numbers can be placed into Montgomery form safely using the reduction. The
        // reduction works so long as the product is less than R=2^256 multiplied by
        // the modulus. This holds because for any `c` smaller than the modulus, we have
        // that (2^256 - 1)*c is an acceptable product for the reduction. Therefore, the
        // reduction always works so long as `c` is in the field; in this case it is either the
        // constant `R2` or `R3`.
        let d0 = Fp([limbs[0], limbs[1], limbs[2], limbs[3]]);
        let d1 = Fp([limbs[4], limbs[5], limbs[6], limbs[7]]);
        // Convert to Montgomery form. `d0` and `d1` are unreduced, so use the
        // portable multiplication: its classical 8-limb reduction is valid for
        // any 256-bit value times a canonical constant, with no precondition
        // on the constant's limbs. The inline-assembly `mul` tolerates an
        // unreduced lhs only while every rhs limb stays at most `2^64 - 4`
        // (see `aarch64_asm.rs`); this cold path is not worth carrying that
        // coupling, and hashing dominates its callers anyway.
        Fp::mul(&d0, &R2).add(&Fp::mul(&d1, &R3))
    }

    /// Converts from an integer represented in little endian
    /// into its (congruent) `Fp` representation.
    #[cfg(not(feature = "cm-field"))]
    pub const fn from_raw(val: [u64; 4]) -> Self {
        (&Fp(val)).mul(&R2)
    }

    /// Converts from an integer represented in little endian
    /// into its (congruent) `Fp` representation.
    #[cfg(feature = "cm-field")]
    pub const fn from_raw(val: [u64; 4]) -> Self {
        Fp(cm::pack(cm::from_raw::<CmP>(val)))
    }

    /// Squares this element.
    #[cfg(not(feature = "cm-field"))]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub const fn square(&self) -> Fp {
        let u = self.square_unreduced();
        Fp::montgomery_reduce(u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7])
    }

    /// Squares this element.
    #[cfg(feature = "cm-field")]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub const fn square(&self) -> Fp {
        Fp(cm::pack(cm::square::<CmP>(cm::unpack(&self.0))))
    }

    #[cfg(not(feature = "cm-field"))]
    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(not(feature = "uninline-portable"), inline(always))]
    const fn montgomery_reduce(
        r0: u64,
        r1: u64,
        r2: u64,
        r3: u64,
        r4: u64,
        r5: u64,
        r6: u64,
        r7: u64,
    ) -> Self {
        // The Montgomery reduction here is based on Algorithm 14.32 in
        // Handbook of Applied Cryptography
        // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

        let k = r0.wrapping_mul(INV);
        let (_, carry) = mac(r0, k, MODULUS_LIMBS[0], 0);
        let (r1, carry) = mac(r1, k, MODULUS_LIMBS[1], carry);
        let (r2, carry) = mac(r2, k, MODULUS_LIMBS[2], carry);
        let (r3, carry) = mac(r3, k, MODULUS_LIMBS[3], carry);
        let (r4, carry2) = adc(r4, 0, carry);

        let k = r1.wrapping_mul(INV);
        let (_, carry) = mac(r1, k, MODULUS_LIMBS[0], 0);
        let (r2, carry) = mac(r2, k, MODULUS_LIMBS[1], carry);
        let (r3, carry) = mac(r3, k, MODULUS_LIMBS[2], carry);
        let (r4, carry) = mac(r4, k, MODULUS_LIMBS[3], carry);
        let (r5, carry2) = adc(r5, carry2, carry);

        let k = r2.wrapping_mul(INV);
        let (_, carry) = mac(r2, k, MODULUS_LIMBS[0], 0);
        let (r3, carry) = mac(r3, k, MODULUS_LIMBS[1], carry);
        let (r4, carry) = mac(r4, k, MODULUS_LIMBS[2], carry);
        let (r5, carry) = mac(r5, k, MODULUS_LIMBS[3], carry);
        let (r6, carry2) = adc(r6, carry2, carry);

        let k = r3.wrapping_mul(INV);
        let (_, carry) = mac(r3, k, MODULUS_LIMBS[0], 0);
        let (r4, carry) = mac(r4, k, MODULUS_LIMBS[1], carry);
        let (r5, carry) = mac(r5, k, MODULUS_LIMBS[2], carry);
        let (r6, carry) = mac(r6, k, MODULUS_LIMBS[3], carry);
        let (r7, _) = adc(r7, carry2, carry);

        // Result may be within MODULUS of the correct value
        (&Fp([r4, r5, r6, r7])).sub(&Fp(MODULUS_LIMBS))
    }

    /// Multiplies `rhs` by `self`, returning the result.
    #[cfg(not(feature = "cm-field"))]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub const fn mul(&self, rhs: &Self) -> Self {
        let u = self.mul_unreduced(rhs);
        Fp::montgomery_reduce(u[0], u[1], u[2], u[3], u[4], u[5], u[6], u[7])
    }

    /// Multiplies `rhs` by `self`, returning the result.
    #[cfg(feature = "cm-field")]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub const fn mul(&self, rhs: &Self) -> Self {
        Fp(cm::pack(cm::mul::<CmP>(cm::unpack(&self.0), cm::unpack(&rhs.0))))
    }

    #[inline]
    fn mul_runtime(&self, rhs: &Self) -> Self {
        #[cfg(all(
            feature = "aarch64-asm",
            not(feature = "cm-field"),
            target_arch = "aarch64",
            target_vendor = "apple"
        ))]
        {
            Fp(super::aarch64_asm::mul(&self.0, &rhs.0, &MODULUS_LIMBS, INV))
        }

        #[cfg(not(all(
            feature = "aarch64-asm",
            not(feature = "cm-field"),
            target_arch = "aarch64",
            target_vendor = "apple"
        )))]
        {
            self.mul(rhs)
        }
    }

    #[inline]
    fn square_runtime(&self) -> Self {
        #[cfg(all(
            feature = "aarch64-asm",
            not(feature = "cm-field"),
            target_arch = "aarch64",
            target_vendor = "apple"
        ))]
        {
            Fp(super::aarch64_asm::square(&self.0, &MODULUS_LIMBS, INV))
        }

        #[cfg(not(all(
            feature = "aarch64-asm",
            not(feature = "cm-field"),
            target_arch = "aarch64",
            target_vendor = "apple"
        )))]
        {
            self.square()
        }
    }

    /// Squares `self` `n` times (`n` must be at least 1), then multiplies the
    /// result by `by`. The assembly backend keeps the accumulator in
    /// registers for the whole chain.
    #[inline]
    fn sqr_n_mul_runtime(&self, n: u32, by: &Self) -> Self {
        assert!(n >= 1);

        #[cfg(all(
            feature = "aarch64-asm",
            not(feature = "cm-field"),
            target_arch = "aarch64",
            target_vendor = "apple"
        ))]
        {
            Fp(super::aarch64_asm::sqr_n_mul(
                &self.0, n as usize, &by.0, &MODULUS_LIMBS, INV,
            ))
        }

        #[cfg(not(all(
            feature = "aarch64-asm",
            not(feature = "cm-field"),
            target_arch = "aarch64",
            target_vendor = "apple"
        )))]
        {
            (0..n).fold(*self, |acc, _| acc.square()).mul(by)
        }
    }

    /// Subtracts `rhs` from `self`, returning the result.
    #[cfg(not(feature = "cm-field"))]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub const fn sub(&self, rhs: &Self) -> Self {
        let (d0, borrow) = sbb(self.0[0], rhs.0[0], 0);
        let (d1, borrow) = sbb(self.0[1], rhs.0[1], borrow);
        let (d2, borrow) = sbb(self.0[2], rhs.0[2], borrow);
        let (d3, borrow) = sbb(self.0[3], rhs.0[3], borrow);

        // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
        // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the modulus.
        let (d0, carry) = adc(d0, MODULUS_LIMBS[0] & borrow, 0);
        let (d1, carry) = adc(d1, MODULUS_LIMBS[1] & borrow, carry);
        let (d2, carry) = adc(d2, MODULUS_LIMBS[2] & borrow, carry);
        let (d3, _) = adc(d3, MODULUS_LIMBS[3] & borrow, carry);

        Fp([d0, d1, d2, d3])
    }

    /// Subtracts `rhs` from `self`, returning the result.
    #[cfg(feature = "cm-field")]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub const fn sub(&self, rhs: &Self) -> Self {
        Fp(cm::pack(cm::sub::<CmP>(cm::unpack(&self.0), cm::unpack(&rhs.0))))
    }

    /// Adds `rhs` to `self`, returning the result.
    #[cfg(not(feature = "cm-field"))]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub const fn add(&self, rhs: &Self) -> Self {
        let (d0, carry) = adc(self.0[0], rhs.0[0], 0);
        let (d1, carry) = adc(self.0[1], rhs.0[1], carry);
        let (d2, carry) = adc(self.0[2], rhs.0[2], carry);
        let (d3, _) = adc(self.0[3], rhs.0[3], carry);

        // Attempt to subtract the modulus, to ensure the value
        // is smaller than the modulus.
        (&Fp([d0, d1, d2, d3])).sub(&Fp(MODULUS_LIMBS))
    }

    /// Adds `rhs` to `self`, returning the result.
    #[cfg(feature = "cm-field")]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub const fn add(&self, rhs: &Self) -> Self {
        Fp(cm::pack(cm::add::<CmP>(cm::unpack(&self.0), cm::unpack(&rhs.0))))
    }

    /// Negates `self`.
    #[cfg(not(feature = "cm-field"))]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub const fn neg(&self) -> Self {
        // Subtract `self` from `MODULUS` to negate. Ignore the final
        // borrow because it cannot underflow; self is guaranteed to
        // be in the field.
        let (d0, borrow) = sbb(MODULUS_LIMBS[0], self.0[0], 0);
        let (d1, borrow) = sbb(MODULUS_LIMBS[1], self.0[1], borrow);
        let (d2, borrow) = sbb(MODULUS_LIMBS[2], self.0[2], borrow);
        let (d3, _) = sbb(MODULUS_LIMBS[3], self.0[3], borrow);

        // `tmp` could be `MODULUS` if `self` was zero. Create a mask that is
        // zero if `self` was zero, and `u64::max_value()` if self was nonzero.
        let mask = (((self.0[0] | self.0[1] | self.0[2] | self.0[3]) == 0) as u64).wrapping_sub(1);

        Fp([d0 & mask, d1 & mask, d2 & mask, d3 & mask])
    }

    /// Negates `self`.
    #[cfg(feature = "cm-field")]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub const fn neg(&self) -> Self {
        Fp(cm::pack(cm::neg(cm::unpack(&self.0))))
    }

    /// Multiplies `rhs` by `self`, returning the unreduced 512-bit product.
    #[cfg(not(feature = "cm-field"))]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub(crate) const fn mul_unreduced(&self, rhs: &Self) -> [u64; 8] {
        // Schoolbook multiplication

        let (r0, carry) = mac(0, self.0[0], rhs.0[0], 0);
        let (r1, carry) = mac(0, self.0[0], rhs.0[1], carry);
        let (r2, carry) = mac(0, self.0[0], rhs.0[2], carry);
        let (r3, r4) = mac(0, self.0[0], rhs.0[3], carry);

        let (r1, carry) = mac(r1, self.0[1], rhs.0[0], 0);
        let (r2, carry) = mac(r2, self.0[1], rhs.0[1], carry);
        let (r3, carry) = mac(r3, self.0[1], rhs.0[2], carry);
        let (r4, r5) = mac(r4, self.0[1], rhs.0[3], carry);

        let (r2, carry) = mac(r2, self.0[2], rhs.0[0], 0);
        let (r3, carry) = mac(r3, self.0[2], rhs.0[1], carry);
        let (r4, carry) = mac(r4, self.0[2], rhs.0[2], carry);
        let (r5, r6) = mac(r5, self.0[2], rhs.0[3], carry);

        let (r3, carry) = mac(r3, self.0[3], rhs.0[0], 0);
        let (r4, carry) = mac(r4, self.0[3], rhs.0[1], carry);
        let (r5, carry) = mac(r5, self.0[3], rhs.0[2], carry);
        let (r6, r7) = mac(r6, self.0[3], rhs.0[3], carry);

        [r0, r1, r2, r3, r4, r5, r6, r7]
    }

    /// Squares this element, returning the unreduced 512-bit product.
    #[cfg(not(feature = "cm-field"))]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub(crate) const fn square_unreduced(&self) -> [u64; 8] {
        let (r1, carry) = mac(0, self.0[0], self.0[1], 0);
        let (r2, carry) = mac(0, self.0[0], self.0[2], carry);
        let (r3, r4) = mac(0, self.0[0], self.0[3], carry);

        let (r3, carry) = mac(r3, self.0[1], self.0[2], 0);
        let (r4, r5) = mac(r4, self.0[1], self.0[3], carry);

        let (r5, r6) = mac(r5, self.0[2], self.0[3], 0);

        let r7 = r6 >> 63;
        let r6 = (r6 << 1) | (r5 >> 63);
        let r5 = (r5 << 1) | (r4 >> 63);
        let r4 = (r4 << 1) | (r3 >> 63);
        let r3 = (r3 << 1) | (r2 >> 63);
        let r2 = (r2 << 1) | (r1 >> 63);
        let r1 = r1 << 1;

        let (r0, carry) = mac(0, self.0[0], self.0[0], 0);
        let (r1, carry) = adc(0, r1, carry);
        let (r2, carry) = mac(r2, self.0[1], self.0[1], carry);
        let (r3, carry) = adc(0, r3, carry);
        let (r4, carry) = mac(r4, self.0[2], self.0[2], carry);
        let (r5, carry) = adc(0, r5, carry);
        let (r6, carry) = mac(r6, self.0[3], self.0[3], carry);
        let (r7, _) = adc(0, r7, carry);

        [r0, r1, r2, r3, r4, r5, r6, r7]
    }
}

#[cfg(all(feature = "deferred", not(feature = "cm-field")))]
impl DeferredField for Fp {
    type Accumulator = Product<Fp>;

    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    fn mul_accumulate(acc: &mut Self::Accumulator, a: &Fp, b: &Fp) {
        acc.accumulate(a.mul_unreduced(b));
    }

    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    fn square_accumulate(acc: &mut Self::Accumulator, a: &Fp) {
        acc.accumulate(a.square_unreduced());
    }

    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    fn reduce(acc: Self::Accumulator) -> Fp {
        /// 2^448 mod p (little-endian limbs).
        const B448: [u64; 4] = [
            0x9b9858f294cf91ba,
            0x8635bd2c4252b065,
            0x496d41af7b9cb714,
            0x1b4b3c4bfffffffc,
        ];
        let limbs = acc.partial_reduce(&B448, &MONT_R2_LIMBS);
        Fp::montgomery_reduce(
            limbs[0], limbs[1], limbs[2], limbs[3], limbs[4], limbs[5], limbs[6], limbs[7],
        )
    }
}

// Under the CM representation the accumulator holds 320-bit sums of the
// raw ring products; one generalized reduction finalizes the whole inner
// product (see `cm::reduce_wide`).
#[cfg(all(feature = "deferred", feature = "cm-field"))]
impl DeferredField for Fp {
    type Accumulator = CmProduct<Fp>;

    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    fn mul_accumulate(acc: &mut Self::Accumulator, a: &Fp, b: &Fp) {
        cm::mul_accumulate(
            &mut acc.v0,
            &mut acc.v1,
            cm::unpack(&a.0),
            cm::unpack(&b.0),
        );
    }

    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    fn square_accumulate(acc: &mut Self::Accumulator, a: &Fp) {
        cm::square_accumulate(&mut acc.v0, &mut acc.v1, cm::unpack(&a.0));
    }

    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    fn reduce(acc: Self::Accumulator) -> Fp {
        Fp(cm::pack(cm::reduce_wide::<CmP>(acc.v0, acc.v1)))
    }
}

impl From<Fp> for [u8; 32] {
    fn from(value: Fp) -> [u8; 32] {
        value.to_repr()
    }
}

impl<'a> From<&'a Fp> for [u8; 32] {
    fn from(value: &'a Fp) -> [u8; 32] {
        value.to_repr()
    }
}

impl ff::Field for Fp {
    const ZERO: Self = Self::zero();
    const ONE: Self = Self::one();

    fn try_random<R: TryRng + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        Ok(Self::from_u512([
            rng.try_next_u64()?,
            rng.try_next_u64()?,
            rng.try_next_u64()?,
            rng.try_next_u64()?,
            rng.try_next_u64()?,
            rng.try_next_u64()?,
            rng.try_next_u64()?,
            rng.try_next_u64()?,
        ]))
    }

    fn double(&self) -> Self {
        self.double()
    }

    #[inline(always)]
    fn square(&self) -> Self {
        self.square_runtime()
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        #[cfg(feature = "sqrt-table")]
        {
            FP_TABLES.sqrt_ratio(num, div)
        }

        #[cfg(not(feature = "sqrt-table"))]
        ff::helpers::sqrt_ratio_generic(num, div)
    }

    #[cfg(feature = "sqrt-table")]
    fn sqrt_alt(&self) -> (Choice, Self) {
        FP_TABLES.sqrt_alt(self)
    }

    /// Computes the square root of this element, if it exists.
    fn sqrt(&self) -> CtOption<Self> {
        #[cfg(feature = "sqrt-table")]
        {
            let (is_square, res) = FP_TABLES.sqrt_alt(self);
            CtOption::new(res, is_square)
        }

        #[cfg(not(feature = "sqrt-table"))]
        ff::helpers::sqrt_tonelli_shanks(self, &T_MINUS1_OVER2)
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    ///
    /// This runs a **variable-time** 62-divstep safegcd inversion (the
    /// crate-internal `modinv62` module): its timing depends on the value
    /// being inverted, which every inversion call site in this fork
    /// tolerates. The result and the `is_some` flag are identical to the
    /// previous (data-oblivious) Fermat implementation, which remains
    /// expressible as `self.pow_vartime(&[p - 2])`.
    fn invert(&self) -> CtOption<Self> {
        #[cfg(not(feature = "cm-field"))]
        {
            match super::modinv62::invert::<super::modinv62::FpParams>(&self.0) {
                Some(limbs) => CtOption::new(Fp(limbs), Choice::from(1)),
                None => CtOption::new(Self::zero(), Choice::from(0)),
            }
        }

        // CM pairs decode to canonical limbs, invert through the same
        // variable-time divstep kernel in canonical mode (seed 1), and
        // re-encode.
        #[cfg(feature = "cm-field")]
        {
            let canonical = cm::decode::<CmP>(cm::unpack(&self.0));
            match super::modinv62::invert::<super::modinv62::FpCanonicalParams>(&canonical) {
                Some(limbs) => {
                    CtOption::new(Fp(cm::pack(cm::encode::<CmP>(limbs))), Choice::from(1))
                }
                None => CtOption::new(Self::zero(), Choice::from(0)),
            }
        }
    }

    fn pow_vartime<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        // Walk the exponent bits MSB-first, fusing each run of squarings with
        // the multiplication that follows it. This performs exactly the same
        // field operations as the classic square-and-multiply loop, but lets
        // the assembly backend keep the accumulator in registers for the
        // whole run.
        let mut res: Option<Self> = None;
        let mut squares = 0;
        for e in exp.as_ref().iter().rev() {
            for i in (0..64).rev() {
                if res.is_some() {
                    squares += 1;
                }

                if ((*e >> i) & 1) == 1 {
                    res = Some(match res {
                        Some(res) => {
                            let res = res.sqr_n_mul_runtime(squares, self);
                            squares = 0;
                            res
                        }
                        None => *self,
                    });
                }
            }
        }

        let mut res = match res {
            Some(res) => res,
            None => return Self::one(),
        };
        // Flush the squarings for any trailing zero bits.
        for _ in 0..squares {
            res = res.square_runtime();
        }
        res
    }
}

impl ff::PrimeField for Fp {
    type Repr = [u8; 32];

    const MODULUS: &'static str =
        "0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001";
    const TWO_INV: Self = Fp::from_raw([
        0xcc96987680000001,
        0x11234c7e04a67c8d,
        0x0000000000000000,
        0x2000000000000000,
    ]);
    const NUM_BITS: u32 = 255;
    const CAPACITY: u32 = 254;
    const MULTIPLICATIVE_GENERATOR: Self = GENERATOR;
    const S: u32 = S;
    const ROOT_OF_UNITY: Self = ROOT_OF_UNITY;
    const ROOT_OF_UNITY_INV: Self = Fp::from_raw([
        0xf0b87c7db2ce91f6,
        0x84a0a1d8859f066f,
        0xb4ed8e647196dad1,
        0x2cd5282c53116b5c,
    ]);
    const DELTA: Self = DELTA;

    fn from_u128(v: u128) -> Self {
        #[cfg(not(feature = "cm-field"))]
        {
            Fp::from_raw([v as u64, (v >> 64) as u64, 0, 0])
        }

        #[cfg(feature = "cm-field")]
        {
            Fp(cm::pack(cm::from_u128::<CmP>(v)))
        }
    }

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = Fp([0, 0, 0, 0]);

        tmp.0[0] = u64::from_le_bytes(repr[0..8].try_into().unwrap());
        tmp.0[1] = u64::from_le_bytes(repr[8..16].try_into().unwrap());
        tmp.0[2] = u64::from_le_bytes(repr[16..24].try_into().unwrap());
        tmp.0[3] = u64::from_le_bytes(repr[24..32].try_into().unwrap());

        // Try to subtract the modulus
        let (_, borrow) = sbb(tmp.0[0], MODULUS_LIMBS[0], 0);
        let (_, borrow) = sbb(tmp.0[1], MODULUS_LIMBS[1], borrow);
        let (_, borrow) = sbb(tmp.0[2], MODULUS_LIMBS[2], borrow);
        let (_, borrow) = sbb(tmp.0[3], MODULUS_LIMBS[3], borrow);

        // If the element is smaller than MODULUS then the
        // subtraction will underflow, producing a borrow value
        // of 0xffff...ffff. Otherwise, it'll be zero.
        let is_some = (borrow as u8) & 1;

        // Convert into the internal representation.
        #[cfg(not(feature = "cm-field"))]
        {
            // Montgomery form: (a.R^0 * R^2) / R = a.R.
            tmp *= &R2;
            CtOption::new(tmp, Choice::from(is_some))
        }

        #[cfg(feature = "cm-field")]
        {
            // The value is only meaningful when `is_some` is set; clear
            // the top bit so even a non-canonical repr stays inside
            // `encode`'s x < 2^255 domain (canonical values never have
            // it set).
            let mut limbs = tmp.0;
            limbs[3] &= (1 << 63) - 1;
            CtOption::new(
                Fp(cm::pack(cm::encode::<CmP>(limbs))),
                Choice::from(is_some),
            )
        }
    }

    fn to_repr(&self) -> Self::Repr {
        // Turn the internal representation into canonical form.
        #[cfg(all(
            feature = "aarch64-asm",
            not(feature = "cm-field"),
            target_arch = "aarch64",
            target_vendor = "apple"
        ))]
        let tmp = Fp(super::aarch64_asm::from_mont(&self.0, &MODULUS_LIMBS, INV));

        #[cfg(all(
            not(feature = "cm-field"),
            not(all(
                feature = "aarch64-asm",
                target_arch = "aarch64",
                target_vendor = "apple"
            ))
        ))]
        let tmp = Fp::montgomery_reduce(self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0);

        #[cfg(feature = "cm-field")]
        let tmp = Fp(cm::decode::<CmP>(cm::unpack(&self.0)));

        let mut res = [0; 32];
        res[0..8].copy_from_slice(&tmp.0[0].to_le_bytes());
        res[8..16].copy_from_slice(&tmp.0[1].to_le_bytes());
        res[16..24].copy_from_slice(&tmp.0[2].to_le_bytes());
        res[24..32].copy_from_slice(&tmp.0[3].to_le_bytes());

        res
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr()[0] & 1)
    }
}

#[cfg(all(feature = "bits", not(target_pointer_width = "64")))]
type ReprBits = [u32; 8];

#[cfg(all(feature = "bits", target_pointer_width = "64"))]
type ReprBits = [u64; 4];

#[cfg(feature = "bits")]
#[cfg_attr(docsrs, doc(cfg(feature = "bits")))]
impl PrimeFieldBits for Fp {
    type ReprBits = ReprBits;

    fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        let bytes = self.to_repr();

        #[cfg(not(target_pointer_width = "64"))]
        let limbs = [
            u32::from_le_bytes(bytes[0..4].try_into().unwrap()),
            u32::from_le_bytes(bytes[4..8].try_into().unwrap()),
            u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
            u32::from_le_bytes(bytes[12..16].try_into().unwrap()),
            u32::from_le_bytes(bytes[16..20].try_into().unwrap()),
            u32::from_le_bytes(bytes[20..24].try_into().unwrap()),
            u32::from_le_bytes(bytes[24..28].try_into().unwrap()),
            u32::from_le_bytes(bytes[28..32].try_into().unwrap()),
        ];

        #[cfg(target_pointer_width = "64")]
        let limbs = [
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
        ];

        FieldBits::new(limbs)
    }

    fn char_le_bits() -> FieldBits<Self::ReprBits> {
        #[cfg(not(target_pointer_width = "64"))]
        {
            FieldBits::new(MODULUS_LIMBS_32)
        }

        #[cfg(target_pointer_width = "64")]
        FieldBits::new(MODULUS_LIMBS)
    }
}

#[cfg(feature = "sqrt-table")]
lazy_static! {
    // The perfect hash parameters are found by `squareroottab.sage` in zcash/pasta.
    #[cfg_attr(docsrs, doc(cfg(feature = "sqrt-table")))]
    static ref FP_TABLES: SqrtTables<Fp> = SqrtTables::new(0x11BE, 1098);
}

impl SqrtTableHelpers for Fp {
    fn pow_by_t_minus1_over2(&self) -> Self {
        let r10 = self.square_runtime();
        let r11 = r10 * self;
        let r110 = r11.square_runtime();
        let r111 = r110 * self;
        let r1001 = r111 * r10;
        let r1101 = r111 * r110;
        let ra = self.sqr_n_mul_runtime(129, self);
        let rb = ra.sqr_n_mul_runtime(7, &r1001);
        let rc = rb.sqr_n_mul_runtime(7, &r1101);
        let rd = rc.sqr_n_mul_runtime(4, &r11);
        let re = rd.sqr_n_mul_runtime(6, &r111);
        let rf = re.sqr_n_mul_runtime(3, &r111);
        let rg = rf.sqr_n_mul_runtime(10, &r1001);
        let rh = rg.sqr_n_mul_runtime(5, &r1001);
        let ri = rh.sqr_n_mul_runtime(4, &r1001);
        let rj = ri.sqr_n_mul_runtime(3, &r111);
        let rk = rj.sqr_n_mul_runtime(4, &r1001);
        let rl = rk.sqr_n_mul_runtime(5, &r11);
        let rm = rl.sqr_n_mul_runtime(4, &r111);
        let rn = rm.sqr_n_mul_runtime(4, &r11);
        let ro = rn.sqr_n_mul_runtime(6, &r1001);
        let rp = ro.sqr_n_mul_runtime(5, &r1101);
        let rq = rp.sqr_n_mul_runtime(4, &r11);
        let rr = rq.sqr_n_mul_runtime(7, &r111);
        let rs = rr.sqr_n_mul_runtime(3, &r11);
        rs.square_runtime() // rt
    }

    fn get_lower_32(&self) -> u32 {
        // TODO: don't convert to canonical form, hash the internal
        // representation. (Requires rebuilding the perfect hash table —
        // and, under cm-field, a canonical representative first.)
        #[cfg(not(feature = "cm-field"))]
        let low = Fp::montgomery_reduce(self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0).0[0];

        #[cfg(feature = "cm-field")]
        let low = cm::decode::<CmP>(cm::unpack(&self.0))[0];

        low as u32
    }
}

impl WithSmallOrderMulGroup<3> for Fp {
    const ZETA: Self = Fp::from_raw([
        0x1dad5ebdfdfe4ab9,
        0x1d1f8bd237ad3149,
        0x2caad5dc57aab1b0,
        0x12ccca834acdba71,
    ]);
}

impl FromUniformBytes<64> for Fp {
    /// Converts a 512-bit little endian integer into
    /// a `Fp` by reducing by the modulus.
    fn from_uniform_bytes(bytes: &[u8; 64]) -> Fp {
        Fp::from_u512([
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
            u64::from_le_bytes(bytes[32..40].try_into().unwrap()),
            u64::from_le_bytes(bytes[40..48].try_into().unwrap()),
            u64::from_le_bytes(bytes[48..56].try_into().unwrap()),
            u64::from_le_bytes(bytes[56..64].try_into().unwrap()),
        ])
    }
}

#[cfg(feature = "gpu")]
impl ec_gpu::GpuName for Fp {
    fn name() -> alloc::string::String {
        ec_gpu::name!()
    }
}

#[cfg(feature = "gpu")]
impl ec_gpu::GpuField for Fp {
    fn one() -> alloc::vec::Vec<u32> {
        crate::fields::u64_to_u32(&MONT_R_LIMBS[..])
    }

    fn r2() -> alloc::vec::Vec<u32> {
        crate::fields::u64_to_u32(&MONT_R2_LIMBS[..])
    }

    fn modulus() -> alloc::vec::Vec<u32> {
        crate::fields::u64_to_u32(&MODULUS_LIMBS[..])
    }
}

/// The GPU contract publishes the MONTGOMERY constants (R, R^2, and the
/// modulus) regardless of the CPU-side representation; pin the exact words
/// so a representation change can never silently leak into GPU kernels.
#[cfg(all(test, feature = "gpu"))]
#[test]
fn gpu_constants_are_montgomery() {
    assert_eq!(
        <Fp as ec_gpu::GpuField>::one(),
        crate::fields::u64_to_u32(&[
            0x34786d38fffffffd,
            0x992c350be41914ad,
            0xffffffffffffffff,
            0x3fffffffffffffff,
        ])
    );
    assert_eq!(
        <Fp as ec_gpu::GpuField>::r2(),
        crate::fields::u64_to_u32(&[
            0x8c78ecb30000000f,
            0xd7d30dbd8b0de0e7,
            0x7797a99bc3c95d18,
            0x096d41af7b9cb714,
        ])
    );
    assert_eq!(
        <Fp as ec_gpu::GpuField>::modulus(),
        crate::fields::u64_to_u32(&[
            0x992d30ed00000001,
            0x224698fc094cf91b,
            0x0000000000000000,
            0x4000000000000000,
        ])
    );
}

#[cfg(all(
    test,
    feature = "aarch64-asm",
    not(feature = "cm-field"),
    target_arch = "aarch64",
    target_vendor = "apple"
))]
fn aarch64_asm_portable_repr(value: Fp) -> [u8; 32] {
    let value = Fp::montgomery_reduce(value.0[0], value.0[1], value.0[2], value.0[3], 0, 0, 0, 0);
    let mut repr = [0; 32];
    for (bytes, limb) in repr.chunks_exact_mut(8).zip(value.0) {
        bytes.copy_from_slice(&limb.to_le_bytes());
    }
    repr
}

#[cfg(all(
    test,
    feature = "aarch64-asm",
    not(feature = "cm-field"),
    target_arch = "aarch64",
    target_vendor = "apple"
))]
fn aarch64_asm_check_repr(value: Fp) {
    let portable = aarch64_asm_portable_repr(value);
    assert_eq!(value.to_repr(), portable);
    assert_eq!(Fp::from_repr(portable).unwrap(), value);
    assert_eq!(value.is_odd().unwrap_u8(), portable[0] & 1);
}

#[cfg(all(
    test,
    feature = "aarch64-asm",
    not(feature = "cm-field"),
    target_arch = "aarch64",
    target_vendor = "apple"
))]
fn aarch64_asm_portable_cmp(lhs: Fp, rhs: Fp) -> core::cmp::Ordering {
    aarch64_asm_portable_repr(lhs)
        .iter()
        .zip(aarch64_asm_portable_repr(rhs).iter())
        .rev()
        .find_map(|(lhs, rhs)| match lhs.cmp(rhs) {
            core::cmp::Ordering::Equal => None,
            ordering => Some(ordering),
        })
        .unwrap_or(core::cmp::Ordering::Equal)
}

#[cfg(all(
    test,
    feature = "aarch64-asm",
    not(feature = "cm-field"),
    target_arch = "aarch64",
    target_vendor = "apple"
))]
#[test]
fn aarch64_asm_matches_portable_arithmetic() {
    use rand::{Rng, SeedableRng};

    let max_montgomery_residue = Fp([MODULUS_LIMBS[0] - 1, MODULUS_LIMBS[1], MODULUS_LIMBS[2], MODULUS_LIMBS[3]]);
    let boundaries = [
        Fp::zero(),
        Fp::one(),
        -Fp::one(),
        Fp::from_raw([1, 0, 0, 0]),
        max_montgomery_residue,
        Fp::from_raw([u64::MAX; 4]),
    ];

    fn portable_sqr_n_mul(value: Fp, n: u32, by: Fp) -> Fp {
        (0..n).fold(value, |acc, _| Fp::square(&acc)).mul(&by)
    }

    for lhs in boundaries {
        aarch64_asm_check_repr(lhs);
        assert_eq!(<Fp as Field>::square(&lhs), Fp::square(&lhs));
        for rhs in boundaries {
            assert_eq!(lhs.cmp(&rhs), aarch64_asm_portable_cmp(lhs, rhs));
            assert_eq!(&lhs * &rhs, Fp::mul(&lhs, &rhs));
            for n in [1, 2, 7] {
                assert_eq!(
                    lhs.sqr_n_mul_runtime(n, &rhs),
                    portable_sqr_n_mul(lhs, n, rhs)
                );
            }
        }
    }

    let mut rng = rand_xorshift::XorShiftRng::from_seed([0x5a; 16]);
    for _ in 0..1024 {
        let lhs = Fp::from_raw([
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ]);
        let rhs = Fp::from_raw([
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ]);

        aarch64_asm_check_repr(lhs);
        assert_eq!(lhs.cmp(&rhs), aarch64_asm_portable_cmp(lhs, rhs));
        assert_eq!(&lhs * &rhs, Fp::mul(&lhs, &rhs));
        assert_eq!(<Fp as Field>::square(&lhs), Fp::square(&lhs));
        for n in [1, 129] {
            assert_eq!(
                lhs.sqr_n_mul_runtime(n, &rhs),
                portable_sqr_n_mul(lhs, n, rhs)
            );
        }
    }
}

#[cfg(not(feature = "cm-field"))]
#[test]
fn test_inv() {
    // Compute -(r^{-1} mod 2^64) mod 2^64 by exponentiating
    // by totient(2**64) - 1

    let mut inv = 1u64;
    for _ in 0..63 {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(MODULUS_LIMBS[0]);
    }
    inv = inv.wrapping_neg();

    assert_eq!(inv, INV);
}

#[test]
fn test_sqrt() {
    // NB: TWO_INV is standing in as a "random" field element
    let v = (Fp::TWO_INV).square().sqrt().unwrap();
    assert!(v == Fp::TWO_INV || (-v) == Fp::TWO_INV);
}

#[test]
fn test_sqrt_32bit_overflow() {
    assert!((Fp::from(5)).sqrt().is_none().unwrap_u8() == 1);
}

#[test]
fn test_pow_by_t_minus1_over2() {
    // NB: TWO_INV is standing in as a "random" field element
    let v = (Fp::TWO_INV).pow_by_t_minus1_over2();
    assert!(v == ff::Field::pow_vartime(&Fp::TWO_INV, &T_MINUS1_OVER2));
}

#[test]
fn test_pow_vartime() {
    use rand::{Rng, SeedableRng};

    // The classic square-and-multiply loop, as a reference for the fused
    // implementation.
    fn pow_vartime_reference(base: &Fp, exp: &[u64]) -> Fp {
        let mut res = Fp::one();
        let mut found_one = false;
        for e in exp.iter().rev() {
            for i in (0..64).rev() {
                if found_one {
                    res = Fp::square(&res);
                }

                if ((*e >> i) & 1) == 1 {
                    found_one = true;
                    res = Fp::mul(&res, base);
                }
            }
        }
        res
    }

    let mut rng = rand_xorshift::XorShiftRng::from_seed([0xa5; 16]);

    let mut exponents = vec![
        [0, 0, 0, 0],
        [1, 0, 0, 0],
        [2, 0, 0, 0],
        // A single high bit exercises the trailing-squarings flush.
        [0, 0, 0, 1 << 63],
        [1 << 63, 0, 0, 0],
        [u64::MAX; 4],
        // The p - 2 exponent used by `invert`.
        [
            0x992d30ecffffffff,
            0x224698fc094cf91b,
            0x0,
            0x4000000000000000,
        ],
    ];
    for _ in 0..10 {
        exponents.push([
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ]);
    }

    for base in [
        Fp::zero(),
        Fp::one(),
        -Fp::one(),
        Fp::random(&mut rng),
        Fp::random(&mut rng),
    ] {
        for exp in &exponents {
            assert_eq!(base.pow_vartime(exp), pow_vartime_reference(&base, exp));
        }
        // Short and empty exponent slices behave like zero-padded ones.
        assert_eq!(base.pow_vartime([7]), pow_vartime_reference(&base, &[7]));
        assert_eq!(
            base.pow_vartime([0u64; 0]),
            pow_vartime_reference(&base, &[])
        );
    }
}

#[test]
fn test_sqrt_ratio_and_alt() {
    // (true, sqrt(num/div)), if num and div are nonzero and num/div is a square in the field
    let num = (Fp::TWO_INV).square();
    let div = Fp::from(25);
    let div_inverse = div.invert().unwrap();
    let expected = Fp::TWO_INV * Fp::from(5).invert().unwrap();
    let (is_square, v) = Fp::sqrt_ratio(&num, &div);
    assert!(bool::from(is_square));
    assert!(v == expected || (-v) == expected);

    let (is_square_alt, v_alt) = Fp::sqrt_alt(&(num * div_inverse));
    assert!(bool::from(is_square_alt));
    assert!(v_alt == v);

    // (false, sqrt(ROOT_OF_UNITY * num/div)), if num and div are nonzero and num/div is a nonsquare in the field
    let num = num * Fp::ROOT_OF_UNITY;
    let expected = Fp::TWO_INV * Fp::ROOT_OF_UNITY * Fp::from(5).invert().unwrap();
    let (is_square, v) = Fp::sqrt_ratio(&num, &div);
    assert!(!bool::from(is_square));
    assert!(v == expected || (-v) == expected);

    let (is_square_alt, v_alt) = Fp::sqrt_alt(&(num * div_inverse));
    assert!(!bool::from(is_square_alt));
    assert!(v_alt == v);

    // (true, 0), if num is zero
    let num = Fp::zero();
    let expected = Fp::zero();
    let (is_square, v) = Fp::sqrt_ratio(&num, &div);
    assert!(bool::from(is_square));
    assert!(v == expected);

    let (is_square_alt, v_alt) = Fp::sqrt_alt(&(num * div_inverse));
    assert!(bool::from(is_square_alt));
    assert!(v_alt == v);

    // (false, 0), if num is nonzero and div is zero
    let num = (Fp::TWO_INV).square();
    let div = Fp::zero();
    let expected = Fp::zero();
    let (is_square, v) = Fp::sqrt_ratio(&num, &div);
    assert!(!bool::from(is_square));
    assert!(v == expected);
}

#[test]
fn test_zeta() {
    assert_eq!(
        format!("{:?}", Fp::ZETA),
        "0x12ccca834acdba712caad5dc57aab1b01d1f8bd237ad31491dad5ebdfdfe4ab9"
    );

    let a = Fp::ZETA;
    assert!(a != Fp::one());
    let b = a * a;
    assert!(b != Fp::one());
    let c = b * a;
    assert!(c == Fp::one());
}

#[test]
fn test_root_of_unity() {
    assert_eq!(
        Fp::ROOT_OF_UNITY.pow_vartime(&[1 << Fp::S, 0, 0, 0]),
        Fp::one()
    );
}

#[test]
fn test_inv_root_of_unity() {
    assert_eq!(Fp::ROOT_OF_UNITY_INV, Fp::ROOT_OF_UNITY.invert().unwrap());
}

#[test]
fn test_inv_2() {
    assert_eq!(Fp::TWO_INV, Fp::from(2).invert().unwrap());
}

#[test]
fn test_delta() {
    assert_eq!(Fp::DELTA, GENERATOR.pow(&[1u64 << Fp::S, 0, 0, 0]));
    assert_eq!(
        Fp::DELTA,
        Fp::MULTIPLICATIVE_GENERATOR.pow(&[1u64 << Fp::S, 0, 0, 0])
    );
}

#[cfg(not(target_pointer_width = "64"))]
#[test]
fn consistent_modulus_limbs() {
    for (a, &b) in MODULUS
        .0
        .iter()
        .flat_map(|&limb| {
            Some(limb as u32)
                .into_iter()
                .chain(Some((limb >> 32) as u32))
        })
        .zip(MODULUS_LIMBS_32.iter())
    {
        assert_eq!(a, b);
    }
}

// Montgomery-coupled (constructs raw residues and uses R2/R3); the CM
// path is covered by the kernel's from_u512 tests and repr_roundtrip.
#[cfg(not(feature = "cm-field"))]
#[test]
fn test_from_u512() {
    assert_eq!(
        Fp::from_raw([
            0x3daec14d565241d9,
            0x0b7af45b6073944b,
            0xea5b8bd611a5bd4c,
            0x150160330625db3d
        ]),
        Fp::from_u512([
            0xee155641297678a1,
            0xd83e156bdbfdbe65,
            0xd9ccd834c68ba0b5,
            0xf508ede312272758,
            0x038df7cbf8228e89,
            0x3505a1e4a3c74b41,
            0xbfa46f775eb82db3,
            0x26ebe27e262f471d
        ])
    );
}

#[cfg(all(
    test,
    feature = "aarch64-asm",
    not(feature = "cm-field"),
    target_arch = "aarch64",
    target_vendor = "apple"
))]
#[test]
fn aarch64_asm_mul_unreduced_lhs_matches_portable() {
    use rand::{Rng, SeedableRng};

    // `from_u512` feeds raw (unreduced) 256-bit digits as the lhs of the
    // inline `mul`, with `R2`/`R3` as the rhs. The five-limb accumulator
    // tolerates an unreduced lhs only while every rhs limb is at most
    // `2^64 - 4` (see the contract in `aarch64_asm.rs`); assert the
    // constants keep that invariant, then pin the behaviour against the
    // portable implementation on the most adversarial inputs known.
    for by in [R2, R3] {
        for limb in by.0 {
            assert!(limb <= u64::MAX - 3);
        }
    }

    // lhs values with the low limbs solved so the first two Montgomery
    // quotients hit (or approach) their maximum `2^64 - 1` while the top
    // limbs are all-ones: jointly the nearest known approach to the
    // carry-chain wrap described in `aarch64_asm.rs`.
    let forced_q_r2 = Fp([0x3cc9961eeeeeeeef, 0x907f42c685cc8a31, u64::MAX, u64::MAX]);
    let forced_q_r3 = Fp([0x032c286da5f9b149, 0x3f747fab2d936552, u64::MAX, u64::MAX]);

    let check = |lhs: Fp, by: Fp| {
        // Inherent `Fp::mul` is the portable implementation; its classical
        // 8-limb reduction is valid for any lhs when `by` is canonical.
        assert_eq!(lhs.mul_runtime(&by), Fp::mul(&lhs, &by), "lhs {:x?}", lhs.0);
    };

    check(Fp([u64::MAX; 4]), R2);
    check(Fp([u64::MAX; 4]), R3);
    check(forced_q_r2, R2);
    check(forced_q_r3, R3);

    let mut rng = rand_xorshift::XorShiftRng::from_seed([0x9d; 16]);
    for i in 0..20_000u32 {
        let mut l = [0u64; 4];
        for w in l.iter_mut() {
            *w = rng.next_u64();
        }
        if i % 2 == 0 {
            l[3] = u64::MAX;
            l[2] = u64::MAX;
        }
        check(Fp(l), R2);
        check(Fp(l), R3);
    }

    // End-to-end `from_u512` against a portable recomposition.
    let portable_from_u512 = |l: [u64; 8]| {
        let d0 = Fp([l[0], l[1], l[2], l[3]]);
        let d1 = Fp([l[4], l[5], l[6], l[7]]);
        Fp::mul(&d0, &R2).add(&Fp::mul(&d1, &R3))
    };
    assert_eq!(
        Fp::from_u512([u64::MAX; 8]),
        portable_from_u512([u64::MAX; 8])
    );
    for _ in 0..10_000u32 {
        let mut l = [0u64; 8];
        for w in l.iter_mut() {
            *w = rng.next_u64();
        }
        l[3] |= 0xc000000000000000;
        l[7] |= 0xc000000000000000;
        assert_eq!(Fp::from_u512(l), portable_from_u512(l), "limbs {:x?}", l);
    }
}

/// Byte-identity tripwire across internal representations: fixed raw inputs
/// must serialize to exactly the same canonical bytes in every mode.
#[test]
fn repr_pinned_vectors() {
    let cases: [([u64; 4], [u8; 32]); 8] = [
        (
            [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
            [
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            ],
        ),
        (
            [0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
            [
                0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            ],
        ),
        (
            [0x0000000000000005, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
            [
                0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            ],
        ),
        (
            [0x992d30ed00000000, 0x224698fc094cf91b, 0x0000000000000000, 0x4000000000000000],
            [
                0x00, 0x00, 0x00, 0x00, 0xed, 0x30, 0x2d, 0x99,
                0x1b, 0xf9, 0x4c, 0x09, 0xfc, 0x98, 0x46, 0x22,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40,
            ],
        ),
        (
            [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
            [
                0xfc, 0xff, 0xff, 0xff, 0x38, 0x6d, 0x78, 0x34,
                0xad, 0x14, 0x19, 0xe4, 0x0b, 0x35, 0x2c, 0x99,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f,
            ],
        ),
        (
            [0x123456789abcdef0, 0xfedcba9876543210, 0x0f1e2d3c4b5a6978, 0x0123456789abcdef],
            [
                0xf0, 0xde, 0xbc, 0x9a, 0x78, 0x56, 0x34, 0x12,
                0x10, 0x32, 0x54, 0x76, 0x98, 0xba, 0xdc, 0xfe,
                0x78, 0x69, 0x5a, 0x4b, 0x3c, 0x2d, 0x1e, 0x0f,
                0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01,
            ],
        ),
        (
            [0x34786d38fffffffd, 0x992c350be41914ad, 0xffffffffffffffff, 0x3fffffffffffffff],
            [
                0xfd, 0xff, 0xff, 0xff, 0x38, 0x6d, 0x78, 0x34,
                0xad, 0x14, 0x19, 0xe4, 0x0b, 0x35, 0x2c, 0x99,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f,
            ],
        ),
        (
            [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x4000000000000000],
            [
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40,
            ],
        ),
    ];
    for (raw, expected) in cases {
        assert_eq!(Fp::from_raw(raw).to_repr(), expected);
    }
}

/// `from_repr` inverts `to_repr` on canonical values, `is_odd` matches the
/// canonical low bit, and non-canonical reprs are rejected — in every mode.
#[test]
fn repr_roundtrip() {
    use rand::{Rng, SeedableRng};
    let mut rng = rand_xorshift::XorShiftRng::from_seed([0x21; 16]);
    for x in [Fp::zero(), Fp::one(), -Fp::one()] {
        assert_eq!(Fp::from_repr(x.to_repr()).unwrap(), x);
    }
    for _ in 0..1000 {
        let x = Fp::from_raw([
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ]);
        assert_eq!(Fp::from_repr(x.to_repr()).unwrap(), x);
        assert_eq!(x.is_odd().unwrap_u8(), x.to_repr()[0] & 1);
    }
    // Non-canonical reprs are rejected.
    let mut bytes = (-Fp::one()).to_repr();
    bytes[0] = bytes[0].wrapping_add(1); // = the modulus itself
    assert!(bool::from(Fp::from_repr(bytes).is_none()));
    assert!(bool::from(Fp::from_repr([0xff; 32]).is_none()));
}
