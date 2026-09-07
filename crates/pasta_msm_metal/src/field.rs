//! Portable 32-bit-limb Montgomery arithmetic for the Pasta base fields.
//!
//! This is the executable specification of the field arithmetic in the
//! Metal kernels (`shaders/pasta_msm.metal`): every function here has a
//! line-for-line twin in the shader, using the same limb layout, the same
//! CIOS schedule, and the same conditional reductions, so the reference
//! backend and the GPU compute bit-identical limbs. Change them together.
//!
//! Elements are eight little-endian `u32` limbs in Montgomery form with
//! $R = 2^{256}$ — exactly the representation `pasta_curves` uses
//! internally (four `u64`s), reinterpreted, so coordinates cross the host
//! boundary without any conversion.
//!
//! Both Pasta primes are congruent to 1 modulo $2^{32}$, which makes the
//! per-limb Montgomery factor $-p^{-1} \bmod 2^{32}$ equal to $2^{32} - 1$
//! for both fields ([`INV32`]); the tests pin that.

/// A field element: eight little-endian 32-bit limbs.
pub type Limbs = [u32; 8];

/// $-p^{-1} \bmod 2^{32}$, shared by both Pasta primes (their low limb is 1).
pub const INV32: u32 = 0xffff_ffff;

/// The constants of one Pasta base field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Field {
    /// The prime modulus.
    pub modulus: Limbs,
    /// $R^2 \bmod p$, the Montgomery conversion factor.
    pub r2: Limbs,
    /// $R \bmod p$: the Montgomery form of 1.
    pub one: Limbs,
}

/// Splits four little-endian `u64` limbs into eight `u32` limbs.
pub const fn limbs_from_u64(limbs: [u64; 4]) -> Limbs {
    let mut out = [0u32; 8];
    let mut i = 0;
    while i < 4 {
        // Truncation is the point: the low and high halves of each limb.
        out[2 * i] = limbs[i] as u32;
        out[2 * i + 1] = (limbs[i] >> 32) as u32;
        i += 1;
    }
    out
}

/// Joins eight little-endian `u32` limbs into four `u64` limbs.
pub const fn limbs_to_u64(limbs: &Limbs) -> [u64; 4] {
    let mut out = [0u64; 4];
    let mut i = 0;
    while i < 4 {
        out[i] = limbs[2 * i] as u64 | ((limbs[2 * i + 1] as u64) << 32);
        i += 1;
    }
    out
}

/// Little-endian bytes of a canonical (non-Montgomery) element.
pub fn limbs_to_bytes(limbs: &Limbs) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (chunk, limb) in out.chunks_exact_mut(4).zip(limbs) {
        chunk.copy_from_slice(&limb.to_le_bytes());
    }
    out
}

/// The base field of Pallas, $\mathbb{F}_p$ (`pasta_curves::Fp`).
pub const PALLAS_BASE: Field = Field {
    modulus: limbs_from_u64([
        0x992d30ed00000001,
        0x224698fc094cf91b,
        0x0000000000000000,
        0x4000000000000000,
    ]),
    r2: limbs_from_u64([
        0x8c78ecb30000000f,
        0xd7d30dbd8b0de0e7,
        0x7797a99bc3c95d18,
        0x096d41af7b9cb714,
    ]),
    one: limbs_from_u64([
        0x34786d38fffffffd,
        0x992c350be41914ad,
        0xffffffffffffffff,
        0x3fffffffffffffff,
    ]),
};

/// The base field of Vesta, $\mathbb{F}_q$ (`pasta_curves::Fq`).
pub const VESTA_BASE: Field = Field {
    modulus: limbs_from_u64([
        0x8c46eb2100000001,
        0x224698fc0994a8dd,
        0x0000000000000000,
        0x4000000000000000,
    ]),
    r2: limbs_from_u64([
        0xfc9678ff0000000f,
        0x67bb433d891a16e3,
        0x7fae231004ccf590,
        0x096d41af7ccfdaa9,
    ]),
    one: limbs_from_u64([
        0x5b2b3e9cfffffffd,
        0x992c350be3420567,
        0xffffffffffffffff,
        0x3fffffffffffffff,
    ]),
};

impl Field {
    /// The additive identity (zero in any representation).
    pub const ZERO: Limbs = [0; 8];

    /// Whether `a` is zero.
    #[inline]
    pub fn is_zero(a: &Limbs) -> bool {
        a.iter().all(|&limb| limb == 0)
    }

    /// `a - modulus` as limbs plus the final borrow (`true` when `a < modulus`).
    #[inline]
    fn sub_modulus(&self, a: &Limbs) -> (Limbs, bool) {
        let mut out = [0u32; 8];
        let mut borrow = 0u64;
        for i in 0..8 {
            let r = (a[i] as u64).wrapping_sub(self.modulus[i] as u64 + borrow);
            out[i] = r as u32;
            borrow = (r >> 63) & 1;
        }
        (out, borrow == 1)
    }

    /// Reduces `a + carry * 2^256`, known to be below `2 * modulus`, into `[0, modulus)`.
    #[inline]
    fn reduce_once(&self, a: &Limbs, carry: bool) -> Limbs {
        let (reduced, borrow) = self.sub_modulus(a);
        // Keep the subtraction when it did not borrow, or when the value
        // overflowed 2^256 (the borrow then cancels the carry).
        if carry || !borrow { reduced } else { *a }
    }

    /// `a + b mod p`.
    #[inline]
    pub fn add(&self, a: &Limbs, b: &Limbs) -> Limbs {
        let mut sum = [0u32; 8];
        let mut carry = 0u64;
        for i in 0..8 {
            let r = a[i] as u64 + b[i] as u64 + carry;
            sum[i] = r as u32;
            carry = r >> 32;
        }
        self.reduce_once(&sum, carry == 1)
    }

    /// `2a mod p`.
    #[inline]
    pub fn double(&self, a: &Limbs) -> Limbs {
        self.add(a, a)
    }

    /// `a - b mod p`.
    #[inline]
    pub fn sub(&self, a: &Limbs, b: &Limbs) -> Limbs {
        let mut diff = [0u32; 8];
        let mut borrow = 0u64;
        for i in 0..8 {
            let r = (a[i] as u64).wrapping_sub(b[i] as u64 + borrow);
            diff[i] = r as u32;
            borrow = (r >> 63) & 1;
        }
        if borrow == 1 {
            // Underflowed: add the modulus back (the carry out cancels).
            let mut carry = 0u64;
            for (limb, modulus) in diff.iter_mut().zip(&self.modulus) {
                let r = *limb as u64 + *modulus as u64 + carry;
                *limb = r as u32;
                carry = r >> 32;
            }
        }
        diff
    }

    /// `-a mod p`.
    #[inline]
    pub fn neg(&self, a: &Limbs) -> Limbs {
        if Self::is_zero(a) {
            Self::ZERO
        } else {
            self.sub(&self.modulus, a)
        }
    }

    /// Montgomery product `a * b * R^-1 mod p` (CIOS, eight 32-bit limbs).
    pub fn mul(&self, a: &Limbs, b: &Limbs) -> Limbs {
        let p = &self.modulus;
        let mut t = [0u32; 10];
        for &bi in b {
            // t += a * b[i]
            let bi = bi as u64;
            let mut carry = 0u64;
            for j in 0..8 {
                let r = t[j] as u64 + (a[j] as u64) * bi + carry;
                t[j] = r as u32;
                carry = r >> 32;
            }
            let r = t[8] as u64 + carry;
            t[8] = r as u32;
            t[9] = (r >> 32) as u32;

            // t = (t + m * p) / 2^32 with m = t[0] * INV32 mod 2^32, which
            // clears the low limb.
            let m = t[0].wrapping_mul(INV32) as u64;
            let r = t[0] as u64 + m * (p[0] as u64);
            let mut carry = r >> 32;
            for j in 1..8 {
                let r = t[j] as u64 + m * (p[j] as u64) + carry;
                t[j - 1] = r as u32;
                carry = r >> 32;
            }
            let r = t[8] as u64 + carry;
            t[7] = r as u32;
            t[8] = t[9] + (r >> 32) as u32;
            t[9] = 0;
        }
        let mut out = [0u32; 8];
        out.copy_from_slice(&t[..8]);
        self.reduce_once(&out, t[8] != 0)
    }

    /// `a^2 * R^-1 mod p`.
    #[inline]
    pub fn square(&self, a: &Limbs) -> Limbs {
        self.mul(a, a)
    }

    /// Converts a canonical integer below `p` into Montgomery form.
    pub fn to_montgomery(&self, canonical: &Limbs) -> Limbs {
        self.mul(canonical, &self.r2)
    }

    /// Converts a Montgomery-form element to its canonical integer.
    pub fn from_montgomery(&self, a: &Limbs) -> Limbs {
        let mut one = [0u32; 8];
        one[0] = 1;
        self.mul(a, &one)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::{Field as _, PrimeField};
    use pasta_curves::arithmetic::{fp_montgomery_limbs, fq_montgomery_limbs};
    use pasta_curves::{Fp, Fq};
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    fn fp(limbs: &Limbs) -> Fp {
        Fp::from_repr(limbs_to_bytes(&PALLAS_BASE.from_montgomery(limbs))).unwrap()
    }

    fn fq(limbs: &Limbs) -> Fq {
        Fq::from_repr(limbs_to_bytes(&VESTA_BASE.from_montgomery(limbs))).unwrap()
    }

    #[test]
    fn inv32_matches_both_moduli() {
        for field in [PALLAS_BASE, VESTA_BASE] {
            assert_eq!(field.modulus[0], 1);
            assert_eq!(field.modulus[0].wrapping_mul(INV32), u32::MAX);
        }
    }

    #[test]
    fn constants_match_pasta_curves() {
        assert_eq!(
            PALLAS_BASE.one,
            limbs_from_u64(fp_montgomery_limbs(&Fp::ONE))
        );
        assert_eq!(
            VESTA_BASE.one,
            limbs_from_u64(fq_montgomery_limbs(&Fq::ONE))
        );
        let modulus_minus_one = -Fp::ONE;
        let canonical =
            PALLAS_BASE.from_montgomery(&limbs_from_u64(fp_montgomery_limbs(&modulus_minus_one)));
        let mut expected = PALLAS_BASE.modulus;
        expected[0] -= 1;
        assert_eq!(canonical, expected);
        let canonical = VESTA_BASE.from_montgomery(&limbs_from_u64(fq_montgomery_limbs(&-Fq::ONE)));
        let mut expected = VESTA_BASE.modulus;
        expected[0] -= 1;
        assert_eq!(canonical, expected);
        // R^2: converting the canonical 1 yields the Montgomery one.
        assert_eq!(
            PALLAS_BASE.to_montgomery(&limbs_from_u64([1, 0, 0, 0])),
            PALLAS_BASE.one
        );
        assert_eq!(
            VESTA_BASE.to_montgomery(&limbs_from_u64([1, 0, 0, 0])),
            VESTA_BASE.one
        );
    }

    #[test]
    fn arithmetic_matches_pasta_curves() {
        let mut rng = XorShiftRng::from_seed([7; 16]);
        for _ in 0..500 {
            let a = Fp::random(&mut rng);
            let b = Fp::random(&mut rng);
            let (al, bl) = (
                limbs_from_u64(fp_montgomery_limbs(&a)),
                limbs_from_u64(fp_montgomery_limbs(&b)),
            );
            assert_eq!(fp(&PALLAS_BASE.mul(&al, &bl)), a * b);
            assert_eq!(fp(&PALLAS_BASE.square(&al)), a.square());
            assert_eq!(fp(&PALLAS_BASE.add(&al, &bl)), a + b);
            assert_eq!(fp(&PALLAS_BASE.sub(&al, &bl)), a - b);
            assert_eq!(fp(&PALLAS_BASE.neg(&al)), -a);
            assert_eq!(fp(&PALLAS_BASE.double(&al)), a.double());
            assert_eq!(
                PALLAS_BASE.mul(&al, &bl),
                limbs_from_u64(fp_montgomery_limbs(&(a * b)))
            );

            let a = Fq::random(&mut rng);
            let b = Fq::random(&mut rng);
            let (al, bl) = (
                limbs_from_u64(fq_montgomery_limbs(&a)),
                limbs_from_u64(fq_montgomery_limbs(&b)),
            );
            assert_eq!(fq(&VESTA_BASE.mul(&al, &bl)), a * b);
            assert_eq!(fq(&VESTA_BASE.add(&al, &bl)), a + b);
            assert_eq!(fq(&VESTA_BASE.sub(&al, &bl)), a - b);
            assert_eq!(fq(&VESTA_BASE.neg(&al)), -a);
            assert_eq!(
                VESTA_BASE.mul(&al, &bl),
                limbs_from_u64(fq_montgomery_limbs(&(a * b)))
            );
        }
    }

    #[test]
    fn edge_values() {
        for field in [PALLAS_BASE, VESTA_BASE] {
            let mut max = field.modulus;
            max[0] -= 1;
            assert_eq!(field.add(&max, &field.one), field.add(&field.one, &max));
            let raw_one = limbs_from_u64([1, 0, 0, 0]);
            assert_eq!(field.add(&max, &max), field.sub(&max, &raw_one));
            assert_eq!(field.sub(&Field::ZERO, &field.one), field.neg(&field.one));
            assert!(Field::is_zero(&field.sub(&max, &max)));
            assert!(Field::is_zero(&field.neg(&Field::ZERO)));
            assert_eq!(field.mul(&max, &field.one), max);
            assert_eq!(field.mul(&max, &Field::ZERO), Field::ZERO);
        }
    }

    #[test]
    fn limb_conversions_round_trip() {
        let limbs = [0x0123_4567_89ab_cdef, u64::MAX, 0, 0x4000_0000_0000_0000];
        assert_eq!(limbs_to_u64(&limbs_from_u64(limbs)), limbs);
        assert_eq!(limbs_to_bytes(&limbs_from_u64([1, 0, 0, 0]))[0], 1);
    }
}
