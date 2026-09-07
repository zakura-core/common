//! Portable arithmetic for the Pasta base fields in the representation the
//! Metal kernels use: twenty 13-bit limbs and carry-free Montgomery
//! multiplication.
//!
//! This is the executable specification of the field arithmetic in
//! `shaders/pasta_msm.metal`: every function here has a line-for-line twin
//! in the shader, with the same limb layout, the same schedule, and the
//! same conditional reductions, so the reference backend and the GPU
//! compute bit-identical limbs. Change them together.
//!
//! # Why 13-bit limbs
//!
//! Apple GPUs have no native 64-bit integer multiply, and their 32-bit
//! multiply-high is a slow path, so a classic 32-bit-limb Montgomery
//! multiplication spends most of its time emulating wide products and
//! threading carries. With limbs of $w = 13$ bits ($n = 20$ limbs cover the
//! 255-bit fields with $R = 2^{260}$), a limb product has 26 bits, and the
//! schoolbook Montgomery loop can accumulate every product that lands on
//! one column — at most $2n = 40$ of them plus one incoming carry — in a
//! plain `u32` before a carry is ever propagated:
//! $40 \cdot 2^{26} + 2^{19} < 2^{32}$. The whole multiplication is then
//! 32-bit multiply-adds with one shift per column (Mitscha-Baude's
//! carry-free schedule, at the limb width that fits 32-bit accumulators).
//! Fourteen-bit limbs would overflow, twelve would waste columns; thirteen
//! is the widest width that fits.
//!
//! The price is conversion: `pasta_curves` holds elements as
//! $a \cdot 2^{256} \bmod p$ in four 64-bit limbs, while the device wants
//! $a \cdot 2^{260} \bmod p$ split into 13-bit limbs. [`Field::from_pasta`]
//! does that with four modular doublings and a bit split per coordinate;
//! the reverse, needed only for the handful of window results, is one
//! Montgomery product by 1 and a join.
//!
//! Both Pasta primes are congruent to 1 modulo $2^{32}$, hence modulo
//! $2^{13}$, so the per-column Montgomery factor $-p^{-1} \bmod 2^{13}$ is
//! $2^{13} - 1$ for both fields ([`MU`]); the tests pin that.

/// Bits per limb.
pub const LIMB_BITS: u32 = 13;
/// Limbs per element: $\lceil 255 / 13 \rceil = 20$, so $R = 2^{260}$.
pub const LIMBS: usize = 20;
/// The limb mask, $2^{13} - 1$.
pub const LIMB_MASK: u32 = (1 << LIMB_BITS) - 1;
/// $-p^{-1} \bmod 2^{13}$, shared by both Pasta primes (they are 1 mod $2^{13}$).
pub const MU: u32 = LIMB_MASK;
/// $\log_2 R$ for the device representation.
pub const R_BITS: u32 = LIMB_BITS * LIMBS as u32;

/// A field element: twenty little-endian 13-bit limbs, each held in a
/// `u32`, in Montgomery form with $R = 2^{260}$. Every value produced by
/// [`Field`] is canonical: limbs below $2^{13}$ and the integer below $p$.
pub type Limbs = [u32; LIMBS];

/// The constants of one Pasta base field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Field {
    /// The prime modulus, as device limbs.
    pub modulus: Limbs,
    /// $R \bmod p$: the Montgomery form of 1.
    pub one: Limbs,
    /// $R^2 \bmod p$, the Montgomery conversion factor.
    pub r2: Limbs,
    /// The prime modulus, as the four 64-bit limbs `pasta_curves` uses.
    pub modulus_u64: [u64; 4],
}

/// Splits a 256-bit little-endian integer into device limbs.
pub const fn split(value: &[u64; 4]) -> Limbs {
    let mut out = [0u32; LIMBS];
    let mut i = 0;
    while i < LIMBS {
        let bit = LIMB_BITS as usize * i;
        let word = bit / 64;
        let offset = bit % 64;
        let mut limb = value[word] >> offset;
        if offset + LIMB_BITS as usize > 64 && word + 1 < 4 {
            limb |= value[word + 1] << (64 - offset);
        }
        // Masked to 13 bits, so the cast cannot truncate.
        out[i] = (limb as u32) & LIMB_MASK;
        i += 1;
    }
    out
}

/// Joins canonical device limbs into a 256-bit little-endian integer.
pub const fn join(limbs: &Limbs) -> [u64; 4] {
    let mut out = [0u64; 4];
    let mut i = 0;
    while i < LIMBS {
        let bit = LIMB_BITS as usize * i;
        let word = bit / 64;
        let offset = bit % 64;
        let limb = limbs[i] as u64;
        out[word] |= limb << offset;
        if offset + LIMB_BITS as usize > 64 && word + 1 < 4 {
            out[word + 1] |= limb >> (64 - offset);
        }
        i += 1;
    }
    out
}

/// Little-endian bytes of a 256-bit integer.
pub fn to_bytes(value: &[u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, limb) in value.iter().enumerate() {
        out[i * 8..(i + 1) * 8].copy_from_slice(&limb.to_le_bytes());
    }
    out
}

/// `2 * value mod modulus` over 64-bit limbs, for `value < modulus`.
const fn double_mod(value: &[u64; 4], modulus: &[u64; 4]) -> [u64; 4] {
    let mut sum = [0u64; 4];
    let mut carry = 0u64;
    let mut i = 0;
    while i < 4 {
        let (s, c1) = value[i].overflowing_add(value[i]);
        let (s, c2) = s.overflowing_add(carry);
        sum[i] = s;
        carry = (c1 as u64) + (c2 as u64);
        i += 1;
    }
    let mut diff = [0u64; 4];
    let mut borrow = 0u64;
    let mut i = 0;
    while i < 4 {
        let (d, b1) = sum[i].overflowing_sub(modulus[i]);
        let (d, b2) = d.overflowing_sub(borrow);
        diff[i] = d;
        borrow = (b1 as u64) + (b2 as u64);
        i += 1;
    }
    if carry != 0 || borrow == 0 { diff } else { sum }
}

/// `2^exponent mod modulus` over 64-bit limbs.
const fn pow2_mod(mut exponent: u32, modulus: &[u64; 4]) -> [u64; 4] {
    let mut value = [1u64, 0, 0, 0];
    while exponent > 0 {
        value = double_mod(&value, modulus);
        exponent -= 1;
    }
    value
}

const fn field(modulus_u64: [u64; 4]) -> Field {
    Field {
        modulus: split(&modulus_u64),
        one: split(&pow2_mod(R_BITS, &modulus_u64)),
        r2: split(&pow2_mod(2 * R_BITS, &modulus_u64)),
        modulus_u64,
    }
}

/// The base field of Pallas, $\mathbb{F}_p$ (`pasta_curves::Fp`).
pub const PALLAS_BASE: Field = field([
    0x992d30ed00000001,
    0x224698fc094cf91b,
    0x0000000000000000,
    0x4000000000000000,
]);

/// The base field of Vesta, $\mathbb{F}_q$ (`pasta_curves::Fq`).
pub const VESTA_BASE: Field = field([
    0x8c46eb2100000001,
    0x224698fc0994a8dd,
    0x0000000000000000,
    0x4000000000000000,
]);

impl Field {
    /// The additive identity (zero in any representation).
    pub const ZERO: Limbs = [0; LIMBS];

    /// Whether `a` is zero.
    #[inline]
    pub fn is_zero(a: &Limbs) -> bool {
        a.iter().all(|&limb| limb == 0)
    }

    /// `a - modulus` as limbs, plus the final borrow (`true` when `a < modulus`).
    /// `a` must be carried (every limb below $2^{13}$).
    #[inline]
    fn sub_modulus(&self, a: &Limbs) -> (Limbs, bool) {
        let mut out = [0u32; LIMBS];
        let mut borrow = 0u32;
        for i in 0..LIMBS {
            let d = a[i].wrapping_sub(self.modulus[i]).wrapping_sub(borrow);
            out[i] = d & LIMB_MASK;
            // Limbs are 13 bits, so a negative difference sets bit 31.
            borrow = d >> 31;
        }
        (out, borrow == 1)
    }

    /// Reduces a carried `a` below `2 * modulus` into `[0, modulus)`.
    #[inline]
    fn reduce_once(&self, a: &Limbs) -> Limbs {
        let (reduced, borrow) = self.sub_modulus(a);
        if borrow { *a } else { reduced }
    }

    /// `a + b mod p`.
    #[inline]
    pub fn add(&self, a: &Limbs, b: &Limbs) -> Limbs {
        let mut sum = [0u32; LIMBS];
        let mut carry = 0u32;
        for i in 0..LIMBS {
            let s = a[i] + b[i] + carry;
            sum[i] = s & LIMB_MASK;
            carry = s >> LIMB_BITS;
        }
        // a + b < 2p < 2^255 < R, so the final carry is always zero.
        self.reduce_once(&sum)
    }

    /// `2a mod p`.
    #[inline]
    pub fn double(&self, a: &Limbs) -> Limbs {
        self.add(a, a)
    }

    /// `a - b mod p`.
    #[inline]
    pub fn sub(&self, a: &Limbs, b: &Limbs) -> Limbs {
        let mut diff = [0u32; LIMBS];
        let mut borrow = 0u32;
        for i in 0..LIMBS {
            let d = a[i].wrapping_sub(b[i]).wrapping_sub(borrow);
            diff[i] = d & LIMB_MASK;
            borrow = d >> 31;
        }
        if borrow == 1 {
            // Underflowed: add the modulus back (the carry out cancels).
            let mut carry = 0u32;
            for (limb, modulus) in diff.iter_mut().zip(&self.modulus) {
                let s = *limb + *modulus + carry;
                *limb = s & LIMB_MASK;
                carry = s >> LIMB_BITS;
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

    /// Montgomery product `a * b * R^-1 mod p`: the carry-free schoolbook
    /// schedule. Column `t[k]` accumulates at most `2 * LIMBS` 26-bit
    /// products plus one 19-bit carry before its own carry is taken, which
    /// fits a `u32` (see the module docs); a bound violation would panic
    /// in debug builds rather than wrap.
    pub fn mul(&self, a: &Limbs, b: &Limbs) -> Limbs {
        let p = &self.modulus;
        let mut t = [0u32; 2 * LIMBS];
        for i in 0..LIMBS {
            // t += a * b[i], column-wise, no carries.
            let bi = b[i];
            for j in 0..LIMBS {
                t[i + j] += a[j] * bi;
            }
            // Clear column i: m = t[i] * mu mod 2^13 makes t[i] + m p[0]
            // divisible by 2^13.
            let m = ((t[i] & LIMB_MASK) * MU) & LIMB_MASK;
            for j in 0..LIMBS {
                t[i + j] += m * p[j];
            }
            // Column i is now a multiple of 2^13: carry it into column
            // i + 1 and forget it.
            t[i + 1] += t[i] >> LIMB_BITS;
        }
        // Carry the upper half into canonical limbs.
        for k in LIMBS..2 * LIMBS - 1 {
            t[k + 1] += t[k] >> LIMB_BITS;
            t[k] &= LIMB_MASK;
        }
        let mut out = [0u32; LIMBS];
        out.copy_from_slice(&t[LIMBS..]);
        // The result is below 2p, so one conditional subtraction reduces it.
        self.reduce_once(&out)
    }

    /// `a^2 * R^-1 mod p`.
    #[inline]
    pub fn square(&self, a: &Limbs) -> Limbs {
        self.mul(a, a)
    }

    /// Converts a canonical integer below `p` into device Montgomery form.
    pub fn to_montgomery(&self, canonical: &[u64; 4]) -> Limbs {
        self.mul(&split(canonical), &self.r2)
    }

    /// Converts a device Montgomery-form element to its canonical integer.
    pub fn to_canonical(&self, a: &Limbs) -> [u64; 4] {
        let mut one = [0u32; LIMBS];
        one[0] = 1;
        join(&self.mul(a, &one))
    }

    /// Converts `pasta_curves`' internal Montgomery form
    /// ($a \cdot 2^{256} \bmod p$ in four 64-bit limbs) into device form
    /// ($a \cdot 2^{260} \bmod p$ in 13-bit limbs): four modular doublings
    /// and a split.
    pub fn from_pasta(&self, montgomery: &[u64; 4]) -> Limbs {
        let mut value = *montgomery;
        for _ in 0..(R_BITS - 256) {
            value = double_mod(&value, &self.modulus_u64);
        }
        split(&value)
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
        Fp::from_repr(to_bytes(&PALLAS_BASE.to_canonical(limbs))).unwrap()
    }

    fn fq(limbs: &Limbs) -> Fq {
        Fq::from_repr(to_bytes(&VESTA_BASE.to_canonical(limbs))).unwrap()
    }

    fn canonical(limbs: &Limbs) -> bool {
        limbs.iter().all(|&limb| limb <= LIMB_MASK)
    }

    #[test]
    fn mu_matches_both_moduli() {
        for field in [PALLAS_BASE, VESTA_BASE] {
            assert_eq!(field.modulus[0], 1);
            assert_eq!((field.modulus[0] * MU) & LIMB_MASK, LIMB_MASK);
            assert!(canonical(&field.modulus));
            assert!(canonical(&field.one));
            assert!(canonical(&field.r2));
        }
    }

    #[test]
    fn split_and_join_round_trip() {
        let value = [0x0123_4567_89ab_cdef, u64::MAX, 0, 0x3fff_ffff_ffff_ffff];
        let limbs = split(&value);
        assert!(canonical(&limbs));
        assert_eq!(join(&limbs), value);
        assert_eq!(join(&split(&[1, 0, 0, 0]))[0], 1);
        assert_eq!(to_bytes(&[1, 0, 0, 0])[0], 1);
    }

    #[test]
    fn constants_match_pasta_curves() {
        for (field, one, minus_one) in [
            (
                PALLAS_BASE,
                fp_montgomery_limbs(&Fp::ONE),
                fp_montgomery_limbs(&-Fp::ONE),
            ),
            (
                VESTA_BASE,
                fq_montgomery_limbs(&Fq::ONE),
                fq_montgomery_limbs(&-Fq::ONE),
            ),
        ] {
            assert_eq!(field.from_pasta(&one), field.one);
            assert_eq!(field.to_montgomery(&[1, 0, 0, 0]), field.one);
            assert_eq!(field.to_canonical(&field.one), [1, 0, 0, 0]);
            assert_eq!(field.mul(&field.one, &field.one), field.one);
            let mut expected = field.modulus_u64;
            expected[0] -= 1;
            assert_eq!(field.to_canonical(&field.from_pasta(&minus_one)), expected);
        }
    }

    #[test]
    fn arithmetic_matches_pasta_curves() {
        let mut rng = XorShiftRng::from_seed([7; 16]);
        for _ in 0..500 {
            let a = Fp::random(&mut rng);
            let b = Fp::random(&mut rng);
            let f = &PALLAS_BASE;
            let (al, bl) = (
                f.from_pasta(&fp_montgomery_limbs(&a)),
                f.from_pasta(&fp_montgomery_limbs(&b)),
            );
            assert_eq!(fp(&f.mul(&al, &bl)), a * b);
            assert_eq!(fp(&f.square(&al)), a.square());
            assert_eq!(fp(&f.add(&al, &bl)), a + b);
            assert_eq!(fp(&f.sub(&al, &bl)), a - b);
            assert_eq!(fp(&f.neg(&al)), -a);
            assert_eq!(fp(&f.double(&al)), a.double());
            // Bit-identical device form, not merely equal field elements.
            assert_eq!(
                f.mul(&al, &bl),
                f.from_pasta(&fp_montgomery_limbs(&(a * b)))
            );
            assert!(canonical(&f.mul(&al, &bl)));

            let a = Fq::random(&mut rng);
            let b = Fq::random(&mut rng);
            let f = &VESTA_BASE;
            let (al, bl) = (
                f.from_pasta(&fq_montgomery_limbs(&a)),
                f.from_pasta(&fq_montgomery_limbs(&b)),
            );
            assert_eq!(fq(&f.mul(&al, &bl)), a * b);
            assert_eq!(fq(&f.add(&al, &bl)), a + b);
            assert_eq!(fq(&f.sub(&al, &bl)), a - b);
            assert_eq!(fq(&f.neg(&al)), -a);
            assert_eq!(
                f.mul(&al, &bl),
                f.from_pasta(&fq_montgomery_limbs(&(a * b)))
            );
        }
    }

    #[test]
    fn edge_values() {
        for field in [PALLAS_BASE, VESTA_BASE] {
            let mut max = field.modulus;
            max[0] -= 1;
            let raw_one = split(&[1, 0, 0, 0]);
            assert_eq!(field.add(&max, &field.one), field.add(&field.one, &max));
            assert_eq!(field.add(&max, &max), field.sub(&max, &raw_one));
            assert_eq!(field.add(&max, &raw_one), Field::ZERO);
            assert_eq!(field.sub(&Field::ZERO, &field.one), field.neg(&field.one));
            assert!(Field::is_zero(&field.sub(&max, &max)));
            assert!(Field::is_zero(&field.neg(&Field::ZERO)));
            assert_eq!(field.mul(&max, &field.one), max);
            assert_eq!(field.mul(&max, &Field::ZERO), Field::ZERO);
            // The largest inputs stress the column bound the most: max is
            // the integer p - 1, so max * R^2 / R is the Montgomery form
            // of p - 1, which is -1.
            assert!(canonical(&field.mul(&max, &max)));
            assert_eq!(field.mul(&max, &field.r2), field.neg(&field.one));
            assert_eq!(field.mul(&field.r2, &raw_one), field.one);
        }
    }
}
