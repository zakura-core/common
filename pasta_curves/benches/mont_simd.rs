//! Native AArch64 experiment: two-lane integer SIMD implementation of the
//! existing four-limb Pasta Montgomery multiplication.

#![cfg(target_arch = "aarch64")]

use core::arch::aarch64::{
    uint32x2_t, uint64x2_t, vaddq_u64, vandq_u64, vbslq_u64, vcltq_u64, vdup_n_u32, vdupq_n_u64,
    vget_lane_u32, vgetq_lane_u64, vmlal_u32, vmovn_u64, vmul_u32, vmull_u32, vset_lane_u32,
    vsetq_lane_u64, vshlq_n_u64, vshrn_n_u64, vshrq_n_u64, vsubq_u64,
};
use core::marker::PhantomData;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use ff::{Field, PrimeField};
use pasta_curves::{Fp, Fq};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

const FP_MODULUS: [u64; 4] = [
    0x992d_30ed_0000_0001,
    0x2246_98fc_094c_f91b,
    0,
    0x4000_0000_0000_0000,
];
const FQ_MODULUS: [u64; 4] = [
    0x8c46_eb21_0000_0001,
    0x2246_98fc_0994_a8dd,
    0,
    0x4000_0000_0000_0000,
];
const FP_INV: u64 = 0x992d_30ec_ffff_ffff;
const FQ_INV: u64 = 0x8c46_eb20_ffff_ffff;

const BATCH_ELEMENTS: [usize; 9] = [2, 8, 32, 128, 512, 2_048, 8_192, 32_768, 65_536];
const BATCH_PAIRS: usize = BATCH_ELEMENTS[BATCH_ELEMENTS.len() - 1] / 2;

trait Params: Copy {
    const MODULUS: [u64; 4];
    const INV: u64;
}

#[derive(Clone, Copy)]
struct FpParams;

impl Params for FpParams {
    const MODULUS: [u64; 4] = FP_MODULUS;
    const INV: u64 = FP_INV;
}

#[derive(Clone, Copy)]
struct FqParams;

impl Params for FqParams {
    const MODULUS: [u64; 4] = FQ_MODULUS;
    const INV: u64 = FQ_INV;
}

/// Two independent four-limb Montgomery residues, one per NEON lane.
#[derive(Clone, Copy)]
struct MontPair<P: Params> {
    limbs: [uint64x2_t; 4],
    marker: PhantomData<P>,
}

/// The same Montgomery residue split into eight 32-bit digits. NEON can
/// widen two 32x32 products directly, avoiding emulation of vector 64x64
/// multiplication while retaining R = 2^256.
#[derive(Clone, Copy)]
struct MontPair32<P: Params> {
    limbs: [uint32x2_t; 8],
    marker: PhantomData<P>,
}

#[inline(always)]
unsafe fn u64_pair(lane0: u64, lane1: u64) -> uint64x2_t {
    vsetq_lane_u64::<1>(lane1, vdupq_n_u64(lane0))
}

#[inline(always)]
unsafe fn u32_pair(lane0: u32, lane1: u32) -> uint32x2_t {
    vset_lane_u32::<1>(lane1, vdup_n_u32(lane0))
}

#[inline(always)]
unsafe fn split_u64(x: uint64x2_t) -> (uint32x2_t, uint32x2_t) {
    (vmovn_u64(x), vshrn_n_u64::<32>(x))
}

/// Exact 64x64 -> 128 multiplication in both lanes, built from NEON's
/// widening 32x32 -> 64 multiplication.
#[inline(always)]
unsafe fn mul_wide(a: uint64x2_t, b: uint64x2_t) -> (uint64x2_t, uint64x2_t) {
    let (a_lo, a_hi) = split_u64(a);
    let (b_lo, b_hi) = split_u64(b);

    let p00 = vmull_u32(a_lo, b_lo);
    let p01 = vmull_u32(a_lo, b_hi);
    let p10 = vmull_u32(a_hi, b_lo);
    let p11 = vmull_u32(a_hi, b_hi);

    let lo1 = vaddq_u64(p00, vshlq_n_u64::<32>(p01));
    let carry1 = vshrq_n_u64::<63>(vcltq_u64(lo1, p00));
    let hi1 = vaddq_u64(vaddq_u64(p11, vshrq_n_u64::<32>(p01)), carry1);

    let lo = vaddq_u64(lo1, vshlq_n_u64::<32>(p10));
    let carry2 = vshrq_n_u64::<63>(vcltq_u64(lo, lo1));
    let hi = vaddq_u64(vaddq_u64(hi1, vshrq_n_u64::<32>(p10)), carry2);
    (lo, hi)
}

/// Low half of two 64x64 products. Montgomery digit generation does not need
/// the high half, so it can omit the high-by-high 32-bit product.
#[inline(always)]
unsafe fn mul_low(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    let (a_lo, a_hi) = split_u64(a);
    let (b_lo, b_hi) = split_u64(b);
    let p00 = vmull_u32(a_lo, b_lo);
    let p01 = vmull_u32(a_lo, b_hi);
    let p10 = vmull_u32(a_hi, b_lo);
    vaddq_u64(
        vaddq_u64(p00, vshlq_n_u64::<32>(p01)),
        vshlq_n_u64::<32>(p10),
    )
}

/// Lane-wise `a + b + carry`, returning the low word and carry word.
#[inline(always)]
unsafe fn adc(a: uint64x2_t, b: uint64x2_t, carry: uint64x2_t) -> (uint64x2_t, uint64x2_t) {
    let ab = vaddq_u64(a, b);
    let carry0 = vshrq_n_u64::<63>(vcltq_u64(ab, a));
    let out = vaddq_u64(ab, carry);
    let carry1 = vshrq_n_u64::<63>(vcltq_u64(out, ab));
    (out, vaddq_u64(carry0, carry1))
}

/// Lane-wise `acc + b*c + carry`, matching the portable backend's `mac`.
#[inline(always)]
unsafe fn mac(
    acc: uint64x2_t,
    b: uint64x2_t,
    c: uint64x2_t,
    carry: uint64x2_t,
) -> (uint64x2_t, uint64x2_t) {
    let (lo, hi) = mul_wide(b, c);
    let sum0 = vaddq_u64(lo, acc);
    let carry0 = vshrq_n_u64::<63>(vcltq_u64(sum0, lo));
    let sum = vaddq_u64(sum0, carry);
    let carry1 = vshrq_n_u64::<63>(vcltq_u64(sum, sum0));
    (sum, vaddq_u64(vaddq_u64(hi, carry0), carry1))
}

/// Lane-wise `a - b - borrow`, with borrow represented as zero or one.
#[inline(always)]
unsafe fn sbb(a: uint64x2_t, b: uint64x2_t, borrow: uint64x2_t) -> (uint64x2_t, uint64x2_t) {
    let ab = vsubq_u64(a, b);
    let borrow0 = vshrq_n_u64::<63>(vcltq_u64(a, b));
    let out = vsubq_u64(ab, borrow);
    let borrow1 = vshrq_n_u64::<63>(vcltq_u64(ab, borrow));
    (out, vaddq_u64(borrow0, borrow1))
}

impl<P: Params> MontPair<P> {
    fn from_words_pair(lane0: [u64; 4], lane1: [u64; 4]) -> Self {
        // SAFETY: Advanced SIMD is mandatory on AArch64.
        let limbs = unsafe {
            [
                u64_pair(lane0[0], lane1[0]),
                u64_pair(lane0[1], lane1[1]),
                u64_pair(lane0[2], lane1[2]),
                u64_pair(lane0[3], lane1[3]),
            ]
        };
        Self {
            limbs,
            marker: PhantomData,
        }
    }

    fn lane_words(&self, lane: usize) -> [u64; 4] {
        assert!(lane < 2);
        // SAFETY: lane is checked above.
        unsafe {
            if lane == 0 {
                [
                    vgetq_lane_u64::<0>(self.limbs[0]),
                    vgetq_lane_u64::<0>(self.limbs[1]),
                    vgetq_lane_u64::<0>(self.limbs[2]),
                    vgetq_lane_u64::<0>(self.limbs[3]),
                ]
            } else {
                [
                    vgetq_lane_u64::<1>(self.limbs[0]),
                    vgetq_lane_u64::<1>(self.limbs[1]),
                    vgetq_lane_u64::<1>(self.limbs[2]),
                    vgetq_lane_u64::<1>(self.limbs[3]),
                ]
            }
        }
    }

    #[inline]
    fn mul(&self, rhs: &Self) -> Self {
        // SAFETY: Advanced SIMD is mandatory on AArch64. The implementation
        // mirrors the portable four-limb product and Montgomery reduction.
        unsafe { self.mul_neon(rhs) }
    }

    #[inline(always)]
    unsafe fn mul_neon(&self, rhs: &Self) -> Self {
        let zero = vdupq_n_u64(0);
        let inv = vdupq_n_u64(P::INV);
        let p = [
            vdupq_n_u64(P::MODULUS[0]),
            vdupq_n_u64(P::MODULUS[1]),
            vdupq_n_u64(P::MODULUS[2]),
            vdupq_n_u64(P::MODULUS[3]),
        ];

        // Schoolbook 4x4 product, exactly matching `mul_unreduced`.
        let (r0, carry) = mac(zero, self.limbs[0], rhs.limbs[0], zero);
        let (r1, carry) = mac(zero, self.limbs[0], rhs.limbs[1], carry);
        let (r2, carry) = mac(zero, self.limbs[0], rhs.limbs[2], carry);
        let (r3, r4) = mac(zero, self.limbs[0], rhs.limbs[3], carry);

        let (r1, carry) = mac(r1, self.limbs[1], rhs.limbs[0], zero);
        let (r2, carry) = mac(r2, self.limbs[1], rhs.limbs[1], carry);
        let (r3, carry) = mac(r3, self.limbs[1], rhs.limbs[2], carry);
        let (r4, r5) = mac(r4, self.limbs[1], rhs.limbs[3], carry);

        let (r2, carry) = mac(r2, self.limbs[2], rhs.limbs[0], zero);
        let (r3, carry) = mac(r3, self.limbs[2], rhs.limbs[1], carry);
        let (r4, carry) = mac(r4, self.limbs[2], rhs.limbs[2], carry);
        let (r5, r6) = mac(r5, self.limbs[2], rhs.limbs[3], carry);

        let (r3, carry) = mac(r3, self.limbs[3], rhs.limbs[0], zero);
        let (r4, carry) = mac(r4, self.limbs[3], rhs.limbs[1], carry);
        let (r5, carry) = mac(r5, self.limbs[3], rhs.limbs[2], carry);
        let (r6, r7) = mac(r6, self.limbs[3], rhs.limbs[3], carry);

        // Four rounds of radix-2^64 Montgomery reduction, exactly matching
        // `montgomery_reduce` in the portable backend.
        let k = mul_low(r0, inv);
        let (_, carry) = mac(r0, k, p[0], zero);
        let (r1, carry) = mac(r1, k, p[1], carry);
        let (r2, carry) = mac(r2, k, p[2], carry);
        let (r3, carry) = mac(r3, k, p[3], carry);
        let (r4, carry2) = adc(r4, zero, carry);

        let k = mul_low(r1, inv);
        let (_, carry) = mac(r1, k, p[0], zero);
        let (r2, carry) = mac(r2, k, p[1], carry);
        let (r3, carry) = mac(r3, k, p[2], carry);
        let (r4, carry) = mac(r4, k, p[3], carry);
        let (r5, carry2) = adc(r5, carry2, carry);

        let k = mul_low(r2, inv);
        let (_, carry) = mac(r2, k, p[0], zero);
        let (r3, carry) = mac(r3, k, p[1], carry);
        let (r4, carry) = mac(r4, k, p[2], carry);
        let (r5, carry) = mac(r5, k, p[3], carry);
        let (r6, carry2) = adc(r6, carry2, carry);

        let k = mul_low(r3, inv);
        let (_, carry) = mac(r3, k, p[0], zero);
        let (r4, carry) = mac(r4, k, p[1], carry);
        let (r5, carry) = mac(r5, k, p[2], carry);
        let (r6, carry) = mac(r6, k, p[3], carry);
        let (r7, _) = adc(r7, carry2, carry);

        // Canonicalize with one conditional subtraction. Montgomery reduction
        // returns a value below 2p.
        let (d0, borrow) = sbb(r4, p[0], zero);
        let (d1, borrow) = sbb(r5, p[1], borrow);
        let (d2, borrow) = sbb(r6, p[2], borrow);
        let (d3, borrow) = sbb(r7, p[3], borrow);
        let use_original = vsubq_u64(zero, borrow);

        Self {
            limbs: [
                vbslq_u64(use_original, r4, d0),
                vbslq_u64(use_original, r5, d1),
                vbslq_u64(use_original, r6, d2),
                vbslq_u64(use_original, r7, d3),
            ],
            marker: PhantomData,
        }
    }
}

impl<P: Params> MontPair32<P> {
    fn from_words_pair(lane0: [u64; 4], lane1: [u64; 4]) -> Self {
        // SAFETY: Advanced SIMD is mandatory on AArch64.
        let limbs = unsafe {
            [
                u32_pair(lane0[0] as u32, lane1[0] as u32),
                u32_pair((lane0[0] >> 32) as u32, (lane1[0] >> 32) as u32),
                u32_pair(lane0[1] as u32, lane1[1] as u32),
                u32_pair((lane0[1] >> 32) as u32, (lane1[1] >> 32) as u32),
                u32_pair(lane0[2] as u32, lane1[2] as u32),
                u32_pair((lane0[2] >> 32) as u32, (lane1[2] >> 32) as u32),
                u32_pair(lane0[3] as u32, lane1[3] as u32),
                u32_pair((lane0[3] >> 32) as u32, (lane1[3] >> 32) as u32),
            ]
        };
        Self {
            limbs,
            marker: PhantomData,
        }
    }

    fn lane_words(&self, lane: usize) -> [u64; 4] {
        assert!(lane < 2);
        // SAFETY: lane is checked above.
        unsafe {
            if lane == 0 {
                [
                    (vget_lane_u32::<0>(self.limbs[0]) as u64)
                        | ((vget_lane_u32::<0>(self.limbs[1]) as u64) << 32),
                    (vget_lane_u32::<0>(self.limbs[2]) as u64)
                        | ((vget_lane_u32::<0>(self.limbs[3]) as u64) << 32),
                    (vget_lane_u32::<0>(self.limbs[4]) as u64)
                        | ((vget_lane_u32::<0>(self.limbs[5]) as u64) << 32),
                    (vget_lane_u32::<0>(self.limbs[6]) as u64)
                        | ((vget_lane_u32::<0>(self.limbs[7]) as u64) << 32),
                ]
            } else {
                [
                    (vget_lane_u32::<1>(self.limbs[0]) as u64)
                        | ((vget_lane_u32::<1>(self.limbs[1]) as u64) << 32),
                    (vget_lane_u32::<1>(self.limbs[2]) as u64)
                        | ((vget_lane_u32::<1>(self.limbs[3]) as u64) << 32),
                    (vget_lane_u32::<1>(self.limbs[4]) as u64)
                        | ((vget_lane_u32::<1>(self.limbs[5]) as u64) << 32),
                    (vget_lane_u32::<1>(self.limbs[6]) as u64)
                        | ((vget_lane_u32::<1>(self.limbs[7]) as u64) << 32),
                ]
            }
        }
    }

    #[inline]
    fn mul(&self, rhs: &Self) -> Self {
        // SAFETY: Advanced SIMD is mandatory on AArch64.
        unsafe { self.mul_neon(rhs) }
    }

    /// Coarsely integrated operand scanning in radix 2^32. This remains the
    /// existing R = 2^256 Montgomery representation at the API boundary, but
    /// uses the digit width NEON can multiply and widen natively.
    #[inline(always)]
    #[allow(clippy::needless_range_loop)]
    unsafe fn mul_neon(&self, rhs: &Self) -> Self {
        let zero = vdupq_n_u64(0);
        let mask = vdupq_n_u64(u32::MAX as u64);
        let inv = vdup_n_u32(P::INV as u32);
        let p = [
            vdup_n_u32(P::MODULUS[0] as u32),
            vdup_n_u32((P::MODULUS[0] >> 32) as u32),
            vdup_n_u32(P::MODULUS[1] as u32),
            vdup_n_u32((P::MODULUS[1] >> 32) as u32),
            vdup_n_u32(P::MODULUS[2] as u32),
            vdup_n_u32((P::MODULUS[2] >> 32) as u32),
            vdup_n_u32(P::MODULUS[3] as u32),
            vdup_n_u32((P::MODULUS[3] >> 32) as u32),
        ];
        let p64 = [
            vdupq_n_u64(P::MODULUS[0] as u32 as u64),
            vdupq_n_u64((P::MODULUS[0] >> 32) as u32 as u64),
            vdupq_n_u64(P::MODULUS[1] as u32 as u64),
            vdupq_n_u64((P::MODULUS[1] >> 32) as u32 as u64),
            vdupq_n_u64(P::MODULUS[2] as u32 as u64),
            vdupq_n_u64((P::MODULUS[2] >> 32) as u32 as u64),
            vdupq_n_u64(P::MODULUS[3] as u32 as u64),
            vdupq_n_u64((P::MODULUS[3] >> 32) as u32 as u64),
        ];

        let mut t = [zero; 9];
        for i in 0..8 {
            let mut carry = zero;
            for j in 0..8 {
                let uv = vaddq_u64(vmlal_u32(t[j], self.limbs[j], rhs.limbs[i]), carry);
                t[j] = vandq_u64(uv, mask);
                carry = vshrq_n_u64::<32>(uv);
            }
            t[8] = vaddq_u64(t[8], carry);

            let m = vmul_u32(vmovn_u64(t[0]), inv);
            carry = zero;
            for j in 0..8 {
                let uv = vaddq_u64(vmlal_u32(t[j], m, p[j]), carry);
                if j != 0 {
                    t[j - 1] = vandq_u64(uv, mask);
                }
                carry = vshrq_n_u64::<32>(uv);
            }
            let uv = vaddq_u64(t[8], carry);
            t[7] = vandq_u64(uv, mask);
            t[8] = vshrq_n_u64::<32>(uv);
        }

        let mut diff = [zero; 8];
        let mut borrow = zero;
        for j in 0..8 {
            let subtrahend = vaddq_u64(p64[j], borrow);
            diff[j] = vandq_u64(vsubq_u64(t[j], subtrahend), mask);
            borrow = vshrq_n_u64::<63>(vcltq_u64(t[j], subtrahend));
        }
        borrow = vshrq_n_u64::<63>(vcltq_u64(t[8], borrow));
        let use_original = vsubq_u64(zero, borrow);

        let mut limbs = [vdup_n_u32(0); 8];
        for j in 0..8 {
            limbs[j] = vmovn_u64(vbslq_u64(use_original, t[j], diff[j]));
        }
        Self {
            limbs,
            marker: PhantomData,
        }
    }
}

fn repr_words<F: PrimeField<Repr = [u8; 32]>>(x: F) -> [u64; 4] {
    let bytes = x.to_repr();
    let mut out = [0u64; 4];
    for (word, chunk) in out.iter_mut().zip(bytes.chunks_exact(8)) {
        *word = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    out
}

fn pow2_256<F: Field>() -> F {
    (0..256).fold(F::ONE, |x, _| x.double())
}

fn validate_fp(samples: &[(Fp, Fp, Fp, Fp)], r: Fp) {
    for &(a0, b0, a1, b1) in samples {
        let lhs = MontPair::<FpParams>::from_words_pair(repr_words(a0 * r), repr_words(a1 * r));
        let rhs = MontPair::<FpParams>::from_words_pair(repr_words(b0 * r), repr_words(b1 * r));
        let got = lhs.mul(&rhs);
        assert_eq!(got.lane_words(0), repr_words((a0 * b0) * r));
        assert_eq!(got.lane_words(1), repr_words((a1 * b1) * r));

        let lhs = MontPair32::<FpParams>::from_words_pair(repr_words(a0 * r), repr_words(a1 * r));
        let rhs = MontPair32::<FpParams>::from_words_pair(repr_words(b0 * r), repr_words(b1 * r));
        let got = lhs.mul(&rhs);
        assert_eq!(got.lane_words(0), repr_words((a0 * b0) * r));
        assert_eq!(got.lane_words(1), repr_words((a1 * b1) * r));
    }
}

fn validate_fq(samples: &[(Fq, Fq, Fq, Fq)], r: Fq) {
    for &(a0, b0, a1, b1) in samples {
        let lhs = MontPair::<FqParams>::from_words_pair(repr_words(a0 * r), repr_words(a1 * r));
        let rhs = MontPair::<FqParams>::from_words_pair(repr_words(b0 * r), repr_words(b1 * r));
        let got = lhs.mul(&rhs);
        assert_eq!(got.lane_words(0), repr_words((a0 * b0) * r));
        assert_eq!(got.lane_words(1), repr_words((a1 * b1) * r));

        let lhs = MontPair32::<FqParams>::from_words_pair(repr_words(a0 * r), repr_words(a1 * r));
        let rhs = MontPair32::<FqParams>::from_words_pair(repr_words(b0 * r), repr_words(b1 * r));
        let got = lhs.mul(&rhs);
        assert_eq!(got.lane_words(0), repr_words((a0 * b0) * r));
        assert_eq!(got.lane_words(1), repr_words((a1 * b1) * r));
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    const VALIDATION_PAIRS: usize = 20_000;
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let fp: Vec<(Fp, Fp, Fp, Fp)> = (0..BATCH_PAIRS)
        .map(|_| {
            (
                Fp::random(&mut rng),
                Fp::random(&mut rng),
                Fp::random(&mut rng),
                Fp::random(&mut rng),
            )
        })
        .collect();
    let fq: Vec<(Fq, Fq, Fq, Fq)> = (0..VALIDATION_PAIRS)
        .map(|_| {
            (
                Fq::random(&mut rng),
                Fq::random(&mut rng),
                Fq::random(&mut rng),
                Fq::random(&mut rng),
            )
        })
        .collect();

    let fp_corners = [
        Fp::ZERO,
        Fp::ONE,
        -Fp::ONE,
        Fp::from(u64::MAX),
        Fp::from_raw([u64::MAX; 4]),
    ];
    let fq_corners = [
        Fq::ZERO,
        Fq::ONE,
        -Fq::ONE,
        Fq::from(u64::MAX),
        Fq::from_raw([u64::MAX; 4]),
    ];
    let fp_corner_cases: Vec<_> = fp_corners
        .iter()
        .flat_map(|&a| fp_corners.iter().map(move |&b| (a, b, b, a)))
        .collect();
    let fq_corner_cases: Vec<_> = fq_corners
        .iter()
        .flat_map(|&a| fq_corners.iter().map(move |&b| (a, b, b, a)))
        .collect();

    let r_fp = pow2_256::<Fp>();
    let r_fq = pow2_256::<Fq>();
    validate_fp(&fp_corner_cases, r_fp);
    validate_fq(&fq_corner_cases, r_fq);
    validate_fp(&fp, r_fp);
    validate_fq(&fq, r_fq);

    let fp_simd: Vec<(MontPair<FpParams>, MontPair<FpParams>)> = fp
        .iter()
        .map(|&(a0, b0, a1, b1)| {
            (
                MontPair::from_words_pair(repr_words(a0 * r_fp), repr_words(a1 * r_fp)),
                MontPair::from_words_pair(repr_words(b0 * r_fp), repr_words(b1 * r_fp)),
            )
        })
        .collect();
    let fp_simd32: Vec<(MontPair32<FpParams>, MontPair32<FpParams>)> = fp
        .iter()
        .map(|&(a0, b0, a1, b1)| {
            (
                MontPair32::from_words_pair(repr_words(a0 * r_fp), repr_words(a1 * r_fp)),
                MontPair32::from_words_pair(repr_words(b0 * r_fp), repr_words(b1 * r_fp)),
            )
        })
        .collect();

    let native_name = if cfg!(feature = "aarch64-asm") {
        "mont-asm"
    } else {
        "mont-portable"
    };
    let mut group = c.benchmark_group("Fp-mont-batch");
    for &elements in &BATCH_ELEMENTS {
        let pairs = elements / 2;
        let native_inputs = &fp[..pairs];
        let simd_inputs = &fp_simd[..pairs];
        let simd32_inputs = &fp_simd32[..pairs];
        group.throughput(Throughput::Elements(elements as u64));

        let mut native_outputs = vec![(Fp::ZERO, Fp::ZERO); pairs];
        group.bench_with_input(
            BenchmarkId::new(native_name, elements),
            &elements,
            |bench, _| {
                bench.iter(|| {
                    for (output, &(a0, b0, a1, b1)) in native_outputs.iter_mut().zip(native_inputs)
                    {
                        *output = (a0 * b0, a1 * b1);
                    }
                    black_box(&native_outputs);
                })
            },
        );

        let mut simd_outputs = vec![fp_simd[0].0; pairs];
        group.bench_with_input(
            BenchmarkId::new("mont-neon64x2", elements),
            &elements,
            |bench, _| {
                bench.iter(|| {
                    for (output, &(lhs, rhs)) in simd_outputs.iter_mut().zip(simd_inputs) {
                        *output = lhs.mul(&rhs);
                    }
                    black_box(&simd_outputs);
                })
            },
        );

        let mut simd32_outputs = vec![fp_simd32[0].0; pairs];
        group.bench_with_input(
            BenchmarkId::new("mont-neon32x2", elements),
            &elements,
            |bench, _| {
                bench.iter(|| {
                    for (output, &(lhs, rhs)) in simd32_outputs.iter_mut().zip(simd32_inputs) {
                        *output = lhs.mul(&rhs);
                    }
                    black_box(&simd32_outputs);
                })
            },
        );
    }
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
