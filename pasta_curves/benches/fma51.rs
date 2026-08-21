//! Native AArch64 experiment: paired Pasta-field Montgomery multiplication
//! with five 51-bit FP64 limbs and two-lane NEON FMA.

#![cfg(target_arch = "aarch64")]

use core::arch::aarch64::{
    float64x2_t, int64x2_t, vaddq_s64, vandq_s64, vandq_u64, vdupq_n_f64, vdupq_n_s64, vdupq_n_u32,
    vdupq_n_u64, vfmaq_f64, vgetq_lane_f64, vgetq_lane_s64, vmulq_u32, vreinterpretq_f64_s64,
    vreinterpretq_f64_u64, vreinterpretq_s64_f64, vreinterpretq_s64_u64, vreinterpretq_u32_s64,
    vreinterpretq_u64_f64, vreinterpretq_u64_s64, vreinterpretq_u64_u32, vsetq_lane_f64,
    vsetq_lane_s64, vshlq_n_u64, vshrq_n_s64, vsubq_f64, vsubq_s64, vsubq_u64,
};
use core::arch::asm;
use core::marker::PhantomData;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use ff::{Field, PrimeField};
use group::Group;
use pasta_curves::{arithmetic::CurveExt, pallas, vesta, Fp, Fq};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

const RADIX_BITS: u32 = 51;
const RADIX: u64 = 1u64 << RADIX_BITS;
const MASK: u64 = RADIX - 1;
const HIGH_BIAS_BITS: u64 = 0x4660_0000_0000_0000; // 2^103
const LOW_CENTER_BITS: u64 = 0x4338_0000_0000_0000; // 3 * 2^51
const SPLIT_BIAS_BITS: u64 = 0x4660_0000_0000_0003; // 2^103 + 3 * 2^51

const BATCH_ELEMENTS: [usize; 9] = [2, 8, 32, 128, 512, 2_048, 8_192, 32_768, 65_536];
const BATCH_MAX_PAIRS: usize = BATCH_ELEMENTS[BATCH_ELEMENTS.len() - 1] / 2;

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

const fn words_to_radix51(w: [u64; 4]) -> [u64; 5] {
    [
        w[0] & MASK,
        ((w[0] >> 51) | (w[1] << 13)) & MASK,
        ((w[1] >> 38) | (w[2] << 26)) & MASK,
        ((w[2] >> 25) | (w[3] << 39)) & MASK,
        w[3] >> 12,
    ]
}

const fn neg_inv_mod_radix(x: u64) -> u64 {
    let mut y = 1u64;
    let mut i = 0;
    while i < 6 {
        y = y.wrapping_mul(2u64.wrapping_sub(x.wrapping_mul(y)));
        i += 1;
    }
    y.wrapping_neg() & MASK
}

trait Params: Copy {
    const MODULUS: [u64; 5];
    const N0: u64 = neg_inv_mod_radix(Self::MODULUS[0]);
    const N0_HI32: u32 = ((Self::N0 + 1) >> 32) as u32;
}

#[derive(Clone, Copy)]
struct FpParams;

impl Params for FpParams {
    const MODULUS: [u64; 5] = words_to_radix51(FP_MODULUS);
}

#[derive(Clone, Copy)]
struct FqParams;

impl Params for FqParams {
    const MODULUS: [u64; 5] = words_to_radix51(FQ_MODULUS);
}

#[derive(Clone, Copy)]
struct Pair51<P: Params> {
    limbs: [float64x2_t; 5],
    marker: PhantomData<P>,
}

/// The lazy integer-limb representation used by Yrrid's field-pair kernel.
/// Each SIMD lane is an independent field element.
#[derive(Clone, Copy)]
struct LazyPair51<P: Params> {
    limbs: [int64x2_t; 5],
    marker: PhantomData<P>,
}

/// Five resolved radix-51 limbs already encoded as packed FP64 values.
/// Yrrid reuses this form when one operand participates in several products.
#[derive(Clone, Copy)]
struct ConvertedPair51<P: Params> {
    limbs: [float64x2_t; 5],
    marker: PhantomData<P>,
}

#[inline(always)]
unsafe fn f64_pair(lane0: u64, lane1: u64) -> float64x2_t {
    let v = vdupq_n_f64(lane0 as f64);
    vsetq_lane_f64::<1>(lane1 as f64, v)
}

#[inline(always)]
unsafe fn i64_pair(lane0: u64, lane1: u64) -> int64x2_t {
    let v = vdupq_n_s64(lane0 as i64);
    vsetq_lane_s64::<1>(lane1 as i64, v)
}

#[inline(always)]
unsafe fn integer_limb_to_f64(x: int64x2_t) -> float64x2_t {
    // For |x| < 2^52, adding the 2^52 IEEE-754 bit pattern and then
    // subtracting 2^52 converts both lanes exactly without a scalar ucvtf.
    let bias_i = vdupq_n_s64(0x4330_0000_0000_0000);
    let bias_f = vreinterpretq_f64_s64(bias_i);
    vsubq_f64(vreinterpretq_f64_s64(vaddq_s64(x, bias_i)), bias_f)
}

/// An instruction-free compiler dependency used to keep each CIOS round
/// behind the Montgomery digit produced by the previous round. Without it,
/// LLVM hoists all 25 input products and spills most of them to the stack.
#[inline(always)]
unsafe fn after_dependency(mut value: float64x2_t, dependency: float64x2_t) -> float64x2_t {
    asm!(
        "// {value:v} depends on {dependency:v}",
        value = inout(vreg) value,
        dependency = in(vreg) dependency,
        options(nomem, nostack, preserves_flags)
    );
    value
}

#[inline(always)]
unsafe fn split_product(a: float64x2_t, b: float64x2_t) -> (int64x2_t, int64x2_t) {
    let high_bias = vdupq_n_f64(f64::from_bits(HIGH_BIAS_BITS));
    let split_bias = vdupq_n_f64(f64::from_bits(SPLIT_BIAS_BITS));
    let high_fp = vfmaq_f64(high_bias, a, b);
    let low_fp = vfmaq_f64(vsubq_f64(split_bias, high_fp), a, b);
    let high = vreinterpretq_s64_u64(vsubq_u64(
        vreinterpretq_u64_f64(high_fp),
        vdupq_n_u64(HIGH_BIAS_BITS),
    ));
    let low = vreinterpretq_s64_u64(vsubq_u64(
        vreinterpretq_u64_f64(low_fp),
        vdupq_n_u64(LOW_CENTER_BITS),
    ));
    (low, high)
}

#[inline(always)]
unsafe fn normalize(t: &mut [int64x2_t; 7]) {
    let mask = vdupq_n_s64(MASK as i64);
    for i in 0..6 {
        let carry = vshrq_n_s64::<51>(t[i]);
        t[i] = vandq_s64(t[i], mask);
        t[i + 1] = vaddq_s64(t[i + 1], carry);
    }
}

fn reduce_lane<P: Params>(mut x: [u64; 6]) -> [u64; 5] {
    loop {
        let ge = x[5] != 0
            || (0..5)
                .rev()
                .find_map(|i| (x[i] != P::MODULUS[i]).then_some(x[i] > P::MODULUS[i]))
                .unwrap_or(true);
        if !ge {
            break;
        }
        let mut borrow = 0u64;
        for (xi, &pi) in x[..5].iter_mut().zip(P::MODULUS.iter()) {
            let sub = pi + borrow;
            let next_borrow = (*xi < sub) as u64;
            *xi = xi.wrapping_sub(sub) & MASK;
            borrow = next_borrow;
        }
        x[5] = x[5].wrapping_sub(borrow);
    }
    debug_assert_eq!(x[5], 0);
    [x[0], x[1], x[2], x[3], x[4]]
}

impl<P: Params> Pair51<P> {
    fn from_words_pair(lane0: [u64; 4], lane1: [u64; 4]) -> Self {
        let a = words_to_radix51(lane0);
        let b = words_to_radix51(lane1);
        // SAFETY: FP64 Advanced SIMD is mandatory on AArch64.
        let limbs = unsafe {
            [
                f64_pair(a[0], b[0]),
                f64_pair(a[1], b[1]),
                f64_pair(a[2], b[2]),
                f64_pair(a[3], b[3]),
                f64_pair(a[4], b[4]),
            ]
        };
        Self {
            limbs,
            marker: PhantomData,
        }
    }

    fn unscaled_one() -> Self {
        Self::from_words_pair([1, 0, 0, 0], [1, 0, 0, 0])
    }

    fn lane_words(&self, lane: usize) -> [u64; 4] {
        // SAFETY: lane is checked by the caller and FP64 Advanced SIMD is
        // mandatory on AArch64.
        let l = unsafe {
            debug_assert!(lane < 2);
            if lane == 0 {
                [
                    vgetq_lane_f64::<0>(self.limbs[0]) as u64,
                    vgetq_lane_f64::<0>(self.limbs[1]) as u64,
                    vgetq_lane_f64::<0>(self.limbs[2]) as u64,
                    vgetq_lane_f64::<0>(self.limbs[3]) as u64,
                    vgetq_lane_f64::<0>(self.limbs[4]) as u64,
                ]
            } else {
                [
                    vgetq_lane_f64::<1>(self.limbs[0]) as u64,
                    vgetq_lane_f64::<1>(self.limbs[1]) as u64,
                    vgetq_lane_f64::<1>(self.limbs[2]) as u64,
                    vgetq_lane_f64::<1>(self.limbs[3]) as u64,
                    vgetq_lane_f64::<1>(self.limbs[4]) as u64,
                ]
            }
        };
        [
            l[0] | (l[1] << 51),
            (l[1] >> 13) | (l[2] << 38),
            (l[2] >> 26) | (l[3] << 25),
            (l[3] >> 39) | (l[4] << 12),
        ]
    }

    #[inline]
    fn mul(&self, rhs: &Self) -> Self {
        // SAFETY: FP64 Advanced SIMD is mandatory on AArch64.
        unsafe { self.mul_neon(rhs) }
    }

    #[inline(always)]
    unsafe fn mul_neon(&self, rhs: &Self) -> Self {
        let zero = vdupq_n_s64(0);
        let mut t = [zero; 7];
        let modulus = [
            vdupq_n_f64(P::MODULUS[0] as f64),
            vdupq_n_f64(P::MODULUS[1] as f64),
            vdupq_n_f64(P::MODULUS[2] as f64),
            vdupq_n_f64(P::MODULUS[3] as f64),
            vdupq_n_f64(P::MODULUS[4] as f64),
        ];

        for i in 0..5 {
            for j in 0..5 {
                let (low, high) = split_product(self.limbs[i], rhs.limbs[j]);
                t[j] = vaddq_s64(t[j], low);
                t[j + 1] = vaddq_s64(t[j + 1], high);
            }
            normalize(&mut t);

            let m0 = (vgetq_lane_s64::<0>(t[0]) as u64).wrapping_mul(P::N0) & MASK;
            let m1 = (vgetq_lane_s64::<1>(t[0]) as u64).wrapping_mul(P::N0) & MASK;
            let m = f64_pair(m0, m1);
            for j in 0..5 {
                let (low, high) = split_product(m, modulus[j]);
                t[j] = vaddq_s64(t[j], low);
                t[j + 1] = vaddq_s64(t[j + 1], high);
            }
            normalize(&mut t);
            debug_assert_eq!(vgetq_lane_s64::<0>(t[0]), 0);
            debug_assert_eq!(vgetq_lane_s64::<1>(t[0]), 0);

            for j in 0..6 {
                t[j] = t[j + 1];
            }
            t[6] = zero;
        }
        normalize(&mut t);

        let mut lane0 = [0u64; 6];
        let mut lane1 = [0u64; 6];
        for i in 0..6 {
            lane0[i] = vgetq_lane_s64::<0>(t[i]) as u64;
            lane1[i] = vgetq_lane_s64::<1>(t[i]) as u64;
        }
        let lane0 = reduce_lane::<P>(lane0);
        let lane1 = reduce_lane::<P>(lane1);
        Self {
            limbs: [
                f64_pair(lane0[0], lane1[0]),
                f64_pair(lane0[1], lane1[1]),
                f64_pair(lane0[2], lane1[2]),
                f64_pair(lane0[3], lane1[3]),
                f64_pair(lane0[4], lane1[4]),
            ],
            marker: PhantomData,
        }
    }
}

impl<P: Params> LazyPair51<P> {
    fn from_words_pair(lane0: [u64; 4], lane1: [u64; 4]) -> Self {
        let a = words_to_radix51(lane0);
        let b = words_to_radix51(lane1);
        // SAFETY: Advanced SIMD is mandatory on AArch64.
        let limbs = unsafe {
            [
                i64_pair(a[0], b[0]),
                i64_pair(a[1], b[1]),
                i64_pair(a[2], b[2]),
                i64_pair(a[3], b[3]),
                i64_pair(a[4], b[4]),
            ]
        };
        Self {
            limbs,
            marker: PhantomData,
        }
    }

    fn unscaled_one() -> Self {
        Self::from_words_pair([1, 0, 0, 0], [1, 0, 0, 0])
    }

    #[inline]
    fn mul(&self, rhs: &Self) -> Self {
        // SAFETY: FP64 Advanced SIMD and fused multiply-add are mandatory on
        // the AArch64 target used by this benchmark.
        unsafe { self.mul_neon(rhs) }
    }

    /// Yrrid's biased-accumulator CIOS structure, adapted only by replacing
    /// its field modulus and Montgomery factor with the Pasta parameters.
    #[inline(always)]
    unsafe fn mul_neon(&self, rhs: &Self) -> Self {
        self.converted_neon().mul_neon(&rhs.converted_neon())
    }

    #[inline]
    fn converted(&self) -> ConvertedPair51<P> {
        // SAFETY: FP64 Advanced SIMD is mandatory on AArch64.
        unsafe { self.converted_neon() }
    }

    /// Converts limbs that are already resolved without first running the
    /// four-step radix-51 carry chain. This is Yrrid's `fieldPairConvertMul`
    /// input path; callers must maintain `0 <= limb < 2^51` in both lanes.
    #[inline]
    fn converted_resolved(&self) -> ConvertedPair51<P> {
        // SAFETY: The caller-facing representation invariant is checked in
        // debug builds, and FP64 Advanced SIMD is mandatory on AArch64.
        unsafe { self.converted_resolved_neon() }
    }

    #[inline(always)]
    unsafe fn converted_resolved_neon(&self) -> ConvertedPair51<P> {
        for &limb in &self.limbs {
            debug_assert!((0..RADIX as i64).contains(&vgetq_lane_s64::<0>(limb)));
            debug_assert!((0..RADIX as i64).contains(&vgetq_lane_s64::<1>(limb)));
        }
        ConvertedPair51 {
            limbs: [
                integer_limb_to_f64(self.limbs[0]),
                integer_limb_to_f64(self.limbs[1]),
                integer_limb_to_f64(self.limbs[2]),
                integer_limb_to_f64(self.limbs[3]),
                integer_limb_to_f64(self.limbs[4]),
            ],
            marker: PhantomData,
        }
    }

    #[inline(always)]
    unsafe fn resolve_limbs(limbs: [int64x2_t; 5]) -> [int64x2_t; 5] {
        let mask = vdupq_n_s64(MASK as i64);
        let r1 = vaddq_s64(limbs[1], vshrq_n_s64::<51>(limbs[0]));
        let r2 = vaddq_s64(limbs[2], vshrq_n_s64::<51>(r1));
        let r3 = vaddq_s64(limbs[3], vshrq_n_s64::<51>(r2));
        let r4 = vaddq_s64(limbs[4], vshrq_n_s64::<51>(r3));
        [
            vandq_s64(limbs[0], mask),
            vandq_s64(r1, mask),
            vandq_s64(r2, mask),
            vandq_s64(r3, mask),
            r4,
        ]
    }

    /// Reduces a non-negative, moderately lazy value to resolved limbs below
    /// the modulus. Pasta's top radix-51 modulus limb is exactly 2^50, so the
    /// top limb supplies a close quotient estimate. As in Yrrid, only a rare
    /// boundary case needs the lower limbs to decide the final subtraction.
    #[inline]
    fn reduced_resolved(&self) -> Self {
        // SAFETY: Advanced SIMD is mandatory on AArch64.
        unsafe { self.reduced_resolved_neon() }
    }

    #[inline(always)]
    unsafe fn reduced_resolved_neon(&self) -> Self {
        debug_assert_eq!(P::MODULUS[4], 1u64 << 50);
        let mut r = Self::resolve_limbs(self.limbs);
        let high0 = vgetq_lane_s64::<0>(r[4]);
        let high1 = vgetq_lane_s64::<1>(r[4]);
        debug_assert!(
            high0 >= 0 && high1 >= 0,
            "reduction input must be non-negative"
        );

        // (high - 1) / 2^50 is a conservative quotient: if `high` is exactly
        // on a modulus boundary we deliberately leave one extra modulus for
        // the exact conditional subtraction below.
        let q0 = (high0 as u64).saturating_sub(1) >> 50;
        let q1 = (high1 as u64).saturating_sub(1) >> 50;
        if q0 | q1 != 0 {
            for (limb, &modulus) in r.iter_mut().zip(P::MODULUS.iter()) {
                *limb = vsubq_s64(*limb, i64_pair(q0 * modulus, q1 * modulus));
            }
            r = Self::resolve_limbs(r);
        }

        let high0 = vgetq_lane_s64::<0>(r[4]) as u64;
        let high1 = vgetq_lane_s64::<1>(r[4]) as u64;
        let high_modulus = P::MODULUS[4];
        if high0 < high_modulus && high1 < high_modulus {
            return Self {
                limbs: r,
                marker: PhantomData,
            };
        }

        let lower_ge_modulus = |lane: usize| {
            (0..5)
                .rev()
                .find_map(|i| {
                    let value = if lane == 0 {
                        vgetq_lane_s64::<0>(r[i]) as u64
                    } else {
                        vgetq_lane_s64::<1>(r[i]) as u64
                    };
                    (value != P::MODULUS[i]).then_some(value > P::MODULUS[i])
                })
                .unwrap_or(true)
        };
        let subtract0 =
            (high0 > high_modulus || (high0 == high_modulus && lower_ge_modulus(0))) as u64;
        let subtract1 =
            (high1 > high_modulus || (high1 == high_modulus && lower_ge_modulus(1))) as u64;
        if subtract0 | subtract1 == 0 {
            return Self {
                limbs: r,
                marker: PhantomData,
            };
        }
        for (limb, &modulus) in r.iter_mut().zip(P::MODULUS.iter()) {
            *limb = vsubq_s64(*limb, i64_pair(subtract0 * modulus, subtract1 * modulus));
        }
        r = Self::resolve_limbs(r);

        for &limb in &r {
            debug_assert!((0..RADIX as i64).contains(&vgetq_lane_s64::<0>(limb)));
            debug_assert!((0..RADIX as i64).contains(&vgetq_lane_s64::<1>(limb)));
        }
        Self {
            limbs: r,
            marker: PhantomData,
        }
    }

    #[inline(always)]
    fn add(&self, rhs: &Self) -> Self {
        // SAFETY: Advanced SIMD is mandatory on AArch64.
        unsafe {
            Self {
                limbs: core::array::from_fn(|i| vaddq_s64(self.limbs[i], rhs.limbs[i])),
                marker: PhantomData,
            }
        }
    }

    #[inline(always)]
    fn sub(&self, rhs: &Self) -> Self {
        // SAFETY: Advanced SIMD is mandatory on AArch64.
        unsafe {
            Self {
                limbs: core::array::from_fn(|i| vsubq_s64(self.limbs[i], rhs.limbs[i])),
                marker: PhantomData,
            }
        }
    }

    #[inline(always)]
    fn add_modulus_multiple<const K: u64>(&self) -> Self {
        // SAFETY: Advanced SIMD is mandatory on AArch64, and all constants
        // used by the point formula fit comfortably in signed 64-bit limbs.
        unsafe {
            Self {
                limbs: core::array::from_fn(|i| {
                    vaddq_s64(self.limbs[i], vdupq_n_s64((P::MODULUS[i] * K) as i64))
                }),
                marker: PhantomData,
            }
        }
    }

    #[inline(always)]
    fn doubled(&self) -> Self {
        self.add(self)
    }

    #[inline(always)]
    fn tripled(&self) -> Self {
        self.doubled().add(self)
    }

    #[inline(always)]
    fn quadrupled(&self) -> Self {
        self.doubled().doubled()
    }

    #[inline(always)]
    fn octupled(&self) -> Self {
        self.quadrupled().doubled()
    }

    #[inline(always)]
    fn times_nine(&self) -> Self {
        self.octupled().add(self)
    }

    #[inline(always)]
    unsafe fn converted_neon(&self) -> ConvertedPair51<P> {
        let r = Self::resolve_limbs(self.limbs);
        ConvertedPair51 {
            limbs: [
                integer_limb_to_f64(r[0]),
                integer_limb_to_f64(r[1]),
                integer_limb_to_f64(r[2]),
                integer_limb_to_f64(r[3]),
                integer_limb_to_f64(r[4]),
            ],
            marker: PhantomData,
        }
    }

    fn lane_words(&self, lane: usize) -> [u64; 4] {
        // Resolve carries before extracting and fully reduce only in this
        // validation helper; the timed kernel deliberately returns lazy limbs.
        let mut l = [0u64; 6];
        for i in 0..5 {
            l[i] = unsafe {
                if lane == 0 {
                    vgetq_lane_s64::<0>(self.limbs[i]) as u64
                } else {
                    vgetq_lane_s64::<1>(self.limbs[i]) as u64
                }
            };
        }
        for i in 0..5 {
            let carry = (l[i] as i64 >> RADIX_BITS) as u64;
            l[i] &= MASK;
            l[i + 1] = l[i + 1].wrapping_add(carry);
        }
        let l = reduce_lane::<P>(l);
        [
            l[0] | (l[1] << 51),
            (l[1] >> 13) | (l[2] << 38),
            (l[2] >> 26) | (l[3] << 25),
            (l[3] >> 39) | (l[4] << 12),
        ]
    }
}

impl<P: Params> ConvertedPair51<P> {
    #[inline]
    fn mul(&self, rhs: &Self) -> LazyPair51<P> {
        // SAFETY: FP64 Advanced SIMD and fused multiply-add are mandatory on
        // the AArch64 target used by this benchmark.
        unsafe { self.mul_neon(rhs) }
    }

    /// Core `fieldPairMul` shape from Yrrid: both operands are already
    /// resolved and converted, while the output remains in lazy integer limbs.
    #[inline(always)]
    unsafe fn mul_neon(&self, rhs: &Self) -> LazyPair51<P> {
        const MAGIC: [u64; 11] = [
            0x7990_0000_0000_0000,
            0x6660_0000_0000_0000,
            0x5330_0000_0000_0000,
            0x8338_0000_0000_0000,
            0xb668_0000_0000_0000,
            0xb018_0000_0000_0000,
            0xc348_0000_0000_0000,
            0xd678_0000_0000_0000,
            0xa670_0000_0000_0000,
            0x7340_0000_0000_0000,
            0,
        ];

        let c3 = vdupq_n_f64(f64::from_bits(HIGH_BIAS_BITS));
        let c4 = vdupq_n_f64(f64::from_bits(SPLIT_BIAS_BITS));
        // Both Pasta moduli have a zero coefficient at radix-51 limb 3.
        // MAGIC absorbs that product's fixed high/low IEEE-754 biases, so the
        // reduction omits its two FMAs, subtraction, and accumulator adds.
        debug_assert_eq!(P::MODULUS[3], 0);
        let modulus = [
            vdupq_n_f64(P::MODULUS[0] as f64),
            vdupq_n_f64(P::MODULUS[1] as f64),
            vdupq_n_f64(P::MODULUS[2] as f64),
            vdupq_n_f64(P::MODULUS[3] as f64),
            vdupq_n_f64(P::MODULUS[4] as f64),
        ];
        let mut sum = [vdupq_n_s64(0); 11];
        for (dst, &magic) in sum.iter_mut().zip(MAGIC.iter()) {
            *dst = vdupq_n_s64(magic as i64);
        }

        let mut dependency = vdupq_n_f64(0.0);
        for i in 0..5 {
            let lhs = after_dependency(self.limbs[i], dependency);
            let mut lh = [vdupq_n_f64(0.0); 5];
            for j in 0..5 {
                lh[j] = vfmaq_f64(c3, lhs, rhs.limbs[j]);
            }
            for j in 0..5 {
                sum[j + 1] = vaddq_s64(sum[j + 1], vreinterpretq_s64_f64(lh[j]));
            }
            for item in &mut lh {
                *item = vsubq_f64(c4, *item);
            }
            for j in 0..5 {
                lh[j] = vfmaq_f64(lh[j], lhs, rhs.limbs[j]);
            }
            for j in 0..5 {
                sum[j] = vaddq_s64(sum[j], vreinterpretq_s64_f64(lh[j]));
            }

            // For both Pasta fields, N0 = k * 2^32 - 1. Compute the two
            // Montgomery digits together with packed 32-bit NEON multiply:
            // q = ((sum[0] * k) << 32) - sum[0] (mod 2^51).
            debug_assert_eq!(P::N0, ((P::N0_HI32 as u64) << 32) - 1);
            let q_product = vmulq_u32(vreinterpretq_u32_s64(sum[0]), vdupq_n_u32(P::N0_HI32));
            let q_shifted = vshlq_n_u64::<32>(vreinterpretq_u64_u32(q_product));
            let q_integer = vandq_u64(
                vsubq_u64(q_shifted, vreinterpretq_u64_s64(sum[0])),
                vdupq_n_u64(MASK),
            );
            let q = integer_limb_to_f64(vreinterpretq_s64_u64(q_integer));
            dependency = vreinterpretq_f64_u64(q_integer);

            lh[0] = vfmaq_f64(c3, q, modulus[0]);
            lh[1] = vfmaq_f64(c3, q, modulus[1]);
            lh[2] = vfmaq_f64(c3, q, modulus[2]);
            lh[4] = vfmaq_f64(c3, q, modulus[4]);
            sum[1] = vaddq_s64(sum[1], vreinterpretq_s64_f64(lh[0]));
            sum[2] = vaddq_s64(sum[2], vreinterpretq_s64_f64(lh[1]));
            sum[3] = vaddq_s64(sum[3], vreinterpretq_s64_f64(lh[2]));
            sum[5] = vaddq_s64(sum[5], vreinterpretq_s64_f64(lh[4]));
            lh[0] = vfmaq_f64(vsubq_f64(c4, lh[0]), q, modulus[0]);
            lh[1] = vfmaq_f64(vsubq_f64(c4, lh[1]), q, modulus[1]);
            lh[2] = vfmaq_f64(vsubq_f64(c4, lh[2]), q, modulus[2]);
            lh[4] = vfmaq_f64(vsubq_f64(c4, lh[4]), q, modulus[4]);

            sum[0] = vaddq_s64(sum[0], vreinterpretq_s64_f64(lh[0]));
            sum[1] = vaddq_s64(sum[1], vreinterpretq_s64_f64(lh[1]));
            sum[0] = vaddq_s64(sum[1], vshrq_n_s64::<51>(sum[0]));
            sum[1] = vaddq_s64(sum[2], vreinterpretq_s64_f64(lh[2]));
            sum[2] = sum[3];
            sum[3] = vaddq_s64(sum[4], vreinterpretq_s64_f64(lh[4]));
            sum[4] = sum[5];
            sum[5] = sum[i + 6];
        }

        LazyPair51 {
            limbs: [sum[0], sum[1], sum[2], sum[3], sum[4]],
            marker: PhantomData,
        }
    }
}

/// Two independent Jacobian points kept lane-paired for an entire point
/// operation. Coordinates are resolved radix-51 Montgomery residues at the
/// operation boundary; intermediate products stay in lazy integer limbs.
#[derive(Clone, Copy)]
struct PointPair51<P: Params> {
    x: LazyPair51<P>,
    y: LazyPair51<P>,
    z: LazyPair51<P>,
}

impl<P: Params> PointPair51<P> {
    /// Pasta's a=0 Jacobian doubling formula, algebraically rescheduled to
    /// reuse converted x/y/a/b operands and avoid converting oversized sums:
    ///
    /// A=X^2, B=Y^2, C=B^2, D=4XB, E=3A, F=E^2,
    /// X3=F-2D, Y3=E(D-X3)-8C, Z3=2YZ.
    #[inline]
    fn double(&self) -> Self {
        // Inputs and outputs are resolved, so conversion does not need a carry
        // chain. The core products remain lazy until a value must be reused.
        let x = self.x.converted_resolved();
        let y = self.y.converted_resolved();
        let z = self.z.converted_resolved();

        let a = x.mul(&x).reduced_resolved();
        let b = y.mul(&y).reduced_resolved();
        let z3 = z.mul(&y).doubled();

        let a_converted = a.converted_resolved();
        let b_converted = b.converted_resolved();
        let c = b_converted.mul(&b_converted);
        let d = x.mul(&b_converted).quadrupled();
        let f = a_converted.mul(&a_converted).times_nine();

        // These explicit modulus offsets make every lazy representative
        // non-negative before the quotient-estimate reduction.
        let x3 = f.sub(&d.doubled()).add_modulus_multiple::<16>();
        let delta = d
            .tripled()
            .sub(&f)
            .add_modulus_multiple::<18>()
            .reduced_resolved();
        let y3 = a_converted
            .mul(&delta.converted_resolved())
            .tripled()
            .sub(&c.octupled())
            .add_modulus_multiple::<16>();

        Self {
            x: x3.reduced_resolved(),
            y: y3.reduced_resolved(),
            z: z3.reduced_resolved(),
        }
    }

    /// The ordinary non-exceptional Jacobian addition path used by the Pasta
    /// implementation, rescheduled so converted operands are shared across
    /// dependent products. As in Yrrid's fast accumulator formula, callers
    /// must handle identities, equal points, and inverse points separately.
    #[inline]
    fn add_nonexceptional(&self, rhs: &Self) -> Self {
        let x1 = self.x.converted_resolved();
        let y1 = self.y.converted_resolved();
        let z1 = self.z.converted_resolved();
        let x2 = rhs.x.converted_resolved();
        let y2 = rhs.y.converted_resolved();
        let z2 = rhs.z.converted_resolved();

        let z1z1 = z1.mul(&z1).reduced_resolved();
        let z2z2 = z2.mul(&z2).reduced_resolved();
        let z1z1_c = z1z1.converted_resolved();
        let z2z2_c = z2z2.converted_resolved();

        let u1 = x1.mul(&z2z2_c).reduced_resolved();
        let u2 = x2.mul(&z1z1_c).reduced_resolved();
        let s1_partial = y1.mul(&z2z2_c).reduced_resolved();
        let s2_partial = y2.mul(&z1z1_c).reduced_resolved();
        let s1 = s1_partial.converted_resolved().mul(&z2).reduced_resolved();
        let s2 = s2_partial.converted_resolved().mul(&z1).reduced_resolved();

        let h = u2.sub(&u1).add_modulus_multiple::<1>().reduced_resolved();
        let h_c = h.converted_resolved();
        let i = h_c.mul(&h_c).quadrupled().reduced_resolved();
        let i_c = i.converted_resolved();
        let j = h_c.mul(&i_c).reduced_resolved();
        let j_c = j.converted_resolved();
        let r = s2
            .sub(&s1)
            .add_modulus_multiple::<1>()
            .doubled()
            .reduced_resolved();
        let r_c = r.converted_resolved();
        let v = u1.converted_resolved().mul(&i_c);
        let r2 = r_c.mul(&r_c);

        let x3 = r2
            .sub(&j)
            .sub(&v.doubled())
            .add_modulus_multiple::<5>()
            .reduced_resolved();
        let s1j = s1.converted_resolved().mul(&j_c);
        let delta = v.sub(&x3).add_modulus_multiple::<1>().reduced_resolved();
        let y3 = r_c
            .mul(&delta.converted_resolved())
            .sub(&s1j.doubled())
            .add_modulus_multiple::<4>()
            .reduced_resolved();

        // ((Z1+Z2)^2-Z1^2-Z2^2)H = 2*Z1*Z2*H. The latter
        // schedule avoids converting an oversized sum and reuses both Zs.
        let z_factor = z1.mul(&z2).doubled().reduced_resolved();
        let z3 = z_factor.converted_resolved().mul(&h_c).reduced_resolved();

        Self {
            x: x3,
            y: y3,
            z: z3,
        }
    }
}

impl PointPair51<FpParams> {
    fn from_pallas_pair(lane0: pallas::Point, lane1: pallas::Point, r: Fp) -> Self {
        let (x0, y0, z0) = lane0.jacobian_coordinates();
        let (x1, y1, z1) = lane1.jacobian_coordinates();
        Self {
            x: LazyPair51::from_words_pair(repr_words(x0 * r), repr_words(x1 * r)),
            y: LazyPair51::from_words_pair(repr_words(y0 * r), repr_words(y1 * r)),
            z: LazyPair51::from_words_pair(repr_words(z0 * r), repr_words(z1 * r)),
        }
    }

    fn lane_pallas(&self, lane: usize) -> pallas::Point {
        let x = decode_lazy_lane::<Fp, FpParams>(&self.x, lane);
        let y = decode_lazy_lane::<Fp, FpParams>(&self.y, lane);
        let z = decode_lazy_lane::<Fp, FpParams>(&self.z, lane);
        Option::<pallas::Point>::from(pallas::Point::new_jacobian(x, y, z)).unwrap()
    }
}

impl PointPair51<FqParams> {
    fn from_vesta_pair(lane0: vesta::Point, lane1: vesta::Point, r: Fq) -> Self {
        let (x0, y0, z0) = lane0.jacobian_coordinates();
        let (x1, y1, z1) = lane1.jacobian_coordinates();
        Self {
            x: LazyPair51::from_words_pair(repr_words(x0 * r), repr_words(x1 * r)),
            y: LazyPair51::from_words_pair(repr_words(y0 * r), repr_words(y1 * r)),
            z: LazyPair51::from_words_pair(repr_words(z0 * r), repr_words(z1 * r)),
        }
    }

    fn lane_vesta(&self, lane: usize) -> vesta::Point {
        let x = decode_lazy_lane::<Fq, FqParams>(&self.x, lane);
        let y = decode_lazy_lane::<Fq, FqParams>(&self.y, lane);
        let z = decode_lazy_lane::<Fq, FqParams>(&self.z, lane);
        Option::<vesta::Point>::from(vesta::Point::new_jacobian(x, y, z)).unwrap()
    }
}

fn repr_words<F: PrimeField<Repr = [u8; 32]>>(x: F) -> [u64; 4] {
    let bytes = x.to_repr();
    let mut out = [0u64; 4];
    for i in 0..4 {
        out[i] = u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap());
    }
    out
}

fn words_repr(words: [u64; 4]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (chunk, word) in bytes.chunks_exact_mut(8).zip(words) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    bytes
}

fn pow2_255<F: Field>() -> F {
    (0..255).fold(F::ONE, |x, _| x.double())
}

fn decode_lazy_lane<F, P>(value: &LazyPair51<P>, lane: usize) -> F
where
    F: PrimeField<Repr = [u8; 32]>,
    P: Params,
{
    let normal = value.mul(&LazyPair51::<P>::unscaled_one());
    Option::<F>::from(F::from_repr(words_repr(normal.lane_words(lane)))).unwrap()
}

fn validate_fp(samples: &[(Fp, Fp, Fp, Fp)]) {
    let r = pow2_255::<Fp>();
    let one = Pair51::<FpParams>::unscaled_one();
    let lazy_one = LazyPair51::<FpParams>::unscaled_one();
    for &(a0, b0, a1, b1) in samples {
        let a = Pair51::<FpParams>::from_words_pair(repr_words(a0 * r), repr_words(a1 * r));
        let b = Pair51::<FpParams>::from_words_pair(repr_words(b0 * r), repr_words(b1 * r));
        let got = a.mul(&b).mul(&one);
        let got0 = Option::<Fp>::from(Fp::from_repr(words_repr(got.lane_words(0)))).unwrap();
        let got1 = Option::<Fp>::from(Fp::from_repr(words_repr(got.lane_words(1)))).unwrap();
        assert_eq!(got0, a0 * b0);
        assert_eq!(got1, a1 * b1);

        let a = LazyPair51::<FpParams>::from_words_pair(repr_words(a0 * r), repr_words(a1 * r));
        let b = LazyPair51::<FpParams>::from_words_pair(repr_words(b0 * r), repr_words(b1 * r));
        let got = a.mul(&b).mul(&lazy_one);
        let got0 = Option::<Fp>::from(Fp::from_repr(words_repr(got.lane_words(0)))).unwrap();
        let got1 = Option::<Fp>::from(Fp::from_repr(words_repr(got.lane_words(1)))).unwrap();
        assert_eq!(got0, a0 * b0);
        assert_eq!(got1, a1 * b1);

        let got = a.converted().mul(&b.converted()).mul(&lazy_one);
        let got0 = Option::<Fp>::from(Fp::from_repr(words_repr(got.lane_words(0)))).unwrap();
        let got1 = Option::<Fp>::from(Fp::from_repr(words_repr(got.lane_words(1)))).unwrap();
        assert_eq!(got0, a0 * b0);
        assert_eq!(got1, a1 * b1);

        let got = a
            .converted_resolved()
            .mul(&b.converted_resolved())
            .mul(&lazy_one);
        let got0 = Option::<Fp>::from(Fp::from_repr(words_repr(got.lane_words(0)))).unwrap();
        let got1 = Option::<Fp>::from(Fp::from_repr(words_repr(got.lane_words(1)))).unwrap();
        assert_eq!(got0, a0 * b0);
        assert_eq!(got1, a1 * b1);
    }
}

fn validate_fq(samples: &[(Fq, Fq, Fq, Fq)]) {
    let r = pow2_255::<Fq>();
    let one = Pair51::<FqParams>::unscaled_one();
    let lazy_one = LazyPair51::<FqParams>::unscaled_one();
    for &(a0, b0, a1, b1) in samples {
        let a = Pair51::<FqParams>::from_words_pair(repr_words(a0 * r), repr_words(a1 * r));
        let b = Pair51::<FqParams>::from_words_pair(repr_words(b0 * r), repr_words(b1 * r));
        let got = a.mul(&b).mul(&one);
        let got0 = Option::<Fq>::from(Fq::from_repr(words_repr(got.lane_words(0)))).unwrap();
        let got1 = Option::<Fq>::from(Fq::from_repr(words_repr(got.lane_words(1)))).unwrap();
        assert_eq!(got0, a0 * b0);
        assert_eq!(got1, a1 * b1);

        let a = LazyPair51::<FqParams>::from_words_pair(repr_words(a0 * r), repr_words(a1 * r));
        let b = LazyPair51::<FqParams>::from_words_pair(repr_words(b0 * r), repr_words(b1 * r));
        let got = a.mul(&b).mul(&lazy_one);
        let got0 = Option::<Fq>::from(Fq::from_repr(words_repr(got.lane_words(0)))).unwrap();
        let got1 = Option::<Fq>::from(Fq::from_repr(words_repr(got.lane_words(1)))).unwrap();
        assert_eq!(got0, a0 * b0);
        assert_eq!(got1, a1 * b1);

        let got = a.converted().mul(&b.converted()).mul(&lazy_one);
        let got0 = Option::<Fq>::from(Fq::from_repr(words_repr(got.lane_words(0)))).unwrap();
        let got1 = Option::<Fq>::from(Fq::from_repr(words_repr(got.lane_words(1)))).unwrap();
        assert_eq!(got0, a0 * b0);
        assert_eq!(got1, a1 * b1);

        let got = a
            .converted_resolved()
            .mul(&b.converted_resolved())
            .mul(&lazy_one);
        let got0 = Option::<Fq>::from(Fq::from_repr(words_repr(got.lane_words(0)))).unwrap();
        let got1 = Option::<Fq>::from(Fq::from_repr(words_repr(got.lane_words(1)))).unwrap();
        assert_eq!(got0, a0 * b0);
        assert_eq!(got1, a1 * b1);
    }
}

fn validate_pallas_points(samples: &[(pallas::Point, pallas::Point)], r: Fp) {
    for &(lane0, lane1) in samples {
        let pair = PointPair51::from_pallas_pair(lane0, lane1, r);
        let doubled = pair.double();
        assert_eq!(doubled.lane_pallas(0), lane0.double());
        assert_eq!(doubled.lane_pallas(1), lane1.double());

        // Exercise the persistent representation boundary as well: outputs
        // from one operation become already-resolved inputs to the next.
        let doubled_twice = doubled.double();
        assert_eq!(doubled_twice.lane_pallas(0), lane0.double().double());
        assert_eq!(doubled_twice.lane_pallas(1), lane1.double().double());
    }
}

fn validate_vesta_points(samples: &[(vesta::Point, vesta::Point)], r: Fq) {
    for &(lane0, lane1) in samples {
        let pair = PointPair51::from_vesta_pair(lane0, lane1, r);
        let doubled = pair.double();
        assert_eq!(doubled.lane_vesta(0), lane0.double());
        assert_eq!(doubled.lane_vesta(1), lane1.double());

        let doubled_twice = doubled.double();
        assert_eq!(doubled_twice.lane_vesta(0), lane0.double().double());
        assert_eq!(doubled_twice.lane_vesta(1), lane1.double().double());
    }
}

fn validate_pallas_additions(
    samples: &[(pallas::Point, pallas::Point, pallas::Point, pallas::Point)],
    r: Fp,
) {
    for &(a0, b0, a1, b1) in samples {
        let lhs = PointPair51::from_pallas_pair(a0, a1, r);
        let rhs = PointPair51::from_pallas_pair(b0, b1, r);
        let sum = lhs.add_nonexceptional(&rhs);
        assert_eq!(sum.lane_pallas(0), a0 + b0);
        assert_eq!(sum.lane_pallas(1), a1 + b1);
    }

    for base in 0..samples.len().saturating_sub(3) {
        let mut native0 = samples[base].0;
        let mut native1 = samples[base].2;
        let mut pair = PointPair51::from_pallas_pair(native0, native1, r);
        for k in 0..4 {
            native0 += samples[base + k].1;
            native1 += samples[base + k].3;
            let rhs = PointPair51::from_pallas_pair(samples[base + k].1, samples[base + k].3, r);
            pair = pair.add_nonexceptional(&rhs);
        }
        assert_eq!(pair.lane_pallas(0), native0);
        assert_eq!(pair.lane_pallas(1), native1);
    }
}

fn validate_vesta_additions(
    samples: &[(vesta::Point, vesta::Point, vesta::Point, vesta::Point)],
    r: Fq,
) {
    for &(a0, b0, a1, b1) in samples {
        let lhs = PointPair51::from_vesta_pair(a0, a1, r);
        let rhs = PointPair51::from_vesta_pair(b0, b1, r);
        let sum = lhs.add_nonexceptional(&rhs);
        assert_eq!(sum.lane_vesta(0), a0 + b0);
        assert_eq!(sum.lane_vesta(1), a1 + b1);
    }

    for base in 0..samples.len().saturating_sub(3) {
        let mut native0 = samples[base].0;
        let mut native1 = samples[base].2;
        let mut pair = PointPair51::from_vesta_pair(native0, native1, r);
        for k in 0..4 {
            native0 += samples[base + k].1;
            native1 += samples[base + k].3;
            let rhs = PointPair51::from_vesta_pair(samples[base + k].1, samples[base + k].3, r);
            pair = pair.add_nonexceptional(&rhs);
        }
        assert_eq!(pair.lane_vesta(0), native0);
        assert_eq!(pair.lane_vesta(1), native1);
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    const VALIDATION_SAMPLES: usize = 50_000;
    const POINT_VALIDATION_SAMPLES: usize = 5_000;
    const BENCH_SAMPLES: usize = 1000;
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let fp: Vec<(Fp, Fp, Fp, Fp)> = (0..VALIDATION_SAMPLES)
        .map(|_| {
            (
                Fp::random(&mut rng),
                Fp::random(&mut rng),
                Fp::random(&mut rng),
                Fp::random(&mut rng),
            )
        })
        .collect();
    let fq: Vec<(Fq, Fq, Fq, Fq)> = (0..VALIDATION_SAMPLES)
        .map(|_| {
            (
                Fq::random(&mut rng),
                Fq::random(&mut rng),
                Fq::random(&mut rng),
                Fq::random(&mut rng),
            )
        })
        .collect();
    let pallas_points: Vec<(pallas::Point, pallas::Point)> = (0..POINT_VALIDATION_SAMPLES)
        .map(|_| {
            (
                pallas::Point::generator() * Fq::random(&mut rng),
                pallas::Point::generator() * Fq::random(&mut rng),
            )
        })
        .collect();
    let vesta_points: Vec<(vesta::Point, vesta::Point)> = (0..POINT_VALIDATION_SAMPLES)
        .map(|_| {
            (
                vesta::Point::generator() * Fp::random(&mut rng),
                vesta::Point::generator() * Fp::random(&mut rng),
            )
        })
        .collect();
    let pallas_additions: Vec<_> = (0..POINT_VALIDATION_SAMPLES)
        .map(|i| {
            let a = pallas_points[i];
            let b = pallas_points[(i + 1) % POINT_VALIDATION_SAMPLES];
            (a.0, b.0, a.1, b.1)
        })
        .collect();
    let vesta_additions: Vec<_> = (0..POINT_VALIDATION_SAMPLES)
        .map(|i| {
            let a = vesta_points[i];
            let b = vesta_points[(i + 1) % POINT_VALIDATION_SAMPLES];
            (a.0, b.0, a.1, b.1)
        })
        .collect();

    let fp_corners = [
        Fp::ZERO,
        Fp::ONE,
        -Fp::ONE,
        Fp::from((1u64 << 51) - 1),
        Fp::from(1u64 << 51),
        Fp::from((1u64 << 51) + 1),
        Fp::from(u64::MAX),
        Fp::from_raw([MASK, MASK, MASK, MASK]),
    ];
    let fq_corners = [
        Fq::ZERO,
        Fq::ONE,
        -Fq::ONE,
        Fq::from((1u64 << 51) - 1),
        Fq::from(1u64 << 51),
        Fq::from((1u64 << 51) + 1),
        Fq::from(u64::MAX),
        Fq::from_raw([MASK, MASK, MASK, MASK]),
    ];
    let fp_corner_cases: Vec<_> = fp_corners
        .iter()
        .flat_map(|&a| fp_corners.iter().map(move |&b| (a, b, b, a)))
        .collect();
    let fq_corner_cases: Vec<_> = fq_corners
        .iter()
        .flat_map(|&a| fq_corners.iter().map(move |&b| (a, b, b, a)))
        .collect();
    validate_fp(&fp_corner_cases);
    validate_fq(&fq_corner_cases);
    validate_fp(&fp);
    validate_fq(&fq);

    let r_fp = pow2_255::<Fp>();
    let pallas_corners = [
        (pallas::Point::identity(), pallas::Point::identity()),
        (pallas::Point::generator(), pallas::Point::identity()),
        (pallas::Point::identity(), pallas::Point::generator()),
        (pallas::Point::generator(), -pallas::Point::generator()),
    ];
    validate_pallas_points(&pallas_corners, r_fp);
    validate_pallas_points(&pallas_points, r_fp);
    validate_pallas_additions(&pallas_additions, r_fp);
    let fp51: Vec<(Pair51<FpParams>, Pair51<FpParams>)> = fp
        .iter()
        .take(BENCH_SAMPLES)
        .map(|&(a0, b0, a1, b1)| {
            (
                Pair51::from_words_pair(repr_words(a0 * r_fp), repr_words(a1 * r_fp)),
                Pair51::from_words_pair(repr_words(b0 * r_fp), repr_words(b1 * r_fp)),
            )
        })
        .collect();
    let fp51_lazy: Vec<(LazyPair51<FpParams>, LazyPair51<FpParams>)> = fp
        .iter()
        .take(BATCH_MAX_PAIRS)
        .map(|&(a0, b0, a1, b1)| {
            (
                LazyPair51::from_words_pair(repr_words(a0 * r_fp), repr_words(a1 * r_fp)),
                LazyPair51::from_words_pair(repr_words(b0 * r_fp), repr_words(b1 * r_fp)),
            )
        })
        .collect();
    let fp51_converted: Vec<(ConvertedPair51<FpParams>, ConvertedPair51<FpParams>)> = fp51_lazy
        .iter()
        .map(|(a, b)| (a.converted(), b.converted()))
        .collect();
    let r_fq = pow2_255::<Fq>();
    let vesta_corners = [
        (vesta::Point::identity(), vesta::Point::identity()),
        (vesta::Point::generator(), vesta::Point::identity()),
        (vesta::Point::identity(), vesta::Point::generator()),
        (vesta::Point::generator(), -vesta::Point::generator()),
    ];
    validate_vesta_points(&vesta_corners, r_fq);
    validate_vesta_points(&vesta_points, r_fq);
    validate_vesta_additions(&vesta_additions, r_fq);
    let fq51: Vec<(Pair51<FqParams>, Pair51<FqParams>)> = fq
        .iter()
        .take(BENCH_SAMPLES)
        .map(|&(a0, b0, a1, b1)| {
            (
                Pair51::from_words_pair(repr_words(a0 * r_fq), repr_words(a1 * r_fq)),
                Pair51::from_words_pair(repr_words(b0 * r_fq), repr_words(b1 * r_fq)),
            )
        })
        .collect();
    let fq51_lazy: Vec<(LazyPair51<FqParams>, LazyPair51<FqParams>)> = fq
        .iter()
        .take(BENCH_SAMPLES)
        .map(|&(a0, b0, a1, b1)| {
            (
                LazyPair51::from_words_pair(repr_words(a0 * r_fq), repr_words(a1 * r_fq)),
                LazyPair51::from_words_pair(repr_words(b0 * r_fq), repr_words(b1 * r_fq)),
            )
        })
        .collect();
    let fq51_converted: Vec<(ConvertedPair51<FqParams>, ConvertedPair51<FqParams>)> = fq51_lazy
        .iter()
        .map(|(a, b)| (a.converted(), b.converted()))
        .collect();
    let pallas51: Vec<PointPair51<FpParams>> = pallas_points
        .iter()
        .take(BENCH_SAMPLES)
        .map(|&(lane0, lane1)| PointPair51::from_pallas_pair(lane0, lane1, r_fp))
        .collect();
    let vesta51: Vec<PointPair51<FqParams>> = vesta_points
        .iter()
        .take(BENCH_SAMPLES)
        .map(|&(lane0, lane1)| PointPair51::from_vesta_pair(lane0, lane1, r_fq))
        .collect();
    let pallas_add51: Vec<(PointPair51<FpParams>, PointPair51<FpParams>)> = pallas_additions
        .iter()
        .take(BENCH_SAMPLES)
        .map(|&(a0, b0, a1, b1)| {
            (
                PointPair51::from_pallas_pair(a0, a1, r_fp),
                PointPair51::from_pallas_pair(b0, b1, r_fp),
            )
        })
        .collect();
    let vesta_add51: Vec<(PointPair51<FqParams>, PointPair51<FqParams>)> = vesta_additions
        .iter()
        .take(BENCH_SAMPLES)
        .map(|&(a0, b0, a1, b1)| {
            (
                PointPair51::from_vesta_pair(a0, a1, r_fq),
                PointPair51::from_vesta_pair(b0, b1, r_fq),
            )
        })
        .collect();

    let mut fp_group = c.benchmark_group("Fp-pair");
    fp_group.throughput(Throughput::Elements(2));
    let mut index = 0usize;
    fp_group.bench_function("native-scalar/2", |bench| {
        bench.iter(|| {
            let (a0, b0, a1, b1) = fp[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box((a0 * b0, a1 * b1))
        })
    });
    index = 0;
    fp_group.bench_function("fma51x2", |bench| {
        bench.iter(|| {
            let (a, b) = fp51[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(a.mul(&b))
        })
    });
    index = 0;
    fp_group.bench_function("fma51x2-yrrid/2", |bench| {
        bench.iter(|| {
            let (a, b) = fp51_lazy[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(a.mul(&b))
        })
    });
    index = 0;
    fp_group.bench_function("fma51x2-yrrid-core/2", |bench| {
        bench.iter(|| {
            let (a, b) = fp51_converted[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(a.mul(&b))
        })
    });
    index = 0;
    fp_group.bench_function("fma51x2-yrrid-convert/2", |bench| {
        bench.iter(|| {
            let (a, b) = fp51_lazy[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(a.converted_resolved().mul(&b.converted_resolved()))
        })
    });
    fp_group.throughput(Throughput::Elements(4));
    index = 0;
    fp_group.bench_function("native-scalar/4", |bench| {
        bench.iter(|| {
            let x0 = fp[index];
            let x1 = fp[index + 1];
            index = (index + 2) % BENCH_SAMPLES;
            black_box([x0.0 * x0.1, x0.2 * x0.3, x1.0 * x1.1, x1.2 * x1.3])
        })
    });
    index = 0;
    fp_group.bench_function("fma51x2-yrrid/4", |bench| {
        bench.iter(|| {
            let (a0, b0) = fp51_lazy[index];
            let (a1, b1) = fp51_lazy[index + 1];
            index = (index + 2) % BENCH_SAMPLES;
            black_box([a0.mul(&b0), a1.mul(&b1)])
        })
    });
    fp_group.throughput(Throughput::Elements(8));
    index = 0;
    fp_group.bench_function("native-scalar/8", |bench| {
        bench.iter(|| {
            let x0 = fp[index];
            let x1 = fp[index + 1];
            let x2 = fp[index + 2];
            let x3 = fp[index + 3];
            index = (index + 4) % BENCH_SAMPLES;
            black_box([
                x0.0 * x0.1,
                x0.2 * x0.3,
                x1.0 * x1.1,
                x1.2 * x1.3,
                x2.0 * x2.1,
                x2.2 * x2.3,
                x3.0 * x3.1,
                x3.2 * x3.3,
            ])
        })
    });
    index = 0;
    fp_group.bench_function("fma51x2-yrrid/8", |bench| {
        bench.iter(|| {
            let (a0, b0) = fp51_lazy[index];
            let (a1, b1) = fp51_lazy[index + 1];
            let (a2, b2) = fp51_lazy[index + 2];
            let (a3, b3) = fp51_lazy[index + 3];
            index = (index + 4) % BENCH_SAMPLES;
            black_box([a0.mul(&b0), a1.mul(&b1), a2.mul(&b2), a3.mul(&b3)])
        })
    });
    fp_group.finish();

    let mut fq_group = c.benchmark_group("Fq-pair");
    fq_group.throughput(Throughput::Elements(2));
    index = 0;
    fq_group.bench_function("native-scalar/2", |bench| {
        bench.iter(|| {
            let (a0, b0, a1, b1) = fq[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box((a0 * b0, a1 * b1))
        })
    });
    index = 0;
    fq_group.bench_function("fma51x2", |bench| {
        bench.iter(|| {
            let (a, b) = fq51[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(a.mul(&b))
        })
    });
    index = 0;
    fq_group.bench_function("fma51x2-yrrid/2", |bench| {
        bench.iter(|| {
            let (a, b) = fq51_lazy[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(a.mul(&b))
        })
    });
    index = 0;
    fq_group.bench_function("fma51x2-yrrid-core/2", |bench| {
        bench.iter(|| {
            let (a, b) = fq51_converted[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(a.mul(&b))
        })
    });
    index = 0;
    fq_group.bench_function("fma51x2-yrrid-convert/2", |bench| {
        bench.iter(|| {
            let (a, b) = fq51_lazy[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(a.converted_resolved().mul(&b.converted_resolved()))
        })
    });
    fq_group.throughput(Throughput::Elements(4));
    index = 0;
    fq_group.bench_function("native-scalar/4", |bench| {
        bench.iter(|| {
            let x0 = fq[index];
            let x1 = fq[index + 1];
            index = (index + 2) % BENCH_SAMPLES;
            black_box([x0.0 * x0.1, x0.2 * x0.3, x1.0 * x1.1, x1.2 * x1.3])
        })
    });
    index = 0;
    fq_group.bench_function("fma51x2-yrrid/4", |bench| {
        bench.iter(|| {
            let (a0, b0) = fq51_lazy[index];
            let (a1, b1) = fq51_lazy[index + 1];
            index = (index + 2) % BENCH_SAMPLES;
            black_box([a0.mul(&b0), a1.mul(&b1)])
        })
    });
    fq_group.throughput(Throughput::Elements(8));
    index = 0;
    fq_group.bench_function("native-scalar/8", |bench| {
        bench.iter(|| {
            let x0 = fq[index];
            let x1 = fq[index + 1];
            let x2 = fq[index + 2];
            let x3 = fq[index + 3];
            index = (index + 4) % BENCH_SAMPLES;
            black_box([
                x0.0 * x0.1,
                x0.2 * x0.3,
                x1.0 * x1.1,
                x1.2 * x1.3,
                x2.0 * x2.1,
                x2.2 * x2.3,
                x3.0 * x3.1,
                x3.2 * x3.3,
            ])
        })
    });
    index = 0;
    fq_group.bench_function("fma51x2-yrrid/8", |bench| {
        bench.iter(|| {
            let (a0, b0) = fq51_lazy[index];
            let (a1, b1) = fq51_lazy[index + 1];
            let (a2, b2) = fq51_lazy[index + 2];
            let (a3, b3) = fq51_lazy[index + 3];
            index = (index + 4) % BENCH_SAMPLES;
            black_box([a0.mul(&b0), a1.mul(&b1), a2.mul(&b2), a3.mul(&b3)])
        })
    });
    fq_group.finish();

    // Test the proposed size-based dispatch in the SIMD path's favor: its
    // operands are already packed in the persistent radix-51 representation,
    // so this excludes the conversion cost a public batch API would incur.
    // If SIMD does not cross over here, adding a conversion-inclusive runtime
    // cutoff cannot improve the result.
    let mut fp_batch_group = c.benchmark_group("Fp-batch-mul");
    for &elements in &BATCH_ELEMENTS {
        let pairs = elements / 2;
        let native_inputs = &fp[..pairs];
        let simd_inputs = &fp51_lazy[..pairs];
        let simd_converted_inputs = &fp51_converted[..pairs];

        fp_batch_group.throughput(Throughput::Elements(elements as u64));

        let mut native_outputs = vec![(Fp::ZERO, Fp::ZERO); pairs];
        fp_batch_group.bench_with_input(
            BenchmarkId::new("mont-native", elements),
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

        let mut simd_outputs = vec![fp51_lazy[0].0; pairs];
        fp_batch_group.bench_with_input(
            BenchmarkId::new("fma51x2-persistent", elements),
            &elements,
            |bench, _| {
                bench.iter(|| {
                    for (output, &(lhs, rhs)) in simd_outputs.iter_mut().zip(simd_inputs) {
                        *output = lhs.converted_resolved().mul(&rhs.converted_resolved());
                    }
                    black_box(&simd_outputs);
                })
            },
        );

        // An intentionally optimistic upper bound for a batch backend: input
        // conversion is outside the timed region, and four pair-products are
        // exposed together so LLVM and the CPU can overlap independent work.
        let mut preconverted_outputs = vec![fp51_lazy[0].0; pairs];
        fp_batch_group.bench_with_input(
            BenchmarkId::new("fma51x2-preconverted-unroll4", elements),
            &elements,
            |bench, _| {
                bench.iter(|| {
                    let chunked_pairs = pairs / 4 * 4;
                    for (outputs, inputs) in preconverted_outputs[..chunked_pairs]
                        .chunks_exact_mut(4)
                        .zip(simd_converted_inputs[..chunked_pairs].chunks_exact(4))
                    {
                        let r0 = inputs[0].0.mul(&inputs[0].1);
                        let r1 = inputs[1].0.mul(&inputs[1].1);
                        let r2 = inputs[2].0.mul(&inputs[2].1);
                        let r3 = inputs[3].0.mul(&inputs[3].1);
                        outputs.copy_from_slice(&[r0, r1, r2, r3]);
                    }
                    for (output, &(lhs, rhs)) in preconverted_outputs[chunked_pairs..]
                        .iter_mut()
                        .zip(&simd_converted_inputs[chunked_pairs..])
                    {
                        *output = lhs.mul(&rhs);
                    }
                    black_box(&preconverted_outputs);
                })
            },
        );
    }
    fp_batch_group.finish();

    let mut pallas_group = c.benchmark_group("Pallas-double-pair");
    pallas_group.throughput(Throughput::Elements(2));
    index = 0;
    pallas_group.bench_function("native-scalar/2", |bench| {
        bench.iter(|| {
            let (lane0, lane1) = pallas_points[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box((lane0.double(), lane1.double()))
        })
    });
    index = 0;
    pallas_group.bench_function("fma51x2-persistent/2", |bench| {
        bench.iter(|| {
            let pair = pallas51[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(pair.double())
        })
    });
    pallas_group.throughput(Throughput::Elements(4));
    index = 0;
    pallas_group.bench_function("native-scalar/4", |bench| {
        bench.iter(|| {
            let a = pallas_points[index];
            let b = pallas_points[index + 1];
            index = (index + 2) % BENCH_SAMPLES;
            black_box([a.0.double(), a.1.double(), b.0.double(), b.1.double()])
        })
    });
    index = 0;
    pallas_group.bench_function("fma51x2-persistent/4", |bench| {
        bench.iter(|| {
            let a = pallas51[index];
            let b = pallas51[index + 1];
            index = (index + 2) % BENCH_SAMPLES;
            black_box([a.double(), b.double()])
        })
    });
    pallas_group.throughput(Throughput::Elements(8));
    index = 0;
    pallas_group.bench_function("native-scalar/8", |bench| {
        bench.iter(|| {
            let a = pallas_points[index];
            let b = pallas_points[index + 1];
            let c = pallas_points[index + 2];
            let d = pallas_points[index + 3];
            index = (index + 4) % BENCH_SAMPLES;
            black_box([
                a.0.double(),
                a.1.double(),
                b.0.double(),
                b.1.double(),
                c.0.double(),
                c.1.double(),
                d.0.double(),
                d.1.double(),
            ])
        })
    });
    index = 0;
    pallas_group.bench_function("fma51x2-persistent/8", |bench| {
        bench.iter(|| {
            let a = pallas51[index];
            let b = pallas51[index + 1];
            let c = pallas51[index + 2];
            let d = pallas51[index + 3];
            index = (index + 4) % BENCH_SAMPLES;
            black_box([a.double(), b.double(), c.double(), d.double()])
        })
    });
    pallas_group.throughput(Throughput::Elements(8));
    index = 0;
    pallas_group.bench_function("native-scalar/chain4", |bench| {
        bench.iter(|| {
            let (mut lane0, mut lane1) = pallas_points[index];
            index = (index + 1) % BENCH_SAMPLES;
            for _ in 0..4 {
                lane0 = lane0.double();
                lane1 = lane1.double();
            }
            black_box((lane0, lane1))
        })
    });
    index = 0;
    pallas_group.bench_function("fma51x2-persistent/chain4", |bench| {
        bench.iter(|| {
            let mut pair = pallas51[index];
            index = (index + 1) % BENCH_SAMPLES;
            for _ in 0..4 {
                pair = pair.double();
            }
            black_box(pair)
        })
    });
    pallas_group.finish();

    let mut vesta_group = c.benchmark_group("Vesta-double-pair");
    vesta_group.throughput(Throughput::Elements(2));
    index = 0;
    vesta_group.bench_function("native-scalar/2", |bench| {
        bench.iter(|| {
            let (lane0, lane1) = vesta_points[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box((lane0.double(), lane1.double()))
        })
    });
    index = 0;
    vesta_group.bench_function("fma51x2-persistent/2", |bench| {
        bench.iter(|| {
            let pair = vesta51[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(pair.double())
        })
    });
    vesta_group.throughput(Throughput::Elements(4));
    index = 0;
    vesta_group.bench_function("native-scalar/4", |bench| {
        bench.iter(|| {
            let a = vesta_points[index];
            let b = vesta_points[index + 1];
            index = (index + 2) % BENCH_SAMPLES;
            black_box([a.0.double(), a.1.double(), b.0.double(), b.1.double()])
        })
    });
    index = 0;
    vesta_group.bench_function("fma51x2-persistent/4", |bench| {
        bench.iter(|| {
            let a = vesta51[index];
            let b = vesta51[index + 1];
            index = (index + 2) % BENCH_SAMPLES;
            black_box([a.double(), b.double()])
        })
    });
    vesta_group.throughput(Throughput::Elements(8));
    index = 0;
    vesta_group.bench_function("native-scalar/8", |bench| {
        bench.iter(|| {
            let a = vesta_points[index];
            let b = vesta_points[index + 1];
            let c = vesta_points[index + 2];
            let d = vesta_points[index + 3];
            index = (index + 4) % BENCH_SAMPLES;
            black_box([
                a.0.double(),
                a.1.double(),
                b.0.double(),
                b.1.double(),
                c.0.double(),
                c.1.double(),
                d.0.double(),
                d.1.double(),
            ])
        })
    });
    index = 0;
    vesta_group.bench_function("fma51x2-persistent/8", |bench| {
        bench.iter(|| {
            let a = vesta51[index];
            let b = vesta51[index + 1];
            let c = vesta51[index + 2];
            let d = vesta51[index + 3];
            index = (index + 4) % BENCH_SAMPLES;
            black_box([a.double(), b.double(), c.double(), d.double()])
        })
    });
    vesta_group.throughput(Throughput::Elements(8));
    index = 0;
    vesta_group.bench_function("native-scalar/chain4", |bench| {
        bench.iter(|| {
            let (mut lane0, mut lane1) = vesta_points[index];
            index = (index + 1) % BENCH_SAMPLES;
            for _ in 0..4 {
                lane0 = lane0.double();
                lane1 = lane1.double();
            }
            black_box((lane0, lane1))
        })
    });
    index = 0;
    vesta_group.bench_function("fma51x2-persistent/chain4", |bench| {
        bench.iter(|| {
            let mut pair = vesta51[index];
            index = (index + 1) % BENCH_SAMPLES;
            for _ in 0..4 {
                pair = pair.double();
            }
            black_box(pair)
        })
    });
    vesta_group.finish();

    let mut pallas_add_group = c.benchmark_group("Pallas-add-pair");
    pallas_add_group.throughput(Throughput::Elements(2));
    index = 0;
    pallas_add_group.bench_function("native-scalar/2", |bench| {
        bench.iter(|| {
            let (a0, b0, a1, b1) = pallas_additions[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box((a0 + b0, a1 + b1))
        })
    });
    index = 0;
    pallas_add_group.bench_function("fma51x2-persistent-nonexceptional/2", |bench| {
        bench.iter(|| {
            let (lhs, rhs) = pallas_add51[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(lhs.add_nonexceptional(&rhs))
        })
    });
    pallas_add_group.throughput(Throughput::Elements(8));
    index = 0;
    pallas_add_group.bench_function("native-scalar/chain4", |bench| {
        bench.iter(|| {
            let base = index;
            index = if index + 5 >= BENCH_SAMPLES {
                0
            } else {
                index + 1
            };
            let mut lane0 = pallas_additions[base].0;
            let mut lane1 = pallas_additions[base].2;
            for k in 0..4 {
                lane0 += pallas_additions[base + k].1;
                lane1 += pallas_additions[base + k].3;
            }
            black_box((lane0, lane1))
        })
    });
    index = 0;
    pallas_add_group.bench_function("fma51x2-persistent-nonexceptional/chain4", |bench| {
        bench.iter(|| {
            let base = index;
            index = if index + 5 >= BENCH_SAMPLES {
                0
            } else {
                index + 1
            };
            let mut acc = pallas_add51[base].0;
            for k in 0..4 {
                acc = acc.add_nonexceptional(&pallas_add51[base + k].1);
            }
            black_box(acc)
        })
    });
    pallas_add_group.finish();

    let mut vesta_add_group = c.benchmark_group("Vesta-add-pair");
    vesta_add_group.throughput(Throughput::Elements(2));
    index = 0;
    vesta_add_group.bench_function("native-scalar/2", |bench| {
        bench.iter(|| {
            let (a0, b0, a1, b1) = vesta_additions[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box((a0 + b0, a1 + b1))
        })
    });
    index = 0;
    vesta_add_group.bench_function("fma51x2-persistent-nonexceptional/2", |bench| {
        bench.iter(|| {
            let (lhs, rhs) = vesta_add51[index];
            index = (index + 1) % BENCH_SAMPLES;
            black_box(lhs.add_nonexceptional(&rhs))
        })
    });
    vesta_add_group.throughput(Throughput::Elements(8));
    index = 0;
    vesta_add_group.bench_function("native-scalar/chain4", |bench| {
        bench.iter(|| {
            let base = index;
            index = if index + 5 >= BENCH_SAMPLES {
                0
            } else {
                index + 1
            };
            let mut lane0 = vesta_additions[base].0;
            let mut lane1 = vesta_additions[base].2;
            for k in 0..4 {
                lane0 += vesta_additions[base + k].1;
                lane1 += vesta_additions[base + k].3;
            }
            black_box((lane0, lane1))
        })
    });
    index = 0;
    vesta_add_group.bench_function("fma51x2-persistent-nonexceptional/chain4", |bench| {
        bench.iter(|| {
            let base = index;
            index = if index + 5 >= BENCH_SAMPLES {
                0
            } else {
                index + 1
            };
            let mut acc = vesta_add51[base].0;
            for k in 0..4 {
                acc = acc.add_nonexceptional(&vesta_add51[base + k].1);
            }
            black_box(acc)
        })
    });
    vesta_add_group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
