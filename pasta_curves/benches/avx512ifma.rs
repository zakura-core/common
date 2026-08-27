//! Benchmark-only AVX-512IFMA experiment for the Pasta fields.
//!
//! This deliberately keeps the SIMD representation out of the production
//! field API. It measures both the optimistic case, where eight independent
//! values remain packed as five radix-2^52 limbs, and the boundary-cost case,
//! where each batch is converted to and from the normal four-limb Montgomery
//! representation. The scalar comparison is eight calls through PR #222's
//! BMI2/ADX field-multiplication dispatch.

#[cfg(target_arch = "x86_64")]
use criterion::{criterion_group, criterion_main};

#[cfg(not(target_arch = "x86_64"))]
fn main() {
    eprintln!("the AVX-512IFMA experiment only builds on x86-64");
}

#[cfg(target_arch = "x86_64")]
criterion_group!(benches, experiment::benchmark);
#[cfg(target_arch = "x86_64")]
criterion_main!(benches);

#[cfg(target_arch = "x86_64")]
mod experiment {
    use core::arch::x86_64::*;
    use core::fmt::Debug;
    use core::ops::{Add, Mul, Neg};

    use criterion::{black_box, Criterion, Throughput};
    use pasta_curves::{Fp, Fq};

    const LANES: usize = 8;
    const LIMBS_52: usize = 5;
    const MASK_52: u64 = (1_u64 << 52) - 1;

    #[derive(Clone, Copy)]
    struct FieldParams {
        name: &'static str,
        modulus_64: [u64; 4],
        modulus_52: [u64; LIMBS_52],
        neg_inv_52: u64,
    }

    const FP_PARAMS: FieldParams = FieldParams {
        name: "Fp",
        modulus_64: [
            0x992d_30ed_0000_0001,
            0x2246_98fc_094c_f91b,
            0x0000_0000_0000_0000,
            0x4000_0000_0000_0000,
        ],
        modulus_52: [
            0x000d_30ed_0000_0001,
            0x000f_c094_cf91_b992,
            0x0000_0000_0022_4698,
            0x0000_0000_0000_0000,
            0x0000_4000_0000_0000,
        ],
        neg_inv_52: 0x000d_30ec_ffff_ffff,
    };

    const FQ_PARAMS: FieldParams = FieldParams {
        name: "Fq",
        modulus_64: [
            0x8c46_eb21_0000_0001,
            0x2246_98fc_0994_a8dd,
            0x0000_0000_0000_0000,
            0x4000_0000_0000_0000,
        ],
        modulus_52: [
            0x0006_eb21_0000_0001,
            0x000f_c099_4a8d_d8c4,
            0x0000_0000_0022_4698,
            0x0000_0000_0000_0000,
            0x0000_4000_0000_0000,
        ],
        neg_inv_52: 0x0006_eb20_ffff_ffff,
    };

    /// Five vectors, each containing the same radix-2^52 limb from eight
    /// independent field elements (a structure-of-arrays layout).
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    #[repr(C, align(64))]
    struct Radix52Batch {
        limbs: [[u64; LANES]; LIMBS_52],
    }

    impl Default for Radix52Batch {
        fn default() -> Self {
            Self {
                limbs: [[0; LANES]; LIMBS_52],
            }
        }
    }

    trait PastaField:
        Copy + Debug + Eq + From<u64> + Add<Output = Self> + Mul<Output = Self> + Neg<Output = Self>
    {
        const PARAMS: FieldParams;
    }

    impl PastaField for Fp {
        const PARAMS: FieldParams = FP_PARAMS;
    }

    impl PastaField for Fq {
        const PARAMS: FieldParams = FQ_PARAMS;
    }

    fn raw_from_field<F: PastaField>(value: F) -> [u64; 4] {
        assert_eq!(core::mem::size_of::<F>(), core::mem::size_of::<[u64; 4]>());
        // Fp and Fq are repr(transparent) wrappers around [u64; 4]. This is a
        // benchmark-only representation bridge, not a proposed public API.
        unsafe { core::mem::transmute_copy(&value) }
    }

    fn field_from_raw<F: PastaField>(value: [u64; 4]) -> F {
        assert_eq!(core::mem::size_of::<F>(), core::mem::size_of::<[u64; 4]>());
        // The callers reduce `value` below the relevant modulus first.
        unsafe { core::mem::transmute_copy(&value) }
    }

    fn subtract_if_ge(value: [u64; 4], modulus: [u64; 4]) -> [u64; 4] {
        let mut difference = [0_u64; 4];
        let mut borrow = false;
        for i in 0..4 {
            let (word, borrow_modulus) = value[i].overflowing_sub(modulus[i]);
            let (word, borrow_in) = word.overflowing_sub(u64::from(borrow));
            difference[i] = word;
            borrow = borrow_modulus || borrow_in;
        }
        if borrow {
            value
        } else {
            difference
        }
    }

    fn times_16_mod(mut value: [u64; 4], modulus: [u64; 4]) -> [u64; 4] {
        for _ in 0..4 {
            let mut doubled = [0_u64; 4];
            let mut carry = 0_u64;
            for i in 0..4 {
                doubled[i] = (value[i] << 1) | carry;
                carry = value[i] >> 63;
            }
            debug_assert_eq!(carry, 0);
            value = subtract_if_ge(doubled, modulus);
        }
        value
    }

    fn divide_by_16_mod(mut value: [u64; 4], modulus: [u64; 4]) -> [u64; 4] {
        for _ in 0..4 {
            if value[0] & 1 == 1 {
                let mut carry = false;
                for i in 0..4 {
                    let (word, carry_value) = value[i].overflowing_add(modulus[i]);
                    let (word, carry_in) = word.overflowing_add(u64::from(carry));
                    value[i] = word;
                    carry = carry_value || carry_in;
                }
                debug_assert!(!carry);
            }

            let mut carry = 0_u64;
            for i in (0..4).rev() {
                let next_carry = value[i] << 63;
                value[i] = (value[i] >> 1) | carry;
                carry = next_carry;
            }
        }
        value
    }

    fn radix_64_to_52(value: [u64; 4]) -> [u64; LIMBS_52] {
        let mut result = [0_u64; LIMBS_52];
        for (i, limb) in result.iter_mut().enumerate() {
            let bit = i * 52;
            let word = bit / 64;
            let shift = bit % 64;
            let mut extracted = value[word] >> shift;
            if shift != 0 && word + 1 < value.len() {
                extracted |= value[word + 1] << (64 - shift);
            }
            *limb = extracted & MASK_52;
        }
        result
    }

    fn radix_52_to_64(value: [u64; LIMBS_52]) -> [u64; 4] {
        let mut result = [0_u64; 4];
        for (i, limb) in value.into_iter().enumerate() {
            debug_assert_eq!(limb & !MASK_52, 0);
            let bit = i * 52;
            let word = bit / 64;
            let shift = bit % 64;
            if word < result.len() {
                result[word] |= limb << shift;
            }
            if shift != 0 && word + 1 < result.len() {
                result[word + 1] |= limb >> (64 - shift);
            }
        }
        result
    }

    fn pack<F: PastaField>(values: &[F; LANES]) -> Radix52Batch {
        let mut result = Radix52Batch::default();
        for lane in 0..LANES {
            // The normal representation uses R = 2^256. IFMA uses
            // R = (2^52)^5 = 2^260, so multiply the stored integer by 16.
            let raw = times_16_mod(raw_from_field(values[lane]), F::PARAMS.modulus_64);
            let limbs = radix_64_to_52(raw);
            for i in 0..LIMBS_52 {
                result.limbs[i][lane] = limbs[i];
            }
        }
        result
    }

    fn unpack<F: PastaField>(values: &Radix52Batch) -> [F; LANES] {
        core::array::from_fn(|lane| {
            let limbs = core::array::from_fn(|i| values.limbs[i][lane]);
            let raw = radix_52_to_64(limbs);
            // Convert R = 2^260 back to the normal R = 2^256.
            field_from_raw(divide_by_16_mod(raw, F::PARAMS.modulus_64))
        })
    }

    fn verify_params(params: FieldParams) {
        assert_eq!(radix_52_to_64(params.modulus_52), params.modulus_64);
        assert_eq!(
            params.modulus_52[0].wrapping_mul(params.neg_inv_52) & MASK_52,
            MASK_52,
            "neg_inv_52 must equal -p^-1 mod 2^52"
        );
    }

    /// Eight independent CIOS Montgomery multiplications in radix 2^52.
    ///
    /// The low and high halves of each 52x52 product accumulate directly into
    /// adjacent limbs. The modulus has a zero fourth radix limb, so those five
    /// multiply-add pairs are omitted. Inputs and output are canonical.
    #[target_feature(enable = "avx512f,avx512ifma")]
    unsafe fn montgomery_mul_8(
        output: &mut Radix52Batch,
        lhs: &Radix52Batch,
        rhs: &Radix52Batch,
        params: FieldParams,
    ) {
        unsafe {
            let zero = _mm512_setzero_si512();
            let mask_52 = _mm512_set1_epi64(MASK_52 as i64);
            let one = _mm512_set1_epi64(1);
            let neg_inv = _mm512_set1_epi64(params.neg_inv_52 as i64);
            let modulus = params.modulus_52.map(|limb| _mm512_set1_epi64(limb as i64));
            debug_assert_eq!(params.modulus_52[3], 0);

            let lhs = lhs
                .limbs
                .each_ref()
                .map(|limb| _mm512_loadu_si512(limb.as_ptr().cast()));
            let rhs = rhs
                .limbs
                .each_ref()
                .map(|limb| _mm512_loadu_si512(limb.as_ptr().cast()));
            let mut t = [zero; LIMBS_52 + 1];

            for rhs_limb in rhs {
                t[0] = _mm512_madd52lo_epu64(t[0], lhs[0], rhs_limb);
                t[1] = _mm512_madd52hi_epu64(t[1], lhs[0], rhs_limb);
                t[1] = _mm512_madd52lo_epu64(t[1], lhs[1], rhs_limb);
                t[2] = _mm512_madd52hi_epu64(t[2], lhs[1], rhs_limb);
                t[2] = _mm512_madd52lo_epu64(t[2], lhs[2], rhs_limb);
                t[3] = _mm512_madd52hi_epu64(t[3], lhs[2], rhs_limb);
                t[3] = _mm512_madd52lo_epu64(t[3], lhs[3], rhs_limb);
                t[4] = _mm512_madd52hi_epu64(t[4], lhs[3], rhs_limb);
                t[4] = _mm512_madd52lo_epu64(t[4], lhs[4], rhs_limb);
                t[5] = _mm512_madd52hi_epu64(t[5], lhs[4], rhs_limb);

                // m = t[0] * (-p^-1) mod 2^52.
                let m = _mm512_madd52lo_epu64(zero, t[0], neg_inv);

                t[0] = _mm512_madd52lo_epu64(t[0], m, modulus[0]);
                t[1] = _mm512_madd52hi_epu64(t[1], m, modulus[0]);
                t[1] = _mm512_madd52lo_epu64(t[1], m, modulus[1]);
                t[2] = _mm512_madd52hi_epu64(t[2], m, modulus[1]);
                t[2] = _mm512_madd52lo_epu64(t[2], m, modulus[2]);
                t[3] = _mm512_madd52hi_epu64(t[3], m, modulus[2]);
                t[4] = _mm512_madd52lo_epu64(t[4], m, modulus[4]);
                t[5] = _mm512_madd52hi_epu64(t[5], m, modulus[4]);

                // t[0] is now divisible by 2^52. Divide the whole redundant
                // accumulator by the radix while retaining its small carry.
                let carry = _mm512_srli_epi64::<52>(t[0]);
                t = [_mm512_add_epi64(t[1], carry), t[2], t[3], t[4], t[5], zero];
            }

            // Normalize the redundant result.
            for i in 0..4 {
                let carry = _mm512_srli_epi64::<52>(t[i]);
                t[i] = _mm512_and_si512(t[i], mask_52);
                t[i + 1] = _mm512_add_epi64(t[i + 1], carry);
            }

            // CIOS returns a value below 2p. Subtract p lane-wise, then select
            // the original value in lanes where the subtraction borrowed.
            let mut difference = [zero; LIMBS_52];
            let mut borrow = 0_u8;
            for i in 0..LIMBS_52 {
                let borrow_vector = _mm512_maskz_mov_epi64(borrow, one);
                let subtrahend = _mm512_add_epi64(modulus[i], borrow_vector);
                difference[i] = _mm512_and_si512(_mm512_sub_epi64(t[i], subtrahend), mask_52);
                borrow = _mm512_cmp_epu64_mask::<{ _MM_CMPINT_LT }>(t[i], subtrahend);
            }

            for i in 0..LIMBS_52 {
                let canonical = _mm512_mask_blend_epi64(borrow, difference[i], t[i]);
                _mm512_storeu_si512(output.limbs[i].as_mut_ptr().cast(), canonical);
            }
        }
    }

    fn scalar_mul_8<F: PastaField>(lhs: &[F; LANES], rhs: &[F; LANES]) -> [F; LANES] {
        core::array::from_fn(|lane| lhs[lane] * rhs[lane])
    }

    fn test_inputs<F: PastaField>() -> ([F; LANES], [F; LANES]) {
        let mut lhs = core::array::from_fn(|i| F::from((i as u64 + 1) * 0x1_0001));
        let mut rhs = core::array::from_fn(|i| F::from((i as u64 + 9) * 0x10_0101));
        lhs[0] = F::from(0);
        lhs[1] = F::from(1);
        lhs[7] = -F::from(1);
        rhs[0] = -F::from(1);
        rhs[1] = F::from(0);
        rhs[7] = -F::from(2);
        (lhs, rhs)
    }

    fn verify<F: PastaField>() {
        verify_params(F::PARAMS);
        let (mut lhs, mut rhs) = test_inputs::<F>();

        for round in 0..128_u64 {
            let expected = scalar_mul_8(&lhs, &rhs);
            let mut packed_result = Radix52Batch::default();
            unsafe {
                montgomery_mul_8(&mut packed_result, &pack(&lhs), &pack(&rhs), F::PARAMS);
            }
            assert_eq!(unpack::<F>(&packed_result), expected);

            lhs = core::array::from_fn(|i| expected[i] + F::from(round + i as u64 + 1));
            rhs = core::array::from_fn(|i| rhs[i] * rhs[(i + 3) % LANES] + F::from(round + 3));
        }

        // Exercise the persistent packed representation across a longer chain;
        // this catches missing carry normalization or non-canonical outputs.
        let (lhs, rhs) = test_inputs::<F>();
        let mut packed_lhs = pack(&lhs);
        let packed_rhs = pack(&rhs);
        let mut expected = lhs;
        for _ in 0..128 {
            let mut next = Radix52Batch::default();
            unsafe { montgomery_mul_8(&mut next, &packed_lhs, &packed_rhs, F::PARAMS) };
            packed_lhs = next;
            expected = scalar_mul_8(&expected, &rhs);
        }
        assert_eq!(unpack::<F>(&packed_lhs), expected);
    }

    fn benchmark_field<F: PastaField>(c: &mut Criterion) {
        verify::<F>();

        let (lhs, rhs) = test_inputs::<F>();
        let packed_lhs = pack(&lhs);
        let packed_rhs = pack(&rhs);
        let mut group = c.benchmark_group(format!("{} batch8 multiply", F::PARAMS.name));
        group.throughput(Throughput::Elements(LANES as u64));

        group.bench_function("pr222_bmi2_adx", |bencher| {
            bencher.iter(|| scalar_mul_8(black_box(&lhs), black_box(&rhs)))
        });

        group.bench_function("avx512ifma_core", |bencher| {
            let mut output = Radix52Batch::default();
            bencher.iter(|| {
                unsafe {
                    montgomery_mul_8(
                        &mut output,
                        black_box(&packed_lhs),
                        black_box(&packed_rhs),
                        F::PARAMS,
                    )
                };
                black_box(output)
            })
        });

        group.bench_function("avx512ifma_with_conversions", |bencher| {
            let mut output = Radix52Batch::default();
            bencher.iter(|| {
                let packed_lhs = pack(black_box(&lhs));
                let packed_rhs = pack(black_box(&rhs));
                unsafe { montgomery_mul_8(&mut output, &packed_lhs, &packed_rhs, F::PARAMS) };
                black_box(unpack::<F>(&output))
            })
        });

        group.finish();
    }

    pub fn benchmark(c: &mut Criterion) {
        assert!(
            is_x86_feature_detected!("avx512f") && is_x86_feature_detected!("avx512ifma"),
            "this benchmark requires AVX-512F and AVX-512IFMA"
        );
        assert!(
            is_x86_feature_detected!("bmi2") && is_x86_feature_detected!("adx"),
            "the PR #222 baseline requires BMI2 and ADX"
        );

        benchmark_field::<Fp>(c);
        benchmark_field::<Fq>(c);
    }
}
