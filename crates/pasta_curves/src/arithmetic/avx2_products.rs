//! Four-way AVX2 expansion and accumulation of challenge-product coefficient
//! vectors (see [`super::CoefficientProducts`]).
//!
//! Each round of the expansion multiplies every coefficient so far by the
//! same challenge, so the challenge is prepared once per round in radix 2^29
//! (scaled by 2^5, which keeps [`mul`]'s products in the scalar fields'
//! Montgomery domain; see [`super::avx2_chord`]) and broadcast to all lanes.
//! The multiplications of a round are independent, so they run at the
//! multiplier's throughput rather than its latency.
//!
//! # Bounds
//!
//! [`mul`] of `a < 2^261` and `b < 2^261` (normalized limbs) is below
//! `a b / 2^261 + p`. A round multiplies a coefficient below `B p` by the
//! scaled challenge `32 u < 32 p`, giving at most
//! `(32 p) (B p) / 2^261 + p = (B p / 2^256 + 1) p`. With
//! `2^254 < p < 2^254 + 2^126`, `p / 2^256` is below `1/4 + 2^-128`, so from
//! canonical inputs (`B = 1`) the bound stays below `4/3 p + 2^-120 p` for any
//! number of rounds: well inside [`mul`]'s limits, with no reduction between
//! rounds.
//!
//! The accumulator adds each round's normalized outputs limb-wise, without
//! carries: limbs 0 to 7 are below 2^29 and limb 8 below 2^23 per vector, so
//! a 64-bit lane overflows only after more than 2^34 vectors. Finishing
//! propagates the carries, unpacks each coefficient to a 320-bit integer and
//! reduces it once.
#![allow(unsafe_code)]

use alloc::vec::Vec;
use core::arch::x86_64::*;
use core::marker::PhantomData;

use super::avx2_chord::{normalize, shl5, unpack_wide};
use super::avx2_sqrt::{L, V, mul, pack};
use super::coefficient_products::expand_coefficient_products;

/// The AVX2 [`super::CoefficientProducts::ProductSums`]: lazily summed
/// radix-2^29 coefficients, four per vector.
pub struct Avx2ProductSums<F> {
    log_len: usize,
    /// Coefficients `4 i .. 4 i + 4` in vector `i`.
    sums: Vec<V>,
    vectors: u64,
    scratch: Vec<V>,
    head: Vec<F>,
    field: PhantomData<F>,
}

impl<F> core::fmt::Debug for Avx2ProductSums<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Avx2ProductSums")
            .field("log_len", &self.log_len)
            .field("vectors", &self.vectors)
            .finish()
    }
}

/// Rounds expanded on the scalar path before the vectors start: they produce
/// the first four coefficients, one vector.
const HEAD_ROUNDS: usize = 2;

impl<F: ff::Field> Avx2ProductSums<F> {
    pub(crate) fn new(log_len: usize) -> Self {
        let vectors = (1usize << log_len).div_ceil(4);
        // SAFETY: an all-zero `__m256i` is a valid value; `_mm256_setzero_si256`
        // needs AVX, which `pasta_curves_avx2` guarantees.
        let zero = unsafe { V([_mm256_setzero_si256(); L]) };
        Avx2ProductSums {
            log_len,
            sums: alloc::vec![zero; vectors],
            vectors: 0,
            scratch: Vec::new(),
            head: Vec::new(),
            field: PhantomData,
        }
    }

    /// Adds the coefficients of `init * prod_i (1 + u_{k-1-i} X^{2^i})`.
    /// `limbs` returns an element's canonical Montgomery limbs.
    pub(crate) fn add<const P0: u64, const P1: u64, const P2: u64, const P3: u64>(
        &mut self,
        u: &[F],
        init: F,
        limbs: impl Fn(&F) -> [u64; 4],
    ) {
        assert_eq!(u.len(), self.log_len, "one challenge per round");
        let head_rounds = u.len().min(HEAD_ROUNDS);
        let (tail, head) = u.split_at(u.len() - head_rounds);
        // The last challenges are the first rounds (see the expansion order).
        expand_coefficient_products(head, init, &mut self.head);
        let mut first = [[0u64; 4]; 4];
        for (out, value) in first.iter_mut().zip(&self.head) {
            *out = limbs(value);
        }
        let challenges: Vec<[u64; 4]> = tail.iter().rev().map(&limbs).collect();
        // SAFETY: `pasta_curves_avx2` guarantees AVX2 (see `avx2_sqrt`).
        unsafe {
            expand_and_add::<P0, P1, P2, P3>(&first, &challenges, &mut self.scratch, &mut self.sums)
        };
        self.vectors += 1;
    }

    pub(crate) fn merge(&mut self, other: Self) {
        assert_eq!(other.log_len, self.log_len, "equal-length vectors");
        // SAFETY: `pasta_curves_avx2` guarantees AVX2.
        unsafe { add_vectors(&mut self.sums, &other.sums) };
        self.vectors += other.vectors;
    }

    /// Reduces each coefficient modulo `modulus` and builds the field
    /// elements from the reduced Montgomery limbs.
    pub(crate) fn finish(self, modulus: &[u64; 4], from_limbs: impl Fn([u64; 4]) -> F) -> Vec<F> {
        let len = 1usize << self.log_len;
        let mut out = Vec::with_capacity(len);
        for v in &self.sums {
            // SAFETY: `pasta_curves_avx2` guarantees AVX2.
            let wide = unsafe { unpack_wide(&normalize(v.0)) };
            for lane in &wide {
                if out.len() < len {
                    out.push(from_limbs(reduce_wide(lane, modulus)));
                }
            }
        }
        out
    }
}

/// Expands from the first four coefficients through `challenges` (in round
/// order) into `scratch`, and adds the result to `sums`.
///
/// The products of a round are independent, so they are computed four at a
/// time to keep several long multiply chains in flight. The last round, half
/// of all coefficients, is added straight into `sums` instead of `scratch`.
#[target_feature(enable = "avx2")]
fn expand_and_add<const P0: u64, const P1: u64, const P2: u64, const P3: u64>(
    first: &[[u64; 4]; 4],
    challenges: &[[u64; 4]],
    scratch: &mut Vec<V>,
    sums: &mut [V],
) {
    scratch.clear();
    scratch.reserve(sums.len() / 2 + 1);
    scratch.push(pack(first));
    let Some((last, rounds)) = challenges.split_last() else {
        add_vectors(sums, scratch);
        return;
    };
    for u in rounds {
        let u32 = shl5(&pack(&[*u; 4]));
        let len = scratch.len();
        let mut i = 0;
        while i + 4 <= len {
            let p0 = mul::<P0, P1, P2, P3>(&u32, &scratch[i]);
            let p1 = mul::<P0, P1, P2, P3>(&u32, &scratch[i + 1]);
            let p2 = mul::<P0, P1, P2, P3>(&u32, &scratch[i + 2]);
            let p3 = mul::<P0, P1, P2, P3>(&u32, &scratch[i + 3]);
            scratch.extend_from_slice(&[p0, p1, p2, p3]);
            i += 4;
        }
        for i in i..len {
            let product = mul::<P0, P1, P2, P3>(&u32, &scratch[i]);
            scratch.push(product);
        }
    }
    // The last round: coefficient vector `i` and its product with the last
    // challenge, vector `len + i`, both go straight into the sums.
    let u32 = shl5(&pack(&[*last; 4]));
    let len = scratch.len();
    let (low, high) = sums.split_at_mut(len);
    add_vectors(low, scratch);
    let mut i = 0;
    while i + 4 <= len {
        let products = [
            mul::<P0, P1, P2, P3>(&u32, &scratch[i]),
            mul::<P0, P1, P2, P3>(&u32, &scratch[i + 1]),
            mul::<P0, P1, P2, P3>(&u32, &scratch[i + 2]),
            mul::<P0, P1, P2, P3>(&u32, &scratch[i + 3]),
        ];
        add_vectors(&mut high[i..i + 4], &products);
        i += 4;
    }
    for i in i..len {
        let product = mul::<P0, P1, P2, P3>(&u32, &scratch[i]);
        add_vectors(&mut high[i..i + 1], core::slice::from_ref(&product));
    }
}

#[target_feature(enable = "avx2")]
fn add_vectors(sums: &mut [V], values: &[V]) {
    for (sum, value) in sums.iter_mut().zip(values) {
        for (s, v) in sum.0.iter_mut().zip(&value.0) {
            *s = _mm256_add_epi64(*s, *v);
        }
    }
}

/// `value mod modulus` for `value < 2^318` and `2^254 < modulus < 2^255`.
///
/// `q = floor(value / 2^254)` is at least `floor(value / modulus)`, and
/// exceeds it by at most one: `value / 2^254 - value / modulus` is
/// `value (modulus - 2^254) / (2^254 modulus)`, below one for these moduli
/// (`modulus - 2^254 < 2^126`) and any `value < 2^380`. So
/// `value - q modulus` lies in `[-modulus, modulus)`.
fn reduce_wide(value: &[u64; 5], modulus: &[u64; 4]) -> [u64; 4] {
    debug_assert!(value[4] >> 62 == 0, "sums stay below 2^318");
    let q = (value[4] << 2) | (value[3] >> 62);
    // q * modulus, in five words.
    let mut product = [0u64; 5];
    let mut carry = 0u128;
    for (word, &limb) in product.iter_mut().zip(modulus) {
        let t = u128::from(q) * u128::from(limb) + carry;
        *word = t as u64;
        carry = t >> 64;
    }
    product[4] = carry as u64;
    // value - q * modulus.
    let mut result = [0u64; 5];
    let mut borrow = false;
    for i in 0..5 {
        let (d, b1) = value[i].overflowing_sub(product[i]);
        let (d, b2) = d.overflowing_sub(u64::from(borrow));
        result[i] = d;
        borrow = b1 | b2;
    }
    if borrow {
        // Negative: add the modulus back once.
        let mut carry = false;
        for i in 0..4 {
            let (s, c1) = result[i].overflowing_add(modulus[i]);
            let (s, c2) = s.overflowing_add(u64::from(carry));
            result[i] = s;
            carry = c1 | c2;
        }
        result[4] = result[4].wrapping_add(u64::from(carry));
    }
    debug_assert_eq!(result[4], 0);
    [result[0], result[1], result[2], result[3]]
}
