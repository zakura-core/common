//! Four-way AVX2 radix-2 FFT butterflies for the Pasta fields.
//!
//! The decimation-in-time butterflies of `halo2_proofs`' FFT spend their time
//! in one twiddle multiplication per butterfly. This module runs four
//! butterflies at once in the radix-2^29 arithmetic of [`super::avx2_sqrt`]
//! (availability and the AVX2 guarantee are documented there). Only AVX2 is
//! used.
//!
//! A transform converts its values to radix 2^29 once, runs every remaining
//! stage there with the same cache-oblivious, depth-first recursion as the
//! scalar code, and converts back once, so each element is converted twice
//! regardless of the number of stages.
//!
//! # Layout
//!
//! A [`Block`] holds four consecutive elements, limb-major, two 29-bit limbs
//! per 64-bit lane: word `m` of the block holds limbs `2m` (low half) and
//! `2m + 1` (high half) of the four elements, so loading and storing a block
//! is a mask or a shift per limb. A block is 160 bytes (40 bytes per element).
//!
//! # Domain and bounds
//!
//! Values stay in the scalar fields' Montgomery domain (`x 2^256`). Twiddles
//! are stored as the Montgomery form of `32 w` (`w 2^261`), so [`mul`]
//! (`a b / 2^261`) of a value and a twiddle is the scalar Montgomery product
//! `x w 2^256`. [`mul`] is exact when limbs 0 to 7 of both inputs are below
//! 2^29 and both values are below 2^261, and returns less than
//! `a b / 2^261 + p`; `p / 2^261` is below `1/128 (1 + 2^-128)`.
//!
//! Values are kept normalized (limbs 0 to 7 below 2^29) but not reduced. With
//! values below `B p`, `B < 64`, and canonical twiddles, a product is below
//! `1.5 p`; a butterfly outputs `a + t` and `a + 2p - t`, both below
//! `(B + 2) p`. Inputs are canonical, the two in-block stages leave values
//! below `4p`, so after `s` further stages values are below `(4 + 2s) p`.
//! [`MAX_STAGES`] keeps that below `64 p < 2^261`, which [`reduce64`]
//! reduces to canonical form on output.
#![allow(unsafe_code)]

use core::arch::x86_64::*;

use alloc::vec::Vec;

use super::avx2_sqrt::{BITS, L, MASK, V, mul, pasta_limbs29};

/// Stages after the in-block ones; keeps values below `64 p`.
const MAX_STAGES: usize = 29;

/// Four consecutive field elements in radix 2^29 (see the module docs).
#[derive(Clone, Copy, Default)]
#[repr(C, align(32))]
pub struct Block([[u64; 4]; 5]);

impl core::fmt::Debug for Block {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Block").finish_non_exhaustive()
    }
}

/// `c p` in radix 2^29, with limbs 0 to 7 raised to at least `2^30 - 2` by
/// borrowing from the next limb, so it limb-wise dominates any normalized
/// subtrahend whose limb 8 is at most `c 2^22 - 2`. (As in `avx2_chord`.)
const fn kp(p: &[u64; L], c: u64) -> [u64; L] {
    let mut k = [0u64; L];
    let mut i = 0;
    while i < L {
        let received = if i < L - 1 { 1 << (BITS + 1) } else { 0 };
        let lent = if i > 0 { 2 } else { 0 };
        k[i] = c * p[i] + received - lent;
        i += 1;
    }
    k
}

#[target_feature(enable = "avx2")]
#[inline]
fn load(b: &Block) -> V {
    let lo = _mm256_set1_epi64x(0xffff_ffff);
    let mut w = [_mm256_setzero_si256(); 5];
    for (w, src) in w.iter_mut().zip(&b.0) {
        // SAFETY: `Block` is 32-byte aligned and each word is 32 bytes.
        *w = unsafe { _mm256_load_si256(src.as_ptr() as *const __m256i) };
    }
    V([
        _mm256_and_si256(w[0], lo),
        _mm256_srli_epi64::<32>(w[0]),
        _mm256_and_si256(w[1], lo),
        _mm256_srli_epi64::<32>(w[1]),
        _mm256_and_si256(w[2], lo),
        _mm256_srli_epi64::<32>(w[2]),
        _mm256_and_si256(w[3], lo),
        _mm256_srli_epi64::<32>(w[3]),
        w[4],
    ])
}

/// Stores a normalized value below 2^261 (every limb below 2^32).
#[target_feature(enable = "avx2")]
#[inline]
fn store(v: &V, b: &mut Block) {
    let v = &v.0;
    let w = [
        _mm256_or_si256(v[0], _mm256_slli_epi64::<32>(v[1])),
        _mm256_or_si256(v[2], _mm256_slli_epi64::<32>(v[3])),
        _mm256_or_si256(v[4], _mm256_slli_epi64::<32>(v[5])),
        _mm256_or_si256(v[6], _mm256_slli_epi64::<32>(v[7])),
        v[8],
    ];
    for (dst, w) in b.0.iter_mut().zip(w) {
        // SAFETY: `Block` is 32-byte aligned and each word is 32 bytes.
        unsafe { _mm256_store_si256(dst.as_mut_ptr() as *mut __m256i, w) };
    }
}

/// Propagates carries so limbs 0 to 7 are below 2^29.
#[target_feature(enable = "avx2")]
#[inline]
pub(super) fn normalize(mut v: [__m256i; L]) -> V {
    let mask = _mm256_set1_epi64x(MASK as i64);
    for i in 0..L - 1 {
        let carry = _mm256_srli_epi64::<BITS>(v[i]);
        v[i] = _mm256_and_si256(v[i], mask);
        v[i + 1] = _mm256_add_epi64(v[i + 1], carry);
    }
    V(v)
}

/// Normalized `a + b`.
#[target_feature(enable = "avx2")]
#[inline]
fn add(a: &V, b: &V) -> V {
    normalize([
        _mm256_add_epi64(a.0[0], b.0[0]),
        _mm256_add_epi64(a.0[1], b.0[1]),
        _mm256_add_epi64(a.0[2], b.0[2]),
        _mm256_add_epi64(a.0[3], b.0[3]),
        _mm256_add_epi64(a.0[4], b.0[4]),
        _mm256_add_epi64(a.0[5], b.0[5]),
        _mm256_add_epi64(a.0[6], b.0[6]),
        _mm256_add_epi64(a.0[7], b.0[7]),
        _mm256_add_epi64(a.0[8], b.0[8]),
    ])
}

/// Normalized `a + k - b`, for `k` from [`kp`] dominating `b`.
#[target_feature(enable = "avx2")]
#[inline]
fn sub(a: &V, b: &V, k: &[__m256i; L]) -> V {
    let mut t = [_mm256_setzero_si256(); L];
    for i in 0..L {
        t[i] = _mm256_sub_epi64(_mm256_add_epi64(a.0[i], k[i]), b.0[i]);
    }
    normalize(t)
}

/// Reduces a normalized value below `64 p` to `[0, p)`.
///
/// `q = floor(v / 2^254)` (limb 8 shifted by 22) is `floor(v / p)` or one
/// more, because `2^254 < p < 2^254 + 2^128` and `v < 2^261`; so `v - q p`
/// lies in `[-p, p)` and at most one `p` is added back. Limbs 0 to 7 get
/// `2^36` added (borrowed as `2^7` from the next limb) so they stay
/// non-negative for the logical carry shifts (`q p_i < 2^35`); only limb 8
/// carries the sign.
#[target_feature(enable = "avx2")]
#[inline]
pub(super) fn reduce64(v: &V, p: &[u64; L]) -> V {
    let q = _mm256_srli_epi64::<22>(v.0[8]);
    let mut t = [_mm256_setzero_si256(); L];
    for i in 0..L {
        let qp = match i {
            0 => q,
            8 => _mm256_slli_epi64::<22>(q),
            _ => _mm256_mul_epu32(q, _mm256_set1_epi64x(p[i] as i64)),
        };
        let offset: i64 = match i {
            0 => 1 << 36,
            8 => -(1 << 7),
            _ => (1 << 36) - (1 << 7),
        };
        t[i] = _mm256_sub_epi64(_mm256_add_epi64(v.0[i], _mm256_set1_epi64x(offset)), qp);
    }
    let mut t = normalize(t).0;
    let negative = _mm256_cmpgt_epi64(_mm256_setzero_si256(), t[8]);
    for (i, t) in t.iter_mut().enumerate() {
        *t = _mm256_add_epi64(
            *t,
            _mm256_and_si256(negative, _mm256_set1_epi64x(p[i] as i64)),
        );
    }
    normalize(t)
}

/// Transposes a 4x4 matrix of 64-bit words (an involution).
#[target_feature(enable = "avx2")]
#[inline]
fn transpose(r: [__m256i; 4]) -> [__m256i; 4] {
    let t0 = _mm256_unpacklo_epi64(r[0], r[1]);
    let t1 = _mm256_unpackhi_epi64(r[0], r[1]);
    let t2 = _mm256_unpacklo_epi64(r[2], r[3]);
    let t3 = _mm256_unpackhi_epi64(r[2], r[3]);
    [
        _mm256_permute2x128_si256::<0x20>(t0, t2),
        _mm256_permute2x128_si256::<0x20>(t1, t3),
        _mm256_permute2x128_si256::<0x31>(t0, t2),
        _mm256_permute2x128_si256::<0x31>(t1, t3),
    ]
}

/// Loads four consecutive canonical elements (little-endian 64-bit words).
#[target_feature(enable = "avx2")]
#[inline]
pub(super) fn from_words(x: &[[u64; 4]]) -> V {
    debug_assert_eq!(x.len(), 4);
    let mut r = [_mm256_setzero_si256(); 4];
    for (r, src) in r.iter_mut().zip(x) {
        // SAFETY: each `[u64; 4]` is 32 readable bytes.
        *r = unsafe { _mm256_loadu_si256(src.as_ptr() as *const __m256i) };
    }
    let w = transpose(r);
    let m = _mm256_set1_epi64x(MASK as i64);
    V([
        _mm256_and_si256(w[0], m),
        _mm256_and_si256(_mm256_srli_epi64::<29>(w[0]), m),
        _mm256_and_si256(
            _mm256_or_si256(_mm256_srli_epi64::<58>(w[0]), _mm256_slli_epi64::<6>(w[1])),
            m,
        ),
        _mm256_and_si256(_mm256_srli_epi64::<23>(w[1]), m),
        _mm256_and_si256(
            _mm256_or_si256(_mm256_srli_epi64::<52>(w[1]), _mm256_slli_epi64::<12>(w[2])),
            m,
        ),
        _mm256_and_si256(_mm256_srli_epi64::<17>(w[2]), m),
        _mm256_and_si256(
            _mm256_or_si256(_mm256_srli_epi64::<46>(w[2]), _mm256_slli_epi64::<18>(w[3])),
            m,
        ),
        _mm256_and_si256(_mm256_srli_epi64::<11>(w[3]), m),
        _mm256_srli_epi64::<40>(w[3]),
    ])
}

/// Stores four canonical values (limbs 0 to 7 below 2^29, limb 8 below 2^23)
/// as little-endian 64-bit words.
#[target_feature(enable = "avx2")]
#[inline]
pub(super) fn to_words(v: &V, x: &mut [[u64; 4]]) {
    debug_assert_eq!(x.len(), 4);
    let l = &v.0;
    let w = [
        _mm256_or_si256(
            _mm256_or_si256(l[0], _mm256_slli_epi64::<29>(l[1])),
            _mm256_slli_epi64::<58>(l[2]),
        ),
        _mm256_or_si256(
            _mm256_or_si256(_mm256_srli_epi64::<6>(l[2]), _mm256_slli_epi64::<23>(l[3])),
            _mm256_slli_epi64::<52>(l[4]),
        ),
        _mm256_or_si256(
            _mm256_or_si256(_mm256_srli_epi64::<12>(l[4]), _mm256_slli_epi64::<17>(l[5])),
            _mm256_slli_epi64::<46>(l[6]),
        ),
        _mm256_or_si256(
            _mm256_or_si256(_mm256_srli_epi64::<18>(l[6]), _mm256_slli_epi64::<11>(l[7])),
            _mm256_slli_epi64::<40>(l[8]),
        ),
    ];
    let r = transpose(w);
    for (dst, r) in x.iter_mut().zip(r) {
        // SAFETY: each `[u64; 4]` is 32 writable bytes.
        unsafe { _mm256_storeu_si256(dst.as_mut_ptr() as *mut __m256i, r) };
    }
}

/// Converts canonical Montgomery limbs to a broadcastable radix-2^29 value.
const fn limbs29(x: &[u64; 4]) -> [u64; L] {
    let mut out = [0u64; L];
    let mut i = 0;
    while i < L {
        let bit = i * BITS as usize;
        let (w, s) = (bit / 64, bit % 64);
        let mut v = x[w] >> s;
        if s + BITS as usize > 64 && w + 1 < 4 {
            v |= x[w + 1] << (64 - s);
        }
        out[i] = v & MASK;
        i += 1;
    }
    out
}

/// Packs four canonical values into a [`Block`] (scalar; used for tables).
fn block_of(x: [[u64; 4]; 4]) -> Block {
    let l = x.map(|x| limbs29(&x));
    let mut b = Block::default();
    for m in 0..5 {
        for (lane, l) in l.iter().enumerate() {
            let hi = if 2 * m + 1 < L { l[2 * m + 1] } else { 0 };
            b.0[m][lane] = l[2 * m] | (hi << 32);
        }
    }
    b
}

/// Twiddles of one transform length in radix 2^29.
///
/// Level `l` (a node of length `n / 2^l`, half `h`) needs twiddles
/// `w^(j 2^l)` for `j < h`; levels with `h >= 4` are stored as blocks, and the
/// in-block length-4 node uses `quarter = w^(n / 4)`.
#[derive(Clone, Default)]
pub struct Twiddles {
    log_n: u32,
    levels: Vec<Vec<Block>>,
    quarter: [u64; 4],
    one: [u64; 4],
}

impl core::fmt::Debug for Twiddles {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Twiddles")
            .field("log_n", &self.log_n)
            .finish_non_exhaustive()
    }
}

impl Twiddles {
    /// Builds the tables from `twiddles[j] = w^j` (`j < n / 2`), given each
    /// twiddle's canonical Montgomery limbs scaled by 32 (`scaled`).
    pub(crate) fn new(n: usize, scaled: impl Fn(usize) -> [u64; 4], one: [u64; 4]) -> Self {
        assert!(n.is_power_of_two() && n >= 8);
        let log_n = n.trailing_zeros();
        let mut levels = Vec::new();
        let mut half = n / 2;
        let mut stride = 1;
        while half >= 4 {
            levels.push(
                (0..half / 4)
                    .map(|b| block_of(core::array::from_fn(|lane| scaled((4 * b + lane) * stride))))
                    .collect(),
            );
            half /= 2;
            stride *= 2;
        }
        Twiddles {
            log_n,
            levels,
            quarter: scaled(n / 4),
            one,
        }
    }

    /// The transform length.
    pub(crate) fn len(&self) -> usize {
        1 << self.log_n
    }
}

/// Reusable radix-2^29 buffer for [`butterflies`].
#[derive(Debug, Default)]
pub struct Scratch(Vec<Block>);

/// Runs the decimation-in-time butterflies of a node at `level` (length
/// `values.len() = n / 2^level`) whose sub-nodes of length `completed` are
/// already transformed, exactly as `halo2_proofs`' scalar recursion does.
///
/// `values` holds canonical Montgomery limbs and receives canonical outputs.
/// Returns `false`, without touching `values`, for shapes this kernel does
/// not cover (nodes shorter than 16, or `completed` of 4 to 8 elements below
/// length 16 — callers then use the scalar path).
#[target_feature(enable = "avx2")]
pub(crate) fn butterflies<const P0: u64, const P1: u64, const P2: u64, const P3: u64>(
    values: &mut [[u64; 4]],
    completed: usize,
    level: usize,
    tw: &Twiddles,
    scratch: &mut Scratch,
) -> bool {
    let p = const { pasta_limbs29(&[P0, P1, P2, P3]) };
    let len = values.len();
    if !len.is_power_of_two()
        || len < 16
        || !completed.is_power_of_two()
        || completed > len
        || len << level != tw.len()
    {
        return false;
    }
    if completed == len {
        return true;
    }
    let stages = (len / completed.max(4)).trailing_zeros() as usize;
    if stages > MAX_STAGES {
        return false;
    }

    let k2c = const { kp(&pasta_limbs29(&[P0, P1, P2, P3]), 2) };
    let mut k2 = [_mm256_setzero_si256(); L];
    for i in 0..L {
        k2[i] = _mm256_set1_epi64x(k2c[i] as i64);
    }

    // Convert in, running the in-block stages (lengths 2 and 4) when needed.
    let blocks = &mut scratch.0;
    blocks.clear();
    blocks.resize(len / 4, Block::default());
    let one = limbs29(&tw.one);
    let quarter = limbs29(&tw.quarter);
    let mut w4 = V([_mm256_setzero_si256(); L]);
    for i in 0..L {
        w4.0[i] = _mm256_set_epi64x(
            quarter[i] as i64,
            one[i] as i64,
            one[i] as i64,
            one[i] as i64,
        );
    }
    for (block, x) in blocks.iter_mut().zip(values.chunks_exact(4)) {
        let mut v = from_words(x);
        if completed == 1 {
            // Length 2: (x0 + x1, x0 - x1, x2 + x3, x2 - x3).
            let (mut a, mut b) = (v, v);
            for i in 0..L {
                a.0[i] = _mm256_permute4x64_epi64::<0b10_10_00_00>(v.0[i]);
                b.0[i] = _mm256_permute4x64_epi64::<0b11_11_01_01>(v.0[i]);
            }
            let s = add(&a, &b);
            let d = sub(&a, &b, &k2);
            for i in 0..L {
                v.0[i] = _mm256_blend_epi32::<0b1100_1100>(s.0[i], d.0[i]);
            }
        }
        if completed <= 2 {
            // Length 4: (y0 + y2, y1 + w y3, y0 - y2, y1 - w y3), with
            // every lane multiplied (by one or w) so all are reduced.
            let m = mul::<P0, P1, P2, P3>(&v, &w4);
            let (mut a, mut b) = (m, m);
            for i in 0..L {
                a.0[i] = _mm256_permute4x64_epi64::<0b01_00_01_00>(m.0[i]);
                b.0[i] = _mm256_permute4x64_epi64::<0b11_10_11_10>(m.0[i]);
            }
            let s = add(&a, &b);
            let d = sub(&a, &b, &k2);
            for i in 0..L {
                v.0[i] = _mm256_blend_epi32::<0b1111_0000>(s.0[i], d.0[i]);
            }
        }
        store(&v, block);
    }

    recurse::<P0, P1, P2, P3>(blocks, completed.max(4) / 4, level, &tw.levels, &k2);

    for (block, x) in blocks.iter().zip(values.chunks_exact_mut(4)) {
        to_words(&reduce64(&load(block), &p), x);
    }
    true
}

/// Whether [`zero_padded`] covers `n = 2^log_n` coefficients for `tw`.
pub(crate) fn zero_padded_applies(log_n: u32, tw: &Twiddles) -> bool {
    let n = 1usize << log_n;
    tw.log_n >= log_n + 2 && n >= 2 && (log_n as usize) <= MAX_STAGES + 1
}

/// The forward FFT of `n = 2^log_n` coefficients zero-padded to the
/// transform length `N = tw.len()`, as `halo2_proofs`'
/// `fft_zero_padded_with_twiddles` computes it: the first retained stage
/// (nodes of length `2E`, `E = N / n`) is materialized directly from the
/// bit-reversed coefficient pairs, then the remaining `log_n - 1` stages run
/// as in [`butterflies`].
///
/// `values` has length `N`; its first `n` entries are the coefficients
/// (canonical Montgomery limbs, natural order), and it receives the canonical
/// evaluations. The caller checks [`zero_padded_applies`] first.
#[target_feature(enable = "avx2")]
pub(crate) fn zero_padded<const P0: u64, const P1: u64, const P2: u64, const P3: u64>(
    values: &mut [[u64; 4]],
    log_n: u32,
    tw: &Twiddles,
    scratch: &mut Scratch,
) {
    let p = const { pasta_limbs29(&[P0, P1, P2, P3]) };
    assert!(zero_padded_applies(log_n, tw));
    let n = 1usize << log_n;
    let big = tw.len();
    assert_eq!(values.len(), big);
    let ext = big / n;

    let k2c = const { kp(&pasta_limbs29(&[P0, P1, P2, P3]), 2) };
    let mut k2 = [_mm256_setzero_si256(); L];
    for i in 0..L {
        k2[i] = _mm256_set1_epi64x(k2c[i] as i64);
    }

    let blocks = &mut scratch.0;
    blocks.clear();
    blocks.resize(big / 4, Block::default());
    // Node length 2E sits at level log2(N / 2E) = log_n - 1; its twiddles
    // are w^(j n / 2) for j < E.
    let first = (log_n - 1) as usize;
    let table = &tw.levels[first];
    debug_assert_eq!(table.len(), ext / 4);
    let reverse = |i: usize| i.reverse_bits() >> (usize::BITS - log_n);
    for (pair, out) in blocks.chunks_exact_mut(ext / 2).enumerate() {
        let left = limbs29(&values[reverse(2 * pair)]);
        let right = limbs29(&values[reverse(2 * pair + 1)]);
        let mut a = V([_mm256_setzero_si256(); L]);
        let mut b = V([_mm256_setzero_si256(); L]);
        for i in 0..L {
            a.0[i] = _mm256_set1_epi64x(left[i] as i64);
            b.0[i] = _mm256_set1_epi64x(right[i] as i64);
        }
        let (lo, hi) = out.split_at_mut(ext / 4);
        for ((lo, hi), w) in lo.iter_mut().zip(hi.iter_mut()).zip(table) {
            let t = mul::<P0, P1, P2, P3>(&b, &load(w));
            store(&add(&a, &t), lo);
            store(&sub(&a, &t, &k2), hi);
        }
    }

    recurse::<P0, P1, P2, P3>(blocks, ext / 2, 0, &tw.levels, &k2);

    for (block, x) in blocks.iter().zip(values.chunks_exact_mut(4)) {
        to_words(&reduce64(&load(block), &p), x);
    }
}

/// The depth-first recursion of the scalar code over blocks, combining two
/// levels per pass (radix 4) where two remain: a node `[Q0 Q1 Q2 Q3]` of
/// quarters runs the level-`l + 1` butterflies of `(Q0, Q1)` and `(Q2, Q3)`
/// and then the level-`l` butterflies of `(Q0 Q1, Q2 Q3)` with each block
/// loaded and stored once. Every value still passes one butterfly per level,
/// so the bounds of the module docs are unchanged.
#[target_feature(enable = "avx2")]
fn recurse<const P0: u64, const P1: u64, const P2: u64, const P3: u64>(
    blocks: &mut [Block],
    completed: usize,
    level: usize,
    levels: &[Vec<Block>],
    k2: &[__m256i; L],
) {
    let n = blocks.len();
    if n == completed {
        return;
    }
    if n / 2 == completed {
        let (left, right) = blocks.split_at_mut(n / 2);
        let table = &levels[level];
        debug_assert_eq!(table.len(), left.len());
        for ((l, r), w) in left.iter_mut().zip(right.iter_mut()).zip(table) {
            let a = load(l);
            let t = mul::<P0, P1, P2, P3>(&load(r), &load(w));
            store(&add(&a, &t), l);
            store(&sub(&a, &t, k2), r);
        }
        return;
    }

    let q = n / 4;
    let (half0, half1) = blocks.split_at_mut(n / 2);
    let (q0, q1) = half0.split_at_mut(q);
    let (q2, q3) = half1.split_at_mut(q);
    if q > completed {
        recurse::<P0, P1, P2, P3>(q0, completed, level + 2, levels, k2);
        recurse::<P0, P1, P2, P3>(q1, completed, level + 2, levels, k2);
        recurse::<P0, P1, P2, P3>(q2, completed, level + 2, levels, k2);
        recurse::<P0, P1, P2, P3>(q3, completed, level + 2, levels, k2);
    }
    let inner = &levels[level + 1];
    let (outer_lo, outer_hi) = levels[level].split_at(q);
    debug_assert_eq!(inner.len(), q);
    for (((((b0, b1), b2), b3), w1), (w0, w0h)) in q0
        .iter_mut()
        .zip(q1.iter_mut())
        .zip(q2.iter_mut())
        .zip(q3.iter_mut())
        .zip(inner)
        .zip(outer_lo.iter().zip(outer_hi))
    {
        let w1 = load(w1);
        let a = load(b0);
        let t = mul::<P0, P1, P2, P3>(&load(b1), &w1);
        let a1 = add(&a, &t);
        let b1v = sub(&a, &t, k2);
        let c = load(b2);
        let t = mul::<P0, P1, P2, P3>(&load(b3), &w1);
        let c1 = add(&c, &t);
        let d1 = sub(&c, &t, k2);
        let t = mul::<P0, P1, P2, P3>(&c1, &load(w0));
        store(&add(&a1, &t), b0);
        store(&sub(&a1, &t, k2), b2);
        let t = mul::<P0, P1, P2, P3>(&d1, &load(w0h));
        store(&add(&b1v, &t), b1);
        store(&sub(&b1v, &t, k2), b3);
    }
}

/// A Pasta field whose FFT butterflies can run in [`butterflies`].
pub(crate) trait Avx2FftField: ff::PrimeField + 'static {
    /// Canonical Montgomery limbs.
    fn fft_limbs(&self) -> [u64; 4];
    /// [`butterflies`] for this field.
    fn fft_butterflies(
        values: &mut [Self],
        completed: usize,
        level: usize,
        tw: &Twiddles,
        scratch: &mut Scratch,
    ) -> bool;
    /// [`zero_padded`] for this field; `values` has the transform length.
    fn fft_zero_padded(values: &mut [Self], log_n: u32, tw: &Twiddles, scratch: &mut Scratch);
}

/// Builds [`Twiddles`] from a scalar table `twiddles[j] = w^j`, `j < n / 2`.
pub(crate) fn twiddles_for<F: Avx2FftField>(twiddles: &[F]) -> Option<Twiddles> {
    let n = twiddles.len() * 2;
    if !n.is_power_of_two() || n < 16 {
        return None;
    }
    let thirty_two = F::from(32);
    Some(Twiddles::new(
        n,
        |j| (twiddles[j] * thirty_two).fft_limbs(),
        thirty_two.fft_limbs(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Fp, Fq};
    use ff::{Field, PrimeField};
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    /// The scalar DIT recursion of `halo2_proofs` (after the bit reversal).
    fn reference<F: Field>(v: &mut [F], completed: usize, chunk: usize, tw: &[F]) {
        let n = v.len();
        if n == completed {
            return;
        }
        let (l, r) = v.split_at_mut(n / 2);
        if n / 2 > completed {
            reference(l, completed, chunk * 2, tw);
            reference(r, completed, chunk * 2, tw);
        }
        for (j, (a, b)) in l.iter_mut().zip(r.iter_mut()).enumerate() {
            let t = *b * tw[j * chunk];
            *b = *a - t;
            *a += t;
        }
    }

    fn check<F: Avx2FftField + PrimeField>(log_n: u32) {
        let n = 1usize << log_n;
        let mut omega = F::ROOT_OF_UNITY;
        for _ in log_n..F::S {
            omega = omega.square();
        }
        let tw: Vec<F> = (0..n / 2).map(|j| omega.pow_vartime([j as u64])).collect();
        let tables = twiddles_for(&tw).unwrap();
        let mut rng = XorShiftRng::from_seed([7; 16]);
        let mut scratch = Scratch::default();
        for completed in [1usize, 2, 4, 16, 32] {
            for level in 0..3usize {
                let len = n >> level;
                if len < 16 || completed > len {
                    continue;
                }
                let mut values: Vec<F> = (0..len)
                    .map(|i| match i % 7 {
                        0 => -F::ONE,
                        1 => F::ZERO,
                        _ => F::random(&mut rng),
                    })
                    .collect();
                let mut expected = values.clone();
                reference(&mut expected, completed, 1 << level, &tw);
                assert!(F::fft_butterflies(
                    &mut values,
                    completed,
                    level,
                    &tables,
                    &mut scratch
                ));
                assert!(
                    values == expected,
                    "log_n {log_n} completed {completed} level {level}"
                );
            }
        }
    }

    #[test]
    fn butterflies_match_scalar() {
        for log_n in 4..=12 {
            check::<Fp>(log_n);
            check::<Fq>(log_n);
        }
    }

    fn check_zero_padded<F: Avx2FftField + PrimeField>(log_n: u32, extended_log_n: u32) {
        let n = 1usize << log_n;
        let big = 1usize << extended_log_n;
        let ext = big / n;
        let mut omega = F::ROOT_OF_UNITY;
        for _ in extended_log_n..F::S {
            omega = omega.square();
        }
        let tw: Vec<F> = (0..big / 2)
            .map(|j| omega.pow_vartime([j as u64]))
            .collect();
        let tables = twiddles_for(&tw).unwrap();
        let mut rng = XorShiftRng::from_seed([9; 16]);
        let coefficients: Vec<F> = (0..n)
            .map(|i| {
                if i % 5 == 0 {
                    -F::ONE
                } else {
                    F::random(&mut rng)
                }
            })
            .collect();
        // The scalar prefix of `fft_zero_padded_with_twiddles`.
        let rev = |i: usize| i.reverse_bits() >> (usize::BITS - log_n);
        let mut expected = Vec::with_capacity(big);
        for pair in 0..n / 2 {
            let (l, r) = (coefficients[rev(2 * pair)], coefficients[rev(2 * pair + 1)]);
            let mut hi = Vec::new();
            for j in 0..ext {
                let t = r * tw[j * (n / 2)];
                expected.push(l + t);
                hi.push(l - t);
            }
            expected.extend(hi);
        }
        reference(&mut expected, 2 * ext, 1, &tw);
        assert!(zero_padded_applies(log_n, &tables));
        let mut values = coefficients;
        values.resize(big, F::ZERO);
        F::fft_zero_padded(&mut values, log_n, &tables, &mut Scratch::default());
        assert!(
            values == expected,
            "log_n {log_n} extended {extended_log_n}"
        );
    }

    #[test]
    fn zero_padded_matches_scalar() {
        for (log_n, ext) in [(1, 3), (2, 2), (3, 3), (6, 2), (8, 3), (11, 3), (9, 5)] {
            check_zero_padded::<Fp>(log_n, log_n + ext);
            check_zero_padded::<Fq>(log_n, log_n + ext);
        }
    }

    /// All-maximal inputs (`p - 1`) exercise the largest bounds.
    #[test]
    fn butterflies_at_maximal_inputs() {
        fn go<F: Avx2FftField + PrimeField>() {
            let log_n = 14;
            let n = 1usize << log_n;
            let mut omega = F::ROOT_OF_UNITY;
            for _ in log_n..F::S {
                omega = omega.square();
            }
            let tw: Vec<F> = (0..n / 2).map(|j| omega.pow_vartime([j as u64])).collect();
            let tables = twiddles_for(&tw).unwrap();
            let mut values = vec![-F::ONE; n];
            let mut expected = values.clone();
            reference(&mut expected, 1, 1, &tw);
            assert!(F::fft_butterflies(
                &mut values,
                1,
                0,
                &tables,
                &mut Scratch::default()
            ));
            assert!(values == expected);
        }
        go::<Fp>();
        go::<Fq>();
    }
}
