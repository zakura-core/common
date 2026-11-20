//! Four-way AVX2 sums of challenge-product coefficient vectors (see
//! [`super::CoefficientProducts`]).
//!
//! # Blocking
//!
//! A product's coefficient vector factors along the bits of the coefficient
//! index: with the low `k1` rounds and the high `k - k1`,
//! `c[h 2^k1 + l] = A[h] B[l]`, where `B` is the expansion of the low rounds
//! (with `init`) and `A` the expansion of the high rounds (with one). The sum
//! over a batch is computed one block of `2^k1` coefficients at a time:
//! block `h` is `sum_p A_p[h] B_p`, accumulated in a few vector registers'
//! worth of memory that stays in L1, while each proof's `B_p` (computed
//! once, `2^k1` coefficients) streams from L2. This costs `2^k + 2^k1 +
//! 2^(k - k1)` multiplications per proof against `2^k - 1` for a direct
//! expansion, but never writes a full coefficient vector per proof. The
//! blocks are independent and run in parallel under `multicore`.
//!
//! # Arithmetic
//!
//! Every multiplication multiplies lanes by one broadcast factor, prepared
//! once in radix 2^29 and scaled by 2^5, which keeps [`mul`]'s products in the
//! scalar fields' Montgomery domain (see [`super::avx2_chord`]).
//!
//! # Bounds
//!
//! [`mul`] of `a < 2^261` and `b < 2^261` (normalized limbs) is below
//! `a b / 2^261 + p`. Multiplying a value below `B p` by a scaled factor
//! `32 u < 32 p` gives at most `(32 p) (B p) / 2^261 + p = (B p / 2^256 + 1) p`.
//! With `2^254 < p < 2^254 + 2^126`, `p / 2^256` is below `1/4 + 2^-128`, so
//! from canonical inputs (`B = 1`) every value of `B_p` and every product
//! `A_p[h] B_p[l]` stays below `4/3 p + 2^-120 p`, inside [`mul`]'s limits
//! with no reduction. Block sums add products limb-wise without carries:
//! limbs 0 to 7 are below 2^29 and limb 8 below 2^23 per product, so a
//! 64-bit lane overflows only after more than 2^34 proofs. Each block is then
//! normalized, unpacked to 320-bit integers and reduced once per coefficient.
#![allow(unsafe_code)]

use alloc::vec::Vec;
use core::arch::x86_64::*;

use super::avx2_chord::{normalize, shl5, unpack_wide};
use super::avx2_sqrt::{L, V, mul, pack};
use super::coefficient_products::{expand_coefficient_products, sum_coefficient_products_scalar};

/// Rounds per block: `2^7` coefficients, 32 vectors (9 KiB) of block sums.
const BLOCK_ROUNDS: usize = 7;

/// Rounds expanded on the scalar path before a `B` expansion starts in
/// vectors: they produce its first four coefficients, one vector.
const HEAD_ROUNDS: usize = 2;

/// Below this many rounds the portable sum is used: a block must hold at
/// least one full vector round.
const MIN_ROUNDS: usize = HEAD_ROUNDS + 2;

/// Returns the sum of the coefficient vectors of `products` (see
/// [`super::CoefficientProducts::sum_coefficient_products`]). `limbs` returns
/// an element's canonical Montgomery limbs, and `from_limbs` builds an element
/// from them; `modulus` is the field modulus.
pub(crate) fn sum_coefficient_products<
    F: ff::Field,
    const P0: u64,
    const P1: u64,
    const P2: u64,
    const P3: u64,
>(
    products: &[(Vec<F>, F)],
    modulus: &[u64; 4],
    limbs: impl Fn(&F) -> [u64; 4] + Sync,
    from_limbs: impl Fn([u64; 4]) -> F + Sync,
) -> Vec<F> {
    let Some((first, _)) = products.first() else {
        return Vec::new();
    };
    let k = first.len();
    if k < MIN_ROUNDS {
        return sum_coefficient_products_scalar(products);
    }
    let k1 = k.min(BLOCK_ROUNDS);
    let block_vectors = (1usize << k1) / 4;

    // Per proof: `B` in vectors (low rounds, with `init`), and the canonical
    // limbs of `A` (high rounds, with one).
    let prepare = |p: usize| -> (Vec<V>, Vec<[u64; 4]>) {
        let (u, init) = &products[p];
        assert_eq!(u.len(), k, "one challenge per round");
        let (high, low) = u.split_at(k - k1);
        let mut head = Vec::new();
        let (tail, first_rounds) = low.split_at(low.len() - HEAD_ROUNDS);
        // The last challenges are the first rounds (see the expansion order).
        expand_coefficient_products(first_rounds, *init, &mut head);
        let first: [[u64; 4]; 4] = core::array::from_fn(|i| limbs(&head[i]));
        let challenges: Vec<[u64; 4]> = tail.iter().rev().map(&limbs).collect();
        // SAFETY: `pasta_curves_avx2` guarantees AVX2 (see `avx2_sqrt`).
        let b = unsafe { expand_vectors::<P0, P1, P2, P3>(&first, &challenges) };
        let mut a = Vec::new();
        expand_coefficient_products(high, F::ONE, &mut a);
        (b, a.iter().map(&limbs).collect())
    };
    let block = |h: usize, prepared: &[(Vec<V>, Vec<[u64; 4]>)]| -> Vec<F> {
        // SAFETY: `pasta_curves_avx2` guarantees AVX2.
        let sums = unsafe { block_sums::<P0, P1, P2, P3>(prepared, h, block_vectors) };
        let mut out = Vec::with_capacity(4 * block_vectors);
        for v in &sums {
            // SAFETY: as above.
            for lane in unsafe { unpack_wide(&normalize(v.0)) } {
                out.push(from_limbs(reduce_wide(&lane, modulus)));
            }
        }
        out
    };

    let blocks = 1usize << (k - k1);
    #[cfg(feature = "multicore")]
    let (prepared, sums) = {
        let prepared = crate::glv::par_map_indices(products.len(), &prepare);
        let sums = crate::glv::par_map_indices(blocks, &|h| block(h, &prepared));
        (prepared, sums)
    };
    #[cfg(not(feature = "multicore"))]
    let (prepared, sums) = {
        let prepared: Vec<_> = (0..products.len()).map(&prepare).collect();
        let sums: Vec<_> = (0..blocks).map(|h| block(h, &prepared)).collect();
        (prepared, sums)
    };
    drop(prepared);
    sums.concat()
}

/// Expands from the first four coefficients through `challenges` (in round
/// order), keeping every coefficient in vectors below `4/3 p`.
#[target_feature(enable = "avx2")]
fn expand_vectors<const P0: u64, const P1: u64, const P2: u64, const P3: u64>(
    first: &[[u64; 4]; 4],
    challenges: &[[u64; 4]],
) -> Vec<V> {
    let mut vectors = Vec::with_capacity(1 << challenges.len());
    vectors.push(pack(first));
    for u in challenges {
        let u32 = shl5(&pack(&[*u; 4]));
        let len = vectors.len();
        for i in 0..len {
            let product = mul::<P0, P1, P2, P3>(&u32, &vectors[i]);
            vectors.push(product);
        }
    }
    vectors
}

/// Block `h`'s lazily summed products `sum_p A_p[h] B_p`.
#[target_feature(enable = "avx2")]
fn block_sums<const P0: u64, const P1: u64, const P2: u64, const P3: u64>(
    prepared: &[(Vec<V>, Vec<[u64; 4]>)],
    h: usize,
    block_vectors: usize,
) -> Vec<V> {
    let zero = V([_mm256_setzero_si256(); L]);
    let mut sums = alloc::vec![zero; block_vectors];
    for (b, a) in prepared {
        let factor = shl5(&pack(&[a[h]; 4]));
        let mut i = 0;
        while i + 4 <= block_vectors {
            // Four independent products in flight.
            let products = [
                mul::<P0, P1, P2, P3>(&factor, &b[i]),
                mul::<P0, P1, P2, P3>(&factor, &b[i + 1]),
                mul::<P0, P1, P2, P3>(&factor, &b[i + 2]),
                mul::<P0, P1, P2, P3>(&factor, &b[i + 3]),
            ];
            for (sum, product) in sums[i..i + 4].iter_mut().zip(&products) {
                add_lanes(sum, product);
            }
            i += 4;
        }
        for i in i..block_vectors {
            let product = mul::<P0, P1, P2, P3>(&factor, &b[i]);
            add_lanes(&mut sums[i], &product);
        }
    }
    sums
}

#[target_feature(enable = "avx2")]
#[inline]
fn add_lanes(sum: &mut V, value: &V) {
    for (s, v) in sum.0.iter_mut().zip(&value.0) {
        *s = _mm256_add_epi64(*s, *v);
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
