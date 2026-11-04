//! This module provides common utilities, traits and structures for group,
//! field and polynomial arithmetic.

pub use ff::Field;
use group::{
    Group as _, GroupOpsOwned, ScalarMulOwned,
    ff::{BatchInvert, PrimeField},
};
pub use pasta_curves::arithmetic::*;

use crate::multicore;

/// This represents an element of a group with basic operations that can be
/// performed. This allows an FFT implementation (for example) to operate
/// generically over either a field or elliptic curve group.
pub trait FftGroup<Scalar: Field>:
    Copy + Send + Sync + 'static + GroupOpsOwned + ScalarMulOwned<Scalar>
{
}

impl<T, Scalar> FftGroup<Scalar> for T
where
    Scalar: Field,
    T: Copy + Send + Sync + 'static + GroupOpsOwned + ScalarMulOwned<Scalar>,
{
}

/// Extension trait for batch-inverting field elements and multiplying every
/// inverse by a common scale.
#[cfg(any(test, feature = "batch"))]
pub(crate) trait BatchInvertAndScale<F: Field> {
    /// Like [`BatchInvert::batch_invert`], but multiplies every nonzero inverse
    /// by `scale`. Zero-valued elements remain zero.
    ///
    /// For nonzero inputs `x_i`, this replaces each input with
    /// `scale * x_i.invert()`. The same `scale` is applied to every inverse;
    /// distinct per-element scales cannot be fused into the shared backward
    /// pass.
    ///
    /// Returns the inverse of the product of all nonzero field elements,
    /// without the scale applied.
    fn batch_inverse_and_scale(self, scale: F) -> F;
}

#[cfg(any(test, feature = "batch"))]
impl<'a, F, I> BatchInvertAndScale<F> for I
where
    F: Field,
    I: IntoIterator<Item = &'a mut F>,
{
    fn batch_inverse_and_scale(self, scale: F) -> F {
        let mut iter = self.into_iter();
        let Some(first) = iter.next() else {
            return F::ONE;
        };
        let first_value = *first;
        let first_is_zero = first_value.is_zero();
        let mut acc = F::conditional_select(&first_value, &F::ONE, first_is_zero);
        let mut products = Vec::with_capacity(iter.size_hint().0);
        for value in iter {
            let current = *value;
            products.push((acc, value));
            acc = F::conditional_select(&(acc * current), &acc, current.is_zero());
        }

        acc = acc.invert().unwrap();
        let product_inverse = acc;

        // Applying the scale once here carries it through the backward pass,
        // instead of multiplying every resulting inverse separately.
        acc *= scale;
        for (product, value) in products.into_iter().rev() {
            let skip = value.is_zero();
            let inverse = product * acc;
            acc = F::conditional_select(&(acc * *value), &acc, skip);
            *value = F::conditional_select(&inverse, value, skip);
        }

        // The first prefix is one, and the accumulator is dead after
        // producing its inverse, so both endpoint multiplications are
        // unnecessary.
        let inverse = F::conditional_select(&acc, &*first, first_is_zero);
        *first = inverse;

        product_inverse
    }
}

/// Performs a small multi-exponentiation operation.
/// Uses the double-and-add algorithm with doublings shared across points.
///
/// # Timing
///
/// This function is variable-time with respect to `coeffs` and intermediate
/// curve points. Callers must explicitly accept timing leakage when the
/// coefficients are secret.
pub fn small_multiexp<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    let coeffs: Vec<_> = coeffs.iter().map(|a| a.to_repr()).collect();
    let mut acc = C::Curve::identity();

    // for byte idx
    for byte_idx in (0..32).rev() {
        // for bit idx
        for bit_idx in (0..8).rev() {
            acc = acc.double();
            // for each coeff
            for coeff_idx in 0..coeffs.len() {
                let byte = coeffs[coeff_idx].as_ref()[byte_idx];
                if ((byte >> bit_idx) & 1) != 0 {
                    acc += bases[coeff_idx];
                }
            }
        }
    }

    acc
}

/// Performs a multi-exponentiation operation.
///
/// This function will panic if coeffs and bases have a different length.
///
/// This will use multithreading if beneficial. It forwards to
/// [`pasta_curves::arithmetic::best_multiexp_vartime`], which halo2 shares
/// with RedPallas batch verification.
///
/// # Timing
///
/// This function is variable-time with respect to `coeffs` and intermediate
/// curve points. Halo proof creation uses it with witness- and
/// blinding-derived coefficients and explicitly accepts that timing leakage.
pub fn best_multiexp<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    assert_eq!(coeffs.len(), bases.len());
    pasta_curves::arithmetic::best_multiexp_vartime(coeffs, bases)
}

/// Performs a radix-$2$ Fast-Fourier Transformation (FFT) on a vector of size
/// $n = 2^k$, when provided `log_n` = $k$ and an element of multiplicative
/// order $n$ called `omega` ($\omega$). The result is that the vector `a`, when
/// interpreted as the coefficients of a polynomial of degree $n - 1$, is
/// transformed into the evaluations of this polynomial at each of the $n$
/// distinct powers of $\omega$. This transformation is invertible by providing
/// $\omega^{-1}$ in place of $\omega$ and dividing each resulting field element
/// by $n$.
///
/// This will use multithreading if beneficial.
pub fn best_fft<Scalar: Field, G: FftGroup<Scalar>>(a: &mut [G], omega: Scalar, log_n: u32) {
    fn bitreverse(mut n: usize, l: usize) -> usize {
        let mut r = 0;
        for _ in 0..l {
            r = (r << 1) | (n & 1);
            n >>= 1;
        }
        r
    }

    let threads = multicore::current_num_threads();
    let log_threads = log2_floor(threads);
    let n = a.len();
    assert_eq!(n, 1 << log_n);

    for k in 0..n {
        let rk = bitreverse(k, log_n as usize);
        if k < rk {
            a.swap(rk, k);
        }
    }

    // precompute twiddle factors
    let twiddles: Vec<_> = (0..(n / 2))
        .scan(Scalar::ONE, |w, _| {
            let tw = *w;
            *w *= &omega;
            Some(tw)
        })
        .collect();

    if log_n <= log_threads {
        let mut chunk = 2_usize;
        let mut twiddle_chunk = n / 2;
        for _ in 0..log_n {
            a.chunks_mut(chunk).for_each(|coeffs| {
                let (left, right) = coeffs.split_at_mut(chunk / 2);

                // case when twiddle factor is one
                let (a, left) = left.split_at_mut(1);
                let (b, right) = right.split_at_mut(1);
                let t = b[0];
                b[0] = a[0];
                a[0] += &t;
                b[0] -= &t;

                left.iter_mut()
                    .zip(right.iter_mut())
                    .enumerate()
                    .for_each(|(i, (a, b))| {
                        let mut t = *b;
                        t *= &twiddles[(i + 1) * twiddle_chunk];
                        *b = *a;
                        *a += &t;
                        *b -= &t;
                    });
            });
            chunk *= 2;
            twiddle_chunk /= 2;
        }
    } else {
        recursive_butterfly_arithmetic(a, n, 1, &twiddles)
    }
}

/// This perform recursive butterfly arithmetic
pub fn recursive_butterfly_arithmetic<Scalar: Field, G: FftGroup<Scalar>>(
    a: &mut [G],
    n: usize,
    twiddle_chunk: usize,
    twiddles: &[Scalar],
) {
    if n == 2 {
        let t = a[1];
        a[1] = a[0];
        a[0] += &t;
        a[1] -= &t;
    } else {
        let (left, right) = a.split_at_mut(n / 2);
        multicore::join(
            || recursive_butterfly_arithmetic(left, n / 2, twiddle_chunk * 2, twiddles),
            || recursive_butterfly_arithmetic(right, n / 2, twiddle_chunk * 2, twiddles),
        );

        // case when twiddle factor is one
        let (a, left) = left.split_at_mut(1);
        let (b, right) = right.split_at_mut(1);
        let t = b[0];
        b[0] = a[0];
        a[0] += &t;
        b[0] -= &t;

        left.iter_mut()
            .zip(right.iter_mut())
            .enumerate()
            .for_each(|(i, (a, b))| {
                let mut t = *b;
                t *= &twiddles[(i + 1) * twiddle_chunk];
                *b = *a;
                *a += &t;
                *b -= &t;
            });
    }
}

/// This evaluates a provided polynomial (in coefficient form) at `point`.
pub fn eval_polynomial<F: Field>(poly: &[F], point: F) -> F {
    // TODO: parallelize?
    poly.iter()
        .rev()
        .fold(F::ZERO, |acc, coeff| acc * point + coeff)
}

/// This computes the inner product of two vectors `a` and `b`.
///
/// This function will panic if the two vectors are not the same size.
pub fn compute_inner_product<F: Field>(a: &[F], b: &[F]) -> F {
    // TODO: parallelize?
    assert_eq!(a.len(), b.len());

    let mut acc = F::ZERO;
    for (a, b) in a.iter().zip(b.iter()) {
        acc += (*a) * (*b);
    }

    acc
}

/// Divides polynomial `a` in `X` by `X - b` with
/// no remainder.
pub fn kate_division<'a, F: Field, I: IntoIterator<Item = &'a F>>(a: I, mut b: F) -> Vec<F>
where
    I::IntoIter: DoubleEndedIterator + ExactSizeIterator,
{
    b = -b;
    let a = a.into_iter();

    let mut q = vec![F::ZERO; a.len() - 1];

    let mut tmp = F::ZERO;
    for (q, r) in q.iter_mut().rev().zip(a.rev()) {
        let mut lead_coeff = *r;
        lead_coeff.sub_assign(&tmp);
        *q = lead_coeff;
        tmp = lead_coeff;
        tmp.mul_assign(&b);
    }

    q
}

/// Batches below this length use the single-chain algorithm: measured on
/// x86-64 (EPYC Zen 4, portable arithmetic), the two-lane variant's fixed
/// overhead (three extra multiplications) and lane bookkeeping only pay for
/// themselves from ~32 elements; on Apple aarch64 with the assembly backend
/// two lanes win at every measured size, but by under 2% below 32 elements,
/// so one shared threshold serves both.
pub(crate) const BATCH_INVERT_TWO_LANE_MIN: usize = 32;

/// In-place batch inversion. Zero elements are skipped (left as zero) —
/// the same outputs as `ff::BatchInverter` — with **variable-time** zero
/// detection. Correctness never assumes zeros are absent: a zero element
/// stays zero and never enters the shared product. The vartime posture is
/// justified because both call sites invert challenge-blinded products
/// (zeros are negligibly likely, so the skip branch is never taken in
/// practice and predicts perfectly), and this crate's `Field::invert` is
/// already variable-time in its input (see the pasta_curves changelog), so
/// constant-time skipping would spend selects protecting a channel the
/// shared inversion already leaks.
///
/// Twin implementations — keep them in step when changing any:
/// `batch_invert_nonzero` in `pasta_curves/src/glv.rs` is the same
/// even/odd two-lane walk without zero handling (the GLV ladder proves its
/// denominators nonzero) and with caller-owned scratch reused across
/// calls; `Curve::batch_normalize` in `pasta_curves/src/curves.rs` fuses
/// the same walk with the Jacobian-to-affine conversion (its output array
/// doubles as the prefix store, so it needs no scratch).
///
/// The classic Montgomery walk runs one serial multiplication chain forward
/// (prefix products) and one backward (substitution), so both passes run at
/// the field multiplication's dependency latency. From
/// [`BATCH_INVERT_TWO_LANE_MIN`] elements, even- and odd-indexed elements
/// instead run two independent chains (throughput-bound), joined around a
/// single shared inversion, for a fixed overhead of three multiplications
/// per call.
pub(crate) fn batch_invert_multi<F: Field>(values: &mut [F]) {
    // At the backward step for element `i`, both the original value (to
    // extend the running inverse) and the prefix product before it (to form
    // the answer) are needed, so an in-place walk requires one auxiliary
    // slot per element.
    let mut scratch = vec![F::ZERO; values.len()];

    if values.len() < BATCH_INVERT_TWO_LANE_MIN {
        let Some((first, values)) = values.split_first_mut() else {
            return;
        };
        let first_is_zero = first.is_zero_vartime();
        let mut acc = if first_is_zero { F::ONE } else { *first };
        for (value, slot) in values.iter().zip(scratch[1..].iter_mut()) {
            *slot = acc;
            if !value.is_zero_vartime() {
                acc *= value;
            }
        }
        // Skipped elements never enter the product, so this cannot fail.
        let mut acc = acc.invert().unwrap();
        for (value, slot) in values.iter_mut().zip(scratch[1..].iter()).rev() {
            if !value.is_zero_vartime() {
                let inverted = acc * slot;
                acc *= *value;
                *value = inverted;
            }
        }
        if !first_is_zero {
            *first = acc;
        }
        return;
    }

    // Two-lane walk, stepped in (even, odd) pairs so the independent chains
    // are explicit. A trailing element (odd length) has an even index and
    // belongs to the first lane.
    let mut acc0 = F::ONE;
    let mut acc1 = F::ONE;
    for (pair, slots) in values.chunks_exact(2).zip(scratch.chunks_exact_mut(2)) {
        slots[0] = acc0;
        if !pair[0].is_zero_vartime() {
            acc0 *= pair[0];
        }
        slots[1] = acc1;
        if !pair[1].is_zero_vartime() {
            acc1 *= pair[1];
        }
    }
    if let (Some(value), Some(slot)) = (
        values.chunks_exact(2).remainder().first(),
        scratch.chunks_exact_mut(2).into_remainder().first_mut(),
    ) {
        *slot = acc0;
        if !value.is_zero_vartime() {
            acc0 *= value;
        }
    }

    // Join the lane products around one shared inversion, then recover each
    // lane's inverse seed.
    let inverse = (acc0 * acc1).invert().unwrap();
    let seed0 = inverse * acc1;
    let seed1 = inverse * acc0;
    let mut acc0 = seed0;
    let mut acc1 = seed1;

    // The odd tail is the highest index, so the backward walk visits it
    // before the pairs.
    if let (Some(value), Some(slot)) = (
        values.chunks_exact_mut(2).into_remainder().first_mut(),
        scratch.chunks_exact(2).remainder().first(),
    ) && !value.is_zero_vartime()
    {
        let inverted = acc0 * slot;
        acc0 *= *value;
        *value = inverted;
    }
    for (pair, slots) in values
        .chunks_exact_mut(2)
        .zip(scratch.chunks_exact(2))
        .rev()
    {
        if !pair[0].is_zero_vartime() {
            let inverted = acc0 * slots[0];
            acc0 *= pair[0];
            pair[0] = inverted;
        }
        if !pair[1].is_zero_vartime() {
            let inverted = acc1 * slots[1];
            acc1 *= pair[1];
            pair[1] = inverted;
        }
    }
}

/// This simple utility function will parallelize an operation that is to be
/// performed over a mutable slice.

pub fn parallelize<T: Send, F: Fn(&mut [T], usize) + Send + Sync + Clone>(v: &mut [T], f: F) {
    // The scheduling below is compiled once per element type rather than once
    // per closure; `f` is called indirectly once per chunk.
    parallelize_dyn(v, &f);
}

fn parallelize_dyn<T: Send>(v: &mut [T], f: &(dyn Fn(&mut [T], usize) + Sync)) {
    let n = v.len();
    let num_threads = multicore::current_num_threads();
    let mut chunk = n / num_threads;
    if chunk < num_threads {
        chunk = n;
    }

    multicore::scope(|scope| {
        for (chunk_num, v) in v.chunks_mut(chunk).enumerate() {
            scope.spawn(move |_| {
                let start = chunk_num * chunk;
                f(v, start);
            });
        }
    });
}

fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow + 1)) <= num {
        pow += 1;
    }

    pow
}

/// Returns coefficients of an n - 1 degree polynomial given a set of n points
/// and their evaluations. This function will panic if two values in `points`
/// are the same.
pub fn lagrange_interpolate<F: Field>(points: &[F], evals: &[F]) -> Vec<F> {
    assert_eq!(points.len(), evals.len());
    if points.len() == 1 {
        // Constant polynomial
        vec![evals[0]]
    } else {
        let mut denoms = Vec::with_capacity(points.len());
        for (j, x_j) in points.iter().enumerate() {
            let mut denom = Vec::with_capacity(points.len() - 1);
            for x_k in points
                .iter()
                .enumerate()
                .filter(|&(k, _)| k != j)
                .map(|a| a.1)
            {
                denom.push(*x_j - x_k);
            }
            denoms.push(denom);
        }
        // Compute (x_j - x_k)^(-1) for each j != i
        denoms.iter_mut().flat_map(|v| v.iter_mut()).batch_invert();

        let mut final_poly = vec![F::ZERO; points.len()];
        for (j, (denoms, eval)) in denoms.into_iter().zip(evals.iter()).enumerate() {
            let mut tmp: Vec<F> = Vec::with_capacity(points.len());
            let mut product = Vec::with_capacity(points.len() - 1);
            tmp.push(F::ONE);
            for (x_k, denom) in points
                .iter()
                .enumerate()
                .filter(|&(k, _)| k != j)
                .map(|a| a.1)
                .zip(denoms)
            {
                product.resize(tmp.len() + 1, F::ZERO);
                for ((a, b), product) in tmp
                    .iter()
                    .chain(std::iter::once(&F::ZERO))
                    .zip(std::iter::once(&F::ZERO).chain(tmp.iter()))
                    .zip(product.iter_mut())
                {
                    *product = *a * (-denom * x_k) + *b * denom;
                }
                std::mem::swap(&mut tmp, &mut product);
            }
            assert_eq!(tmp.len(), points.len());
            assert_eq!(product.len(), points.len() - 1);
            for (final_coeff, interpolation_coeff) in final_poly.iter_mut().zip(tmp) {
                *final_coeff += interpolation_coeff * eval;
            }
        }
        final_poly
    }
}

#[cfg(test)]
use rand::rng;

#[cfg(test)]
use crate::pasta::{Ep, EpAffine, Eq, EqAffine, Fp, Fq};

#[test]
fn test_batch_inverse_and_scale() {
    let original = [Fp::ZERO, Fp::from(2), Fp::from(3), Fp::ZERO, Fp::from(5)];
    let scale = Fp::from(7);
    let mut values = original;

    let product_inverse = values.iter_mut().batch_inverse_and_scale(scale);
    let expected_product = original
        .iter()
        .filter(|value| !value.is_zero_vartime())
        .product::<Fp>()
        .invert()
        .unwrap();

    assert_eq!(product_inverse, expected_product);
    for (value, original) in values.iter().zip(original) {
        let expected = original
            .invert()
            .map(|inverse| inverse * scale)
            .unwrap_or(Fp::ZERO);
        assert_eq!(*value, expected);
    }
}

#[test]
fn test_batch_inverse_and_scale_boundaries() {
    let mut empty: [Fq; 0] = [];
    assert_eq!(
        empty.iter_mut().batch_inverse_and_scale(Fq::from(9)),
        Fq::ONE
    );

    let mut singleton = [Fq::from(4)];
    let singleton_inverse = Fq::from(4).invert().unwrap();
    assert_eq!(
        singleton.iter_mut().batch_inverse_and_scale(Fq::from(9)),
        singleton_inverse
    );
    assert_eq!(singleton, [singleton_inverse * Fq::from(9)]);

    let original = [Fq::ZERO, Fq::from(2), Fq::from(3)];
    let mut scaled = original;
    let product_inverse = scaled.iter_mut().batch_inverse_and_scale(Fq::ZERO);
    assert_eq!(product_inverse, Fq::from(6).invert().unwrap());
    assert_eq!(scaled, [Fq::ZERO; 3]);

    let mut inverted = original;
    let mut expected = original;
    let expected_product_inverse = expected.iter_mut().batch_invert();
    let product_inverse = inverted.iter_mut().batch_inverse_and_scale(Fq::ONE);
    assert_eq!(product_inverse, expected_product_inverse);
    assert_eq!(inverted, expected);
}

#[cfg(test)]
fn assert_multiexp_matches_naive<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) {
    let expected = coeffs
        .iter()
        .zip(bases)
        .map(|(coeff, base)| *base * coeff)
        .fold(C::Curve::identity(), |acc, val| acc + val);

    assert_eq!(best_multiexp(coeffs, bases), expected);
}

#[test]
fn test_multiexp() {
    let mut rng = rng();
    for len in [0, 1, 2, 3, 4, 31, 32, 33, 255, 256, 257] {
        let coeffs = (0..len).map(|_| Fp::random(&mut rng)).collect::<Vec<_>>();
        let bases = (0..len)
            .map(|_| EqAffine::from(Eq::random(&mut rng)))
            .collect::<Vec<_>>();

        assert_multiexp_matches_naive(&coeffs, &bases);

        let coeffs = (0..len).map(|_| Fq::random(&mut rng)).collect::<Vec<_>>();
        let bases = (0..len)
            .map(|_| EpAffine::from(Ep::random(&mut rng)))
            .collect::<Vec<_>>();

        assert_multiexp_matches_naive(&coeffs, &bases);
    }
}

#[test]
fn test_multiexp_booth_boundaries() {
    let mut rng = rng();
    let mut fp_high_bit = Fp::ONE;
    for _ in 0..254 {
        fp_high_bit = fp_high_bit.double();
    }
    let fp_scalars = [
        Fp::ZERO,
        Fp::ONE,
        -Fp::ONE,
        Fp::from(3),
        Fp::from(4),
        Fp::from(7),
        Fp::from(8),
        fp_high_bit,
    ];
    let fp_coeffs = fp_scalars.into_iter().cycle().take(32).collect::<Vec<_>>();
    let fp_bases = (0..fp_coeffs.len())
        .map(|_| EqAffine::from(Eq::random(&mut rng)))
        .collect::<Vec<_>>();
    assert_multiexp_matches_naive(&fp_coeffs, &fp_bases);

    let mut fq_high_bit = Fq::ONE;
    for _ in 0..254 {
        fq_high_bit = fq_high_bit.double();
    }
    let fq_scalars = [
        Fq::ZERO,
        Fq::ONE,
        -Fq::ONE,
        Fq::from(3),
        Fq::from(4),
        Fq::from(7),
        Fq::from(8),
        fq_high_bit,
    ];
    let fq_coeffs = fq_scalars.into_iter().cycle().take(32).collect::<Vec<_>>();
    let fq_bases = (0..fq_coeffs.len())
        .map(|_| EpAffine::from(Ep::random(&mut rng)))
        .collect::<Vec<_>>();
    assert_multiexp_matches_naive(&fq_coeffs, &fq_bases);
}

/// The GLV multiscalar backend parallelizes its Signed-Booth windows when the
/// Rayon pool has more than one thread (`pasta_curves/multicore`, forwarded by
/// this crate's `multicore` feature). `test_multiexp`'s sizes stop just past
/// the GLV threshold, and the default CI feature set omits `multicore`, so
/// exercise the parallel path explicitly: sizes the backend's cost model
/// selects GLV for, run inside one-thread and three-thread pools, must both
/// equal the naive sum and each other.
#[cfg(feature = "multicore")]
#[test]
fn test_multiexp_parallel_glv_matches_naive() {
    use maybe_rayon::ThreadPoolBuilder;

    fn check<C: CurveAffine>(len: usize) {
        let mut rng = rng();
        let coeffs = (0..len)
            .map(|_| C::Scalar::random(&mut rng))
            .collect::<Vec<_>>();
        let bases = (0..len)
            .map(|_| C::from(C::Curve::random(&mut rng)))
            .collect::<Vec<_>>();
        let expected = coeffs
            .iter()
            .zip(&bases)
            .map(|(coeff, base)| *base * coeff)
            .fold(C::Curve::identity(), |acc, val| acc + val);

        let mut results = Vec::new();
        for threads in [1usize, 3] {
            let pool = ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .expect("test thread pool");
            let result = pool.install(|| {
                assert_eq!(
                    multicore::current_num_threads(),
                    threads,
                    "the multiexp must observe the installed pool"
                );
                best_multiexp(&coeffs, &bases)
            });
            assert_eq!(result, expected, "{len} terms on {threads} thread(s)");
            results.push(result);
        }
        assert_eq!(results[0], results[1]);
    }

    // Sizes at which the backend's cost model selects GLV (see the
    // `multiexp_window_bits` / `should_use_glv_multiexp` tests in
    // `pasta_curves::glv`), so the parallel window path is what runs.
    for len in [2_150, 4_300] {
        check::<EqAffine>(len);
        check::<EpAffine>(len);
    }
}

#[test]
fn test_lagrange_interpolate() {
    let mut rng = rng();

    let points = (0..5).map(|_| Fp::random(&mut rng)).collect::<Vec<_>>();
    let evals = (0..5).map(|_| Fp::random(&mut rng)).collect::<Vec<_>>();

    for coeffs in 0..5 {
        let points = &points[0..coeffs];
        let evals = &evals[0..coeffs];

        let poly = lagrange_interpolate(points, evals);
        assert_eq!(poly.len(), points.len());

        for (point, eval) in points.iter().zip(evals) {
            assert_eq!(eval_polynomial(&poly, *point), *eval);
        }
    }
}

#[cfg(test)]
mod batch_invert_multi_tests {
    use super::*;
    use crate::pasta::Fp;
    use group::ff::BatchInvert;

    #[test]
    fn matches_ff_batch_invert_with_zeros() {
        // Lengths cover the empty slice, the single-chain branch, the
        // threshold crossing, odd and even two-lane lengths, and a large
        // batch; zeros are planted at both even and odd indices, with both
        // nonzero and zero leading elements.
        let mut state = 0x4c4c_4c4c_u64;
        let mut next = move || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            state
        };
        for leading_zero in [false, true] {
            for n in [0usize, 1, 2, 3, 7, 31, 32, 33, 64, 257, 1000] {
                let values: Vec<Fp> = (0..n)
                    .map(|i| {
                        if (leading_zero && i == 0) || i % 5 == 3 {
                            Fp::zero()
                        } else {
                            Fp::from(next() | 1)
                        }
                    })
                    .collect();
                let mut expected = values.clone();
                expected.iter_mut().batch_invert();
                let mut ours = values.clone();
                batch_invert_multi(&mut ours);
                assert_eq!(ours, expected, "n = {n}, leading zero = {leading_zero}");
            }
        }
    }
}
