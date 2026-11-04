//! Variable-time multiscalar multiplication shared by `halo2_proofs` and
//! RedPallas batch verification.
//!
//! [`best_multiexp_vartime`] first offers the multiplication to the curve's
//! specialized planner ([`CurveExt::try_multiexp_vartime_with_threads`], the
//! GLV backends for Pallas and Vesta). When the planner declines, it runs the
//! generic Signed-Booth bucket method below, so every size gets an answer
//! without callers keeping a fallback of their own.

use alloc::{vec, vec::Vec};

use ff::PrimeField;
use group::Group as _;
#[cfg(feature = "multicore")]
use maybe_rayon::prelude::*;

use super::{CurveAffine, CurveExt};

/// Computes $\sum_i [\mathit{coeffs}_i] \mathit{bases}_i$, using the current
/// Rayon pool when that is estimated to help.
///
/// # Panics
///
/// Panics if `coeffs` and `bases` have different lengths.
///
/// # Timing
///
/// Variable-time with respect to `coeffs` and intermediate curve points.
/// Callers must explicitly accept timing leakage when the coefficients are
/// secret.
pub fn best_multiexp_vartime<C: CurveAffine>(coeffs: &[C::ScalarExt], bases: &[C]) -> C::CurveExt {
    best_multiexp_vartime_with_threads(coeffs, bases, current_num_threads())
}

/// Like [`best_multiexp_vartime`], but uses at most `max_threads` workers of
/// the current Rayon pool (at least one). Callers with small batches can pass
/// `1` to stay on the calling thread, where splitting would cost more in
/// wake-ups than it saves.
///
/// # Panics
///
/// Panics if `coeffs` and `bases` have different lengths.
///
/// # Timing
///
/// Same as [`best_multiexp_vartime`].
pub fn best_multiexp_vartime_with_threads<C: CurveAffine>(
    coeffs: &[C::ScalarExt],
    bases: &[C],
    max_threads: usize,
) -> C::CurveExt {
    assert_eq!(coeffs.len(), bases.len());
    let num_threads = max_threads.clamp(1, current_num_threads());
    if let Some(result) = C::CurveExt::try_multiexp_vartime_with_threads(coeffs, bases, num_threads)
    {
        return result;
    }
    signed_booth_multiexp(coeffs, bases, num_threads)
}

/// Floors of `e^k` for `k = 4..=22`.
///
/// These preserve the established `ceil(ln(terms))` window schedule without
/// requiring floating-point transcendental functions, which are unavailable
/// in `no_std` builds.
const DEFAULT_MULTIEXP_WINDOW_THRESHOLDS: [u32; 19] = [
    54,
    148,
    403,
    1_096,
    2_980,
    8_103,
    22_026,
    59_874,
    162_754,
    442_413,
    1_202_604,
    3_269_017,
    8_886_110,
    24_154_952,
    65_659_969,
    178_482_300,
    485_165_195,
    1_318_815_734,
    3_584_912_846,
];

pub(crate) fn default_multiexp_window_bits(terms: usize) -> Option<usize> {
    if terms < 4 {
        Some(1)
    } else if terms < 32 {
        Some(3)
    } else {
        let terms = u32::try_from(terms).ok()?;
        let threshold = DEFAULT_MULTIEXP_WINDOW_THRESHOLDS
            .iter()
            .position(|upper| terms <= *upper)
            .unwrap_or(DEFAULT_MULTIEXP_WINDOW_THRESHOLDS.len());
        Some(4 + threshold)
    }
}

fn current_num_threads() -> usize {
    #[cfg(feature = "multicore")]
    {
        maybe_rayon::current_num_threads()
    }
    #[cfg(not(feature = "multicore"))]
    {
        1
    }
}

/// The generic Signed-Booth bucket method (formerly the body of
/// `halo2_proofs::arithmetic::best_multiexp`).
fn signed_booth_multiexp<C: CurveAffine>(
    coeffs: &[C::ScalarExt],
    bases: &[C],
    num_threads: usize,
) -> C::CurveExt {
    // `ceil(ln(terms))` above 32 terms, without floating point.
    let c = default_multiexp_window_bits(bases.len())
        .unwrap_or(4 + DEFAULT_MULTIEXP_WINDOW_THRESHOLDS.len());

    // Convert to canonical representations once instead of once per window.
    let coeffs = coeffs.iter().map(PrimeField::to_repr).collect::<Vec<_>>();

    let mut multi_buckets: Vec<BoothBuckets<C>> =
        vec![BoothBuckets::new(c); booth_window_count(&coeffs, c)];

    // Each window's bucket sum is independent, so workers fill windows in
    // parallel. The windows are then combined on this thread by Horner's
    // rule, which costs about one scalar's worth of doublings in total;
    // shifting every window by its own offset in parallel instead would
    // spend about `c * windows^2 / 2` doublings.
    #[cfg(feature = "multicore")]
    let window_sums = if should_parallelize_multiexp(coeffs.len(), num_threads) {
        multi_buckets
            .par_iter_mut()
            .enumerate()
            .map(|(i, buckets)| buckets.sum(&coeffs, bases, i))
            .collect::<Vec<_>>()
    } else {
        serial_window_sums(&mut multi_buckets, &coeffs, bases)
    };
    #[cfg(not(feature = "multicore"))]
    let window_sums = {
        let _ = num_threads;
        serial_window_sums(&mut multi_buckets, &coeffs, bases)
    };

    window_sums
        .into_iter()
        .rev()
        .fold(C::CurveExt::identity(), |mut sum, window| {
            // restore original evaluation point
            (0..c).for_each(|_| sum = sum.double());
            sum + window
        })
}

fn serial_window_sums<C: CurveAffine>(
    multi_buckets: &mut [BoothBuckets<C>],
    coeffs: &[<C::ScalarExt as PrimeField>::Repr],
    bases: &[C],
) -> Vec<C::CurveExt> {
    multi_buckets
        .iter_mut()
        .enumerate()
        .map(|(i, buckets)| buckets.sum(coeffs, bases, i))
        .collect()
}

#[cfg(feature = "multicore")]
fn should_parallelize_multiexp(num_coeffs: usize, num_threads: usize) -> bool {
    // The parallel algorithm shifts each window result independently. With a
    // single worker, this only adds doublings compared to serial evaluation.
    num_threads > 1 && num_coeffs > num_threads
}

#[derive(Clone, Copy)]
enum Bucket<C: CurveAffine> {
    None,
    Affine(C),
    Projective(C::CurveExt),
}

impl<C: CurveAffine> Bucket<C> {
    fn add_assign(&mut self, other: C) {
        *self = match *self {
            Bucket::None => Bucket::Affine(other),
            Bucket::Affine(a) => Bucket::Projective(a + other),
            Bucket::Projective(mut a) => {
                a += other;
                Bucket::Projective(a)
            }
        }
    }

    fn add(self, mut other: C::CurveExt) -> C::CurveExt {
        match self {
            Bucket::None => other,
            Bucket::Affine(a) => {
                other += a;
                other
            }
            Bucket::Projective(a) => other + &a,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct BoothDigit {
    magnitude: usize,
    negative: bool,
}

fn booth_digit(bytes: &[u8], window_bits: usize, window: usize) -> BoothDigit {
    debug_assert!(window_bits > 0);
    debug_assert!(window_bits < u64::BITS as usize);

    let window_start = window * window_bits;
    let byte_start = window_start / 8;
    let mut encoded = [0; 8];
    if byte_start < bytes.len() {
        for (slot, byte) in encoded.iter_mut().zip(&bytes[byte_start..]) {
            *slot = *byte;
        }
    }

    let bit_offset = window_start - byte_start * 8;
    let radix = 1usize << window_bits;
    let value = ((u64::from_le_bytes(encoded) >> bit_offset) as usize) & (radix - 1);
    let overlap = if window_start == 0 {
        0
    } else {
        let bit = window_start - 1;
        bytes
            .get(bit / 8)
            .map_or(0, |byte| usize::from((byte >> (bit % 8)) & 1))
    };

    // The bit below each window is its carry-in, while the window's high bit
    // is its carry-out. These terms cancel between adjacent windows, leaving
    // a signed digit whose magnitude is at most half the radix.
    if value < radix / 2 {
        BoothDigit {
            magnitude: value + overlap,
            negative: false,
        }
    } else {
        let magnitude = radix - value - overlap;
        BoothDigit {
            magnitude,
            negative: magnitude != 0,
        }
    }
}

fn booth_window_count<R: AsRef<[u8]>>(reprs: &[R], window_bits: usize) -> usize {
    debug_assert!(window_bits > 0);

    let repr_bytes = reprs
        .iter()
        .map(|repr| repr.as_ref().len())
        .max()
        .unwrap_or(0);
    let repr_bits = repr_bytes
        .checked_mul(u8::BITS as usize)
        .expect("scalar representation is too large");

    // Integer division reserves an additional carry window exactly when the
    // representation ends on a window boundary. Otherwise, the last partial
    // window cannot produce a carry.
    repr_bits / window_bits + 1
}

#[derive(Clone)]
struct BoothBuckets<C: CurveAffine> {
    c: usize,
    coeffs: Vec<Bucket<C>>,
}

impl<C: CurveAffine> BoothBuckets<C> {
    fn new(c: usize) -> Self {
        Self {
            c,
            coeffs: vec![Bucket::None; 1 << (c - 1)],
        }
    }

    fn sum(
        &mut self,
        coeffs: &[<C::ScalarExt as PrimeField>::Repr],
        bases: &[C],
        i: usize,
    ) -> C::CurveExt {
        // Recode each scalar window into a signed digit and add its base to
        // the bucket for the digit's magnitude.
        for (coeff, base) in coeffs.iter().zip(bases.iter()) {
            let digit = booth_digit(coeff.as_ref(), self.c, i);
            if digit.magnitude != 0 {
                let base = if digit.negative { -*base } else { *base };
                self.coeffs[digit.magnitude - 1].add_assign(base);
            }
        }
        // Summation by parts
        // e.g. 3a + 2b + 1c = a +
        //                    (a) + b +
        //                    ((a) + b) + c
        let mut acc = C::CurveExt::identity();
        let mut sum = C::CurveExt::identity();
        self.coeffs.iter().rev().for_each(|b| {
            sum = b.add(sum);
            acc += sum;
        });
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Ep, EpAffine, Eq, Fp, Fq};
    use ff::Field;
    use group::Curve as _;
    use group::CurveAffine as _;
    use rand::SeedableRng as _;
    use rand_xorshift::XorShiftRng;

    fn naive<C: CurveAffine>(coeffs: &[C::ScalarExt], bases: &[C]) -> C::CurveExt {
        coeffs
            .iter()
            .zip(bases)
            .map(|(coeff, base)| *base * coeff)
            .fold(C::CurveExt::identity(), |acc, val| acc + val)
    }

    /// Every size, including the planner's gap between its GLV-Strauss and
    /// GLV bucket ranges, and every thread cap must match the naive sum.
    #[test]
    fn best_multiexp_vartime_matches_naive() {
        let mut rng = XorShiftRng::from_seed([0x5a; 16]);
        for len in [
            0usize, 1, 2, 3, 4, 7, 16, 17, 31, 32, 33, 49, 66, 67, 97, 194, 255, 256, 257, 385,
        ] {
            let coeffs = (0..len).map(|_| Fq::random(&mut rng)).collect::<Vec<_>>();
            let bases = (0..len)
                .map(|_| Ep::random(&mut rng).to_affine())
                .collect::<Vec<_>>();
            let expected = naive(&coeffs, &bases);
            assert_eq!(
                best_multiexp_vartime(&coeffs, &bases),
                expected,
                "Pallas, {len} terms"
            );
            for max_threads in [0, 1, 2, 64] {
                assert_eq!(
                    best_multiexp_vartime_with_threads(&coeffs, &bases, max_threads),
                    expected,
                    "Pallas, {len} terms, max_threads {max_threads}"
                );
            }

            let coeffs = (0..len).map(|_| Fp::random(&mut rng)).collect::<Vec<_>>();
            let bases = (0..len)
                .map(|_| Eq::random(&mut rng).to_affine())
                .collect::<Vec<_>>();
            assert_eq!(
                best_multiexp_vartime(&coeffs, &bases),
                naive(&coeffs, &bases),
                "Vesta, {len} terms"
            );
        }
    }

    /// Identity bases and zero, one, and short (128-bit) scalars, as RedPallas
    /// batch verification produces them.
    #[test]
    fn best_multiexp_vartime_handles_identity_and_short_scalars() {
        let mut rng = XorShiftRng::from_seed([0x5a; 16]);
        for len in [5usize, 50, 194, 385] {
            let coeffs = (0..len)
                .map(|i| match i % 4 {
                    0 => Fq::ZERO,
                    1 => Fq::from_u128(u128::from(i as u64) << 64 | 0x5a5a),
                    2 => Fq::ONE,
                    _ => Fq::random(&mut rng),
                })
                .collect::<Vec<_>>();
            let bases = (0..len)
                .map(|i| {
                    if i % 5 == 2 {
                        EpAffine::identity()
                    } else {
                        Ep::random(&mut rng).to_affine()
                    }
                })
                .collect::<Vec<_>>();
            assert_eq!(
                best_multiexp_vartime(&coeffs, &bases),
                naive(&coeffs, &bases),
                "{len} terms"
            );
        }
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn best_multiexp_vartime_matches_across_pool_sizes() {
        let mut rng = XorShiftRng::from_seed([0x5a; 16]);
        for len in [7usize, 49, 194, 385] {
            let coeffs = (0..len).map(|_| Fq::random(&mut rng)).collect::<Vec<_>>();
            let bases = (0..len)
                .map(|_| Ep::random(&mut rng).to_affine())
                .collect::<Vec<_>>();
            let expected = naive(&coeffs, &bases);
            for threads in [1usize, 2, 3, 8] {
                let pool = maybe_rayon::ThreadPoolBuilder::new()
                    .num_threads(threads)
                    .build()
                    .expect("test thread pool");
                assert_eq!(
                    pool.install(|| best_multiexp_vartime(&coeffs, &bases)),
                    expected,
                    "{len} terms on {threads} threads"
                );
            }
        }
    }

    #[cfg(test)]
    fn evaluate_le_bytes(bytes: &[u8]) -> Fp {
        bytes.iter().rev().fold(Fp::ZERO, |mut acc, byte| {
            for bit in (0..u8::BITS).rev() {
                acc = acc.double();
                if (byte >> bit) & 1 != 0 {
                    acc += Fp::ONE;
                }
            }
            acc
        })
    }

    #[cfg(test)]
    fn evaluate_booth_digits(bytes: &[u8], window_bits: usize) -> Fp {
        (0..booth_window_count(&[bytes], window_bits))
            .rev()
            .fold(Fp::ZERO, |mut acc, window| {
                for _ in 0..window_bits {
                    acc = acc.double();
                }

                let digit = booth_digit(bytes, window_bits, window);
                let magnitude = Fp::from(digit.magnitude as u64);
                if digit.negative {
                    acc -= magnitude;
                } else {
                    acc += magnitude;
                }
                acc
            })
    }

    #[test]
    fn test_booth_digit_boundaries() {
        let assert_digit = |bytes: &[u8], window_bits, window, magnitude, negative| {
            assert_eq!(
                booth_digit(bytes, window_bits, window),
                BoothDigit {
                    magnitude,
                    negative,
                }
            );
        };

        let repr_bytes = <Fp as PrimeField>::Repr::default().as_ref().len();
        let mut bytes = vec![0; repr_bytes];
        assert_digit(&bytes, 3, 0, 0, false);

        bytes[0] = 3;
        assert_digit(&bytes, 3, 0, 3, false);

        bytes[0] = 4;
        assert_digit(&bytes, 3, 0, 4, true);
        assert_digit(&bytes, 3, 1, 1, false);

        bytes[0] = 7;
        assert_digit(&bytes, 3, 0, 1, true);
        assert_digit(&bytes, 3, 1, 1, false);

        let bytes = vec![u8::MAX; repr_bytes];
        assert_digit(&bytes, 8, 31, 0, false);
        assert_digit(&bytes, 8, 32, 1, false);
    }

    #[test]
    fn test_booth_digit_wide_representation() {
        const WIDE_REPR_BYTES: usize = 40;
        const FIRST_WIDE_BYTE: usize = 32;
        const WINDOW_BITS: usize = 8;
        const HALF_RADIX: usize = 1 << (WINDOW_BITS - 1);

        // A high-half value in the first byte above 256 bits produces a negative
        // digit whose carry must be consumed by the following window.
        let mut bytes = [0; WIDE_REPR_BYTES];
        let short_bytes = [0; FIRST_WIDE_BYTE];
        assert_eq!(
            booth_window_count(&[short_bytes.as_slice(), bytes.as_slice()], WINDOW_BITS),
            WIDE_REPR_BYTES + 1
        );

        bytes[FIRST_WIDE_BYTE] = HALF_RADIX as u8;
        assert_eq!(
            booth_digit(&bytes, WINDOW_BITS, FIRST_WIDE_BYTE),
            BoothDigit {
                magnitude: HALF_RADIX,
                negative: true,
            }
        );
        assert_eq!(
            booth_digit(&bytes, WINDOW_BITS, FIRST_WIDE_BYTE + 1),
            BoothDigit {
                magnitude: 1,
                negative: false,
            }
        );

        // The final data window likewise has a following carry-only window.
        bytes = [0; WIDE_REPR_BYTES];
        bytes[WIDE_REPR_BYTES - 1] = HALF_RADIX as u8;
        assert_eq!(
            booth_digit(&bytes, WINDOW_BITS, WIDE_REPR_BYTES - 1),
            BoothDigit {
                magnitude: HALF_RADIX,
                negative: true,
            }
        );
        assert_eq!(
            booth_digit(&bytes, WINDOW_BITS, WIDE_REPR_BYTES),
            BoothDigit {
                magnitude: 1,
                negative: false,
            }
        );

        let first_high_bit = {
            let mut bytes = [0; WIDE_REPR_BYTES];
            bytes[FIRST_WIDE_BYTE + 1] = 1;
            bytes
        };
        let all_ones = [u8::MAX; WIDE_REPR_BYTES];
        // Folding into `Fp` avoids a big-integer test dependency while exercising
        // the complete 320-bit recoding schedule.
        for bytes in [&bytes, &first_high_bit, &all_ones] {
            for window_bits in [1, 3, 5, 8, 9] {
                assert_eq!(
                    evaluate_booth_digits(bytes, window_bits),
                    evaluate_le_bytes(bytes)
                );
            }
        }
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn test_multiexp_algorithm_selection() {
        assert!(!should_parallelize_multiexp(usize::MAX, 1));
        assert!(!should_parallelize_multiexp(2, 2));
        assert!(should_parallelize_multiexp(3, 2));
    }
}
