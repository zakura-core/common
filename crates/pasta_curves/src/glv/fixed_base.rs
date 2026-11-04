//! Doubling-free sums over a few fixed bases.
//!
//! Each scalar is split by GLV into two signed halves of at most
//! [`GLV_COMPONENT_BITS`] bits, $k = k_1 + k_2\lambda$, and each half is
//! recoded into signed digits of [`WINDOW_BITS`] bits. The table stores, for
//! every base $P$ and window $w$, the positive multiples
//! $m \cdot 2^{w \cdot \mathrm{WINDOW\_BITS}} P$ for
//! $m \in 1..=2^{\mathrm{WINDOW\_BITS} - 1}$, already shifted into position,
//! so evaluation needs no doublings:
//!
//! - a negative digit (or a negative half) negates the stored point;
//! - the $k_2$ half uses $\phi(Q) = (\zeta x, y)$ of the stored point $Q$,
//!   one field multiplication, since $\phi(Q) = \lambda Q$.
//!
//! Storing only the $P$ multiples and deriving the $\phi(P)$ ones on the fly
//! halves the table relative to recoding full-width scalars at the same
//! window width, at the cost of one multiplication per $k_2$ addition.
//!
//! [`PreparedFixedBaseSum::sum_batch_vartime`] evaluates many independent
//! sums together. Each sum is a list of known affine points, so the sums are
//! the buckets of the MSM's affine bucket reducer (`reduce_affine_buckets`):
//! pairwise trees reduced level by level, with one shared inversion per level
//! (Montgomery's trick) and complete formulas for doublings and cancellations.
//! An affine addition then costs about half a mixed projective one.

use alloc::{boxed::Box, vec, vec::Vec};
use core::fmt;

use ff::{Field, WithSmallOrderMulGroup};

use super::{
    AffinePoint, GLV_COMPONENT_BITS, GlvParams, decompose, private, reduce_affine_buckets,
};
use crate::arithmetic::PreparedFixedBaseSum;

/// The signed-digit window width.
///
/// Seven bits keep the table at about 76 KiB per base (19 windows of 64
/// points). Wider windows mean fewer additions per half-scalar (19 at 7 bits,
/// 22 at 6) for twice the table per extra bit.
/// Measured on Zen 4 for Orchard's seven bases, 7 bits committed instances
/// 1.36x faster than the old fixed-window path, against 1.20x at 6 bits.
const WINDOW_BITS: usize = 7;

/// Positive digit magnitudes per window, `1..=2^(WINDOW_BITS - 1)`.
const MAGNITUDES: usize = 1 << (WINDOW_BITS - 1);

/// Windows per half-scalar. A half has at most [`GLV_COMPONENT_BITS`] bits,
/// and signed recoding can carry into one more window.
const WINDOWS: usize = GLV_COMPONENT_BITS / WINDOW_BITS + 1;

/// Sums reduced together by one call to the affine bucket reducer.
///
/// Each Orchard-shaped sum holds about 270 points (17 KiB), so a reduction
/// over many sums outgrows the core's L2 cache; on Zen 4, 64 or 128 sums per
/// call ran about a third slower per sum than 8 to 32. Larger batches are split.
const REDUCE_SUMS: usize = 16;

/// Builds a [`PreparedFixedBaseSum`] over `bases`.
pub(crate) fn prepare_fixed_base_sum<C: GlvParams>(
    bases: &[C::AffineExt],
) -> Box<dyn PreparedFixedBaseSum<C>> {
    Box::new(FixedBaseSum::<C>::new(bases))
}

/// The positioned multiples of each base, laid out by base, then window,
/// then magnitude.
struct FixedBaseSum<C: GlvParams> {
    bases: usize,
    points: Vec<C::AffineExt>,
}

impl<C: GlvParams> fmt::Debug for FixedBaseSum<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FixedBaseSum")
            .field("bases", &self.bases)
            .field("points", &self.points.len())
            .finish()
    }
}

impl<C: GlvParams> FixedBaseSum<C> {
    fn new(bases: &[C::AffineExt]) -> Self {
        let mut projective = Vec::with_capacity(bases.len() * WINDOWS * MAGNITUDES);
        for base in bases {
            let mut shifted = C::from(*base);
            for _ in 0..WINDOWS {
                let mut multiple = shifted;
                for _ in 0..MAGNITUDES {
                    projective.push(multiple);
                    multiple += shifted;
                }
                for _ in 0..WINDOW_BITS {
                    shifted = shifted.double();
                }
            }
        }
        let mut points = vec![C::AffineExt::default(); projective.len()];
        C::batch_normalize(&projective, &mut points);
        FixedBaseSum {
            bases: bases.len(),
            points,
        }
    }

    /// Calls `f(point, negate)` for each nonzero signed digit of
    /// `[(-1)^negative * half] * P_base`, or of `phi` of it when `endo`. The
    /// term is `-point` when `negate` is set.
    fn for_each_term(
        &self,
        base: usize,
        negative: bool,
        half: u128,
        endo: bool,
        mut f: impl FnMut(C::AffineExt, bool),
    ) {
        let windows = &self.points[base * WINDOWS * MAGNITUDES..][..WINDOWS * MAGNITUDES];
        let mut carry = 0u128;
        for window in 0..WINDOWS {
            let shift = window * WINDOW_BITS;
            let bits = if shift < 128 {
                (half >> shift) & ((1 << WINDOW_BITS) - 1)
            } else {
                0
            };
            let mut value = bits + carry;
            // Signed digits in -2^(b-1)..=2^(b-1): values above the midpoint
            // borrow from the next window.
            let digit_negative = value > MAGNITUDES as u128;
            if digit_negative {
                value = (1 << WINDOW_BITS) - value;
                carry = 1;
            } else {
                carry = 0;
            }
            if value == 0 {
                continue;
            }
            // `value` is at most `MAGNITUDES`, so the cast is lossless.
            let point = windows[window * MAGNITUDES + value as usize - 1];
            let point = if endo {
                let (x, y) = C::affine_xy(&point);
                C::affine_unchecked(x * C::Base::ZETA, y, private::CrateToken(()))
            } else {
                point
            };
            f(point, negative ^ digit_negative);
        }
        debug_assert_eq!(carry, 0, "a half fits in WINDOWS signed windows");
    }

    /// Calls `f(point, negate)` for every term of `sum_i [k_i] P_i`.
    fn for_each_sum_term(&self, scalars: &[C::ScalarExt], mut f: impl FnMut(C::AffineExt, bool)) {
        assert!(
            scalars.len() <= self.bases,
            "at most one scalar per prepared base"
        );
        for (base, scalar) in scalars.iter().enumerate() {
            let ((negative1, half1), (negative2, half2)) = decompose::<C>(scalar);
            self.for_each_term(base, negative1, half1, false, &mut f);
            self.for_each_term(base, negative2, half2, true, &mut f);
        }
    }
}

impl<C: GlvParams> PreparedFixedBaseSum<C> for FixedBaseSum<C> {
    fn bases(&self) -> usize {
        self.bases
    }

    fn sum_vartime(&self, scalars: &[C::ScalarExt]) -> C {
        let mut acc = C::identity();
        self.for_each_sum_term(scalars, |point, negate| {
            if negate {
                acc -= point;
            } else {
                acc += point;
            }
        });
        acc
    }

    fn sum_batch_vartime(&self, scalars: &[&[C::ScalarExt]]) -> Vec<C> {
        scalars
            .chunks(REDUCE_SUMS)
            .flat_map(|chunk| self.reduce_sums(chunk))
            .collect()
    }
}

impl<C: GlvParams> FixedBaseSum<C> {
    /// Reduces the sums of `scalars` together; see [`REDUCE_SUMS`].
    fn reduce_sums(&self, scalars: &[&[C::ScalarExt]]) -> Vec<C> {
        // One bucket per sum, laid out contiguously for the reducer.
        let mut points =
            Vec::with_capacity(scalars.iter().map(|s| s.len()).sum::<usize>() * 2 * WINDOWS);
        let mut offsets = Vec::with_capacity(scalars.len() + 1);
        offsets.push(0);
        for scalars in scalars {
            self.for_each_sum_term(scalars, |point, negate| {
                let (x, y) = C::affine_xy(&point);
                // Table entries of an identity base are the identity, encoded
                // as (0, 0). The reducer requires non-identity points, and
                // they contribute nothing.
                if !(x.is_zero_vartime() && y.is_zero_vartime()) {
                    points.push(AffinePoint {
                        x,
                        y: if negate { -y } else { y },
                    });
                }
            });
            offsets.push(points.len());
        }
        match reduce_affine_buckets(points, offsets) {
            Some(sums) => sums
                .into_iter()
                .map(|sum| match sum {
                    Some(p) => C::from(C::affine_unchecked(p.x, p.y, private::CrateToken(()))),
                    None => C::identity(),
                })
                .collect(),
            // The reducer declines only if its complete formulas meet a zero
            // denominator, which valid points rule out; stay correct anyway.
            None => scalars.iter().map(|s| self.sum_vartime(s)).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use ff::{Field, FromUniformBytes, PrimeField};
    use group::CurveAffine as _;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    use super::{GlvParams, WINDOWS, prepare_fixed_base_sum};
    use crate::{pallas, vesta};

    fn check<C: GlvParams>()
    where
        C::ScalarExt: FromUniformBytes<64>,
    {
        let mut rng = XorShiftRng::seed_from_u64(0x6c76);
        let bases: Vec<C::AffineExt> = (0..5)
            .map(|_| C::random(&mut rng).to_affine())
            .chain(core::iter::once(C::identity().to_affine()))
            .collect();
        let table = prepare_fixed_base_sum::<C>(&bases);
        assert_eq!(table.bases(), bases.len());

        let mut edges = Vec::from([
            C::ScalarExt::ZERO,
            C::ScalarExt::ONE,
            -C::ScalarExt::ONE,
            C::ScalarExt::from(31),
            C::ScalarExt::from(32),
            C::ScalarExt::from(33),
            -C::ScalarExt::from(32),
            C::ScalarExt::from(u64::MAX),
            C::ScalarExt::from_u128(u128::MAX),
        ]);
        edges.extend((0..64).map(|_| C::ScalarExt::random(&mut rng)));

        for chunk in edges.chunks(bases.len()) {
            let expected: C = chunk.iter().zip(&bases).map(|(k, p)| *p * k).sum();
            assert_eq!(table.sum_vartime(chunk), expected);
        }
        // Fewer scalars than bases leaves the rest at zero.
        for len in 0..=bases.len() {
            let scalars = &edges[edges.len() - len..];
            let expected: C = scalars.iter().zip(&bases).map(|(k, p)| *p * k).sum();
            assert_eq!(table.sum_vartime(scalars), expected, "{len} scalars");
        }
        assert_eq!(WINDOWS, 19);
    }

    #[test]
    fn fixed_base_sum_matches_native_mul() {
        check::<pallas::Point>();
        check::<vesta::Point>();
    }

    /// The batched sums equal the per-sum ones, including identity bases,
    /// zero and short scalar vectors, and pairs that hit the equal-x fallback.
    fn check_batch<C: GlvParams>()
    where
        C::ScalarExt: FromUniformBytes<64>,
    {
        let mut rng = XorShiftRng::seed_from_u64(0x6261);
        let p = C::random(&mut rng).to_affine();
        // A repeated base with equal or opposite scalars makes identical or
        // negated terms, so the trees meet doublings and cancellations.
        let bases = [
            p,
            p,
            C::random(&mut rng).to_affine(),
            C::identity().to_affine(),
        ];
        let table = prepare_fixed_base_sum::<C>(&bases);
        let k = C::ScalarExt::random(&mut rng);
        let mut columns: Vec<Vec<C::ScalarExt>> = Vec::from([
            Vec::new(),
            Vec::from([C::ScalarExt::ZERO]),
            Vec::from([k, k]),
            Vec::from([k, -k]),
            Vec::from([k, k, k, k]),
            Vec::from([C::ScalarExt::ONE, -C::ScalarExt::ONE, C::ScalarExt::ONE]),
        ]);
        columns.extend((0..20).map(|i| {
            (0..(i % 5))
                .map(|_| C::ScalarExt::random(&mut rng))
                .collect()
        }));
        for count in [0, 1, 2, 7, columns.len()] {
            let slices: Vec<&[C::ScalarExt]> = columns[..count].iter().map(Vec::as_slice).collect();
            let expected: Vec<C> = slices.iter().map(|s| table.sum_vartime(s)).collect();
            assert_eq!(table.sum_batch_vartime(&slices), expected, "{count} sums");
        }
    }

    #[test]
    fn fixed_base_sum_batch_matches_single() {
        check_batch::<pallas::Point>();
        check_batch::<vesta::Point>();
    }

    #[test]
    #[should_panic(expected = "at most one scalar per prepared base")]
    fn fixed_base_sum_rejects_extra_scalars() {
        let table = prepare_fixed_base_sum::<pallas::Point>(&[pallas::Affine::generator()]);
        let _ = table.sum_vartime(&[pallas::Scalar::ONE, pallas::Scalar::ONE]);
    }
}
