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

use alloc::{boxed::Box, vec, vec::Vec};
use core::fmt;

use ff::WithSmallOrderMulGroup;

use super::{GLV_COMPONENT_BITS, GlvParams, decompose, private};
use crate::arithmetic::PreparedFixedBaseSum;

/// The signed-digit window width.
///
/// Six bits keep the table at about 44 KiB per base. At this width the GLV
/// table runs at the speed of a full-width signed-window table of the same
/// width while storing half as many points.
const WINDOW_BITS: usize = 6;

/// Positive digit magnitudes per window, `1..=2^(WINDOW_BITS - 1)`.
const MAGNITUDES: usize = 1 << (WINDOW_BITS - 1);

/// Windows per half-scalar. A half has at most [`GLV_COMPONENT_BITS`] bits,
/// and signed recoding can carry into one more window.
const WINDOWS: usize = GLV_COMPONENT_BITS / WINDOW_BITS + 1;

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

    /// Adds `[(-1)^negative * half] * P_base`, or `phi` of it when `endo`,
    /// to `acc`.
    fn add_half(&self, acc: &mut C, base: usize, negative: bool, half: u128, endo: bool) {
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
            if negative ^ digit_negative {
                *acc -= point;
            } else {
                *acc += point;
            }
        }
        debug_assert_eq!(carry, 0, "a half fits in WINDOWS signed windows");
    }
}

impl<C: GlvParams> PreparedFixedBaseSum<C> for FixedBaseSum<C> {
    fn bases(&self) -> usize {
        self.bases
    }

    fn sum_vartime(&self, scalars: &[C::ScalarExt]) -> C {
        assert!(
            scalars.len() <= self.bases,
            "at most one scalar per prepared base"
        );
        let mut acc = C::identity();
        for (base, scalar) in scalars.iter().enumerate() {
            let ((negative1, half1), (negative2, half2)) = decompose::<C>(scalar);
            self.add_half(&mut acc, base, negative1, half1, false);
            self.add_half(&mut acc, base, negative2, half2, true);
        }
        acc
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
        assert_eq!(WINDOWS, 22);
    }

    #[test]
    fn fixed_base_sum_matches_native_mul() {
        check::<pallas::Point>();
        check::<vesta::Point>();
    }

    #[test]
    #[should_panic(expected = "at most one scalar per prepared base")]
    fn fixed_base_sum_rejects_extra_scalars() {
        let table = prepare_fixed_base_sum::<pallas::Point>(&[pallas::Affine::generator()]);
        let _ = table.sum_vartime(&[pallas::Scalar::ONE, pallas::Scalar::ONE]);
    }
}
