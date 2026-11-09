//! Square roots and power-of-two roots of unity from compile-time field tables.

use super::{PastaField, PrimeModulus, Reduced, ReductionState, TWO_ADICITY};

#[cfg(feature = "sqrt-table-large")]
mod large;
#[cfg(feature = "sqrt-table-large")]
pub(super) use large::LargeSqrtTable;

/// Constructs reduced field entries from Montgomery limbs in constant tables.
///
/// Table initializers evaluate this at compile time. Runtime arithmetic borrows
/// the resulting field values directly.
///
/// # Panics
///
/// Panics if any entry is at least [`M::MODULUS`](PrimeModulus::MODULUS).
pub(super) const fn field_elements<M: PrimeModulus, const N: usize>(
    limbs: [[u64; 4]; N],
) -> [PastaField<M, Reduced>; N] {
    let mut fields = [PastaField::ZERO; N];
    let mut k = 0;
    while k < N {
        fields[k] = PastaField::from_montgomery_limbs(limbs[k]);
        k += 1;
    }
    fields
}

impl<M: PrimeModulus> PastaField<M, Reduced> {
    /// The fixed nonsquare used by [`Self::sqrt_alt`] and [`Self::sqrt_ratio`].
    ///
    /// This is [`Self::root_of_unity(32)`](Self::root_of_unity), namely
    /// `5^((p - 1) / 2^32)` for the field modulus `p`.
    pub const SQRT_NONSQUARE: Self = M::ROOTS[TWO_ADICITY as usize];

    /// Returns a square root, or `None` for a nonsquare.
    ///
    /// Zero returns `Some(Self::ZERO)`. Either root may be returned, and the
    /// choice may differ between [table configurations](crate#features).
    /// Tables require no allocation or runtime initialization. Branches and
    /// table accesses depend on the input; there is no constant-time guarantee
    /// for secret inputs.
    ///
    /// ```
    /// use zakura_udon::field::Fp;
    ///
    /// let square = <Fp>::from_u64(7).square().reduce();
    /// assert_eq!(square.sqrt().unwrap().square().reduce(), square);
    /// assert_eq!(Fp::ZERO.sqrt(), Some(Fp::ZERO));
    /// assert_eq!(Fp::from_u64(5).sqrt(), None);
    /// ```
    pub fn sqrt(&self) -> Option<Self> {
        if self.is_zero() {
            return Some(Self::ZERO);
        }

        // With p - 1 = t * 2^32, one fixed exponentiation initializes both
        // self^((t + 1)/2) and self^t. Both algorithms share this schedule.
        self.sqrt_with_exponent(M::pow_sqrt_exponent(&self.into_loose()))
    }

    // Completes `sqrt` for a nonzero input and `w = pow_sqrt_exponent(self)`.
    pub(crate) fn sqrt_with_exponent(&self, w: PastaField<M>) -> Option<Self> {
        #[cfg(feature = "sqrt-table-large")]
        {
            M::sqrt_large(self, w)
        }
        #[cfg(not(feature = "sqrt-table-large"))]
        {
            super::algorithms::tonelli_shanks_with_roots(
                &self.into_loose(),
                w,
                |k| M::ROOTS[k as usize].into_loose(),
                TWO_ADICITY,
            )
            .map(PastaField::reduce)
        }
    }

    /// Square roots of nonzero lanes with one interleaved exponentiation pass.
    ///
    /// Every lane's result matches [`Self::sqrt`] on the same input, including
    /// the choice of root. Lanes must be nonzero; zero inputs take `sqrt`'s
    /// short-circuit instead.
    pub(crate) fn sqrt_lanes<const L: usize>(values: &[Self; L]) -> [Option<Self>; L] {
        debug_assert!(values.iter().all(|value| !value.is_zero()));
        let w = M::pow_sqrt_exponent_lanes(&values.map(Self::into_loose));
        core::array::from_fn(|lane| values[lane].sqrt_with_exponent(w[lane]))
    }

    /// Returns `(is_square, root)` for this value or a fixed nonsquare multiple.
    ///
    /// If `is_square` is true, `root^2 = self`. Otherwise,
    /// `root^2 = self * Self::SQRT_NONSQUARE`. Zero returns `(true, Self::ZERO)`.
    /// Either sign may be returned; the choice need not match [`Self::sqrt`]
    /// and may differ between [table configurations](crate#features).
    ///
    /// Both cases share one exponentiation and require no allocation or runtime
    /// table initialization. Branches and table accesses depend on the input;
    /// there is no constant-time guarantee for secret inputs.
    ///
    /// ```
    /// use zakura_udon::field::Fp;
    ///
    /// let value = <Fp>::from_u64(5).reduce();
    /// let (is_square, root) = value.sqrt_alt();
    /// assert!(!is_square);
    /// assert_eq!(root.square().reduce(), value.mul(&Fp::SQRT_NONSQUARE).reduce());
    /// ```
    pub fn sqrt_alt(&self) -> (bool, Self) {
        if self.is_zero() {
            return (true, Self::ZERO);
        }
        let w = M::pow_sqrt_exponent(&self.into_loose());
        let x = self.mul(&w);
        finish::<M>(x, x.mul(&w))
    }

    /// Returns `(is_square, root)` for `self / denominator` without inversion.
    ///
    /// For a nonzero denominator, `is_square` is true exactly when the ratio is
    /// a square (including zero). Then `root^2 * denominator = self`.
    /// Otherwise, `root^2 * denominator = self * Self::SQRT_NONSQUARE`.
    ///
    /// A zero numerator returns `(true, Self::ZERO)`, including `0 / 0`.
    /// A nonzero numerator with zero denominator returns `(false, Self::ZERO)`;
    /// neither root equation applies in that case.
    /// Either sign may be returned, independently of [`Self::sqrt`] and the
    /// [table configuration](crate#features).
    ///
    /// This operation requires no allocation or runtime table initialization.
    /// Branches and table accesses depend on the inputs; there is no
    /// constant-time guarantee for secret inputs.
    ///
    /// ```
    /// use zakura_udon::field::Fp;
    ///
    /// let numerator = <Fp>::from_u64(12).reduce();
    /// let denominator = <Fp>::from_u64(3).reduce();
    /// let (is_square, root) = numerator.sqrt_ratio(&denominator);
    /// assert!(is_square);
    /// assert_eq!(root.square().mul(&denominator).reduce(), numerator);
    /// assert_eq!(numerator.sqrt_ratio(&Fp::ZERO), (false, Fp::ZERO));
    /// ```
    pub fn sqrt_ratio(&self, denominator: &Self) -> (bool, Self) {
        if self.is_zero() {
            return (true, Self::ZERO);
        }
        if denominator.is_zero() {
            return (false, Self::ZERO);
        }

        // Write p - 1 = t * 2^32 and a = self / denominator. With product =
        // self * denominator and w = product^((t - 1)/2), x = self * w and
        // z = product * w^2 satisfy x^2 = a * z. Also z = product^t lies in
        // the order-2^32 subgroup, so correcting it needs no inverse.
        let product = self.mul(denominator);
        let w = M::pow_sqrt_exponent(&product);
        finish::<M>(self.mul(&w), product.mul(&w.square()))
    }
}

// For nonzero a, x^2 = a * t and t lies in the order-2^32 subgroup.
// Correct x to a root of a, or a * SQRT_NONSQUARE when a is nonsquare.
fn finish<M: PrimeModulus>(x: PastaField<M>, t: PastaField<M>) -> (bool, PastaField<M, Reduced>) {
    #[cfg(feature = "sqrt-table-large")]
    {
        M::sqrt_finish_large(x, t)
    }
    #[cfg(not(feature = "sqrt-table-large"))]
    {
        let (is_square, root) = super::algorithms::tonelli_shanks_alt_with_roots(
            x,
            t,
            |k| M::ROOTS[k as usize].into_loose(),
            TWO_ADICITY,
        );
        (is_square, root.reduce())
    }
}

impl<M: PrimeModulus, S: ReductionState> PastaField<M, S> {
    /// Returns a primitive root of order `2^log_size`, or `None` above 32.
    ///
    /// The selected root is `5^((p - 1) / 2^log_size)`, where `p` is
    /// [`M::MODULUS`](PrimeModulus::MODULUS). `log_size = 0` returns one.
    pub const fn root_of_unity(log_size: u32) -> Option<Self> {
        if log_size > TWO_ADICITY {
            return None;
        }
        Some(Self::from_montgomery(M::ROOTS[log_size as usize].limbs))
    }

    /// Returns the inverse of [`Self::root_of_unity`], or `None` above 32.
    pub const fn root_of_unity_inverse(log_size: u32) -> Option<Self> {
        if log_size > TWO_ADICITY {
            return None;
        }
        Some(Self::from_montgomery(
            M::INVERSE_ROOTS[log_size as usize].limbs,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{PallasBase, PallasScalar, pasta::algorithms};

    fn check<M: PrimeModulus>() {
        let root = PastaField::<M>::root_of_unity(32).unwrap();
        let compare = |value: PastaField<M>| {
            let w = M::pow_sqrt_exponent(&value);
            let reference = algorithms::tonelli_shanks(&value, w, root, TWO_ADICITY);
            let small = algorithms::tonelli_shanks_with_roots(
                &value,
                w,
                |k| M::ROOTS[k as usize].into_loose(),
                TWO_ADICITY,
            );
            assert_eq!(
                (small).map(|value| value.reduce()),
                (reference).map(|value| value.reduce())
            );
            let result = value.reduce().sqrt();
            assert_eq!(result.is_some(), reference.is_some());
            if let Some(result) = result {
                assert_eq!(result.square().reduce(), value.reduce());
                let reference = reference.unwrap();
                assert!(result == reference.reduce() || result == reference.neg().reduce());
            }
        };
        compare(PastaField::ZERO);
        // Vary each byte of subgroup input exponents and straddle their carry
        // boundaries. Five's odd-cofactor power is root, so its inverse exponent
        // is u32::MAX; rounding that exponent must not overflow a 32-bit target.
        for shift in [0, 8, 16, 24] {
            for digit in 0..256u64 {
                compare(root.pow_u64(digit << shift));
            }
        }
        for exponent in [
            255, 256, 257, 65535, 65536, 65537, 0xffffff, 0x1000000, 0xfffffffe, 0xffffffff,
        ] {
            compare(root.pow_u64(exponent));
        }
        compare(PastaField::from_u64(5));
        assert!(PastaField::<M, Reduced>::from_u64(5).sqrt().is_none());
    }

    #[test]
    fn square_root_algorithms_agree_on_subgroup_boundaries() {
        check::<PallasBase>();
        check::<PallasScalar>();
    }
}
