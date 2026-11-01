//! Montgomery butterflies over the ordinary loose field representation.
//!
//! Working values and twiddles stay in `[0, 2p)`, including on unwind.

use super::{
    PastaField, PrimeModulus,
    word::{adc, mac},
};

#[cfg(any(test, not(all(udon_asm, not(miri)))))]
use super::word::subtract_limbs;

#[cfg(test)]
mod experiments;

/// Divides a loose Montgomery value by `2^log_size`, returning a loose value.
///
/// Requires `log_size <= 32` and input limbs `x < 2p`. Both Pasta primes have
/// `p = 1 mod 2^32`, so `q = -x mod 2^log_size` makes `x + q*p` divisible by
/// `2^log_size`. This preserves Montgomery scale. For a canonical input the
/// quotient is below `p`; for a loose input and `log_size >= 1`, it is below
/// `(1 + 2^-log_size)*p < 2p`. At zero, return the input unchanged.
#[inline]
pub(crate) fn divide_by_power_of_two<M: PrimeModulus>(
    value: PastaField<M>,
    log_size: u32,
) -> PastaField<M> {
    debug_assert!(log_size <= 32);
    debug_assert!(super::word::compare_limbs(&value.limbs, &M::TWICE_MODULUS).is_lt());
    if log_size == 0 {
        return value;
    }
    let [x0, x1, x2, x3] = value.limbs;
    let mask = (1u64 << log_size) - 1;
    let q = x0.wrapping_neg() & mask;
    let (r0, carry) = mac(x0, q, M::MODULUS[0], 0);
    let (r1, carry) = mac(x1, q, M::MODULUS[1], carry);
    let (r2, carry) = adc(x2, 0, carry);
    let (r3, carry) = adc(x3, q << 62, carry);
    // The numerator may exceed four limbs. Its high limb is below 2^log_size
    // because the quotient is below 2p < 2^256; preserve it in the final shift.
    let r4 = (q >> 2) + carry;
    debug_assert_eq!(r0 & mask, 0);
    debug_assert!(r4 <= mask);
    PastaField::from_montgomery([
        (r0 >> log_size) | (r1 << (64 - log_size)),
        (r1 >> log_size) | (r2 << (64 - log_size)),
        (r2 >> log_size) | (r3 << (64 - log_size)),
        (r3 >> log_size) | (r4 << (64 - log_size)),
    ])
}

/// Multiplies a loose value by a loose scale.
#[inline]
pub(crate) fn scale<M: PrimeModulus>(
    value: PastaField<M>,
    factor: &PastaField<M>,
) -> PastaField<M> {
    debug_assert!(super::word::compare_limbs(&value.limbs, &M::TWICE_MODULUS).is_lt());
    PastaField::from_montgomery(multiply::<M>(&value.limbs, &factor.limbs))
}

// Coarsely integrated operand scanning (CIOS) combines limb multiplication
// with Montgomery reduction: lhs, rhs, and result are below 2p.
// The full loose multiplication bound is proved in montgomery::square_run.
// The sealed Pasta moduli have limbs [p0, p1, 0, 1 << 62], which lets
// reduction replace two multiplication steps with shifts and addition.
// Keep the portable loop separate from ordinary multiplication so FFT inlining
// decisions do not change the field's ordinary multiplication kernel.
// Assembly shares the field kernel to keep its coverage in sync.
#[inline]
fn multiply<M: PrimeModulus>(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 4] {
    #[cfg(all(udon_asm, not(miri)))]
    {
        super::montgomery::montgomery_multiply_loose::<M>(lhs, rhs)
    }
    #[cfg(not(all(udon_asm, not(miri))))]
    {
        let mut accumulator = [0; 5];
        for rhs_limb in rhs {
            let mut carry = 0;
            for index in 0..4 {
                (accumulator[index], carry) = mac(accumulator[index], lhs[index], *rhs_limb, carry);
            }
            let (upper, product_overflow) = adc(accumulator[4], carry, 0);
            accumulator[4] = upper;
            let multiplier = accumulator[0].wrapping_mul(M::MONTGOMERY_INV);
            let (cancelled, carry) = mac(accumulator[0], multiplier, M::MODULUS[0], 0);
            debug_assert_eq!(cancelled, 0);
            let (r0, carry) = mac(accumulator[1], multiplier, M::MODULUS[1], carry);
            let (r1, carry) = adc(accumulator[2], 0, carry);
            let (r2, carry) = adc(accumulator[3], multiplier << 62, carry);
            let (r3, reduction_overflow) = adc(accumulator[4], multiplier >> 2, carry);
            accumulator = [r0, r1, r2, r3, product_overflow + reduction_overflow];
        }
        debug_assert_eq!(accumulator[4], 0);
        accumulator[..4].try_into().unwrap()
    }
}

// Both inputs, outputs, and any supplied twiddle are loose.
// None represents twiddle one, avoiding an identity multiplication.
#[inline]
pub(crate) fn butterfly<M: PrimeModulus>(
    left: &mut PastaField<M>,
    right: &mut PastaField<M>,
    twiddle: Option<&PastaField<M>>,
) {
    let product = match twiddle {
        Some(twiddle) => multiply::<M>(&right.limbs, &twiddle.limbs),
        None => right.limbs,
    };
    #[cfg(all(udon_asm, not(miri)))]
    {
        let sum = super::montgomery::add_twice_modulus::<M>(&left.limbs, &product);
        let difference = super::montgomery::sub_twice_modulus::<M>(&left.limbs, &product);
        left.limbs = sum;
        right.limbs = difference;
    }
    #[cfg(not(all(udon_asm, not(miri))))]
    {
        let modulus = M::TWICE_MODULUS;
        debug_assert!(super::word::compare_limbs(&left.limbs, &modulus).is_lt());
        debug_assert!(super::word::compare_limbs(&product, &modulus).is_lt());
        let mut sum = [0; 4];
        let mut carry = 0;
        for (index, limb) in sum.iter_mut().enumerate() {
            (*limb, carry) = adc(left.limbs[index], product[index], carry);
        }
        let (reduced, borrow) = subtract_limbs(&sum, &modulus);
        if carry != 0 || borrow == 0 {
            sum = reduced;
        }
        let (mut difference, borrow) = subtract_limbs(&left.limbs, &product);
        if borrow != 0 {
            let mut carry = 0;
            for (limb, modulus) in difference.iter_mut().zip(modulus) {
                (*limb, carry) = adc(*limb, modulus, carry);
            }
            debug_assert_eq!(carry, 1);
        }
        left.limbs = sum;
        right.limbs = difference;
    }
}

/// Decimation-in-frequency butterfly.
///
/// Adds and subtracts before multiplying the difference. The same loose range
/// bound holds as for [`butterfly`].
#[inline]
pub(crate) fn butterfly_dif<M: PrimeModulus>(
    left: &mut PastaField<M>,
    right: &mut PastaField<M>,
    twiddle: Option<&PastaField<M>>,
) {
    butterfly(left, right, None);
    if let Some(twiddle) = twiddle {
        right.limbs = multiply::<M>(&right.limbs, &twiddle.limbs);
    }
}

/// Two independent butterflies, scheduling their products together.
#[inline]
pub(crate) fn butterfly_pair<M: PrimeModulus, const DIF: bool>(
    left: &mut [PastaField<M>; 2],
    right: &mut [PastaField<M>; 2],
    twiddles: [Option<&PastaField<M>>; 2],
) {
    if DIF {
        butterfly(&mut left[0], &mut right[0], None);
        butterfly(&mut left[1], &mut right[1], None);
    }
    let first = twiddles[0].map_or(right[0], |twiddle| scale(right[0], twiddle));
    let second = twiddles[1].map_or(right[1], |twiddle| scale(right[1], twiddle));
    *right = [first, second];
    if !DIF {
        butterfly(&mut left[0], &mut right[0], None);
        butterfly(&mut left[1], &mut right[1], None);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::pasta::test_support::{CORPUS_SEED, xorshift64};
    use crate::field::{PallasBase, PallasScalar};
    use num_bigint::BigUint;

    fn integer(limbs: [u64; 4]) -> BigUint {
        limbs
            .iter()
            .rev()
            .fold(BigUint::from(0u32), |value, limb| (value << 64) + limb)
    }

    fn field<M: PrimeModulus>(value: &BigUint) -> PastaField<M> {
        let digits = value.to_u64_digits();
        // Bypass checked construction to exercise the kernel's loose range.
        let mut field = PastaField::ZERO;
        field.limbs = core::array::from_fn(|i| digits.get(i).copied().unwrap_or(0));
        field
    }

    fn boundaries<M: PrimeModulus>() {
        let p = integer(M::MODULUS);
        let twice = &p * 2u32;
        let radix = BigUint::from(1u32) << 256usize;
        let negative_inverse = &radix - p.modinv(&radix).unwrap();
        let redc = |product: BigUint| {
            let q = &product * &negative_inverse % &radix;
            (product + q * &p) / &radix
        };
        let values = [
            BigUint::from(0u32),
            BigUint::from(1u32),
            &p - 1u32,
            p.clone(),
            &p + 1u32,
            &twice - 1u32,
        ];
        for left in &values {
            for right in &values {
                for twiddle in [
                    None,
                    Some(PastaField::ZERO),
                    Some(PastaField::ONE),
                    Some(PastaField::<_>::ONE.neg()),
                    Some(PastaField::from_u64(7)),
                    Some(field::<M>(&BigUint::from(1u32))),
                    Some(field::<M>(&(&p / 2u32))),
                    Some(field::<M>(&(&p - 2u32))),
                    Some(field::<M>(&(&p - 1u32))),
                    Some(field::<M>(&p)),
                    Some(field::<M>(&(&p + 1u32))),
                    Some(field::<M>(&(&twice - 1u32))),
                ] {
                    let product = twiddle.map_or_else(
                        || right.clone(),
                        |twiddle| redc(right * integer(twiddle.montgomery_limbs())),
                    );
                    if let Some(twiddle) = twiddle {
                        let scaled = scale(field::<M>(right), &twiddle);
                        assert!(integer(scaled.limbs) < twice);
                        assert_eq!(integer(scaled.limbs), product);
                    }
                    let mut low = field::<M>(left);
                    let mut high = field::<M>(right);
                    butterfly(&mut low, &mut high, twiddle.as_ref());
                    assert!(integer(low.limbs) < twice);
                    assert!(integer(high.limbs) < twice);
                    assert_eq!(integer(low.limbs), (left + &product) % &twice);
                    assert_eq!(integer(high.limbs), (left + &twice - &product) % &twice);
                    let mut low = field::<M>(left);
                    let mut high = field::<M>(right);
                    butterfly_dif(&mut low, &mut high, twiddle.as_ref());
                    assert!(integer(low.limbs) < twice);
                    assert!(integer(high.limbs) < twice);
                    assert_eq!(integer(low.limbs), (left + right) % &twice);
                    let difference = (left + &twice - right) % &twice;
                    let expected = twiddle.map_or_else(
                        || difference.clone(),
                        |twiddle| redc(&difference * integer(twiddle.limbs)),
                    );
                    assert_eq!(integer(high.limbs), expected);
                    for dif in [false, true] {
                        let mut lows = [field::<M>(left); 2];
                        let mut highs = [field::<M>(right); 2];
                        let twiddles = [twiddle.as_ref(), None];
                        if dif {
                            butterfly_pair::<M, true>(&mut lows, &mut highs, twiddles);
                        } else {
                            butterfly_pair::<M, false>(&mut lows, &mut highs, twiddles);
                        }
                        for i in 0..2 {
                            let product = if i == 0 {
                                product.clone()
                            } else {
                                right.clone()
                            };
                            let sum = if dif {
                                (left + right) % &twice
                            } else {
                                (left + &product) % &twice
                            };
                            let difference = if dif {
                                if i == 0 {
                                    expected.clone()
                                } else {
                                    (left + &twice - right) % &twice
                                }
                            } else {
                                (left + &twice - &product) % &twice
                            };
                            assert!(integer(lows[i].limbs) < twice);
                            assert!(integer(highs[i].limbs) < twice);
                            assert_eq!(integer(lows[i].limbs), sum);
                            assert_eq!(integer(highs[i].limbs), difference);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn loose_butterflies_match_integer_arithmetic_at_modulus_boundaries() {
        boundaries::<PallasBase>();
        boundaries::<PallasScalar>();
    }

    fn division<M: PrimeModulus>() {
        let p = integer(M::MODULUS);
        let twice = &p * 2u32;
        let mut values = std::vec![
            BigUint::from(0u32),
            BigUint::from(1u32),
            &p - 1u32,
            p.clone(),
            &p + 1u32,
            &twice - 1u32,
        ];
        // Exercise correction bits, carries into each limb, and the fifth
        // numerator limb, with both canonical and loose representatives.
        for bit in [
            1usize, 2, 31, 32, 33, 63, 64, 65, 127, 128, 129, 191, 192, 193, 253, 254, 255,
        ] {
            let power = BigUint::from(1u32) << bit;
            for value in [&power - 1u32, power.clone(), &power + 1u32] {
                values.push(value.clone());
                if value < p {
                    values.extend([&p - &value, &p + &value, &twice - &value]);
                }
            }
        }
        let mut seed = CORPUS_SEED;
        for _ in 0..128 {
            let mut limbs = core::array::from_fn(|_| xorshift64(&mut seed));
            limbs[3] &= (1 << 63) - 1;
            values.push(integer(limbs));
        }
        for log_size in 0..=32 {
            let inverse = (BigUint::from(1u32) << log_size as usize).modpow(&(&p - 2u32), &p);
            for value in &values {
                assert!(value < &twice);
                let result = divide_by_power_of_two(field::<M>(value), log_size);
                // Compare raw Montgomery integers: the operation must divide
                // without changing the representation's Montgomery scale.
                assert!(integer(result.limbs) < twice);
                assert_eq!(
                    integer(result.limbs) % &p,
                    (value * &inverse) % &p,
                    "k={log_size}"
                );
            }
        }
    }

    #[test]
    fn inverse_power_scaling_matches_integers_for_canonical_and_loose_inputs() {
        division::<PallasBase>();
        division::<PallasScalar>();
    }

    fn partial_finish<M: PrimeModulus>() {
        use std::panic::{AssertUnwindSafe, catch_unwind};

        let p = integer(M::MODULUS);
        let original: [PastaField<M>; 4] = core::array::from_fn(|i| field(&(&p + i as u32)));
        for completed in 0..=original.len() {
            let mut values = original;
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    for value in &mut values[..completed] {
                        *value = divide_by_power_of_two(*value, 1);
                    }
                    panic!("interrupt inverse scaling");
                }))
                .is_err()
            );
            for (i, value) in values.iter().enumerate() {
                let expected = if i < completed {
                    (BigUint::from(i as u32) * (&p + 1u32) / 2u32) % &p
                } else {
                    BigUint::from(i as u32)
                };
                assert!(integer(value.limbs) < &p * 2u32);
                assert_eq!(integer(value.limbs) % &p, expected);
                if i >= completed {
                    assert_eq!(value.limbs, original[i].limbs);
                }
            }
        }
    }

    #[test]
    fn interrupted_inverse_scaling_leaves_valid_loose_values_without_cleanup() {
        partial_finish::<PallasBase>();
        partial_finish::<PallasScalar>();
    }

    fn partial_butterfly<M: PrimeModulus>() {
        use std::panic::{AssertUnwindSafe, catch_unwind};

        let a = PastaField::<M>::ONE.neg();
        let b = PastaField::<M>::from_u64(2).neg();
        let mut values = [a, b];
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                let (left, right) = values.split_at_mut(1);
                butterfly(&mut left[0], &mut right[0], None);
                panic!("interrupt loose region");
            }))
            .is_err()
        );
        let twice = integer(M::MODULUS) * 2u32;
        for (value, expected) in values.iter().zip([a.add(&b), a.sub(&b)]) {
            assert!(integer(value.limbs) < twice);
            assert_eq!(value.reduce(), expected.reduce());
        }
    }

    #[test]
    fn interrupted_butterflies_leave_valid_loose_values_without_cleanup() {
        partial_butterfly::<PallasBase>();
        partial_butterfly::<PallasScalar>();
    }
}
