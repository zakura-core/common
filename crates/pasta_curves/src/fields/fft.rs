//! FFT-local residues below twice the modulus. No noncanonical field value
//! escapes this module: scratch uses limbs and outputs are normalized.

use crate::arithmetic::{adc, sbb};
use alloc::vec::Vec;

type Limbs = [u64; 4];

#[inline(always)]
fn subtract_if_possible(value: Limbs, high: u64, modulus: Limbs) -> Limbs {
    let (d0, borrow) = sbb(value[0], modulus[0], 0);
    let (d1, borrow) = sbb(value[1], modulus[1], borrow);
    let (d2, borrow) = sbb(value[2], modulus[2], borrow);
    let (d3, borrow) = sbb(value[3], modulus[3], borrow);
    let (_, borrow) = sbb(high, 0, borrow);
    let difference = [d0, d1, d2, d3];
    core::array::from_fn(|i| (value[i] & borrow) | (difference[i] & !borrow))
}

#[inline(always)]
fn add(left: Limbs, right: Limbs, modulus: Limbs) -> Limbs {
    let (s0, carry) = adc(left[0], right[0], 0);
    let (s1, carry) = adc(left[1], right[1], carry);
    let (s2, carry) = adc(left[2], right[2], carry);
    let (s3, carry) = adc(left[3], right[3], carry);
    // Four Pasta moduli exceed 2^256, so retain the carry when comparing
    // against twice the modulus.
    subtract_if_possible([s0, s1, s2, s3], carry, modulus)
}

#[inline(always)]
fn sub(left: Limbs, right: Limbs, modulus: Limbs) -> Limbs {
    let (d0, borrow) = sbb(left[0], right[0], 0);
    let (d1, borrow) = sbb(left[1], right[1], borrow);
    let (d2, borrow) = sbb(left[2], right[2], borrow);
    let (d3, borrow) = sbb(left[3], right[3], borrow);
    let (d0, carry) = adc(d0, modulus[0] & borrow, 0);
    let (d1, carry) = adc(d1, modulus[1] & borrow, carry);
    let (d2, carry) = adc(d2, modulus[2] & borrow, carry);
    let (d3, _) = adc(d3, modulus[3] & borrow, carry);
    [d0, d1, d2, d3]
}

pub(super) fn transform<F: Copy>(
    values: &mut [F],
    completed: usize,
    stride: usize,
    twiddle: impl Fn(usize) -> F,
    load: impl Fn(F) -> Limbs,
    store: impl Fn(Limbs) -> F,
    multiply: impl Fn(Limbs, Limbs) -> Limbs,
    modulus: Limbs,
) {
    assert!(values.len().is_power_of_two());
    assert!(completed.is_power_of_two() && completed <= values.len());
    assert!(stride.checked_mul(values.len()).is_some());
    let (p0, carry) = adc(modulus[0], modulus[0], 0);
    let (p1, carry) = adc(modulus[1], modulus[1], carry);
    let (p2, carry) = adc(modulus[2], modulus[2], carry);
    let (p3, carry) = adc(modulus[3], modulus[3], carry);
    debug_assert_eq!(carry, 0);
    let twice_modulus = [p0, p1, p2, p3];
    let mut scratch: Vec<_> = values.iter().copied().map(&load).collect();

    fn recurse(
        values: &mut [Limbs],
        completed: usize,
        stride: usize,
        twiddle: &impl Fn(usize) -> Limbs,
        multiply: &impl Fn(Limbs, Limbs) -> Limbs,
        twice_modulus: Limbs,
    ) {
        if values.len() == completed {
            return;
        }
        let half = values.len() / 2;
        let (left, right) = values.split_at_mut(half);
        recurse(
            left,
            completed,
            stride * 2,
            twiddle,
            multiply,
            twice_modulus,
        );
        recurse(
            right,
            completed,
            stride * 2,
            twiddle,
            multiply,
            twice_modulus,
        );
        for (index, (left, right)) in left.iter_mut().zip(right).enumerate() {
            let product = if index == 0 {
                *right
            } else {
                multiply(*right, twiddle(index * stride))
            };
            let original = *left;
            *left = add(original, product, twice_modulus);
            *right = sub(original, product, twice_modulus);
        }
    }

    recurse(
        &mut scratch,
        completed,
        stride,
        &|i| load(twiddle(i)),
        &multiply,
        twice_modulus,
    );
    for (value, raw) in values.iter_mut().zip(scratch) {
        *value = store(subtract_if_possible(raw, 0, modulus));
    }
}

#[cfg(test)]
pub(super) fn check_boundaries<F: ff::Field>(
    modulus: Limbs,
    load: impl Fn(F) -> Limbs,
    store: impl Fn(Limbs) -> F,
) {
    let zero = [0; 4];
    let one = [1, 0, 0, 0];
    let twice = {
        let (p0, carry) = adc(modulus[0], modulus[0], 0);
        let (p1, carry) = adc(modulus[1], modulus[1], carry);
        let (p2, carry) = adc(modulus[2], modulus[2], carry);
        let (p3, _) = adc(modulus[3], modulus[3], carry);
        [p0, p1, p2, p3]
    };
    let inputs = [
        zero,
        one,
        sub(modulus, one, twice),
        modulus,
        add(modulus, one, twice),
        sub(zero, one, twice),
    ];
    let canonical = |raw| store(subtract_if_possible(raw, 0, modulus));
    for a in inputs {
        for b in inputs {
            let sum = add(a, b, twice);
            let difference = sub(a, b, twice);
            assert_eq!(subtract_if_possible(sum, 0, twice), sum);
            assert_eq!(subtract_if_possible(difference, 0, twice), difference);
            assert_eq!(load(canonical(sum)), load(canonical(a) + canonical(b)));
            assert_eq!(
                load(canonical(difference)),
                load(canonical(a) - canonical(b))
            );
        }
    }
}
