//! Montgomery multiplication and reduction for the Pasta primes.
//!
//! Multiplication and reduction exploit the sealed Pasta modulus shape.

use super::PrimeModulus;

use super::word::{
    adc, borrow_sub_limbs, carry_add, carry_add_limbs, mac, subtract_limbs, wide_mul,
};

/// Subtracts `p` if the integer is at least `p`.
///
/// Inputs below `2p` produce a reduced residue.
#[inline]
pub(super) const fn reduce_once<M: PrimeModulus>(limbs: [u64; 4]) -> [u64; 4] {
    let (reduced, borrow) = subtract_limbs(&limbs, &M::MODULUS);
    if borrow == 0 { reduced } else { limbs }
}

/// Reduces a five-limb integer below `4p` modulo `2p`.
#[inline]
pub(super) fn reduce_twice_modulus<M: PrimeModulus>(limbs: [u64; 4], carry: u64) -> [u64; 4] {
    let (reduced, borrow) = subtract_limbs(&limbs, &M::TWICE_MODULUS);
    if carry != 0 || borrow == 0 {
        reduced
    } else {
        limbs
    }
}

/// Computes `lhs + rhs mod 2p` in `[0, 2p)` for inputs below `2p`.
///
/// The sum is below `4p`, which can exceed the radix, so the top carry takes
/// part in the single conditional subtraction of `2p`.
#[inline(always)]
pub(super) fn add_twice_modulus<M: PrimeModulus>(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 4] {
    #[cfg(all(udon_asm, not(miri)))]
    {
        crate::field::asm::add_loose(lhs, rhs, &M::TWICE_MODULUS)
    }
    #[cfg(not(all(udon_asm, not(miri))))]
    {
        add_twice_modulus_rust::<M>(lhs, rhs)
    }
}

/// Portable [`add_twice_modulus`]; the oracle for the assembly block.
#[cfg_attr(all(udon_asm, not(miri)), allow(dead_code))]
#[inline(always)]
pub(super) fn add_twice_modulus_rust<M: PrimeModulus>(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 4] {
    let (sum, carry) = carry_add_limbs(lhs, rhs);
    let (reduced, borrow) = borrow_sub_limbs(&sum, &M::TWICE_MODULUS);
    if carry || !borrow { reduced } else { sum }
}

/// Computes `lhs - rhs mod 2p` in `[0, 2p)` for inputs below `2p`, adding
/// `2p` back exactly when the subtraction borrows.
#[inline(always)]
pub(super) fn sub_twice_modulus<M: PrimeModulus>(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 4] {
    #[cfg(all(udon_asm, not(miri)))]
    {
        crate::field::asm::sub_loose(lhs, rhs, &M::TWICE_MODULUS)
    }
    #[cfg(not(all(udon_asm, not(miri))))]
    {
        sub_twice_modulus_rust::<M>(lhs, rhs)
    }
}

/// Portable [`sub_twice_modulus`]; the oracle for the assembly block.
#[cfg_attr(all(udon_asm, not(miri)), allow(dead_code))]
#[inline(always)]
pub(super) fn sub_twice_modulus_rust<M: PrimeModulus>(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 4] {
    let (difference, borrow) = borrow_sub_limbs(lhs, rhs);
    let mask = (borrow as u64).wrapping_neg();
    let twice = M::TWICE_MODULUS;
    let restore = [
        twice[0] & mask,
        twice[1] & mask,
        twice[2] & mask,
        twice[3] & mask,
    ];
    carry_add_limbs(&difference, &restore).0
}

/// Computes `lhs * rhs * R^-1 mod p` in `[0, 2p)`, with `R = 2^256`.
///
/// Both inputs may lie in `[0, 2p)`; see the closure proof below. Conversion
/// also uses this kernel with `lhs < R` and `rhs = R2 < p`, whose product is
/// below `pR`. The live CIOS accumulator fits because `lhs + p < 3p < R`
/// for field arithmetic; conversion's integrated result is below `2p`.
#[inline(always)]
pub(super) fn montgomery_multiply<M: PrimeModulus>(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 4] {
    debug_assert_eq!(M::MODULUS[2], 0);
    debug_assert_eq!(M::MODULUS[3], 1 << 62);

    // Coarsely integrated operand scanning keeps only the live five-limb
    // accumulator. Each round adds one schoolbook row and immediately cancels
    // its low limb. The two upper Pasta modulus limbs are zero and 2^62, so
    // their products require only carry propagation and shifts.
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

/// Computes `lhs * rhs * R^-1 mod p` in `[0, 2p)` for inputs below `2p`.
///
/// This is the field multiplication kernel; conversion from integers below
/// `R` uses [`montgomery_multiply`]. With both inputs below `2p`, each
/// round's five-limb sum `acc + lhs * b + q * p` stays below
/// `3p + 2^319 + 2^318 < 2^320`, and the shifted result stays below
/// `lhs + p < 3p < R` (the CIOS invariant), so no limb above the fourth
/// survives between rounds and no sixth-limb count is needed. The row's low
/// and high halves are folded in separate carry chains. The cancelled limb
/// `acc0 + low(q * p0)` is zero modulo `2^64`, so its carry is `acc0 != 0`
/// and the low product is never formed; `p[2] = 0` and `p[3] = 2^62` reduce
/// the remaining products to shifts.
#[inline(always)]
pub(super) fn montgomery_multiply_loose<M: PrimeModulus>(
    lhs: &[u64; 4],
    rhs: &[u64; 4],
) -> [u64; 4] {
    debug_assert_eq!(M::MODULUS[2], 0);
    debug_assert_eq!(M::MODULUS[3], 1 << 62);
    debug_assert!(super::word::compare_limbs(lhs, &M::TWICE_MODULUS).is_lt());
    debug_assert!(super::word::compare_limbs(rhs, &M::TWICE_MODULUS).is_lt());
    #[cfg(all(udon_asm, not(miri)))]
    {
        crate::field::asm::montgomery_multiply_loose::<M>(lhs, rhs)
    }
    #[cfg(not(all(udon_asm, not(miri))))]
    {
        montgomery_multiply_loose_rust::<M>(lhs, rhs)
    }
}

/// The portable form of [`montgomery_multiply_loose`], and the oracle for
/// the assembly form.
#[cfg_attr(all(udon_asm, not(miri)), allow(dead_code))]
#[inline(always)]
pub(super) fn montgomery_multiply_loose_rust<M: PrimeModulus>(
    lhs: &[u64; 4],
    rhs: &[u64; 4],
) -> [u64; 4] {
    let [a0, a1, a2, a3] = *lhs;
    let (mut r0, mut r1, mut r2, mut r3) = (0u64, 0u64, 0u64, 0u64);
    for &b in rhs {
        let (l0, h0) = wide_mul(a0, b);
        let (l1, h1) = wide_mul(a1, b);
        let (l2, h2) = wide_mul(a2, b);
        let (l3, h3) = wide_mul(a3, b);

        let (s0, carry) = carry_add(r0, l0, false);
        let (s1, carry) = carry_add(r1, l1, carry);
        let (s2, carry) = carry_add(r2, l2, carry);
        let (s3, carry) = carry_add(r3, l3, carry);
        let s4 = carry as u64;
        let (s1, carry) = carry_add(s1, h0, false);
        let (s2, carry) = carry_add(s2, h1, carry);
        let (s3, carry) = carry_add(s3, h2, carry);
        let (s4, carry) = carry_add(s4, h3, carry);
        debug_assert!(!carry);

        let q = s0.wrapping_mul(M::MONTGOMERY_INV);
        let (_, qh0) = wide_mul(q, M::MODULUS[0]);
        let (ql1, qh1) = wide_mul(q, M::MODULUS[1]);
        let (t1, carry) = carry_add(s1, ql1, s0 != 0);
        let (t2, carry) = carry_add(s2, 0, carry);
        let (t3, carry) = carry_add(s3, q << 62, carry);
        let (t4, carry) = carry_add(s4, 0, carry);
        debug_assert!(!carry);
        let (n0, carry) = carry_add(t1, qh0, false);
        let (n1, carry) = carry_add(t2, qh1, carry);
        let (n2, carry) = carry_add(t3, 0, carry);
        let (n3, carry) = carry_add(t4, q >> 2, carry);
        debug_assert!(!carry);
        (r0, r1, r2, r3) = (n0, n1, n2, n3);
    }
    [r0, r1, r2, r3]
}

/// Squares a loose Montgomery residue, retaining the `[0, 2p)` bound.
#[inline(always)]
pub(super) fn montgomery_square<M: PrimeModulus>(value: &[u64; 4]) -> [u64; 4] {
    #[cfg(all(udon_asm, not(miri)))]
    {
        crate::field::asm::square::<M>(value)
    }
    #[cfg(not(all(udon_asm, not(miri))))]
    {
        montgomery_reduce_unreduced::<M>(super::word::square_wide(value))
    }
}

/// Montgomery REDC: maps an eight-limb integer below `p * R` to its
/// reduced residue after multiplication by `R^-1`, where `R = 2^256`.
#[cfg(any(test, not(all(udon_asm, not(miri)))))]
#[inline(always)]
pub(super) fn montgomery_reduce<M: PrimeModulus>(limbs: [u64; 8]) -> [u64; 4] {
    reduce_once::<M>(montgomery_reduce_unreduced::<M>(limbs))
}

/// Computes REDC without its final conditional subtraction.
///
/// Requires `limbs < pR + p²`, where `R = 2^256`.
/// The result is below `2p + p²/R < 3p`.
/// For Pasta, `p < R/3`, so `limbs + (R - 1)p < 2pR + p² < R²`;
/// cancellation therefore fits in eight limbs throughout. A caller with
/// input below `pR` produces a loose result below `2p`. Producing a reduced
/// result takes one subtraction, or two for the wider input bound.
#[inline(always)]
pub(super) fn montgomery_reduce_unreduced<M: PrimeModulus>(limbs: [u64; 8]) -> [u64; 4] {
    #[cfg(all(udon_asm, not(miri)))]
    {
        crate::field::asm::reduce_wide::<M>(limbs)
    }
    #[cfg(not(all(udon_asm, not(miri))))]
    {
        // Cancel only the low half, then add the untouched high half once.
        // This is the same REDC integer as full-width cancellation. Under the
        // documented bound the final sum is below 3p < R, so no carry is lost.
        let [mut r0, mut r1, mut r2, mut r3, t4, t5, t6, t7] = limbs;
        for _ in 0..4 {
            let k = r0.wrapping_mul(M::MONTGOMERY_INV);
            let (cancelled, carry) = mac(r0, k, M::MODULUS[0], 0);
            debug_assert_eq!(cancelled, 0);
            let (s0, carry) = mac(r1, k, M::MODULUS[1], carry);
            let (s1, carry) = adc(r2, 0, carry);
            let (s2, carry) = adc(r3, k << 62, carry);
            let s3 = (k >> 2) + carry;
            (r0, r1, r2, r3) = (s0, s1, s2, s3);
        }
        let (r0, carry) = adc(r0, t4, 0);
        let (r1, carry) = adc(r1, t5, carry);
        let (r2, carry) = adc(r2, t6, carry);
        let (r3, carry) = adc(r3, t7, carry);
        debug_assert_eq!(carry, 0);
        [r0, r1, r2, r3]
    }
}

/// Repeated squaring and an optional product, all in `[0, 2p)`.
///
/// Closure for the Pasta primes is stronger than the generic REDC bound.
/// Write `p = R/4 + c`; the parameters assert `16c² < R` and `3p < R`.
/// Suppose `a,b < 2p` but `u = (ab + mp)/R >= 2p`, with `0 <= m < R`.
/// Then `ab >= pR + p`. Set `A = 2p-a`, `B = 2p-b`, and `S = A+B`.
/// If `S >= 2c+1`, AM-GM gives
/// `ab <= (R/2+c-1/2)² < pR`, a contradiction. Hence `S <= 2c`,
/// `0 < AB <= c² < p`, and, with `L = 4c-2S`, `ab = pR + pL + AB`.
/// Write `u = 2p+k` and `j = L+m-R`; then `kR = AB+jp`, so
/// `0 <= j <= L-1` and `AB+jc = (4k-j)R/4`. But
/// `0 < AB+jc < 4c² < R/4`, impossible for a multiple of `R/4`.
/// Thus arbitrary chains of loose products and squares remain below `2p`.
#[inline]
pub(super) fn square_run<M: PrimeModulus>(
    value: &[u64; 4],
    count: usize,
    factor: Option<&[u64; 4]>,
) -> [u64; 4] {
    #[cfg(all(udon_asm, not(miri)))]
    {
        if count == 0 {
            return factor.map_or(*value, |factor| {
                montgomery_multiply_loose::<M>(value, factor)
            });
        }
        match factor {
            Some(factor) => crate::field::asm::sqr_n_mul::<M>(value, count, factor),
            None if count == 1 => montgomery_square::<M>(value),
            None => crate::field::asm::sqr_n::<M>(value, count),
        }
    }
    #[cfg(not(all(udon_asm, not(miri))))]
    {
        let mut value = *value;
        for _ in 0..count {
            value = montgomery_reduce_unreduced::<M>(super::word::square_wide(&value));
        }
        match factor {
            Some(factor) => montgomery_multiply_loose::<M>(&value, factor),
            None => value,
        }
    }
}
