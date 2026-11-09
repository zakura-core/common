//! Deferred normalization for field arithmetic.
//!
//! This module provides the [`DeferredField`] trait and a wide [`Product`]
//! accumulator. Together they enable accumulating multiple unreduced
//! Montgomery products before performing a single expensive reduction.
//! This is useful for operations like inner products where many
//! multiplications feed into a sum.

use core::fmt::Debug;

use crate::arithmetic::adc;
#[cfg(not(all(
    feature = "aarch64-asm",
    target_arch = "aarch64",
    any(target_family = "unix", target_os = "none"),
    target_pointer_width = "64",
    target_endian = "little"
)))]
use crate::arithmetic::mac;

// Keep the assembly exception within this private arithmetic backend.
#[allow(unsafe_code)]
#[cfg(all(
    feature = "aarch64-asm",
    target_arch = "aarch64",
    any(target_family = "unix", target_os = "none"),
    target_pointer_width = "64",
    target_endian = "little"
))]
mod aarch64;

#[cfg(target_arch = "aarch64")]
pub(crate) const INNER_PRODUCT_BLOCK_SIZE: usize = 32;

/// A trait for fields that support deferred reduction of products.
///
/// Instead of reducing each multiplication result immediately, callers
/// accumulate products into an [`Accumulator`](Self::Accumulator) via
/// [`mul_accumulate`](Self::mul_accumulate) and
/// [`square_accumulate`](Self::square_accumulate), then perform a single
/// reduction at the end with [`reduce`](Self::reduce). The
/// [`inner_product`](Self::inner_product) operation manages its own serial
/// block structure.
pub trait DeferredField: ff::Field {
    /// A wide accumulator for unreduced products.
    type Accumulator: Copy + Clone + Debug + Default;

    /// Multiplies `a` by `b` and adds the result into `acc`.
    fn mul_accumulate(acc: &mut Self::Accumulator, a: &Self, b: &Self);

    /// Computes the inner product of `lhs` and `rhs`.
    ///
    /// This method is serial. Callers should parallelize independent work at
    /// the highest level that cleanly exposes it.
    ///
    /// # Panics
    ///
    /// Panics if `lhs` and `rhs` have different lengths.
    #[inline]
    fn inner_product(lhs: &[Self], rhs: &[Self]) -> Self {
        assert_eq!(lhs.len(), rhs.len());
        let mut accumulator = Self::Accumulator::default();
        for (lhs, rhs) in lhs.iter().zip(rhs) {
            Self::mul_accumulate(&mut accumulator, lhs, rhs);
        }
        Self::reduce(accumulator)
    }

    /// Squares `a` and adds the result into `acc`.
    fn square_accumulate(acc: &mut Self::Accumulator, a: &Self);

    /// Reduces the accumulator to a canonical field element.
    fn reduce(acc: Self::Accumulator) -> Self;
}

/// A wide accumulator for unreduced Montgomery products over field `F`.
///
/// This stores a running sum of 512-bit products with a 64-bit carry for
/// overflow beyond 512 bits. Products are added internally by
/// [`DeferredField::mul_accumulate`] and [`DeferredField::square_accumulate`].
///
/// Call [`DeferredField::reduce`] to fold the carry back into range and
/// perform Montgomery reduction.
#[derive(Clone, Copy, Debug)]
pub struct Product<F> {
    limbs: [u64; 8],
    carry: u64,
    _marker: core::marker::PhantomData<F>,
}

impl<F> Default for Product<F> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<F> Product<F> {
    /// The zero (additive identity) accumulator.
    pub const ZERO: Self = Product {
        limbs: [0; 8],
        carry: 0,
        _marker: core::marker::PhantomData,
    };

    /// Multiplies two raw 256-bit values and adds their 512-bit product into
    /// this accumulator.
    ///
    /// Each multiplication row starts from the corresponding accumulator
    /// limbs. The row's full-limb carry and the preceding one-bit overflow are
    /// then added to the next untouched limb. This incorporates every
    /// accumulator limb exactly once, without first materializing the product
    /// and adding it in a second pass.
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub(crate) fn mul_accumulate(&mut self, lhs: &[u64; 4], rhs: &[u64; 4]) {
        #[cfg(all(
            feature = "aarch64-asm",
            target_arch = "aarch64",
            any(target_family = "unix", target_os = "none"),
            target_pointer_width = "64",
            target_endian = "little"
        ))]
        {
            let (limbs, overflow) = aarch64::mul_accumulate(self.limbs, lhs, rhs);
            self.limbs = limbs;
            let (carry, carry_overflow) = self.carry.overflowing_add(overflow);
            debug_assert!(
                !carry_overflow,
                "carry overflow: too many accumulated products"
            );
            self.carry = carry;
        }
        #[cfg(not(all(
            feature = "aarch64-asm",
            target_arch = "aarch64",
            any(target_family = "unix", target_os = "none"),
            target_pointer_width = "64",
            target_endian = "little"
        )))]
        {
            // Row 0 contributes lhs[0] * rhs at limbs 0 through 3. Starting the
            // multiply-add chain from the stored limbs incorporates that part of
            // the old accumulator. Its full-limb carry enters untouched limb 4;
            // `overflow` is the resulting one-bit carry into limb 5.
            let (d0, carry) = mac(self.limbs[0], lhs[0], rhs[0], 0);
            let (d1, carry) = mac(self.limbs[1], lhs[0], rhs[1], carry);
            let (d2, carry) = mac(self.limbs[2], lhs[0], rhs[2], carry);
            let (d3, carry) = mac(self.limbs[3], lhs[0], rhs[3], carry);
            let (d4, overflow) = adc(self.limbs[4], carry, 0);

            // Row 1 begins at limb 1 and updates the partially formed limbs 1
            // through 4. Its full-limb carry and row 0's one-bit overflow are
            // combined with untouched accumulator limb 5.
            let (d1, carry) = mac(d1, lhs[1], rhs[0], 0);
            let (d2, carry) = mac(d2, lhs[1], rhs[1], carry);
            let (d3, carry) = mac(d3, lhs[1], rhs[2], carry);
            let (d4, carry) = mac(d4, lhs[1], rhs[3], carry);
            let (d5, overflow) = adc(self.limbs[5], carry, overflow);

            // Row 2 repeats the same carry handoff one limb higher, covering
            // partially formed limbs 2 through 5 and untouched limb 6.
            let (d2, carry) = mac(d2, lhs[2], rhs[0], 0);
            let (d3, carry) = mac(d3, lhs[2], rhs[1], carry);
            let (d4, carry) = mac(d4, lhs[2], rhs[2], carry);
            let (d5, carry) = mac(d5, lhs[2], rhs[3], carry);
            let (d6, overflow) = adc(self.limbs[6], carry, overflow);

            // Row 3 finishes the 256-by-256-bit product in limbs 3 through 6.
            // Its carry and row 2's overflow are combined with the final stored
            // accumulator limb.
            let (d3, carry) = mac(d3, lhs[3], rhs[0], 0);
            let (d4, carry) = mac(d4, lhs[3], rhs[1], carry);
            let (d5, carry) = mac(d5, lhs[3], rhs[2], carry);
            let (d6, carry) = mac(d6, lhs[3], rhs[3], carry);
            let (d7, overflow) = adc(self.limbs[7], carry, overflow);

            // The final one-bit overflow is the only contribution beyond the
            // 512-bit limb array. Fold it into the accumulator's external carry.
            self.limbs = [d0, d1, d2, d3, d4, d5, d6, d7];
            let (carry, carry_overflow) = self.carry.overflowing_add(overflow);
            debug_assert!(
                !carry_overflow,
                "carry overflow: too many accumulated products"
            );
            self.carry = carry;
        }
    }

    /// Multiplies corresponding raw 256-bit values and adds their 512-bit
    /// products into this accumulator.
    #[cfg(target_arch = "aarch64")]
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub(crate) fn mul_accumulate_block<T, L>(&mut self, lhs: &[T], rhs: &[T], limbs: L)
    where
        L: Copy + for<'a> Fn(&'a T) -> &'a [u64; 4],
    {
        assert_eq!(lhs.len(), rhs.len());

        macro_rules! add_block {
            ($columns:ident, $lhs_limb:literal, $rhs_limb:literal) => {{
                let (lhs_quads, lhs_remainder) = lhs.as_chunks::<4>();
                let (rhs_quads, rhs_remainder) = rhs.as_chunks::<4>();
                for (lhs, rhs) in lhs_quads.iter().zip(rhs_quads) {
                    add_product(
                        &mut $columns[0],
                        limbs(&lhs[0])[$lhs_limb],
                        limbs(&rhs[0])[$rhs_limb],
                    );
                    add_product(
                        &mut $columns[1],
                        limbs(&lhs[1])[$lhs_limb],
                        limbs(&rhs[1])[$rhs_limb],
                    );
                    add_product(
                        &mut $columns[2],
                        limbs(&lhs[2])[$lhs_limb],
                        limbs(&rhs[2])[$rhs_limb],
                    );
                    add_product(
                        &mut $columns[3],
                        limbs(&lhs[3])[$lhs_limb],
                        limbs(&rhs[3])[$rhs_limb],
                    );
                }
                for (lhs, rhs) in lhs_remainder.iter().zip(rhs_remainder) {
                    let lhs = limbs(lhs);
                    let rhs = limbs(rhs);
                    add_product(&mut $columns[0], lhs[$lhs_limb], rhs[$rhs_limb]);
                }
            }};
        }

        // Comba columns let every product in the block share each carry
        // handoff. Three limbs suffice for every realizable input slice: a
        // 64-bit target can hold fewer than 2^59 four-limb values, so the
        // widest column sums fewer than 2^61 128-bit products.
        let mut columns = [[self.limbs[0], 0, 0], [0; 3], [0; 3], [0; 3]];
        add_block!(columns, 0, 0);
        let mut column = merge_columns(columns);
        self.limbs[0] = column[0];

        columns = start_columns(self.limbs[1], column[1], column[2]);
        add_block!(columns, 0, 1);
        add_block!(columns, 1, 0);
        column = merge_columns(columns);
        self.limbs[1] = column[0];

        columns = start_columns(self.limbs[2], column[1], column[2]);
        add_block!(columns, 0, 2);
        add_block!(columns, 1, 1);
        add_block!(columns, 2, 0);
        column = merge_columns(columns);
        self.limbs[2] = column[0];

        columns = start_columns(self.limbs[3], column[1], column[2]);
        add_block!(columns, 0, 3);
        add_block!(columns, 1, 2);
        add_block!(columns, 2, 1);
        add_block!(columns, 3, 0);
        column = merge_columns(columns);
        self.limbs[3] = column[0];

        columns = start_columns(self.limbs[4], column[1], column[2]);
        add_block!(columns, 1, 3);
        add_block!(columns, 2, 2);
        add_block!(columns, 3, 1);
        column = merge_columns(columns);
        self.limbs[4] = column[0];

        columns = start_columns(self.limbs[5], column[1], column[2]);
        add_block!(columns, 2, 3);
        add_block!(columns, 3, 2);
        column = merge_columns(columns);
        self.limbs[5] = column[0];

        columns = start_columns(self.limbs[6], column[1], column[2]);
        add_block!(columns, 3, 3);
        column = merge_columns(columns);
        self.limbs[6] = column[0];

        column = start_column(self.limbs[7], column[1], column[2]);
        self.limbs[7] = column[0];
        debug_assert_eq!(column[2], 0);
        let (carry, overflow) = self.carry.overflowing_add(column[1]);
        debug_assert!(!overflow, "carry overflow: too many accumulated products");
        self.carry = carry;
    }

    /// Adds a raw 512-bit product (8 limbs) into this accumulator.
    ///
    /// Each call contributes at most 1 to `carry`; overflow of the 64-bit
    /// carry requires 2^64 accumulated products (~590 exabytes of input).
    #[inline]
    pub(crate) fn accumulate(&mut self, product: [u64; 8]) {
        let (d0, c) = adc(self.limbs[0], product[0], 0);
        let (d1, c) = adc(self.limbs[1], product[1], c);
        let (d2, c) = adc(self.limbs[2], product[2], c);
        let (d3, c) = adc(self.limbs[3], product[3], c);
        let (d4, c) = adc(self.limbs[4], product[4], c);
        let (d5, c) = adc(self.limbs[5], product[5], c);
        let (d6, c) = adc(self.limbs[6], product[6], c);
        let (d7, c) = adc(self.limbs[7], product[7], c);
        self.limbs = [d0, d1, d2, d3, d4, d5, d6, d7];
        let (carry, overflow) = self.carry.overflowing_add(c);
        debug_assert!(!overflow, "carry overflow: too many accumulated products");
        self.carry = carry;
    }

    /// Folds `carry` (bits 512+) and `limbs[7]` (bits 448–511) into the lower
    /// 448 bits using precomputed residues of $2^{448}$ and $2^{512}$ modulo
    /// the field prime.
    ///
    /// The result fits in 8 limbs with value $< 2^{449} < Rp$, safe for
    /// Montgomery reduction.
    #[cfg_attr(not(feature = "uninline-portable"), inline)]
    pub(crate) fn partial_reduce(&self, b448: &[u64; 4], r2: &[u64; 4]) -> [u64; 8] {
        #[cfg(all(
            feature = "aarch64-asm",
            target_arch = "aarch64",
            any(target_family = "unix", target_os = "none"),
            target_pointer_width = "64",
            target_endian = "little"
        ))]
        {
            aarch64::partial_reduce(self.limbs, self.carry, b448, r2)
        }
        #[cfg(not(all(
            feature = "aarch64-asm",
            target_arch = "aarch64",
            any(target_family = "unix", target_os = "none"),
            target_pointer_width = "64",
            target_endian = "little"
        )))]
        {
            let b7 = self.limbs[7];
            let b8 = self.carry;

            // Compute b7 * b448 (5 limbs)
            let (t0, c) = mac(0, b7, b448[0], 0);
            let (t1, c) = mac(0, b7, b448[1], c);
            let (t2, c) = mac(0, b7, b448[2], c);
            let (t3, c) = mac(0, b7, b448[3], c);
            let t4 = c;

            // Accumulate b8 * r2
            let (t0, c) = mac(t0, b8, r2[0], 0);
            let (t1, c) = mac(t1, b8, r2[1], c);
            let (t2, c) = mac(t2, b8, r2[2], c);
            let (t3, c) = mac(t3, b8, r2[3], c);
            let (t4, t5) = adc(t4, 0, c);
            debug_assert!(
                t5 == 0,
                "folding term overflow: t4 + carry does not fit in 64 bits"
            );

            // Add to lower 7 limbs
            let (d0, c) = adc(self.limbs[0], t0, 0);
            let (d1, c) = adc(self.limbs[1], t1, c);
            let (d2, c) = adc(self.limbs[2], t2, c);
            let (d3, c) = adc(self.limbs[3], t3, c);
            let (d4, c) = adc(self.limbs[4], t4, c);
            let (d5, c) = adc(self.limbs[5], 0, c);
            let (d6, c) = adc(self.limbs[6], 0, c);
            let (d7, _) = adc(0, 0, c);

            // B448 < 2^253 and r2 < 2^252, so the folding term
            // b7 * B448 + b8 * r2 < 2^317 + 2^316 < 2^318.
            // The full value is < 2^448 + 2^318 < 2^449, so d7 is at most 1.
            debug_assert!(d7 <= 1);

            [d0, d1, d2, d3, d4, d5, d6, d7]
        }
    }
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn add_product(column: &mut [u64; 3], lhs: u64, rhs: u64) {
    let product = (lhs as u128) * (rhs as u128);
    let (low, low_carry) = column[0].overflowing_add(product as u64);
    let (middle, high_carry) = column[1].overflowing_add((product >> 64) as u64);
    let (middle, middle_carry) = middle.overflowing_add(low_carry as u64);
    let carry = high_carry as u64 + middle_carry as u64;
    let (high, overflow) = column[2].overflowing_add(carry);
    debug_assert!(!overflow);
    *column = [low, middle, high];
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn start_column(accumulator: u64, carry_low: u64, carry_high: u64) -> [u64; 3] {
    let (low, carry) = accumulator.overflowing_add(carry_low);
    let (middle, high) = carry_high.overflowing_add(carry as u64);
    [low, middle, high as u64]
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn start_columns(accumulator: u64, carry_low: u64, carry_high: u64) -> [[u64; 3]; 4] {
    [
        start_column(accumulator, carry_low, carry_high),
        [0; 3],
        [0; 3],
        [0; 3],
    ]
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn merge_columns(columns: [[u64; 3]; 4]) -> [u64; 3] {
    let [mut result, column1, column2, column3] = columns;
    for column in [column1, column2, column3] {
        let (low, carry) = adc(result[0], column[0], 0);
        let (middle, carry) = adc(result[1], column[1], carry);
        let (high, overflow) = adc(result[2], column[2], carry);
        debug_assert_eq!(overflow, 0);
        result = [low, middle, high];
    }
    result
}

#[cfg(test)]
mod tests {
    use super::{DeferredField, Product};
    use crate::arithmetic::mac;
    use ff::Field;
    use proptest::prelude::*;
    use rand::{Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use std::vec::Vec;

    const SEED: [u8; 16] = [
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ];

    fn mul_unreduced(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 8] {
        let (r0, carry) = mac(0, lhs[0], rhs[0], 0);
        let (r1, carry) = mac(0, lhs[0], rhs[1], carry);
        let (r2, carry) = mac(0, lhs[0], rhs[2], carry);
        let (r3, r4) = mac(0, lhs[0], rhs[3], carry);

        let (r1, carry) = mac(r1, lhs[1], rhs[0], 0);
        let (r2, carry) = mac(r2, lhs[1], rhs[1], carry);
        let (r3, carry) = mac(r3, lhs[1], rhs[2], carry);
        let (r4, r5) = mac(r4, lhs[1], rhs[3], carry);

        let (r2, carry) = mac(r2, lhs[2], rhs[0], 0);
        let (r3, carry) = mac(r3, lhs[2], rhs[1], carry);
        let (r4, carry) = mac(r4, lhs[2], rhs[2], carry);
        let (r5, r6) = mac(r5, lhs[2], rhs[3], carry);

        let (r3, carry) = mac(r3, lhs[3], rhs[0], 0);
        let (r4, carry) = mac(r4, lhs[3], rhs[1], carry);
        let (r5, carry) = mac(r5, lhs[3], rhs[2], carry);
        let (r6, r7) = mac(r6, lhs[3], rhs[3], carry);

        [r0, r1, r2, r3, r4, r5, r6, r7]
    }

    #[cfg(target_arch = "aarch64")]
    fn raw_limbs(value: &[u64; 4]) -> &[u64; 4] {
        value
    }

    #[test]
    fn fused_mul_accumulate_matches_two_pass() {
        let mut rng = XorShiftRng::from_seed(SEED);
        let max = [u64::MAX; 4];
        for case in 0..=10_000 {
            let (lhs, rhs) = if case == 0 {
                (max, max)
            } else {
                (
                    core::array::from_fn(|_| rng.next_u64()),
                    core::array::from_fn(|_| rng.next_u64()),
                )
            };
            let limbs = core::array::from_fn(|_| rng.next_u64());
            let carry = rng.next_u64() >> 1;
            let mut two_pass = Product::<()> {
                limbs,
                carry,
                _marker: core::marker::PhantomData,
            };
            let mut fused = two_pass;

            two_pass.accumulate(mul_unreduced(&lhs, &rhs));
            fused.mul_accumulate(&lhs, &rhs);

            assert_eq!(fused.limbs, two_pass.limbs);
            assert_eq!(fused.carry, two_pass.carry);
        }
    }

    /// Exercise complete carry propagation, including the external carry's
    /// last available bit, with an independent multiply-then-add reference.
    #[test]
    fn mul_accumulate_carry_boundaries() {
        let inputs = [
            [0; 4],
            [1, 0, 0, 0],
            [u64::MAX; 4],
            [0, 0, 0, u64::MAX],
            [u64::MAX, 0, u64::MAX, 0],
        ];
        for lhs in &inputs {
            for rhs in &inputs {
                for limbs in [[0; 8], [u64::MAX; 8]] {
                    for carry in [0, u64::MAX - 1] {
                        let mut expected = Product::<()> {
                            limbs,
                            carry,
                            _marker: core::marker::PhantomData,
                        };
                        let mut actual = expected;
                        expected.accumulate(mul_unreduced(lhs, rhs));
                        actual.mul_accumulate(lhs, rhs);
                        assert_eq!(actual.limbs, expected.limbs);
                        assert_eq!(actual.carry, expected.carry);
                    }
                }
            }
        }
    }

    // Use half-width digits and plain u64 arithmetic so this oracle shares
    // neither the production carry helpers nor the assembly's row schedule.
    fn reference_multiply_add_32(
        mut accumulator: [u32; 18],
        lhs: [u64; 4],
        rhs: [u64; 4],
    ) -> [u32; 18] {
        let lhs: [u32; 8] = core::array::from_fn(|i| (lhs[i / 2] >> (32 * (i % 2))) as u32);
        let rhs: [u32; 8] = core::array::from_fn(|i| (rhs[i / 2] >> (32 * (i % 2))) as u32);
        for (i, lhs) in lhs.into_iter().enumerate() {
            let mut carry = 0;
            for (j, rhs) in rhs.into_iter().enumerate() {
                // (2^32 - 1)^2 + 2 * (2^32 - 1) fits in u64.
                let sum = u64::from(lhs) * u64::from(rhs) + u64::from(accumulator[i + j]) + carry;
                accumulator[i + j] = sum as u32;
                carry = sum >> 32;
            }
            for limb in &mut accumulator[i + rhs.len()..] {
                let sum = u64::from(*limb) + carry;
                *limb = sum as u32;
                carry = sum >> 32;
            }
            assert_eq!(carry, 0, "reference accumulator overflow");
        }
        accumulator
    }

    fn arbitrary_carry_limb() -> impl Strategy<Value = u64> {
        prop_oneof![
            4 => any::<u64>(),
            1 => Just(0),
            1 => Just(1),
            1 => Just(u64::MAX),
            1 => Just(u64::MAX - 1),
            1 => Just(1 << 63),
        ]
    }

    proptest! {
        #[test]
        fn mul_accumulate_sequences_match_32_bit_reference(
            limbs in proptest::array::uniform8(arbitrary_carry_limb()),
            carry in any::<u64>(),
            products in proptest::collection::vec(
                (
                    proptest::array::uniform4(arbitrary_carry_limb()),
                    proptest::array::uniform4(arbitrary_carry_limb()),
                ),
                0..=32,
            ),
        ) {
            // Leave room for the sequence's external carries.
            let carry = carry >> 1;
            let mut actual = Product::<()> {
                limbs,
                carry,
                _marker: core::marker::PhantomData,
            };
            let words: [u64; 9] = core::array::from_fn(|i| if i < 8 { limbs[i] } else { carry });
            let mut expected: [u32; 18] =
                core::array::from_fn(|i| (words[i / 2] >> (32 * (i % 2))) as u32);
            for (lhs, rhs) in products {
                actual.mul_accumulate(&lhs, &rhs);
                expected = reference_multiply_add_32(expected, lhs, rhs);
                let words: [u64; 9] = core::array::from_fn(|i|
                    u64::from(expected[2 * i]) | (u64::from(expected[2 * i + 1]) << 32));
                prop_assert_eq!(&actual.limbs, &words[..8]);
                prop_assert_eq!(actual.carry, words[8]);
            }
        }
    }

    proptest! {
        #[test]
        fn partial_reduce_matches_32_bit_reference(
            limbs in proptest::array::uniform8(arbitrary_carry_limb()),
            carry in arbitrary_carry_limb(),
            mut b448 in proptest::array::uniform4(arbitrary_carry_limb()),
            mut r2 in proptest::array::uniform4(arbitrary_carry_limb()),
        ) {
            // Exercise the entire permitted range, including residues beyond
            // the particular constants used by the two fields.
            b448[3] &= (1 << 61) - 1;
            r2[3] &= (1 << 60) - 1;
            let accumulator = Product::<()> {
                limbs,
                carry,
                _marker: core::marker::PhantomData,
            };
            let low: [u32; 18] = core::array::from_fn(|i|
                if i < 14 { (limbs[i / 2] >> (32 * (i % 2))) as u32 } else { 0 });
            let expected = reference_multiply_add_32(low, [limbs[7], 0, 0, 0], b448);
            let expected = reference_multiply_add_32(expected, [carry, 0, 0, 0], r2);
            let words: [u64; 8] = core::array::from_fn(|i|
                u64::from(expected[2 * i]) | (u64::from(expected[2 * i + 1]) << 32));
            prop_assert_eq!(accumulator.partial_reduce(&b448, &r2), words);
            prop_assert!(words[7] <= 1);
            prop_assert_eq!(&expected[16..], &[0, 0]);
        }
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "carry overflow: too many accumulated products")]
    fn mul_accumulate_rejects_external_carry_overflow() {
        let mut accumulator = Product::<()> {
            limbs: [u64::MAX; 8],
            carry: u64::MAX,
            _marker: core::marker::PhantomData,
        };
        accumulator.mul_accumulate(&[1, 0, 0, 0], &[1, 0, 0, 0]);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn block_mul_accumulate_matches_scalar_calls() {
        let mut rng = XorShiftRng::from_seed(SEED);
        let max = [u64::MAX; 4];
        for len in [0, 1, 2, 3, 4, 5, 31, 32] {
            for case in 0..=1_000 {
                let lhs = if case == 0 {
                    vec![max; len]
                } else {
                    (0..len)
                        .map(|_| core::array::from_fn(|_| rng.next_u64()))
                        .collect::<Vec<_>>()
                };
                let rhs = if case == 0 {
                    vec![max; len]
                } else {
                    (0..len)
                        .map(|_| core::array::from_fn(|_| rng.next_u64()))
                        .collect::<Vec<_>>()
                };
                let limbs = core::array::from_fn(|_| rng.next_u64());
                let carry = rng.next_u64() >> 1;
                let mut scalar = Product::<()> {
                    limbs,
                    carry,
                    _marker: core::marker::PhantomData,
                };
                let mut blocked = scalar;

                for (lhs, rhs) in lhs.iter().zip(&rhs) {
                    scalar.mul_accumulate(lhs, rhs);
                }
                blocked.mul_accumulate_block(&lhs, &rhs, raw_limbs);

                assert_eq!(blocked.limbs, scalar.limbs, "len={len}, case={case}");
                assert_eq!(blocked.carry, scalar.carry, "len={len}, case={case}");
            }
        }
    }

    macro_rules! deferred_field_tests {
        ($F:ty, $mod:ident, $adversarial_a:expr_2021, $adversarial_b:expr_2021) => {
            mod $mod {
                use super::*;

                #[test]
                fn accumulate_roundtrip() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    for _ in 0..100 {
                        let a = <$F>::random(&mut rng);
                        let b = <$F>::random(&mut rng);
                        let mut acc = <$F as DeferredField>::Accumulator::default();
                        <$F>::mul_accumulate(&mut acc, &a, &b);
                        assert_eq!(<$F>::reduce(acc), a * b);
                    }
                }

                #[test]
                fn square_accumulate_roundtrip() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    for _ in 0..100 {
                        let a = <$F>::random(&mut rng);
                        let mut acc = <$F as DeferredField>::Accumulator::default();
                        <$F>::square_accumulate(&mut acc, &a);
                        assert_eq!(<$F>::reduce(acc), a.square());
                    }
                }

                #[test]
                fn test_inner_product() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    for len in [0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 100, 255, 256, 10_000] {
                        let a: Vec<$F> = (0..len).map(|_| <$F>::random(&mut rng)).collect();
                        let b: Vec<$F> = (0..len).map(|_| <$F>::random(&mut rng)).collect();

                        let eager: $F = a.iter().zip(b.iter()).map(|(x, y)| *x * *y).sum();
                        let lazy = <$F>::inner_product(&a, &b);

                        assert_eq!(eager, lazy, "mismatch at len={len}");
                    }
                }

                #[test]
                fn reduce_zero() {
                    assert_eq!(
                        <$F>::reduce(<$F as DeferredField>::Accumulator::default()),
                        <$F>::ZERO,
                    );
                }

                #[test]
                fn long_scalar_accumulation_matches_eager() {
                    // Force many carries beyond the eight-limb product while
                    // checking reductions at increasing sequence lengths.
                    const TERMS: usize = 1 << 16;
                    let mut rng = XorShiftRng::from_seed(SEED);
                    let mut accumulator = <$F as DeferredField>::Accumulator::default();
                    let mut expected = <$F>::ZERO;
                    for count in 1..=TERMS {
                        let lhs = <$F>::random(&mut rng);
                        let rhs = <$F>::random(&mut rng);
                        <$F>::mul_accumulate(&mut accumulator, &lhs, &rhs);
                        expected += lhs * rhs;
                        if count.is_power_of_two() {
                            assert_eq!(<$F>::reduce(accumulator), expected, "terms={count}");
                        }
                    }
                }

                #[test]
                fn square_vs_mul() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    for _ in 0..100 {
                        let a = <$F>::random(&mut rng);
                        let mut sq_acc = <$F as DeferredField>::Accumulator::default();
                        <$F>::square_accumulate(&mut sq_acc, &a);
                        let mut mul_acc = <$F as DeferredField>::Accumulator::default();
                        <$F>::mul_accumulate(&mut mul_acc, &a, &a);
                        assert_eq!(
                            <$F>::reduce(sq_acc),
                            <$F>::reduce(mul_acc),
                            "square_accumulate and mul_accumulate(a, a) diverged",
                        );
                    }
                }

                #[test]
                fn mixed_accumulate() {
                    let mut rng = XorShiftRng::from_seed(SEED);
                    for _ in 0..20 {
                        let a = <$F>::random(&mut rng);
                        let b = <$F>::random(&mut rng);
                        let c = <$F>::random(&mut rng);
                        let mut acc = <$F as DeferredField>::Accumulator::default();
                        <$F>::mul_accumulate(&mut acc, &a, &b);
                        <$F>::square_accumulate(&mut acc, &c);
                        assert_eq!(<$F>::reduce(acc), a * b + c.square());
                    }
                }

                /// Regression: elements with top limb ~0x3F whose products have
                /// limbs[7] ~0x0F. These adversarial elements exercise the
                /// partial-reduction path in the lazy Product accumulator.
                #[test]
                fn regression_overflow() {
                    let a = $adversarial_a;
                    let b = $adversarial_b;
                    let a_arr = [a; 100];
                    let b_arr = [b; 100];

                    let eager: $F = a_arr.iter().zip(b_arr.iter()).map(|(x, y)| *x * *y).sum();
                    let lazy = <$F>::inner_product(&a_arr, &b_arr);

                    assert_eq!(eager, lazy, "inner_product returned non-canonical result");
                }
            }
        };
    }

    deferred_field_tests!(
        crate::Fp,
        fp,
        crate::Fp([
            0x0361524c2cc0f859u64,
            0xae68690a78bc7175,
            0xe66cd36e68ef8f5f,
            0x3fa6524a713b7e05,
        ]),
        crate::Fp([
            0x7a1c5e3b9d204f61u64,
            0xc48e0b71a2d5f389,
            0xd9f247a0856c13be,
            0x3d8a19f5e6c7b042,
        ])
    );
    deferred_field_tests!(
        crate::Fq,
        fq,
        crate::Fq([
            0x31d0b6640589f877u64,
            0xf87f43fdf6062541,
            0xb7d6467b2f5a522a,
            0x3eb025240950fd13,
        ]),
        crate::Fq([
            0x5e9a3c71f8b20d46u64,
            0xa3d1e6f504879c2b,
            0xcb45a8d2e1f36790,
            0x3c47d2a8b10e5f93,
        ])
    );
}

#[cfg(feature = "alloc")]
pub use buffer::DeferredBuffer;

#[cfg(feature = "alloc")]
mod buffer {
    use alloc::vec::Vec;
    use core::any::TypeId;

    use super::DeferredField;

    #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
    use crate::arithmetic::avx2_fold::{self, Lanes};

    /// Casts a slice whose element type was checked to be `T`.
    #[allow(unsafe_code)]
    fn cast<G: 'static, T: 'static>(values: &[G]) -> &[T] {
        assert_eq!(TypeId::of::<G>(), TypeId::of::<T>());
        // SAFETY: `G` and `T` are the same type.
        unsafe { &*(values as *const [G] as *const [T]) }
    }

    #[allow(unsafe_code)]
    fn cast_mut<G: 'static, T: 'static>(values: &mut [G]) -> &mut [T] {
        assert_eq!(TypeId::of::<G>(), TypeId::of::<T>());
        // SAFETY: `G` and `T` are the same type.
        unsafe { &mut *(values as *mut [G] as *mut [T]) }
    }

    /// Per-row deferred accumulators for weighted sums `sum_k t_k s_k`.
    ///
    /// For the Pasta fields on builds with the AVX2 kernels, rows are
    /// accumulated four at a time in AVX2; otherwise each row holds a
    /// [`DeferredField::Accumulator`]. Callers pass rows as slices of a type
    /// `G` that must be `F` (checked at run time), so generic code can use the
    /// buffer after selecting `F` by `TypeId`.
    ///
    /// This is an internal cross-crate bridge for `halo2_proofs`.
    #[doc(hidden)]
    #[derive(Clone, Debug, Default)]
    pub struct DeferredBuffer<F: DeferredField> {
        scalar: Vec<F::Accumulator>,
        #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
        lanes: Option<LanesState<F>>,
        len: usize,
    }

    #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
    #[derive(Clone, Debug)]
    struct LanesState<F> {
        lanes: Lanes,
        /// Canonical partial sums of earlier term runs (see `MAX_TERMS`).
        partial: Option<Vec<F>>,
    }

    #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
    impl core::fmt::Debug for Lanes {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.debug_struct("Lanes").field("len", &self.len()).finish()
        }
    }

    #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
    fn is_pasta<F: 'static>() -> bool {
        TypeId::of::<F>() == TypeId::of::<crate::Fp>()
            || TypeId::of::<F>() == TypeId::of::<crate::Fq>()
    }

    /// Canonical Montgomery limbs of a Pasta element (checked type).
    #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
    fn limbs<F: 'static>(values: &[F]) -> &[[u64; 4]] {
        if TypeId::of::<F>() == TypeId::of::<crate::Fp>() {
            let v: &[crate::Fp] = cast(values);
            crate::fields::fp_limbs(v)
        } else {
            let v: &[crate::Fq] = cast(values);
            crate::fields::fq_limbs(v)
        }
    }

    impl<F: DeferredField + 'static> DeferredBuffer<F> {
        /// Resizes the buffer to `len` rows. Contents become unspecified until
        /// the next `initialize*` call.
        pub fn resize(&mut self, len: usize) {
            self.len = len;
            #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
            if is_pasta::<F>() {
                let state = self.lanes.get_or_insert_with(|| LanesState {
                    lanes: Lanes::default(),
                    partial: None,
                });
                // A previous fold's partials have the old length.
                state.partial = None;
                state.lanes.resize(len);
                return;
            }
            self.scalar.resize(len, F::Accumulator::default());
        }

        /// The number of rows.
        pub fn len(&self) -> usize {
            self.len
        }

        /// Whether the buffer has no rows.
        pub fn is_empty(&self) -> bool {
            self.len == 0
        }

        /// Starts each row's sum at `terms[i] * power`.
        pub fn initialize<G: 'static>(&mut self, terms: &[G], power: &G) {
            self.power_term(terms, power, true);
        }

        /// Adds `terms[i] * power` to each row.
        pub fn accumulate<G: 'static>(&mut self, terms: &[G], power: &G) {
            self.power_term(terms, power, false);
        }

        /// Starts each row's sum at `terms[i] * factors[i]`.
        pub fn initialize_products<G: 'static>(&mut self, terms: &[G], factors: &[G]) {
            self.product_term(terms, factors, true);
        }

        /// Adds `terms[i] * factors[i]` to each row.
        pub fn accumulate_products<G: 'static>(&mut self, terms: &[G], factors: &[G]) {
            self.product_term(terms, factors, false);
        }

        #[allow(unsafe_code)]
        fn power_term<G: 'static>(&mut self, terms: &[G], power: &G, init: bool) {
            let terms: &[F] = cast(terms);
            let power: &F = &cast(core::slice::from_ref(power))[0];
            assert_eq!(terms.len(), self.len);
            #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
            if let Some(state) = self.lanes.as_mut() {
                let restart = Self::spill_if_full(state, init);
                let power32 = power.double().double().double().double().double();
                let power32 = limbs(core::slice::from_ref(&power32))[0];
                // SAFETY: `pasta_curves_avx2` guarantees AVX2 (see
                // `avx2_sqrt`).
                unsafe {
                    avx2_fold::accumulate_power(
                        &mut state.lanes,
                        limbs(terms),
                        power32,
                        init || restart,
                    )
                };
                if init {
                    state.partial = None;
                }
                return;
            }
            for (acc, term) in self.scalar.iter_mut().zip(terms) {
                if init {
                    *acc = F::Accumulator::default();
                }
                F::mul_accumulate(acc, term, power);
            }
        }

        #[allow(unsafe_code)]
        fn product_term<G: 'static>(&mut self, terms: &[G], factors: &[G], init: bool) {
            let terms: &[F] = cast(terms);
            let factors: &[F] = cast(factors);
            assert_eq!(terms.len(), self.len);
            assert_eq!(factors.len(), self.len);
            #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
            if let Some(state) = self.lanes.as_mut() {
                let restart = Self::spill_if_full(state, init);
                // SAFETY: as in `power_term`.
                unsafe {
                    avx2_fold::accumulate_products(
                        &mut state.lanes,
                        limbs(terms),
                        limbs(factors),
                        init || restart,
                    )
                };
                if init {
                    state.partial = None;
                }
                return;
            }
            for ((acc, term), factor) in self.scalar.iter_mut().zip(terms).zip(factors) {
                if init {
                    *acc = F::Accumulator::default();
                }
                F::mul_accumulate(acc, term, factor);
            }
        }

        /// Before a term that would exceed the lane bound, moves the current
        /// sums into canonical partials; returns whether the lanes must
        /// restart with this term.
        #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
        fn spill_if_full(state: &mut LanesState<F>, init: bool) -> bool {
            if init || state.lanes.terms() < avx2_fold::MAX_TERMS {
                return false;
            }
            let mut sums = alloc::vec![F::ZERO; state.lanes.len()];
            Self::reduce_lanes(&state.lanes, &mut sums);
            match state.partial.as_mut() {
                Some(partial) => {
                    for (partial, sum) in partial.iter_mut().zip(&sums) {
                        *partial += sum;
                    }
                }
                None => state.partial = Some(sums),
            }
            true
        }

        #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
        #[allow(unsafe_code)]
        fn reduce_lanes(lanes: &Lanes, out: &mut [F]) {
            // SAFETY: as in `power_term`; `F` is a Pasta field here.
            unsafe {
                if TypeId::of::<F>() == TypeId::of::<crate::Fp>() {
                    crate::fields::fp_fold_reduce(lanes, cast_mut(out));
                } else {
                    crate::fields::fq_fold_reduce(lanes, cast_mut(out));
                }
            }
        }

        /// Writes each row's sum to `out` (canonical).
        pub fn reduce_into<G: 'static>(&self, out: &mut [G]) {
            let out: &mut [F] = cast_mut(out);
            assert_eq!(out.len(), self.len);
            #[cfg(all(feature = "sqrt-table", pasta_curves_avx2))]
            if let Some(state) = self.lanes.as_ref() {
                Self::reduce_lanes(&state.lanes, out);
                if let Some(partial) = state.partial.as_ref() {
                    for (out, partial) in out.iter_mut().zip(partial) {
                        *out += partial;
                    }
                }
                return;
            }
            for (out, acc) in out.iter_mut().zip(&self.scalar) {
                *out = F::reduce(*acc);
            }
        }
    }
}

#[cfg(all(test, feature = "alloc"))]
mod buffer_tests {
    use super::{DeferredBuffer, DeferredField};
    use crate::{Fp, Fq};
    use alloc::vec::Vec;
    use ff::Field;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    /// Folds `terms` random terms over `len` rows, or every input `fixed`.
    fn check<F: DeferredField + 'static>(len: usize, terms: usize, fixed: Option<F>) {
        let mut rng = XorShiftRng::from_seed([5; 16]);
        let value = |rng: &mut XorShiftRng| fixed.unwrap_or_else(|| F::random(&mut *rng));
        let mut buffer = DeferredBuffer::<F>::default();
        buffer.resize(len);
        let mut expected = alloc::vec![F::ZERO; len];
        for k in 0..terms {
            let t: Vec<F> = (0..len).map(|_| value(&mut rng)).collect();
            if k % 3 == 2 {
                let f: Vec<F> = (0..len).map(|_| value(&mut rng)).collect();
                for ((e, t), f) in expected.iter_mut().zip(&t).zip(&f) {
                    *e += *t * f;
                }
                if k == 0 {
                    buffer.initialize_products(&t, &f);
                } else {
                    buffer.accumulate_products(&t, &f);
                }
            } else {
                let s = value(&mut rng);
                for (e, t) in expected.iter_mut().zip(&t) {
                    *e += *t * s;
                }
                if k == 0 {
                    buffer.initialize(&t, &s);
                } else {
                    buffer.accumulate(&t, &s);
                }
            }
        }
        let mut out = alloc::vec![F::ZERO; len];
        buffer.reduce_into(&mut out);
        assert!(out == expected, "len {len} terms {terms} fixed {fixed:?}");

        // Reinitializing discards the previous sum, including partials.
        let t: Vec<F> = (0..len).map(|_| value(&mut rng)).collect();
        buffer.initialize(&t, &F::ONE);
        buffer.reduce_into(&mut out);
        assert!(out == t);
    }

    #[test]
    fn deferred_buffer_matches_field_arithmetic() {
        for len in [1, 2, 3, 4, 5, 7, 8, 9, 64] {
            for terms in [1, 2, 6, 7, 13, 247, 248, 249, 700] {
                check::<Fp>(len, terms, None);
                check::<Fq>(len, terms, None);
            }
        }
        // -1 has a zero bottom limb; 2^254 - 1 (as the Montgomery form) sets
        // every radix-2^29 limb, the worst case for column growth.
        let full = [u64::MAX, u64::MAX, u64::MAX, (1 << 62) - 1];
        for terms in [1, 6, 7, 248, 249, 700] {
            check::<Fp>(5, terms, Some(-Fp::ONE));
            check::<Fq>(5, terms, Some(-Fq::ONE));
            check::<Fp>(5, terms, Some(Fp(full)));
            check::<Fq>(5, terms, Some(Fq(full)));
        }
        check::<Fp>(2048, 40, None);
    }
}
