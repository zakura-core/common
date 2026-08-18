// Copyright (c) 2023 Privacy Scaling Explorations Team
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// This is a variable-time, four-limb specialization of the Bernstein--Yang
// safegcd inverter in crypto-bigint 0.7.5's `src/modular/safegcd.rs`. The
// implementation is derived from the algorithm in https://eprint.iacr.org/2019/266
// and that Apache-2.0 OR MIT licensed implementation.

const LIMBS: usize = 4;
const WIDE_LIMBS: usize = LIMBS + 1;
const BATCH_SIZE: u32 = 62;

type Uint = [u64; LIMBS];
type Wide = [u64; WIDE_LIMBS];
type Matrix = [[i64; 2]; 2];

#[derive(Clone, Copy)]
struct Signed {
    negative: bool,
    magnitude: Uint,
}

impl Signed {
    const ZERO: Self = Self {
        negative: false,
        magnitude: [0; LIMBS],
    };

    #[inline]
    const fn positive(magnitude: Uint) -> Self {
        Self {
            negative: false,
            magnitude,
        }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.magnitude == [0; LIMBS]
    }

    /// Returns the signed low 63 bits used to compute one divstep batch.
    #[inline]
    fn lowest(&self) -> i64 {
        let magnitude = (self.magnitude[0] & (u64::MAX >> 1)) as i64;
        if self.negative {
            magnitude.wrapping_neg()
        } else {
            magnitude
        }
    }
}

/// Computes the inverse of a Montgomery residue modulo `modulus`.
///
/// `modulus_inverse` is `modulus^-1 mod 2^64`, and `adjuster` is `R^2
/// mod modulus`. Using `R^2` makes both the input and output Montgomery
/// residues, avoiding a conversion or a final field multiplication.
pub(super) fn invert_montgomery_vartime(
    value: Uint,
    modulus: Uint,
    modulus_inverse: u64,
    adjuster: Uint,
) -> Option<Uint> {
    debug_assert_eq!(modulus[0] & 1, 1);
    debug_assert_eq!(modulus[0].wrapping_mul(modulus_inverse), 1);
    debug_assert!(!ge_uint(value, modulus));
    debug_assert!(!ge_uint(adjuster, modulus));

    if value == [0; LIMBS] {
        return None;
    }

    let (mut f, mut g) = (Signed::positive(modulus), Signed::positive(value));
    let (mut d, mut e) = (Signed::ZERO, Signed::positive(adjuster));
    let mut delta = 1i64;

    // The half-delta safegcd bound for a 256-bit container is 591 divsteps.
    let mut steps = (45907 * 256 + 30179) / 19929;
    while steps > 0 && !g.is_zero() {
        let batch = steps.min(BATCH_SIZE);
        let (next_delta, matrix) = jump(f.lowest(), g.lowest(), delta, batch);
        (f, g) = update_fg(f, g, matrix);
        (d, e) = update_de(d, e, modulus, modulus_inverse, matrix);
        delta = next_delta;
        steps -= batch;
    }

    if !g.is_zero() || f.magnitude != [1, 0, 0, 0] {
        return None;
    }

    if d.negative != f.negative && !d.is_zero() {
        Some(sub_uint(modulus, d.magnitude))
    } else {
        Some(d.magnitude)
    }
}

/// Computes a transition matrix for `batch` half-delta divsteps using only
/// the low signed 63 bits of the full-width state.
#[inline]
fn jump(mut f: i64, mut g: i64, mut delta: i64, mut batch: u32) -> (i64, Matrix) {
    debug_assert_eq!(f & 1, 1, "f must be odd");
    let mut matrix = [[1i64, 0], [0, 1]];

    while batch > 0 {
        if (g & 1) != 0 {
            if delta > 0 {
                let next_g = g.wrapping_sub(f);
                f = core::mem::replace(&mut g, next_g);
                delta = 2i64.wrapping_sub(delta);
                matrix = [
                    matrix[1],
                    [
                        matrix[1][0].wrapping_sub(matrix[0][0]),
                        matrix[1][1].wrapping_sub(matrix[0][1]),
                    ],
                ];
            } else {
                g = g.wrapping_add(f);
                delta = 2i64.wrapping_add(delta);
                matrix[1][0] = matrix[1][0].wrapping_add(matrix[0][0]);
                matrix[1][1] = matrix[1][1].wrapping_add(matrix[0][1]);
            }
        } else {
            delta = 2i64.wrapping_add(delta);
        }

        g >>= 1;
        matrix[0][0] = matrix[0][0].wrapping_shl(1);
        matrix[0][1] = matrix[0][1].wrapping_shl(1);
        batch -= 1;
    }

    (delta, matrix)
}

#[inline]
fn update_fg(a: Signed, b: Signed, matrix: Matrix) -> (Signed, Signed) {
    (
        lincomb_reduce_shift(a, b, matrix[0][0], matrix[0][1]),
        lincomb_reduce_shift(a, b, matrix[1][0], matrix[1][1]),
    )
}

#[inline]
fn update_de(
    a: Signed,
    b: Signed,
    modulus: Uint,
    modulus_inverse: u64,
    matrix: Matrix,
) -> (Signed, Signed) {
    (
        lincomb_reduce_shift_mod(a, b, matrix[0][0], matrix[0][1], modulus, modulus_inverse),
        lincomb_reduce_shift_mod(a, b, matrix[1][0], matrix[1][1], modulus, modulus_inverse),
    )
}

#[inline]
fn lincomb_reduce_shift(a: Signed, b: Signed, c: i64, d: i64) -> Signed {
    let (wide, negative) = lincomb(a, b, c, d);
    debug_assert_eq!(wide[0] & ((1u64 << BATCH_SIZE) - 1), 0);
    Signed {
        negative,
        magnitude: shr_62(wide),
    }
}

#[inline]
fn lincomb_reduce_shift_mod(
    a: Signed,
    b: Signed,
    c: i64,
    d: i64,
    modulus: Uint,
    modulus_inverse: u64,
) -> Signed {
    let (wide, mut negative) = lincomb(a, b, c, d);

    // Subtract a multiple of the modulus that clears the low 62 bits.
    let factor = wide[0].wrapping_mul(modulus_inverse) & ((1u64 << BATCH_SIZE) - 1);
    let modulus_multiple = mul_word(modulus, factor);
    let (wide, reversed) = sub_wide_abs(wide, modulus_multiple);
    negative ^= reversed;

    debug_assert_eq!(wide[0] & ((1u64 << BATCH_SIZE) - 1), 0);
    let mut magnitude = shr_62(wide);
    if ge_uint(magnitude, modulus) {
        magnitude = sub_uint(magnitude, modulus);
    }
    debug_assert!(!ge_uint(magnitude, modulus));

    Signed {
        negative: negative && magnitude != [0; LIMBS],
        magnitude,
    }
}

/// Computes the signed magnitude of `a*c + b*d` in five limbs.
#[inline]
fn lincomb(a: Signed, b: Signed, c: i64, d: i64) -> (Wide, bool) {
    let x = mul_word(a.magnitude, c.unsigned_abs());
    let y = mul_word(b.magnitude, d.unsigned_abs());
    let x_negative = a.negative ^ c.is_negative();
    let y_negative = b.negative ^ d.is_negative();

    if x_negative == y_negative {
        let sum = add_wide(x, y);
        (sum, x_negative && sum != [0; WIDE_LIMBS])
    } else {
        let (difference, y_is_larger) = sub_wide_abs(x, y);
        let negative = if y_is_larger { y_negative } else { x_negative };
        (difference, negative && difference != [0; WIDE_LIMBS])
    }
}

#[inline]
fn mul_word(value: Uint, word: u64) -> Wide {
    let mut output = [0u64; WIDE_LIMBS];
    let mut carry = 0u128;
    let mut i = 0;
    while i < LIMBS {
        let product = value[i] as u128 * word as u128 + carry;
        output[i] = product as u64;
        carry = product >> 64;
        i += 1;
    }
    output[LIMBS] = carry as u64;
    output
}

#[inline]
fn add_wide(lhs: Wide, rhs: Wide) -> Wide {
    let mut output = [0u64; WIDE_LIMBS];
    let mut carry = 0u128;
    let mut i = 0;
    while i < WIDE_LIMBS {
        let sum = lhs[i] as u128 + rhs[i] as u128 + carry;
        output[i] = sum as u64;
        carry = sum >> 64;
        i += 1;
    }
    debug_assert_eq!(carry, 0);
    output
}

/// Returns `|lhs - rhs|` and whether `rhs` was larger.
#[inline]
fn sub_wide_abs(lhs: Wide, rhs: Wide) -> (Wide, bool) {
    if ge_wide(lhs, rhs) {
        (sub_wide(lhs, rhs), false)
    } else {
        (sub_wide(rhs, lhs), true)
    }
}

#[inline]
fn sub_wide(lhs: Wide, rhs: Wide) -> Wide {
    let mut output = [0u64; WIDE_LIMBS];
    let mut borrow = 0u128;
    let mut i = 0;
    while i < WIDE_LIMBS {
        let rhs_with_borrow = rhs[i] as u128 + borrow;
        output[i] = (lhs[i] as u128).wrapping_sub(rhs_with_borrow) as u64;
        borrow = ((lhs[i] as u128) < rhs_with_borrow) as u128;
        i += 1;
    }
    debug_assert_eq!(borrow, 0);
    output
}

#[inline]
fn shr_62(value: Wide) -> Uint {
    debug_assert_eq!(value[WIDE_LIMBS - 1] >> BATCH_SIZE, 0);
    [
        (value[0] >> BATCH_SIZE) | (value[1] << 2),
        (value[1] >> BATCH_SIZE) | (value[2] << 2),
        (value[2] >> BATCH_SIZE) | (value[3] << 2),
        (value[3] >> BATCH_SIZE) | (value[4] << 2),
    ]
}

#[inline]
fn ge_wide(lhs: Wide, rhs: Wide) -> bool {
    let mut i = WIDE_LIMBS;
    while i > 0 {
        i -= 1;
        if lhs[i] != rhs[i] {
            return lhs[i] > rhs[i];
        }
    }
    true
}

#[inline]
fn ge_uint(lhs: Uint, rhs: Uint) -> bool {
    let mut i = LIMBS;
    while i > 0 {
        i -= 1;
        if lhs[i] != rhs[i] {
            return lhs[i] > rhs[i];
        }
    }
    true
}

#[inline]
fn sub_uint(lhs: Uint, rhs: Uint) -> Uint {
    let mut output = [0u64; LIMBS];
    let mut borrow = 0u128;
    let mut i = 0;
    while i < LIMBS {
        let rhs_with_borrow = rhs[i] as u128 + borrow;
        output[i] = (lhs[i] as u128).wrapping_sub(rhs_with_borrow) as u64;
        borrow = ((lhs[i] as u128) < rhs_with_borrow) as u128;
        i += 1;
    }
    debug_assert_eq!(borrow, 0);
    output
}
