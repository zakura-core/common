//! Private Apple AArch64 backend for the Pasta fields.
//!
//! Montgomery multiplication and squaring are implemented as inline `asm!`
//! blocks below; the fused repeated-squaring chain and the canonical-form
//! conversion remain in `src/asm/pasta_mul-armv8.S` and are reached through
//! `extern "C"`.
//!
//! The inline blocks are register-renamed transcriptions of the vendored
//! Semolina v0.1.4 routines (`mul_mont_pasta`, and the squaring loop body of
//! `sqr_n_mul_mont_pasta`), with rhs limbs and the modulus constants supplied
//! in registers instead of loaded from memory. Because the operands are
//! ordinary register operands and the blocks are declared
//! `options(pure, nomem, nostack)`, LLVM inlines the wrappers into callers
//! and keeps field values in registers between operations — there is no
//! call, pointer, or ABI-clobber traffic per field operation.
//!
//! Like the assembly file, the arithmetic relies on the shared Pasta modulus
//! shape: `modulus[2] = 0` and `modulus[3] = 2^62` (materialized inline as an
//! immediate). Only `modulus[0]`, `modulus[1]`, and `inv` vary between Fp
//! and Fq, so a single implementation serves both fields.
//!
//! Canonicity contract (same as the assembly): `rhs` in `mul` and the input
//! of `square` must be canonical (below the modulus). `lhs` in `mul` may be
//! an unreduced 256-bit value **only if every `rhs` limb is at most
//! `2^64 - 4`**; with both operands canonical the routines are always safe.
//! Outputs are canonical.
//!
//! The `lhs` caveat exists because `mul` keeps a five-limb accumulator (one
//! word fewer than textbook CIOS). The only carry chain that can wrap is the
//! one folding in the high cross-products: its tail computes
//! `acc4 + high(lhs[3] * rhs_limb) + carry` with `acc4 <= 2`, which reaches
//! `2^64` only when `high(lhs[3] * rhs_limb) >= 2^64 - 3`, i.e. when
//! `lhs[3]` and some `rhs` limb are both within 3 of `2^64`. A canonical
//! `lhs` has `lhs[3] <= 2^62`, and any `rhs` limb `<= 2^64 - 4` caps the
//! high product at `2^64 - 5`, so either condition alone rules the wrap out.
//! The one unreduced-`lhs` caller is `from_u512`, whose `rhs` operands are
//! the `R2`/`R3` constants; their limbs sit far below the bound (see the
//! `aarch64_asm_mul_unreduced_lhs_matches_portable` tests in `fp.rs` and
//! `fq.rs`, which pin this case against the portable implementation).
//!
//! There are no branches and no memory accesses inside the blocks, so the
//! code is constant-time.

use core::arch::asm;

type Limbs = [u64; 4];

extern "C" {
    fn pasta_curves_sqr_n_mul_mont_pasta(
        out: *mut Limbs,
        value: *const Limbs,
        count: usize,
        rhs: *const Limbs,
        modulus: *const Limbs,
        inv: u64,
    );
    fn pasta_curves_from_mont_pasta(
        out: *mut Limbs,
        value: *const Limbs,
        modulus: *const Limbs,
        inv: u64,
    );
}

/// Multiplies two Montgomery residues for a Pasta modulus. `rhs` must be
/// canonical. `lhs` may be unreduced only if every `rhs` limb is at most
/// `2^64 - 4`; see the module docs for the carry-chain bound behind this.
#[inline(always)]
pub(super) fn mul(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    let (o0, o1, o2, o3): (u64, u64, u64, u64);
    // SAFETY: straight-line register-only arithmetic; no memory access, no
    // stack use, and outputs depend only on the declared inputs.
    unsafe {
        asm!(
            // Round 0: lhs * rhs[0], then cancel the low limb.
            "mul {r0}, {a0}, {b0}",
            "mul {r1}, {a1}, {b0}",
            "mul {r2}, {a2}, {b0}",
            "mul {r3}, {a3}, {b0}",
            "umulh {t0}, {a0}, {b0}",
            "umulh {t1}, {a1}, {b0}",
            "mul {q}, {inv}, {r0}",
            "umulh {t2}, {a2}, {b0}",
            "umulh {t3}, {a3}, {b0}",
            "adds {r1}, {r1}, {t0}",
            "adcs {r2}, {r2}, {t1}",
            "mul {t1}, {p1}, {q}",
            "adcs {r3}, {r3}, {t2}",
            "adc {r4}, xzr, {t3}",
            "lsl {t3}, {q}, #62",
            "subs xzr, {r0}, #1",
            "umulh {t0}, {p0}, {q}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {p1}, {q}",
            "adcs {r2}, {r2}, xzr",
            "adcs {r3}, {r3}, {t3}",
            "lsr {t3}, {q}, #2",
            "adc {r4}, {r4}, xzr",
            "adds {r0}, {r1}, {t0}",
            "mul {t0}, {a0}, {b1}",
            "adcs {r1}, {r2}, {t1}",
            "mul {t1}, {a1}, {b1}",
            "adcs {r2}, {r3}, xzr",
            "mul {t2}, {a2}, {b1}",
            "adcs {r3}, {r4}, {t3}",
            "mul {t3}, {a3}, {b1}",
            "adc {r4}, xzr, xzr",
            // Round 1.
            "adds {r0}, {r0}, {t0}",
            "umulh {t0}, {a0}, {b1}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {a1}, {b1}",
            "adcs {r2}, {r2}, {t2}",
            "mul {q}, {inv}, {r0}",
            "umulh {t2}, {a2}, {b1}",
            "adcs {r3}, {r3}, {t3}",
            "umulh {t3}, {a3}, {b1}",
            "adc {r4}, {r4}, xzr",
            "adds {r1}, {r1}, {t0}",
            "adcs {r2}, {r2}, {t1}",
            "mul {t1}, {p1}, {q}",
            "adcs {r3}, {r3}, {t2}",
            "adc {r4}, {r4}, {t3}",
            "lsl {t3}, {q}, #62",
            "subs xzr, {r0}, #1",
            "umulh {t0}, {p0}, {q}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {p1}, {q}",
            "adcs {r2}, {r2}, xzr",
            "adcs {r3}, {r3}, {t3}",
            "lsr {t3}, {q}, #2",
            "adc {r4}, {r4}, xzr",
            "adds {r0}, {r1}, {t0}",
            "mul {t0}, {a0}, {b2}",
            "adcs {r1}, {r2}, {t1}",
            "mul {t1}, {a1}, {b2}",
            "adcs {r2}, {r3}, xzr",
            "mul {t2}, {a2}, {b2}",
            "adcs {r3}, {r4}, {t3}",
            "mul {t3}, {a3}, {b2}",
            "adc {r4}, xzr, xzr",
            // Round 2.
            "adds {r0}, {r0}, {t0}",
            "umulh {t0}, {a0}, {b2}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {a1}, {b2}",
            "adcs {r2}, {r2}, {t2}",
            "mul {q}, {inv}, {r0}",
            "umulh {t2}, {a2}, {b2}",
            "adcs {r3}, {r3}, {t3}",
            "umulh {t3}, {a3}, {b2}",
            "adc {r4}, {r4}, xzr",
            "adds {r1}, {r1}, {t0}",
            "adcs {r2}, {r2}, {t1}",
            "mul {t1}, {p1}, {q}",
            "adcs {r3}, {r3}, {t2}",
            "adc {r4}, {r4}, {t3}",
            "lsl {t3}, {q}, #62",
            "subs xzr, {r0}, #1",
            "umulh {t0}, {p0}, {q}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {p1}, {q}",
            "adcs {r2}, {r2}, xzr",
            "adcs {r3}, {r3}, {t3}",
            "lsr {t3}, {q}, #2",
            "adc {r4}, {r4}, xzr",
            "adds {r0}, {r1}, {t0}",
            "mul {t0}, {a0}, {b3}",
            "adcs {r1}, {r2}, {t1}",
            "mul {t1}, {a1}, {b3}",
            "adcs {r2}, {r3}, xzr",
            "mul {t2}, {a2}, {b3}",
            "adcs {r3}, {r4}, {t3}",
            "mul {t3}, {a3}, {b3}",
            "adc {r4}, xzr, xzr",
            // Round 3.
            "adds {r0}, {r0}, {t0}",
            "umulh {t0}, {a0}, {b3}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {a1}, {b3}",
            "adcs {r2}, {r2}, {t2}",
            "mul {q}, {inv}, {r0}",
            "umulh {t2}, {a2}, {b3}",
            "adcs {r3}, {r3}, {t3}",
            "umulh {t3}, {a3}, {b3}",
            "adc {r4}, {r4}, xzr",
            "adds {r1}, {r1}, {t0}",
            "adcs {r2}, {r2}, {t1}",
            "mul {t1}, {p1}, {q}",
            "adcs {r3}, {r3}, {t2}",
            "adc {r4}, {r4}, {t3}",
            "lsl {t3}, {q}, #62",
            "subs xzr, {r0}, #1",
            "umulh {t0}, {p0}, {q}",
            "adcs {r1}, {r1}, {t1}",
            "umulh {t1}, {p1}, {q}",
            "adcs {r2}, {r2}, xzr",
            "adcs {r3}, {r3}, {t3}",
            "lsr {t3}, {q}, #2",
            "adc {r4}, {r4}, xzr",
            // Final shift.
            "adds {r0}, {r1}, {t0}",
            "adcs {r1}, {r2}, {t1}",
            "adcs {r2}, {r3}, xzr",
            "adcs {r3}, {r4}, {t3}",
            "adc {r4}, xzr, xzr",
            // Conditional subtraction of p = [p0, p1, 0, 2^62].
            "mov {q}, #0x4000000000000000",
            "subs {t0}, {r0}, {p0}",
            "sbcs {t1}, {r1}, {p1}",
            "sbcs {t2}, {r2}, xzr",
            "sbcs {t3}, {r3}, {q}",
            "sbcs xzr, {r4}, xzr",
            "csel {r0}, {r0}, {t0}, lo",
            "csel {r1}, {r1}, {t1}, lo",
            "csel {r2}, {r2}, {t2}, lo",
            "csel {r3}, {r3}, {t3}, lo",
            a0 = in(reg) lhs[0],
            a1 = in(reg) lhs[1],
            a2 = in(reg) lhs[2],
            a3 = in(reg) lhs[3],
            b0 = in(reg) rhs[0],
            b1 = in(reg) rhs[1],
            b2 = in(reg) rhs[2],
            b3 = in(reg) rhs[3],
            p0 = in(reg) modulus[0],
            p1 = in(reg) modulus[1],
            inv = in(reg) inv,
            q = out(reg) _,
            t0 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            t3 = out(reg) _,
            r0 = out(reg) o0,
            r1 = out(reg) o1,
            r2 = out(reg) o2,
            r3 = out(reg) o3,
            r4 = out(reg) _,
            options(pure, nomem, nostack),
        );
    }
    [o0, o1, o2, o3]
}

/// Squares a canonical Montgomery residue for a Pasta modulus.
#[inline(always)]
pub(super) fn square(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    let mut a0 = value[0];
    let mut a1 = value[1];
    let mut a2 = value[2];
    let mut a3 = value[3];
    // SAFETY: straight-line register-only arithmetic; no memory access, no
    // stack use, and outputs depend only on the declared inputs.
    unsafe {
        asm!(
            // 512-bit square: cross products, doubling, diagonals.
            "mul {z1}, {a1}, {a0}",
            "umulh {w1}, {a1}, {a0}",
            "mul {z2}, {a2}, {a0}",
            "umulh {w2}, {a2}, {a0}",
            "mul {z3}, {a3}, {a0}",
            "umulh {z4}, {a3}, {a0}",
            "adds {z2}, {z2}, {w1}",
            "mul {w0}, {a2}, {a1}",
            "umulh {w1}, {a2}, {a1}",
            "adcs {z3}, {z3}, {w2}",
            "mul {w2}, {a3}, {a1}",
            "umulh {w3}, {a3}, {a1}",
            "adc {z4}, {z4}, xzr",
            "mul {z5}, {a3}, {a2}",
            "umulh {z6}, {a3}, {a2}",
            "adds {w1}, {w1}, {w2}",
            "mul {z0}, {a0}, {a0}",
            "adc {w2}, {w3}, xzr",
            "adds {z3}, {z3}, {w0}",
            "umulh {a0}, {a0}, {a0}",
            "adcs {z4}, {z4}, {w1}",
            "mul {w1}, {a1}, {a1}",
            "adcs {z5}, {z5}, {w2}",
            "umulh {a1}, {a1}, {a1}",
            "adc {z6}, {z6}, xzr",
            "adds {z1}, {z1}, {z1}",
            "mul {w2}, {a2}, {a2}",
            "adcs {z2}, {z2}, {z2}",
            "umulh {a2}, {a2}, {a2}",
            "adcs {z3}, {z3}, {z3}",
            "mul {w3}, {a3}, {a3}",
            "adcs {z4}, {z4}, {z4}",
            "umulh {a3}, {a3}, {a3}",
            "adcs {z5}, {z5}, {z5}",
            "adcs {z6}, {z6}, {z6}",
            "adc {z7}, xzr, xzr",
            "mul {q}, {inv}, {z0}",
            "adds {z1}, {z1}, {a0}",
            "adcs {z2}, {z2}, {w1}",
            "adcs {z3}, {z3}, {a1}",
            "adcs {z4}, {z4}, {w2}",
            "adcs {z5}, {z5}, {a2}",
            "adcs {z6}, {z6}, {w3}",
            "adc {z7}, {z7}, {a3}",
            // Four Montgomery cancellations on the low half.
            "mul {w1}, {p1}, {q}",
            "lsl {w3}, {q}, #62",
            "subs xzr, {z0}, #1",
            "umulh {w0}, {p0}, {q}",
            "adcs {z1}, {z1}, {w1}",
            "umulh {w1}, {p1}, {q}",
            "adcs {z2}, {z2}, xzr",
            "adcs {z3}, {z3}, {w3}",
            "lsr {w3}, {q}, #2",
            "adc {cy}, xzr, xzr",
            "adds {z0}, {z1}, {w0}",
            "adcs {z1}, {z2}, {w1}",
            "adcs {z2}, {z3}, xzr",
            "mul {q}, {inv}, {z0}",
            "adc {z3}, {cy}, {w3}",
            "mul {w1}, {p1}, {q}",
            "lsl {w3}, {q}, #62",
            "subs xzr, {z0}, #1",
            "umulh {w0}, {p0}, {q}",
            "adcs {z1}, {z1}, {w1}",
            "umulh {w1}, {p1}, {q}",
            "adcs {z2}, {z2}, xzr",
            "adcs {z3}, {z3}, {w3}",
            "lsr {w3}, {q}, #2",
            "adc {cy}, xzr, xzr",
            "adds {z0}, {z1}, {w0}",
            "adcs {z1}, {z2}, {w1}",
            "adcs {z2}, {z3}, xzr",
            "mul {q}, {inv}, {z0}",
            "adc {z3}, {cy}, {w3}",
            "mul {w1}, {p1}, {q}",
            "lsl {w3}, {q}, #62",
            "subs xzr, {z0}, #1",
            "umulh {w0}, {p0}, {q}",
            "adcs {z1}, {z1}, {w1}",
            "umulh {w1}, {p1}, {q}",
            "adcs {z2}, {z2}, xzr",
            "adcs {z3}, {z3}, {w3}",
            "lsr {w3}, {q}, #2",
            "adc {cy}, xzr, xzr",
            "adds {z0}, {z1}, {w0}",
            "adcs {z1}, {z2}, {w1}",
            "adcs {z2}, {z3}, xzr",
            "mul {q}, {inv}, {z0}",
            "adc {z3}, {cy}, {w3}",
            "mul {w1}, {p1}, {q}",
            "lsl {w3}, {q}, #62",
            "subs xzr, {z0}, #1",
            "umulh {w0}, {p0}, {q}",
            "adcs {z1}, {z1}, {w1}",
            "umulh {w1}, {p1}, {q}",
            "adcs {z2}, {z2}, xzr",
            "adcs {z3}, {z3}, {w3}",
            "lsr {w3}, {q}, #2",
            "adc {cy}, xzr, xzr",
            "adds {z0}, {z1}, {w0}",
            "adcs {z1}, {z2}, {w1}",
            "adcs {z2}, {z3}, xzr",
            "adc {z3}, {cy}, {w3}",
            // Add the upper half of the square.
            "adds {a0}, {z0}, {z4}",
            "adcs {a1}, {z1}, {z5}",
            "adcs {a2}, {z2}, {z6}",
            "adc {a3}, {z3}, {z7}",
            // Conditional subtraction (candidate < 1.25p).
            "mov {q}, #0x4000000000000000",
            "subs {z0}, {a0}, {p0}",
            "sbcs {z1}, {a1}, {p1}",
            "sbcs {z2}, {a2}, xzr",
            "sbcs {z3}, {a3}, {q}",
            "csel {a0}, {a0}, {z0}, lo",
            "csel {a1}, {a1}, {z1}, lo",
            "csel {a2}, {a2}, {z2}, lo",
            "csel {a3}, {a3}, {z3}, lo",
            a0 = inout(reg) a0,
            a1 = inout(reg) a1,
            a2 = inout(reg) a2,
            a3 = inout(reg) a3,
            p0 = in(reg) modulus[0],
            p1 = in(reg) modulus[1],
            inv = in(reg) inv,
            q = out(reg) _,
            cy = out(reg) _,
            z0 = out(reg) _,
            z1 = out(reg) _,
            z2 = out(reg) _,
            z3 = out(reg) _,
            z4 = out(reg) _,
            z5 = out(reg) _,
            z6 = out(reg) _,
            z7 = out(reg) _,
            w0 = out(reg) _,
            w1 = out(reg) _,
            w2 = out(reg) _,
            w3 = out(reg) _,
            options(pure, nomem, nostack),
        );
    }
    [a0, a1, a2, a3]
}

/// Squares a canonical Montgomery residue `count` times, then multiplies the
/// result by the canonical Montgomery residue `rhs`, keeping the accumulator
/// in registers throughout.
#[inline]
pub(super) fn sqr_n_mul(
    value: &Limbs,
    count: usize,
    rhs: &Limbs,
    modulus: &Limbs,
    inv: u64,
) -> Limbs {
    // The assembly decrements the count before testing it, so a zero count
    // would wrap around and effectively never terminate.
    assert!(count >= 1);
    let mut out = Limbs::default();
    // SAFETY: All pointers refer to four initialized `u64` limbs for the
    // duration of the call. The backend writes exactly four limbs to `out`.
    unsafe {
        pasta_curves_sqr_n_mul_mont_pasta(&mut out, value, count, rhs, modulus, inv);
    }
    out
}

/// Converts a canonical Montgomery residue into its canonical integer.
#[inline]
pub(super) fn from_mont(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    let mut out = Limbs::default();
    // SAFETY: All pointers refer to four initialized `u64` limbs for the
    // duration of the call. The backend writes exactly four limbs to `out`.
    unsafe {
        pasta_curves_from_mont_pasta(&mut out, value, modulus, inv);
    }
    out
}
