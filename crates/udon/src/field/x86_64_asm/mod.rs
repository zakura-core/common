//! x86-64 arithmetic for loose Pasta Montgomery residues.
//!
//! This contains the crate's unsafe arithmetic for x86-64, selected by the
//! build script (see the crate-level `x86_64-asm` feature documentation) and
//! unavailable under Miri. Multiplication uses MULX (BMI2) with ADCX/ADOX
//! dual carry chains (ADX). There is no runtime dispatch: an assembly-enabled
//! binary faults with an illegal instruction on a CPU without BMI2 and ADX.
//!
//! The multiplication and squaring rounds are transcriptions of the x86-64
//! backend in zakura-pasta-curves, itself a transcription of the AArch64
//! Semolina routines behind the `aarch64-asm` backend: a five-limb CIOS
//! accumulator, one Montgomery cancellation per round, and the shared Pasta
//! modulus shape, `p[2] = 0` and `p[3] = 2^62`, materialized as shifts so
//! only `p[0]`, `p[1]`, and `inv` distinguish the two fields. Unlike the
//! pasta_curves kernels, every routine here keeps the loose `[0, 2p)`
//! contract of the Rust kernels in `pasta::montgomery` and omits the closing
//! conditional subtraction; it computes the same integer, so the Rust kernel
//! remains its oracle. The bounds analysis of the AArch64 module carries over
//! verbatim: with both inputs below `2p`, the top limbs are at most `2^63`,
//! each round's five-limb sum `acc + lhs * b + q * p` stays below `2^320`,
//! and the final candidate `(lhs * rhs + m * p) / R` is below `2p < R` by the
//! closure proof in `pasta::montgomery::square_run`, so no fifth limb exists.
//! Wide reduction accepts the larger bound documented in
//! `pasta::montgomery::montgomery_reduce_unreduced`.
//!
//! Operand limbs are addressed through pointers (`readonly` memory operands)
//! rather than individual registers: x86-64 leaves thirteen allocatable
//! registers to inline assembly, and the interleaved rounds need nearly all
//! of them. The modulus and inverse share one parameter block. Unlike the
//! zakura-pasta-curves backend, the register-heavy blocks are inlined: the
//! call boundary and its memory round trip measured dearer than the spills
//! it avoids (multiplication 15.0 ns inlined against 15.6 ns called, squaring
//! 12.9 ns against 16.1 ns, and 1024-term inner products 8.2 µs against
//! 13.9 µs on Skylake-X), and the allocator spills callers' values around
//! the block rather than failing. The repeated-square chains loop in Rust
//! around the inlined square, so no external assembler is needed.
//!
//! Arithmetic bounds concern correctness, not memory validity. Every block
//! reads only the fixed-size arrays behind its declared pointers and has no
//! branches; arbitrary limb bits cannot change addresses, stack use, or
//! control flow.

#![allow(unsafe_code)]

use core::arch::asm;

use super::pasta::PrimeModulus;

mod products;
pub(crate) use products::{mul_accumulate, partial_reduce};

type Limbs = [u64; 4];

/// The modulus limbs followed by `-p^-1 mod 2^64`, addressed through one
/// pointer by every Montgomery kernel.
#[inline(always)]
fn params<M: PrimeModulus>() -> &'static [u64; 5] {
    const {
        &[
            M::MODULUS[0],
            M::MODULUS[1],
            M::MODULUS[2],
            M::MODULUS[3],
            M::MONTGOMERY_INV,
        ]
    }
}

#[inline(always)]
fn assert_loose<M: PrimeModulus>(value: &Limbs) {
    debug_assert!(
        value
            .iter()
            .rev()
            .cmp(M::TWICE_MODULUS.iter().rev())
            .is_lt()
    );
}

// The three shared instruction sequences below are assembled by `concat!` so
// one text serves every kernel. Each names its registers explicitly: the
// `asm!` block using a sequence must declare those operands, and `rdx` is
// the implicit MULX source throughout. Memory operands are passed as literal
// `[base + offset]` strings so the same sequence can read through whichever
// pointer a kernel holds its operands behind.

/// The 512-bit square of the four limbs at `$a0..$a3` into `{z0}..{z7}`:
/// cross products, one doubling pass, then the diagonals. Clobbers `{t1}`,
/// `{t2}`, and `rdx`. The square of a value below `2^255` is below `2^510`,
/// so neither the doubling pass nor the diagonal chain carries out of `{z7}`.
macro_rules! square_wide {
    ($a0:literal, $a1:literal, $a2:literal, $a3:literal) => {
        concat!(
            "xor {z5:e}, {z5:e}\n",
            "xor {z6:e}, {z6:e}\n",
            "xor {z7:e}, {z7:e}\n",
            "mov rdx, qword ptr ",
            $a0,
            "\n",
            // a0*a1, a0*a2, a0*a3.
            "mulx {t1}, {z1}, qword ptr ",
            $a1,
            "\n",
            "mulx {t2}, {z2}, qword ptr ",
            $a2,
            "\n",
            "mulx {z4}, {z3}, qword ptr ",
            $a3,
            "\n",
            "add {z2}, {t1}\n",
            "adc {z3}, {t2}\n",
            "adc {z4}, 0\n",
            "mov rdx, qword ptr ",
            $a1,
            "\n",
            // a1*a2, a1*a3.
            "mulx {t2}, {t1}, qword ptr ",
            $a2,
            "\n",
            "add {z3}, {t1}\n",
            "adc {z4}, {t2}\n",
            "adc {z5}, 0\n",
            "mulx {t2}, {t1}, qword ptr ",
            $a3,
            "\n",
            "add {z4}, {t1}\n",
            "adc {z5}, {t2}\n",
            "adc {z6}, 0\n",
            "mov rdx, qword ptr ",
            $a2,
            "\n",
            // a2*a3.
            "mulx {t2}, {t1}, qword ptr ",
            $a3,
            "\n",
            "add {z5}, {t1}\n",
            "adc {z6}, {t2}\n",
            "adc {z7}, 0\n",
            // Double the cross products.
            "add {z1}, {z1}\n",
            "adc {z2}, {z2}\n",
            "adc {z3}, {z3}\n",
            "adc {z4}, {z4}\n",
            "adc {z5}, {z5}\n",
            "adc {z6}, {z6}\n",
            "adc {z7}, {z7}\n",
            // Add the diagonal squares in one carry chain (MOV and MULX
            // preserve flags).
            "mov rdx, qword ptr ",
            $a0,
            "\n",
            "mulx {t2}, {z0}, rdx\n",
            "add {z1}, {t2}\n",
            "mov rdx, qword ptr ",
            $a1,
            "\n",
            "mulx {t2}, {t1}, rdx\n",
            "adc {z2}, {t1}\n",
            "adc {z3}, {t2}\n",
            "mov rdx, qword ptr ",
            $a2,
            "\n",
            "mulx {t2}, {t1}, rdx\n",
            "adc {z4}, {t1}\n",
            "adc {z5}, {t2}\n",
            "mov rdx, qword ptr ",
            $a3,
            "\n",
            "mulx {t2}, {t1}, rdx\n",
            "adc {z6}, {t1}\n",
            "adc {z7}, {t2}\n",
        )
    };
}

/// Four Montgomery cancellations on the window `{z0}..{z3}`, dividing the
/// low product half by `R`: each step chooses `q` so the lowest live limb
/// plus `q * p[0]` vanishes, adds `q * p`, and drops that limb. The window
/// rotates down one register per step with `{cy}` as the carried fifth limb,
/// so the reduced value ends in `{cy}, {z0}, {z1}, {z2}`. Reads the
/// parameters at `{p}` and clobbers `{t1}`, `{t2}`, and `rdx`. Each step's
/// sum is below `2^256 + 2^64 * p < 2^319`, so the shifted window fits four
/// limbs and the carried limb stays below `2^63`.
macro_rules! cancel_low_half {
    () => {
        concat!(
            // Step 0: window [z0, z1, z2, z3], carry into cy.
            "mov rdx, {z0}\n",
            "imul rdx, qword ptr [{p} + 32]\n",
            // t1/t2 = low/high(q*p1).
            "mulx {t2}, {t1}, qword ptr [{p} + 8]\n",
            "mov {cy}, rdx\n",
            // low(q*p3); p2 is zero.
            "shl {cy}, 62\n",
            // low(q*p0) cancels limb 0; its carry is one exactly when the
            // limb is nonzero, which NEG leaves in CF.
            "neg {z0}\n",
            "adc {z1}, {t1}\n",
            "adc {z2}, 0\n",
            "adc {z3}, {cy}\n",
            "mov {cy}, 0\n",
            "adc {cy}, 0\n",
            // t1 = high(q*p0); the low half is spent.
            "mulx {t1}, {z0}, qword ptr [{p}]\n",
            "mov {z0}, rdx\n",
            "shr {z0}, 2\n",
            "add {z1}, {t1}\n",
            "adc {z2}, {t2}\n",
            "adc {z3}, 0\n",
            "adc {cy}, {z0}\n",
            // Step 1: window [z1, z2, z3, cy], carry into z0.
            "mov rdx, {z1}\n",
            "imul rdx, qword ptr [{p} + 32]\n",
            "mulx {t2}, {t1}, qword ptr [{p} + 8]\n",
            "mov {z0}, rdx\n",
            "shl {z0}, 62\n",
            "neg {z1}\n",
            "adc {z2}, {t1}\n",
            "adc {z3}, 0\n",
            "adc {cy}, {z0}\n",
            "mov {z0}, 0\n",
            "adc {z0}, 0\n",
            "mulx {t1}, {z1}, qword ptr [{p}]\n",
            "mov {z1}, rdx\n",
            "shr {z1}, 2\n",
            "add {z2}, {t1}\n",
            "adc {z3}, {t2}\n",
            "adc {cy}, 0\n",
            "adc {z0}, {z1}\n",
            // Step 2: window [z2, z3, cy, z0], carry into z1.
            "mov rdx, {z2}\n",
            "imul rdx, qword ptr [{p} + 32]\n",
            "mulx {t2}, {t1}, qword ptr [{p} + 8]\n",
            "mov {z1}, rdx\n",
            "shl {z1}, 62\n",
            "neg {z2}\n",
            "adc {z3}, {t1}\n",
            "adc {cy}, 0\n",
            "adc {z0}, {z1}\n",
            "mov {z1}, 0\n",
            "adc {z1}, 0\n",
            "mulx {t1}, {z2}, qword ptr [{p}]\n",
            "mov {z2}, rdx\n",
            "shr {z2}, 2\n",
            "add {z3}, {t1}\n",
            "adc {cy}, {t2}\n",
            "adc {z0}, 0\n",
            "adc {z1}, {z2}\n",
            // Step 3: window [z3, cy, z0, z1], carry into z2.
            "mov rdx, {z3}\n",
            "imul rdx, qword ptr [{p} + 32]\n",
            "mulx {t2}, {t1}, qword ptr [{p} + 8]\n",
            "mov {z2}, rdx\n",
            "shl {z2}, 62\n",
            "neg {z3}\n",
            "adc {cy}, {t1}\n",
            "adc {z0}, 0\n",
            "adc {z1}, {z2}\n",
            "mov {z2}, 0\n",
            "adc {z2}, 0\n",
            "mulx {t1}, {z3}, qword ptr [{p}]\n",
            "mov {z3}, rdx\n",
            "shr {z3}, 2\n",
            "add {cy}, {t1}\n",
            "adc {z0}, {t2}\n",
            "adc {z1}, 0\n",
            "adc {z2}, {z3}\n",
        )
    };
}

/// Montgomery multiplication of the limbs at `$a0..$a3` by those at
/// `$b0..$b3`, both below `2p`, leaving `lhs * rhs * R^-1 mod p` below `2p`
/// in `{z4}, {z0}, {z1}, {z2}`. The five-limb accumulator starts in
/// `{z0}..{z4}` and its window rotates down one register per round: the
/// register cancelled by the round's Montgomery step becomes the next round's
/// fifth limb. `{z5}`, `{z6}`, `{z7}` stage multiplier halves and shifted
/// `q * p[3]` terms so no flag-writing instruction lands inside a carry
/// chain. Reads the parameters at `{p}` and clobbers `rdx`.
macro_rules! mul_rounds {
    ($a0:literal, $a1:literal, $a2:literal, $a3:literal,
     $b0:literal, $b1:literal, $b2:literal, $b3:literal) => {
        concat!(
            // Round 0: initialize the accumulator with lhs * b[0].
            "mov rdx, qword ptr ",
            $b0,
            "\n",
            "mulx {z1}, {z0}, qword ptr ",
            $a0,
            "\n",
            "mulx {z2}, {z5}, qword ptr ",
            $a1,
            "\n",
            "add {z1}, {z5}\n",
            "mulx {z3}, {z5}, qword ptr ",
            $a2,
            "\n",
            "adc {z2}, {z5}\n",
            "mulx {z4}, {z5}, qword ptr ",
            $a3,
            "\n",
            "adc {z3}, {z5}\n",
            "adc {z4}, 0\n",
            // Montgomery step 0: q = limb0 * inv; add q*p; shift one limb.
            "mov rdx, {z0}\n",
            "imul rdx, qword ptr [{p} + 32]\n",
            "mulx {z6}, {z5}, qword ptr [{p} + 8]\n",
            "mov {z7}, rdx\n",
            "shl {z7}, 62\n",
            "neg {z0}\n",
            "adc {z1}, {z5}\n",
            "adc {z2}, 0\n",
            "adc {z3}, {z7}\n",
            "adc {z4}, 0\n",
            "mulx {z5}, {z7}, qword ptr [{p}]\n",
            "mov {z7}, rdx\n",
            "shr {z7}, 2\n",
            "mov {z0}, 0\n",
            "add {z1}, {z5}\n",
            "adc {z2}, {z6}\n",
            "adc {z3}, 0\n",
            "adc {z4}, {z7}\n",
            "adc {z0}, 0\n",
            // Round 1: window [z1, z2, z3, z4, z0]; add lhs * b[1] on dual
            // carry chains (CF: low halves, OF: high halves).
            "mov rdx, qword ptr ",
            $b1,
            "\n",
            "xor {z5:e}, {z5:e}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a0,
            "\n",
            "adcx {z1}, {z5}\n",
            "adox {z2}, {z6}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a1,
            "\n",
            "adcx {z2}, {z5}\n",
            "adox {z3}, {z6}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a2,
            "\n",
            "adcx {z3}, {z5}\n",
            "adox {z4}, {z6}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a3,
            "\n",
            "adcx {z4}, {z5}\n",
            "adox {z0}, {z6}\n",
            "mov {z5}, 0\n",
            "adcx {z0}, {z5}\n",
            "adox {z0}, {z5}\n",
            // Montgomery step 1.
            "mov rdx, {z1}\n",
            "imul rdx, qword ptr [{p} + 32]\n",
            "mulx {z6}, {z5}, qword ptr [{p} + 8]\n",
            "mov {z7}, rdx\n",
            "shl {z7}, 62\n",
            "neg {z1}\n",
            "adc {z2}, {z5}\n",
            "adc {z3}, 0\n",
            "adc {z4}, {z7}\n",
            "adc {z0}, 0\n",
            "mulx {z5}, {z7}, qword ptr [{p}]\n",
            "mov {z7}, rdx\n",
            "shr {z7}, 2\n",
            "mov {z1}, 0\n",
            "add {z2}, {z5}\n",
            "adc {z3}, {z6}\n",
            "adc {z4}, 0\n",
            "adc {z0}, {z7}\n",
            "adc {z1}, 0\n",
            // Round 2: window [z2, z3, z4, z0, z1]; add lhs * b[2].
            "mov rdx, qword ptr ",
            $b2,
            "\n",
            "xor {z5:e}, {z5:e}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a0,
            "\n",
            "adcx {z2}, {z5}\n",
            "adox {z3}, {z6}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a1,
            "\n",
            "adcx {z3}, {z5}\n",
            "adox {z4}, {z6}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a2,
            "\n",
            "adcx {z4}, {z5}\n",
            "adox {z0}, {z6}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a3,
            "\n",
            "adcx {z0}, {z5}\n",
            "adox {z1}, {z6}\n",
            "mov {z5}, 0\n",
            "adcx {z1}, {z5}\n",
            "adox {z1}, {z5}\n",
            // Montgomery step 2.
            "mov rdx, {z2}\n",
            "imul rdx, qword ptr [{p} + 32]\n",
            "mulx {z6}, {z5}, qword ptr [{p} + 8]\n",
            "mov {z7}, rdx\n",
            "shl {z7}, 62\n",
            "neg {z2}\n",
            "adc {z3}, {z5}\n",
            "adc {z4}, 0\n",
            "adc {z0}, {z7}\n",
            "adc {z1}, 0\n",
            "mulx {z5}, {z7}, qword ptr [{p}]\n",
            "mov {z7}, rdx\n",
            "shr {z7}, 2\n",
            "mov {z2}, 0\n",
            "add {z3}, {z5}\n",
            "adc {z4}, {z6}\n",
            "adc {z0}, 0\n",
            "adc {z1}, {z7}\n",
            "adc {z2}, 0\n",
            // Round 3: window [z3, z4, z0, z1, z2]; add lhs * b[3].
            "mov rdx, qword ptr ",
            $b3,
            "\n",
            "xor {z5:e}, {z5:e}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a0,
            "\n",
            "adcx {z3}, {z5}\n",
            "adox {z4}, {z6}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a1,
            "\n",
            "adcx {z4}, {z5}\n",
            "adox {z0}, {z6}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a2,
            "\n",
            "adcx {z0}, {z5}\n",
            "adox {z1}, {z6}\n",
            "mulx {z6}, {z5}, qword ptr ",
            $a3,
            "\n",
            "adcx {z1}, {z5}\n",
            "adox {z2}, {z6}\n",
            "mov {z5}, 0\n",
            "adcx {z2}, {z5}\n",
            "adox {z2}, {z5}\n",
            // Montgomery step 3. Loose inputs bound the candidate below
            // 2p < R (see the module docs), so the final shift produces no
            // fifth limb and the shift's carry adc is omitted.
            "mov rdx, {z3}\n",
            "imul rdx, qword ptr [{p} + 32]\n",
            "mulx {z6}, {z5}, qword ptr [{p} + 8]\n",
            "mov {z7}, rdx\n",
            "shl {z7}, 62\n",
            "neg {z3}\n",
            "adc {z4}, {z5}\n",
            "adc {z0}, 0\n",
            "adc {z1}, {z7}\n",
            "adc {z2}, 0\n",
            "mulx {z5}, {z7}, qword ptr [{p}]\n",
            "mov {z7}, rdx\n",
            "shr {z7}, 2\n",
            "add {z4}, {z5}\n",
            "adc {z0}, {z6}\n",
            "adc {z1}, 0\n",
            "adc {z2}, {z7}\n",
        )
    };
}

/// Computes `lhs * rhs * R^-1 mod p` in `[0, 2p)` for inputs below `2p`.
// Inlined despite consuming nearly every register; see the module docs.
#[inline(always)]
pub(crate) fn montgomery_multiply_loose<M: PrimeModulus>(lhs: &Limbs, rhs: &Limbs) -> Limbs {
    assert_loose::<M>(lhs);
    assert_loose::<M>(rhs);
    let (o0, o1, o2, o3): (u64, u64, u64, u64);
    // SAFETY: straight-line arithmetic reading only the thirteen words
    // behind the three passed references (`readonly`); no stack use, and
    // outputs depend only on the declared inputs. All memory addresses are
    // input-independent.
    unsafe {
        asm!(
            mul_rounds!(
                "[{a}]", "[{a} + 8]", "[{a} + 16]", "[{a} + 24]",
                "[{b}]", "[{b} + 8]", "[{b} + 16]", "[{b} + 24]"
            ),
            a = in(reg) lhs.as_ptr(),
            b = in(reg) rhs.as_ptr(),
            p = in(reg) params::<M>().as_ptr(),
            z0 = out(reg) o1,
            z1 = out(reg) o2,
            z2 = out(reg) o3,
            z3 = out(reg) _,
            z4 = out(reg) o0,
            z5 = out(reg) _,
            z6 = out(reg) _,
            z7 = out(reg) _,
            out("rdx") _,
            options(pure, readonly, nostack),
        );
    }
    [o0, o1, o2, o3]
}

/// Computes `lhs + rhs mod 2p` in `[0, 2p)` for inputs below `2p`.
///
/// `twice_modulus` is `2p`. The sum is below `4p`, which can exceed the
/// radix, so the block keeps the top carry and folds it into the single
/// conditional subtraction of `2p`: the reduced candidate is selected when
/// the addition carried or the subtraction did not borrow. This computes the
/// same function as the portable kernel in `pasta::montgomery` on all inputs.
#[inline(always)]
pub(crate) fn add_loose(lhs: &Limbs, rhs: &Limbs, twice_modulus: &Limbs) -> Limbs {
    let [mut r0, mut r1, mut r2, mut r3] = *lhs;
    // SAFETY: straight-line arithmetic reading only the words behind the two
    // passed references (`readonly`); no stack use, and outputs depend only
    // on the declared inputs. All memory addresses are input-independent.
    unsafe {
        asm!(
            "mov {c}, 0",
            "add {r0}, qword ptr [{b}]",
            "adc {r1}, qword ptr [{b} + 8]",
            "adc {r2}, qword ptr [{b} + 16]",
            "adc {r3}, qword ptr [{b} + 24]",
            "adc {c}, 0",                        // c = carry out of the sum.
            "mov {t0}, {r0}",
            "mov {t1}, {r1}",
            "mov {t2}, {r2}",
            "mov {t3}, {r3}",
            "sub {t0}, qword ptr [{m}]",
            "sbb {t1}, qword ptr [{m} + 8]",
            "sbb {t2}, qword ptr [{m} + 16]",
            "sbb {t3}, qword ptr [{m} + 24]",
            // CF is set exactly when the sum did not carry and the
            // subtraction borrowed: keep the sum, otherwise reduce.
            "sbb {c}, 0",
            "cmovnc {r0}, {t0}",
            "cmovnc {r1}, {t1}",
            "cmovnc {r2}, {t2}",
            "cmovnc {r3}, {t3}",
            r0 = inout(reg) r0,
            r1 = inout(reg) r1,
            r2 = inout(reg) r2,
            r3 = inout(reg) r3,
            b = in(reg) rhs.as_ptr(),
            m = in(reg) twice_modulus.as_ptr(),
            t0 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            t3 = out(reg) _,
            c = out(reg) _,
            options(pure, readonly, nostack),
        );
    }
    [r0, r1, r2, r3]
}

/// Computes `lhs - rhs mod modulus` for inputs below `modulus`.
///
/// Loose arithmetic supplies `2p`; canonical arithmetic supplies `p`. The
/// modulus is added back exactly when the subtraction borrows, discarding
/// the final carry after wrapping modulo `2^256`.
#[inline(always)]
pub(crate) fn sub_loose(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs) -> Limbs {
    let [mut r0, mut r1, mut r2, mut r3] = *lhs;
    // SAFETY: straight-line arithmetic reading only the words behind the two
    // passed references (`readonly`); no stack use, and outputs depend only
    // on the declared inputs. The conditional loads use fixed,
    // input-independent addresses.
    unsafe {
        asm!(
            "sub {r0}, qword ptr [{b}]",
            "sbb {r1}, qword ptr [{b} + 8]",
            "sbb {r2}, qword ptr [{b} + 16]",
            "sbb {r3}, qword ptr [{b} + 24]",
            // MOV and CMOV preserve the borrow flag from the subtraction.
            "mov {m0}, 0",
            "mov {m1}, 0",
            "mov {m2}, 0",
            "mov {m3}, 0",
            "cmovc {m0}, qword ptr [{p}]",
            "cmovc {m1}, qword ptr [{p} + 8]",
            "cmovc {m2}, qword ptr [{p} + 16]",
            "cmovc {m3}, qword ptr [{p} + 24]",
            "add {r0}, {m0}",
            "adc {r1}, {m1}",
            "adc {r2}, {m2}",
            "adc {r3}, {m3}",
            r0 = inout(reg) r0,
            r1 = inout(reg) r1,
            r2 = inout(reg) r2,
            r3 = inout(reg) r3,
            b = in(reg) rhs.as_ptr(),
            p = in(reg) modulus.as_ptr(),
            m0 = out(reg) _,
            m1 = out(reg) _,
            m2 = out(reg) _,
            m3 = out(reg) _,
            options(pure, readonly, nostack),
        );
    }
    [r0, r1, r2, r3]
}

/// Subtracts two unsigned 256-bit integers, wrapping modulo `2^256`.
#[inline(always)]
pub(crate) fn subtract_wrapping(lhs: &Limbs, rhs: &Limbs) -> Limbs {
    let [mut r0, mut r1, mut r2, mut r3] = *lhs;
    // SAFETY: straight-line arithmetic reading only the words behind the
    // passed reference (`readonly`); no stack use, and all inputs, outputs,
    // and modified flags are declared.
    unsafe {
        asm!(
            "sub {r0}, qword ptr [{b}]",
            "sbb {r1}, qword ptr [{b} + 8]",
            "sbb {r2}, qword ptr [{b} + 16]",
            "sbb {r3}, qword ptr [{b} + 24]",
            r0 = inout(reg) r0,
            r1 = inout(reg) r1,
            r2 = inout(reg) r2,
            r3 = inout(reg) r3,
            b = in(reg) rhs.as_ptr(),
            options(pure, readonly, nostack),
        );
    }
    [r0, r1, r2, r3]
}

/// Squares a loose residue, returning its exact unreduced REDC.
///
/// The 512-bit square is reduced by cancelling its low half and adding the
/// untouched high half once; the sum stays below `2p` (see the module docs),
/// so no carry escapes and no conditional subtraction is needed. The input
/// pointer's register is reclaimed as the reduction's carry limb once the
/// square has consumed the last load.
#[inline(always)]
pub(crate) fn square<M: PrimeModulus>(value: &Limbs) -> Limbs {
    assert_loose::<M>(value);
    let (o0, o1, o2, o3): (u64, u64, u64, u64);
    // SAFETY: straight-line arithmetic reading only the words behind the two
    // passed references (`readonly`); no stack use, and outputs depend only
    // on the declared inputs. All memory addresses are input-independent.
    unsafe {
        asm!(
            square_wide!("[{cy}]", "[{cy} + 8]", "[{cy} + 16]", "[{cy} + 24]"),
            cancel_low_half!(),
            "add {cy}, {z4}",
            "adc {z0}, {z5}",
            "adc {z1}, {z6}",
            "adc {z2}, {z7}",
            cy = inout(reg) value.as_ptr() => o0,
            p = in(reg) params::<M>().as_ptr(),
            z0 = out(reg) o1,
            z1 = out(reg) o2,
            z2 = out(reg) o3,
            z3 = out(reg) _,
            z4 = out(reg) _,
            z5 = out(reg) _,
            z6 = out(reg) _,
            z7 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            out("rdx") _,
            options(pure, readonly, nostack),
        );
    }
    [o0, o1, o2, o3]
}

/// REDC for `limbs < pR + p²`, producing the exact integer below `3p`.
///
/// The low half is reduced independently, then the untouched high half is
/// added. The input bound gives a final sum below `2p + p²/R < 3p < R`.
#[inline(always)]
pub(crate) fn reduce_wide<M: PrimeModulus>(limbs: [u64; 8]) -> Limbs {
    let (o0, o1, o2, o3): (u64, u64, u64, u64);
    // SAFETY: straight-line arithmetic reading only the eight input limbs and
    // the parameter block behind the two declared pointers (`readonly`); no
    // stack use of its own, and outputs depend only on the declared inputs.
    // No addresses or branches depend on the limb values.
    unsafe {
        asm!(
            "mov {z0}, qword ptr [{w}]",
            "mov {z1}, qword ptr [{w} + 8]",
            "mov {z2}, qword ptr [{w} + 16]",
            "mov {z3}, qword ptr [{w} + 24]",
            cancel_low_half!(),
            // Add the upper half; the sum stays below 3p < R, so no carry
            // escapes.
            "add {cy}, qword ptr [{w} + 32]",
            "adc {z0}, qword ptr [{w} + 40]",
            "adc {z1}, qword ptr [{w} + 48]",
            "adc {z2}, qword ptr [{w} + 56]",
            w = in(reg) limbs.as_ptr(),
            p = in(reg) params::<M>().as_ptr(),
            cy = out(reg) o0,
            z0 = out(reg) o1,
            z1 = out(reg) o2,
            z2 = out(reg) o3,
            z3 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            out("rdx") _,
            options(pure, readonly, nostack),
        );
    }
    [o0, o1, o2, o3]
}

/// Converts a loose Montgomery residue to its canonical integer.
///
/// Reducing the residue with an implicit zero upper half yields
/// `value * R^-1 mod p` at most `p`, so one conditional subtraction
/// canonicalizes it. The input pointer's register is reclaimed as a
/// temporary once the limbs are loaded.
#[inline(always)]
pub(crate) fn from_mont<M: PrimeModulus>(value: &Limbs) -> Limbs {
    assert_loose::<M>(value);
    let (o0, o1, o2, o3): (u64, u64, u64, u64);
    // SAFETY: straight-line arithmetic reading only the words behind the two
    // passed references (`readonly`); no stack use, and outputs depend only
    // on the declared inputs. All memory addresses are input-independent.
    unsafe {
        asm!(
            "mov {z0}, qword ptr [{v}]",
            "mov {z1}, qword ptr [{v} + 8]",
            "mov {z2}, qword ptr [{v} + 16]",
            "mov {z3}, qword ptr [{v} + 24]",
            cancel_low_half!(),
            // Conditional subtraction of p = [p0, p1, 0, p3].
            "mov {t1}, {cy}",
            "mov {t2}, {z0}",
            "mov {z3}, {z1}",
            "mov {v}, {z2}",
            "sub {t1}, qword ptr [{p}]",
            "sbb {t2}, qword ptr [{p} + 8]",
            "sbb {z3}, 0",
            "sbb {v}, qword ptr [{p} + 24]",
            // No borrow (CF clear) means the candidate is at least p, so the
            // subtracted value is the canonical output.
            "cmovnc {cy}, {t1}",
            "cmovnc {z0}, {t2}",
            "cmovnc {z1}, {z3}",
            "cmovnc {z2}, {v}",
            v = inout(reg) value.as_ptr() => _,
            p = in(reg) params::<M>().as_ptr(),
            cy = out(reg) o0,
            z0 = out(reg) o1,
            z1 = out(reg) o2,
            z2 = out(reg) o3,
            z3 = out(reg) _,
            t1 = out(reg) _,
            t2 = out(reg) _,
            out("rdx") _,
            options(pure, readonly, nostack),
        );
    }
    [o0, o1, o2, o3]
}

/// Squares a loose residue a positive number of times, without canonicalizing.
///
/// A fused assembly loop was measured slower than this loop around the
/// inlined [`square`]: with every register committed to the square, the loop
/// had to round-trip the running value through memory each iteration, and
/// the store-forwarding latency landed on the critical path (square roots
/// measured 8.3 µs against 7.7 µs here and 8.0 µs portable on Skylake-X).
#[inline(never)]
pub(crate) fn sqr_n<M: PrimeModulus>(value: &Limbs, count: usize) -> Limbs {
    // Shared with the AArch64 chains; `square_run` handles empty chains.
    assert!(count >= 1);
    let mut acc = *value;
    for _ in 0..count {
        acc = square::<M>(&acc);
    }
    acc
}

/// Squares a loose residue a positive number of times, then multiplies by `rhs`.
#[inline(never)]
pub(crate) fn sqr_n_mul<M: PrimeModulus>(value: &Limbs, count: usize, rhs: &Limbs) -> Limbs {
    montgomery_multiply_loose::<M>(&sqr_n::<M>(value, count), rhs)
}
