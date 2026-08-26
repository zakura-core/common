//! Private x86-64 backend for the Pasta fields.
//!
//! Montgomery multiplication is implemented as one inline `asm!` block using
//! MULX (BMI2) with dual ADCX/ADOX carry chains (ADX). Squaring routes
//! through the multiplication: one carefully-verified block is a smaller
//! correctness surface than two, and the routed square still beats the
//! portable dedicated squaring (21.0 vs 21.9 ns measured on Skylake-X). A
//! dedicated assembly squaring is measured *headroom*, not a wash — the
//! AArch64 backend's inline square runs 5–6% ahead of its multiplication
//! (an earlier contrary reading came from a benchmark cell in which the
//! inherent portable `square` shadowed `Field::square`; the fp/fq benches
//! now call the trait path explicitly) — and is the natural follow-up
//! alongside tighter scheduling of this block.
//!
//! The round structure is a transcription of the AArch64 backend
//! (`aarch64_asm.rs`), which is itself the upstream Semolina
//! `mul_mont_pasta`: a five-limb CIOS accumulator, one Montgomery
//! cancellation per round, and the shared Pasta modulus shape —
//! `modulus[2] = 0` and `modulus[3] = 2^62` — materialized as shifts, so
//! only `modulus[0]`, `modulus[1]`, and `inv` distinguish Fp from Fq.
//! Because the mathematical structure is identical, the AArch64 module's
//! bounds analysis carries over verbatim; see its module docs for the
//! five-limb no-wrap argument.
//!
//! Unlike the AArch64 block, operand limbs are addressed through pointers
//! (`readonly` memory operands) rather than individual registers: the
//! interleaved rounds plus staging temporaries do not fit x86-64's fourteen
//! allocatable registers with twelve limbs pinned. The loads are L1 hits off
//! the multiplier's critical path.
//!
//! Canonicity contract (same as the AArch64 backend): `rhs` must be
//! canonical (below the modulus) — the five-limb accumulator drops the
//! candidate's would-be fifth limb, and for `rhs >= R - p` the result would
//! be an incorrect residue that still looks canonical. `lhs` may be an
//! unreduced 256-bit value only if every `rhs` limb is at most `2^64 - 4`
//! (the accumulator no-wrap bound). Both requirements are debug-asserted at
//! the boundary a canonical caller crosses; outputs are canonical.
//!
//! The block is straight-line: no branches, no data-dependent memory
//! addresses, and a CMOV-based final conditional subtraction, so the code is
//! constant-time.
//!
//! ISA requirement: MULX needs BMI2 and ADCX/ADOX need ADX (Intel Broadwell
//! / AMD Zen or newer). The feature is opt-in precisely because this is not
//! checked at runtime; enabling it on an older CPU faults with an illegal
//! instruction.

use core::arch::asm;

type Limbs = [u64; 4];

/// Whether `value < modulus` as little-endian 256-bit integers.
#[inline(always)]
fn is_canonical(value: &Limbs, modulus: &Limbs) -> bool {
    for i in (0..4).rev() {
        if value[i] != modulus[i] {
            return value[i] < modulus[i];
        }
    }
    false
}

/// Multiplies two Montgomery residues for a Pasta modulus. `rhs` must be
/// canonical (debug-asserted; a violation yields an incorrect residue, see
/// the module docs). `lhs` may be unreduced only if every `rhs` limb is at
/// most `2^64 - 4`; see the AArch64 module docs for the carry-chain bound
/// behind this.
#[inline(always)]
pub(super) fn mul(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    debug_assert!(
        is_canonical(rhs, modulus),
        "x86_64_asm::mul requires a canonical rhs"
    );
    let (o0, o1, o2, o3): (u64, u64, u64, u64);
    // SAFETY: straight-line arithmetic reading only the twelve limbs behind
    // the three passed references (`readonly`); no stack use, and outputs
    // depend only on the declared inputs.
    //
    // Register roles: the five-limb accumulator lives in {ae}/{be}/{ce}/
    // {de}/{ee} and its window rotates down one register per round (the
    // register cancelled by the round's Montgomery step becomes the next
    // round's fifth limb), so after four rounds the candidate sits in
    // {ee},{ae},{be},{ce}. {s1}/{s2}/{s3} stage multiplier halves and
    // shifted `q * modulus[3]` terms so no flag-writing instruction lands
    // inside a carry chain. RDX is the implicit MULX source: each round's
    // `rhs` limb, then the round's Montgomery factor `q`.
    unsafe {
        asm!(
            // Round 0: initialize the accumulator with lhs * rhs[0].
            "mov rdx, qword ptr [{b}]",          // rdx = b[0].
            "mulx {be}, {ae}, qword ptr [{a}]",  // ae = low(a[0]*b[0]), be = high.
            "mulx {ce}, {s1}, qword ptr [{a} + 8]",
            "add {be}, {s1}",                    // Fold low(a[1]*b[0]) into limb 1.
            "mulx {de}, {s1}, qword ptr [{a} + 16]",
            "adc {ce}, {s1}",                    // Fold low(a[2]*b[0]) and carry.
            "mulx {ee}, {s1}, qword ptr [{a} + 24]",
            "adc {de}, {s1}",                    // Fold low(a[3]*b[0]) and carry.
            "adc {ee}, 0",                       // Fifth limb of lhs * b[0].

            // Montgomery step 0: q = limb0 * inv; add q*p; shift one limb.
            "mov rdx, {ae}",
            "imul rdx, {inv}",                   // rdx = q (low 64 bits only).
            "mulx {s2}, {s1}, qword ptr [{p} + 8]", // s1 = low(q*p[1]), s2 = high (kept).
            "mov {s3}, rdx",
            "shl {s3}, 62",                      // s3 = low(q*p[3]); p[2] contributes nothing.
            // low(q*p[0]) cancels limb 0; its carry is one exactly when the
            // limb is nonzero, which NEG leaves in CF.
            "neg {ae}",                          // CF = (limb0 != 0); ae is dead.
            "adc {be}, {s1}",                    // Add low(q*p[1]) and the cancellation carry.
            "adc {ce}, 0",                       // Propagate across zero p[2].
            "adc {de}, {s3}",                    // Add low(q*p[3]) and carry.
            "adc {ee}, 0",                       // Propagate into the fifth limb.
            "mulx {s1}, {s3}, qword ptr [{p}]",  // s1 = high(q*p[0]); the low half is spent.
            "mov {s3}, rdx",
            "shr {s3}, 2",                       // s3 = high(q*p[3]).
            "mov {ae}, 0",                       // Next round's fifth limb (MOV keeps flags).
            "add {be}, {s1}",                    // New limb 0 includes high(q*p[0]).
            "adc {ce}, {s2}",                    // New limb 1 includes high(q*p[1]).
            "adc {de}, 0",                       // New limb 2; p[2] contributes zero.
            "adc {ee}, {s3}",                    // New limb 3 includes high(q*p[3]).
            "adc {ae}, 0",                       // Capture the reduction carry as limb 4.

            // Round 1: accumulator window is [be,ce,de,ee,ae]; add lhs*b[1]
            // on dual carry chains (CF: low halves, OF: high halves).
            "mov rdx, qword ptr [{b} + 8]",      // rdx = b[1].
            "xor {s1}, {s1}",                    // Clear CF and OF.
            "mulx {s2}, {s1}, qword ptr [{a}]",
            "adcx {be}, {s1}",
            "adox {ce}, {s2}",
            "mulx {s2}, {s1}, qword ptr [{a} + 8]",
            "adcx {ce}, {s1}",
            "adox {de}, {s2}",
            "mulx {s2}, {s1}, qword ptr [{a} + 16]",
            "adcx {de}, {s1}",
            "adox {ee}, {s2}",
            "mulx {s2}, {s1}, qword ptr [{a} + 24]",
            "adcx {ee}, {s1}",
            "adox {ae}, {s2}",
            "mov {s1}, 0",
            "adcx {ae}, {s1}",                   // Close the CF chain into limb 4.
            "adox {ae}, {s1}",                   // Close the OF chain into limb 4.

            // Montgomery step 1.
            "mov rdx, {be}",
            "imul rdx, {inv}",
            "mulx {s2}, {s1}, qword ptr [{p} + 8]",
            "mov {s3}, rdx",
            "shl {s3}, 62",
            "neg {be}",
            "adc {ce}, {s1}",
            "adc {de}, 0",
            "adc {ee}, {s3}",
            "adc {ae}, 0",
            "mulx {s1}, {s3}, qword ptr [{p}]",
            "mov {s3}, rdx",
            "shr {s3}, 2",
            "mov {be}, 0",
            "add {ce}, {s1}",
            "adc {de}, {s2}",
            "adc {ee}, 0",
            "adc {ae}, {s3}",
            "adc {be}, 0",

            // Round 2: window [ce,de,ee,ae,be]; add lhs*b[2].
            "mov rdx, qword ptr [{b} + 16]",
            "xor {s1}, {s1}",
            "mulx {s2}, {s1}, qword ptr [{a}]",
            "adcx {ce}, {s1}",
            "adox {de}, {s2}",
            "mulx {s2}, {s1}, qword ptr [{a} + 8]",
            "adcx {de}, {s1}",
            "adox {ee}, {s2}",
            "mulx {s2}, {s1}, qword ptr [{a} + 16]",
            "adcx {ee}, {s1}",
            "adox {ae}, {s2}",
            "mulx {s2}, {s1}, qword ptr [{a} + 24]",
            "adcx {ae}, {s1}",
            "adox {be}, {s2}",
            "mov {s1}, 0",
            "adcx {be}, {s1}",
            "adox {be}, {s1}",

            // Montgomery step 2.
            "mov rdx, {ce}",
            "imul rdx, {inv}",
            "mulx {s2}, {s1}, qword ptr [{p} + 8]",
            "mov {s3}, rdx",
            "shl {s3}, 62",
            "neg {ce}",
            "adc {de}, {s1}",
            "adc {ee}, 0",
            "adc {ae}, {s3}",
            "adc {be}, 0",
            "mulx {s1}, {s3}, qword ptr [{p}]",
            "mov {s3}, rdx",
            "shr {s3}, 2",
            "mov {ce}, 0",
            "add {de}, {s1}",
            "adc {ee}, {s2}",
            "adc {ae}, 0",
            "adc {be}, {s3}",
            "adc {ce}, 0",

            // Round 3: window [de,ee,ae,be,ce]; add lhs*b[3].
            "mov rdx, qword ptr [{b} + 24]",
            "xor {s1}, {s1}",
            "mulx {s2}, {s1}, qword ptr [{a}]",
            "adcx {de}, {s1}",
            "adox {ee}, {s2}",
            "mulx {s2}, {s1}, qword ptr [{a} + 8]",
            "adcx {ee}, {s1}",
            "adox {ae}, {s2}",
            "mulx {s2}, {s1}, qword ptr [{a} + 16]",
            "adcx {ae}, {s1}",
            "adox {be}, {s2}",
            "mulx {s2}, {s1}, qword ptr [{a} + 24]",
            "adcx {be}, {s1}",
            "adox {ce}, {s2}",
            "mov {s1}, 0",
            "adcx {ce}, {s1}",
            "adox {ce}, {s1}",

            // Montgomery step 3. Canonical rhs bounds the candidate below
            // 2p < R, so the final shift produces no fifth limb (see the
            // AArch64 module docs); the shift's carry adc is omitted.
            "mov rdx, {de}",
            "imul rdx, {inv}",
            "mulx {s2}, {s1}, qword ptr [{p} + 8]",
            "mov {s3}, rdx",
            "shl {s3}, 62",
            "neg {de}",
            "adc {ee}, {s1}",
            "adc {ae}, 0",
            "adc {be}, {s3}",
            "adc {ce}, 0",
            "mulx {s1}, {s3}, qword ptr [{p}]",
            "mov {s3}, rdx",
            "shr {s3}, 2",
            "add {ee}, {s1}",                    // Final candidate limb 0.
            "adc {ae}, {s2}",                    // Final candidate limb 1.
            "adc {be}, 0",                       // Final candidate limb 2.
            "adc {ce}, {s3}",                    // Final candidate limb 3.

            // Conditional subtraction of p = [p0, p1, 0, 2^62].
            "movabs rdx, 0x4000000000000000",    // Materialize p[3] = 2^62.
            "mov {s1}, {ee}",
            "mov {s2}, {ae}",
            "mov {s3}, {be}",
            "mov {de}, {ce}",
            "sub {s1}, qword ptr [{p}]",         // Tentative limb 0 = candidate - p[0].
            "sbb {s2}, qword ptr [{p} + 8]",     // Tentative limb 1 minus p[1].
            "sbb {s3}, 0",                       // Tentative limb 2; p[2] is zero.
            "sbb {de}, rdx",                     // Tentative limb 3 minus p[3].
            // No borrow (CF clear) means the candidate is at least p, so the
            // subtracted value is the canonical output.
            "cmovnc {ee}, {s1}",
            "cmovnc {ae}, {s2}",
            "cmovnc {be}, {s3}",
            "cmovnc {ce}, {de}",
            a = in(reg) lhs.as_ptr(),
            b = in(reg) rhs.as_ptr(),
            p = in(reg) modulus.as_ptr(),
            inv = in(reg) inv,
            ae = out(reg) o1,
            be = out(reg) o2,
            ce = out(reg) o3,
            de = out(reg) _,
            ee = out(reg) o0,
            s1 = out(reg) _,
            s2 = out(reg) _,
            s3 = out(reg) _,
            out("rdx") _,
            options(pure, readonly, nostack),
        );
    }
    [o0, o1, o2, o3]
}

/// Squares a canonical Montgomery residue for a Pasta modulus (the input's
/// canonicity is debug-asserted). Routed through [`mul`]; see the module
/// docs for why no dedicated squaring block exists.
#[inline(always)]
pub(super) fn square(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    debug_assert!(
        is_canonical(value, modulus),
        "x86_64_asm::square requires a canonical input"
    );
    mul(value, value, modulus, inv)
}
