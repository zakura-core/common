//! Private x86-64 backend for the Pasta fields.
//!
//! Montgomery multiplication and squaring are implemented as inline `asm!`
//! blocks using MULX (BMI2) with ADCX/ADOX dual carry chains (ADX) in the
//! multiplication rows. Two negative scheduling results are pinned here so
//! they are not retried on this microarchitecture family: routing squaring
//! through the multiplication measured 2–5% *slower* (run-dependent) than
//! the dedicated squaring below (21.0 vs 20.0–20.7 ns on Skylake-X —
//! mirroring the AArch64
//! backend, whose inline square also beats its multiplication; an earlier
//! contrary reading came from a benchmark cell in which the inherent
//! portable `square` shadowed `Field::square`), and merging each
//! Montgomery step's two carry sweeps into interleaved ADCX/ADOX chains
//! (staging all five `q*p` operands flag-free, `TEST` to clear both
//! chains) measured ~10% slower than the two short sequential sweeps
//! (22.3 vs 20.2 ns) despite the shorter nominal dependency length.
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
//! Canonicity contract (same as the AArch64 backend): `rhs` in `mul` and
//! the input of `square` must be canonical (below the modulus) — the
//! five-limb accumulator drops the candidate's would-be fifth limb, and
//! for `rhs >= R - p` the result would be an incorrect residue that still
//! looks canonical. Both routines debug-assert that precondition, and with
//! both operands canonical they are always safe. `lhs` in `mul` may be an
//! unreduced 256-bit value only if every `rhs` limb is at most `2^64 - 4`
//! (the accumulator no-wrap bound) — a condition that is *not* asserted:
//! no current caller passes an unreduced `lhs` (`from_u512`, the one place
//! that produces one, uses the portable path), and the
//! `x86_64_asm_mul_unreduced_lhs_near_modulus_rhs_matches_portable` tests
//! in `fp.rs`/`fq.rs` pin the allowance. Outputs are canonical.
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

/// Multiplies a lazy Montgomery residue below `2p` by a canonical one and
/// returns the Montgomery candidate without its final subtraction.
///
/// The product is below `2p^2 < R * p`; the result is below `1.5p`. The
/// tighter lazy-lhs bound also keeps every five-limb CIOS accumulator in range,
/// without the per-limb rhs restriction needed for an arbitrary 256-bit lhs.
#[inline(always)]
#[cfg(feature = "x86_64-lazy-asm")]
pub(super) fn mul_lazy(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    debug_assert!(
        is_canonical(rhs, modulus),
        "x86_64_asm::mul_lazy requires a canonical rhs"
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

            // Leave the candidate in [0, 2p); point-formula callers defer
            // canonicalization until a comparison or output coordinate.
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
/// canonicity is debug-asserted).
///
/// A transcription of the AArch64 backend's dedicated squaring: the 512-bit
/// square as cross products, one doubling pass, and the diagonals (ten MULX
/// against the multiplication's sixteen), then four Montgomery
/// cancellations on a rotating four-limb window with a carried fifth limb,
/// the high product half folded in (the sum stays below `2p`, so no carry
/// escapes — see the AArch64 module's bounds), and a CMOV conditional
/// subtraction. Measured 2–5% ahead of squaring through [`mul`] on
/// Skylake-X (20.0–20.7 vs 21.0 ns across runs), mirroring the AArch64
/// backend's own square-over-mul margin.
#[inline(always)]
pub(super) fn square(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    debug_assert!(
        is_canonical(value, modulus),
        "x86_64_asm::square requires a canonical input"
    );
    let (o0, o1, o2, o3): (u64, u64, u64, u64);
    // SAFETY: straight-line arithmetic reading only the limbs behind the two
    // passed references (`readonly`); no stack use, and outputs depend only
    // on the declared inputs. The input pointer's register is reclaimed as
    // the reduction's carry limb once phase 1 has consumed the last load.
    unsafe {
        asm!(
            // Phase 1: the 512-bit square in z0..z7.
            // Cross products a[i]*a[j] (i < j), accumulated as they stream.
            "xor {z5:e}, {z5:e}",
            "xor {z6:e}, {z6:e}",
            "xor {z7:e}, {z7:e}",
            "mov rdx, qword ptr [{a}]",
            "mulx {t1}, {z1}, qword ptr [{a} + 8]",  // a0*a1.
            "mulx {t2}, {z2}, qword ptr [{a} + 16]", // a0*a2.
            "mulx {z4}, {z3}, qword ptr [{a} + 24]", // a0*a3.
            "add {z2}, {t1}",                        // Fold high(a0*a1).
            "adc {z3}, {t2}",                        // Fold high(a0*a2) and carry.
            "adc {z4}, 0",
            "mov rdx, qword ptr [{a} + 8]",
            "mulx {t2}, {t1}, qword ptr [{a} + 16]", // a1*a2.
            "add {z3}, {t1}",
            "adc {z4}, {t2}",
            "adc {z5}, 0",
            "mulx {t2}, {t1}, qword ptr [{a} + 24]", // a1*a3.
            "add {z4}, {t1}",
            "adc {z5}, {t2}",
            "adc {z6}, 0",
            "mov rdx, qword ptr [{a} + 16]",
            "mulx {t2}, {t1}, qword ptr [{a} + 24]", // a2*a3.
            "add {z5}, {t1}",
            "adc {z6}, {t2}",
            "adc {z7}, 0",
            // Double the cross products. The doubled sum is below 2^512, so
            // no carry leaves z7.
            "add {z1}, {z1}",
            "adc {z2}, {z2}",
            "adc {z3}, {z3}",
            "adc {z4}, {z4}",
            "adc {z5}, {z5}",
            "adc {z6}, {z6}",
            "adc {z7}, {z7}",
            // Add the diagonal squares in one carry chain (MOV and MULX
            // preserve flags).
            "mov rdx, qword ptr [{a}]",
            "mulx {t2}, {z0}, rdx",                  // z0 = low(a0^2).
            "add {z1}, {t2}",                        // High(a0^2).
            "mov rdx, qword ptr [{a} + 8]",
            "mulx {t2}, {t1}, rdx",
            "adc {z2}, {t1}",
            "adc {z3}, {t2}",
            "mov rdx, qword ptr [{a} + 16]",
            "mulx {t2}, {t1}, rdx",
            "adc {z4}, {t1}",
            "adc {z5}, {t2}",
            "mov rdx, qword ptr [{a} + 24]",
            "mulx {t2}, {t1}, rdx",
            "adc {z6}, {t1}",
            "adc {z7}, {t2}",                        // a^2 < 2^510: no carry out.

            // Phase 2: four Montgomery cancellations on the low half, the
            // same two-sweep step as [`mul`]'s. The window rotates down one
            // register per step; {a} (its loads are done) serves as the
            // first carried fifth limb.
            // Step 0: window [z0, z1, z2, z3], carry into {a}.
            "mov rdx, {z0}",
            "imul rdx, {inv}",                       // rdx = q.
            "mulx {t2}, {t1}, qword ptr [{p} + 8]",  // t1/t2 = low/high(q*p1).
            "mov {a}, rdx",
            "shl {a}, 62",                           // low(q*p3); p2 is zero.
            "neg {z0}",                              // CF = (limb0 != 0).
            "adc {z1}, {t1}",
            "adc {z2}, 0",
            "adc {z3}, {a}",
            "mov {a}, 0",
            "adc {a}, 0",                            // Carry above limb 3.
            "mulx {t1}, {z0}, qword ptr [{p}]",      // t1 = high(q*p0); low is spent.
            "mov {z0}, rdx",
            "shr {z0}, 2",                           // high(q*p3).
            "add {z1}, {t1}",                        // New limb 0.
            "adc {z2}, {t2}",                        // New limb 1 += high(q*p1).
            "adc {z3}, 0",                           // New limb 2.
            "adc {a}, {z0}",                         // New limb 3 += high(q*p3).
            // Step 1: window [z1, z2, z3, a], carry into z0.
            "mov rdx, {z1}",
            "imul rdx, {inv}",
            "mulx {t2}, {t1}, qword ptr [{p} + 8]",
            "mov {z0}, rdx",
            "shl {z0}, 62",
            "neg {z1}",
            "adc {z2}, {t1}",
            "adc {z3}, 0",
            "adc {a}, {z0}",
            "mov {z0}, 0",
            "adc {z0}, 0",
            "mulx {t1}, {z1}, qword ptr [{p}]",
            "mov {z1}, rdx",
            "shr {z1}, 2",
            "add {z2}, {t1}",
            "adc {z3}, {t2}",
            "adc {a}, 0",
            "adc {z0}, {z1}",
            // Step 2: window [z2, z3, a, z0], carry into z1.
            "mov rdx, {z2}",
            "imul rdx, {inv}",
            "mulx {t2}, {t1}, qword ptr [{p} + 8]",
            "mov {z1}, rdx",
            "shl {z1}, 62",
            "neg {z2}",
            "adc {z3}, {t1}",
            "adc {a}, 0",
            "adc {z0}, {z1}",
            "mov {z1}, 0",
            "adc {z1}, 0",
            "mulx {t1}, {z2}, qword ptr [{p}]",
            "mov {z2}, rdx",
            "shr {z2}, 2",
            "add {z3}, {t1}",
            "adc {a}, {t2}",
            "adc {z0}, 0",
            "adc {z1}, {z2}",
            // Step 3: window [z3, a, z0, z1], carry into z2.
            "mov rdx, {z3}",
            "imul rdx, {inv}",
            "mulx {t2}, {t1}, qword ptr [{p} + 8]",
            "mov {z2}, rdx",
            "shl {z2}, 62",
            "neg {z3}",
            "adc {a}, {t1}",
            "adc {z0}, 0",
            "adc {z1}, {z2}",
            "mov {z2}, 0",
            "adc {z2}, 0",
            "mulx {t1}, {z3}, qword ptr [{p}]",
            "mov {z3}, rdx",
            "shr {z3}, 2",
            "add {a}, {t1}",
            "adc {z0}, {t2}",
            "adc {z1}, 0",
            "adc {z2}, {z3}",

            // Fold in the high product half; the sum stays below 2p, so no
            // carry escapes and a four-limb conditional subtraction suffices.
            "add {a}, {z4}",
            "adc {z0}, {z5}",
            "adc {z1}, {z6}",
            "adc {z2}, {z7}",
            "movabs rdx, 0x4000000000000000",        // p3 = 2^62.
            "mov {t1}, {a}",
            "mov {t2}, {z0}",
            "mov {z3}, {z1}",
            "mov {z4}, {z2}",
            "sub {t1}, qword ptr [{p}]",
            "sbb {t2}, qword ptr [{p} + 8]",
            "sbb {z3}, 0",
            "sbb {z4}, rdx",
            "cmovnc {a}, {t1}",
            "cmovnc {z0}, {t2}",
            "cmovnc {z1}, {z3}",
            "cmovnc {z2}, {z4}",
            a = inout(reg) value.as_ptr() => o0,
            p = in(reg) modulus.as_ptr(),
            inv = in(reg) inv,
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

/// Squares a formula-derived lazy Montgomery residue and returns the candidate
/// without its final subtraction. The caller maintains the documented `< 2p`
/// range invariant.
///
/// A transcription of the AArch64 backend's dedicated squaring: the 512-bit
/// square as cross products, one doubling pass, and the diagonals (ten MULX
/// against the multiplication's sixteen), then four Montgomery
/// cancellations on a rotating four-limb window with a carried fifth limb,
/// and the high product half folded in. This variant omits the canonical
/// routine's CMOV conditional subtraction.
#[inline(always)]
#[cfg(feature = "x86_64-lazy-asm")]
pub(super) fn square_lazy(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    let (o0, o1, o2, o3): (u64, u64, u64, u64);
    // SAFETY: straight-line arithmetic reading only the limbs behind the two
    // passed references (`readonly`); no stack use, and outputs depend only
    // on the declared inputs. The input pointer's register is reclaimed as
    // the reduction's carry limb once phase 1 has consumed the last load.
    unsafe {
        asm!(
            // Phase 1: the 512-bit square in z0..z7.
            // Cross products a[i]*a[j] (i < j), accumulated as they stream.
            "xor {z5:e}, {z5:e}",
            "xor {z6:e}, {z6:e}",
            "xor {z7:e}, {z7:e}",
            "mov rdx, qword ptr [{a}]",
            "mulx {t1}, {z1}, qword ptr [{a} + 8]",  // a0*a1.
            "mulx {t2}, {z2}, qword ptr [{a} + 16]", // a0*a2.
            "mulx {z4}, {z3}, qword ptr [{a} + 24]", // a0*a3.
            "add {z2}, {t1}",                        // Fold high(a0*a1).
            "adc {z3}, {t2}",                        // Fold high(a0*a2) and carry.
            "adc {z4}, 0",
            "mov rdx, qword ptr [{a} + 8]",
            "mulx {t2}, {t1}, qword ptr [{a} + 16]", // a1*a2.
            "add {z3}, {t1}",
            "adc {z4}, {t2}",
            "adc {z5}, 0",
            "mulx {t2}, {t1}, qword ptr [{a} + 24]", // a1*a3.
            "add {z4}, {t1}",
            "adc {z5}, {t2}",
            "adc {z6}, 0",
            "mov rdx, qword ptr [{a} + 16]",
            "mulx {t2}, {t1}, qword ptr [{a} + 24]", // a2*a3.
            "add {z5}, {t1}",
            "adc {z6}, {t2}",
            "adc {z7}, 0",
            // Double the cross products. The doubled sum is below 2^512, so
            // no carry leaves z7.
            "add {z1}, {z1}",
            "adc {z2}, {z2}",
            "adc {z3}, {z3}",
            "adc {z4}, {z4}",
            "adc {z5}, {z5}",
            "adc {z6}, {z6}",
            "adc {z7}, {z7}",
            // Add the diagonal squares in one carry chain (MOV and MULX
            // preserve flags).
            "mov rdx, qword ptr [{a}]",
            "mulx {t2}, {z0}, rdx",                  // z0 = low(a0^2).
            "add {z1}, {t2}",                        // High(a0^2).
            "mov rdx, qword ptr [{a} + 8]",
            "mulx {t2}, {t1}, rdx",
            "adc {z2}, {t1}",
            "adc {z3}, {t2}",
            "mov rdx, qword ptr [{a} + 16]",
            "mulx {t2}, {t1}, rdx",
            "adc {z4}, {t1}",
            "adc {z5}, {t2}",
            "mov rdx, qword ptr [{a} + 24]",
            "mulx {t2}, {t1}, rdx",
            "adc {z6}, {t1}",
            "adc {z7}, {t2}",                        // The 512-bit square has no carry out.

            // Phase 2: four Montgomery cancellations on the low half, the
            // same two-sweep step as [`mul`]'s. The window rotates down one
            // register per step; {a} (its loads are done) serves as the
            // first carried fifth limb.
            // Step 0: window [z0, z1, z2, z3], carry into {a}.
            "mov rdx, {z0}",
            "imul rdx, {inv}",                       // rdx = q.
            "mulx {t2}, {t1}, qword ptr [{p} + 8]",  // t1/t2 = low/high(q*p1).
            "mov {a}, rdx",
            "shl {a}, 62",                           // low(q*p3); p2 is zero.
            "neg {z0}",                              // CF = (limb0 != 0).
            "adc {z1}, {t1}",
            "adc {z2}, 0",
            "adc {z3}, {a}",
            "mov {a}, 0",
            "adc {a}, 0",                            // Carry above limb 3.
            "mulx {t1}, {z0}, qword ptr [{p}]",      // t1 = high(q*p0); low is spent.
            "mov {z0}, rdx",
            "shr {z0}, 2",                           // high(q*p3).
            "add {z1}, {t1}",                        // New limb 0.
            "adc {z2}, {t2}",                        // New limb 1 += high(q*p1).
            "adc {z3}, 0",                           // New limb 2.
            "adc {a}, {z0}",                         // New limb 3 += high(q*p3).
            // Step 1: window [z1, z2, z3, a], carry into z0.
            "mov rdx, {z1}",
            "imul rdx, {inv}",
            "mulx {t2}, {t1}, qword ptr [{p} + 8]",
            "mov {z0}, rdx",
            "shl {z0}, 62",
            "neg {z1}",
            "adc {z2}, {t1}",
            "adc {z3}, 0",
            "adc {a}, {z0}",
            "mov {z0}, 0",
            "adc {z0}, 0",
            "mulx {t1}, {z1}, qword ptr [{p}]",
            "mov {z1}, rdx",
            "shr {z1}, 2",
            "add {z2}, {t1}",
            "adc {z3}, {t2}",
            "adc {a}, 0",
            "adc {z0}, {z1}",
            // Step 2: window [z2, z3, a, z0], carry into z1.
            "mov rdx, {z2}",
            "imul rdx, {inv}",
            "mulx {t2}, {t1}, qword ptr [{p} + 8]",
            "mov {z1}, rdx",
            "shl {z1}, 62",
            "neg {z2}",
            "adc {z3}, {t1}",
            "adc {a}, 0",
            "adc {z0}, {z1}",
            "mov {z1}, 0",
            "adc {z1}, 0",
            "mulx {t1}, {z2}, qword ptr [{p}]",
            "mov {z2}, rdx",
            "shr {z2}, 2",
            "add {z3}, {t1}",
            "adc {a}, {t2}",
            "adc {z0}, 0",
            "adc {z1}, {z2}",
            // Step 3: window [z3, a, z0, z1], carry into z2.
            "mov rdx, {z3}",
            "imul rdx, {inv}",
            "mulx {t2}, {t1}, qword ptr [{p} + 8]",
            "mov {z2}, rdx",
            "shl {z2}, 62",
            "neg {z3}",
            "adc {a}, {t1}",
            "adc {z0}, 0",
            "adc {z1}, {z2}",
            "mov {z2}, 0",
            "adc {z2}, 0",
            "mulx {t1}, {z3}, qword ptr [{p}]",
            "mov {z3}, rdx",
            "shr {z3}, 2",
            "add {a}, {t1}",
            "adc {z0}, {t2}",
            "adc {z1}, 0",
            "adc {z2}, {z3}",

            // Fold in the high product half; the sum stays below 2p, so no
            // carry escapes and a four-limb conditional subtraction suffices.
            "add {a}, {z4}",
            "adc {z0}, {z5}",
            "adc {z1}, {z6}",
            "adc {z2}, {z7}",
            // Keep the four-limb candidate lazy; the point formula performs
            // one conditional subtraction at each canonical boundary.
            a = inout(reg) value.as_ptr() => o0,
            p = in(reg) modulus.as_ptr(),
            inv = in(reg) inv,
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
