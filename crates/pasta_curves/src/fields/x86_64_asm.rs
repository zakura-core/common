//! Private x86_64 backend for the Pasta fields.
//!
//! Montgomery multiplication is implemented as an inline `asm!` block using
//! BMI2 `mulx` with the ADX dual carry chains (`adcx`/`adox`), following the
//! CIOS "no-carry" variant (goff, Algorithm 2): after each round the
//! accumulator's carry limb and the reduction carry are folded into a single
//! word without overflow. That optimization is valid because the shared
//! Pasta modulus shape has `modulus[3] = 2^62 < (2^63 - 1)` (and
//! `modulus[2] = 0`, which the block exploits by propagating the round's
//! carries through zero instead of multiplying).
//!
//! Only `modulus[0]`, `modulus[1]`, `modulus[3]`, and `inv` vary between Fp
//! and Fq, so a single implementation serves both fields.
//!
//! Canonicity contract: both operands must be canonical (below the modulus);
//! this is debug-asserted. The output is canonical: the candidate after the
//! final round is below `2p`, and the closing conditional subtraction
//! reduces it.
//!
//! The block contains no branches; the only memory accesses are the operand
//! and output slots, so the code is constant-time.
//!
//! This backend requires the `bmi2` and `adx` target features at run time.
//! It is gated behind the opt-in `x86_64-asm` Cargo feature (mirroring
//! `aarch64-asm`), and callers must only enable that feature for CPUs with
//! ADX support (all Intel Broadwell+ / AMD Zen+ cores).

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

/// Multiplies two canonical Montgomery residues for a Pasta modulus
/// (canonicity of both operands is debug-asserted). The output is canonical.
#[inline(always)]
pub(super) fn mul(lhs: &Limbs, rhs: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    debug_assert!(
        is_canonical(lhs, modulus),
        "x86_64_asm::mul requires a canonical lhs"
    );
    debug_assert!(
        is_canonical(rhs, modulus),
        "x86_64_asm::mul requires a canonical rhs"
    );
    let mut out = [0u64; 4];
    // SAFETY: straight-line arithmetic reading only the four operand limbs
    // behind `a`, `b`, and `m` and writing the four output limbs behind `o`;
    // no stack use, and the clobbered registers are declared. The `mulx`,
    // `adcx`, and `adox` instructions require the BMI2 and ADX target
    // features, which the `x86_64-asm` feature's contract guarantees.
    unsafe {
        asm!(
            // Accumulator t0..t4 = (r8, r9, r10, r11, r12).
            // Round 0: t = lhs * rhs[0] (fresh accumulator, single chain).
            "mov rdx, qword ptr [{b} + 0]",     // rdx = rhs[0].
            "xor r12d, r12d",                   // Clear CF/OF; t4 = 0.
            "mulx r9, r8, qword ptr [{a} + 0]", // t0/t1 = lhs[0] * rhs[0].
            "mulx r10, rcx, qword ptr [{a} + 8]", // t2 = high(lhs[1] * rhs[0]).
            "adcx r9, rcx",                     // Fold low(lhs[1] * rhs[0]) into t1.
            "mulx r11, rcx, qword ptr [{a} + 16]", // t3 = high(lhs[2] * rhs[0]).
            "adcx r10, rcx",                    // Fold low(lhs[2] * rhs[0]) into t2.
            "mulx r12, rcx, qword ptr [{a} + 24]", // t4 = high(lhs[3] * rhs[0]).
            "adcx r11, rcx",                    // Fold low(lhs[3] * rhs[0]) into t3.
            "adc r12, 0",                       // Propagate the final carry into t4.
            // Reduction 0: t = (t + m * modulus) / 2^64 with m = t0 * inv.
            "mov rdx, r8",
            "imul rdx, {inv}",                  // rdx = m.
            "xor ecx, ecx",                     // Clear CF/OF for the dual chains.
            "mulx r13, rcx, qword ptr [{m} + 0]",
            "adcx r8, rcx",                     // t0 + low(m * p[0]) = 0; CF carries.
            "adox r9, r13",                     // Fold high(m * p[0]) into t1.
            "mulx r13, rcx, qword ptr [{m} + 8]",
            "adcx r9, rcx",                     // Fold low(m * p[1]) into t1.
            "adox r10, r13",                    // Fold high(m * p[1]) into t2.
            "mov ecx, 0",
            "adcx r10, rcx",                    // p[2] = 0: propagate CF only.
            "adox r11, rcx",                    // p[2] = 0: propagate OF only.
            "mulx r13, rcx, qword ptr [{m} + 24]",
            "adcx r11, rcx",                    // Fold low(m * p[3]) into t3.
            "adox r12, r13",                    // Fold high(m * p[3]) into t4.
            "mov ecx, 0",
            "adcx r12, rcx",                    // Fold the CF chain's carry into t4.
            "adox r12, rcx",                    // Fold the OF chain's carry into t4.
            "mov r8, r9",                       // Shift out the cancelled limb.
            "mov r9, r10",
            "mov r10, r11",
            "mov r11, r12",

            // Round 1: t += lhs * rhs[1] (dual carry chains).
            "mov rdx, qword ptr [{b} + 8]",
            "xor r12d, r12d",                   // Clear CF/OF; t4 = 0.
            "mulx r13, rcx, qword ptr [{a} + 0]",
            "adox r8, rcx",                     // Low products ride the OF chain.
            "adcx r9, r13",                     // High products ride the CF chain.
            "mulx r13, rcx, qword ptr [{a} + 8]",
            "adox r9, rcx",
            "adcx r10, r13",
            "mulx r13, rcx, qword ptr [{a} + 16]",
            "adox r10, rcx",
            "adcx r11, r13",
            "mulx r13, rcx, qword ptr [{a} + 24]",
            "adox r11, rcx",
            "mov edx, 0",
            "adcx r12, r13",                    // t4 = high(lhs[3] * rhs[1]) + CF.
            "adox r12, rdx",                    // Fold the OF chain's carry into t4.
            // Reduction 1.
            "mov rdx, r8",
            "imul rdx, {inv}",
            "xor ecx, ecx",
            "mulx r13, rcx, qword ptr [{m} + 0]",
            "adcx r8, rcx",
            "adox r9, r13",
            "mulx r13, rcx, qword ptr [{m} + 8]",
            "adcx r9, rcx",
            "adox r10, r13",
            "mov ecx, 0",
            "adcx r10, rcx",
            "adox r11, rcx",
            "mulx r13, rcx, qword ptr [{m} + 24]",
            "adcx r11, rcx",
            "adox r12, r13",
            "mov ecx, 0",
            "adcx r12, rcx",
            "adox r12, rcx",
            "mov r8, r9",
            "mov r9, r10",
            "mov r10, r11",
            "mov r11, r12",

            // Round 2: t += lhs * rhs[2].
            "mov rdx, qword ptr [{b} + 16]",
            "xor r12d, r12d",
            "mulx r13, rcx, qword ptr [{a} + 0]",
            "adox r8, rcx",
            "adcx r9, r13",
            "mulx r13, rcx, qword ptr [{a} + 8]",
            "adox r9, rcx",
            "adcx r10, r13",
            "mulx r13, rcx, qword ptr [{a} + 16]",
            "adox r10, rcx",
            "adcx r11, r13",
            "mulx r13, rcx, qword ptr [{a} + 24]",
            "adox r11, rcx",
            "mov edx, 0",
            "adcx r12, r13",
            "adox r12, rdx",
            // Reduction 2.
            "mov rdx, r8",
            "imul rdx, {inv}",
            "xor ecx, ecx",
            "mulx r13, rcx, qword ptr [{m} + 0]",
            "adcx r8, rcx",
            "adox r9, r13",
            "mulx r13, rcx, qword ptr [{m} + 8]",
            "adcx r9, rcx",
            "adox r10, r13",
            "mov ecx, 0",
            "adcx r10, rcx",
            "adox r11, rcx",
            "mulx r13, rcx, qword ptr [{m} + 24]",
            "adcx r11, rcx",
            "adox r12, r13",
            "mov ecx, 0",
            "adcx r12, rcx",
            "adox r12, rcx",
            "mov r8, r9",
            "mov r9, r10",
            "mov r10, r11",
            "mov r11, r12",

            // Round 3: t += lhs * rhs[3].
            "mov rdx, qword ptr [{b} + 24]",
            "xor r12d, r12d",
            "mulx r13, rcx, qword ptr [{a} + 0]",
            "adox r8, rcx",
            "adcx r9, r13",
            "mulx r13, rcx, qword ptr [{a} + 8]",
            "adox r9, rcx",
            "adcx r10, r13",
            "mulx r13, rcx, qword ptr [{a} + 16]",
            "adox r10, rcx",
            "adcx r11, r13",
            "mulx r13, rcx, qword ptr [{a} + 24]",
            "adox r11, rcx",
            "mov edx, 0",
            "adcx r12, r13",
            "adox r12, rdx",
            // Reduction 3. The candidate lands in (r9, r10, r11, r12).
            "mov rdx, r8",
            "imul rdx, {inv}",
            "xor ecx, ecx",
            "mulx r13, rcx, qword ptr [{m} + 0]",
            "adcx r8, rcx",
            "adox r9, r13",
            "mulx r13, rcx, qword ptr [{m} + 8]",
            "adcx r9, rcx",
            "adox r10, r13",
            "mov ecx, 0",
            "adcx r10, rcx",
            "adox r11, rcx",
            "mulx r13, rcx, qword ptr [{m} + 24]",
            "adcx r11, rcx",
            "adox r12, r13",
            "mov ecx, 0",
            "adcx r12, rcx",
            "adox r12, rcx",

            // Conditional subtraction: the candidate is below 2p.
            "mov rcx, r9",
            "sub rcx, qword ptr [{m} + 0]",
            "mov rdx, r10",
            "sbb rdx, qword ptr [{m} + 8]",
            "mov r13, r11",
            "sbb r13, 0",                       // p[2] = 0.
            "mov r8, r12",
            "sbb r8, qword ptr [{m} + 24]",
            "cmovnc r9, rcx",                   // No borrow: keep the reduced value.
            "cmovnc r10, rdx",
            "cmovnc r11, r13",
            "cmovnc r12, r8",

            "mov qword ptr [{o} + 0], r9",
            "mov qword ptr [{o} + 8], r10",
            "mov qword ptr [{o} + 16], r11",
            "mov qword ptr [{o} + 24], r12",

            a = in(reg) lhs.as_ptr(),
            b = in(reg) rhs.as_ptr(),
            m = in(reg) modulus.as_ptr(),
            o = in(reg) out.as_mut_ptr(),
            inv = in(reg) inv,
            out("rcx") _,
            out("rdx") _,
            out("r8") _,
            out("r9") _,
            out("r10") _,
            out("r11") _,
            out("r12") _,
            out("r13") _,
            options(nostack),
        );
    }
    out
}

/// Squares a canonical Montgomery residue for a Pasta modulus (the input's
/// canonicity is debug-asserted). The output is canonical.
#[inline(always)]
pub(super) fn square(value: &Limbs, modulus: &Limbs, inv: u64) -> Limbs {
    mul(value, value, modulus, inv)
}

/// Squares `value` `count` times (`count` must be at least 1).
#[inline]
pub(super) fn sqr_n(value: &Limbs, count: usize, modulus: &Limbs, inv: u64) -> Limbs {
    debug_assert!(count >= 1);
    let mut acc = square(value, modulus, inv);
    for _ in 1..count {
        acc = square(&acc, modulus, inv);
    }
    acc
}

/// Squares `value` `count` times (`count` must be at least 1), then
/// multiplies the result by `rhs`.
#[inline]
pub(super) fn sqr_n_mul(
    value: &Limbs,
    count: usize,
    rhs: &Limbs,
    modulus: &Limbs,
    inv: u64,
) -> Limbs {
    mul(&sqr_n(value, count, modulus, inv), rhs, modulus, inv)
}
