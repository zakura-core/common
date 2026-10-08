//! Unreduced 256-by-256 multiplication accumulated into eight limbs, and
//! the fold of the accumulator's top words back into the low seven.
//!
//! These compute the same functions as the AArch64 kernels in
//! `field::aarch64_asm::products`, whose module docs give the carry
//! analysis. Write B = 2^64. Each multiplication row adds its low product
//! words on the CF chain and its high words on the OF chain, consumes the
//! previous row's pending carry at word i + 4, and leaves its own pending at
//! word i + 5. After row i, the initial low i + 5 words plus the processed
//! partial product are below 2 * B^(i + 5), so the carry out of word i + 4
//! is 0 or 1: at most one of the two chains carries, and their sum is the
//! next pending carry. The returned overflow is at most one because
//! acc + lhs * rhs < 2^513. All input limbs may be arbitrary u64 values; no
//! field bound is assumed.
//!
//! The eight accumulator limbs, the pending carry, two pointers, two
//! multiplier halves, and `rdx` exceed the thirteen registers available to
//! inline assembly, so the rows are split across two blocks that hand the
//! pending carry over in a register; the finished low limbs of the first
//! block are not operands of the second. Both blocks are inlined into the
//! product-sum loops (see the parent module docs).

use core::arch::asm;

/// One schoolbook row: `rdx` holds the multiplier limb, `$z` names a zeroed
/// register for closing the chains, and the previous pending carry in
/// `{ovf}` is consumed at the row's fifth word before `{ovf}` receives the
/// new pending carry.
macro_rules! accumulate_row {
    ($a:literal, $d0:literal, $d1:literal, $d2:literal, $d3:literal, $d4:literal) => {
        concat!(
            "mov rdx, qword ptr ",
            $a,
            "\n",
            // Clear CF and OF; the register is overwritten by the first MULX.
            "xor {lo:e}, {lo:e}\n",
            "mulx {hi}, {lo}, qword ptr [{b}]\n",
            "adcx ",
            $d0,
            ", {lo}\n",
            "adox ",
            $d1,
            ", {hi}\n",
            "mulx {hi}, {lo}, qword ptr [{b} + 8]\n",
            "adcx ",
            $d1,
            ", {lo}\n",
            "adox ",
            $d2,
            ", {hi}\n",
            "mulx {hi}, {lo}, qword ptr [{b} + 16]\n",
            "adcx ",
            $d2,
            ", {lo}\n",
            "adox ",
            $d3,
            ", {hi}\n",
            "mulx {hi}, {lo}, qword ptr [{b} + 24]\n",
            "adcx ",
            $d3,
            ", {lo}\n",
            "adox ",
            $d4,
            ", {hi}\n",
            // Close the CF chain into the fifth word together with the
            // previous pending carry, then collect both chains' carries.
            "mov {lo}, 0\n",
            "adcx ",
            $d4,
            ", {ovf}\n",
            "mov {ovf}, 0\n",
            "adcx {ovf}, {lo}\n",
            "adox {ovf}, {lo}\n",
        )
    };
}

#[inline(always)]
pub(crate) fn mul_accumulate(
    accumulator: [u64; 8],
    lhs: &[u64; 4],
    rhs: &[u64; 4],
) -> ([u64; 8], u64) {
    let [
        mut d0,
        mut d1,
        mut d2,
        mut d3,
        mut d4,
        mut d5,
        mut d6,
        mut d7,
    ] = accumulator;
    let mut overflow: u64 = 0;
    // SAFETY: straight-line arithmetic reading only the eight words behind
    // the two passed references (`readonly`); no stack use, and outputs
    // depend only on the declared inputs. There are no data-dependent
    // addresses or control flow.
    unsafe {
        // Rows 0 and 1 touch accumulator words 0 through 6.
        asm!(
            accumulate_row!("[{a}]", "{d0}", "{d1}", "{d2}", "{d3}", "{d4}"),
            accumulate_row!("[{a} + 8]", "{d1}", "{d2}", "{d3}", "{d4}", "{d5}"),
            d0 = inout(reg) d0,
            d1 = inout(reg) d1,
            d2 = inout(reg) d2,
            d3 = inout(reg) d3,
            d4 = inout(reg) d4,
            d5 = inout(reg) d5,
            ovf = inout(reg) overflow,
            a = in(reg) lhs.as_ptr(),
            b = in(reg) rhs.as_ptr(),
            lo = out(reg) _,
            hi = out(reg) _,
            out("rdx") _,
            options(pure, readonly, nostack),
        );
        // Rows 2 and 3 touch accumulator words 2 through 7.
        asm!(
            accumulate_row!("[{a} + 16]", "{d2}", "{d3}", "{d4}", "{d5}", "{d6}"),
            accumulate_row!("[{a} + 24]", "{d3}", "{d4}", "{d5}", "{d6}", "{d7}"),
            d2 = inout(reg) d2,
            d3 = inout(reg) d3,
            d4 = inout(reg) d4,
            d5 = inout(reg) d5,
            d6 = inout(reg) d6,
            d7 = inout(reg) d7,
            ovf = inout(reg) overflow,
            a = in(reg) lhs.as_ptr(),
            b = in(reg) rhs.as_ptr(),
            lo = out(reg) _,
            hi = out(reg) _,
            out("rdx") _,
            options(pure, readonly, nostack),
        );
    }
    ([d0, d1, d2, d3, d4, d5, d6, d7], overflow)
}

/// Folds the top two accumulator words into the lower seven words.
///
/// Requires `b448 < 2^253` and `r2 < 2^252`, as for both Pasta fields.
/// Thus the folding term is less than 2^318 and fits in five words;
/// adding the original low 448 bits gives a result less than 2^449.
#[inline(never)]
pub(crate) fn partial_reduce(
    wide: [u64; 8],
    carry: u64,
    b448: &[u64; 4],
    r2: &[u64; 4],
) -> [u64; 8] {
    debug_assert!(b448[3] < (1 << 61));
    debug_assert!(r2[3] < (1 << 60));
    let [mut d0, mut d1, mut d2, mut d3, mut d4, mut d5, mut d6, b7] = wide;
    let d7;
    let fold = [
        b448[0], b448[1], b448[2], b448[3], r2[0], r2[1], r2[2], r2[3],
    ];
    // SAFETY: straight-line arithmetic reading only the eight folding words
    // behind the declared pointer (`readonly`); no stack use, and outputs
    // depend only on the declared inputs. The bounds above ensure the
    // folded value cannot carry out of the eighth word.
    unsafe {
        asm!(
            // Clear CF and OF and zero the eighth word.
            "xor {d7:e}, {d7:e}",
            // Add b7 * b448 at words 0 through 4.
            "mulx {hi}, {lo}, qword ptr [{f}]",
            "adcx {d0}, {lo}",
            "adox {d1}, {hi}",
            "mulx {hi}, {lo}, qword ptr [{f} + 8]",
            "adcx {d1}, {lo}",
            "adox {d2}, {hi}",
            "mulx {hi}, {lo}, qword ptr [{f} + 16]",
            "adcx {d2}, {lo}",
            "adox {d3}, {hi}",
            "mulx {hi}, {lo}, qword ptr [{f} + 24]",
            "adcx {d3}, {lo}",
            "adox {d4}, {hi}",
            // Close both chains through the top word.
            "mov {lo}, 0",
            "adcx {d4}, {lo}",
            "adox {d5}, {lo}",
            "adcx {d5}, {lo}",
            "adox {d6}, {lo}",
            "adcx {d6}, {lo}",
            "adox {d7}, {lo}",
            "adcx {d7}, {lo}",
            // Add carry * r2 the same way; the spent carry register becomes
            // the zero register and its XOR clears both chains.
            "mov rdx, {c}",
            "xor {c:e}, {c:e}",
            "mulx {hi}, {lo}, qword ptr [{f} + 32]",
            "adcx {d0}, {lo}",
            "adox {d1}, {hi}",
            "mulx {hi}, {lo}, qword ptr [{f} + 40]",
            "adcx {d1}, {lo}",
            "adox {d2}, {hi}",
            "mulx {hi}, {lo}, qword ptr [{f} + 48]",
            "adcx {d2}, {lo}",
            "adox {d3}, {hi}",
            "mulx {hi}, {lo}, qword ptr [{f} + 56]",
            "adcx {d3}, {lo}",
            "adox {d4}, {hi}",
            "adcx {d4}, {c}",
            "adox {d5}, {c}",
            "adcx {d5}, {c}",
            "adox {d6}, {c}",
            "adcx {d6}, {c}",
            "adox {d7}, {c}",
            "adcx {d7}, {c}",
            d0 = inout(reg) d0,
            d1 = inout(reg) d1,
            d2 = inout(reg) d2,
            d3 = inout(reg) d3,
            d4 = inout(reg) d4,
            d5 = inout(reg) d5,
            d6 = inout(reg) d6,
            d7 = out(reg) d7,
            f = in(reg) fold.as_ptr(),
            c = inout(reg) carry => _,
            lo = out(reg) _,
            hi = out(reg) _,
            inout("rdx") b7 => _,
            options(pure, readonly, nostack),
        );
    }
    [d0, d1, d2, d3, d4, d5, d6, d7]
}
