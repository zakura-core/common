//! Shared field constants for the circuit recipes and prover kernels.

use udon::field::Fp;
use udon::fp_hex;

use crate::expressions::CONSTANT_COUNT;

/// The shared field constants indexable by constant and scaling nodes,
/// fully evaluated at compile time.
///
/// Entries 18–26 and 27–35 match the row-major `MDS` and `MDS_INV`
/// for Pallas `P128Pow5T3` in `crates/halo2_poseidon/src/fp.rs`. That
/// source records the Grain parameter-generation command.
pub const CONSTANTS: [Fp; CONSTANT_COUNT] = [
    // 0: 2: selector root, binary radix, and doubling coefficient.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000002"),
    // 1: 3: selector root and curve-doubling coefficient.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000003"),
    // 2: 4: selector root and scaling coefficient.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000004"),
    // 3: 5: selector root and Pallas curve coefficient b in y^2 = x^3 + b.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000005"),
    // 4: 6: selector root.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000006"),
    // 5: 1: multiplicative identity and selector root.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000001"),
    // 6: 2^10: ten-bit word radix and recomposition coefficient.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000400"),
    // 7: 1/2 in Fp: converts doubled slope products to y-coordinates.
    fp_hex!("0x2000000000000000000000000000000011234c7e04a67c8dcc96987680000001"),
    // 8: 2^124: variable-base scalar decomposition boundary.
    fp_hex!("0x0000000000000000000000000000000010000000000000000000000000000000"),
    // 9: 2^6: scalar and range-check recomposition coefficient.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000040"),
    // 10: t_Q = q - 2^254: Pallas scalar-modulus offset.
    fp_hex!("0x00000000000000000000000000000000224698fc0994a8dd8c46eb2100000001"),
    // 11: 2^3: three-bit fixed-base digit radix.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000008"),
    // 12: 7: selector and three-bit digit root.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000007"),
    // 13: 0: leading zero in fixed-base interpolation.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000000"),
    // 14: 2^120: fixed-base scalar decomposition coefficient.
    fp_hex!("0x0000000000000000000000000000000001000000000000000000000000000000"),
    // 15: 2^252: high scalar-digit radix.
    fp_hex!("0x1000000000000000000000000000000000000000000000000000000000000000"),
    // 16: 2^130: canonicity-witness offset before subtracting t_P.
    fp_hex!("0x0000000000000000000000000000000400000000000000000000000000000000"),
    // 17: t_P = p - 2^254: Pallas base-modulus canonicity offset.
    fp_hex!("0x00000000000000000000000000000000224698fc094cf91b992d30ed00000001"),
    // 18: Poseidon MDS[0][0].
    fp_hex!("0x0ab5e5b874a68de7b3d59fbdc8c9ead497d7a0ab23850b56323f2486d7e11b63"),
    // 19: Poseidon MDS[0][1].
    fp_hex!("0x31916628e58a5abb293f0f0d886c7954240d4a7cbf7357368eca5596e996ab5e"),
    // 20: Poseidon MDS[0][2].
    fp_hex!("0x07c045d5f5e9e5a6d803952bbb364fdfa0a3b71a5fb1573519d1cf25d8e8345d"),
    // 21: Poseidon MDS[1][0].
    fp_hex!("0x233162630ebf9ed7f8e24f66822c2d9f3a0a464048bd770ad049cdc8d085167c"),
    // 22: Poseidon MDS[1][1].
    fp_hex!("0x25cae2599892a8b0b36664548d60957d78f8365c85bbab07402270113e047a2e"),
    // 23: Poseidon MDS[1][2].
    fp_hex!("0x22f5b5e1e6081c9774938717989a19579aad3d8262efd83ff84d806f685f747a"),
    // 24: Poseidon MDS[2][0].
    fp_hex!("0x2e29dd59c64b1037f333aa91c383346421680eabc56bc15dfee7a9944f84dbe4"),
    // 25: Poseidon MDS[2][1].
    fp_hex!("0x1d1aab4ec1cd678892d15e7dceef1665cbeaf48b3a0624c3c771effa43263664"),
    // 26: Poseidon MDS[2][2].
    fp_hex!("0x3bf763086a18936451e0cbead65516b975872c39b59a31f615639415f6e85ef1"),
    // 27: Poseidon inverse MDS[0][0].
    fp_hex!("0x2cc057f3fa14687acc59ffd00de864434543705f35e98ab5c6de463cd1404e6b"),
    // 28: Poseidon inverse MDS[0][1].
    fp_hex!("0x32e7c439f2f967e55fd72b55df208385fadbf8ae7ae24796171840417cab7576"),
    // 29: Poseidon inverse MDS[0][2].
    fp_hex!("0x2eae5df8c3115969f461778abf6c91fa1403db6f50302040942645bd7d4464e0"),
    // 30: Poseidon inverse MDS[1][0].
    fp_hex!("0x07bf368481067199db18b4aefe68d26d13f074fde9a18b29a1ca1516a4a1a6a0"),
    // 31: Poseidon inverse MDS[1][1].
    fp_hex!("0x2aec6906c63f3cf1018a918b9dac5dadbb1d65040c85c1bfe82425bc1b23a059"),
    // 32: Poseidon inverse MDS[1][2].
    fp_hex!("0x0952e0243aec2af01215944a64a246b276b2a7139db71b36e0541adf238e0781"),
    // 33: Poseidon inverse MDS[2][0].
    fp_hex!("0x2fcbba6f9159a219723a63a0c09dab26aef9112e952fdbb52a418d8d73a7c908"),
    // 34: Poseidon inverse MDS[2][1].
    fp_hex!("0x1ec7372574f3851bb4ddd4b4d6452256c5e4960d7424cd3776efab42d4fba90b"),
    // 35: Poseidon inverse MDS[2][2].
    fp_hex!("0x0d0c2efd6472f12a3c26fa4b7d25b1e487a7435d30f8be81adc8933c6f3c72ee"),
    // 36: 2^240: high message-piece recomposition coefficient.
    fp_hex!("0x0001000000000000000000000000000000000000000000000000000000000000"),
    // 37: 2^5: bit-piece recomposition coefficient.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000020"),
    // 38: 2^4: bit-piece recomposition coefficient.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000010"),
    // 39: 2^9: bit-piece recomposition coefficient.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000200"),
    // 40: 2^250: bit-piece recomposition coefficient.
    fp_hex!("0x0400000000000000000000000000000000000000000000000000000000000000"),
    // 41: 2^254: top-bit recomposition coefficient.
    fp_hex!("0x4000000000000000000000000000000000000000000000000000000000000000"),
    // 42: 2^245: bit-piece recomposition coefficient.
    fp_hex!("0x0020000000000000000000000000000000000000000000000000000000000000"),
    // 43: 2^140: canonicity-witness offset before subtracting t_P.
    fp_hex!("0x0000000000000000000000000000100000000000000000000000000000000000"),
    // 44: 2^8: bit-piece recomposition coefficient.
    fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000100"),
    // 45: 2^58: bit-piece recomposition coefficient.
    fp_hex!("0x0000000000000000000000000000000000000000000000000400000000000000"),
    // 46: 2^249: bit-piece recomposition coefficient.
    fp_hex!("0x0200000000000000000000000000000000000000000000000000000000000000"),
    // 47: Sinsemilla S[0].x: inactive lookup fallback coordinate.
    fp_hex!("0x0db5218be6881f0f1431d4ea7d4afc7b29a05bafbede62b55a91eb912044ea5f"),
    // 48: Sinsemilla S[0].y: inactive lookup fallback coordinate.
    fp_hex!("0x2f0f40c2f152a01c9caf66298493d5d0944a041c2e65ba0117c24f76bf8e6483"),
];

/// The shared expression constant at `index` (the `CONST`/`MUL_CONST`
/// operand table), for direct kernels that mirror an expression program.
/// `index` is in `0..CONSTANT_COUNT` and names a pool entry, not a field value.
///
/// # Panics
///
/// Panics if `index >= CONSTANT_COUNT`.
#[inline]
pub const fn constant(index: usize) -> Fp {
    CONSTANTS[index]
}

/// The Poseidon MDS matrix, row-major over shared constants 18 through 26.
/// The gate programs consume the same nine values through `CONST` and
/// `MUL_CONST` operands, so building the matrix from the same table keeps the
/// witness builder's copy single-sourced with the expression table.
pub const POSEIDON_MDS: [[Fp; 3]; 3] = [
    [CONSTANTS[18], CONSTANTS[19], CONSTANTS[20]],
    [CONSTANTS[21], CONSTANTS[22], CONSTANTS[23]],
    [CONSTANTS[24], CONSTANTS[25], CONSTANTS[26]],
];

/// How a scaling node multiplies by its pool constant: the small powers of
/// two, three, one, and zero the pool contains have exact chains of
/// doublings and additions that are cheaper than a Montgomery multiplication.
///
/// A doubling is four limb shifts and one conditional subtraction, so a chain
/// of up to [`MAX_DOUBLINGS`] doublings is well under one multiplication;
/// wider powers of two stay general until their cost is derived.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScaleChain {
    /// The constant is zero: the product is zero.
    Zero,
    /// The constant is one: the product is the value itself.
    Identity,
    /// The constant is `2^k` for `1 ≤ k ≤ MAX_DOUBLINGS`: `k` doublings.
    Doublings(u32),
    /// The constant is three: one doubling and one addition.
    Triple,
    /// Any other constant: one general multiplication.
    General,
}

/// The widest power of two a scaling node evaluates as doublings.
pub const MAX_DOUBLINGS: u32 = 3;

const fn limbs_equal(left: [u64; 4], right: [u64; 4]) -> bool {
    left[0] == right[0] && left[1] == right[1] && left[2] == right[2] && left[3] == right[3]
}

/// Montgomery limbs of the reference values the chains stand for, each
/// converted once at compile time.
const ZERO_LIMBS: [u64; 4] = <Fp>::ZERO.montgomery_limbs();
const ONE_LIMBS: [u64; 4] = <Fp>::ONE.montgomery_limbs();
const THREE_LIMBS: [u64; 4] =
    udon::fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000003")
        .montgomery_limbs();
const POWER_OF_TWO_LIMBS: [[u64; 4]; MAX_DOUBLINGS as usize] = [
    udon::fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000002")
        .montgomery_limbs(),
    udon::fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000004")
        .montgomery_limbs(),
    udon::fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000008")
        .montgomery_limbs(),
];

/// Classifies one pool constant at compile time by its exact value.
const fn classify(constant: Fp) -> ScaleChain {
    let limbs = constant.reduce().montgomery_limbs();
    if limbs_equal(limbs, ZERO_LIMBS) {
        return ScaleChain::Zero;
    }
    if limbs_equal(limbs, ONE_LIMBS) {
        return ScaleChain::Identity;
    }
    if limbs_equal(limbs, THREE_LIMBS) {
        return ScaleChain::Triple;
    }
    let mut k = 0;
    while k < POWER_OF_TWO_LIMBS.len() {
        if limbs_equal(limbs, POWER_OF_TWO_LIMBS[k]) {
            return ScaleChain::Doublings(k as u32 + 1);
        }
        k += 1;
    }
    ScaleChain::General
}

/// The scaling chain of every pool constant, derived at compile time.
pub const SCALE_CHAINS: [ScaleChain; CONSTANT_COUNT] = {
    let mut chains = [ScaleChain::General; CONSTANT_COUNT];
    let mut index = 0;
    while index < CONSTANT_COUNT {
        chains[index] = classify(CONSTANTS[index]);
        index += 1;
    }
    chains
};

const _: () = {
    assert!(MAX_DOUBLINGS == 3);
    assert!(matches!(SCALE_CHAINS[0], ScaleChain::Doublings(1)));
    assert!(matches!(SCALE_CHAINS[1], ScaleChain::Triple));
    assert!(matches!(SCALE_CHAINS[2], ScaleChain::Doublings(2)));
    assert!(matches!(SCALE_CHAINS[5], ScaleChain::Identity));
    assert!(matches!(SCALE_CHAINS[11], ScaleChain::Doublings(3)));
    assert!(matches!(SCALE_CHAINS[13], ScaleChain::Zero));
};

/// Multiplies `value` by the pool constant at `index`, as a doubling or
/// addition chain when the constant has one ([`SCALE_CHAINS`]). Exact: every
/// chain computes the same canonical field element as the multiplication.
/// With a literal `index` the dispatch folds away after inlining.
/// `index` is in `0..CONSTANT_COUNT`, the same pool index as [`constant`].
///
/// # Panics
///
/// Panics if `index >= CONSTANT_COUNT`.
#[inline(always)]
pub fn scale(value: &Fp, index: usize) -> Fp {
    match SCALE_CHAINS[index] {
        ScaleChain::Zero => <Fp>::ZERO,
        ScaleChain::Identity => *value,
        ScaleChain::Doublings(1) => value.double(),
        ScaleChain::Doublings(2) => value.mul_by_4(),
        ScaleChain::Doublings(_) => value.mul_by_8(),
        ScaleChain::Triple => value.triple(),
        ScaleChain::General => value.mul(&CONSTANTS[index]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every chain reproduces the multiplication exactly on values spanning
    /// small integers, the top of the field, and wide pseudo-random residues.
    #[test]
    fn scale_chains_match_constant_multiplication() {
        let mut samples = alloc::vec![
            <Fp>::ZERO,
            <Fp>::ONE,
            <Fp>::ONE.neg(),
            <Fp>::from_u64(2),
            <Fp>::from_u64(u64::MAX),
        ];
        let mut seed = <Fp>::from_u64(0x9e37_79b9_7f4a_7c15);
        for _ in 0..8 {
            seed = seed.square().add(&<Fp>::ONE);
            samples.push(seed);
            samples.push(seed.neg());
        }
        for (index, constant) in CONSTANTS.iter().enumerate() {
            for value in &samples {
                assert_eq!(
                    scale(value, index).reduce(),
                    value.mul(constant).reduce(),
                    "constant {index}"
                );
            }
        }
        let chained = SCALE_CHAINS
            .iter()
            .filter(|chain| **chain != ScaleChain::General)
            .count();
        assert_eq!(chained, 6);
    }
}
