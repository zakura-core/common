//! Fixed-only selector preparation for the fused gate evaluator.
//!
//! The recipe is circuit shape: which fixed queries feed each prepared
//! selector and the `q · ∏(cᵢ − q)` factor chains over them. The prover fills
//! its prepared selector matrix with [`prepare_gate_selectors`] over the
//! extended coset, embeds the equivalent generated artifact, or computes one
//! row on demand while proving. The host-side generator uses the same recipe,
//! so these preparation paths agree by construction.
//!
//! A compressed selector column holds a small integer on active circuit rows.
//! Its gate selectors are polynomials `q * product(c - q)` that omit one root
//! at a time. These are unnormalized products, not Boolean indicators; on the
//! extended coset, `q` can be any field element. The factored evaluation below
//! also works at roots without division or special cases.
//!
//! [`crate::queries`] owns the frame descriptors. This module owns the prepared
//! row's slot order, which is also the gate-selector artifact's element order.

use udon::field::Fp;

// Preserve the original frame-descriptor paths. Query structure is defined
// in queries; this module owns only the fixed-selector preparation recipe.
pub use crate::queries::{GATE_QUERY_COUNT, GATE_QUERY_DESCRIPTORS, QueryKind};

/// Number of prepared values before the final shared prefix in each row.
///
/// Prepared slots `0..38` contain selectors. Slots 38 and 39 contain the
/// `q · (1-q) · (2-q) · (3-q)` prefixes for frame slots 47 and 48. Prepared
/// slot 40 follows them with the prefix for frame slot 46. The count retains
/// this split because the fused evaluator addresses that final prefix directly.
pub const PREPARED_GATE_SELECTOR_COUNT: usize = 40;

/// Index in [`crate::queries::FIXED_QUERIES`] supplying the final prefix.
/// This is fixed column 26, read through gate-frame slot 46.
pub const PREPARED_GATE_SELECTOR_FIXED_QUERY: usize = 26;

/// Length of one prepared selector row: the [`PREPARED_GATE_SELECTOR_COUNT`]
/// prepared values followed by the fixed-only prefix
/// at index `PREPARED_GATE_SELECTOR_COUNT`,
/// so the fold reads it instead of recomputing three multiplications per row.
pub const PREPARED_GATE_SELECTOR_ROW: usize = PREPARED_GATE_SELECTOR_COUNT + 1;

/// The small shared constants the selector chains subtract, indexed exactly
/// as the prover's expression-constant table (whose indices the frozen
/// source-tree digest pins), so the recipe below reads identically in both
/// crates.
const fn constant(index: usize) -> Fp {
    match index {
        0 => const { crate::constants::CONSTANTS[0] },
        1 => const { crate::constants::CONSTANTS[1] },
        2 => const { crate::constants::CONSTANTS[2] },
        3 => const { crate::constants::CONSTANTS[3] },
        4 => const { crate::constants::CONSTANTS[4] },
        5 => const { crate::constants::CONSTANTS[5] },
        12 => const { crate::constants::CONSTANTS[12] },
        _ => panic!("selector chains use only the small shared constants"),
    }
}

/// All leave-one-out selectors over roots `1..=ROOTS`, without division.
/// Prefixes include `q`; suffixes share the remaining factors. This works
/// unchanged when `q` is any root or zero. Entry `r - 1` is
/// `q * product(c - q for c in 1..=ROOTS, c != r)`.
/// The callers below use root counts between four and six.
fn selector_family<const ROOTS: usize>(q: Fp) -> [Fp; ROOTS] {
    let roots = [
        constant(5),
        constant(0),
        constant(1),
        constant(2),
        constant(3),
        constant(4),
        constant(12),
    ];
    let factors: [Fp; ROOTS] = core::array::from_fn(|i| roots[i].sub(&q));
    let mut prefixes = [q; ROOTS];
    for i in 1..ROOTS {
        prefixes[i] = prefixes[i - 1].mul(&factors[i - 1]);
    }
    let mut result = prefixes;
    let mut suffix = factors[ROOTS - 1];
    for i in (0..ROOTS - 1).rev() {
        result[i] = prefixes[i].mul(&suffix);
        if i != 0 {
            suffix = suffix.mul(&factors[i]);
        }
    }
    result
}

/// The first three seven-root selectors and the prefix that reconstructs
/// the remaining four in the fold. Entries 0..3 omit roots 1, 2, and 3,
/// respectively. Entry 3 is `q * (1-q) * (2-q) * (3-q)`, shared by the
/// selectors that omit roots 4 through 7; those are completed by the prover.
fn seven_root_selectors(q: Fp) -> [Fp; 4] {
    let f1 = constant(5).sub(&q);
    let f2 = constant(0).sub(&q);
    let f3 = constant(1).sub(&q);
    let tail = constant(2)
        .sub(&q)
        .mul(&constant(3).sub(&q))
        .mul(&constant(4).sub(&q))
        .mul(&constant(12).sub(&q));
    let q_tail = q.mul(&tail);
    let q_f1_f2 = q.mul(&f1).mul(&f2);
    [
        q_tail.mul(&f2.mul(&f3)),
        q_tail.mul(&f1.mul(&f3)),
        q_f1_f2.mul(&tail),
        q_f1_f2.mul(&f3),
    ]
}

/// Evaluates the fixed-only gate selectors in fused-kernel consumption order.
///
/// `queries` is a gate frame in [`GATE_QUERY_DESCRIPTORS`] order. Only the
/// fixed slots listed below are read, so the host generator can leave advice
/// slots zero. The output is 38 selectors followed by three shared prefixes.
/// All slot ranges below are half-open:
///
/// | Fixed column | Input frame slot | Selector output slots | Prefix output slot |
/// | --- | --- | --- | --- |
/// | 18 | 38 | 0..3, 7..10 | — |
/// | 19 | 39 | 3..7 | — |
/// | 20 | 40 | 10..15 | — |
/// | 21 | 41 | 15..19 | — |
/// | 24 | 44 | 19..23 | — |
/// | 25 | 45 | 23..25, 27..31 | — |
/// | 26 | 46 | 25..27, 31 | 40 |
/// | 27 | 47 | 32..35 | 38 |
/// | 28 | 48 | 35..38 | 39 |
pub fn prepare_gate_selectors(
    queries: &[Fp; GATE_QUERY_COUNT],
) -> [Fp; PREPARED_GATE_SELECTOR_ROW] {
    let fixed_18_selectors = selector_family::<6>(queries[38]);
    let fixed_19_selectors = selector_family::<4>(queries[39]);
    let fixed_20_selectors = selector_family::<5>(queries[40]);
    let fixed_21_selectors = selector_family::<4>(queries[41]);
    let fixed_24_selectors = selector_family::<4>(queries[44]);
    let fixed_25_selectors = selector_family::<6>(queries[45]);
    let fixed_26_selectors = seven_root_selectors(queries[46]);
    let fixed_27_selectors = seven_root_selectors(queries[47]);
    let fixed_28_selectors = seven_root_selectors(queries[48]);
    [
        fixed_18_selectors[0],
        fixed_18_selectors[1],
        fixed_18_selectors[2],
        fixed_19_selectors[0],
        fixed_19_selectors[1],
        fixed_19_selectors[2],
        fixed_19_selectors[3],
        fixed_18_selectors[3],
        fixed_18_selectors[4],
        fixed_18_selectors[5],
        fixed_20_selectors[0],
        fixed_20_selectors[1],
        fixed_20_selectors[2],
        fixed_20_selectors[3],
        fixed_20_selectors[4],
        fixed_21_selectors[0],
        fixed_21_selectors[1],
        fixed_21_selectors[2],
        fixed_21_selectors[3],
        fixed_24_selectors[0],
        fixed_24_selectors[1],
        fixed_24_selectors[2],
        fixed_24_selectors[3],
        fixed_25_selectors[0],
        fixed_25_selectors[1],
        fixed_26_selectors[0],
        fixed_26_selectors[1],
        fixed_25_selectors[2],
        fixed_25_selectors[3],
        fixed_25_selectors[4],
        fixed_25_selectors[5],
        fixed_26_selectors[2],
        fixed_27_selectors[0],
        fixed_27_selectors[1],
        fixed_27_selectors[2],
        fixed_28_selectors[0],
        fixed_28_selectors[1],
        fixed_28_selectors[2],
        fixed_27_selectors[3],
        fixed_28_selectors[3],
        fixed_26_selectors[3],
    ]
}
