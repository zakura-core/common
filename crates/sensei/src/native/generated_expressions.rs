//! Hand-maintained fused kernels for the pinned Orchard/Halo 2 gate and
//! lookup polynomials, with test-only source-tree references.
//!
//! `reference.rs` owns the test-only `TREES` table and recursive `evaluate`
//! oracle, exposed here for existing test callers. `tests.rs` holds the
//! agreement tests, structural censuses, and manual benchmarks. See the
//! [expression execution map](crate::native#expression-execution-paths) for
//! production consumers, agreement tests, and the reference's independence boundary.
//! Tree structure is pinned alongside the historical imported container
//! digest, with only the reviewed curve-selector reassociation undone.
//!
//! The gate/lookup index layout, constants, and fused
//! kernels remain hand-maintained. The `*_matches_tree_reference` tests pin
//! their arithmetic to the source trees; degree and dependency censuses pin
//! the degree-class memberships and query reads. Keep these references
//! separate from the optimized kernels they check.

#[cfg(test)]
use crate::Error;
use sensei_shared::N;

use super::field::{Fp, ProductSum};

pub(crate) use super::expression_layout::*;

// The query frame is circuit shape from `sensei-shared`; Sensei's complete
// selector recipe is shared by its runtime and host-side generator.
pub(crate) use crate::selector_preparation::{
    PREPARED_GATE_SELECTOR_COUNT, PREPARED_GATE_SELECTOR_FIXED_QUERY, PREPARED_GATE_SELECTOR_ROW,
    prepare_gate_selectors,
};
pub(crate) use sensei_shared::queries::{GATE_QUERY_COUNT, GATE_QUERY_DESCRIPTORS, QueryKind};

pub(crate) use sensei_shared::constants::{POSEIDON_MDS, constant, scale};

/// `2^130 = constant(8)·constant(9)` (`2^124·2^6`), the fixed scale of gate
/// 14's first body, folded at compile time instead of multiplied per row.
const TWO_POW_130: Fp =
    udon::fp_hex!("0x0000000000000000000000000000000400000000000000000000000000000000");

/// Expands to the `q · ∏(cᵢ − q)` gate-selector product chain: `q` times
/// `constant(cᵢ) - q` for each listed constant.
///
/// This direct chain is the reference for the combined digit polynomials,
/// paired-root forms [`range_8`] and [`range_4`], and prepared selectors.
#[cfg(test)]
macro_rules! selector {
    ($q:expr, $($c:literal),+ $(,)?) => {
        $q $(.mul(&constant($c).sub(&$q)))+
    };
}

/// Pair-product constants for [`range_8`], absent from the shared table.
const TWELVE: Fp =
    udon::fp_hex!("0x000000000000000000000000000000000000000000000000000000000000000c");
const SIXTY: Fp =
    udon::fp_hex!("0x000000000000000000000000000000000000000000000000000000000000003c");

/// `x(1−x)…(7−x)` in three products by pairing roots about `7/2`:
/// with `t = x(7−x)` and `u = t(12−t)`, the product is `u(60−4t−u)`.
/// The single-Action fold uses this separate range evaluation because it
/// cannot amortize preparation of combined digit/range coefficients.
#[inline(always)]
fn range_8(x: &Fp) -> Fp {
    let t = x.mul(&constant(12).sub(x));
    let u = t.mul(&TWELVE.sub(&t));
    u.mul(&SIXTY.sub(&t.mul_by_4()).sub(&u))
}

/// The four-root range polynomial `x(1−x)(2−x)(3−x)` (`selector!(x, 5, 0,
/// 1)`) in two products instead of three: with `t = x(3 − x)`,
/// `(1−x)(2−x) = 2 − t`, so the product is `t(2 − t)`.
#[inline(always)]
fn range_4(x: &Fp) -> Fp {
    let t = x.mul(&constant(1).sub(x));
    t.mul(&constant(0).sub(&t))
}

/// `v·(a − b) + (1 − v)·(a + b)`, distributed to `a + b − (2v)·b`: one
/// product instead of two, exact for every field element `v` (no
/// Booleanity is assumed). Pinned against the direct form by
/// `complementary_control_identities_match_direct_products`.
#[inline(always)]
fn complementary_blend(v: &Fp, a: &Fp, b: &Fp) -> Fp {
    a.add(b).sub(&v.double().mul(b))
}

/// The incomplete-addition selection pair
/// `(c − (s·b + (1 − s)·a), d − (s·a + (1 − s)·b))`, distributed through
/// the shared `D = s·(b − a)` to `(c − a − D, d − b + D)`: one product
/// instead of four, exact for every field element `s`. Pinned against the
/// direct forms by `complementary_control_identities_match_direct_products`.
#[inline(always)]
fn complementary_select(s: &Fp, a: &Fp, b: &Fp, c: &Fp, d: &Fp) -> (Fp, Fp) {
    let shared = s.mul(&b.sub(a));
    (c.sub(a).sub(&shared), d.sub(b).add(&shared))
}

/// The degree-seven digit polynomial of constraints 56 and 59,
/// `q[25] + q[27]·t + … + q[33]·t⁷ − q[0]`, evaluated separately by
/// Horner's rule for one Action.
#[inline(always)]
fn digit_polynomial(t: &Fp, q: &[Fp; GATE_QUERY_COUNT]) -> Fp {
    q[33]
        .mul_add(t, &q[32])
        .mul_add(t, &q[31])
        .mul_add(t, &q[30])
        .mul_add(t, &q[29])
        .mul_add(t, &q[28])
        .mul_add(t, &q[27])
        .mul_add(t, &q[25])
        .sub(&q[0])
}

/// The digit polynomial plus its challenge-scaled range polynomial, with
/// the Action's claimed coordinate subtracted after the shared fixed
/// coefficients have been evaluated. Eight Horner products replace seven
/// digit products and three paired-root range products, before weighting.
/// Here `D(t) = q[25] + q[27]·t + … + q[33]·t⁷ − q[0]` and
/// `R(t) = t(1−t)…(7−t)`; the coefficients encode `D(t) + ρ·R(t) + q[0]`.
#[inline(always)]
fn combined_digit_polynomial(t: &Fp, coefficients: &[Fp; 9], claimed: &Fp) -> Fp {
    coefficients[8]
        .mul_add(t, &coefficients[7])
        .mul_add(t, &coefficients[6])
        .mul_add(t, &coefficients[5])
        .mul_add(t, &coefficients[4])
        .mul_add(t, &coefficients[3])
        .mul_add(t, &coefficients[2])
        .mul_add(t, &coefficients[1])
        .mul_add(t, &coefficients[0])
        .sub(claimed)
}

/// Largest number of constraints folded by one gate in [`evaluate_gate_family`].
pub(crate) const MAX_GATE_CONSTRAINTS: usize = 14;

/// Constraint slots one generated bilinear kernel covers.
const BILINEAR_BLOCK_LEN: usize = 4;

/// First constraint of gate 6's bilinear block: programs 13..17 are
/// `(x·x') · {x' − x, y' + y} · {λ² − x − x' − x_r, λ(x − x_r) − y − y_r}`,
/// recognized from the source recipes at expansion and lowered to
/// `weighted_bilinear_kernel_13`, so the fold pays two products and one
/// limb product for the block instead of six and four.
const GATE_6_BILINEAR_FIRST: usize = 13;
const _: () = assert!(
    GATES[6].start <= GATE_6_BILINEAR_FIRST
        && GATE_6_BILINEAR_FIRST + BILINEAR_BLOCK_LEN <= GATES[6].end,
    "gate 6's bilinear block must lie inside gate 6"
);

// The generated kernels read `Fp`, `RowSum`, `GATE_QUERY_COUNT`,
// `GATE_CONSTRAINT_COUNT`, `constant`, and `scale` from this module.
sensei_macros::weighted_bilinear_kernel!(13);

/// The groups lowered by `weighted_factor_kernel!`, by program:
/// gate 20's five `adv8` products, gate 32's `adv4` and `adv14` groups of
/// four, and the paired gates 43/54's `adv9` group at the second bank's
/// slots. Each kernel returns the shared factor and the reduced weighted
/// sum of the other operands; the fold adds their product as one limb
/// product for the whole group. The range banks' three-member groups are
/// not lowered: two of their three products are already shared across gates
/// below.
#[cfg(test)]
const FACTOR_GROUPS: [&[usize]; 4] = [
    &[67, 68, 69, 70, 72],
    &[105, 111, 112, 114],
    &[106, 115, 116, 118],
    &[186, 190, 191, 192],
];
sensei_macros::weighted_factor_kernel!([67, 68, 69, 70, 72]);
sensei_macros::weighted_factor_kernel!([105, 111, 112, 114]);
sensei_macros::weighted_factor_kernel!([106, 115, 116, 118]);
sensei_macros::weighted_factor_kernel!([186, 190, 191, 192]);

/// The row-level accumulator of the fused fold: one deferred product sum
/// per row per Action, reduced once when the row's value is taken.
pub(crate) type RowSum = ProductSum<super::field::PallasBase>;

/// Folds one gate's constraints `c_i` under its selector `s` into the
/// row's [`RowSum`].
///
/// Derivation: the protocol folds constraints one at a time as
/// `A ← A · y + s_i · c_i`, so an Action's row value is
/// `Σ_i s_i · c_i · P[i]` with `P[i]` the absolute power owed to slot `i`
/// (`powers`, formed once per proof). A gate's constraints share `s`, so
/// the folder builds `Σ_i c_i · P[i]` with a bounded product sum for up to
/// three terms, or [`ProductSum`] for larger gates, and, at [`Self::finish`],
/// adds `s · (that sum)` to
/// the row as one unreduced limb product — no per-gate Horner step and no
/// alignment shift. [`Self::skip`] advances past a slot whose constraint is
/// folded elsewhere ([`GATE_PROGRAMS_2N`], [`GATE_PROGRAMS_4N`], or the
/// shared affine pass); a gate whose every slot is skipped adds nothing.
/// Field arithmetic is exact, so the row value equals the sequential
/// fold's; equality with the tree reference is pinned by
/// `fused_gate_kernel_matches_tree_reference`.
struct GateFolder<'a, const COUNT: usize, const PRODUCTS: usize> {
    small: [[Fp; 3]; 2],
    row: &'a mut RowSum,
    powers: &'a [Fp; GATE_CONSTRAINT_COUNT],
    slot: usize,
    end: usize,
    selector: Fp,
    terms: usize,
    folded: RowSum,
}

impl<'a, const COUNT: usize, const PRODUCTS: usize> GateFolder<'a, COUNT, PRODUCTS> {
    #[inline(always)]
    fn new(
        row: &'a mut RowSum,
        powers: &'a [Fp; GATE_CONSTRAINT_COUNT],
        first_slot: usize,
        selector: Fp,
    ) -> Self {
        debug_assert!((1..=MAX_GATE_CONSTRAINTS).contains(&COUNT));
        debug_assert!(first_slot + COUNT <= GATE_CONSTRAINT_COUNT);
        Self {
            row,
            powers,
            slot: first_slot,
            end: first_slot + COUNT,
            selector,
            terms: 0,
            folded: ProductSum::new(),
            small: [[Fp::ZERO; 3]; 2],
        }
    }

    #[inline(always)]
    fn add_product(&mut self, left: Fp, right: Fp) {
        debug_assert!(self.terms < PRODUCTS);
        if PRODUCTS <= 3 {
            self.small[0][self.terms] = left;
            self.small[1][self.terms] = right;
        } else {
            self.folded.add_product(&left, &right);
        }
        self.terms += 1;
    }

    #[inline(always)]
    fn consume(&mut self, constraint: Fp) {
        debug_assert!(self.slot < self.end);
        self.add_product(constraint, self.powers[self.slot]);
        self.slot += 1;
    }

    /// Consumes four consecutive slots at once from a generated
    /// `weighted_bilinear_kernel!` pair: `left · right` already equals
    /// `Σ c_i · P[slot_i]` over the four slots, so the block enters the
    /// gate's sum as one unreduced limb product instead of four.
    #[inline(always)]
    fn consume_bilinear(&mut self, (left, right): (Fp, Fp)) {
        debug_assert!(self.slot + BILINEAR_BLOCK_LEN <= self.end);
        self.add_product(left, right);
        self.slot += BILINEAR_BLOCK_LEN;
    }

    /// Adds a shared-factor group: `factor · weighted` already equals
    /// `Σ c_i · P[slot_i]` over the group's slots, so the group enters the
    /// gate's sum as one unreduced limb product. The group's slots advance
    /// through [`Self::group_member`] where they fall in the schedule.
    #[inline(always)]
    fn consume_group(&mut self, (factor, weighted): (Fp, Fp)) {
        self.add_product(factor, weighted);
    }

    /// Advances past a slot whose constraint a group kernel carries.
    #[inline(always)]
    fn group_member(&mut self) {
        debug_assert!(self.slot < self.end);
        self.slot += 1;
    }

    /// Advances past a constraint whose contribution is folded elsewhere;
    /// the slot still occupies its position in the protocol fold order.
    #[inline(always)]
    fn skip(&mut self) {
        debug_assert!(self.slot < self.end);
        self.slot += 1;
    }

    #[inline(always)]
    fn finish(self) {
        debug_assert_eq!(self.slot, self.end);
        debug_assert_eq!(self.terms, PRODUCTS);
        if self.terms != 0 {
            let folded = if PRODUCTS <= 3 {
                match self.terms {
                    1 => self.small[0][0].mul(&self.small[1][0]),
                    2 => Fp::sum_of_products(
                        self.small[0].first_chunk::<2>().unwrap(),
                        self.small[1].first_chunk::<2>().unwrap(),
                    ),
                    3 => Fp::sum_of_products(&self.small[0], &self.small[1]),
                    _ => unreachable!(),
                }
            } else {
                self.folded.finish()
            };
            self.row.add_product(&self.selector, &folded);
        }
    }
}

/// Fixed frame slots used to prepare coefficients shared by all Actions:
/// eight digit coefficients, two digit selectors, and two addition selectors.
pub(crate) const ROW_COEFFICIENT_QUERY_SLOTS: [usize; 12] =
    [25, 27, 28, 29, 30, 31, 32, 33, 42, 43, 36, 37];

mod affine;

/// Challenge-only coefficients shared by every row and Action of a proof.
pub(crate) struct GateChallengeCoefficients {
    affine: affine::Coefficients,
    /// The weights of gate 21's fifth powers before its row selector.
    mds_21: [Fp; 3],
    output_22: [Fp; 3],
    /// The advance between the two banks of paired gates.
    y_37: Fp,
    /// Nonconstant coefficients of `y·R(t)` and `y⁻³·R(t)`, where
    /// `R(t) = t(1−t)…(7−t)`. The second bank is zero when `y = 0`.
    digit_range_shifts: [[Fp; 8]; 2],
}

impl GateChallengeCoefficients {
    pub(crate) fn new(powers: &[Fp; GATE_CONSTRAINT_COUNT], y_37: Fp, y: Fp) -> Self {
        let weights = [powers[75], powers[76], powers[77]];
        // P55/P56 = y and P62/P59 = y⁻³. At y = 0 every affected
        // absolute slot power is zero, so both weighted gates vanish;
        // choosing zero shifts preserves that case without division by zero.
        let inverse = y.invert().unwrap_or(<Fp>::ZERO);
        let digit_range_shifts = [y, inverse.square().mul(&inverse)].map(|ratio| {
            [5040, -13068, 13132, -6769, 1960, -322, 28, -1]
                .map(|coefficient| ratio.mul(&<Fp>::from_i64(coefficient)))
        });
        Self {
            affine: affine::Coefficients::new(powers),
            output_22: [27, 28, 29].map(|i| powers[79].mul(&constant(i))),
            // Transpose the fixed map onto the challenge weights once:
            // s · Σ_i P_i · Σ_j M_ij · U_j = Σ_j s · (Σ_i P_i · M_ij) · U_j.
            mds_21: core::array::from_fn(|column| {
                <Fp>::sum_of_products(
                    &weights,
                    &[
                        POSEIDON_MDS[0][column],
                        POSEIDON_MDS[1][column],
                        POSEIDON_MDS[2][column],
                    ],
                )
            }),
            y_37,
            digit_range_shifts,
        }
    }
}

/// One extended row's gate-fold coefficients: fixed digit polynomials and
/// products of prepared selectors, fixed selector-query chains, and challenge
/// powers that [`evaluate_gate_family`] applies to Action-dependent bodies.
///
/// All of them depend only on the row (through the prepared selector row and
/// the fixed frame slots [`ROW_COEFFICIENT_QUERY_SLOTS`]) and on the
/// challenge, so [`Self::for_row`] builds a row's set once and every Action
/// folded at that row shares it. [`GateChallengeCoefficients`] carries gate
/// 21's weights through the fixed MDS map and scales the digit range
/// polynomials once per proof. Gate weights use the absolute in-Action slot
/// powers `P[i]`, so each body enters the row's [`RowSum`] with its full
/// selector and challenge weight (pinned, with the kernel, by
/// `fused_gate_kernel_matches_tree_reference`).
pub(crate) struct GateRowCoefficients<'a> {
    affine: &'a affine::Coefficients,
    /// The addition triples' shared bodies, exceptional term, q14, and
    /// common cubic. The affine pass owns their two coordinate differences.
    add_gates_shared: [[Fp; 7]; 2],
    /// `selector · P[slot]` for the one-constraint gates 2, 7, 10, 24 and
    /// 28 (slots 5, 23, 34, 85 and 95).
    gate_2: Fp,
    curve_weights: [Fp; 3],
    gate_7: Fp,
    gate_10: Fp,
    gate_24: Fp,
    gate_28: Fp,
    /// Fixed-query selectors times the incomplete additions' cubic slot powers.
    incomplete_cubic: [Fp; 2],
    /// Combined digit/range polynomials, amortized across multiple Actions.
    digits: Option<DigitRowCoefficients>,
    /// Paired selectors of gates 33..36 with 44..47.
    paired_33_36: [Fp; 4],
    /// Paired selectors of gates 37/48 and 38/49.
    paired_37: Fp,
    paired_38: Fp,
    /// `selector_39 · y^5 + selector_41`, the weight of the shared bodies of
    /// gates 39/41 and 50/52 folded at the second bank's slots 177..181.
    weight_39_41: Fp,
    /// `selector_40 · P[176]`: the paired middle gates 40/51's selector at
    /// their second-bank slot.
    weight_40: Fp,
    /// Paired selectors of gates 42/53 and 43/54.
    paired_42: Fp,
    paired_43: Fp,
    /// Combined nonlinear weights of gates 33..42 and 44..53. In order:
    /// `q7(1-q7)`, `q8(1-q8)`, then
    /// the coefficients inside `q18 * (a(1-q18) + u*q7 + v*q22
    /// + k*(y*q9+q10))`. All six weights are shared by the row's Actions.
    paired_nonlinear: [Fp; 6],
    /// Gate 21's weights carried through the Poseidon MDS map, with gate
    /// 22's first constraint added to the shared first fifth power's weight.
    mds_21: [Fp; 3],
    /// Combined output weights from gate 21 and gate 22's second constraint.
    /// Together with `mds_21`, these enter the row as six unreduced products.
    negated_weights_21: [Fp; 3],
    weights_22: [Fp; 2],
    /// The challenge itself, the relative weight between a generated
    /// bilinear block's adjacent slots (`P[i] = y · P[i + 1]`).
    y: Fp,
}

/// `D(t) + y·R(t)` and `D(t) + y⁻³·R(t)` before subtracting `q[0]`,
/// under the weights `q[42]·P56` and `q[43]·P59` respectively.
struct DigitRowCoefficients {
    polynomials: [[Fp; 9]; 2],
    weights: [Fp; 2],
}

impl<'a> GateRowCoefficients<'a> {
    /// Builds one row's coefficients from its prepared selector row, the
    /// frame values at
    /// [`ROW_COEFFICIENT_QUERY_SLOTS`] (in that order), the absolute slot powers
    /// `powers[i]` the row fold accumulates under, the relative challenge
    /// powers (`y_powers[k] = y^k`) and the challenge-only coefficients.
    /// `shared_affine` also prepares combined digit polynomials, whose setup
    /// is amortized across the row's Actions.
    #[inline(always)]
    pub(crate) fn for_row(
        selectors: &[Fp; PREPARED_GATE_SELECTOR_COUNT],
        fixed_queries: [Fp; ROW_COEFFICIENT_QUERY_SLOTS.len()],
        powers: &[Fp; GATE_CONSTRAINT_COUNT],
        y_powers: &[Fp; MAX_GATE_CONSTRAINTS + 1],
        challenge: &'a GateChallengeCoefficients,
        shared_affine: bool,
    ) -> Self {
        let y_37 = &challenge.y_37;
        // An addition triple's last two gates share their final four
        // advice-dependent bodies: gate `a` (six constraints at `first..`)
        // and gate `b` (four constraints at `first + 6..`); combine their
        // selector/slot-power coefficients.
        let add_gate = |selector_a: Fp, selector_b: Fp, first: usize| -> [Fp; 6] {
            let a_shared_3 = selector_a.mul(&powers[first + 5]);
            let b_shared_3 = selector_b.mul(&powers[first + 9]);
            // Both banks advance by the same challenge powers. Combine
            // their last weight before advancing; this also holds at y = 0.
            let shared_3 = a_shared_3.add(&b_shared_3);
            // The coordinate constraints use their weights in the affine pass.
            [
                shared_3.mul(&y_powers[3]),
                shared_3.mul(&y_powers[2]),
                shared_3.mul(&y_powers[1]),
                shared_3,
                a_shared_3.neg(),
                b_shared_3.neg(),
            ]
        };
        let [c0, c1, c2, c3, c4, c5, c6, c7, s16, s18, s25, s29] = fixed_queries;
        let digits = shared_affine.then(|| {
            // Borrow the proof-level shifts instead of copying both large
            // arrays through an owning map at every row.
            let polynomial = |shifts: &[Fp; 8]| {
                [
                    c0,
                    c1.add(&shifts[0]),
                    c2.add(&shifts[1]),
                    c3.add(&shifts[2]),
                    c4.add(&shifts[3]),
                    c5.add(&shifts[4]),
                    c6.add(&shifts[5]),
                    c7.add(&shifts[6]),
                    shifts[7],
                ]
            };
            DigitRowCoefficients {
                polynomials: [
                    polynomial(&challenge.digit_range_shifts[0]),
                    polynomial(&challenge.digit_range_shifts[1]),
                ],
                weights: [s16.mul(&powers[56]), s18.mul(&powers[59])],
            }
        });
        let tail47 = &selectors[42..46];
        let tail48 = &selectors[46..50];
        let paired = |selector: &Fp, tail: &Fp| selector.mul(y_37).add(tail);
        let selector_37 = paired(&selectors[38], &selectors[35]);
        let selector_38 = paired(&selectors[39], &selectors[36]);
        let selector_39 = paired(&selectors[40], &selectors[37]);
        let selector_40 = paired(&selectors[41], &tail48[0]);
        let selector_41 = paired(&selectors[32], &tail48[1]);

        let add_gates = [
            add_gate(selectors[8], selectors[9], 24),
            add_gate(selectors[11], selectors[12], 35),
        ];
        let add_gates_shared = core::array::from_fn(|bank| {
            let c = add_gates[bank];
            let single = selectors[7 + bank * 3].mul(&powers[23 + bank * 11]);
            [
                c[0],
                c[1],
                c[2],
                c[3],
                c[4].sub(&single).mul(&constant(7)),
                c[5],
                c[1].add(&c[3]).neg().mul(&constant(7)),
            ]
        });
        // The challenge weights already passed through the MDS map. Only
        // the row selector remains (pinned by `mds_weights_match_row_fold`).
        let weights_22 = [powers[78], powers[79]].map(|power| selectors[19].mul(&power));
        let mut mds_21 = challenge.mds_21.map(|weight| selectors[18].mul(&weight));
        mds_21[0] = mds_21[0].add(&weights_22[0]);
        let mut coefficients = Self {
            affine: &challenge.affine,
            mds_21,
            negated_weights_21: core::array::from_fn(|i| {
                Fp::sum_of_products(
                    &[selectors[18], selectors[19]],
                    &[powers[75 + i], challenge.output_22[i]],
                )
                .neg()
            }),
            weights_22,
            add_gates_shared,
            gate_2: selectors[2].mul(&powers[5]),
            curve_weights: [
                selectors[3].mul(&powers[6]),
                selectors[3].mul(&powers[7]),
                selectors[4].mul(&powers[8]),
            ],
            gate_7: selectors[7].mul(&powers[23]),
            gate_10: selectors[10].mul(&powers[34]),
            gate_24: selectors[21].mul(&powers[85]),
            gate_28: selectors[24].mul(&powers[95]),
            incomplete_cubic: [s25.mul(&powers[87]), s29.mul(&powers[97])],
            digits,
            paired_33_36: [
                paired(&selectors[28], &tail47[0]),
                paired(&selectors[29], &tail47[1]),
                paired(&selectors[30], &tail47[2]),
                paired(&selectors[31], &tail47[3]),
            ],
            paired_37: selector_37,
            paired_38: selector_38,
            weight_39_41: selector_39.mul(&y_powers[5]).add(&selector_41),
            weight_40: selector_40.mul(&powers[176]),
            paired_42: paired(&selectors[33], &tail48[2]),
            paired_43: paired(&selectors[34], &tail48[3]),
            paired_nonlinear: [Fp::ZERO; 6],
            y: y_powers[1],
        };
        {
            // The paired gates reuse Boolean bodies and q18*q9/q10. Move
            // their selector/slot weights onto those common bodies before
            // evaluating any Action. P[i] = y*P[i+1] aligns adjacent slots
            // without division, including at y = 0.
            let a = coefficients.paired_33_36[0].mul(&powers[157]);
            let b = coefficients.paired_33_36[1].mul(&powers[160]);
            let d = coefficients.paired_33_36[3].mul(&powers[163]);
            let e = coefficients.paired_37.mul(&powers[165]);
            let f = coefficients.paired_38.mul(&powers[171]);
            let g = coefficients.weight_39_41.mul(&powers[180]);
            let h = coefficients.paired_42.mul(&powers[185]);
            coefficients.paired_nonlinear = [
                b.mul_add(&y_powers[1], &d),
                a.mul_add(&y_powers[1], &b).add(&e),
                a,
                f.mul(&y_powers[2]),
                h.mul(&y_powers[2]),
                f.add(&g).add(&h),
            ];
        }
        coefficients
    }
}

/// The two Sinsemilla banks' `(b + d)·(2p + a − b²)` at this row and its
/// `+1` rotation. Gates 24/25 and 28/29 share these with lookup inputs 1/2.
pub(crate) struct SinsemillaCubics {
    pub(crate) current: [Fp; 2],
    pub(crate) next: [Fp; 2],
}

impl SinsemillaCubics {
    #[inline(always)]
    fn evaluate(q: &[Fp; GATE_QUERY_COUNT], slots: [[usize; 4]; 2]) -> [Fp; 2] {
        slots.map(|[p, a, b, d]| {
            q[b].add(&q[d])
                .mul(&q[p].double().add(&q[a]).sub(&q[b].square()))
        })
    }

    #[inline(always)]
    pub(crate) fn at_row(q: &[Fp; GATE_QUERY_COUNT]) -> [Fp; 2] {
        Self::evaluate(q, [[0, 1, 3, 4], [5, 6, 8, 9]])
    }

    #[inline(always)]
    pub(crate) fn at_next_row(q: &[Fp; GATE_QUERY_COUNT]) -> [Fp; 2] {
        Self::evaluate(q, [[16, 17, 13, 14], [15, 22, 19, 10]])
    }

    #[cfg(test)]
    fn from_frame(q: &[Fp; GATE_QUERY_COUNT]) -> Self {
        Self {
            current: Self::at_row(q),
            next: Self::at_next_row(q),
        }
    }
}

/// Test entry point for the complete sequence of tiled gate families.
#[cfg(test)]
pub(crate) fn evaluate_gates<const SHARED_AFFINE: bool>(
    q: &[Fp; GATE_QUERY_COUNT],
    cubics: &SinsemillaCubics,
    selectors: &[Fp; PREPARED_GATE_SELECTOR_COUNT],
    coefficients: &GateRowCoefficients,
    powers: &[Fp; GATE_CONSTRAINT_COUNT],
    row: &mut RowSum,
) {
    let curve = first_curve_relation(&|slot| q[slot]);
    evaluate_gate_family::<SHARED_AFFINE, 0>(
        q,
        cubics,
        &curve,
        selectors,
        coefficients,
        powers,
        row,
    );
    evaluate_gate_family::<SHARED_AFFINE, 1>(
        q,
        cubics,
        &curve,
        selectors,
        coefficients,
        powers,
        row,
    );
    evaluate_gate_family::<SHARED_AFFINE, 2>(
        q,
        cubics,
        &curve,
        selectors,
        coefficients,
        powers,
        row,
    );
    evaluate_gate_family::<SHARED_AFFINE, 3>(
        q,
        cubics,
        &curve,
        selectors,
        coefficients,
        powers,
        row,
    );
    evaluate_gate_family::<SHARED_AFFINE, 4>(
        q,
        cubics,
        &curve,
        selectors,
        coefficients,
        powers,
        row,
    );
    evaluate_gate_family::<SHARED_AFFINE, 5>(
        q,
        cubics,
        &curve,
        selectors,
        coefficients,
        powers,
        row,
    );
}

/// Curve body shared by the 8N gates and the nested 4N class at the same row.
#[inline]
pub(crate) fn first_curve_relation(query: &impl Fn(usize) -> Fp) -> Fp {
    let x = query(0);
    let mut sum = ProductSum::new();
    sum.add_square(&query(1));
    sum.add_product(&x.square().neg(), &x);
    sum.add_term(&constant(3).neg());
    sum.finish()
}

/// Evaluates one gate family for one row in protocol order.
///
/// `coefficients` is the row's shared [`GateRowCoefficients`]; `q` is one
/// Action's query frame at that row; `cubics` contains that frame's current
/// and rotated Sinsemilla values; `powers[i]` is the absolute power owed
/// to gate slot `i` in the Action's block; `row` is the Action's row
/// [`RowSum`], into which every gate adds `selector · Σ body · P[slot]` as
/// one unreduced limb product. With `SHARED_AFFINE`, the constraints whose
/// bodies are affine in the advice queries (`affine(…)` below) only advance
/// the slot schedule here — [`evaluate_affine_gates`] folds them once per
/// row for every Action on the challenge-weighted aggregated frame;
/// paired gates 33..42 and 44..53 share their nonlinear weights in both paths.
/// With it false the last family adds the single-Action affine contribution.
///
/// Hand-maintained mirror of gate programs `0..GATE_CONSTRAINT_COUNT`: each
/// block folds one gate's constraints in expression-index order through
/// [`GateFolder`] from the gate's first slot, one-constraint gates add their
/// body under the row's shared `selector · P[slot]` weight, and every slot
/// — including those of the [`GATE_PROGRAMS_2N`]/[`GATE_PROGRAMS_4N`]
/// constraints this kernel skips — keeps its position. Invariants: the
/// slots are the tree reference's protocol order, and the total fold
/// equals the source-tree fold — both pinned by
/// `fused_gate_kernel_matches_tree_reference`. Rewrite freely inside those
/// bounds; the golden proofs hold the result.
///
/// Families cover gates 0–6, 7–12, 13–20, 21–22, 23–32, and 33–54.
/// The caller retains the unreduced row accumulator across all six calls.
#[inline(never)]
pub(crate) fn evaluate_gate_family<const SHARED_AFFINE: bool, const FAMILY: usize>(
    q: &[Fp; GATE_QUERY_COUNT],
    cubics: &SinsemillaCubics,
    curve_relation: &Fp,
    selectors: &[Fp; PREPARED_GATE_SELECTOR_COUNT],
    coefficients: &GateRowCoefficients,
    powers: &[Fp; GATE_CONSTRAINT_COUNT],
    row: &mut RowSum,
) {
    // Expand the fold in place, preserving its arithmetic and slot schedule.
    // `skip` reserves a slot for a constraint evaluated on a smaller coset;
    // `affine(…)` marks a body the affine pass owns (its slot is reserved
    // the same way); `bilinear(…)`
    // takes a generated kernel's factor pair for four slots at once;
    // `grouped` reserves a slot a `group(…)` carries, and `group(…)` adds
    // its shared factor and weighted sum without advancing.
    macro_rules! gate {
        // Protocol slots and remaining products differ after affine/class
        // extraction and grouping. Select the bounded kernel by products.
        (@products) => { 0 };
        (@products skip, $($rest:tt)*) => { gate!(@products $($rest)*) };
        (@products affine($body:expr), $($rest:tt)*) => { gate!(@products $($rest)*) };
        (@products grouped, $($rest:tt)*) => { gate!(@products $($rest)*) };
        (@products bilinear($pair:expr), $($rest:tt)*) => { 1 + gate!(@products $($rest)*) };
        (@products group($pair:expr), $($rest:tt)*) => { 1 + gate!(@products $($rest)*) };
        (@products $body:expr, $($rest:tt)*) => { 1 + gate!(@products $($rest)*) };
        (@rest $gate:ident,) => {};
        (@rest $gate:ident, skip, $($rest:tt)*) => {
            $gate.skip();
            gate!(@rest $gate, $($rest)*);
        };
        (@rest $gate:ident, affine($body:expr), $($rest:tt)*) => {
            $gate.skip();
            gate!(@rest $gate, $($rest)*);
        };
        (@rest $gate:ident, bilinear($pair:expr), $($rest:tt)*) => {
            $gate.consume_bilinear($pair);
            gate!(@rest $gate, $($rest)*);
        };
        (@rest $gate:ident, grouped, $($rest:tt)*) => {
            $gate.group_member();
            gate!(@rest $gate, $($rest)*);
        };
        (@rest $gate:ident, group($pair:expr), $($rest:tt)*) => {
            $gate.consume_group($pair);
            gate!(@rest $gate, $($rest)*);
        };
        (@rest $gate:ident, $next:expr, $($rest:tt)*) => {
            $gate.consume($next);
            gate!(@rest $gate, $($rest)*);
        };
        ($count:literal, $first_slot:expr, $selector:expr, $($rest:tt)*) => {{
            let mut gate = GateFolder::<$count, { gate!(@products $($rest)*) }>::new(
                row, powers, $first_slot, $selector,
            );
            gate!(@rest gate, $($rest)*);
            gate.finish();
        }};
    }
    // A one-constraint gate: its body under the row's shared
    // `selector · P[slot]` weight.
    macro_rules! single {
        ($weight:expr, $body:expr $(,)?) => {
            row.add_product(&$body, &$weight);
        };
    }
    // Keep the original affine body visible beside its protocol slot;
    // the affine pass evaluates it for both single and shared Action frames.
    macro_rules! single_affine {
        ($slot:literal, $selector:expr, $body:expr $(,)?) => {};
    }

    if FAMILY == 0 {
        // Gate 0: expressions 0..4.
        gate!(
            4,
            0,
            selectors[0],
            q[0].sub(&q[1]).sub(&q[2].mul(&q[3])),
            q[0].mul(&q[4].sub(&q[5])),
            q[0].mul(&constant(5).sub(&q[6])),
            q[1].mul(&constant(5).sub(&q[7])),
        );
        // Gate 1: expression 4.
        single_affine!(4, selectors[1], q[7].add(&q[8]).sub(&q[6]));
        // Gate 2: expression 5.
        single!(
            coefficients.gate_2,
            q[11].mul(&constant(6)).mul(&q[10]).sub(&q[9]),
        );
        row.add_product(
            curve_relation,
            &Fp::sum_of_products(
                &[q[0], q[1]],
                &[coefficients.curve_weights[0], coefficients.curve_weights[1]],
            )
            .add(&coefficients.curve_weights[2]),
        );
        {
            // Gate 5: expressions 9..11.
            let v1 = q[0].sub(&q[2]);
            let v2 = q[1].sub(&q[3]);
            let mut secant = ProductSum::new();
            secant.add_square(&v2);
            secant.add_product(&q[12].add(&q[2]).add(&q[0]).neg(), &v1.square());
            gate!(
                2,
                9,
                selectors[5],
                secant.finish().neg(),
                q[13]
                    .add(&q[3])
                    .mul_sub_product(&v1, &v2, &q[2].sub(&q[12])),
            );
        }
        {
            // Gate 6: expressions 11..23. Slots 13..17 are the generated
            // bilinear block (`GATE_6_BILINEAR_FIRST`); the kernel re-derives
            // its `x' − x` and `y' + y` operands from the frame (two additions)
            // rather than sharing `v1`/`v7`, keeping its inputs the source
            // recipes alone.
            let v1 = q[2].sub(&q[0]);
            let v2 = constant(5).sub(&v1.mul(&q[5]));
            let v7 = q[3].add(&q[1]);
            let v9 = constant(5).sub(&q[0].mul(&q[6]));
            let v10 = constant(5).sub(&q[2].mul(&q[7]));
            let v11 = v2.sub(&v7.mul(&q[8]));
            // Each exceptional-case pair shares its factor: sum the two
            // coordinate differences under their absolute slot weights first.
            // This saves three products and three intermediate reductions per
            // row, without assuming Boolean controls or a valid curve point.
            gate!(
                12,
                11,
                selectors[6],
                v1.mul(&v1.mul(&q[4]).sub(&q[3].sub(&q[1]))),
                v2.mul(&q[1].double().mul(&q[4]).sub(&q[0].square().triple()),),
                bilinear(weighted_bilinear_kernel_13(q, &coefficients.y, powers)),
                grouped,
                grouped,
                grouped,
                grouped,
                grouped,
                grouped,
                group((
                    v9,
                    <Fp>::sum_of_products(
                        &[q[12].sub(&q[2]), q[13].sub(&q[3])],
                        &[powers[17], powers[18]],
                    ),
                )),
                group((
                    v10,
                    <Fp>::sum_of_products(
                        &[q[12].sub(&q[0]), q[13].sub(&q[1])],
                        &[powers[19], powers[20]],
                    ),
                )),
                group((
                    v11,
                    <Fp>::sum_of_products(&[q[12], q[13]], &[powers[21], powers[22]]),
                )),
            );
        }
        // The addition triples differ only in their selector and query indices:
    }
    if FAMILY == 1 {
        // a one-constraint gate under the row's shared weight, then the two
        // gates sharing their final four advice-dependent bodies under the
        // row's combined selector/slot-power coefficients
        // (`GateRowCoefficients::add_gates`).
        macro_rules! add_gates {
            ($weight:expr, $pair:literal, [$q3:literal, $q4:literal, $q5:literal, $q9:literal,
            $q11:literal, $q13:literal, $q14:literal, $q15:literal]) => {{
                let exceptional = q[$q14]
                    .add(&q[$q15])
                    .mul(&q[$q13].sub(&q[$q14].square().sub(&q[$q13]).sub(&q[16])));
                single!($weight, q[$q4]);
                {
                    let v1 = q[$q9].sub(&q[$q11].double());
                    let v2 = q[$q4].square().sub(&q[$q3]).sub(&q[0]);
                    let v3 = q[$q4].add(&q[$q5]).mul(&q[$q3].sub(&v2));
                    let shared_0 = v1.sub(&v1.square());
                    let shared_1 = Fp::sum_of_products(
                        &[q[$q4], v1.double().sub(&constant(5))],
                        &[q[$q3].sub(&q[0]), q[1]],
                    );
                    let shared_2 = q[$q5].square().sub(&q[$q13]).sub(&v2).sub(&q[$q3]);
                    let shared_3 = q[$q5].mul(&q[$q3].sub(&q[$q13]));
                    {
                        // The affine `x − x'`, `y − y'` bodies belong to the
                        // shared pass; the remaining coefficients keep their
                        // absolute powers.
                        let bodies = [
                            shared_0,
                            shared_1,
                            shared_2,
                            shared_3,
                            exceptional,
                            q[$q14],
                            v3,
                        ];
                        for (body, weight) in
                            bodies.iter().zip(&coefficients.add_gates_shared[$pair])
                        {
                            row.add_product(body, weight);
                        }
                    }
                }
            }};
        }
        // Gates 7..10: expressions 23..34; gates 10..13: expressions 34..45.
        add_gates!(coefficients.gate_7, 0, [3, 4, 5, 9, 11, 13, 14, 15]);
        add_gates!(coefficients.gate_10, 1, [7, 8, 2, 6, 20, 18, 19, 12]);
    }
    if FAMILY == 2 {
        {
            // Gate 13: expressions 45..47. Constraint 46's complementary
            // controls distribute: `v·(a − b) + (1 − v)·(a + b)`
            // is `a + b − 2v·b` for arbitrary `v`, one product instead of two;
            // `2·q[11]` is a doubling rather than a product by the table's `2`.
            let v1 = q[10].sub(&q[11].double());
            gate!(
                2,
                45,
                selectors[13],
                v1.sub(&v1.square()),
                complementary_blend(&v1, &q[9], &q[21]),
            );
        }
        // Gate 14: expressions 47..52.
        gate!(
            5,
            47,
            selectors[14],
            affine(q[8].sub(&q[7].add(&q[23].mul(&TWO_POW_130)))),
            affine(q[20].sub(&q[7]).sub(&constant(10))),
            q[23].mul(&q[6].sub(&constant(8))),
            q[23].mul(&q[18]),
            constant(5)
                .sub(&q[23])
                .mul(&constant(5).sub(&q[6].mul(&q[22])))
                .mul(&q[18]),
        );
        {
            // Gate 15: expressions 52..55. Constraints 53 and 54 distribute
            // their complementary controls: with `w = 1 − v`,
            // `v·a + w·(a − b) = a − w·b` and `v·c + w·(c + d) = c + w·d` for
            // arbitrary `v`, one product each instead of two.
            let v1 = q[10].sub(&q[9].double());
            let v2 = constant(5).sub(&v1);
            gate!(
                3,
                52,
                selectors[15],
                v1.mul(&v2),
                q[0].sub(&v2.mul(&q[16])),
                q[1].add(&v2.mul(&q[17])),
            );
        }
        if SHARED_AFFINE {
            // Gates 16/17: P55·R(t) + P56·D(t) = P56·(D(t) + y·R(t)).
            // Slots 57/58 remain on the 2N/4N classes. The row coefficients
            // include q[42] and the absolute slot power, shared by all Actions.
            let digits = coefficients
                .digits
                .as_ref()
                .expect("shared digit coefficients are prepared");
            let gate_16_input = q[4].sub(&q[14].mul_by_8());
            single!(
                digits.weights[0],
                combined_digit_polynomial(&gate_16_input, &digits.polynomials[0], &q[0]),
            );
            // Gate 18: P59·D(t) + P62·R(t) = P59·(D(t) + y⁻³·R(t)).
            // Slots 60/61 remain on the 2N/4N classes; q[43] is in the weight.
            single!(
                digits.weights[1],
                combined_digit_polynomial(&q[4], &digits.polynomials[1], &q[0]),
            );
        } else {
            // With one Action, keep the separate evaluations: the combined
            // coefficients have no reuse to repay their preparation cost.
            let gate_16_input = q[4].sub(&q[14].mul_by_8());
            gate!(
                4,
                55,
                q[42],
                range_8(&gate_16_input),
                digit_polynomial(&gate_16_input, q),
                skip, // Program 57 folds on the 2N class.
                skip, // Program 58 folds on the 4N class.
            );
            gate!(
                4,
                59,
                q[43],
                digit_polynomial(&q[4], q),
                skip, // Program 60 folds on the 2N class.
                skip, // Program 61 folds on the 4N class.
                range_8(&q[4]),
            );
        }
        // Gate 19: expressions 63..67.
        gate!(
            4,
            63,
            selectors[16],
            q[5].sub(&q[5].square()),
            q[4].square().sub(&constant(5)),
            q[1].sub(&q[3]).mul(&q[1].add(&q[3])),
            q[4].mul(&q[1]).sub(&q[3]),
        );
        {
            // Gate 20: expressions 67..75. Programs 67..71 and 72 are the
            // generated `adv8` group (`FACTOR_GROUPS[0]`).
            gate!(
                8,
                67,
                selectors[17],
                grouped,
                grouped,
                grouped,
                grouped,
                range_4(&q[7]),
                grouped,
                skip, // Program 73 folds on the 4N class.
                skip, // Program 74 folds on the 4N class.
                group(weighted_factor_kernel_67(q, powers)),
            );
        }
    }
    if FAMILY == 3 {
        let gate_21_base = q[6].add(&q[28]);
        let gate_21_base_squared = gate_21_base.square();
        let gate_21_base_fifth = gate_21_base_squared.square().mul(&gate_21_base);
        {
            // Gate 21: expressions 75..78. The three MDS rows' weights are
            // carried into the row coefficients: each fifth power enters
            // the row once under its combined weight and each subtracted
            // next-state value once under its negated slot weight — six
            // unreduced products in place of nine MDS products, three weighted
            // bodies and the selector product, with their four finishes.
            let v4 = q[7].add(&q[29]);
            let v5 = v4.square();
            let v6 = v5.square().mul(&v4);
            let v7 = q[8].add(&q[30]);
            let v8 = v7.square();
            let v9 = v8.square().mul(&v7);
            for (power, weight) in [gate_21_base_fifth, v6, v9]
                .iter()
                .zip(&coefficients.mds_21)
            {
                row.add_product(power, weight);
            }
            if !SHARED_AFFINE {
                for (value, weight) in [q[22], q[18], q[19]]
                    .iter()
                    .zip(&coefficients.negated_weights_21)
                {
                    row.add_product(value, weight);
                }
            }
        }
        {
            // Gate 22: expressions 78..82.
            let v3 = q[7].add(&q[29]);
            let v4 = q[8].add(&q[30]);
            const MDS_ROW: [Fp<udon::field::Reduced>; 3] = [
                constant(18).reduce(),
                constant(19).reduce(),
                constant(20).reduce(),
            ];
            let v5 = <Fp>::sum_of_products(&[q[5], v3, v4], &MDS_ROW).add(&q[31]);
            let v6 = v5.square();
            if !SHARED_AFFINE {
                row.add_product(&q[5], &coefficients.weights_22[0].neg());
            }
            row.add_product(&v6.square().mul(&v5), &coefficients.weights_22[1]);
        }
    }
    if FAMILY == 4 {
        // Gate 23: expressions 82..85, all folded on the 4N class; under
        // absolute slot powers nothing remains here.
        // The incomplete-addition quartets share the same constraint bodies.
        macro_rules! incomplete_add_gates {
            ($bank:literal, $weight:expr, $s:literal, $first:literal, [$q0:literal, $q1:literal, $q2:literal,
            $q3:literal, $q4:literal], [$q12:literal, $q13:literal, $q14:literal,
            $q16:literal, $q17:literal, $q25:literal, $q34:literal, $q36:literal]) => {{
                // The quartet's first gate, at slot `$first`.
                single!($weight, q[$q25].double().sub(&cubics.current[$bank]),);
                {
                    // The second gate's first constraint (slot `$first + 1`) folds
                    // on the 2N class; its second, at `$first + 2`, is gated by
                    // the fixed query at frame slot `$q36`.
                    let v1 = q[$q34].square().sub(&q[$q34]);
                    let constraint = Fp::sum_of_products(
                        &[q[$q4].mul_by_4(), v1],
                        &[
                            q[$q0].sub(&q[$q16]),
                            cubics.next[$bank].sub(&q[$q13].double()),
                        ],
                    )
                    .sub(&cubics.current[$bank].add(&cubics.next[$bank]).double());
                    row.add_product(&constraint, &coefficients.incomplete_cubic[$bank]);
                }
                {
                    // The control `s = q[$q4]` selects between the two input
                    // coordinates in both bodies: one shared product
                    // `D = s·(q[$q1] − q[$q0])` replaces the four
                    // `s·x + (1 − s)·x'` products, exactly for arbitrary `s`.
                    let (select_0, select_1) =
                        complementary_select(&q[$q4], &q[$q0], &q[$q1], &q[$q2], &q[$q3]);
                    gate!(
                        3,
                        $first + 3,
                        selectors[$s + 1],
                        select_0,
                        select_1,
                        q[$q4].sub(&q[$q4].square()),
                    );
                }
                // The quartet's last gate is affine throughout; its four
                // slots belong to the affine pass.
                gate!(
                    4,
                    $first + 6,
                    selectors[$s + 2],
                    affine(q[$q0].sub(&q[$q16].mul(&constant(6))).sub(&q[$q14])),
                    affine(
                        q[$q16]
                            .add(
                                &q[$q1]
                                    .sub(&q[$q17].mul(&constant(6)))
                                    .add(&q[$q12].mul(&constant(6)))
                                    .mul(&constant(36)),
                            )
                            .sub(&q[$q3])
                    ),
                    affine(q[$q13].add(&q[$q2].mul(&constant(37))).sub(&q[$q4])),
                    affine(q[$q17].sub(&q[$q12].add(&q[$q13].mul(&constant(37))))),
                );
            }};
        }
        // Gates 24..28: expressions 85..95; gates 28..32: expressions 95..105.
        incomplete_add_gates!(
            0,
            coefficients.gate_24,
            21,
            85,
            [0, 1, 2, 3, 4],
            [12, 13, 14, 16, 17, 25, 34, 36]
        );
        incomplete_add_gates!(
            1,
            coefficients.gate_28,
            24,
            95,
            [5, 6, 7, 8, 9],
            [18, 19, 10, 15, 22, 27, 35, 37]
        );
        {
            // Gate 32: expressions 105..119. The `adv4` products (105, 111,
            // 112, 114) and `adv14` products (106, 115, 116, 118) are the
            // generated groups `FACTOR_GROUPS[1]` and `FACTOR_GROUPS[2]`.
            gate!(
                14,
                105,
                selectors[27],
                grouped,
                grouped,
                affine(q[2].sub(&<Fp>::sum_of_products(
                    &[q[3], q[4], q[5]],
                    &[constant(5), constant(38), constant(37)],
                ))),
                affine(q[12].sub(&q[13].add(&q[14].mul(&constant(39))))),
                affine(
                    <Fp>::sum_of_products(
                        &[q[1], q[3], q[4]],
                        &[constant(5), constant(40), constant(41)],
                    )
                    .sub(&q[0])
                ),
                affine(
                    <Fp>::sum_of_products(
                        &[q[5].add(&q[17].mul(&constant(37))), q[13], q[14]],
                        &[constant(5), constant(42), constant(41)],
                    )
                    .sub(&q[16])
                ),
                grouped,
                grouped,
                affine(q[1].add(&constant(16)).sub(&constant(17)).sub(&q[7])),
                grouped,
                grouped,
                grouped,
                affine(
                    q[5].add(&q[17].mul(&constant(37)))
                        .add(&constant(43))
                        .sub(&constant(17))
                        .sub(&q[18])
                ),
                grouped,
                group(weighted_factor_kernel_105(q, powers)),
                group(weighted_factor_kernel_106(q, powers)),
            );
        }
    }
    if FAMILY == 5 {
        // Gates 33..43 and 44..54 have the same constraint bodies: fold each pair
        // once at the second bank's slots (156..193) under the row's paired
        // selector coefficients (the prepared selectors times `y^37` plus the
        // leave-one-out tails of the fixed queries at slots 46..48, formed once
        // per row in `GateRowCoefficients::for_row`).
        {
            let [c7, c8, a, u, v, k] = &coefficients.paired_nonlinear;
            // The affine pass owns the other bodies in these seven groups.
            // Collect the remaining terms across groups into two Boolean
            // contributions and one factored q18 contribution. This inner dot
            // product replaces the seven separately reduced gate sums.
            let inner = <Fp>::sum_of_products(
                &[
                    constant(5).sub(&q[18]),
                    q[7],
                    q[22],
                    q[9].mul_add(&coefficients.y, &q[10]),
                ],
                &[*a, *u, *v, *k],
            );
            row.add_product(&q[7].sub(&q[7].square()), c7);
            row.add_product(&q[8].sub(&q[8].square()), c8);
            row.add_product(&q[18], &inner);
        }
        // Gates 43 and 54: expressions 149..156 and 186..193. The `adv9`
        // products (186, 190, 191, 192) are the generated group
        // `FACTOR_GROUPS[3]`, weighted at the second bank's slots like the
        // rest of the pair.
        gate!(
            7,
            186,
            coefficients.paired_43,
            grouped,
            affine(q[15].sub(&<Fp>::sum_of_products(
                &[q[6], q[7], q[22]],
                &[constant(5), constant(0), constant(6)],
            ))),
            affine(q[5].sub(&<Fp>::sum_of_products(
                &[q[15], q[8], q[9]],
                &[constant(5), constant(40), constant(41)],
            ))),
            affine(q[15].add(&constant(16)).sub(&constant(17)).sub(&q[19])),
            grouped,
            grouped,
            grouped,
            group(weighted_factor_kernel_186(q, powers)),
        );
        if !SHARED_AFFINE {
            row.add_term(&evaluate_affine_gates::<false>(
                q,
                &Fp::ONE,
                selectors,
                coefficients,
                powers,
            ));
        }
    }
}

/// The advice frame slots the 8N and 4N affine gate families read; the fold
/// aggregates exactly these across Actions for their shared evaluations.
pub(crate) const AFFINE_QUERY_SLOTS: [usize; 23] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24,
];

/// Folds, once per row for every Action, the 36 gate constraint bodies that
/// are affine in the advice queries. With `MIXED_TERMS`, also folds the
/// four affine summands of the nonlinear gates 21 and 22. These remain on
/// the 8N domain: individual summands need not vanish on the base domain.
///
/// Derivation: a constraint `i` of Action `a` enters the fold as
/// `y^(215·(A−1−a)) · y^22 · y^(192−i) · s_i · c_i(q_a)`. For a body affine in
/// the queries, `Σ_a w_a · c_i(q_a) = c_i(Σ_a w_a · q_a)` with every additive
/// constant scaled by `W = Σ_a w_a`, so the family is evaluated on the
/// aggregated frame `q = Σ_a w_a · q_a` (on [`AFFINE_QUERY_SLOTS`]) and the
/// caller adds the result unscaled to the last Action's row sum. `powers[i]`
/// is the absolute in-Action power of gate slot `i` (the same table the
/// fused kernel accumulates under, so the `y^22` rule-block offset is
/// inside it); paired-bank bodies use their second bank's index with the
/// row's paired coefficient, whose `y^37` covers the first bank, the
/// gates-39/41 weight carries its `y^5` offset and `weight_40` its slot's
/// power, as in the kernel. Field arithmetic is exact, so the split fold is
/// equal as field elements to `evaluate_gates::<false>` (pinned by
/// `shared_affine_pass_matches_fused_kernel`).
pub(crate) fn evaluate_affine_gates<const MIXED_TERMS: bool>(
    q: &[Fp; GATE_QUERY_COUNT],
    weight_sum: &Fp,
    selectors: &[Fp; PREPARED_GATE_SELECTOR_COUNT],
    coefficients: &GateRowCoefficients,
    powers: &[Fp; GATE_CONSTRAINT_COUNT],
) -> Fp {
    let gate_1 = q[7].add(&q[8]).sub(&q[6]).mul(&powers[4]);
    let delta_x = q[0].sub(&q[16]);
    let delta_y = q[1].sub(&q[17]);
    let gate_8 = Fp::sum_of_products(&[delta_x, delta_y], &[powers[24], powers[25]]);
    let gate_11 = Fp::sum_of_products(&[delta_x, delta_y], &[powers[35], powers[36]]);
    let gate_14 = coefficients.affine.gate_14(q, weight_sum);
    let gate_27 = coefficients.affine.gate_27(q, weight_sum);
    let gate_31 = coefficients.affine.gate_31(q, weight_sum);
    let gate_32 = coefficients.affine.gate_32(q, weight_sum);
    let difference = q[6].sub(&q[7]);
    let gate_33 = coefficients.affine.gate_33(q, &difference);
    let gate_34 = coefficients.affine.gate_34(q, &difference);
    let gate_35 = coefficients.affine.gate_35(q, &difference);
    let gate_36 = coefficients.affine.gate_36(q, &difference);
    let gate_37 = coefficients.affine.gate_37(q, &difference);
    let gate_38 = coefficients.affine.gate_38(q, weight_sum);
    let gates_39_41 = coefficients.affine.gates_39_41(q, weight_sum);
    let gate_40 = coefficients.affine.gate_40(q, weight_sum);
    let gate_42 = coefficients.affine.gate_42(q, weight_sum);
    let gate_43 = coefficients.affine.gate_43(q, weight_sum);
    let left = [
        selectors[1],
        selectors[8],
        selectors[11],
        selectors[14],
        selectors[23],
        selectors[26],
        selectors[27],
        coefficients.paired_33_36[0],
        coefficients.paired_33_36[1],
        coefficients.paired_33_36[2],
        coefficients.paired_33_36[3],
        coefficients.paired_37,
        coefficients.paired_38,
        coefficients.weight_39_41,
        coefficients.weight_40,
        coefficients.paired_42,
        coefficients.paired_43,
        coefficients.negated_weights_21[0],
        coefficients.negated_weights_21[1],
        coefficients.negated_weights_21[2],
        coefficients.weights_22[0].neg(),
    ];
    let right = [
        gate_1,
        gate_8,
        gate_11,
        gate_14,
        gate_27,
        gate_31,
        gate_32,
        gate_33,
        gate_34,
        gate_35,
        gate_36,
        gate_37,
        gate_38,
        gates_39_41,
        gate_40,
        gate_42,
        gate_43,
        q[22],
        q[18],
        q[19],
        q[5],
    ];
    if MIXED_TERMS {
        Fp::sum_of_products(&left, &right)
    } else {
        Fp::sum_of_products::<17>(
            left[..17].try_into().unwrap(),
            right[..17].try_into().unwrap(),
        )
    }
}

/// Gate constraint programs of total degree 3, whose quotient contribution
/// is determined by the 2N sub-coset. [`evaluate_gate_family`]
/// skips their y-slots; [`evaluate_gates_2n`] folds them on the class. The
/// membership is hand-listed and pinned by the tree degree census
/// (`quotient_degree_class_census`).
pub(crate) const GATE_PROGRAMS_2N: [usize; 4] = [57, 60, 86, 96];

/// Gate constraint programs of total degree 4–5 on the 4N sub-coset, carved
/// out of [`evaluate_gate_family`] like [`GATE_PROGRAMS_2N`] and folded by
/// [`evaluate_affine_gates_4n`] and the shared curve body.
pub(crate) const GATE_PROGRAMS_4N: [usize; 9] = [58, 61, 73, 74, 80, 81, 82, 83, 84];

/// The specialized gate kernels and the gate programs each implements: the
/// fused row kernel takes every gate constraint except the carved
/// degree-class lists, which their class kernels fold on their own domains.
/// Metadata for review and the `kernel_metadata` tests; row evaluation never
/// dispatches on it.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum GateKernel {
    /// [`evaluate_gate_family`], on the 8N extended coset.
    Fused,
    /// [`evaluate_gates_2n`], on the 2N class.
    Class2N,
    /// [`evaluate_gates_4n`], on the 4N class.
    Class4N,
}

#[cfg(test)]
impl GateKernel {
    pub(crate) const ALL: [Self; 3] = [Self::Fused, Self::Class2N, Self::Class4N];

    /// Whether this kernel implements gate program `program`.
    pub(crate) fn implements(self, program: usize) -> bool {
        match self {
            Self::Class2N => GATE_PROGRAMS_2N.contains(&program),
            Self::Class4N => GATE_PROGRAMS_4N.contains(&program),
            Self::Fused => {
                program < GATE_CONSTRAINT_COUNT
                    && !GATE_PROGRAMS_2N.contains(&program)
                    && !GATE_PROGRAMS_4N.contains(&program)
            }
        }
    }
}

/// Folds the [`GATE_PROGRAMS_2N`] constraints for one class row onto
/// `accumulator`.
///
/// `query` maps a frame index (as in [`GATE_QUERY_DESCRIPTORS`]) to the
/// query value at the row; `y_powers[k]` is the absolute y-power owed to
/// `GATE_PROGRAMS_2N[k]`'s slot in the protocol fold order.
pub(crate) fn evaluate_gates_2n(
    query: &impl Fn(usize) -> Fp,
    y_powers: &[Fp; GATE_PROGRAMS_2N.len()],
    accumulator: &mut Fp,
) {
    // Programs 57/60: the second curve relation under gates 17/18's plain
    // fixed-query selectors.
    let second_curve_relation = query(5).square().sub(&query(1)).sub(&query(26));
    let selector_pair = <Fp>::sum_of_products(&[query(42), query(43)], &[y_powers[0], y_powers[1]]);
    // Program 86: gate 25's incomplete-addition x-coordinate constraint.
    let gate_25 = query(4)
        .sub(&query(3))
        .mul(&query(4).add(&query(3)))
        .sub(&query(16))
        .add(&query(1));
    // Program 96: gate 29's analog on its second query block.
    let gate_29 = query(9)
        .sub(&query(8))
        .mul(&query(9).add(&query(8)))
        .sub(&query(15))
        .add(&query(6));
    *accumulator = accumulator.add(&<Fp>::sum_of_products(
        &[
            selector_pair,
            query(36).mul(&y_powers[2]),
            query(37).mul(&y_powers[3]),
        ],
        &[second_curve_relation, gate_25, gate_29],
    ));
}

/// The 4N class's slot powers and gate 22's fixed linear map carried onto
/// those powers. Built once per proof using the in-Action slot powers.
pub(crate) struct Gate4NCoefficients {
    powers: [Fp; GATE_PROGRAMS_4N.len()],
    linear_22: [Fp; 6],
}

impl Gate4NCoefficients {
    pub(crate) fn new(powers: [Fp; GATE_PROGRAMS_4N.len()]) -> Self {
        let weights = [powers[4], powers[5]];
        Self {
            powers,
            linear_22: core::array::from_fn(|column| {
                if column < 3 {
                    <Fp>::sum_of_products(&weights, &[constant(21 + column), constant(24 + column)])
                } else {
                    <Fp>::sum_of_products(&weights, &[constant(27 + column), constant(30 + column)])
                        .neg()
                }
            }),
        }
    }
}

/// Independent per-Action entry point for the class-kernel comparisons.
#[cfg(test)]
pub(crate) fn evaluate_gates_4n(
    query: &impl Fn(usize) -> Fp,
    prepared_selectors: &[Fp; PREPARED_GATE_SELECTOR_COUNT],
    coefficients: &Gate4NCoefficients,
    accumulator: &mut Fp,
) {
    let mut row = RowSum::new();
    row.add_product(
        &first_curve_relation(query),
        &Fp::sum_of_products(
            &[query(42), query(43)],
            &[coefficients.powers[0], coefficients.powers[1]],
        ),
    );
    evaluate_affine_gates_4n::<false>(query, &Fp::ONE, prepared_selectors, coefficients, &mut row);
    *accumulator = accumulator.add(&row.finish());
}

/// Folds the seven affine 4N constraints. With `WEIGHTED`, query values
/// are Action-weighted sums, including fixed columns used inside bodies;
/// constant terms scale by `weight_sum`, while selectors remain unweighted.
pub(crate) fn evaluate_affine_gates_4n<const WEIGHTED: bool>(
    query: &impl Fn(usize) -> Fp,
    weight_sum: &Fp,
    prepared_selectors: &[Fp; PREPARED_GATE_SELECTOR_COUNT],
    coefficients: &Gate4NCoefficients,
    row: &mut RowSum,
) {
    let y_powers = &coefficients.powers;
    let constant_term = constant(17).sub(&constant(16));
    let constant_term = if WEIGHTED {
        constant_term.mul(weight_sum)
    } else {
        constant_term
    };
    // Programs 73/74: gate 20's linear constraints.
    let gate_20 = <Fp>::sum_of_products(
        &[
            query(24).sub(&query(7).add(&query(8).mul_by_4())),
            query(6)
                .sub(&query(20))
                .add(&query(24).mul(&constant(15)))
                .add(&constant_term),
        ],
        &[y_powers[2], y_powers[3]],
    );
    // Programs 80/81: gate 22's two linear constraints share their six
    // inputs. Their fixed maps have already been combined under the two
    // slot powers, leaving one product sum over those inputs and the two
    // round constants.
    let v3 = query(7).add(&query(29));
    let v4 = query(8).add(&query(30));
    let gate_22 = <Fp>::sum_of_products(
        &[
            query(5),
            v3,
            v4,
            query(22),
            query(18),
            query(19),
            query(32),
            query(33),
        ],
        &[
            coefficients.linear_22[0],
            coefficients.linear_22[1],
            coefficients.linear_22[2],
            coefficients.linear_22[3],
            coefficients.linear_22[4],
            coefficients.linear_22[5],
            y_powers[4],
            y_powers[5],
        ],
    );
    // Programs 82–84: all of gate 23.
    let gate_23 = <Fp>::sum_of_products(
        &[
            query(20).add(&query(6)).sub(&query(22)),
            query(23).add(&query(7)).sub(&query(18)),
            query(24).sub(&query(19)),
        ],
        &[y_powers[6], y_powers[7], y_powers[8]],
    );
    row.add_product(&prepared_selectors[17], &gate_20);
    row.add_product(&prepared_selectors[19], &gate_22);
    row.add_product(&prepared_selectors[20], &gate_23);
}

/// Interpolation bodies 56 and 59 share their seven successive powers
/// locally. The tree reference deliberately retains its cloned power chains.
#[cfg(test)]
pub(crate) fn interpolation_body(
    program: usize,
    query: &mut impl FnMut(QueryKind, usize) -> Result<Fp, Error>,
) -> Result<Fp, Error> {
    let digit = match program {
        56 => query(QueryKind::Advice, 4)?.sub(&query(QueryKind::Advice, 14)?.mul(&constant(11))),
        59 => query(QueryKind::Advice, 4)?,
        _ => return Err(Error::InternalInvariant),
    };
    let mut powers = [<Fp>::ONE; 8];
    for i in 1..powers.len() {
        powers[i] = powers[i - 1].mul(&digit);
    }
    let mut coefficients = [<Fp>::ZERO; 8];
    coefficients[0] = query(QueryKind::Fixed, 0)?;
    for (coefficient, index) in coefficients[1..].iter_mut().zip(3..=9) {
        *coefficient = query(QueryKind::Fixed, index)?;
    }
    Ok(<Fp>::sum_of_products(&powers, &coefficients)
        .add(&constant(13))
        .sub(&query(QueryKind::Advice, 0)?))
}

/// Full-round Poseidon bodies 75..78: compute the S-boxes once, then apply
/// all three MDS rows. Callers group only rows active under all three gates.
#[cfg(test)]
pub(crate) fn poseidon_full_round_bodies(
    query: &mut impl FnMut(QueryKind, usize) -> Result<Fp, Error>,
) -> Result<[Fp; 3], Error> {
    let mut powers = [<Fp>::ZERO; 3];
    for (i, power) in powers.iter_mut().enumerate() {
        let base = query(QueryKind::Advice, 6 + i)?.add(&query(QueryKind::Fixed, 4 + i)?);
        *power = base.square().square().mul(&base);
    }
    let mut bodies = [<Fp>::ZERO; 3];
    for (i, output) in [22, 18, 19].into_iter().enumerate() {
        bodies[i] = <Fp>::sum_of_products(&powers, &POSEIDON_MDS[i])
            .sub(&query(QueryKind::Advice, output)?);
    }
    Ok(bodies)
}

/// Gate 25's two body programs — the largest gate family by active rows
/// (992 rows each) after the curve gate — with their frame: the current-row
/// advice queries `a₀, a₁, a₃, a₄`, the next-row queries of the same four
/// columns (`a₁₆, a₁₇, a₁₃, a₁₄`), and fixed query 10. Program 86's body is
/// `a₄² − ((a₁₆ + (a₃² − a₀ − a₁)) + a₀)` and program 87's is
/// `4·a₄·(a₀ − a₁₆) − (2·(a₃ + a₄)·(a₀ − (a₃² − a₀ − a₁)) + (2 − f·(f − 1))·
/// (a₁₃ + a₁₄)·(a₁₆ − (a₁₃² − a₁₆ − a₁₇)) + 2·f·(f − 1)·a₁₃)`, each in the
/// tree's exact association; both carry a fixed root factor, so the
/// sparse check evaluates them only on their active rows.
#[cfg(test)]
pub(crate) const GATE_25_PROGRAMS: [usize; 2] = [86, 87];
#[cfg(test)]
const GATE_25_ADVICE_QUERIES: [usize; 4] = [0, 1, 3, 4];
#[cfg(test)]
const GATE_25_NEXT_ADVICE_QUERIES: [usize; 4] = [16, 17, 13, 14];
#[cfg(test)]
const GATE_25_FIXED_QUERY: usize = 10;

/// Gate 25's bodies resolved to base-domain columns: `columns` are the four
/// advice columns (read at the row and the next row) and `fixed` the fixed
/// column of query 10.
#[cfg(test)]
#[derive(Clone, Copy)]
pub(crate) struct Gate25BodyKernel {
    program: usize,
    columns: [usize; 4],
    fixed: usize,
}

#[cfg(test)]
impl Gate25BodyKernel {
    /// The kernel for gate `expression`, or `None` when it is not a gate 25
    /// program or the frame does not resolve as expected. Retained as a
    /// differential reference for the compiled recipe bodies.
    pub(crate) fn resolve(target: &super::target::FixedTarget, expression: usize) -> Option<Self> {
        if !GATE_25_PROGRAMS.contains(&expression) {
            return None;
        }
        let queries = target.queries();
        let mut columns = [0; 4];
        for ((slot, &current), &next) in columns
            .iter_mut()
            .zip(&GATE_25_ADVICE_QUERIES)
            .zip(&GATE_25_NEXT_ADVICE_QUERIES)
        {
            let current = queries.advice().get(current)?;
            let next = queries.advice().get(next)?;
            if current.rotation != 0 || next.column != current.column || next.rotation != 1 {
                return None;
            }
            *slot = current.column;
        }
        let fixed = queries.fixed().get(GATE_25_FIXED_QUERY)?;
        if fixed.rotation != 0
            || target
                .fixed_values()
                .get(fixed.column)
                .is_none_or(|values| values.len() != super::target::N)
        {
            return None;
        }
        Some(Self {
            program: expression,
            columns,
            fixed: fixed.column,
        })
    }

    /// Whether `advice` has the four columns, each of `N` rows.
    pub(crate) fn accepts<A: AsRef<[Fp]>>(&self, advice: &[A]) -> bool {
        self.columns.iter().all(|&column| {
            advice
                .get(column)
                .is_some_and(|values| values.as_ref().len() == super::target::N)
        })
    }

    /// The body's value at `row`.
    #[inline]
    pub(crate) fn row<A: AsRef<[Fp]>>(&self, advice: &[A], fixed: &[[Fp; N]], row: usize) -> Fp {
        let next = super::evaluation::rotated_row(row, 1);
        let [c0, c1, c3, c4] = self.columns;
        let at = |column: usize, row: usize| advice[column].as_ref()[row];
        let (a0, a1, a3, a4) = (at(c0, row), at(c1, row), at(c3, row), at(c4, row));
        // The next-row queries: a₁₆ = a₀⁺, a₁₇ = a₁⁺, a₁₃ = a₃⁺, a₁₄ = a₄⁺.
        let (a16, a17, a13, a14) = (at(c0, next), at(c1, next), at(c3, next), at(c4, next));
        // `a₃² − a₀ − a₁`, as the bytecode forms it.
        let inner = a3.mul(&a3).sub(&a0).sub(&a1);
        match self.program {
            86 => a4.mul(&a4).sub(&a16.add(&inner).add(&a0)),
            _ => {
                let f = fixed[self.fixed][row];
                let t1 = a4.mul(&constant(2)).mul(&a0.sub(&a16));
                let q1 = a0.sub(&inner);
                let t2 = a3.add(&a4).mul(&q1).mul(&constant(0));
                let f_gate = f.mul(&f.sub(&constant(5)));
                let g = constant(0).sub(&f_gate);
                let q2 = a16.sub(&a13.mul(&a13).sub(&a16).sub(&a17));
                let t3 = a13.add(&a14).mul(&q2);
                let sum = t2.add(&g.mul(&t3)).add(&f_gate.mul(&constant(0)).mul(&a13));
                t1.sub(&sum)
            }
        }
    }
}

/// Components per Sinsemilla lookup input tuple.
pub(crate) const SINSEMILLA_INPUT_COMPONENTS: usize = 3;

/// The two lookups whose input side is the Sinsemilla family — `(lookup
/// index, first input program)` — and the frame of each: fixed queries
/// `(selector, run)`, the short-range advice query with its `+1` rotation
/// partner, the selected advice query, and the quadratic's `(b, d, p, q)`
/// advice queries. The programs are, in order, the short-range input
/// `f_s · (a − 2¹⁰ · (f_r − f_r · (f_r − 1)) · a⁺)`, the selected advice
/// `f_s · a_c + (1 − f_s) · K47`, and the selected quadratic
/// `f_s · (K7 · (a_b + a_d) · (2·a_p + a_q − a_b²) − a_b · (a_p − a_q)) +
/// (1 − f_s) · K48` — the same three components the extended-coset
/// compression kernels implement.
const SINSEMILLA_INPUT_LOOKUPS: [SinsemillaInputFrame; 2] = [
    SinsemillaInputFrame {
        lookup: 1,
        first_program: 195,
        selector_query: 16,
        run_query: 10,
        short_query: 2,
        short_next_query: 12,
        advice_query: 1,
        quadratic_queries: [3, 4, 0, 1],
    },
    SinsemillaInputFrame {
        lookup: 2,
        first_program: 201,
        selector_query: 17,
        run_query: 13,
        short_query: 7,
        short_next_query: 18,
        advice_query: 6,
        quadratic_queries: [8, 9, 5, 6],
    },
];

#[derive(Clone, Copy)]
struct SinsemillaInputFrame {
    lookup: usize,
    first_program: usize,
    selector_query: usize,
    run_query: usize,
    short_query: usize,
    short_next_query: usize,
    advice_query: usize,
    quadratic_queries: [usize; 4],
}

/// One Sinsemilla lookup's input family resolved to base-domain columns:
/// evaluates the three input components at a row directly, so preflight can
/// form the row's tuple, probe membership, and emit the feeds in one pass
/// without the flat evaluator. Columns are indices into the advice matrix and
/// the fixed values; every query is unrotated except the short-range
/// partner, which reads the next row.
#[derive(Clone, Copy)]
pub(crate) struct SinsemillaInputKernel {
    selector: usize,
    run: usize,
    short: usize,
    advice: usize,
    quadratic: [usize; 4],
}

impl SinsemillaInputKernel {
    /// The kernel for lookup `lookup_index`, or `None` when it is not a
    /// Sinsemilla input lookup or its queries do not resolve to the expected
    /// columns and rotations (the flat evaluator then evaluates the programs).
    pub(crate) fn resolve(
        target: &super::target::FixedTarget,
        lookup_index: usize,
    ) -> Option<Self> {
        let frame = SINSEMILLA_INPUT_LOOKUPS
            .iter()
            .find(|frame| frame.lookup == lookup_index)?;
        let lookup = target.lookups().get(lookup_index)?;
        if lookup.inputs().start != frame.first_program
            || lookup.inputs().len() != SINSEMILLA_INPUT_COMPONENTS
        {
            return None;
        }
        let queries = target.queries();
        let fixed = |query: usize| {
            let query = queries.fixed().get(query)?;
            (query.rotation == 0).then_some(query.column)
        };
        let advice = |query: usize| {
            let query = queries.advice().get(query)?;
            (query.rotation == 0).then_some(query.column)
        };
        let short = advice(frame.short_query)?;
        let short_next = queries.advice().get(frame.short_next_query)?;
        if short_next.column != short || short_next.rotation != 1 {
            return None;
        }
        let mut quadratic = [0; 4];
        for (slot, &query) in quadratic.iter_mut().zip(&frame.quadratic_queries) {
            *slot = advice(query)?;
        }
        let kernel = Self {
            selector: fixed(frame.selector_query)?,
            run: fixed(frame.run_query)?,
            short,
            advice: advice(frame.advice_query)?,
            quadratic,
        };
        let n = super::target::N;
        let column_ok = |columns: &[[Fp; N]], column: usize| {
            columns.get(column).is_some_and(|values| values.len() == n)
        };
        (column_ok(target.fixed_values(), kernel.selector)
            && column_ok(target.fixed_values(), kernel.run))
        .then_some(kernel)
    }

    /// Whether `advice` has the columns this kernel reads, each of `N` rows.
    pub(crate) fn accepts<A: AsRef<[Fp]>>(&self, advice: &[A]) -> bool {
        let n = super::target::N;
        [self.short, self.advice]
            .into_iter()
            .chain(self.quadratic)
            .all(|column| {
                advice
                    .get(column)
                    .is_some_and(|values| values.as_ref().len() == n)
            })
    }

    /// The three input components at `row`, in program order. `advice` must
    /// satisfy [`Self::accepts`] and `fixed` is the target's fixed values.
    #[inline]
    pub(crate) fn row<A: AsRef<[Fp]>>(
        &self,
        advice: &[A],
        fixed: &[[Fp; N]],
        row: usize,
    ) -> [Fp; SINSEMILLA_INPUT_COMPONENTS] {
        let next = super::evaluation::rotated_row(row, 1);
        let f_s = fixed[self.selector][row];
        let f_r = fixed[self.run][row];
        let one_minus_selector = <Fp>::ONE.sub(&f_s);

        let (a, a_next) = (
            advice[self.short].as_ref()[row],
            advice[self.short].as_ref()[next],
        );
        let run_gate = f_r.sub(&f_r.mul(&f_r.sub(&<Fp>::ONE)));
        let short = f_s.mul(&a.sub(&run_gate.mul(&a_next).mul(&constant(6))));

        let selected_advice = f_s
            .mul(&advice[self.advice].as_ref()[row])
            .add(&one_minus_selector.mul(&constant(47)));

        let [b, d, p, q] = self.quadratic;
        let (a_b, a_d, a_p, a_q) = (
            advice[b].as_ref()[row],
            advice[d].as_ref()[row],
            advice[p].as_ref()[row],
            advice[q].as_ref()[row],
        );
        let quadratic = a_p.add(&a_p).add(&a_q).sub(&a_b.square());
        let selected = constant(7)
            .mul(&a_b.add(&a_d).mul(&quadratic))
            .sub(&a_b.mul(&a_p.sub(&a_q)));
        let selected_quadratic = f_s
            .mul(&selected)
            .add(&one_minus_selector.mul(&constant(48)));

        [short, selected_advice, selected_quadratic]
    }
}

/// The range-check lookup's input program (lookup 0, program 193) and its
/// frame: fixed queries `(selector, run)` and the advice query with its `+1`
/// rotation partner. The program is the windowed range input
/// `f_s · (f_r · (a − 2¹⁰ · a⁺) + (1 − f_r) · a)`, the same component the
/// extended-coset compression kernel implements.
const RANGE_CHECK_INPUT_LOOKUP: usize = 0;
const RANGE_CHECK_INPUT_PROGRAM: usize = 193;
const RANGE_CHECK_SELECTOR_FIXED_QUERY: usize = 14;
const RANGE_CHECK_RUN_FIXED_QUERY: usize = 15;
const RANGE_CHECK_ADVICE_QUERY: usize = 9;
const RANGE_CHECK_NEXT_ADVICE_QUERY: usize = 10;

/// The range-check lookup's single input component resolved to base-domain
/// columns; see [`SinsemillaInputKernel`] for the fused preflight role.
#[derive(Clone, Copy)]
pub(crate) struct RangeCheckInputKernel {
    selector: usize,
    run: usize,
    column: usize,
}

impl RangeCheckInputKernel {
    /// The kernel for lookup `lookup_index`, or `None` when it is not the
    /// range-check lookup or its queries do not resolve as expected.
    pub(crate) fn resolve(
        target: &super::target::FixedTarget,
        lookup_index: usize,
    ) -> Option<Self> {
        if lookup_index != RANGE_CHECK_INPUT_LOOKUP {
            return None;
        }
        let lookup = target.lookups().get(lookup_index)?;
        if lookup.inputs().start != RANGE_CHECK_INPUT_PROGRAM || lookup.inputs().len() != 1 {
            return None;
        }
        let queries = target.queries();
        let fixed = |query: usize| {
            let query = queries.fixed().get(query)?;
            (query.rotation == 0).then_some(query.column)
        };
        let advice = queries.advice().get(RANGE_CHECK_ADVICE_QUERY)?;
        let next = queries.advice().get(RANGE_CHECK_NEXT_ADVICE_QUERY)?;
        if advice.rotation != 0 || next.column != advice.column || next.rotation != 1 {
            return None;
        }
        let kernel = Self {
            selector: fixed(RANGE_CHECK_SELECTOR_FIXED_QUERY)?,
            run: fixed(RANGE_CHECK_RUN_FIXED_QUERY)?,
            column: advice.column,
        };
        let n = super::target::N;
        let column_ok = |columns: &[[Fp; N]], column: usize| {
            columns.get(column).is_some_and(|values| values.len() == n)
        };
        (column_ok(target.fixed_values(), kernel.selector)
            && column_ok(target.fixed_values(), kernel.run))
        .then_some(kernel)
    }

    /// Whether `advice` has the column this kernel reads, of `N` rows.
    pub(crate) fn accepts<A: AsRef<[Fp]>>(&self, advice: &[A]) -> bool {
        advice
            .get(self.column)
            .is_some_and(|values| values.as_ref().len() == super::target::N)
    }

    /// The input component at `row`.
    #[inline]
    pub(crate) fn row<A: AsRef<[Fp]>>(&self, advice: &[A], fixed: &[[Fp; N]], row: usize) -> Fp {
        let next = super::evaluation::rotated_row(row, 1);
        let (f_s, f_r) = (fixed[self.selector][row], fixed[self.run][row]);
        let (a, a_next) = (
            advice[self.column].as_ref()[row],
            advice[self.column].as_ref()[next],
        );
        let windowed = a.sub(&a_next.mul(&constant(6)));
        f_s.mul(&f_r.mul(&windowed).add(&<Fp>::ONE.sub(&f_r).mul(&a)))
    }
}

/// Largest component count of any fused lookup input kernel.
pub(crate) const MAX_LOOKUP_INPUT_COMPONENTS: usize = SINSEMILLA_INPUT_COMPONENTS;

/// A lookup whose input side preflight evaluates and checks in one fused
/// pass: every circuit lookup has one, so no lookup input reaches the
/// flat evaluator in preflight.
#[derive(Clone, Copy)]
pub(crate) enum LookupInputKernel {
    Sinsemilla(SinsemillaInputKernel),
    RangeCheck(RangeCheckInputKernel),
}

impl LookupInputKernel {
    /// The fused kernel for `lookup_index`, if its input side is one of the
    /// pinned families and resolves against the query tables.
    pub(crate) fn resolve(
        target: &super::target::FixedTarget,
        lookup_index: usize,
    ) -> Option<Self> {
        SinsemillaInputKernel::resolve(target, lookup_index)
            .map(Self::Sinsemilla)
            .or_else(|| RangeCheckInputKernel::resolve(target, lookup_index).map(Self::RangeCheck))
    }

    /// Input components per row (the lookup's tuple arity).
    pub(crate) fn components(&self) -> usize {
        match self {
            Self::Sinsemilla(_) => SINSEMILLA_INPUT_COMPONENTS,
            Self::RangeCheck(_) => 1,
        }
    }

    /// Whether `advice` has every column the kernel reads, of `N` rows.
    pub(crate) fn accepts<A: AsRef<[Fp]>>(&self, advice: &[A]) -> bool {
        match self {
            Self::Sinsemilla(kernel) => kernel.accepts(advice),
            Self::RangeCheck(kernel) => kernel.accepts(advice),
        }
    }

    /// Writes the row's tuple into `out[..components()]` and returns it.
    #[inline]
    pub(crate) fn row<'a, A: AsRef<[Fp]>>(
        &self,
        advice: &[A],
        fixed: &[[Fp; N]],
        row: usize,
        out: &'a mut [Fp; MAX_LOOKUP_INPUT_COMPONENTS],
    ) -> &'a [Fp] {
        match self {
            Self::Sinsemilla(kernel) => {
                *out = kernel.row(advice, fixed, row);
                &out[..]
            }
            Self::RangeCheck(kernel) => {
                out[0] = kernel.row(advice, fixed, row);
                &out[..1]
            }
        }
    }
}

#[cfg(test)]
mod reference;
#[cfg(test)]
use reference::TREES;
#[cfg(test)]
pub(crate) use reference::{ProgramTrees, evaluate, program_trees};

#[cfg(test)]
mod tests;
