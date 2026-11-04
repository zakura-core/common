//! Fixed affine maps transposed onto the proof's constraint weights.
//!
//! Each sparse row retains only query coefficients that can be nonzero.
//! The virtual query 49 supplies the sum of Action weights for constants.
//! Construction-only key 50 denotes q6 - q7; it never indexes the query frame.

use super::{Fp, GATE_CONSTRAINT_COUNT, GATE_QUERY_COUNT, TWO_POW_130, constant};
use udon::field::Reduced;

const DIFFERENCE: usize = 50;

struct Linear<const N: usize> {
    weights: [Fp; N],
}

struct ReducedLinear<const N: usize> {
    weights: [Fp<Reduced>; N],
}
impl<const N: usize> ReducedLinear<N> {
    fn new(sources: [usize; N], constraints: &[(Fp, &[(usize, Fp)])]) -> Self {
        Self::from_loose(Linear::new(sources, constraints).weights)
    }
    fn from_loose(weights: [Fp; N]) -> Self {
        const { assert!(N == 2 || N == 3) };
        Self {
            weights: weights.map(Fp::reduce),
        }
    }
    #[inline(always)]
    fn evaluate(&self, values: [Fp; N]) -> Fp {
        Fp::sum_of_products(&values, &self.weights)
    }
}
impl<const N: usize> Linear<N> {
    fn new(sources: [usize; N], constraints: &[(Fp, &[(usize, Fp)])]) -> Self {
        let mut weights = [Fp::ZERO; N];
        for (power, terms) in constraints {
            for (query, coefficient) in *terms {
                let index = sources.iter().position(|source| source == query).unwrap();
                weights[index] = power.mul_add(coefficient, &weights[index]);
            }
        }
        Self { weights }
    }
    #[inline(always)]
    fn evaluate(&self, values: [Fp; N]) -> Fp {
        Fp::sum_of_products(&values, &self.weights)
    }
}

pub(super) struct Coefficients {
    gate_14: Linear<5>,
    gate_27: Linear<10>,
    gate_31: Linear<10>,
    gate_32: Linear<14>,
    gate_33: Linear<4>,
    gate_34: Linear<4>,
    gate_35: ReducedLinear<2>,
    gate_36: ReducedLinear<3>,
    gate_37: ReducedLinear<2>,
    gate_38: Linear<6>,
    gates_39_41: Linear<6>,
    gate_40: Linear<4>,
    gate_42: Linear<7>,
    gate_43: Linear<9>,
}
impl Coefficients {
    pub(super) fn new(p: &[Fp; GATE_CONSTRAINT_COUNT]) -> Self {
        Self {
            gate_14: Linear::new(
                [7, 8, 20, 23, 49],
                &[
                    (
                        p[47],
                        &[(8, Fp::ONE), (7, <Fp>::ONE.neg()), (23, TWO_POW_130.neg())],
                    ),
                    (
                        p[48],
                        &[
                            (20, Fp::ONE),
                            (7, <Fp>::ONE.neg()),
                            (49, constant(10).neg()),
                        ],
                    ),
                ],
            ),
            gate_27: Linear::new(
                [0, 1, 2, 3, 4, 12, 13, 14, 16, 17],
                &[
                    (
                        p[91],
                        &[(0, Fp::ONE), (16, constant(6).neg()), (14, <Fp>::ONE.neg())],
                    ),
                    (
                        p[92],
                        &[
                            (16, Fp::ONE),
                            (1, constant(36)),
                            (17, constant(6).mul(&constant(36)).neg()),
                            (12, constant(6).mul(&constant(36))),
                            (3, <Fp>::ONE.neg()),
                        ],
                    ),
                    (
                        p[93],
                        &[(13, Fp::ONE), (2, constant(37)), (4, <Fp>::ONE.neg())],
                    ),
                    (
                        p[94],
                        &[
                            (17, Fp::ONE),
                            (12, <Fp>::ONE.neg()),
                            (13, constant(37).neg()),
                        ],
                    ),
                ],
            ),
            gate_31: Linear::new(
                [5, 6, 7, 8, 9, 10, 15, 18, 19, 22],
                &[
                    (
                        p[101],
                        &[(5, Fp::ONE), (15, constant(6).neg()), (10, <Fp>::ONE.neg())],
                    ),
                    (
                        p[102],
                        &[
                            (15, Fp::ONE),
                            (6, constant(36)),
                            (22, constant(6).mul(&constant(36)).neg()),
                            (18, constant(6).mul(&constant(36))),
                            (8, <Fp>::ONE.neg()),
                        ],
                    ),
                    (
                        p[103],
                        &[(19, Fp::ONE), (7, constant(37)), (9, <Fp>::ONE.neg())],
                    ),
                    (
                        p[104],
                        &[
                            (22, Fp::ONE),
                            (18, <Fp>::ONE.neg()),
                            (19, constant(37).neg()),
                        ],
                    ),
                ],
            ),
            gate_32: Linear::new(
                [0, 1, 2, 3, 4, 5, 7, 12, 13, 14, 16, 17, 18, 49],
                &[
                    (
                        p[107],
                        &[
                            (2, Fp::ONE),
                            (3, <Fp>::ONE.neg()),
                            (4, constant(38).neg()),
                            (5, constant(37).neg()),
                        ],
                    ),
                    (
                        p[108],
                        &[
                            (12, Fp::ONE),
                            (13, <Fp>::ONE.neg()),
                            (14, constant(39).neg()),
                        ],
                    ),
                    (
                        p[109],
                        &[
                            (1, Fp::ONE),
                            (3, constant(40)),
                            (4, constant(41)),
                            (0, <Fp>::ONE.neg()),
                        ],
                    ),
                    (
                        p[110],
                        &[
                            (5, Fp::ONE),
                            (17, constant(37)),
                            (13, constant(42)),
                            (14, constant(41)),
                            (16, <Fp>::ONE.neg()),
                        ],
                    ),
                    (
                        p[113],
                        &[
                            (1, Fp::ONE),
                            (7, <Fp>::ONE.neg()),
                            (49, constant(16).sub(&constant(17))),
                        ],
                    ),
                    (
                        p[117],
                        &[
                            (5, Fp::ONE),
                            (17, constant(37)),
                            (18, <Fp>::ONE.neg()),
                            (49, constant(43).sub(&constant(17))),
                        ],
                    ),
                ],
            ),
            gate_33: Linear::new(
                [DIFFERENCE, 8, 18, 19],
                &[(
                    p[158],
                    &[
                        (DIFFERENCE, Fp::ONE),
                        (8, constant(38).neg()),
                        (18, constant(37).neg()),
                        (19, constant(9).neg()),
                    ],
                )],
            ),
            gate_34: Linear::new(
                [DIFFERENCE, 8, 18, 19],
                &[(
                    p[161],
                    &[
                        (DIFFERENCE, Fp::ONE),
                        (8, constant(0).neg()),
                        (18, constant(2).neg()),
                        (19, constant(6).neg()),
                    ],
                )],
            ),
            gate_35: ReducedLinear::new(
                [DIFFERENCE, 8],
                &[(p[162], &[(DIFFERENCE, Fp::ONE), (8, constant(9).neg())])],
            ),
            gate_36: ReducedLinear::new(
                [DIFFERENCE, 18, 22],
                &[(
                    p[164],
                    &[
                        (DIFFERENCE, Fp::ONE),
                        (22, constant(0).neg()),
                        (18, constant(6).neg()),
                    ],
                )],
            ),
            gate_37: ReducedLinear::new(
                [DIFFERENCE, 8],
                &[(p[166], &[(DIFFERENCE, Fp::ONE), (8, constant(37).neg())])],
            ),
            gate_38: Linear::new(
                [6, 7, 8, 18, 19, 49],
                &[
                    (
                        p[167],
                        &[
                            (8, Fp::ONE),
                            (7, constant(40)),
                            (18, constant(41)),
                            (6, <Fp>::ONE.neg()),
                        ],
                    ),
                    (
                        p[168],
                        &[
                            (8, Fp::ONE),
                            (49, constant(16).sub(&constant(17))),
                            (19, <Fp>::ONE.neg()),
                        ],
                    ),
                ],
            ),
            gates_39_41: Linear::new(
                [6, 7, 8, 18, 19, 49],
                &[
                    (
                        p[177],
                        &[
                            (7, Fp::ONE),
                            (8, constant(38)),
                            (18, constant(41)),
                            (6, <Fp>::ONE.neg()),
                        ],
                    ),
                    (
                        p[178],
                        &[
                            (7, Fp::ONE),
                            (8, constant(38)),
                            (49, constant(43).sub(&constant(17))),
                            (19, <Fp>::ONE.neg()),
                        ],
                    ),
                ],
            ),
            gate_40: Linear::new(
                [6, 7, 8, 9],
                &[(
                    Fp::ONE,
                    &[
                        (7, Fp::ONE),
                        (8, constant(44)),
                        (9, constant(45)),
                        (6, <Fp>::ONE.neg()),
                    ],
                )],
            ),
            gate_42: Linear::new(
                [6, 7, 8, 18, 19, 22, 49],
                &[
                    (
                        p[181],
                        &[
                            (7, Fp::ONE),
                            (8, constant(39)),
                            (22, constant(46)),
                            (18, constant(41)),
                            (6, <Fp>::ONE.neg()),
                        ],
                    ),
                    (
                        p[182],
                        &[
                            (7, Fp::ONE),
                            (8, constant(39)),
                            (49, constant(16).sub(&constant(17))),
                            (19, <Fp>::ONE.neg()),
                        ],
                    ),
                ],
            ),
            gate_43: Linear::new(
                [5, 6, 7, 8, 9, 15, 19, 22, 49],
                &[
                    (
                        p[187],
                        &[
                            (15, Fp::ONE),
                            (6, <Fp>::ONE.neg()),
                            (7, constant(0).neg()),
                            (22, constant(6).neg()),
                        ],
                    ),
                    (
                        p[188],
                        &[
                            (5, Fp::ONE),
                            (15, <Fp>::ONE.neg()),
                            (8, constant(40).neg()),
                            (9, constant(41).neg()),
                        ],
                    ),
                    (
                        p[189],
                        &[
                            (15, Fp::ONE),
                            (49, constant(16).sub(&constant(17))),
                            (19, <Fp>::ONE.neg()),
                        ],
                    ),
                ],
            ),
        }
    }
    #[inline(always)]
    pub(super) fn gate_14(&self, q: &[Fp; GATE_QUERY_COUNT], weight_sum: &Fp) -> Fp {
        self.gate_14
            .evaluate([q[7], q[8], q[20], q[23], *weight_sum])
    }
    #[inline(always)]
    pub(super) fn gate_27(&self, q: &[Fp; GATE_QUERY_COUNT], _weight_sum: &Fp) -> Fp {
        self.gate_27.evaluate([
            q[0], q[1], q[2], q[3], q[4], q[12], q[13], q[14], q[16], q[17],
        ])
    }
    #[inline(always)]
    pub(super) fn gate_31(&self, q: &[Fp; GATE_QUERY_COUNT], _weight_sum: &Fp) -> Fp {
        self.gate_31.evaluate([
            q[5], q[6], q[7], q[8], q[9], q[10], q[15], q[18], q[19], q[22],
        ])
    }
    #[inline(always)]
    pub(super) fn gate_32(&self, q: &[Fp; GATE_QUERY_COUNT], weight_sum: &Fp) -> Fp {
        self.gate_32.evaluate([
            q[0],
            q[1],
            q[2],
            q[3],
            q[4],
            q[5],
            q[7],
            q[12],
            q[13],
            q[14],
            q[16],
            q[17],
            q[18],
            *weight_sum,
        ])
    }
    #[inline(always)]
    pub(super) fn gate_33(&self, q: &[Fp; GATE_QUERY_COUNT], difference: &Fp) -> Fp {
        self.gate_33.evaluate([*difference, q[8], q[18], q[19]])
    }
    #[inline(always)]
    pub(super) fn gate_34(&self, q: &[Fp; GATE_QUERY_COUNT], difference: &Fp) -> Fp {
        self.gate_34.evaluate([*difference, q[8], q[18], q[19]])
    }
    #[inline(always)]
    pub(super) fn gate_35(&self, q: &[Fp; GATE_QUERY_COUNT], difference: &Fp) -> Fp {
        self.gate_35.evaluate([*difference, q[8]])
    }
    #[inline(always)]
    pub(super) fn gate_36(&self, q: &[Fp; GATE_QUERY_COUNT], difference: &Fp) -> Fp {
        self.gate_36.evaluate([*difference, q[18], q[22]])
    }
    #[inline(always)]
    pub(super) fn gate_37(&self, q: &[Fp; GATE_QUERY_COUNT], difference: &Fp) -> Fp {
        self.gate_37.evaluate([*difference, q[8]])
    }
    #[inline(always)]
    pub(super) fn gate_38(&self, q: &[Fp; GATE_QUERY_COUNT], weight_sum: &Fp) -> Fp {
        self.gate_38
            .evaluate([q[6], q[7], q[8], q[18], q[19], *weight_sum])
    }
    #[inline(always)]
    pub(super) fn gates_39_41(&self, q: &[Fp; GATE_QUERY_COUNT], weight_sum: &Fp) -> Fp {
        self.gates_39_41
            .evaluate([q[6], q[7], q[8], q[18], q[19], *weight_sum])
    }
    #[inline(always)]
    pub(super) fn gate_40(&self, q: &[Fp; GATE_QUERY_COUNT], _weight_sum: &Fp) -> Fp {
        self.gate_40.evaluate([q[6], q[7], q[8], q[9]])
    }
    #[inline(always)]
    pub(super) fn gate_42(&self, q: &[Fp; GATE_QUERY_COUNT], weight_sum: &Fp) -> Fp {
        self.gate_42
            .evaluate([q[6], q[7], q[8], q[18], q[19], q[22], *weight_sum])
    }
    #[inline(always)]
    pub(super) fn gate_43(&self, q: &[Fp; GATE_QUERY_COUNT], weight_sum: &Fp) -> Fp {
        self.gate_43.evaluate([
            q[5],
            q[6],
            q[7],
            q[8],
            q[9],
            q[15],
            q[19],
            q[22],
            *weight_sum,
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use udon::field::{PallasBase, PrimeModulus};

    fn sample(state: &mut u64, upper: bool) -> Fp {
        let mut limbs = core::array::from_fn(|_| {
            *state ^= *state << 13;
            *state ^= *state >> 7;
            *state ^= *state << 17;
            *state
        });
        limbs[3] &= 0x3fff_ffff_ffff_ffff;
        if upper {
            let mut carry = 0u128;
            for (limb, modulus) in limbs.iter_mut().zip(PallasBase::MODULUS) {
                let sum = u128::from(*limb) + u128::from(modulus) + carry;
                *limb = sum as u64;
                carry = sum >> 64;
            }
            assert_eq!(carry, 0);
        }
        Fp::from_montgomery_limbs(limbs)
    }

    #[test]
    fn compressed_maps_match_original_constraints_and_layout() {
        assert_eq!(size_of::<Coefficients>(), 86 * size_of::<Fp>());
        assert_eq!(91 * size_of::<Fp>() - size_of::<Coefficients>(), 160);
        assert_eq!(align_of::<Coefficients>(), align_of::<Fp>());
        assert_eq!(size_of::<ReducedLinear<2>>(), 2 * size_of::<Fp>());
        assert_eq!(size_of::<ReducedLinear<3>>(), 3 * size_of::<Fp>());
        let mut maximum = PallasBase::MODULUS;
        let mut carry = 0;
        for limb in &mut maximum {
            let next = *limb >> 63;
            *limb = (*limb << 1) | carry;
            carry = next;
        }
        assert_eq!(carry, 0);
        for limb in &mut maximum {
            let (value, borrow) = limb.overflowing_sub(1);
            *limb = value;
            if !borrow {
                break;
            }
        }
        let edges = [
            <Fp>::ZERO,
            <Fp>::ONE,
            <Fp>::ONE.neg(),
            Fp::from_montgomery_limbs(PallasBase::MODULUS),
            Fp::from_montgomery_limbs(maximum),
        ];
        let mut state = 0x693a_41d5_8f20_9b77;
        for case in 0..80 {
            let mut q: [Fp; GATE_QUERY_COUNT] = core::array::from_fn(|i| {
                if case < edges.len() {
                    edges[(case + i) % edges.len()]
                } else {
                    sample(&mut state, (case + i) % 2 == 0)
                }
            });
            if case % 7 == 0 {
                q[7] = q[6];
            }
            if case % 11 == 0 {
                for slot in [8, 18, 19, 22] {
                    q[slot] = Fp::ZERO;
                }
            }
            for mode in 0..4 {
                let powers = core::array::from_fn(|_| match mode {
                    0 => Fp::ZERO,
                    1 => Fp::ONE,
                    2 => <Fp>::ONE.neg(),
                    _ => sample(&mut state, case % 2 == 0),
                });
                let coefficients = Coefficients::new(&powers);
                let difference = q[6].sub(&q[7]);
                let actual = [
                    coefficients.gate_33(&q, &difference),
                    coefficients.gate_34(&q, &difference),
                    coefficients.gate_35(&q, &difference),
                    coefficients.gate_36(&q, &difference),
                    coefficients.gate_37(&q, &difference),
                ];
                // The original Loose maps retain separate q6/q7 terms and
                // original trailing operand order; they never use key50.
                let original = [
                    Linear::new(
                        [6, 7, 8, 18, 19],
                        &[(
                            powers[158],
                            &[
                                (6, Fp::ONE),
                                (7, <Fp>::ONE.neg()),
                                (8, constant(38).neg()),
                                (18, constant(37).neg()),
                                (19, constant(9).neg()),
                            ],
                        )],
                    )
                    .evaluate([q[6], q[7], q[8], q[18], q[19]]),
                    Linear::new(
                        [6, 7, 8, 18, 19],
                        &[(
                            powers[161],
                            &[
                                (6, Fp::ONE),
                                (7, <Fp>::ONE.neg()),
                                (8, constant(0).neg()),
                                (18, constant(2).neg()),
                                (19, constant(6).neg()),
                            ],
                        )],
                    )
                    .evaluate([q[6], q[7], q[8], q[18], q[19]]),
                    Linear::new(
                        [6, 7, 8],
                        &[(
                            powers[162],
                            &[(6, Fp::ONE), (7, <Fp>::ONE.neg()), (8, constant(9).neg())],
                        )],
                    )
                    .evaluate([q[6], q[7], q[8]]),
                    Linear::new(
                        [6, 7, 18, 22],
                        &[(
                            powers[164],
                            &[
                                (6, Fp::ONE),
                                (7, <Fp>::ONE.neg()),
                                (22, constant(0).neg()),
                                (18, constant(6).neg()),
                            ],
                        )],
                    )
                    .evaluate([q[6], q[7], q[18], q[22]]),
                    Linear::new(
                        [6, 7, 8],
                        &[(
                            powers[166],
                            &[(6, Fp::ONE), (7, <Fp>::ONE.neg()), (8, constant(37).neg())],
                        )],
                    )
                    .evaluate([q[6], q[7], q[8]]),
                ];
                let explicit = [
                    q[6].sub(&q[7])
                        .sub(&q[8].mul(&<Fp>::from_u64(16)))
                        .sub(&q[18].mul(&<Fp>::from_u64(32)))
                        .sub(&q[19].mul(&<Fp>::from_u64(64)))
                        .mul(&powers[158]),
                    q[6].sub(&q[7])
                        .sub(&q[8].double())
                        .sub(&q[18].mul(&<Fp>::from_u64(4)))
                        .sub(&q[19].mul(&<Fp>::from_u64(1024)))
                        .mul(&powers[161]),
                    q[6].sub(&q[7])
                        .sub(&q[8].mul(&<Fp>::from_u64(64)))
                        .mul(&powers[162]),
                    q[6].sub(&q[7])
                        .sub(&q[22].double())
                        .sub(&q[18].mul(&<Fp>::from_u64(1024)))
                        .mul(&powers[164]),
                    q[6].sub(&q[7])
                        .sub(&q[8].mul(&<Fp>::from_u64(32)))
                        .mul(&powers[166]),
                ];
                assert_eq!(actual.map(Fp::reduce), original.map(Fp::reduce));
                assert_eq!(actual.map(Fp::reduce), explicit.map(Fp::reduce));
            }
        }
    }
}
