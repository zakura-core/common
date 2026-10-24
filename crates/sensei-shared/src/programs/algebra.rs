//! Arithmetic traits and shared recipe combinators.

use super::{ONE_INDEX, T_P_INDEX, TWO_POW_130_INDEX, TWO_POW_140_INDEX};

/// Arithmetic operations whose tree structure and field implementation differ.
///
/// Constant indices must be in `0..CONSTANT_COUNT`
/// ([`crate::expressions::CONSTANT_COUNT`]). The [`Fp`](udon::field::Fp)
/// implementation panics on out-of-range pool reads;
/// [`Expression`](crate::expressions::Expression) stores indices without
/// checking them, leaving validation to expression consumers.
pub trait Value: Clone {
    /// Reads a field constant by its shared pool index in `0..CONSTANT_COUNT`.
    fn constant(index: u8) -> Self;
    /// Forms an ordered sum.
    fn add(self, rhs: Self) -> Self;
    /// Forms an ordered product.
    fn mul(self, rhs: Self) -> Self;
    /// Negates this value.
    fn neg(self) -> Self;
    /// Scales by a shared pool constant with `index` in `0..CONSTANT_COUNT`.
    fn multiply_constant(self, index: u8) -> Self;

    /// Subtracts the right operand.
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        self.add(rhs.neg())
    }
    /// Squares this value.
    #[inline(always)]
    fn square(self) -> Self {
        self.clone().mul(self)
    }
    /// Forms one matrix row using three consecutive pool coefficients.
    /// `coefficient`, `coefficient + 1`, and `coefficient + 2` must all be valid
    /// pool indices as described by [`Value`].
    #[inline(always)]
    fn mix([x, y, z]: [Self; 3], coefficient: u8) -> Self {
        x.multiply_constant(coefficient)
            .add(y.multiply_constant(coefficient + 1))
            .add(z.multiply_constant(coefficient + 2))
    }
}

/// Query leaves and recipe combinators. `gated` is lazy in its fixed factor
/// so the sparse row algebra does not read or evaluate that factor at all.
///
/// Query arguments to these helpers must be valid slots in the corresponding
/// fixed or advice query table (see the [module documentation](crate::programs)).
/// Constant arguments follow [`Value`]'s pool-index contract. These bounds
/// are caller preconditions: tree construction retains unchecked indices,
/// while field evaluation can panic when reading them.
pub trait Algebra {
    /// The value represented by this algebra.
    type Value: Value;
    /// Reads a slot in `0..FIXED_QUERIES.len()`
    /// ([`crate::queries::FIXED_QUERIES`]), resolving its column and rotation.
    fn fixed(&self, index: u8) -> Self::Value;
    /// Reads a slot in `0..ADVICE_QUERIES.len()`
    /// ([`crate::queries::ADVICE_QUERIES`]), resolving its column and rotation.
    fn advice(&self, index: u8) -> Self::Value;
    /// Applies a lazy fixed factor to a constraint body.
    ///
    /// Tree construction and full field evaluation multiply `factor()` by
    /// `body`. Sparse preflight returns `body` without calling `factor`, and
    /// must check it only on the prepared rows where that fixed factor is
    /// nonzero. There, the body and product have equivalent zero tests; their
    /// field values need not be equal. Rows with a zero factor already satisfy
    /// the full constraint and are skipped by sparse preflight.
    fn gated(&self, factor: impl FnOnce() -> Self::Value, body: Self::Value) -> Self::Value;

    /// Reads a field constant by its shared pool index in `0..CONSTANT_COUNT`,
    /// following [`Value::constant`].
    #[inline(always)]
    fn constant(&self, index: u8) -> Self::Value {
        Self::Value::constant(index)
    }

    // Subtraction is an ADD of a NEG; do not cancel nested negations.
    /// Subtracts two values in this algebra.
    #[inline(always)]
    fn sub(&self, left: Self::Value, right: Self::Value) -> Self::Value {
        left.sub(right)
    }

    /// Squares this value.
    #[inline(always)]
    fn square(&self, x: Self::Value) -> Self::Value {
        x.square()
    }

    // The original addition chain is ((x * x) * (x * x)) * x.
    /// Raises a value to the fifth power using the source addition chain.
    #[inline(always)]
    fn pow5(&self, x: Self::Value) -> Self::Value {
        self.square(self.square(x.clone())).mul(x)
    }

    // Fold left, retaining the leading x and the order of all (c - x) factors.
    /// Multiplies a value by the ordered constant-minus-value factors.
    /// Each element of `roots` is a pool index in `0..CONSTANT_COUNT`; the
    /// leading factor is `x` itself.
    #[inline(always)]
    fn vanishing(&self, x: Self::Value, roots: &[u8]) -> Self::Value {
        roots.iter().fold(x.clone(), |product, &index| {
            product.mul(self.sub(self.constant(index), x.clone()))
        })
    }

    /// Builds a fixed-query selector with the given pool-index roots.
    /// `query` is a [`Self::fixed`] slot; `roots` follows [`Self::vanishing`].
    #[inline(always)]
    fn selector(&self, query: u8, roots: &[u8]) -> Self::Value {
        self.vanishing(self.fixed(query), roots)
    }

    /// Builds the Boolean constraint on a value.
    #[inline(always)]
    fn boolean(&self, x: Self::Value) -> Self::Value {
        self.vanishing(x, &[5])
    }

    /// Selects between two values using a Boolean value.
    #[inline(always)]
    fn select(&self, bit: Self::Value, yes: Self::Value, no: Self::Value) -> Self::Value {
        bit.clone()
            .mul(yes)
            .add(self.sub(self.constant(ONE_INDEX), bit).mul(no))
    }

    /// Extracts a radix digit from two advice queries.
    /// `current` and `next` are [`Self::advice`] slots; `radix` is a constant
    /// pool index in `0..CONSTANT_COUNT`, not a literal radix. For example,
    /// index 6 supplies radix 1024.
    #[inline(always)]
    fn digit(&self, current: u8, next: u8, radix: u8) -> Self::Value {
        self.sub(
            self.advice(current),
            self.advice(next).multiply_constant(radix),
        )
    }

    // An unscaled leading advice query followed by scaled advice queries.
    /// Forms a linear combination with an unscaled leading query.
    /// `first` and each term's first element are [`Self::advice`] slots;
    /// each term's second element is a pool index in `0..CONSTANT_COUNT`.
    #[inline(always)]
    fn linear(&self, first: u8, terms: &[(u8, u8)]) -> Self::Value {
        terms
            .iter()
            .fold(self.advice(first), |sum, &(query, coefficient)| {
                sum.add(self.advice(query).multiply_constant(coefficient))
            })
    }

    /// Builds the curve equation for two advice queries.
    #[inline(always)]
    fn on_curve(&self, x: u8, y: u8) -> Self::Value {
        self.sub(
            self.sub(
                self.square(self.advice(y)),
                self.square(self.advice(x)).mul(self.advice(x)),
            ),
            self.constant(3),
        )
    }

    // x-coordinate of a secant sum, and the repeated (s + t) * (x - x_sum).
    /// Builds the x-coordinate expression for a secant addition.
    #[inline(always)]
    fn secant_x(&self, slope: u8, x: u8, other_x: u8) -> Self::Value {
        self.sub(
            self.sub(self.square(self.advice(slope)), self.advice(x)),
            self.advice(other_x),
        )
    }

    /// Builds the repeated slope product in incomplete addition.
    #[inline(always)]
    fn slope_product(&self, s: u8, t: u8, x: u8, other_x: u8) -> Self::Value {
        self.advice(s)
            .add(self.advice(t))
            .mul(self.sub(self.advice(x), self.secant_x(s, x, other_x)))
    }

    // Fixed-column interpolation at a three-bit digit. Retain the leading
    // one in every power and the zero at the head of the sum.
    /// Evaluates fixed-column interpolation at a digit.
    #[inline(always)]
    fn interpolate_x(&self, x: Self::Value) -> Self::Value {
        let mut power = self.constant(ONE_INDEX);
        let mut sum = self.constant(13).add(power.clone().mul(self.fixed(0)));
        for query in 3..=9 {
            power = power.mul(x.clone());
            sum = sum.add(power.clone().mul(self.fixed(query)));
        }
        self.sub(sum, self.advice(0))
    }

    // Four constraints shared by the variable-base addition steps. The two
    // slopes are consecutive secants, and bit selects the sign of advice(1).
    // Lazy inputs avoid computing values used only by sibling constraints.
    /// Builds one of the four incomplete-addition constraints.
    /// `index` selects a constraint in `0..4`; `s`, `t`, `x`, and `next_x` are
    /// [`Self::advice`] slots. The closures are called only by the selected body.
    ///
    /// # Panics
    ///
    /// Panics if `index >= 4`.
    #[inline(always)]
    fn incomplete_addition(
        &self,
        index: usize,
        [s, t, x, next_x]: [u8; 4],
        bit: impl FnOnce() -> Self::Value,
        next_y: impl FnOnce() -> Self::Value,
    ) -> Self::Value {
        let y = || self.slope_product(s, t, x, 0).multiply_constant(7);
        match index {
            0 => self.boolean(bit()),
            1 => self
                .sub(
                    self.advice(s).mul(self.sub(self.advice(x), self.advice(0))),
                    y(),
                )
                .add(
                    self.sub(bit().multiply_constant(0), self.constant(ONE_INDEX))
                        .mul(self.advice(1)),
                ),
            2 => self.sub(
                self.sub(
                    self.sub(self.square(self.advice(t)), self.advice(next_x)),
                    self.secant_x(s, x, 0),
                ),
                self.advice(x),
            ),
            3 => self.sub(
                self.sub(
                    self.advice(t)
                        .mul(self.sub(self.advice(x), self.advice(next_x))),
                    y(),
                ),
                next_y(),
            ),
            _ => unreachable!(),
        }
    }

    // One three-wide matrix row, with consecutive pool coefficients. Keep the
    // first term scaled and the sums left-associated (no leading zero).
    /// Forms one matrix row using three consecutive pool coefficients.
    /// All three indices starting at `coefficient` must be valid pool indices;
    /// see [`Value::mix`].
    #[inline(always)]
    fn mix(&self, values: [Self::Value; 3], coefficient: u8) -> Self::Value {
        Self::Value::mix(values, coefficient)
    }

    /// Builds the three full-round S-box outputs.
    #[inline(always)]
    fn poseidon_state(&self) -> [Self::Value; 3] {
        [
            self.pow5(self.advice(6).add(self.fixed(4))),
            self.pow5(self.advice(7).add(self.fixed(5))),
            self.pow5(self.advice(8).add(self.fixed(6))),
        ]
    }

    /// Builds one full-round Poseidon constraint.
    /// `row` selects a matrix row in `0..3`.
    ///
    /// # Panics
    ///
    /// Panics if `row >= 3`.
    #[inline(always)]
    fn poseidon_full_round_body(&self, row: u8) -> Self::Value {
        self.sub(
            self.mix(self.poseidon_state(), 18 + 3 * row),
            self.advice([22, 18, 19][usize::from(row)]),
        )
    }

    /// Share the three S-boxes across the jointly scheduled full-round gates.
    /// Builds three full-round constraints with shared S-box outputs.
    #[inline(always)]
    fn poseidon_full_round_bodies(&self) -> [Self::Value; 3] {
        let state = self.poseidon_state();
        core::array::from_fn(|row| {
            self.sub(
                self.mix(state.clone(), 18 + 3 * row as u8),
                self.advice([22, 18, 19][row]),
            )
        })
    }

    /// Builds one range-check constraint.
    /// `index` selects one of this helper's 37 constraints in `0..37`.
    ///
    /// # Panics
    ///
    /// Panics if `index >= 37`.
    #[inline(always)]
    fn range_body(&self, index: usize) -> Self::Value {
        match index {
            0 => self.boolean(self.advice(8)),
            1 => self.boolean(self.advice(18)),
            2 => self.sub(
                self.advice(6),
                self.linear(7, &[(8, 38), (18, 37), (19, 9)]),
            ),
            3 => self.boolean(self.advice(7)),
            4 => self.boolean(self.advice(8)),
            5 => self.sub(self.advice(6), self.linear(7, &[(8, 0), (18, 2), (19, 6)])),
            6 => self.sub(self.advice(6), self.linear(7, &[(8, 9)])),
            7 => self.boolean(self.advice(7)),
            8 => self.sub(self.advice(6), self.linear(7, &[(22, 0), (18, 6)])),
            9 => self.boolean(self.advice(8)),
            10 => self.sub(self.advice(6), self.linear(7, &[(8, 37)])),
            11 => self.sub(self.linear(8, &[(7, 40), (18, 41)]), self.advice(6)),
            12 => self.sub(
                self.sub(
                    self.advice(8).add(self.constant(TWO_POW_130_INDEX)),
                    self.constant(T_P_INDEX),
                ),
                self.advice(19),
            ),
            13 => self.advice(18).mul(self.advice(7)),
            14 => self.advice(18).mul(self.advice(9)),
            15 => self.advice(18).mul(self.advice(10)),
            16 => self.sub(self.linear(7, &[(8, 38), (18, 41)]), self.advice(6)),
            17 => self.sub(
                self.sub(
                    self.linear(7, &[(8, 38)])
                        .add(self.constant(TWO_POW_140_INDEX)),
                    self.constant(T_P_INDEX),
                ),
                self.advice(19),
            ),
            18 => self.advice(18).mul(self.advice(9)),
            19 => self.advice(18).mul(self.advice(10)),
            20 => self.sub(self.linear(7, &[(8, 44), (9, 45)]), self.advice(6)),
            21 => self.sub(self.linear(7, &[(8, 38), (18, 41)]), self.advice(6)),
            22 => self.sub(
                self.sub(
                    self.linear(7, &[(8, 38)])
                        .add(self.constant(TWO_POW_140_INDEX)),
                    self.constant(T_P_INDEX),
                ),
                self.advice(19),
            ),
            23 => self.advice(18).mul(self.advice(9)),
            24 => self.advice(18).mul(self.advice(10)),
            25 => self.sub(
                self.linear(7, &[(8, 39), (22, 46), (18, 41)]),
                self.advice(6),
            ),
            26 => self.sub(
                self.sub(
                    self.linear(7, &[(8, 39)])
                        .add(self.constant(TWO_POW_130_INDEX)),
                    self.constant(T_P_INDEX),
                ),
                self.advice(19),
            ),
            27 => self.advice(18).mul(self.advice(22)),
            28 => self.advice(18).mul(self.advice(9)),
            29 => self.advice(18).mul(self.advice(10)),
            30 => self.boolean(self.advice(9)),
            31 => self.sub(self.advice(15), self.linear(6, &[(7, 0), (22, 6)])),
            32 => self.sub(self.advice(5), self.linear(15, &[(8, 40), (9, 41)])),
            33 => self.sub(
                self.sub(
                    self.advice(15).add(self.constant(TWO_POW_130_INDEX)),
                    self.constant(T_P_INDEX),
                ),
                self.advice(19),
            ),
            34 => self.advice(9).mul(self.advice(8)),
            35 => self.advice(9).mul(self.advice(18)),
            36 => self.advice(9).mul(self.advice(10)),
            _ => unreachable!(),
        }
    }
}
