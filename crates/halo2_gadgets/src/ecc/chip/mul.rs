use super::{CircuitVersion, EccPoint, NonIdentityEccPoint, ScalarVar, T_Q, add};
use crate::utilities::{
    lookup_range_check::{PallasLookupRangeCheck, PallasLookupRangeCheckConfig},
    {bool_check, ternary},
};
use std::{
    convert::TryInto,
    ops::{Deref, Range},
};

use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Selector},
    poly::Rotation,
};

use pasta_curves::{arithmetic::CurveAffine, pallas};

mod complete;
pub(super) mod incomplete;
mod overflow;

/// Number of bits for which complete addition needs to be used in variable-base
/// scalar multiplication
const NUM_COMPLETE_BITS: usize = 3;

// Bits used in incomplete addition. k_{254} to k_{4} inclusive
const INCOMPLETE_LEN: usize = pallas::Scalar::NUM_BITS as usize - 1 - NUM_COMPLETE_BITS;

// Bits k_{254} to k_{4} inclusive are used in incomplete addition.
// The `hi` half is k_{254} to k_{130} inclusive (length 125 bits).
// (It is a coincidence that k_{130} matches the boundary of the
// overflow check described in [the book](https://zcash.github.io/halo2/design/gadgets/ecc/var-base-scalar-mul.html#overflow-check).)
const INCOMPLETE_HI_RANGE: Range<usize> = 0..INCOMPLETE_HI_LEN;
const INCOMPLETE_HI_LEN: usize = INCOMPLETE_LEN / 2;

// Bits k_{254} to k_{4} inclusive are used in incomplete addition.
// The `lo` half is k_{129} to k_{4} inclusive (length 126 bits).
const INCOMPLETE_LO_RANGE: Range<usize> = INCOMPLETE_HI_LEN..INCOMPLETE_LEN;
const INCOMPLETE_LO_LEN: usize = INCOMPLETE_LEN - INCOMPLETE_HI_LEN;

// Bits k_{3} to k_{1} inclusive are used in complete addition.
// Bit k_{0} is handled separately.
const COMPLETE_RANGE: Range<usize> = INCOMPLETE_LEN..(INCOMPLETE_LEN + NUM_COMPLETE_BITS);

#[derive(Clone, Copy, Debug)]
struct JacobianPoint {
    x: pallas::Base,
    y: pallas::Base,
    z: pallas::Base,
}

impl JacobianPoint {
    fn from_affine(point: pallas::Affine) -> Self {
        let coordinates = point
            .coordinates()
            .expect("the variable-base multiplication base is nonidentity");
        Self {
            x: *coordinates.x(),
            y: *coordinates.y(),
            z: pallas::Base::ONE,
        }
    }

    /// Doubles a nonidentity Pallas point without exceptional-case handling.
    fn double_unchecked(self) -> Self {
        // dbl-2009-l for a short-Weierstrass curve with a = 0.
        let a = self.x.square();
        let b = self.y.square();
        let c = b.square();
        let d = ((self.x + b).square() - a - c).double();
        let e = a.double() + a;
        let f = e.square();
        let z = (self.z * self.y).double();
        let x = f - d.double();
        let y = e * (d - x) - c.double().double().double();

        Self { x, y, z }
    }

    /// Adds a nonidentity affine point that is neither equal to nor the
    /// negation of `self`.
    fn add_mixed_unchecked(self, x: pallas::Base, y: pallas::Base) -> Self {
        let z_squared = self.z.square();
        let u = x * z_squared;
        let s = y * z_squared * self.z;
        let h = u - self.x;
        let hh = h.square();
        let i = hh.double().double();
        let j = h * i;
        let r = (s - self.y).double();
        let v = self.x * i;
        let result_x = r.square() - j - v.double();
        let result_y = r * (v - result_x) - (self.y * j).double();
        let result_z = (self.z + h).square() - z_squared - hh;

        Self {
            x: result_x,
            y: result_y,
            z: result_z,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct AffinePoint {
    x: pallas::Base,
    y: pallas::Base,
}

#[derive(Clone, Copy, Debug)]
struct IncompleteRowWitness {
    z: pallas::Base,
    point: AffinePoint,
    lambda_1: pallas::Base,
    lambda_2: pallas::Base,
}

#[derive(Clone, Debug)]
struct IncompleteMulWitness {
    rows: Vec<IncompleteRowWitness>,
    output: AffinePoint,
}

impl IncompleteMulWitness {
    fn new(base: pallas::Affine, scalar: &pallas::Base) -> Self {
        let coordinates = base
            .coordinates()
            .expect("the variable-base multiplication base is nonidentity");
        let base_x = *coordinates.x();
        let base_y = *coordinates.y();
        let mut bits = scalar_mul_bits(scalar);
        bits.reverse();

        // For the incomplete prefix, the accumulator coefficient starts at 2
        // and follows c' = 2c +/- 1. At row i in 0..251 it is between 2^i + 1
        // and 3 * 2^i - 1. Thus c < 2^252 and 3c < 9 * 2^250 < q, so neither c
        // nor 3c can be 0 or +/-1 modulo the Pallas group order q. The final
        // output coefficient is also nonzero because it is less than 2^253.
        let mut accumulator = JacobianPoint::from_affine(base).double_unchecked();
        let mut accumulators = Vec::with_capacity(INCOMPLETE_LEN + 1);
        accumulators.push(accumulator);
        for bit in &bits[..INCOMPLETE_LEN] {
            accumulator = accumulator.double_unchecked();
            let addend_y = if *bit { base_y } else { -base_y };
            accumulator = accumulator.add_mixed_unchecked(base_x, addend_y);
            accumulators.push(accumulator);
        }

        let affine = batch_normalize_nonidentity(&accumulators);
        let mut denominators = Vec::with_capacity(INCOMPLETE_LEN * 2);
        for points in affine.windows(2) {
            let current = points[0];
            let next = points[1];
            denominators.push(current.x - base_x);
            denominators.push(current.x - next.x);
        }
        batch_invert_nonzero(&mut denominators);

        let mut z = pallas::Base::ZERO;
        let mut rows = Vec::with_capacity(INCOMPLETE_LEN);
        for ((bit, points), inverses) in bits[..INCOMPLETE_LEN]
            .iter()
            .zip(affine.windows(2))
            .zip(denominators.chunks_exact(2))
        {
            let current = points[0];
            let next = points[1];
            let addend_y = if *bit { base_y } else { -base_y };
            z = z.double() + pallas::Base::from(*bit as u64);
            rows.push(IncompleteRowWitness {
                z,
                point: current,
                lambda_1: (current.y - addend_y) * inverses[0],
                lambda_2: (current.y + next.y) * inverses[1],
            });
        }

        Self {
            rows,
            output: *affine.last().expect("the accumulator list is nonempty"),
        }
    }

    fn point(&self, index: usize) -> AffinePoint {
        if index == self.rows.len() {
            self.output
        } else {
            self.rows[index].point
        }
    }
}

fn batch_normalize_nonidentity(points: &[JacobianPoint]) -> Vec<AffinePoint> {
    let mut z_inverses = points.iter().map(|point| point.z).collect::<Vec<_>>();
    batch_invert_nonzero(&mut z_inverses);
    points
        .iter()
        .zip(z_inverses)
        .map(|(point, z_inverse)| {
            let z_squared = z_inverse.square();
            AffinePoint {
                x: point.x * z_squared,
                y: point.y * z_squared * z_inverse,
            }
        })
        .collect()
}

fn batch_invert_nonzero(values: &mut [pallas::Base]) {
    let mut scratch = Vec::with_capacity(values.len());
    let mut accumulator = pallas::Base::ONE;
    for value in values.iter() {
        scratch.push(accumulator);
        accumulator *= value;
    }

    accumulator = accumulator
        .invert()
        .expect("incomplete multiplication denominators are nonzero");
    for (value, prefix) in values.iter_mut().zip(scratch).rev() {
        let original = *value;
        *value = accumulator * prefix;
        accumulator *= original;
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Config<Lookup: PallasLookupRangeCheck = PallasLookupRangeCheckConfig> {
    // Selector used to check switching logic on LSB
    q_mul_lsb: Selector,
    // Configuration used in complete addition
    add_config: add::Config,
    // Configuration used for `hi` bits of the scalar
    hi_config: incomplete::Config<INCOMPLETE_HI_LEN>,
    // Configuration used for `lo` bits of the scalar
    lo_config: incomplete::Config<INCOMPLETE_LO_LEN>,
    // Configuration used for complete addition part of double-and-add algorithm
    complete_config: complete::Config,
    // Configuration used to check for overflow
    overflow_config: overflow::Config<Lookup>,
}

impl<Lookup: PallasLookupRangeCheck> Config<Lookup> {
    pub(super) fn configure(
        meta: &mut ConstraintSystem<pallas::Base>,
        add_config: add::Config,
        lookup_config: Lookup,
        advices: [Column<Advice>; 10],
    ) -> Self {
        let hi_config = incomplete::Config::configure(
            meta, advices[9], advices[3], advices[0], advices[1], advices[4], advices[5],
        );
        let lo_config = incomplete::Config::configure(
            meta, advices[6], advices[7], advices[0], advices[1], advices[8], advices[2],
        );
        let complete_config = complete::Config::configure(meta, advices[9], add_config);
        let overflow_config =
            overflow::Config::configure(meta, lookup_config, advices[6..9].try_into().unwrap());

        let config = Self {
            q_mul_lsb: meta.selector(),
            add_config,
            hi_config,
            lo_config,
            complete_config,
            overflow_config,
        };

        config.create_gate(meta);

        assert_eq!(
            config.hi_config.double_and_add.x_p, config.lo_config.double_and_add.x_p,
            "x_p is shared across hi and lo halves."
        );
        assert_eq!(
            config.hi_config.y_p, config.lo_config.y_p,
            "y_p is shared across hi and lo halves."
        );

        // For both hi_config and lo_config:
        // z and lambda1 are assigned on the same row as the add_config output.
        // Therefore, z and lambda1 must not overlap with add_config.x_qr, add_config.y_qr.
        let add_config_outputs = config.add_config.output_columns();
        {
            assert!(
                !add_config_outputs.contains(&config.hi_config.z),
                "incomplete config z cannot overlap with complete addition columns."
            );
            assert!(
                !add_config_outputs.contains(&config.hi_config.double_and_add.lambda_1),
                "incomplete config lambda1 cannot overlap with complete addition columns."
            );
        }
        {
            assert!(
                !add_config_outputs.contains(&config.lo_config.z),
                "incomplete config z cannot overlap with complete addition columns."
            );
            assert!(
                !add_config_outputs.contains(&config.lo_config.double_and_add.lambda_1),
                "incomplete config lambda1 cannot overlap with complete addition columns."
            );
        }

        config
    }

    fn create_gate(&self, meta: &mut ConstraintSystem<pallas::Base>) {
        // If `lsb` is 0, (x, y) = (x_p, -y_p). If `lsb` is 1, (x, y) = (0,0).
        // https://p.z.cash/halo2-0.1:ecc-var-mul-lsb-gate?partial
        meta.create_gate("LSB check", |meta| {
            let q_mul_lsb = meta.query_selector(self.q_mul_lsb);

            let z_1 = meta.query_advice(self.complete_config.z_complete, Rotation::cur());
            let z_0 = meta.query_advice(self.complete_config.z_complete, Rotation::next());
            let x_p = meta.query_advice(self.add_config.x_p, Rotation::cur());
            let y_p = meta.query_advice(self.add_config.y_p, Rotation::cur());
            let base_x = meta.query_advice(self.add_config.x_p, Rotation::next());
            let base_y = meta.query_advice(self.add_config.y_p, Rotation::next());

            //    z_0 = 2 * z_1 + k_0
            // => k_0 = z_0 - 2 * z_1
            let lsb = z_0 - z_1 * pallas::Base::from(2);

            let bool_check = bool_check(lsb.clone());

            // `lsb` = 0 => (x_p, y_p) = (x, -y)
            // `lsb` = 1 => (x_p, y_p) = (0,0)
            let lsb_x = ternary(lsb.clone(), x_p.clone(), x_p - base_x);
            let lsb_y = ternary(lsb, y_p.clone(), y_p + base_y);

            Constraints::with_selector(
                q_mul_lsb,
                [
                    ("bool_check", bool_check),
                    ("lsb_x", lsb_x),
                    ("lsb_y", lsb_y),
                ],
            )
        });
    }

    pub(super) fn assign(
        &self,
        mut layouter: impl Layouter<pallas::Base>,
        alpha: AssignedCell<pallas::Base, pallas::Base>,
        base: &NonIdentityEccPoint,
        circuit_version: CircuitVersion,
    ) -> Result<(EccPoint, ScalarVar), Error> {
        let (result, zs): (EccPoint, Vec<Z<pallas::Base>>) = layouter.assign_region(
            || "variable-base scalar mul",
            |mut region| {
                let offset = 0;

                // Case `base` into an `EccPoint` for later use.
                let base_point: EccPoint = base.clone().into();

                // Decompose `k = alpha + t_q` bitwise (big-endian bit order).
                let bits = decompose_for_scalar_mul(alpha.value());
                let incomplete_witness = base
                    .point()
                    .zip(alpha.value().copied())
                    .map(|(base, scalar)| IncompleteMulWitness::new(base, &scalar));
                let incomplete_witness = incomplete_witness.as_ref();

                // Define ranges for each part of the algorithm.
                let bits_incomplete_hi = &bits[INCOMPLETE_HI_RANGE];
                let bits_incomplete_lo = &bits[INCOMPLETE_LO_RANGE];
                let lsb = bits[pallas::Scalar::NUM_BITS as usize - 1];

                // Initialize the accumulator `acc = [2]base` using complete addition.
                let acc =
                    self.add_config
                        .assign_region(&base_point, &base_point, offset, &mut region)?;

                // Increase the offset by 1 after complete addition.
                let offset = offset + 1;

                // Initialize the running sum for scalar decomposition to zero.
                //
                // `incomplete::Config::double_and_add` will copy this cell directly into
                // itself. This is fine because we are just assigning the same value to
                // the same cell twice, and then applying an equality constraint between
                // the cell and itself (which the permutation argument treats as a no-op).
                let z_init = Z(region.assign_advice_from_constant(
                    || "z_init = 0",
                    self.hi_config.z,
                    offset,
                    pallas::Base::zero(),
                )?);

                // Double-and-add (incomplete addition) for the `hi` half of the scalar decomposition
                let (x_a, y_a, zs_incomplete_hi) = self.hi_config.double_and_add(
                    &mut region,
                    offset,
                    base,
                    bits_incomplete_hi,
                    (X(acc.x), Y(acc.y), z_init.clone()),
                    circuit_version,
                    incomplete_witness,
                    INCOMPLETE_HI_RANGE,
                )?;

                // Double-and-add (incomplete addition) for the `lo` half of the scalar decomposition
                let z = zs_incomplete_hi.last().expect("should not be empty");
                let (x_a, y_a, zs_incomplete_lo) = self.lo_config.double_and_add(
                    &mut region,
                    offset,
                    base,
                    bits_incomplete_lo,
                    (x_a, y_a, z.clone()),
                    circuit_version,
                    incomplete_witness,
                    INCOMPLETE_LO_RANGE,
                )?;

                // Move from incomplete addition to complete addition.
                // Inside incomplete::double_and_add, the offset was increased once after initialization
                // of the running sum.
                // Then, the final assignment of double-and-add was made on row + offset + 1.
                // Outside of incomplete addition, we must account for these offset increases by adding
                // 2 to the incomplete addition length.
                assert!(INCOMPLETE_LO_RANGE.len() >= INCOMPLETE_HI_RANGE.len());
                let offset = offset + INCOMPLETE_LO_RANGE.len() + 2;

                // Complete addition
                let (acc, zs_complete) = {
                    let z = zs_incomplete_lo.last().expect("should not be empty");
                    // Bits used in complete addition. k_{3} to k_{1} inclusive
                    // The LSB k_{0} is handled separately.
                    let bits_complete = &bits[COMPLETE_RANGE];
                    self.complete_config.assign_region(
                        &mut region,
                        offset,
                        bits_complete,
                        &base_point,
                        x_a,
                        y_a,
                        z.clone(),
                    )?
                };

                // Each iteration of the complete addition uses two rows.
                let offset = offset + COMPLETE_RANGE.len() * 2;

                // Process the least significant bit
                let z_1 = zs_complete.last().unwrap().clone();
                let (result, z_0) = self.process_lsb(&mut region, offset, base, acc, z_1, lsb)?;

                #[cfg(test)]
                // Check that the correct multiple is obtained.
                {
                    use group::Curve;

                    let base = base.point();
                    let alpha = alpha
                        .value()
                        .map(|alpha| pallas::Scalar::from_repr(alpha.to_repr()).unwrap());
                    let real_mul = base.zip(alpha).map(|(base, alpha)| base * alpha);
                    let result = result.point();

                    real_mul
                        .zip(result)
                        .assert_if_known(|(real_mul, result)| &real_mul.to_affine() == result);
                }

                let zs = {
                    let mut zs = std::iter::empty()
                        .chain(Some(z_init))
                        .chain(zs_incomplete_hi)
                        .chain(zs_incomplete_lo)
                        .chain(zs_complete)
                        .chain(Some(z_0))
                        .collect::<Vec<_>>();
                    assert_eq!(zs.len(), pallas::Scalar::NUM_BITS as usize + 1);

                    // This reverses zs to give us [z_0, z_1, ..., z_{254}, z_{255}].
                    zs.reverse();
                    zs
                };

                Ok((result, zs))
            },
        )?;

        self.overflow_config.overflow_check(
            layouter.namespace(|| "overflow check"),
            alpha.clone(),
            &zs,
        )?;

        Ok((result, ScalarVar::BaseFieldElem(alpha)))
    }

    /// Processes the final scalar bit `k_0`.
    ///
    /// Assumptions for this sub-region:
    /// - `acc_x` and `acc_y` are assigned in row `offset` by the previous complete
    ///   addition. They will be copied into themselves.
    /// - `z_1 is assigned in row `offset` by the mul::complete region assignment. We only
    ///   use its value here.
    ///
    /// `x_p` and `y_p` are assigned here, and then copied into themselves by the complete
    /// addition subregion.
    ///
    /// ```text
    /// | x_p  | y_p  | acc_x | acc_y | complete addition  | z_1 | q_mul_lsb = 1
    /// |base_x|base_y| res_x | res_y |   |   |    |   |   | z_0 |
    /// ```
    ///
    /// [Specification](https://p.z.cash/halo2-0.1:ecc-var-mul-lsb-gate?partial).
    fn process_lsb(
        &self,
        region: &mut Region<'_, pallas::Base>,
        offset: usize,
        base: &NonIdentityEccPoint,
        acc: EccPoint,
        z_1: Z<pallas::Base>,
        lsb: Value<bool>,
    ) -> Result<(EccPoint, Z<pallas::Base>), Error> {
        // Enforce switching logic on LSB using a custom gate
        self.q_mul_lsb.enable(region, offset)?;

        // z_1 has been assigned at (z_complete, offset).
        // Assign z_0 = 2⋅z_1 + k_0
        let z_0 = {
            let z_0_val = z_1.value().zip(lsb).map(|(z_1, lsb)| {
                let lsb = pallas::Base::from(lsb as u64);
                z_1.double() + lsb
            });
            let z_0_cell = region.assign_advice(
                || "z_0",
                self.complete_config.z_complete,
                offset + 1,
                || z_0_val,
            )?;

            Z(z_0_cell)
        };

        // Copy in `base_x`, `base_y` to use in the LSB gate
        base.x()
            .copy_advice(|| "copy base_x", region, self.add_config.x_p, offset + 1)?;
        base.y()
            .copy_advice(|| "copy base_y", region, self.add_config.y_p, offset + 1)?;

        // If `lsb` is 0, return `Acc + (-P)`. If `lsb` is 1, simply return `Acc + 0`.
        let x = lsb.and_then(|lsb| {
            if !lsb {
                base.x.value().cloned()
            } else {
                Value::known(Assigned::Zero)
            }
        });

        let y = lsb.and_then(|lsb| {
            if !lsb {
                -base.y.value()
            } else {
                Value::known(Assigned::Zero)
            }
        });

        let x_cell = region.assign_advice(|| "x", self.add_config.x_p, offset, || x)?;
        let y_cell = region.assign_advice(|| "y", self.add_config.y_p, offset, || y)?;

        let p = EccPoint::from_coordinates_unchecked(x_cell, y_cell);

        // Return the result of the final complete addition as `[scalar]B`
        let result = self.add_config.assign_region(&p, &acc, offset, region)?;

        Ok((result, z_0))
    }
}

#[derive(Clone, Debug)]
// `x`-coordinate of the accumulator.
struct X<F: Field>(AssignedCell<Assigned<F>, F>);
impl<F: Field> Deref for X<F> {
    type Target = AssignedCell<Assigned<F>, F>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug)]
// `y`-coordinate of the accumulator.
struct Y<F: Field>(AssignedCell<Assigned<F>, F>);
impl<F: Field> Deref for Y<F> {
    type Target = AssignedCell<Assigned<F>, F>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug)]
// Cumulative sum `z` used to decompose the scalar.
struct Z<F: Field>(AssignedCell<F, F>);
impl<F: Field> Deref for Z<F> {
    type Target = AssignedCell<F, F>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

fn scalar_mul_bits(scalar: &pallas::Base) -> Vec<bool> {
    // We use `k = scalar + t_q` in the double-and-add algorithm, where
    // the scalar field `F_q = 2^254 + t_q`.
    // Note that the addition `scalar + t_q` is not reduced, so it must be
    // computed over 256-bit integers rather than in the field. The sum
    // cannot overflow 256 bits: `scalar` is at most 255 bits and `t_q` is
    // at most 127 bits.
    let mut k = [0u64; 4];
    let repr = scalar.to_repr();
    for (limb, chunk) in k.iter_mut().zip(repr.chunks(8)) {
        *limb = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    let t_q = [T_Q as u64, (T_Q >> 64) as u64, 0, 0];
    let mut carry = 0u128;
    for (k_limb, t_q_limb) in k.iter_mut().zip(t_q) {
        let sum = *k_limb as u128 + t_q_limb as u128 + carry;
        *k_limb = sum as u64;
        carry = sum >> 64;
    }

    // Little-endian bit representation of `k`.
    let bitstring = k
        .into_iter()
        .flat_map(|limb| limb.to_le_bytes())
        .flat_map(|byte| (0..8).map(move |shift| (byte >> shift) % 2 == 1));

    // Take the first 255 bits.
    bitstring
        .take(pallas::Scalar::NUM_BITS as usize)
        .collect::<Vec<_>>()
}

// https://p.z.cash/halo2-0.1:ecc-var-mul-witness-scalar?partial
fn decompose_for_scalar_mul(scalar: Value<&pallas::Base>) -> Vec<Value<bool>> {
    let bitstring = scalar.map(scalar_mul_bits);

    // Transpose.
    let mut bitstring = bitstring.transpose_vec(pallas::Scalar::NUM_BITS as usize);
    // Reverse to get the big-endian bit representation.
    bitstring.reverse();
    bitstring
}

#[cfg(test)]
pub mod tests {
    use group::{
        Curve, CurveAffine as _, Group,
        ff::{Field, PrimeField},
    };
    use halo2_proofs::{
        circuit::{Chip, Layouter, Value},
        plonk::Error,
    };
    use pasta_curves::{
        arithmetic::{CurveAffine, mul_fp_by_inverse_power_of_two},
        pallas,
    };
    use rand::rng;

    use crate::{
        ecc::{
            EccInstructions, NonIdentityPoint, Point, ScalarVar,
            chip::{EccChip, EccPoint},
            tests::TestFixedBases,
        },
        utilities::{UtilitiesInstructions, lookup_range_check::PallasLookupRangeCheck},
    };

    #[test]
    fn incomplete_witness_matches_group_arithmetic_and_gate_equations() {
        let mut rng = rng();
        let base = pallas::Point::random(&mut rng).to_affine();
        let coordinates = base.coordinates().unwrap();
        let base_x = *coordinates.x();
        let base_y = *coordinates.y();
        let scalars = [
            pallas::Base::ZERO,
            pallas::Base::ONE,
            -pallas::Base::ONE,
            pallas::Base::random(&mut rng),
        ];

        for scalar in scalars {
            let witness = super::IncompleteMulWitness::new(base, &scalar);
            let mut bits = super::scalar_mul_bits(&scalar);
            bits.reverse();
            let mut accumulator = base.to_curve().double();

            for (index, bit) in bits[..super::INCOMPLETE_LEN].iter().enumerate() {
                let row = witness.rows[index];
                let current = accumulator.to_affine();
                let current_coordinates = current.coordinates().unwrap();
                assert_eq!(row.point.x, *current_coordinates.x());
                assert_eq!(row.point.y, *current_coordinates.y());

                let addend_y = if *bit { base_y } else { -base_y };
                let next = witness.point(index + 1);
                let x_r = row.lambda_1.square() - row.point.x - base_x;
                let reconstructed_y = mul_fp_by_inverse_power_of_two(
                    &((row.lambda_1 + row.lambda_2) * (row.point.x - x_r)),
                    1,
                );
                assert_eq!(reconstructed_y, row.point.y);
                assert_eq!(
                    row.lambda_1 * (row.point.x - base_x),
                    row.point.y - addend_y,
                );
                assert_eq!(row.lambda_2.square() - x_r - row.point.x, next.x,);
                assert_eq!(row.lambda_2 * (row.point.x - next.x), row.point.y + next.y,);

                accumulator = accumulator.double()
                    + if *bit {
                        base.to_curve()
                    } else {
                        -base.to_curve()
                    };
            }

            let output = accumulator.to_affine();
            let output_coordinates = output.coordinates().unwrap();
            assert_eq!(witness.output.x, *output_coordinates.x());
            assert_eq!(witness.output.y, *output_coordinates.y());
        }
    }

    pub(crate) fn test_mul<Lookup: PallasLookupRangeCheck>(
        chip: EccChip<TestFixedBases, Lookup>,
        mut layouter: impl Layouter<pallas::Base>,
        p: &NonIdentityPoint<pallas::Affine, EccChip<TestFixedBases, Lookup>>,
        p_val: pallas::Affine,
    ) -> Result<(), Error> {
        let column = chip.config().advices[0];

        fn constrain_equal_non_id<
            EccChip: EccInstructions<pallas::Affine, Point = EccPoint> + Clone + Eq + std::fmt::Debug,
        >(
            chip: EccChip,
            mut layouter: impl Layouter<pallas::Base>,
            base_val: pallas::Affine,
            scalar_val: pallas::Base,
            result: Point<pallas::Affine, EccChip>,
        ) -> Result<(), Error> {
            // Move scalar from base field into scalar field (which always fits
            // for Pallas).
            let scalar = pallas::Scalar::from_repr(scalar_val.to_repr()).unwrap();
            let expected = NonIdentityPoint::new(
                chip,
                layouter.namespace(|| "expected point"),
                Value::known((base_val * scalar).to_affine()),
            )?;
            result.constrain_equal(layouter.namespace(|| "constrain result"), &expected)
        }

        // [a]B
        {
            let scalar_val = pallas::Base::random(&mut rng());
            let (result, _) = {
                let scalar = chip.load_private(
                    layouter.namespace(|| "random scalar"),
                    column,
                    Value::known(scalar_val),
                )?;
                let scalar = ScalarVar::from_base(
                    chip.clone(),
                    layouter.namespace(|| "ScalarVar from_base"),
                    &scalar,
                )?;
                p.mul(layouter.namespace(|| "random [a]B"), scalar)?
            };
            constrain_equal_non_id(
                chip.clone(),
                layouter.namespace(|| "random [a]B"),
                p_val,
                scalar_val,
                result,
            )?;
        }

        // [0]B should return (0,0) since variable-base scalar multiplication
        // uses complete addition for the final bits of the scalar.
        {
            let scalar_val = pallas::Base::zero();
            let (result, _) = {
                let scalar = chip.load_private(
                    layouter.namespace(|| "zero"),
                    column,
                    Value::known(scalar_val),
                )?;
                let scalar = ScalarVar::from_base(
                    chip.clone(),
                    layouter.namespace(|| "ScalarVar from_base"),
                    &scalar,
                )?;
                p.mul(layouter.namespace(|| "[0]B"), scalar)?
            };
            result
                .inner()
                .is_identity()
                .assert_if_known(|is_identity| *is_identity);
        }

        // [-1]B (the largest possible base field element)
        {
            let scalar_val = -pallas::Base::one();
            let (result, _) = {
                let scalar = chip.load_private(
                    layouter.namespace(|| "-1"),
                    column,
                    Value::known(scalar_val),
                )?;
                let scalar = ScalarVar::from_base(
                    chip.clone(),
                    layouter.namespace(|| "ScalarVar from_base"),
                    &scalar,
                )?;
                p.mul(layouter.namespace(|| "[-1]B"), scalar)?
            };
            constrain_equal_non_id(
                chip,
                layouter.namespace(|| "[-1]B"),
                p_val,
                scalar_val,
                result,
            )?;
        }

        Ok(())
    }

    /// Test for the variable-base scalar-mul base-anchoring fix.
    ///
    /// This drives the real `Circuit::configure` + `FloorPlanner::synthesize` (so
    /// that the production `mul::Config` / `incomplete::Config::double_and_add` runs)
    /// through a copy-recording `Assignment`, and asserts that the fixed circuit
    /// emits extra copy (equality) constraints relative to the insecure one. The
    /// extra constraints are exactly the base anchors — `base.{x,y}` copied into the
    /// incomplete-addition `x_p`/`y_p` columns. If the anchor is removed, the two
    /// circuits emit identical copies and this fails. Copies are structural, so the
    /// witness is left unknown (no malicious-witness construction needed).
    mod base_anchoring {
        use crate::{
            ecc::{
                CircuitVersion, NonIdentityPoint, ScalarVar,
                chip::{EccChip, EccConfig},
                tests::TestFixedBases,
            },
            utilities::{
                UtilitiesInstructions,
                lookup_range_check::{LookupRangeCheck, PallasLookupRangeCheckConfig},
            },
        };
        use group::{Curve, Group};
        use halo2_proofs::{
            circuit::{Layouter, SimpleFloorPlanner, Value},
            plonk::{
                Advice, Any, Assigned, Assignment, Circuit, Column, ConstraintSystem, Error, Fixed,
                FloorPlanner, Instance, Selector,
            },
        };
        use pasta_curves::pallas;
        use std::collections::BTreeSet;

        /// An `Assignment` that records the copy constraints and selector enables, so a test
        /// can inspect both which equality constraints and at which rows they were emitted.
        #[derive(Default)]
        struct CopyRecorder {
            copies: Vec<(Column<Any>, usize, Column<Any>, usize)>,
            selectors: Vec<(Selector, usize)>,
        }

        impl Assignment<pallas::Base> for CopyRecorder {
            fn enter_region<NR, N>(&mut self, _: N)
            where
                NR: Into<String>,
                N: FnOnce() -> NR,
            {
            }
            fn exit_region(&mut self) {}
            fn enable_selector<A, AR>(
                &mut self,
                _: A,
                selector: &Selector,
                row: usize,
            ) -> Result<(), Error>
            where
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                self.selectors.push((*selector, row));
                Ok(())
            }
            fn query_instance(
                &self,
                _: Column<Instance>,
                _: usize,
            ) -> Result<Value<pallas::Base>, Error> {
                Ok(Value::unknown())
            }
            fn assign_advice<V, VR, A, AR>(
                &mut self,
                _: A,
                _: Column<Advice>,
                _: usize,
                _: V,
            ) -> Result<(), Error>
            where
                V: FnOnce() -> Value<VR>,
                VR: Into<Assigned<pallas::Base>>,
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                Ok(())
            }
            fn assign_fixed<V, VR, A, AR>(
                &mut self,
                _: A,
                _: Column<Fixed>,
                _: usize,
                _: V,
            ) -> Result<(), Error>
            where
                V: FnOnce() -> Value<VR>,
                VR: Into<Assigned<pallas::Base>>,
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                Ok(())
            }
            fn copy(
                &mut self,
                left_column: Column<Any>,
                left_row: usize,
                right_column: Column<Any>,
                right_row: usize,
            ) -> Result<(), Error> {
                self.copies
                    .push((left_column, left_row, right_column, right_row));
                Ok(())
            }
            fn fill_from_row(
                &mut self,
                _: Column<Fixed>,
                _: usize,
                _: Value<Assigned<pallas::Base>>,
            ) -> Result<(), Error> {
                Ok(())
            }
            fn push_namespace<NR, N>(&mut self, _: N)
            where
                NR: Into<String>,
                N: FnOnce() -> NR,
            {
            }
            fn pop_namespace(&mut self, _: Option<String>) {}
        }

        /// Minimal circuit that performs a single variable-base scalar multiplication.
        struct MulCircuit {
            circuit_version: CircuitVersion,
        }

        #[derive(Clone)]
        struct MulConfig {
            ecc: EccConfig<TestFixedBases>,
            constants: Column<Fixed>,
        }

        impl Circuit<pallas::Base> for MulCircuit {
            type Config = MulConfig;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                MulCircuit {
                    circuit_version: self.circuit_version,
                }
            }

            fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> MulConfig {
                let advices = [
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                    meta.advice_column(),
                ];
                let lookup_table = meta.lookup_table_column();
                let lagrange_coeffs = [
                    meta.fixed_column(),
                    meta.fixed_column(),
                    meta.fixed_column(),
                    meta.fixed_column(),
                    meta.fixed_column(),
                    meta.fixed_column(),
                    meta.fixed_column(),
                    meta.fixed_column(),
                ];
                let constants = meta.fixed_column();
                meta.enable_constant(constants);
                let range_check =
                    PallasLookupRangeCheckConfig::configure(meta, advices[9], lookup_table);
                let ecc = EccChip::<TestFixedBases>::configure(
                    meta,
                    advices,
                    lagrange_coeffs,
                    range_check,
                );
                MulConfig { ecc, constants }
            }

            fn synthesize(
                &self,
                config: MulConfig,
                mut layouter: impl Layouter<pallas::Base>,
            ) -> Result<(), Error> {
                let chip = EccChip::construct(config.ecc.clone(), self.circuit_version);
                let base = NonIdentityPoint::new(
                    chip.clone(),
                    layouter.namespace(|| "base"),
                    Value::known(pallas::Point::generator().to_affine()),
                )?;
                let scalar = chip.load_private(
                    layouter.namespace(|| "scalar"),
                    config.ecc.advices[0],
                    Value::known(pallas::Base::from(7)),
                )?;
                let scalar =
                    ScalarVar::from_base(chip, layouter.namespace(|| "scalar var"), &scalar)?;
                base.mul(layouter.namespace(|| "[scalar] base"), scalar)?;
                Ok(())
            }
        }

        type Copy = (Column<Any>, usize, Column<Any>, usize);

        /// Synthesizes `MulCircuit` for the given version through a [`CopyRecorder`].
        fn record(circuit_version: CircuitVersion) -> CopyRecorder {
            let circuit = MulCircuit { circuit_version };
            let mut cs = ConstraintSystem::<pallas::Base>::default();
            let config = MulCircuit::configure(&mut cs);
            let constants = vec![config.constants];
            let mut recorder = CopyRecorder::default();
            <MulCircuit as Circuit<pallas::Base>>::FloorPlanner::synthesize(
                &mut recorder,
                &circuit,
                config,
                constants,
            )
            .expect("synthesis should succeed");
            recorder
        }

        #[test]
        fn fixed_circuit_anchors_incomplete_base() {
            let insecure: BTreeSet<Copy> = record(CircuitVersion::InsecureUnanchoredBase)
                .copies
                .into_iter()
                .collect();
            let fixed_recorder = record(CircuitVersion::AnchoredBase);
            let fixed: BTreeSet<Copy> = fixed_recorder.copies.iter().cloned().collect();

            // The fix only adds copy constraints; it changes no layout. So every copy the
            // insecure circuit emits must still be present in the fixed circuit.
            assert!(
                insecure.is_subset(&fixed),
                "the fixed circuit must retain every copy constraint of the insecure circuit"
            );

            // `configure` is deterministic, so this config's columns/selectors match the run.
            let config = MulCircuit::configure(&mut ConstraintSystem::default());
            let mul = &config.ecc.mul;
            let x_p = Column::<Any>::from(mul.hi_config.double_and_add.x_p);
            let y_p = Column::<Any>::from(mul.hi_config.y_p);

            // The anchor must sit on the first incomplete-addition row — the row where the
            // `(x_p, y_p)`-constancy gate `q_mul_2` first fires — so that constancy propagates
            // the base to every subsequent incomplete row. (Anchoring one row earlier, on the
            // `q_mul_1` doubling row, would not be reached by the constancy chain.)
            let first_incomplete_row = fixed_recorder
                .selectors
                .iter()
                .filter(|(s, _)| *s == mul.hi_config.q_mul_2)
                .map(|&(_, row)| row)
                .min()
                .expect("q_mul_2 must be enabled");

            // The `hi` and `lo` halves share the `x_p`/`y_p` columns (see `Config::configure`) and
            // anchor at the same offset, so the four `copy_advice` calls collapse to exactly two
            // new equality constraints. Each is recorded as `(dst_col, dst_row, src_col, src_row)`:
            // the `copy_advice` writes the anchored cell at `(x_p|y_p, first_incomplete_row)` and
            // equates it to the source base coordinate, which this circuit witnesses in the same
            // column at row 0.
            let extra: BTreeSet<Copy> = fixed.difference(&insecure).cloned().collect();
            assert_eq!(
                extra,
                [
                    (x_p, first_incomplete_row, x_p, 0),
                    (y_p, first_incomplete_row, y_p, 0),
                ]
                .into_iter()
                .collect()
            );
        }
    }
}
