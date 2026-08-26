use super::{
    add, add_incomplete, EccBaseFieldElemFixed, EccScalarFixed, EccScalarFixedShort, FixedPoint,
    NonIdentityEccPoint, FIXED_BASE_WINDOW_SIZE, H,
};
use crate::utilities::decompose_running_sum::RunningSumConfig;

use std::marker::PhantomData;

use group::ff::{Field, PrimeField, PrimeFieldBits};
#[cfg(test)]
use group::{Curve, CurveAffine as _, Group};
use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    plonk::{
        Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Fixed,
        Selector, VirtualCells,
    },
    poly::Rotation,
};
use lazy_static::lazy_static;
use pasta_curves::{arithmetic::CurveAffine, pallas};
#[cfg(test)]
use subtle::{ConditionallySelectable, ConstantTimeEq};

pub mod base_field_elem;
pub mod full_width;
pub mod short;

lazy_static! {
    static ref H_BASE: pallas::Base = pallas::Base::from(H as u64);
}

/// Computes the points selected by a fixed-base scalar's windows.
#[cfg(test)]
fn compute_window_points(base: pallas::Affine, windows: &[usize]) -> Vec<pallas::Affine> {
    assert!(!windows.is_empty());
    assert!(windows.iter().all(|window| *window < H));

    let mut window_base = base.to_curve();
    let mut offset_acc = pallas::Point::identity();
    let mut points = Vec::with_capacity(windows.len());

    for window in windows.iter().take(windows.len() - 1) {
        // Select from every possible [(k_w + 2) * 8^w] B, generating all of
        // them independently of k_w.
        let offset = window_base.double();
        points.push(select_window_point(offset, window_base, *window));

        // The most-significant window subtracts the accumulated offsets.
        offset_acc += offset;

        // Advance from [8^w] B to [8^(w + 1)] B.
        for _ in 0..FIXED_BASE_WINDOW_SIZE {
            window_base = window_base.double();
        }
    }

    // Select from every possible
    // [k_w * 8^w] B - sum_{j=0}^{w-1} [2 * 8^j] B, generating all of them
    // independently of k_w.
    points.push(select_window_point(
        -offset_acc,
        window_base,
        windows[windows.len() - 1],
    ));

    let mut affine_points = vec![pallas::Affine::identity(); points.len()];
    pallas::Point::batch_normalize(&points, &mut affine_points);
    affine_points
}

/// Selects the `window`th point of the length-`H` sequence by visiting and
/// conditionally selecting from every candidate, starting at `start` and
/// advancing by `step`.
#[cfg(test)]
fn select_window_point(start: pallas::Point, step: pallas::Point, window: usize) -> pallas::Point {
    let mut candidate = start;
    let mut selected = start;
    for digit in 1..H {
        candidate += step;
        let choice = (window as u8).ct_eq(&(digit as u8));
        selected = pallas::Point::conditional_select(&selected, &candidate, choice);
    }
    selected
}

#[derive(Clone, Copy)]
struct WindowWitness {
    x: pallas::Base,
    y: pallas::Base,
    u: pallas::Base,
}

#[derive(Clone, Copy)]
struct WindowAccumulator {
    x: pallas::Base,
    y: pallas::Base,
    z: pallas::Base,
    z_sq: pallas::Base,
    z_cubed: pallas::Base,
}

impl WindowAccumulator {
    fn from_affine(point: WindowWitness) -> Self {
        Self {
            x: point.x,
            y: point.y,
            z: pallas::Base::ONE,
            z_sq: pallas::Base::ONE,
            z_cubed: pallas::Base::ONE,
        }
    }

    fn add_mixed(
        &mut self,
        point: WindowWitness,
    ) -> (Assigned<pallas::Base>, Assigned<pallas::Base>) {
        let x_p = point.x * self.z_sq;
        let y_p = point.y * self.z_cubed;
        let h = x_p - self.x;
        let r = y_p - self.y;
        let h_sq = h.square();
        let h_cubed = h_sq * h;
        let x_h_sq = self.x * h_sq;
        let x = r.square() - h_cubed - x_h_sq.double();
        let y = r * (x_h_sq - x) - self.y * h_cubed;
        let z = self.z * h;
        let z_sq = z.square();
        let z_cubed = z_sq * z;

        *self = Self {
            x,
            y,
            z,
            z_sq,
            z_cubed,
        };

        (Assigned::Rational(x, z_sq), Assigned::Rational(y, z_cubed))
    }
}

fn evaluate_lagrange_polynomial_for_window<const WINDOW: usize>(
    coefficients: &[pallas::Base; H],
) -> pallas::Base {
    coefficients
        .iter()
        .rev()
        .copied()
        .reduce(|accumulator, coefficient| {
            let product = match WINDOW {
                1 => accumulator,
                2 => accumulator.double(),
                3 => accumulator.double() + accumulator,
                4 => accumulator.double().double(),
                5 => accumulator.double().double() + accumulator,
                6 => (accumulator.double() + accumulator).double(),
                7 => accumulator.double().double().double() - accumulator,
                _ => unreachable!("window is a nonzero three-bit value"),
            };
            product + coefficient
        })
        .expect("a fixed-base interpolation polynomial is non-empty")
}

fn evaluate_lagrange_polynomial(coefficients: &[pallas::Base; H], window: usize) -> pallas::Base {
    // Witness generation is not required to be constant-time. Specializing on
    // the three-bit window avoids full field multiplications in the Horner loop.
    match window {
        0 => coefficients[0],
        1 => evaluate_lagrange_polynomial_for_window::<1>(coefficients),
        2 => evaluate_lagrange_polynomial_for_window::<2>(coefficients),
        3 => evaluate_lagrange_polynomial_for_window::<3>(coefficients),
        4 => evaluate_lagrange_polynomial_for_window::<4>(coefficients),
        5 => evaluate_lagrange_polynomial_for_window::<5>(coefficients),
        6 => evaluate_lagrange_polynomial_for_window::<6>(coefficients),
        7 => evaluate_lagrange_polynomial_for_window::<7>(coefficients),
        _ => panic!("fixed-base window must fit in three bits"),
    }
}

fn reconstruct_window_witnesses(
    lagrange_coeffs: &[[pallas::Base; H]],
    us: &[[<pallas::Base as PrimeField>::Repr; H]],
    zs: &[u64],
    windows: &[usize],
) -> Vec<WindowWitness> {
    assert_eq!(lagrange_coeffs.len(), windows.len());
    assert_eq!(us.len(), windows.len());
    assert_eq!(zs.len(), windows.len());
    assert!(windows.iter().all(|window| *window < H));

    windows
        .iter()
        .enumerate()
        .map(|(index, window)| {
            let x = evaluate_lagrange_polynomial(&lagrange_coeffs[index], *window);
            let u = pallas::Base::from_repr(us[index][*window])
                .expect("stored fixed-base u-coordinate is canonical");
            let y = u.square() - pallas::Base::from(zs[index]);
            WindowWitness { x, y, u }
        })
        .collect()
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Config<FixedPoints: super::FixedPoints<pallas::Affine>> {
    running_sum_config: RunningSumConfig<pallas::Base, FIXED_BASE_WINDOW_SIZE>,
    // The fixed Lagrange interpolation coefficients for `x_p`.
    lagrange_coeffs: [Column<Fixed>; H],
    // The fixed `z` for each window such that `y + z = u^2`.
    fixed_z: Column<Fixed>,
    // Decomposition of an `n-1`-bit scalar into `k`-bit windows:
    // a = a_0 + 2^k(a_1) + 2^{2k}(a_2) + ... + 2^{(n-1)k}(a_{n-1})
    window: Column<Advice>,
    // y-coordinate of accumulator (only used in the final row).
    u: Column<Advice>,
    // Configuration for `add`
    add_config: add::Config,
    // Configuration for `add_incomplete`
    add_incomplete_config: add_incomplete::Config,
    _marker: PhantomData<FixedPoints>,
}

impl<FixedPoints: super::FixedPoints<pallas::Affine>> Config<FixedPoints> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn configure(
        meta: &mut ConstraintSystem<pallas::Base>,
        lagrange_coeffs: [Column<Fixed>; H],
        window: Column<Advice>,
        u: Column<Advice>,
        add_config: add::Config,
        add_incomplete_config: add_incomplete::Config,
    ) -> Self {
        meta.enable_equality(window);
        meta.enable_equality(u);

        let q_running_sum = meta.selector();
        let running_sum_config = RunningSumConfig::configure(meta, q_running_sum, window);

        let config = Self {
            running_sum_config,
            lagrange_coeffs,
            fixed_z: meta.fixed_column(),
            window,
            u,
            add_config,
            add_incomplete_config,
            _marker: PhantomData,
        };

        // Check relationships between `add_config` and `add_incomplete_config`.
        assert_eq!(
            config.add_config.x_p, config.add_incomplete_config.x_p,
            "add and add_incomplete are used internally in mul_fixed."
        );
        assert_eq!(
            config.add_config.y_p, config.add_incomplete_config.y_p,
            "add and add_incomplete are used internally in mul_fixed."
        );
        for advice in [config.window, config.u].iter() {
            assert_ne!(
                *advice, config.add_config.x_qr,
                "Do not overlap with output columns of add."
            );
            assert_ne!(
                *advice, config.add_config.y_qr,
                "Do not overlap with output columns of add."
            );
        }

        config.running_sum_coords_gate(meta);

        config
    }

    /// Check that each window in the running sum decomposition uses the correct y_p
    /// and interpolated x_p.
    ///
    /// This gate is used both in the mul_fixed::base_field_elem and mul_fixed::short
    /// helpers, which decompose the scalar using a running sum.
    ///
    /// This gate is not used in the mul_fixed::full_width helper, since the full-width
    /// scalar is witnessed directly as three-bit windows instead of being decomposed
    /// via a running sum.
    fn running_sum_coords_gate(&self, meta: &mut ConstraintSystem<pallas::Base>) {
        meta.create_gate("Running sum coordinates check", |meta| {
            let q_mul_fixed_running_sum =
                meta.query_selector(self.running_sum_config.q_range_check());

            let z_cur = meta.query_advice(self.window, Rotation::cur());
            let z_next = meta.query_advice(self.window, Rotation::next());

            //    z_{i+1} = (z_i - a_i) / 2^3
            // => a_i = z_i - z_{i+1} * 2^3
            let word = z_cur - z_next * pallas::Base::from(H as u64);

            Constraints::with_selector(q_mul_fixed_running_sum, self.coords_check(meta, word))
        });
    }

    /// [Specification](https://p.z.cash/halo2-0.1:ecc-fixed-mul-coordinates).
    #[allow(clippy::op_ref)]
    fn coords_check(
        &self,
        meta: &mut VirtualCells<'_, pallas::Base>,
        window: Expression<pallas::Base>,
    ) -> Vec<(&'static str, Expression<pallas::Base>)> {
        let y_p = meta.query_advice(self.add_config.y_p, Rotation::cur());
        let x_p = meta.query_advice(self.add_config.x_p, Rotation::cur());
        let z = meta.query_fixed(self.fixed_z);
        let u = meta.query_advice(self.u, Rotation::cur());

        let window_pow: Vec<Expression<pallas::Base>> = (0..H)
            .map(|pow| {
                (0..pow).fold(Expression::Constant(pallas::Base::one()), |acc, _| {
                    acc * window.clone()
                })
            })
            .collect();

        let interpolated_x = window_pow.iter().zip(self.lagrange_coeffs.iter()).fold(
            Expression::Constant(pallas::Base::zero()),
            |acc, (window_pow, coeff)| acc + (window_pow.clone() * meta.query_fixed(*coeff)),
        );

        // Check interpolation of x-coordinate
        let x_check = interpolated_x - x_p.clone();
        // Check that `y + z = u^2`, where `z` is fixed and `u`, `y` are witnessed
        let y_check = u.square() - y_p.clone() - z;
        // Check that (x, y) is on the curve
        let on_curve =
            y_p.square() - x_p.clone().square() * x_p - Expression::Constant(pallas::Affine::b());

        vec![
            ("check x", x_check),
            ("check y", y_check),
            ("on-curve", on_curve),
        ]
    }

    #[allow(clippy::type_complexity)]
    fn assign_region_inner<F: FixedPoint<pallas::Affine>, const NUM_WINDOWS: usize>(
        &self,
        region: &mut Region<'_, pallas::Base>,
        offset: usize,
        scalar: &ScalarFixed,
        base: &F,
        coords_check_toggle: Selector,
    ) -> Result<(NonIdentityEccPoint, NonIdentityEccPoint), Error> {
        let lagrange_coeffs = base.lagrange_coeffs();
        let us = base.u();
        let zs = base.z();
        assert_eq!(lagrange_coeffs.len(), NUM_WINDOWS);
        assert_eq!(us.len(), NUM_WINDOWS);
        assert_eq!(zs.len(), NUM_WINDOWS);

        // Assign fixed columns for given fixed base
        self.assign_fixed_constants::<NUM_WINDOWS>(
            region,
            offset,
            &lagrange_coeffs,
            &zs,
            coords_check_toggle,
        )?;

        let scalar_windows_usize = scalar.windows_usize();
        assert_eq!(scalar_windows_usize.len(), NUM_WINDOWS);
        let window_witnesses: Value<Vec<_>> = scalar_windows_usize.iter().copied().collect();
        let window_witnesses = window_witnesses
            .map(|windows| reconstruct_window_witnesses(&lagrange_coeffs, &us, &zs, &windows))
            .transpose_vec(NUM_WINDOWS);

        // Initialize accumulator
        let mut accumulator = window_witnesses[0].map(WindowAccumulator::from_affine);
        let acc = self.process_window(region, offset, 0, window_witnesses[0])?;

        // Process all windows excluding least and most significant windows
        let acc = self.add_incomplete::<NUM_WINDOWS>(
            region,
            offset,
            acc,
            &window_witnesses,
            &mut accumulator,
        )?;

        // Process most significant window
        let mul_b = self.process_window(
            region,
            offset,
            NUM_WINDOWS - 1,
            window_witnesses[NUM_WINDOWS - 1],
        )?;

        Ok((acc, mul_b))
    }

    /// [Specification](https://p.z.cash/halo2-0.1:ecc-fixed-mul-load-base).
    fn assign_fixed_constants<const NUM_WINDOWS: usize>(
        &self,
        region: &mut Region<'_, pallas::Base>,
        offset: usize,
        lagrange_coeffs: &[[pallas::Base; H]],
        zs: &[u64],
        coords_check_toggle: Selector,
    ) -> Result<(), Error> {
        assert_eq!(lagrange_coeffs.len(), NUM_WINDOWS);
        assert_eq!(zs.len(), NUM_WINDOWS);

        // Assign fixed columns for given fixed base
        for window in 0..NUM_WINDOWS {
            coords_check_toggle.enable(region, window + offset)?;

            // Assign x-coordinate Lagrange interpolation coefficients
            for k in 0..H {
                region.assign_fixed(
                    || {
                        format!(
                            "Lagrange interpolation coeff for window: {:?}, k: {:?}",
                            window, k
                        )
                    },
                    self.lagrange_coeffs[k],
                    window + offset,
                    || Value::known(lagrange_coeffs[window][k]),
                )?;
            }

            // Assign z-values for each window
            region.assign_fixed(
                || format!("z-value for window: {:?}", window),
                self.fixed_z,
                window + offset,
                || Value::known(pallas::Base::from(zs[window])),
            )?;
        }

        Ok(())
    }

    /// Assigns the values used to process a window.
    fn process_window(
        &self,
        region: &mut Region<'_, pallas::Base>,
        offset: usize,
        w: usize,
        witness: Value<WindowWitness>,
    ) -> Result<NonIdentityEccPoint, Error> {
        // Assign the fixed-window multiple.
        let mul_b = {
            let x = witness.map(|witness| {
                let x = witness.x;
                assert!(x != pallas::Base::zero());
                x.into()
            });
            let x = region.assign_advice(
                || format!("mul_b_x, window {}", w),
                self.add_config.x_p,
                offset + w,
                || x,
            )?;

            let y = witness.map(|witness| {
                let y = witness.y;
                assert!(y != pallas::Base::zero());
                y.into()
            });
            let y = region.assign_advice(
                || format!("mul_b_y, window {}", w),
                self.add_config.y_p,
                offset + w,
                || y,
            )?;

            NonIdentityEccPoint::from_coordinates_unchecked(x, y)
        };

        // Assign u = (y_p + z_w).sqrt()
        let u_val = witness.map(|witness| witness.u);
        region.assign_advice(|| "u", self.u, offset + w, || u_val)?;

        Ok(mul_b)
    }

    fn add_incomplete<const NUM_WINDOWS: usize>(
        &self,
        region: &mut Region<'_, pallas::Base>,
        offset: usize,
        mut acc: NonIdentityEccPoint,
        window_witnesses: &[Value<WindowWitness>],
        accumulator: &mut Value<WindowAccumulator>,
    ) -> Result<NonIdentityEccPoint, Error> {
        for w in (0..NUM_WINDOWS)
            // The MSB is processed separately.
            .take(NUM_WINDOWS - 1)
            // Skip k_0 (already processed).
            .skip(1)
        {
            // Compute [(k_w + 2) ⋅ 8^w]B
            //
            // This assigns the coordinates of the returned point into the input cells for
            // the incomplete addition gate, which will then copy them into themselves.
            let mul_b = self.process_window(region, offset, w, window_witnesses[w])?;

            let result = accumulator
                .as_mut()
                .zip(window_witnesses[w])
                .map(|(accumulator, point)| accumulator.add_mixed(point));

            // Add to the accumulator.
            //
            // After the first loop, the accumulator will already be in the input cells
            // for the incomplete addition gate, and will be copied into themselves.
            acc = self.add_incomplete_config.assign_region_with_result(
                &mul_b,
                &acc,
                result,
                offset + w,
                region,
            )?;
        }
        Ok(acc)
    }
}

enum ScalarFixed {
    FullWidth(EccScalarFixed),
    Short(EccScalarFixedShort),
    BaseFieldElem(EccBaseFieldElemFixed),
}

impl From<&EccScalarFixed> for ScalarFixed {
    fn from(scalar_fixed: &EccScalarFixed) -> Self {
        Self::FullWidth(scalar_fixed.clone())
    }
}

impl From<&EccScalarFixedShort> for ScalarFixed {
    fn from(scalar_fixed: &EccScalarFixedShort) -> Self {
        Self::Short(scalar_fixed.clone())
    }
}

impl From<&EccBaseFieldElemFixed> for ScalarFixed {
    fn from(base_field_elem: &EccBaseFieldElemFixed) -> Self {
        Self::BaseFieldElem(base_field_elem.clone())
    }
}

impl ScalarFixed {
    /// The scalar decomposition was done in the base field. For computation
    /// outside the circuit, we now convert them back into the scalar field.
    ///
    /// This function does not require that the base field fits inside the scalar field,
    /// because the window size fits into either field.
    fn windows_field(&self) -> Vec<Value<pallas::Scalar>> {
        let running_sum_to_windows = |zs: Vec<AssignedCell<pallas::Base, pallas::Base>>| {
            (0..(zs.len() - 1))
                .map(|idx| {
                    let z_cur = zs[idx].value();
                    let z_next = zs[idx + 1].value();
                    let word = z_cur - z_next * Value::known(*H_BASE);
                    // This assumes that the endianness of the encodings of pallas::Base
                    // and pallas::Scalar are the same. They happen to be, but we need to
                    // be careful if this is generalised.
                    word.map(|word| pallas::Scalar::from_repr(word.to_repr()).unwrap())
                })
                .collect::<Vec<_>>()
        };
        match self {
            Self::BaseFieldElem(scalar) => running_sum_to_windows(scalar.running_sum.to_vec()),
            Self::Short(scalar) => running_sum_to_windows(
                scalar
                    .running_sum
                    .as_ref()
                    .expect("EccScalarFixedShort has been constrained")
                    .to_vec(),
            ),
            Self::FullWidth(scalar) => scalar
                .windows
                .as_ref()
                .expect("EccScalarFixed has been witnessed")
                .iter()
                .map(|bits| {
                    // This assumes that the endianness of the encodings of pallas::Base
                    // and pallas::Scalar are the same. They happen to be, but we need to
                    // be careful if this is generalised.
                    bits.value()
                        .map(|value| pallas::Scalar::from_repr(value.to_repr()).unwrap())
                })
                .collect::<Vec<_>>(),
        }
    }

    /// The scalar decomposition is guaranteed to be in three-bit windows, so we construct
    /// `usize` indices from the lowest three bits of each window field element for
    /// convenient indexing into `u`-values.
    fn windows_usize(&self) -> Vec<Value<usize>> {
        self.windows_field()
            .iter()
            .map(|window| {
                window.map(|window| {
                    window
                        .to_le_bits()
                        .iter()
                        .by_vals()
                        .take(FIXED_BASE_WINDOW_SIZE)
                        .rev()
                        .fold(0, |acc, b| 2 * acc + usize::from(b))
                })
            })
            .collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ecc::chip::{NUM_WINDOWS, NUM_WINDOWS_SHORT};
    use crate::ecc::tests::{FullWidth, Short};
    /// Offset applied to non-MSB windows to avoid identity points.
    const WINDOW_OFFSET: usize = 2;

    fn scalar_mul_window_points(base: pallas::Affine, windows: &[usize]) -> Vec<pallas::Affine> {
        let h = pallas::Scalar::from(H as u64);
        let mut points = windows
            .iter()
            .take(windows.len() - 1)
            .enumerate()
            .map(|(w, window)| {
                let scalar = pallas::Scalar::from((*window + WINDOW_OFFSET) as u64)
                    * h.pow([w as u64, 0, 0, 0]);
                (base * scalar).to_affine()
            })
            .collect::<Vec<_>>();

        let offset = (0..(windows.len() - 1)).fold(pallas::Scalar::zero(), |acc, w| {
            acc + pallas::Scalar::from(WINDOW_OFFSET as u64).pow([
                FIXED_BASE_WINDOW_SIZE as u64 * w as u64 + 1,
                0,
                0,
                0,
            ])
        });
        let w = windows.len() - 1;
        let scalar = pallas::Scalar::from(windows[w] as u64) * h.pow([w as u64, 0, 0, 0]) - offset;
        points.push((base * scalar).to_affine());

        points
    }

    #[test]
    fn window_points_match_curve_multiplication() {
        let base = pallas::Point::generator().to_affine();

        for num_windows in [NUM_WINDOWS_SHORT, NUM_WINDOWS] {
            let mut cases = (0..H)
                .map(|digit| vec![digit; num_windows])
                .collect::<Vec<_>>();
            cases.push((0..num_windows).map(|w| w % H).collect());
            for windows in cases {
                assert_eq!(
                    compute_window_points(base, &windows),
                    scalar_mul_window_points(base, &windows),
                );
            }
        }
    }

    fn assert_reconstructed_window_witnesses<F>(base: F, num_windows: usize)
    where
        F: FixedPoint<pallas::Affine>,
    {
        let lagrange_coeffs = base.lagrange_coeffs();
        let us = base.u();
        let zs = base.z();
        assert_eq!(lagrange_coeffs.len(), num_windows);
        assert_eq!(us.len(), num_windows);
        assert_eq!(zs.len(), num_windows);

        let mut cases = (0..H)
            .map(|digit| vec![digit; num_windows])
            .collect::<Vec<_>>();
        cases.push((0..num_windows).map(|window| window % H).collect());

        for windows in cases {
            let expected = compute_window_points(base.generator(), &windows);
            let reconstructed = reconstruct_window_witnesses(&lagrange_coeffs, &us, &zs, &windows);
            for (expected, reconstructed) in expected.iter().zip(reconstructed) {
                let expected = expected.coordinates().unwrap();
                assert_eq!(*expected.x(), reconstructed.x);
                assert_eq!(*expected.y(), reconstructed.y);
            }
        }
    }

    #[test]
    fn reconstructed_window_witnesses_match_curve_points() {
        assert_reconstructed_window_witnesses(FullWidth::from_pallas_generator(), NUM_WINDOWS);
        assert_reconstructed_window_witnesses(Short, NUM_WINDOWS_SHORT);
    }

    #[test]
    fn window_accumulator_matches_curve_addition() {
        let base = pallas::Point::generator().to_affine();

        for num_windows in [NUM_WINDOWS_SHORT, NUM_WINDOWS] {
            let windows = (0..num_windows)
                .map(|window| window % H)
                .collect::<Vec<_>>();
            let points = compute_window_points(base, &windows);
            let first = points[0].coordinates().unwrap();
            let mut accumulator = WindowAccumulator::from_affine(WindowWitness {
                x: *first.x(),
                y: *first.y(),
                u: pallas::Base::ZERO,
            });
            let mut expected = points[0].to_curve();

            for point in points.iter().take(num_windows - 1).skip(1) {
                let coordinates = point.coordinates().unwrap();
                expected += point.to_curve();
                let (x, y) = accumulator.add_mixed(WindowWitness {
                    x: *coordinates.x(),
                    y: *coordinates.y(),
                    u: pallas::Base::ZERO,
                });

                assert_eq!(
                    pallas::Affine::from_xy(x.evaluate(), y.evaluate()).unwrap(),
                    expected.to_affine(),
                );
            }
        }
    }
}
