//! Jacobian-coordinate Pallas accumulator shared by the witness computations
//! of variable-base scalar multiplication and Sinsemilla hashing.

use ff::Field;
use pasta_curves::{arithmetic::CurveAffine, pallas};

#[inline(always)]
pub(crate) fn square_with_runtime_backend(value: &pallas::Base) -> pallas::Base {
    // Method syntax selects `pallas::Base`'s portable inherent square.
    // Trait dispatch selects the configured runtime backend instead.
    Field::square(value)
}

/// A Pallas point in Jacobian coordinates, caching `z^2`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ProjectivePoint {
    pub(crate) x: pallas::Base,
    pub(crate) y: pallas::Base,
    pub(crate) z: pallas::Base,
    pub(crate) z_sq: pallas::Base,
}

/// Slope numerators of one incomplete `2A + P` step; both slopes share the new
/// accumulator's `z` as their denominator.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DoubleAndAddWitness {
    pub(crate) lambda_1_numerator: pallas::Base,
    pub(crate) lambda_2_numerator: pallas::Base,
}

impl ProjectivePoint {
    pub(crate) fn from_affine(point: pallas::Affine) -> Self {
        let coordinates = point
            .coordinates()
            .expect("the accumulator starts from a nonidentity point");
        Self {
            x: *coordinates.x(),
            y: *coordinates.y(),
            z: pallas::Base::ONE,
            z_sq: pallas::Base::ONE,
        }
    }

    /// Doubles a nonidentity Pallas point without exceptional-case handling.
    pub(crate) fn double_unchecked(self) -> Self {
        // dbl-2009-l for a short-Weierstrass curve with a = 0.
        let a = square_with_runtime_backend(&self.x);
        let b = square_with_runtime_backend(&self.y);
        let c = square_with_runtime_backend(&b);
        let d = (square_with_runtime_backend(&(self.x + b)) - a - c).double();
        let e = a.double() + a;
        let f = square_with_runtime_backend(&e);
        let z = (self.z * self.y).double();
        let z_sq = square_with_runtime_backend(&z);
        let x = f - d.double();
        let y = e * (d - x) - c.double().double().double();

        Self { x, y, z, z_sq }
    }

    /// Computes witnesses for the incomplete addition `2A + P` while keeping
    /// the accumulator in Jacobian coordinates. The returned rational values
    /// are the same affine values assigned by the circuit's witness flow.
    pub(crate) fn double_and_add(
        &mut self,
        (x_p, y_p): (pallas::Base, pallas::Base),
    ) -> DoubleAndAddWitness {
        let z_cubed = self.z_sq * self.z;
        let h = x_p * self.z_sq - self.x;
        let r = y_p * z_cubed - self.y;

        let h_sq = square_with_runtime_backend(&h);
        let h_cubed = h_sq * h;
        let x_h_sq = self.x * h_sq;
        let x_r = square_with_runtime_backend(&r) - h_cubed - Field::double(&x_h_sq);
        let d = x_h_sq - x_r;

        let d_sq = square_with_runtime_backend(&d);
        let d_cubed = d_sq * d;
        let y_h_cubed = self.y * h_cubed;
        // Scale lambda_1 by d so it shares z_new as its denominator with
        // lambda_2. The product is also needed for lambda_2's numerator.
        let r_d = r * d;
        let lambda_2_numerator = Field::double(&y_h_cubed) - r_d;

        let x_h_sq_d_sq = x_h_sq * d_sq;
        // Since d = x_h_sq - x_r, this saves a field multiplication over
        // computing (x_h_sq + x_r) * d_sq directly.
        let x_new = square_with_runtime_backend(&lambda_2_numerator) - Field::double(&x_h_sq_d_sq)
            + d_cubed;
        let y_new = lambda_2_numerator * (x_h_sq_d_sq - x_new) - y_h_cubed * d_cubed;
        let z_new = self.z * h * d;
        let z_new_sq = square_with_runtime_backend(&z_new);

        *self = Self {
            x: x_new,
            y: y_new,
            z: z_new,
            z_sq: z_new_sq,
        };

        DoubleAndAddWitness {
            lambda_1_numerator: r_d,
            lambda_2_numerator,
        }
    }
}
