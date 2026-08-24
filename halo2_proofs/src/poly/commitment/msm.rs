use super::Params;
use crate::arithmetic::{best_multiexp, CurveAffine};
use ff::Field;
use group::Group;

use std::collections::BTreeMap;

/// A multiscalar multiplication in the polynomial commitment scheme
#[derive(Debug, Clone)]
pub struct MSM<'a, C: CurveAffine> {
    pub(crate) params: &'a Params<C>,
    g_scalars: Option<Vec<C::Scalar>>,
    w_scalar: Option<C::Scalar>,
    u_scalar: Option<C::Scalar>,
    // x-coordinate -> (scalar, y-coordinate)
    other: BTreeMap<C::Base, (C::Scalar, C::Base)>,
}

impl<'a, C: CurveAffine> MSM<'a, C> {
    /// Create a new, empty MSM using the provided parameters.
    pub fn new(params: &'a Params<C>) -> Self {
        let g_scalars = None;
        let w_scalar = None;
        let u_scalar = None;
        let other = BTreeMap::new();

        MSM {
            params,
            g_scalars,
            w_scalar,
            u_scalar,
            other,
        }
    }

    /// Add another multiexp into this one
    pub fn add_msm(&mut self, other: &Self) {
        for (x, (scalar, y)) in other.other.iter() {
            self.other
                .entry(*x)
                .and_modify(|(our_scalar, our_y)| {
                    if our_y == y {
                        *our_scalar += *scalar;
                    } else {
                        assert!(*our_y == -*y);
                        *our_scalar -= *scalar;
                    }
                })
                .or_insert((*scalar, *y));
        }

        if let Some(g_scalars) = &other.g_scalars {
            self.add_to_g_scalars(g_scalars);
        }

        if let Some(w_scalar) = &other.w_scalar {
            self.add_to_w_scalar(*w_scalar);
        }

        if let Some(u_scalar) = &other.u_scalar {
            self.add_to_u_scalar(*u_scalar);
        }
    }

    /// Add arbitrary term (the scalar and the point)
    pub fn append_term(&mut self, scalar: C::Scalar, point: C) {
        if !bool::from(point.is_identity()) {
            let xy = point.coordinates().unwrap();
            let x = *xy.x();
            let y = *xy.y();

            self.other
                .entry(x)
                .and_modify(|(our_scalar, our_y)| {
                    if *our_y == y {
                        *our_scalar += scalar;
                    } else {
                        assert!(*our_y == -y);
                        *our_scalar -= scalar;
                    }
                })
                .or_insert((scalar, y));
        }
    }

    /// Add a value to the first entry of `g_scalars`.
    pub fn add_constant_term(&mut self, constant: C::Scalar) {
        if let Some(g_scalars) = self.g_scalars.as_mut() {
            g_scalars[0] += &constant;
        } else {
            let mut g_scalars = vec![C::Scalar::ZERO; self.params.n as usize];
            g_scalars[0] += &constant;
            self.g_scalars = Some(g_scalars);
        }
    }

    /// Add a vector of scalars to `g_scalars`. This function will panic if the
    /// caller provides a slice of scalars that is not of length `params.n`.
    pub fn add_to_g_scalars(&mut self, scalars: &[C::Scalar]) {
        assert_eq!(scalars.len(), self.params.n as usize);
        if let Some(g_scalars) = &mut self.g_scalars {
            for (g_scalar, scalar) in g_scalars.iter_mut().zip(scalars.iter()) {
                *g_scalar += scalar;
            }
        } else {
            self.g_scalars = Some(scalars.to_vec());
        }
    }

    /// Add to `w_scalar`
    pub fn add_to_w_scalar(&mut self, scalar: C::Scalar) {
        self.w_scalar = self.w_scalar.map_or(Some(scalar), |a| Some(a + &scalar));
    }

    /// Add to `u_scalar`
    pub fn add_to_u_scalar(&mut self, scalar: C::Scalar) {
        self.u_scalar = self.u_scalar.map_or(Some(scalar), |a| Some(a + &scalar));
    }

    /// Scale all scalars in the MSM by some scaling factor
    pub fn scale(&mut self, factor: C::Scalar) {
        if let Some(g_scalars) = &mut self.g_scalars {
            for g_scalar in g_scalars {
                // Verifier construction can leave this vector sparse until
                // the IPA coefficient expansion is added.
                if !bool::from(g_scalar.is_zero()) {
                    *g_scalar *= &factor;
                }
            }
        }

        for other in self.other.values_mut() {
            other.0 *= factor;
        }

        self.w_scalar = self.w_scalar.map(|a| a * &factor);
        self.u_scalar = self.u_scalar.map(|a| a * &factor);
    }

    /// The MSM's accumulated terms as borrowed views over the private fields: the `g_scalars`
    /// (coefficients of the SRS generators `params.g`), `w_scalar` and `u_scalar` (coefficients of
    /// `params.w` and `params.u`), and the `other` map of accumulated commitment terms. This is the
    /// single source of truth for what this MSM represents; both [`eval`](Self::eval) and the
    /// fingerprint export are defined in terms of it, so the exported view cannot drift from the
    /// evaluated one. Returning borrows keeps `eval` — the production verifier hot path — free of the
    /// `O(params.n)` `g_scalars` copy; only the (feature-gated) fingerprint export clones.
    #[allow(clippy::type_complexity)]
    fn terms(
        &self,
    ) -> (
        Option<&[C::Scalar]>,
        Option<C::Scalar>,
        Option<C::Scalar>,
        &BTreeMap<C::Base, (C::Scalar, C::Base)>,
    ) {
        (
            self.g_scalars.as_deref(),
            self.w_scalar,
            self.u_scalar,
            &self.other,
        )
    }

    /// Perform multiexp and check that it results in zero
    pub fn eval(self) -> bool {
        let (g_scalars, w_scalar, u_scalar, other) = self.terms();

        // A prepared fixed-base zero-check over [g..., w, u] (built by
        // `Params::prepare_zero_checks`) evaluates the identity test
        // directly, with the accumulated commitment terms as its extras.
        // The decomposition evaluated here is the same `terms()` view the
        // fallback below consumes. The prepared check runs the extras as
        // their own planned MSM (concurrent with its fixed windows), so
        // extras-heavy checks — batch verification accumulates dozens of
        // commitment terms per proof — stay ahead far longer than when
        // the extras rode the prepared check's residual tail. They still
        // do not stay ahead forever: once the extras outnumber the fixed
        // bases, folding everything into one planned MSM prices the fixed
        // bases at that larger MSM's (cheaper) marginal per-term cost.
        // End-to-end Ironwood batch validation measures the prepared path
        // ahead or even through extras ≈ 0.75n (32-bundle batches) and
        // behind by ~5% on wide pools at extras ≈ 1.5n (64 bundles); the
        // crossover sits at the fixed-base count itself.
        if let Some(prepared) = self.params.zero_check() {
            let n = self.params.n as usize;
            if prepared.terms() == n + 2 && other.len() <= n {
                let mut fixed = vec![C::Scalar::ZERO; n + 2];
                if let Some(g_scalars) = g_scalars {
                    fixed[..n].copy_from_slice(g_scalars);
                }
                if let Some(w_scalar) = w_scalar {
                    fixed[n] = w_scalar;
                }
                if let Some(u_scalar) = u_scalar {
                    fixed[n + 1] = u_scalar;
                }
                let extra: Vec<(C::Scalar, C)> = other
                    .iter()
                    .map(|(x, (scalar, y))| (*scalar, C::from_xy(*x, *y).unwrap()))
                    .collect();
                return prepared.is_zero_with_terms_vartime(&fixed, &extra);
            }
        }

        let len = g_scalars.map(<[_]>::len).unwrap_or(0)
            + w_scalar.map(|_| 1).unwrap_or(0)
            + u_scalar.map(|_| 1).unwrap_or(0)
            + other.len();
        let mut scalars: Vec<C::Scalar> = Vec::with_capacity(len);
        let mut bases: Vec<C> = Vec::with_capacity(len);

        scalars.extend(other.values().map(|(scalar, _)| *scalar));
        bases.extend(other.iter().map(|(x, (_, y))| C::from_xy(*x, *y).unwrap()));

        if let Some(w_scalar) = w_scalar {
            scalars.push(w_scalar);
            bases.push(self.params.w);
        }

        if let Some(u_scalar) = u_scalar {
            scalars.push(u_scalar);
            bases.push(self.params.u);
        }

        if let Some(g_scalars) = g_scalars {
            scalars.extend(g_scalars);
            bases.extend(self.params.g.iter());
        }

        assert_eq!(scalars.len(), len);

        bool::from(best_multiexp(&scalars, &bases).is_identity())
    }

    /// The MSM's accumulated terms, exposed for capturing the verifier fingerprint without consuming
    /// it: the `g_scalars`, `w_scalar`, `u_scalar`, and the `other` terms as `(scalar, x, y)` for each
    /// accumulated commitment point. Built from [`terms`](Self::terms) — the exact decomposition
    /// [`eval`](Self::eval) evaluates — so the exported fingerprint is the evaluated view by
    /// construction. The owned copies here are confined to this dev-only path.
    #[cfg(feature = "unstable-verifier-fingerprint")]
    #[allow(clippy::type_complexity)]
    pub(crate) fn fingerprint_terms(
        &self,
    ) -> (
        Option<Vec<C::Scalar>>,
        Option<C::Scalar>,
        Option<C::Scalar>,
        Vec<(C::Scalar, C::Base, C::Base)>,
    ) {
        let (g_scalars, w_scalar, u_scalar, other) = self.terms();
        let other = other
            .iter()
            .map(|(x, (scalar, y))| (*scalar, *x, *y))
            .collect();
        (g_scalars.map(<[_]>::to_vec), w_scalar, u_scalar, other)
    }
}

#[cfg(test)]
mod tests {
    use crate::poly::commitment::{Params, MSM};
    use group::Curve;
    use pasta_curves::{arithmetic::CurveAffine, EpAffine, Fp, Fq};

    #[test]
    fn msm_arithmetic() {
        // Once plain, once with the prepared fixed-base zero-check armed:
        // `eval` must agree either way.
        let params = Params::new(4);
        exercise_msm_arithmetic(&params);
        params.prepare_zero_checks();
        exercise_msm_arithmetic(&params);
    }

    fn exercise_msm_arithmetic(params: &Params<EpAffine>) {
        let base = EpAffine::from_xy(-Fp::one(), Fp::from(2)).unwrap();
        let base_viol = (base + base).to_affine();

        let mut a: MSM<EpAffine> = MSM::new(params);
        a.append_term(Fq::one(), base);
        // a = [1] P
        assert!(!a.clone().eval());
        a.append_term(Fq::one(), base);
        // a = [1+1] P
        assert!(!a.clone().eval());
        a.append_term(-Fq::one(), base_viol);
        // a = [1+1] P + [-1] 2P
        assert!(a.clone().eval());
        let b = a.clone();

        // Append a point that is the negation of an existing one.
        a.append_term(Fq::from(4), -base);
        // a = [1+1-4] P + [-1] 2P
        assert!(!a.clone().eval());
        a.append_term(Fq::from(2), base_viol);
        // a = [1+1-4] P + [-1+2] 2P
        assert!(a.clone().eval());

        // Add two MSMs with common bases.
        a.scale(Fq::from(3));
        a.add_msm(&b);
        // a = [3*(1+1)+(1+1-4)] P + [3*(-1)+(-1+2)] 2P
        assert!(a.clone().eval());

        let mut c: MSM<EpAffine> = MSM::new(&params);
        c.append_term(Fq::from(2), base);
        c.append_term(Fq::one(), -base_viol);
        // c = [2] P + [1] (-2P)
        assert!(c.clone().eval());
        // Add two MSMs with bases that differ only in sign.
        a.add_msm(&c);
        assert!(a.eval());
    }
}
