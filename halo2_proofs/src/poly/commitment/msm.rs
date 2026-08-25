use super::Params;
use crate::arithmetic::{best_multiexp, CurveAffine};
use ff::Field;
use group::Group;

use std::collections::BTreeMap;

type ArbitraryTerm<C> = (
    <C as CurveAffine>::Base,
    (<C as CurveAffine>::ScalarExt, <C as CurveAffine>::Base),
);

/// A multiscalar multiplication in the polynomial commitment scheme
#[derive(Debug, Clone)]
pub struct MSM<'a, C: CurveAffine> {
    pub(crate) params: &'a Params<C>,
    g_scalars: Option<Vec<C::Scalar>>,
    w_scalar: Option<C::Scalar>,
    u_scalar: Option<C::Scalar>,
    // x-coordinate -> (scalar, y-coordinate)
    other: BTreeMap<C::Base, (C::Scalar, C::Base)>,
    // Batch reduction moves arbitrary terms here and canonicalizes them once
    // before the final multiscalar multiplication.
    batched_other: Vec<ArbitraryTerm<C>>,
}

fn canonicalize_other<C: CurveAffine>(mut terms: Vec<ArbitraryTerm<C>>) -> Vec<ArbitraryTerm<C>> {
    // The stable sort keeps the first-encountered orientation for each
    // x-coordinate. Which orientation that is depends on aggregation order
    // (Rayon's reduction shape is not fixed), but the choice cannot affect
    // the evaluated sum: `(scalar, P)` and `(-scalar, -P)` are the same term,
    // and the coalescing below negates the scalar exactly when the stored
    // orientation differs.
    terms.sort_by(|a, b| a.0.cmp(&b.0));

    let mut canonical = Vec::with_capacity(terms.len());
    for (x, (scalar, y)) in terms {
        if let Some((our_x, (our_scalar, our_y))) = canonical.last_mut() {
            if *our_x == x {
                if *our_y == y {
                    *our_scalar += scalar;
                } else {
                    assert!(*our_y == -y);
                    *our_scalar -= scalar;
                }
                continue;
            }
        }
        canonical.push((x, (scalar, y)));
    }

    canonical
}

impl<'a, C: CurveAffine> MSM<'a, C> {
    /// Create a new, empty MSM using the provided parameters.
    pub fn new(params: &'a Params<C>) -> Self {
        let g_scalars = None;
        let w_scalar = None;
        let u_scalar = None;
        let other = BTreeMap::new();
        let batched_other = vec![];

        MSM {
            params,
            g_scalars,
            w_scalar,
            u_scalar,
            other,
            batched_other,
        }
    }

    fn add_other(&mut self, x: C::Base, scalar: C::Scalar, y: C::Base) {
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

    /// Add another multiexp into this one
    pub fn add_msm(&mut self, other: &Self) {
        for (x, (scalar, y)) in other.other.iter() {
            self.add_other(*x, *scalar, *y);
        }
        for (x, (scalar, y)) in other.batched_other.iter() {
            self.add_other(*x, *scalar, *y);
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

    /// Adds an owned MSM while deferring arbitrary-point coalescing until the
    /// completed batch is evaluated.
    pub(crate) fn add_msm_batch(&mut self, other: Self) {
        let Self {
            g_scalars,
            w_scalar,
            u_scalar,
            other,
            batched_other,
            ..
        } = other;

        self.batched_other
            .reserve(other.len() + batched_other.len());
        self.batched_other.extend(other);
        self.batched_other.extend(batched_other);

        if let Some(g_scalars) = g_scalars {
            if let Some(our_g_scalars) = &mut self.g_scalars {
                assert_eq!(our_g_scalars.len(), g_scalars.len());
                for (our_scalar, scalar) in our_g_scalars.iter_mut().zip(g_scalars) {
                    *our_scalar += scalar;
                }
            } else {
                self.g_scalars = Some(g_scalars);
            }
        }

        if let Some(w_scalar) = w_scalar {
            self.add_to_w_scalar(w_scalar);
        }
        if let Some(u_scalar) = u_scalar {
            self.add_to_u_scalar(u_scalar);
        }
    }

    /// Add arbitrary term (the scalar and the point)
    pub fn append_term(&mut self, scalar: C::Scalar, point: C) {
        if !bool::from(point.is_identity()) {
            let xy = point.coordinates().unwrap();
            let x = *xy.x();
            let y = *xy.y();
            self.add_other(x, scalar, y);
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
        for (_, (scalar, _)) in self.batched_other.iter_mut() {
            *scalar *= factor;
        }

        self.w_scalar = self.w_scalar.map(|a| a * &factor);
        self.u_scalar = self.u_scalar.map(|a| a * &factor);
    }

    fn multiexp(self) -> C::Curve {
        let Self {
            params,
            g_scalars,
            w_scalar,
            u_scalar,
            other,
            mut batched_other,
        } = self;

        let other_len = if batched_other.is_empty() {
            other.len()
        } else {
            batched_other.extend(other.iter().map(|(x, values)| (*x, *values)));
            batched_other = canonicalize_other::<C>(batched_other);
            batched_other.len()
        };
        let len = g_scalars.as_deref().map(<[_]>::len).unwrap_or(0)
            + w_scalar.map(|_| 1).unwrap_or(0)
            + u_scalar.map(|_| 1).unwrap_or(0)
            + other_len;
        let mut scalars: Vec<C::Scalar> = Vec::with_capacity(len);
        let mut bases: Vec<C> = Vec::with_capacity(len);

        if batched_other.is_empty() {
            scalars.extend(other.values().map(|(scalar, _)| *scalar));
            bases.extend(other.iter().map(|(x, (_, y))| C::from_xy(*x, *y).unwrap()));
        } else {
            scalars.extend(batched_other.iter().map(|(_, (scalar, _))| *scalar));
            bases.extend(
                batched_other
                    .iter()
                    .map(|(x, (_, y))| C::from_xy(*x, *y).unwrap()),
            );
        }

        if let Some(w_scalar) = w_scalar {
            scalars.push(w_scalar);
            bases.push(params.w);
        }

        if let Some(u_scalar) = u_scalar {
            scalars.push(u_scalar);
            bases.push(params.u);
        }

        if let Some(g_scalars) = g_scalars {
            scalars.extend(g_scalars);
            bases.extend(params.g.iter());
        }

        assert_eq!(scalars.len(), len);

        best_multiexp(&scalars, &bases)
    }

    /// Perform multiexp and check that it results in zero
    pub fn eval(self) -> bool {
        bool::from(self.multiexp().is_identity())
    }

    /// The MSM's accumulated terms, exposed for capturing the verifier fingerprint without consuming
    /// it: the `g_scalars`, `w_scalar`, `u_scalar`, and the `other` terms as `(scalar, x, y)` for each
    /// accumulated commitment point. This uses the same canonicalization as
    /// [`eval`](Self::eval), so the exported fingerprint cannot drift from the
    /// evaluated view. The owned copies are confined to this dev-only path.
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
        let mut other = self
            .other
            .iter()
            .map(|(x, (scalar, y))| (*scalar, *x, *y))
            .collect::<Vec<_>>();
        if !self.batched_other.is_empty() {
            let mut combined = self.batched_other.clone();
            combined.extend(self.other.iter().map(|(x, values)| (*x, *values)));
            other = canonicalize_other::<C>(combined)
                .into_iter()
                .map(|(x, (scalar, y))| (scalar, x, y))
                .collect();
        }
        (self.g_scalars.clone(), self.w_scalar, self.u_scalar, other)
    }
}

#[cfg(test)]
mod tests {
    use crate::poly::commitment::{Params, MSM};
    use group::Curve;
    use pasta_curves::{arithmetic::CurveAffine, EpAffine, Fp, Fq};

    #[test]
    fn msm_arithmetic() {
        let base = EpAffine::from_xy(-Fp::one(), Fp::from(2)).unwrap();
        let base_viol = (base + base).to_affine();

        let params = Params::new(4);
        let mut a: MSM<EpAffine> = MSM::new(&params);
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

    #[test]
    fn batch_aggregation_matches_incremental_aggregation() {
        let params = Params::<EpAffine>::new(6);
        let mut components = Vec::with_capacity(64);

        for proof in 0..64 {
            let mut msm = MSM::new(&params);
            let g_scalars = (0..params.n)
                .map(|index| Fq::from(u64::from(index) + proof + 1))
                .collect::<Vec<_>>();
            msm.add_to_g_scalars(&g_scalars);
            msm.add_to_w_scalar(Fq::from(proof + 3));
            msm.add_to_u_scalar(Fq::from(proof + 5));

            // Exercise common points, proof-specific points, repeated points,
            // and opposite orientations of the same point.
            msm.append_term(Fq::from(proof + 7), params.g[1]);
            msm.append_term(Fq::from(proof + 11), params.g[2]);
            msm.append_term(Fq::from(proof + 13), -params.g[2]);
            msm.append_term(Fq::from(proof + 17), params.g[3 + proof as usize % 32]);
            if proof % 2 == 0 {
                msm.scale(Fq::from(19));
            }
            components.push(msm);
        }

        let mut incremental = MSM::new(&params);
        for component in &components {
            incremental.add_msm(component);
        }

        let mut batched = MSM::new(&params);
        for component in components.iter().cloned() {
            batched.add_msm_batch(component);
        }

        let expected = incremental.multiexp();
        assert_eq!(expected, batched.multiexp());

        // Match the tree-shaped reduction used by the multicore batch
        // verifier: aggregate proofs into worker-local MSMs, then aggregate
        // the worker results.
        let mut workers = (0..4).map(|_| MSM::new(&params)).collect::<Vec<_>>();
        for (index, component) in components.into_iter().enumerate() {
            workers[index % 4].add_msm_batch(component);
        }
        let mut reduced = MSM::new(&params);
        for worker in workers {
            reduced.add_msm_batch(worker);
        }

        assert_eq!(expected, reduced.multiexp());
    }
}
