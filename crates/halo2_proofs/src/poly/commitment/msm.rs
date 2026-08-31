use super::Params;
use crate::arithmetic::{CurveAffine, CurveExt, best_multiexp};
use ff::Field;
use group::Group;

use std::collections::BTreeMap;

/// The widest thread pool on which the prepared verifier zero-check stays
/// engaged. The prepared evaluation stops scaling past this width — its
/// wide-radix codebook has fewer window tasks than the unprepared orbit
/// backend, and under contention its reduction inflates in total work —
/// while the unprepared planner keeps scaling, so on full pools the
/// prepared path measures *slower* despite its large low-thread wins.
/// Measured end-to-end on the Orchard-shaped verifier (k = 11,
/// within-process interleaved cells): armed vs unarmed at 1 action is
/// −22% at 4 threads and −8% at 8 threads (prepared wins), but +15% at
/// 16 threads (Apple M4 Max) and +22–27% at a 32-thread pool
/// (32-hw-thread Skylake-X) — the crossover sits between 8 and 16 on both
/// architectures, on the assembly and portable field backends alike.
#[cfg(any(feature = "multicore", feature = "orbits"))]
pub(crate) const PREPARED_MSM_MAX_THREADS: usize = 8;

type ArbitraryTerm<C> = (
    <C as CurveAffine>::Base,
    (<C as CurveAffine>::ScalarExt, <C as CurveAffine>::Base),
);

#[derive(Clone, Copy, Eq, PartialEq)]
enum ScalarProfile {
    General,
    FullWidth,
}

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
        if let Some((our_x, (our_scalar, our_y))) = canonical.last_mut()
            && *our_x == x
        {
            if *our_y == y {
                *our_scalar += scalar;
            } else {
                assert!(*our_y == -y);
                *our_scalar -= scalar;
            }
            continue;
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

    fn multiexp_terms(self) -> (Vec<C::Scalar>, Vec<C>) {
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

        (scalars, bases)
    }

    fn multiexp(self) -> C::Curve {
        let (scalars, bases) = self.multiexp_terms();
        best_multiexp(&scalars, &bases)
    }

    /// Perform multiexp and check that it results in zero.
    pub fn eval(self) -> bool {
        self.eval_with_profile(ScalarProfile::General)
    }

    /// Evaluates a verifier MSM whose dominant generator-scalar vector is
    /// expected to be random-like and full-width.
    pub(crate) fn eval_full_width(self) -> bool {
        self.eval_with_profile(ScalarProfile::FullWidth)
    }

    #[cfg_attr(not(feature = "orbits"), allow(unused_mut))]
    fn eval_with_profile(mut self, scalar_profile: ScalarProfile) -> bool {
        // A prepared fixed-base zero-check over [g..., w, u] (built by
        // `Params::prepare_zero_checks`, under the opt-in `orbits`
        // feature) evaluates the identity test
        // directly, with the accumulated commitment terms as its extras.
        // The decomposition evaluated here is the same view the
        // `multiexp` fallback below consumes, including the one-shot
        // canonicalization of batch-reduced terms. The prepared check
        // runs the extras as their own planned MSM (concurrent with its
        // fixed windows), so extras-heavy checks — batch verification
        // accumulates dozens of commitment terms per proof — stay ahead
        // far longer than when the extras rode the prepared check's
        // residual tail. They still do not stay ahead forever: once the
        // extras outnumber the fixed bases, folding everything into one
        // planned MSM prices the fixed bases at that larger MSM's
        // (cheaper) marginal per-term cost. End-to-end Ironwood batch
        // validation measures the prepared path ahead or even through
        // extras ≈ 0.75n (32-bundle batches) and behind by ~5% on wide
        // pools at extras ≈ 1.5n (64 bundles); the crossover sits at the
        // fixed-base count itself.
        //
        // The prepared path is also gated on the pool width: past
        // [`PREPARED_MSM_MAX_THREADS`] effective threads the
        // unprepared planner out-scales the prepared evaluation and the
        // armed check measures slower end-to-end (see the constant's
        // docs), so wide pools fall through to the plain multiexp and
        // arming is never a pessimization.
        #[cfg(feature = "orbits")]
        if crate::multicore::current_num_threads() <= PREPARED_MSM_MAX_THREADS
            && let Some(prepared) = self.params.zero_check()
        {
            let n = self.params.n as usize;
            if prepared.terms() == n + super::PREPARED_COMMITMENT_EXTRA_BASES {
                if !self.batched_other.is_empty() {
                    // Canonicalize in place rather than on a clone: the
                    // merged view serves the prepared check's extras, and
                    // if the guard below falls through, `multiexp`
                    // re-canonicalizes the already-canonical buffer, which
                    // is idempotent.
                    let mut combined = std::mem::take(&mut self.batched_other);
                    combined.extend(self.other.iter().map(|(x, values)| (*x, *values)));
                    self.other.clear();
                    self.batched_other = canonicalize_other::<C>(combined);
                }
                let extra: Vec<(C::Scalar, C)> = if self.batched_other.is_empty() {
                    self.other
                        .iter()
                        .map(|(x, (scalar, y))| (*scalar, C::from_xy(*x, *y).unwrap()))
                        .collect()
                } else {
                    self.batched_other
                        .iter()
                        .map(|(x, (scalar, y))| (*scalar, C::from_xy(*x, *y).unwrap()))
                        .collect()
                };
                if extra.len() <= n {
                    let mut fixed =
                        vec![C::Scalar::ZERO; n + super::PREPARED_COMMITMENT_EXTRA_BASES];
                    if let Some(g_scalars) = &self.g_scalars {
                        fixed[..n].copy_from_slice(g_scalars);
                    }
                    if let Some(w_scalar) = self.w_scalar {
                        fixed[n] = w_scalar;
                    }
                    if let Some(u_scalar) = self.u_scalar {
                        fixed[n + 1] = u_scalar;
                    }
                    return prepared.is_zero_with_terms_vartime(&fixed, &extra);
                }
            }
        }

        if scalar_profile == ScalarProfile::General {
            return bool::from(self.multiexp().is_identity());
        }

        let (scalars, bases) = self.multiexp_terms();
        if let Some(is_identity) =
            C::CurveExt::try_multiexp_full_width_is_identity_vartime(&scalars, &bases)
        {
            return is_identity;
        }
        bool::from(best_multiexp(&scalars, &bases).is_identity())
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
    use crate::poly::commitment::{MSM, Params};
    use ff::Field;
    use group::{Curve, Group};
    use pasta_curves::{
        EpAffine, Fp, Fq,
        arithmetic::{CurveAffine, CurveExt},
    };

    fn cancelling_full_width_msm(params: &Params<EpAffine>) -> MSM<'_, EpAffine> {
        let g_scalars = (0..params.n)
            .map(|index| Fq::from(index + 2).invert().unwrap())
            .collect::<Vec<_>>();
        let mut msm = MSM::new(params);
        msm.add_to_g_scalars(&g_scalars);
        let sum = msm.clone().multiexp();
        assert!(!bool::from(sum.is_identity()));
        msm.append_term(-Fq::ONE, sum.to_affine());
        msm
    }

    #[test]
    fn eval_full_width_is_exact() {
        let params = Params::<EpAffine>::new(8);
        let valid = cancelling_full_width_msm(&params);
        assert!(valid.clone().eval_full_width());

        let mut invalid = valid;
        invalid.append_term(Fq::ONE, params.w);
        assert!(!invalid.eval_full_width());
    }

    #[test]
    fn eval_full_width_falls_back_below_glv_threshold() {
        let params = Params::<EpAffine>::new(4);
        let valid = cancelling_full_width_msm(&params);
        let (scalars, bases) = valid.clone().multiexp_terms();
        assert!(
            <<EpAffine as CurveAffine>::CurveExt as CurveExt>::
                try_multiexp_full_width_is_identity_vartime(&scalars, &bases)
                .is_none()
        );
        assert!(valid.clone().eval_full_width());

        let mut invalid = valid;
        invalid.append_term(Fq::ONE, params.w);
        assert!(!invalid.eval_full_width());
    }

    #[test]
    fn msm_arithmetic() {
        // Once plain, once with the prepared fixed-base zero-check armed
        // (arming is a no-op without the `orbits` feature): `eval` must
        // agree either way.
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

    /// Pins the prepared zero-check's fixed-scalar placement: `eval` hands
    /// `g_scalars` to the preparation's first `n` slots and `w`/`u` to the
    /// last two, matching `prepare_zero_checks`' base order, so cancelling
    /// each fixed term against an extra term of the same point must accept
    /// while cancelling against the *wrong* point must reject. Runs
    /// unarmed first and armed second with identical verdicts (without the
    /// `orbits` feature arming is a no-op and both runs take the plain
    /// multiexp).
    #[test]
    fn eval_prepared_fixed_scalar_placement() {
        let params = Params::<EpAffine>::new(4);
        let n = params.n as usize;

        exercise_fixed_scalar_placement(&params, n);
        let armed = params.prepare_zero_checks();
        #[cfg(feature = "orbits")]
        {
            // The guard preconditions of `eval`'s prepared branch: armed,
            // and the preparation covers exactly [g..., w, u]. Every case
            // below keeps its extras count at or below `n`, so each
            // armed `eval` routes through the prepared check whenever the
            // pool is within the prepared thread gate (guaranteed by the
            // capped pool at the end of this test).
            assert!(armed, "Pasta params must arm under the orbits feature");
            let prepared = params.zero_check().expect("armed above");
            assert_eq!(
                prepared.terms(),
                n + super::super::PREPARED_COMMITMENT_EXTRA_BASES
            );
        }
        #[cfg(not(feature = "orbits"))]
        assert!(!armed);
        // Ambient pool first, then two capped pools: one within the
        // prepared thread gate pins the prepared placement itself, and one
        // just past it pins the armed fall-through of `eval` to the plain
        // multiexp — both regardless of the host's width.
        exercise_fixed_scalar_placement(&params, n);
        #[cfg(all(feature = "orbits", feature = "multicore"))]
        for num_threads in [
            super::PREPARED_MSM_MAX_THREADS,
            super::PREPARED_MSM_MAX_THREADS + 1,
        ] {
            maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(num_threads)
                .build()
                .expect("test pool must build")
                .install(|| exercise_fixed_scalar_placement(&params, n));
        }
    }

    fn exercise_fixed_scalar_placement(params: &Params<EpAffine>, n: usize) {
        let s = Fq::from(0xC0FF_EE11);

        // w cancelled against W accepts; against U rejects. Transposing
        // the preparation's last two slots would swap these two verdicts.
        let mut w_ok = MSM::new(params);
        w_ok.add_to_w_scalar(s);
        w_ok.append_term(-s, params.w);
        assert!(w_ok.eval());
        let mut w_swapped = MSM::new(params);
        w_swapped.add_to_w_scalar(s);
        w_swapped.append_term(-s, params.u);
        assert!(!w_swapped.eval());

        // u symmetric.
        let mut u_ok = MSM::new(params);
        u_ok.add_to_u_scalar(s);
        u_ok.append_term(-s, params.u);
        assert!(u_ok.eval());
        let mut u_swapped = MSM::new(params);
        u_swapped.add_to_u_scalar(s);
        u_swapped.append_term(-s, params.w);
        assert!(!u_swapped.eval());

        // g scalars land on their own generators (start and end of the
        // slice, catching any offset).
        let mut g_scalars = vec![Fq::zero(); n];
        g_scalars[0] = Fq::from(3);
        g_scalars[n - 1] = Fq::from(7);
        let mut g_ok = MSM::new(params);
        g_ok.add_to_g_scalars(&g_scalars);
        g_ok.append_term(-g_scalars[0], params.g[0]);
        g_ok.append_term(-g_scalars[n - 1], params.g[n - 1]);
        assert!(g_ok.eval());
        let mut g_off = MSM::new(params);
        let mut perturbed = g_scalars.clone();
        perturbed[0] += Fq::one();
        g_off.add_to_g_scalars(&perturbed);
        g_off.append_term(-g_scalars[0], params.g[0]);
        g_off.append_term(-g_scalars[n - 1], params.g[n - 1]);
        assert!(!g_off.eval());

        // All three fixed parts at once, accumulated through the batched
        // buffer so `eval`'s in-place canonicalization path is covered.
        let mut fixed_part = MSM::new(params);
        fixed_part.add_to_g_scalars(&g_scalars);
        fixed_part.add_to_w_scalar(s);
        fixed_part.add_to_u_scalar(s + s);
        let mut extras_part = MSM::new(params);
        extras_part.append_term(-g_scalars[0], params.g[0]);
        extras_part.append_term(-g_scalars[n - 1], params.g[n - 1]);
        extras_part.append_term(-s, params.w);
        extras_part.append_term(-(s + s), params.u);
        let mut batched = MSM::new(params);
        batched.add_msm_batch(fixed_part);
        batched.add_msm_batch(extras_part);
        let mut broken = batched.clone();
        assert!(batched.eval());
        broken.append_term(Fq::one(), params.g[1]);
        assert!(!broken.eval());
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

    /// Covers the interactions the batch-aggregation test does not reach:
    /// `add_msm` reading a batched source, an MSM evaluating with both the
    /// incremental map and the batched buffer populated, scaling after batch
    /// accumulation, and coalescing that cancels a point's scalar exactly.
    #[test]
    fn batched_msm_interoperates_with_incremental_paths() {
        let params = Params::<EpAffine>::new(4);

        let make_components = || {
            (0..6u64)
                .map(|index| {
                    let mut msm = MSM::new(&params);
                    let g_scalars = (0..params.n)
                        .map(|slot| Fq::from(slot + index + 1))
                        .collect::<Vec<_>>();
                    msm.add_to_g_scalars(&g_scalars);
                    msm.add_to_w_scalar(Fq::from(2 * index + 1));
                    msm.add_to_u_scalar(Fq::from(3 * index + 1));
                    msm.append_term(Fq::from(index + 2), params.g[1]);
                    // The same point in both orientations, with scalars that
                    // cancel exactly once coalesced (three of each).
                    if index % 2 == 0 {
                        msm.append_term(Fq::from(5), params.g[2]);
                    } else {
                        msm.append_term(Fq::from(5), -params.g[2]);
                    }
                    msm.append_term(Fq::from(7 + index), params.g[3 + index as usize]);
                    msm
                })
                .collect::<Vec<_>>()
        };

        fn incremental<'a>(
            params: &'a Params<EpAffine>,
            components: Vec<MSM<'a, EpAffine>>,
        ) -> MSM<'a, EpAffine> {
            let mut acc = MSM::new(params);
            for component in &components {
                acc.add_msm(component);
            }
            acc
        }
        fn batched<'a>(
            params: &'a Params<EpAffine>,
            components: Vec<MSM<'a, EpAffine>>,
        ) -> MSM<'a, EpAffine> {
            let mut acc = MSM::new(params);
            for component in components {
                acc.add_msm_batch(component);
            }
            acc
        }
        let expected = incremental(&params, make_components()).multiexp();

        // `add_msm` must drain a source whose terms live in the batched
        // buffer rather than the incremental map.
        let mut via_add_msm = MSM::new(&params);
        via_add_msm.add_msm(&batched(&params, make_components()));
        assert_eq!(expected, via_add_msm.multiexp());

        // Evaluation must merge both storages when terms were appended after
        // batch accumulation, including a fresh x and a new orientation of an
        // already-batched point.
        let mut mixed = batched(&params, make_components());
        mixed.append_term(Fq::from(23), params.g[4]);
        mixed.append_term(Fq::from(29), -params.g[3]);
        let mut mixed_reference = incremental(&params, make_components());
        mixed_reference.append_term(Fq::from(23), params.g[4]);
        mixed_reference.append_term(Fq::from(29), -params.g[3]);
        assert_eq!(mixed_reference.multiexp(), mixed.multiexp());

        // Scaling must reach the batched buffer.
        let mut scaled = batched(&params, make_components());
        scaled.scale(Fq::from(31));
        let mut scaled_reference = incremental(&params, make_components());
        scaled_reference.scale(Fq::from(31));
        assert_eq!(scaled_reference.multiexp(), scaled.multiexp());

        // The dev-only fingerprint must canonicalize the batched buffer to
        // the exact view the incremental accumulation exports; the insertion
        // order above pins the same first-encountered orientation for both.
        #[cfg(feature = "unstable-verifier-fingerprint")]
        assert_eq!(
            batched(&params, make_components()).fingerprint_terms(),
            incremental(&params, make_components()).fingerprint_terms(),
        );

        // A batch whose only terms cancel exactly still evaluates, and to
        // the identity.
        let mut first = MSM::new(&params);
        first.append_term(Fq::from(21), params.g[1]);
        let mut second = MSM::new(&params);
        second.append_term(Fq::from(21), -params.g[1]);
        let mut cancelled = MSM::new(&params);
        cancelled.add_msm_batch(first);
        cancelled.add_msm_batch(second);
        assert!(cancelled.eval());
    }
}
