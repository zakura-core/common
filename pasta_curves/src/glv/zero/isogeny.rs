//! Batched evaluation of the small-norm endomorphisms $\alpha = 1 - \phi$
//! (degree 3) and $\beta = 1 + \alpha = 2 - \phi$ (degree 7).
//!
//! Both Pasta curves have CM by $\mathbf{Z}[\omega]$; beyond the free unit
//! actions, the cheapest non-unit endomorphisms are $\alpha$ and $\beta$,
//! with eigenvalues $1 - \lambda$ and $2 - \lambda$ on the prime-order
//! group. The prepared zero-check uses these maps for its fixed-base
//! relation scan (detecting bases related by $u$, $u\alpha$, or $u\beta$),
//! and they are the natural generators of the residue-unit subgroups the
//! codebook prepares.
//!
//! $\alpha$ is evaluated by its degree-3 rational map: with $s = 1 - \zeta$
//! (so $s^2 = -3\zeta$) and curve constant $b$,
//!
//! $$\alpha(x, y) = \left(\frac{x^3 + 4b}{s^2 x^2},\;
//!   \frac{y(x^3 - 8b)}{s^3 x^3}\right),$$
//!
//! batched with one shared Montgomery inversion of the $s^3x^3$
//! denominators (the $s^2x^2$ inverse is recovered as $sx \cdot (s^3x^3)^{-1}$).
//! A nonidentity rational point cannot have $x = 0$ — such a point would
//! generate the degree-3 kernel, which meets the prime-order rational group
//! trivially — but malformed inputs are still routed through a projective
//! $P - \phi(P)$ fallback rather than trusted.
//!
//! $\beta$ is evaluated as $P + \alpha(P)$ with a second batched affine
//! addition pass; its denominator $x(\alpha P) - x(P)$ vanishes only when
//! $\alpha(P) = \pm P$, i.e. when $[\lambda]P$ or $[2 - \lambda]P$ is the
//! identity, which again forces $P$ to be the identity.

use alloc::vec::Vec;

use ff::{Field, WithSmallOrderMulGroup};
use group::CurveAffine as _;

use super::super::{batch_invert_nonzero, private, GlvParams};

/// Batched affine $\alpha(P) = P - \phi(P)$. Identity inputs map to the
/// identity; any exceptional input (never a valid nonidentity point) falls
/// back to the projective definition.
pub(crate) fn alpha_affine_batch<C: GlvParams>(points: &[C::AffineExt]) -> Vec<C::AffineExt> {
    let s = C::Base::ONE - C::Base::ZETA;
    let s_squared = s.square();
    let s_cubed = s_squared * s;
    let b4 = C::b().double().double();
    let b8 = b4.double();

    let mut outputs = alloc::vec![C::AffineExt::identity(); points.len()];
    // (input index, x, y, x³) of every regular point.
    #[allow(clippy::type_complexity)]
    let mut regular: Vec<(usize, C::Base, C::Base, C::Base)> = Vec::with_capacity(points.len());
    let mut fallback: Vec<usize> = Vec::new();
    for (index, point) in points.iter().enumerate() {
        if bool::from(point.is_identity()) {
            continue;
        }
        let (x, y) = C::affine_xy(point);
        if bool::from(x.is_zero()) {
            fallback.push(index);
            continue;
        }
        regular.push((index, x, y, x.square() * x));
    }

    let mut denominators: Vec<C::Base> = regular
        .iter()
        .map(|&(_, _, _, x_cubed)| s_cubed * x_cubed)
        .collect();
    let mut scratch = alloc::vec![C::Base::ZERO; denominators.len()];
    if !denominators.is_empty() {
        batch_invert_nonzero(&mut denominators, &mut scratch);
    }
    for (&(index, x, y, x_cubed), inverse) in regular.iter().zip(&denominators) {
        let out_x = (x_cubed + b4) * s * x * inverse;
        let out_y = y * (x_cubed - b8) * inverse;
        outputs[index] = C::affine_unchecked(out_x, out_y, private::CrateToken(()));
    }

    if !fallback.is_empty() {
        let projective: Vec<C> = fallback
            .iter()
            .map(|&index| {
                let p = C::from(points[index]);
                p - p.endo()
            })
            .collect();
        let mut affine = alloc::vec![C::AffineExt::identity(); projective.len()];
        C::batch_normalize(&projective, &mut affine);
        for (&index, &value) in fallback.iter().zip(&affine) {
            outputs[index] = value;
        }
    }
    outputs
}

/// Batched affine $\beta(P) = P + \alpha(P)$. Identity maps to identity;
/// exceptional inputs (never valid nonidentity points) fall back to the
/// projective definition $2P - \phi(P)$.
pub(crate) fn beta_affine_batch<C: GlvParams>(points: &[C::AffineExt]) -> Vec<C::AffineExt> {
    let alphas = alpha_affine_batch::<C>(points);
    let mut outputs = alloc::vec![C::AffineExt::identity(); points.len()];
    // (input index, x, y, xα, yα).
    #[allow(clippy::type_complexity)]
    let mut regular: Vec<(usize, C::Base, C::Base, C::Base, C::Base)> =
        Vec::with_capacity(points.len());
    let mut fallback: Vec<usize> = Vec::new();
    for (index, (point, alpha)) in points.iter().zip(&alphas).enumerate() {
        if bool::from(point.is_identity()) {
            continue;
        }
        let (x, y) = C::affine_xy(point);
        let (ax, ay) = C::affine_xy(alpha);
        if bool::from(alpha.is_identity()) || x == ax {
            fallback.push(index);
            continue;
        }
        regular.push((index, x, y, ax, ay));
    }

    let mut denominators: Vec<C::Base> = regular.iter().map(|&(_, x, _, ax, _)| ax - x).collect();
    let mut scratch = alloc::vec![C::Base::ZERO; denominators.len()];
    if !denominators.is_empty() {
        batch_invert_nonzero(&mut denominators, &mut scratch);
    }
    for (&(index, x, y, ax, ay), inverse) in regular.iter().zip(&denominators) {
        let slope = (ay - y) * inverse;
        let out_x = slope.square() - x - ax;
        let out_y = slope * (x - out_x) - y;
        outputs[index] = C::affine_unchecked(out_x, out_y, private::CrateToken(()));
    }

    if !fallback.is_empty() {
        let projective: Vec<C> = fallback
            .iter()
            .map(|&index| {
                let p = C::from(points[index]);
                p.double() - p.endo()
            })
            .collect();
        let mut affine = alloc::vec![C::AffineExt::identity(); projective.len()];
        C::batch_normalize(&projective, &mut affine);
        for (&index, &value) in fallback.iter().zip(&affine) {
            outputs[index] = value;
        }
    }
    outputs
}

#[cfg(test)]
mod tests {
    use super::super::super::{testutil, GlvParams};
    use super::*;
    use crate::{pallas, vesta};

    fn test_points<C: GlvParams>() -> Vec<C::AffineExt> {
        let generator = C::generator();
        let mut points: Vec<C::AffineExt> = testutil::scalars::<C::ScalarExt>(40)
            .map(|k| (generator * k).to_affine())
            .collect();
        points.push(C::AffineExt::identity());
        points.push(generator.to_affine());
        points.push((-generator).to_affine());
        points
    }

    /// α by the rational map equals P − φ(P) equals [1 − λ]P.
    fn alpha_matches_definitions<C: GlvParams>() {
        let points = test_points::<C>();
        let alphas = alpha_affine_batch::<C>(&points);
        let lambda = C::ScalarExt::ZETA;
        for (point, alpha) in points.iter().zip(&alphas) {
            let p = C::from(*point);
            let expected = p - p.endo();
            assert_eq!(C::from(*alpha), expected, "α must equal P − φ(P)");
            assert_eq!(
                expected,
                p * (C::ScalarExt::ONE - lambda),
                "α must have eigenvalue 1 − λ"
            );
            assert!(bool::from(C::from(*alpha).is_on_curve()));
        }
    }

    /// β = P + α(P) equals 2P − φ(P) equals [2 − λ]P.
    fn beta_matches_definitions<C: GlvParams>() {
        let points = test_points::<C>();
        let betas = beta_affine_batch::<C>(&points);
        let lambda = C::ScalarExt::ZETA;
        for (point, beta) in points.iter().zip(&betas) {
            let p = C::from(*point);
            let expected = p.double() - p.endo();
            assert_eq!(C::from(*beta), expected, "β must equal 2P − φ(P)");
            assert_eq!(
                expected,
                p * (C::ScalarExt::from(2) - lambda),
                "β must have eigenvalue 2 − λ"
            );
        }
    }

    macro_rules! isogeny_tests {
        ($mod_name:ident, $curve:ty) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn alpha() {
                    alpha_matches_definitions::<$curve>();
                }
                #[test]
                fn beta() {
                    beta_matches_definitions::<$curve>();
                }
            }
        };
    }

    isogeny_tests!(pallas_isogeny, pallas::Point);
    isogeny_tests!(vesta_isogeny, vesta::Point);
}
