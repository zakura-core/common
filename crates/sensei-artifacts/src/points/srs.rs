//! The inverse group transform deriving the Lagrange-basis SRS.
//!
//! Over the size-`n` multiplicative subgroup domain, the Lagrange polynomial
//! at `ω^j` has coefficients `L_j(X) = n⁻¹ · Σ_i ω^{−ij} X^i`, so the
//! Lagrange-basis generator is `g_lagrange[j] = n⁻¹ · Σ_i ω^{−ij} · g[i]` —
//! the inverse transform of the coefficient-basis SRS, with point-valued
//! butterflies. The transform itself is `udon::fft` running over
//! `udon`'s trait implementations (vartime, host-side, public data); this
//! module uses the shared domain roots and rejects identity outputs. The
//! prover's digest pins fail closed on any convention slip.

use udon::curve::{VestaAffine, VestaProjective, batch_normalize};
use udon::fft::reference::inverse_transform;

use crate::{Error, domain::inverse_domain};

/// The Lagrange-basis SRS vector derived from the coefficient-basis one by
/// the inverse group transform. Every output must be nonidentity (the pinned
/// SRS has no identity Lagrange generator).
pub(crate) fn lagrange_srs(coefficient_bases: &[VestaAffine]) -> Result<Vec<VestaAffine>, Error> {
    let (root_inverse, size_inverse) = inverse_domain(coefficient_bases.len())?;
    let mut values: Vec<VestaProjective> = coefficient_bases
        .iter()
        .map(VestaProjective::from_affine)
        .collect();
    inverse_transform(&mut values, &root_inverse, &size_inverse);

    {
        let mut output = vec![udon::curve::Point::IDENTITY; values.len()];
        let mut scratch = vec![udon::field::PastaField::ZERO; values.len()];
        batch_normalize(&values, &mut output, &mut scratch);
        output
    }
    .iter()
    .enumerate()
    .map(|(index, point)| {
        point
            .as_affine()
            .copied()
            .ok_or_else(|| Error::new(format!("lagrange SRS generator {index} is the identity")))
    })
    .collect()
}
