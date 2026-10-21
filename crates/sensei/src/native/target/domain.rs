//! Domain, boundary, permutation-identity, and instance preparation.
//!
//! Whole impls stay beside their load-time derivations. Shared records remain
//! in the parent so target composition and its independent tests retain their
//! existing private field access.

use alloc::{boxed::Box, sync::Arc, vec::Vec};

use crate::native::field::Fp;
use crate::native::polynomial::{FpCosetTiles, base_coefficients_to_extended_coset_tiles};
use sensei_shared::{EXTENDED_N, INSTANCE_VALUE_COUNT, K, N, USABLE_ROWS_END};

use super::{
    Boundaries, Domain, InstanceBasisRows, PermutationIdentities, PreparedInstance, TargetError,
};

impl PreparedInstance {
    /// The load-time alternative to the embedded artifact, producing the same
    /// values the generator bakes (pinned by the embedded-vs-derived test).
    #[cfg_attr(all(embed_instance_bases, not(test)), allow(dead_code))]
    pub(super) fn derive() -> Result<Self, TargetError> {
        let omega_inverse = <Fp>::root_of_unity_inverse(K).ok_or(TargetError::Malformed)?;
        let size_inverse = <Fp>::power_of_two_inverse(K);
        let mut coefficients = alloc::vec![ [<Fp>::ZERO; INSTANCE_VALUE_COUNT]; N];
        // L_j(X) = N⁻¹ Σ_k (ω⁻ʲ)^k X^k: write each progression directly
        // into the transposed destination, without unit vectors or FFTs.
        let mut step = <Fp>::ONE;
        for row in 0..INSTANCE_VALUE_COUNT {
            let mut value = size_inverse;
            for transposed in &mut coefficients {
                transposed[row] = value;
                value = value.mul(&step);
            }
            step = step.mul(&omega_inverse);
        }
        Self::new(InstanceBasisRows::derived(coefficients, N)?)
    }

    /// Prepares the fixed-support factorization beside the coefficient bases:
    /// `S = (X^N − 1) / H` by exact division (the remainder must vanish),
    /// its extended coset through the ordinary residue transforms, and the
    /// interpolation map `q_j = L_j / S(ω^j)` over the degree-below-`m`
    /// Lagrange basis `L_j` of the populated rows. Single-threaded apart from
    /// the per-residue transforms, so the values are independent of the
    /// worker count.
    pub(super) fn new(coefficients: InstanceBasisRows) -> Result<Self, TargetError> {
        use udon::polynomial::{
            divide_linear_in_place, divide_monic_in_place, vanishing_polynomial,
        };

        let omega = <Fp>::root_of_unity(K).ok_or(TargetError::Malformed)?;
        let mut supported = [<Fp>::ZERO; INSTANCE_VALUE_COUNT];
        let mut point = <Fp>::ONE;
        for row in &mut supported {
            *row = point;
            point = point.mul(&omega);
        }
        // `H`, monic of degree `m`, coefficients low to high.
        let mut vanishing = [<Fp>::ZERO; INSTANCE_VALUE_COUNT + 1];
        vanishing_polynomial(&supported, &mut vanishing).map_err(|_| TargetError::Dimension)?;
        // `S = (X^N − 1) / H`; Udon retains the remainder before the quotient.
        let mut dividend = alloc::vec![ <Fp>::ZERO; N + 1];
        dividend[N] = <Fp>::ONE;
        dividend[0] = <Fp>::ONE.neg();
        let remainder_len =
            divide_monic_in_place(&mut dividend, &vanishing).map_err(|_| TargetError::Malformed)?;
        if dividend[..remainder_len]
            .iter()
            .any(|remainder| !remainder.is_zero())
        {
            return Err(TargetError::Malformed);
        }
        dividend.copy_within(remainder_len.., 0);
        dividend.truncate(dividend.len() - remainder_len);
        dividend.resize(N, <Fp>::ZERO);
        let support_coefficients = dividend;
        let support = base_coefficients_to_extended_coset_tiles(&support_coefficients)
            .ok_or(TargetError::Dimension)?;
        let mut interpolation =
            Box::new([[<Fp>::ZERO; INSTANCE_VALUE_COUNT]; INSTANCE_VALUE_COUNT]);
        let size_inverse = <Fp>::power_of_two_inverse(K);
        for (row, root) in supported.iter().enumerate() {
            let mut numerator = vanishing;
            let remainder_len = divide_linear_in_place(&mut numerator, root);
            let (remainder, numerator) = numerator.split_at(remainder_len);
            if remainder.iter().any(|value| !value.is_zero()) {
                return Err(TargetError::Malformed);
            }
            // S·H = X^N − 1 gives S(r)·H′(r) = N/r at a supported
            // subgroup root r. The inverse interpolation denominator is r/N.
            let scale = root.mul(&size_inverse);
            if numerator.len() != INSTANCE_VALUE_COUNT {
                return Err(TargetError::Dimension);
            }
            for (degree, coefficient) in numerator.iter().enumerate() {
                interpolation[degree][row] = coefficient.mul(&scale);
            }
        }
        Ok(Self {
            coefficients,
            support: Arc::new(support),
            interpolation,
        })
    }

    /// Forms the extended coset as `S · q` from the populated instance
    /// prefix: `q`'s `m` coefficients come from the interpolation map,
    /// evaluated by the short-support residue transforms and multiplied by
    /// the prepared support coset (see [`PreparedInstance`]).
    pub(crate) fn coset(
        &self,
        values: &[Fp],
        fft: &crate::native::polynomial::PreparedFft,
        execution: crate::native::worker::Execution<'_>,
    ) -> Result<FpCosetTiles, TargetError> {
        let values: &[Fp; INSTANCE_VALUE_COUNT] =
            values.try_into().map_err(|_| TargetError::Dimension)?;
        let quotient: [Fp; INSTANCE_VALUE_COUNT] = core::array::from_fn(|degree| {
            <Fp>::sum_of_products(&self.interpolation[degree], values)
        });
        fft.short_product(&quotient, &self.support, execution)
            .ok_or(TargetError::Dimension)
    }

    /// Transposed Lagrange bases for expanding one combined opening prefix.
    pub(crate) fn coefficient_rows(&self) -> &[[Fp; INSTANCE_VALUE_COUNT]] {
        self.coefficients.rows()
    }

    /// Lagrange weights shared by all instance evaluations at one point.
    /// Udon handles exact nodes both inside and outside the populated prefix.
    pub(crate) fn evaluation_weights(
        &self,
        point: &Fp,
    ) -> Result<[Fp; INSTANCE_VALUE_COUNT], TargetError> {
        let mut weights = [Fp::ZERO; INSTANCE_VALUE_COUNT];
        udon::fft::Domain::new(K)
            .map_err(|_| TargetError::Malformed)?
            .subgroup()
            .evaluate_lagrange(
                point,
                0..INSTANCE_VALUE_COUNT,
                &mut weights,
                &mut [Fp::ZERO; INSTANCE_VALUE_COUNT],
            )
            .map_err(|_| TargetError::Malformed)?;
        Ok(weights)
    }
}

impl Domain {
    pub(super) fn derive() -> Result<Self, TargetError> {
        use udon::fft::{Domain as FftDomain, VanishingDivision};

        let omega = <Fp>::root_of_unity(K).ok_or(TargetError::Malformed)?;
        let omega_inverse = <Fp>::root_of_unity_inverse(K).ok_or(TargetError::Malformed)?;
        let extended = FftDomain::new(EXTENDED_N.ilog2()).map_err(|_| TargetError::Malformed)?;
        let coset_generator = <Fp>::ZETA;
        let division = VanishingDivision::new(extended, &coset_generator, N)
            .map_err(|_| TargetError::Malformed)?;
        let mut vanishing_inverses = [<Fp>::ZERO; EXTENDED_N / N];
        division.prepare_factors(&mut vanishing_inverses, &mut [<Fp>::ZERO; EXTENDED_N / N]);
        Ok(Self {
            omega,
            omega_inverse,
            extended_omega: extended.root(),
            coset_generator,
            permutation_delta: <Fp>::DELTA,
            vanishing_inverses,
        })
    }

    pub(crate) fn omega(&self) -> &Fp {
        &self.omega
    }

    pub(crate) fn omega_inverse(&self) -> &Fp {
        &self.omega_inverse
    }

    pub(crate) fn extended_omega(&self) -> &Fp {
        &self.extended_omega
    }

    pub(crate) fn coset_generator(&self) -> &Fp {
        &self.coset_generator
    }

    pub(crate) fn permutation_delta(&self) -> &Fp {
        &self.permutation_delta
    }

    /// Inverses of `x^N - 1` on the extended coset, in natural row order.
    ///
    /// They repeat every `EXTENDED_N / N` rows and depend only on this domain,
    /// so every proof reuses the same preparation.
    pub(crate) fn vanishing_inverses(&self) -> &[Fp; EXTENDED_N / N] {
        &self.vanishing_inverses
    }
}

impl Boundaries {
    /// The load-time alternative to the embedded artifact, producing the same
    /// values the generator bakes (pinned by the embedded-vs-derived test).
    #[cfg_attr(all(embed_boundaries, not(test)), allow(dead_code))]
    pub(super) fn derive() -> Result<Self, TargetError> {
        use udon::fft::{ConstantPrefixExpansion, Domain};

        let mut l_0 = alloc::vec![Fp::ZERO; EXTENDED_N];
        let mut active_rows = alloc::vec![Fp::ZERO; EXTENDED_N];
        ConstantPrefixExpansion::prepare(
            Domain::new(K)
                .map_err(|_| TargetError::Dimension)?
                .subgroup(),
            Domain::new(sensei_shared::EXTENDED_K)
                .map_err(|_| TargetError::Dimension)?
                .coset(),
            &mut l_0,
            &mut active_rows,
        )
        .map_err(|_| TargetError::Dimension)?;
        // L_j(x) = L_0(x * omega_N^-j). One base rotation is eight
        // positions in these natural-order extended samples.
        let rotated = |row: usize, basis: usize| {
            l_0[(row + EXTENDED_N - basis * (EXTENDED_N / N)) % EXTENDED_N]
        };
        let l_last = (0..EXTENDED_N)
            .map(|row| rotated(row, USABLE_ROWS_END))
            .collect();
        for (row, active) in active_rows.iter_mut().enumerate() {
            *active = Fp::ONE;
            for basis in USABLE_ROWS_END..N {
                *active = active.sub(&rotated(row, basis));
            }
        }
        Ok(Self::Derived {
            l_0,
            l_last,
            active_rows,
        })
    }

    pub(crate) fn l_0(&self) -> &[Fp] {
        match self {
            #[cfg(embed_boundaries)]
            Self::Embedded(rows) => &rows[0],
            Self::Derived { l_0, .. } => l_0,
        }
    }

    pub(crate) fn l_last(&self) -> &[Fp] {
        match self {
            #[cfg(embed_boundaries)]
            Self::Embedded(rows) => &rows[1],
            Self::Derived { l_last, .. } => l_last,
        }
    }

    pub(crate) fn active_rows(&self) -> &[Fp] {
        match self {
            #[cfg(embed_boundaries)]
            Self::Embedded(rows) => &rows[2],
            Self::Derived { active_rows, .. } => active_rows,
        }
    }
}

impl PermutationIdentities {
    pub(super) fn derive(values: Vec<[Fp; N]>) -> Result<Self, TargetError> {
        if values.is_empty() {
            return Err(TargetError::Dimension);
        }

        let deltas = values.iter().map(|column| column[0]).collect();

        Ok(Self { values, deltas })
    }

    pub(crate) fn values(&self) -> &[[Fp; N]] {
        &self.values
    }

    pub(crate) fn deltas(&self) -> &[Fp] {
        &self.deltas
    }
}
