//! This module provides an implementation of a variant of (Turbo)[PLONK][plonk]
//! that is designed specifically for the polynomial commitment scheme described
//! in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021
//! [plonk]: https://eprint.iacr.org/2019/953

use blake2b_simd::Params as Blake2bParams;
use group::ff::{Field, FromUniformBytes, PrimeField};

use crate::arithmetic::{CurveAffine, best_multiexp};
use crate::poly::{
    Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, PinnedEvaluationDomain,
    Polynomial, ProvingKeyTwiddles, commitment::Params,
};
use crate::transcript::{ChallengeScalar, EncodedChallenge, Transcript};

mod assigned;
mod circuit;
mod error;
mod evaluation;
mod evaluator_schedule;
mod keygen;
mod lookup;
pub(crate) mod permutation;
mod vanishing;

mod prover;
mod verifier;

#[cfg(feature = "unstable-verifier-fingerprint")]
#[cfg_attr(docsrs, doc(cfg(feature = "unstable-verifier-fingerprint")))]
pub mod fingerprint;

pub use assigned::*;
pub use circuit::*;
pub use error::*;
pub use keygen::*;
pub use prover::*;
pub use verifier::*;

use std::{
    any::{Any as StdAny, TypeId},
    io,
    sync::Arc,
};

fn commit_instance<C: CurveAffine>(params: &Params<C>, instance: &[C::Scalar]) -> C::Curve {
    let mut commitment = C::Curve::from(params.w);
    commitment += best_multiexp::<C>(instance, &params.g_lagrange[..instance.len()]);
    commitment
}

fn parallelize_two<A: Send, B: Send>(
    left: &mut [A],
    right: &mut [B],
    f: impl Fn(&mut [A], &mut [B], usize) + Send + Sync + Clone,
) {
    assert_eq!(left.len(), right.len());
    let num_threads = crate::multicore::current_num_threads();
    let mut chunk = left.len() / num_threads;
    if chunk < num_threads {
        chunk = left.len();
    }

    crate::multicore::scope(|scope| {
        for (chunk_num, (left, right)) in left
            .chunks_mut(chunk)
            .zip(right.chunks_mut(chunk))
            .enumerate()
        {
            let f = f.clone();
            scope.spawn(move |_| f(left, right, chunk_num * chunk));
        }
    });
}

/// Builds the prefix products of `numerators[i] / denominators[i]` with one
/// field inversion.
fn prefix_products_of_fractions<F: Field>(
    mut numerators: Vec<F>,
    mut denominators: Vec<F>,
    fraction_rows: usize,
    initial: F,
) -> Vec<F> {
    assert_eq!(numerators.len(), denominators.len());
    assert!(fraction_rows < numerators.len());

    // Compute the inverse of the complete denominator product with two
    // independent multiplication chains. A zero denominator is negligible
    // for challenge-blinded products, but retain the current zero-skipping
    // behavior below for exactness on every input.
    let mut denominator_even = F::ONE;
    let mut denominator_odd = F::ONE;
    let mut pairs = denominators[..fraction_rows].chunks_exact(2);
    for pair in &mut pairs {
        denominator_even *= pair[0];
        denominator_odd *= pair[1];
    }
    if let Some(value) = pairs.remainder().first() {
        denominator_even *= value;
    }

    let denominator_product = denominator_even * denominator_odd;
    if let Some(mut denominator_inverse) = Option::<F>::from(denominator_product.invert()) {
        // First form every numerator prefix. The following reverse walk uses
        // D_i / (D_0 ... D_i) = 1 / (D_0 ... D_{i-1}) to recover the matching
        // denominator prefix without inverting each row separately.
        let mut numerator_prefix = initial;
        for numerator in &mut numerators[..fraction_rows] {
            let current = *numerator;
            *numerator = numerator_prefix;
            numerator_prefix *= current;
        }
        numerators[fraction_rows] = numerator_prefix * denominator_inverse;

        for row in (0..fraction_rows).rev() {
            denominator_inverse *= denominators[row];
            numerators[row] *= denominator_inverse;
        }
    } else {
        // Match `batch_invert_multi` for the vanishingly unlikely case in
        // which a challenge-blinded denominator is zero.
        crate::arithmetic::batch_invert_multi(&mut denominators[..fraction_rows]);
        let mut state = initial;
        for (numerator, denominator_inverse) in numerators[..fraction_rows]
            .iter_mut()
            .zip(&denominators[..fraction_rows])
        {
            let ratio = *numerator * denominator_inverse;
            *numerator = state;
            state *= ratio;
        }
        numerators[fraction_rows] = state;
    }

    numerators
}

#[cfg(test)]
mod prefix_products_of_fractions_tests {
    use super::prefix_products_of_fractions;
    use group::ff::Field;
    use pasta_curves::Fp;

    fn pseudo_random_values(len: usize, mut state: u64) -> Vec<Fp> {
        (0..len)
            .map(|_| {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                Fp::from(state)
            })
            .collect()
    }

    fn reference_prefix_products(
        mut numerators: Vec<Fp>,
        mut denominators: Vec<Fp>,
        fraction_rows: usize,
        initial: Fp,
    ) -> Vec<Fp> {
        crate::arithmetic::batch_invert_multi(&mut denominators[..fraction_rows]);

        let mut state = initial;
        for (numerator, denominator_inverse) in numerators[..fraction_rows]
            .iter_mut()
            .zip(&denominators[..fraction_rows])
        {
            let ratio = *numerator * denominator_inverse;
            *numerator = state;
            state *= ratio;
        }
        numerators[fraction_rows] = state;
        numerators
    }

    #[test]
    fn matches_batch_inversion_for_random_nonzero_products() {
        for fraction_rows in [0, 1, 2, 31, 32, 33, 2_042] {
            let len = fraction_rows + 6;
            let numerators = pseudo_random_values(len, 0x1234_5678_9abc_def0);
            let mut denominators = pseudo_random_values(len, 0xfedc_ba98_7654_3210);
            for denominator in &mut denominators[..fraction_rows] {
                if bool::from(denominator.is_zero()) {
                    *denominator = Fp::ONE;
                }
            }
            let initial = Fp::from(0x0123_4567_89ab_cdef);

            let expected = reference_prefix_products(
                numerators.clone(),
                denominators.clone(),
                fraction_rows,
                initial,
            );
            let actual =
                prefix_products_of_fractions(numerators, denominators, fraction_rows, initial);

            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn zero_denominators_match_zero_skipping_batch_inversion() {
        let fraction_rows = 65;
        let numerators = pseudo_random_values(fraction_rows + 6, 0x3141_5926_5358_9793);
        let base_denominators = pseudo_random_values(fraction_rows + 6, 0x2718_2818_2845_9045);
        let initial = Fp::from(42);

        for zero_rows in [vec![0], vec![32], vec![64], vec![0, 17, 64]] {
            let mut denominators = base_denominators.clone();
            for row in zero_rows {
                denominators[row] = Fp::ZERO;
            }
            let expected = reference_prefix_products(
                numerators.clone(),
                denominators.clone(),
                fraction_rows,
                initial,
            );
            let actual = prefix_products_of_fractions(
                numerators.clone(),
                denominators,
                fraction_rows,
                initial,
            );

            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn zero_numerators_match_the_reference_prefix_chain() {
        let fraction_rows = 65;
        let mut numerators = pseudo_random_values(fraction_rows + 6, 0x0123_4567_89ab_cdef);
        let denominators = pseudo_random_values(fraction_rows + 6, 0xfedc_ba98_7654_3210);
        numerators[0] = Fp::ZERO;
        numerators[32] = Fp::ZERO;
        numerators[64] = Fp::ZERO;
        let initial = Fp::from(42);

        let expected = reference_prefix_products(
            numerators.clone(),
            denominators.clone(),
            fraction_rows,
            initial,
        );
        let actual = prefix_products_of_fractions(numerators, denominators, fraction_rows, initial);

        assert_eq!(actual, expected);
    }

    #[test]
    fn leaves_blinding_rows_untouched() {
        const DOMAIN_ROWS: usize = 2_048;
        const BLINDING_FACTORS: usize = 5;
        const FRACTION_ROWS: usize = DOMAIN_ROWS - (BLINDING_FACTORS + 1);

        let numerators = pseudo_random_values(DOMAIN_ROWS, 0xa5a5_a5a5_5a5a_5a5a);
        let mut denominators = pseudo_random_values(DOMAIN_ROWS, 0x5a5a_5a5a_a5a5_a5a5);
        denominators[DOMAIN_ROWS - 1] = Fp::ZERO;
        let numerator_tail = numerators[FRACTION_ROWS + 1..].to_vec();
        let products =
            prefix_products_of_fractions(numerators, denominators, FRACTION_ROWS, Fp::ONE);

        assert_eq!(&products[FRACTION_ROWS + 1..], &numerator_tail);
    }
}

/// Computes `base^(2^exponent)` using the public exponent directly.
fn pow_by_power_of_two<F: Field + 'static>(base: F, exponent: u32) -> F {
    if TypeId::of::<F>() == TypeId::of::<pasta_curves::Fp>() {
        let value = (&base as &dyn StdAny)
            .downcast_ref::<pasta_curves::Fp>()
            .expect("the field type was checked");
        let result = pasta_curves::arithmetic::square_fp_n(value, exponent);
        return *(&result as &dyn StdAny)
            .downcast_ref::<F>()
            .expect("the field type was checked");
    }
    if TypeId::of::<F>() == TypeId::of::<pasta_curves::Fq>() {
        let value = (&base as &dyn StdAny)
            .downcast_ref::<pasta_curves::Fq>()
            .expect("the field type was checked");
        let result = pasta_curves::arithmetic::square_fq_n(value, exponent);
        return *(&result as &dyn StdAny)
            .downcast_ref::<F>()
            .expect("the field type was checked");
    }

    let mut base = base;
    for _ in 0..exponent {
        base = base.square();
    }
    base
}

#[cfg(test)]
mod power_of_two_tests {
    use super::pow_by_power_of_two;
    use pasta_curves::{Fp, Fq};

    #[test]
    fn matches_repeated_field_squaring() {
        let fp = Fp::from(0x9e37_79b9_7f4a_7c15);
        let fq = Fq::from(0x0123_4567_89ab_cdef);

        for exponent in [0, 1, 2, 11, 64] {
            let expected_fp = (0..exponent).fold(fp, |value, _| value.square());
            let expected_fq = (0..exponent).fold(fq, |value, _| value.square());
            assert_eq!(pow_by_power_of_two(fp, exponent), expected_fp);
            assert_eq!(pow_by_power_of_two(fq, exponent), expected_fq);
        }
    }
}

/// This is a verifying key which allows for the verification of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct VerifyingKey<C: CurveAffine> {
    domain: EvaluationDomain<C::Scalar>,
    fixed_commitments: Vec<C>,
    permutation: permutation::VerifyingKey<C>,
    cs: ConstraintSystem<C::Scalar>,
    /// Cached maximum degree of `cs` (which doesn't change after construction).
    cs_degree: usize,
    /// The representative of this `VerifyingKey` in transcripts.
    transcript_repr: C::Scalar,
}

impl<C: CurveAffine> VerifyingKey<C>
where
    C::Scalar: FromUniformBytes<64>,
{
    fn from_parts(
        domain: EvaluationDomain<C::Scalar>,
        fixed_commitments: Vec<C>,
        permutation: permutation::VerifyingKey<C>,
        cs: ConstraintSystem<C::Scalar>,
    ) -> Self {
        // Compute cached values.
        let cs_degree = cs.degree();

        let mut vk = Self {
            domain,
            fixed_commitments,
            permutation,
            cs,
            cs_degree,
            // Temporary, this is not pinned.
            transcript_repr: C::Scalar::ZERO,
        };

        let mut hasher = Blake2bParams::new()
            .hash_length(64)
            .personal(b"Halo2-Verify-Key")
            .to_state();

        let s = format!("{:?}", vk.pinned());

        hasher.update(&(s.len() as u64).to_le_bytes());
        hasher.update(s.as_bytes());

        // Hash in final Blake2bState
        vk.transcript_repr = C::Scalar::from_uniform_bytes(hasher.finalize().as_array());

        vk
    }
}

impl<C: CurveAffine> VerifyingKey<C> {
    /// Hashes a verification key into a transcript.
    pub fn hash_into<E: EncodedChallenge<C>, T: Transcript<C, E>>(
        &self,
        transcript: &mut T,
    ) -> io::Result<()> {
        transcript.common_scalar(self.transcript_repr)?;

        Ok(())
    }

    /// Obtains a pinned representation of this verification key that contains
    /// the minimal information necessary to reconstruct the verification key.
    pub fn pinned(&self) -> PinnedVerificationKey<'_, C> {
        PinnedVerificationKey {
            base_modulus: C::Base::MODULUS,
            scalar_modulus: C::Scalar::MODULUS,
            domain: self.domain.pinned(),
            fixed_commitments: &self.fixed_commitments,
            permutation: &self.permutation,
            cs: self.cs.pinned(),
        }
    }
}

/// Minimal representation of a verification key that can be used to identify
/// its active contents.
#[allow(dead_code)]
#[derive(Debug)]
pub struct PinnedVerificationKey<'a, C: CurveAffine> {
    base_modulus: &'static str,
    scalar_modulus: &'static str,
    domain: PinnedEvaluationDomain<'a, C::Scalar>,
    cs: PinnedConstraintSystem<'a, C::Scalar>,
    fixed_commitments: &'a Vec<C>,
    permutation: &'a permutation::VerifyingKey<C>,
}
/// This is a proving key which allows for the creation of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct ProvingKey<C: CurveAffine> {
    vk: VerifyingKey<C>,
    l0: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    l_blind: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    l_last: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    fixed_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
    fixed_polys: Vec<Polynomial<C::Scalar, Coeff>>,
    fixed_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    cached_selector_families: Arc<[CachedSelectorFamily<C::Scalar>]>,
    permutation: permutation::ProvingKey<C>,
    /// Kept out of [`VerifyingKey`] so verifier-only users do not pay its
    /// memory cost.
    fft_twiddles: ProvingKeyTwiddles<C::Scalar>,
    /// Circuit-type-erased floor-planning data produced during key generation.
    floor_plan: Option<FloorPlan>,
    /// Bounded, prover-only compiled quotient plans prepared during keygen and
    /// replaced lazily if evaluator-shape validation rejects them.
    quotient_plans: Arc<evaluator_schedule::QuotientPlans<C::Scalar>>,
}

#[derive(Debug)]
struct CachedSelectorFamily<F> {
    // The source entry in `fixed_cosets` stores the selector for root one.
    column_index: usize,
    // The remaining entries correspond to roots two through the family size.
    selectors: Box<[Polynomial<F, ExtendedLagrangeCoeff>]>,
}

impl<C: CurveAffine> ProvingKey<C> {
    /// Get the underlying [`VerifyingKey`].
    pub fn get_vk(&self) -> &VerifyingKey<C> {
        &self.vk
    }
}

impl<C: CurveAffine> VerifyingKey<C> {
    /// Get the underlying [`EvaluationDomain`].
    pub fn get_domain(&self) -> &EvaluationDomain<C::Scalar> {
        &self.domain
    }
}

#[derive(Clone, Copy, Debug)]
struct Theta;
type ChallengeTheta<F> = ChallengeScalar<F, Theta>;

#[derive(Clone, Copy, Debug)]
struct Beta;
type ChallengeBeta<F> = ChallengeScalar<F, Beta>;

#[derive(Clone, Copy, Debug)]
struct Gamma;
type ChallengeGamma<F> = ChallengeScalar<F, Gamma>;

#[derive(Clone, Copy, Debug)]
struct Y;
type ChallengeY<F> = ChallengeScalar<F, Y>;

#[derive(Clone, Copy, Debug)]
struct X;
type ChallengeX<F> = ChallengeScalar<F, X>;
