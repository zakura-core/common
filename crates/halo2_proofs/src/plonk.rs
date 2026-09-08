//! This module provides an implementation of a variant of (Turbo)[PLONK][plonk]
//! that is designed specifically for the polynomial commitment scheme described
//! in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021
//! [plonk]: https://eprint.iacr.org/2019/953

use blake2b_simd::Params as Blake2bParams;
#[cfg(feature = "batch")]
use ff::WithSmallOrderMulGroup;
use group::ff::{Field, FromUniformBytes, PrimeField};

#[cfg(feature = "batch")]
use crate::PREPARED_INSTANCE_ROWS;
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

/// Builds the prefix products of `numerators[i] / denominators[i]`.
///
/// The common nonzero-denominator path uses one field inversion. A zero
/// denominator causes one failed aggregate inversion and at most one
/// successful inversion of the nonempty prefix before the first zero.
fn prefix_products_of_fractions<F: Field>(
    mut numerators: Vec<F>,
    mut denominators: Vec<F>,
    fraction_rows: usize,
    initial: F,
) -> Vec<F> {
    assert_eq!(numerators.len(), denominators.len());
    assert!(fraction_rows < numerators.len());

    if fraction_rows == 0 {
        numerators[0] = initial;
        return numerators;
    }

    // Build numerator prefixes while the independent denominator product
    // chains are in flight. Starting at row one, store each denominator pair
    // as `[d_low * d_high, d_high]`; this is sufficient to process both rows
    // independently during the reverse walk below.
    let mut numerator_prefix = initial;
    let first_numerator = numerators[0];
    numerators[0] = numerator_prefix;
    numerator_prefix *= first_numerator;

    let mut denominator_even = denominators[0];
    let mut denominator_odd = None;
    let mut pair_count = 0;
    let mut low_row = 1;
    while low_row + 1 < fraction_rows {
        let high_row = low_row + 1;
        let low = denominators[low_row];
        let high = denominators[high_row];
        let pair = low * high;
        pair_count += 1;

        // These challenge-blinded denominators already enter the variable-time
        // inversion below. Retaining `low` when `high` is zero makes this
        // encoding recoverable without any backup allocation.
        if !high.is_zero_vartime() {
            denominators[low_row] = pair;
        }

        let low_numerator = numerators[low_row];
        numerators[low_row] = numerator_prefix;
        numerator_prefix *= low_numerator;
        let high_numerator = numerators[high_row];
        numerators[high_row] = numerator_prefix;
        numerator_prefix *= high_numerator;

        if let Some(denominator_odd) = denominator_odd.as_mut() {
            if pair_count % 2 == 0 {
                denominator_even *= pair;
            } else {
                *denominator_odd *= pair;
            }
        } else {
            denominator_odd = Some(pair);
        }
        low_row += 2;
    }
    if low_row < fraction_rows {
        let numerator = numerators[low_row];
        numerators[low_row] = numerator_prefix;
        numerator_prefix *= numerator;

        if let Some(denominator_odd) = denominator_odd.as_mut() {
            if pair_count % 2 == 0 {
                *denominator_odd *= denominators[low_row];
            } else {
                denominator_even *= denominators[low_row];
            }
        } else {
            denominator_odd = Some(denominators[low_row]);
        }
    }
    let denominator_product = denominator_odd
        .map(|denominator_odd| denominator_even * denominator_odd)
        .unwrap_or(denominator_even);
    numerators[fraction_rows] = numerator_prefix;

    if let Some(denominator_inverse) = Option::<F>::from(denominator_product.invert()) {
        apply_denominator_prefixes(
            &mut numerators,
            &denominators,
            fraction_rows,
            denominator_inverse,
        );
    } else {
        // Find the first original zero while multiplying the encoded factors
        // strictly before it. If a high denominator is zero, its low partner
        // was deliberately retained rather than encoded as a pair product.
        let mut denominator_prefix = F::ONE;
        let mut first_zero = None;
        if denominators[0].is_zero_vartime() {
            first_zero = Some(0);
        } else {
            denominator_prefix = denominators[0];
            for pair_index in 0..pair_count {
                let low_row = 1 + 2 * pair_index;
                let high_row = low_row + 1;
                let low_or_pair = denominators[low_row];
                let high = denominators[high_row];
                if low_or_pair.is_zero_vartime() {
                    first_zero = Some(low_row);
                    break;
                }
                denominator_prefix *= low_or_pair;
                if high.is_zero_vartime() {
                    first_zero = Some(high_row);
                    break;
                }
            }
        }

        let remainder_row = 1 + 2 * pair_count;
        if first_zero.is_none() && remainder_row < fraction_rows {
            if denominators[remainder_row].is_zero_vartime() {
                first_zero = Some(remainder_row);
            } else {
                denominator_prefix *= denominators[remainder_row];
            }
        }

        let first_zero = first_zero.expect("a zero product has a zero factor");
        if first_zero > 0 {
            apply_denominator_prefixes(
                &mut numerators,
                &denominators,
                first_zero,
                denominator_prefix.invert().unwrap(),
            );
        }
        numerators[first_zero + 1..=fraction_rows].fill(F::ZERO);
    }

    numerators
}

fn apply_denominator_prefixes<F: Field>(
    numerators: &mut [F],
    denominators: &[F],
    fraction_rows: usize,
    mut denominator_inverse: F,
) {
    debug_assert!(fraction_rows > 0);
    numerators[fraction_rows] *= denominator_inverse;

    // Handle an unpaired final denominator before walking pairs backward.
    let pair_count = (fraction_rows - 1) / 2;
    let remainder_row = 1 + 2 * pair_count;
    if remainder_row < fraction_rows {
        denominator_inverse *= denominators[remainder_row];
        numerators[remainder_row] *= denominator_inverse;
    }

    for pair_index in (0..pair_count).rev() {
        let low_row = 1 + 2 * pair_index;
        let high_row = low_row + 1;
        let high_inverse = denominator_inverse * denominators[high_row];
        let next_inverse = denominator_inverse * denominators[low_row];
        numerators[high_row] *= high_inverse;
        numerators[low_row] *= next_inverse;
        denominator_inverse = next_inverse;
    }
}

#[cfg(test)]
mod prefix_products_of_fractions_tests {
    use super::prefix_products_of_fractions;
    use group::ff::Field;
    use pasta_curves::Fp;

    const TEST_LCG_MULTIPLIER: u64 = 6_364_136_223_846_793_005;
    const TEST_LCG_INCREMENT: u64 = 1_442_695_040_888_963_407;
    const FULL_FRACTION_ROWS: usize = 2_042;

    fn pseudo_random_values(len: usize, mut state: u64) -> Vec<Fp> {
        (0..len)
            .map(|_| {
                state = state
                    .wrapping_mul(TEST_LCG_MULTIPLIER)
                    .wrapping_add(TEST_LCG_INCREMENT);
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

    fn assert_zero_denominators_match_reference(fraction_rows: usize, zero_rows: &[usize]) {
        let len = fraction_rows + 6;
        let numerators = pseudo_random_values(len, 0x3141_5926_5358_9793);
        let mut denominators = pseudo_random_values(len, 0x2718_2818_2845_9045);
        for row in zero_rows {
            denominators[*row] = Fp::ZERO;
        }
        let initial = Fp::from(42);

        let expected = reference_prefix_products(
            numerators.clone(),
            denominators.clone(),
            fraction_rows,
            initial,
        );
        let actual = prefix_products_of_fractions(numerators, denominators, fraction_rows, initial);

        assert_eq!(actual, expected, "zero rows: {zero_rows:?}");
    }

    #[test]
    fn matches_batch_inversion_for_random_nonzero_products() {
        for fraction_rows in [0, 1, 2, 31, 32, 33, FULL_FRACTION_ROWS] {
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
        const FRACTION_ROWS: usize = 65;

        for row in 0..FRACTION_ROWS {
            assert_zero_denominators_match_reference(FRACTION_ROWS, &[row]);
        }

        // Exercise adjacent zeros and cases where the first zero is in the
        // low or high half of a pair.
        for zero_rows in [
            &[1, 2][..],
            &[1, 18, 33],
            &[2, 3],
            &[2, 17, 34],
            &[0, 17, 64],
        ] {
            assert_zero_denominators_match_reference(FRACTION_ROWS, zero_rows);
        }

        // An even number of fraction rows leaves the final denominator
        // unpaired.
        assert_zero_denominators_match_reference(FRACTION_ROWS + 1, &[FRACTION_ROWS]);
    }

    #[test]
    fn zero_denominator_bitmasks_match_zero_skipping_batch_inversion() {
        for fraction_rows in 0..=8 {
            for zero_mask in 0..(1_usize << fraction_rows) {
                let zero_rows = (0..fraction_rows)
                    .filter(|row| zero_mask & (1 << row) != 0)
                    .collect::<Vec<_>>();
                assert_zero_denominators_match_reference(fraction_rows, &zero_rows);
            }
        }
    }

    #[test]
    fn random_and_full_length_zero_patterns_match_the_reference() {
        let mut state = 0x6a09_e667_f3bc_c909_u64;
        let mut next = || {
            state = state
                .wrapping_mul(TEST_LCG_MULTIPLIER)
                .wrapping_add(TEST_LCG_INCREMENT);
            state
        };

        for _ in 0..32 {
            let fraction_rows = next() as usize % (FULL_FRACTION_ROWS + 1);
            let mut zero_rows = (0..4)
                .filter_map(|_| (fraction_rows > 0).then(|| next() as usize % fraction_rows))
                .collect::<Vec<_>>();
            zero_rows.sort_unstable();
            zero_rows.dedup();
            assert_zero_denominators_match_reference(fraction_rows, &zero_rows);
        }

        for zero_rows in [&[0][..], &[1], &[2], &[1_023, 1_500], &[2_040], &[2_041]] {
            assert_zero_denominators_match_reference(FULL_FRACTION_ROWS, zero_rows);
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
    /// Circuit configuration retained by an opted-in circuit.
    circuit_config: Option<CircuitConfigCache>,
    /// Orchard's public-instance interpolation and extended-coset factor.
    #[cfg(feature = "batch")]
    prepared_instance_coset: Option<Arc<PreparedInstanceCoset<C::Scalar>>>,
    /// Bounded, prover-only compiled quotient plans prepared during keygen and
    /// replaced lazily if evaluator-shape validation rejects them.
    quotient_plans: Arc<evaluator_schedule::QuotientPlans<C::Scalar>>,
}

#[cfg(feature = "batch")]
#[derive(Debug)]
struct PreparedInstanceCoset<F> {
    // Coefficient-major basis for q(X), where the zero-padded instance
    // polynomial is S(X)q(X).
    interpolation: [[F; PREPARED_INSTANCE_ROWS]; PREPARED_INSTANCE_ROWS],
    // Extended-coset evaluations of
    // S(X) = (X^n - 1) / product_{i=0}^{9}(X - omega^i).
    support: Polynomial<F, ExtendedLagrangeCoeff>,
}

#[cfg(feature = "batch")]
impl<F: Field + From<u64>> PreparedInstanceCoset<F> {
    fn new(domain: &EvaluationDomain<F>, twiddles: &ProvingKeyTwiddles<F>, n: u64) -> Self
    where
        F: WithSmallOrderMulGroup<3>,
    {
        let omega = domain.get_omega();
        let roots: [F; PREPARED_INSTANCE_ROWS] =
            std::array::from_fn(|index| omega.pow_vartime([index as u64]));
        let support_divisor = roots.iter().fold(vec![F::ONE], |coefficients, root| {
            multiply_by_linear_factor(&coefficients, *root)
        });

        // The support is independent of instance values, so key generation
        // pays for its full transform once.
        let mut vanishing = vec![F::ZERO; n as usize + 1];
        vanishing[0] = -F::ONE;
        vanishing[n as usize] = F::ONE;
        let mut support = divide_by_monic(&vanishing, &support_divisor);
        support.resize(n as usize, F::ZERO);
        let support =
            domain.coeff_to_extended_with_twiddles(domain.coeff_from_vec(support), twiddles);

        let n_inverse = F::from(n).invert().unwrap();
        let mut interpolation = [[F::ZERO; PREPARED_INSTANCE_ROWS]; PREPARED_INSTANCE_ROWS];
        for (row, root) in roots.iter().enumerate() {
            // The full-domain Lagrange basis is
            //
            // L_i(X) = (root_i / n) (X^n - 1) / (X - root_i).
            //
            // Dividing out the shared support leaves this degree-nine basis
            // for q(X).
            let basis = divide_by_monic_linear(&support_divisor, *root);
            let scale = *root * n_inverse;
            for (coefficient, basis) in interpolation.iter_mut().zip(basis) {
                coefficient[row] = basis * scale;
            }
        }

        Self {
            interpolation,
            support,
        }
    }

    fn evaluate(
        &self,
        values: &[F],
        domain: &EvaluationDomain<F>,
        twiddles: &ProvingKeyTwiddles<F>,
    ) -> Polynomial<F, ExtendedLagrangeCoeff>
    where
        F: WithSmallOrderMulGroup<3>,
    {
        assert_eq!(values.len(), PREPARED_INSTANCE_ROWS);
        let coefficients = self
            .interpolation
            .iter()
            .map(|basis| {
                basis
                    .iter()
                    .zip(values)
                    .fold(F::ZERO, |sum, (basis, value)| sum + *basis * value)
            })
            .collect();
        domain.coeff_prefix_to_extended_with_factor(coefficients, &self.support, twiddles)
    }
}

#[cfg(feature = "batch")]
fn multiply_by_linear_factor<F: Field>(coefficients: &[F], root: F) -> Vec<F> {
    let mut product = vec![F::ZERO; coefficients.len() + 1];
    for (index, coefficient) in coefficients.iter().enumerate() {
        product[index] -= *coefficient * root;
        product[index + 1] += coefficient;
    }
    product
}

#[cfg(feature = "batch")]
fn divide_by_monic<F: Field>(dividend: &[F], divisor: &[F]) -> Vec<F> {
    assert!(!divisor.is_empty());
    assert_eq!(divisor.last(), Some(&F::ONE));
    assert!(dividend.len() >= divisor.len());

    let divisor_degree = divisor.len() - 1;
    let mut remainder = dividend.to_vec();
    let mut quotient = vec![F::ZERO; dividend.len() - divisor_degree];
    for degree in (divisor_degree..dividend.len()).rev() {
        let coefficient = remainder[degree];
        let quotient_index = degree - divisor_degree;
        quotient[quotient_index] = coefficient;
        for (index, divisor) in divisor.iter().enumerate() {
            remainder[quotient_index + index] -= coefficient * divisor;
        }
    }
    debug_assert!(
        remainder[..divisor_degree]
            .iter()
            .all(|coefficient| bool::from(coefficient.is_zero()))
    );
    quotient
}

#[cfg(feature = "batch")]
fn divide_by_monic_linear<F: Field>(dividend: &[F], root: F) -> Vec<F> {
    divide_by_monic(dividend, &[-root, F::ONE])
}

#[cfg(all(test, feature = "batch"))]
mod prepared_instance_coset_tests {
    use std::fmt::Debug;

    use ff::WithSmallOrderMulGroup;
    use pasta_curves::{Fp, Fq};

    use super::{EvaluationDomain, PREPARED_INSTANCE_ROWS, PreparedInstanceCoset};

    const ORCHARD_DEGREE: u32 = 9;

    fn check<F>()
    where
        F: WithSmallOrderMulGroup<3> + From<u64> + Debug + Eq,
    {
        let n = 1 << crate::ORCHARD_K;
        let domain = EvaluationDomain::<F>::new(ORCHARD_DEGREE, crate::ORCHARD_K);
        let twiddles = domain.proving_key_twiddles();
        let prepared = PreparedInstanceCoset::new(&domain, &twiddles, n);
        let pools = [1, 2, 6].map(|threads| {
            maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap()
        });

        let check_values = |values: [F; PREPARED_INSTANCE_ROWS]| {
            let mut lagrange = domain.empty_lagrange();
            lagrange[..][..PREPARED_INSTANCE_ROWS].copy_from_slice(&values);
            let coefficients = domain.lagrange_prefix_to_coeff_with_twiddles(
                lagrange,
                PREPARED_INSTANCE_ROWS,
                &twiddles,
            );
            let expected = domain.coeff_to_extended_with_twiddles(coefficients, &twiddles);
            for pool in &pools {
                let actual = pool.install(|| prepared.evaluate(&values, &domain, &twiddles));
                assert_eq!(actual[..], expected[..]);
            }
        };

        for row in 0..PREPARED_INSTANCE_ROWS {
            let mut values = [F::ZERO; PREPARED_INSTANCE_ROWS];
            values[row] = F::ONE;
            check_values(values);
        }
        check_values(std::array::from_fn(|row| F::from(row as u64 + 1)));
    }

    #[test]
    fn prepared_instance_coset_matches_full_transform() {
        check::<Fp>();
        check::<Fq>();
    }
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
