use ff::Field;
use rand_core::Rng;

use super::super::{Coeff, Polynomial, evaluate_polynomial_with_powers, power_vector};
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
use super::PREPARED_DEFERRED_IPA_ROUNDS;
use super::{Blind, Params};
#[cfg(feature = "multicore")]
use crate::PreparedSparseCommitments;
use crate::arithmetic::{CurveAffine, CurveExt, best_multiexp, compute_inner_product};
use crate::transcript::{EncodedChallenge, TranscriptWrite};

use group::{Curve, Group};
use pasta_curves::{deferred::DeferredField, pallas, vesta};
use std::any::{Any, TypeId};
use std::io;

/// Samples the sparse polynomial that masks the final folded IPA scalar,
///
/// $$s(X) = \sum_{t=0}^{k-1} \alpha_t (X^{2^t} - x^{2^t}),$$
///
/// returning `(index, coefficient)` pairs in increasing index order over
/// the support $\{0, 1, 2, 4, \ldots, 2^{k-1}\}$. It satisfies $s(x) = 0$
/// for every choice of the $\alpha_t$, and the parent module's HVZK proof
/// shows the scalar it masks is either uniform or publicly zero.
fn sample_ipa_masking_polynomial<F: Field, R: Rng>(k: u32, x: F, rng: &mut R) -> Vec<(usize, F)> {
    let mut constant = F::ZERO;
    let mut coefficients = Vec::with_capacity(k as usize + 1);
    coefficients.push((0, F::ZERO));

    let mut x_power = x; // x^{2^t}, by repeated squaring
    for t in 0..k {
        let alpha = F::random(&mut *rng);
        constant -= alpha * x_power;
        coefficients.push((1 << t, alpha));
        x_power = x_power.square();
    }
    coefficients[0].1 = constant;

    coefficients
}

fn ipa_masking_commitment<C: CurveAffine>(
    coefficients: &[(usize, C::Scalar)],
    blind: Blind<C::Scalar>,
    params: &Params<C>,
) -> C::Curve {
    // A mask on any other support could leave IPA rounds unmasked without
    // failing any later check, so require exactly the constant plus each
    // power-of-two index for these params.
    assert_eq!(coefficients.len(), params.k as usize + 1);
    assert_eq!(coefficients[0].0, 0);
    for (t, (index, _)) in coefficients[1..].iter().enumerate() {
        assert_eq!(*index, 1 << t);
    }

    #[cfg(feature = "multicore")]
    if let Some(commitment) = params.commit_sparse(coefficients, blind) {
        return commitment;
    }

    let mut scalars = Vec::with_capacity(coefficients.len() + 1);
    let mut bases = Vec::with_capacity(coefficients.len() + 1);
    for (index, coefficient) in coefficients {
        scalars.push(*coefficient);
        bases.push(params.g[*index]);
    }
    scalars.push(blind.0);
    bases.push(params.w);

    best_multiexp(&scalars, &bases)
}

fn ipa_round_multiexp<C: CurveAffine>(
    coeffs: &[C::Scalar],
    bases: &[C],
    value: C::Scalar,
    randomness: C::Scalar,
    params: &Params<C>,
    z: C::Scalar,
) -> C::Curve {
    let mut round_coeffs = Vec::with_capacity(coeffs.len() + 2);
    round_coeffs.extend_from_slice(coeffs);
    round_coeffs.extend_from_slice(&[value * z, randomness]);

    let mut round_bases = Vec::with_capacity(bases.len() + 2);
    round_bases.extend_from_slice(bases);
    round_bases.extend_from_slice(&[params.u, params.w]);

    best_multiexp(&round_coeffs, &round_bases)
}

#[derive(Clone, Copy)]
struct IpaRoundTerms<'a, C: CurveAffine> {
    coeffs: &'a [C::Scalar],
    bases: &'a [C],
    value: C::Scalar,
    randomness: C::Scalar,
}

fn ipa_round_multiexps<C: CurveAffine>(
    l: IpaRoundTerms<'_, C>,
    r: IpaRoundTerms<'_, C>,
    params: &Params<C>,
    z: C::Scalar,
) -> (C::Curve, C::Curve) {
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    if let Some(fixed_bases) = params.fixed_base_table() {
        let ((l_body, r_body), (l_auxiliary, r_auxiliary)) = crate::multicore::join(
            || {
                crate::multicore::join(
                    || best_multiexp(l.coeffs, l.bases),
                    || best_multiexp(r.coeffs, r.bases),
                )
            },
            || {
                fixed_bases.multiply_ipa_rounds(
                    l.value * z,
                    l.randomness,
                    r.value * z,
                    r.randomness,
                )
            },
        );
        return (l_body + l_auxiliary, r_body + r_auxiliary);
    }

    crate::multicore::join(
        || ipa_round_multiexp(l.coeffs, l.bases, l.value, l.randomness, params, z),
        || ipa_round_multiexp(r.coeffs, r.bases, r.value, r.randomness, params, z),
    )
}

fn compute_ipa_hi_evaluation_deferred<F: Field + 'static, T: DeferredField + 'static>(
    polynomial: &dyn Any,
    powers: &dyn Any,
    half: usize,
) -> F {
    let polynomial = polynomial
        .downcast_ref::<Vec<T>>()
        .expect("the polynomial field was checked before conversion");
    let powers = powers
        .downcast_ref::<Vec<T>>()
        .expect("the power-vector field was checked before conversion");
    assert_eq!(polynomial.len(), half * 2);
    assert!(powers.len() >= half);
    let result = T::inner_product(&polynomial[half..], &powers[..half]);
    *(&result as &dyn Any)
        .downcast_ref::<F>()
        .expect("the evaluation field matches the polynomial field")
}

fn compute_ipa_hi_evaluation_pasta<F: Field + 'static>(
    polynomial: &dyn Any,
    powers: &dyn Any,
    half: usize,
) -> F {
    if TypeId::of::<F>() == TypeId::of::<pallas::Base>() {
        return compute_ipa_hi_evaluation_deferred::<F, pallas::Base>(polynomial, powers, half);
    }
    if TypeId::of::<F>() == TypeId::of::<vesta::Base>() {
        return compute_ipa_hi_evaluation_deferred::<F, vesta::Base>(polynomial, powers, half);
    }

    // Downcasting the complete owned buffers is safe and avoids per-element
    // type checks in the specialized path.
    let polynomial = polynomial
        .downcast_ref::<Vec<F>>()
        .expect("the polynomial has the expected field");
    let powers = powers
        .downcast_ref::<Vec<F>>()
        .expect("the power vector has the expected field");
    assert_eq!(polynomial.len(), half * 2);
    assert!(powers.len() >= half);
    compute_inner_product(&polynomial[half..], &powers[..half])
}

/// Extends the block weights for `G_lo + challenge * G_hi` without retaining
/// one scalar per generator. Reverse traversal keeps unread weights intact.
#[cfg(all(feature = "multicore", not(feature = "orbits")))]
fn extend_deferred_generator_weights<F: Field>(weights: &mut Vec<F>, challenge: F) {
    let old_len = weights.len();
    weights.resize(2 * old_len, F::ZERO);
    for block in (0..old_len).rev() {
        let weight = weights[block];
        weights[2 * block] = weight;
        weights[2 * block + 1] = weight * challenge;
    }
}

/// Create a polynomial commitment opening proof for the polynomial defined
/// by the coefficients `px`, the blinding factor `blind` used for the
/// polynomial commitment, and the point `x` that the polynomial is
/// evaluated at.
///
/// This function will panic if the provided polynomial is too large with
/// respect to the polynomial commitment parameters.
///
/// **Important:** This function assumes that the provided `transcript` has
/// already seen the common inputs: the polynomial commitment P, the claimed
/// opening v, and the point x. It's probably also nice for the transcript
/// to have seen the elliptic curve description and the URS, if you want to
/// be rigorous.
pub fn create_proof<C: CurveAffine, E: EncodedChallenge<C>, R: Rng, T: TranscriptWrite<C, E>>(
    params: &Params<C>,
    rng: R,
    transcript: &mut T,
    p_poly: &Polynomial<C::Scalar, Coeff>,
    p_blind: Blind<C::Scalar>,
    x_3: C::Scalar,
) -> io::Result<()> {
    assert_eq!(p_poly.len(), params.n as usize);
    let powers = power_vector(x_3, params.n as usize);
    create_proof_with_powers(params, rng, transcript, p_poly, p_blind, x_3, powers)
}

/// Creates an opening proof while reusing the successive powers of `x_3`.
///
/// `powers` must be the length-`params.n` vector produced by [`power_vector`]
/// for `x_3`.
pub(in crate::poly) fn create_proof_with_powers<
    C: CurveAffine,
    E: EncodedChallenge<C>,
    R: Rng,
    T: TranscriptWrite<C, E>,
>(
    params: &Params<C>,
    mut rng: R,
    transcript: &mut T,
    p_poly: &Polynomial<C::Scalar, Coeff>,
    p_blind: Blind<C::Scalar>,
    x_3: C::Scalar,
    powers: Vec<C::Scalar>,
) -> io::Result<()> {
    // We're limited to polynomials of degree n - 1.
    assert_eq!(p_poly.len(), params.n as usize);
    assert_eq!(powers.len(), params.n as usize);

    // Sample a sparse random polynomial with a root at x_3, supported on the
    // constant and power-of-two coefficients. See the parent module's
    // sparse-masking HVZK proof.
    let s_poly = sample_ipa_masking_polynomial(params.k, x_3, &mut rng);
    let s_poly_blind = Blind(C::Scalar::random(&mut rng));

    // Commit the k + 1 mask coefficients and the independent blind.
    let s_poly_commitment = ipa_masking_commitment(&s_poly, s_poly_blind, params).to_affine();
    transcript.write_point(s_poly_commitment)?;

    // Challenge that will ensure that the prover cannot change P but can only
    // witness a random polynomial commitment that agrees with P at x_3, with high
    // probability.
    let xi = *transcript.squeeze_challenge_scalar::<()>();

    // Challenge that ensures that the prover did not interfere with the U term
    // in their commitments.
    let z = *transcript.squeeze_challenge_scalar::<()>();

    // We'll be opening `P' = P - [v] G_0 + [ξ] S` to ensure it has a root at
    // zero.
    let mut p_prime_poly = p_poly.clone();
    for (index, mask) in &s_poly {
        p_prime_poly[*index] += *mask * xi;
    }
    let v = evaluate_polynomial_with_powers(&p_prime_poly, &powers);
    p_prime_poly[0] -= &v;
    let p_prime_blind = s_poly_blind * Blind(xi) + p_blind;

    // This accumulates the synthetic blinding factor `f` starting
    // with the blinding factor for `P'`.
    let mut f = p_prime_blind.0;

    // Initialize the vector `p_prime` as the coefficients of the polynomial.
    let mut p_prime = p_prime_poly.values;
    assert_eq!(p_prime.len(), params.n as usize);

    // At every round, b[i] = b_scale * x_3^i. Keeping that invariant in
    // scalar form avoids materializing and folding the power vector.
    let mut b_scale = C::Scalar::ONE;

    // Subtracting `v` above made the evaluation of `p_prime` at `x_3` zero.
    // Tracking the evaluation through each fold lets one half-evaluation
    // determine both IPA inner products.
    let mut p_prime_at_x_3 = C::Scalar::ZERO;

    // Snapshot the complete prepared context before choosing the symbolic
    // generator representation. A missing table or an unmeasured pool width
    // keeps every round on the existing eager path.
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    let deferred_ipa = params.prepared_deferred_ipa();
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    let mut generator_weights = vec![C::Scalar::ONE];
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    let mut generator_challenges = Vec::with_capacity(PREPARED_DEFERRED_IPA_ROUNDS as usize);

    // The eager path progressively collapses `G'`. The deferred path leaves it
    // empty until all leading folds are materialized together.
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    let mut g_prime = if deferred_ipa.is_some() {
        Vec::new()
    } else {
        params.g.clone()
    };
    #[cfg(any(not(feature = "multicore"), feature = "orbits"))]
    let mut g_prime = params.g.clone();

    // Perform the inner product argument, round by round.
    for j in 0..params.k {
        // Half the length of `p_prime`, `b`, and `G'`.
        let half = 1 << (params.k - j - 1);

        // If P(X) = P_lo(X) + X^half P_hi(X), its tracked evaluation and
        // P_hi(x_3) determine P_lo(x_3). This computes both IPA inner products
        // from one half-sized inner product against the original powers.
        let x_3_to_half = powers[half];
        let p_hi_at_x_3 = compute_ipa_hi_evaluation_pasta::<C::Scalar>(&p_prime, &powers, half);
        let p_lo_at_x_3 = p_prime_at_x_3 - x_3_to_half * p_hi_at_x_3;
        let b_hi_scale = b_scale * x_3_to_half;
        let value_l_j = b_scale * p_hi_at_x_3;
        let value_r_j = b_hi_scale * p_lo_at_x_3;
        let l_j_randomness = C::Scalar::random(&mut rng);
        let r_j_randomness = C::Scalar::random(&mut rng);

        let ordinary_round = || {
            let l_terms = IpaRoundTerms {
                coeffs: &p_prime[half..],
                bases: &g_prime[0..half],
                value: value_l_j,
                randomness: l_j_randomness,
            };
            let r_terms = IpaRoundTerms {
                coeffs: &p_prime[0..half],
                bases: &g_prime[half..],
                value: value_r_j,
                randomness: r_j_randomness,
            };

            // The first eager round can still reuse the coefficient table even
            // when the complete deferred context was unavailable.
            let prepared_round = (j == 0).then(|| {
                params.try_prepared_first_ipa_round(
                    l_terms.coeffs,
                    r_terms.coeffs,
                    l_terms.value * z,
                    l_terms.randomness,
                    r_terms.value * z,
                    r_terms.randomness,
                )
            });
            prepared_round
                .flatten()
                .unwrap_or_else(|| ipa_round_multiexps(l_terms, r_terms, params, z))
        };

        #[cfg(all(feature = "multicore", not(feature = "orbits")))]
        let (l_j, r_j) = if let Some(prepared) = deferred_ipa
            .as_ref()
            .filter(|_| j < PREPARED_DEFERRED_IPA_ROUNDS)
        {
            if j == 0 {
                prepared.first_round(
                    &p_prime[half..],
                    &p_prime[..half],
                    value_l_j * z,
                    l_j_randomness,
                    value_r_j * z,
                    r_j_randomness,
                )
            } else {
                prepared.round(
                    &p_prime,
                    half,
                    &generator_weights,
                    value_l_j * z,
                    l_j_randomness,
                    value_r_j * z,
                    r_j_randomness,
                )
            }
        } else {
            ordinary_round()
        };
        #[cfg(any(not(feature = "multicore"), feature = "orbits"))]
        let (l_j, r_j) = ordinary_round();
        // Normalize the two round points together so they share one field
        // inversion.
        let points = [l_j, r_j];
        let mut affine = [C::identity(); 2];
        C::Curve::batch_normalize(&points, &mut affine);
        let [l_j, r_j] = affine;

        // Feed L and R into the real transcript
        transcript.write_point(l_j)?;
        transcript.write_point(r_j)?;

        let u_j = *transcript.squeeze_challenge_scalar::<()>();
        let u_j_inv = u_j.invert().unwrap(); // TODO, bubble this up

        // Collapse `p_prime`.
        // TODO: parallelize
        #[allow(clippy::assign_op_pattern)]
        for i in 0..half {
            p_prime[i] = p_prime[i] + &(p_prime[i + half] * &u_j_inv);
        }
        p_prime.truncate(half);
        if j + 1 < params.k {
            p_prime_at_x_3 = p_lo_at_x_3 + u_j_inv * p_hi_at_x_3;
            b_scale += b_hi_scale * u_j;
        }

        // Collapse `G'`, or extend the symbolic block weights and materialize
        // all leading folds once the ordinary rounds take over.
        #[cfg(all(feature = "multicore", not(feature = "orbits")))]
        if let Some(prepared) = deferred_ipa
            .as_ref()
            .filter(|_| j < PREPARED_DEFERRED_IPA_ROUNDS)
        {
            extend_deferred_generator_weights(&mut generator_weights, u_j);
            generator_challenges.push(u_j);
            if j + 1 == PREPARED_DEFERRED_IPA_ROUNDS {
                g_prime = prepared
                    .materialize(&generator_weights, &params.g[..half])
                    .unwrap_or_else(|| {
                        // An exotic scalar representation can decline after
                        // the context probe. Replaying the public folds is
                        // slower but preserves the proof exactly.
                        let mut generators = params.g.clone();
                        for &challenge in &generator_challenges {
                            parallel_generator_collapse(&mut generators, challenge);
                            generators.truncate(generators.len() / 2);
                        }
                        generators
                    });
            }
        } else {
            parallel_generator_collapse(&mut g_prime, u_j);
            g_prime.truncate(half);
        }
        #[cfg(any(not(feature = "multicore"), feature = "orbits"))]
        {
            parallel_generator_collapse(&mut g_prime, u_j);
            g_prime.truncate(half);
        }

        // Update randomness (the synthetic blinding factor at the end)
        f += &(l_j_randomness * &u_j_inv);
        f += &(r_j_randomness * &u_j);
    }

    // We have fully collapsed `p_prime`, `b`, `G'`
    assert_eq!(p_prime.len(), 1);
    let c = p_prime[0];

    transcript.write_scalar(c)?;
    transcript.write_scalar(f)?;

    Ok(())
}

fn parallel_generator_collapse<C: CurveAffine>(g: &mut [C], challenge: C::Scalar) {
    let len = g.len() / 2;
    let (g_lo, g_hi) = g.split_at_mut(len);
    let g_hi: &[C] = g_hi;
    let chunk_size = len.div_ceil(crate::multicore::current_num_threads());

    crate::multicore::scope(|scope| {
        for (chunk_index, g_lo) in g_lo.chunks_mut(chunk_size).enumerate() {
            let start = chunk_index * chunk_size;
            scope.spawn(move |_| {
                let g_hi = &g_hi[start..start + g_lo.len()];
                let mut scaled = vec![C::Curve::identity(); g_hi.len()];
                // The Fiat-Shamir challenge is public, so variable-time
                // scalar multiplication is appropriate here.
                <C::Curve as CurveExt>::batch_mul_same_scalar_vartime(
                    g_hi,
                    &challenge,
                    &mut scaled,
                );
                for (scaled, g_lo) in scaled.iter_mut().zip(g_lo.iter()) {
                    *scaled += *g_lo;
                }
                C::Curve::batch_normalize(&scaled, g_lo);
            });
        }
    });
}

#[cfg(test)]
mod tests {
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    use super::super::{
        DEFERRED_IPA_MATERIALIZATION_ODD_MULTIPLES, DEFERRED_IPA_MATERIALIZATION_WNAF_WIDTH,
        DeferredIpaGeneratorTable, PREPARED_DEFERRED_IPA_ROUNDS, ScalarByteOrder,
        deferred_ipa_round_scalars, prepared_deferred_ipa_rounds, scalar_byte_order,
    };
    use super::{
        Params, compute_ipa_hi_evaluation_pasta, ipa_masking_commitment, ipa_round_multiexp,
        parallel_generator_collapse, sample_ipa_masking_polynomial,
    };
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    use super::{create_proof, extend_deferred_generator_weights};
    use crate::arithmetic::{CurveAffine, best_multiexp, compute_inner_product, eval_polynomial};
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    use crate::poly::Polynomial;
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    use crate::poly::commitment::prepared_commitment_max_threads;
    use crate::poly::{EvaluationDomain, commitment::Blind, power_vector};
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    use crate::transcript::{Blake2bWrite, Challenge255, Transcript, TranscriptWrite};
    #[cfg(feature = "multicore")]
    use crate::{PREPARED_SPARSE_COMMITMENT_K, PreparedSparseCommitments};
    use ff::Field;
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    use ff::{FromUniformBytes, PrimeField};
    use group::{Curve, Group};
    use pasta_curves::{pallas, vesta};
    use rand::rng;
    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    use rand::{SeedableRng, rngs::StdRng};
    use std::fmt::Debug;

    fn full_width_scalar<C: CurveAffine>() -> C::Scalar {
        (C::Scalar::from(0x9E37_79B9_7F4A_7C15u64).square()
            + C::Scalar::from(0x0123_4567_89AB_CDEFu64))
        .square()
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    fn prior_signed_radix_digit<C: CurveAffine>(
        bytes: &[u8],
        window: usize,
        little: bool,
    ) -> isize {
        const WIDTH: usize = 6;

        let bit_start = window * WIDTH;
        let live_bits = (C::Scalar::NUM_BITS as usize)
            .saturating_sub(bit_start)
            .min(WIDTH);
        let value =
            DeferredIpaGeneratorTable::<C>::window_value(bytes, bit_start, live_bits, little)
                .unwrap();
        let carry = if bit_start == 0 {
            0
        } else {
            DeferredIpaGeneratorTable::<C>::bit(bytes, bit_start - 1, little).unwrap()
        };
        let radix = 1 << WIDTH;
        if value < radix / 2 {
            (value + carry) as isize
        } else {
            -((radix - value - carry) as isize)
        }
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    fn assert_wnaf_recode<C>()
    where
        C: CurveAffine,
        C::Scalar: FromUniformBytes<64> + Debug,
    {
        let little = match scalar_byte_order::<C::Scalar>() {
            ScalarByteOrder::LittleEndian => true,
            ScalarByteOrder::BigEndian => false,
            ScalarByteOrder::Unsupported => panic!("Pasta scalar byte order is supported"),
        };
        let recode = |scalar: C::Scalar| {
            DeferredIpaGeneratorTable::<C>::wnaf_digits(scalar.to_repr().as_ref(), little)
                .expect("canonical Pasta scalars have a width-seven wNAF")
        };
        assert!(recode(C::Scalar::ZERO).into_iter().all(|digit| digit == 0));
        let positive_max = recode(C::Scalar::from(63));
        assert_eq!(positive_max[0], 63);
        let negative_max = recode(C::Scalar::from(65));
        assert_eq!(negative_max[0], -63);
        assert_eq!(negative_max[7], 1);
        let boundary_carry = recode(C::Scalar::from(127));
        assert_eq!(boundary_carry[0], -1);
        assert_eq!(boundary_carry[7], 1);
        let top_exponent = u64::from(C::Scalar::NUM_BITS - 1);
        let top_carry_scalar = C::Scalar::from(2).pow_vartime([top_exponent]) - C::Scalar::ONE;
        let top_carry = recode(top_carry_scalar);
        assert_eq!(top_carry[0], -1);
        assert_eq!(top_carry[top_exponent as usize], 1);
        assert_eq!(top_carry.iter().filter(|&&digit| digit != 0).count(), 2);
        let full_width = -C::Scalar::ONE;
        let full_width_repr = full_width.to_repr();
        assert_eq!(
            (0..C::Scalar::NUM_BITS as usize).rfind(|&bit| {
                DeferredIpaGeneratorTable::<C>::bit(full_width_repr.as_ref(), bit, little)
                    == Some(1)
            }),
            Some(C::Scalar::NUM_BITS as usize - 1),
        );
        let mut scalars = vec![
            C::Scalar::ZERO,
            C::Scalar::ONE,
            full_width,
            C::Scalar::from(31),
            C::Scalar::from(32),
            C::Scalar::from(33),
            C::Scalar::from(63),
            C::Scalar::from(64),
            C::Scalar::from(65),
            C::Scalar::from(127),
            C::Scalar::from(128),
            C::Scalar::from(129),
            full_width_scalar::<C>(),
        ];
        for exponent in [
            1,
            6,
            7,
            8,
            62,
            63,
            64,
            126,
            127,
            128,
            252,
            253,
            top_exponent,
        ] {
            let power = C::Scalar::from(2).pow_vartime([exponent]);
            scalars.extend([power - C::Scalar::ONE, power, power + C::Scalar::ONE]);
        }
        let mut rng = StdRng::seed_from_u64(0x574e_4146_2d52_4543);
        scalars.extend((0..512).map(|_| C::Scalar::random(&mut rng)));

        for scalar in scalars {
            let repr = scalar.to_repr();
            let digits = recode(scalar);
            let mut reversed = repr.as_ref().to_vec();
            reversed.reverse();
            assert_eq!(
                DeferredIpaGeneratorTable::<C>::wnaf_digits(&reversed, !little)
                    .expect("the reversed representation also recodes"),
                digits,
            );

            let mut reconstructed = C::Scalar::ZERO;
            for &digit in digits.iter().rev() {
                reconstructed = reconstructed.double();
                let magnitude = C::Scalar::from(u64::from(digit.unsigned_abs()));
                if digit > 0 {
                    reconstructed += magnitude;
                } else if digit < 0 {
                    reconstructed -= magnitude;
                }
            }
            assert_eq!(reconstructed, scalar);

            for (bit, &digit) in digits.iter().enumerate() {
                if digit == 0 {
                    continue;
                }
                assert_eq!(digit % 2, if digit > 0 { 1 } else { -1 });
                assert!(
                    usize::from(digit.unsigned_abs())
                        < 2 * DEFERRED_IPA_MATERIALIZATION_ODD_MULTIPLES
                );
                let following = digits
                    .iter()
                    .skip(bit + 1)
                    .take(DEFERRED_IPA_MATERIALIZATION_WNAF_WIDTH - 1);
                assert!(following.into_iter().all(|&digit| digit == 0));
            }
        }
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    fn wnaf_operation_counts<C>()
    where
        C: CurveAffine,
        C::Scalar: FromUniformBytes<64>,
    {
        const BATCHES: usize = 256;
        const PRIOR_WIDTH: usize = 6;

        let little = match scalar_byte_order::<C::Scalar>() {
            ScalarByteOrder::LittleEndian => true,
            ScalarByteOrder::BigEndian => false,
            ScalarByteOrder::Unsupported => panic!("Pasta scalar byte order is supported"),
        };
        let prior_windows = C::Scalar::NUM_BITS as usize / PRIOR_WIDTH + 1;
        let mut prior_additions = 0;
        let mut wnaf_additions = 0;
        let mut wnaf_doublings = 0;
        let mut rng = StdRng::seed_from_u64(0x574e_4146_2d43_4e54);

        for _ in 0..BATCHES {
            let mut scalars = vec![C::Scalar::ONE];
            for _ in 0..PREPARED_DEFERRED_IPA_ROUNDS {
                extend_deferred_generator_weights(&mut scalars, C::Scalar::random(&mut rng));
            }
            let mut top_bit = None;
            for scalar in scalars.into_iter().skip(1) {
                let repr = scalar.to_repr();
                prior_additions += (0..prior_windows)
                    .filter(|&window| {
                        prior_signed_radix_digit::<C>(repr.as_ref(), window, little) != 0
                    })
                    .count();
                let digits =
                    DeferredIpaGeneratorTable::<C>::wnaf_digits(repr.as_ref(), little).unwrap();
                wnaf_additions += digits.iter().filter(|&&digit| digit != 0).count();
                top_bit = top_bit.max(digits.iter().rposition(|&digit| digit != 0));
            }
            wnaf_doublings += top_bit.unwrap_or(0);
        }

        let prior_doublings = BATCHES * (prior_windows - 1) * PRIOR_WIDTH;
        eprintln!(
            "{}: prior additions {prior_additions}, wNAF additions \
             {wnaf_additions}, prior doublings {prior_doublings}, wNAF \
             doublings {wnaf_doublings}",
            core::any::type_name::<C>(),
        );
        assert!(wnaf_additions * 5 < prior_additions * 4);
        assert!(wnaf_doublings <= prior_doublings + 3 * BATCHES);
    }

    fn round_multiexp_matches_split<C>()
    where
        C: CurveAffine + core::fmt::Debug,
    {
        let params = Params::<C>::new(3);
        let full_width = full_width_scalar::<C>();
        let coeffs = [
            C::Scalar::ZERO,
            C::Scalar::ONE,
            -C::Scalar::ONE,
            C::Scalar::from(2),
            full_width,
        ];
        let bases = &params.g[..coeffs.len()];

        for (value, randomness, z) in [
            (C::Scalar::ZERO, C::Scalar::ZERO, C::Scalar::ZERO),
            (C::Scalar::ONE, -C::Scalar::ONE, C::Scalar::from(2)),
            (full_width, full_width.square(), -C::Scalar::ONE),
        ] {
            let expected = best_multiexp(&coeffs, bases)
                + best_multiexp(&[value * z, randomness], &[params.u, params.w]);
            assert_eq!(
                ipa_round_multiexp(&coeffs, bases, value, randomness, &params, z),
                expected,
            );
        }
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    fn prepared_first_round_matches_ordinary<C>()
    where
        C: CurveAffine + core::fmt::Debug,
    {
        const K: u32 = 6;

        let params = Params::<C>::new(K);
        let half = 1 << (K - 1);
        let mut scalar = full_width_scalar::<C>();
        let coefficients = (0..2 * half)
            .map(|index| {
                scalar = scalar.square() + C::Scalar::from(index as u64 + 1);
                scalar
            })
            .collect::<Vec<_>>();
        let (p_lo, p_hi) = coefficients.split_at(half);
        let l_value = scalar.square() + C::Scalar::from(71);
        let l_randomness = l_value.square() + C::Scalar::from(73);
        let r_value = l_randomness.square() + C::Scalar::from(79);
        let r_randomness = r_value.square() + C::Scalar::from(83);
        let z = r_randomness.square() + C::Scalar::from(89);

        let unprepared_pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();
        unprepared_pool.install(|| {
            assert!(
                params
                    .try_prepared_first_ipa_round(
                        p_hi,
                        p_lo,
                        l_value * z,
                        l_randomness,
                        r_value * z,
                        r_randomness,
                    )
                    .is_none()
            );
        });

        assert!(params.prepare_commitments());
        for workers in [1, 4] {
            let pool = maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(workers)
                .build()
                .unwrap();
            pool.install(|| {
                let expected_l =
                    ipa_round_multiexp(p_hi, &params.g[..half], l_value, l_randomness, &params, z);
                let expected_r =
                    ipa_round_multiexp(p_lo, &params.g[half..], r_value, r_randomness, &params, z);
                let (actual_l, actual_r) = params
                    .try_prepared_first_ipa_round(
                        p_hi,
                        p_lo,
                        l_value * z,
                        l_randomness,
                        r_value * z,
                        r_randomness,
                    )
                    .unwrap();
                assert_eq!(actual_l, expected_l);
                assert_eq!(actual_r, expected_r);
            });
        }

        #[cfg(feature = "multicore")]
        maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(prepared_commitment_max_threads(K) + 1)
            .build()
            .unwrap()
            .install(|| {
                assert!(
                    params
                        .try_prepared_first_ipa_round(
                            p_hi,
                            p_lo,
                            l_value * z,
                            l_randomness,
                            r_value * z,
                            r_randomness,
                        )
                        .is_none()
                );
            });
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    fn prepared_first_round_preserves_opening_proof<C>()
    where
        C: CurveAffine,
        C::Scalar: FromUniformBytes<64>,
    {
        const K: u32 = 6;
        const PROOF_SEED: u64 = 0x4950_412d_524f_554e;

        let params = Params::<C>::new(K);
        let polynomial = Polynomial::from_coefficients(
            (0..1 << K)
                .map(|index| C::Scalar::from(index as u64 + 1))
                .collect(),
        );
        let blind = Blind(C::Scalar::from(17));
        let create_seeded_proof = || {
            let commitment = params.commit(&polynomial, blind).to_affine();
            let mut transcript = Blake2bWrite::<Vec<u8>, C, Challenge255<C>>::init(vec![]);
            transcript.write_point(commitment).unwrap();
            let x = *transcript.squeeze_challenge_scalar::<()>();
            transcript
                .write_scalar(eval_polynomial(&polynomial, x))
                .unwrap();
            create_proof(
                &params,
                StdRng::seed_from_u64(PROOF_SEED),
                &mut transcript,
                &polynomial,
                blind,
                x,
            )
            .unwrap();
            transcript.finalize()
        };
        let narrow_pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();

        let unprepared = narrow_pool.install(create_seeded_proof);
        assert!(params.prepare_commitments());
        let prepared = narrow_pool.install(create_seeded_proof);
        assert_eq!(prepared, unprepared);

        #[cfg(feature = "multicore")]
        {
            let wide_pool = maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(prepared_commitment_max_threads(K) + 1)
                .build()
                .unwrap();
            let gated_fallback = wide_pool.install(create_seeded_proof);
            assert_eq!(gated_fallback, unprepared);
        }
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    fn deferred_round_scalars_match_eager<C>()
    where
        C: CurveAffine + Debug,
    {
        const K: u32 = 6;

        let params = Params::<C>::new(K);
        let mut coefficient = full_width_scalar::<C>();
        let mut p_prime = (0..1 << K)
            .map(|index| {
                coefficient = coefficient.square() + C::Scalar::from(index as u64 + 1);
                coefficient
            })
            .collect::<Vec<_>>();
        let mut g_prime = params.g.clone();
        let mut weights = vec![C::Scalar::ONE];
        let challenges = [
            C::Scalar::ONE,
            -C::Scalar::ONE,
            C::Scalar::from(2),
            full_width_scalar::<C>(),
        ];

        for challenge in challenges {
            let half = p_prime.len() / 2;
            let l_scalars = deferred_ipa_round_scalars(&p_prime, half, &weights, false);
            let r_scalars = deferred_ipa_round_scalars(&p_prime, half, &weights, true);
            assert_eq!(
                best_multiexp(&l_scalars, &params.g),
                best_multiexp(&p_prime[half..], &g_prime[..half]),
            );
            assert_eq!(
                best_multiexp(&r_scalars, &params.g),
                best_multiexp(&p_prime[..half], &g_prime[half..]),
            );

            let challenge_inverse = challenge.invert().unwrap();
            for index in 0..half {
                let high = p_prime[index + half];
                p_prime[index] += high * challenge_inverse;
            }
            p_prime.truncate(half);
            parallel_generator_collapse(&mut g_prime, challenge);
            g_prime.truncate(half);
            extend_deferred_generator_weights(&mut weights, challenge);
        }
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    fn deferred_materialization_matches_native<C>()
    where
        C: CurveAffine + Debug,
    {
        const K: u32 = 8;

        let params = Params::<C>::new(K);
        let mut table = DeferredIpaGeneratorTable::new(&params.g)
            .expect("Pasta scalar encodings support deferred materialization");
        let count = params.g.len() >> PREPARED_DEFERRED_IPA_ROUNDS;
        let power = C::Scalar::from(2).pow_vartime([60]);
        let top = C::Scalar::from(2)
            .pow_vartime([u64::from(C::Scalar::NUM_BITS.checked_sub(1).unwrap())]);
        let scalars = [
            C::Scalar::ONE,
            C::Scalar::ZERO,
            -C::Scalar::ONE,
            C::Scalar::from(63),
            C::Scalar::from(64),
            C::Scalar::from(65),
            C::Scalar::from(127),
            C::Scalar::from(128),
            C::Scalar::from(129),
            power - C::Scalar::ONE,
            power,
            power + C::Scalar::ONE,
            top - C::Scalar::ONE,
            top,
            top + C::Scalar::ONE,
            full_width_scalar::<C>(),
        ];
        let assert_materialization = |scalars: &[C::Scalar]| {
            let actual = table
                .materialize(scalars, &params.g[..count])
                .expect("canonical Pasta scalars must materialize");
            for (lane, actual) in actual.iter().enumerate() {
                let bases = (0..scalars.len())
                    .map(|block| params.g[block * count + lane])
                    .collect::<Vec<_>>();
                assert_eq!(actual.to_curve(), best_multiexp(scalars, &bases));
            }
        };
        assert_materialization(&scalars);

        let mut scalar_one_only = [C::Scalar::ZERO; 1 << PREPARED_DEFERRED_IPA_ROUNDS];
        scalar_one_only[0] = C::Scalar::ONE;
        assert_eq!(
            table
                .materialize(&scalar_one_only, &params.g[..count])
                .expect("all-zero cached blocks must materialize"),
            params.g[..count],
        );

        let mut dense = [C::Scalar::ZERO; 1 << PREPARED_DEFERRED_IPA_ROUNDS];
        dense[0] = C::Scalar::ONE;
        let mut rng = StdRng::seed_from_u64(0x574e_4146_2d44_454e);
        for scalar in &mut dense[1..] {
            *scalar = C::Scalar::random(&mut rng);
        }
        assert_materialization(&dense);
        assert_eq!(
            table.retained_bytes(),
            (params.g.len() - count)
                * DEFERRED_IPA_MATERIALIZATION_ODD_MULTIPLES
                * core::mem::size_of::<C>(),
        );

        let challenges = [
            C::Scalar::from(3),
            C::Scalar::from(5),
            -C::Scalar::ONE,
            full_width_scalar::<C>(),
        ];
        let mut weights = vec![C::Scalar::ONE];
        let mut eager = params.g.clone();
        for challenge in challenges {
            extend_deferred_generator_weights(&mut weights, challenge);
            parallel_generator_collapse(&mut eager, challenge);
            eager.truncate(eager.len() / 2);
        }
        assert_eq!(
            table
                .materialize(&weights, &params.g[..count])
                .expect("structured fold weights must materialize"),
            eager,
        );

        table.byte_order = ScalarByteOrder::Unsupported;
        assert!(table.materialize(&weights, &params.g[..count]).is_none());
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    fn prepared_deferred_rounds_preserve_opening_proof<C>()
    where
        C: CurveAffine,
        C::Scalar: FromUniformBytes<64>,
    {
        const K: u32 = 11;
        const PROOF_SEED: u64 = 0x6465_6665_7272_6564;

        let params = Params::<C>::new(K);
        let polynomial = Polynomial::from_coefficients(
            (0..1 << K)
                .map(|index| C::Scalar::from((index as u64).wrapping_mul(17).wrapping_add(3)))
                .collect(),
        );
        let blind = Blind(C::Scalar::from(23));
        let create_seeded_proof = || {
            let commitment = params.commit(&polynomial, blind).to_affine();
            let mut transcript = Blake2bWrite::<Vec<u8>, C, Challenge255<C>>::init(vec![]);
            transcript.write_point(commitment).unwrap();
            let x = *transcript.squeeze_challenge_scalar::<()>();
            transcript
                .write_scalar(eval_polynomial(&polynomial, x))
                .unwrap();
            create_proof(
                &params,
                StdRng::seed_from_u64(PROOF_SEED),
                &mut transcript,
                &polynomial,
                blind,
                x,
            )
            .unwrap();
            transcript.finalize()
        };
        let narrow_pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();

        assert!(narrow_pool.install(|| params.prepared_deferred_ipa().is_none()));
        let unprepared = narrow_pool.install(create_seeded_proof);
        let mut serialized_before = vec![];
        params.write(&mut serialized_before).unwrap();
        assert!(
            maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(4)
                .build()
                .unwrap()
                .install(|| params.prepare_commitments())
        );

        let table = params
            .commitment_tables_cache
            .deferred_ipa()
            .expect("k = 11 preparation retains the materialization table");
        assert_eq!(table.retained_bytes(), 3_932_160);
        let cloned_table = params
            .clone()
            .commitment_tables_cache
            .deferred_ipa()
            .expect("params clones share the materialization table");
        assert!(std::sync::Arc::ptr_eq(&table, &cloned_table));
        let mut serialized_after = vec![];
        params.write(&mut serialized_after).unwrap();
        assert_eq!(serialized_after, serialized_before);
        let deserialized = Params::<C>::read(&mut serialized_before.as_slice()).unwrap();
        assert!(
            deserialized
                .commitment_tables_cache
                .deferred_ipa()
                .is_none()
        );

        table.set_force_decline(true);
        let replay_fallback = narrow_pool.install(|| {
            assert!(params.prepared_deferred_ipa().is_some());
            create_seeded_proof()
        });
        table.set_force_decline(false);
        assert_eq!(replay_fallback, unprepared);

        let max_threads = prepared_commitment_max_threads(K);
        for workers in [1, max_threads] {
            let pool = maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(workers)
                .build()
                .unwrap();
            let prepared = pool.install(|| {
                assert!(params.prepared_deferred_ipa().is_some());
                create_seeded_proof()
            });
            assert_eq!(prepared, unprepared);
        }

        let wide_pool = maybe_rayon::ThreadPoolBuilder::new()
            .num_threads(max_threads + 1)
            .build()
            .unwrap();
        let gated_fallback = wide_pool.install(|| {
            assert!(params.prepared_deferred_ipa().is_none());
            create_seeded_proof()
        });
        assert_eq!(gated_fallback, unprepared);
    }

    fn masking_polynomial_is_sparse_and_commits_correctly<C>()
    where
        C: CurveAffine + core::fmt::Debug,
    {
        for k in [1u32, 6, 11] {
            let params = Params::<C>::new(k);
            let domain = EvaluationDomain::new(1, k);
            let x = full_width_scalar::<C>();
            let mut rng = rng();
            let coefficients = sample_ipa_masking_polynomial(k, x, &mut rng);

            let expected_support: Vec<usize> =
                core::iter::once(0).chain((0..k).map(|t| 1 << t)).collect();
            assert_eq!(
                coefficients
                    .iter()
                    .map(|(index, _)| *index)
                    .collect::<Vec<_>>(),
                expected_support,
            );

            let mut full = domain.empty_coeff();
            for (index, coefficient) in &coefficients {
                full[*index] = *coefficient;
            }
            assert_eq!(eval_polynomial(&full, x), C::Scalar::ZERO);

            let blind = Blind(C::Scalar::random(&mut rng));
            assert_eq!(
                ipa_masking_commitment(&coefficients, blind, &params),
                params.commit(&full, blind),
            );
            #[cfg(feature = "multicore")]
            if k == PREPARED_SPARSE_COMMITMENT_K {
                assert!(params.prepare_sparse_commitment());
                assert_eq!(
                    ipa_masking_commitment(&coefficients, blind, &params),
                    params.commit(&full, blind),
                );
            }
        }
    }

    /// Apply the prover's IPA collapse to the coefficient vector `s` and
    /// return the fully folded scalar.
    fn collapsed_scalar<F: Field>(mut s: Vec<F>, challenges: &[F]) -> F {
        let mut len = s.len();
        for u_j in challenges {
            let u_j_inv = u_j.invert().unwrap();
            let half = len / 2;
            for i in 0..half {
                let hi = s[i + half];
                s[i] += hi * u_j_inv;
            }
            len = half;
        }
        s[0]
    }

    fn masking_basis_detects_every_non_evaluation_fold<C>()
    where
        C: CurveAffine + core::fmt::Debug,
    {
        const K: u32 = 8;
        let n = 1usize << K;
        let x = full_width_scalar::<C>();
        let mut rng = rng();

        // The challenge pattern that selects the parent module's zero case:
        // u_{k-1-t} = x^{-2^t} for every t.
        let mut zero_case = vec![C::Scalar::ZERO; K as usize];
        let mut x_power = x;
        for t in 0..K as usize {
            zero_case[K as usize - 1 - t] = x_power.invert().unwrap();
            x_power = x_power.square();
        }

        // Under that pattern the collapse is the public evaluation
        // functional at x — the parent module's product formula — pinned
        // here on a dense random polynomial to anchor `collapsed_scalar`
        // against an independent evaluation.
        let dense: Vec<C::Scalar> = (0..n).map(|_| C::Scalar::random(&mut rng)).collect();
        assert_eq!(
            collapsed_scalar(dense.clone(), &zero_case),
            eval_polynomial(&dense, x),
        );

        // The sampled mask is a linear combination of the basis vectors
        // s_t(X) = X^{2^t} - x^{2^t}, and each basis vector folds to the
        // linear-functional coefficient u_{k-1-t}^{-1} - x^{2^t} from the
        // parent module. Check deterministically that this coefficient is
        // zero under the zero-case pattern and nonzero the moment the one
        // challenge controlling index 2^t deviates: the functional's
        // coefficients all vanish exactly in the zero case, so the folded
        // mask is uniform whenever any challenge deviates. A
        // prefix-supported mask has no basis vector at large 2^t, so
        // early-round deviations go undetected there.
        let two = C::Scalar::from(2);
        let mut x_power = x;
        for t in 0..K as usize {
            let mut basis_mask = vec![C::Scalar::ZERO; n];
            basis_mask[0] = -x_power;
            basis_mask[1 << t] = C::Scalar::ONE;

            assert_eq!(
                collapsed_scalar(basis_mask.clone(), &zero_case),
                C::Scalar::ZERO,
            );

            // Deviate deterministically in the one challenge controlling
            // index 2^t.
            let j = K as usize - 1 - t;
            let mut challenges = zero_case.clone();
            challenges[j] *= two;

            let expected = challenges[j].invert().unwrap() - x_power;
            assert_ne!(expected, C::Scalar::ZERO);
            assert_eq!(collapsed_scalar(basis_mask, &challenges), expected);

            x_power = x_power.square();
        }
    }

    fn generator_collapse_matches_native<C>()
    where
        C: CurveAffine + core::fmt::Debug,
    {
        let points: Vec<C> = (0..16)
            .map(|i| {
                if i == 3 || i == 12 {
                    C::identity()
                } else {
                    C::from(C::Curve::generator() * C::Scalar::from(i as u64 + 1))
                }
            })
            .collect();
        let full_width = full_width_scalar::<C>();
        let challenges = [
            C::Scalar::ZERO,
            C::Scalar::ONE,
            -C::Scalar::ONE,
            C::Scalar::from(2),
            full_width,
        ];

        for challenge in challenges {
            let half = points.len() / 2;
            let expected_projective: Vec<C::Curve> = points[..half]
                .iter()
                .zip(points[half..].iter())
                .map(|(g_lo, g_hi)| g_lo.to_curve() + (*g_hi * challenge))
                .collect();
            let mut expected = vec![C::identity(); half];
            C::Curve::batch_normalize(&expected_projective, &mut expected);

            let mut actual = points.clone();
            parallel_generator_collapse(&mut actual, challenge);
            assert_eq!(&actual[..half], expected);
        }
    }

    fn deferred_hi_evaluation_matches_eager<F: Field + From<u64> + 'static>() {
        for half in [1, 2, 3, 31, 32, 2_048] {
            let polynomial = (0..half * 2)
                .scan(F::from(7), |value, index| {
                    *value = value.square() + F::from(index as u64 + 1);
                    Some(*value)
                })
                .collect::<Vec<_>>();
            let powers = (0..half * 2)
                .scan(F::from(11), |value, index| {
                    *value = value.square() + F::from(index as u64 + 3);
                    Some(*value)
                })
                .collect::<Vec<_>>();

            assert_eq!(
                compute_ipa_hi_evaluation_pasta::<F>(&polynomial, &powers, half),
                compute_inner_product(&polynomial[half..], &powers[..half]),
            );
        }
    }

    fn compact_b_state_matches_explicit_folds<F>()
    where
        F: Field + From<u64> + Debug + 'static,
    {
        for k in [1, 2, 3, 6, 11] {
            let length = 1 << k;
            for point in [F::ZERO, F::ONE, -F::ONE, F::from(19)] {
                let powers = power_vector(point, length);
                let mut polynomial = (0..length)
                    .map(|index| F::from((index * 17 + 3) as u64))
                    .collect::<Vec<_>>();
                let evaluation = eval_polynomial(&polynomial, point);
                polynomial[0] -= evaluation;

                let mut b = powers.clone();
                let mut polynomial_at_point = F::ZERO;
                let mut b_scale = F::ONE;

                for round in 0..k {
                    let half = 1 << (k - round - 1);
                    let expected_l = compute_inner_product(&polynomial[half..], &b[..half]);
                    let expected_r = compute_inner_product(&polynomial[..half], &b[half..]);

                    let point_to_half = powers[half];
                    let p_hi_at_point =
                        compute_ipa_hi_evaluation_pasta::<F>(&polynomial, &powers, half);
                    let p_lo_at_point = polynomial_at_point - point_to_half * p_hi_at_point;
                    let b_hi_scale = b_scale * point_to_half;

                    assert_eq!(b_scale * p_hi_at_point, expected_l);
                    assert_eq!(b_hi_scale * p_lo_at_point, expected_r);

                    let challenge = if round == 0 {
                        -F::ONE
                    } else {
                        F::from((round + 2) as u64)
                    };
                    let challenge_inverse = challenge.invert().unwrap();
                    for index in 0..half {
                        let p_hi = polynomial[index + half];
                        let b_hi = b[index + half];
                        polynomial[index] += p_hi * challenge_inverse;
                        b[index] += b_hi * challenge;
                    }
                    polynomial.truncate(half);
                    b.truncate(half);

                    polynomial_at_point = p_lo_at_point + challenge_inverse * p_hi_at_point;
                    b_scale += b_hi_scale * challenge;
                    assert_eq!(polynomial_at_point, eval_polynomial(&polynomial, point));

                    for (index, value) in b.iter().enumerate() {
                        assert_eq!(*value, b_scale * powers[index]);
                    }
                }
            }
        }
    }

    #[test]
    fn generator_collapse_matches_native_pallas() {
        generator_collapse_matches_native::<pallas::Affine>();
    }

    #[test]
    fn generator_collapse_matches_native_vesta() {
        generator_collapse_matches_native::<vesta::Affine>();
    }

    #[test]
    fn round_multiexp_matches_split_pallas() {
        round_multiexp_matches_split::<pallas::Affine>();
    }

    #[test]
    fn round_multiexp_matches_split_vesta() {
        round_multiexp_matches_split::<vesta::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn prepared_first_round_matches_ordinary_pallas() {
        prepared_first_round_matches_ordinary::<pallas::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn prepared_first_round_matches_ordinary_vesta() {
        prepared_first_round_matches_ordinary::<vesta::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn prepared_first_round_preserves_unprepared_opening_proof_pallas() {
        prepared_first_round_preserves_opening_proof::<pallas::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn prepared_first_round_preserves_unprepared_opening_proof_vesta() {
        prepared_first_round_preserves_opening_proof::<vesta::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn deferred_ipa_policy_is_limited_to_k_11() {
        assert_eq!(prepared_deferred_ipa_rounds(10), None);
        assert_eq!(prepared_deferred_ipa_rounds(11), Some(4));
        assert_eq!(prepared_deferred_ipa_rounds(12), None);
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn deferred_round_scalars_match_eager_pallas() {
        deferred_round_scalars_match_eager::<pallas::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn deferred_round_scalars_match_eager_vesta() {
        deferred_round_scalars_match_eager::<vesta::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn deferred_materialization_wnaf_recode_pallas() {
        assert_wnaf_recode::<pallas::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn deferred_materialization_wnaf_recode_vesta() {
        assert_wnaf_recode::<vesta::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn deferred_materialization_wnaf_operation_counts_pallas() {
        wnaf_operation_counts::<pallas::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn deferred_materialization_wnaf_operation_counts_vesta() {
        wnaf_operation_counts::<vesta::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn deferred_materialization_matches_native_pallas() {
        deferred_materialization_matches_native::<pallas::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn deferred_materialization_matches_native_vesta() {
        deferred_materialization_matches_native::<vesta::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn prepared_deferred_rounds_preserve_opening_proof_pallas() {
        prepared_deferred_rounds_preserve_opening_proof::<pallas::Affine>();
    }

    #[cfg(all(feature = "multicore", not(feature = "orbits")))]
    #[test]
    fn prepared_deferred_rounds_preserve_opening_proof_vesta() {
        prepared_deferred_rounds_preserve_opening_proof::<vesta::Affine>();
    }

    #[test]
    fn masking_polynomial_is_sparse_and_commits_correctly_pallas() {
        masking_polynomial_is_sparse_and_commits_correctly::<pallas::Affine>();
    }

    #[test]
    fn masking_polynomial_is_sparse_and_commits_correctly_vesta() {
        masking_polynomial_is_sparse_and_commits_correctly::<vesta::Affine>();
    }

    #[test]
    fn masking_basis_detects_every_non_evaluation_fold_pallas() {
        masking_basis_detects_every_non_evaluation_fold::<pallas::Affine>();
    }

    #[test]
    fn masking_basis_detects_every_non_evaluation_fold_vesta() {
        masking_basis_detects_every_non_evaluation_fold::<vesta::Affine>();
    }

    #[test]
    fn deferred_hi_evaluation_matches_eager_pallas_base() {
        deferred_hi_evaluation_matches_eager::<pallas::Base>();
    }

    #[test]
    fn deferred_hi_evaluation_matches_eager_vesta_base() {
        deferred_hi_evaluation_matches_eager::<vesta::Base>();
    }

    #[test]
    fn compact_b_state_matches_explicit_folds_pallas_base() {
        compact_b_state_matches_explicit_folds::<pallas::Base>();
    }

    #[test]
    fn compact_b_state_matches_explicit_folds_vesta_base() {
        compact_b_state_matches_explicit_folds::<vesta::Base>();
    }
}
