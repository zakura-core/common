use ff::Field;
use rand_core::Rng;

use super::super::{Coeff, Polynomial, evaluate_polynomial_with_powers, power_vector};
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

    // Initialize the vector `G'` from the URS. We'll be progressively collapsing
    // this vector into smaller and smaller vectors until it is of length 1.
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

        // The first round uses the original SRS bases, so it can reuse the
        // coefficient table retained by `prepare_commitments`. Later rounds
        // use transcript-dependent folded bases and keep the ordinary MSM.
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
        let (l_j, r_j) = prepared_round
            .flatten()
            .unwrap_or_else(|| ipa_round_multiexps(l_terms, r_terms, params, z));
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

        // The final folded generator is not used by the prover.
        if half > 1 {
            parallel_generator_collapse(&mut g_prime, u_j);
            g_prime.truncate(half);
        }

        // Update randomness (the synthetic blinding factor at the end)
        f += &(l_j_randomness * &u_j_inv);
        f += &(r_j_randomness * &u_j);
    }

    // The polynomial coefficients have fully collapsed.
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
    #[cfg(any(feature = "multicore", feature = "orbits"))]
    use super::create_proof;
    use super::{
        Params, compute_ipa_hi_evaluation_pasta, ipa_masking_commitment, ipa_round_multiexp,
        parallel_generator_collapse, sample_ipa_masking_polynomial,
    };
    use crate::arithmetic::{CurveAffine, best_multiexp, compute_inner_product, eval_polynomial};
    #[cfg(any(feature = "multicore", feature = "orbits"))]
    use crate::poly::commitment::prepared_commitment_max_threads;
    use crate::poly::{EvaluationDomain, commitment::Blind, power_vector};
    #[cfg(any(feature = "multicore", feature = "orbits"))]
    use crate::transcript::{Blake2bWrite, Challenge255, Transcript, TranscriptWrite};
    #[cfg(feature = "multicore")]
    use crate::{PREPARED_SPARSE_COMMITMENT_K, PreparedSparseCommitments};
    use ff::Field;
    use group::{Curve, Group};
    use pasta_curves::{pallas, vesta};
    use rand::rng;
    #[cfg(any(feature = "multicore", feature = "orbits"))]
    use rand::{SeedableRng, rngs::StdRng};
    use std::fmt::Debug;

    fn full_width_scalar<C: CurveAffine>() -> C::Scalar {
        (C::Scalar::from(0x9E37_79B9_7F4A_7C15u64).square()
            + C::Scalar::from(0x0123_4567_89AB_CDEFu64))
        .square()
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

    #[cfg(any(feature = "multicore", feature = "orbits"))]
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

    #[cfg(any(feature = "multicore", feature = "orbits"))]
    fn prepared_first_round_preserves_opening_proof() {
        const K: u32 = 6;
        const PROOF_SEED: u64 = 0x4950_412d_524f_554e;

        let params = Params::<pallas::Affine>::new(K);
        let domain = EvaluationDomain::new(1, K);
        let mut polynomial = domain.empty_coeff();
        for (index, coefficient) in polynomial.iter_mut().enumerate() {
            *coefficient = pallas::Scalar::from(index as u64 + 1);
        }
        let blind = Blind(pallas::Scalar::from(17));
        let create_seeded_proof = || {
            let commitment = params.commit(&polynomial, blind).to_affine();
            let mut transcript =
                Blake2bWrite::<Vec<u8>, pallas::Affine, Challenge255<_>>::init(vec![]);
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

    #[cfg(any(feature = "multicore", feature = "orbits"))]
    #[test]
    fn prepared_first_round_matches_ordinary_pallas() {
        prepared_first_round_matches_ordinary::<pallas::Affine>();
    }

    #[cfg(any(feature = "multicore", feature = "orbits"))]
    #[test]
    fn prepared_first_round_matches_ordinary_vesta() {
        prepared_first_round_matches_ordinary::<vesta::Affine>();
    }

    #[cfg(any(feature = "multicore", feature = "orbits"))]
    #[test]
    fn prepared_first_round_preserves_unprepared_opening_proof() {
        prepared_first_round_preserves_opening_proof();
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
