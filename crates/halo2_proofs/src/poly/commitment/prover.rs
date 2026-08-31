use ff::Field;
use rand_core::Rng;

use super::super::{Coeff, Polynomial, evaluate_polynomial_with_powers, power_vector};
use super::{Blind, Params};
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

fn compute_ipa_inner_products_deferred<F: Field + 'static, T: DeferredField + 'static>(
    a: &dyn Any,
    b: &dyn Any,
    half: usize,
) -> (F, F) {
    let a = a
        .downcast_ref::<Vec<T>>()
        .expect("the inner-product field was checked before conversion");
    let b = b
        .downcast_ref::<Vec<T>>()
        .expect("the inner-product field was checked before conversion");
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), half * 2);
    let result = crate::multicore::join(
        || T::inner_product(&a[half..], &b[..half]),
        || T::inner_product(&a[..half], &b[half..]),
    );
    *(&result as &dyn Any)
        .downcast_ref::<(F, F)>()
        .expect("the inner-product output matches its input field")
}

fn compute_ipa_inner_products_pasta<F: Field + 'static>(
    a: &dyn Any,
    b: &dyn Any,
    half: usize,
) -> (F, F) {
    if TypeId::of::<F>() == TypeId::of::<pallas::Base>() {
        return compute_ipa_inner_products_deferred::<F, pallas::Base>(a, b, half);
    }
    if TypeId::of::<F>() == TypeId::of::<vesta::Base>() {
        return compute_ipa_inner_products_deferred::<F, vesta::Base>(a, b, half);
    }

    // Downcasting the complete owned buffers is safe and avoids per-element
    // type checks in the specialized path.
    let a = a
        .downcast_ref::<Vec<F>>()
        .expect("the inner-product input has the expected field");
    let b = b
        .downcast_ref::<Vec<F>>()
        .expect("the inner-product input has the expected field");
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), half * 2);
    crate::multicore::join(
        || compute_inner_product(&a[half..], &b[..half]),
        || compute_inner_product(&a[..half], &b[half..]),
    )
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

    // The inner product of `p_prime` and `b` is the evaluation of the
    // polynomial at `x_3`.
    let mut b = powers;

    // Initialize the vector `G'` from the URS. We'll be progressively collapsing
    // this vector into smaller and smaller vectors until it is of length 1.
    let mut g_prime = params.g.clone();

    // Perform the inner product argument, round by round.
    for j in 0..params.k {
        let half = 1 << (params.k - j - 1); // half the length of `p_prime`, `b`, `G'`

        // Compute the scalar terms needed by L and R before their MSMs.
        let (value_l_j, value_r_j) =
            compute_ipa_inner_products_pasta::<C::Scalar>(&p_prime, &b, half);
        let l_j_randomness = C::Scalar::random(&mut rng);
        let r_j_randomness = C::Scalar::random(&mut rng);

        // Include the U and W terms in each main MSM so their doublings are
        // shared with the round commitment.
        let (l_j, r_j) = crate::multicore::join(
            || {
                ipa_round_multiexp(
                    &p_prime[half..],
                    &g_prime[0..half],
                    value_l_j,
                    l_j_randomness,
                    params,
                    z,
                )
            },
            || {
                ipa_round_multiexp(
                    &p_prime[0..half],
                    &g_prime[half..],
                    value_r_j,
                    r_j_randomness,
                    params,
                    z,
                )
            },
        );
        let l_j = l_j.to_affine();
        let r_j = r_j.to_affine();

        // Feed L and R into the real transcript
        transcript.write_point(l_j)?;
        transcript.write_point(r_j)?;

        let u_j = *transcript.squeeze_challenge_scalar::<()>();
        let u_j_inv = u_j.invert().unwrap(); // TODO, bubble this up

        // Collapse `p_prime` and `b`.
        // TODO: parallelize
        #[allow(clippy::assign_op_pattern)]
        for i in 0..half {
            p_prime[i] = p_prime[i] + &(p_prime[i + half] * &u_j_inv);
            b[i] = b[i] + &(b[i + half] * &u_j);
        }
        p_prime.truncate(half);
        b.truncate(half);

        // Collapse `G'`
        parallel_generator_collapse(&mut g_prime, u_j);
        g_prime.truncate(half);

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
    use super::{
        Params, compute_ipa_inner_products_pasta, ipa_masking_commitment, ipa_round_multiexp,
        parallel_generator_collapse, sample_ipa_masking_polynomial,
    };
    use crate::arithmetic::{CurveAffine, best_multiexp, compute_inner_product, eval_polynomial};
    use crate::poly::{EvaluationDomain, commitment::Blind};
    use ff::Field;
    use group::{Curve, Group};
    use pasta_curves::{pallas, vesta};
    use rand::rng;

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

    fn deferred_inner_product_matches_eager<F: Field + From<u64> + 'static>() {
        for half in [0, 1, 2, 3, 31, 32, 2_048] {
            let a = (0..half * 2)
                .scan(F::from(7), |value, index| {
                    *value = value.square() + F::from(index as u64 + 1);
                    Some(*value)
                })
                .collect::<Vec<_>>();
            let b = (0..half * 2)
                .scan(F::from(11), |value, index| {
                    *value = value.square() + F::from(index as u64 + 3);
                    Some(*value)
                })
                .collect::<Vec<_>>();

            let (left, right) = compute_ipa_inner_products_pasta::<F>(&a, &b, half);
            assert_eq!(left, compute_inner_product(&a[half..], &b[..half]));
            assert_eq!(right, compute_inner_product(&a[..half], &b[half..]));
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
    fn deferred_inner_product_matches_eager_pallas_base() {
        deferred_inner_product_matches_eager::<pallas::Base>();
    }

    #[test]
    fn deferred_inner_product_matches_eager_vesta_base() {
        deferred_inner_product_matches_eager::<vesta::Base>();
    }
}
