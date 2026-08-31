use super::super::{
    ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, Error, ProvingKey,
    circuit::Expression,
};
use super::Argument;
use crate::{
    arithmetic::{CurveAffine, parallelize},
    plonk::evaluation::{EvaluationPoint, EvaluationQuery},
    poly::{
        self, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation,
        commitment::{Blind, Params},
        multiopen::ProverQuery,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};
use ff::WithSmallOrderMulGroup;
use group::{Curve, ff::Field};
use rand_core::Rng;
use std::{
    iter,
    ops::{Mul, MulAssign},
};

#[derive(Debug)]
pub(in crate::plonk) struct Permuted<C: CurveAffine, Ev> {
    compressed_input_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_input_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    compressed_input_coset: poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>,
    permuted_input_poly: Polynomial<C::Scalar, Coeff>,
    permuted_input_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    permuted_input_blind: Blind<C::Scalar>,
    compressed_table_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    compressed_table_coset: poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>,
    permuted_table_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_table_poly: Polynomial<C::Scalar, Coeff>,
    permuted_table_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    permuted_table_blind: Blind<C::Scalar>,
}

#[derive(Debug)]
pub(in crate::plonk) struct Committed<C: CurveAffine, Ev> {
    permuted: Permuted<C, Ev>,
    product_poly: Polynomial<C::Scalar, Coeff>,
    product_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    product_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) struct Constructed<C: CurveAffine> {
    permuted_input_poly: Polynomial<C::Scalar, Coeff>,
    permuted_input_blind: Blind<C::Scalar>,
    permuted_table_poly: Polynomial<C::Scalar, Coeff>,
    permuted_table_blind: Blind<C::Scalar>,
    product_poly: Polynomial<C::Scalar, Coeff>,
    product_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) struct Evaluated<C: CurveAffine> {
    constructed: Constructed<C>,
}

pub(in crate::plonk) struct PermutedBlinding<F: Field> {
    input_rows: Vec<F>,
    table_rows: Vec<F>,
    input_blind: Blind<F>,
    table_blind: Blind<F>,
}

pub(in crate::plonk) struct PreparedPermuted<C: CurveAffine, Ev> {
    compressed_input_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_input_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    compressed_input_coset: poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>,
    permuted_input_poly: Polynomial<C::Scalar, Coeff>,
    permuted_input_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    permuted_input_commitment: C,
    permuted_input_blind: Blind<C::Scalar>,
    compressed_table_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    compressed_table_coset: poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>,
    permuted_table_expression: Polynomial<C::Scalar, LagrangeCoeff>,
    permuted_table_poly: Polynomial<C::Scalar, Coeff>,
    permuted_table_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    permuted_table_commitment: C,
    permuted_table_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) struct ProductBlinding<F: Field> {
    rows: Vec<F>,
    product_blind: Blind<F>,
}

pub(in crate::plonk) struct PreparedProduct<C: CurveAffine, Ev> {
    permuted: Permuted<C, Ev>,
    product_poly: Polynomial<C::Scalar, Coeff>,
    product_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    product_commitment: C,
    product_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) fn sample_permuted_blinding<C: CurveAffine, R: Rng>(
    pk: &ProvingKey<C>,
    mut rng: R,
) -> PermutedBlinding<C::Scalar> {
    let blind_rows = pk.vk.cs.blinding_factors() + 1;
    PermutedBlinding {
        input_rows: (0..blind_rows)
            .map(|_| C::Scalar::random(&mut rng))
            .collect(),
        table_rows: (0..blind_rows)
            .map(|_| C::Scalar::random(&mut rng))
            .collect(),
        input_blind: Blind(C::Scalar::random(&mut rng)),
        table_blind: Blind(C::Scalar::random(&mut rng)),
    }
}

pub(in crate::plonk) fn sample_product_blinding<C: CurveAffine, R: Rng>(
    pk: &ProvingKey<C>,
    mut rng: R,
) -> ProductBlinding<C::Scalar> {
    ProductBlinding {
        rows: (0..pk.vk.cs.blinding_factors())
            .map(|_| C::Scalar::random(&mut rng))
            .collect(),
        product_blind: Blind(C::Scalar::random(&mut rng)),
    }
}

/// Builds the coset-basis AST for one theta-compressed lookup side.
///
/// Every [`Expression`] must have had its virtual selectors removed.
pub(in crate::plonk) fn compress_expressions_coset<E: Copy, F: Field>(
    expressions: &[Expression<F>],
    theta: F,
    fixed_cosets: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
    advice_cosets: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
    instance_cosets: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
) -> poly::Ast<E, F, ExtendedLagrangeCoeff> {
    expressions
        .iter()
        .map(|expression| {
            expression.evaluate(
                &poly::Ast::ConstantTerm,
                &|_| panic!("virtual selectors are removed during optimization"),
                &|query| {
                    fixed_cosets[query.column_index]
                        .with_rotation(query.rotation)
                        .into()
                },
                &|query| {
                    advice_cosets[query.column_index]
                        .with_rotation(query.rotation)
                        .into()
                },
                &|query| {
                    instance_cosets[query.column_index]
                        .with_rotation(query.rotation)
                        .into()
                },
                &|a| -a,
                &|a, b| a + b,
                &|a, b| a * b,
                &|a, scalar| a * scalar,
            )
        })
        .reduce(|acc, expression| acc * poly::Ast::ConstantTerm(theta) + expression)
        .unwrap_or(poly::Ast::ConstantTerm(F::ZERO))
}

impl<F: WithSmallOrderMulGroup<3>> Argument<F> {
    /// Prepares the compressed, permuted input and table polynomials.
    ///
    /// This phase does not mutate the shared evaluator or transcript, so
    /// independent lookup arguments can run in parallel. The caller must pass
    /// the result to [`PreparedPermuted::finalize`] in circuit order.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn prepare_permuted<C, Ev: Copy + Send + Sync, Ec: Copy + Send + Sync>(
        &self,
        pk: &ProvingKey<C>,
        params: &Params<C>,
        domain: &EvaluationDomain<C::Scalar>,
        value_evaluator: &poly::Evaluator<Ev, C::Scalar, LagrangeCoeff>,
        theta: ChallengeTheta<C>,
        advice_values: &[poly::AstLeaf<Ev, LagrangeCoeff>],
        fixed_values: &[poly::AstLeaf<Ev, LagrangeCoeff>],
        instance_values: &[poly::AstLeaf<Ev, LagrangeCoeff>],
        advice_cosets: &[poly::AstLeaf<Ec, ExtendedLagrangeCoeff>],
        fixed_cosets: &[poly::AstLeaf<Ec, ExtendedLagrangeCoeff>],
        instance_cosets: &[poly::AstLeaf<Ec, ExtendedLagrangeCoeff>],
        blinding: PermutedBlinding<C::Scalar>,
    ) -> Result<PreparedPermuted<C, Ec>, Error>
    where
        C: CurveAffine<ScalarExt = F>,
        C::Curve: Mul<F, Output = C::Curve> + MulAssign<F>,
    {
        // Closure to get values of expressions and compress them
        let compress_expressions = |expressions: &[Expression<C::Scalar>]| {
            // Values of input expressions involved in the lookup
            let unpermuted_expressions: Vec<_> = expressions
                .iter()
                .map(|expression| {
                    expression.evaluate(
                        &|scalar| poly::Ast::ConstantTerm(scalar),
                        &|_| panic!("virtual selectors are removed during optimization"),
                        &|query| {
                            fixed_values[query.column_index]
                                .with_rotation(query.rotation)
                                .into()
                        },
                        &|query| {
                            advice_values[query.column_index]
                                .with_rotation(query.rotation)
                                .into()
                        },
                        &|query| {
                            instance_values[query.column_index]
                                .with_rotation(query.rotation)
                                .into()
                        },
                        &|a| -a,
                        &|a, b| a + b,
                        &|a, b| a * b,
                        &|a, scalar| a * scalar,
                    )
                })
                .collect();

            // Compressed version of expressions
            let compressed_expression = unpermuted_expressions
                .into_iter()
                .reduce(|acc, expression| acc * *theta + expression)
                .unwrap_or(poly::Ast::ConstantTerm(C::Scalar::ZERO));

            // Compressed version of cosets
            let compressed_coset = compress_expressions_coset(
                expressions,
                *theta,
                fixed_cosets,
                advice_cosets,
                instance_cosets,
            );

            (
                compressed_coset,
                value_evaluator.evaluate(&compressed_expression, domain),
            )
        };

        // Get values of input expressions involved in the lookup and compress them
        let (compressed_input_coset, compressed_input_expression) =
            compress_expressions(&self.input_expressions);

        // Get values of table expressions involved in the lookup and compress them
        let (compressed_table_coset, compressed_table_expression) =
            compress_expressions(&self.table_expressions);

        // Permute compressed (InputExpression, TableExpression) pair
        let (permuted_input_expression, permuted_table_expression) = permute_expression_pair::<C>(
            pk,
            params,
            domain,
            &blinding.input_rows,
            &blinding.table_rows,
            &compressed_input_expression,
            &compressed_table_expression,
        )?;

        let permuted_input_blind = blinding.input_blind;
        let permuted_table_blind = blinding.table_blind;

        // Convert and commit to the input and table permutations concurrently.
        let commit_values = |values: &Polynomial<C::Scalar, LagrangeCoeff>,
                             blind: Blind<C::Scalar>| {
            let poly = pk
                .vk
                .domain
                .lagrange_to_coeff_with_twiddles(values.clone(), &pk.fft_twiddles);
            let coset = pk
                .vk
                .domain
                .coeff_to_extended_with_twiddles(poly.clone(), &pk.fft_twiddles);
            let commitment = params.commit_lagrange(values, blind).to_affine();
            (poly, coset, commitment)
        };
        let (
            (permuted_input_poly, permuted_input_coset, permuted_input_commitment),
            (permuted_table_poly, permuted_table_coset, permuted_table_commitment),
        ) = crate::multicore::join(
            || commit_values(&permuted_input_expression, permuted_input_blind),
            || commit_values(&permuted_table_expression, permuted_table_blind),
        );

        Ok(PreparedPermuted {
            compressed_input_expression,
            compressed_input_coset,
            permuted_input_expression,
            permuted_input_poly,
            permuted_input_coset,
            permuted_input_commitment,
            permuted_input_blind,
            compressed_table_expression,
            compressed_table_coset,
            permuted_table_expression,
            permuted_table_poly,
            permuted_table_coset,
            permuted_table_commitment,
            permuted_table_blind,
        })
    }
}

impl<C: CurveAffine, Ev: Copy + Send + Sync> PreparedPermuted<C, Ev> {
    /// Writes commitments and registers cosets in circuit order.
    pub(in crate::plonk) fn finalize<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        evaluator: &mut poly::Evaluator<Ev, C::Scalar, ExtendedLagrangeCoeff>,
        transcript: &mut T,
    ) -> Result<Permuted<C, Ev>, Error> {
        transcript.write_point(self.permuted_input_commitment)?;
        transcript.write_point(self.permuted_table_commitment)?;

        let permuted_input_coset = evaluator.register_poly(self.permuted_input_coset);
        let permuted_table_coset = evaluator.register_poly(self.permuted_table_coset);

        Ok(Permuted {
            compressed_input_expression: self.compressed_input_expression,
            permuted_input_expression: self.permuted_input_expression,
            compressed_input_coset: self.compressed_input_coset,
            permuted_input_poly: self.permuted_input_poly,
            permuted_input_coset,
            permuted_input_blind: self.permuted_input_blind,
            compressed_table_expression: self.compressed_table_expression,
            compressed_table_coset: self.compressed_table_coset,
            permuted_table_expression: self.permuted_table_expression,
            permuted_table_poly: self.permuted_table_poly,
            permuted_table_coset,
            permuted_table_blind: self.permuted_table_blind,
        })
    }
}

impl<C: CurveAffine, Ev: Copy + Send + Sync> Permuted<C, Ev> {
    /// Constructs the grand product polynomial for this lookup.
    pub(in crate::plonk) fn prepare_product(
        self,
        pk: &ProvingKey<C>,
        params: &Params<C>,
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        blinding: ProductBlinding<C::Scalar>,
    ) -> PreparedProduct<C, Ev> {
        let blinding_factors = pk.vk.cs.blinding_factors();
        assert_eq!(blinding.rows.len(), blinding_factors);
        // Goal is to compute the products of fractions
        //
        // Numerator: (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        //            * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        // Denominator: (a'(\omega^i) + \beta) (s'(\omega^i) + \gamma)
        //
        // where a_j(X) is the jth input expression in this lookup,
        // where a'(X) is the compression of the permuted input expressions,
        // s_j(X) is the jth table expression in this lookup,
        // s'(X) is the compression of the permuted table expressions,
        // and i is the ith row of the expression.
        let mut lookup_product = vec![C::Scalar::ZERO; params.n as usize];
        // Denominator uses the permuted input expression and permuted table expression
        parallelize(&mut lookup_product, |lookup_product, start| {
            for ((lookup_product, permuted_input_value), permuted_table_value) in lookup_product
                .iter_mut()
                .zip(self.permuted_input_expression[start..].iter())
                .zip(self.permuted_table_expression[start..].iter())
            {
                *lookup_product = (*beta + permuted_input_value) * &(*gamma + permuted_table_value);
            }
        });

        // Batch invert to obtain the denominators for the lookup product
        // polynomials
        crate::arithmetic::batch_invert_multi(&mut lookup_product);

        // Finish the computation of the entire fraction by computing the numerators
        // (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        // * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        parallelize(&mut lookup_product, |product, start| {
            for ((product, &input_term), &table_term) in product
                .iter_mut()
                .zip(self.compressed_input_expression[start..].iter())
                .zip(self.compressed_table_expression[start..].iter())
            {
                *product *= &(input_term + &*beta);
                *product *= &(table_term + &*gamma);
            }
        });

        // The product vector is a vector of products of fractions of the form
        //
        // Numerator: (\theta^{m-1} a_0(\omega^i) + \theta^{m-2} a_1(\omega^i) + ... + \theta a_{m-2}(\omega^i) + a_{m-1}(\omega^i) + \beta)
        //            * (\theta^{m-1} s_0(\omega^i) + \theta^{m-2} s_1(\omega^i) + ... + \theta s_{m-2}(\omega^i) + s_{m-1}(\omega^i) + \gamma)
        // Denominator: (a'(\omega^i) + \beta) (s'(\omega^i) + \gamma)
        //
        // where there are m input expressions and m table expressions,
        // a_j(\omega^i) is the jth input expression in this lookup,
        // a'j(\omega^i) is the permuted input expression,
        // s_j(\omega^i) is the jth table expression in this lookup,
        // s'(\omega^i) is the permuted table expression,
        // and i is the ith row of the expression.

        // Compute the evaluations of the lookup product polynomial
        // over our domain, starting with z[0] = 1
        // Reuse the fraction vector for z instead of allocating a second
        // domain-sized vector. This includes the "last" row, which should be
        // a boolean (and ideally 1, else soundness is broken).
        let usable_rows = params.n as usize - blinding_factors;
        let mut state = C::Scalar::ONE;
        for product in lookup_product.iter_mut().take(usable_rows) {
            let current = *product;
            *product = state;
            state *= &current;
        }
        lookup_product.truncate(usable_rows);
        lookup_product.extend(blinding.rows);
        assert_eq!(lookup_product.len(), params.n as usize);
        let z = pk.vk.domain.lagrange_from_vec(lookup_product);

        #[cfg(feature = "sanity-checks")]
        // This test works only with intermediate representations in this method.
        // It can be used for debugging purposes.
        {
            // While in Lagrange basis, check that product is correctly constructed
            let u = (params.n as usize) - (blinding_factors + 1);

            // l_0(X) * (1 - z(X)) = 0
            assert_eq!(z[0], C::Scalar::ONE);

            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            // - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
            for i in 0..u {
                let mut left = z[i + 1];
                let permuted_input_value = &self.permuted_input_expression[i];

                let permuted_table_value = &self.permuted_table_expression[i];

                left *= &(*beta + permuted_input_value);
                left *= &(*gamma + permuted_table_value);

                let mut right = z[i];
                let mut input_term = self.compressed_input_expression[i];

                let mut table_term = self.compressed_table_expression[i];

                input_term += &(*beta);
                table_term += &(*gamma);
                right *= &(input_term * &table_term);

                assert_eq!(left, right);
            }

            // l_last(X) * (z(X)^2 - z(X)) = 0
            // Assertion will fail only when soundness is broken, in which
            // case this z[u] value will be zero. (bad!)
            assert_eq!(z[u], C::Scalar::ONE);
        }

        let product_blind = blinding.product_blind;
        let (product_commitment, (z, product_coset)) = crate::multicore::join(
            || params.commit_lagrange(&z, product_blind).to_affine(),
            || {
                let z = pk
                    .vk
                    .domain
                    .lagrange_to_coeff_with_twiddles(z.clone(), &pk.fft_twiddles);
                let coset = pk
                    .vk
                    .domain
                    .coeff_to_extended_with_twiddles(z.clone(), &pk.fft_twiddles);
                (z, coset)
            },
        );

        PreparedProduct {
            permuted: self,
            product_poly: z,
            product_coset,
            product_commitment,
            product_blind,
        }
    }
}

impl<C: CurveAffine, Ev: Copy + Send + Sync> PreparedProduct<C, Ev> {
    /// Writes the product commitment and registers its coset in circuit order.
    pub(in crate::plonk) fn finalize<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        evaluator: &mut poly::Evaluator<Ev, C::Scalar, ExtendedLagrangeCoeff>,
        transcript: &mut T,
    ) -> Result<Committed<C, Ev>, Error> {
        let product_coset = evaluator.register_poly(self.product_coset);

        // Hash product commitment.
        transcript.write_point(self.product_commitment)?;

        Ok(Committed {
            permuted: self.permuted,
            product_poly: self.product_poly,
            product_coset,
            product_blind: self.product_blind,
        })
    }
}

/// Builds the lookup constraint ASTs without evaluating polynomial rows.
pub(in crate::plonk) fn construct_constraints<E: Copy, F: Field>(
    compressed_input: poly::Ast<E, F, ExtendedLagrangeCoeff>,
    permuted_input: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    compressed_table: poly::Ast<E, F, ExtendedLagrangeCoeff>,
    permuted_table: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    product: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    beta: F,
    gamma: F,
    l0: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    l_blind: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    l_last: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
) -> impl Iterator<Item = poly::Ast<E, F, ExtendedLagrangeCoeff>> {
    let active_rows = poly::Ast::one() - (poly::Ast::from(l_last) + l_blind);
    let beta = poly::Ast::ConstantTerm(beta);
    let gamma = poly::Ast::ConstantTerm(gamma);

    iter::empty()
        // l_0(X) * (1 - z(X)) = 0
        .chain(Some((poly::Ast::one() - product) * l0))
        // l_last(X) * (z(X)^2 - z(X)) = 0
        .chain(Some(
            (poly::Ast::from(product) * product - product) * l_last,
        ))
        // (1 - (l_last(X) + l_blind(X))) * (
        //   z(omega X) (a'(X) + beta) (s'(X) + gamma)
        //   - z(X) (compressed_input(X) + beta)
        //     (compressed_table(X) + gamma)
        // ) = 0
        .chain({
            let left: poly::Ast<_, _, _> =
                poly::Ast::<_, F, _>::from(product.with_rotation(Rotation::next()))
                    * (poly::Ast::from(permuted_input) + beta.clone())
                    * (poly::Ast::from(permuted_table) + gamma.clone());

            let right: poly::Ast<_, _, _> =
                poly::Ast::from(product) * (compressed_input + beta) * (compressed_table + gamma);

            Some((left - right) * active_rows.clone())
        })
        // l_0(X) * (a'(X) - s'(X)) = 0
        .chain(Some(
            (poly::Ast::from(permuted_input) - permuted_table) * l0,
        ))
        // (1 - (l_last + l_blind)) *
        // (a'(X) - s'(X)) * (a'(X) - a'(omega^-1 X)) = 0
        .chain(Some(
            (poly::Ast::<_, F, _>::from(permuted_input) - permuted_table)
                * (poly::Ast::from(permuted_input)
                    - permuted_input.with_rotation(Rotation::prev()))
                * active_rows,
        ))
}

impl<'a, C: CurveAffine, Ev: Copy + Send + Sync + 'a> Committed<C, Ev> {
    /// Given a Lookup with input expressions, table expressions, permuted input
    /// expression, permuted table expression, and grand product polynomial, this
    /// method constructs constraints that must hold between these values.
    /// This method returns the constraints as a vector of ASTs for polynomials in
    /// the extended evaluation domain.
    pub(in crate::plonk) fn construct(
        self,
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        l0: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
        l_blind: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
        l_last: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    ) -> (
        Constructed<C>,
        impl Iterator<Item = poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>> + 'a,
    ) {
        let permuted = self.permuted;
        let expressions = construct_constraints(
            permuted.compressed_input_coset,
            permuted.permuted_input_coset,
            permuted.compressed_table_coset,
            permuted.permuted_table_coset,
            self.product_coset,
            *beta,
            *gamma,
            l0,
            l_blind,
            l_last,
        );

        (
            Constructed {
                permuted_input_poly: permuted.permuted_input_poly,
                permuted_input_blind: permuted.permuted_input_blind,
                permuted_table_poly: permuted.permuted_table_poly,
                permuted_table_blind: permuted.permuted_table_blind,
                product_poly: self.product_poly,
                product_blind: self.product_blind,
            },
            expressions,
        )
    }
}

impl<C: CurveAffine> Constructed<C> {
    pub(in crate::plonk) fn evaluation_queries(&self) -> [EvaluationQuery<'_, C::Scalar>; 5] {
        [
            EvaluationQuery {
                polynomial: &self.product_poly,
                point: EvaluationPoint::Current,
            },
            EvaluationQuery {
                polynomial: &self.product_poly,
                point: EvaluationPoint::Next,
            },
            EvaluationQuery {
                polynomial: &self.permuted_input_poly,
                point: EvaluationPoint::Current,
            },
            EvaluationQuery {
                polynomial: &self.permuted_input_poly,
                point: EvaluationPoint::Previous,
            },
            EvaluationQuery {
                polynomial: &self.permuted_table_poly,
                point: EvaluationPoint::Current,
            },
        ]
    }

    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        evaluations: &mut impl Iterator<Item = C::Scalar>,
        transcript: &mut T,
    ) -> Result<Evaluated<C>, Error> {
        // Hash each advice evaluation.
        for _ in 0..self.evaluation_queries().len() {
            let evaluation = evaluations
                .next()
                .expect("one result is returned for every lookup evaluation query");
            transcript.write_scalar(evaluation)?;
        }

        Ok(Evaluated { constructed: self })
    }
}

impl<C: CurveAffine> Evaluated<C> {
    pub(in crate::plonk) fn open<'a>(
        &'a self,
        pk: &'a ProvingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = ProverQuery<'a, C>> + Clone {
        let x_inv = pk.vk.domain.rotate_omega(*x, Rotation::prev());
        let x_next = pk.vk.domain.rotate_omega(*x, Rotation::next());

        iter::empty()
            // Open lookup product commitments at x
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.product_poly,
                blind: self.constructed.product_blind,
            }))
            // Open lookup input commitments at x
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.permuted_input_poly,
                blind: self.constructed.permuted_input_blind,
            }))
            // Open lookup table commitments at x
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.permuted_table_poly,
                blind: self.constructed.permuted_table_blind,
            }))
            // Open lookup input commitments at x_inv
            .chain(Some(ProverQuery {
                point: x_inv,
                poly: &self.constructed.permuted_input_poly,
                blind: self.constructed.permuted_input_blind,
            }))
            // Open lookup product commitments at x_next
            .chain(Some(ProverQuery {
                point: x_next,
                poly: &self.constructed.product_poly,
                blind: self.constructed.product_blind,
            }))
    }
}

type ExpressionPair<F> = (Polynomial<F, LagrangeCoeff>, Polynomial<F, LagrangeCoeff>);

fn permute_usable_values<F: Field + Ord>(
    mut input_values: Vec<F>,
    mut table_values: Vec<F>,
) -> Result<(Vec<F>, Vec<F>), Error> {
    assert_eq!(input_values.len(), table_values.len());

    crate::multicore::join(
        || input_values.sort_unstable(),
        || table_values.sort_unstable(),
    );

    let usable_rows = input_values.len();
    let mut permuted_table_values = vec![F::ZERO; usable_rows];
    let mut consumed_table_rows = Vec::new();
    let mut table_row = 0;

    let mut repeated_input_rows = input_values
        .iter()
        .zip(permuted_table_values.iter_mut())
        .enumerate()
        .filter_map(|(row, (input_value, table_value))| {
            if row == 0 || *input_value != input_values[row - 1] {
                *table_value = *input_value;
                while table_row < usable_rows && table_values[table_row] < *input_value {
                    table_row += 1;
                }
                if table_values.get(table_row) == Some(input_value) {
                    consumed_table_rows.push(table_row);
                    table_row += 1;
                    None
                } else {
                    Some(Err(Error::ConstraintSystemFailure))
                }
            } else {
                Some(Ok(row))
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    let mut consumed_table_rows = consumed_table_rows.into_iter().peekable();
    for (row, value) in table_values.into_iter().enumerate() {
        if consumed_table_rows.peek() == Some(&row) {
            consumed_table_rows.next();
        } else {
            permuted_table_values[repeated_input_rows.pop().unwrap()] = value;
        }
    }
    assert!(consumed_table_rows.next().is_none());
    assert!(repeated_input_rows.is_empty());

    Ok((input_values, permuted_table_values))
}

/// Given a vector of input values A and a vector of table values S,
/// this method permutes A and S to produce A' and S', such that:
/// - like values in A' are vertically adjacent to each other; and
/// - the first row in a sequence of like values in A' is the row
///   that has the corresponding value in S'.
///
/// This method returns (A', S') if no errors are encountered.
fn permute_expression_pair<C: CurveAffine>(
    pk: &ProvingKey<C>,
    params: &Params<C>,
    domain: &EvaluationDomain<C::Scalar>,
    input_blinds: &[C::Scalar],
    table_blinds: &[C::Scalar],
    input_expression: &Polynomial<C::Scalar, LagrangeCoeff>,
    table_expression: &Polynomial<C::Scalar, LagrangeCoeff>,
) -> Result<ExpressionPair<C::Scalar>, Error> {
    let blinding_factors = pk.vk.cs.blinding_factors();
    let blind_rows = blinding_factors + 1;
    let usable_rows = params.n as usize - blind_rows;

    let mut input_values = input_expression.to_vec();
    input_values.truncate(usable_rows);
    let table_values = table_expression.iter().take(usable_rows).copied().collect();
    let (mut permuted_input_expression, mut permuted_table_coeffs) =
        permute_usable_values(input_values, table_values)?;

    assert_eq!(input_blinds.len(), blind_rows);
    assert_eq!(table_blinds.len(), blind_rows);
    permuted_input_expression.extend_from_slice(input_blinds);
    permuted_table_coeffs.extend_from_slice(table_blinds);
    assert_eq!(permuted_input_expression.len(), params.n as usize);
    assert_eq!(permuted_table_coeffs.len(), params.n as usize);

    #[cfg(feature = "sanity-checks")]
    {
        let mut last = None;
        for (a, b) in permuted_input_expression
            .iter()
            .zip(permuted_table_coeffs.iter())
            .take(usable_rows)
        {
            if *a != *b {
                assert_eq!(*a, last.unwrap());
            }
            last = Some(*a);
        }
    }

    Ok((
        domain.lagrange_from_vec(permuted_input_expression),
        domain.lagrange_from_vec(permuted_table_coeffs),
    ))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use pasta_curves::pallas;

    use super::*;

    const TEST_ALPHABET_SIZE: usize = 3;

    // This is the previous BTreeMap implementation, retained as an oracle for
    // exact output ordering and error behavior.
    fn reference_permutation<F: Field + Ord>(
        mut input_values: Vec<F>,
        table_values: Vec<F>,
    ) -> Result<(Vec<F>, Vec<F>), Error> {
        input_values.sort();
        let mut leftovers = table_values
            .into_iter()
            .fold(BTreeMap::new(), |mut counts, value| {
                *counts.entry(value).or_insert(0_u32) += 1;
                counts
            });
        let mut permuted_table_values = vec![F::ZERO; input_values.len()];
        let mut repeated_input_rows = input_values
            .iter()
            .zip(permuted_table_values.iter_mut())
            .enumerate()
            .filter_map(|(row, (input_value, table_value))| {
                if row == 0 || *input_value != input_values[row - 1] {
                    *table_value = *input_value;
                    if let Some(count) = leftovers.get_mut(input_value) {
                        assert!(*count > 0);
                        *count -= 1;
                        None
                    } else {
                        Some(Err(Error::ConstraintSystemFailure))
                    }
                } else {
                    Some(Ok(row))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        for (value, count) in leftovers {
            for _ in 0..count {
                permuted_table_values[repeated_input_rows.pop().unwrap()] = value;
            }
        }
        assert!(repeated_input_rows.is_empty());

        Ok((input_values, permuted_table_values))
    }

    fn values(values: &[u64]) -> Vec<pallas::Scalar> {
        values.iter().copied().map(pallas::Scalar::from).collect()
    }

    fn small_vectors(len: usize) -> Vec<Vec<pallas::Scalar>> {
        (0..TEST_ALPHABET_SIZE.pow(u32::try_from(len).expect("test length fits in u32")))
            .map(|mut encoded| {
                (0..len)
                    .map(|_| {
                        let value = u64::try_from(encoded % TEST_ALPHABET_SIZE)
                            .expect("test alphabet values fit in u64");
                        encoded /= TEST_ALPHABET_SIZE;
                        pallas::Scalar::from(value)
                    })
                    .collect()
            })
            .collect()
    }

    #[test]
    fn sorted_lookup_permutation_matches_reference_exhaustively() {
        for len in 0..=4 {
            let vectors = small_vectors(len);
            for input in &vectors {
                for table in &vectors {
                    let actual = permute_usable_values(input.clone(), table.clone());
                    match reference_permutation(input.clone(), table.clone()) {
                        Ok(expected) => assert_eq!(actual.unwrap(), expected),
                        Err(Error::ConstraintSystemFailure) => {
                            assert!(matches!(actual, Err(Error::ConstraintSystemFailure)))
                        }
                        Err(_) => panic!("reference returned an unexpected error"),
                    }
                }
            }
        }
    }

    #[test]
    fn sorted_lookup_permutation_preserves_output_order() {
        let input = values(&[2, 2, 5, 1, 7, 2, 6, 4]);
        let table = values(&[5, 1, 2, 3, 2, 4, 6, 7]);

        assert_eq!(
            permute_usable_values(input, table).unwrap(),
            (
                values(&[1, 2, 2, 2, 4, 5, 6, 7]),
                values(&[1, 2, 3, 2, 4, 5, 6, 7]),
            )
        );
    }

    #[test]
    fn sorted_lookup_permutation_rejects_missing_value() {
        let input = values(&[1, 2, 2, 7]);
        let table = values(&[1, 2, 3, 4]);

        assert!(matches!(
            permute_usable_values(input.clone(), table.clone()),
            Err(Error::ConstraintSystemFailure)
        ));
        assert!(matches!(
            reference_permutation(input, table),
            Err(Error::ConstraintSystemFailure)
        ));
    }
}
