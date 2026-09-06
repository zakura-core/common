use group::{
    Curve, Group,
    ff::{Field, PrimeField, WithSmallOrderMulGroup},
};
use maybe_rayon::prelude::*;
use rand_core::Rng;
use std::{convert::Infallible, iter};

use super::super::{ChallengeBeta, ChallengeGamma, ChallengeX, circuit::Any};
use super::{Argument, ProvingKey, permutation_chunk_len};
use crate::{
    arithmetic::{CurveAffine, best_multiexp, parallelize},
    plonk::{
        self, Error,
        evaluation::{EvaluationPoint, EvaluationQuery},
        evaluator_schedule::QuotientPoly,
    },
    poly::{
        self, Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation,
        commitment::{Blind, Params},
        multiopen::ProverQuery,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};

pub struct CommittedSet<C: CurveAffine, Ev> {
    permutation_product_poly: Polynomial<C::Scalar, Coeff>,
    permutation_product_coset: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    permutation_product_blind: Blind<C::Scalar>,
}

pub(crate) struct Committed<C: CurveAffine, Ev> {
    sets: Vec<CommittedSet<C, Ev>>,
}

struct SetBlinding<F: Field> {
    rows: Vec<F>,
    product_blind: Blind<F>,
}

struct PreparedFractions<F: Field> {
    numerators: Vec<F>,
    denominators: Vec<F>,
    blinding: SetBlinding<F>,
}

enum PreparedProduct<F: Field> {
    Fractions(PreparedFractions<F>),
    Identity(SetBlinding<F>),
}

struct UntransformedSet<F: Field> {
    product: Polynomial<F, LagrangeCoeff>,
    product_blind: Blind<F>,
}

enum UnpreparedSet<F: Field> {
    Dense(UntransformedSet<F>),
    Identity {
        constant: F,
        blinding: SetBlinding<F>,
    },
}

#[derive(Clone, Copy)]
struct ConstantPrefix<'a, F: Field> {
    constant: F,
    prefix_len: usize,
    tail: &'a [F],
}

// Bounds both the stack storage and the per-coefficient work of the direct
// transform.
const MAX_DIRECT_TRANSFORM_TAIL_LEN: usize = 8;

pub(in crate::plonk) struct PermutationBlinding<F: Field> {
    sets: Vec<SetBlinding<F>>,
}

struct PreparedSet<C: CurveAffine> {
    permutation_product_poly: Polynomial<C::Scalar, Coeff>,
    permutation_product_coset: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    permutation_product_commitment: C,
    permutation_product_blind: Blind<C::Scalar>,
}

pub(in crate::plonk) struct Prepared<C: CurveAffine> {
    sets: Vec<PreparedSet<C>>,
}

pub struct ConstructedSet<C: CurveAffine> {
    permutation_product_poly: Polynomial<C::Scalar, Coeff>,
    permutation_product_blind: Blind<C::Scalar>,
}

pub(crate) struct Constructed<C: CurveAffine> {
    sets: Vec<ConstructedSet<C>>,
}

pub(crate) struct Evaluated<C: CurveAffine> {
    constructed: Constructed<C>,
}

impl Argument {
    pub(in crate::plonk) fn sample_blinding<C: CurveAffine, R: Rng>(
        &self,
        pk: &plonk::ProvingKey<C>,
        mut rng: R,
    ) -> PermutationBlinding<C::Scalar> {
        let chunk_len = permutation_chunk_len(pk.vk.cs_degree);
        let blinding_factors = pk.vk.cs.blinding_factors();

        PermutationBlinding {
            sets: self
                .columns
                .chunks(chunk_len)
                .map(|_| SetBlinding {
                    rows: (0..blinding_factors)
                        .map(|_| C::Scalar::random(&mut rng))
                        .collect(),
                    product_blind: Blind(C::Scalar::random(&mut rng)),
                })
                .collect(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn commit<
        C: CurveAffine,
        E: EncodedChallenge<C>,
        Ev: Copy + Send + Sync,
        R: Rng,
        T: TranscriptWrite<C, E>,
    >(
        &self,
        params: &Params<C>,
        pk: &plonk::ProvingKey<C>,
        pkey: &ProvingKey<C>,
        advice: &[Polynomial<C::Scalar, LagrangeCoeff>],
        fixed: &[Polynomial<C::Scalar, LagrangeCoeff>],
        instance: &[Polynomial<C::Scalar, LagrangeCoeff>],
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        circuit_index: usize,
        evaluator: &mut poly::Evaluator<Ev, C::Scalar, ExtendedLagrangeCoeff>,
        mut rng: R,
        transcript: &mut T,
    ) -> Result<Committed<C, Ev>, Error> {
        let mut sets = vec![];
        self.prepare_sets(
            params,
            pk,
            pkey,
            advice,
            fixed,
            instance,
            beta,
            gamma,
            |rows| {
                for z in rows {
                    *z = C::Scalar::random(&mut rng);
                }
                Blind(C::Scalar::random(&mut rng))
            },
            |set| {
                let set_index = sets.len();
                let permutation_product_coset = evaluator.register_poly_with_tag(
                    set.permutation_product_coset,
                    QuotientPoly::PermutationProduct {
                        circuit_index,
                        set_index,
                    }
                    .into(),
                );

                // Hash the permutation product commitment
                transcript.write_point(set.permutation_product_commitment)?;

                sets.push(CommittedSet {
                    permutation_product_poly: set.permutation_product_poly,
                    permutation_product_coset,
                    permutation_product_blind: set.permutation_product_blind,
                });
                Ok::<(), Error>(())
            },
        )?;

        Ok(Committed { sets })
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn prepare<C: CurveAffine>(
        &self,
        params: &Params<C>,
        pk: &plonk::ProvingKey<C>,
        pkey: &ProvingKey<C>,
        advice: &[Polynomial<C::Scalar, LagrangeCoeff>],
        fixed: &[Polynomial<C::Scalar, LagrangeCoeff>],
        instance: &[Polynomial<C::Scalar, LagrangeCoeff>],
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        blinding: PermutationBlinding<C::Scalar>,
    ) -> Prepared<C> {
        let mut blindings = blinding.sets.into_iter();
        let mut sets = Vec::with_capacity(blindings.len());
        let result: Result<(), Infallible> = self.prepare_sets(
            params,
            pk,
            pkey,
            advice,
            fixed,
            instance,
            beta,
            gamma,
            |rows| {
                let blinding = blindings
                    .next()
                    .expect("one blinding value set is sampled per permutation set");
                rows.copy_from_slice(&blinding.rows);
                blinding.product_blind
            },
            |set| {
                sets.push(set);
                Ok(())
            },
        );
        result.unwrap_or_else(|never| match never {});

        Prepared { sets }
    }

    /// Prepares one circuit's permutation sets concurrently without mutating
    /// the transcript or the shared polynomial evaluator.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn prepare_sets_in_parallel<C: CurveAffine>(
        &self,
        params: &Params<C>,
        pk: &plonk::ProvingKey<C>,
        pkey: &ProvingKey<C>,
        advice: &[Polynomial<C::Scalar, LagrangeCoeff>],
        fixed: &[Polynomial<C::Scalar, LagrangeCoeff>],
        instance: &[Polynomial<C::Scalar, LagrangeCoeff>],
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        blinding: PermutationBlinding<C::Scalar>,
    ) -> Prepared<C> {
        if blinding.sets.len() <= 1 {
            return self.prepare(
                params, pk, pkey, advice, fixed, instance, beta, gamma, blinding,
            );
        }

        let domain = &pk.vk.domain;
        let chunk_len = permutation_chunk_len(pk.vk.cs_degree);
        let blinding_factors = pk.vk.cs.blinding_factors();

        assert_eq!(self.columns.len(), pkey.permutations.len());
        assert_eq!(self.columns.len(), pkey.identity_columns.len());

        // Record the initial delta power for each set. The numerator ratios
        // are then independent across sets.
        let mut deltaomega = C::Scalar::ONE;
        let set_inputs = self
            .columns
            .chunks(chunk_len)
            .zip(pkey.permutations.chunks(chunk_len))
            .zip(pkey.identity_columns.chunks(chunk_len))
            .map(|((columns, permutations), identity_columns)| {
                let initial_deltaomega = deltaomega;
                for _ in columns {
                    deltaomega *= &C::Scalar::DELTA;
                }
                (
                    columns,
                    permutations,
                    initial_deltaomega,
                    identity_columns.iter().all(|&identity| identity),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(set_inputs.len(), blinding.sets.len());

        // Indexed collection preserves set order for the dependent prefix
        // chain and eventual transcript writes.
        let prepared_products = set_inputs
            .into_par_iter()
            .zip(blinding.sets.into_par_iter())
            .map(
                |((columns, permutations, initial_deltaomega, is_identity), blinding)| {
                    if is_identity && blinding_factors <= MAX_DIRECT_TRANSFORM_TAIL_LEN {
                        return PreparedProduct::Identity(blinding);
                    }
                    let (numerators, denominators, _) = prepare_fractions(
                        params,
                        domain,
                        columns,
                        permutations,
                        advice,
                        fixed,
                        instance,
                        beta,
                        gamma,
                        initial_deltaomega,
                        blinding_factors,
                    );
                    PreparedProduct::Fractions(PreparedFractions {
                        numerators,
                        denominators,
                        blinding,
                    })
                },
            )
            .collect::<Vec<_>>();

        // Each set starts with the preceding set's final product, so this
        // short prefix chain remains serial.
        let mut last_z = C::Scalar::ONE;
        let products = prepared_products
            .into_iter()
            .map(|prepared| match prepared {
                PreparedProduct::Fractions(prepared) => {
                    let blinding = prepared.blinding;
                    UnpreparedSet::Dense(build_product::<C>(
                        domain,
                        blinding_factors,
                        &mut last_z,
                        prepared.numerators,
                        prepared.denominators,
                        |rows| {
                            rows.copy_from_slice(&blinding.rows);
                            blinding.product_blind
                        },
                    ))
                }
                PreparedProduct::Identity(blinding) => UnpreparedSet::Identity {
                    constant: last_z,
                    blinding,
                },
            })
            .collect::<Vec<_>>();

        let sets = products
            .into_par_iter()
            .map(|set| match set {
                UnpreparedSet::Dense(set) => prepare_product(params, pk, set),
                UnpreparedSet::Identity { constant, blinding } => {
                    prepare_identity_product(params, pk, constant, blinding)
                }
            })
            .collect();

        Prepared { sets }
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare_sets<C: CurveAffine, E>(
        &self,
        params: &Params<C>,
        pk: &plonk::ProvingKey<C>,
        pkey: &ProvingKey<C>,
        advice: &[Polynomial<C::Scalar, LagrangeCoeff>],
        fixed: &[Polynomial<C::Scalar, LagrangeCoeff>],
        instance: &[Polynomial<C::Scalar, LagrangeCoeff>],
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        mut set_blinding: impl FnMut(&mut [C::Scalar]) -> Blind<C::Scalar>,
        mut finish_set: impl FnMut(PreparedSet<C>) -> Result<(), E>,
    ) -> Result<(), E> {
        let domain = &pk.vk.domain;

        // How many columns can be included in a single permutation polynomial?
        // We need to multiply by z(X) and (1 - (l_last(X) + l_blind(X))). This
        // will never underflow because of the requirement of at least a degree
        // 3 circuit for the permutation argument.
        let chunk_len = permutation_chunk_len(pk.vk.cs_degree);
        let blinding_factors = pk.vk.cs.blinding_factors();

        assert_eq!(self.columns.len(), pkey.permutations.len());
        assert_eq!(self.columns.len(), pkey.identity_columns.len());

        // Each column gets its own delta power.
        let mut deltaomega = C::Scalar::ONE;

        // Track the "last" value from the previous column set
        let mut last_z = C::Scalar::ONE;

        for ((columns, permutations), identity_columns) in self
            .columns
            .chunks(chunk_len)
            .zip(pkey.permutations.chunks(chunk_len))
            .zip(pkey.identity_columns.chunks(chunk_len))
        {
            let is_identity = identity_columns.iter().all(|&identity| identity)
                && blinding_factors <= MAX_DIRECT_TRANSFORM_TAIL_LEN;
            if is_identity {
                for _ in columns {
                    deltaomega *= &C::Scalar::DELTA;
                }
                let mut rows = vec![C::Scalar::ZERO; blinding_factors];
                let product_blind = set_blinding(&mut rows);
                finish_set(prepare_identity_product(
                    params,
                    pk,
                    last_z,
                    SetBlinding {
                        rows,
                        product_blind,
                    },
                ))?;
                continue;
            }

            let (numerators, denominators, next_deltaomega) = prepare_fractions(
                params,
                domain,
                columns,
                permutations,
                advice,
                fixed,
                instance,
                beta,
                gamma,
                deltaomega,
                blinding_factors,
            );
            deltaomega = next_deltaomega;
            let product = build_product::<C>(
                domain,
                blinding_factors,
                &mut last_z,
                numerators,
                denominators,
                |rows| set_blinding(rows),
            );
            finish_set(prepare_product(params, pk, product))?;
        }

        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
/// Builds the permutation constraint ASTs without evaluating polynomial rows.
///
/// The product leaves and permutation cosets must correspond, in order, to
/// [`Argument::columns`] split according to `cs_degree`. The column-leaf slices
/// must contain every column referenced by the argument.
pub(in crate::plonk) fn construct_constraints<E: Copy, F: WithSmallOrderMulGroup<3>>(
    argument: &Argument,
    cs_degree: usize,
    blinding_factors: usize,
    products: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
    advice_cosets: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
    fixed_cosets: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
    instance_cosets: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
    permutation_cosets: &[poly::AstLeaf<E, ExtendedLagrangeCoeff>],
    l0: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    l_blind: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
    l_last: poly::AstLeaf<E, ExtendedLagrangeCoeff>,
) -> Vec<poly::Ast<E, F, ExtendedLagrangeCoeff>> {
    let chunk_len = permutation_chunk_len(cs_degree);
    let last_rotation = Rotation(-((blinding_factors + 1) as i32));
    let mut expressions = vec![];

    // Enforce only for the first set.
    // l_0(X) * (1 - z_0(X)) = 0
    if let Some(first) = products.first() {
        expressions.push((poly::Ast::one() - *first) * l0);
    }

    // Enforce only for the last set.
    // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
    if let Some(last) = products.last() {
        expressions.push(((poly::Ast::from(*last) * *last) - *last) * l_last);
    }

    // Except for the first set, enforce.
    // l_0(X) * (z_i(X) - z_{i-1}(omega^(last) X)) = 0
    expressions.extend(
        products
            .iter()
            .skip(1)
            .zip(products.iter())
            .map(|(product, previous)| {
                (poly::Ast::from(*product) - previous.with_rotation(last_rotation)) * l0
            }),
    );

    // For every set, enforce the permutation grand-product relation.
    expressions.extend(
        products
            .iter()
            .zip(argument.columns.chunks(chunk_len))
            .zip(permutation_cosets.chunks(chunk_len))
            .enumerate()
            .map(|(chunk_index, ((product, columns), cosets))| {
                let mut left = poly::Ast::<_, F, _>::from(product.with_rotation(Rotation::next()));
                for (values, permutation) in columns
                    .iter()
                    .map(|&column| match column.column_type() {
                        Any::Advice => &advice_cosets[column.index()],
                        Any::Fixed => &fixed_cosets[column.index()],
                        Any::Instance => &instance_cosets[column.index()],
                    })
                    .zip(cosets.iter())
                {
                    left *= poly::Ast::<_, F, _>::from(*values)
                        + (poly::Ast::ChallengeTerm(poly::EvaluationChallenge::Beta)
                            * poly::Ast::from(*permutation))
                        + poly::Ast::ChallengeTerm(poly::EvaluationChallenge::Gamma);
                }

                let mut right = poly::Ast::from(*product);
                let mut current_delta = F::DELTA.pow_vartime([(chunk_index * chunk_len) as u64]);
                for values in columns.iter().map(|&column| match column.column_type() {
                    Any::Advice => &advice_cosets[column.index()],
                    Any::Fixed => &fixed_cosets[column.index()],
                    Any::Instance => &instance_cosets[column.index()],
                }) {
                    right *= poly::Ast::from(*values)
                        + poly::Ast::LinearChallengeTerm {
                            challenge: poly::EvaluationChallenge::Beta,
                            factor: current_delta,
                        }
                        + poly::Ast::ChallengeTerm(poly::EvaluationChallenge::Gamma);
                    current_delta *= &F::DELTA;
                }

                (left - right) * (poly::Ast::one() - (poly::Ast::from(l_last) + l_blind))
            }),
    );

    expressions
}

#[allow(clippy::too_many_arguments)]
fn prepare_fractions<C: CurveAffine>(
    params: &Params<C>,
    domain: &poly::EvaluationDomain<C::Scalar>,
    columns: &[plonk::Column<Any>],
    permutations: &[Polynomial<C::Scalar, LagrangeCoeff>],
    advice: &[Polynomial<C::Scalar, LagrangeCoeff>],
    fixed: &[Polynomial<C::Scalar, LagrangeCoeff>],
    instance: &[Polynomial<C::Scalar, LagrangeCoeff>],
    beta: ChallengeBeta<C>,
    gamma: ChallengeGamma<C>,
    mut deltaomega: C::Scalar,
    blinding_factors: usize,
) -> (Vec<C::Scalar>, Vec<C::Scalar>, C::Scalar) {
    let fraction_rows = params.n as usize - (blinding_factors + 1);
    let mut numerators = vec![C::Scalar::ZERO; params.n as usize];
    let mut denominators = vec![C::Scalar::ZERO; params.n as usize];
    let omega = domain.get_omega();
    let beta_delta = deltaomega * &*beta;
    super::super::parallelize_two(
        &mut numerators[..fraction_rows],
        &mut denominators[..fraction_rows],
        |numerators, denominators, start| {
            let omega_start = omega.pow_vartime([start as u64]);
            let mut column_beta_delta = beta_delta;
            for (column_index, (&column, permuted_values)) in
                columns.iter().zip(permutations).enumerate()
            {
                let values = match column.column_type() {
                    Any::Advice => advice,
                    Any::Fixed => fixed,
                    Any::Instance => instance,
                };
                let mut row_beta_deltaomega = column_beta_delta * &omega_start;
                for (((numerator, denominator), value), permuted_value) in numerators
                    .iter_mut()
                    .zip(denominators.iter_mut())
                    .zip(values[column.index()][start..].iter())
                    .zip(permuted_values[start..].iter())
                {
                    let numerator_factor = row_beta_deltaomega + &*gamma + value;
                    let denominator_factor = *beta * permuted_value + &*gamma + value;
                    if column_index == 0 {
                        *numerator = numerator_factor;
                        *denominator = denominator_factor;
                    } else {
                        *numerator *= &numerator_factor;
                        *denominator *= &denominator_factor;
                    }
                    row_beta_deltaomega *= &omega;
                }
                if column_index + 1 < columns.len() {
                    column_beta_delta *= &C::Scalar::DELTA;
                }
            }
        },
    );
    for _ in columns {
        deltaomega *= &C::Scalar::DELTA;
    }

    (numerators, denominators, deltaomega)
}

fn build_product<C: CurveAffine>(
    domain: &poly::EvaluationDomain<C::Scalar>,
    blinding_factors: usize,
    last_z: &mut C::Scalar,
    numerators: Vec<C::Scalar>,
    denominators: Vec<C::Scalar>,
    set_blinding: impl FnOnce(&mut [C::Scalar]) -> Blind<C::Scalar>,
) -> UntransformedSet<C::Scalar> {
    let usable_rows = numerators.len() - blinding_factors;
    let product = super::super::prefix_products_of_fractions(
        numerators,
        denominators,
        usable_rows - 1,
        *last_z,
    );

    let mut product = domain.lagrange_from_vec(product);
    let product_blind = set_blinding(&mut product[usable_rows..]);
    *last_z = product[usable_rows - 1];

    UntransformedSet {
        product,
        product_blind,
    }
}

fn prepare_product<C: CurveAffine>(
    params: &Params<C>,
    pk: &plonk::ProvingKey<C>,
    set: UntransformedSet<C::Scalar>,
) -> PreparedSet<C> {
    let blind = set.product_blind;
    let z = set.product;
    let constant_prefix = (z.len() == params.g_lagrange.len())
        .then(|| detect_constant_prefix(&z, pk.vk.cs.blinding_factors()))
        .flatten();
    let sparse_transform_prefix =
        constant_prefix.filter(|prefix| prefix.tail.len() <= MAX_DIRECT_TRANSFORM_TAIL_LEN);
    let (commitment, (polynomial, coset)) = crate::multicore::join(
        || {
            constant_prefix
                .map(|prefix| commit_constant_prefix(params, prefix, blind))
                .unwrap_or_else(|| params.commit_lagrange(&z, blind))
        },
        || {
            sparse_transform_prefix
                .map(|prefix| transform_constant_prefix(&pk.vk.domain, &pk.l0, prefix))
                .unwrap_or_else(|| {
                    let polynomial = pk
                        .vk
                        .domain
                        .lagrange_to_coeff_with_twiddles(z.clone(), &pk.fft_twiddles);
                    let coset = pk
                        .vk
                        .domain
                        .coeff_to_extended_with_twiddles(polynomial.clone(), &pk.fft_twiddles);
                    (polynomial, coset)
                })
        },
    );

    PreparedSet {
        permutation_product_poly: polynomial,
        permutation_product_coset: coset,
        permutation_product_commitment: commitment.to_affine(),
        permutation_product_blind: blind,
    }
}

/// Prepares an identity permutation set without materializing its fractions.
///
/// Every numerator factor equals its denominator factor, so every nonzero
/// ratio is one. Without a zero shared factor, retaining the incoming product
/// agrees with the generic fraction and prefix-product construction.
///
/// A zero shared factor makes the local row relation `0 = 0`, but retaining
/// the product need not give a valid witness for the complete chunk chain.
/// The generic path takes subsequent product states to zero; this shortcut
/// can retain a nonzero state. A later nonidentity chunk can then encounter
/// a zero denominator and nonzero numerator, making its row relation
/// impossible to satisfy with that incoming state.
///
/// This optimization accepts the resulting negligible completeness error:
/// an exceptional challenge can produce an unverifiable proof. Under the
/// production Fiat-Shamir transcript's random-oracle assumptions, advice is
/// committed before `beta` and `gamma` are sampled. For fixed advice and
/// `beta`, each shared factor vanishes at exactly one value of `gamma`.
/// With `M` relevant factors over a field of order `q`, a union bound is
/// `M / q`, up to the negligible bias from reducing 64-byte challenges.
/// This is not an unconditional correctness guarantee for forced or custom
/// challenges; see the
/// [accepted allowance](https://github.com/zakura-core/common/pull/396#issuecomment-5562831454).
fn prepare_identity_product<C: CurveAffine>(
    params: &Params<C>,
    pk: &plonk::ProvingKey<C>,
    constant: C::Scalar,
    blinding: SetBlinding<C::Scalar>,
) -> PreparedSet<C> {
    assert!(blinding.rows.len() <= MAX_DIRECT_TRANSFORM_TAIL_LEN);
    let prefix = ConstantPrefix {
        constant,
        prefix_len: params.n as usize - blinding.rows.len(),
        tail: &blinding.rows,
    };
    let blind = blinding.product_blind;
    let (commitment, (polynomial, coset)) = crate::multicore::join(
        || commit_constant_prefix(params, prefix, blind),
        || transform_constant_prefix(&pk.vk.domain, &pk.l0, prefix),
    );

    PreparedSet {
        permutation_product_poly: polynomial,
        permutation_product_coset: coset,
        permutation_product_commitment: commitment.to_affine(),
        permutation_product_blind: blind,
    }
}

fn detect_constant_prefix<'a, F: Field>(
    values: &'a [F],
    blinding_factors: usize,
) -> Option<ConstantPrefix<'a, F>> {
    let prefix_len = values.len().checked_sub(blinding_factors)?;
    let (&constant, prefix) = values.get(..prefix_len)?.split_first()?;
    if prefix.iter().any(|value| *value != constant) {
        return None;
    }

    Some(ConstantPrefix {
        constant,
        prefix_len,
        tail: &values[prefix_len..],
    })
}

/// Commits to a polynomial whose non-blinding rows are constant.
///
/// A constant Lagrange vector represents a constant coefficient polynomial,
/// so its commitment is the constant times `g[0]`. The remaining terms are
/// the differences between the blinded tail and that constant, plus the
/// commitment blind.
fn commit_constant_prefix<C: CurveAffine>(
    params: &Params<C>,
    prefix: ConstantPrefix<'_, C::Scalar>,
    blind: Blind<C::Scalar>,
) -> C::Curve {
    let mut scalars = Vec::with_capacity(prefix.tail.len() + 2);
    let mut bases = Vec::with_capacity(prefix.tail.len() + 2);
    if !bool::from(prefix.constant.is_zero()) {
        scalars.push(prefix.constant);
        bases.push(params.g[0]);
    }
    for (offset, &value) in prefix.tail.iter().enumerate() {
        let delta = value - prefix.constant;
        if !bool::from(delta.is_zero()) {
            scalars.push(delta);
            bases.push(params.g_lagrange[prefix.prefix_len + offset]);
        }
    }
    if !bool::from(blind.0.is_zero()) {
        scalars.push(blind.0);
        bases.push(params.w);
    }

    if scalars.is_empty() {
        C::Curve::identity()
    } else {
        best_multiexp::<C>(&scalars, &bases)
    }
}

/// Transforms a constant prefix plus a short tail without running FFTs.
///
/// For base-domain size `n`, the tail evaluation at row `n - r` contributes
/// `delta / n * (omega^k)^r` to coefficient `k`. On the extended coset it
/// contributes `delta * L_0(g * Omega^(k + extension * r))`, which is a cyclic
/// shift of the already-retained `L_0` evaluations.
fn transform_constant_prefix<F: WithSmallOrderMulGroup<3>>(
    domain: &poly::EvaluationDomain<F>,
    l0_extended: &Polynomial<F, ExtendedLagrangeCoeff>,
    prefix: ConstantPrefix<'_, F>,
) -> (Polynomial<F, Coeff>, Polynomial<F, ExtendedLagrangeCoeff>) {
    let tail_len = prefix.tail.len();
    assert!(tail_len <= MAX_DIRECT_TRANSFORM_TAIL_LEN);

    let n = prefix.prefix_len + tail_len;
    let mut coefficients = domain.empty_coeff();
    let mut extended = domain.empty_extended();
    assert_eq!(coefficients.len(), n);
    assert_eq!(l0_extended.len(), extended.len());
    assert_eq!(extended.len() % n, 0);

    if tail_len == 0 {
        coefficients[0] = prefix.constant;
        parallelize(&mut extended, |values, _| values.fill(prefix.constant));
        return (coefficients, extended);
    }

    // Index `r - 1` holds the correction for evaluation row `n - r`.
    assert!(n.is_power_of_two());
    let inverse_n = (0..n.trailing_zeros()).fold(F::ONE, |value, _| value * F::TWO_INV);
    let mut deltas = [F::ZERO; MAX_DIRECT_TRANSFORM_TAIL_LEN];
    let mut scaled_deltas = [F::ZERO; MAX_DIRECT_TRANSFORM_TAIL_LEN];
    for (index, &value) in prefix.tail.iter().rev().enumerate() {
        let delta = value - prefix.constant;
        deltas[index] = delta;
        scaled_deltas[index] = delta * inverse_n;
    }

    let extension = extended.len() / n;
    crate::multicore::join(
        || {
            let omega = domain.get_omega();
            parallelize(&mut coefficients, |coefficients, start| {
                let mut omega_power = omega.pow_vartime([start as u64]);
                for (offset, coefficient) in coefficients.iter_mut().enumerate() {
                    let mut value = scaled_deltas[tail_len - 1];
                    for delta in scaled_deltas[..tail_len - 1].iter().rev() {
                        value = value * omega_power + delta;
                    }
                    value *= omega_power;
                    if start + offset == 0 {
                        value += prefix.constant;
                    }
                    *coefficient = value;
                    omega_power *= omega;
                }
            });
        },
        || {
            let extended_len = extended.len();
            let wrapped_len = extension * tail_len;
            let unwrapped_len = extended_len - wrapped_len;
            let (unwrapped, wrapped) = extended.split_at_mut(unwrapped_len);

            parallelize(unwrapped, |values, start| {
                for (offset, value) in values.iter_mut().enumerate() {
                    let mut result = prefix.constant;
                    let mut l0_index = start + offset + extension;
                    for delta in &deltas[..tail_len] {
                        result += *delta * l0_extended[l0_index];
                        l0_index += extension;
                    }
                    *value = result;
                }
            });

            for (offset, value) in wrapped.iter_mut().enumerate() {
                let mut result = prefix.constant;
                let mut l0_index = unwrapped_len + offset + extension;
                for delta in &deltas[..tail_len] {
                    if l0_index >= extended_len {
                        l0_index -= extended_len;
                    }
                    result += *delta * l0_extended[l0_index];
                    l0_index += extension;
                }
                *value = result;
            }
        },
    );

    (coefficients, extended)
}

impl<C: CurveAffine> Prepared<C> {
    pub(in crate::plonk) fn commit<
        E: EncodedChallenge<C>,
        Ev: Copy + Send + Sync,
        T: TranscriptWrite<C, E>,
    >(
        self,
        evaluator: &mut poly::Evaluator<Ev, C::Scalar, ExtendedLagrangeCoeff>,
        transcript: &mut T,
        circuit_index: usize,
    ) -> Result<Committed<C, Ev>, Error> {
        let mut sets = Vec::with_capacity(self.sets.len());
        for (set_index, set) in self.sets.into_iter().enumerate() {
            let permutation_product_coset = evaluator.register_poly_with_tag(
                set.permutation_product_coset,
                QuotientPoly::PermutationProduct {
                    circuit_index,
                    set_index,
                }
                .into(),
            );

            // Hash the permutation product commitment
            transcript.write_point(set.permutation_product_commitment)?;

            sets.push(CommittedSet {
                permutation_product_poly: set.permutation_product_poly,
                permutation_product_coset,
                permutation_product_blind: set.permutation_product_blind,
            });
        }

        Ok(Committed { sets })
    }
}

impl<C: CurveAffine, Ev: Copy + Send + Sync> Committed<C, Ev> {
    /// Finishes the permutation argument without rebuilding its quotient ASTs.
    pub(in crate::plonk) fn into_constructed(self) -> Constructed<C> {
        Constructed {
            sets: self
                .sets
                .into_iter()
                .map(|set| ConstructedSet {
                    permutation_product_poly: set.permutation_product_poly,
                    permutation_product_blind: set.permutation_product_blind,
                })
                .collect(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn construct<'a>(
        self,
        pk: &'a plonk::ProvingKey<C>,
        p: &'a Argument,
        advice_cosets: &'a [poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        fixed_cosets: &'a [poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        instance_cosets: &'a [poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        permutation_cosets: &'a [poly::AstLeaf<Ev, ExtendedLagrangeCoeff>],
        l0: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
        l_blind: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
        l_last: poly::AstLeaf<Ev, ExtendedLagrangeCoeff>,
    ) -> (
        Constructed<C>,
        impl Iterator<Item = poly::Ast<Ev, C::Scalar, ExtendedLagrangeCoeff>> + 'a,
    ) {
        let constructed = Constructed {
            sets: self
                .sets
                .iter()
                .map(|set| ConstructedSet {
                    permutation_product_poly: set.permutation_product_poly.clone(),
                    permutation_product_blind: set.permutation_product_blind,
                })
                .collect(),
        };
        let products = self
            .sets
            .iter()
            .map(|set| set.permutation_product_coset)
            .collect::<Vec<_>>();
        let expressions = construct_constraints(
            p,
            pk.vk.cs_degree,
            pk.vk.cs.blinding_factors(),
            &products,
            advice_cosets,
            fixed_cosets,
            instance_cosets,
            permutation_cosets,
            l0,
            l_blind,
            l_last,
        );

        (constructed, expressions.into_iter())
    }
}

impl<C: CurveAffine> super::ProvingKey<C> {
    pub(in crate::plonk) fn open(
        &self,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = ProverQuery<'_, C>> + Clone {
        self.polys.iter().map(move |poly| ProverQuery {
            point: *x,
            poly,
            blind: Blind::default(),
        })
    }

    pub(in crate::plonk) fn evaluation_queries(
        &self,
    ) -> impl Iterator<Item = EvaluationQuery<'_, C::Scalar>> {
        self.polys.iter().map(|polynomial| EvaluationQuery {
            polynomial,
            point: EvaluationPoint::Current,
        })
    }

    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        &self,
        evaluations: &mut impl Iterator<Item = C::Scalar>,
        transcript: &mut T,
    ) -> Result<(), Error> {
        // Hash permutation evals
        for _ in &self.polys {
            let eval = evaluations
                .next()
                .expect("one result is returned for every permutation-key evaluation query");
            transcript.write_scalar(eval)?;
        }

        Ok(())
    }
}

impl<C: CurveAffine> Constructed<C> {
    pub(in crate::plonk) fn evaluation_queries(
        &self,
    ) -> impl Iterator<Item = EvaluationQuery<'_, C::Scalar>> {
        self.sets.iter().enumerate().flat_map(|(index, set)| {
            [
                Some(EvaluationQuery {
                    polynomial: &set.permutation_product_poly,
                    point: EvaluationPoint::Current,
                }),
                Some(EvaluationQuery {
                    polynomial: &set.permutation_product_poly,
                    point: EvaluationPoint::Next,
                }),
                (index + 1 < self.sets.len()).then_some(EvaluationQuery {
                    polynomial: &set.permutation_product_poly,
                    point: EvaluationPoint::Last,
                }),
            ]
            .into_iter()
            .flatten()
        })
    }

    pub(in crate::plonk) fn evaluate<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        self,
        evaluations: &mut impl Iterator<Item = C::Scalar>,
        transcript: &mut T,
    ) -> Result<Evaluated<C>, Error> {
        let evaluation_count = self.evaluation_queries().count();
        for _ in 0..evaluation_count {
            let evaluation = evaluations
                .next()
                .expect("one result is returned for every permutation evaluation query");
            transcript.write_scalar(evaluation)?;
        }

        Ok(Evaluated { constructed: self })
    }
}

impl<C: CurveAffine> Evaluated<C> {
    pub(in crate::plonk) fn open<'a>(
        &'a self,
        pk: &'a plonk::ProvingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = ProverQuery<'a, C>> + Clone {
        let blinding_factors = pk.vk.cs.blinding_factors();
        let x_next = pk.vk.domain.rotate_omega(*x, Rotation::next());
        let x_last = pk
            .vk
            .domain
            .rotate_omega(*x, Rotation(-((blinding_factors + 1) as i32)));

        iter::empty()
            .chain(self.constructed.sets.iter().flat_map(move |set| {
                iter::empty()
                    // Open permutation product commitments at x and \omega x
                    .chain(Some(ProverQuery {
                        point: *x,
                        poly: &set.permutation_product_poly,
                        blind: set.permutation_product_blind,
                    }))
                    .chain(Some(ProverQuery {
                        point: x_next,
                        poly: &set.permutation_product_poly,
                        blind: set.permutation_product_blind,
                    }))
            }))
            // Open it at \omega^{last} x for all but the last set. This rotation is only
            // sensical for the first row, but we only use this rotation in a constraint
            // that is gated on l_0.
            .chain(
                self.constructed
                    .sets
                    .iter()
                    .rev()
                    .skip(1)
                    .flat_map(move |set| {
                        Some(ProverQuery {
                            point: x_last,
                            poly: &set.permutation_product_poly,
                            blind: set.permutation_product_blind,
                        })
                    }),
            )
    }
}

#[cfg(test)]
mod constant_prefix_tests {
    use super::{commit_constant_prefix, detect_constant_prefix};
    use crate::{
        arithmetic::CurveAffine,
        poly::{
            EvaluationDomain, LagrangeCoeff, Polynomial,
            commitment::{Blind, Params},
        },
    };
    use group::ff::{Field, WithSmallOrderMulGroup};
    use pasta_curves::{EpAffine, EqAffine, Fp, Fq};
    use proptest::prelude::*;

    const K: u32 = 4;
    const BLINDING_FACTORS: usize = 5;

    fn try_commit_constant_prefix<C: CurveAffine>(
        params: &Params<C>,
        values: &[C::Scalar],
        blind: Blind<C::Scalar>,
        blinding_factors: usize,
    ) -> Option<C::Curve> {
        if values.len() != params.g_lagrange.len() {
            return None;
        }

        detect_constant_prefix(values, blinding_factors)
            .map(|prefix| commit_constant_prefix(params, prefix, blind))
    }

    fn polynomial_with_constant_prefix<C: CurveAffine>(
        constant: C::Scalar,
        tail: &[C::Scalar],
    ) -> Polynomial<C::Scalar, LagrangeCoeff> {
        let domain = EvaluationDomain::new(1, K);
        let mut values = vec![constant; 1 << K];
        let tail_start = values.len() - tail.len();
        values[tail_start..].copy_from_slice(tail);
        domain.lagrange_from_vec(values)
    }

    fn assert_edge_constants_match<C: CurveAffine>()
    where
        C::Scalar: From<u64>,
    {
        let params = Params::<C>::new(K);
        let zero_tail = [C::Scalar::ZERO; BLINDING_FACTORS];
        let zero_polynomial = polynomial_with_constant_prefix::<C>(C::Scalar::ZERO, &zero_tail);
        let zero_blind = Blind(C::Scalar::ZERO);
        let sparse_zero =
            try_commit_constant_prefix(&params, &zero_polynomial, zero_blind, BLINDING_FACTORS)
                .expect("the zero polynomial has a constant prefix");
        assert_eq!(
            sparse_zero,
            params.commit_lagrange(&zero_polynomial, zero_blind)
        );

        for constant in [C::Scalar::ZERO, C::Scalar::ONE, C::Scalar::from(17)] {
            for blind in [C::Scalar::ZERO, C::Scalar::from(29)] {
                let tail = [
                    constant,
                    C::Scalar::ZERO,
                    C::Scalar::ONE,
                    C::Scalar::from(41),
                    constant,
                ];
                let polynomial = polynomial_with_constant_prefix::<C>(constant, &tail);
                let blind = Blind(blind);

                let sparse =
                    try_commit_constant_prefix(&params, &polynomial, blind, BLINDING_FACTORS)
                        .expect("the polynomial has a constant prefix");
                assert_eq!(sparse, params.commit_lagrange(&polynomial, blind));
            }
        }
    }

    fn assert_sparse_tail_transforms_match<F: WithSmallOrderMulGroup<3>>() {
        let domain = EvaluationDomain::<F>::new(9, K);
        let twiddles = domain.proving_key_twiddles();
        let mut l0 = domain.empty_lagrange();
        l0[0] = F::ONE;
        let l0 = domain.lagrange_to_coeff_with_twiddles(l0, &twiddles);
        let l0 = domain.coeff_to_extended_with_twiddles(l0, &twiddles);

        for tail_len in 0..=super::MAX_DIRECT_TRANSFORM_TAIL_LEN {
            for constant in [F::ZERO, F::from(17)] {
                let mut values = vec![constant; 1 << K];
                for (index, value) in values[(1 << K) - tail_len..].iter_mut().enumerate() {
                    *value = match index % 3 {
                        0 => constant,
                        1 => F::ZERO,
                        _ => F::from(41 + index as u64),
                    };
                }
                let polynomial = domain.lagrange_from_vec(values);
                let prefix = detect_constant_prefix(&polynomial, tail_len)
                    .expect("the test polynomial has a constant prefix");

                let expected_coefficients =
                    domain.lagrange_to_coeff_with_twiddles(polynomial.clone(), &twiddles);
                let expected_extended = domain
                    .coeff_to_extended_with_twiddles(expected_coefficients.clone(), &twiddles);
                let (actual_coefficients, actual_extended) =
                    super::transform_constant_prefix(&domain, &l0, prefix);

                assert_eq!(&actual_coefficients[..], &expected_coefficients[..]);
                assert_eq!(&actual_extended[..], &expected_extended[..]);
            }
        }
    }

    #[test]
    fn constant_prefix_matches_dense_commitment_for_edge_constants() {
        assert_edge_constants_match::<EqAffine>();
        assert_edge_constants_match::<EpAffine>();
    }

    #[test]
    fn sparse_tail_transforms_match_ffts_for_both_pasta_fields() {
        assert_sparse_tail_transforms_match::<Fp>();
        assert_sparse_tail_transforms_match::<Fq>();
    }

    #[test]
    fn nonconstant_or_empty_prefix_uses_the_dense_fallback() {
        let params = Params::<EqAffine>::new(K);
        let tail = [Fp::from(2); BLINDING_FACTORS];
        let mut polynomial = polynomial_with_constant_prefix::<EqAffine>(Fp::from(7), &tail);
        polynomial[3] = Fp::from(8);
        let blind = Blind(Fp::from(11));

        assert!(
            try_commit_constant_prefix(&params, &polynomial, blind, BLINDING_FACTORS).is_none()
        );
        assert!(try_commit_constant_prefix(&params, &polynomial, blind, 1 << K).is_none());
        assert!(try_commit_constant_prefix(&params, &polynomial, blind, (1 << K) + 1).is_none());

        let fallback = try_commit_constant_prefix(&params, &polynomial, blind, BLINDING_FACTORS)
            .unwrap_or_else(|| params.commit_lagrange(&polynomial, blind));
        assert_eq!(fallback, params.commit_lagrange(&polynomial, blind));
    }

    #[test]
    fn wrong_length_is_declined() {
        let params = Params::<EqAffine>::new(K);
        let blind = Blind(Fp::from(11));
        let short = vec![Fp::from(7); params.g_lagrange.len() - 1];
        let long = vec![Fp::from(7); params.g_lagrange.len() + 1];

        assert!(try_commit_constant_prefix(&params, &short, blind, BLINDING_FACTORS).is_none());
        assert!(try_commit_constant_prefix(&params, &long, blind, BLINDING_FACTORS).is_none());
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(32))]

        #[test]
        fn arbitrary_constant_prefixes_match_dense_commitments(
            constant in any::<u64>(),
            tail in prop::collection::vec(any::<u64>(), BLINDING_FACTORS),
            blind in any::<u64>(),
        ) {
            let params = Params::<EqAffine>::new(K);
            let constant = Fp::from(constant);
            let tail = tail.into_iter().map(Fp::from).collect::<Vec<_>>();
            let polynomial = polynomial_with_constant_prefix::<EqAffine>(constant, &tail);
            let blind = Blind(Fp::from(blind));

            let sparse = try_commit_constant_prefix(
                &params,
                &polynomial,
                blind,
                BLINDING_FACTORS,
            )
            .expect("the polynomial has a constant prefix");
            prop_assert_eq!(sparse, params.commit_lagrange(&polynomial, blind));
        }
    }
}

#[cfg(all(test, feature = "multicore"))]
mod tests {
    use super::permutation_chunk_len;
    use crate::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error, SingleVerifier, create_proof,
            keygen_pk, keygen_vk, verify_proof,
        },
        poly::commitment::Params,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use pasta_curves::{EqAffine, Fp};
    use rand::{SeedableRng, rngs::StdRng};

    const COPIED_COLUMNS: usize = 3;
    const EQUALITY_COLUMNS: usize = 7;
    const MINIMUM_DEGREE: usize = 4;
    const PROOF_K: u32 = 7;
    const MAX_PROOF_CIRCUITS: usize = 4;
    const PROOF_CIRCUIT_COUNTS: [usize; 3] = [1, 2, MAX_PROOF_CIRCUITS];
    const PROOF_THREAD_COUNTS: [usize; 2] = [6, 10];
    const PROOF_SEED: u64 = 0x5045_524d_5554_4508;

    #[derive(Clone, Copy)]
    struct PermutationConfig {
        columns: [Column<Advice>; EQUALITY_COLUMNS],
    }

    #[derive(Clone, Copy)]
    struct PermutationCircuit {
        value: Fp,
    }

    impl Circuit<Fp> for PermutationCircuit {
        type Config = PermutationConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self { value: Fp::from(0) }
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            meta.set_minimum_degree(MINIMUM_DEGREE);
            let columns = std::array::from_fn(|_| meta.advice_column());
            for column in columns.iter().copied() {
                meta.enable_equality(column);
            }
            PermutationConfig { columns }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "permutation copies",
                |mut region| {
                    let mut cells = Vec::with_capacity(COPIED_COLUMNS);
                    for (offset, column) in config.columns[..COPIED_COLUMNS].iter().enumerate() {
                        cells.push(
                            region
                                .assign_advice(
                                    || "value",
                                    *column,
                                    offset,
                                    || Value::known(self.value),
                                )?
                                .cell(),
                        );
                    }
                    for cells in cells.windows(2) {
                        region.constrain_equal(cells[0], cells[1])?;
                    }
                    Ok(())
                },
            )
        }
    }

    #[test]
    fn proof_bytes_match_identity_shortcut_and_preparation_schedules() {
        // This domain is large enough for `parallelize` to assign more than
        // one chunk at the tested worker counts, covering nonzero offsets.
        let params: Params<EqAffine> = Params::new(PROOF_K);
        let circuit = PermutationCircuit { value: Fp::from(0) };
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");

        let columns = pk.vk.cs.permutation.get_columns();
        assert_eq!(columns.len(), EQUALITY_COLUMNS);
        assert_eq!(
            pk.permutation.identity_columns,
            [false, false, false, true, true, true, true]
        );
        let chunk_len = permutation_chunk_len(pk.vk.cs_degree);
        assert!(
            columns.chunks(chunk_len).count() > 1,
            "the test requires several permutation sets",
        );
        assert_ne!(
            columns.len() % chunk_len,
            0,
            "the test requires a partial final permutation set",
        );

        let circuits: [PermutationCircuit; MAX_PROOF_CIRCUITS] =
            std::array::from_fn(|index| PermutationCircuit {
                value: Fp::from(index as u64 + 1),
            });
        let no_instance_columns: &[&[Fp]] = &[];
        let instances = [no_instance_columns; MAX_PROOF_CIRCUITS];

        let mut generic_pk = pk.clone();
        generic_pk.permutation.identity_columns.fill(false);

        let prove = |pk: &crate::plonk::ProvingKey<EqAffine>, circuit_count, threads| {
            let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
            maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap()
                .install(|| {
                    create_proof(
                        &params,
                        pk,
                        &circuits[..circuit_count],
                        &instances[..circuit_count],
                        StdRng::seed_from_u64(PROOF_SEED),
                        &mut transcript,
                    )
                })
                .expect("proof generation should not fail");
            transcript.finalize()
        };

        let verify = |proof: &[u8], circuit_count| {
            let strategy = SingleVerifier::new(&params);
            let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof);
            verify_proof(
                &params,
                pk.get_vk(),
                strategy,
                &instances[..circuit_count],
                &mut transcript,
            )
            .expect("proof verification should not fail");
        };

        for circuit_count in PROOF_CIRCUIT_COUNTS {
            let serial = prove(&pk, circuit_count, 1);
            let generic = prove(&generic_pk, circuit_count, 1);
            assert_eq!(serial, generic);
            verify(&serial, circuit_count);
            for threads in PROOF_THREAD_COUNTS {
                let parallel = prove(&pk, circuit_count, threads);
                assert_eq!(serial, parallel);
                verify(&parallel, circuit_count);
            }
        }
    }

    #[test]
    fn identity_product_remains_valid_when_a_shared_factor_is_zero() {
        // This checks only an isolated identity chunk's row and terminal
        // relations. It does not establish compatibility with a later
        // nonidentity chunk; see `prepare_identity_product` for the accepted
        // negligible completeness error in the full chain.
        use group::ff::{Field, PrimeField};

        const ROWS: usize = 16;
        const COLLISION_ROW: usize = 7;

        let beta = Fp::from(17);
        let gamma = Fp::from(29);
        let omega = Fp::ROOT_OF_UNITY;
        let mut delta_omega = Fp::ONE;
        let mut values = [Fp::ZERO; ROWS];
        let mut permutations = [Fp::ZERO; ROWS];
        for row in 0..ROWS {
            permutations[row] = delta_omega;
            values[row] = Fp::from(row as u64 + 1);
            delta_omega *= omega;
        }
        values[COLLISION_ROW] = -(beta * permutations[COLLISION_ROW] + gamma);

        for retained_product in [Fp::ZERO, Fp::ONE] {
            let mut saw_zero = false;
            for row in 0..ROWS - 1 {
                let numerator = values[row] + beta * permutations[row] + gamma;
                let denominator = values[row] + beta * permutations[row] + gamma;
                saw_zero |= bool::from(denominator.is_zero());

                // Keeping z unchanged satisfies this local row relation,
                // including the collision where both sides are zero.
                assert_eq!(
                    retained_product * denominator - retained_product * numerator,
                    Fp::ZERO
                );
            }
            assert!(saw_zero);
            assert_eq!(retained_product.square() - retained_product, Fp::ZERO);
        }
    }
}
