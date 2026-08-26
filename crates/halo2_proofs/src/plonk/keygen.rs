#![allow(clippy::int_plus_one)]

use std::ops::Range;

use ff::{Field, FromUniformBytes};
use group::Curve;
use maybe_rayon::prelude::*;

use super::{
    Assigned, Error, LagrangeCoeff, Polynomial, ProvingKey, VerifyingKey,
    circuit::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Fixed, FloorPlanner, Instance,
        Selector,
    },
    permutation,
};
use crate::{
    arithmetic::{CurveAffine, best_multiexp},
    circuit::Value,
    poly::{
        EvaluationDomain, batch_invert_assigned,
        commitment::{Blind, Params},
    },
};

// Compacting pays for its scan and allocation once at least a quarter of a
// fixed polynomial's terms are zero.
const SPARSE_FIXED_COMMITMENT_ZERO_FRACTION_DENOMINATOR: usize = 4;

fn commit_fixed_lagrange<C: CurveAffine>(
    params: &Params<C>,
    polynomial: &Polynomial<C::Scalar, LagrangeCoeff>,
) -> C::Curve {
    #[cfg(feature = "orbits")]
    if params.lagrange_table().is_some() {
        return params.commit_lagrange(polynomial, Blind::default());
    }

    let zero_count = polynomial
        .iter()
        .filter(|scalar| bool::from(scalar.is_zero()))
        .count();

    if polynomial.len() == params.g_lagrange.len()
        && zero_count * SPARSE_FIXED_COMMITMENT_ZERO_FRACTION_DENOMINATOR >= polynomial.len()
    {
        let mut scalars = Vec::with_capacity(polynomial.len() - zero_count + 1);
        let mut bases = Vec::with_capacity(scalars.capacity());
        for (scalar, base) in polynomial.iter().zip(&params.g_lagrange) {
            if !bool::from(scalar.is_zero()) {
                scalars.push(*scalar);
                bases.push(*base);
            }
        }
        scalars.push(Blind::default().0);
        bases.push(params.w);

        best_multiexp::<C>(&scalars, &bases)
    } else {
        params.commit_lagrange(polynomial, Blind::default())
    }
}

pub(crate) fn create_domain<C, ConcreteCircuit>(
    params: &Params<C>,
) -> (
    EvaluationDomain<C::Scalar>,
    ConstraintSystem<C::Scalar>,
    ConcreteCircuit::Config,
)
where
    C: CurveAffine,
    ConcreteCircuit: Circuit<C::Scalar>,
{
    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut cs);

    let degree = cs.degree();

    let domain = EvaluationDomain::new(degree as u32, params.k);

    (domain, cs, config)
}

/// Assembly to be used in circuit synthesis.
#[derive(Debug)]
struct Assembly<F: Field> {
    k: u32,
    fixed: Vec<Polynomial<Assigned<F>, LagrangeCoeff>>,
    permutation: permutation::keygen::Assembly,
    selectors: Vec<Vec<bool>>,
    // A range of available rows for assignment and copies.
    usable_rows: Range<usize>,
    _marker: std::marker::PhantomData<F>,
}

impl<F: Field> Assignment<F> for Assembly<F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.selectors[selector.0][row] = true;

        Ok(())
    }

    fn query_instance(&self, _: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        // There is no instance in this context.
        Ok(Value::unknown())
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Advice>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // We only care about fixed columns here
        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        *self
            .fixed
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&left_row) || !self.usable_rows.contains(&right_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.permutation
            .copy(left_column, left_row, right_column, right_row)
    }

    fn fill_from_row(
        &mut self,
        column: Column<Fixed>,
        from_row: usize,
        to: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&from_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        let col = self
            .fixed
            .get_mut(column.index())
            .ok_or(Error::BoundsFailure)?;

        let filler = to.assign()?;
        for row in self.usable_rows.clone().skip(from_row) {
            col[row] = filler;
        }

        Ok(())
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

/// Generate a `VerifyingKey` from an instance of `Circuit`.
pub fn keygen_vk<C, ConcreteCircuit>(
    params: &Params<C>,
    circuit: &ConcreteCircuit,
) -> Result<VerifyingKey<C>, Error>
where
    C: CurveAffine,
    C::Scalar: FromUniformBytes<64>,
    ConcreteCircuit: Circuit<C::Scalar>,
{
    let (domain, cs, config) = create_domain::<C, ConcreteCircuit>(params);

    if (params.n as usize) < cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k));
    }

    let mut assembly: Assembly<C::Scalar> = Assembly {
        k: params.k,
        fixed: vec![domain.empty_lagrange_assigned(); cs.num_fixed_columns],
        permutation: permutation::keygen::Assembly::new(params.n as usize, &cs.permutation),
        selectors: vec![vec![false; params.n as usize]; cs.num_selectors],
        usable_rows: 0..params.n as usize - (cs.blinding_factors() + 1),
        _marker: std::marker::PhantomData,
    };

    // Synthesize the circuit to obtain URS
    ConcreteCircuit::FloorPlanner::synthesize(
        &mut assembly,
        circuit,
        config,
        cs.constants.clone(),
    )?;

    let mut fixed = batch_invert_assigned(assembly.fixed);
    let (cs, selector_polys, _) = cs.compress_selectors(assembly.selectors);
    fixed.extend(
        selector_polys
            .into_iter()
            .map(|poly| domain.lagrange_from_vec(poly)),
    );

    let permutation_vk = assembly
        .permutation
        .build_vk(params, &domain, &cs.permutation);

    let fixed_commitments_projective = fixed
        .iter()
        .map(|polynomial| commit_fixed_lagrange(params, polynomial))
        .collect::<Vec<_>>();
    let mut fixed_commitments = vec![C::identity(); fixed_commitments_projective.len()];
    C::Curve::batch_normalize(&fixed_commitments_projective, &mut fixed_commitments);

    Ok(VerifyingKey::from_parts(
        domain,
        fixed_commitments,
        permutation_vk,
        cs,
    ))
}

/// Generate a `ProvingKey` from a `VerifyingKey` and an instance of `Circuit`.
pub fn keygen_pk<C, ConcreteCircuit>(
    params: &Params<C>,
    vk: VerifyingKey<C>,
    circuit: &ConcreteCircuit,
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    ConcreteCircuit: Circuit<C::ScalarExt> + Sync,
    <ConcreteCircuit as Circuit<C::ScalarExt>>::Config: Send,
{
    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut cs);

    let cs = cs;

    if (params.n as usize) < cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k));
    }

    let mut assembly: Assembly<C::Scalar> = Assembly {
        k: params.k,
        fixed: vec![vk.domain.empty_lagrange_assigned(); cs.num_fixed_columns],
        permutation: permutation::keygen::Assembly::new(params.n as usize, &cs.permutation),
        selectors: vec![vec![false; params.n as usize]; cs.num_selectors],
        usable_rows: 0..params.n as usize - (cs.blinding_factors() + 1),
        _marker: std::marker::PhantomData,
    };

    // Synthesize the circuit to obtain URS and retain reusable planning data.
    let floor_plan = ConcreteCircuit::FloorPlanner::synthesize_batch(
        core::slice::from_mut(&mut assembly),
        core::slice::from_ref(circuit),
        config,
        &cs.constants,
        None,
    )?;

    let mut fixed = batch_invert_assigned(assembly.fixed);
    let (cs, selector_polys, compressed_selectors) = cs.compress_selectors(assembly.selectors);
    fixed.extend(
        selector_polys
            .into_iter()
            .map(|poly| vk.domain.lagrange_from_vec(poly)),
    );

    let fft_twiddles = vk.domain.proving_key_twiddles();
    let (fixed_polys, fixed_cosets) = vk
        .domain
        .batch_lagrange_to_coeff_and_extended(&fixed, &fft_twiddles);

    let compressed_selector_cosets = compressed_selectors
        .into_par_iter()
        .map(|(column_index, combination_len, assigned_root)| {
            if combination_len < crate::MIN_SELECTOR_FAMILY_LEN {
                return None;
            }

            let mut selector = fixed_cosets[column_index].clone();
            for value in selector.iter_mut() {
                let query = *value;
                let mut result = query;
                for root in 1..=combination_len {
                    if root != assigned_root {
                        result *= C::Scalar::from(root as u64) - query;
                    }
                }
                *value = result;
            }

            Some(super::CompressedSelectorCoset {
                column_index,
                combination_len,
                assigned_root,
                selector,
            })
        })
        .collect::<Vec<Option<_>>>()
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();

    let permutation_pk =
        assembly
            .permutation
            .build_pk(params, &vk.domain, &cs.permutation, &fft_twiddles);

    // Compute l_0(X)
    // TODO: this can be done more efficiently
    let mut l0 = vk.domain.empty_lagrange();
    l0[0] = C::Scalar::ONE;
    let l0 = vk.domain.lagrange_to_coeff_with_twiddles(l0, &fft_twiddles);
    let l0 = vk.domain.coeff_to_extended_with_twiddles(l0, &fft_twiddles);

    // Compute l_blind(X) which evaluates to 1 for each blinding factor row
    // and 0 otherwise over the domain.
    let mut l_blind = vk.domain.empty_lagrange();
    for evaluation in l_blind[..].iter_mut().rev().take(cs.blinding_factors()) {
        *evaluation = C::Scalar::ONE;
    }
    let l_blind = vk
        .domain
        .lagrange_to_coeff_with_twiddles(l_blind, &fft_twiddles);
    let l_blind = vk
        .domain
        .coeff_to_extended_with_twiddles(l_blind, &fft_twiddles);

    // Compute l_last(X) which evaluates to 1 on the first inactive row (just
    // before the blinding factors) and 0 otherwise over the domain
    let mut l_last = vk.domain.empty_lagrange();
    l_last[params.n as usize - cs.blinding_factors() - 1] = C::Scalar::ONE;
    let l_last = vk
        .domain
        .lagrange_to_coeff_with_twiddles(l_last, &fft_twiddles);
    let l_last = vk
        .domain
        .coeff_to_extended_with_twiddles(l_last, &fft_twiddles);

    Ok(ProvingKey {
        vk,
        l0,
        l_blind,
        l_last,
        fixed_values: fixed,
        fixed_polys,
        fixed_cosets,
        compressed_selector_cosets: compressed_selector_cosets.into(),
        permutation: permutation_pk,
        fft_twiddles,
        floor_plan,
    })
}

#[cfg(test)]
mod tests {
    use super::commit_fixed_lagrange;
    use crate::{
        pasta::{EqAffine, Fp},
        poly::{
            EvaluationDomain,
            commitment::{Blind, Params},
        },
    };

    #[test]
    fn sparse_fixed_commitment_matches_generic_commitment() {
        const K: u32 = 4;

        let params = Params::<EqAffine>::new(K);
        let domain = EvaluationDomain::new(1, K);
        let mut polynomial = domain.empty_lagrange();
        polynomial[0] = Fp::from(3);
        polynomial[5] = Fp::from(7);

        assert_eq!(
            commit_fixed_lagrange(&params, &polynomial),
            params.commit_lagrange(&polynomial, Blind::default())
        );
    }
}
