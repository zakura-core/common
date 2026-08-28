#![allow(clippy::int_plus_one)]

use std::{cmp::Reverse, mem::size_of, ops::Range};

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

#[derive(Debug)]
struct CompressedSelectorFamily {
    column_index: usize,
    combination_len: usize,
    assigned_roots: Vec<usize>,
}

impl CompressedSelectorFamily {
    fn additional_cached_polynomials(&self) -> Option<usize> {
        // The root-one output reuses the family's source coset.
        self.combination_len.checked_sub(1)
    }
}

// This bounds only field-element payload newly retained for
// compressed-selector cosets beyond the proving key's existing polynomials.
// Allocator rounding and the small `Box`/polynomial metadata are not included.
const MEBIBYTE: usize = 1024 * 1024;
const MAX_ADDITIONAL_COMPRESSED_SELECTOR_CACHE_BYTES: usize = 21 * MEBIBYTE;

#[derive(Debug)]
struct CompressedSelectorCachePlan {
    families: Vec<CompressedSelectorFamily>,
    additional_payload_bytes: usize,
}

fn group_compressed_selectors(
    compressed_selectors: Vec<(usize, usize, usize)>,
) -> Vec<CompressedSelectorFamily> {
    let mut families: Vec<CompressedSelectorFamily> = vec![];

    for (column_index, combination_len, assigned_root) in compressed_selectors {
        if combination_len < crate::MIN_SELECTOR_FAMILY_LEN {
            continue;
        }

        match families
            .iter_mut()
            .find(|family| family.column_index == column_index)
        {
            Some(family) => {
                assert_eq!(family.combination_len, combination_len);
                family.assigned_roots.push(assigned_root);
            }
            None => families.push(CompressedSelectorFamily {
                column_index,
                combination_len,
                assigned_roots: vec![assigned_root],
            }),
        }
    }

    for family in &families {
        assert_eq!(family.assigned_roots.len(), family.combination_len);
        assert!(
            family
                .assigned_roots
                .iter()
                .copied()
                .eq(1..=family.combination_len)
        );
    }

    families
}

fn plan_compressed_selector_cache(
    families: Vec<CompressedSelectorFamily>,
    selector_len: usize,
    element_size: usize,
    max_payload_bytes: usize,
) -> CompressedSelectorCachePlan {
    // The enumeration index makes the tie-break explicit instead of relying
    // on the sort implementation's stability.
    let mut families = families.into_iter().enumerate().collect::<Vec<_>>();
    families.sort_by_key(|(index, family)| (Reverse(family.combination_len), *index));

    let mut selected = Vec::new();
    let mut additional_payload_bytes = 0usize;
    for (_, family) in families {
        let Some(family_payload_bytes) = family
            .additional_cached_polynomials()
            .and_then(|polynomials| polynomials.checked_mul(selector_len))
            .and_then(|elements| elements.checked_mul(element_size))
        else {
            // An unrepresentable payload cannot fit in a `usize` budget.
            continue;
        };
        let Some(next_payload_bytes) = additional_payload_bytes.checked_add(family_payload_bytes)
        else {
            continue;
        };
        if next_payload_bytes <= max_payload_bytes {
            additional_payload_bytes = next_payload_bytes;
            selected.push(family);
        }
    }

    CompressedSelectorCachePlan {
        families: selected,
        additional_payload_bytes,
    }
}

fn evaluate_compressed_selector_family<F: Field + From<u64>>(
    query_and_first_selector: &mut [F],
    mut selectors: Vec<&mut [F]>,
    min_chunk_len: usize,
) {
    let combination_len = selectors.len() + 1;
    assert!(combination_len >= crate::MIN_SELECTOR_FAMILY_LEN);
    assert!(
        selectors
            .iter()
            .all(|selector| selector.len() == query_and_first_selector.len())
    );

    if query_and_first_selector.len() <= min_chunk_len {
        for offset in 0..query_and_first_selector.len() {
            let query = query_and_first_selector[offset];
            // For root `a`, combine the shared products
            //
            // q * product_{r < a}(r - q) * product_{r > a}(r - q).
            let mut prefix = query;
            query_and_first_selector[offset] = prefix;
            for assigned_root in 1..combination_len {
                prefix *= F::from(assigned_root as u64) - query;
                selectors[assigned_root - 1][offset] = prefix;
            }

            let mut suffix = F::from(combination_len as u64) - query;
            for assigned_root in (0..combination_len - 1).rev() {
                if assigned_root == 0 {
                    query_and_first_selector[offset] *= suffix;
                } else {
                    selectors[assigned_root - 1][offset] *= suffix;
                }
                if assigned_root > 0 {
                    suffix *= F::from((assigned_root + 1) as u64) - query;
                }
            }
        }
        return;
    }

    let midpoint = query_and_first_selector.len() / 2;
    let (query_left, query_right) = query_and_first_selector.split_at_mut(midpoint);
    let (selector_left, selector_right) = selectors
        .into_iter()
        .map(|selector| selector.split_at_mut(midpoint))
        .unzip();
    crate::multicore::join(
        || evaluate_compressed_selector_family(query_left, selector_left, min_chunk_len),
        || evaluate_compressed_selector_family(query_right, selector_right, min_chunk_len),
    );
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
    let (fixed_polys, mut fixed_cosets) = vk
        .domain
        .batch_lagrange_to_coeff_and_extended(&fixed, &fft_twiddles);

    let cache_plan = plan_compressed_selector_cache(
        group_compressed_selectors(compressed_selectors),
        vk.domain.extended_len(),
        size_of::<C::Scalar>(),
        MAX_ADDITIONAL_COMPRESSED_SELECTOR_CACHE_BYTES,
    );
    assert!(cache_plan.additional_payload_bytes <= MAX_ADDITIONAL_COMPRESSED_SELECTOR_CACHE_BYTES);

    let mut selector_families_by_column = std::iter::repeat_with(|| None)
        .take(fixed_cosets.len())
        .collect::<Vec<_>>();
    for family in cache_plan.families {
        let column_index = family.column_index;
        assert!(
            selector_families_by_column[column_index]
                .replace(family)
                .is_none()
        );
    }

    // Compressed-selector columns are allocated internally and only occur in
    // the gate expressions replaced by the evaluator. Reuse each source coset
    // as the first cached selector so a family retains only m - 1 new cosets.
    let cached_selector_families = fixed_cosets
        .par_iter_mut()
        .zip(selector_families_by_column.into_par_iter())
        .filter_map(|(query_and_first_selector, family)| {
            let family = family?;
            let mut selectors = (1..family.combination_len)
                .map(|_| vk.domain.empty_extended())
                .collect::<Vec<_>>();
            let selector_slices = selectors
                .iter_mut()
                .map(|selector| &mut selector[..])
                .collect();
            let min_chunk_len = std::cmp::max(
                query_and_first_selector.len() / crate::multicore::current_num_threads(),
                1,
            );
            evaluate_compressed_selector_family(
                query_and_first_selector,
                selector_slices,
                min_chunk_len,
            );

            Some(super::CachedSelectorFamily {
                column_index: family.column_index,
                selectors: selectors.into_boxed_slice(),
            })
        })
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
        cached_selector_families: cached_selector_families.into(),
        permutation: permutation_pk,
        fft_twiddles,
        floor_plan,
    })
}
#[cfg(test)]
mod tests {
    use super::{
        CompressedSelectorFamily, MAX_ADDITIONAL_COMPRESSED_SELECTOR_CACHE_BYTES,
        commit_fixed_lagrange, evaluate_compressed_selector_family, plan_compressed_selector_cache,
    };
    use crate::{
        pasta::{EqAffine, Fp},
        poly::{
            EvaluationDomain,
            commitment::{Blind, Params},
        },
    };
    use ff::Field;
    use pasta_curves::{pallas, vesta};

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

    fn family(column_index: usize, combination_len: usize) -> CompressedSelectorFamily {
        CompressedSelectorFamily {
            column_index,
            combination_len,
            assigned_roots: (1..=combination_len).collect(),
        }
    }

    #[test]
    fn compressed_selector_cache_plan_is_bounded_and_whole_family() {
        let plan = plan_compressed_selector_cache(
            vec![
                family(0, 5),
                family(1, 7),
                family(2, 5),
                family(3, 6),
                CompressedSelectorFamily {
                    column_index: 4,
                    combination_len: usize::MAX,
                    assigned_roots: vec![],
                },
            ],
            1,
            8,
            80,
        );

        assert_eq!(plan.additional_payload_bytes, 80);
        assert_eq!(
            plan.families
                .iter()
                .map(|family| family.column_index)
                .collect::<Vec<_>>(),
            [1, 0]
        );
        assert!(
            plan.families
                .iter()
                .all(|family| family.assigned_roots.len() == family.combination_len)
        );
    }

    #[test]
    fn compressed_selector_cache_plan_rejects_checked_arithmetic_overflow() {
        // A malformed empty family cannot underflow the reuse discount.
        let plan = plan_compressed_selector_cache(vec![family(0, 0)], 1, 1, usize::MAX);
        assert!(plan.families.is_empty());
        assert_eq!(plan.additional_payload_bytes, 0);

        // Overflow while counting field elements in one family.
        let plan = plan_compressed_selector_cache(vec![family(0, 3)], usize::MAX, 1, usize::MAX);
        assert!(plan.families.is_empty());
        assert_eq!(plan.additional_payload_bytes, 0);

        // Overflow while converting a field-element count to bytes.
        let plan = plan_compressed_selector_cache(vec![family(0, 2)], usize::MAX, 2, usize::MAX);
        assert!(plan.families.is_empty());
        assert_eq!(plan.additional_payload_bytes, 0);

        // Overflow while adding another whole family to the running total.
        let plan = plan_compressed_selector_cache(
            vec![family(0, 3), family(1, 2)],
            usize::MAX / 2,
            1,
            usize::MAX,
        );
        assert_eq!(plan.families.len(), 1);
        assert_eq!(plan.families[0].column_index, 0);
        assert_eq!(plan.additional_payload_bytes, usize::MAX - 1);
    }

    #[test]
    fn compressed_selector_cache_plan_is_deterministic_and_tie_stable() {
        let make_families = || vec![family(10, 5), family(20, 7), family(11, 5), family(21, 7)];
        let selected_columns = |plan: super::CompressedSelectorCachePlan| {
            plan.families
                .into_iter()
                .map(|family| family.column_index)
                .collect::<Vec<_>>()
        };

        let first = plan_compressed_selector_cache(make_families(), 1, 1, 16);
        let second = plan_compressed_selector_cache(make_families(), 1, 1, 16);
        assert_eq!(selected_columns(first), [20, 21, 10]);
        assert_eq!(selected_columns(second), [20, 21, 10]);
    }

    #[test]
    fn orchard_compressed_selectors_use_20_5_mib_of_additional_payload() {
        const ORCHARD_EXTENDED_LEN: usize = 1 << 14;
        const ORCHARD_SELECTOR_FAMILY_LENGTHS: [usize; 9] = [6, 4, 5, 4, 4, 6, 7, 7, 7];
        const ORCHARD_ADDITIONAL_CACHE_BYTES: usize = 20 * super::MEBIBYTE + super::MEBIBYTE / 2;

        let plan = plan_compressed_selector_cache(
            ORCHARD_SELECTOR_FAMILY_LENGTHS
                .into_iter()
                .enumerate()
                .map(|(column_index, combination_len)| family(column_index, combination_len))
                .collect(),
            ORCHARD_EXTENDED_LEN,
            size_of::<pallas::Base>(),
            MAX_ADDITIONAL_COMPRESSED_SELECTOR_CACHE_BYTES,
        );

        assert_eq!(
            plan.families
                .iter()
                .map(|family| family.combination_len)
                .sum::<usize>(),
            50
        );
        assert_eq!(
            plan.families
                .iter()
                .map(|family| family
                    .additional_cached_polynomials()
                    .expect("selected selector families are nonempty"))
                .sum::<usize>(),
            41
        );
        assert_eq!(
            plan.additional_payload_bytes,
            ORCHARD_ADDITIONAL_CACHE_BYTES
        );
        assert_eq!(
            MAX_ADDITIONAL_COMPRESSED_SELECTOR_CACHE_BYTES - plan.additional_payload_bytes,
            super::MEBIBYTE / 2
        );
    }

    fn check_compressed_selector_family<F: Field + From<u64>>() {
        const COMBINATION_LEN: usize = 7;

        let original_query = [
            F::ZERO,
            F::ONE,
            F::from(2),
            F::from(COMBINATION_LEN as u64),
            -F::ONE,
            F::from(19),
        ];
        let mut query_and_first_selector = original_query;
        let mut remaining_selectors =
            vec![vec![F::ZERO; original_query.len()]; COMBINATION_LEN - 1];
        let selector_slices = remaining_selectors
            .iter_mut()
            .map(|selector| &mut selector[..])
            .collect();

        // A one-element chunk exercises the parallel splitting path.
        evaluate_compressed_selector_family(&mut query_and_first_selector, selector_slices, 1);

        for assigned_root in 0..COMBINATION_LEN {
            let selector = if assigned_root == 0 {
                &query_and_first_selector[..]
            } else {
                &remaining_selectors[assigned_root - 1]
            };
            for (query, actual) in original_query.iter().zip(selector) {
                let expected = (1..=COMBINATION_LEN)
                    .filter(|root| *root != assigned_root + 1)
                    .fold(*query, |product, root| {
                        product * (F::from(root as u64) - query)
                    });
                assert_eq!(*actual, expected);
            }
        }
    }

    #[test]
    fn compressed_selector_prefix_suffix_matches_independent_products() {
        check_compressed_selector_family::<pallas::Base>();
        check_compressed_selector_family::<vesta::Base>();
    }
}
