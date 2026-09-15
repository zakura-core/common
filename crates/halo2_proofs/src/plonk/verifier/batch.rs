use group::{
    Curve, Group,
    ff::{Field, FromUniformBytes, PrimeField},
};
use pasta_curves::arithmetic::CurveAffine;
use rand::rngs::SysRng;
use std::sync::Arc;

use super::super::{instance_scalar_digit, prepared_instance_scalar_repr};
use super::{VerificationStrategy, validate_instances, verify_proof_with_instance_commitments};
use crate::{
    INSTANCE_WINDOW_BITS, INSTANCE_WINDOW_ENTRIES_PER_BASE, InstanceWindowTable,
    MAX_CACHED_INSTANCE_ROWS, PREPARED_INSTANCE_FIRST_ROW_CACHE_ENTRIES,
    PREPARED_INSTANCE_WINDOW_MAGNITUDES, PreparedInstanceFirstRowTable,
    multicore::{IntoParallelIterator, TryFoldAndReduce},
    plonk::{Error, VerifyingKey, commit_instance},
    poly::commitment::{Guard, MSM, Params},
    transcript::{Blake2bRead, EncodedChallenge},
};

#[cfg(feature = "multicore")]
use crate::multicore::{IndexedParallelIterator, ParallelIterator};

/// A proof verification strategy that returns the proof's MSM.
///
/// `BatchVerifier` handles the accumulation of the MSMs for the batched proofs.
#[derive(Debug)]
struct BatchStrategy<'params, C: CurveAffine> {
    msm: MSM<'params, C>,
    // The common coefficient for every term in this proof's verifier
    // equation. Applying different coefficients to different terms would
    // change the equation instead of merely weighting it within the batch.
    batching_scalar: C::Scalar,
}

impl<'params, C: CurveAffine> BatchStrategy<'params, C> {
    fn new(params: &'params Params<C>, batching_scalar: C::Scalar) -> Self {
        BatchStrategy {
            msm: MSM::new(params),
            batching_scalar,
        }
    }
}

impl<'params, C: CurveAffine> VerificationStrategy<'params, C> for BatchStrategy<'params, C> {
    type Output = MSM<'params, C>;

    fn process<E: EncodedChallenge<C>>(
        self,
        f: impl FnOnce(MSM<'params, C>) -> Result<Guard<'params, C, E>, Error>,
    ) -> Result<Self::Output, Error> {
        let BatchStrategy {
            msm,
            batching_scalar,
        } = self;
        let guard = f(msm)?;
        Ok(guard.use_challenges_with_scale(batching_scalar))
    }
}

#[derive(Debug)]
struct BatchItem<C: CurveAffine> {
    instances: Vec<Vec<Vec<C::Scalar>>>,
    proof: Vec<u8>,
}

struct InstanceFixedWindowTable<C: CurveAffine> {
    base_count: usize,
    multiples: Arc<Vec<C>>,
}

impl<C: CurveAffine> InstanceFixedWindowTable<C> {
    fn new(params: &Params<C>, base_count: usize) -> Self {
        Self {
            base_count,
            multiples: params.instance_window_table(base_count),
        }
    }

    fn commit(
        &self,
        params: &Params<C>,
        scalars: &[C::Scalar],
        first_row_product: Option<C::Curve>,
    ) -> C::Curve {
        assert!(scalars.len() <= self.base_count);

        let window_count = (C::Scalar::NUM_BITS as usize).div_ceil(INSTANCE_WINDOW_BITS);
        let scalar_reprs = scalars.iter().map(PrimeField::to_repr).collect::<Vec<_>>();
        let mut variable = C::Curve::identity();

        for window in (0..window_count).rev() {
            if window + 1 != window_count {
                for _ in 0..INSTANCE_WINDOW_BITS {
                    variable = variable.double();
                }
            }

            let first_base = usize::from(first_row_product.is_some());
            for (base_index, scalar) in scalar_reprs.iter().enumerate().skip(first_base) {
                let digit = fixed_window_digit(scalar.as_ref(), window, INSTANCE_WINDOW_BITS);
                if digit != 0 {
                    variable +=
                        self.multiples[base_index * INSTANCE_WINDOW_ENTRIES_PER_BASE + digit - 1];
                }
            }
        }

        let mut commitment = C::Curve::from(params.w);
        if let Some(first_row_product) = first_row_product {
            commitment += first_row_product;
        }
        commitment += variable;
        commitment
    }

    #[cfg(test)]
    fn retained_bytes(&self) -> usize {
        self.multiples.len() * core::mem::size_of::<C>()
    }
}

fn commit_instance_with_table<C: CurveAffine>(
    params: &Params<C>,
    table: &InstanceFixedWindowTable<C>,
    instance: &[C::Scalar],
    first_row_product: Option<C::Curve>,
) -> C::Curve {
    if instance.len() <= table.base_count {
        table.commit(params, instance, first_row_product)
    } else {
        commit_instance(params, instance)
    }
}

fn evaluate_prepared_first_row<C: CurveAffine>(
    table: &PreparedInstanceFirstRowTable<C>,
    scalar: C::Scalar,
) -> Option<C::Curve> {
    let repr = prepared_instance_scalar_repr(&scalar, table.scalar_bits, table.byte_order)?;
    let mut product = C::Curve::identity();
    for window in 0..table.windows {
        let digit =
            instance_scalar_digit(repr.as_ref(), window, table.scalar_bits, table.byte_order);
        if digit.magnitude != 0 {
            let point = window * PREPARED_INSTANCE_WINDOW_MAGNITUDES + digit.magnitude - 1;
            let point = table.points[point];
            product += if digit.negative { -point } else { point };
        }
    }
    Some(product)
}

fn cached_first_row_product<C: CurveAffine>(
    table: &PreparedInstanceFirstRowTable<C>,
    scalar: C::Scalar,
    prepare_miss: bool,
) -> Option<C::Curve> {
    {
        let products = table
            .products
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some((_, product)) = products
            .iter()
            .find(|(cached_scalar, _)| *cached_scalar == scalar)
        {
            return Some(*product);
        }
    }
    if !prepare_miss {
        return None;
    }

    let product = evaluate_prepared_first_row(table, scalar)?;
    let mut products = table
        .products
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some((_, cached_product)) = products
        .iter()
        .find(|(cached_scalar, _)| *cached_scalar == scalar)
    {
        return Some(*cached_product);
    }
    // FIFO is sufficient for the expected sequence of block anchors and
    // keeps adversarial public inputs from increasing retained memory.
    if products.len() == PREPARED_INSTANCE_FIRST_ROW_CACHE_ENTRIES {
        products.remove(0);
    }
    products.push((scalar, product));
    Some(product)
}

fn batch_first_row_products<C: CurveAffine>(
    params: &Params<C>,
    table: &InstanceFixedWindowTable<C>,
    instances: &[&[C::Scalar]],
) -> Vec<Option<C::Curve>> {
    let mut products = vec![None; instances.len()];
    let Some(first_row_table) = params.prepared_instance_first_row_table() else {
        return products;
    };
    let mut values = instances
        .iter()
        .enumerate()
        .filter(|(_, instance)| !instance.is_empty() && instance.len() <= table.base_count)
        .map(|(index, instance)| (instance[0].to_repr(), index, instance[0]))
        .collect::<Vec<_>>();
    values.sort_unstable_by(|left, right| left.0.as_ref().cmp(right.0.as_ref()));

    let mut group_start = 0;
    while group_start < values.len() {
        let mut group_end = group_start + 1;
        while group_end < values.len()
            && values[group_start].0.as_ref() == values[group_end].0.as_ref()
        {
            group_end += 1;
        }
        // Unique misses retain the ordinary combined commitment path. A
        // repeated value amortizes preparing its product within this batch.
        if let Some(product) = cached_first_row_product(
            &first_row_table,
            values[group_start].2,
            group_end - group_start > 1,
        ) {
            for (_, index, _) in &values[group_start..group_end] {
                products[*index] = Some(product);
            }
        }
        group_start = group_end;
    }
    products
}

fn fixed_window_digit(bytes: &[u8], window: usize, window_bits: usize) -> usize {
    let bit_start = window * window_bits;
    let byte_start = bit_start / u8::BITS as usize;
    let bit_offset = bit_start % u8::BITS as usize;
    let low = bytes.get(byte_start).copied().unwrap_or(0);
    let high = bytes.get(byte_start + 1).copied().unwrap_or(0);
    let encoded = u16::from(low) | (u16::from(high) << u8::BITS);
    usize::from((encoded >> bit_offset) & ((1 << window_bits) - 1))
}

fn compute_batch_instance_commitments<C: CurveAffine>(
    params: &Params<C>,
    vk: &VerifyingKey<C>,
    items: &[BatchItem<C>],
) -> Result<Vec<Vec<Vec<C>>>, Error> {
    let mut item_column_counts = Vec::with_capacity(items.len());
    let mut max_cached_instance_len = 0;

    for item in items {
        let instance_columns = item
            .instances
            .iter()
            .map(|instances| instances.iter().map(Vec::as_slice).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let instances = instance_columns
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        validate_instances(params, vk, &instances)?;

        // Table construction costs 255 points per row. Longer, caller-sized
        // columns remain valid but use the generic MSM below.
        max_cached_instance_len = item
            .instances
            .iter()
            .flat_map(|instances| instances.iter())
            .map(Vec::len)
            .filter(|instance_len| *instance_len <= MAX_CACHED_INSTANCE_ROWS)
            .fold(max_cached_instance_len, usize::max);
        item_column_counts.push(item.instances.iter().map(Vec::len).collect::<Vec<_>>());
    }

    let table = InstanceFixedWindowTable::new(params, max_cached_instance_len);
    let instances = items
        .iter()
        .flat_map(|item| item.instances.iter())
        .flat_map(|instances| instances.iter())
        .map(Vec::as_slice)
        .collect::<Vec<_>>();
    let first_row_products = batch_first_row_products(params, &table, &instances);
    let projective = instances
        .into_iter()
        .zip(first_row_products)
        .map(|(instance, first_row_product)| {
            commit_instance_with_table(params, &table, instance, first_row_product)
        })
        .collect::<Vec<_>>();
    let mut affine = vec![C::identity(); projective.len()];
    C::Curve::batch_normalize(&projective, &mut affine);
    let mut affine = affine.into_iter();
    let commitments = item_column_counts
        .into_iter()
        .map(|proof_column_counts| {
            proof_column_counts
                .into_iter()
                .map(|column_count| affine.by_ref().take(column_count).collect())
                .collect()
        })
        .collect();
    assert!(affine.next().is_none());

    Ok(commitments)
}

/// A verifier that checks multiple proofs in a batch. **This requires the
/// `batch` crate feature to be enabled.**
#[derive(Debug, Default)]
pub struct BatchVerifier<C: CurveAffine> {
    items: Vec<BatchItem<C>>,
}

impl<C: CurveAffine> BatchVerifier<C> {
    /// Constructs a new batch verifier.
    pub fn new() -> Self {
        Self { items: vec![] }
    }

    /// Adds a proof to the batch.
    pub fn add_proof(&mut self, instances: Vec<Vec<Vec<C::Scalar>>>, proof: Vec<u8>) {
        self.items.push(BatchItem { instances, proof })
    }
}

impl<C: CurveAffine> BatchVerifier<C>
where
    C::Scalar: FromUniformBytes<64>,
{
    /// Finalizes the batch and checks its validity.
    ///
    /// Returns `false` if *some* proof was invalid. If the caller needs to identify
    /// specific failing proofs, it must re-process the proofs separately.
    ///
    /// This uses [`SysRng`] internally instead of taking an `R: Rng` argument, because
    /// the internal parallelization requires access to a RNG that is guaranteed to not
    /// clone its internal state when shared between threads.
    pub fn finalize(self, params: &Params<C>, vk: &VerifyingKey<C>) -> bool {
        fn accumulate_msm<'params, C: CurveAffine>(
            mut acc: MSM<'params, C>,
            msm: MSM<'params, C>,
        ) -> MSM<'params, C> {
            acc.add_msm_batch(msm);
            acc
        }

        let items = self.items;
        let instance_commitments = match compute_batch_instance_commitments(params, vk, &items) {
            Ok(instance_commitments) => instance_commitments,
            Err(_) => return false,
        };
        let items = items
            .into_iter()
            .zip(instance_commitments)
            .collect::<Vec<_>>();

        let final_msm = items
            .into_par_iter()
            .enumerate()
            .map(|(i, (item, instance_commitments))| {
                let instances: Vec<Vec<_>> = item
                    .instances
                    .iter()
                    .map(|i| i.iter().map(|c| &c[..]).collect())
                    .collect();
                let instances: Vec<_> = instances.iter().map(|i| &i[..]).collect();

                // Every proof and instance is already owned by this batch, so
                // the prover has fixed all equations before these coefficients
                // are chosen. Fix the first coefficient at one; every later
                // equation receives an independent random coefficient rho_i.
                // This prevents invalid equations from cancelling each other,
                // except with negligible probability.
                let rho_i = if i == 0 {
                    C::Scalar::ONE
                } else {
                    C::Scalar::try_random(&mut SysRng).expect("system randomness must be available")
                };
                let strategy = BatchStrategy::new(params, rho_i);
                let mut transcript = Blake2bRead::init(&item.proof[..]);
                verify_proof_with_instance_commitments(
                    params,
                    vk,
                    strategy,
                    &instances,
                    instance_commitments,
                    &mut transcript,
                )
                .map_err(|e| {
                    tracing::debug!("Batch item {} failed verification: {}", i, e);
                    e
                })
            })
            .try_fold_and_reduce(
                || params.empty_msm(),
                |acc, res| res.map(|proof_msm| accumulate_msm(acc, proof_msm)),
            );

        match final_msm {
            Ok(msm) => msm.eval(),
            Err(_) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use ff::{Field, FromUniformBytes};
    use pasta_curves::{EpAffine, EqAffine, Fp, Fq};

    use super::{InstanceFixedWindowTable, batch_first_row_products, commit_instance_with_table};
    use crate::{
        INSTANCE_WINDOW_ENTRIES_PER_BASE, InstanceWindowTable, MAX_CACHED_INSTANCE_ROWS,
        plonk::commit_instance, poly::commitment::Params,
    };

    #[test]
    fn fixed_window_instance_commitments_match_signed_booth() {
        macro_rules! check_curve {
            ($curve:ty, $scalar:ty) => {{
                const K: u32 = 7;

                let params = Params::<$curve>::new(K);
                let table = InstanceFixedWindowTable::new(&params, MAX_CACHED_INSTANCE_ROWS);
                assert_eq!(
                    table.retained_bytes(),
                    MAX_CACHED_INSTANCE_ROWS
                        * INSTANCE_WINDOW_ENTRIES_PER_BASE
                        * core::mem::size_of::<$curve>(),
                );

                for len in [0, 1, 10, 17, 63, 64, 65, 127] {
                    let mut instance = (0..len)
                        .map(|index| {
                            let mut bytes = [0; 64];
                            for (offset, byte) in bytes.iter_mut().enumerate() {
                                *byte = (index as u8)
                                    .wrapping_mul(73)
                                    .wrapping_add((offset as u8).wrapping_mul(29))
                                    .wrapping_add(17);
                            }
                            <$scalar as FromUniformBytes<64>>::from_uniform_bytes(&bytes)
                        })
                        .collect::<Vec<_>>();
                    if let Some(value) = instance.get_mut(0) {
                        *value = <$scalar>::ZERO;
                    }
                    if let Some(value) = instance.get_mut(1) {
                        *value = <$scalar>::ONE;
                    }
                    if let Some(value) = instance.get_mut(2) {
                        *value = -<$scalar>::ONE;
                    }

                    assert_eq!(
                        commit_instance_with_table(&params, &table, &instance, None),
                        commit_instance(&params, &instance),
                    );
                }
            }};
        }

        check_curve!(EqAffine, Fp);
        check_curve!(EpAffine, Fq);
    }

    #[test]
    fn repeated_first_rows_use_cached_products_without_changing_commitments() {
        macro_rules! check_curve {
            ($curve:ty, $scalar:ty) => {{
                const K: u32 = 7;
                const ROWS: usize = 10;

                let params = Params::<$curve>::new(K);
                assert!(params.prepare_instance_first_row_table());
                let table = InstanceFixedWindowTable::new(&params, ROWS);
                let repeated = <$scalar>::from(17);
                let unique = <$scalar>::from(29);
                let instance = |first, offset| {
                    core::iter::once(first)
                        .chain((1..ROWS).map(|row| <$scalar>::from((row + offset) as u64)))
                        .collect::<Vec<_>>()
                };
                let instances = [
                    instance(repeated, 0),
                    instance(unique, 1),
                    instance(repeated, 2),
                ];
                let instance_refs = instances.iter().map(Vec::as_slice).collect::<Vec<_>>();
                let products = batch_first_row_products(&params, &table, &instance_refs);

                assert!(products[0].is_some());
                assert!(products[1].is_none());
                assert_eq!(products[0], products[2]);
                for (instance, product) in instance_refs.into_iter().zip(products) {
                    assert_eq!(
                        commit_instance_with_table(&params, &table, instance, product),
                        commit_instance(&params, instance),
                    );
                }

                let cached = params.prepared_instance_first_row_table().unwrap();
                assert_eq!(cached.products.lock().unwrap().len(), 1);
                let single = [instances[0].as_slice()];
                assert!(batch_first_row_products(&params, &table, &single)[0].is_some());
            }};
        }

        check_curve!(EqAffine, Fp);
        check_curve!(EpAffine, Fq);
    }

    #[test]
    fn first_row_product_cache_is_bounded() {
        const K: u32 = 7;

        let params = Params::<EqAffine>::new(K);
        assert!(params.prepare_instance_first_row_table());
        let table = InstanceFixedWindowTable::new(&params, 1);
        let instances = (0..=crate::PREPARED_INSTANCE_FIRST_ROW_CACHE_ENTRIES)
            .flat_map(|value| {
                let instance = vec![Fp::from(value as u64 + 1)];
                [instance.clone(), instance]
            })
            .collect::<Vec<_>>();
        let instance_refs = instances.iter().map(Vec::as_slice).collect::<Vec<_>>();
        assert!(
            batch_first_row_products(&params, &table, &instance_refs)
                .into_iter()
                .all(|product| product.is_some()),
        );

        assert_eq!(
            params
                .prepared_instance_first_row_table()
                .unwrap()
                .products
                .lock()
                .unwrap()
                .len(),
            crate::PREPARED_INSTANCE_FIRST_ROW_CACHE_ENTRIES,
        );
    }
}
