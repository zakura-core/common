use group::{
    Curve, Group,
    ff::{Field, FromUniformBytes, PrimeField},
};
use pasta_curves::arithmetic::CurveAffine;
use rand::rngs::SysRng;
use std::sync::Arc;

use super::{VerificationStrategy, validate_instances, verify_proof_with_instance_commitments};
use crate::{
    INSTANCE_WINDOW_BITS, INSTANCE_WINDOW_ENTRIES_PER_BASE, MAX_CACHED_INSTANCE_ROWS,
    PreparedCommitmentTables,
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

    fn commit(&self, params: &Params<C>, scalars: &[C::Scalar]) -> C::Curve {
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

            for (base_index, scalar) in scalar_reprs.iter().enumerate() {
                let digit = fixed_window_digit(scalar.as_ref(), window, INSTANCE_WINDOW_BITS);
                if digit != 0 {
                    variable +=
                        self.multiples[base_index * INSTANCE_WINDOW_ENTRIES_PER_BASE + digit - 1];
                }
            }
        }

        let mut commitment = C::Curve::from(params.w);
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
) -> C::Curve {
    if instance.len() <= table.base_count {
        table.commit(params, instance)
    } else {
        commit_instance(params, instance)
    }
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
    let projective = items
        .iter()
        .flat_map(|item| item.instances.iter())
        .flat_map(|instances| instances.iter())
        .map(|instance| commit_instance_with_table(params, &table, instance))
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

    use super::{InstanceFixedWindowTable, commit_instance_with_table};
    use crate::{
        INSTANCE_WINDOW_ENTRIES_PER_BASE, MAX_CACHED_INSTANCE_ROWS, plonk::commit_instance,
        poly::commitment::Params,
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
                        commit_instance_with_table(&params, &table, &instance),
                        commit_instance(&params, &instance),
                    );
                }
            }};
        }

        check_curve!(EqAffine, Fp);
        check_curve!(EpAffine, Fq);
    }
}
