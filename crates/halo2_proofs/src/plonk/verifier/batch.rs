use group::{
    Curve, Group,
    ff::{Field, FromUniformBytes, PrimeField},
};
use pasta_curves::arithmetic::CurveAffine;
use rand::rngs::SysRng;
use std::sync::Arc;

use super::{VerificationStrategy, validate_instances, verify_proof_with_instance_commitments};
use crate::{
    INSTANCE_WINDOW_BITS, INSTANCE_WINDOW_ENTRIES_PER_BASE, InstanceWindowTable,
    MAX_CACHED_INSTANCE_ROWS, PREPARED_INSTANCE_DENSE_ROWS, PREPARED_INSTANCE_ROWS,
    instance_flag_mask,
    multicore::{IntoParallelIterator, TryFoldAndReduce},
    plonk::{Error, VerifyingKey, commit_instance},
    poly::commitment::{Guard, MSM, Params},
    transcript::{Blake2bRead, EncodedChallenge},
};

const SERIAL_INSTANCE_WINDOW_BITS: usize = 8;
// Lockstep bookkeeping pays off with three or more instance columns.
const MIN_LOCKSTEP_INSTANCE_COLUMNS: usize = 3;

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

        let window_count = (C::Scalar::NUM_BITS as usize).div_ceil(SERIAL_INSTANCE_WINDOW_BITS);
        let scalar_reprs = scalars.iter().map(PrimeField::to_repr).collect::<Vec<_>>();
        let mut variable = C::Curve::identity();

        for window in (0..window_count).rev() {
            if window + 1 != window_count {
                for _ in 0..SERIAL_INSTANCE_WINDOW_BITS {
                    variable = variable.double();
                }
            }

            for (base_index, scalar) in scalar_reprs.iter().enumerate() {
                let digit = unsigned_fixed_window_digit(
                    scalar.as_ref(),
                    window,
                    SERIAL_INSTANCE_WINDOW_BITS,
                );
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

    fn commit_batch(&self, params: &Params<C>, instances: &[&[C::Scalar]]) -> Vec<C::Curve> {
        if instances.len() < MIN_LOCKSTEP_INSTANCE_COLUMNS {
            return instances
                .iter()
                .map(|instance| {
                    if instance.len() <= self.base_count {
                        self.commit(params, instance)
                    } else {
                        commit_instance(params, instance)
                    }
                })
                .collect();
        }

        let mut commitments = vec![C::Curve::identity(); instances.len()];
        let cached_instances = instances
            .iter()
            .enumerate()
            .filter_map(|(output_index, instance)| {
                if instance.len() <= self.base_count {
                    Some((output_index, *instance))
                } else {
                    commitments[output_index] = commit_instance(params, instance);
                    None
                }
            })
            .collect::<Vec<_>>();
        let cached_count = cached_instances.len();
        // Store representations base-major so every inner loop reads a
        // contiguous row while updating independent output accumulators.
        let mut scalar_reprs = vec![C::Scalar::ZERO.to_repr(); self.base_count * cached_count];
        for (cached_index, (_, instance)) in cached_instances.iter().enumerate() {
            for (base_index, scalar) in instance.iter().enumerate() {
                scalar_reprs[base_index * cached_count + cached_index] = scalar.to_repr();
            }
        }

        let window_count = signed_instance_window_count(C::Scalar::NUM_BITS as usize);
        for window in (0..window_count).rev() {
            if window + 1 != window_count {
                for _ in 0..INSTANCE_WINDOW_BITS {
                    for (output_index, _) in &cached_instances {
                        commitments[*output_index] = commitments[*output_index].double();
                    }
                }
            }

            for base_index in 0..self.base_count {
                for (cached_index, (output_index, _)) in cached_instances.iter().enumerate() {
                    let scalar = &scalar_reprs[base_index * cached_count + cached_index];
                    let digit =
                        signed_fixed_window_digit(scalar.as_ref(), window, INSTANCE_WINDOW_BITS);
                    if digit.magnitude != 0 {
                        let mut multiple = self.multiples
                            [base_index * INSTANCE_WINDOW_ENTRIES_PER_BASE + digit.magnitude - 1];
                        if digit.negative {
                            multiple = -multiple;
                        }
                        commitments[*output_index] += multiple;
                    }
                }
            }
        }

        let blind = C::Curve::from(params.w);
        for (output_index, _) in cached_instances {
            commitments[output_index] += blind;
        }
        commitments
    }

    /// Commits every column, splitting the columns into one contiguous chunk
    /// per worker. Each chunk runs [`Self::commit_batch`] on its own
    /// accumulators, so the result is identical to one serial call.
    ///
    /// A chunk never drops below the lockstep threshold, so splitting never
    /// moves a column from the lockstep path to per-column commitments.
    fn commit_batch_parallel(
        &self,
        params: &Params<C>,
        instances: &[&[C::Scalar]],
    ) -> Vec<C::Curve> {
        let chunk_len = instances
            .len()
            .div_ceil(crate::multicore::current_num_threads())
            .max(MIN_LOCKSTEP_INSTANCE_COLUMNS);
        if chunk_len >= instances.len() {
            return self.commit_batch(params, instances);
        }
        (0..instances.len().div_ceil(chunk_len))
            .into_par_iter()
            .map(|chunk| {
                let start = chunk * chunk_len;
                let end = (start + chunk_len).min(instances.len());
                self.commit_batch(params, &instances[start..end])
            })
            .collect::<Vec<_>>()
            .concat()
    }

    #[cfg(test)]
    fn retained_bytes(&self) -> usize {
        self.multiples.len() * core::mem::size_of::<C>()
    }
}

#[cfg(test)]
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

#[derive(Clone, Copy)]
struct FixedWindowDigit {
    magnitude: usize,
    negative: bool,
}

fn signed_instance_window_count(scalar_bits: usize) -> usize {
    // A full high window can carry into one more window. A partial high
    // window cannot carry, so it already occupies this final slot.
    scalar_bits / INSTANCE_WINDOW_BITS + 1
}

fn unsigned_fixed_window_digit(bytes: &[u8], window: usize, window_bits: usize) -> usize {
    let bit_start = window * window_bits;
    let byte_start = bit_start / u8::BITS as usize;
    let bit_offset = bit_start % u8::BITS as usize;
    let low = bytes.get(byte_start).copied().unwrap_or(0);
    let high = bytes.get(byte_start + 1).copied().unwrap_or(0);
    let encoded = u16::from(low) | (u16::from(high) << u8::BITS);
    usize::from((encoded >> bit_offset) & ((1 << window_bits) - 1))
}

fn signed_fixed_window_digit(bytes: &[u8], window: usize, window_bits: usize) -> FixedWindowDigit {
    let bit_start = window * window_bits;
    let byte_start = bit_start / u8::BITS as usize;
    let bit_offset = bit_start % u8::BITS as usize;
    let low = bytes.get(byte_start).copied().unwrap_or(0);
    let high = bytes.get(byte_start + 1).copied().unwrap_or(0);
    let encoded = u16::from(low) | (u16::from(high) << u8::BITS);
    let radix = 1usize << window_bits;
    let value = usize::from(encoded >> bit_offset) & (radix - 1);
    let overlap = if bit_start == 0 {
        0
    } else {
        let bit = bit_start - 1;
        bytes.get(bit / u8::BITS as usize).map_or(0, |byte| {
            usize::from((byte >> (bit % u8::BITS as usize)) & 1)
        })
    };

    // The bit below each window is its carry-in, while the window's high bit
    // is its carry-out. These cancel between adjacent windows.
    if value < radix / 2 {
        FixedWindowDigit {
            magnitude: value + overlap,
            negative: false,
        }
    } else {
        let magnitude = radix - value - overlap;
        FixedWindowDigit {
            magnitude,
            negative: magnitude != 0,
        }
    }
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

        // Table construction costs INSTANCE_WINDOW_ENTRIES_PER_BASE points
        // per row. Longer, caller-sized columns use the generic MSM below.
        max_cached_instance_len = item
            .instances
            .iter()
            .flat_map(|instances| instances.iter())
            .map(Vec::len)
            .filter(|instance_len| *instance_len <= MAX_CACHED_INSTANCE_ROWS)
            .fold(max_cached_instance_len, usize::max);
        item_column_counts.push(item.instances.iter().map(Vec::len).collect::<Vec<_>>());
    }

    let instances = items
        .iter()
        .flat_map(|item| item.instances.iter())
        .flat_map(|instances| instances.iter())
        .map(Vec::as_slice)
        .collect::<Vec<_>>();
    let projective = commit_glv_instances(params, &instances).unwrap_or_else(|| {
        InstanceFixedWindowTable::new(params, max_cached_instance_len)
            .commit_batch_parallel(params, &instances)
    });
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

/// Commits every column with the doubling-free GLV table when every column
/// has the one-column Orchard instance shape: [`PREPARED_INSTANCE_DENSE_ROWS`]
/// full-width rows followed by [`crate::PREPARED_INSTANCE_BOOLEAN_ROWS`] Boolean
/// rows. The columns are split into one contiguous chunk per worker.
///
/// Returns `None`, committing nothing, if any column has another length or a
/// Boolean row that is neither zero nor one, or if the params have no GLV
/// table; the caller then uses the generic fixed-window path.
fn commit_glv_instances<C: CurveAffine>(
    params: &Params<C>,
    instances: &[&[C::Scalar]],
) -> Option<Vec<C::Curve>> {
    if instances.is_empty()
        || instances
            .iter()
            .any(|column| column.len() != PREPARED_INSTANCE_ROWS)
    {
        return None;
    }
    let masks = instances
        .iter()
        .map(|column| instance_flag_mask(column))
        .collect::<Option<Vec<_>>>()?;
    let table = params.glv_instance_table()?;

    let chunk_len = instances
        .len()
        .div_ceil(crate::multicore::current_num_threads());
    Some(
        (0..instances.len().div_ceil(chunk_len))
            .into_par_iter()
            .map(|chunk| {
                let start = chunk * chunk_len;
                let end = (start + chunk_len).min(instances.len());
                // One batched call per chunk: the dense sums share their
                // affine reduction and its inversions.
                let dense = instances[start..end]
                    .iter()
                    .map(|column| &column[..PREPARED_INSTANCE_DENSE_ROWS])
                    .collect::<Vec<_>>();
                let sums = table.dense.sum_batch_vartime(&dense);
                // `zip` would silently drop columns if an implementation
                // returned fewer sums than it was given.
                debug_assert_eq!(sums.len(), dense.len(), "one sum per column");
                sums.into_iter()
                    .zip(&masks[start..end])
                    .map(|(sum, &mask)| table.offsets[mask] + sum)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
            .concat(),
    )
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
            // Each contribution passed through the IPA challenge expansion,
            // which normally produces random-like, full-width coefficients,
            // before being scaled into the batch. The batch coefficients are
            // fresh, sampled after every proof equation is fixed, and discarded
            // after this check, so batch verification explicitly accepts the
            // variable-time MSM's timing leakage.
            Ok(msm) => msm.eval_full_width(),
            Err(_) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use ff::{Field, FromUniformBytes};
    use pasta_curves::{EpAffine, EqAffine, Fp, Fq};

    use super::{
        InstanceFixedWindowTable, commit_glv_instances, commit_instance_with_table,
        signed_fixed_window_digit, signed_instance_window_count,
    };
    use crate::{
        INSTANCE_WINDOW_BITS, INSTANCE_WINDOW_ENTRIES_PER_BASE, MAX_CACHED_INSTANCE_ROWS,
        plonk::commit_instance, poly::commitment::Params,
    };

    #[test]
    fn signed_instance_windows_preserve_top_bit_carries() {
        for bits in [8, 9, 10, 17, 18, 19, 26, 27, 28, 35, 36, 37, 62, 63, 64] {
            let high_bit = 1u128 << (bits - 1);
            for value in [0, 1, high_bit - 1, high_bit, (1u128 << bits) - 1] {
                let bytes = (value as u64).to_le_bytes();
                let mut reconstructed = 0i128;
                for window in 0..signed_instance_window_count(bits) {
                    let digit = signed_fixed_window_digit(&bytes, window, INSTANCE_WINDOW_BITS);
                    assert!(digit.magnitude <= INSTANCE_WINDOW_ENTRIES_PER_BASE);
                    let magnitude = digit.magnitude as i128;
                    let signed = if digit.negative {
                        -magnitude
                    } else {
                        magnitude
                    };
                    reconstructed += signed << (window * INSTANCE_WINDOW_BITS);
                }
                assert_eq!(reconstructed, value as i128, "{bits}-bit value {value}");
            }
        }
    }

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

                let instances = [0, 1, 10, 17, 63, 64, 65, 127]
                    .into_iter()
                    .map(|len| {
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
                        instance
                    })
                    .collect::<Vec<_>>();
                let instance_slices = instances.iter().map(Vec::as_slice).collect::<Vec<_>>();
                let batched = table.commit_batch(&params, &instance_slices);

                for (instance, batched) in instances.iter().zip(batched) {
                    assert_eq!(
                        commit_instance_with_table(&params, &table, &instance),
                        commit_instance(&params, &instance),
                    );
                    assert_eq!(batched, commit_instance(&params, &instance));
                }

                assert!(table.commit_batch(&params, &[]).is_empty());
                for column_count in [1, 2, 3] {
                    for columns in instance_slices.chunks(column_count) {
                        for (instance, commitment) in
                            columns.iter().zip(table.commit_batch(&params, columns))
                        {
                            assert_eq!(commitment, commit_instance(&params, instance));
                        }
                    }
                }
            }};
        }

        check_curve!(EqAffine, Fp);
        check_curve!(EpAffine, Fq);
    }

    /// Orchard-shaped columns: seven full-width rows, then three flags taking
    /// every mask in turn.
    fn orchard_shaped_columns(count: u64) -> Vec<Vec<Fp>> {
        (0..count)
            .map(|column| {
                let mut rows = (0..7u64)
                    .map(|row| {
                        let mut bytes = [0; 64];
                        let mut x = (column * 16 + row).wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
                        for chunk in bytes.chunks_mut(8) {
                            x ^= x << 13;
                            x ^= x >> 7;
                            x ^= x << 17;
                            chunk.copy_from_slice(&x.to_le_bytes());
                        }
                        Fp::from_uniform_bytes(&bytes)
                    })
                    .collect::<Vec<_>>();
                rows[(column % 7) as usize] = match column % 3 {
                    0 => Fp::ZERO,
                    1 => Fp::ONE,
                    _ => -Fp::ONE,
                };
                rows.extend((0..3).map(|flag| {
                    if (column >> flag) & 1 == 1 {
                        Fp::ONE
                    } else {
                        Fp::ZERO
                    }
                }));
                rows
            })
            .collect()
    }

    #[test]
    fn glv_instance_commitments_match_fixed_window() {
        let params = Params::<EqAffine>::new(7);
        let table = InstanceFixedWindowTable::new(&params, 10);
        let columns = orchard_shaped_columns(19);
        let slices = columns.iter().map(Vec::as_slice).collect::<Vec<_>>();

        let glv = commit_glv_instances(&params, &slices).expect("Orchard-shaped columns");
        assert_eq!(glv, table.commit_batch(&params, &slices));
        for (column, commitment) in slices.iter().zip(&glv) {
            assert_eq!(*commitment, commit_instance(&params, column));
        }
    }

    #[test]
    fn glv_instance_commitments_decline_other_shapes() {
        let params = Params::<EqAffine>::new(7);
        let columns = orchard_shaped_columns(4);
        let mut slices = columns.iter().map(Vec::as_slice).collect::<Vec<_>>();
        assert!(commit_glv_instances(&params, &[]).is_none());

        // A column of another length declines the whole batch.
        slices[2] = &columns[2][..9];
        assert!(commit_glv_instances(&params, &slices).is_none());

        // So does a Boolean row that is neither zero nor one.
        let mut non_boolean = columns[1].clone();
        non_boolean[8] = Fp::from(2);
        let slices = [columns[0].as_slice(), non_boolean.as_slice()];
        assert!(commit_glv_instances(&params, &slices).is_none());
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn glv_instance_commitments_match_across_pool_widths() {
        let params = Params::<EqAffine>::new(7);
        let columns = orchard_shaped_columns(23);
        let slices = columns.iter().map(Vec::as_slice).collect::<Vec<_>>();
        let serial = slices
            .iter()
            .map(|column| commit_instance(&params, column))
            .collect::<Vec<_>>();
        for threads in [1, 2, 3, 4, 8] {
            let pool = maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .expect("test thread pool builds");
            for count in [1, 2, 5, 23] {
                let glv = pool.install(|| commit_glv_instances(&params, &slices[..count]));
                assert_eq!(
                    glv.as_deref(),
                    Some(&serial[..count]),
                    "threads {threads}, columns {count}"
                );
            }
        }
    }

    #[cfg(feature = "multicore")]
    #[test]
    fn parallel_instance_commitments_match_serial_lockstep() {
        const K: u32 = 7;

        let params = Params::<EqAffine>::new(K);
        let table = InstanceFixedWindowTable::new(&params, 10);
        let instances = (0..23u64)
            .map(|column| {
                (0..10u64)
                    .map(|row| {
                        let mut bytes = [0; 64];
                        bytes[..8].copy_from_slice(&(column * 10 + row).to_le_bytes());
                        bytes[8] = 0x5a;
                        Fp::from_uniform_bytes(&bytes)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let slices = instances.iter().map(Vec::as_slice).collect::<Vec<_>>();

        // Column counts below, at, and above the lockstep threshold, and ones
        // that do not divide evenly across the pool.
        for threads in [1, 2, 3, 4, 8] {
            let pool = maybe_rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .expect("test thread pool builds");
            for columns in [0, 1, 2, 3, 4, 5, 7, 11, 23] {
                let slices = &slices[..columns];
                let parallel = pool.install(|| table.commit_batch_parallel(&params, slices));
                assert_eq!(
                    parallel,
                    table.commit_batch(&params, slices),
                    "threads {threads}, columns {columns}",
                );
            }
        }
    }
}
