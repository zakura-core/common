use group::{
    Curve, Group,
    ff::{Field, FromUniformBytes, PrimeField},
};
use pasta_curves::arithmetic::CurveAffine;
use rand::rngs::SysRng;
use std::{
    io::{self, Read},
    sync::Arc,
};

use super::{VerificationStrategy, validate_instances, verify_proof_with_instance_commitments};
use crate::{
    INSTANCE_WINDOW_BITS, INSTANCE_WINDOW_ENTRIES_PER_BASE, InstanceWindowTable,
    MAX_CACHED_INSTANCE_ROWS,
    multicore::{IntoParallelIterator, TryFoldAndReduce},
    plonk::{Error, VerifyingKey, commit_instance},
    poly::commitment::{Guard, MSM, Params},
    transcript::{
        Blake2bRead, Challenge255, ChallengeScalar, EncodedChallenge, Transcript, TranscriptRead,
    },
};

const SERIAL_INSTANCE_WINDOW_BITS: usize = 8;
// Lockstep bookkeeping pays off with three or more instance columns.
const MIN_LOCKSTEP_INSTANCE_COLUMNS: usize = 3;

#[cfg(feature = "multicore")]
use crate::multicore::{IndexedParallelIterator, ParallelIterator};

const POINT_DECODE_LANES: usize = 8;

fn point_decode_enabled<C: CurveAffine>() -> bool {
    #[cfg(all(feature = "x86_64-asm", target_arch = "x86_64"))]
    {
        let curve = core::any::TypeId::of::<C>();
        (curve == core::any::TypeId::of::<pasta_curves::pallas::Affine>()
            || curve == core::any::TypeId::of::<pasta_curves::vesta::Affine>())
            && std::is_x86_feature_detected!("avx512f")
            && std::is_x86_feature_detected!("avx512ifma")
            && std::is_x86_feature_detected!("avx512vl")
    }
    #[cfg(not(all(feature = "x86_64-asm", target_arch = "x86_64")))]
    {
        false
    }
}

/// A sequential transcript with bounded immutable point-decoding lookahead.
///
/// Cached results are keyed by their exact proof-byte offset. Peeking does
/// not consume bytes, absorb points, squeeze challenges, or report errors.
/// Every actual read still consumes the original slice before using a hint;
/// invalid encodings and identity points fail at the same read as before.
struct BatchSliceRead<'a, C: CurveAffine>
where
    C::Scalar: FromUniformBytes<64>,
{
    remaining: &'a [u8],
    proof_len: usize,
    hash: Blake2bRead<&'a [u8], C, Challenge255<C>>,
    cache: [Option<C>; POINT_DECODE_LANES],
    cache_start: usize,
    cache_active: bool,
    decode_enabled: bool,
    #[cfg(test)]
    force_scalar_decode: bool,
}

impl<'a, C: CurveAffine> BatchSliceRead<'a, C>
where
    C::Scalar: FromUniformBytes<64>,
{
    fn init(proof: &'a [u8]) -> Self {
        Self {
            remaining: proof,
            proof_len: proof.len(),
            hash: Blake2bRead::init(&[]),
            cache: [None; POINT_DECODE_LANES],
            cache_start: 0,
            cache_active: false,
            decode_enabled: point_decode_enabled::<C>(),
            #[cfg(test)]
            force_scalar_decode: false,
        }
    }

    fn refill_points(&mut self, offset: usize, first: &C::Repr, repr_bytes: usize) {
        #[cfg(test)]
        let enabled = self.decode_enabled || self.force_scalar_decode;
        #[cfg(not(test))]
        let enabled = self.decode_enabled;
        if !enabled {
            return;
        }
        let Some(lookahead_bytes) = repr_bytes.checked_mul(POINT_DECODE_LANES - 1) else {
            return;
        };
        if repr_bytes == 0
            || first.as_ref().len() != repr_bytes
            || self.remaining.len() < lookahead_bytes
        {
            return;
        }
        let mut reprs: [C::Repr; POINT_DECODE_LANES] = core::array::from_fn(|_| C::Repr::default());
        for (lane, repr) in reprs.iter_mut().enumerate() {
            if repr.as_mut().len() != repr_bytes {
                return;
            }
            if lane == 0 {
                repr.as_mut().copy_from_slice(first.as_ref());
            } else {
                let start = (lane - 1) * repr_bytes;
                repr.as_mut()
                    .copy_from_slice(&self.remaining[start..start + repr_bytes]);
            }
        }
        #[cfg(test)]
        if self.force_scalar_decode {
            self.cache = reprs.map(|repr| Option::from(C::from_bytes(&repr)));
            self.cache_start = offset;
            self.cache_active = true;
            return;
        }

        let Some(decoded) = pasta_curves::arithmetic::try_batch_from_bytes8::<C>(&reprs) else {
            // Unsupported configurations use the original scalar decoder.
            // Do not allocate future representations or repeat this attempt.
            self.decode_enabled = false;
            return;
        };
        self.cache = decoded.map(Option::from);
        self.cache_start = offset;
        self.cache_active = true;
    }
}

impl<C: CurveAffine> Transcript<C, Challenge255<C>> for BatchSliceRead<'_, C>
where
    C::Scalar: FromUniformBytes<64>,
{
    fn squeeze_challenge(&mut self) -> Challenge255<C> {
        self.hash.squeeze_challenge()
    }

    fn squeeze_challenge_scalar<T>(&mut self) -> ChallengeScalar<C, T> {
        self.hash.squeeze_challenge_scalar()
    }

    fn common_point(&mut self, point: C) -> io::Result<()> {
        self.hash.common_point(point)
    }

    fn common_scalar(&mut self, scalar: C::Scalar) -> io::Result<()> {
        self.hash.common_scalar(scalar)
    }
}

impl<C: CurveAffine> TranscriptRead<C, Challenge255<C>> for BatchSliceRead<'_, C>
where
    C::Scalar: FromUniformBytes<64>,
{
    fn read_point(&mut self) -> io::Result<C> {
        let mut repr = C::Repr::default();
        let repr_bytes = repr.as_mut().len();
        let offset = self.proof_len - self.remaining.len();
        let cache_index = |start: usize| {
            offset
                .checked_sub(start)
                .filter(|delta| repr_bytes != 0 && delta % repr_bytes == 0)
                .map(|delta| delta / repr_bytes)
                .filter(|index| *index < POINT_DECODE_LANES)
        };
        self.remaining.read_exact(repr.as_mut())?;
        if !self.cache_active || cache_index(self.cache_start).is_none() {
            self.cache_active = false;
            self.refill_points(offset, &repr, repr_bytes);
        }
        let point: C = if self.cache_active {
            cache_index(self.cache_start).and_then(|index| self.cache[index])
        } else {
            Option::from(C::from_bytes(&repr))
        }
        .ok_or_else(|| io::Error::new(io::ErrorKind::Other, "invalid point encoding in proof"))?;
        self.common_point(point)?;
        Ok(point)
    }

    fn read_scalar(&mut self) -> io::Result<C::Scalar> {
        let mut repr = <C::Scalar as PrimeField>::Repr::default();
        self.remaining.read_exact(repr.as_mut())?;
        self.cache_active = false;
        let scalar: C::Scalar = Option::from(C::Scalar::from_repr(repr)).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "invalid field element encoding in proof",
            )
        })?;
        self.common_scalar(scalar)?;
        Ok(scalar)
    }
}

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

    let table = InstanceFixedWindowTable::new(params, max_cached_instance_len);
    let instances = items
        .iter()
        .flat_map(|item| item.instances.iter())
        .flat_map(|instances| instances.iter())
        .map(Vec::as_slice)
        .collect::<Vec<_>>();
    let projective = table.commit_batch(params, &instances);
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
                let mut transcript = BatchSliceRead::init(&item.proof[..]);
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
    use group::{Curve, Group};
    use pasta_curves::{EpAffine, EqAffine, Fp, Fq};
    use std::{
        cell::Cell,
        io::{self, Read},
        rc::Rc,
    };

    use super::{
        BatchSliceRead, CurveAffine, InstanceFixedWindowTable, POINT_DECODE_LANES, PrimeField,
        commit_instance_with_table, signed_fixed_window_digit, signed_instance_window_count,
    };
    use crate::{
        INSTANCE_WINDOW_BITS, INSTANCE_WINDOW_ENTRIES_PER_BASE, MAX_CACHED_INSTANCE_ROWS,
        plonk::commit_instance,
        poly::commitment::Params,
        transcript::{Blake2bRead, Challenge255, Transcript, TranscriptRead},
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

    struct ObservedSlice<'a> {
        remaining: &'a [u8],
        consumed: Rc<Cell<usize>>,
    }

    impl Read for ObservedSlice<'_> {
        fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
            let result = self.remaining.read(output);
            if let Ok(count) = result {
                self.consumed.set(self.consumed.get() + count);
            }
            result
        }

        fn read_exact(&mut self, output: &mut [u8]) -> io::Result<()> {
            let before = self.remaining.len();
            let result = self.remaining.read_exact(output);
            self.consumed
                .set(self.consumed.get() + before - self.remaining.len());
            result
        }
    }

    fn same_result<T: core::fmt::Debug + PartialEq>(
        actual: io::Result<T>,
        expected: io::Result<T>,
    ) {
        match (actual, expected) {
            (Ok(actual), Ok(expected)) => assert_eq!(actual, expected),
            (Err(actual), Err(expected)) => {
                assert_eq!(actual.kind(), expected.kind());
                assert_eq!(actual.to_string(), expected.to_string());
            }
            (actual, expected) => panic!("transcript results differ: {actual:?}/{expected:?}"),
        }
    }

    fn check_slice_transcript<C: CurveAffine>()
    where
        C::Scalar: FromUniformBytes<64>,
    {
        let generator = C::Curve::generator().to_affine();
        let points: Vec<_> = (1..=3 * POINT_DECODE_LANES + 1)
            .map(|index| {
                (C::Curve::from(generator) * C::Scalar::from(index as u64))
                    .to_affine()
                    .to_bytes()
            })
            .collect();
        let scalar = C::Scalar::from(19);
        let mut proof = Vec::new();
        // The first lookahead crosses a challenge, and the second reaches
        // into scalar bytes. Scalar reads must invalidate unused hints.
        for point in &points[..POINT_DECODE_LANES + 3] {
            proof.extend_from_slice(point.as_ref());
        }
        proof.extend_from_slice(scalar.to_repr().as_ref());
        for point in &points[POINT_DECODE_LANES + 3..] {
            proof.extend_from_slice(point.as_ref());
        }
        let consumed = Rc::new(Cell::new(0));
        let mut expected = Blake2bRead::<_, C, Challenge255<C>>::init(ObservedSlice {
            remaining: &proof,
            consumed: consumed.clone(),
        });
        let mut actual = BatchSliceRead::<C>::init(&proof);
        actual.force_scalar_decode = true;
        same_result(actual.common_scalar(scalar), expected.common_scalar(scalar));
        same_result(
            actual.common_point(generator),
            expected.common_point(generator),
        );
        for index in 0..points.len() {
            if index == POINT_DECODE_LANES + 3 {
                same_result(actual.read_scalar(), expected.read_scalar());
                assert!(!actual.cache_active);
            }
            same_result(actual.read_point(), expected.read_point());
            assert_eq!(actual.proof_len - actual.remaining.len(), consumed.get());
            if index % 2 == 1 {
                let left = actual.squeeze_challenge();
                let right = expected.squeeze_challenge();
                assert_eq!(&left[..], &right[..]);
            }
            if index % 3 == 2 {
                let left = actual.squeeze_challenge_scalar::<()>();
                let right = expected.squeeze_challenge_scalar::<()>();
                assert_eq!(*left, *right);
            }
        }
        same_result(actual.read_point(), expected.read_point());
        assert_eq!(actual.proof_len - actual.remaining.len(), consumed.get());

        // Every speculative lane is checked for error timing and state:
        // invalid encodings must not absorb a point; identity still absorbs
        // the existing point prefix before common_point rejects it.
        for bad_lane in 0..POINT_DECODE_LANES {
            for identity in [false, true] {
                let mut proof = Vec::new();
                for (lane, repr) in points[..2 * POINT_DECODE_LANES].iter().enumerate() {
                    if lane == bad_lane {
                        let mut bad = C::Repr::default();
                        if !identity {
                            bad.as_mut().fill(u8::MAX);
                        }
                        proof.extend_from_slice(bad.as_ref());
                    } else {
                        proof.extend_from_slice(repr.as_ref());
                    }
                }
                let consumed = Rc::new(Cell::new(0));
                let mut expected = Blake2bRead::<_, C, Challenge255<C>>::init(ObservedSlice {
                    remaining: &proof,
                    consumed: consumed.clone(),
                });
                let mut actual = BatchSliceRead::<C>::init(&proof);
                actual.force_scalar_decode = true;
                for _ in 0..=bad_lane {
                    same_result(actual.read_point(), expected.read_point());
                    assert_eq!(actual.proof_len - actual.remaining.len(), consumed.get());
                    let left = actual.squeeze_challenge();
                    let right = expected.squeeze_challenge();
                    assert_eq!(&left[..], &right[..]);
                }
                // Also compare continuation after the error; no future
                // cached lane may have changed the earlier transcript state.
                same_result(actual.read_point(), expected.read_point());
                assert_eq!(
                    &actual.squeeze_challenge()[..],
                    &expected.squeeze_challenge()[..]
                );
            }
        }

        let repr_bytes = points[0].as_ref().len();
        for available in 0..2 * POINT_DECODE_LANES * repr_bytes {
            let proof: Vec<_> = points[..2 * POINT_DECODE_LANES]
                .iter()
                .flat_map(|point| point.as_ref().iter().copied())
                .collect();
            let consumed = Rc::new(Cell::new(0));
            let mut expected = Blake2bRead::<_, C, Challenge255<C>>::init(ObservedSlice {
                remaining: &proof[..available],
                consumed: consumed.clone(),
            });
            let mut actual = BatchSliceRead::<C>::init(&proof[..available]);
            actual.force_scalar_decode = true;
            for _ in 0..=available / repr_bytes {
                same_result(actual.read_point(), expected.read_point());
                assert_eq!(actual.proof_len - actual.remaining.len(), consumed.get());
            }
            assert_eq!(
                &actual.squeeze_challenge()[..],
                &expected.squeeze_challenge()[..]
            );
        }

        let mut invalid_scalar = <C::Scalar as PrimeField>::Repr::default();
        invalid_scalar.as_mut().fill(u8::MAX);
        let mut expected = Blake2bRead::<_, C, Challenge255<C>>::init(invalid_scalar.as_ref());
        let mut actual = BatchSliceRead::<C>::init(invalid_scalar.as_ref());
        same_result(actual.read_scalar(), expected.read_scalar());
        assert_eq!(
            &actual.squeeze_challenge()[..],
            &expected.squeeze_challenge()[..]
        );
    }

    #[test]
    fn batch_slice_transcript_pallas() {
        check_slice_transcript::<EpAffine>();
    }

    #[test]
    fn batch_slice_transcript_vesta() {
        check_slice_transcript::<EqAffine>();
    }

    fn check_native_cache_when_available<C: CurveAffine>()
    where
        C::Scalar: FromUniformBytes<64>,
    {
        let generator = C::Curve::generator();
        let reprs = core::array::from_fn(|lane| {
            (generator * C::Scalar::from(lane as u64 + 1))
                .to_affine()
                .to_bytes()
        });
        let supported = pasta_curves::arithmetic::try_batch_from_bytes8::<C>(&reprs).is_some()
            && super::point_decode_enabled::<C>();
        let proof: Vec<u8> = reprs
            .iter()
            .flat_map(|repr| repr.as_ref().iter().copied())
            .collect();
        let mut transcript = BatchSliceRead::<C>::init(&proof);
        for (lane, repr) in reprs.iter().enumerate() {
            let expected: C = Option::from(C::from_bytes(repr)).unwrap();
            assert_eq!(transcript.read_point().unwrap(), expected);
            assert_eq!(transcript.cache_active, supported);
            assert_eq!(
                transcript.proof_len - transcript.remaining.len(),
                (lane + 1) * repr.as_ref().len()
            );
        }
    }

    #[test]
    fn batch_slice_native_cache_pallas() {
        check_native_cache_when_available::<EpAffine>();
    }

    #[test]
    fn batch_slice_native_cache_vesta() {
        check_native_cache_when_available::<EqAffine>();
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
}
