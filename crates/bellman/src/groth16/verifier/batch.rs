//! Performs batch Groth16 proof verification.
//!
//! Batch verification asks whether *all* proofs in some set are valid,
//! rather than asking whether *each* of them is valid. This allows sharing
//! computations among all proof verifications, performing less work overall
//! at the cost of higher latency (the entire batch must complete), complexity of
//! caller code (which must assemble a batch of proofs across work-items),
//! and loss of the ability to easily pinpoint failing proofs.
//!
//! This batch verification implementation is non-adaptive, in the sense that it
//! assumes that all the proofs in the batch are verifiable by the same
//! `VerifyingKey`. The reason is that if you have different proof statements,
//! you need to specify which statement you are proving, which means that you
//! need to refer to or lookup a particular `VerifyingKey`. In practice, with
//! large enough batches, it's manageable and not much worse performance-wise to
//! keep batches of each statement type, vs one large adaptive batch.

use std::{borrow::Cow, ops::AddAssign};

use ff::{Field, PrimeField};
use group::{Curve, CurveAffine, Group, prime::PrimeCurve};
use pairing::{MillerLoopResult, MultiMillerLoop};
use rand_core::{CryptoRng, Rng, TryRng};

#[cfg(feature = "multicore")]
use rand::rngs::SysRng;

#[cfg(feature = "multicore")]
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    prelude::ParallelSlice,
};

use crate::{
    VerificationError,
    groth16::{PreparedVerifyingKey, Proof, VerifyingKey},
};

/// Width of the wNAF digits used to multiply by 128-bit batch weights.
const WEIGHT_WNAF_WIDTH: u32 = 5;

/// Samples batch weights: `1` for the first item when `unit_first` is set,
/// and an independent uniform nonzero 128-bit integer for every other item.
///
/// For a batch with an invalid proof, fix every weight except that of one
/// invalid proof that is not a unit-weight proof (if the only invalid proof
/// has weight 1, the check fails outright). Exactly one value of the
/// remaining weight satisfies the combined check modulo r, and distinct
/// 128-bit integers stay distinct modulo r, so the batch is accepted with
/// probability at most 1 / (2^128 - 1), independent of the batch size.
/// That argument needs every random weight in one pairing equation to be
/// independent and at most one weight to be 1.
fn random_weights<R: TryRng + ?Sized>(
    rng: &mut R,
    count: usize,
    unit_first: bool,
) -> Result<Vec<u128>, R::Error> {
    // One read fills every weight, so a system RNG costs one call per batch.
    let mut bytes = vec![0u8; count * 16];
    rng.try_fill_bytes(&mut bytes)?;
    let mut weights = Vec::with_capacity(count);
    for (i, chunk) in bytes.chunks_exact(16).enumerate() {
        if unit_first && i == 0 {
            weights.push(1);
            continue;
        }
        let mut weight = u128::from_le_bytes(chunk.try_into().expect("16-byte chunk"));
        while weight == 0 {
            let mut redraw = [0u8; 16];
            rng.try_fill_bytes(&mut redraw)?;
            weight = u128::from_le_bytes(redraw);
        }
        weights.push(weight);
    }
    Ok(weights)
}

/// Width-`WEIGHT_WNAF_WIDTH` non-adjacent form of `k`, least significant
/// digit first, with trailing zero digits removed. Every nonzero digit is
/// odd and lies in (-2^(w-1), 2^(w-1)).
fn wnaf_u128(k: u128) -> Vec<i8> {
    let width = 1u32 << WEIGHT_WNAF_WIDTH;
    let window_mask = width - 1;
    // A final carry can produce one digit beyond bit 127.
    let mut naf = vec![0i8; 129];
    let mut pos = 0;
    let mut carry = 0;
    while pos < naf.len() {
        let bits = if pos < 128 {
            (k >> pos) as u32 & window_mask
        } else {
            0
        };
        let window = carry + bits;
        if window & 1 == 0 {
            // An even window keeps the carry: either carry and the low bit
            // are both 0, or both 1.
            pos += 1;
            continue;
        }
        if window < width / 2 {
            carry = 0;
            naf[pos] = window as i8;
        } else {
            carry = 1;
            naf[pos] = (window as i8).wrapping_sub(width as i8);
        }
        pos += WEIGHT_WNAF_WIDTH as usize;
    }
    debug_assert_eq!(carry, 0);
    let len = naf.iter().rposition(|&d| d != 0).map_or(0, |i| i + 1);
    naf.truncate(len);
    naf
}

/// Computes `sum(weights[i] * points[i])` in variable time.
///
/// The weights are public once the batch is fixed, so variable time is safe.
/// Points share one doubling chain (interleaved wNAF). A weight of 1 adds its
/// point directly.
fn vartime_weighted_sum<G: PrimeCurve>(
    points: impl IntoIterator<Item = G::Affine>,
    weights: &[u128],
) -> G {
    let mut unit = G::identity();
    let mut nafs = Vec::with_capacity(weights.len());
    let mut tables = Vec::with_capacity(weights.len());
    let mut top = 0;
    for (point, &weight) in points.into_iter().zip(weights) {
        if weight == 1 {
            unit += point;
            continue;
        }
        let naf = wnaf_u128(weight);
        top = top.max(naf.len());
        nafs.push(naf);
        // Odd multiples P, 3P, ..., (2^(w-1) - 1)P.
        let point = point.to_curve();
        let double = point.double();
        let mut table = Vec::with_capacity(1 << (WEIGHT_WNAF_WIDTH - 2));
        table.push(point);
        for i in 1..(1 << (WEIGHT_WNAF_WIDTH - 2)) {
            let next = table[i - 1] + double;
            table.push(next);
        }
        tables.push(table);
    }

    let mut acc = G::identity();
    for i in (0..top).rev() {
        acc = acc.double();
        for (naf, table) in nafs.iter().zip(&tables) {
            match naf.get(i).copied().unwrap_or(0) {
                0 => {}
                d if d > 0 => acc += table[(d / 2) as usize],
                d => acc -= table[(-d / 2) as usize],
            }
        }
    }
    acc + unit
}

/// A batch verification item.
///
/// This struct exists to allow batch processing to be decoupled from the
/// lifetime of the message. This is useful when using the batch verification
/// API in an async context.
#[derive(Clone, Debug)]
pub struct Item<E: MultiMillerLoop> {
    proof: Proof<E>,
    inputs: Vec<E::Fr>,
}

impl<E: MultiMillerLoop> From<(&Proof<E>, &[E::Fr])> for Item<E> {
    fn from((proof, inputs): (&Proof<E>, &[E::Fr])) -> Self {
        (proof.clone(), inputs.to_owned()).into()
    }
}

impl<E: MultiMillerLoop> From<(Proof<E>, Vec<E::Fr>)> for Item<E> {
    fn from((proof, inputs): (Proof<E>, Vec<E::Fr>)) -> Self {
        Self { proof, inputs }
    }
}

impl<E: MultiMillerLoop> Item<E> {
    /// Perform non-batched verification of this `Item`.
    ///
    /// This is useful (in combination with `Item::clone`) for implementing
    /// fallback logic when batch verification fails.
    pub fn verify_single(self, pvk: &PreparedVerifyingKey<E>) -> Result<(), VerificationError> {
        super::verify_proof(pvk, &self.proof, &self.inputs)
    }
}

/// A batch verification context.
///
/// In practice, you would create a batch verifier for each proof statement
/// requiring the same `VerifyingKey`.
#[derive(Debug)]
pub struct Verifier<E: MultiMillerLoop> {
    items: Vec<Item<E>>,
}

/// Reusable fixed G2 pairing terms from a Groth16 verifying key.
#[derive(Clone)]
pub struct PreparedBatchG2<E: MultiMillerLoop> {
    source_beta_g2: E::G2Affine,
    source_gamma_g2: E::G2Affine,
    source_delta_g2: E::G2Affine,
    beta_g2: E::G2Prepared,
    gamma_g2: E::G2Prepared,
    delta_g2: E::G2Prepared,
}

impl<E: MultiMillerLoop> std::fmt::Debug for PreparedBatchG2<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreparedBatchG2").finish_non_exhaustive()
    }
}

impl<E: MultiMillerLoop> From<&VerifyingKey<E>> for PreparedBatchG2<E> {
    fn from(vk: &VerifyingKey<E>) -> Self {
        Self {
            source_beta_g2: vk.beta_g2,
            source_gamma_g2: vk.gamma_g2,
            source_delta_g2: vk.delta_g2,
            beta_g2: E::prepare_reusable_g2(vk.beta_g2),
            gamma_g2: E::prepare_reusable_g2(vk.gamma_g2),
            delta_g2: E::prepare_reusable_g2(vk.delta_g2),
        }
    }
}

impl<E: MultiMillerLoop> PreparedBatchG2<E> {
    // The raw verifier uses each G2 term once, so extra reusable preparation
    // would cost more than it saves.
    fn for_one_batch(vk: &VerifyingKey<E>) -> Self {
        Self {
            source_beta_g2: vk.beta_g2,
            source_gamma_g2: vk.gamma_g2,
            source_delta_g2: vk.delta_g2,
            beta_g2: vk.beta_g2.into(),
            gamma_g2: vk.gamma_g2.into(),
            delta_g2: vk.delta_g2.into(),
        }
    }
}

/// Fixed G2 pairing terms for repeated batches under one verifying key.
///
/// Creating this once prepares beta, gamma, and delta for repeated batches.
/// Engines can spend more time preparing these terms to speed up verification.
pub struct PreparedBatchVerifyingKey<'a, E: MultiMillerLoop> {
    vk: &'a VerifyingKey<E>,
    g2: Cow<'a, PreparedBatchG2<E>>,
}

/// Weighted sums for proofs in one pairing equation.
struct WeightedTerms<E: MultiMillerLoop> {
    /// Each proof's weighted A, paired with its negated B.
    a_terms: Vec<(E::G1Affine, E::G2Prepared)>,
    /// Weighted public inputs, with the implicit leading 1.
    gammas: Vec<E::Fr>,
    /// Weighted sum of C.
    delta: E::G1,
    /// Sum of weights.
    y: E::Fr,
}

struct PreparedBatchTerms<E: MultiMillerLoop> {
    variable: Vec<(E::G1Affine, E::G2Prepared)>,
    delta: E::G1Affine,
    gamma: E::G1Affine,
    beta: E::G1Affine,
}

impl<E: MultiMillerLoop> PreparedBatchTerms<E> {
    fn with_key<'a>(
        &'a self,
        key: &'a PreparedBatchVerifyingKey<'_, E>,
    ) -> Vec<(&'a E::G1Affine, &'a E::G2Prepared)> {
        let mut terms = self
            .variable
            .iter()
            .map(|(a, b)| (a, b))
            .collect::<Vec<_>>();
        terms.extend([
            (&self.delta, &key.g2.delta_g2),
            (&self.gamma, &key.g2.gamma_g2),
            (&self.beta, &key.g2.beta_g2),
        ]);
        terms
    }
}

impl<E: MultiMillerLoop> std::fmt::Debug for PreparedBatchVerifyingKey<'_, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreparedBatchVerifyingKey")
            .finish_non_exhaustive()
    }
}

impl<'a, E: MultiMillerLoop> From<&'a VerifyingKey<E>> for PreparedBatchVerifyingKey<'a, E> {
    fn from(vk: &'a VerifyingKey<E>) -> Self {
        Self {
            vk,
            g2: Cow::Owned(PreparedBatchG2::from(vk)),
        }
    }
}

impl<'a, E: MultiMillerLoop> PreparedBatchVerifyingKey<'a, E> {
    /// Borrows fixed G2 terms from [`PreparedBatchG2`].
    ///
    /// Returns an error if the key has different beta, gamma, or delta G2 terms.
    pub fn from_cached(
        vk: &'a VerifyingKey<E>,
        g2: &'a PreparedBatchG2<E>,
    ) -> Result<Self, VerificationError> {
        if g2.source_beta_g2 != vk.beta_g2
            || g2.source_gamma_g2 != vk.gamma_g2
            || g2.source_delta_g2 != vk.delta_g2
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        Ok(Self {
            vk,
            g2: Cow::Borrowed(g2),
        })
    }

    // The raw verifier uses each G2 term once, so extra reusable preparation
    // would cost more than it saves.
    fn for_one_batch(vk: &'a VerifyingKey<E>) -> Self {
        Self {
            vk,
            g2: Cow::Owned(PreparedBatchG2::for_one_batch(vk)),
        }
    }
}

// Need to impl Default by hand to avoid a derived E: Default bound
impl<E: MultiMillerLoop> Default for Verifier<E> {
    fn default() -> Self {
        Self { items: Vec::new() }
    }
}

impl<E: MultiMillerLoop> Verifier<E>
where
    E::G1: AddAssign<E::G1>,
{
    /// Construct a new batch verifier.
    pub fn new() -> Self {
        Self::default()
    }

    /// Queue a (proof, inputs) tuple for verification.
    pub fn queue<I: Into<Item<E>>>(&mut self, item: I) {
        self.items.push(item.into())
    }

    /// Perform batch verification with a particular [`VerifyingKey`].
    ///
    /// For repeated batches, prepare the key once and use
    /// [`Verifier::verify_prepared`].
    pub fn verify<R: Rng + CryptoRng>(
        self,
        rng: R,
        vk: &VerifyingKey<E>,
    ) -> Result<(), VerificationError> {
        if self
            .items
            .iter()
            .any(|Item { inputs, .. }| inputs.len() + 1 != vk.ic.len())
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        if self.items.is_empty() {
            return Ok(());
        }
        let pvk = PreparedBatchVerifyingKey::for_one_batch(vk);
        if self.items.len() == 1 {
            return Self::verify_one_prepared(&self.items[0], &pvk);
        }
        self.verify_prepared_unchecked(rng, &pvk)
    }

    /// Verify a batch using fixed G2 terms prepared for its verifying key.
    pub fn verify_prepared<R: Rng + CryptoRng>(
        self,
        rng: R,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let vk = pvk.vk;
        if self
            .items
            .iter()
            .any(|Item { inputs, .. }| inputs.len() + 1 != vk.ic.len())
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        if self.items.is_empty() {
            return Ok(());
        }
        if self.items.len() == 1 {
            return Self::verify_one_prepared(&self.items[0], pvk);
        }
        self.verify_prepared_unchecked(rng, pvk)
    }

    // A single proof cannot cancel another invalid proof, so the batch
    // randomizer is unnecessary. This also avoids multiplying A, C, and
    // alpha by that randomizer.
    fn verify_one_prepared(
        item: &Item<E>,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let vk = pvk.vk;
        let mut gamma = vk.ic[0].to_curve();
        for (input, base) in item.inputs.iter().zip(vk.ic.iter().skip(1)) {
            gamma += *base * input;
        }
        let gamma = E::g1_to_affine_vartime(&gamma);
        let neg_b = (-item.proof.b).into();

        if E::multi_miller_loop(&[
            (&item.proof.a, &neg_b),
            (&item.proof.c, &pvk.g2.delta_g2),
            (&gamma, &pvk.g2.gamma_g2),
            (&vk.alpha_g1, &pvk.g2.beta_g2),
        ])
        .final_exponentiation()
            == E::Gt::identity()
        {
            Ok(())
        } else {
            Err(VerificationError::InvalidProof)
        }
    }

    /// Verify two batches using different [`PreparedBatchVerifyingKey`] values
    /// in one Miller loop.
    ///
    /// The first proof of `self` has weight 1; every other proof in both
    /// batches gets an independent nonzero randomizer. Only one proof in the
    /// combined pairing equation may have weight 1, so `other` gets none.
    /// This shares the Miller-loop squares and final exponentiation.
    pub fn verify_joint_prepared<R: Rng + CryptoRng>(
        self,
        other: Self,
        mut rng: R,
        key: &PreparedBatchVerifyingKey<'_, E>,
        other_key: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        if self
            .items
            .iter()
            .any(|item| item.inputs.len() + 1 != key.vk.ic.len())
            || other
                .items
                .iter()
                .any(|item| item.inputs.len() + 1 != other_key.vk.ic.len())
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        if self.items.is_empty() {
            return other.verify_prepared(rng, other_key);
        }
        if other.items.is_empty() {
            return self.verify_prepared(rng, key);
        }

        let first = self.randomize_terms(&mut rng, key, true);
        let second = other.randomize_terms(&mut rng, other_key, false);
        let mut terms = first.with_key(key);
        terms.extend(second.with_key(other_key));

        if E::multi_miller_loop(&terms).final_exponentiation() == E::Gt::identity() {
            Ok(())
        } else {
            Err(VerificationError::InvalidProof)
        }
    }

    #[allow(non_snake_case)]
    fn verify_prepared_unchecked<R: Rng + CryptoRng>(
        self,
        rng: R,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let terms = self.randomize_terms(rng, pvk, true);
        if E::multi_miller_loop(&terms.with_key(pvk)).final_exponentiation() == E::Gt::identity() {
            Ok(())
        } else {
            Err(VerificationError::InvalidProof)
        }
    }

    /// Weighs a run of proofs that belong to one pairing equation.
    fn weigh(items: &[Item<E>], weights: &[u128], ic_len: usize) -> WeightedTerms<E> {
        let mut gammas = vec![E::Fr::ZERO; ic_len];
        let mut y = E::Fr::ZERO;
        for (Item { inputs, .. }, &weight) in items.iter().zip(weights) {
            let weight = E::Fr::from_u128(weight);
            gammas[0] += weight; // a_0 is implicitly set to 1
            for (a_i, gamma_i) in Iterator::zip(inputs.iter(), gammas.iter_mut().skip(1)) {
                *gamma_i += weight * a_i;
            }
            y += weight;
        }

        // Each A pairs with its own B, so each needs its own multiplication;
        // all C terms pair with delta and share one weighted sum.
        let weighted_a = items
            .iter()
            .zip(weights)
            .map(|(item, &weight)| vartime_weighted_sum::<E::G1>([item.proof.a], &[weight]))
            .collect::<Vec<_>>();
        let mut affine_a = vec![E::G1Affine::identity(); weighted_a.len()];
        E::G1::batch_normalize(&weighted_a, &mut affine_a);
        let a_terms = affine_a
            .into_iter()
            .zip(items)
            .map(|(a, item)| (a, (-item.proof.b).into()))
            .collect();
        let delta = vartime_weighted_sum(items.iter().map(|item| item.proof.c), weights);

        WeightedTerms {
            a_terms,
            gammas,
            delta,
            y,
        }
    }

    /// Builds the batch's pairing terms. When `unit_first` is set, the first
    /// proof has weight 1. Every other proof gets an independent nonzero
    /// 128-bit weight (see [`random_weights`]). At most one proof in a
    /// combined pairing equation may have weight 1: two unit-weight proofs
    /// could carry errors that cancel.
    #[allow(non_snake_case)]
    fn randomize_terms<R: Rng + CryptoRng>(
        self,
        mut rng: R,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
        unit_first: bool,
    ) -> PreparedBatchTerms<E> {
        let vk = pvk.vk;
        let weights = random_weights(&mut rng, self.items.len(), unit_first)
            .unwrap_or_else(|never| match never {});
        let WeightedTerms {
            a_terms: ml_terms,
            gammas: acc_Gammas,
            delta: acc_Delta,
            y: acc_Y,
        } = Self::weigh(&self.items, &weights, vk.ic.len());

        let delta = acc_Delta.to_affine();

        let Psi = vk
            .ic
            .iter()
            .zip(acc_Gammas.iter())
            .map(|(&Psi_i, acc_Gamma_i)| Psi_i * acc_Gamma_i)
            .sum();

        let gamma = E::G1Affine::from(Psi);

        // Covers the [acc_Y]⋅e(alpha_g1, beta_g2) component
        //
        // The multiplication by acc_Y is expensive -- it involves
        // exponentiating by acc_Y because the result of the pairing is an
        // element of a multiplicative subgroup of a large extension field.
        // Instead, we add
        //     ([acc_Y]⋅alpha_g1, beta_g2)
        // to our Miller loop terms because
        //     [acc_Y]⋅e(alpha_g1, beta_g2) = e([acc_Y]⋅alpha_g1, beta_g2)
        let beta = E::G1Affine::from(vk.alpha_g1 * acc_Y);

        PreparedBatchTerms {
            variable: ml_terms,
            delta,
            gamma,
            beta,
        }
    }

    /// Perform batch verification using the global Rayon thread pool.
    ///
    /// For repeated batches, prepare the key once and use
    /// [`Verifier::verify_multicore_prepared`].
    #[cfg(feature = "multicore")]
    pub fn verify_multicore(self, vk: &VerifyingKey<E>) -> Result<(), VerificationError> {
        if self
            .items
            .iter()
            .any(|Item { inputs, .. }| inputs.len() + 1 != vk.ic.len())
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        if self.items.is_empty() {
            return Ok(());
        }
        let pvk = PreparedBatchVerifyingKey::for_one_batch(vk);
        if self.items.len() == 1 {
            return Self::verify_one_prepared(&self.items[0], &pvk);
        }
        self.verify_multicore_prepared_unchecked(&pvk)
    }

    /// Verify a batch with prepared fixed G2 terms using the global Rayon
    /// thread pool.
    #[cfg(feature = "multicore")]
    pub fn verify_multicore_prepared(
        self,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let vk = pvk.vk;
        if self
            .items
            .iter()
            .any(|Item { inputs, .. }| inputs.len() + 1 != vk.ic.len())
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        if self.items.is_empty() {
            return Ok(());
        }
        if self.items.len() == 1 {
            return Self::verify_one_prepared(&self.items[0], pvk);
        }
        self.verify_multicore_prepared_unchecked(pvk)
    }

    #[cfg(feature = "multicore")]
    #[allow(non_snake_case)]
    fn verify_multicore_prepared_unchecked(
        self,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let vk = pvk.vk;
        struct Accumulator<E: MultiMillerLoop> {
            gammas: Vec<E::Fr>,
            delta: E::G1,
            y: E::Fr,
            ml_result: Option<E::Result>,
        }

        impl<E: MultiMillerLoop> Accumulator<E> {
            fn new(ic_len: usize) -> Self {
                Accumulator {
                    gammas: vec![E::Fr::ZERO; ic_len],
                    delta: E::G1::identity(),
                    y: E::Fr::ZERO,
                    ml_result: None,
                }
            }
        }

        let ic_len = vk.ic.len();

        // Give each Rayon thread a Miller-loop work item while retaining
        // batching within each loop when parallelism is scarce.
        const MAX_CHUNK_SIZE: usize = 8;
        let threads = rayon::current_num_threads();
        let chunk_size = self.items.len().div_ceil(threads).clamp(1, MAX_CHUNK_SIZE);

        // Every proof gets an independent 128-bit weight, except that the
        // first proof of chunk 0 has weight 1. All chunks feed one pairing
        // equation, so no other chunk may also have a unit-weight proof:
        // errors in two unit-weight proofs could cancel.
        let acc = self
            .items
            .par_chunks(chunk_size)
            .enumerate()
            .map(|(chunk_index, items)| {
                let weights = random_weights(&mut SysRng, items.len(), chunk_index == 0)
                    .expect("system randomness must be available");
                let terms = Self::weigh(items, &weights, ic_len);
                let ml_terms = terms
                    .a_terms
                    .iter()
                    .map(|(a, b)| (a, b))
                    .collect::<Vec<_>>();
                Accumulator::<E> {
                    gammas: terms.gammas,
                    delta: terms.delta,
                    y: terms.y,
                    ml_result: Some(E::multi_miller_loop(&ml_terms[..])),
                }
            })
            .reduce(
                || Accumulator::<E>::new(ic_len),
                |mut a, b| {
                    for (a, b) in a.gammas.iter_mut().zip(b.gammas.into_iter()) {
                        *a += b;
                    }
                    a.delta += b.delta;
                    a.y += b.y;
                    a.ml_result = match (a.ml_result, b.ml_result) {
                        (Some(a), Some(b)) => Some(a + b),
                        (Some(a), None) | (None, Some(a)) => Some(a),
                        (None, None) => None,
                    };
                    a
                },
            );

        match acc.ml_result {
            None => Ok(()),
            Some(mut ml_result) => {
                // TODO: could use a multiexp (Bos-Coster maybe?)
                let psi = vk
                    .ic
                    .iter()
                    .zip(acc.gammas.into_iter())
                    .map(|(&psi_i, acc_gamma_i)| psi_i * acc_gamma_i)
                    .sum();

                ml_result += E::multi_miller_loop(&[
                    (&acc.delta.to_affine(), &pvk.g2.delta_g2),
                    (&E::G1Affine::from(psi), &pvk.g2.gamma_g2),
                    (&E::G1Affine::from(vk.alpha_g1 * acc.y), &pvk.g2.beta_g2),
                ]);

                if ml_result.final_exponentiation() == E::Gt::identity() {
                    Ok(())
                } else {
                    Err(VerificationError::InvalidProof)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bls12_381::{G1Affine, G1Projective, Scalar};
    use core::convert::Infallible;
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    fn edge_weights() -> Vec<u128> {
        let mut weights = vec![
            1,
            2,
            3,
            15,
            16,
            17,
            31,
            32,
            33,
            u64::MAX as u128,
            1 << 64,
            (1 << 64) + 1,
            1 << 127,
            (1 << 127) - 1,
            u128::MAX,
            u128::MAX - 1,
            u128::MAX - 16,
            0x5555_5555_5555_5555_5555_5555_5555_5555,
            0xaaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa,
            0xf0f0_f0f0_f0f0_f0f0_f0f0_f0f0_f0f0_f0f0,
        ];
        // Long runs of ones around every window boundary exercise the carry.
        for shift in 0..128 {
            weights.push(u128::MAX >> shift);
            weights.push(u128::MAX << shift);
        }
        weights
    }

    #[test]
    fn wnaf_digits_reconstruct_the_weight() {
        let mut rng = XorShiftRng::from_seed([7; 16]);
        let mut weights = edge_weights();
        weights.extend(
            (0..1000).map(|_| u128::from(rng.next_u64()) << 64 | u128::from(rng.next_u64())),
        );
        let half = 1i8 << (WEIGHT_WNAF_WIDTH - 1);
        for weight in weights {
            let naf = wnaf_u128(weight);
            assert!(naf.len() <= 129);
            let mut value = Scalar::ZERO;
            let mut previous_nonzero: Option<usize> = None;
            for (i, &digit) in naf.iter().enumerate().rev() {
                value = value.double()
                    + Scalar::from(digit.unsigned_abs() as u64)
                        * if digit < 0 { -Scalar::ONE } else { Scalar::ONE };
                if digit != 0 {
                    assert_eq!(digit & 1, 1, "{weight:#x}: even digit");
                    assert!(-half < digit && digit < half, "{weight:#x}: digit {digit}");
                    if let Some(j) = previous_nonzero {
                        assert!(
                            j - i >= WEIGHT_WNAF_WIDTH as usize,
                            "{weight:#x}: adjacent digits"
                        );
                    }
                    previous_nonzero = Some(i);
                }
            }
            assert_eq!(value, Scalar::from_u128(weight), "{weight:#x}");
        }
        assert!(wnaf_u128(0).is_empty());
    }

    #[test]
    fn weighted_sum_matches_scalar_multiplication() {
        let mut rng = XorShiftRng::from_seed([9; 16]);
        let random_point = |rng: &mut XorShiftRng| {
            G1Affine::from(G1Projective::generator() * Scalar::random(&mut *rng))
        };

        for weight in edge_weights() {
            let point = random_point(&mut rng);
            assert_eq!(
                vartime_weighted_sum::<G1Projective>([point], &[weight]),
                point * Scalar::from_u128(weight),
                "{weight:#x}"
            );
        }

        for count in [0, 1, 2, 3, 8, 33] {
            let points = (0..count)
                .map(|_| random_point(&mut rng))
                .collect::<Vec<_>>();
            let mut weights = random_weights(&mut rng, count, true).unwrap();
            if count > 2 {
                weights[2] = u128::MAX;
            }
            let expected: G1Projective = points
                .iter()
                .zip(&weights)
                .map(|(point, &weight)| point * Scalar::from_u128(weight))
                .sum();
            assert_eq!(
                vartime_weighted_sum::<G1Projective>(points.iter().copied(), &weights),
                expected,
                "{count} points"
            );
        }
        assert_eq!(
            vartime_weighted_sum::<G1Projective>([G1Affine::identity()], &[u128::MAX]),
            G1Projective::identity()
        );
    }

    /// Yields zero bytes for the first `zeros` bytes, then 0x01 bytes.
    struct ZerosThenOnes {
        zeros: usize,
    }

    impl TryRng for ZerosThenOnes {
        type Error = Infallible;

        fn try_next_u32(&mut self) -> Result<u32, Infallible> {
            let mut bytes = [0; 4];
            self.try_fill_bytes(&mut bytes)?;
            Ok(u32::from_le_bytes(bytes))
        }

        fn try_next_u64(&mut self) -> Result<u64, Infallible> {
            let mut bytes = [0; 8];
            self.try_fill_bytes(&mut bytes)?;
            Ok(u64::from_le_bytes(bytes))
        }

        fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Infallible> {
            for byte in dst {
                *byte = if self.zeros > 0 {
                    self.zeros -= 1;
                    0
                } else {
                    1
                };
            }
            Ok(())
        }
    }

    #[test]
    fn random_weights_are_nonzero_with_one_unit_weight() {
        let ones = u128::from_le_bytes([1; 16]);
        // The first 48 bytes cover three weights: the unit slot and two zero
        // draws that must be redrawn.
        let mut rng = ZerosThenOnes { zeros: 48 };
        assert_eq!(
            random_weights(&mut rng, 4, true).unwrap(),
            vec![1, ones, ones, ones]
        );
        let mut rng = ZerosThenOnes { zeros: 16 };
        assert_eq!(
            random_weights(&mut rng, 2, false).unwrap(),
            vec![ones, ones]
        );
        assert!(random_weights(&mut rng, 0, true).unwrap().is_empty());

        let mut rng = XorShiftRng::from_seed([3; 16]);
        let weights = random_weights(&mut rng, 64, true).unwrap();
        assert_eq!(weights[0], 1);
        assert!(
            weights[1..].iter().all(|&w| w > 1 << 64),
            "weights use all 128 bits"
        );
    }
}
