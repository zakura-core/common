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
use group::{Curve, CurveAffine, Group, WnafBase, WnafScalar};
use pairing::{MillerLoopResult, MultiMillerLoop};
use rand_core::{CryptoRng, Rng};

#[cfg(feature = "multicore")]
use rand::rngs::SysRng;
#[cfg(feature = "multicore")]
use rand_core::TryRng;

#[cfg(feature = "multicore")]
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    prelude::ParallelSlice,
};

use crate::{
    VerificationError,
    groth16::{PUBLIC_INPUT_WINDOW, PreparedVerifyingKey, Proof, VerifyingKey},
};

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
            gamma += mul_vartime::<E>(base, input);
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
    /// batches gets an independent random 128-bit weight. Only one proof in the
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

    /// Adds one proof to the batch accumulators with weight `z`, where `None`
    /// means weight 1 and skips the scalar multiplications.
    ///
    /// Proofs, public inputs, and batch weights are all public, so the
    /// weighted points use variable-time wNAF multiplication. `z·A` is pushed
    /// in projective form; [`Accumulator::finish`] normalizes every point at once.
    fn accumulate(Item { proof, inputs }: &Item<E>, z: Option<E::Fr>, acc: &mut Accumulator<E>) {
        acc.neg_bs.push((-proof.b).into());
        match z {
            None => {
                acc.a_terms.push(proof.a.to_curve());
                acc.gammas[0] += E::Fr::ONE; // a_0 is implicitly set to 1
                for (a_i, acc_gamma_i) in
                    Iterator::zip(inputs.iter(), acc.gammas.iter_mut().skip(1))
                {
                    *acc_gamma_i += a_i;
                }
                acc.delta += proof.c.to_curve();
                acc.y += E::Fr::ONE;
            }
            Some(z) => {
                let z_wnaf = WnafScalar::<E::Fr, WEIGHT_WINDOW>::new(&z);
                acc.a_terms
                    .push(&WnafBase::<E::G1, WEIGHT_WINDOW>::new(proof.a.to_curve()) * &z_wnaf);
                acc.gammas[0] += &z; // a_0 is implicitly set to 1
                for (a_i, acc_gamma_i) in
                    Iterator::zip(inputs.iter(), acc.gammas.iter_mut().skip(1))
                {
                    *acc_gamma_i += &(z * a_i);
                }
                acc.delta += &WnafBase::<E::G1, WEIGHT_WINDOW>::new(proof.c.to_curve()) * &z_wnaf;
                acc.y += &z;
            }
        }
    }

    /// Builds the batch's pairing terms. When `unit_first` is set, the first
    /// proof has weight 1 and every other proof gets an independent random
    /// 128-bit weight (see [`random_weight`]). At most one proof in a combined pairing equation may
    /// have weight 1: two unit-weight proofs could carry errors that cancel.
    fn randomize_terms<R: Rng + CryptoRng>(
        self,
        mut rng: R,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
        unit_first: bool,
    ) -> PreparedBatchTerms<E> {
        let mut acc = Accumulator::new(pvk.vk.ic.len(), self.items.len());
        for (i, item) in self.items.iter().enumerate() {
            let z = if unit_first && i == 0 {
                None
            } else {
                Some(random_weight(|| {
                    u128::from(rng.next_u64()) | (u128::from(rng.next_u64()) << 64)
                }))
            };
            Self::accumulate(item, z, &mut acc);
        }
        acc.finish(pvk.vk)
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
    fn verify_multicore_prepared_unchecked(
        self,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let vk = pvk.vk;
        let ic_len = vk.ic.len();

        // Give each Rayon thread a Miller-loop work item while retaining
        // batching within each loop when parallelism is scarce.
        const MAX_CHUNK_SIZE: usize = 8;
        let threads = rayon::current_num_threads();
        let chunk_size = self.items.len().div_ceil(threads).clamp(1, MAX_CHUNK_SIZE);

        // The first proof of chunk 0 has weight 1; every other proof gets an
        // independent random weight. Only one proof in the final pairing
        // equation may have weight 1: two unit-weight proofs could carry
        // errors that cancel.
        let (acc, ml_result) = self
            .items
            .par_chunks(chunk_size)
            .enumerate()
            .map(|(chunk_index, items)| {
                let mut acc = Accumulator::<E>::new(ic_len, items.len());
                for (i, item) in items.iter().enumerate() {
                    let z = if chunk_index == 0 && i == 0 {
                        None
                    } else {
                        Some(random_weight(|| {
                            let mut bytes = [0; 16];
                            SysRng
                                .try_fill_bytes(&mut bytes)
                                .expect("system randomness must be available");
                            u128::from_le_bytes(bytes)
                        }))
                    };
                    Self::accumulate(item, z, &mut acc);
                }
                let ml_result = acc.proof_miller_loop();
                (acc, Some(ml_result))
            })
            .reduce(
                || (Accumulator::<E>::new(ic_len, 0), None),
                |(mut a, a_ml), (b, b_ml)| {
                    for (a, b) in a.gammas.iter_mut().zip(b.gammas) {
                        *a += b;
                    }
                    a.delta += b.delta;
                    a.y += b.y;
                    let ml = match (a_ml, b_ml) {
                        (Some(a), Some(b)) => Some(a + b),
                        (Some(a), None) | (None, Some(a)) => Some(a),
                        (None, None) => None,
                    };
                    (a, ml)
                },
            );

        let Some(mut ml_result) = ml_result else {
            return Ok(());
        };
        let [delta, gamma, beta] = normalize::<E>(&acc.key_points(vk))[..] else {
            unreachable!("three key points");
        };
        ml_result += E::multi_miller_loop(&[
            (&delta, &pvk.g2.delta_g2),
            (&gamma, &pvk.g2.gamma_g2),
            (&beta, &pvk.g2.beta_g2),
        ]);

        if ml_result.final_exponentiation() == E::Gt::identity() {
            Ok(())
        } else {
            Err(VerificationError::InvalidProof)
        }
    }
}

/// wNAF window for the 128-bit batch weights.
const WEIGHT_WINDOW: usize = 4;

/// Draws a batch weight uniformly from `[1, 2^128)`.
///
/// If any proof in a batch is invalid, the batch passes for at most one value
/// of that proof's weight, so with probability at most `1/(2^128 - 1)`. That
/// is below the roughly 2^-117 security level of BLS12-381. Weights shorter
/// than the field halve the doublings in each weighted multiplication.
fn random_weight<F: PrimeField>(mut draw: impl FnMut() -> u128) -> F {
    loop {
        let weight = draw();
        if weight != 0 {
            return F::from_u128(weight);
        }
    }
}

/// Multiplies a public point by a public full-width scalar in variable time.
fn mul_vartime<E: MultiMillerLoop>(base: &E::G1Affine, scalar: &E::Fr) -> E::G1 {
    &WnafBase::<E::G1, PUBLIC_INPUT_WINDOW>::new(base.to_curve())
        * &WnafScalar::<E::Fr, PUBLIC_INPUT_WINDOW>::new(scalar)
}

/// Converts `points` to affine form with one shared field inversion.
fn normalize<E: MultiMillerLoop>(points: &[E::G1]) -> Vec<E::G1Affine> {
    let mut affine = vec![E::G1Affine::identity(); points.len()];
    E::G1::batch_normalize(points, &mut affine);
    affine
}

/// Weighted sums of a batch's proofs.
struct Accumulator<E: MultiMillerLoop> {
    /// `z·A` for each proof, in projective form.
    a_terms: Vec<E::G1>,
    /// `-B` for each proof, in the same order as `a_terms`.
    neg_bs: Vec<E::G2Prepared>,
    /// `Σ z·a_i` for each public input `i`, with `a_0 = 1`.
    gammas: Vec<E::Fr>,
    /// `Σ z·C`.
    delta: E::G1,
    /// `Σ z`.
    y: E::Fr,
}

impl<E: MultiMillerLoop> Accumulator<E> {
    fn new(ic_len: usize, proofs: usize) -> Self {
        Self {
            a_terms: Vec::with_capacity(proofs),
            neg_bs: Vec::with_capacity(proofs),
            gammas: vec![E::Fr::ZERO; ic_len],
            delta: E::G1::identity(),
            y: E::Fr::ZERO,
        }
    }

    /// The G1 points paired with the key's delta, gamma, and beta:
    /// `Σ z·C`, `Ψ = Σ_i ic_i·gammas_i`, and `[Σ z]·alpha`.
    ///
    /// The beta term stands in for `[Σ z]·e(alpha, beta)`, which would need
    /// an exponentiation in the target group: `[y]·e(alpha, beta) = e([y]·alpha, beta)`.
    fn key_points(&self, vk: &VerifyingKey<E>) -> [E::G1; 3] {
        let psi = vk
            .ic
            .iter()
            .zip(&self.gammas)
            .map(|(base, scalar)| mul_vartime::<E>(base, scalar))
            .sum();
        [self.delta, psi, mul_vartime::<E>(&vk.alpha_g1, &self.y)]
    }

    /// Runs the Miller loop over the accumulated `(z·A, -B)` pairs.
    #[cfg(feature = "multicore")]
    fn proof_miller_loop(&mut self) -> E::Result {
        let a_terms = normalize::<E>(&std::mem::take(&mut self.a_terms));
        let neg_bs = std::mem::take(&mut self.neg_bs);
        let terms = a_terms.iter().zip(neg_bs.iter()).collect::<Vec<_>>();
        E::multi_miller_loop(&terms)
    }

    /// Builds the batch's pairing terms, normalizing every G1 point with one
    /// shared inversion.
    fn finish(mut self, vk: &VerifyingKey<E>) -> PreparedBatchTerms<E> {
        let key_points = self.key_points(vk);
        self.a_terms.extend(key_points);
        let mut affine = normalize::<E>(&self.a_terms);
        let beta = affine.pop().expect("key points were appended");
        let gamma = affine.pop().expect("key points were appended");
        let delta = affine.pop().expect("key points were appended");
        PreparedBatchTerms {
            variable: affine.into_iter().zip(self.neg_bs).collect(),
            delta,
            gamma,
            beta,
        }
    }
}
