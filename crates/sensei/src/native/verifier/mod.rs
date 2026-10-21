//! Shared verifier for the three pinned Orchard circuits.
//!
//! The keys share the evaluation domain, gate and lookup expressions, query
//! order, and opening protocol. Their circuit differences are encoded in the
//! fixed-column and permutation commitments, so [`quotient_evaluation`] and
//! [`super::protocol::opening`] apply to all three. Each proof's transcript
//! absorbs its selected key's representative to bind it to that circuit.
//!
//! Historical instances populate nine rows; post-NU6.3 adds
//! `disable_cross_address` as the tenth. [`VerificationRequest::new`] requires
//! that flag to be false for historical keys. All remaining rows are zero,
//! allowing [`absorb_instances`] and the final equation to use prefixes of one
//! shared Lagrange bank.
//!
//! The `pinned_keys_and_instance_prefixes_match_reference` test checks the
//! shared constraint system, commitments, transcript representatives, and
//! instance prefixes against Orchard. Verification trusts these embedded key
//! facts; adding a version requires checking that it fits this shared structure.
//!
//! Each worker folds complete weighted proof equations. Instance commitments
//! enter the transcript as points, but their equation terms are distributed
//! over the populated Lagrange bases and W. Terms for the SRS and deduplicated
//! verifying-key bank accumulate across all proofs before the single final
//! identity check.
//!
//! After [`VerificationRequest::new`] accepts the request shape, malformed
//! encodings, transcript degeneracies, and a nonidentity final equation report
//! [`Error::InvalidProof`]. These concern a fixed proof/statement transcript;
//! resampling batch weights cannot change its challenges. Only a zero weight
//! sampled independently by [`verify`] requests [`Error::RetryRandomness`].
//! MSM shape failures instead report [`Error::InternalInvariant`]: [`Equation`]
//! and [`VerifierRuntime`] assemble their banks, indices, and output sizes
//! internally. Neither a failed proof equation nor a broken MSM shape
//! establishes a particular private-witness failure. See [`Error`] for caller
//! recovery.
//!
//! # Preparation and scratch
//!
//! See [`super::srs`] for the shared runtime owners and workspace retention
//! policy. [`VerifierRuntime::get`] obtains the shared SRS and executor before
//! preparing its own verifying-key bank in that executor. [`RUNTIME`] retains a
//! successful `VerifierRuntime`; unlike the prover's cell it stores no
//! `Result`. The public [`crate::warm_up_verifier`] contract describes this
//! preparation-only entry point, which acquires no verification scratch.
//!
//! [`verify`] returns immediately for an empty batch. Otherwise it samples batch
//! weights on the calling thread before runtime initialization, scratch
//! acquisition, or pool entry; a singleton needs no draws. The borrowed
//! [`RandomSource`] stays on that thread, allowing reentrant callbacks, and only
//! the weights reach workers. Each worker chunk creates its own [`Equation`]
//! and [`MsmWorkspace`]; that scratch is dropped after folding the chunk. After
//! merging successful equations, [`VerifierRuntime::check`] borrows a separate
//! workspace for the final MSM. Only this last workspace participates in the
//! runtime's idle-slot retention policy.

use super::{
    commitment::{FixedGenerator, MsmWorkspace},
    executor::PoolExecutor,
    expression_layout::{GATE_CONSTRAINT_COUNT, LOOKUPS},
    programs::{self, Algebra},
    protocol::{
        POINT_SETS,
        opening::{
            ActionPolynomial, FixedPolynomial, OPENING_GROUPS, OPENING_POINTS, OPENING_ROTATIONS,
        },
    },
    queries::{ADVICE_QUERIES, ColumnKind, FIXED_QUERIES, PERMUTATION_COLUMNS},
    srs::{PREPARED_POINTS, PreparedSrs},
    transcript::Reader,
    worker::Execution,
};
use crate::{
    Error, RandomSource, VerificationRequest,
    rng::sample_fp,
    tuning::{self, WorkspaceRetention},
    types::NativeStatement,
};
use sensei_shared::{
    ADVICE_COLUMNS, BLINDING_FACTORS, FIXED_COLUMNS, INSTANCE_VALUE_COUNT, K, N,
    PERMUTATION_CHUNK_LEN, PERMUTATION_COLUMN_COUNT, PERMUTATION_SETS, QUOTIENT_PIECES,
    commitment_tables::Codebook,
    records::{VERIFIER_POINT_COUNT, VERIFIER_VERSION_COUNT, VerifierCommitments},
};
use std::sync::{Arc, Mutex, OnceLock};
use udon::{
    curve::{
        PreparedAffinePoint, Vesta, VestaAffine, VestaPoint, VestaProjective, batch_normalize,
    },
    field::{Fp, Fq, batch_invert},
    msm::{AlphaTable, Bases, Input},
};

// Equation::fixed segments: coefficient SRS 0..FIXED_OFFSET, verifying-key
// commitments FIXED_OFFSET..INSTANCE_OFFSET, instance Lagrange bases
// INSTANCE_OFFSET..BLIND_GENERATOR_SLOT, then the blinding generator W and IPA
// generator U at BLIND_GENERATOR_SLOT and IPA_GENERATOR_SLOT.
const FIXED_OFFSET: usize = N;
const INSTANCE_OFFSET: usize = FIXED_OFFSET + VERIFIER_POINT_COUNT;
const BLIND_GENERATOR_SLOT: usize = INSTANCE_OFFSET + INSTANCE_VALUE_COUNT;
const IPA_GENERATOR_SLOT: usize = BLIND_GENERATOR_SLOT + 1;
const BANK_LEN: usize = IPA_GENERATOR_SLOT + 1;
const LOOKUP_COUNT: usize = LOOKUPS.len();
const ROUNDS: usize = K as usize;

// Stored permutation grand-product evaluations at rotations 0, +1, and
// -(BLINDING_FACTORS + 1). The final set omits the last evaluation.
const PERMUTATION_EVAL_CURRENT: usize = 0;
const PERMUTATION_EVAL_NEXT: usize = 1;
const PERMUTATION_EVAL_LAST: usize = 2;

// Stored lookup slots 0/1 hold the grand product at rotations 0/+1. The
// remaining slots hold the permuted input at 0/-1 and permuted table at 0.
const LOOKUP_EVAL_INPUT_CURRENT: usize = 2;
const LOOKUP_EVAL_INPUT_PREVIOUS: usize = 3;
const LOOKUP_EVAL_TABLE: usize = 4;

crate::static_data::embed_struct! {
    /// Default-blinded commitments and each version's column mapping.
    pub(in crate::native) static VK_DATA: VerifierCommitments =
        artifact_path!(verifier_commitments);
}
const VK_COMMITMENTS: &[VestaAffine; VERIFIER_POINT_COUNT] = &VK_DATA.points;
const VERSION_MASKS: usize = 1 << VERIFIER_VERSION_COUNT;

struct VerifierRuntime {
    srs: Arc<PreparedSrs>,
    vk_bases: Vec<PreparedAffinePoint<Vesta>>,
    vk_indices: [Vec<u32>; VERSION_MASKS],
    codebook: Arc<Codebook>,
    executor: &'static PoolExecutor,
    idle: Mutex<Option<MsmWorkspace>>,
}

static RUNTIME: OnceLock<VerifierRuntime> = OnceLock::new();

impl VerifierRuntime {
    fn get() -> &'static Self {
        RUNTIME.get_or_init(|| Self::new(PreparedSrs::shared(), PoolExecutor::get()))
    }
    fn new(srs: Arc<PreparedSrs>, executor: &'static PoolExecutor) -> Self {
        // Only the VK commitments need verifier-owned point expansions. The
        // residue codebook is shared with every equal-width SRS bank.
        let codebook = srs.codebook(tuning::VERIFIER_FIXED_ALPHA_WIDTH);
        // The shared SRS supplies the codebook for this fixed tuning width;
        // the embedded VK bank's constant length must have representable sizes.
        let requirements = codebook
            .view()
            .description()
            .requirements::<Vesta, PreparedAffinePoint<Vesta>>(VK_COMMITMENTS.len())
            .expect("fixed verifier bank");
        let mut vk_bases = vec![
            PreparedAffinePoint::from_affine(&VestaAffine::GENERATOR);
            requirements.table_entries
        ];
        executor.run(|context| {
            AlphaTable::prepare(
                codebook.view(),
                VK_COMMITMENTS,
                &mut vk_bases,
                &mut vec![VestaProjective::IDENTITY; requirements.projective_scratch],
                &mut vec![Fq::ZERO; requirements.field_scratch],
                executor.budget(),
                context,
            );
        });
        Self {
            srs,
            vk_bases,
            vk_indices: core::array::from_fn(|mask| {
                let mut used = [false; VERIFIER_POINT_COUNT];
                for (version, columns) in VK_DATA.columns.iter().enumerate() {
                    if mask & (1 << version) != 0 {
                        for &index in columns {
                            used[index as usize] = true;
                        }
                    }
                }
                used.iter()
                    .enumerate()
                    .filter_map(|(i, &used)| used.then_some(i as u32))
                    .collect()
            }),
            codebook,
            executor,
            idle: Mutex::new(None),
        }
    }
    fn check(&self, equation: &Equation) -> Result<(), Error> {
        let retain = tuning::WORKSPACE == WorkspaceRetention::RetainOne;
        let mut scratch = if retain {
            self.idle.lock().unwrap_or_else(|e| e.into_inner()).take()
        } else {
            None
        }
        .unwrap_or_else(MsmWorkspace::new);
        let result = self.evaluate(equation, &mut scratch).and_then(|point| {
            if point.is_identity() {
                Ok(())
            } else {
                Err(Error::InvalidProof)
            }
        });
        if retain {
            let mut idle = self.idle.lock().unwrap_or_else(|e| e.into_inner());
            if idle.is_none() {
                *idle = Some(scratch);
            }
        }
        result
    }
    fn evaluate(
        &self,
        equation: &Equation,
        scratch: &mut MsmWorkspace,
    ) -> Result<VestaProjective, Error> {
        self.executor.run(|executor| {
            let mut output = [VestaProjective::IDENTITY; 4];
            let bases =
                Bases::AlphaPrepared(AlphaTable::bind(self.codebook.view(), &self.vk_bases));
            let indices = &self.vk_indices[usize::from(equation.versions)];
            let mut selected = [Fp::ZERO; VERIFIER_POINT_COUNT];
            // Current-only and complete-prefix unions retain the dense path.
            // Other combinations index the same prepared bank without copying points.
            let vk_input = if indices
                .last()
                .is_none_or(|&last| last as usize + 1 == indices.len())
            {
                Input::new(
                    bases.range(0..indices.len()),
                    &equation.fixed[FIXED_OFFSET..FIXED_OFFSET + indices.len()],
                )
            } else {
                for (scalar, &index) in selected.iter_mut().zip(indices) {
                    *scalar = equation.fixed[FIXED_OFFSET + index as usize];
                }
                // VerifierRuntime::new derives in-bank indices, paired above
                // with one scalar each.
                Input::indexed(bases, indices, &selected[..indices.len()])
                    .map_err(|_| Error::InternalInvariant)?
            };
            // Equation::new/point/merge preserve these bank and point/scalar
            // lengths; four inputs require exactly the four outputs above.
            scratch
                .prepare(
                    &[
                        Input::new(self.srs.coefficient_bases(), &equation.fixed[..N]),
                        vk_input,
                        Input::new(
                            self.srs.lagrange_bases().range(0..INSTANCE_VALUE_COUNT),
                            &equation.fixed[INSTANCE_OFFSET..BLIND_GENERATOR_SLOT],
                        ),
                        Input::new(Bases::Affine(&equation.points), &equation.scalars),
                    ],
                    self.executor.budget(),
                )
                .map_err(|_| Error::InternalInvariant)?
                .execute(&mut output, executor)
                .map_err(|_| Error::InternalInvariant)?;
            let fixed = FixedGenerator::sum(
                [&self.srs.blind_generator, &self.srs.ipa_generator],
                &[
                    equation.fixed[BLIND_GENERATOR_SLOT],
                    equation.fixed[IPA_GENERATOR_SLOT],
                ],
            );
            Ok(output.iter().fold(fixed, |sum, point| sum.add(point)))
        })
    }
}

pub(crate) fn warm_up_verifier() {
    let _ = VerifierRuntime::get();
}

#[cfg(all(test, feature = "prover"))]
pub(super) fn prepared_srs_for_test() -> Option<&'static Arc<PreparedSrs>> {
    RUNTIME.get().map(|runtime| &runtime.srs)
}

pub(crate) fn verify(
    requests: &[VerificationRequest<'_>],
    rng: &mut dyn RandomSource,
) -> Result<(), Error> {
    if requests.is_empty() {
        return Ok(());
    }
    // Sample before executor initialization and scratch acquisition. The first
    // proof has weight one; each later equation receives an independent weight.
    let mut weights = vec![<Fp>::ONE; requests.len()];
    for weight in &mut weights[1..] {
        *weight = sample_fp(rng)?;
        if weight.is_zero() {
            // A zero weight would omit a proof's equation. Retry the batch
            // with fresh weights; its proof transcripts need not change.
            return Err(Error::RetryRandomness);
        }
    }
    let runtime = VerifierRuntime::get();
    let results = runtime.executor.run(|executor| {
        let execution = Execution::new(executor, runtime.executor.budget());
        // Bounded number of worker-local fixed banks, independent of batch size.
        let workers = execution.budget.get();
        let chunk = requests.len().div_ceil(workers);
        execution.map(
            requests.chunks(chunk).zip(weights.chunks(chunk)),
            |(requests, weights), execution| {
                let mut equation = Equation::new();
                let mut msm = MsmWorkspace::new();
                for (request, &weight) in requests.iter().zip(weights) {
                    equation.proof(request, weight, &runtime.srs, &mut msm, execution.serial())?;
                }
                Ok::<_, Error>(equation)
            },
        )
    });
    let mut combined = Equation::new();
    for result in results {
        combined.merge(result?);
    }
    runtime.check(&combined)
}

struct Equation {
    versions: u8,
    fixed: Vec<Fp>,
    points: Vec<VestaAffine>,
    scalars: Vec<Fp>,
    #[cfg(test)]
    challenges: Vec<[u8; 32]>,
}
impl Equation {
    fn new() -> Self {
        Self {
            versions: 0,
            fixed: vec![<Fp>::ZERO; BANK_LEN],
            points: Vec::new(),
            scalars: Vec::new(),
            #[cfg(test)]
            challenges: Vec::new(),
        }
    }
    fn merge(&mut self, other: Self) {
        self.versions |= other.versions;
        for (a, b) in self.fixed.iter_mut().zip(other.fixed) {
            *a = a.add(&b);
        }
        self.points.extend(other.points);
        self.scalars.extend(other.scalars);
    }
    fn point(&mut self, reader: &mut Reader<'_>) -> Result<usize, Error> {
        let index = self.points.len();
        self.points.push(reader.point()?);
        self.scalars.push(<Fp>::ZERO);
        Ok(index)
    }
    fn points<const C: usize>(&mut self, reader: &mut Reader<'_>) -> Result<[usize; C], Error> {
        let mut indices = [0; C];
        for index in &mut indices {
            *index = self.point(reader)?;
        }
        Ok(indices)
    }
    fn proof(
        &mut self,
        request: &VerificationRequest<'_>,
        weight: Fp,
        srs: &PreparedSrs,
        msm: &mut MsmWorkspace,
        execution: Execution<'_>,
    ) -> Result<(), Error> {
        let mut reader = Reader::new(request.proof);
        let version = request.version;
        self.versions |= 1 << version.index();
        let columns = &VK_DATA.columns[version.index()];
        let instance_len = version.instance_len();
        reader.common_scalar(&version.vk_representative());
        let statements: Vec<_> = request.statements.iter().map(|s| s.native()).collect();
        absorb_instances(&mut reader, &statements, instance_len, srs, msm, execution)?;
        let mut actions: Vec<_> = (0..statements.len())
            .map(|_| ActionData::default())
            .collect();
        for a in &mut actions {
            a.advice = self.points(&mut reader)?;
        }
        let theta = reader.challenge();
        for a in &mut actions {
            for pair in &mut a.lookup_pairs {
                *pair = self.points(&mut reader)?;
            }
        }
        let beta = reader.challenge();
        let gamma = reader.challenge();
        for a in &mut actions {
            a.permutation = self.points(&mut reader)?;
        }
        for a in &mut actions {
            a.lookup_products = self.points(&mut reader)?;
        }
        let vanishing = self.point(&mut reader)?;
        let y = reader.challenge();
        let quotient: [usize; QUOTIENT_PIECES] = self.points(&mut reader)?;
        let x = reader.challenge();
        // Claimed instance evaluations are proof inputs, including for malformed
        // proofs; substituting honest evaluations changes the reference equation.
        for a in &mut actions {
            a.instance_eval = reader.scalar()?;
        }
        for a in &mut actions {
            a.advice_evals = reader.scalars()?;
        }
        let fixed_evals = reader.scalars::<{ FIXED_QUERIES.len() }>()?;
        let vanishing_eval = reader.scalar()?;
        let sigma_evals = reader.scalars::<PERMUTATION_COLUMN_COUNT>()?;
        for a in &mut actions {
            for (i, set) in a.permutation_evals.iter_mut().enumerate() {
                set[PERMUTATION_EVAL_CURRENT] = reader.scalar()?;
                set[PERMUTATION_EVAL_NEXT] = reader.scalar()?;
                if i + 1 < PERMUTATION_SETS {
                    set[PERMUTATION_EVAL_LAST] = reader.scalar()?;
                }
            }
        }
        for a in &mut actions {
            for lookup in &mut a.lookup_evals {
                *lookup = reader.scalars()?;
            }
        }
        let xn = x.pow_u64(N as u64);
        let h_eval = quotient_evaluation(
            &actions,
            &fixed_evals,
            &sigma_evals,
            Challenges {
                theta,
                beta,
                gamma,
                y,
                x,
                xn,
            },
        )?;
        let x1 = reader.challenge();
        let x2 = reader.challenge();
        let q_prime = self.point(&mut reader)?;
        let x3 = reader.challenge();
        let u: [Fp; POINT_SETS] = reader.scalars()?;
        let x4 = reader.challenge();
        // K = 11 is a fixed circuit parameter within Fp's 2-adicity (32);
        // neither the request nor the transcript chooses this domain.
        let omega = <Fp>::root_of_unity(K).expect("fixed domain");
        let omega_inv = <Fp>::root_of_unity_inverse(K).expect("fixed domain");
        let points = OPENING_ROTATIONS.map(|rotation| {
            x.mul(&if rotation < 0 {
                omega_inv.pow_u64((-rotation) as u64)
            } else {
                omega.pow_u64(rotation as u64)
            })
        });
        if x.is_zero() {
            return Err(Error::InvalidProof);
        }
        let mut eval_sets = [[<Fp>::ZERO; OPENING_POINTS]; POINT_SETS];
        let mut group_weight = weight;
        for (group_index, group) in OPENING_GROUPS.iter().enumerate().rev() {
            let mut power = <Fp>::ONE;
            let evals = &mut eval_sets[group_index];
            for &polynomial in group.fixed().iter().rev() {
                let coefficient = power.mul(&group_weight);
                let eval = match polynomial {
                    FixedPolynomial::Fixed(column) => {
                        let slot = FIXED_OFFSET + columns[column as usize] as usize;
                        self.fixed[slot] = self.fixed[slot].add(&coefficient);
                        fixed_evals[fixed_query(column as usize)]
                    }
                    FixedPolynomial::Sigma(column) => {
                        let slot = FIXED_OFFSET + columns[FIXED_COLUMNS + column as usize] as usize;
                        self.fixed[slot] = self.fixed[slot].add(&coefficient);
                        sigma_evals[column as usize]
                    }
                    FixedPolynomial::Quotient => {
                        let mut coefficient = coefficient;
                        for &index in &quotient {
                            self.scalars[index] = self.scalars[index].add(&coefficient);
                            coefficient = coefficient.mul(&xn);
                        }
                        h_eval
                    }
                    FixedPolynomial::Vanishing => {
                        self.scalars[vanishing] = self.scalars[vanishing].add(&coefficient);
                        vanishing_eval
                    }
                };
                for point in group.point_ids() {
                    evals[point] = evals[point].add(&power.mul(&eval));
                }
                power = power.mul(&x1);
            }
            for (a, statement) in actions.iter().zip(&statements).rev() {
                for &polynomial in group.per_action().iter().rev() {
                    let coefficient = power.mul(&group_weight);
                    match polynomial {
                        ActionPolynomial::Instance => {
                            for (slot, value) in self.fixed
                                [INSTANCE_OFFSET..INSTANCE_OFFSET + instance_len]
                                .iter_mut()
                                .zip(statement.iter())
                            {
                                *slot = slot.add(&coefficient.mul(value));
                            }
                            self.fixed[BLIND_GENERATOR_SLOT] =
                                self.fixed[BLIND_GENERATOR_SLOT].add(&coefficient);
                        }
                        _ => {
                            let index = a.commitment(polynomial);
                            self.scalars[index] = self.scalars[index].add(&coefficient);
                        }
                    }
                    for point in group.point_ids() {
                        evals[point] = evals[point]
                            .add(&power.mul(&a.evaluation(polynomial, OPENING_ROTATIONS[point])));
                    }
                    power = power.mul(&x1);
                }
            }
            group_weight = group_weight.mul(&x4);
        }
        self.scalars[q_prime] = self.scalars[q_prime].add(&group_weight);
        let mut v = multiopen_evaluation(&points, &eval_sets, &u, x2, x3)?;
        for eval in u {
            v = v.mul(&x4).add(&eval);
        }
        self.ipa(&mut reader, v, x3, weight)?;
        #[cfg(test)]
        self.challenges.extend_from_slice(&reader.challenges);
        reader.finish()
    }
    fn ipa(&mut self, reader: &mut Reader<'_>, v: Fp, x: Fp, weight: Fp) -> Result<(), Error> {
        let s = self.point(reader)?;
        self.scalars[s] = self.scalars[s].add(&weight.mul(&reader.challenge()));
        let z = reader.challenge();
        let mut rounds = [[0; 2]; ROUNDS];
        let mut u = [<Fp>::ZERO; ROUNDS];
        for (round, challenge) in rounds.iter_mut().zip(&mut u) {
            *round = self.points(reader)?;
            *challenge = reader.challenge();
        }
        let c = reader.scalar()?;
        let f = reader.scalar()?;
        let mut inv = u;
        invert(&mut inv)?;
        for (([l, r], u), inverse) in rounds.into_iter().zip(u).zip(inv) {
            self.scalars[l] = self.scalars[l].add(&weight.mul(&inverse));
            self.scalars[r] = self.scalars[r].add(&weight.mul(&u));
        }
        let mut b = <Fp>::ONE;
        let mut x_power = x;
        let mut coefficients = [<Fp>::ZERO; N];
        coefficients[0] = c.neg().mul(&weight);
        let mut len = 1;
        for challenge in u.into_iter().rev() {
            b = b.mul(&<Fp>::ONE.add(&challenge.mul(&x_power)));
            x_power = x_power.square();
            for i in 0..len {
                coefficients[len + i] = coefficients[i].mul(&challenge);
            }
            len *= 2;
        }
        for (slot, value) in self.fixed[..N].iter_mut().zip(coefficients) {
            *slot = slot.add(&value);
        }
        self.fixed[0] = self.fixed[0].sub(&weight.mul(&v));
        self.fixed[IPA_GENERATOR_SLOT] =
            self.fixed[IPA_GENERATOR_SLOT].sub(&weight.mul(&c).mul(&b).mul(&z));
        self.fixed[BLIND_GENERATOR_SLOT] = self.fixed[BLIND_GENERATOR_SLOT].sub(&weight.mul(&f));
        Ok(())
    }
}

fn absorb_instances(
    reader: &mut Reader<'_>,
    statements: &[NativeStatement],
    instance_len: usize,
    srs: &PreparedSrs,
    msm: &mut MsmWorkspace,
    execution: Execution<'_>,
) -> Result<(), Error> {
    let bases = srs.lagrange_bases().range(0..instance_len);
    let inputs: Vec<_> = statements
        .iter()
        .map(|s| Input::new(bases, &s[..instance_len]))
        .collect();
    let mut projective = vec![VestaProjective::IDENTITY; statements.len()];
    // The version selects a prefix of NativeStatement and the same SRS bank;
    // one output was allocated per input. Failure is an internal MSM contract.
    msm.prepare(&inputs, execution.budget)
        .map_err(|_| Error::InternalInvariant)?
        .execute(&mut projective, &execution)
        .map_err(|_| Error::InternalInvariant)?;
    for point in &mut projective {
        *point = point.add_mixed(&PREPARED_POINTS.blind_generator);
    }
    let mut points = vec![VestaPoint::IDENTITY; statements.len()];
    let mut scratch = vec![Fq::ZERO; statements.len()];
    batch_normalize(&projective, &mut points, &mut scratch);
    for point in points {
        reader.common_point(&point)?;
    }
    Ok(())
}

#[derive(Default)]
struct ActionData {
    advice: [usize; ADVICE_COLUMNS],
    lookup_pairs: [[usize; 2]; LOOKUP_COUNT],
    permutation: [usize; PERMUTATION_SETS],
    lookup_products: [usize; LOOKUP_COUNT],
    instance_eval: Fp,
    advice_evals: [Fp; ADVICE_QUERIES.len()],
    permutation_evals: [[Fp; 3]; PERMUTATION_SETS],
    lookup_evals: [[Fp; 5]; LOOKUP_COUNT],
}
impl ActionData {
    fn commitment(&self, polynomial: ActionPolynomial) -> usize {
        match polynomial {
            ActionPolynomial::Advice(i) => self.advice[i as usize],
            ActionPolynomial::Permutation(i) => self.permutation[i as usize],
            ActionPolynomial::LookupProduct(i) => self.lookup_products[i as usize],
            ActionPolynomial::LookupInput(i) => self.lookup_pairs[i as usize][0],
            ActionPolynomial::LookupTable(i) => self.lookup_pairs[i as usize][1],
            ActionPolynomial::Instance => unreachable!("instances fold into the fixed bank"),
        }
    }
    fn evaluation(&self, polynomial: ActionPolynomial, rotation: i32) -> Fp {
        match polynomial {
            ActionPolynomial::Instance => self.instance_eval,
            ActionPolynomial::Advice(column) => {
                // OPENING_GROUPS is const-derived from ADVICE_QUERIES; the
                // caller supplies only that group's polynomial/rotation pairs.
                self.advice_evals[ADVICE_QUERIES
                    .iter()
                    .position(|q| q.column == column as usize && q.rotation == rotation)
                    .expect("derived query")]
            }
            ActionPolynomial::Permutation(i) => {
                self.permutation_evals[i as usize][match rotation {
                    0 => PERMUTATION_EVAL_CURRENT,
                    1 => PERMUTATION_EVAL_NEXT,
                    _ => PERMUTATION_EVAL_LAST,
                }]
            }
            ActionPolynomial::LookupProduct(i) => {
                // Slots 0/1 hold the grand product at rotations 0/+1.
                self.lookup_evals[i as usize][usize::from(rotation != 0)]
            }
            ActionPolynomial::LookupInput(i) => {
                self.lookup_evals[i as usize][if rotation == 0 {
                    LOOKUP_EVAL_INPUT_CURRENT
                } else {
                    LOOKUP_EVAL_INPUT_PREVIOUS
                }]
            }
            ActionPolynomial::LookupTable(i) => self.lookup_evals[i as usize][LOOKUP_EVAL_TABLE],
        }
    }
}
fn fixed_query(column: usize) -> usize {
    // Opening fixed columns are derived from FIXED_QUERIES. The other caller
    // uses the pinned PERMUTATION_COLUMNS, whose fixed columns are queried at 0.
    FIXED_QUERIES
        .iter()
        .position(|q| q.column == column)
        .expect("fixed column query")
}
struct Evaluations<'a> {
    fixed: &'a [Fp],
    advice: &'a [Fp],
}
impl Algebra for Evaluations<'_> {
    type Value = Fp;
    fn fixed(&self, index: u8) -> Fp {
        self.fixed[index as usize]
    }
    fn advice(&self, index: u8) -> Fp {
        self.advice[index as usize]
    }
    fn gated(&self, factor: impl FnOnce() -> Fp, body: Fp) -> Fp {
        factor().mul(&body)
    }
}
struct Challenges {
    theta: Fp,
    beta: Fp,
    gamma: Fp,
    y: Fp,
    x: Fp,
    xn: Fp,
}
fn quotient_evaluation(
    actions: &[ActionData],
    fixed: &[Fp],
    sigma: &[Fp],
    Challenges {
        theta,
        beta,
        gamma,
        y,
        x,
        xn,
    }: Challenges,
) -> Result<Fp, Error> {
    // The same fixed K/Fp domain used by Equation::proof; no proof input
    // affects root availability.
    let omega_inv = <Fp>::root_of_unity_inverse(K).expect("fixed domain");
    let mut roots = [<Fp>::ONE; BLINDING_FACTORS + 2];
    for i in 1..roots.len() {
        roots[i] = roots[i - 1].mul(&omega_inv);
    }
    let mut denominators = roots.map(|root| x.sub(&root));
    invert(&mut denominators)?;
    let scale = xn.sub(&<Fp>::ONE).mul(&<Fp>::power_of_two_inverse(K));
    let lagrange = core::array::from_fn::<_, { BLINDING_FACTORS + 2 }, _>(|i| {
        roots[i].mul(&scale).mul(&denominators[i])
    });
    let l0 = lagrange[0];
    let last = lagrange[BLINDING_FACTORS + 1];
    let active = <Fp>::ONE.sub(&lagrange[1..].iter().fold(<Fp>::ZERO, |a, b| a.add(b)));
    let mut fold = <Fp>::ZERO;
    let mut push = |term| {
        fold = fold.mul(&y).add(&term);
    };
    for a in actions {
        let algebra = Evaluations {
            fixed,
            advice: &a.advice_evals,
        };
        for index in 0..GATE_CONSTRAINT_COUNT {
            push(programs::expression(&algebra, index));
        }
        push(l0.mul(&<Fp>::ONE.sub(&a.permutation_evals[0][PERMUTATION_EVAL_CURRENT])));
        let last_z = a.permutation_evals[PERMUTATION_SETS - 1][PERMUTATION_EVAL_CURRENT];
        push(last.mul(&last_z.square().sub(&last_z)));
        for i in 1..PERMUTATION_SETS {
            push(
                l0.mul(
                    &a.permutation_evals[i][PERMUTATION_EVAL_CURRENT]
                        .sub(&a.permutation_evals[i - 1][PERMUTATION_EVAL_LAST]),
                ),
            );
        }
        let mut delta = beta.mul(&x);
        for (set, columns) in PERMUTATION_COLUMNS
            .chunks(PERMUTATION_CHUNK_LEN)
            .enumerate()
        {
            let mut left = a.permutation_evals[set][PERMUTATION_EVAL_NEXT];
            let mut right = a.permutation_evals[set][PERMUTATION_EVAL_CURRENT];
            for (i, column) in columns.iter().enumerate() {
                let eval = match column.kind {
                    ColumnKind::Instance => a.instance_eval,
                    ColumnKind::Advice => {
                        a.evaluation(ActionPolynomial::Advice(column.index as u8), 0)
                    }
                    ColumnKind::Fixed => fixed[fixed_query(column.index)],
                };
                left = left.mul(
                    &eval
                        .add(&beta.mul(&sigma[set * PERMUTATION_CHUNK_LEN + i]))
                        .add(&gamma),
                );
                right = right.mul(&eval.add(&delta).add(&gamma));
                delta = delta.mul(&<Fp>::DELTA);
            }
            push(active.mul(&left.sub(&right)));
        }
        for (lookup, [z, z_next, input, input_prev, table]) in LOOKUPS.iter().zip(a.lookup_evals) {
            let compress = |range: super::expression_layout::ExpressionRange| {
                range.indices().fold(<Fp>::ZERO, |acc, i| {
                    acc.mul(&theta).add(&programs::expression(&algebra, i))
                })
            };
            push(l0.mul(&<Fp>::ONE.sub(&z)));
            push(last.mul(&z.square().sub(&z)));
            push(
                active.mul(
                    &z_next.mul(&input.add(&beta)).mul(&table.add(&gamma)).sub(
                        &z.mul(&compress(lookup.inputs()).add(&beta))
                            .mul(&compress(lookup.tables()).add(&gamma)),
                    ),
                ),
            );
            push(l0.mul(&input.sub(&table)));
            push(active.mul(&input.sub(&table)).mul(&input.sub(&input_prev)));
        }
    }
    Ok(fold.mul(&xn.sub(&<Fp>::ONE).invert().ok_or(Error::InvalidProof)?))
}

fn invert(values: &mut [Fp]) -> Result<(), Error> {
    // These denominators/challenges come from the supplied proof transcript.
    // Unlike prover retries, fresh verifier batch weights cannot change them.
    if values.iter().any(<Fp>::is_zero) {
        return Err(Error::InvalidProof);
    }
    // All callers invert small fixed protocol sets, never one value per Action.
    let mut scratch = [<Fp>::ZERO; POINT_SETS * (OPENING_POINTS + 1)];
    batch_invert(values, &mut scratch[..values.len()]);
    Ok(())
}
fn multiopen_evaluation(
    points: &[Fp; OPENING_POINTS],
    evals: &[[Fp; OPENING_POINTS]; POINT_SETS],
    u: &[Fp; POINT_SETS],
    x2: Fp,
    x3: Fp,
) -> Result<Fp, Error> {
    let mut denominators = Vec::with_capacity(POINT_SETS * (OPENING_POINTS + 1));
    for group in &OPENING_GROUPS {
        for j in group.point_ids() {
            denominators.push(
                group
                    .point_ids()
                    .filter(|&k| k != j)
                    .fold(<Fp>::ONE, |a, k| a.mul(&points[j].sub(&points[k]))),
            );
        }
        denominators.push(
            group
                .point_ids()
                .fold(<Fp>::ONE, |a, j| a.mul(&x3.sub(&points[j]))),
        );
    }
    invert(&mut denominators)?;
    // The identical OPENING_GROUPS traversal below consumes the interpolation
    // entries and then one vanishing entry appended for each group above.
    let mut inverse = denominators.into_iter();
    let mut v = <Fp>::ZERO;
    for ((group, evals), &u) in OPENING_GROUPS.iter().zip(evals).zip(u) {
        let mut r = <Fp>::ZERO;
        for j in group.point_ids() {
            let numerator = group
                .point_ids()
                .filter(|&k| k != j)
                .fold(<Fp>::ONE, |a, k| a.mul(&x3.sub(&points[k])));
            r = r.add(
                &evals[j]
                    .mul(&numerator)
                    .mul(&inverse.next().expect("interpolation denominator")),
            );
        }
        v = v.mul(&x2).add(
            &u.sub(&r)
                .mul(&inverse.next().expect("vanishing denominator")),
        );
    }
    Ok(v)
}

#[cfg(test)]
mod tests;
