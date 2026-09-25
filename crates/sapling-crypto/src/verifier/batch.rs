use bellman::groth16;
use bls12_381::Bls12;
use group::GroupEncoding;
use rand_core::{CryptoRng, Rng};
use std::sync::OnceLock;

use super::SaplingVerificationContextInner;
use crate::{
    bundle::{Authorized, Bundle},
    circuit::{OutputVerifyingKey, SpendVerifyingKey},
};

#[cfg(feature = "multicore")]
const MAX_JOINT_PROOFS_PER_KIND: usize = 1;

/// Borrowed Sapling verifying keys for repeated [`BatchValidator`]s.
///
/// Each key's fixed G2 terms are prepared on first use. Keeping this value
/// across batches reuses that preparation without preparing an unused key.
pub struct PreparedBatchVerifyingKeys<'a> {
    spend_vk: &'a SpendVerifyingKey,
    output_vk: &'a OutputVerifyingKey,
    spend: OnceLock<groth16::batch::PreparedBatchVerifyingKey<'a, Bls12>>,
    output: OnceLock<groth16::batch::PreparedBatchVerifyingKey<'a, Bls12>>,
}

impl<'a> PreparedBatchVerifyingKeys<'a> {
    /// Borrows the Spend and Output verifying keys for batch validation.
    pub fn new(spend_vk: &'a SpendVerifyingKey, output_vk: &'a OutputVerifyingKey) -> Self {
        Self {
            spend_vk,
            output_vk,
            spend: OnceLock::new(),
            output: OnceLock::new(),
        }
    }

    fn spend(&self) -> &groth16::batch::PreparedBatchVerifyingKey<'a, Bls12> {
        self.spend
            .get_or_init(|| groth16::batch::PreparedBatchVerifyingKey::from(&self.spend_vk.0))
    }

    fn output(&self) -> &groth16::batch::PreparedBatchVerifyingKey<'a, Bls12> {
        self.output
            .get_or_init(|| groth16::batch::PreparedBatchVerifyingKey::from(&self.output_vk.0))
    }
}

/// Batch validation context for Sapling.
///
/// This batch-validates Spend and Output proofs, and RedJubjub signatures.
///
/// Signatures are verified assuming ZIP 216 is active.
pub struct BatchValidator {
    bundles_added: bool,
    spend_proof_count: usize,
    output_proof_count: usize,
    spend_proofs: groth16::batch::Verifier<Bls12>,
    output_proofs: groth16::batch::Verifier<Bls12>,
    signatures: redjubjub::batch::Verifier,
}

impl Default for BatchValidator {
    fn default() -> Self {
        Self::new()
    }
}

impl BatchValidator {
    /// Constructs a new batch validation context.
    pub fn new() -> Self {
        BatchValidator {
            bundles_added: false,
            spend_proof_count: 0,
            output_proof_count: 0,
            spend_proofs: groth16::batch::Verifier::new(),
            output_proofs: groth16::batch::Verifier::new(),
            signatures: redjubjub::batch::Verifier::new(),
        }
    }

    /// Checks the bundle against Sapling-specific consensus rules, and adds its proof and
    /// signatures to the validator.
    ///
    /// Returns `false` if the bundle doesn't satisfy all of the consensus rules. This
    /// `BatchValidator` can continue to be used regardless, but some or all of the proofs
    /// and signatures from this bundle may have already been added to the batch even if
    /// it fails other consensus rules.
    pub fn check_bundle<V: Copy + Into<i64>>(
        &mut self,
        bundle: Bundle<Authorized, V>,
        sighash: [u8; 32],
    ) -> bool {
        self.bundles_added = true;

        let mut ctx = SaplingVerificationContextInner::new();

        for spend in bundle.shielded_spends() {
            // Deserialize the proof
            let zkproof = match groth16::Proof::read(&spend.zkproof()[..]) {
                Ok(p) => p,
                Err(_) => return false,
            };

            // Check the Spend consensus rules, and batch its proof and spend
            // authorization signature.
            let consensus_rules_passed = ctx.check_spend(
                spend.cv(),
                *spend.anchor(),
                &spend.nullifier().0,
                spend.rk(),
                zkproof,
                self,
                |this, rk| {
                    this.signatures
                        .queue(((*rk).into(), *spend.spend_auth_sig(), &sighash));
                    true
                },
                |this, proof, public_inputs| {
                    this.spend_proofs.queue((proof, public_inputs.to_vec()));
                    this.spend_proof_count += 1;
                    true
                },
            );
            if !consensus_rules_passed {
                return false;
            }
        }

        for output in bundle.shielded_outputs() {
            // Deserialize the ephemeral key
            let epk = match jubjub::ExtendedPoint::from_bytes(&output.ephemeral_key().0).into() {
                Some(p) => p,
                None => return false,
            };

            // Deserialize the proof
            let zkproof = match groth16::Proof::read(&output.zkproof()[..]) {
                Ok(p) => p,
                Err(_) => return false,
            };

            // Check the Output consensus rules, and batch its proof.
            let consensus_rules_passed = ctx.check_output(
                output.cv(),
                *output.cmu(),
                epk,
                zkproof,
                |proof, public_inputs| {
                    self.output_proofs.queue((proof, public_inputs.to_vec()));
                    self.output_proof_count += 1;
                    true
                },
            );
            if !consensus_rules_passed {
                return false;
            }
        }

        // Check the whole-bundle consensus rules, and batch the binding signature.
        ctx.final_check(*bundle.value_balance(), |bvk| {
            self.signatures
                .queue((bvk.into(), bundle.authorization().binding_sig, &sighash));
            true
        })
    }

    /// Batch-validates the accumulated bundles.
    ///
    /// Returns `true` if every proof and signature in every bundle added to the batch
    /// validator is valid, or `false` if one or more are invalid. No attempt is made to
    /// figure out which of the accumulated bundles might be invalid; if that information
    /// is desired, construct separate [`BatchValidator`]s for sub-batches of the bundles.
    pub fn validate<R: Rng + CryptoRng>(
        self,
        spend_vk: &SpendVerifyingKey,
        output_vk: &OutputVerifyingKey,
        mut rng: R,
    ) -> bool {
        if !self.bundles_added {
            // An empty batch is always valid, but is not free to run; skip it.
            return true;
        }

        if let Err(e) = self.signatures.verify(&mut rng) {
            #[cfg(feature = "std")]
            tracing::debug!("Signature batch validation failed: {}", e);
            #[cfg(not(feature = "std"))]
            tracing::debug!("Signature batch validation failed: {:?}", e);
            return false;
        }

        #[cfg(feature = "multicore")]
        let verify_proofs = |batch: groth16::batch::Verifier<Bls12>, vk| batch.verify_multicore(vk);

        #[cfg(not(feature = "multicore"))]
        let mut verify_proofs =
            |batch: groth16::batch::Verifier<Bls12>, vk| batch.verify(&mut rng, vk);

        if verify_proofs(self.spend_proofs, &spend_vk.0).is_err() {
            tracing::debug!("Spend proof batch validation failed");
            return false;
        }

        if verify_proofs(self.output_proofs, &output_vk.0).is_err() {
            tracing::debug!("Output proof batch validation failed");
            return false;
        }

        true
    }

    /// Batch-validates using keys prepared across multiple validators.
    ///
    /// As with [`BatchValidator::validate`], this returns `true` only when
    /// every queued proof and signature is valid. Preparation occurs after
    /// signature verification and only for proof types present in the batch.
    pub fn validate_prepared<R: Rng + CryptoRng>(
        self,
        keys: &PreparedBatchVerifyingKeys<'_>,
        mut rng: R,
    ) -> bool {
        if !self.bundles_added {
            return true;
        }

        if let Err(e) = self.signatures.verify(&mut rng) {
            #[cfg(feature = "std")]
            tracing::debug!("Signature batch validation failed: {}", e);
            #[cfg(not(feature = "std"))]
            tracing::debug!("Signature batch validation failed: {:?}", e);
            return false;
        }

        // The joint path wins for one Spend and one Output proof. Larger
        // batches can run faster through the parallel verifier.
        #[cfg(feature = "multicore")]
        let use_joint = self.spend_proof_count > 0
            && self.output_proof_count > 0
            && self.spend_proof_count <= MAX_JOINT_PROOFS_PER_KIND
            && self.output_proof_count <= MAX_JOINT_PROOFS_PER_KIND;
        #[cfg(not(feature = "multicore"))]
        let use_joint = self.spend_proof_count > 0 && self.output_proof_count > 0;

        if use_joint {
            if self
                .spend_proofs
                .verify_joint_prepared(self.output_proofs, &mut rng, keys.spend(), keys.output())
                .is_err()
            {
                tracing::debug!("Sapling proof batch validation failed");
                return false;
            }
            return true;
        }

        if self.spend_proof_count > 0 {
            #[cfg(feature = "multicore")]
            let result = self.spend_proofs.verify_multicore_prepared(keys.spend());
            #[cfg(not(feature = "multicore"))]
            let result = self.spend_proofs.verify_prepared(&mut rng, keys.spend());

            if result.is_err() {
                tracing::debug!("Spend proof batch validation failed");
                return false;
            }
        }

        if self.output_proof_count > 0 {
            #[cfg(feature = "multicore")]
            let result = self.output_proofs.verify_multicore_prepared(keys.output());
            #[cfg(not(feature = "multicore"))]
            let result = self.output_proofs.verify_prepared(&mut rng, keys.output());

            if result.is_err() {
                tracing::debug!("Output proof batch validation failed");
                return false;
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::super::{OUTPUT_PUBLIC_INPUT_COUNT, SPEND_PUBLIC_INPUT_COUNT};
    use super::{BatchValidator, PreparedBatchVerifyingKeys};
    use crate::circuit::{OutputVerifyingKey, SpendVerifyingKey};
    use alloc::vec::Vec;
    use bellman::{Circuit, ConstraintSystem, SynthesisError, groth16};
    use bls12_381::{Bls12, Scalar};
    use ff::Field;

    struct PublicInputs<const N: usize> {
        values: Option<[Scalar; N]>,
    }

    impl<const N: usize> Circuit<Scalar> for PublicInputs<N> {
        fn synthesize<CS: ConstraintSystem<Scalar>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let witness = cs.alloc(
                || "witness",
                || {
                    self.values
                        .map(|values| values[0])
                        .ok_or(SynthesisError::AssignmentMissing)
                },
            )?;

            for index in 0..N {
                let input = cs.alloc_input(
                    || format!("input {index}"),
                    || {
                        self.values
                            .map(|values| values[index])
                            .ok_or(SynthesisError::AssignmentMissing)
                    },
                )?;
                let source = if index == 0 { witness } else { input };
                cs.enforce(
                    || format!("input {index} is correct"),
                    |lc| lc + source,
                    |lc| lc + CS::one(),
                    |lc| lc + input,
                );
            }
            Ok(())
        }
    }

    fn proof<const N: usize>(
        rng: &mut impl rand_core::CryptoRng,
    ) -> (
        groth16::VerifyingKey<Bls12>,
        groth16::Proof<Bls12>,
        Vec<Scalar>,
    ) {
        let values: [Scalar; N] = core::array::from_fn(|_| Scalar::random(&mut *rng));
        let params = groth16::generate_random_parameters::<Bls12, _, _>(
            PublicInputs::<N> { values: None },
            &mut *rng,
        )
        .unwrap();
        let proof = groth16::create_random_proof(
            PublicInputs {
                values: Some(values),
            },
            &params,
            rng,
        )
        .unwrap();
        (params.vk, proof, values.to_vec())
    }

    fn validator(
        spend: Option<(&groth16::Proof<Bls12>, &[Scalar])>,
        output: Option<(&groth16::Proof<Bls12>, &[Scalar])>,
    ) -> BatchValidator {
        let mut validator = BatchValidator::new();
        validator.bundles_added = true;
        if let Some((proof, inputs)) = spend {
            validator
                .spend_proofs
                .queue((proof.clone(), inputs.to_vec()));
            validator.spend_proof_count = 1;
        }
        if let Some((proof, inputs)) = output {
            validator
                .output_proofs
                .queue((proof.clone(), inputs.to_vec()));
            validator.output_proof_count = 1;
        }
        validator
    }

    #[test]
    fn prepared_validation_reuses_only_needed_keys() {
        let mut rng = rand::rng();
        let (spend_vk, spend_proof, spend_inputs) = proof::<SPEND_PUBLIC_INPUT_COUNT>(&mut rng);
        let (output_vk, output_proof, output_inputs) = proof::<OUTPUT_PUBLIC_INPUT_COUNT>(&mut rng);
        let spend_vk = SpendVerifyingKey(spend_vk);
        let output_vk = OutputVerifyingKey(output_vk);
        let keys = PreparedBatchVerifyingKeys::new(&spend_vk, &output_vk);

        assert!(BatchValidator::new().validate_prepared(&keys, &mut rng));
        assert!(validator(None, None).validate_prepared(&keys, &mut rng));
        assert!(keys.spend.get().is_none());
        assert!(keys.output.get().is_none());

        let spend = Some((&spend_proof, spend_inputs.as_slice()));
        assert!(validator(spend, None).validate(&spend_vk, &output_vk, &mut rng));
        assert!(validator(spend, None).validate_prepared(&keys, &mut rng));
        assert!(keys.spend.get().is_some());
        assert!(keys.output.get().is_none());

        let output = Some((&output_proof, output_inputs.as_slice()));
        assert!(validator(None, output).validate(&spend_vk, &output_vk, &mut rng));
        assert!(validator(None, output).validate_prepared(&keys, &mut rng));
        assert!(keys.output.get().is_some());

        assert!(validator(spend, output).validate(&spend_vk, &output_vk, &mut rng));
        assert!(validator(spend, output).validate_prepared(&keys, &mut rng));

        let mut invalid_inputs = spend_inputs.clone();
        invalid_inputs[0] += Scalar::ONE;
        let invalid_spend = Some((&spend_proof, invalid_inputs.as_slice()));
        assert!(!validator(invalid_spend, output).validate_prepared(&keys, &mut rng));

        let mut invalid_inputs = output_inputs.clone();
        invalid_inputs[0] += Scalar::ONE;
        let invalid_output = Some((&output_proof, invalid_inputs.as_slice()));
        assert!(!validator(spend, invalid_output).validate_prepared(&keys, &mut rng));

        let mut large = validator(spend, output);
        for _ in 1..9 {
            large
                .spend_proofs
                .queue((spend_proof.clone(), spend_inputs.clone()));
            large
                .output_proofs
                .queue((output_proof.clone(), output_inputs.clone()));
        }
        large.spend_proof_count = 9;
        large.output_proof_count = 9;
        assert!(large.validate_prepared(&keys, &mut rng));
    }

    #[test]
    #[ignore = "release-mode performance measurement"]
    fn bench_joint_prepared_validation() {
        use std::{hint::black_box, time::Instant};

        let mut rng = rand::rng();
        let (spend_vk, spend_proof, spend_inputs) = proof::<SPEND_PUBLIC_INPUT_COUNT>(&mut rng);
        let (output_vk, output_proof, output_inputs) = proof::<OUTPUT_PUBLIC_INPUT_COUNT>(&mut rng);
        let spend_vk = SpendVerifyingKey(spend_vk);
        let output_vk = OutputVerifyingKey(output_vk);
        let keys = PreparedBatchVerifyingKeys::new(&spend_vk, &output_vk);
        let spend = (&spend_proof, spend_inputs.as_slice());
        let output = (&output_proof, output_inputs.as_slice());

        let make_validator = |count| {
            let mut validator = BatchValidator::new();
            validator.bundles_added = true;
            for _ in 0..count {
                validator
                    .spend_proofs
                    .queue((spend.0.clone(), spend.1.to_vec()));
                validator
                    .output_proofs
                    .queue((output.0.clone(), output.1.to_vec()));
            }
            validator.spend_proof_count = count;
            validator.output_proof_count = count;
            validator
        };

        // Warm key preparation and both verifier paths before measuring.
        assert!(make_validator(1).validate_prepared(&keys, &mut rng));

        for count in [1, 2, 8, 16] {
            let mut separate = Vec::with_capacity(40);
            let mut joint = Vec::with_capacity(40);
            for iteration in 0..40 {
                let measure_separate = |rng: &mut _, timings: &mut Vec<u128>| {
                    let validator = make_validator(count);
                    let start = Instant::now();
                    assert!(validator.signatures.verify(&mut *rng).is_ok());
                    #[cfg(feature = "multicore")]
                    {
                        assert!(
                            validator
                                .spend_proofs
                                .verify_multicore_prepared(keys.spend())
                                .is_ok()
                        );
                        assert!(
                            validator
                                .output_proofs
                                .verify_multicore_prepared(keys.output())
                                .is_ok()
                        );
                    }
                    #[cfg(not(feature = "multicore"))]
                    {
                        assert!(
                            validator
                                .spend_proofs
                                .verify_prepared(&mut *rng, keys.spend())
                                .is_ok()
                        );
                        assert!(
                            validator
                                .output_proofs
                                .verify_prepared(&mut *rng, keys.output())
                                .is_ok()
                        );
                    }
                    timings.push(black_box(start.elapsed().as_micros()));
                };
                let measure_joint = |rng: &mut _, timings: &mut Vec<u128>| {
                    let validator = make_validator(count);
                    let start = Instant::now();
                    assert!(black_box(validator.validate_prepared(&keys, rng)));
                    timings.push(black_box(start.elapsed().as_micros()));
                };
                if iteration % 2 == 0 {
                    measure_separate(&mut rng, &mut separate);
                    measure_joint(&mut rng, &mut joint);
                } else {
                    measure_joint(&mut rng, &mut joint);
                    measure_separate(&mut rng, &mut separate);
                }
            }
            separate.sort_unstable();
            joint.sort_unstable();
            std::println!(
                "{count}+{count}: separate {} us, joint {} us",
                separate[separate.len() / 2],
                joint[joint.len() / 2],
            );
        }
    }

    #[test]
    #[ignore = "release-mode performance measurement"]
    fn bench_repeated_prepared_validation() {
        use std::{hint::black_box, time::Instant};

        let mut rng = rand::rng();
        let (spend_vk, spend_proof, spend_inputs) = proof::<SPEND_PUBLIC_INPUT_COUNT>(&mut rng);
        let (output_vk, output_proof, output_inputs) = proof::<OUTPUT_PUBLIC_INPUT_COUNT>(&mut rng);
        let spend_vk = SpendVerifyingKey(spend_vk);
        let output_vk = OutputVerifyingKey(output_vk);
        let keys = PreparedBatchVerifyingKeys::new(&spend_vk, &output_vk);
        let spend = Some((&spend_proof, spend_inputs.as_slice()));
        let output = Some((&output_proof, output_inputs.as_slice()));

        // Warm both keys before timing repeated validations.
        assert!(validator(spend, output).validate_prepared(&keys, &mut rng));

        for (name, spend, output) in [
            ("Spend only", spend, None),
            ("Output only", None, output),
            ("Spend + Output", spend, output),
        ] {
            let mut raw = Vec::with_capacity(100);
            let mut prepared = Vec::with_capacity(100);
            for iteration in 0..100 {
                let measure_raw = |rng: &mut _, timings: &mut Vec<u128>| {
                    let start = Instant::now();
                    black_box(validator(spend, output).validate(&spend_vk, &output_vk, rng));
                    timings.push(start.elapsed().as_micros());
                };
                let measure_prepared = |rng: &mut _, timings: &mut Vec<u128>| {
                    let start = Instant::now();
                    black_box(validator(spend, output).validate_prepared(&keys, rng));
                    timings.push(start.elapsed().as_micros());
                };
                if iteration % 2 == 0 {
                    measure_raw(&mut rng, &mut raw);
                    measure_prepared(&mut rng, &mut prepared);
                } else {
                    measure_prepared(&mut rng, &mut prepared);
                    measure_raw(&mut rng, &mut raw);
                }
            }
            raw.sort_unstable();
            prepared.sort_unstable();
            std::println!(
                "{name}: raw median {} us, prepared median {} us",
                raw[raw.len() / 2],
                prepared[prepared.len() / 2],
            );
        }
    }
}
