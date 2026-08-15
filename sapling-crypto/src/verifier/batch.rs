use alloc::vec::Vec;

use bellman::{groth16, VerificationError};
use bls12_381::Bls12;
use group::Curve;
use rand_core::{CryptoRng, RngCore};

use super::SaplingVerificationContextInner;
use crate::{
    bundle::{Authorized, Bundle},
    circuit::{OutputVerifyingKey, SpendVerifyingKey},
};

/// Batch validation context for Sapling.
///
/// This batch-validates Spend and Output proofs, and RedJubjub signatures.
///
/// Signatures are verified assuming ZIP 216 is active.
pub struct BatchValidator {
    bundles_added: bool,
    spend_proofs: ProofBatch,
    output_proofs: ProofBatch,
    signatures: redjubjub::batch::Verifier,
}

type ProofBatch = Vec<groth16::batch::Item<Bls12>>;

fn verify_proofs<R: RngCore + CryptoRng>(
    proofs: ProofBatch,
    verifying_key: &groth16::VerifyingKey<Bls12>,
    prepared_verifying_key: &groth16::PreparedVerifyingKey<Bls12>,
    rng: &mut R,
) -> Result<(), VerificationError> {
    let proofs = match <[groth16::batch::Item<Bls12>; 1]>::try_from(proofs) {
        Ok([proof]) => return proof.verify_single(prepared_verifying_key),
        Err(proofs) => proofs,
    };

    let mut batch = groth16::batch::Verifier::new();
    for proof in proofs {
        batch.queue(proof);
    }

    #[cfg(feature = "multicore")]
    {
        let _ = rng;
        batch.verify_multicore(verifying_key)
    }

    #[cfg(not(feature = "multicore"))]
    batch.verify(rng, verifying_key)
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
            spend_proofs: Vec::new(),
            output_proofs: Vec::new(),
            signatures: redjubjub::batch::Verifier::new(),
        }
    }

    /// Checks the bundle against Sapling-specific consensus rules, and adds its
    /// proof and signatures to the validator.
    ///
    /// Returns `false` if the bundle doesn't satisfy all of the consensus
    /// rules. This `BatchValidator` can continue to be used regardless, but
    /// some or all of the proofs and signatures from this bundle may have
    /// already been added to the batch even if it fails other consensus rules.
    pub fn check_bundle<V: Copy + Into<i64>>(
        &mut self,
        bundle: Bundle<Authorized, V>,
        sighash: [u8; 32],
    ) -> bool {
        self.bundles_added = true;

        let mut ctx = SaplingVerificationContextInner::new();
        let point_count = bundle.shielded_spends().len() + bundle.shielded_outputs().len();

        // Batch the inversions needed to decode the randomized verification
        // keys and ephemeral keys. Avoid batch-allocation overhead when there
        // is only one point.
        let single_decoded_point;
        let decoded_points_storage;
        let decoded_points = if point_count == 1 {
            let encoding = if let Some(spend) = bundle.shielded_spends().first() {
                <[u8; 32]>::from(*spend.rk())
            } else if let Some(output) = bundle.shielded_outputs().first() {
                output.ephemeral_key().0
            } else {
                return false;
            };
            single_decoded_point = [jubjub::AffinePoint::from_bytes(encoding)];
            &single_decoded_point[..]
        } else {
            decoded_points_storage = jubjub::AffinePoint::batch_from_bytes(
                bundle
                    .shielded_spends()
                    .iter()
                    .map(|spend| <[u8; 32]>::from(*spend.rk()))
                    .chain(
                        bundle
                            .shielded_outputs()
                            .iter()
                            .map(|output| output.ephemeral_key().0),
                    ),
            );
            &decoded_points_storage
        };

        let (rks, epks) = decoded_points.split_at(bundle.shielded_spends().len());
        if decoded_points
            .iter()
            .any(|point| !bool::from(point.is_some()))
        {
            return false;
        }

        // Batch the inversions needed to obtain the affine value-commitment
        // coordinates used as public inputs. Again, avoid allocation overhead
        // for a single point.
        let single_value_commitment_affine;
        let value_commitments_affine_storage;
        let value_commitments_affine = if point_count == 1 {
            let value_commitment = if let Some(spend) = bundle.shielded_spends().first() {
                spend.cv().as_inner()
            } else if let Some(output) = bundle.shielded_outputs().first() {
                output.cv().as_inner()
            } else {
                return false;
            };
            single_value_commitment_affine = [value_commitment.to_affine()];
            &single_value_commitment_affine[..]
        } else {
            let value_commitments = bundle
                .shielded_spends()
                .iter()
                .map(|spend| *spend.cv().as_inner())
                .chain(
                    bundle
                        .shielded_outputs()
                        .iter()
                        .map(|output| *output.cv().as_inner()),
                )
                .collect::<Vec<_>>();
            let mut normalized = vec![jubjub::AffinePoint::identity(); value_commitments.len()];
            jubjub::ExtendedPoint::batch_normalize(&value_commitments, &mut normalized);
            value_commitments_affine_storage = normalized;
            &value_commitments_affine_storage
        };
        let (spend_cvs, output_cvs) =
            value_commitments_affine.split_at(bundle.shielded_spends().len());

        for ((spend, rk), cv) in bundle.shielded_spends().iter().zip(rks).zip(spend_cvs) {
            let Some(rk) = Option::from(*rk) else {
                return false;
            };

            // Deserialize the proof
            let zkproof = match groth16::Proof::read(&spend.zkproof()[..]) {
                Ok(p) => p,
                Err(_) => return false,
            };

            // Check the Spend consensus rules, and batch its proof and spend
            // authorization signature.
            let consensus_rules_passed = ctx.check_spend(
                spend.cv(),
                *cv,
                *spend.anchor(),
                &spend.nullifier().0,
                spend.rk(),
                rk,
                zkproof,
                self,
                |this, rk| {
                    this.signatures
                        .queue(((*rk).into(), *spend.spend_auth_sig(), &sighash));
                    true
                },
                |this, proof, public_inputs| {
                    this.spend_proofs
                        .push(groth16::batch::Item::from((proof, public_inputs.to_vec())));
                    true
                },
            );
            if !consensus_rules_passed {
                return false;
            }
        }

        for ((output, epk), cv) in bundle.shielded_outputs().iter().zip(epks).zip(output_cvs) {
            let Some(epk) = Option::from(*epk) else {
                return false;
            };

            // Deserialize the proof
            let zkproof = match groth16::Proof::read(&output.zkproof()[..]) {
                Ok(p) => p,
                Err(_) => return false,
            };

            // Check the Output consensus rules, and batch its proof.
            let consensus_rules_passed = ctx.check_output(
                output.cv(),
                *cv,
                *output.cmu(),
                epk,
                zkproof,
                |proof, public_inputs| {
                    self.output_proofs
                        .push(groth16::batch::Item::from((proof, public_inputs.to_vec())));
                    true
                },
            );
            if !consensus_rules_passed {
                return false;
            }
        }

        // Check the whole-bundle consensus rules, and batch the binding
        // signature.
        ctx.final_check(*bundle.value_balance(), |bvk| {
            self.signatures
                .queue((bvk.into(), bundle.authorization().binding_sig, &sighash));
            true
        })
    }

    /// Batch-validates the accumulated bundles.
    ///
    /// Returns `true` if every proof and signature in every bundle added to the
    /// batch validator is valid, or `false` if one or more are invalid. No
    /// attempt is made to figure out which of the accumulated bundles might be
    /// invalid; if that information is desired, construct separate
    /// [`BatchValidator`]s for sub-batches of the bundles.
    pub fn validate<R: RngCore + CryptoRng>(
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

        if verify_proofs(
            self.spend_proofs,
            spend_vk.batch_verifying_key(),
            spend_vk.prepared_verifying_key(),
            &mut rng,
        )
        .is_err()
        {
            tracing::debug!("Spend proof batch validation failed");
            return false;
        }

        if verify_proofs(
            self.output_proofs,
            output_vk.batch_verifying_key(),
            output_vk.prepared_verifying_key(),
            &mut rng,
        )
        .is_err()
        {
            tracing::debug!("Output proof batch validation failed");
            return false;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use alloc::{vec, vec::Vec};

    use bellman::{
        groth16::{self, Proof},
        Circuit, ConstraintSystem, SynthesisError,
    };
    use bls12_381::{Bls12, G1Affine, G2Affine, Scalar};
    use group::{Group, GroupEncoding};
    use rand_core::{OsRng, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use zcash_note_encryption::{EphemeralKeyBytes, ENC_CIPHERTEXT_SIZE, OUT_CIPHERTEXT_SIZE};

    use super::{verify_proofs, BatchValidator};
    use crate::{
        bundle::{Authorized, Bundle, GrothProofBytes, OutputDescription},
        note::ExtractedNoteCommitment,
        value::{NoteValue, ValueCommitTrapdoor, ValueCommitment},
    };

    const TEST_SIGHASH: [u8; 32] = [0; 32];

    struct MultiplicationCircuit {
        a: Option<Scalar>,
        b: Option<Scalar>,
    }

    impl Circuit<Scalar> for MultiplicationCircuit {
        fn synthesize<CS: ConstraintSystem<Scalar>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let product = cs.alloc_input(
                || "product",
                || {
                    self.a
                        .zip(self.b)
                        .map(|(a, b)| a * b)
                        .ok_or(SynthesisError::AssignmentMissing)
                },
            )?;

            cs.enforce(
                || "a * b = product",
                |lc| lc + a,
                |lc| lc + b,
                |lc| lc + product,
            );

            Ok(())
        }
    }

    fn bundle_with_epks(epks: Vec<[u8; 32]>) -> Bundle<Authorized, i64> {
        let mut rng = XorShiftRng::from_seed([0x5a; 16]);
        let mut proof = Vec::new();
        Proof::<Bls12> {
            a: G1Affine::generator(),
            b: G2Affine::generator(),
            c: G1Affine::generator(),
        }
        .write(&mut proof)
        .unwrap();
        let proof = GrothProofBytes::try_from(proof).unwrap();

        let outputs = epks
            .into_iter()
            .map(|epk| {
                OutputDescription::from_parts(
                    ValueCommitment::derive(
                        NoteValue::from_raw(1),
                        ValueCommitTrapdoor::random(&mut rng),
                    ),
                    ExtractedNoteCommitment::from_bytes(&Scalar::from(1).to_bytes()).unwrap(),
                    EphemeralKeyBytes::from(epk),
                    [0; ENC_CIPHERTEXT_SIZE],
                    [0; OUT_CIPHERTEXT_SIZE],
                    proof,
                )
            })
            .collect();

        Bundle::from_parts(
            vec![],
            outputs,
            0,
            Authorized {
                binding_sig: redjubjub::Signature::from([0; 64]),
            },
        )
        .unwrap()
    }

    #[test]
    fn batch_point_preparation_preserves_consensus_checks() {
        let valid_epk = jubjub::SubgroupPoint::generator().to_bytes();
        let identity_epk = jubjub::ExtendedPoint::identity().to_bytes();
        let mut noncanonical_identity_epk = identity_epk;
        noncanonical_identity_epk[31] |= 0x80;

        let mut validator = BatchValidator::new();
        assert!(validator.check_bundle(bundle_with_epks(vec![valid_epk]), TEST_SIGHASH));

        let mut validator = BatchValidator::new();
        assert!(validator.check_bundle(bundle_with_epks(vec![valid_epk, valid_epk]), TEST_SIGHASH));

        for epks in [
            vec![identity_epk],
            vec![noncanonical_identity_epk],
            vec![valid_epk, [0xff; 32]],
        ] {
            let mut validator = BatchValidator::new();
            assert!(!validator.check_bundle(bundle_with_epks(epks), TEST_SIGHASH));
        }
    }

    #[test]
    fn proof_verification_handles_single_and_batched_proofs() {
        let mut rng = OsRng;
        let parameters = groth16::generate_random_parameters::<Bls12, _, _>(
            MultiplicationCircuit { a: None, b: None },
            &mut rng,
        )
        .unwrap();
        let prepared_verifying_key = groth16::prepare_verifying_key(&parameters.vk);

        let a = Scalar::from(3);
        let b = Scalar::from(4);
        let product = a * b;
        let proof = groth16::create_random_proof(
            MultiplicationCircuit {
                a: Some(a),
                b: Some(b),
            },
            &parameters,
            &mut rng,
        )
        .unwrap();

        let item = |proof, public_input| groth16::batch::Item::from((proof, vec![public_input]));

        assert!(verify_proofs(
            vec![item(proof.clone(), product)],
            &parameters.vk,
            &prepared_verifying_key,
            &mut rng,
        )
        .is_ok());
        assert!(verify_proofs(
            vec![item(proof.clone(), product + Scalar::from(1))],
            &parameters.vk,
            &prepared_verifying_key,
            &mut rng,
        )
        .is_err());
        assert!(verify_proofs(
            vec![item(proof.clone(), product), item(proof, product)],
            &parameters.vk,
            &prepared_verifying_key,
            &mut rng,
        )
        .is_ok());
    }
}
