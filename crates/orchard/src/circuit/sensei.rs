//! Typed Orchard witnesses, statements, and keys backed by Sensei.
//!
//! Keys select embedded protocol material. Historical versions remain available
//! for verification; only the current version supports witness construction.

use crate::Proof;
#[cfg(feature = "prover")]
use crate::{
    Note,
    builder::SpendInfo,
    constants::MERKLE_DEPTH_ORCHARD,
    keys::{
        CommitIvkRandomness, DiversifiedTransmissionKey, NullifierDerivingKey, SpendValidatingKey,
    },
    note::{
        Rho,
        commitment::{NoteCommitTrapdoor, NoteCommitment},
    },
    spec::NonIdentityPallasPoint,
    tree::MerkleHashOrchard,
    value::{NoteValue, ValueCommitTrapdoor},
};
use alloc::string::String;
#[cfg(feature = "verifier")]
use alloc::vec::Vec;
#[cfg(feature = "prover")]
use rand::Rng;
#[cfg(feature = "prover")]
use sensei::primitives::pallas;

#[cfg(feature = "prover")]
use super::{CircuitError, UnsupportedCircuitVersion};
/// A proof request, witness, or verification failure from the native backend.
use super::{OrchardCircuitVersion, ProofError};

/// A typed witness for one current Orchard Action.
#[cfg(feature = "prover")]
#[derive(Clone, Debug)]
pub(crate) struct Circuit {
    pub(crate) path: [MerkleHashOrchard; MERKLE_DEPTH_ORCHARD],
    pub(crate) pos: u32,
    pub(crate) g_d_old: NonIdentityPallasPoint,
    pub(crate) pk_d_old: DiversifiedTransmissionKey,
    pub(crate) v_old: NoteValue,
    pub(crate) rho_old: Rho,
    pub(crate) psi_old: pallas::Base,
    pub(crate) rcm_old: NoteCommitTrapdoor,
    pub(crate) cm_old: NoteCommitment,
    pub(crate) alpha: crate::primitives::redpallas::SpendAuthRandomizer,
    pub(crate) ak: SpendValidatingKey,
    pub(crate) nk: NullifierDerivingKey,
    pub(crate) rivk: CommitIvkRandomness,
    pub(crate) g_d_new: NonIdentityPallasPoint,
    pub(crate) pk_d_new: DiversifiedTransmissionKey,
    pub(crate) v_new: NoteValue,
    pub(crate) psi_new: pallas::Base,
    pub(crate) rcm_new: NoteCommitTrapdoor,
    pub(crate) rcv: ValueCommitTrapdoor,
    pub(crate) circuit_version: OrchardCircuitVersion,
}

#[cfg(feature = "prover")]
impl Circuit {
    /// This constructor is public to enable creation of custom builders.
    /// If you are not creating a custom builder, use [`Builder`] to compose
    /// and authorize a transaction.
    ///
    /// Constructs a `Circuit` for the given `circuit_version` from the following components:
    /// - `spend`: [`SpendInfo`] of the note spent in scope of the action
    /// - `output_note`: a note created in scope of the action
    /// - `alpha`: a scalar used for randomization of the action spend validating key
    /// - `rcv`: trapdoor for the action value commitment
    ///
    /// Returns [`CircuitError::UnsupportedVersion`] for historical circuit versions, or
    /// [`CircuitError::RhoMismatch`] if the output's `rho` differs from the spent nullifier.
    ///
    /// [`SpendInfo`]: crate::builder::SpendInfo
    /// [`Builder`]: crate::builder::Builder
    pub(crate) fn from_action_context(
        spend: SpendInfo,
        output_note: Note,
        alpha: crate::primitives::redpallas::SpendAuthRandomizer,
        rcv: ValueCommitTrapdoor,
        circuit_version: OrchardCircuitVersion,
    ) -> Result<Circuit, CircuitError> {
        circuit_version
            .check_proving_support()
            .map_err(CircuitError::UnsupportedVersion)?;
        if Rho::from_nf_old(spend.note.nullifier(&spend.fvk)) != output_note.rho() {
            return Err(CircuitError::RhoMismatch);
        }
        Ok(Self::from_action_context_unchecked(
            spend,
            output_note,
            alpha,
            rcv,
        ))
    }

    pub(crate) fn from_action_context_unchecked(
        spend: SpendInfo,
        output_note: Note,
        alpha: crate::primitives::redpallas::SpendAuthRandomizer,
        rcv: ValueCommitTrapdoor,
    ) -> Circuit {
        let sender_address = spend.note.recipient();
        let rho_old = spend.note.rho();
        let psi_old = spend.note.psi();
        let rcm_old = spend.note.rcm();
        // Unwitnessed spends (a deferred-anchor bundle, ZIP 374) exist only in bundles
        // that refuse in-memory building, and no public constructor produces one, so a
        // spend that reaches circuit construction always carries its Merkle path.
        let merkle_path = spend
            .merkle_path
            .expect("a spend used as a circuit witness carries a Merkle path");

        let psi_new = output_note.psi();
        let rcm_new = output_note.rcm();

        Circuit {
            path: merkle_path.auth_path(),
            pos: merkle_path.position(),
            g_d_old: sender_address.g_d(),
            pk_d_old: *sender_address.pk_d(),
            v_old: spend.note.value(),
            rho_old,
            psi_old,
            rcm_old,
            cm_old: spend.note.commitment(),
            alpha,
            ak: spend.fvk.clone().into(),
            nk: *spend.fvk.nk(),
            rivk: spend.fvk.rivk(spend.scope),
            g_d_new: output_note.recipient().g_d(),
            pk_d_new: *output_note.recipient().pk_d(),
            v_new: output_note.value(),
            psi_new,
            rcm_new,
            rcv,
            circuit_version: OrchardCircuitVersion::PostNu6_3,
        }
    }
}
/// An Orchard verification key selecting immutable embedded protocol material.
#[derive(Debug)]
pub struct VerifyingKey {
    circuit_version: OrchardCircuitVersion,
}
impl VerifyingKey {
    /// Selects the verifying key for an explicit circuit version.
    pub fn build(circuit_version: OrchardCircuitVersion) -> Self {
        Self { circuit_version }
    }
    /// Returns the selected circuit version.
    pub fn circuit_version(&self) -> OrchardCircuitVersion {
        self.circuit_version
    }
    /// Whether this key enforces the cross-address restriction.
    pub fn supports_cross_address_restriction(&self) -> bool {
        self.circuit_version.supports_cross_address_restriction()
    }
    /// Returns the historical pinned key description with canonical LF line endings.
    pub(crate) fn pinned_description(&self) -> String {
        match self.circuit_version {
            OrchardCircuitVersion::InsecurePreNu6_2 => {
                include_str!("../circuit_data/circuit_description_insecure")
            }
            OrchardCircuitVersion::FixedPostNu6_2 => {
                include_str!("../circuit_data/circuit_description_fixed")
            }
            OrchardCircuitVersion::PostNu6_3 => {
                include_str!("../circuit_data/circuit_description_post_nu6_3")
            }
        }
        .replace("\r\n", "\n")
    }
    /// BLAKE2b-256 of the pinned description, personalized with `Orchard-VkFprint`.
    pub fn fingerprint(&self) -> [u8; 32] {
        const PERSONALIZATION: &[u8] = b"Orchard-VkFprint";
        blake2b_simd::Params::new()
            .hash_length(32)
            .personal(PERSONALIZATION)
            .hash(self.pinned_description().as_bytes())
            .as_bytes()
            .try_into()
            .unwrap()
    }
    /// Eagerly prepares Sensei's shared verification state.
    #[cfg(feature = "verifier")]
    pub fn prepare_batch_validation(&self) -> bool {
        sensei::warm_up_verifier();
        true
    }
}

/// The current Orchard proving key, selecting Sensei's embedded circuit material.
#[cfg(feature = "prover")]
#[derive(Debug)]
pub struct ProvingKey {
    circuit_version: OrchardCircuitVersion,
}
#[cfg(feature = "prover")]
impl ProvingKey {
    /// Selects a proving key; historical versions cannot construct proofs.
    pub fn build(
        circuit_version: OrchardCircuitVersion,
    ) -> Result<Self, UnsupportedCircuitVersion> {
        circuit_version.check_proving_support()?;
        Ok(Self { circuit_version })
    }
    /// Eagerly prepares Sensei's shared proving state.
    pub fn prepare_proving(&self) -> bool {
        sensei::warm_up_prover();
        true
    }
    /// Returns the matching verification key without initializing verification.
    pub fn verifying_key(&self) -> VerifyingKey {
        VerifyingKey::build(self.circuit_version)
    }
    /// Returns the selected circuit version.
    pub fn circuit_version(&self) -> OrchardCircuitVersion {
        self.circuit_version
    }
    /// Whether this key enforces the cross-address restriction.
    pub fn supports_cross_address_restriction(&self) -> bool {
        self.circuit_version.supports_cross_address_restriction()
    }
}

use super::Instance;
impl Instance {
    /// Encodes each instance as a Sensei public statement.
    ///
    /// `rk` is already held in affine form; the projective `cv_net` points are
    /// normalized together with one shared inversion.
    pub(crate) fn natives(instances: &[Self]) -> Vec<sensei::PublicStatement> {
        let cv_nets: Vec<pallas::Point> = instances.iter().map(|i| i.cv_net.point()).collect();
        let mut affine = alloc::vec![pallas::Affine::default(); cv_nets.len()];
        pallas::Point::batch_normalize(&cv_nets, &mut affine);
        instances
            .iter()
            .zip(affine)
            .map(|(i, cv_net)| sensei::PublicStatement {
                anchor: i.anchor.inner(),
                // An identity cv_net is encoded as (0, 0).
                cv_net: cv_net.raw_coordinates(),
                nf_old: i.nf_old.inner(),
                rk: i.rk.native().raw_coordinates(),
                cmx: i.cmx.inner(),
                enable_spend: i.enable_spend,
                enable_output: i.enable_output,
                disable_cross_address: i.cross_address_disabled,
            })
            .collect()
    }
}

#[cfg(feature = "prover")]
impl Circuit {
    fn native(&self) -> sensei::PrivateWitness {
        fn point(p: NonIdentityPallasPoint) -> sensei::NonIdentityPallasPoint {
            sensei::NonIdentityPallasPoint::from_native(
                *p.native()
                    .to_point()
                    .as_affine()
                    .expect("nonidentity witness point"),
            )
        }
        sensei::PrivateWitness {
            path: self.path.map(|node| node.inner()),
            position: self.pos,
            g_d_old: point(self.g_d_old),
            pk_d_old: point(self.pk_d_old.inner()),
            v_old: self.v_old.inner(),
            rho_old: self.rho_old.into_inner(),
            psi_old: self.psi_old,
            rcm_old: self.rcm_old.inner(),
            cm_old: self.cm_old.inner().to_affine(),
            alpha: self.alpha.scalar(),
            ak: self.ak.native(),
            nk: self.nk.inner(),
            rivk: self.rivk.inner(),
            g_d_new: point(self.g_d_new),
            pk_d_new: point(self.pk_d_new.inner()),
            v_new: self.v_new.inner(),
            psi_new: self.psi_new,
            rcm_new: self.rcm_new.inner(),
            rcv: self.rcv.inner(),
        }
    }
}

/// Classifies a failure of the Sensei prover.
///
/// [`Proof::create`] rejects malformed request shapes before reaching the backend, but
/// unlike Halo2 the Sensei prover checks the witness itself, so a statement the witness
/// does not prove is a caller-input failure rather than a backend fault. The randomness
/// source never fails (`impl Rng` is infallible) and a randomness retry is performed
/// before classification, so the randomness variants indicate an internal fault here.
#[cfg(feature = "prover")]
fn prover_error(error: sensei::Error) -> ProofError {
    match error {
        sensei::Error::InvalidInput
        | sensei::Error::InvalidStatement
        | sensei::Error::UnsatisfiedWitness => ProofError::InvalidInput,
        sensei::Error::InvalidProof
        | sensei::Error::RngFailure
        | sensei::Error::RetryRandomness
        | sensei::Error::InternalInvariant => ProofError::InternalInvariant,
    }
}

/// Classifies a failure of the Sensei verifier.
///
/// Request validation rejects statement shapes the selected key cannot attest to as the
/// caller's input. Malformed transcript contents and a failed verification equation are
/// the ways a proof fails to verify. A singleton verification draws no batch weights, so
/// the randomness variants — like the prover-only witness checks — indicate an internal
/// fault here.
#[cfg(feature = "verifier")]
fn verifier_error(error: sensei::Error) -> ProofError {
    match error {
        sensei::Error::InvalidInput | sensei::Error::InvalidStatement => ProofError::InvalidInput,
        sensei::Error::InvalidProof => ProofError::InvalidProof,
        sensei::Error::UnsatisfiedWitness
        | sensei::Error::RngFailure
        | sensei::Error::RetryRandomness
        | sensei::Error::InternalInvariant => ProofError::InternalInvariant,
    }
}

impl Proof {
    /// Bare proof verification historically consumes a prefix. Bundle constructors enforce
    /// modern canonical lengths; preserve the original bytes for serialization and hashing.
    pub(crate) fn verification_bytes(&self, actions: usize) -> Result<&[u8], ProofError> {
        self.0
            .get(..Self::expected_proof_size(actions))
            .ok_or(ProofError::InvalidProof)
    }

    /// Proves current Orchard Actions using native witnesses and statements.
    /// Counts must match and the witness versions must match the proving key.
    #[cfg(feature = "prover")]
    pub(crate) fn create(
        pk: &ProvingKey,
        circuits: &[Circuit],
        instances: &[Instance],
        mut rng: impl Rng,
    ) -> Result<Self, ProofError> {
        if circuits.is_empty()
            || circuits.len() != instances.len()
            || circuits
                .iter()
                .any(|c| c.circuit_version != pk.circuit_version)
        {
            return Err(ProofError::InvalidInput);
        }
        let actions = circuits
            .iter()
            .zip(Instance::natives(instances))
            .map(|(c, statement)| sensei::Action {
                statement,
                witness: c.native(),
            })
            .collect();
        let request = sensei::ProvingRequest::new(actions).map_err(prover_error)?;
        // A negligible random event requests one retry with fresh draws; classification
        // reports a second occurrence as a backend fault.
        let mut proof = sensei::create_proof(&request, &mut || Ok(rng.next_u64()));
        if matches!(proof, Err(sensei::Error::RetryRandomness)) {
            proof = sensei::create_proof(&request, &mut || Ok(rng.next_u64()));
        }
        proof.map(Proof).map_err(prover_error)
    }

    /// Verifies a proof for the selected protocol version and ordered statements.
    ///
    /// Verification reads the canonical proof from the front of the bytes and ignores
    /// anything after it. Callers verifying proofs obtained as raw bytes must first check
    /// the length against [`Proof::expected_proof_size`]. [`Bundle::try_from_parts`] does
    /// so for every bundle version except the historical pre-NU6.2 pool, so proofs taken
    /// from an authorized bundle need no separate check.
    ///
    /// # Errors
    ///
    /// Returns [`ProofError::InvalidInput`] if `instances` is empty, or if any instance
    /// disables cross-address transfers and `vk` is not an
    /// [`OrchardCircuitVersion::PostNu6_3`] verifying key.
    ///
    /// Returns [`ProofError::InvalidProof`] if the proof does not verify for `instances`,
    /// including when its encoding is truncated or corrupted.
    ///
    /// Returns [`ProofError::InternalInvariant`] if the backend fails an internal check.
    ///
    /// [`Bundle::try_from_parts`]: crate::Bundle::try_from_parts
    #[cfg(feature = "verifier")]
    pub fn verify(&self, vk: &VerifyingKey, instances: &[Instance]) -> Result<(), ProofError> {
        if instances.is_empty() {
            return Err(ProofError::InvalidInput);
        }
        let statements = Instance::natives(instances);
        let request = sensei::VerificationRequest::new(
            vk.circuit_version.native(),
            &statements,
            self.verification_bytes(instances.len())?,
        )
        .map_err(verifier_error)?;
        // A singleton verification uses no random batch weight.
        sensei::verify_proofs(&[request], &mut || Err(sensei::RandomnessError))
            .map_err(verifier_error)
    }
}

#[cfg(all(test, feature = "prover", feature = "verifier"))]
mod classification_tests {
    use super::{ProofError, prover_error, verifier_error};

    /// A backend error and the classes the prover and verifier adapters must assign it.
    #[test]
    fn backend_errors_classify_per_operation() {
        type Case = (sensei::Error, ProofError, ProofError);
        let table: &[Case] = &[
            (
                sensei::Error::InvalidInput,
                ProofError::InvalidInput,
                ProofError::InvalidInput,
            ),
            (
                sensei::Error::InvalidStatement,
                ProofError::InvalidInput,
                ProofError::InvalidInput,
            ),
            (
                sensei::Error::UnsatisfiedWitness,
                ProofError::InvalidInput,
                ProofError::InternalInvariant,
            ),
            (
                sensei::Error::InvalidProof,
                ProofError::InternalInvariant,
                ProofError::InvalidProof,
            ),
            (
                sensei::Error::RngFailure,
                ProofError::InternalInvariant,
                ProofError::InternalInvariant,
            ),
            (
                sensei::Error::RetryRandomness,
                ProofError::InternalInvariant,
                ProofError::InternalInvariant,
            ),
            (
                sensei::Error::InternalInvariant,
                ProofError::InternalInvariant,
                ProofError::InternalInvariant,
            ),
        ];
        for &(error, as_prover, as_verifier) in table {
            assert_eq!(prover_error(error), as_prover, "{error:?}");
            assert_eq!(verifier_error(error), as_verifier, "{error:?}");
        }
    }
}

#[cfg(test)]
mod instance_tests {
    use super::Instance;
    use crate::{
        bundle::Flags,
        note::{ExtractedNoteCommitment, Nullifier},
        primitives::redpallas::VerificationKey,
        rng_compat::OsRng,
        tree::Anchor,
        value::{ValueCommitTrapdoor, ValueCommitment, ValueSum},
    };
    use alloc::vec::Vec;

    #[test]
    fn batched_statements_match_per_instance_encoding() {
        let mut rng = OsRng;
        let identity = ValueCommitment::derive(ValueSum::zero(), ValueCommitTrapdoor::zero());
        assert_eq!(identity.to_bytes(), [0; 32]);
        // Place an identity cv_net first (where the running product starts), in the
        // middle, and last.
        let instances: Vec<Instance> = (0..20)
            .map(|i| {
                let cv_net = if [0, 7, 19].contains(&i) {
                    identity.clone()
                } else {
                    ValueCommitment::derive(
                        ValueSum::from_raw(i64::from(i) * 1_000 - 5_000),
                        ValueCommitTrapdoor::random(&mut rng),
                    )
                };
                Instance::from_parts(
                    Anchor::from_bytes([0; 32]).unwrap(),
                    cv_net,
                    Nullifier::dummy(&mut rng),
                    VerificationKey::dummy(),
                    ExtractedNoteCommitment::from_bytes(&[0; 32]).unwrap(),
                    Flags::ENABLED,
                )
                .unwrap()
            })
            .collect();

        assert!(Instance::natives(&[]).is_empty());
        for len in 0..=instances.len() {
            let statements = Instance::natives(&instances[..len]);
            assert_eq!(statements.len(), len);
            for (instance, statement) in instances.iter().zip(&statements) {
                assert_eq!(statement.cv_net, (instance.cv_net.x(), instance.cv_net.y()));
                assert_eq!(statement.rk, instance.rk.native().raw_coordinates());
                assert_eq!(statement.anchor, instance.anchor.inner());
                assert_eq!(statement.nf_old, instance.nf_old.inner());
                assert_eq!(statement.cmx, instance.cmx.inner());
            }
        }
    }
}
