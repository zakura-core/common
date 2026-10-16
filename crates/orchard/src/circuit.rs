//! Orchard proof statements, protocol versions, and opaque proving and verifying keys.
//!
//! Circuit synthesis is private. Use the builder or PCZT APIs to produce proofs.
//!
//! ```compile_fail
//! use orchard::circuit::{Circuit, Config};
//! ```

mod halo2;

use halo2 as selected;

pub use crate::Proof;
#[cfg(feature = "prover")]
pub(crate) use selected::Circuit;
#[cfg(feature = "prover")]
pub use selected::ProvingKey;
pub use selected::VerifyingKey;

/// Selects which version of the Orchard Action circuit to build.
///
/// [`FixedPostNu6_2`] and [`InsecurePreNu6_2`] produce different verifying keys: the fixed
/// circuit anchors the variable-base scalar-multiplication base, while
/// the pre-NU6.2 one does not. [`PostNu6_3`] extends the fixed circuit by enforcing the
/// same-address check, i.e. `(g_d^old, pk_d^old) = (g_d^new, pk_d^new)`, when the
/// boolean `disableCrossAddress` public input is set.
///
/// This is a runtime value rather than a type parameter, chosen when building a
/// `ProvingKey` or [`VerifyingKey`], so the circuit version can be
/// threaded dynamically (e.g. across an FFI boundary).
///
/// Historical versions are retained for verifying the block chain from NU5 activation.
/// Only `PostNu6_3` supports proving, including in tests.
///
/// [`FixedPostNu6_2`]: OrchardCircuitVersion::FixedPostNu6_2
/// [`InsecurePreNu6_2`]: OrchardCircuitVersion::InsecurePreNu6_2
/// [`PostNu6_3`]: OrchardCircuitVersion::PostNu6_3
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OrchardCircuitVersion {
    /// The insecure pre-NU6.2 circuit, in which the variable-base scalar-multiplication base
    /// is not anchored to the real base. For reconstructing the historical (NU5..NU6.2)
    /// verifying key only — never for proving or current verification.
    InsecurePreNu6_2,
    /// The fixed circuit used between NU6.2 and NU6.3, retained for historical verification.
    FixedPostNu6_2,
    /// The post-NU 6.3 circuit. This uses the fixed circuit with additional constraints
    /// enforcing the `disableCrossAddress` public input.
    PostNu6_3,
}

impl OrchardCircuitVersion {
    /// Returns whether this version supports constructing witnesses and proving keys.
    pub fn supports_proving(self) -> bool {
        matches!(self, Self::PostNu6_3)
    }

    /// Returns an error if this version cannot construct witnesses or proving keys.
    pub fn check_proving_support(self) -> Result<(), UnsupportedCircuitVersion> {
        if self.supports_proving() {
            Ok(())
        } else {
            Err(UnsupportedCircuitVersion(self))
        }
    }

    /// Whether this circuit version enforces the `disableCrossAddress` public input.
    ///
    /// Statements with `disableCrossAddress = 1` can be proven and verified only with
    /// keys for a circuit version that constrains the flag. [`PostNu6_3`] constrains it;
    /// older circuit versions leave it unconstrained, so they cannot enforce — and must
    /// not be asked to attest to — the restriction.
    ///
    /// [`PostNu6_3`]: OrchardCircuitVersion::PostNu6_3
    pub fn supports_cross_address_restriction(self) -> bool {
        match self {
            OrchardCircuitVersion::InsecurePreNu6_2 | OrchardCircuitVersion::FixedPostNu6_2 => {
                false
            }
            OrchardCircuitVersion::PostNu6_3 => true,
        }
    }
}

/// A historical circuit version for which proving is no longer supported.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnsupportedCircuitVersion(OrchardCircuitVersion);

impl UnsupportedCircuitVersion {
    /// The rejected circuit version.
    pub fn circuit_version(self) -> OrchardCircuitVersion {
        self.0
    }
}

impl core::fmt::Display for UnsupportedCircuitVersion {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Orchard proving is not supported for {:?}", self.0)
    }
}

impl core::error::Error for UnsupportedCircuitVersion {}

/// An error constructing an Orchard Action witness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum CircuitError {
    /// The selected historical circuit does not support witness construction.
    UnsupportedVersion(UnsupportedCircuitVersion),
    /// The output note's `rho` does not match the spent note's nullifier.
    RhoMismatch,
}

impl core::fmt::Display for CircuitError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnsupportedVersion(e) => e.fmt(f),
            Self::RhoMismatch => {
                f.write_str("output rho does not match the spent note's nullifier")
            }
        }
    }
}

impl core::error::Error for CircuitError {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::UnsupportedVersion(e) => Some(e),
            Self::RhoMismatch => None,
        }
    }
}

use core::fmt;

/// An error returned while preparing, creating, or verifying an Orchard proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum ProofError {
    /// The request has an unsupported shape or contains an invalid encoding.
    InvalidInput,
    /// The public statement does not agree with the private witness.
    InvalidStatement,
    /// The private witness does not satisfy the Ironwood Action circuit.
    UnsatisfiedWitness,
    /// The proof does not verify for the supplied statements.
    InvalidProof,
    /// The caller-supplied randomness source failed.
    RngFailure,
    /// A negligible random event requires retrying with fresh randomness.
    RetryRandomness,
    /// The selected backend encountered an unexpected internal failure.
    InternalInvariant,
}

impl fmt::Display for ProofError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::InvalidInput => "invalid proof input",
            Self::InvalidStatement => "public statement does not match the witness",
            Self::UnsatisfiedWitness => "witness does not satisfy the fixed circuit",
            Self::InvalidProof => "invalid proof",
            Self::RngFailure => "randomness source failed",
            Self::RetryRandomness => "fresh randomness is required",
            Self::InternalInvariant => "internal proof invariant failed",
        })
    }
}

impl core::error::Error for ProofError {}

impl ProofError {
    fn from_backend(error: crate::backend::halo2_proofs::plonk::Error) -> Self {
        use crate::backend::halo2_proofs::plonk::Error;
        match error {
            Error::InvalidInstances => Self::InvalidInput,
            Error::Synthesis => Self::UnsatisfiedWitness,
            _ => Self::InvalidProof,
        }
    }
}

use crate::{
    Anchor,
    bundle::Flags,
    note::{ExtractedNoteCommitment, Nullifier},
    primitives::redpallas::{SpendAuth, VerificationKey},
    value::ValueCommitment,
};
/// Public inputs to the Orchard Action circuit.
///
/// # Invariants
///
/// Every `Instance` has a non-identity `rk`.
#[derive(Clone, Debug)]
pub struct Instance {
    anchor: Anchor,
    cv_net: ValueCommitment,
    nf_old: Nullifier,
    rk: VerificationKey<SpendAuth>,
    cmx: ExtractedNoteCommitment,
    enable_spend: bool,
    enable_output: bool,
    cross_address_disabled: bool,
}

impl Instance {
    /// Constructs an [`Instance`] from its constituent parts.
    ///
    /// This API can be used in combination with `Proof::verify` to build verification
    /// pipelines for many proofs, where you don't want to pass around the full bundle.
    /// Use `Bundle::verify_proof` instead if you have the full bundle.
    ///
    /// The provided [`Flags`] are encoded into the spend/output enable public inputs and
    /// the `disableCrossAddress` public input, which is set to the negation of
    /// [`Flags::cross_address_enabled`]. If cross-address transfers are disabled,
    /// callers must use a proving or verifying key whose circuit version supports the
    /// cross-address restriction. Bundle and PCZT proving, `Proof::verify`, and
    /// `crate::bundle::BatchValidator` enforce this.
    ///
    /// Returns `None` if `rk` is the identity Pallas point.
    /// zcashd v6.12.1 and Zebra 4.3.1 both added a consensus rule rejecting
    /// transactions whose Orchard actions have an identity `rk`; the Zcash
    /// protocol specification will be updated to match, and this crate
    /// aligns with that rule.
    ///
    /// See:
    /// - <https://zodl.com/zcashd-zebra-april-2026-disclosure/>
    /// - <https://zfnd.org/zebra-4-3-1-critical-security-fixes-dockerized-mining-and-ci-hardening/>
    ///
    pub fn from_parts(
        anchor: Anchor,
        cv_net: ValueCommitment,
        nf_old: Nullifier,
        rk: VerificationKey<SpendAuth>,
        cmx: ExtractedNoteCommitment,
        flags: Flags,
    ) -> Option<Self> {
        (!rk.is_identity()).then_some(Instance {
            anchor,
            cv_net,
            nf_old,
            rk,
            cmx,
            enable_spend: flags.spends_enabled(),
            enable_output: flags.outputs_enabled(),
            cross_address_disabled: !flags.cross_address_enabled(),
        })
    }

    /// Returns the Merkle tree anchor of this instance.
    pub(crate) fn anchor(&self) -> &Anchor {
        &self.anchor
    }

    /// Returns the commitment to the net value of this instance.
    pub(crate) fn cv_net(&self) -> &ValueCommitment {
        &self.cv_net
    }

    /// Returns the nullifier of the note being spent by this instance.
    pub(crate) fn nf_old(&self) -> &Nullifier {
        &self.nf_old
    }

    /// Returns the randomized verification key of this instance.
    pub(crate) fn rk(&self) -> &VerificationKey<SpendAuth> {
        &self.rk
    }

    /// Returns the commitment to the new note being created by this instance.
    pub(crate) fn cmx(&self) -> &ExtractedNoteCommitment {
        &self.cmx
    }

    /// Returns whether the spend is enabled for this instance.
    pub(crate) fn enable_spend(&self) -> bool {
        self.enable_spend
    }

    /// Returns whether the output is enabled for this instance.
    pub(crate) fn enable_output(&self) -> bool {
        self.enable_output
    }

    /// Returns whether cross-address transfers are disabled for this instance.
    pub(crate) fn cross_address_disabled(&self) -> bool {
        self.cross_address_disabled
    }
}
