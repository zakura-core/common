//! Host and test glue between Sensei policy and the artifact registry.

use crate::tuning::{self, OptionalPreparation, Preparation};
use sensei_artifacts::{ARTIFACTS, ArtifactId};

pub(crate) fn selected() -> Vec<ArtifactId> {
    if !cfg!(feature = "prover") {
        let mut selected = vec![ArtifactId::PrimitivePoints];
        if cfg!(feature = "verifier") {
            selected.extend([ArtifactId::SrsPoints, ArtifactId::VerifierCommitments]);
            if tuning::COMMITMENT_TABLES.embedded_entries() != 0 {
                selected.push(ArtifactId::CommitmentTables);
            }
        }
        return selected;
    }
    ARTIFACTS
        .iter()
        .filter(|artifact| match artifact.id {
            ArtifactId::CommitmentTables => tuning::COMMITMENT_TABLES.embedded_entries() != 0,
            ArtifactId::WindowTables => tuning::WINDOW_TABLES == Preparation::Embed,
            ArtifactId::FixedCoefficients => tuning::FIXED_COEFFICIENTS == Preparation::Embed,
            ArtifactId::SigmaCoefficients => tuning::SIGMA_COEFFICIENTS == Preparation::Embed,
            ArtifactId::FixedCosets => tuning::FIXED_COSETS == Preparation::Embed,
            ArtifactId::SigmaCosets => tuning::SIGMA_COSETS == Preparation::Embed,
            // Sensei generates its complete selector layout locally.
            ArtifactId::GateSelectors => false,
            ArtifactId::InstanceBases => tuning::INSTANCE_BASES == Preparation::Embed,
            ArtifactId::Boundaries => tuning::BOUNDARIES == Preparation::Embed,
            ArtifactId::FftTables => tuning::FFT_TABLES == OptionalPreparation::Embed,
            ArtifactId::ExpansionScales => tuning::EXPANSION_SCALES == OptionalPreparation::Embed,
            // Embedding the combined record would duplicate the two split sets.
            ArtifactId::Points => false,
            ArtifactId::PrimitivePoints
            | ArtifactId::SrsPoints
            | ArtifactId::VerifierCommitments
            | ArtifactId::FixedWindowXBases
            | ArtifactId::FixedWindowYBases
            | ArtifactId::FixedWindowUBases
            | ArtifactId::FixedTuples
            | ArtifactId::TupleAssignments
            | ArtifactId::SigmaMap => true,
        })
        .map(|artifact| artifact.id)
        .collect()
}
