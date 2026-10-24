//! Artifact names, encoders, stored forms, and typed identifiers.
//!
//! This ordered inventory drives registry-based build emission, consumer paths
//! and cfgs, and the determinism tests. Keep disabled artifacts registered: the
//! tests exercise their encoders under the default commitment-table policy even
//! when Sensei derives those values at load. Sensei's build script also produces
//! complete selector rows outside this registry; see [`ArtifactId::GateSelectors`].

use crate::{
    Error, RawStore,
    context::Context,
    fixed_base_tables, fixed_columns,
    points::{self, window_bases},
    polynomials::{basis, coefficients, cosets, selectors},
    raw::permutation,
};

/// A deterministic artifact generator using the raw inputs, circuit recipes,
/// registry entry's stored form, and default commitment-table policy.
///
/// Source-only artifacts accept the same argument but do not read it. Encoders
/// construct and serialize their own values; they do not write output files.
/// The default policy is [`sensei_shared::commitment_tables::DEFAULT`]; use
/// [`crate::emit_generated_with_commitment_tables`] for a configured policy.
pub type Generator = fn(&RawStore) -> Result<Vec<u8>, Error>;

/// Artifact identities independent of file names and embedding policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArtifactId {
    /// Optional affine commitment acceleration tables. Contents depend on the
    /// commitment-table policy; the default policy produces an empty payload.
    CommitmentTables,
    /// Combined SRS and primitive points in [`sensei_shared::PreparedPointsFile`].
    Points,
    /// Sinsemilla generators in [`sensei_shared::PrimitivePointsFile`].
    PrimitivePoints,
    /// Proof commitment generators in [`sensei_shared::SrsPointsFile`].
    SrsPoints,
    /// Deduplicated fixed/permutation commitments and mappings for all three keys.
    VerifierCommitments,
    /// The `fixed-coefficients` artifact.
    FixedCoefficients,
    /// The `sigma-coefficients` artifact.
    SigmaCoefficients,
    /// The `fixed-cosets` artifact.
    FixedCosets,
    /// The `sigma-cosets` artifact.
    SigmaCosets,
    /// The shared 41-element selector row for every extended-coset row, in
    /// [`sensei_shared::selectors::prepare_gate_selectors`] order.
    ///
    /// Sensei's `artifact_selection.rs` excludes this registered artifact.
    /// When complete selectors are embedded, Sensei's `build.rs` separately
    /// generates 50-element rows as `gate-selectors-complete.<stored-form>.pod`
    /// and adds that file to `artifact-manifest.json`. The consumer in
    /// `native/target/mod.rs` uses a direct `OUT_DIR` path, separate from the
    /// registry's generated `artifact_path!(gate_selectors)` arm.
    GateSelectors,
    /// The `window-tables` artifact.
    WindowTables,
    /// The `instance-bases` artifact.
    InstanceBases,
    /// The `boundaries` artifact.
    Boundaries,
    /// The `fixed-window-x-bases` artifact.
    FixedWindowXBases,
    /// The `fixed-window-y-bases` artifact.
    FixedWindowYBases,
    /// The `fixed-window-u-bases` artifact.
    FixedWindowUBases,
    /// The `fixed-tuples` artifact.
    FixedTuples,
    /// The `tuple-assignments.pod` artifact.
    TupleAssignments,
    /// The `sigma-map.pod` artifact.
    SigmaMap,
    /// Prepared FFT twiddles and inverse finish scales.
    FftTables,
    /// Prepared residue expansion scales.
    ExpansionScales,
}

/// Preparation layer associated with an artifact.
///
/// This classification describes which consumers can use the data. It does not
/// enable artifacts, select Cargo features, or enforce dependency isolation.
/// See [`ArtifactId::domain`] for the assignment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArtifactDomain {
    /// Reusable cryptographic primitive data, with no SRS dependency.
    Primitives,
    /// Commitment-system preparation shared by proof roles.
    Srs,
    /// Circuit preparation and combined records that span layers.
    Circuit,
}

impl ArtifactId {
    /// Identifies which preparation layer owns this artifact.
    ///
    /// [`Self::Points`] combines primitive and SRS data and is classified as
    /// [`ArtifactDomain::Circuit`]. Use [`Self::PrimitivePoints`] or
    /// [`Self::SrsPoints`] to prepare those sets independently.
    pub const fn domain(self) -> ArtifactDomain {
        match self {
            Self::PrimitivePoints => ArtifactDomain::Primitives,
            Self::SrsPoints | Self::CommitmentTables => ArtifactDomain::Srs,
            _ => ArtifactDomain::Circuit,
        }
    }
}

/// One registered artifact the pipeline can generate into `OUT_DIR`.
pub struct Artifact {
    /// Base name under `OUT_DIR`. Field-element-bearing artifacts append
    /// their stored form's descriptor — the full name is
    /// [`Artifact::file_name`] — while representation-invariant entries use
    /// the stem (extension included) verbatim.
    pub stem: &'static str,
    /// The stored form this entry's generator encodes, or `None` for
    /// representation-invariant integer artifacts.
    pub form: Option<&'static str>,
    /// The generator producing the artifact's bytes under the default
    /// commitment-table policy; see [`Generator`].
    pub generate: Generator,
    /// Typed identifier used by consumers to select emitted artifacts.
    pub id: ArtifactId,
    /// The consumer's embedding `cfg` token, or `None` for canonical inputs.
    pub cfg: Option<&'static str>,
    /// One-line description of the artifact's role.
    pub doc: &'static str,
}

impl Artifact {
    /// The artifact's file name under `OUT_DIR`: descriptor-suffixed
    /// (`{stem}.{descriptor}.pod`) for field-bearing artifacts, the plain
    /// stem otherwise.
    pub fn file_name(&self) -> String {
        match self.form {
            Some(form) => format!("{}.{}.pod", self.stem, form),
            None => self.stem.to_owned(),
        }
    }

    /// The artifact's identifier in the generated `artifact_path!` macro:
    /// the stem without its extension, hyphens as underscores
    /// (`fixed-coefficients` → `fixed_coefficients`,
    /// `tuple-assignments.pod` → `tuple_assignments`).
    pub fn ident(&self) -> String {
        let stem = self.stem.split('.').next().unwrap_or(self.stem);
        stem.replace('-', "_")
    }
}

type ContextEncoder = fn(&Context<'_>) -> Result<Vec<u8>, Error>;

// Keep standalone wrappers and context-aware emission in the same inventory.
// The public function-pointer API still creates independent preparations.
macro_rules! artifacts {
    ($(Artifact {
        stem: $stem:expr,
        form: $form:expr,
        generate: $generate:path,
        $($field:ident: $value:expr,)*
    },)*) => {
        /// The artifact encoders provided by this crate, keyed by (artifact,
        /// stored form). Field-bearing entries encode [`udon::STORED_FORM`]
        /// using the concrete Udon types in the shared records. Names do not
        /// encode the commitment-table policy, which can change payload bytes.
        ///
        /// Emission and path rendering walk this slice in order. Sensei's build
        /// script also reads its `cfg` tokens, and the determinism test exercises
        /// every entry under the default policy regardless of the embed setting.
        /// Feature and preparation policy select primitive, verifier, and prover
        /// payloads; the separate complete-selector build product is described
        /// by [`ArtifactId::GateSelectors`].
        ///
        /// List registered file names without reading raw inputs or generating bytes:
        ///
        /// ```
        /// use zakura_sensei_artifacts::{ARTIFACTS, ArtifactId, artifact};
        ///
        /// let names: Vec<_> = ARTIFACTS.iter().map(|entry| entry.file_name()).collect();
        /// assert!(names.iter().any(|name| name == "sigma-map.pod"));
        /// assert_eq!(artifact("sigma-map.pod").unwrap().id, ArtifactId::SigmaMap);
        /// ```
        pub static ARTIFACTS: &[Artifact] = &[$(Artifact {
            stem: $stem,
            form: $form,
            generate: |raw| $generate(&Context::new(raw)),
            $($field: $value,)*
        },)*];

        pub(crate) static ENCODERS: &[ContextEncoder] = &[
            $($generate,)*
        ];
    };
}

artifacts! {
    Artifact {
        stem: "primitive-points",
        form: Some(udon::STORED_FORM),
        generate: points::primitive_points,
        id: ArtifactId::PrimitivePoints,
        cfg: None,
        doc: "Sinsemilla generators, independent of SRS and circuit preparation",
    },
    Artifact {
        stem: "srs-points",
        form: Some(udon::STORED_FORM),
        generate: points::srs_points,
        id: ArtifactId::SrsPoints,
        cfg: None,
        doc: "SRS, prefix sums, blinding and IPA points shared by proof roles",
    },
    Artifact {
        stem: "commitment-tables",
        form: Some(udon::STORED_FORM),
        generate: crate::commitment_tables::generate,
        id: ArtifactId::CommitmentTables,
        cfg: Some("embed_commitment_tables"),
        doc: "optional affine commitment table expansions; rotations cached during warmup",
    },
    Artifact {
        stem: "points",
        form: Some(udon::STORED_FORM),
        generate: points::generate,
        id: ArtifactId::Points,
        cfg: None,
        doc: "affine SRS, prefix-sum, Sinsemilla, blinding, and IPA points",
    },
    Artifact {
        stem: "verifier-commitments",
        form: Some(udon::STORED_FORM),
        generate: points::verifier_commitments,
        id: ArtifactId::VerifierCommitments,
        cfg: None,
        doc: "deduplicated default-blinded verifier commitments and per-version column mappings",
    },
    Artifact {
        stem: "fixed-coefficients",
        form: Some(udon::STORED_FORM),
        generate: coefficients::generate_fixed,
        id: ArtifactId::FixedCoefficients,
        cfg: Some("embed_fixed_coefficients"),
        doc: "fixed-polynomial coefficients, derived from the sparse sources and layout",
    },
    Artifact {
        stem: "sigma-coefficients",
        form: Some(udon::STORED_FORM),
        generate: coefficients::generate_sigma,
        id: ArtifactId::SigmaCoefficients,
        cfg: Some("embed_sigma_coefficients"),
        doc: "sigma-polynomial coefficients, derived from the permutation map",
    },
    Artifact {
        stem: "fixed-cosets",
        form: Some(udon::STORED_FORM),
        generate: cosets::generate_fixed,
        id: ArtifactId::FixedCosets,
        cfg: Some("embed_fixed_cosets"),
        doc: "fixed-polynomial extended cosets, derived from the sparse sources and layout",
    },
    Artifact {
        stem: "sigma-cosets",
        form: Some(udon::STORED_FORM),
        generate: cosets::generate_sigma,
        id: ArtifactId::SigmaCosets,
        cfg: Some("embed_sigma_cosets"),
        doc: "sigma-polynomial extended cosets, derived from the permutation map",
    },
    Artifact {
        stem: "gate-selectors",
        form: Some(udon::STORED_FORM),
        generate: selectors::generate,
        id: ArtifactId::GateSelectors,
        cfg: Some("embed_gate_selectors"),
        doc: "prepared fixed-only gate selectors on every extended-coset row",
    },
    Artifact {
        stem: "window-tables",
        form: Some(udon::STORED_FORM),
        generate: fixed_base_tables::generate,
        id: ArtifactId::WindowTables,
        cfg: Some("embed_window_tables"),
        doc: "joint (x, y, u) fixed-base window entries for every multiplication region",
    },
    Artifact {
        stem: "instance-bases",
        form: Some(udon::STORED_FORM),
        generate: basis::generate_instance_bases,
        id: ArtifactId::InstanceBases,
        cfg: Some("embed_instance_bases"),
        doc: "transposed interpolation bases for the populated instance rows",
    },
    Artifact {
        stem: "boundaries",
        form: Some(udon::STORED_FORM),
        generate: basis::generate_boundaries,
        id: ArtifactId::Boundaries,
        cfg: Some("embed_boundaries"),
        doc: "extended-coset boundary polynomials l_0 and l_last and the active-row mask",
    },
    Artifact {
        stem: "fixed-window-x-bases",
        form: Some(udon::STORED_FORM),
        generate: window_bases::generate_x,
        id: ArtifactId::FixedWindowXBases,
        cfg: None,
        doc: "Vesta points x(window, digit)·G_row for every fixed-base window and digit",
    },
    Artifact {
        stem: "fixed-window-y-bases",
        form: Some(udon::STORED_FORM),
        generate: window_bases::generate_y,
        id: ArtifactId::FixedWindowYBases,
        cfg: None,
        doc: "Vesta points y(window, digit)·G_row for every fixed-base window and digit",
    },
    Artifact {
        stem: "fixed-window-u-bases",
        form: Some(udon::STORED_FORM),
        generate: window_bases::generate_u,
        id: ArtifactId::FixedWindowUBases,
        cfg: None,
        doc: "Vesta points u(window, digit)·G_row for every fixed-base window and digit",
    },
    Artifact {
        stem: "fixed-tuples",
        form: Some(udon::STORED_FORM),
        generate: fixed_columns::generate_tuples,
        id: ArtifactId::FixedTuples,
        cfg: None,
        doc: "distinct nonzero row tuples of fixed columns 3-11, in at-rest form",
    },
    Artifact {
        stem: "tuple-assignments.pod",
        form: None,
        generate: fixed_columns::generate_assignments,
        id: ArtifactId::TupleAssignments,
        cfg: None,
        doc: "sparse row-to-tuple assignments",
    },
    Artifact {
        stem: "sigma-map.pod",
        form: None,
        generate: permutation::generate,
        id: ArtifactId::SigmaMap,
        cfg: None,
        doc: "permutation as column-major target-cell indices",
    },
    Artifact {
        stem: "fft-tables",
        form: Some(udon::STORED_FORM),
        generate: crate::fft::generate_tables,
        id: ArtifactId::FftTables,
        cfg: Some("embed_fft_tables"),
        doc: "FFT twiddles and inverse finish scales in plan order",
    },
    Artifact {
        stem: "expansion-scales",
        form: Some(udon::STORED_FORM),
        generate: crate::fft::generate_scales,
        id: ArtifactId::ExpansionScales,
        cfg: Some("embed_expansion_scales"),
        doc: "residue-major expansion scales for each coset domain",
    },
}

/// Looks up one artifact by its complete [`Artifact::file_name`].
///
/// For example, use `points.mont-u64x4.pod`, not the stem `points`.
/// Disabled artifacts remain available for lookup.
pub fn artifact(name: &str) -> Option<&'static Artifact> {
    ARTIFACTS
        .iter()
        .find(|artifact| artifact.file_name() == name)
}

/// Generates the named artifact's bytes using the default commitment-table policy.
///
/// The name is the complete [`Artifact::file_name`]. This does not consult
/// a consumer's selection or write a file; unknown names and encoder failures
/// return an [`Error`].
///
/// The policy is [`sensei_shared::commitment_tables::DEFAULT`], under which
/// [`ArtifactId::CommitmentTables`] produces an empty payload. A build using
/// [`crate::emit_generated_with_commitment_tables`] can emit different bytes
/// for the same name; reproduce those bytes with the same inputs, recipes,
/// stored form, and policy.
pub fn generate(name: &str, raw: &RawStore) -> Result<Vec<u8>, Error> {
    let artifact =
        artifact(name).ok_or_else(|| Error::new(format!("unknown artifact `{name}`")))?;
    (artifact.generate)(raw)
}
