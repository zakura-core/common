//! Generates every embedded artifact into `OUT_DIR`.
//!
//! Stage one of the data pipeline: host generators in `sensei-artifacts` and
//! this script turn the canonical raw inputs under this package's `data/raw/`
//! into the exact bytes the embedding declarations read back zero-copy
//! (stage two, `bento`).
//! Nothing generated is checked in. The output bytes are target-independent
//! (little-endian layout, guarded by a compile error on big-endian targets),
//! so host generation composes with cross-compilation.

use sensei_shared::dimensions::{EXTENDED_N, N};
use std::{fs, path::PathBuf};

mod artifact_selection;
#[allow(dead_code, unused_imports)]
#[path = "src/selector_preparation.rs"]
mod selector_preparation;
#[path = "src/tuning.rs"]
mod tuning;

fn main() {
    println!("cargo::rerun-if-changed=data/raw");
    println!("cargo::rerun-if-changed=src/tuning.rs");
    println!("cargo::rerun-if-changed=artifact_selection.rs");
    println!("cargo::rerun-if-changed=src/selector_preparation.rs");
    // Emit cfgs for selected artifacts and the optional complete selector table.
    let selected = artifact_selection::selected();
    for artifact in sensei_artifacts::ARTIFACTS {
        if let Some(token) = artifact.cfg {
            println!("cargo::rustc-check-cfg=cfg({token})");
            if selected.contains(&artifact.id)
                || (artifact.id == sensei_artifacts::ArtifactId::GateSelectors
                    && cfg!(feature = "prover")
                    && tuning::GATE_SELECTORS == tuning::OptionalPreparation::Embed)
            {
                println!("cargo::rustc-cfg={token}");
            }
        }
    }
    // Generate the selected registry artifacts using the configured commitment tables.
    let data_dir = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").expect("cargo sets this"))
        .join("data");
    let out_dir = PathBuf::from(std::env::var_os("OUT_DIR").expect("cargo sets this"));
    let raw = sensei_artifacts::RawStore::new(data_dir);
    let mut names = sensei_artifacts::emit_generated_with_commitment_tables(
        &raw,
        &out_dir,
        &selected,
        tuning::COMMITMENT_TABLES,
    )
    .expect("generating embedded artifacts");
    // Generate complete selectors only when the prover embeds them.
    if cfg!(feature = "prover") && tuning::GATE_SELECTORS == tuning::OptionalPreparation::Embed {
        let fixed_name = concat!("fixed-cosets.", udon::stored_form!(), ".pod");
        let fixed = if names.iter().any(|name| name == fixed_name) {
            fs::read(out_dir.join(fixed_name)).expect("reading fixed cosets")
        } else {
            sensei_artifacts::generate(fixed_name, &raw).expect("generating fixed cosets")
        };
        let field_bytes = core::mem::size_of::<udon::field::Fp>();
        let mut bytes = Vec::with_capacity(
            selector_preparation::PREPARED_GATE_SELECTOR_ROW * EXTENDED_N * field_bytes,
        );
        for row in 0..EXTENDED_N {
            let queries = sensei_shared::queries::GATE_QUERY_DESCRIPTORS.map(|(kind, index)| {
                if kind != sensei_shared::queries::QueryKind::Fixed {
                    return udon::field::Fp::ZERO;
                }
                let query = sensei_shared::queries::FIXED_QUERIES[index];
                assert_eq!(query.rotation, 0);
                // Fixed cosets store each residue contiguously; selector
                // rows use the extended domain's natural order.
                let residues = EXTENDED_N / N;
                let offset =
                    (query.column * EXTENDED_N + row % residues * N + row / residues) * field_bytes;
                udon::field::Fp::from_montgomery_limbs(core::array::from_fn(|limb| {
                    u64::from_le_bytes(
                        fixed[offset + limb * 8..offset + limb * 8 + 8]
                            .try_into()
                            .unwrap(),
                    )
                }))
            });
            let prepared = selector_preparation::prepare_gate_selectors(&queries)
                .map(|value| value.reduce().into_loose());
            bytes.extend_from_slice(bento::bytes_of(&prepared));
        }
        // Keep this filename in sync with GATE_SELECTORS in src/native/target/embedded.rs.
        let name = concat!("gate-selectors-complete.", udon::stored_form!(), ".pod");
        fs::write(out_dir.join(name), bytes).expect("writing complete selectors");
        names.push(name.to_owned());
    }
    // Write the manifest from this build's selected payloads, never stale OUT_DIR files.
    let entries: Vec<_> = names
        .iter()
        .map(|name| {
            let bytes = fs::metadata(out_dir.join(name))
                .expect("emitted artifact")
                .len();
            format!("  {{\"file\": {name:?}, \"bytes\": {bytes}}}")
        })
        .collect();
    fs::write(
        out_dir.join("artifact-manifest.json"),
        format!("[\n{}\n]\n", entries.join(",\n")),
    )
    .expect("writing artifact manifest");
    fs::write(out_dir.join("tuning.rs"), include_str!("src/tuning.rs"))
        .expect("recording preparation policy");
}
