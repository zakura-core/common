//! A downstream build script generates field records for typed embedding.

use std::{collections::BTreeMap, fs, path::Path};

use super::harness::{Consumer, arithmetic_feature_sets};

#[test]
#[ignore = "slow nested Cargo builds; run explicitly with --ignored"]
fn generated_fields_embed_in_a_downstream_consumer() {
    let consumer = Consumer::new(
        "field-embedding-consumer",
        "field/fixtures/embedding",
        "udon",
        &[],
    );
    // Arithmetic and square-root features must preserve stored representations,
    // including when the generator itself uses assembly.
    let mut stored = None;
    for features in arithmetic_feature_sets() {
        consumer.check("run", features, &[], None, &[]);
        let artifacts = generated_artifacts(&consumer.target);
        assert_eq!(
            artifacts.keys().map(String::as_str).collect::<Vec<_>>(),
            ["field-values-mont-u64x4.bin", "fp-values-mont-u64x4.bin"]
        );
        match &stored {
            None => stored = Some(artifacts),
            Some(first) => assert_eq!(
                first, &artifacts,
                "stored bytes must not depend on arithmetic features"
            ),
        }
    }
}

// Collects the generated files across the consumer's build script out
// directories. Cargo may keep one directory per feature set; entries sharing a
// filename must already agree before the configurations are compared.
fn generated_artifacts(target: &Path) -> BTreeMap<String, Vec<u8>> {
    let mut artifacts = BTreeMap::new();
    let build = target.join("release/build");
    for entry in fs::read_dir(&build).expect("read the nested build directory") {
        let path = entry.unwrap().path();
        let out = path.join("out");
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if !name.starts_with("field-embedding-consumer-") || !out.is_dir() {
            continue;
        }
        for file in fs::read_dir(&out).unwrap() {
            let file = file.unwrap().path();
            let name = file.file_name().unwrap().to_string_lossy().into_owned();
            let bytes = fs::read(&file).unwrap();
            if let Some(previous) = artifacts.insert(name.clone(), bytes) {
                assert_eq!(
                    previous, artifacts[&name],
                    "artifact {name} differs between out directories"
                );
            }
        }
    }
    artifacts
}
