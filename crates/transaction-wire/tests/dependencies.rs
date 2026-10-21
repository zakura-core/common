//! Guards the crate's normal dependency graph: a consumer that depends only on
//! this crate must not pull in shielded-protocol, proving, primitives, wallet or
//! node crates. Dev-dependencies (the typed-decoder oracle) are excluded.

use std::process::Command;

/// Substrings that must not appear in any normal or build dependency name.
const FORBIDDEN: &[&str] = &[
    "orchard",
    "sapling",
    "halo2",
    "bellman",
    "jubjub",
    "pasta",
    "bls12",
    "redjubjub",
    "reddsa",
    "primitives",
    "proofs",
    "keys",
    "wallet",
    "client",
    "zakurad",
    "state",
    "network",
    "rpc",
];

/// The only Common crates allowed in the graph.
const ALLOWED_COMMON: &[&str] = &["zakura-transaction-wire", "zakura-protocol"];

#[test]
fn normal_dependencies_exclude_shielded_wallet_and_node_crates() {
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let output = Command::new(cargo)
        .args([
            "tree",
            "--package",
            "zakura-transaction-wire",
            "--edges",
            "no-dev",
            "--target",
            "all",
            "--prefix",
            "none",
            "--format",
            "{p}",
        ])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("run cargo tree");
    assert!(
        output.status.success(),
        "cargo tree failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut names: Vec<&str> = std::str::from_utf8(&output.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| line.split_whitespace().next())
        .collect();
    names.sort_unstable();
    names.dedup();

    assert!(names.contains(&"zakura-protocol"), "{names:?}");
    for name in &names {
        assert!(
            !FORBIDDEN.iter().any(|f| name.contains(f)),
            "forbidden normal dependency {name}"
        );
        assert!(
            !name.starts_with("zakura-") || ALLOWED_COMMON.contains(name),
            "unexpected Common dependency {name}"
        );
    }
    eprintln!("{} packages: {names:?}", names.len());
}
