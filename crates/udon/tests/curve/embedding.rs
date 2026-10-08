//! An owner embeds both table kinds and entry layouts for both curves.

use super::harness::{Consumer, arithmetic_feature_sets};

#[test]
#[ignore = "slow nested Cargo builds; run explicitly with --ignored"]
fn generated_curve_tables_embed_in_a_downstream_consumer() {
    let consumer = Consumer::new(
        "curve-embedding-consumer",
        "curve/fixtures/embedding",
        "udon",
        &[],
    );
    for features in arithmetic_feature_sets() {
        for (damage, diagnostic) in [
            ("", None),
            (
                "truncate",
                Some("embedded byte length must equal the requested type's size"),
            ),
        ] {
            consumer.check(
                "run",
                features,
                &[("CURVE_ARTIFACT_DAMAGE", damage)],
                diagnostic,
                &["src/lib.rs", "src/record.rs"],
            );
        }
    }
}
