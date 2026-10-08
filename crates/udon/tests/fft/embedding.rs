//! A downstream owner prepares FFT tables and embeds them in a `no_std` library.

use super::harness::{Consumer, arithmetic_feature_sets};

#[test]
#[ignore = "slow nested Cargo builds; run explicitly with --ignored"]
fn generated_fft_tables_embed_in_a_downstream_consumer() {
    let consumer = Consumer::new(
        "fft-embedding-consumer",
        "fft/fixtures/embedding",
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
                &[("FFT_ARTIFACT_DAMAGE", damage)],
                diagnostic,
                &["src/pod/storage.rs"],
            );
        }
    }
}
