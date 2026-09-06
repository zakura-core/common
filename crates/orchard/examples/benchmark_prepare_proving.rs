use std::{hint::black_box, time::Instant};

use orchard::circuit::{OrchardCircuitVersion, ProvingKey};

fn main() {
    let samples = std::env::var("ZAKURA_BENCH_SAMPLES")
        .ok()
        .and_then(|samples| samples.parse::<usize>().ok())
        .unwrap_or(20);
    for sample in 0..samples {
        let key = ProvingKey::build(OrchardCircuitVersion::PostNu6_3);
        let start = Instant::now();
        assert!(black_box(&key).prepare_proving());
        println!(
            "prepare-proving sample={sample} nanos={}",
            start.elapsed().as_nanos()
        );
    }
}
