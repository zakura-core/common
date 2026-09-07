//! Times the CPU planner, the reference backend, and (on Apple silicon)
//! the Metal backend on random Vesta MSMs of increasing size.
//!
//! ```text
//! cargo run --release -p zakura-pasta-msm-metal --example msm_bench -- [max_log2] [runs]
//! ```
//!
//! Environment overrides: `PASTA_MSM_METAL_WINDOW_BITS`,
//! `PASTA_MSM_METAL_CHUNK_LOG2` (see `Config::from_env`), and
//! `PASTA_MSM_BENCH_REFERENCE=1` to include the (slow) reference backend.

use std::time::{Duration, Instant};

use ff::Field;
use group::{Curve, Group};
use pasta_curves::arithmetic::CurveExt;
use pasta_curves::vesta;
use pasta_msm_metal::curves::Vesta;
use pasta_msm_metal::pipeline::{Backend, Config, Plan, Reference, multiexp};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

fn median(mut samples: Vec<Duration>) -> Duration {
    samples.sort();
    samples[samples.len() / 2]
}

fn time<T>(runs: usize, mut f: impl FnMut() -> T) -> (Duration, T) {
    let mut samples = Vec::with_capacity(runs);
    let mut last = None;
    for _ in 0..runs {
        let start = Instant::now();
        last = Some(f());
        samples.push(start.elapsed());
    }
    (median(samples), last.expect("at least one run"))
}

fn main() {
    let mut args = std::env::args().skip(1);
    let max_log2: u32 = args.next().and_then(|a| a.parse().ok()).unwrap_or(16);
    let runs: usize = args.next().and_then(|a| a.parse().ok()).unwrap_or(5);
    let with_reference = std::env::var("PASTA_MSM_BENCH_REFERENCE").is_ok();
    let config = Config {
        min_terms: 0,
        ..Config::from_env()
    };

    let backends: Vec<(&str, Box<dyn Backend>)> = {
        let mut list: Vec<(&str, Box<dyn Backend>)> = Vec::new();
        if with_reference {
            list.push(("reference", Box::new(Reference)));
        }
        #[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
        match pasta_msm_metal::metal::Metal::open() {
            Ok(metal) => {
                eprintln!("Metal device: {}", metal.device_name());
                list.push(("metal", Box::new(metal)));
            }
            Err(error) => eprintln!("Metal unavailable: {error}"),
        }
        list
    };

    let mut rng = XorShiftRng::from_seed([42; 16]);
    println!(
        "terms\tplan\tcpu_us\t{}",
        backends
            .iter()
            .map(|(n, _)| format!("{n}_us"))
            .collect::<Vec<_>>()
            .join("\t")
    );
    for log2 in 10..=max_log2 {
        let terms = 1usize << log2;
        let scalars: Vec<vesta::Scalar> = (0..terms)
            .map(|_| vesta::Scalar::random(&mut rng))
            .collect();
        let bases: Vec<vesta::Affine> = (0..terms)
            .map(|_| vesta::Point::random(&mut rng).to_affine())
            .collect();
        let plan = Plan::new(terms, &config);

        let (cpu_time, expected) = time(runs, || {
            vesta::Point::try_multiexp_vartime(&scalars, &bases).expect("cpu planner")
        });
        let mut row = format!(
            "{terms}\tc={} w={} s=2^{}\t{}",
            plan.window_bits,
            plan.windows,
            plan.chunk_log2,
            cpu_time.as_micros()
        );
        for (name, backend) in &backends {
            let (backend_time, got) = time(runs, || {
                multiexp::<Vesta>(backend.as_ref(), &config, &scalars, &bases)
            });
            match got {
                Some(point) if point == expected => {
                    row.push_str(&format!("\t{}", backend_time.as_micros()))
                }
                Some(_) => row.push_str(&format!("\t{} (WRONG RESULT)", backend_time.as_micros())),
                None => row.push_str(&format!("\t{} (declined)", backend_time.as_micros())),
            }
            let _ = name;
        }
        println!("{row}");
    }
}
