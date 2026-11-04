use super::*;
use crate::{
    native::{runtime, verifier},
    verification_corpus as corpus,
};
use std::{process::Command, sync::Barrier};

fn verify_mixed() {
    let fixtures = corpus::VERSIONS.map(|version| corpus::small(version, 1));
    let requests = fixtures.each_ref().map(corpus::Fixture::request);
    crate::verify_proofs(&requests, &mut || Ok(83)).unwrap();
}

#[test]
fn concurrent_codebook_requests_share_each_width() {
    let books = Codebooks::default();
    let barrier = Barrier::new(6);
    let results = std::thread::scope(|scope| {
        let threads: Vec<_> = (0..6)
            .map(|_| {
                scope.spawn(|| {
                    barrier.wait();
                    [5, 6, 7].map(|width| books.get(width))
                })
            })
            .collect();
        threads
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect::<Vec<_>>()
    });
    for result in &results {
        for (index, book) in result.iter().enumerate() {
            assert!(Arc::ptr_eq(book, &results[0][index]));
            assert_eq!(book.view().description().window_bits(), index as u8 + 5);
        }
        assert!(!Arc::ptr_eq(&result[0], &result[1]));
        assert!(!Arc::ptr_eq(&result[1], &result[2]));
    }
}

/// Each child starts with cold process caches, independently of the
/// unit test runner's ordering. Exercise both the serial fallback and a pool.
#[test]
#[cfg_attr(debug_assertions, ignore = "full preparation requires --release")]
fn warmup_orders_share_one_srs() {
    const SCENARIO: &str = "SENSEI_SRS_WARMUP_ORDER";
    let Ok(order) = std::env::var(SCENARIO) else {
        for workers in [1, 2] {
            for order in [
                "prover-first",
                "verifier-first",
                "concurrent",
                "verify-current",
                "verify-fixed",
                "verify-insecure",
                "verify-mixed",
            ] {
                let output = Command::new(std::env::current_exe().unwrap())
                    .args([
                        "--exact",
                        "native::srs::tests::warmup_orders_share_one_srs",
                        "--include-ignored",
                        "--nocapture",
                    ])
                    .env(SCENARIO, order)
                    .env("SENSEI_BENCH_WORKERS", workers.to_string())
                    .output()
                    .unwrap();
                assert!(
                    output.status.success(),
                    "{order}, {workers} workers:\n{}\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                );
            }
        }
        return;
    };

    assert!(SRS.get().is_none());
    assert!(runtime::prepared_srs_for_test().is_none());
    assert!(verifier::prepared_srs_for_test().is_none());

    let fixtures = corpus::VERSIONS.map(|version| corpus::small(version, 1));
    let requests = fixtures.each_ref().map(corpus::Fixture::request);
    assert_eq!(
        crate::verify_proofs(&requests, &mut || Err(crate::RandomnessError)),
        Err(crate::Error::RngFailure)
    );
    assert_eq!(
        crate::verify_proofs(&requests, &mut || Ok(0)),
        Err(crate::Error::RetryRandomness)
    );
    assert!(SRS.get().is_none());
    assert!(runtime::prepared_srs_for_test().is_none());
    assert!(verifier::prepared_srs_for_test().is_none());
    crate::verify_proofs(&[], &mut || panic!("empty batch must not use randomness")).unwrap();
    assert!(SRS.get().is_none());
    assert!(runtime::prepared_srs_for_test().is_none());
    assert!(verifier::prepared_srs_for_test().is_none());

    match order.as_str() {
        "prover-first" => {
            crate::warm_up_prover();
            assert!(runtime::prepared_srs_for_test().is_some());
            assert!(verifier::prepared_srs_for_test().is_none());
            crate::warm_up_verifier();
        }
        "verifier-first" => {
            crate::warm_up_verifier();
            assert!(verifier::prepared_srs_for_test().is_some());
            assert!(runtime::prepared_srs_for_test().is_none());
            crate::warm_up_prover();
        }
        "verify-current" | "verify-fixed" | "verify-insecure" | "verify-mixed" => {
            if order == "verify-mixed" {
                verify_mixed();
            } else {
                let index = match order.as_str() {
                    "verify-current" => 0,
                    "verify-fixed" => 1,
                    "verify-insecure" => 2,
                    _ => unreachable!(),
                };
                crate::verify_proofs(&requests[index..index + 1], &mut || panic!("singleton RNG"))
                    .unwrap();
            }
            assert!(verifier::prepared_srs_for_test().is_some());
            assert!(runtime::prepared_srs_for_test().is_none());
            verify_mixed();
            assert!(runtime::prepared_srs_for_test().is_none());
            crate::warm_up_prover();
        }
        "concurrent" => {
            let barrier = Barrier::new(6);
            let warmers: [fn(); 6] = [
                crate::warm_up_prover,
                verify_mixed,
                crate::warm_up,
                crate::warm_up_verifier,
                crate::warm_up_prover,
                crate::warm_up_verifier,
            ];
            std::thread::scope(|scope| {
                for warm in warmers {
                    let barrier = &barrier;
                    scope.spawn(move || {
                        barrier.wait();
                        warm();
                    });
                }
            });
        }
        _ => panic!("unknown warmup order"),
    }

    let srs = PreparedSrs::shared();
    for _ in 0..2 {
        crate::warm_up();
        crate::warm_up_prover();
        crate::warm_up_verifier();
        assert!(Arc::ptr_eq(&srs, SRS.get().unwrap()));
        assert!(Arc::ptr_eq(&srs, runtime::prepared_srs_for_test().unwrap()));
        assert!(Arc::ptr_eq(
            &srs,
            verifier::prepared_srs_for_test().unwrap()
        ));
    }
}
