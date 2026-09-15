use std::{
    ffi::{CStr, CString},
    hint::black_box,
    os::raw::c_char,
    time::{Duration, Instant},
};

use orchard::{
    builder::{Builder, BundleType},
    bundle::{BundleVersion, TxVersion},
    circuit::ProvingKey,
    keys::{FullViewingKey, Scope, SpendAuthorizingKey, SpendingKey},
    value::NoteValue,
    Anchor, Bundle,
};
use rand::{rngs::StdRng, SeedableRng};
use serde::Serialize;

#[cfg(all(feature = "historical-root", feature = "orbits-prover"))]
compile_error!("the root-commit Orchard implementation has no orbits prover");

const ACTION_COUNT: usize = 2;
const BUILD_PROFILE: &str = if cfg!(debug_assertions) {
    "debug"
} else {
    "release"
};
const KEYGEN_SAMPLES: usize = 5;
const PROVING_SAMPLES: usize = 10;
const PROVING_WARMUPS: usize = 1;
const KEYGEN_COOLDOWN: Duration = Duration::from_millis(750);
const PROVING_COOLDOWN: Duration = Duration::from_secs(5);
const POST_WARMUP_COOLDOWN: Duration = Duration::from_secs(10);
const FIXTURE_ADDRESS_INDEX: u32 = 0;
const FIXTURE_NOTE_VALUE: u64 = 10;
/// The Orchard builder API fixes memo fields at 512 bytes.
const FIXTURE_MEMO_SIZE: usize = 512;
const FIXTURE_MEMO: [u8; FIXTURE_MEMO_SIZE] = [0; FIXTURE_MEMO_SIZE];
const FIXTURE_SPENDING_KEY: [u8; 32] = [7; 32];
const FIXTURE_ANCHOR: [u8; 32] = [0; 32];
const FIXTURE_SEED: [u8; 32] = [0x42; 32];
const WARMUP_PROOF_SEED: [u8; 32] = [0x18; 32];
const PROOF_SEED_DOMAIN: u8 = 0x24;
#[cfg(not(feature = "historical-root"))]
const KEYGEN_DEFINITION: &str =
    "ProvingKey::build (embedded k=11 Params decode + Halo2 VK and PK generation) + \
     ProvingKey::verifying_key";
#[cfg(feature = "historical-root")]
const KEYGEN_DEFINITION: &str =
    "ProvingKey::build (k=11 Params generation + Halo2 VK and PK generation) + \
     VerifyingKey::build (separate k=11 Params generation + Halo2 VK generation)";
#[cfg(not(feature = "orbits-prover"))]
const ORCHARD_FEATURES: &[&str] = &["circuit", "multicore", "std"];
#[cfg(feature = "orbits-prover")]
const ORCHARD_FEATURES: &[&str] = &["circuit", "multicore", "orbits", "std"];
const PROVING_KEY_PREPARED: bool = cfg!(feature = "prepared-prover");

#[derive(Serialize)]
struct BenchmarkOutput {
    schema_version: u32,
    device: DeviceMetadata,
    build: BuildMetadata,
    workload: WorkloadMetadata,
    cold_init: ColdInit,
    keygen_ms: f64,
    prove_2_actions_ms: f64,
    keygen: SampleSummary,
    prove_2_actions: SampleSummary,
}

#[derive(Serialize)]
struct DeviceMetadata {
    hardware_identifier: String,
    model: String,
    soc: String,
    os_version: String,
    active_processor_count: usize,
    rayon_threads: usize,
    thermal_state_start: String,
}

#[derive(Serialize)]
struct BuildMetadata {
    profile: &'static str,
    git_commit: &'static str,
    git_dirty: bool,
    rust_version: &'static str,
    compiler_optimization_flags: &'static str,
    target_triple: &'static str,
    xcode_version: &'static str,
    orchard_features: &'static [&'static str],
}

#[derive(Serialize)]
struct WorkloadMetadata {
    value_pool: &'static str,
    bundle_version: &'static str,
    circuit_version: String,
    actions: usize,
    action_shape: &'static str,
    proof_api: &'static str,
    keygen_definition: &'static str,
    proving_key_prepared: bool,
    proving_timer_excludes: &'static [&'static str],
    keygen_cooldown_ms: u128,
    proving_warmups: usize,
    post_warmup_cooldown_ms: u128,
    proving_cooldown_ms: u128,
}

#[derive(Serialize)]
struct ColdInit {
    first_keygen_ms: f64,
    note: &'static str,
}

#[derive(Serialize)]
struct SampleSummary {
    samples_ms: Vec<f64>,
    min_ms: f64,
    median_ms: f64,
    mean_ms: f64,
    p95_ms: f64,
    sample_count: usize,
}

impl SampleSummary {
    fn from_samples(samples_ms: Vec<f64>) -> Self {
        assert!(!samples_ms.is_empty());
        let mut sorted = samples_ms.clone();
        sorted.sort_by(f64::total_cmp);
        let sample_count = sorted.len();
        let middle = sample_count / 2;
        let median_ms = if sample_count.is_multiple_of(2) {
            (sorted[middle - 1] + sorted[middle]) / 2.0
        } else {
            sorted[middle]
        };
        // Nearest-rank percentile: ceil(0.95 * n), converted to a zero-based
        // index. This intentionally returns the maximum for small sample sets.
        let p95_index = (95 * sample_count).div_ceil(100) - 1;

        Self {
            min_ms: sorted[0],
            median_ms,
            mean_ms: samples_ms.iter().sum::<f64>() / sample_count as f64,
            p95_ms: sorted[p95_index],
            sample_count,
            samples_ms,
        }
    }
}

fn elapsed_ms(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1_000.0
}

fn proof_seed(sample: usize) -> [u8; 32] {
    let mut seed = [PROOF_SEED_DOMAIN; 32];
    seed[..8].copy_from_slice(&(sample as u64).to_le_bytes());
    seed
}

type UnprovenBundle = Bundle<
    orchard::builder::InProgress<orchard::builder::Unproven, orchard::builder::Unauthorized>,
    i64,
>;

fn build_two_action_fixture() -> (UnprovenBundle, SpendAuthorizingKey) {
    let bundle_version = BundleVersion::orchard_v3();
    let spending_key = SpendingKey::from_bytes(FIXTURE_SPENDING_KEY).unwrap();
    let spend_authorizing_key = SpendAuthorizingKey::from(&spending_key);
    let full_viewing_key = FullViewingKey::from(&spending_key);
    let recipient = full_viewing_key.address_at(FIXTURE_ADDRESS_INDEX, Scope::Internal);
    let mut builder = Builder::new(
        BundleType::DEFAULT,
        bundle_version,
        bundle_version.default_flags(),
        Anchor::from_bytes(FIXTURE_ANCHOR).unwrap(),
    )
    .unwrap();

    for _ in 0..ACTION_COUNT {
        builder
            .add_change_output(
                full_viewing_key.clone(),
                None,
                recipient,
                NoteValue::from_raw(FIXTURE_NOTE_VALUE),
                FIXTURE_MEMO,
            )
            .unwrap();
    }

    let bundle = builder
        .build(&mut StdRng::from_seed(FIXTURE_SEED))
        .unwrap()
        .expect("two outputs produce an Orchard bundle")
        .0;
    assert_eq!(bundle.actions().len(), ACTION_COUNT);
    (bundle, spend_authorizing_key)
}

fn run_benchmark(mut device: DeviceMetadata) -> BenchmarkOutput {
    let bundle_version = BundleVersion::orchard_v3();
    let circuit_version = bundle_version.circuit_version();

    // No Orchard or Halo2 work happens before this loop. The first sample is
    // therefore the process-cold key-set initialization cost. The final keys
    // are retained and reused by every proof. Optional proving preparation
    // happens after this timed region.
    let mut keygen_samples = Vec::with_capacity(KEYGEN_SAMPLES);
    let mut proving_key = None;
    let mut verifying_key = None;
    for sample in 0..KEYGEN_SAMPLES {
        if sample > 0 {
            std::thread::sleep(KEYGEN_COOLDOWN);
        }
        let start = Instant::now();
        let key = ProvingKey::build(circuit_version);
        #[cfg(not(feature = "historical-root"))]
        let verifier = key.verifying_key();
        #[cfg(feature = "historical-root")]
        let verifier = orchard::circuit::VerifyingKey::build(circuit_version);
        keygen_samples.push(elapsed_ms(start));
        black_box(&key);
        black_box(&verifier);
        if sample + 1 == KEYGEN_SAMPLES {
            proving_key = Some(key);
            verifying_key = Some(verifier);
        }
    }
    let cold_keygen_ms = keygen_samples[0];
    let keygen = SampleSummary::from_samples(keygen_samples);
    let proving_key = proving_key.expect("the final keygen sample retains its key");
    let verifying_key = verifying_key.expect("the final keygen sample retains its verifier");
    // Read the pool size only after cold key generation so this metadata call
    // cannot initialize Rayon ahead of the first-use sample.
    device.rayon_threads = rayon::current_num_threads();

    #[cfg(feature = "prepared-prover")]
    {
        let prepared = proving_key.prepare_proving();
        assert!(
            prepared,
            "the benchmark must perform first-time preparation"
        );
        black_box(prepared);
    }

    let (fixture, spend_authorizing_key) = build_two_action_fixture();
    assert_eq!(fixture.circuit_version(), proving_key.circuit_version());
    let sighash: [u8; 32] = fixture
        .commitment(TxVersion::V6)
        .expect("the Orchard v3 fixture is representable in a v6 transaction")
        .into();

    for _ in 0..PROVING_WARMUPS {
        let warmup = fixture
            .clone()
            .create_proof(&proving_key, StdRng::from_seed(WARMUP_PROOF_SEED))
            .expect("the two-Action warmup proof must succeed");
        let warmup = warmup
            .apply_signatures(
                StdRng::from_seed(WARMUP_PROOF_SEED),
                sighash,
                std::slice::from_ref(&spend_authorizing_key),
            )
            .expect("the fabricated spends are signed by the fixture key");
        warmup
            .verify_proof(&verifying_key)
            .expect("the two-Action warmup proof must verify");
        black_box(warmup);
    }
    std::thread::sleep(POST_WARMUP_COOLDOWN);

    let mut proving_samples = Vec::with_capacity(PROVING_SAMPLES);
    for sample in 0..PROVING_SAMPLES {
        if sample > 0 {
            std::thread::sleep(PROVING_COOLDOWN);
        }
        // Bundle cloning and RNG setup are deliberately outside the timed
        // region. The varying deterministic blinding seed prevents proof
        // replacement while preserving the exact statement and Action shape.
        let sample_bundle = black_box(fixture.clone());
        let proof_rng = StdRng::from_seed(proof_seed(sample));
        let start = Instant::now();
        let proven = sample_bundle
            .create_proof(&proving_key, proof_rng)
            .expect("the two-Action benchmark proof must succeed");
        proving_samples.push(elapsed_ms(start));
        black_box(proven);
    }
    let prove_2_actions = SampleSummary::from_samples(proving_samples);

    BenchmarkOutput {
        schema_version: 2,
        device,
        build: BuildMetadata {
            profile: BUILD_PROFILE,
            git_commit: env!("ORCHARD_BENCH_GIT_COMMIT"),
            git_dirty: env!("ORCHARD_BENCH_GIT_DIRTY") == "true",
            rust_version: env!("ORCHARD_BENCH_RUST_VERSION"),
            compiler_optimization_flags: env!("ORCHARD_BENCH_OPT_FLAGS"),
            target_triple: env!("ORCHARD_BENCH_TARGET"),
            xcode_version: env!("ORCHARD_BENCH_XCODE_VERSION"),
            orchard_features: ORCHARD_FEATURES,
        },
        workload: WorkloadMetadata {
            value_pool: "Orchard",
            bundle_version: "BundleVersion::orchard_v3()",
            circuit_version: format!("{:?}", circuit_version),
            actions: ACTION_COUNT,
            action_shape:
                "two wallet-controlled change outputs with two fabricated zero-valued spends",
            proof_api: "Bundle::create_proof",
            keygen_definition: KEYGEN_DEFINITION,
            proving_key_prepared: PROVING_KEY_PREPARED,
            proving_timer_excludes: &[
                "proving- and verifying-key construction",
                "optional ProvingKey::prepare_proving",
                "bundle construction and cloning",
                "RNG construction",
                "FFI and XCTest overhead",
                "proof verification",
            ],
            keygen_cooldown_ms: KEYGEN_COOLDOWN.as_millis(),
            proving_warmups: PROVING_WARMUPS,
            post_warmup_cooldown_ms: POST_WARMUP_COOLDOWN.as_millis(),
            proving_cooldown_ms: PROVING_COOLDOWN.as_millis(),
        },
        cold_init: ColdInit {
            first_keygen_ms: cold_keygen_ms,
            note: "first Orchard/Halo2 operation in the XCTest process",
        },
        keygen_ms: keygen.median_ms,
        prove_2_actions_ms: prove_2_actions.median_ms,
        keygen,
        prove_2_actions,
    }
}

unsafe fn required_string(value: *const c_char, name: &str) -> Result<String, String> {
    if value.is_null() {
        return Err(format!("{name} must not be null"));
    }
    // SAFETY: The caller contract requires a live, NUL-terminated C string.
    unsafe { CStr::from_ptr(value) }
        .to_str()
        .map(str::to_owned)
        .map_err(|error| format!("{name} is not UTF-8: {error}"))
}

/// Runs the benchmark and returns owned UTF-8 JSON.
///
/// The caller must release the result with
/// [`orchard_ios_benchmark_string_free`]. All input pointers must reference
/// live, NUL-terminated UTF-8 strings for the duration of this call.
///
/// # Safety
///
/// Every input pointer must be non-null and point to a live, NUL-terminated
/// UTF-8 string for the entire call. The returned pointer must be released
/// exactly once with [`orchard_ios_benchmark_string_free`].
#[no_mangle]
pub unsafe extern "C" fn orchard_ios_benchmark_run(
    hardware_identifier: *const c_char,
    model: *const c_char,
    soc: *const c_char,
    os_version: *const c_char,
    thermal_state_start: *const c_char,
    active_processor_count: usize,
) -> *mut c_char {
    let result = (|| {
        if cfg!(debug_assertions) {
            return Err("the benchmark must be built with Cargo --release".to_owned());
        }
        let device = DeviceMetadata {
            // SAFETY: Each pointer is governed by this function's caller
            // contract and copied before the benchmark starts.
            hardware_identifier: unsafe {
                required_string(hardware_identifier, "hardware_identifier")?
            },
            model: unsafe { required_string(model, "model")? },
            soc: unsafe { required_string(soc, "soc")? },
            os_version: unsafe { required_string(os_version, "os_version")? },
            thermal_state_start: unsafe {
                required_string(thermal_state_start, "thermal_state_start")?
            },
            active_processor_count,
            rayon_threads: 0,
        };
        serde_json::to_string(&run_benchmark(device)).map_err(|error| error.to_string())
    })();

    let json = match result {
        Ok(json) => json,
        Err(error) => serde_json::json!({ "error": error }).to_string(),
    };
    CString::new(json)
        .expect("serialized JSON contains no interior NUL")
        .into_raw()
}

/// Releases a string returned by [`orchard_ios_benchmark_run`].
///
/// # Safety
///
/// `value` must be null or a pointer returned by
/// [`orchard_ios_benchmark_run`] that has not already been freed.
#[no_mangle]
pub unsafe extern "C" fn orchard_ios_benchmark_string_free(value: *mut c_char) {
    if !value.is_null() {
        // SAFETY: The caller contract requires a pointer returned by
        // `CString::into_raw` in `orchard_ios_benchmark_run`, exactly once.
        drop(unsafe { CString::from_raw(value) });
    }
}
