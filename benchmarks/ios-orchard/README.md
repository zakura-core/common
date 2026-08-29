# Orchard prover benchmark on a physical iPhone

This isolated harness measures the production Orchard proving path on a real
iOS ARM64 device. It emits one JSON attachment and an identical one-line JSON
record in the XCTest log.

## What the benchmark measures

Current main's timed key-set initialization calls
`ProvingKey::build(BundleVersion::orchard_v3().circuit_version())` and then
`ProvingKey::verifying_key()`. The build does **not** generate the Halo2
polynomial-commitment parameters from scratch. Orchard embeds a canonical
131,140-byte encoding of the fixed `k = 11` Pasta parameters; every build decodes
that blob, synthesizes an empty current Orchard Action circuit, runs Halo2
`keygen_vk`, and then runs `keygen_pk`. The verifying-key accessor clones the
already-built parameters and VK. Orchard has no proving-key serializer or
process-global production proving-key cache. A wallet or service is expected
to retain and reuse both resulting keys.

The default mode does not enable Orchard's opt-in `orbits` feature and never
calls `ProvingKey::prepare_proving`. The comparison matrix uses
`orbits-prover` for its unprepared case and `prepared-prover` for its prepared
case. Both therefore use the same `orbits` MSM implementation; the only
difference is that `prepared-prover` calls `ProvingKey::prepare_proving` once
after all timed key-generation samples and before the proof warmup.
Preparation builds and caches fixed-base commitment tables. It is
intentionally outside both timed regions and is not reported as a benchmark;
the prepared mode measures only how reusing those tables changes
`Bundle::create_proof`.

The proof fixture uses `Builder`, `BundleType::DEFAULT`, and
`BundleVersion::orchard_v3()` to create two wallet-controlled change outputs.
Each is paired with the fabricated zero-valued same-receiver spend required by
the post-NU6.3 cross-address restriction: exactly two Orchard Actions under the
current circuit.
The timed call is the public `Bundle::create_proof` path. It includes public
instance construction, witness synthesis for both Actions, all Halo2 polynomial
work and commitments, Fiat-Shamir transcript work, and proof serialization.
It excludes key construction, bundle construction and cloning, RNG
construction, FFI/XCTest overhead, signatures, and verification.

The first of five key-generation samples is also reported as cold first use.
There is one verified proof warmup, followed by ten recorded proof samples.
The statement and Action shape never change; each proof uses a deterministic,
sample-indexed blinding seed so proof computation cannot be replaced by a
constant. Rust `Instant` supplies the monotonic high-resolution clock, and
`black_box` consumes keys and proofs. A ten-second cooldown follows the warmup,
and a five-second untimed cooldown separates proof samples to limit sustained
thermal load. JSON includes raw samples, minimum, median, mean, nearest-rank
p95, sample counts, thermal state, logical CPU/Rayon counts, source/toolchain
metadata, and exact optimization flags.

## Build the physical-iOS Rust library

The default CPU tuning is `apple-a17`, which enables modern Apple-silicon code
generation while keeping the binary usable across the comparison devices.

```console
./benchmarks/ios-orchard/scripts/build-rust.sh
```

Build the apples-to-apples unprepared and prepared variants with:

```console
ORCHARD_IOS_BENCH_FEATURES=orbits-prover \
    ./benchmarks/ios-orchard/scripts/build-rust.sh
ORCHARD_IOS_BENCH_FEATURES=prepared-prover \
    ./benchmarks/ios-orchard/scripts/build-rust.sh
```

This builds `aarch64-apple-ios` in Cargo release mode with `opt-level=3`, fat
LTO, one codegen unit, and aborting panics. The output is:

```text
target/aarch64-apple-ios/release/liborchard_ios_benchmark.a
```

## Build, sign, and package XCTest

```console
./benchmarks/ios-orchard/scripts/build-xctest.sh
./benchmarks/ios-orchard/scripts/package-firebase.sh
```

Xcode builds the Swift app and hosted unit test with the `Release`
configuration for `iphoneos`, never `iphonesimulator`. The script ad-hoc signs
the products so `codesign --verify` succeeds without a local Apple developer
identity; Firebase Test Lab re-signs uploaded test products with its own
profile. The upload artifact is:

```text
benchmarks/ios-orchard/artifacts/orchard-ios-xctest.zip
```

## Run on Firebase Test Lab

Firebase Test Lab was selected because its current iOS interface accepts one
standard XCTest ZIP, runs it on physical iPhones, has a direct `gcloud` CI/API
workflow, and retains raw logs plus `.xcresult` artifacts. As checked in August
2026, `iphone16pro` with iOS 18.3 has physical-device capacity. The launch
script rechecks the live catalog before every run.

AWS Device Farm also supports physical iOS XCTest, but requires separate `.ipa`
and XCTest uploads, a project, a device pool, upload polling, run scheduling,
and artifact enumeration. BrowserStack and Sauce support real-device XCUITest
through REST APIs, but also require separate application/test assets. Firebase
is the smaller end-to-end path for this non-UI benchmark.

One-time account setup:

```console
gcloud auth login
export GOOGLE_CLOUD_PROJECT=YOUR_FIREBASE_PROJECT_ID
```

The project must have billing enabled for physical-device testing. Then the
single build/upload/run/download/extract command is:

```console
./benchmarks/ios-orchard/scripts/run-firebase.sh
```

It enables the required APIs, creates a dedicated results bucket if necessary,
validates `iphone16pro` / iOS 18.3, launches the physical-device test, downloads
the raw results, exports the kept XCTest JSON attachment, validates it with
`jq`, and prints its path. Override the device for a later matrix with:

```console
FIREBASE_IOS_MODEL=iphone15pro FIREBASE_IOS_VERSION=18.0 \
    ./benchmarks/ios-orchard/scripts/run-firebase.sh
```

To extract an already-downloaded result tree:

```console
./benchmarks/ios-orchard/scripts/extract-result.sh \
    DOWNLOADED_RESULTS orchard-benchmark.json
```

## Run on an iPhone 17 Pro

Firebase's current physical-device catalog does not include an iPhone 17 Pro.
BrowserStack App Automate currently provides `iPhone 17 Pro-26` and supports
hosted XCTest bundles through its `xctestrun-build` API. The Firebase package
already contains the required app-hosted test bundle and `.xctestrun` metadata,
so it is reused without changing the timed Rust workload.

Run the script in a terminal. It securely prompts for BrowserStack App
Automate credentials without echoing or storing the access key:

```console
./benchmarks/ios-orchard/scripts/run-browserstack.sh
```

The script builds a minimal hosted-XCTest package, uploads the release test,
selects the physical
`iPhone 17 Pro-26`, waits for completion, downloads the result bundle, and
extracts `orchard-benchmark.json`. CI may instead provide
`BROWSERSTACK_USERNAME` and `BROWSERSTACK_ACCESS_KEY` in its secret store. Do
not commit or print the access key.

## Local verification

The cryptographic harness can run natively on the Mac without XCTest:

```console
CARGO_PROFILE_RELEASE_OPT_LEVEL=3 \
CARGO_PROFILE_RELEASE_LTO=fat \
CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 \
CARGO_PROFILE_RELEASE_PANIC=abort \
ORCHARD_BENCH_OPT_FLAGS='opt-level=3,lto=fat,codegen-units=1,panic=abort,target-cpu=native' \
RUSTFLAGS='-C target-cpu=native' \
cargo run --locked --release -p orchard-ios-benchmark \
    --bin orchard-ios-benchmark-host
```

That result is only a functional check and must not be reported as the iPhone
measurement. `build-xctest.sh` separately verifies that the actual release
device test bundle links, has ARM64 Mach-O binaries, and passes `codesign`
verification.

## Run on a personally owned iPhone

Connect the iPhone by USB, unlock it, trust the Mac, enable Developer Mode, and
add an Apple account under Xcode Settings > Accounts. Xcode must show the phone
under Window > Devices and Simulators. Find the account's ten-character team ID
in the Xcode account details or Apple Developer membership page.

With exactly one iPhone connected, run:

```console
DEVELOPMENT_TEAM=YOUR_TEAM_ID \
    ./benchmarks/ios-orchard/scripts/run-local-iphone.sh
```

If Xcode knows about multiple iPhones, select one explicitly:

```console
DEVELOPMENT_TEAM=YOUR_TEAM_ID IOS_DEVICE_ID=DEVICE_UDID \
    ./benchmarks/ios-orchard/scripts/run-local-iphone.sh
```

Run the comparable unprepared and prepared variants by passing their Cargo
features through the local runner:

```console
DEVELOPMENT_TEAM=YOUR_TEAM_ID IOS_DEVICE_ID=DEVICE_UDID \
ORCHARD_IOS_BENCH_FEATURES=orbits-prover \
    ./benchmarks/ios-orchard/scripts/run-local-iphone.sh
DEVELOPMENT_TEAM=YOUR_TEAM_ID IOS_DEVICE_ID=DEVICE_UDID \
ORCHARD_IOS_BENCH_FEATURES=prepared-prover \
    ./benchmarks/ios-orchard/scripts/run-local-iphone.sh
```

The script builds Rust and XCTest in release mode, uses automatic development
signing, installs and runs only the benchmark test on the physical phone, saves
the `.xcresult`, and extracts the machine-readable JSON. Keep the phone
unlocked for initial provisioning. No simulator product is built or run.

## Compare the repository root commit

The repository's first commit is
`16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b`. It already contains the complete
Orchard prover. Its `ProvingKey::build` differs materially from current main:
it runs `Params::new(11)` to generate the polynomial-commitment parameters,
then runs `keygen_vk` and `keygen_pk`. It has no `prepare_proving` API.

The historical runner creates an isolated detached worktree, overlays this
benchmark-only harness, and builds the root-commit cryptographic sources with
the same Rust 1.98 compiler, Release flags, fixture, sample counts, and iPhone
harness used for current main. Neither side enables `orbits` or prepares the
proving key. Historical key-set initialization uses the root commit's original
API and calls `VerifyingKey::build` separately. Each timed historical sample
therefore includes the second parameter generation and second VK generation in
`keygen_ms`. Run it on the connected phone with:

```console
DEVELOPMENT_TEAM=YOUR_TEAM_ID \
    ./benchmarks/ios-orchard/scripts/run-local-iphone-root-commit.sh
```

Results are written under
`benchmarks/ios-orchard/artifacts/history/16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b/`.
Set `ORCHARD_IOS_HISTORY_TOOLCHAIN=1.85.1` only if the comparison should also
reproduce the root commit's original compiler instead of holding the compiler
constant. The historical runner supports neither `orbits-prover` nor
`prepared-prover`, because the root implementation has no equivalent API.
