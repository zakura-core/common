#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
TARGET="${ORCHARD_IOS_RUST_TARGET:-aarch64-apple-ios}"
TARGET_CPU="${ORCHARD_IOS_TARGET_CPU:-apple-a17}"
DEPLOYMENT_TARGET="${ORCHARD_IOS_DEPLOYMENT_TARGET:-17.0}"
OPT_FLAGS="opt-level=3,lto=fat,codegen-units=1,panic=abort,target-cpu=${TARGET_CPU},ios-min=${DEPLOYMENT_TARGET}"

export CARGO_PROFILE_RELEASE_OPT_LEVEL=3
export CARGO_PROFILE_RELEASE_LTO=fat
export CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
export CARGO_PROFILE_RELEASE_PANIC=abort
export CARGO_PROFILE_RELEASE_INCREMENTAL=false
export RUSTFLAGS="${RUSTFLAGS:-} -C target-cpu=${TARGET_CPU}"
export IPHONEOS_DEPLOYMENT_TARGET="${DEPLOYMENT_TARGET}"
export ORCHARD_BENCH_OPT_FLAGS="${OPT_FLAGS}"
export ORCHARD_BENCH_XCODE_VERSION
ORCHARD_BENCH_XCODE_VERSION="$(xcodebuild -version | tr '\n' ' ' | sed 's/ $//')"

rustup target add "${TARGET}"
cargo_args=(
    build
    --manifest-path "${REPO_ROOT}/Cargo.toml"
    --locked
    --release
    --target "${TARGET}"
    -p orchard-ios-benchmark
    --lib
)
if [[ -n "${ORCHARD_IOS_BENCH_FEATURES:-}" ]]; then
    cargo_args+=(--features "${ORCHARD_IOS_BENCH_FEATURES}")
fi
cargo "${cargo_args[@]}"

LIBRARY="${REPO_ROOT}/target/${TARGET}/release/liborchard_ios_benchmark.a"
test -f "${LIBRARY}"
file "${LIBRARY}"
echo "Rust static library: ${LIBRARY}"
