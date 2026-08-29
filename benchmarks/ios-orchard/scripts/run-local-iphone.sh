#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
PROJECT="${BENCH_ROOT}/ios/OrchardBenchmark.xcodeproj"
DERIVED_DATA="${BENCH_ROOT}/artifacts/LocalDerivedData"

if [[ -z "${DEVELOPMENT_TEAM:-}" ]]; then
    echo "Set DEVELOPMENT_TEAM to your Apple development team ID." >&2
    exit 1
fi

device_id="${IOS_DEVICE_ID:-}"
if [[ -z "${device_id}" ]]; then
    device_ids="$(xcrun devicectl list devices \
        --filter "hardwareProperties.platform == 'iOS'" \
        --columns UDID \
        --hide-default-columns \
        --hide-headers \
        --timeout 30)"
    device_count="$(wc -w <<<"${device_ids}" | tr -d ' ')"
    if [[ "${device_count}" -ne 1 ]]; then
        echo "Expected one connected iPhone; found ${device_count}." >&2
        echo "Set IOS_DEVICE_ID when more than one device is paired." >&2
        xcrun devicectl list devices >&2 || true
        exit 1
    fi
    device_id="${device_ids}"
fi

run_stamp="$(date -u +%Y%m%dT%H%M%SZ)"
result_base="${ORCHARD_IOS_RESULT_BASE:-${BENCH_ROOT}/artifacts/local}"
result_root="${result_base}/${run_stamp}"
result_bundle="${result_root}/OrchardBenchmark.xcresult"
mkdir -p "${result_root}"

"${SCRIPT_DIR}/build-rust.sh"

xcodebuild \
    -project "${PROJECT}" \
    -scheme OrchardBenchmark \
    -configuration Release \
    -destination "platform=iOS,id=${device_id}" \
    -destination-timeout 120 \
    -derivedDataPath "${DERIVED_DATA}" \
    -resultBundlePath "${result_bundle}" \
    -parallel-testing-enabled NO \
    -only-testing:OrchardBenchmarkTests/OrchardBenchmarkTests/testTwoActionProver \
    -allowProvisioningUpdates \
    -allowProvisioningDeviceRegistration \
    DEVELOPMENT_TEAM="${DEVELOPMENT_TEAM}" \
    CODE_SIGN_STYLE=Automatic \
    CODE_SIGNING_ALLOWED=YES \
    test

"${SCRIPT_DIR}/extract-result.sh" \
    "${result_bundle}" \
    "${result_root}/orchard-benchmark.json"

echo "Local iPhone result: ${result_root}/orchard-benchmark.json"
