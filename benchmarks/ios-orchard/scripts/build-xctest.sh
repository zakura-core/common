#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
DERIVED_DATA="${BENCH_ROOT}/artifacts/DerivedData"
PROJECT="${BENCH_ROOT}/ios/OrchardBenchmark.xcodeproj"

"${SCRIPT_DIR}/build-rust.sh"

xcodebuild \
    -project "${PROJECT}" \
    -scheme OrchardBenchmark \
    -configuration Release \
    -sdk iphoneos \
    -destination 'generic/platform=iOS' \
    -derivedDataPath "${DERIVED_DATA}" \
    CODE_SIGNING_ALLOWED=NO \
    build-for-testing

PRODUCTS="${DERIVED_DATA}/Build/Products"
APP="${PRODUCTS}/Release-iphoneos/OrchardBenchmark.app"
TEST_BUNDLE="${APP}/PlugIns/OrchardBenchmarkTests.xctest"

test -d "${APP}"
test -d "${TEST_BUNDLE}"

# Firebase re-signs uploaded iOS test products. Ad-hoc signing first makes the
# package structurally signed and locally verifiable without requiring a
# developer certificate or provisioning profile on the build host.
codesign --force --sign - --timestamp=none "${TEST_BUNDLE}"
codesign --force --sign - --timestamp=none "${APP}"
codesign --verify --deep --strict --verbose=2 "${APP}"
codesign --verify --deep --strict --verbose=2 "${TEST_BUNDLE}"

file "${APP}/OrchardBenchmark"
file "${TEST_BUNDLE}/OrchardBenchmarkTests"
find "${PRODUCTS}" -maxdepth 1 -name '*.xctestrun' -print
echo "Release XCTest products: ${PRODUCTS}"
