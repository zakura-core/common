#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
PRODUCTS="${BENCH_ROOT}/artifacts/DerivedData/Build/Products"
PACKAGE="${BENCH_ROOT}/artifacts/orchard-ios-xctest.zip"
TEMP_DIR="$(mktemp -d)"
trap 'rm -rf "${TEMP_DIR}"' EXIT

"${SCRIPT_DIR}/build-xctest.sh"

XCTESTRUN_COUNT="$(find "${PRODUCTS}" -maxdepth 1 -name '*.xctestrun' | wc -l | tr -d ' ')"
if [[ "${XCTESTRUN_COUNT}" -ne 1 ]]; then
    echo "Expected exactly one .xctestrun file in ${PRODUCTS}" >&2
    exit 1
fi

XCTESTRUN_FILE="$(find "${PRODUCTS}" -maxdepth 1 -name '*.xctestrun' -print -quit)"
XCTESTRUN_NAME="$(basename "${XCTESTRUN_FILE}")"
(
    cd "${PRODUCTS}"
    zip -qry "${TEMP_DIR}/orchard-ios-xctest.zip" \
        Release-iphoneos \
        "${XCTESTRUN_NAME}"
)
mkdir -p "$(dirname "${PACKAGE}")"
mv -f "${TEMP_DIR}/orchard-ios-xctest.zip" "${PACKAGE}"

shasum -a 256 "${PACKAGE}"
unzip -l "${PACKAGE}"
echo "Firebase XCTest package: ${PACKAGE}"
