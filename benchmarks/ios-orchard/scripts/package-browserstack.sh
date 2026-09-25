#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
PRODUCTS="${BENCH_ROOT}/artifacts/DerivedData/Build/Products"
PACKAGE="${BENCH_ROOT}/artifacts/orchard-browserstack-xctestrun.zip"
TEMP_DIR="$(mktemp -d)"
trap 'rm -rf "${TEMP_DIR}"' EXIT

"${SCRIPT_DIR}/build-xctest.sh"

app="${PRODUCTS}/Release-iphoneos/OrchardBenchmark.app"
xctestrun="$(find "${PRODUCTS}" -maxdepth 1 -name '*.xctestrun' -print -quit)"
test -d "${app}"
test -f "${xctestrun}"

is_hosted="$(plutil -extract OrchardBenchmarkTests.IsAppHostedTestBundle raw \
    -o - "${xctestrun}")"
if [[ "${is_hosted}" != "true" ]]; then
    echo "Expected an app-hosted XCTest bundle." >&2
    exit 1
fi

mkdir -p "${TEMP_DIR}/Release-iphoneos"
/bin/cp -R "${app}" "${TEMP_DIR}/Release-iphoneos/"
/bin/cp "${xctestrun}" "${TEMP_DIR}/"
(
    cd "${TEMP_DIR}"
    zip -qry "${PACKAGE}" \
        Release-iphoneos/OrchardBenchmark.app \
        "$(basename "${xctestrun}")"
)

shasum -a 256 "${PACKAGE}"
echo "BrowserStack XCTest package: ${PACKAGE}"
