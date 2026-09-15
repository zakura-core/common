#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
PACKAGE="${BENCH_ROOT}/artifacts/orchard-browserstack-xctestrun.zip"
DEVICE="${BROWSERSTACK_IOS_DEVICE:-iPhone 17 Pro-26}"
API_ROOT="https://api-cloud.browserstack.com/app-automate/xcuitest/v2"

if [[ -z "${BROWSERSTACK_USERNAME:-}" || -z "${BROWSERSTACK_ACCESS_KEY:-}" ]]; then
    if [[ ! -t 0 ]]; then
        echo "Set BROWSERSTACK_USERNAME and BROWSERSTACK_ACCESS_KEY." >&2
        exit 1
    fi
    read -r -p "BrowserStack username: " BROWSERSTACK_USERNAME
    read -r -s -p "BrowserStack access key: " BROWSERSTACK_ACCESS_KEY
    echo
    export BROWSERSTACK_USERNAME BROWSERSTACK_ACCESS_KEY
fi

"${SCRIPT_DIR}/package-browserstack.sh"

upload_response="$(curl --silent --show-error \
    --user "${BROWSERSTACK_USERNAME}:${BROWSERSTACK_ACCESS_KEY}" \
    --request POST \
    "${API_ROOT}/test-suite" \
    --form "file=@${PACKAGE}" \
    --form "custom_id=orchard-ios-benchmark")"
if ! test_suite_url="$(jq --exit-status --raw-output \
    '.test_suite_url // .test_url' <<<"${upload_response}")"; then
    echo "BrowserStack test-suite upload failed:" >&2
    jq . <<<"${upload_response}" >&2 || echo "${upload_response}" >&2
    exit 1
fi

commit="$(git -C "${BENCH_ROOT}" rev-parse --short=12 HEAD)"
request="$(jq --null-input \
    --arg device "${DEVICE}" \
    --arg suite "${test_suite_url}" \
    --arg project "Orchard prover ${commit}" \
    '{
        devices: [$device],
        testSuite: $suite,
        project: $project,
        singleRunnerInvocation: true,
        enableResultBundle: true
    }')"
build_response="$(curl --silent --show-error \
    --user "${BROWSERSTACK_USERNAME}:${BROWSERSTACK_ACCESS_KEY}" \
    --request POST \
    "${API_ROOT}/xctestrun-build" \
    --header 'Content-Type: application/json' \
    --data "${request}")"
if ! build_id="$(jq --exit-status --raw-output \
    '.build_id' <<<"${build_response}")"; then
    echo "BrowserStack build creation failed:" >&2
    jq . <<<"${build_response}" >&2 || echo "${build_response}" >&2
    exit 1
fi
results="${BENCH_ROOT}/artifacts/browserstack/${build_id}"
mkdir -p "${results}"
printf '%s\n' "${build_response}" >"${results}/build-response.json"

echo "BrowserStack build: ${build_id}"
echo "Device: ${DEVICE}"

while true; do
    status_response="$(curl --fail --silent --show-error \
        --user "${BROWSERSTACK_USERNAME}:${BROWSERSTACK_ACCESS_KEY}" \
        "${API_ROOT}/builds/${build_id}")"
    status="$(jq --raw-output '.status // "unknown"' \
        <<<"${status_response}" | tr '[:upper:]' '[:lower:]')"
    echo "BrowserStack status: ${status}"
    case "${status}" in
        passed|failed|error|timedout|timed_out|skipped)
            break
            ;;
        queued|running|unknown)
            sleep 15
            ;;
        *)
            echo "Unexpected BrowserStack status: ${status}" >&2
            exit 1
            ;;
    esac
done
printf '%s\n' "${status_response}" >"${results}/build-status.json"

session_id="$(jq --exit-status --raw-output \
    '[.devices[].sessions[].id][0]' <<<"${status_response}")"
result_zip="${results}/result-bundle.zip"
curl --fail --silent --show-error \
    --user "${BROWSERSTACK_USERNAME}:${BROWSERSTACK_ACCESS_KEY}" \
    "${API_ROOT}/builds/${build_id}/sessions/${session_id}/resultbundle" \
    --output "${result_zip}"
ditto -x -k "${result_zip}" "${results}/result-bundle"

"${SCRIPT_DIR}/extract-result.sh" \
    "${results}/result-bundle" \
    "${results}/orchard-benchmark.json"

if [[ "${status}" != "passed" ]]; then
    echo "BrowserStack build finished with status: ${status}" >&2
    exit 1
fi

echo "BrowserStack result: ${results}/orchard-benchmark.json"
