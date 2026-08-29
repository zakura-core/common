#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
PACKAGE="${BENCH_ROOT}/artifacts/orchard-ios-xctest.zip"
MODEL="${FIREBASE_IOS_MODEL:-iphone16pro}"
OS_VERSION="${FIREBASE_IOS_VERSION:-18.3}"
LOCAL_GCLOUD="/private/tmp/orchard-gcloud-sdk/google-cloud-sdk/bin/gcloud"
GCLOUD_BIN="${GCLOUD_BIN:-$(command -v gcloud || true)}"

if [[ -z "${GCLOUD_BIN}" && -x "${LOCAL_GCLOUD}" ]]; then
    GCLOUD_BIN="${LOCAL_GCLOUD}"
fi
if [[ -z "${GCLOUD_BIN}" || ! -x "${GCLOUD_BIN}" ]]; then
    echo "Install the Google Cloud CLI, then authenticate with gcloud auth login." >&2
    exit 1
fi
export CLOUDSDK_CONFIG="${CLOUDSDK_CONFIG:-${BENCH_ROOT}/artifacts/gcloud-config}"
mkdir -p "${CLOUDSDK_CONFIG}"

PROJECT_ID="${GOOGLE_CLOUD_PROJECT:-$("${GCLOUD_BIN}" config get-value project 2>/dev/null)}"
if [[ -z "${PROJECT_ID}" || "${PROJECT_ID}" == "(unset)" ]]; then
    echo "Set GOOGLE_CLOUD_PROJECT to a Firebase-enabled Google Cloud project." >&2
    exit 1
fi
if [[ -z "$("${GCLOUD_BIN}" auth list --filter=status:ACTIVE --format='value(account)')" ]]; then
    echo "Authenticate with gcloud auth login or a service account." >&2
    exit 1
fi

"${SCRIPT_DIR}/package-firebase.sh"

"${GCLOUD_BIN}" services enable \
    firebase.googleapis.com \
    testing.googleapis.com \
    toolresults.googleapis.com \
    storage.googleapis.com \
    --project "${PROJECT_ID}"

"${GCLOUD_BIN}" firebase test ios models describe "${MODEL}" \
    --project "${PROJECT_ID}"
"${GCLOUD_BIN}" firebase test ios list-device-capacities \
    --project "${PROJECT_ID}" \
    --filter="modelId=${MODEL} AND versionId=${OS_VERSION}"

RESULTS_BUCKET="${FIREBASE_RESULTS_BUCKET:-${PROJECT_ID}-orchard-ios-benchmark}"
if ! "${GCLOUD_BIN}" storage buckets describe "gs://${RESULTS_BUCKET}" \
    --project "${PROJECT_ID}" >/dev/null 2>&1; then
    "${GCLOUD_BIN}" storage buckets create "gs://${RESULTS_BUCKET}" \
        --project "${PROJECT_ID}" \
        --location=US \
        --uniform-bucket-level-access
fi

COMMIT="$(git -C "${BENCH_ROOT}" rev-parse --short=12 HEAD)"
RUN_STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
RESULTS_DIR="orchard-ios-${COMMIT}-${RUN_STAMP}"
LOCAL_RESULTS="${BENCH_ROOT}/artifacts/cloud/${RESULTS_DIR}"

"${GCLOUD_BIN}" firebase test ios run \
    --project "${PROJECT_ID}" \
    --type=xctest \
    --test "${PACKAGE}" \
    --device "model=${MODEL},version=${OS_VERSION},locale=en,orientation=portrait" \
    --timeout=30m \
    --no-record-video \
    --num-flaky-test-attempts=0 \
    --results-bucket="${RESULTS_BUCKET}" \
    --results-dir="${RESULTS_DIR}" \
    --client-details="matrixLabel=Orchard ${COMMIT}"

mkdir -p "${LOCAL_RESULTS}"
"${GCLOUD_BIN}" storage cp --recursive \
    "gs://${RESULTS_BUCKET}/${RESULTS_DIR}/**" \
    "${LOCAL_RESULTS}"

"${SCRIPT_DIR}/extract-result.sh" \
    "${LOCAL_RESULTS}" \
    "${LOCAL_RESULTS}/orchard-benchmark.json"
