#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 2 ]]; then
    echo "usage: $0 DOWNLOADED_RESULTS OUTPUT_JSON" >&2
    exit 2
fi

RESULTS="$1"
OUTPUT="$2"
TEMP_DIR="$(mktemp -d)"
trap 'rm -rf "${TEMP_DIR}"' EXIT

mkdir -p "$(dirname "${OUTPUT}")"

attachment="$(find "${RESULTS}" -type f -name 'orchard-benchmark.json' -print -quit)"
if [[ -z "${attachment}" ]]; then
    while IFS= read -r -d '' result_bundle; do
        export_dir="${TEMP_DIR}/$(basename "${result_bundle}")-attachments"
        xcrun xcresulttool export attachments \
            --path "${result_bundle}" \
            --output-path "${export_dir}" >/dev/null
    done < <(find "${RESULTS}" -type d -name '*.xcresult' -print0)
    attachment="$(find "${TEMP_DIR}" -type f -name 'orchard-benchmark.json' -print -quit)"
    if [[ -z "${attachment}" ]]; then
        while IFS= read -r -d '' manifest; do
            exported_name="$(jq -r '
                [.[].attachments[]
                    | select(.suggestedHumanReadableName
                        | startswith("orchard-benchmark"))
                    | .exportedFileName][0] // empty
            ' "${manifest}")"
            if [[ -n "${exported_name}" ]]; then
                attachment="$(dirname "${manifest}")/${exported_name}"
                break
            fi
        done < <(find "${TEMP_DIR}" -type f -name 'manifest.json' -print0)
    fi
fi

if [[ -n "${attachment}" ]]; then
    cp "${attachment}" "${OUTPUT}"
else
    line="$(rg -a --no-line-number --only-matching \
        'ORCHARD_BENCHMARK_JSON=\{.*\}' "${RESULTS}" | tail -1 || true)"
    if [[ -z "${line}" ]]; then
        echo "No Orchard benchmark JSON found under ${RESULTS}" >&2
        exit 1
    fi
    printf '%s\n' "${line#*ORCHARD_BENCHMARK_JSON=}" >"${OUTPUT}"
fi

jq . "${OUTPUT}"
echo "Benchmark JSON: ${OUTPUT}"
