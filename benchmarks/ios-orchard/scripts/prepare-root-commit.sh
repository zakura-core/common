#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
ROOT_COMMIT="16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b"
HISTORY_ROOT="${ORCHARD_IOS_HISTORY_WORKTREE:-/private/tmp/libraries-ios-orchard-root-16d18d2}"
HISTORY_BENCH="${HISTORY_ROOT}/benchmarks/ios-orchard"

if [[ -e "${HISTORY_ROOT}" ]]; then
    actual_commit="$(git -C "${HISTORY_ROOT}" rev-parse HEAD)"
    if [[ "${actual_commit}" != "${ROOT_COMMIT}" ]]; then
        echo "Historical worktree has unexpected commit: ${actual_commit}" >&2
        exit 1
    fi
else
    git -C "${REPO_ROOT}" worktree add --detach \
        "${HISTORY_ROOT}" "${ROOT_COMMIT}"
fi

mkdir -p "${HISTORY_BENCH}"
rsync -a \
    --exclude artifacts \
    --exclude .DS_Store \
    "${BENCH_ROOT}/" "${HISTORY_BENCH}/"

if ! rg -q '"benchmarks/ios-orchard"' "${HISTORY_ROOT}/Cargo.toml"; then
    sed -i '' '/members = \[/a\
    "benchmarks/ios-orchard",\
' "${HISTORY_ROOT}/Cargo.toml"
fi

sed -i '' \
    's/orchard = { package = "zakura-orchard", /orchard = { /' \
    "${HISTORY_BENCH}/Cargo.toml"
sed -i '' \
    's/rand = { version = "0.10"/rand = { version = "0.8"/' \
    "${HISTORY_BENCH}/Cargo.toml"

RUSTUP_TOOLCHAIN="${ORCHARD_IOS_HISTORY_TOOLCHAIN:-1.98.0}" \
    cargo metadata \
        --manifest-path "${HISTORY_ROOT}/Cargo.toml" \
        --format-version 1 >/dev/null

echo "Historical benchmark worktree: ${HISTORY_ROOT}"
