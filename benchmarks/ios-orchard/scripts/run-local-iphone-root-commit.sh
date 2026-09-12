#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCH_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
ROOT_COMMIT="16d18d2a43d0aecdfcf9e9d02469c16ebf20e50b"
HISTORY_ROOT="${ORCHARD_IOS_HISTORY_WORKTREE:-/private/tmp/libraries-ios-orchard-root-16d18d2}"

"${SCRIPT_DIR}/prepare-root-commit.sh"

export ORCHARD_IOS_BENCH_FEATURES=historical-root
export ORCHARD_IOS_RESULT_BASE="${BENCH_ROOT}/artifacts/history/${ROOT_COMMIT}"
export RUSTUP_TOOLCHAIN="${ORCHARD_IOS_HISTORY_TOOLCHAIN:-1.98.0}"

"${HISTORY_ROOT}/benchmarks/ios-orchard/scripts/run-local-iphone.sh"
