#!/usr/bin/env bash

set -uo pipefail

if (( $# != 3 )); then
  echo "usage: $0 PACKAGES DENY_WARNINGS RUN_TESTS" >&2
  exit 2
fi

read -r -a packages <<< "$1"
deny_warnings=$2
run_tests=$3

if (( ${#packages[@]} == 0 )); then
  echo "at least one package is required" >&2
  exit 2
fi
for value in "$deny_warnings" "$run_tests"; do
  if [[ "$value" != true && "$value" != false ]]; then
    echo "boolean arguments must be true or false" >&2
    exit 2
  fi
done

package_args=()
for package in "${packages[@]}"; do
  package_args+=(--package "$package")
done

if ! features=$(python3 .github/scripts/supported_features.py "${packages[@]}"); then
  exit 1
fi
feature_args=()
if [[ -n "$features" ]]; then
  feature_args=(--features "$features")
fi

status=0
run_check() {
  local label=$1
  shift

  echo "::group::$label"
  if ! "$@"; then
    status=1
  fi
  echo "::endgroup::"
}

run_check "Stable supported-feature check" \
  cargo +stable check --locked "${feature_args[@]}" --all-targets \
  "${package_args[@]}"

lint_args=()
if [[ "$deny_warnings" == true ]]; then
  lint_args+=(-- -D warnings)
fi
run_check "Stable Clippy" \
  cargo +stable clippy --locked "${feature_args[@]}" --all-targets --no-deps \
  "${package_args[@]}" "${lint_args[@]}"

if [[ "$run_tests" == true ]]; then
  run_check "Stable tests" cargo +stable test --locked "${package_args[@]}"
fi

run_check "MSRV check" \
  cargo +1.97.0 check --locked "${package_args[@]}"

exit "$status"
