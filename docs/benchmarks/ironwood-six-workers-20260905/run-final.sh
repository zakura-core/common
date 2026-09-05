#!/usr/bin/env bash
set -euo pipefail
transaction_root=$1
transaction_host=$2
cd "$transaction_root"
transaction_leg=0
for transaction_variant in control final final control; do
    transaction_leg=$((transaction_leg + 1))
    transaction_label="$transaction_host-t6-$transaction_variant-confirm$transaction_leg"
    date -u
    printf '%s\n' "$transaction_label"
    env RAYON_NUM_THREADS=6 IRONWOOD_K11_PROVER_THREADS=6 \
        "$transaction_root/bin/$transaction_variant" --bench \
        '^ironwood-k11/prove-(2-actions-two-real-spends|[345]-actions)$' \
        --save-baseline "$transaction_label"
done
for transaction_variant in control final; do
    transaction_label="$transaction_host-t6-$transaction_variant-first"
    date -u
    printf '%s\n' "$transaction_label"
    env RAYON_NUM_THREADS=6 IRONWOOD_K11_PROVER_THREADS=6 \
        "$transaction_root/bin/$transaction_variant" --bench \
        '^ironwood-k11-first-after-build-and-prepare/prove-(2-actions-two-real-spends|5-actions)$' \
        --save-baseline "$transaction_label"
done
{
    date -u
    hostname
    uptime
    if [[ $(uname -s) == Darwin ]]; then
        pmset -g therm
        shasum -a256 bin/control bin/final
    else
        sha256sum bin/control bin/final
    fi
    ps -Ao pid,pcpu,comm | sort -k2 -nr | head -12 || true
} > results/final-telemetry-after.txt
touch final-measured
