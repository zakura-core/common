#!/usr/bin/env bash
set -euo pipefail
transaction_root=$1
transaction_host=$2
cd "$transaction_root"
transaction_leg=0
for transaction_variant in inversion lazy lazy inversion; do
    transaction_leg=$((transaction_leg + 1))
    transaction_label="$transaction_host-t4-$transaction_variant-lazy$transaction_leg"
    date -u
    printf '%s\n' "$transaction_label"
    env RAYON_NUM_THREADS=4 IRONWOOD_K11_PROVER_THREADS=4 \
        "$transaction_root/bin/$transaction_variant" --bench \
        '^ironwood-k11/prove-(2-actions-two-real-spends|[345]-actions)$' \
        --save-baseline "$transaction_label"
done
touch lazy-measured
