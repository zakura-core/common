#!/usr/bin/env bash
set -euo pipefail
transaction_root=$1
transaction_host=$2
cd "$transaction_root"
mkdir -p results
{
    date -u
    hostname
    uname -sm
    uptime
    . "$HOME/.cargo/env"
    rustc +1.97.1 --version
    cargo +1.97.1 --version
    if [[ $(uname -s) == Darwin ]]; then
        sysctl -n machdep.cpu.brand_string hw.ncpu
        pmset -g therm
        shasum -a256 bin/control bin/inversion
    else
        lscpu
        sha256sum bin/control bin/inversion
    fi
    ps -Ao pid,pcpu,comm | sort -k2 -nr | head -12 || true
} > results/inversion-telemetry-before.txt
transaction_leg=0
for transaction_variant in control inversion inversion control; do
    transaction_leg=$((transaction_leg + 1))
    transaction_label="$transaction_host-t4-$transaction_variant-$transaction_leg"
    date -u
    printf '%s\n' "$transaction_label"
    env RAYON_NUM_THREADS=4 IRONWOOD_K11_PROVER_THREADS=4 \
        "$transaction_root/bin/$transaction_variant" --bench \
        '^ironwood-k11/prove-(2-actions-two-real-spends|[345]-actions)$' \
        --save-baseline "$transaction_label"
done
{
    date -u
    uptime
    if [[ $(uname -s) == Darwin ]]; then pmset -g therm; fi
    ps -Ao pid,pcpu,comm | sort -k2 -nr | head -12 || true
} > results/inversion-telemetry-after.txt
touch inversion-measured
