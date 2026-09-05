#!/usr/bin/env bash
set -euo pipefail
transaction_root=$1
transaction_host=$2
cd "$transaction_root"
mkdir -p results
telemetry() {
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
        shasum -a256 bin/*
    else
        lscpu
        sha256sum bin/*
    fi
    ps -Ao pid,pcpu,comm | sort -k2 -nr | head -12 || true
}
telemetry > results/six-telemetry-before.txt
transaction_leg=0
for transaction_variant in control inversion lazy planned configured streamed control; do
    transaction_leg=$((transaction_leg + 1))
    transaction_label="$transaction_host-t6-$transaction_variant-screen$transaction_leg"
    date -u
    printf '%s\n' "$transaction_label"
    env RAYON_NUM_THREADS=6 IRONWOOD_K11_PROVER_THREADS=6 \
        "$transaction_root/bin/$transaction_variant" --bench \
        '^ironwood-k11/prove-(2-actions-two-real-spends|[345]-actions)$' \
        --save-baseline "$transaction_label"
done
telemetry > results/six-telemetry-after.txt
touch six-measured
