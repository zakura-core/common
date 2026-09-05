#!/usr/bin/env bash
set -euo pipefail
transaction_root=$1
transaction_variant=$2
. "$HOME/.cargo/env"
cd "$transaction_root"
mkdir -p "$transaction_variant" bin
tar -xzf "$transaction_variant.tar.gz" -C "$transaction_variant"
cd "$transaction_variant"
env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
    CARGO_TARGET_DIR="$transaction_root/target/$transaction_variant" \
    cargo +1.97.1 bench --locked -j 4 -p zakura-orchard --features circuit \
    --bench ironwood_k11_prover --no-run --message-format=json \
    > "$transaction_root/$transaction_variant-build.jsonl"
transaction_binary=$(sed -n '/"name":"ironwood_k11_prover"/s/.*"executable":"\([^"]*\)".*/\1/p' \
    "$transaction_root/$transaction_variant-build.jsonl" | tail -1)
test -x "$transaction_binary"
cp "$transaction_binary" "$transaction_root/bin/$transaction_variant"
touch "$transaction_root/$transaction_variant-built"
