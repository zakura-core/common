# Image for Anthropic's OSS Scanner (https://red.anthropic.com/oss-scanner/), which
# enrolls this repository as projects/zakura-common in https://github.com/anthropics/oss-scanner.
#
# The scanner builds this file with the repository checkout as the build context and
# with network access, then audits the result with no network at all. So this build
# installs the toolchain, fetches every crate, and compiles the workspace's test
# binaries in the configurations CI tests, leaving `cargo` able to work offline.
# .oss-scanner/threat_model.md says what matters and how to run things.

# The Rust release rust-toolchain.toml pins for development. The digest pins the
# bytes the scanner builds from: the tag stays a tag, and Docker Hub re-publishes
# `1.97.1-bookworm` when Debian ships a point release. Refresh with
#   docker buildx imagetools inspect rust:1.97.1-bookworm --format '{{.Manifest.Digest}}'
# Dependabot's docker entry in .github/dependabot.yml proposes the refresh.
FROM rust:1.99.0-bookworm@sha256:114c7a4425406451c2866b6aafe69fe29b1b298832db1277d411ac73c82d04d6
ENV DEBIAN_FRONTEND=noninteractive

# libfontconfig1-dev is for halo2's dev-graph feature (plotters). python3 runs
# .github/scripts/supported_features.py, which CI uses to pick each crate's features.
RUN apt-get update && apt-get install -y --no-install-recommends \
      libfontconfig1-dev pkg-config python3 \
    && rm -rf /var/lib/apt/lists/*

# scanner contract: the checkout lives inside the image, at /src
COPY . /src
WORKDIR /src

# The image's toolchain is the one rust-toolchain.toml pins; RUSTUP_TOOLCHAIN makes
# rustup use it rather than look for a download. Clippy and rustfmt are the components
# rust-toolchain.toml asks for. Debug info and frame pointers are for debuggers and
# profilers; the test profile already optimizes the arithmetic crates (see Cargo.toml).
ENV RUSTUP_TOOLCHAIN=1.97.1 \
    CARGO_INCREMENTAL=0 \
    CARGO_PROFILE_RELEASE_DEBUG=limited \
    RUSTFLAGS="-C force-frame-pointers=yes"
RUN rustup component add clippy rustfmt

# Every crate in Cargo.lock, for every target and feature, so that builds with other
# features than the ones below also work offline.
RUN cargo fetch --locked

# Compile the test binaries in each configuration CI tests (.github/workflows/ci.yml),
# without running them. Running them is `cargo test` with the same arguments.
RUN cargo test --locked --no-run -p zakura-equihash --all-features
RUN cargo test --locked --no-run -p zakura-orchard
RUN cargo test --locked --no-run -p zakura-orchard \
      --no-default-features --features backend-halo2 --features circuit,multicore,wallet
RUN cargo test --locked --no-run --release \
      -p zakura-halo2-gadgets -p zakura-halo2-poseidon -p zakura-halo2-proofs \
      --no-default-features --features batch,dev-graph,gadget-traces,test-dependencies,orbits
RUN cargo test --locked --no-run \
      -p zakura-pairing -p zakura-bls12-381 -p zakura-jubjub -p zakura-bellman -p zakura-sapling-crypto \
      --all-features
RUN cargo test --locked --no-run -p zakura-sapling-crypto \
      --no-default-features --features circuit,multicore,wallet --release
RUN cargo test --locked --no-run \
      -p zakura-address -p zakura-keys -p zakura-primitives -p zakura-protocol \
      -p zakura-proofs -p zakura-transparent -p zakura-zip321 \
      --features "$(python3 .github/scripts/supported_features.py zakura-address zakura-keys zakura-primitives zakura-protocol zakura-proofs zakura-transparent zakura-zip321)"
RUN cargo test --locked --no-run -p zakura-pasta-curves --all-features
RUN cargo test --locked --no-run -p zakura-reddsa -p zakura-reddsa-frost \
      --features nightly,serde,thiserror,zeroize
RUN cargo test --locked --no-run -p zakura-redjubjub --all-features
RUN cargo test --locked --no-run \
      -p zakura-sinsemilla -p zakura-note-encryption -p zakura-halo2-legacy-pdqsort \
      --features "$(python3 .github/scripts/supported_features.py zakura-sinsemilla zakura-note-encryption zakura-halo2-legacy-pdqsort)"
RUN cargo test --locked --no-run \
      -p zakura-bento-core -p zakura-bento-macros -p zakura-bento -p zakura-udon --all-features

# Run the cheap tests so the image is known to work, but do not let a failing test abort
# the build.
RUN (timeout 900 cargo test --locked -p zakura-equihash -p zakura-pasta-curves --all-features \
     || echo "WARNING: tests reported failures")

# Everything is fetched: from here on cargo never tries the network.
ENV CARGO_NET_OFFLINE=true
