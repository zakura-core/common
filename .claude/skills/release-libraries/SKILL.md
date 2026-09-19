---
name: release-libraries
description: >-
  Prepare and validate a coordinated release of the zakura-* library crates.
  Use when bumping the workspace version, assembling changelogs for a release,
  preparing a release PR, or publishing the crates to crates.io.
---

# Release the Zakura Common libraries

The 17 crates version in lockstep from `[workspace.package]` in the root
`Cargo.toml`. Changelog policy is canonical in `docs/changelog/guidelines.md`;
this skill adds the mechanics that are easy to miss.

## Safety

- Preparing or reviewing a release does not authorize publishing it. Get
  explicit confirmation immediately before `cargo publish`.
- Publish only from a merged, green `main`.

## Version bump

1. `version` in `[workspace.package]` — every crate inherits it.
2. The intra-workspace `version = "..."` requirements in
   `[workspace.dependencies]` (same file, one place).
3. `cargo metadata --locked` must still succeed and `Cargo.lock` should show
   only the 17 member version lines changing.

## Changelog assembly

After the version bump, on the release branch:

```sh
./scripts/changelog.py release vX.Y.Z
```

This folds every pending `docs/changelog/unreleased/<PR>.md` fragment into the
matching crates' `CHANGELOG.md` version sections and deletes the fragments;
when assembling a stable `X.Y.Z` it also collapses any `X.Y.Z-rc*` sections
into the stable section. Review and commit the result. The gate form is:

```sh
./scripts/changelog.py release vX.Y.Z --check
```

which fails while fragments remain or assembled changelogs are uncommitted.
Label the release PR `A-release`: the changelog CI check then requires zero
pending fragments instead of a PR-owned fragment.

## Pre-publish checks

- Full suite: `cargo test --release --workspace --all-features --locked`.
- Docs as docs.rs will build them:
  `RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --workspace --no-deps --all-features --locked`.
- Package contents: `cargo package --list -p <crate>` for each crate — no
  stray files; LICENSE/COPYRIGHT/katex symlinks materialize as real files.
- Semver: use the [semver policy](../../../docs/semver-policy.md), including
  approved feature removals. For a release, run
  `python3 .github/scripts/check_semver.py --baseline-version <prev> --package <crate>`.
  This keeps the checker's normal feature selection. Add `--default-features`
  to reproduce CI. The bare checker reports compatibility findings without
  applying the repository's exceptions.

## Publishing

`cargo package`/`cargo publish` resolve the version-stripped path
dependencies against crates.io, so a crate cannot even be packaged until its
workspace dependencies are published at the new version. Publish bottom-up:

1. `zakura-halo2-legacy-pdqsort`, `zakura-pairing`, `zakura-pasta-curves`
2. `zakura-bls12-381`, `zakura-jubjub`
3. `zakura-bellman`, `zakura-reddsa`, `zakura-sinsemilla`,
   `zakura-halo2-poseidon`, then `zakura-halo2-proofs`,
   `zakura-halo2-gadgets`
4. `zakura-redjubjub`, `zakura-sapling-crypto`, `zakura-orchard`
5. `zakura-keys`, `zakura-primitives`, `zakura-proofs`

Verify each publish is visible on crates.io before publishing its dependents.
