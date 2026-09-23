# Changelog fragments

Every pull request that changes a Rust source file or any `Cargo.toml` owns
exactly one file in this directory. This keeps concurrent work out of the
shared per-crate changelogs — fragments from different PRs can never conflict
or block each other — and makes the unreleased notes reviewable with the
change that introduced them. Other pull requests do not need a fragment.

After opening a draft Rust or `Cargo.toml` PR, create
`docs/changelog/unreleased/<PR-number>.md`. Scope each entry to the crate it
belongs to, using the crate's package name as a section heading and Keep a
Changelog categories beneath it:

```markdown
## zakura-orchard

### Fixed

- Fixed the consumer-visible behavior
  ([#123](https://github.com/zakura-core/common/pull/123)).

## zakura-halo2-proofs

### Added

- Added the new API ([#123](https://github.com/zakura-core/common/pull/123)).
```

Valid categories are `Added`, `Changed`, `Deprecated`, `Removed`, `Fixed`, and
`Security`. Crate headings must be workspace package names (`zakura-*`).
Multiple crates and categories belong in the same fragment. Write complete
Keep a Changelog list items, including the PR link, phrased for a crates.io
consumer of the crate.

For an internal-only Rust or `Cargo.toml` PR, use an explicit marker and
explain the exclusion:

```markdown
<!-- changelog: none -->

This PR only changes tests and has no crate-consumer-visible effect.
```

Run `./scripts/changelog.py check` to validate pending fragments. Release PRs
run `./scripts/changelog.py release vX.Y.Z` after version bumps; that command
folds each fragment's entries into the matching crate's `CHANGELOG.md` and
deletes the consumed fragments. Stable assembly also combines and replaces all
matching pre-release sections (`X.Y.Z-alpha.N`, `X.Y.Z-beta.N`, `X.Y.Z-rc.N`)
with one `X.Y.Z` section.
