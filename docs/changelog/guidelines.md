# Changelog Guidelines

How and when to update the changelogs in this repository.

## Which file records what

| File | Records | Audience |
| --- | --- | --- |
| `docs/changelog/unreleased/<PR>.md` | Unreleased entries owned by one PR | Reviewers and release tooling |
| `crates/<name>/CHANGELOG.md` | That crate's released public-API history | crates.io consumers of the crate |

Each crate's `CHANGELOG.md` ships inside its published package. Entries
describe the crate's public API and observable behavior from a consumer's
perspective; internal implementation details, refactors, and CI changes live
in commit messages and pull requests instead.

## Per-crate changelog structure

Each `crates/<name>/CHANGELOG.md` contains, in order:

1. A fixed header identifying the Keep a Changelog format and the
   public-API-only entry policy.
2. An `## [Unreleased]` heading, normally with an empty body — pending entries
   live in fragments, not here.
3. `## [x.y.z] - YYYY-MM-DD` sections, newest first.
4. For a crate that began as a fork: a `## Record of Fork` section at the
   end of the file — the permanent provenance record. It names the crate and
   version the code was forked from, links that repository and the exact
   commit (taken from the `.cargo_vcs_info.json` of the published artifact
   that was vendored), and records the commit in this repository that
   imported the code. For the crates that were ported between dependency
   stacks at import time, the record says so.

A forked crate's version lineage restarts at `1.0.0`; it does not continue
the original numbering, and these files intentionally do not reproduce
pre-fork release history (the repository the code was forked from remains the
record for that).

## The 1.0.0 baseline ("Initial release")

`1.0.0` is each crate's first release from this repository, cut at the fork
point, so there are no earlier releases to describe deltas against:

- Until `1.0.0` ships, the fragment requirement is inactive. The initial
  entries — a reconstruction of the public differences between the fork
  point and the `1.0.0` crate (see "Initial 1.0.0 entries" below) — are curated
  directly in each crate's `## [Unreleased]` body; the stable assembly turns
  them into the dated `## [1.0.0]` section at release.
- The `1.0.0-rc*` release candidates are pre-releases of `1.0.0` and never get
  their own entries or sections.

After `1.0.0`, normal fragment-based maintenance (everything below) applies.

## One fragment per Rust pull request

PRs that change a Rust source file or any `Cargo.toml` do not edit the shared
per-crate changelogs. After opening a draft PR, add exactly one
`docs/changelog/unreleased/<PR-number>.md` file. Keeping each PR in its own
file avoids merge conflicts while preserving the link between the change, its
review, and its release note. Other PRs do not need a fragment.

A fragment scopes entries to crates by package name, with Keep a Changelog
categories beneath each crate heading; internal-only PRs use the explicit
`<!-- changelog: none -->` marker with a reason. The concise format reference
is in [`unreleased/README.md`](unreleased/README.md).

Dependabot PRs and release PRs are automated exceptions to the one-file check:
Dependabot is exempt, and release PRs (labeled `A-release`) must instead
consume every pending fragment.

Run `./scripts/changelog.py check` locally. CI validates the syntax, checks
the fragment filename matches the PR number, verifies crate headings name real
workspace members, and keeps the provenance records intact.

## Writing entries

- Categories: `### Added`, `### Changed`, `### Deprecated`, `### Removed`,
  `### Fixed`, `### Security`. Prefer `Fixed` if you're not sure.
- Write for a crates.io consumer of the crate: describe the observable effect,
  not the implementation. Start each item with a verb and link the PR, for
  example
  `- Fixed X so that Y ([#123](https://github.com/zakura-core/common/pull/123)).`
- Performance changes worth a consumer's attention get one line describing the
  visible effect, not the technique.
- Security entries must not describe an undisclosed or unfixed vulnerability;
  coordinate timing with the disclosure process.

## Release assembly

After the workspace version is bumped on the release branch, run:

```sh
./scripts/changelog.py release vX.Y.Z
```

The command validates and consumes all pending fragments, merges their entries
by crate and category with any hand-written `Unreleased` bodies, and creates a
new version section in each affected crate's changelog. Crates with no entries
for the release are left untouched. Review and commit the generated changelogs
and fragment deletions.

Pre-releases (`X.Y.Z-alpha.N`, `X.Y.Z-beta.N`, `X.Y.Z-rc.N`) get temporary
version sections. When the matching stable version is assembled, the tool
combines those sections from oldest to newest with any later unreleased
entries, removes the pre-release sections, and creates one stable section per
crate.

`./scripts/changelog.py release vX.Y.Z --check` fails if fragments remain or
the assembled changelogs were not committed; release PRs must contain no
pending fragment files.

## Initial 1.0.0 entries

The entries held in each crate's `## [Unreleased]` body until `1.0.0` is
assembled describe the public differences between the fork point and the
released `1.0.0` crate, reconstructed as follows:

1. For each crate, diff the current source against the original artifact
   recorded in its `## Record of Fork` section
   (`https://static.crates.io/crates/<name>/<name>-<version>.crate`).
2. Catalog only consumer-visible differences, in roughly this order: the crate
   rename (`package = "zakura-*"`; library target names and therefore `use`
   paths are unchanged); dependency major versions that appear in public
   signatures (the `ff`/`group` 0.14 stack, `rand_core` 0.10, the
   in-workspace replacements of `bellman`/`bls12_381`/`jubjub`/`pairing`/…);
   added, removed, or changed public items and trait implementations; added or
   removed cargo features and changed feature defaults; MSRV (1.91) and
   edition (2024); behavioral changes observable through the same API.
3. Phrase entries for someone adapting code from the original crate to this
   crate, not for someone reviewing our development history.
