# SemVer policy

Published crates in this repository follow Semantic Versioning except for
feature removals explicitly recorded in the permanent
[SemVer ignore list](../.github/semver-ignore-list.json). All other API
compatibility failures block CI.

CI enforces this guarantee by running `cargo-semver-checks` against the latest
stable crates.io baseline. To ignore a Cargo feature removal in a minor
release, add the exact package, feature name, and reason to the ignore list.
Add future entries under the same package or a new package object.

For example, the `zakura-primitives/zip-233` entry permits its removal in
`1.3.0` against `1.2.0`. Removing `multicore` still needs its own entry, and
removing `zip-233` in `1.2.1` still fails. The checker decides bump levels,
including for `0.x` versions and prereleases.

Entries are permanent, including if a feature is reintroduced and removed
again. Once the baseline no longer contains the feature, there is nothing to
ignore. Delete an entry to stop ignoring that removal. An empty ignore list is
valid.

[The wrapper](../.github/scripts/check_semver.py) prints the tool version and
streams logs. Only a completed check whose sole failures are feature removals
on the ignore list can pass. Warnings remain visible. Unknown report formats
fail with a separate diagnostic. Inspect the original log before updating the
parser for a new checker format. CI's existing 30-minute job timeout applies.

```sh
python3 .github/scripts/check_semver.py --package zakura-primitives --default-features
python3 .github/scripts/test_check_semver.py
```

For release checks, add `--baseline-version <prev>` and omit
`--default-features` to retain the checker's normal feature selection.
The bare checker does not apply the repository's ignore list.
