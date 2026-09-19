# Semver policy

CI checks public API compatibility against the latest stable crates.io release
selected by `cargo-semver-checks`. Normal version-bump requirements still apply.

## Accepted feature removals

To accept removing a Cargo feature in a minor release, add its exact package
name, feature name, and reason to
[the feature removal allowlist](../.github/semver-feature-removals.json):

```json
{
  "zakura-primitives": {
    "zip-233": "Accepted for a minor release in #458. Removed an unused feature."
  }
}
```

Add more feature entries under the same package, or another package object, as
needed. Entries are permanent. Once a published baseline no longer contains a
feature, its entry has nothing to exempt and does not need to be removed.

For example, removing `zip-233` in `1.3.0` passes against `1.2.0`. Removing
`multicore` at the same time still fails unless it has its own accepted entry.
Removing `zip-233` in `1.2.1` also fails because the exception requires a minor
bump. The checker decides what counts as a minor bump, including for `0.x`
versions and prereleases.

The exception only covers the removed feature name. It does not exempt removed
functions, fields, or other API changes reported by the checker. CI continues
to check default features, so this is not a guarantee about all optional APIs.
Keep consumer migration instructions in the normal release notes.

## Implementation

[The wrapper](../.github/scripts/check_semver.py) runs the original command,
preserves its output, and accepts a semver failure only when every reported
removal is allowed for that package and the checker identifies a minor bump.
It does not change package manifests, the baseline, or enabled features.

The tool currently has no stable structured diagnostics interface. The wrapper
therefore checks the complete feature-removal report, including the failure
count and summary. An unrecognized report format, an additional failure, or a
tool error still fails CI. If a tool update changes this format, update the
parser and its regression tests after inspecting the original log.

Run a package check and the policy tests with:

```sh
python3 .github/scripts/check_semver.py --package zakura-primitives
python3 .github/scripts/test_check_semver.py
python3 .github/scripts/test_affected_semver_packages.py
```
