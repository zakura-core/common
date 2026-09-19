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
    "zip-233": "Minor-release exception approved in #465 for the unused feature removed in #458."
  }
}
```

Add more feature entries under the same package, or another package object, as
needed. Entries are permanent. Once a published baseline no longer contains a
feature, its entry has nothing to exempt and does not need to be removed.
An entry also covers a later removal if that feature name is reintroduced.
To deliberately revoke an exception, remove the entry. Empty package objects
and an empty allowlist are valid.

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

[The wrapper](../.github/scripts/check_semver.py) prints the tool version,
streams its output, and accepts a semver failure only when every reported
removal is allowed for that package and the checker identifies a minor bump.
Warning sections remain visible and do not block an approved removal.
Unexpected UTF-8 bytes are replaced so the surrounding log is preserved.
Checks have a 25-minute timeout. On CI and macOS, timeout or cancellation also
terminates child processes. Output already streamed stays in the log.

The tool currently has no stable structured diagnostics interface. The wrapper
therefore checks the complete feature-removal report, including the failure
count and summary. An unrecognized report format, an additional failure, or a
tool error still fails CI. If a tool update changes this format, update the
parser and its regression tests after inspecting the original log. Format
errors are reported separately from failures not covered by the allowlist.

Run a package check and the policy tests with:

```sh
python3 .github/scripts/check_semver.py --package zakura-primitives --default-features
python3 .github/scripts/test_check_semver.py
python3 .github/scripts/test_affected_semver_packages.py
```

For release checks, use `--baseline-version <prev>` to select the previous
published version. Omit `--default-features` to retain the bare checker's normal
feature selection, which also enables features it considers stable. The raw
`cargo semver-checks` command does not apply this repository's exceptions.
