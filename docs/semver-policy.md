# Semver policy

CI runs `cargo-semver-checks` against the latest stable crates.io baseline.
To accept a Cargo feature removal in a minor release, add the exact package,
feature name, and reason to [the allowlist](../.github/semver-feature-removals.json).
Add future exceptions under the same package or a new package object.

For example, the `zakura-primitives/zip-233` entry permits its removal in
`1.3.0` against `1.2.0`. Removing `multicore` still needs its own entry, and
removing `zip-233` in `1.2.1` still fails. Other API failures still block CI.
The checker decides bump levels, including for `0.x` versions and prereleases.

Entries are permanent, including if a feature is reintroduced and removed
again. Once the baseline no longer contains the feature, there is nothing to
exempt. Delete an entry to revoke approval. An empty allowlist is valid.

[The wrapper](../.github/scripts/check_semver.py) prints the tool version and
streams logs. Only a completed check reporting approved feature removals as
its sole failure can pass. Warnings remain visible. Unknown report formats
fail with a separate diagnostic. Inspect the original log before updating the
parser for a new checker format. CI's existing 30-minute job timeout applies.

```sh
python3 .github/scripts/check_semver.py --package zakura-primitives --default-features
python3 .github/scripts/test_check_semver.py
```

For release checks, add `--baseline-version <prev>` and omit
`--default-features` to retain the checker's normal feature selection.
The bare checker does not apply the repository's exceptions.
