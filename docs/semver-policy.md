# API compatibility

Semver CI compares each affected crate's default public API and feature names
against its latest stable crates.io release. Supported API breaks and feature
removals require an appropriate version bump.

## Unused experimental features

`.github/semver-feature-exceptions.toml` lists unused experimental features that
are outside the compatibility promise. Each entry names one package and one
feature and explains the exception. Wildcards and default features are rejected,
including features enabled indirectly by a local default-feature alias.

The initial exception is `zakura-primitives / zip-233`. Its old V6 amount field
was never used by Zakura. Removing that feature and the APIs behind it is
accepted within the 1.x series. This exception does not change the supported
V6 encoding or the current NU7 implementation.

The CI wrapper runs `cargo semver-checks --default-features`. For an excluded
feature that has been removed, it temporarily adds only an empty feature name
to the checked manifest. It restores the original manifest when the check
finishes, including failures. This narrowly excludes that feature-name removal
from the upstream check. It does not restore the experimental code, enable the
feature, suppress API lints, or change the published manifest.

APIs gated exclusively by optional features are outside this default-feature
check's coverage. Functional feature-matrix tests remain separate. Adding an
exception does not suppress failures for API changes visible in the checked
configuration or for other removed features.

Run the same check locally with:

```sh
python3 .github/scripts/check_semver.py --package zakura-primitives
```

Policy changes select all workspace packages for semver CI. The policy tests
also run the real checker on small fixture crates to prove an excluded removal
passes while an unlisted feature removal and a supported function removal fail.
