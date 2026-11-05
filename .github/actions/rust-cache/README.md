# Rust build caching

Use this action after installing every toolchain needed by a Linux job. Pass a
stable `key` for the job's dependency-cache bucket. The action's automatic key
also includes the runner, installed Rust toolchains, manifests, lockfile, Cargo
configuration, and compiler environment such as `RUSTFLAGS`.

Two layers cover different build work:

- `rust-cache` restores Cargo's registry and compiled dependencies. Its default
  cleanup excludes workspace crates and incremental state.
- `sccache` hashes compiler inputs and reuses eligible compilation outputs,
  including unchanged workspace libraries. Its keys distinguish features,
  compiler flags, generated inputs, and toolchains. Check-only invocations and
  linked test binaries still need compilation; this does not cache test results.

Only pushes to `main` write either layer. Pull requests and merge groups restore
the caches in read-only mode. Builds still execute every existing check and test
command, including the isolated Orchard producer and consumer configurations.

The compiler-cache action reports hit, miss, and non-cacheable counts at job
completion. Compare those statistics with Cargo's `Finished` timings when
evaluating reuse; a dependency-cache hit alone does not imply a compiler hit.
Build-script execution can still rerun even when its dependencies are cached.
If compiler-cache installation fails, checks continue with the ordinary compiler
and the dependency-cache layer.

Start with the repository's existing cache quota. Inspect cache usage and
evictions after the `main` caches have warmed before increasing it. Keep buckets
limited to the enabled Linux validation jobs so other platforms and inactive
matrices do not duplicate the initial cache working set.
