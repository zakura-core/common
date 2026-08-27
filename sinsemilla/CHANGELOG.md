# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

- Added `UncheckedFixedLengthHashDomain::hash_with_first_word` for messages
  whose first Sinsemilla word is already decoded and whose suffix remains a
  bit iterator.
- Prepared the `1.0.0-rc.4` release.
- Replaced `lazy_static` (`spin_no_std`) with `once_cell` plus an
  exactly-once initialization wrapper for the affine generator table,
  removing the `spin` dependency.

- Added `BatchHashWorkspace` and
  `UncheckedFixedLengthHashDomain::hash_words_batch_with_workspace` so callers
  can retain the weighted batch evaluator's temporary allocations.
- The fixed-length weighted evaluator precomputes its first addition and, for
  the first eight possible leading words, its second addition. This removes
  runtime batch-affine columns from the widest Orchard Merkle tree levels at
  the cost of a 512 KiB larger weighted table.
- Prepared the `1.0.0-rc.3` release.
- Weighted batch evaluation now uses the configured runtime field backend for
  squaring.
- Prepared the `1.0.0-rc.2` release.
- The batched fixed-length weighted evaluator now processes two independent
  incomplete mixed additions in parallel and omits exceptional-case checks
  under its existing discrete-logarithm relation assumption.
- The batched fixed-length weighted evaluator avoids repeating affine identity
  checks when reading its construction-time-validated generator table.
- Added `UncheckedFixedLengthHashDomain::hash_words` and
  `UncheckedFixedLengthHashDomain::hash_words_batch` for extracted hashes of
  pre-decoded words. The batch method processes messages position-first and
  shares projective normalization across the batch. The point-valued method is
  exposed as `UncheckedFixedLengthHashDomain::hash_words_to_point`.
- The fixed-length weighted evaluator now reuses the streaming message-word
  conversion, removing its padded message allocation.
- Added an unchecked fixed-length, position-weighted hash evaluator that moves
  per-word doublings into a compact reusable generator table. This evaluator
  relies on the discrete-logarithm relation (DLR) assumption to rule out
  Sinsemilla's exceptional incomplete-addition cases; the generic evaluator
  retains exact partial-function semantics.
- Sinsemilla hashing now evaluates each message-word step with an
  algebraically equivalent doubling and mixed addition, avoiding a full
  projective addition while preserving incomplete-addition failures.
- Updated the curve traits to `ff 0.14` and `group 0.14`.
- The precomputed Sinsemilla $S$ generators are decoded once and reused across
  hashes instead of validating their coordinates for every message word.
- Sinsemilla hashing now converts messages directly into words instead of
  allocating an intermediate padded bit vector.
- Forked from upstream `sinsemilla` and renamed to `zakura-sinsemilla`; this changelog starts
  fresh for the Zakura fork's initial release.
- Restarted the version lineage at 1.0.0, leaving behind the inherited upstream
  version (0.1.0); the initial Zakura release will be preceded by `1.0.0-rc` release
  candidates.
