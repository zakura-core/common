# Encoding and note-encryption ownership migration

## Baselines and release status

Common main: `b679027d`; node main: `0a7ecd432`; wallet main: `0497bc3`.
Work uses isolated worktrees; the original checkouts and their changes are
preserved. No benchmarks, crate publication, or PR merges are part of this work.

Both upstream archives were verified against the node's fetched main lockfile:

| Source | SHA-256 | Upstream source commit |
| --- | --- | --- |
| `zcash_encoding 0.4.0` | `1440921903cdb86133fb9e2fe800be488015db2939a30bedb413078a1acb0306` | `661e0383e829c894fa0691543a379891a304ad0e` |
| `zcash_note_encryption 0.4.2` | `e1cb1b9170c94370e3d66c5cc0877661db743337588b64de7711239eed462198` | `a8c90d1ce3737cc5898e0bf232ea325a5a61ec9f` |

Common **3.0.0** is staged at the user's request. All published Common
members and both consumer requirement sets use that coordinated major
release. This covers the breaking public dependency identity changes.
Node libraries are reviewed independently against their latest stable
releases; the node binary's major version is not automatically bumped.

Common uses inherited workspace package metadata, upstream library targets,
explicit renamed workspace edges with defaults disabled, and one coordinated
version for all published crates. The new member follows those conventions.
All 23 published Common members are staged at 3.0.0; independently
versioned unpublished members retain their versions. This coordinated major
also changes the crate identity of existing Common types in consumer APIs;
callers must rebuild the family together. No other public definitions or
visibility are changed by the version staging.
Its upstream authors and both licenses are retained. The new package inherits
Common edition 2024 and MSRV 1.91 (upstream used edition 2021 and MSRV
1.56.1). Encoding carries its
upstream authorship and exact license files under `src/encoding/`.

## Public API changes

`zakura-protocol` adds the public module `zcash_protocol::encoding`.
The migrated namespaces have the same signatures and behavior as 0.4.0:

- `MAX_COMPACT_SIZE: u32`.
- `CompactSize::{read, read_t, write, serialized_size}`.
- `Vector::{read, read_collected, read_collected_mut, write, write_nonempty,
  write_sized, serialized_size_of_u8_vec}`.
- `Array::{read, read_collected, read_collected_mut, write}`.
- `Optional::{read, write}`.
- `ReverseHex::{encode, decode}`.

The five namespace types now have `zakura-protocol` identity rather than
`zcash_encoding` identity. Serialization bytes and reader validation are
unchanged. In particular, the 0.4 writer continues to accept values above
`MAX_COMPACT_SIZE`; the 0.5 limit check is intentionally absent.
`Vector::write_nonempty` preserves its public `nonempty 0.11` argument type.
Supporting imports and tests are private; no supporting public or
`pub(crate)` helper is introduced. Protocol's existing `std` feature forwards
`corez/std`, carrying the old encoding `std` feature behavior. Allocation
remains available without `std`; no new allocation feature gate is introduced.
All other consumer feature names and defaults remain unchanged.

`zakura-note-encryption` is a new published-package surface, with the upstream
`zcash_note_encryption` library target. Its API shapes and signatures are
preserved, but every trait and nominal wrapper has a new package identity.
The complete named inventory below was compared against upstream rustdoc JSON
with all features enabled: 64 entries have the same shape/signature. The
`batch` module remains public only with `alloc`; `BatchDomain` and its default
batch methods remain gated by `alloc`. `NoteEncryption::new_with_esk` remains
gated by `pre-zip-212`. Defaults still enable only `alloc`.

### Constants

- `COMPACT_NOTE_SIZE`.
- `NOTE_PLAINTEXT_SIZE`.
- `OUT_PLAINTEXT_SIZE`.
- `ENC_CIPHERTEXT_SIZE`.
- `OUT_CIPHERTEXT_SIZE`.

### Types

- `OutgoingCipherKey`.
- `EphemeralKeyBytes`.
- `NotePlaintextBytes`.
- `OutPlaintextBytes`.
- `NoteEncryption`.

### Traits

- `Domain`.
- `BatchDomain`.
- `ShieldedOutput`.

### Associated types

- `Domain::EphemeralSecretKey`.
- `Domain::EphemeralPublicKey`.
- `Domain::PreparedEphemeralPublicKey`.
- `Domain::SharedSecret`.
- `Domain::SymmetricKey`.
- `Domain::Note`.
- `Domain::Recipient`.
- `Domain::DiversifiedTransmissionKey`.
- `Domain::IncomingViewingKey`.
- `Domain::OutgoingViewingKey`.
- `Domain::ValueCommitment`.
- `Domain::ExtractedCommitment`.
- `Domain::ExtractedCommitmentBytes`.
- `Domain::Memo`.

### Functions and methods

- `batch::try_note_decryption`.
- `batch::try_compact_note_decryption`.
- `Domain::derive_esk`.
- `Domain::get_pk_d`.
- `Domain::prepare_epk`.
- `Domain::ka_derive_public`.
- `Domain::ka_agree_enc`.
- `Domain::ka_agree_dec`.
- `Domain::kdf`.
- `Domain::note_plaintext_bytes`.
- `Domain::derive_ock`.
- `Domain::outgoing_plaintext_bytes`.
- `Domain::epk_bytes`.
- `Domain::epk`.
- `Domain::cmstar`.
- `Domain::parse_note_plaintext_without_memo_ivk`.
- `Domain::parse_note_plaintext_without_memo_ovk`.
- `Domain::extract_memo`.
- `Domain::extract_pk_d`.
- `Domain::extract_esk`.
- `BatchDomain::batch_kdf`.
- `BatchDomain::batch_epk`.
- `BatchDomain::batch_ka_agree_dec`.
- `ShieldedOutput::ephemeral_key`.
- `ShieldedOutput::cmstar_bytes`.
- `ShieldedOutput::enc_ciphertext`.
- `NoteEncryption::new`.
- `NoteEncryption::new_with_esk`.
- `NoteEncryption::esk`.
- `NoteEncryption::epk`.
- `NoteEncryption::encrypt_note_plaintext`.
- `NoteEncryption::encrypt_outgoing_plaintext`.
- `try_note_decryption`.
- `try_compact_note_decryption`.
- `try_output_recovery_with_ovk`.
- `try_output_recovery_with_ock`.
- `try_output_recovery_with_pkd_esk`.

The tuple fields/constructors of `OutgoingCipherKey`, `EphemeralKeyBytes`,
`NotePlaintextBytes`, and `OutPlaintextBytes` remain public. Retained explicit
implementations include `OutgoingCipherKey: From<[u8; 32]> + AsRef<[u8]>` and
`EphemeralKeyBytes: Debug + AsRef<[u8]> + From<[u8; 32]> + ConstantTimeEq`;
`EphemeralKeyBytes` retains its derived `Clone`, `PartialEq`, and `Eq`.
No conversion hides an added clone. No cryptographic implementation, trait
method, encryption/recovery function, authentication check, or commitment
check is removed. `no_std` and `deny(unsafe_code)` remain in force.

## Public and crate-visible dependent type changes

Retaining the library target spelling does not preserve type identity. All
Common, node, and selected Zakura wallet edges move together. In particular:

- Orchard: `NoteEncryptionDomain` (including `OrchardDomain`, `IronwoodDomain`,
  and the crate-visible `BundleDomain`) implements the fork's `Domain` and
  `BatchDomain`. `Action`, `bundle::Output`, and `CompactAction` implement the
  fork's `ShieldedOutput`. `OrchardNoteEncryption` and `IronwoodNoteEncryption`
  alias the fork's `NoteEncryption`. `CompactAction::from_parts` accepts the
  fork's `EphemeralKeyBytes`.
- Sapling: `SaplingDomain` implements the fork's `Domain` and `BatchDomain`.
  `CompactOutputDescription::ephemeral_key`,
  `OutputDescription::{ephemeral_key, from_parts}`, and
  `OutputDescriptionV5::from_parts` use the fork's `EphemeralKeyBytes`.
  `CompactOutputDescription` and `OutputDescription` implement the fork's
  `ShieldedOutput`. `note_encryption::prf_ock` uses the fork's byte/key
  wrappers; `sapling_note_encryption` returns its `NoteEncryption`.
  `try_sapling_note_decryption` and `try_sapling_compact_note_decryption` use
  its `ShieldedOutput` bounds; `try_sapling_output_recovery_with_ock` accepts
  its `OutgoingCipherKey`.
- Primitives: Sapling/Orchard transaction components continue to use the same
  ciphertext sizes and now construct fork wrappers for the migrated Sapling
  output APIs. Public transaction/builder APIs transitively expose the
  migrated Sapling/Orchard types. No handwritten signature is changed.
- Wallet: client-backend public scanning/decryption bounds
  (`ScanningKeyOps`, `ScanningKeys`, `ScanningKey`, `scan_block` and related
  generic APIs) refer to the fork traits.
  `WalletOutput::{from_parts, ephemeral_key}` and both compact protobuf output
  and action `ephemeral_key` accessors use the fork wrapper. PCZT's
  Orchard/Sapling integration and the facade's Zakura re-exports follow the
  same family. SQLite implements/consumes those wallet APIs. These public
  dependency changes need consumer release review even without new methods.
- Node: recovery imports now select the fork. The direct note-encryption
  recovery adapters are private. `decrypts_successfully` retains its
  signature and behavior. Common 3.0 public dependencies and
  re-exports were reviewed independently: existing chain/network/state/RPC/
  node-services major bumps suffice; consensus is staged at 11.0.0 and
  script/header-chain at 5.0.0. Utils retains its pending patch. The binary
  remains 1.6.1.

Existing `pub(crate)` surfaces are also affected by the wrapper/trait
identity change: Orchard/Sapling PCZT `Output::ock`, Sapling PCZT
`Output::ephemeral_key`, both protocols' `EphemeralPublicKey::to_bytes`,
Sapling `SharedSecret::{kdf_sapling, kdf_sapling_inner}`, Orchard
`SharedSecret::{kdf_orchard, kdf_orchard_inner}`, Orchard's internal `batch_kdf`,
`BundleDomain`, and Sapling `OutputDescription::ephemeral_key_mut`. Wallet
client-backend crate-visible `scan::{DecryptedOutput, Decryptor, BatchReceiver,
Batch}` and its scanning `IronwoodDomain` alias also acquire the fork
trait/domain identity.
Their visibility does not increase. No new `pub(crate)` item, enum variant,
feature, type alias, or handwritten function signature is added to consumers.

## Verification strategy and local overrides

Common is verified directly as a path-based workspace. Consumer worktrees
use temporary `[patch.crates-io]` entries in their local `.cargo/config.toml`
for **every published Common package**, so a registry copy cannot coexist
with the locally modified family. These overrides and the resulting local
consumer lockfiles must not be committed. Production declarations remain
explicit `package = "zakura-*"` dependencies with registry versions.

The wallet generated manifest is reproduced from the untouched upstream
workspace and `manifests/sources.toml`. The generator's removal rule drops
`zcash_encoding` and its obsolete adjacent upstream comment. Vendored wallet
member manifests and source imports are maintained directly, as its current
merge-based sync workflow requires. Graph policy forbids both upstream
encoding and note encryption. The separately selected `lrz` facade remains
an upstream-only backend; its inactive packages may appear in the workspace
lockfile/metadata but must not enter the Zakura production build.

Folding encoding removes one compilation unit. Forking note encryption
changes ownership; it does not itself reduce compilation work. No timing or
benchmark claim is made.

Draft PRs: [Common #540](https://github.com/zakura-core/common/pull/540),
[node #1292](https://github.com/zakura-core/zakura/pull/1292), and
[wallet #84](https://github.com/zakura-core/wallet-libraries/pull/84).

## Release order and remaining dependencies

1. Review the staged Common 3.0.0 major release and affected wallet
   prerelease and node library versions. The node binary release is separate.
2. Merge and publish Common in dependency order. `zakura-note-encryption`
   and `zakura-protocol` are foundation packages; publish them before
   Orchard/Sapling, addresses/transparent, keys, primitives, and proofs.
3. Regenerate node and wallet lockfiles from the published registry artifacts,
   then rerun locked feature/graph checks without local overrides. Consumer
   drafts retain their original registry lockfiles until this is possible;
   a staging dependency on the unpublished new package cannot resolve there.
4. Publish the wallet's PCZT, backend, SQLite, and facade as required by its
   public dependency change; the reviewed node library majors are staged. This task publishes or merges none of these artifacts.

## Validation evidence

All production-code checks below use the imported baseline implementations.
Consumer runs use local Common 3.0.0 sources. Registry validation must follow
publication.

| Common package | `check --no-default-features` | `check --all-features --all-targets` |
| --- | --- | --- |
| `zakura-protocol` | Pass | Pass |
| `zakura-address` | Pass | Pass |
| `zakura-keys` | Pass | Pass |
| `zakura-primitives` | Pass | Pass |
| `zakura-transparent` | Pass | Pass |
| `zakura-note-encryption` | Pass | Pass |
| `zakura-orchard` | Pass | Pass |
| `zakura-sapling-crypto` | Pass | Pass |

Additional successful checks:

- Note encryption with no defaults and each of `alloc`, `pre-zip-212`, and
  `alloc,pre-zip-212`; Rust 1.91 no-default protocol/note checks.
- Protocol tests: 40 unit + 7 compatibility tests without defaults;
  44 unit + 7 compatibility tests with all features. All four upstream
  encoding tests are retained. Address: 32 unit + 9 doctests; transparent:
  9 unit tests.
- Orchard/Sapling `note_encryption` tests: 9 + 26 passed with defaults;
  9 + 26 passed with defaults disabled and only each crate's `std` enabled.
  Both runs exercise recovery vectors and authentication/commitment failures;
  Orchard exercises Ironwood encryption, compact decryption, and batching.
- Formatting and protocol/note all-feature all-target Clippy with warnings
  denied. Two narrow Clippy allowances retain the original nested check and
  `repeat().take()` expression instead of modifying cryptographic code.
- Both foundation crates passed `cargo package --allow-dirty --locked
  --offline`, including compilation of their packaged source. Package lists
  include the upstream licenses and provenance; protocol also includes
  encoding's original license files and the compatibility tests.
- `cargo semver-checks -p zakura-protocol --baseline-root <fetched-main>
  --default-features`: 223 checks passed. This verifies existing protocol API
  compatibility; release review still treats the module as an additive API.
- Source token comparison preserves encoding implementation and upstream
  tests after module scaffolding/import formatting/comments, and preserves
  both note-encryption source files after import formatting/comments and the
  two lint attributes. All-feature rustdoc inventory comparison preserves
  all 64 named note-encryption API shapes and signatures.
- Final Common 3.0.0 reruns passed all 24 feature-matrix commands, both
  protocol feature test sets, both domain-vector configurations, MSRV 1.91,
  foundation Clippy, and both packaged-source verifications.
- Node: two chain domain/routing tests, three `coinbase_outputs` tests,
  one nonzero-key recovery rejection vector, and chain Clippy passed.
- Wallet: Orchard/default-PCZT/SQLite-without-Orchard/transparent feature
  checks passed; backend scanning passed 23 tests; SQLite Ironwood passed
  67 tests; PCZT `internal-tests` passed three selected V2 anchor round trips
  covering Sapling, Orchard, and Ironwood. Final 3.0.0 Orchard, transparent,
  SQLite, scoped Clippy, scanning/Ironwood/PCZT, facade, and graph runs passed.
  Clippy reports existing unused code/import warnings in the wallet stack;
  no blanket suppression is introduced.
- Wallet's repository graph verifier passed with 599 reachable packages,
  including 27 Zakura packages and no forbidden upstream package. Generator
  reproduction from the pristine upstream manifest passed twice. The wallet Python tooling tests passed (12 tests), including a new
  source-generation regression covering encoding removal, feature defaults,
  and deterministic regeneration.

Resolved production graphs for the node binary and selected wallet consumers
contain no standalone `zcash_encoding` or upstream `zcash_note_encryption`,
and exactly one `zakura-note-encryption`. Common metadata likewise contains
only the fork. Temporary overrides and consumer lockfiles are excluded from
PRs; published registry-only resolution remains a delivery prerequisite.

An extra Orchard test run with `std` fully disabled could not compile the
existing test-only `std::println!` in `tree.rs`; the crate-level `extern crate
std` is feature gated in fetched main too. Its no-std library check passed,
and the test suite passed with circuits/multicore disabled and `std` enabled.
This migration does not change that unrelated test harness.

The literal/terminology audit found only the retained upstream CompactSize
reader/writer discriminants and boundary literals, including the intentionally
unbounded 0.4 writer. New compatibility tests use `MAX_COMPACT_SIZE`. No new
protocol label, domain separator, duplicated cryptographic constant, or
terminology change is introduced.
