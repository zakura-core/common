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

The release number is deliberately deferred at the user's request. All
`2.2.0` requirements in the coordinated migration are staging values, **not a
proposal to republish or modify already-published 2.2.0 artifacts**. This is a
breaking public dependency migration. Choose a coordinated Common version
that covers the break, review consumer library release levels, and rewrite
all staging requirements before merging or publishing. The node binary's
major version is not automatically bumped by this ownership change.

Common uses inherited workspace package metadata, upstream library targets,
explicit renamed workspace edges with defaults disabled, and one coordinated
version for all published crates. The new member follows those conventions.
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
  signature and behavior. The eventual Common release-number change must be
  reviewed for every node library exposing Common types or re-exports;
  library versions and the binary release version are separate decisions.

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

## Release order and remaining dependencies

1. Select the breaking coordinated Common release number and update all
   Common workspace versions plus both consumer requirement sets. Review
   affected wallet prerelease and node library versions; do not automatically
   bump the node binary's major version.
2. Merge and publish Common in dependency order. `zakura-note-encryption`
   and `zakura-protocol` are foundation packages; publish them before
   Orchard/Sapling, addresses/transparent, keys, primitives, and proofs.
3. Regenerate node and wallet lockfiles from the published registry artifacts,
   then rerun locked feature/graph checks without local overrides. Consumer
   drafts retain their original registry lockfiles until this is possible;
   a staging dependency on the unpublished new package cannot resolve there.
4. Publish the wallet's PCZT, backend, SQLite, and facade as required by its
   public dependency change; finalize node library version review before
   releasing the node. This task publishes or merges none of these artifacts.
