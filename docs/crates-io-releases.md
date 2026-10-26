# Crates.io releases

Common releases use `.github/workflows/publish-crates.yml`, following
[Zakura's workflow](https://github.com/zakura-core/zakura/blob/main/.github/workflows/publish-crates.yml)
and [wallet-libraries' protected release](https://github.com/zakura-core/wallet-libraries/pull/183).
Only a manual dispatch from `main` in `zakura-core/common` is allowed. Every
checkout uses the dispatch commit, even if main advances while approval is pending.
There is one repository-wide release concurrency group; active releases are never
cancelled by a later dispatch. No versions are bumped and no tags are created.

## One-time setup

A repository administrator must configure the `crates-io` GitHub Environment:

- Required reviewer: `ebfull` (Sean).
- Allow Sean to approve his own dispatch (`prevent_self_review: false`).
- Disable administrator bypass (`can_admins_bypass: false`).
- Custom deployment branch policy: only the branch `main`; no tag policies.

Inspect the environment and its deployment branch policies before editing. Retain
any unrelated environment configuration, and avoid duplicate branch policies.
For a new environment, an administrator can run:

```sh
gh api --method PUT repos/zakura-core/common/environments/crates-io --input - <<'JSON'
{
  "wait_timer": 0,
  "prevent_self_review": false,
  "reviewers": [{"type": "User", "id": 3794471}],
  "can_admins_bypass": false,
  "deployment_branch_policy": {
    "protected_branches": false,
    "custom_branch_policies": true
  }
}
JSON
gh api --method POST repos/zakura-core/common/environments/crates-io/deployment-branch-policies \
  -f name=main -f type=branch
```

Read both endpoints back after configuration. The release preflight refuses a
missing or incorrectly protected environment before scheduling either OIDC job.
This also prevents GitHub from silently creating an unprotected environment.

Each selected crate needs this crates.io Trusted Publisher:

| Field | Value |
| --- | --- |
| GitHub owner | `zakura-core` |
| Repository | `common` |
| Workflow filename | `publish-crates.yml` |
| Environment | `crates-io` |

A crate owner must inspect the crate's **Settings → Trusted Publishing**, add this
configuration only if it is absent, preserve other publishers, and read the saved
configuration back. Do not change crate ownership or create a publishing token.
For programmatic setup with an existing authorized credential, crates.io exposes
`GET /api/v1/trusted_publishing/github_configs?crate=NAME` and
`POST /api/v1/trusted_publishing/github_configs`; the POST body is
`{"github_config":{"crate":"NAME","repository_owner":"zakura-core","repository_name":"common","workflow_filename":"publish-crates.yml","environment":"crates-io"}}`.
Keep credentials in their existing local credential store or Infisical, read them
at runtime, and never print their values or put them in command arguments.

During initial setup, the available GitHub account lacked repository admin rights.
The authenticated crates.io account could configure only `zakura-reddsa-frost`;
its exact publisher was added and read back. All other selected crates were owned
only by `ebfull`, and their private publisher settings could not be inspected by
that account. Sean must inspect and configure those crates. The current release
selection is listed below; this list is documentation, not the workflow's input.

- `zakura-bento-core`
- `zakura-bento-macros`
- `zakura-bento`
- `zakura-udon`
- `zakura-sensei-shared`
- `zakura-sensei-artifacts`
- `zakura-sensei-macros`
- `zakura-sensei`
- `zakura-protocol`
- `zakura-pairing`
- `zakura-equihash`
- `zakura-pasta-curves`
- `zakura-note-encryption`
- `zakura-address`
- `zakura-bls12-381`
- `zakura-halo2-poseidon`
- `zakura-sinsemilla`
- `zakura-halo2-proofs`
- `zakura-transparent`
- `zakura-zip321`
- `zakura-bellman`
- `zakura-jubjub`
- `zakura-halo2-gadgets`
- `zakura-reddsa`
- `zakura-orchard-legacy`
- `zakura-orchard`
- `zakura-reddsa-frost`
- `zakura-redjubjub`
- `zakura-sapling-crypto`
- `zakura-keys`
- `zakura-primitives`
- `zakura-proofs`

Cargo metadata currently selects all 32 workspace members. Sensei, Udon, Bento,
and their implementation crates retain independent versions (Udon is `0.2.0`,
the rest `0.1.0`), separate from the coordinated Common release.
New members and publishing policy changes are discovered automatically. Local
dependencies must also allow crates.io publication; optional, target-specific,
build, and development edges all participate in the dependency order. A cycle
or excluded local dependency stops the plan. Cargo's full packaging verification
checks version requirements.

## Verify after merge

After the workflow merges and the exact main commit's `CI` workflow and
`test success` aggregate job both pass, dispatch:

```sh
gh workflow run publish-crates.yml --repo zakura-core/common --ref main -f mode=verify
```

Verification checks all selected registry versions and rejects yanks and registry
errors. It runs one locked Cargo dry-run containing only unpublished versions, so
new workspace versions can resolve one another while dependencies on versions
already available resolve from crates.io. Local copies of published versions
cannot substitute for the immutable code users will download. If every version
is already published, no packaging or compilation is needed. The compile check
uses Cargo's default package features; broader feature tests remain in CI. The
receipt records the commit, Git tree, ordered names, versions, manifests,
dependencies, registry status, and whether verification succeeded.

Only then does the OIDC smoke job request environment approval. Sean must approve
it. That job exchanges a short-lived token and revokes it in the authentication
action's post step, without exposing it to repository code or uploading a crate.
The action is pinned to the same reviewed commit as Zakura. A successful smoke
exchange proves authentication works; it does not prove that every selected
crate has been configured, so owners must read back each publisher separately.

## Publish only with separate authorization

An explicitly authorized publication uses `mode=publish`. It repeats verification
and environment approval. Before token exchange, a fresh checkout validates the
receipt against the same clean commit and ordered versions. The upload step
validates again, uses locked dependencies and `--no-verify`, and skips already
available versions. Only this step receives the temporary registry token.
If a version's registry availability changes after verification, publication
stops and requires verification again; it cannot silently switch a dependency
from verified local code to newly available registry code. This check runs for
every selected version before any upload and again immediately before each
version is uploaded or skipped.
Toolchain installation, compilation, and environment waiting happen beforehand.
The authentication action revokes the token when the job finishes.

Each newly uploaded version must appear in both the crates.io API and sparse
index before its dependents upload. Its Trusted Publishing attribution must
identify GitHub, `zakura-core/common`, the workflow run ID, and the dispatch SHA.
Existing versions need availability and a non-yanked status but are not claimed
as uploads by this run. Registry failures stop immediately; only a version's
404 response means it is absent.

## Recover an interrupted release

Download the verification and publication artifacts and inspect the failed step,
workflow summary, and receipt before resuming. Receipts are saved before uploads
and after each transition, so completed uploads survive a later failure. Full
Cargo registry errors remain in the step log; HTTP API/index error bodies remain
in the receipt and log. A failed upload is recorded as `upload_started`, because
an error can occur after the registry accepted it. `uploaded_unconfirmed` means
Cargo completed but availability or attribution confirmation did not.

Rerun **all jobs of the original workflow run** to retain its dispatch commit and
redo verification with current registry state. If main has advanced, a new main
dispatch selects the newer commit. Never reuse a failed receipt, hand-edit a
receipt, bypass verification, or substitute a receipt from another checkout.
Read registry versions first; reruns skip versions that already exist and wait
for their index availability. An attribution mismatch stops the release for
owner investigation. Existing versions cannot be overwritten. A yanked version
requires preparing a new manifest version through normal review.

A verification failure requires a code or packaging fix before a new dispatch.
An expired/revoked token requires a fresh run with Sean's approval. Do not fall
back to a permanent publishing token. GitHub artifacts and step summaries are
retained on failures; no cancellation of an active release is automatic.

## Tests

The Workflow security workflow runs the focused release safety tests whenever
GitHub configuration changes. To run them locally:

```sh
python3 -m unittest discover -s .github/scripts/tests -v
actionlint .github/workflows/publish-crates.yml .github/workflows/workflow-security.yml
```
