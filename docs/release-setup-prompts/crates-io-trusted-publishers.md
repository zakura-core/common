# Agent prompt: configure crates.io Trusted Publishers

Configure crates.io Trusted Publishing for every publishable workspace crate
in zakura-core/common.

Reference: [release workflow](../../.github/workflows/publish-crates.yml) and
[v4.0.0-rc0 release PR](https://github.com/zakura-core/common/pull/594).

Use a clean, isolated checkout of current origin/main. Preserve existing local
edits and read the repository's instructions before acting.

Determine the selected crates from current Cargo metadata:

```sh
cargo metadata --locked --no-deps --format-version 1
```

Select only packages whose IDs are in workspace_members and whose publish
field is either null or an array containing "crates-io". Do not use a fixed
crate list. The release currently selects 25 of 29 members, including
`zakura-orchard-legacy`. Udon and the three Bento crates have `publish = false`
and are excluded. If the discovered selection differs, report and reconcile
the difference before changing publisher configuration.

For every selected crate, ensure this exact GitHub Trusted Publisher exists:

```text
repository_owner: zakura-core
repository_name: common
workflow_filename: publish-crates.yml
environment: crates-io
```

Use Sean's existing authorized crates.io login. Confirm the account owns each
selected crate before changing its settings. Prefer the signed-in settings UI;
do not extract browser session cookies or read a publishing token.
Never display credential values, put them in command arguments, or write
them into source or documentation. Do not create a new publishing token.

Inspect each crate's existing publishers first. Preserve all other
publishers and add the requested configuration only if it is absent.
Do not assume earlier setup is still correct: inspect `zakura-reddsa-frost`
as well as `zakura-orchard-legacy` and every other selected crate. A 401 or 403
is an access blocker, not evidence that a publisher is absent.

Preferred UI:
crates.io → crate → Settings → Trusted Publishing

If an authorized API client is already available and handles authentication
without exposing credentials, the crates.io API also supports:

```text
GET /api/v1/trusted_publishing/github_configs?crate=NAME&per_page=100
POST /api/v1/trusted_publishing/github_configs
```

POST body:

```json
{
  "github_config": {
    "crate": "NAME",
    "repository_owner": "zakura-core",
    "repository_name": "common",
    "workflow_filename": "publish-crates.yml",
    "environment": "crates-io"
  }
}
```

Follow pagination when present. Read back each configuration after adding
it, confirm the exact four publishing identity fields, and verify that
previous publishers remain present.

If the account does not own a crate, or a permission check denies access,
report the crate and blocker. Do not change ownership, delete publishers,
or retry using another identity.

Return a credential-free table with one row per selected crate: settings URL,
status (`already correct`, `added and verified`, or `blocked`), the four saved
identity fields, and a reason for any blocker. Report selected and verified
counts; completion requires every selected crate to pass readback.

A successful OIDC token exchange alone does not verify authorization for all
crates. Do not dispatch a workflow, approve a GitHub deployment, publish any
crate, change versions, create tags, change ownership, or merge a PR.
