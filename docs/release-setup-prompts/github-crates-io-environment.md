# Agent prompt: configure the GitHub release environment

Configure the GitHub Environment "crates-io" in zakura-core/common for the
existing [release workflow](../../.github/workflows/publish-crates.yml).
This enables the CI publishing path used by the
[v4.0.0-rc0 release PR](https://github.com/zakura-core/common/pull/594).

Use an existing authorized GitHub account with repository admin rights.
Inspect the environment and deployment branch policies before changing
anything. Preserve unrelated settings and secrets; do not add credentials.

Required final configuration:

```text
Environment name: crates-io
Required reviewer: exactly the GitHub user ebfull
prevent_self_review: false
can_admins_bypass: false
deployment_branch_policy:
  protected_branches: false
  custom_branch_policies: true
Deployment policies: exactly one branch policy named main; no tag policies
```

Allowing self-review is intentional: Sean must be able to approve a run
that he dispatched himself.

UI:
GitHub → zakura-core/common → Settings → Environments → crates-io

First check repository permissions and list environments. A 404 on an individual
environment is not sufficient evidence of absence when access is uncertain.
Confirm the signed-in account has repository administrator rights before any write.

Create the environment if absent. Set ebfull as the required reviewer,
leave "Prevent self-review" unchecked, disable administrator bypass, and
select branch restrictions allowing only the branch main.

API endpoints:

```text
GET /repos/zakura-core/common
GET /repos/zakura-core/common/environments
GET /repos/zakura-core/common/environments/crates-io
PUT /repos/zakura-core/common/environments/crates-io
GET /repos/zakura-core/common/environments/crates-io/deployment-branch-policies
POST /repos/zakura-core/common/environments/crates-io/deployment-branch-policies
```

Resolve `ebfull` through `GET /users/ebfull` and confirm the returned numeric ID
before using it as the reviewer. For a new environment, the PUT body is:

```json
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
```

The branch-policy POST body is:

```json
{"name": "main", "type": "branch"}
```

For an existing environment, inspect and reconcile its settings rather than
blindly replacing unrelated configuration. Avoid duplicate branch policies.

Read both the environment and all deployment branch policies back afterward,
following pagination. For an existing configuration that requires removing an
unexpected policy or reviewer, report the discrepancy to Sean before removing it.
Confirm ebfull's reviewer identity, self-review allowed, administrator bypass
disabled, and exactly the main branch policy with no tag policies.

If admin permission is missing, stop and report the blocker. Do not retry
with another identity or weaken the required protections.

Return the environment URL, whether it was already correct or changed, and a
credential-free comparison of every required setting with its saved value.
Include all branch policies and any unresolved blockers. Configuration readback
proves setup only; it does not prove OIDC authentication or publication.

Do not dispatch
the publishing workflow, merge the PR, or publish crates.
