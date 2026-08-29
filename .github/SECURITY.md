# Security policy

This repository contains general-purpose cryptographic libraries. In
particular, the Halo 2 APIs allow downstream users to construct circuits with
security properties that depend on the circuit's design. The mere ability to
construct a malformed, underconstrained, or otherwise insecure circuit is not a
vulnerability in this repository.

## Scope

A vulnerability in any crate in this repository, including
`zakura-halo2-gadgets`, `zakura-orchard`, `zakura-halo2-proofs`, and
`zakura-halo2-poseidon`, is in scope only when it has a concrete security impact
on at least one of the following:

- Orchard proof verification as used by Zakura;
- the Orchard signature hash; or
- the soundness of the verifier in
  [`valargroup/voting-circuits`](https://github.com/valargroup/voting-circuits).

A report should identify the affected target and explain a concrete path from
the reported behavior to that security impact.

Reports about arbitrary or example circuits, downstream circuits other than the
ones listed above, misuse of an API, or violations of documented preconditions
are out of scope unless they also demonstrate one of the impacts listed above.
General correctness, performance, and API-design issues without such an impact
should be reported as ordinary GitHub issues instead of security
vulnerabilities.

## Reporting an in-scope vulnerability

Do not open a public issue for an in-scope vulnerability. Submit it privately
through [Zakura's security advisory
reporting](https://github.com/zakura-core/zakura/security/advisories/new), and
state that the report concerns `zakura-core/libraries`.
