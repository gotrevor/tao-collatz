# Repository agent policy

The reviewer-facing blueprint and campaign governance are coordinator-owned.
Proof workers must treat the following paths as read-only:

- `BLUEPRINT.md`
- `SKELETON-SPEC.md`
- `blueprint/**`
- `judge/**`
- `DIRECTION.md`
- `EXECUTABILITY.md`
- `STATUS.md`
- `tools/tao_stmt_diff.py`

Proof workers may edit only the Lean files assigned to their branch and a
branch-specific handoff note when requested. They must not use `git add -A`,
must not edit a watched theorem statement, and must not commit directly to
`main`.

The coordinator owns blueprint reconciliation, statement ratification,
cross-branch integration, and proof-status changes. Before merging proof work,
the coordinator runs the watched-statement diff, the relevant file build, the
full build, and fresh `#print axioms` checks.

An intentional coordinator governance commit may bypass the local protected
path hook by setting `TAO_ALLOW_GOVERNANCE_EDIT=1`. This override is not
available to proof workers.
