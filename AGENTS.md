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

This policy is **guidance, not a hook**. The protected-path pre-commit hook that
originally accompanied it was removed (2026-07-14): it was theater. An agent with a
shell sets the override env var, and `--no-verify` walks through a pre-commit hook
anyway, so it stopped nothing a worker actually decided to do — while adding a
per-repo `core.hooksPath=.githooks` that *replaced* the global hook and silently
dropped the Lean green-gate and the protected-branch guard (the documented root cause
of lean-gallery's 2026-07-05 `main` divergence).

**The enforcement is the judge, and it is retrospective by design**: every pass runs a
statement differ over the watched set, a dated `#print axioms` on every claimed node,
and a diff of the governance paths above. A worker cannot hide an edit from a diff.
That is cheaper than a gate and it has caught every real incident so far.
