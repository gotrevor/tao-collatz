# tao-collatz — repository agent policy & always-loaded context

Formalizing Tao 2019, *Almost all orbits of the Collatz map attain almost bounded values*
(arXiv:1909.03562v5), in Lean 4 + mathlib. Target: Theorem 1.3, zero sorries, zero axioms beyond
`[propext, Classical.choice, Quot.sound]`. **Status: summit reached 2026-07-15** (both headlines
discharged, kernel-verified); judge ratification reads still owed — see the newest handoff.

## Read these, in this order

1. **`DIRECTION.md` → CURRENT DIRECTIVE.** The judge/operator layer writes it. **It outranks every
   handoff**, and it is re-read every lap — so it is also how a running treadmill gets redirected
   mid-flight.
2. The newest `HANDOFF-*.md` — the previous lap's baton. (Superseded ones: `archive/handoff/`.)
3. `PENDING_WORK.md` — open items and attack paths.

The judge's seat: **`judge/JUDGE.md`** (standing brief) → newest `judge/HANDOFF-JUDGE-*.md` (live state).

## The blueprint rules — binding

@blueprint_rules.md

**One node, one claim. Pinning a node means writing its Lean statement with `sorry`.**
A green border on the dep-graph means *the statement is in Lean*, never *this is finished*;
an **orange** border means the statement is not written yet, and an orange node is the **only**
work the sorry census cannot see. So **report remaining work as "N sorries + M orange nodes."**
**Never set a `\leanok` yourself** — ratification is the judge's/operator's (see the
trust-the-treadmill ruling in DIRECTION.md), and a `\leanok` over a node with no theorem is a
FALSE GREEN that fails the build (`./tools/blueprint_audit.py`).

*(Reasoning, failure modes, how-to: `blueprint_architecture.md`.)*

## House rules

- **Statements are copy-not-compose.** Render verbatim against the paper's numbered display **plus
  the standing context that display sits in** — §7 opens *"Let n ≥ 1, let ξ ∈ ℤ/3ⁿℤ be not divisible
  by 3"*, so both belong in every §7 statement even though Lemma 7.4's display states neither. Tag
  `-- RATIFY-<node>`, record where each hypothesis came from, then freeze. **Let the paper dictate the
  statement; let the proof dictate only the proof** — a hypothesis the proof turns out not to need
  still belongs if the paper declares it: keep it, silence the linter, say why. **A ratified statement
  is the judge's to change** — want it stronger or more general? Add that *beside* the pin and let the
  pin delegate to it. To change the pin itself, write **`JUDGE-FLAG:`** in `PENDING_WORK.md` + your
  handoff, and move on. Full rule, incl. the definitions a statement reaches: `blueprint_rules.md` §4.
- **A `sorry` is honest; a weakened theorem is a lie that compiles.** If a statement will not yield,
  **decompose it** into named sub-`sorry`s and prove what you can. **Raising the sorry count that way
  is PROGRESS.** Register load-bearing sub-lemmas as blueprint sub-nodes in the SAME pass you coin
  them (`C9B1` style) — every node-shaped name must resolve on the map.
- **Never claim a node "COMPLETE" or "verified."** Report `#print axioms` output as *evidence* and
  write *"believed clean, judge to verify."* The judge's dated run is what makes it true.
- Prefer **`decide +kernel`** over `native_decide` (which trusts the compiler and plants an axiom).
  If you must, tag it `-- NATIVE_DECIDE:`.
- Local `maxHeartbeats` bumps need a `-- HEARTBEAT:` justification comment.
- **Commit green, commit often.** A lap that ends with uncommitted work has thrown it away.
- Bare `git` is hook-blocked → use `git-safe`.

## Worker policy (multi-branch fan-out mode)

*Scope note: this section governs fan-out proof workers on assigned branches. The single-treadmill
mode (one box, whole repo) commits directly to `main` — that is how the 2026-07 campaign ran.*

The reviewer-facing blueprint and campaign governance are coordinator-owned.
Fan-out proof workers must treat the following paths as read-only:

- `BLUEPRINT.md`
- `blueprint/**`
- `judge/**`
- `DIRECTION.md`
- `STATUS.md`
- `tools/tao_stmt_diff.py`

Fan-out proof workers may edit only the Lean files assigned to their branch and a
branch-specific handoff note when requested. They must not use `git add -A`,
must not edit a watched theorem statement, and must not commit directly to `main`.

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
