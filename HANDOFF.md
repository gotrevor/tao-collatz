# HANDOFF — effective-constants campaign COMPLETE (2026-07-16, lap 3–4)

**Read `DIRECTION.md` first.** `PENDING_WORK.md` has the full ledger. Operator has called
this a merge checkpoint: **ship-PR & merge are the host's next move (step 4)** — nothing
development-side remains.

## Final state

- Branch `explicit-rate-hold-weight`, tree clean, all green:
  - Full build 3327 jobs; comparator 8600 jobs.
  - `tao_stmt_diff.py` 31/31 byte-identical on every commit.
  - `lean-axiom-gate --exact -i TaoCollatz.Statement` ✓ on all three headlines
    (`tao_collatz`, `tao_collatz_quantitative`, `tao_collatz_quantitative_explicit`).
  - `TaoCollatz/` 0 real sorries; `./tools/check_blueprint.py` ALL CHECKS PASS (16 checks).
- **The headline deliverable is LIVE**: `TaoCollatz/Statement.lean` is the three-statement
  surface with `cTao := 1/(640000000 * Real.log 2)` and `tao_collatz_quantitative_explicit`
  proved (commit `4aebe01`), via `c_ladder_lower` + `tao_collatz_quantitative_spine_of_le`
  (`Sec3/Reduction.lean`). Comparator entry in place (`9b4833a`); `config.json` lists the
  new theorem name; `Solution.lean` untouched.
- **check16** (`005ac86`): exact-arithmetic numeric trap for the cTao min-tree (blueprint
  rule "every pin ships with a trap") — collapses exactly to `1/(640000000·ln 2)`,
  lower-bounds every leaf, fires on the square-forgotten `linearDecay` rendering. It also
  caught a float slip in the lap-1 ledger (true value 2.25421e-9, not 2.2547e-9; corrected).

## For the host (step 4)

- Ship-PR + PR #6 note update. Note the corrected float above when updating the note.
- Judge still owes ratification reads on: the step-2 explicit siblings (statement-copies of
  ratified originals with a def in the c-slot), and the new `Statement.lean` /
  `Challenge.lean` additions. Believed clean; judge's dated run makes it true.

## Loose ends (cosmetic only, deliberately not done)

- ~12 module docstrings still carry historical "carries `sorry`" prose from before the
  summit (e.g. `Sec5/FirstPassage.lean:15`, `Prob/Basic.lean:17`). Stale but harmless;
  a reviewer greps 0 real sorries. Left for a docs pass to avoid churn at merge time.

## Gotchas this campaign (see also lap-3 list in git history)

- `div_le_div_iff` doesn't exist here — use `one_div_le_one_div_of_le` or `gcongr`.
- `gcongr` fully discharges `a/L/20 ≤ b/L/20` from context; a trailing `<;> linarith`
  FAILS the build ("linarith does nothing").
- `lean-axiom-gate` needs `-i TaoCollatz.Statement` (default root-lib import chokes on the
  sourceless `Comparator` lib name).
- Unused-binder linter is warningAsError: an unreferenced hypothesis fails the build.
