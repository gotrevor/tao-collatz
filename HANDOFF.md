# HANDOFF — effective-constants campaign, lap 3 (2026-07-16)

**Read `DIRECTION.md` first — it is the directive.** `PENDING_WORK.md` has the full ledger.

## State: STEP 3 COMPLETE — the explicit headline is LIVE

- Branch `explicit-rate-hold-weight`, all work committed, full build green (3327 jobs;
  comparator 8600).
- ✅ **STEP 3 (3a + 3b + 3c) done in one lap** (commits `4aebe01`, `9b4833a`; operator
  sign-off `6852905`, step re-order `7c9c494`):
  - `TaoCollatz/Statement.lean` now the three-statement surface:
    `cTao := 1/(640000000 * Real.log 2)` + `tao_collatz_quantitative_explicit`, proved
    (no sorry ever committed — pin and discharge landed together).
  - Proof route (`Sec3/Reduction.lean`): `c_ladder_lower` (min-tree lower bound; binding
    branch `c_valSumTail` = exactly `cTao`, numeric leaves ≥ 1/5) +
    `tao_collatz_quantitative_spine_of_le` (rpow-exponent monotonicity for `N₀ ≥ 3`;
    `N₀ = 2` absorbed by `max C (log 2)^c₀` and `0 ≤ logProb`).
  - Comparator: `Challenge.lean` has `cTao` (byte-identical body) + the theorem over the
    challenge vocabulary, sorry-by-design; `config.json` lists the new name;
    `Solution.lean` untouched.
- Evidence (believed clean, judge to verify): `tao_stmt_diff.py` 31/31 byte-identical on
  every commit; `lean-axiom-gate --exact -i TaoCollatz.Statement` ✓ on all three headlines
  (note: pass `-i TaoCollatz.Statement`; the default root-lib import chokes on the
  sourceless `Comparator` lib name); `TaoCollatz/` greps 0 real sorries (12 grep hits are
  stale docstring prose only).

## Next lap

1. **STEP 4 is OPERATOR-GATED and flagged READY** in PENDING_WORK.md — ship-PR + PR #6
   note update belong to the host. Nothing development-side remains in the DIRECTION scope.
2. If DIRECTION is unchanged when you land: there is no open `c`-path work. Do NOT invent
   side quests (Sec6/Sec7/`C`-side are forbidden drift). Check DIRECTION for a new
   directive first; absent one, judge-support work (e.g. keeping ledgers accurate) only.

## Gotchas hit this lap

- `div_le_div_iff` does not exist under that name in this mathlib — use
  `one_div_le_one_div_of_le` + `nlinarith`, or `gcongr`.
- `gcongr` on `a / L / 20 ≤ b / L / 20` discharges everything from context (h1 + log 2 > 0
  via positivity); appending `<;> linarith` FAILS the build ("linarith does nothing").
- `lean-axiom-gate` needs `-i TaoCollatz.Statement` in this repo (see above).
- Unused-binder linter is warningAsError: an unreferenced `(hc₀ : 0 < c₀)` hypothesis
  fails the build — the spine weakening lemma deliberately takes only `c₀ ≤ c_ladder`.
