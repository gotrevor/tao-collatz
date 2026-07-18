# HANDOFF — Tier-1 tower tightening, lap 0 (operator prep, 2026-07-18) 🗼

**Fresh campaign.  Read `DIRECTION.md` (the directive) + `TIER1-TOWER-TIGHTENING-PLAN.md`
(the spec) before doing anything.**  The previous campaign (assembled big-C) is ratified,
merged (PR #10), and closed; its handoffs live in `archive/handoff/` and its DIRECTION in
git history.  Nothing from it is live work.

## State at prep

- Branch `tier1-tower-tightening`, off merged main `4dde699`.  The campaign runs in the
  worktree `~/src/tao-collatz-tier1` (host-side note; in the box the repo mount is the
  same as always).  Everything merges via PR — main is protected.
- **The pin is PLANTED** (judge, 2026-07-18): `Statement.lean` has
  `CTao := hyperoperation 4 10 10` + `tao_collatz_quantitative_fully_explicit := sorry`
  (shielded); `Challenge.lean` matches in lockstep.  Comparator CI is RED until discharge
  — by design.  `TaoCollatz/` sorry census = **1** (the pin; was 0 post-#10).
  `tenTower_nine_eq_hyperoperation` (the `10↑↑10` bridge) is already proved in
  `Basic/ExplicitConstants.lean`.
- Build green (8600 jobs, planted-sorry warning is shielded).  Differ baseline = the plant
  commit ("plant the Tier-1 campaign pin"); expect 39/39 from there on.
- `BigCTower.lean` (3256 lines) carries the 242-step `_succ` climb to `tenTower 62` —
  all slop except the cubic `encWindowIter` recurrence (2 real levels).  Honest height 3:
  check19's `log₁₀log₁₀ C_renewalWhite ≈ 10^3009.5` + plan §1.
- **Nothing started on the calculus.**  Lap 1 = the Design B lemma bank + the POC gate
  (`C_fpLocation` cluster, `8 → ≤ 3`).  Do not touch downstream clusters before the POC
  is green.

## Next

1. Calculus bank (4 batched lemmas) — plan §2 Design B.
2. POC: `C_fpLocation ≤ tenTower 2` (or `3`).  Green → convert bottom-up (plan §3).
   Fights → `JUDGE-FLAG:` + `box stuck`.
3. Ceiling at the honest height + `check28`; **discharge the pin LAST** (removes the
   run's `--done-when` gate condition — see DIRECTION Stop discipline).
