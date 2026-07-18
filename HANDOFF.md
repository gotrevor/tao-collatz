# HANDOFF — Tier-1 tower tightening, lap 0 (operator prep, 2026-07-18) 🗼

**Fresh campaign.  Read `DIRECTION.md` (the directive) + `TIER1-TOWER-TIGHTENING-PLAN.md`
(the spec) before doing anything.**  The previous campaign (assembled big-C) is ratified,
merged (PR #10), and closed; its handoffs live in `archive/handoff/` and its DIRECTION in
git history.  Nothing from it is live work.

## State at prep

- Branch `tier1-tower-tightening`, off merged main `4dde699` (post-#10:
  `CTao := hyperoperation 4 10 63`, `tao_collatz_quantitative_fully_explicit` proved).
  Build green at baseline; `TaoCollatz/` **0 sorries**; differ baseline `4dde699`.
- `BigCTower.lean` (3256 lines) carries the 242-step `_succ` climb to `tenTower 62` —
  all slop except the cubic `encWindowIter` recurrence (2 real levels).  The honest height
  is 3: check19's `log₁₀log₁₀ C_renewalWhite ≈ 10^3009.5` + the plan's §1 argument.
- **Nothing has been started on the calculus.**  Lap 1 = the Design B lemma bank in
  `Basic/ExplicitConstants.lean` + the POC gate (`C_fpLocation` cluster, `8 → ≤ 3`).
  Do not touch downstream clusters before the POC is green.

## Next

1. Calculus bank (4 batched lemmas) — plan §2 Design B.
2. POC: `C_fpLocation ≤ tenTower 2` (or `3`).  Green → phase 2.  Fights → `JUDGE-FLAG:` +
   `box stuck`.
3. Phase 2 bottom-up per plan §3; `check28` with the ceiling restatement.
