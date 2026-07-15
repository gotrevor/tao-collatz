# Handoff: C9 B1 CLOSED — rib 1 proved, B1 assembly fully axiom-clean

**Date**: 2026-07-15. **Branch** `main`, **HEAD `bafc3fb`**. Build 🟢 green (full `lake build`,
3324 jobs). Tree clean.
**Read `DIRECTION.md` first** — CURRENT DIRECTIVE = close C9 → C6 → headline.

## This lap: rib 1 `perNHarmonic_eq_sum_cn` PROVED → **B1 (the (5.20) geomHalf→syracZ reindex) is DONE**

Executed the prior handoff's plan exactly; compiled on the first build.

- Added hypotheses `(hx : Real.exp 1024 ≤ x) (hkn : n - mZero x ≤ nZero x)` to the rib-1 statement
  (internal decomposition below the `stabilization` pin — allowed). Needed because `E'` must dominate
  the modulus: `cn_window_size hx hkn` (i) gives `2·3^k+2 ≤ lo ≤ M`, so `3^k ≤ M`, so the affine size
  guard `fnat ≤ M·2^{pre}` is automatic (`fnat_lt_pow_mul`) and `solvable_iff_fmapZ` applies.
- Proof: LHS mask `good∧E'∧dvd∧guard` rewritten per-(ā,M) to the residue fiber `good∧E'∧(M:ZMod)=F ā`,
  inner M-sum factored via `tsum_mul_left`; RHS per-X `perNGoodMass·cn` pushed into the ā-tsum
  (`← tsum_mul_right`), swapped via `Summable.tsum_finsetSum` (summability from `iid_fiber_summable`
  + the good⟹iid-mass pointwise congr), collapsed by `Finset.sum_ite_eq` at `X = F ā`; `ring`.
- Assembly `perNHarmonic_eq_harmZfine_approx`: statement UNTOUCHED (it's the B1 pin); only its `x₀`
  raised `exp 1 → exp 1024` and the two hypotheses passed (`hkn` via `mem_Iy_le_nZero hn`).
- `#print axioms`: both `perNHarmonic_eq_sum_cn` and `perNHarmonic_eq_harmZfine_approx` →
  `[propext, Classical.choice, Quot.sound]` — believed clean, judge to verify.

## State: **5 sorries + 0 orange**

B1 + B2 both done ⇒ `harmonic_to_Z` (the (5.20) C10 seam, the directive's single objective) rests
only on the three self-contained leaves. All in `Sec5/Stabilization.lean` except headlines:

1. `perNTerm_harmonic_approx` (:328) — (5.19) analytic layer: perNTerm → perNHarmonic/norm. Likely
   the hardest remaining (pointmass + windowMass estimates all exist per its docstring; assembly work).
2. `Iy_count_ratio` (:1434-ish, grep) — (5.9) lattice/window count.
3. `mainZ_bound` (:302) — |mainZ| ≤ C, crude harmonic bound (mirror `cn_bound`'s integral test at
   coarse scale m₀; likely the easiest).
4. `Statement.lean:24,31` — frozen headlines; discharge when C6 lands.

## Next steps

1. Attack the three C9 leaves (directive's forbidden-drift clause is now MOOT — `harmonic_to_Z`'s
   structural content is fully decomposed and proved; the leaves are the remaining C9 work).
   Suggested order: hardest-first = `perNTerm_harmonic_approx`, but all three are route-safe.
2. Then C9 assembly axiom-clean → C6 (§3 reduction Thm 1.3 ⟸ 1.6 ⟸ 3.1 ⟸ Prop 1.11) → headline.

## Rails
- Do NOT edit ratified pins (C7/C8/C10 statements, `stabilization`, headlines) or frozen constants.
- `git-safe` at `~/personal/bin/git-safe`; bare `git` hook-blocked. Axiom recipe: `ZZ_ax.lean` +
  `lake env lean` + `rm`.
