# Handoff: C8 assembly wired + 2 of 3 legs proved — C8 down to 2 sorries

**Date**: 2026-07-15. **Branch** `main`, **HEAD `d6ea49d`**. Build 🟢 green (full `lake build`,
3322 jobs, pre-commit verified). Tree clean.
**Read `DIRECTION.md` first** — its CURRENT DIRECTIVE outranks this doc. Order:
**C10 ✅ → C8 (pin ✅) → C7 (prove ✅) → C8 close (IN PROGRESS, ~66% of the analytic content proved) → C9**.

## What this lap did (3 green commits, all on C8 = Prop 5.2 / (5.8))

1. **`e7353aa`** — PROVED **`goodTuple_prefix_dev_sum`** (the (5.12) analytic core). This makes
   **`approx_good_tuple_whp` (5.12) fully axiom-clean** (`#print axioms` = `[propext,
   Classical.choice, Quot.sound]`). Route insight: transfer the length-`n₀` valuation vector ONCE
   (`valuation_dist 1 K` at `n'=3n₀`, one dTV `≪ 2^{-cd n₀}`), then push the geomHalf prefix marginal
   `iidMap_pre'` to `iidSum geomHalf n` and apply the two-sided `geomHalf_tail_bound` per prefix. Per-prefix
   `valuation_dist` at length `n` does NOT work (its dTV sum is a constant geometric series). Banked
   reusable analytic glue: `log_le_eps_mul_real`, `log_rpow_mul_exp_neg_le_one` (poly-log ≪ stretched
   exp), `Gweight_prefix_decay`, `iid_prefix_twosided_eq`, `pre_eq_fin_sum_castLE'`/`iidMap_pre'`.
2. **`b7bd6fb`** — PROVED the **`first_passage_approx` assembly skeleton**. Introduced bridge def
   **`firstPassMid`** (= `ℙ(Pass∈E)` restricted to `good`, partitioned by `T_x=n` over `I_y`) and
   proved `first_passage_approx` as the triangle `|ℙ−mid| + |mid−approxMainTerm|` (`abs_sub_le` +
   `min c₁ c₂`, mirrors `approx_passtime_window`). **This confirms the pinned `approxMainTerm`
   typechecks through the assembly** — route-decisive concern now isolated in ONE leg. `#print axioms`
   first_passage_approx = trust base + `sorryAx` (the two legs only). Moved `first_passage_approx` to
   the END of the file (after its sub-lemmas); a pointer comment remains at its old location.
3. **`d6ea49d`** — PROVED **`first_passage_window_reduce`** (leg 2, `|ℙ(Pass∈E) − firstPassMid| ≤
   C log^{-c}x`). Collapse `firstPassMid` to the single event `ℙ({T_x∈Iy ∧ Pass∈E ∧ good})` via
   `Summable.tsum_finsetSum` + disjointness of `{T_x=n}`; pointwise-dominate
   `ind{Pass∈E} ≤ ind Sbig + ind¬good + ind¬window`; `Sbig ⊆ {Pass∈E}` makes the abs the nonneg
   difference bounded by the two PROVED whp lemmas. Axiom-clean modulo `passtime_window_inner`.

## C8 = `first_passage_approx` — 2 remaining sorries (both `Sec5/ApproxFormula.lean`)

Hardest-first (full attack plans in PENDING_WORK.md top):

1. **`first_passage_affine_reindex`** (:874) — **ROUTE-DECISIVE**, leg 1 of the assembly.
   `|firstPassMid − approxMainTerm| ≤ C log^{-c}x`. Two sub-steps:
   - (5.17) `B_{n,y}` step-back-`m₀` event identity: for `n∈Iy`, `{T_x=n ∧ Pass∈E ∧ good}` =
     `{Syr^{n-m₀}N ∈ E' ∧ good}` (E' = `Eprime`). **EXACT** — attack THIS first, via
     `syr_iterate_key` / `passTime` / `passLoc` / `Eprime` defs. The `Eprime` size bounds come from
     the (5.13/5.14) good-tuple orbit estimate (`Syr^{n-m₀}N ≈ (3/4)^{n-m₀}N_y`) — that estimate is
     the analytic sub-hole here; the pure event-algebra "step back" is exact.
   - (5.18) Lemma 2.1 affine reindex: `ℙ({Syr^{n-m₀}N∈E'} ∧ good) → ∑_ā∑_M ℙ(Aff_ā(N_y)=M)` (the
     `approxMainTerm` summand). **APPROXIMATE** — `Aff` uses truncating ℕ-÷; truncation coincidences
     absorbed in `O(log^{-c}x)`. Kernels `aff_valVec_eq_syr` (✅) + `valVec_unique` (✅) drive the main
     term. **Do NOT attempt an exact `=` reindex** (see module docstring + PENDING "ROUTE-DECISIVE INSIGHT").
2. **`passtime_window_inner`** (:640) — (5.16) window term ONLY: `{passes ∧ T_x∉Iy}`, the integral
   test that `N_y` avoids the `2 log^{0.8}x` edge collars; reuse C7's `classMass`/`windowMass`/`intTest_*`
   machinery in `Sec5.FirstPassage`.

Then **C9 = `stabilization`** (`FirstPassage.lean:1343`, Prop 1.11, consumes C10 ✅ + C8).

## Reusable helpers banked this session (all in `ApproxFormula.lean`, axiom-clean unless noted)
- Analytic: `log_le_eps_mul_real`, `log_rpow_mul_exp_neg_le_one`, `Gweight_prefix_decay`.
- Marginal: `pre_eq_fin_sum_castLE'`, `iidMap_pre'` (inline copies of Sec6 lemmas — Sec6 not imported
  here), `iid_prefix_twosided_eq`.
- Bridge def `firstPassMid`; the two legs `first_passage_window_reduce` (✅ proved) and
  `first_passage_affine_reindex` (owed).

## Rails / notes
- **Truncation insight** (module docstring + PENDING): the (5.18) reindex is `≤`/approximate, never
  `=`. A grind lap that tries an exact reindex identity WILL fail on the truncation set.
- `linarith`-rpow-poison gotcha (auto-memory `lean-linarith-decimal-rpow-poison`) still applies.
- Watched statements (`fine_scale_mixing`/`stabilization`) + all ratified pins + RATIFY-C8
  statements/defs UNTOUCHED. Never set `\leanok` yourself. Judge to flip C7/C10 `\leanok` and ratify
  the new C8 sub-lemma pins.
- Axiom-check recipe: write `TaoCollatz/ZZ_ax.lean` importing the module with `#print axioms <name>`,
  `lake env lean` it, then `rm -f` (don't leave it — breaks the build tree).
- `git-safe` at `/Users/gotrevor/personal/bin/git-safe` (`export PATH="$HOME/personal/bin:$PATH"`).
- Work report: **2 sorries + 0 orange nodes** in C8 (`first_passage_affine_reindex`,
  `passtime_window_inner`); C8's overall assembly is proved, only these two legs/cores remain.
