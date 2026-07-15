# Handoff: C8 event/skeleton layer DONE — 3 isolated analytic cores remain

**Date**: 2026-07-15. **Branch** `main`, **HEAD `c2052e3`**. Build 🟢 green (full `lake build`,
3322 jobs, pre-commit verified). Tree clean.
**Read `DIRECTION.md` first** — its CURRENT DIRECTIVE (top review-lap update, `810518b`) outranks this
doc. Order: **C10 ✅ → C8 (pin ✅) → C7 (prove ✅) → C8 close (IN PROGRESS) → C9**.

## Where we are: C7 done, C8 skeleton done

This was a review lap that verified **C7 `first_passage_nonescape` (1.19) is axiom-clean** (the stale
directive still listed C7 as live target) and retargeted to the **C8-close** leg. Then drove C8:
both pinned whp sub-lemmas of Prop 5.2 are now **proved modulo isolated analytic cores**, and C7 is
wired into C8. DIRECTION / STATUS / PENDING all refreshed this lap.

## What this lap did (3 green commits, all on the C8 crux)

1. **`4dc8616`** — review + retarget; proved Lemma 2.1 kernel **`aff_valVec_eq_syr`**
   (`Aff N k (valVec N k) = syr^[k] N`); banked the **truncation route-insight** (our `Aff` uses
   truncating ℕ-÷ vs Tao's exact ÷, so the (5.18) reindex is APPROXIMATE, absorbed in `O(log^-c x)`
   — NOT an exact identity; not a JUDGE-FLAG). See `ApproxFormula.lean` module docstring + PENDING top.
2. **`9e84cc9`** — proved **`approx_passtime_window` (5.16)**, the C7 consumer. Split the complement
   into disjoint `{¬passes} ⊕ {passes ∧ T_x∉Iy}`; `{¬passes}` = `first_passage_nonescape` (C7) via
   `escape_to_log`; isolated `passtime_window_inner` (window edges). **C8's C7-dependence discharged.**
3. **`c2052e3`** — proved **`approx_good_tuple_whp` (5.12)** skeleton via `not_goodTuple_iff_prefix_dev`
   (odd-support reduction) + even-mass=0 + Finset union bound; isolated `goodTuple_prefix_dev_sum`.

## C8 = `first_passage_approx` — 3 remaining sorries (all in `Sec5/ApproxFormula.lean`)

All three are now SHARP, independent cores (not opaque pins). Hardest-first order (PENDING top has the
full attack for each):

1. **`goodTuple_prefix_dev_sum`** (:241) — (5.12) analytic core: `∑_{n≤n₀} ℙ(|valSum N n − 2n| ≥
   log^0.6 x) ≤ C log^-c x`. **START HERE** — directly precedented by C7's `valSum_lower_geom`
   (`FirstPassage.lean:1013`, SAME machinery: `valuation_dist` transfer to `geomHalf.iid`, two-sided
   `geomHalf_tail_bound`, `Gweight`). Per prefix: transfer + prefix marginal (`pre a n` under
   `geomHalf.iid n₀` is `|Geom(2)_n|`; cf. C10 `iidMap_pre`) + `geomHalf_tail_bound` + `Gweight` sum.
2. **`passtime_window_inner`** (:332) — (5.16) window term: `{passes ∧ T_x∉Iy}`, the integral test
   that `N_y` avoids the `2 log^0.8 x` edge collars; reuse C7's `classMass`/`windowMass`/`intTest_*`.
3. **`first_passage_approx`** (:212) — the assembly. Step-4 `B_{n,y}` event chain (EXACT, no error:
   `syr_iterate_key` + `passTime`/`passLoc`/`Eprime` defs) then step-5 approximate affine reindex
   (`aff_valVec_eq_syr` + `valVec_unique`, truncation in the error per the INSIGHT). Read Tao pp.22–25
   (`papers/tao-2019-almost-all-orbits.pdf`) — I extracted the full proof; see PENDING "Tao's Prop 5.2
   proof → Lean decomposition".

Then **C9 = `stabilization`** (`FirstPassage.lean:1351`, Prop 1.11, consumes C10 ✅ + C8).

## Reusable helpers banked this lap (all axiom-clean, in `ApproxFormula.lean` shared-glue section)
- `aff_valVec_eq_syr`, `valVec_pos` (already existed in `ValuationDist.lean:393`),
- `expect_le_add_of_indicator_le`, `expect_le_sum_of_indicator_le` (PMF.expect subadditivity, binary +
  Finset), `escape_to_log` (`x^-c ≤ (log x)^-c` for `x≥e`), `not_goodTuple_iff_prefix_dev`.

## Rails / notes
- **Truncation insight is banked (PENDING + module docstring): the reindex is `≤`/approximate, never
  `=`.** A grind lap that tries an exact reindex identity will fail on the truncation set.
- `linarith`-rpow-poison gotcha still applies (auto-memory `lean-linarith-decimal-rpow-poison`):
  `y^alpha`/big-literal rpow atoms poison `linarith`; opaque them via `obtain ⟨Y,hY⟩ : ∃ Y, ... = Y`.
- Watched statements (`fine_scale_mixing`/`stabilization`) + all ratified pins + RATIFY-C8
  statements/defs UNTOUCHED. Never set `\leanok` yourself. Judge to flip C7 `\leanok`.
- Axiom-check recipe: write `TaoCollatz/ZZ_ax_check.lean` importing the module with `#print axioms
  <name>`, `lake env lean` it, then `rm -f` (don't leave it — breaks the build tree).
- Pre-existing `info: Error in Linarith.normalizeDenominatorsLHS` at `Prob/CharFn1.lean:166` is an
  info-level non-error (build stays EXIT 0); ignore.
- `git-safe` at `/Users/gotrevor/personal/bin/git-safe` (`export PATH="$HOME/personal/bin:$PATH"`).
