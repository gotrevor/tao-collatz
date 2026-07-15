# Handoff: C9 crux DECOMPOSED — assembly proved, 3 faithful analytic leaves remain

**Date**: 2026-07-15. **Branch** `main`, **HEAD `663ac1d`**. Build 🟢 green (full `lake build`, 3324
jobs; pre-commit verified every commit). Tree clean, nothing uncommitted.
**Read `DIRECTION.md` first** — CURRENT DIRECTIVE (JUDGE PASS 30 + review refresh) outranks this doc.
Campaign order: C10 ✅ → C8 ✅ → C7 ✅ → **C9 (this session's focus)** → C6 → headline.

## What this session did — attacked C9 `stabilization` (Prop 1.11) end-to-end

Five green commits, all building on the prior. C8/C10 were already PROVEN (axiom-clean) coming in.

1. `12d62f0` — **C9 assembly-spine PROBE (directive step 1): the seam FITS.** Created
   `Sec5/Stabilization.lean` (imports `Sec5.ApproxFormula` + `Sec6.MixingFromDecay`). **Relocated
   `stabilization` there VERBATIM** from `FirstPassage.lean` — statement byte-identical (differ ✅
   character-identical; RATIFY-3 preserved) — because C8/C10 are both DOWNSTREAM of FirstPassage
   (import cycle otherwise). Differ `SEARCH_FILES` + root `TaoCollatz.lean` import updated to follow
   the pin. `stabilization` proved modulo 2 ribs; the C8 leg composed with ZERO interface friction.
2. `cfdaa70` — **C9 rib 1 CLOSED axiom-clean**: `dTV_passLoc_event_witness` (Hahn sign-split
   `∑|P₁−P₂| = 2∑max(P₁−P₂,0)`, witnessed by odd event `E⊆[1,x]`; passLoc pushforward supported on
   odds ≤x). Banked reusable helpers `expect_map_indicator`, `passLoc_odd/le/le_cast`.
3. `f327547` — **rib 2 refactored to the paper's actual mechanism.** Source-read PDF pp.25–27:
   `ℙ(Pass∈E) = (1+O)(2/log(4/3))·Z + O(log^{-c})` where **`Z` (5.21) is WINDOW-INDEPENDENT** — the
   `log y`,`(α−1)` cancel against `#I_y` (5.9). Defined `mainZ x E` (= Tao's Z), reduced rib 2
   (`approxMainTerm_window_stable`, now PROVED via a triangle) to the y-free `approxMainTerm_to_Z`.
4. `663ac1d` — **C9 crux DECOMPOSED + assembly PROVED.** `approxMainTerm_to_Z` now proved from 3
   faithful sub-lemmas; the (5.19)+(5.20)+(5.9) combination + log-cancellation is machine-checked.

## State: 5 sorries + 0 orange nodes  (`#print axioms stabilization` = trust base + sorryAx)

- `Statement.lean:24,31` — the two headline stubs (Thm 1.3 / Thm 3.1), frozen; discharge when C6 lands.
- **`Sec5/Stabilization.lean` — the 3 C9 leaves** (all faithful, precisely stated, and PROVABLY
  sufficient — the kernel checked the assembly wires them to `stabilization`):
  - **`perNTerm_eval` (:221)** — (5.19)+(5.20). Per-n term `= mainZ/((α−1)/2·log y)` up to relative
    `O(log^{-c})`. **THE hard leaf & the SOLE C10 consumer** (Lemma 5.3 `c_n≪1` + `fine_scale_mixing`).
  - **`Iy_count_ratio` (:233)** — (5.9). `#I_y/((α−1)/2·log y) = 2/log(4/3) + O(log^{-c})`. Pure
    lattice-count = interval length + O(1). **Cheapest, most self-contained leaf.**
  - **`mainZ_bound` (:244)** — `|mainZ x E| ≤ C` (Z = O(1)). Small.

The C9 spine is fully wired: `stabilization ← approxMainTerm_window_stable ← approxMainTerm_to_Z ←
{the 3 leaves}`. Everything ABOVE the leaves is proved.

## 🚩 JUDGE-FLAGS (open, for the judge — grind laps flag & continue)
1. **Ratify `first_passage_approx` (C8) as PROVEN + flip its proof `\leanok`** — blueprint_audit reports
   it MISSED FLIP (axiom-clean). C9 now *uses* its theorem. (Open since C8 closed last session.)
2. **Confirm the `stabilization` RELOCATION** `FirstPassage.lean` → `Sec5/Stabilization.lean` (statement
   byte-identical; forced by import acyclicity — C8/C10 are downstream). Differ SEARCH_FILES updated.
3. **`mainZ`, `perNTerm`, `approxMainTerm_to_Z` are new internal decompositions BELOW the ratified
   `stabilization` pin** (allowed). Not blueprint nodes; no numeric trap owed. `perNTerm_eval` /
   `Iy_count_ratio` / `mainZ_bound` render (5.19)/(5.20)/(5.9)/(5.21) — worth a judge cross-read vs pp.25–27.

## Next steps — fill the 3 C9 leaves (hardest-first = `perNTerm_eval`)
`perNTerm_eval` is route-decisive (the C10 consumer). Sub-decompose:
- **(5.19)** single-value mass: the affine event `3^{n−m₀}N+fnat=M·2^{pre ā}` has ≤1 solution `N*`;
  `logUnifOdd y (y^α) N* = (1/N*)/D`, `D = ∑_{odd N∈[y,y^α]} 1/N = (1+O(1/x))·(α−1)/2·log y`
  (harmonic-sum via integral test over odds — reuse C7's `intTest_*` in `FirstPassage.lean`).
- **(5.20)** `𝔼_{ā∼Geom(2)^{n−m₀}} c_n(F_{n−m₀}(ā) mod 3^{n−m₀}) = mainZ + O(log^{-c})`; Lemma 5.3
  `c_n≪1` via (5.25)/(5.26) integral test + CRT; **`fine_scale_mixing` makes `𝔼 c_n ≈ Z`**.
  ⚠ **SEAM-PROBE the `fine_scale_mixing` `osc m n (syracZ n density)` interface against (5.20) FIRST** —
  it is the route-decisive C9 unknown (analogous to this session's C8↔C9 probe).
- `Iy_count_ratio` + `mainZ_bound` are self-contained banks (lean on proved `mem_Iy_bounds`,
  `mem_Iy_le_nZero`, `mZero_le_of_mem_Iy`). Do them when `perNTerm_eval` stalls.

## Rails / notes
- **Do NOT edit ratified pins** (C7/C8/C10 statements, `stabilization`, the two headlines). Constants
  FROZEN: `epsBW=1/10^1000`, `caConst=30`, `alpha=1.001`. `git-safe` at `~/personal/bin/git-safe`.
- Axiom recipe: write `TaoCollatz/ZZ_ax.lean` importing the module + `#print axioms <name>`,
  `lake env lean` it, then `rm -f` (don't leave it — breaks the build tree).
- Gotchas this session (corpus-worthy): local dedup lemmas are `PMF.toReal_tsum_mul_ofReal` /
  `PMF.tsum_map_mul` (namespace `PMF`, not bare); `Summable.tsum_sub` is dot-form only (no free
  `tsum_sub`); triangle `|a+b|≤|a|+|b|` is **`abs_add_le`** (NOT `abs_add`) in this mathlib;
  `(x^a)^b=x^(a*b)` via `Real.rpow_mul hx0`; `open Classical in` must precede the DOCSTRING, not sit
  between docstring and def. `Real.log_rpow hxpos : log(x^a)=a*log x`.
- **Work report: 5 sorries + 0 orange.** C9 crux decomposed into 3 machine-checked-sufficient leaves;
  the full analytic assembly is proved. Only `perNTerm_eval` (C10 consumer), `Iy_count_ratio`,
  `mainZ_bound` remain before C9 is axiom-clean → then C6 (§3 reduction) → headline.
