# Handoff: 🏆 C8 CLOSED, AXIOM-CLEAN — next = C9 `stabilization`

**Date**: 2026-07-15. **Branch** `main`, **HEAD `39aeadc`**. Build 🟢 green (full `lake build`, 3323
jobs; pre-commit verified every commit). Tree clean, nothing uncommitted.
**Read `DIRECTION.md` first** — CURRENT DIRECTIVE (JUDGE PASS 30 + this session's review refresh) outranks
this doc. Campaign order: C10 ✅ → C8 (pin ✅) → C7 ✅ → **C8 close ✅ (THIS SESSION)** → **C9** → C6 → headline.

## What this session did — CLOSED C8 (`first_passage_approx` = Prop 5.2 / (5.8))

Started as a review lap with C8 down to one hole (the 5.17 reverse leg `steppedMid_le_firstPassMid_add`).
Closed it fully. `#print axioms first_passage_approx = [propext, Classical.choice, Quot.sound]` (verified).

Six green commits (all axiom-clean unless noted):
1. `ad7a1d3` — review: narrowed DIRECTION to the reverse leg; recorded the **CaseA/CaseB** split +
   roadmap correction (handoff step 2b's "`approx_passtime_window` covers Case B" was FALSE — disjointness
   only holds on Case A `n−m₀ ≤ T_x N`). Refreshed STATUS.md.
2. `bb0c567` — PROVED the reverse-leg **structural reduction**. Pointwise ternary domination
   `𝟙_{T_n} ≤ 𝟙_{S_n} + 𝟙_{¬good⁽ⁿ⁰⁾∧T_x=n} + 𝟙_{E′∧T_x<n−m₀}`; Case-A middle sets collapse EXACTLY
   (disjoint `T_x=n`) to `E[𝟙_{¬good}] ≤ C log^{-c}` via `approx_good_tuple_whp`. New axiom-clean helpers
   `sum_expect_le_of_indicator_ge` (reverse finite union bound for `PMF.expect`), `passes_of_eprime`.
3. `d0e3ac9` — **KEY INSIGHT**: keep the `good⁽ⁿ⁻ᵐ⁰⁾` conjunct (available since `N ∈ T_n`). A good orbit
   decreases (`syr^[j]N ≈ (3/4)^j N`), so after passing (`≤ x` at `T_x N < n−m₀`) it sits below
   `(3/4)x·2^{2log^{0.6}x}`, FAR under the `E′` floor `exp(−log^{0.7}x)(4/3)^{m₀}x ≈ x^{1+δ}`. So the
   early-return event is **EMPTY** for large x → `reverse_early_return_whp` proved by an empty-set argument
   (`expect_mono_on_support` to `∅`), modulo one deterministic inequality.
4. `0bea9d1` — PROVED that inequality `earlyReturn_size_contra` (pure real analysis, no probability/orbits):
   `(4/3)^{m₀} ≥ exp(log(4/3)(βL−1))` (floor bound, `β=(α−1)/100=1/100000`); bound both sides to `exp(·)`,
   reduce to the master polynomial `log2 + 2L^0.6 log2 + L^0.7 + log(4/3) < β log(4/3) L`, closed via
   `5 L^0.7 < β log(4/3) L` (from `L = L^0.7·L^0.3` and `L^0.3 > 5/(β log(4/3))` at the chosen threshold).
   → **C8 axiom-clean.**
5–6. `d0e3ac9`/`39aeadc` docs (PENDING_WORK: C8-closed + JUDGE-FLAG + C9 attack plan).

## State: 3 sorries + 0 orange nodes
- `Statement.lean:24,31` — the two headline stubs (Thm 1.3 / Thm 3.1), frozen; discharge when C6 lands.
- `Sec5/FirstPassage.lean:1399` — **C9 `stabilization`** (Prop 1.11), consumes C10 ✅ + C8 ✅ (both PROVEN).

## 🚩 JUDGE-FLAG (directive event-trigger b — do this before heavy C9 work)
C8's last hole just closed. **Ratify `first_passage_approx` as PROVEN + flip its proof `\leanok`** before
C9 switches from *citing* C8's statement to *using* its theorem. Worth a paper cross-check on
`earlyReturn_size_contra` (the E′ `(4/3)^{m₀}x` floor vs the decreasing good-orbit ceiling — pp.23–24,
(5.10)/(5.13)–(5.16)); it is a deterministic real inequality, not in `check_blueprint.py` yet.

## Next steps — C9 `stabilization` (Prop 1.11)
Directive step 1 (the **C9 assembly-spine PROBE**) was never done — do it FIRST (it's the single highest
de-risk move now that both inputs are proven theorems):
1. In `Sec5/FirstPassage.lean` / `Stabilization.lean`, state Lemma 5.3 (`c_n(X) ≪ 1`) and (5.18)–(5.21) as
   **sorried local lemmas**, and make the Prop 1.11 (`stabilization`) assembly **compile** using
   `first_passage_approx` (C8) and `fine_scale_mixing` (C10 = `Sec6/MixingFromDecay.lean:29`) as black
   boxes. SEAM TEST, ~1–2 laps, NOT a proof.
2. ⚠ **If the C8/C10 interfaces do NOT fit** (quantifier order, uniformity in `n`, normalization) →
   `JUDGE-FLAG:` the exact mismatch. Do NOT edit the ratified C8/C10 pins. Decomposing *below*
   `stabilization` is fine; the pin is WATCHED.
3. If the assembly compiles, C9 reduces to filling the sorried ribs → then C6 (§3 reduction) → headlines.

## Rails / notes
- **Do NOT edit ratified pins** (`Eprime`, `Iy`, `firstPassMid`, `steppedMid`, `approxMainTerm`,
  C8/C7/C10 statements, `stabilization`, the two headlines). Constants FROZEN: `epsBW=1/10^1000`,
  `caConst=30`, `alpha=1.001`.
- `git-safe` at `/Users/gotrevor/personal/bin/git-safe` (`export PATH="$HOME/personal/bin:$PATH"`).
  Axiom-check recipe: write `TaoCollatz/ZZ_ax.lean` importing the module with `#print axioms <name>`,
  `lake env lean` it, then `rm -f` (don't leave it — breaks the build tree).
- Gotchas hit this session (corpus-worthy): `gcongr` on a triple product `a*b*c ≤ a*b'*c'` can mis-split
  (produced ONE goal not two) — use explicit `mul_le_mul (mul_le_mul_of_nonneg_left …) … (by positivity)`.
  `div_mul_cancel₀ 5 (h : d ≠ 0) : 5/d * d = 5` works; `positivity` proves the `≠ 0`. Decimal-rpow
  (`Real.log x ^ (0.6:ℝ)`): `set L06 := …` and feed `nlinarith` products as explicit hints; the exponent
  split `L^0.7 * L^0.3 = L` via `← Real.rpow_add … ; show (0.7:ℝ)+0.3=1 by norm_num; Real.rpow_one`.
- **Work report: 3 sorries + 0 orange.** C8 (Prop 5.2) CLOSED + axiom-clean this session; only C9 + the two
  frozen headline stubs remain before the §3 reduction (C6) and the final headline assembly.
