import TaoCollatz.Basic.Collatz
import TaoCollatz.Basic.LogDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §3 reduction — the C6 intermediates (Thm 3.1 Syracuse form, Thm 1.6, the (1.2) bridge)

Pins for the §3 chain `Prop 1.11 ⟹ Thm 3.1 (Syracuse) ⟹ Thm 1.6 ⟹ Thm 1.3`, plus the
(1.2) odd-part reduction that converts each Syracuse claim to its Collatz form. Every
theorem here is a sorried STATEMENT (blueprint pin), written copy-not-compose against
arXiv:1909.03562v5 §1.2 (pp.4–5) and §3 (pp.16–18). Numeric traps: `check14`/`check15`
in `tools/check_blueprint.py`.

Pinned this lap (2026-07-15); NOT yet judge-ratified. JUDGE-FLAG: ratify-on-pin owed.

Statement notes for the judge (faithfulness choices, flagged, not silently made):
* `tao_syracuse` takes `f : ℕ → ℝ` with `Tendsto f atTop atTop` where the paper's
  `f : 2ℕ+1 → ℝ` has `lim_{N→∞} f(N) = ∞` along odd `N`. The two forms are equivalent:
  the conclusion only samples `f` at odd `N`, and any paper-`f` extends to all of `ℕ`
  (constantly on evens between consecutive odds) preserving the limit. This mirrors the
  frozen `tao_collatz` headline's rendering of Thm 1.3's hypothesis.
* Thm 3.1's two displays ("… or equivalently …", p.16) are BOTH pinned
  (`tao_syracuse_quantitative_sum`, `tao_syracuse_quantitative`): the sum form is what
  the dyadic covering argument produces and what the (1.2) pullback consumes; the
  probability form mirrors the frozen `tao_collatz_quantitative` headline. Their
  equivalence (normalize by the odd-window harmonic mass ≍ log x) is part of the C6
  proof obligation, not assumed.
-/

namespace TaoCollatz

open Filter

/-- **Theorem 3.1, Syracuse sum form** (Tao 2019 p.16, first display):
`∑_{N ∈ 2ℕ+1 ∩ [1,x], Syrmin(N) > N₀} 1/N ≪ log x / (log N₀)^c`. -/
-- RATIFY-C6a
theorem tao_syracuse_quantitative_sum :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      logSum {N | N₀ < syrMin N} (oddInterval x)
        ≤ C * Real.log x / (Real.log N₀) ^ c := by
  sorry

/-- **Theorem 3.1, Syracuse probability form** (Tao 2019 p.16, second display):
`ℙ(Syrmin(Log(2ℕ+1 ∩ [1,x])) ≤ N₀) ≥ 1 − O(log^{-c} N₀)`. -/
-- RATIFY-C6b
theorem tao_syracuse_quantitative :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ c ≤ logProb {N | syrMin N ≤ N₀} (oddInterval x) := by
  sorry

/-- **Theorem 1.6** (Tao 2019 p.4): for `f` with `f(N) → ∞`, almost all odd `N`
(log density on the odd window) satisfy `Syrmin(N) < f(N)`. -/
-- RATIFY-C6c (domain-of-`f` rendering flagged in the module docstring)
theorem tao_syracuse (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) :
    AlmostAllOdd fun N => (syrMin N : ℝ) < f N := by
  sorry

/-! ## The (1.2) odd-part reduction — bridge lemmas

Worker-authored internal decomposition (below the C6 pin, not paper-numbered displays):
the two forms of "by (1.2), pass to odd parts" used on p.5 (Thm 1.6 ⟹ Thm 1.3) and
p.16 ("In particular, by (1.2)…"). Both rest on the PROVED `colMin_eq_syrMin_oddPart`
and the 2-adic splitting `∑_{N ≤ x, oddPart N ∈ A} 1/N = ∑_a 2^{-a} ∑_{M ∈ A ∩ 2ℕ+1,
2^a M ≤ x} 1/M ≤ 2 ∑_{M ∈ A ∩ 2ℕ+1 ∩ [1,x]} 1/M`. -/

/-- Quantitative (1.2) pullback: the full-window log-mass of an odd-part preimage is at
most twice the odd-window log-mass of the set (geometric series over `ν₂`). Feeds the
Colmin forms of Thm 3.1 from the Syracuse forms. -/
theorem logSum_oddPart_pullback (A : Set ℕ) (x : ℕ) :
    logSum {N | oddPart N ∈ A} (posInterval x) ≤ 2 * logSum A (oddInterval x) := by
  sorry

/-- Qualitative (1.2) reduction (paper p.5, ¶ after Thm 1.6): an almost-all-odd property
pulls back along `oddPart` to an almost-all property on `ℕ+`. -/
theorem almostAllPos_oddPart_of_almostAllOdd (P : ℕ → Prop) (h : AlmostAllOdd P) :
    AlmostAllPos fun N => P (oddPart N) := by
  sorry

/-! ## Spine — the headlines from the intermediates

Sorried wiring theorems, byte-identical in statement to the two frozen
`Statement.lean` headlines. When these close, the frozen sorries discharge by `exact`
(the ONLY edit `Statement.lean` ever receives). Proof routes, per §3:
* quantitative spine: `tao_syracuse_quantitative_sum` + `logSum_oddPart_pullback` +
  `colMin_eq_syrMin_oddPart` + harmonic-mass bounds on `posInterval`.
* headline spine: apply `tao_syracuse` at `f̃(M) := inf {f N | N ≥ M}` (which still
  `→ ∞`), then `almostAllPos_oddPart_of_almostAllOdd` + `oddPart N ≤ N` gives
  `colMin N = syrMin (oddPart N) < f̃ (oddPart N) ≤ f N`. -/

/-- Spine for **Theorem 1.3**: statement identical to the frozen `tao_collatz`. -/
theorem tao_collatz_spine (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) :
    AlmostAllPos fun N => (colMin N : ℝ) < f N := by
  sorry

/-- Spine for **Theorem 3.1 (Colmin form)**: statement identical to the frozen
`tao_collatz_quantitative`. -/
theorem tao_collatz_quantitative_spine :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ c ≤ logProb {N | colMin N ≤ N₀} (posInterval x) := by
  sorry

end TaoCollatz
