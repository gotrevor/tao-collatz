import TaoCollatz.Basic.Collatz
import TaoCollatz.Basic.LogDensity
import TaoCollatz.Sec3.Reduction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# TRUSTED BASE — the main theorem statements

This file is the only trusted surface of the library (BLUEPRINT §3): Theorem 1.3 and
Theorem 3.1 of Tao 2019 (arXiv:1909.03562), stated from first principles. TaoCollatz
imports here are ONLY `Basic.Collatz` + `Basic.LogDensity` (elementary defs: `col`,
`colMin`, log density via Finset sums and `Tendsto`); the mathlib `Pow.Real` import
supplies just the `rpow` notation used in Theorem 3.1's error term.

Axiom gate: `#print axioms tao_collatz` must be exactly
`[propext, Classical.choice, Quot.sound]` at campaign end.
-/

namespace TaoCollatz

/-- **Theorem 1.3** (Tao 2019): for any `f : ℕ → ℝ` with `f(N) → ∞`, almost all `N`
(in logarithmic density) satisfy `Colmin(N) < f(N)`. -/
theorem tao_collatz (f : ℕ → ℝ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    AlmostAllPos fun N => (colMin N : ℝ) < f N := by
  exact tao_collatz_spine f hf

/-- **Theorem 3.1** (Tao 2019, `Colmin` form): quantitative version — the log-probability
that `Colmin(N) ≤ N₀` on the window `[1, x]` is at least `1 - C/(log N₀)^c`. -/
theorem tao_collatz_quantitative :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ c ≤ logProb {N | colMin N ≤ N₀} (posInterval x) := by
  exact tao_collatz_quantitative_spine

end TaoCollatz
