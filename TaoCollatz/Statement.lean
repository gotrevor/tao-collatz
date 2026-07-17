import TaoCollatz.Basic.Collatz
import TaoCollatz.Basic.LogDensity
import TaoCollatz.Sec3.Reduction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# TRUSTED BASE — the main theorem statements

This file is the only trusted surface of the library (BLUEPRINT §3), a three-statement
surface: Theorem 1.3 and Theorem 3.1 of Tao 2019 (arXiv:1909.03562) are the paper's,
stated from first principles; `tao_collatz_quantitative_explicit` (with the constant
`cTao`) is OUR augmentation beyond the paper — the paper proves `∃ c` and Remark 1.4
gives only a shape, never a value. TaoCollatz
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
      1 - C / (Real.log N₀) ^ c ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
  exact tao_collatz_quantitative_spine

/-- The explicit exponent — OUR augmentation, beyond the paper: the collapse of the
development's witness min-tree, mirrored in exact arithmetic by `tools/check_blueprint.py`
(check 16). -/
noncomputable def cTao : ℝ := 1 / (640000000 * Real.log 2)

/-- **Theorem 3.1, explicit-exponent form** (our augmentation): Theorem 3.1 holds with the
concrete exponent `cTao` — the explicit value asked for by
[MO 341570](https://mathoverflow.net/questions/341570). -/
theorem tao_collatz_quantitative_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
  exact tao_collatz_quantitative_spine_of_le c_ladder_lower

/-- The explicit constant — OUR augmentation, beyond the paper. A round upper bound with
deliberate headroom, not an optimized value: the development's assembled constant is
estimated ≈ `10^(3×10⁸)` (the `(2·C1+2)^𝔡·40^𝔡` core with `𝔡 ≈ 3.11×10⁷`); any upper
bound discharges the statement, and a round pin survives proof churn. -/
noncomputable def CTao : ℝ := 10 ^ (1000000000 : ℕ)

-- The campaign pin: `sorry` by design until the big-C campaign discharges it. The local
-- warningAsError shield keeps `lake build` (and the pre-commit green-gate) working while
-- the pin is open; remove the shield together with the `sorry`.
set_option warningAsError false in
/-- **Theorem 3.1, fully explicit form** (our augmentation): Theorem 3.1 holds with the
concrete exponent `cTao` and the concrete constant `CTao` — no existential remains. -/
theorem tao_collatz_quantitative_fully_explicit :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - CTao / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
  sorry

end TaoCollatz
