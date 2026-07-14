import TaoCollatz.Sec6.MixingCore

/-! The main-density branch of the §6 conditioning proof. -/

open scoped BigOperators

namespace TaoCollatz

/-- **Obligation 1+2 (main term)**: the oscillation of the §6 main density is polynomially small in
the high regime. This is (6.10)+(6.11) [per-conditioning osc `≤ D·√(3ⁿ2⁻ˡ)`, obl-3 DONE] summed over
the `(k,l)` partition via `osc_mainDensity_le` [k-sum cast, DONE] with `D = C_A·q⁻ᴬ` [obl 2, `hunif`
from `head_factor_norm_le_charFn`], then the geometric `l`-sum `∑ √(2⁻ˡ)` + `k`-count + the constant
chase absorbing `n^{O(C_A²)}` into a larger characteristic-function exponent `A′`. -/
theorem osc_mainHigh_bound (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, ∀ hmn : m ≤ n, n₀ ≤ n → 9 * n ≤ 10 * m →
      osc m n hmn (mainHigh A n) ≤ C * (m : ℝ) ^ (-A) := by
  sorry

end TaoCollatz
