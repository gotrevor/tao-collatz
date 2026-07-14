import TaoCollatz.Sec6.MixingCore

/-! The main-density branch of the §6 conditioning proof. -/

open scoped BigOperators

namespace TaoCollatz

/-- The tight valuation window used by `mainHigh` is nonempty-compatible for all sufficiently
large `n`: its quadratic-in-`C_A` logarithmic loss is eventually dominated by the linear main
term. This discharges the `hwin` hypothesis of `lRange_hbudget`; no numerical cutoff is exposed. -/
theorem eventually_ca_window (A : ℝ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ((caConst A) ^ 2 - 2 * caConst A) * Real.log (n : ℝ)
        ≤ (n : ℝ) * Real.log 3 / Real.log 2 := by
  let D : ℝ := (caConst A) ^ 2 - 2 * caConst A
  have hC : 30 ≤ caConst A := caConst_ge_thirty A
  have hD : 0 < D := by
    dsimp [D]
    nlinarith
  obtain ⟨n₀, hn₀⟩ := log_le_eps_mul_of_large D⁻¹ (inv_pos.mpr hD)
  refine ⟨n₀, fun n hn => ?_⟩
  have hlog := hn₀ n hn
  have hDn : D * Real.log (n : ℝ) ≤ (n : ℝ) := by
    calc
      D * Real.log (n : ℝ) ≤ D * (D⁻¹ * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog hD.le
      _ = (n : ℝ) := by rw [← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hratio : (n : ℝ) ≤ (n : ℝ) * Real.log 3 / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlog23 (Nat.cast_nonneg n)
  change D * Real.log (n : ℝ) ≤ _
  exact hDn.trans hratio

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
