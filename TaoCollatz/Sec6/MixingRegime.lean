import TaoCollatz.Sec6.MixingCore

/-! The scale-telescope branch of the §6 proof. -/

namespace TaoCollatz

/-- **(6.1) the regime reduction** (C10, obligation 0): the general bound for all `1 ≤ m ≤ n` follows
from the high-regime bound (`0.9n ≤ m ≤ n`, large `n`). Tao p.28: once (1.23) holds in the regime
`0.9n ≤ m ≤ n`, the (1.22)-consistency telescope across scales gives it for general `10 ≤ m ≤ n`, and
`1 ≤ m < 10` follows trivially from the triangle inequality; the finitely many small `n < n₀` are
absorbed by the trivial `osc ≤ 2` bound (a probability density has total mass ≤ 1) into a large constant. -/
theorem osc_syracZ_regime_telescope (A : ℝ) (hA : 0 < A)
    (hhigh : ∃ C > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, ∀ hmn : m ≤ n, n₀ ≤ n → 9 * n ≤ 10 * m →
        osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A)) :
    ∃ C > 0, ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A) := by
  sorry

end TaoCollatz
