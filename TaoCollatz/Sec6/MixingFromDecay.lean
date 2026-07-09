import TaoCollatz.Fourier.ZMod3
import TaoCollatz.Syracuse.SyracRV
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §6: fine-scale mixing from character decay (node C10) — statement of Prop 1.14

Paper anchor: Tao 2019 §6, Proposition 1.14 (deduced from Prop 1.17 via Plancherel).
Statement only (`sorry`).
-/

namespace TaoCollatz

/-- **Proposition 1.14** (fine-scale mixing): the `Syrac(ℤ/3ⁿℤ)` density oscillates
little at scale `3ᵐ`, uniformly with polynomial decay `m^{-A}` for every `A`. -/
theorem fine_scale_mixing (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A) := by
  sorry

end TaoCollatz
