import TaoCollatz.Fourier.ZMod3
import TaoCollatz.Syracuse.SyracRV
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §7 crux: character-sum decay (node X11) — statement of Prop 1.17

Paper anchor: Tao 2019 Proposition 1.17 — **THE CRUX STATEMENT**. The nontrivial
characters of `Syrac(ℤ/3ⁿℤ)` decay polynomially in `n`, uniformly in `ξ`. Statement
only (`sorry`); the whole §7 machinery (nodes X1–X11) discharges it.
-/

namespace TaoCollatz

/-- **Proposition 1.17** (character-sum decay): for every `A`, the character sum of
`Syrac(ℤ/3ⁿℤ)` at any frequency `ξ` not divisible by 3 is `≤ C·n^{-A}`, uniformly in `ξ`. -/
theorem charFn_decay (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ∀ ξ : ZMod (3 ^ n), ¬ (3 ∣ ξ.val) →
      ‖(syracZ n).cexpect fun Y => eC (-(ξ.val * Y.val : ℚ) / 3 ^ n)‖
        ≤ C * (n : ℝ) ^ (-A) := by
  sorry

end TaoCollatz
