import TaoCollatz.Sec7.Reduction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §7 crux: character-sum decay (node X11) — statement of Prop 1.17

Paper anchor: Tao 2019 Proposition 1.17 — **THE CRUX STATEMENT**. The nontrivial
characters of `Syrac(ℤ/3ⁿℤ)` decay polynomially in `n`, uniformly in `ξ`.
PROVED (2026-07-12) from Proposition 7.1 (`key_fourier_decay`, `Sec7/Reduction.lean`)
via the (1.26) seam: `syracZ` is BY DEFINITION the pushforward of `Geom(2)ⁿ` under
the reversed character sum, so `cexpect_map` transports the bound.
-/

namespace TaoCollatz

/-- **Proposition 1.17** (character-sum decay): for every `A`, the character sum of
`Syrac(ℤ/3ⁿℤ)` at any frequency `ξ` not divisible by 3 is `≤ C·n^{-A}`, uniformly in `ξ`. -/
theorem charFn_decay (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ∀ ξ : ZMod (3 ^ n), ¬ (3 ∣ ξ.val) →
      ‖(syracZ n).cexpect fun Y => eC (-(ξ.val * Y.val : ℚ) / 3 ^ n)‖
        ≤ C * (n : ℝ) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := key_fourier_decay A hA
  refine ⟨C, hC0, fun n hn ξ hξ => ?_⟩
  rw [syracZ, cexpect_map _ _ _ (fun Y => (eC_norm _).le)]
  exact hC n hn ξ hξ

end TaoCollatz
