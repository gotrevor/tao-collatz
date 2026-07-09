import TaoCollatz.Sec7.Setup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# §7.1: white-point cancellation (node X2)

Paper anchor: Tao 2019 Lemma 7.2. The character factor at a white point satisfies
`|f| ≤ |cos(π θ)| ≤ exp(-ε³)`. The elementary bound `|cos(π θ)| ≤ 1` is proved; the
sharp `≤ exp(-ε³)` half (white ⇒ `|θ| > ε`) carries `sorry`.
-/

open scoped Real

namespace TaoCollatz

/-- The magnitude factor `|cos(π θ(j,l))|` controlling the character sum (Lemma 7.2). -/
noncomputable def cosπθ (n ξ : ℕ) (j : ℕ) (l : ℤ) : ℝ :=
  Real.cos (Real.pi * (θq n ξ j l : ℝ))

/-- Elementary bound: `|cos(π θ)| ≤ 1` (the trivial half of Lemma 7.2). -/
theorem cosπθ_abs_le_one (n ξ : ℕ) (j : ℕ) (l : ℤ) : |cosπθ n ξ j l| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- **Lemma 7.2** (white cancellation): at a white point the character magnitude decays,
`|cos(π θ)| ≤ exp(-ε³)`. -/
theorem white_cos_bound (n ξ : ℕ) (j : ℕ) (l : ℤ) (hw : white n ξ j l) :
    |cosπθ n ξ j l| ≤ Real.exp (-(epsBW : ℝ) ^ 3) := by
  sorry

end TaoCollatz
