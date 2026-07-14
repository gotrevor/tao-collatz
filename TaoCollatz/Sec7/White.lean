import TaoCollatz.Sec7.Setup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# §7.1: white-point cancellation (node X2)

Paper anchor: Tao 2019 Lemma 7.2. The character factor at a white point satisfies
`|f| ≤ |cos(π θ)| ≤ exp(-ε³)`. The elementary bound `|cos(π θ)| ≤ 1` is proved; the
sharp `≤ exp(-ε³)` half (white ⇒ `|θ| > ε`) carries `sorry`.
-/

open scoped Real

namespace TaoCollatz

-- `epsBW = 10⁻¹⁰⁰⁰`: raise the `norm_num` exponentiation cap so `10^1000` evaluates.
set_option exponentiation.threshold 3000

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
  set t : ℝ := ((θq n ξ j l : ℚ) : ℝ) with ht
  -- |θ| ≤ 1/2 (signed fractional part) and ε < |θ| (whiteness)
  have htq : |θq n ξ j l| ≤ 1 / 2 := by
    rw [θq, sfrac]
    exact abs_sub_round _
  have ht2 : |t| ≤ 1 / 2 := by
    rw [ht, ← Rat.cast_abs]
    calc ((|θq n ξ j l| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr htq
      _ = 1 / 2 := by norm_num
  have hεq : epsBW < |θq n ξ j l| := lt_of_not_ge fun h => hw h
  have hε : ((epsBW : ℚ) : ℝ) < |t| := by
    rw [ht, ← Rat.cast_abs]
    exact Rat.cast_lt.mpr hεq
  have hεval : ((epsBW : ℚ) : ℝ) = 1 / 10 ^ 1000 := by
    rw [show epsBW = 1 / 10 ^ 1000 from rfl]
    push_cast
    norm_num
  have hπ := Real.pi_gt_three
  -- cos(πt) ≥ 0 on |t| ≤ 1/2
  have habs : |Real.pi * t| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
    nlinarith [abs_nonneg t]
  have hnn : 0 ≤ Real.cos (Real.pi * t) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · nlinarith [abs_le.mp ht2]
    · nlinarith [abs_le.mp ht2]
  -- quadratic bound: cos(πt) ≤ 1 − 2t²
  have hquad : Real.cos (Real.pi * t) ≤ 1 - 2 * t ^ 2 := by
    have hb := Real.cos_le_one_sub_mul_cos_sq habs
    have hπt : 2 / Real.pi ^ 2 * (Real.pi * t) ^ 2 = 2 * t ^ 2 := by
      field_simp
    rw [hπt] at hb
    exact hb
  have hsq : ((epsBW : ℚ) : ℝ) ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    have h0 : (0 : ℝ) ≤ ((epsBW : ℚ) : ℝ) := by rw [hεval]; norm_num
    nlinarith [hε]
  calc |cosπθ n ξ j l| = Real.cos (Real.pi * t) := by
        rw [cosπθ, ht, abs_of_nonneg hnn]
    _ ≤ 1 - 2 * t ^ 2 := hquad
    _ ≤ 1 + -((epsBW : ℚ) : ℝ) ^ 3 := by rw [hεval] at hsq ⊢; nlinarith
    _ ≤ Real.exp (-((epsBW : ℚ) : ℝ) ^ 3) := by
        rw [add_comm]
        exact Real.add_one_le_exp _

end TaoCollatz
