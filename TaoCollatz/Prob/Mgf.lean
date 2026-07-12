import TaoCollatz.Prob.Tilt

/-!
# Moment generating functions of the d=1 renewal laws (node S3, step (F2))

Paper anchor: Tao 2019 pp.15–16 (the MGF `M(λ)` of Lemma 2.2's tilting step) and
(7.30) (the `Hold` MGF strip, Lemma 7.6 engine). This file instantiates the generic
tilting layer (`Prob/Tilt.lean`) at the exponential weight `expW λ a = e^{λa}` on `ℕ`
and computes the partition functions of the d=1 laws in closed form:

* `tiltZ geomHalf (expW λ) = r(1-r)⁻¹` with `r = e^λ/2` — an exact geometric series,
  every `λ` (both sides are `∞` past the strip `e^λ < 2`).
* `tiltZ pascal = (tiltZ geomHalf)²` — via `pascal = iidSum geomHalf 2` and
  `tiltZ_iidSum`, on the strip.
* `tiltZ pascalNe3 + 3⁻¹·e^{3λ} = (4/3)·tiltZ pascal` — the `b = 3` atom split
  (`pascalNe3` is `pascal` conditioned off `3`, reweighted `4/3`).

The numeric strip bounds (`Z_p(λ) < 4/3·(1-δ)` for `|λ| ≤ 1/50`, feeding `Hold` MGF
finiteness) are the next step.
-/

open scoped ENNReal

namespace TaoCollatz

/-- The exponential tilt weight `a ↦ e^{λa}` on `ℕ`. -/
noncomputable def expW (lam : ℝ) : ℕ → ℝ≥0∞ :=
  fun a => ENNReal.ofReal (Real.exp (lam * a))

theorem expW_zero (lam : ℝ) : expW lam 0 = 1 := by
  rw [expW]
  norm_num

theorem expW_add (lam : ℝ) (a b : ℕ) :
    expW lam (a + b) = expW lam a * expW lam b := by
  rw [expW, expW, expW, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- **The `Geom(2)` MGF, exact** (paper p.15's `M(λ)` prototype): a geometric
series, valid for every `λ` (both sides are `∞` off the strip `e^λ < 2`). -/
theorem tiltZ_geomHalf (lam : ℝ) :
    tiltZ geomHalf (expW lam)
      = ENNReal.ofReal (Real.exp lam / 2)
          * (1 - ENNReal.ofReal (Real.exp lam / 2))⁻¹ := by
  set r := ENNReal.ofReal (Real.exp lam / 2) with hr
  have hterm : ∀ a : ℕ, geomHalf a * expW lam a
      = if a = 0 then 0 else r ^ a := by
    intro a
    rw [geomHalf_apply, expW]
    split_ifs with h
    · rw [zero_mul]
    · rw [hr, ← ENNReal.ofReal_pow (by positivity), div_pow,
        show (Real.exp lam ^ a / 2 ^ a) = Real.exp lam ^ a * (2 ^ a)⁻¹ from
          div_eq_mul_inv _ _,
        ENNReal.ofReal_mul (by positivity), ← Real.exp_nat_mul,
        ENNReal.ofReal_inv_of_pos (by positivity)]
      rw [show ENNReal.ofReal ((2 : ℝ) ^ a) = 2 ^ a from by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
        ← ENNReal.inv_pow, mul_comm]
      congr 2
      ring
  rw [tiltZ, tsum_congr hterm, tsum_ite_zero_eq_succ (fun a => r ^ a),
    ENNReal.tsum_geometric_add_one]

theorem tiltZ_geomHalf_ne_zero (lam : ℝ) : tiltZ geomHalf (expW lam) ≠ 0 := by
  rw [tiltZ_geomHalf]
  refine mul_ne_zero ?_ ?_
  · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  · exact ENNReal.inv_ne_zero.mpr (ne_top_of_le_ne_top ENNReal.one_ne_top
      tsub_le_self)

theorem tiltZ_geomHalf_ne_top {lam : ℝ} (hlam : Real.exp lam < 2) :
    tiltZ geomHalf (expW lam) ≠ ∞ := by
  rw [tiltZ_geomHalf]
  have hr1 : ENNReal.ofReal (Real.exp lam / 2) < 1 :=
    ENNReal.ofReal_lt_one.mpr (by linarith)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (by
      rw [Ne, tsub_eq_zero_iff_le, not_le]
      exact hr1))

/-- **The `Pascal` MGF is the square of the `Geom(2)` MGF** (on the strip):
`pascal = iidSum geomHalf 2` + MGF multiplicativity. -/
theorem tiltZ_pascal {lam : ℝ} (hlam : Real.exp lam < 2) :
    tiltZ pascal (expW lam) = (tiltZ geomHalf (expW lam)) ^ 2 := by
  rw [pascal_eq_iidSum]
  exact tiltZ_iidSum geomHalf (expW_zero lam) (expW_add lam)
    (tiltZ_geomHalf_ne_zero lam) (tiltZ_geomHalf_ne_top hlam) 2

/-- `pascalNe3` is `pascal` conditioned off the `b = 3` atom, reweighted `4/3`
(pointwise form of the definition). -/
theorem pascalNe3_eq_ite (b : ℕ) :
    pascalNe3 b = (4 / 3 : ℝ≥0∞) * (if b = 3 then 0 else pascal b) := by
  classical
  show (if b < 2 ∨ b = 3 then (0 : ℝ≥0∞)
      else (4 / 3) * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b))
    = (4 / 3 : ℝ≥0∞) * (if b = 3 then 0
      else if b < 2 then 0 else ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b)
  by_cases h3 : b = 3
  · rw [if_pos (Or.inr h3), if_pos h3, mul_zero]
  · by_cases h2 : b < 2
    · rw [if_pos (Or.inl h2), if_neg h3, if_pos h2, mul_zero]
    · rw [if_neg (by tauto), if_neg h3, if_neg h2]

/-- The `Pascal` mass at `3` is `4⁻¹`. -/
theorem pascal_apply_three : pascal 3 = 4⁻¹ := by
  show (if 3 < 2 then (0 : ℝ≥0∞) else ((3 - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 3) = 4⁻¹
  rw [if_neg (by omega)]
  rw [show ((3 - 1 : ℕ) : ℝ≥0∞) = 2 from by norm_num, ← ENNReal.inv_pow,
    show ((2 : ℝ≥0∞) ^ 3)⁻¹ = 8⁻¹ from by norm_num]
  rw [show (2 : ℝ≥0∞) * 8⁻¹ = (2 * 8⁻¹ : ℝ≥0∞) from rfl]
  rw [show (8 : ℝ≥0∞) = 2 * 4 from by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul]

/-- **The `pascalNe3` MGF, atom-split form** (total, no `ℝ≥0∞` subtraction):
`Z_{pascalNe3}(λ) + 3⁻¹·e^{3λ} = (4/3)·Z_{pascal}(λ)`. -/
theorem tiltZ_pascalNe3_add (lam : ℝ) :
    tiltZ pascalNe3 (expW lam) + 3⁻¹ * expW lam 3
      = (4 / 3 : ℝ≥0∞) * tiltZ pascal (expW lam) := by
  classical
  have hsplit : tiltZ pascal (expW lam)
      = pascal 3 * expW lam 3
        + ∑' b, if b = 3 then 0 else pascal b * expW lam b := by
    rw [tiltZ]
    convert ENNReal.tsum_eq_add_tsum_ite (f := fun b => pascal b * expW lam b) 3
      using 3
    funext b
    split_ifs <;> rfl
  have hne3 : tiltZ pascalNe3 (expW lam)
      = (4 / 3 : ℝ≥0∞) * ∑' b, if b = 3 then 0 else pascal b * expW lam b := by
    rw [tiltZ, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun b => ?_
    rw [pascalNe3_eq_ite]
    split_ifs with h
    · simp
    · ring
  rw [hne3, hsplit, mul_add, pascal_apply_three, ← mul_assoc,
    show (4 / 3 : ℝ≥0∞) * 4⁻¹ = 3⁻¹ from by
      rw [div_eq_mul_inv, show (4 : ℝ≥0∞) * 3⁻¹ * 4⁻¹ = (4 * 4⁻¹) * 3⁻¹ from by ring,
        ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul],
    add_comm]

end TaoCollatz
