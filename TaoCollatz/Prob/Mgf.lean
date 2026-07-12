import TaoCollatz.Prob.Tilt
import TaoCollatz.Sec7.Holding

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

/-! ### Numeric strip bounds on the box `|λ| ≤ 1/50` -/

/-- `e^x ≤ (1-x)⁻¹` on `[0, 1)` (from `1 - x ≤ e^{-x}`). -/
theorem exp_le_inv_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Real.exp x ≤ (1 - x)⁻¹ := by
  have hpos : 0 < 1 - x := by linarith
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have h : 1 - x ≤ (Real.exp x)⁻¹ := by
    have := Real.add_one_le_exp (-x)
    rw [Real.exp_neg] at this
    linarith
  have hmul : Real.exp x * (1 - x) ≤ 1 := by
    have h2 := mul_le_mul_of_nonneg_left h hexp.le
    rwa [mul_inv_cancel₀ hexp.ne'] at h2
  calc Real.exp x = Real.exp x * (1 - x) * (1 - x)⁻¹ := by field_simp
    _ ≤ 1 * (1 - x)⁻¹ := mul_le_mul_of_nonneg_right hmul (by positivity)
    _ = (1 - x)⁻¹ := one_mul _

/-- Monotone evaluation of the geometric closed form `r(1-r)⁻¹` at a rational
majorant of the ratio. -/
theorem geom_closed_le {q q' : ℝ} (h0 : 0 ≤ q) (hqq : q ≤ q') (h1 : q' < 1) :
    ENNReal.ofReal q * (1 - ENNReal.ofReal q)⁻¹
      ≤ ENNReal.ofReal (q' / (1 - q')) := by
  have h1q' : 0 < 1 - q' := by linarith
  have h0' : 0 ≤ q' := le_trans h0 hqq
  have hstep : ENNReal.ofReal q * (1 - ENNReal.ofReal q)⁻¹
      ≤ ENNReal.ofReal q' * (1 - ENNReal.ofReal q')⁻¹ := by
    gcongr <;> exact ENNReal.ofReal_le_ofReal hqq
  refine le_trans hstep (le_of_eq ?_)
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ← ENNReal.ofReal_sub 1 h0', ← ENNReal.ofReal_inv_of_pos h1q',
    ← ENNReal.ofReal_mul h0', div_eq_mul_inv]

/-- `Geom(2)` MGF bound on the strip `λ ≤ 1/50`: `Z ≤ 25/24`. -/
theorem tiltZ_geomHalf_le {lam : ℝ} (hhi : lam ≤ 1 / 50) :
    tiltZ geomHalf (expW lam) ≤ ENNReal.ofReal (25 / 24) := by
  have hexp : Real.exp lam ≤ 50 / 49 := by
    calc Real.exp lam ≤ Real.exp (1 / 50) := Real.exp_le_exp.mpr hhi
      _ ≤ (1 - 1 / 50)⁻¹ := exp_le_inv_one_sub (by norm_num) (by norm_num)
      _ ≤ 50 / 49 := by norm_num
  rw [tiltZ_geomHalf]
  calc ENNReal.ofReal (Real.exp lam / 2) * (1 - ENNReal.ofReal (Real.exp lam / 2))⁻¹
      ≤ ENNReal.ofReal ((25 / 49) / (1 - 25 / 49)) :=
        geom_closed_le (by positivity) (by linarith) (by norm_num)
    _ = ENNReal.ofReal (25 / 24) := by norm_num

/-- The `pascalNe3` mass at `2` is `3⁻¹`. -/
theorem pascalNe3_apply_two : pascalNe3 2 = 3⁻¹ := by
  show (if 2 < 2 ∨ 2 = 3 then (0 : ℝ≥0∞)
      else (4 / 3) * (((2 - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 2)) = 3⁻¹
  rw [if_neg (by omega)]
  rw [show ((2 - 1 : ℕ) : ℝ≥0∞) = 1 from by norm_num, one_mul, ← ENNReal.inv_pow,
    show ((2 : ℝ≥0∞) ^ 2)⁻¹ = 4⁻¹ from by norm_num, div_eq_mul_inv,
    show (4 : ℝ≥0∞) * 3⁻¹ * 4⁻¹ = (4 * 4⁻¹) * 3⁻¹ from by ring,
    ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul]

theorem tiltZ_pascalNe3_ne_zero (lam : ℝ) : tiltZ pascalNe3 (expW lam) ≠ 0 := by
  intro h0
  have hle : pascalNe3 2 * expW lam 2 ≤ tiltZ pascalNe3 (expW lam) :=
    ENNReal.le_tsum 2
  rw [h0, le_zero_iff, mul_eq_zero] at hle
  rcases hle with h | h
  · rw [pascalNe3_apply_two] at h
    exact absurd h (by norm_num)
  · rw [expW, ENNReal.ofReal_eq_zero] at h
    exact absurd h (not_le.mpr (Real.exp_pos _))

/-- **`pascalNe3` MGF bound on the box `|λ| ≤ 1/50`**: `Z_{ne3}(λ) ≤ 57/50` — the
`b = 3` atom removal pulls the MGF strictly below `4/3`, which is what makes the
`Hold` geometric-series ratio `(3/4)e^{λ₁}Z_{ne3} < 1`. -/
theorem tiltZ_pascalNe3_le {lam : ℝ} (hlo : -(1 / 50) ≤ lam) (hhi : lam ≤ 1 / 50) :
    tiltZ pascalNe3 (expW lam) ≤ ENNReal.ofReal (57 / 50) := by
  have hexp2 : Real.exp lam < 2 := by
    calc Real.exp lam ≤ Real.exp (1 / 50) := Real.exp_le_exp.mpr hhi
      _ ≤ (1 - 1 / 50)⁻¹ := exp_le_inv_one_sub (by norm_num) (by norm_num)
      _ < 2 := by norm_num
  have hZp : tiltZ pascal (expW lam) ≤ ENNReal.ofReal (625 / 576) := by
    rw [tiltZ_pascal hexp2]
    calc (tiltZ geomHalf (expW lam)) ^ 2
        ≤ (ENNReal.ofReal (25 / 24)) ^ 2 :=
          pow_le_pow_left' (tiltZ_geomHalf_le hhi) 2
      _ = ENNReal.ofReal (625 / 576) := by
          rw [← ENNReal.ofReal_pow (by norm_num)]
          norm_num
  have he3 : ENNReal.ofReal (47 / 150) ≤ 3⁻¹ * expW lam 3 := by
    rw [expW, show ((3 : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / 3) from by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
          ENNReal.ofReal_ofNat, one_div],
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have h := Real.add_one_le_exp (lam * 3)
    nlinarith
  have hfin : (3 : ℝ≥0∞)⁻¹ * expW lam 3 ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top
  have hmain : tiltZ pascalNe3 (expW lam) + 3⁻¹ * expW lam 3
      ≤ ENNReal.ofReal (57 / 50) + 3⁻¹ * expW lam 3 := by
    rw [tiltZ_pascalNe3_add lam]
    calc (4 / 3 : ℝ≥0∞) * tiltZ pascal (expW lam)
        ≤ (4 / 3 : ℝ≥0∞) * ENNReal.ofReal (625 / 576) := by gcongr
      _ = ENNReal.ofReal (625 / 432) := by
          rw [show (4 / 3 : ℝ≥0∞) = ENNReal.ofReal (4 / 3) from by
              rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat,
                ENNReal.ofReal_ofNat],
            ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
      _ ≤ ENNReal.ofReal (57 / 50) + ENNReal.ofReal (47 / 150) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (by norm_num)
      _ ≤ ENNReal.ofReal (57 / 50) + 3⁻¹ * expW lam 3 := by gcongr
  exact (ENNReal.add_le_add_iff_right hfin).mp hmain

/-! ### The `Hold` MGF (paper (7.30), Lemma 7.6 engine) -/

/-- The 2-D exponential tilt weight on the renewal lattice `ℕ × ℤ`. -/
noncomputable def expW2 (l1 l2 : ℝ) : ℕ × ℤ → ℝ≥0∞ :=
  fun d => ENNReal.ofReal (Real.exp (l1 * d.1 + l2 * d.2))

theorem expW2_zero (l1 l2 : ℝ) : expW2 l1 l2 0 = 1 := by
  simp [expW2]

theorem expW2_add (l1 l2 : ℝ) (a b : ℕ × ℤ) :
    expW2 l1 l2 (a + b) = expW2 l1 l2 a * expW2 l1 l2 b := by
  simp only [expW2]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

/-- `expW2` splits into its two coordinate weights. -/
theorem expW2_eq_mul (l1 l2 : ℝ) (d : ℕ × ℤ) :
    expW2 l1 l2 d = expW2 l1 0 d * expW2 0 l2 d := by
  simp only [expW2]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- Squaring an `expW2` weight doubles the tilt. -/
theorem expW2_sq (l1 l2 : ℝ) (d : ℕ × ℤ) :
    expW2 l1 l2 d ^ 2 = expW2 (2 * l1) (2 * l2) d := by
  simp only [expW2]
  rw [sq, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- **Cauchy–Schwarz split of the 2-D MGF** ((G2) reduction of node S3):
`Z(λ₁,λ₂)² ≤ Z(2λ₁,0)·Z(0,2λ₂)`. Cauchy–Schwarz preserves the first-order (mean)
term exactly, so the 2-D second-order bound `Z ≤ e^{4λ₁+16λ₂+K|λ|²}` reduces to the
two 1-D closed-form bounds. -/
theorem tiltZ_expW2_sq_le (p : PMF (ℕ × ℤ)) (l1 l2 : ℝ) :
    tiltZ p (expW2 l1 l2) ^ 2
      ≤ tiltZ p (expW2 (2 * l1) 0) * tiltZ p (expW2 0 (2 * l2)) := by
  rw [tiltZ]
  calc (∑' d, p d * expW2 l1 l2 d) ^ 2
      = (∑' d, p d * (expW2 l1 0 d * expW2 0 l2 d)) ^ 2 := by
        congr 1
        exact tsum_congr fun d => by rw [expW2_eq_mul]
    _ ≤ (∑' d, p d * (expW2 l1 0 d) ^ 2) * (∑' d, p d * (expW2 0 l2 d) ^ 2) :=
        tsum_mul_mul_sq_le (fun d : ℕ × ℤ => p d) (expW2 l1 0) (expW2 0 l2)
    _ = tiltZ p (expW2 (2 * l1) 0) * tiltZ p (expW2 0 (2 * l2)) := by
        rw [tiltZ, tiltZ]
        congr 1
        · exact tsum_congr fun d => by
            rw [expW2_sq, show (2 : ℝ) * 0 = 0 from by norm_num]
        · exact tsum_congr fun d => by
            rw [expW2_sq, show (2 : ℝ) * 0 = 0 from by norm_num]

/-- **The `Hold` MGF factorization** (paper (7.30)): conditioning on the `Geom(4)`
draw `k`, the increment block contributes `e^{3λ₂}·Z_{ne3}(λ₂)^{k-1}`. -/
theorem tiltZ_hold_factor (l1 l2 : ℝ)
    (hZ0 : tiltZ pascalNe3 (expW l2) ≠ 0) (hZt : tiltZ pascalNe3 (expW l2) ≠ ∞) :
    tiltZ hold (expW2 l1 l2)
      = ∑' k : ℕ, geomQuarter k
          * (ENNReal.ofReal (Real.exp (l1 * k + 3 * l2))
            * (tiltZ pascalNe3 (expW l2)) ^ (k - 1)) := by
  rw [tiltZ]
  unfold hold
  rw [PMF.tsum_bind_mul]
  refine tsum_congr fun k => ?_
  congr 1
  rw [PMF.tsum_map_mul]
  have hterm : ∀ v : Fin (k - 1) → ℕ,
      (pascalNe3.iid (k - 1)) v
          * expW2 l1 l2 ((k : ℕ), ((3 : ℤ) + ∑ i, (v i : ℤ)))
        = ENNReal.ofReal (Real.exp (l1 * k + 3 * l2))
          * ((pascalNe3.iid (k - 1)) v * expW l2 (∑ i, v i)) := by
    intro v
    simp only [expW2, expW]
    rw [show l1 * (((k : ℕ), ((3 : ℤ) + ∑ i, (v i : ℤ))).1 : ℕ)
          + l2 * ((((k : ℕ), ((3 : ℤ) + ∑ i, (v i : ℤ))).2 : ℤ) : ℝ)
        = (l1 * k + 3 * l2) + l2 * ((∑ i, v i : ℕ) : ℝ) from by
      push_cast
      ring]
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  congr 1
  have hiid : ∑' v, (pascalNe3.iid (k - 1)) v * expW l2 (∑ i, v i)
      = tiltZ (iidSum pascalNe3 (k - 1)) (expW l2) := by
    rw [tiltZ, iidSum, PMF.tsum_map_mul]
  rw [hiid, tiltZ_iidSum pascalNe3 (expW_zero l2) (expW_add l2) hZ0 hZt]

theorem tiltZ_hold_ne_zero (l1 l2 : ℝ) : tiltZ hold (expW2 l1 l2) ≠ 0 := by
  intro h0
  have hle : hold (1, 3) * expW2 l1 l2 (1, 3) ≤ tiltZ hold (expW2 l1 l2) :=
    ENNReal.le_tsum _
  rw [h0, le_zero_iff, mul_eq_zero] at hle
  rcases hle with h | h
  · have h13 := hold_apply_one_three
    rw [h, ENNReal.toReal_zero] at h13
    norm_num at h13
  · rw [expW2, ENNReal.ofReal_eq_zero] at h
    exact absurd h (not_le.mpr (Real.exp_pos _))

/-- **`Hold` MGF numeric bound on the box `|λᵢ| ≤ 1/50`** (paper (7.30), the Lemma
7.6 engine, quantitative form): the conditional factorization is dominated by a
geometric series with ratio `(3/4)·e^{λ₁}·Z_{ne3}(λ₂) ≤ 171/196 < 1`, giving
`Z_hold ≤ 1 + (1 - 171/196)⁻¹ = 221/25`. The explicit constant feeds the tilted
atom-mass lower bounds of step (F3). -/
theorem tiltZ_hold_le {l1 l2 : ℝ} (h1lo : -(1 / 50) ≤ l1) (h1hi : l1 ≤ 1 / 50)
    (h2lo : -(1 / 50) ≤ l2) (h2hi : l2 ≤ 1 / 50) :
    tiltZ hold (expW2 l1 l2) ≤ ENNReal.ofReal (221 / 25) := by
  have hZ0 := tiltZ_pascalNe3_ne_zero l2
  have hZle := tiltZ_pascalNe3_le h2lo h2hi
  have hZt : tiltZ pascalNe3 (expW l2) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZle
  have hexp1 : Real.exp l1 ≤ 50 / 49 := by
    calc Real.exp l1 ≤ Real.exp (1 / 50) := Real.exp_le_exp.mpr h1hi
      _ ≤ (1 - 1 / 50)⁻¹ := exp_le_inv_one_sub (by norm_num) (by norm_num)
      _ ≤ 50 / 49 := by norm_num
  have hexp3 : Real.exp (3 * l2) ≤ 50 / 47 := by
    calc Real.exp (3 * l2) ≤ Real.exp (3 / 50) :=
          Real.exp_le_exp.mpr (by linarith)
      _ ≤ (1 - 3 / 50)⁻¹ := exp_le_inv_one_sub (by norm_num) (by norm_num)
      _ ≤ 50 / 47 := by norm_num
  rw [tiltZ_hold_factor l1 l2 hZ0 hZt]
  have hbound : ∀ k : ℕ, geomQuarter k
        * (ENNReal.ofReal (Real.exp (l1 * k + 3 * l2))
          * (tiltZ pascalNe3 (expW l2)) ^ (k - 1))
      ≤ ENNReal.ofReal (171 / 196) ^ (k - 1) := by
    intro k
    match k with
    | 0 =>
      rw [show geomQuarter 0 = 0 from rfl, zero_mul]
      positivity
    | (j + 1) =>
      rw [show geomQuarter (j + 1)
          = 4⁻¹ * (3 * 4⁻¹) ^ ((j + 1) - 1) from by
        rw [show geomQuarter (j + 1)
            = if (j + 1) = 0 then 0 else 4⁻¹ * (3 * 4⁻¹) ^ ((j + 1) - 1) from rfl,
          if_neg (by omega)],
        Nat.add_sub_cancel]
      have hsplit : ENNReal.ofReal (Real.exp (l1 * (j + 1 : ℕ) + 3 * l2))
          = ENNReal.ofReal (Real.exp l1 * Real.exp (3 * l2))
            * ENNReal.ofReal (Real.exp l1) ^ j := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (by positivity), ← Real.exp_nat_mul, ← Real.exp_add,
          ← Real.exp_add]
        congr 2
        push_cast
        ring
      rw [hsplit]
      calc 4⁻¹ * (3 * 4⁻¹) ^ j
            * (ENNReal.ofReal (Real.exp l1 * Real.exp (3 * l2))
              * ENNReal.ofReal (Real.exp l1) ^ j
              * (tiltZ pascalNe3 (expW l2)) ^ j)
          = (4⁻¹ * ENNReal.ofReal (Real.exp l1 * Real.exp (3 * l2)))
            * ((3 * 4⁻¹) * ENNReal.ofReal (Real.exp l1)
              * tiltZ pascalNe3 (expW l2)) ^ j := by
            rw [mul_pow, mul_pow]
            ring
        _ ≤ (4⁻¹ * ENNReal.ofReal ((50 / 49) * (50 / 47)))
            * ((3 * 4⁻¹) * ENNReal.ofReal (50 / 49)
              * ENNReal.ofReal (57 / 50)) ^ j := by
            have ha : ENNReal.ofReal (Real.exp l1 * Real.exp (3 * l2))
                ≤ ENNReal.ofReal ((50 / 49) * (50 / 47)) :=
              ENNReal.ofReal_le_ofReal
                (mul_le_mul hexp1 hexp3 (Real.exp_pos _).le (by norm_num))
            have hb : ENNReal.ofReal (Real.exp l1) ≤ ENNReal.ofReal (50 / 49) :=
              ENNReal.ofReal_le_ofReal hexp1
            gcongr
        _ ≤ 1 * ENNReal.ofReal (171 / 196) ^ j := by
            gcongr
            · calc (4 : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((50 / 49) * (50 / 47))
                  = ENNReal.ofReal ((1 / 4) * ((50 / 49) * (50 / 47))) := by
                    rw [show ((4 : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / 4) from by
                        rw [ENNReal.ofReal_div_of_pos (by norm_num),
                          ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div],
                      ← ENNReal.ofReal_mul (by norm_num)]
                _ ≤ 1 := by
                    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from
                        ENNReal.ofReal_one.symm]
                    exact ENNReal.ofReal_le_ofReal (by norm_num)
            · calc (3 : ℝ≥0∞) * 4⁻¹ * ENNReal.ofReal (50 / 49)
                    * ENNReal.ofReal (57 / 50)
                  = ENNReal.ofReal (3 * (1 / 4) * (50 / 49) * (57 / 50)) := by
                    rw [show ((4 : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / 4) from by
                        rw [ENNReal.ofReal_div_of_pos (by norm_num),
                          ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div],
                      show ((3 : ℝ≥0∞)) = ENNReal.ofReal 3 from
                        (ENNReal.ofReal_ofNat 3).symm,
                      ← ENNReal.ofReal_mul (by norm_num),
                      ← ENNReal.ofReal_mul (by norm_num),
                      ← ENNReal.ofReal_mul (by norm_num)]
                _ ≤ ENNReal.ofReal (171 / 196) :=
                    ENNReal.ofReal_le_ofReal (by norm_num)
        _ = ENNReal.ofReal (171 / 196) ^ j := one_mul _
  refine le_trans (ENNReal.tsum_le_tsum hbound) ?_
  have hgeom : ∑' k : ℕ, ENNReal.ofReal (171 / 196) ^ (k - 1)
      = 1 + ∑' j : ℕ, ENNReal.ofReal (171 / 196) ^ j := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    congr 1
  rw [hgeom, ENNReal.tsum_geometric]
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (171 / 196) = ENNReal.ofReal (25 / 196) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub 1 (by norm_num)]
    norm_num
  rw [hsub, ← ENNReal.ofReal_inv_of_pos (by norm_num),
    show ((25 / 196 : ℝ))⁻¹ = 196 / 25 from by norm_num,
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **`Hold` MGF finiteness on the box `|λᵢ| ≤ 1/50`** (paper (7.30), the Lemma 7.6
engine): corollary of the numeric bound `tiltZ_hold_le`. -/
theorem tiltZ_hold_ne_top {l1 l2 : ℝ} (h1lo : -(1 / 50) ≤ l1) (h1hi : l1 ≤ 1 / 50)
    (h2lo : -(1 / 50) ≤ l2) (h2hi : l2 ≤ 1 / 50) :
    tiltZ hold (expW2 l1 l2) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tiltZ_hold_le h1lo h1hi h2lo h2hi)

/-! ### Tilted `Hold` atom masses (step (F3b)) -/

/-- **Tilted `Hold` atom-mass lower bound** ((F3b) of node S3): on the tilt box
`|λᵢ| ≤ 1/50`, any `hold` atom `y` in the window `y₁ ≤ 2`, `0 ≤ y₂ ≤ 8` of mass
`≥ 1/32` keeps mass `≥ 1/400` after tilting: the weight loses at most
`e^{-1/5} ≥ 4/5` and the partition function is at most `221/25`
(`(1/32)·(4/5)·(25/221) = 5/1768 > 1/400`). Feeds `charFn_decay_of_atoms` at
`μ = 1/400` for the tilted walk — the four nondegeneracy atoms
`(1,3), (2,5), (2,7), (2,8)` all lie in the window. -/
theorem tilt_hold_apply_ge {l1 l2 : ℝ} (h1lo : -(1 / 50) ≤ l1) (h1hi : l1 ≤ 1 / 50)
    (h2lo : -(1 / 50) ≤ l2) (h2hi : l2 ≤ 1 / 50) (y : ℕ × ℤ)
    (hy1 : (y.1 : ℝ) ≤ 2) (hy2 : (0 : ℝ) ≤ (y.2 : ℝ)) (hy2' : (y.2 : ℝ) ≤ 8)
    (hm : (1 / 32 : ℝ) ≤ (hold y).toReal) :
    (1 / 400 : ℝ)
      ≤ ((tilt hold (expW2 l1 l2) (tiltZ_hold_ne_zero l1 l2)
          (tiltZ_hold_ne_top h1lo h1hi h2lo h2hi)) y).toReal := by
  have hZ0 := tiltZ_hold_ne_zero l1 l2
  have hZt := tiltZ_hold_ne_top h1lo h1hi h2lo h2hi
  rw [tilt_apply, ENNReal.toReal_mul, ENNReal.toReal_mul]
  -- weight lower bound: the exponent is ≥ -1/5 on the window
  have hw : (4 / 5 : ℝ) ≤ (expW2 l1 l2 y).toReal := by
    rw [expW2, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    have hy1' : (0 : ℝ) ≤ (y.1 : ℝ) := Nat.cast_nonneg _
    have habs : -(1 / 5) ≤ l1 * (y.1 : ℝ) + l2 * (y.2 : ℝ) := by nlinarith
    calc (4 / 5 : ℝ) = -(1 / 5) + 1 := by norm_num
      _ ≤ Real.exp (-(1 / 5)) := Real.add_one_le_exp _
      _ ≤ Real.exp (l1 * (y.1 : ℝ) + l2 * (y.2 : ℝ)) := Real.exp_le_exp.mpr habs
  -- partition function upper bound in ℝ
  have hZr : (tiltZ hold (expW2 l1 l2)).toReal ≤ 221 / 25 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (tiltZ_hold_le h1lo h1hi h2lo h2hi)
    rwa [ENNReal.toReal_ofReal (by norm_num)] at h
  have hZpos : 0 < (tiltZ hold (expW2 l1 l2)).toReal := ENNReal.toReal_pos hZ0 hZt
  have hinv : (25 / 221 : ℝ) ≤ ((tiltZ hold (expW2 l1 l2))⁻¹).toReal := by
    rw [ENNReal.toReal_inv]
    calc (25 / 221 : ℝ) = (221 / 25 : ℝ)⁻¹ := by norm_num
      _ ≤ ((tiltZ hold (expW2 l1 l2)).toReal)⁻¹ := inv_anti₀ hZpos hZr
  calc (1 / 400 : ℝ) ≤ 1 / 32 * (4 / 5) * (25 / 221) := by norm_num
    _ ≤ (hold y).toReal * (expW2 l1 l2 y).toReal
          * ((tiltZ hold (expW2 l1 l2))⁻¹).toReal :=
        mul_le_mul
          (mul_le_mul hm hw (by norm_num) ENNReal.toReal_nonneg)
          hinv (by norm_num)
          (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

end TaoCollatz
