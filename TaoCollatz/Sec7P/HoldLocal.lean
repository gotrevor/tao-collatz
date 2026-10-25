/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.Unroll
import TaoCollatz.Sec7P.HoldTail

/-!
# Uniform tilted center bounds for the `Pascal(p)` holding walk

This is the probability-law-dependent center-regime part of Tao's Lemma 2.2(i).
The positive exponential moment from `Sec7P.HoldTail` controls every tilt in the
smaller box `|λᵢ| ≤ 1/1000`.  The four aperiodicity atoms therefore retain a
uniform mass after tilting, and the existing p-free finite circle method gives
a center point-mass bound independent of `p`.
-/

open scoped ENNReal

namespace TaoCollatz.Sec7P

/-- The holding-law MGF is uniformly bounded throughout the small tilt box.
Only the upper sides of the box enter because both holding coordinates are
nonnegative on support. -/
theorem tiltZ_holdP_le_box_window {p l1 l2 : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (h1hi : l1 ≤ 1 / 1000) (h2hi : l2 ≤ 1 / 1000) :
    TaoCollatz.tiltZ (holdP p (by linarith) (by linarith))
        (TaoCollatz.expW2 l1 l2) ≤ ENNReal.ofReal 6 := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let P := holdP p hp0' hp1'
  rw [TaoCollatz.tiltZ]
  calc
    (∑' d : ℕ × ℤ, P d * TaoCollatz.expW2 l1 l2 d) ≤
        ∑' d : ℕ × ℤ, P d * TaoCollatz.expW2 (1 / 1000) (1 / 1000) d := by
      refine ENNReal.tsum_le_tsum fun d => ?_
      by_cases hd : P d = 0
      · simp [hd]
      · have hmem : d ∈ P.support := by
          rw [PMF.mem_support_iff]
          exact hd
        have hd1 : 0 ≤ (d.1 : ℝ) := Nat.cast_nonneg _
        have hd2z : 3 ≤ d.2 := by
          dsimp [P] at hmem
          exact holdP_support_snd_ge p hp0' hp1' d hmem
        have hd2 : 0 ≤ (d.2 : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ d.2)
        gcongr
        rw [TaoCollatz.expW2, TaoCollatz.expW2]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
    _ ≤ ENNReal.ofReal 6 := tiltZ_holdP_le_window hp0 hp1

/-- Every exponential tilt of `holdP` has nonzero partition function. -/
theorem tiltZ_holdP_ne_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (l1 l2 : ℝ) :
    TaoCollatz.tiltZ (holdP p hp0 hp1) (TaoCollatz.expW2 l1 l2) ≠ 0 := by
  intro h0
  have hle : holdP p hp0 hp1 (1, 3) * TaoCollatz.expW2 l1 l2 (1, 3) ≤
      TaoCollatz.tiltZ (holdP p hp0 hp1) (TaoCollatz.expW2 l1 l2) :=
    ENNReal.le_tsum _
  rw [h0, le_zero_iff, mul_eq_zero] at hle
  rcases hle with h | h
  · have h13 := holdP_apply_one_three p hp0 hp1
    rw [h, ENNReal.toReal_zero] at h13
    exact (pairThreeProb_pos p hp0 hp1).ne' h13.symm
  · rw [TaoCollatz.expW2, ENNReal.ofReal_eq_zero] at h
    exact (not_le.mpr (Real.exp_pos _)) h

/-- Finiteness of the holding-law MGF throughout the small campaign tilt box. -/
theorem tiltZ_holdP_ne_top_window {p l1 l2 : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (h1hi : l1 ≤ 1 / 1000) (h2hi : l2 ≤ 1 / 1000) :
    TaoCollatz.tiltZ (holdP p (by linarith) (by linarith))
        (TaoCollatz.expW2 l1 l2) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (tiltZ_holdP_le_box_window hp0 hp1 h1hi h2hi)

/-- A small atom of `holdP` keeps at least mass `1/25000` after any tilt in
the `1/1000` box.  The inputs cover all four circle-method atoms. -/
theorem tilt_holdP_apply_ge_window {p l1 l2 : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (h1lo : -(1 / 1000) ≤ l1) (h1hi : l1 ≤ 1 / 1000)
    (h2lo : -(1 / 1000) ≤ l2) (h2hi : l2 ≤ 1 / 1000)
    (y : ℕ × ℤ) (hy1 : (y.1 : ℝ) ≤ 2)
    (hy2 : (0 : ℝ) ≤ (y.2 : ℝ)) (hy2' : (y.2 : ℝ) ≤ 8)
    (hm : (1 / 4000 : ℝ) ≤ (holdP p (by linarith) (by linarith) y).toReal) :
    (1 / 25000 : ℝ) ≤
      ((TaoCollatz.tilt (holdP p (by linarith) (by linarith))
        (TaoCollatz.expW2 l1 l2)
        (tiltZ_holdP_ne_zero p (by linarith) (by linarith) l1 l2)
        (tiltZ_holdP_ne_top_window hp0 hp1 h1hi h2hi)) y).toReal := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let P := holdP p hp0' hp1'
  let Z := TaoCollatz.tiltZ P (TaoCollatz.expW2 l1 l2)
  have hZ0 : Z ≠ 0 := tiltZ_holdP_ne_zero p hp0' hp1' l1 l2
  have hZt : Z ≠ ∞ := tiltZ_holdP_ne_top_window hp0 hp1 h1hi h2hi
  change (1 / 25000 : ℝ) ≤
    ((TaoCollatz.tilt P (TaoCollatz.expW2 l1 l2) hZ0 hZt) y).toReal
  rw [TaoCollatz.tilt_apply, ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hy1' : 0 ≤ (y.1 : ℝ) := Nat.cast_nonneg _
  have hw : (99 / 100 : ℝ) ≤ (TaoCollatz.expW2 l1 l2 y).toReal := by
    rw [TaoCollatz.expW2, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    have hexp : -(1 / 100 : ℝ) ≤ l1 * (y.1 : ℝ) + l2 * (y.2 : ℝ) := by
      nlinarith
    calc
      (99 / 100 : ℝ) = -(1 / 100) + 1 := by norm_num
      _ ≤ Real.exp (-(1 / 100)) := Real.add_one_le_exp _
      _ ≤ Real.exp (l1 * (y.1 : ℝ) + l2 * (y.2 : ℝ)) :=
        Real.exp_le_exp.mpr hexp
  have hZr : Z.toReal ≤ 6 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (tiltZ_holdP_le_box_window hp0 hp1 h1hi h2hi)
    rwa [ENNReal.toReal_ofReal (by norm_num)] at h
  have hZpos : 0 < Z.toReal := ENNReal.toReal_pos hZ0 hZt
  have hinv : (1 / 6 : ℝ) ≤ Z⁻¹.toReal := by
    rw [ENNReal.toReal_inv]
    calc
      (1 / 6 : ℝ) = (6 : ℝ)⁻¹ := by norm_num
      _ ≤ Z.toReal⁻¹ := inv_anti₀ hZpos hZr
  calc
    (1 / 25000 : ℝ) ≤ 1 / 4000 * (99 / 100) * (1 / 6) := by norm_num
    _ ≤ (P y).toReal * (TaoCollatz.expW2 l1 l2 y).toReal * Z⁻¹.toReal :=
      mul_le_mul
        (mul_le_mul hm hw (by norm_num) ENNReal.toReal_nonneg)
        hinv (by norm_num)
        (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-- Uniform center-regime point-mass bound for every exponentially tilted
`Pascal(p)` holding walk in the small box. -/
theorem tiltHoldP_apply_le_center_window {p l1 l2 : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (h1lo : -(1 / 1000) ≤ l1) (h1hi : l1 ≤ 1 / 1000)
    (h2lo : -(1 / 1000) ≤ l2) (h2hi : l2 ≤ 1 / 1000)
    (n : ℕ) (v : ℕ × ℤ) :
    let hp0' : 0 < p := by linarith
    let hp1' : p < 1 := by linarith
    let P := holdP p hp0' hp1'
    let r := TaoCollatz.tilt P (TaoCollatz.expW2 l1 l2)
      (tiltZ_holdP_ne_zero p hp0' hp1' l1 l2)
      (tiltZ_holdP_ne_top_window hp0 hp1 h1hi h2hi)
    ((TaoCollatz.iidSum r n) v).toReal ≤
      (32 * 312500000 : ℝ) ^ 2 / (1 + (n : ℝ)) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let P := holdP p hp0' hp1'
  let r := TaoCollatz.tilt P (TaoCollatz.expW2 l1 l2)
    (tiltZ_holdP_ne_zero p hp0' hp1' l1 l2)
    (tiltZ_holdP_ne_top_window hp0 hp1 h1hi h2hi)
  dsimp only
  have hatoms := holdP_four_atoms_lower_window hp0 hp1
  have hmap : ∀ {N : ℕ} [NeZero N] (y : ℕ × ℤ),
      (y.1 : ℝ) ≤ 2 → (0 : ℝ) ≤ (y.2 : ℝ) → (y.2 : ℝ) ≤ 8 →
      (1 / 4000 : ℝ) ≤ (P y).toReal →
      (1 / 25000 : ℝ) ≤
        ((r.map (TaoCollatz.modPair N)) (TaoCollatz.modPair N y)).toReal := by
    intro N _ y hy1 hy20 hy2 hm
    exact (tilt_holdP_apply_ge_window hp0 hp1 h1lo h1hi h2lo h2hi
      y hy1 hy20 hy2 hm).trans
        (ENNReal.toReal_mono (PMF.apply_ne_top _ _)
          (PMF.apply_le_map_apply r (TaoCollatz.modPair N) y))
  have hdec : ∀ (N : ℕ) [NeZero N], 4 ≤ N → ∀ ξ : ZMod N × ZMod N,
      ‖TaoCollatz.charFn (r.map (TaoCollatz.modPair N)) ξ‖ ^ 2 ≤
        1 - (((TaoCollatz.nd ξ.1 : ℝ) / N) ^ 2 +
          ((TaoCollatz.nd ξ.2 : ℝ) / N) ^ 2) / 312500000 := by
    intro N _ hN ξ
    obtain ⟨h13, h25, h27, h28⟩ := hatoms
    have h := TaoCollatz.charFn_decay_of_atoms hN
      (r.map (TaoCollatz.modPair N)) (μ := (1 / 25000 : ℝ)) (by norm_num)
      (hmap (1, 3) (by norm_num) (by norm_num) (by norm_num) h13)
      (hmap (2, 5) (by norm_num) (by norm_num) (by norm_num) h25)
      (hmap (2, 7) (by norm_num) (by norm_num) (by norm_num) h27)
      (hmap (2, 8) (by norm_num) (by norm_num) (by norm_num) h28) ξ
    refine le_trans h (le_of_eq ?_)
    ring
  exact TaoCollatz.iidSum_apply_le_center_of_decay r
    (c := 312500000) (by norm_num) hdec n v
/-- A global second-order exponential bound with a deliberately coarse remainder. -/
theorem exp_le_one_add_mul_add_sq_exp_abs (y : ℝ) :
    Real.exp y ≤ 1 + y + y ^ 2 * Real.exp |y| := by
  by_cases hy : |y| ≤ 1
  · have h := Real.exp_bound hy (n := 2) (by norm_num)
    norm_num [Finset.sum_range_succ] at h
    have hrem : Real.exp y - (1 + y) ≤ y ^ 2 * Real.exp |y| := by
      calc
        Real.exp y - (1 + y) ≤ |Real.exp y - (1 + y)| := le_abs_self _
        _ ≤ 3 / 4 * |y| ^ 2 := by
          simpa [abs_pow, mul_comm] using h
        _ ≤ y ^ 2 * Real.exp |y| := by
          rw [sq_abs]
          have he : (3 / 4 : ℝ) ≤ Real.exp |y| := by
            calc
              (3 / 4 : ℝ) ≤ 1 := by norm_num
              _ ≤ Real.exp |y| := Real.one_le_exp (abs_nonneg y)
          simpa [mul_comm] using mul_le_mul_of_nonneg_left he (sq_nonneg y)
    linarith
  · push Not at hy
    rcases lt_or_ge y 0 with hyneg | hypos
    · have hy1 : y ≤ -1 := by
        rw [abs_of_neg hyneg] at hy
        linarith
      have hlin : 0 ≤ y ^ 2 * Real.exp |y| + y := by
        have he : 1 ≤ Real.exp |y| := Real.one_le_exp (abs_nonneg y)
        have hsq : -y ≤ y ^ 2 := by nlinarith [sq_nonneg (y + 1)]
        nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg y)]
      have hexp : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hyneg.le
      linarith
    · have hy1 : 1 ≤ y := by
        rw [abs_of_nonneg hypos] at hy
        linarith
      have hepos : 0 < Real.exp y := Real.exp_pos y
      have hsq : 1 ≤ y ^ 2 := by nlinarith
      rw [abs_of_nonneg hypos]
      nlinarith [mul_le_mul_of_nonneg_right hsq hepos.le]

/-- A fixed positive exponential moment absorbs the quadratic factor. -/
theorem sq_le_sixteen_million_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 ≤ 16000000 * Real.exp (x / 2000) := by
  have hlin : x / 4000 ≤ Real.exp (x / 4000) := by
    calc
      x / 4000 ≤ 1 + x / 4000 := by linarith
      _ ≤ Real.exp (x / 4000) := by
        simpa [add_comm] using Real.add_one_le_exp (x / 4000)
  have h0 : 0 ≤ x / 4000 := by positivity
  have hpow := pow_le_pow_left₀ h0 hlin 2
  rw [show Real.exp (x / 4000) ^ 2 = Real.exp (x / 2000) by
    rw [sq, ← Real.exp_add]
    congr 1
    ring] at hpow
  nlinarith

/-- Pointwise Taylor control on the small tilt window. -/
theorem exp_mul_le_mean_remainder {mu x : ℝ} (hx : 0 ≤ x)
    (hmu : |mu| ≤ 1 / 2000) :
    Real.exp (mu * x) ≤
      1 + mu * x + 16000000 * mu ^ 2 * Real.exp (x / 1000) := by
  calc
    Real.exp (mu * x) ≤
        1 + mu * x + (mu * x) ^ 2 * Real.exp |mu * x| :=
      exp_le_one_add_mul_add_sq_exp_abs _
    _ ≤ 1 + mu * x + 16000000 * mu ^ 2 * Real.exp (x / 1000) := by
      have habs : |mu * x| ≤ x / 2000 := by
        rw [abs_mul, abs_of_nonneg hx]
        nlinarith
      have he := Real.exp_le_exp.mpr habs
      have hs := sq_le_sixteen_million_mul_exp hx
      have hmul : x ^ 2 * Real.exp |mu * x| ≤
          16000000 * Real.exp (x / 1000) := by
        calc
          x ^ 2 * Real.exp |mu * x| ≤
              (16000000 * Real.exp (x / 2000)) * Real.exp (x / 2000) := by
            exact mul_le_mul hs he (by positivity) (by positivity)
          _ = 16000000 * Real.exp (x / 1000) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 1
            ring
      nlinarith [mul_le_mul_of_nonneg_left hmul (sq_nonneg mu)]

/-- A fixed exponential moment and the exact first moment give a uniform
quadratic MGF envelope. -/
theorem tiltZ_natCoord_le_quad (P : PMF (ℕ × ℤ)) (X : (ℕ × ℤ) → ℕ)
    (mean : ℝ) (hmean0 : 0 ≤ mean)
    (hmean : ∑' d, P d * (X d : ℝ≥0∞) = ENNReal.ofReal mean)
    (hmgf : TaoCollatz.tiltZ P
        (fun d => ENNReal.ofReal (Real.exp ((X d : ℝ) / 1000))) ≤ ENNReal.ofReal 6)
    {mu : ℝ} (hmulo : -(1 / 2000) ≤ mu) (muhi : mu ≤ 1 / 2000) :
    TaoCollatz.tiltZ P
        (fun d => ENNReal.ofReal (Real.exp (mu * (X d : ℝ)))) ≤
      ENNReal.ofReal (1 + mean * mu + 96000000 * mu ^ 2) := by
  have habsmu : |mu| ≤ 1 / 2000 := (abs_le).2 ⟨hmulo, muhi⟩
  have hfixedTop : TaoCollatz.tiltZ P
      (fun d => ENNReal.ofReal (Real.exp ((X d : ℝ) / 1000))) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmgf
  have htargetFixed : TaoCollatz.tiltZ P
      (fun d => ENNReal.ofReal (Real.exp (mu * (X d : ℝ)))) ≤
        TaoCollatz.tiltZ P
          (fun d => ENNReal.ofReal (Real.exp ((X d : ℝ) / 1000))) := by
    rw [TaoCollatz.tiltZ, TaoCollatz.tiltZ]
    refine ENNReal.tsum_le_tsum fun d => ?_
    gcongr
    have hX0 : (0 : ℝ) ≤ X d := Nat.cast_nonneg _
    nlinarith [le_trans (le_abs_self mu) habsmu]
  have htargetTop : TaoCollatz.tiltZ P
      (fun d => ENNReal.ofReal (Real.exp (mu * (X d : ℝ)))) ≠ ∞ :=
    ne_top_of_le_ne_top hfixedTop htargetFixed
  have hPTop : ∑' d, P d ≠ ∞ := by rw [P.tsum_coe]; exact ENNReal.one_ne_top
  have hPSum : Summable (fun d => (P d).toReal) := ENNReal.summable_toReal hPTop
  have hmeanTop : ∑' d, P d * (X d : ℝ≥0∞) ≠ ∞ := by
    rw [hmean]
    exact ENNReal.ofReal_ne_top
  have hmeanSum : Summable (fun d => (P d).toReal * (X d : ℝ)) := by
    have h := ENNReal.summable_toReal hmeanTop
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using h
  have hExpSum : Summable
      (fun d => (P d).toReal * Real.exp ((X d : ℝ) / 1000)) := by
    have h := ENNReal.summable_toReal hfixedTop
    simpa only [TaoCollatz.tiltZ, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  let f : (ℕ × ℤ) → ℝ := fun d =>
    (P d).toReal * Real.exp (mu * (X d : ℝ))
  let g : (ℕ × ℤ) → ℝ := fun d =>
    (P d).toReal * (1 + mu * (X d : ℝ) +
      16000000 * mu ^ 2 * Real.exp ((X d : ℝ) / 1000))
  have hpoint : ∀ d, f d ≤ g d := by
    intro d
    dsimp [f, g]
    exact mul_le_mul_of_nonneg_left
      (exp_mul_le_mean_remainder (Nat.cast_nonneg _) habsmu) ENNReal.toReal_nonneg
  have hgSum : Summable g := by
    have h := (hPSum.add (hmeanSum.mul_left mu)).add
      (hExpSum.mul_left (16000000 * mu ^ 2))
    convert h using 1
    funext d
    dsimp [g]
    ring
  have hfSum : Summable f :=
    Summable.of_nonneg_of_le (fun d => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
      hpoint hgSum
  have hsumfg : ∑' d, f d ≤ ∑' d, g d := hfSum.tsum_le_tsum hpoint hgSum
  have hPsumEq : ∑' d, (P d).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun d => P.apply_ne_top d), P.tsum_coe]
    norm_num
  have hmeanReal : ∑' d, (P d).toReal * (X d : ℝ) = mean := by
    have h := congrArg ENNReal.toReal hmean
    rw [ENNReal.tsum_toReal_eq (fun d => ENNReal.mul_ne_top (P.apply_ne_top d)
      (by finiteness)), ENNReal.toReal_ofReal hmean0] at h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using h
  have hExpLe : ∑' d, (P d).toReal * Real.exp ((X d : ℝ) / 1000) ≤ 6 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmgf
    rw [TaoCollatz.tiltZ, ENNReal.tsum_toReal_eq
      (fun d => ENNReal.mul_ne_top (P.apply_ne_top d) ENNReal.ofReal_ne_top),
      ENNReal.toReal_ofReal (by norm_num)] at h
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  have hgEval : ∑' d, g d = 1 + mu * mean +
      (16000000 * mu ^ 2) *
        ∑' d, (P d).toReal * Real.exp ((X d : ℝ) / 1000) := by
    have hmuSum := hmeanSum.mul_left mu
    have hremSum := hExpSum.mul_left (16000000 * mu ^ 2)
    have hshape : g = fun d =>
        (P d).toReal + mu * ((P d).toReal * (X d : ℝ)) +
          (16000000 * mu ^ 2) *
            ((P d).toReal * Real.exp ((X d : ℝ) / 1000)) := by
      funext d
      dsimp [g]
      ring
    rw [hshape, (hPSum.add hmuSum).tsum_add hremSum,
      hPSum.tsum_add hmuSum, tsum_mul_left, tsum_mul_left,
      hPsumEq, hmeanReal]
  have htargetReal :
      (TaoCollatz.tiltZ P
        (fun d => ENNReal.ofReal (Real.exp (mu * (X d : ℝ))))).toReal ≤
          1 + mean * mu + 96000000 * mu ^ 2 := by
    have htoReal :
        (TaoCollatz.tiltZ P
          (fun d => ENNReal.ofReal (Real.exp (mu * (X d : ℝ))))).toReal = ∑' d, f d := by
      rw [TaoCollatz.tiltZ, ENNReal.tsum_toReal_eq
        (fun d => ENNReal.mul_ne_top (P.apply_ne_top d) ENNReal.ofReal_ne_top)]
      exact tsum_congr fun d => by
        dsimp [f]
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [htoReal]
    calc
      ∑' d, f d ≤ ∑' d, g d := hsumfg
      _ = 1 + mu * mean + (16000000 * mu ^ 2) *
          ∑' d, (P d).toReal * Real.exp ((X d : ℝ) / 1000) := hgEval
      _ ≤ 1 + mean * mu + 96000000 * mu ^ 2 := by
        have hcoef : 0 ≤ 16000000 * mu ^ 2 := mul_nonneg (by norm_num) (sq_nonneg mu)
        nlinarith [mul_le_mul_of_nonneg_left hExpLe hcoef]
  have hrhs0 : 0 ≤ 1 + mean * mu + 96000000 * mu ^ 2 :=
    ENNReal.toReal_nonneg.trans htargetReal
  apply (ENNReal.toReal_le_toReal htargetTop ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hrhs0]
  exact htargetReal

/-- First-coordinate quadratic MGF bound, uniform on the campaign window. -/
theorem tiltZ_holdP_fst_le_quad_window {p mu : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (hmulo : -(1 / 2000) ≤ mu) (muhi : mu ≤ 1 / 2000) :
    TaoCollatz.tiltZ (holdP p (by linarith) (by linarith))
        (TaoCollatz.expW2 mu 0) ≤
      ENNReal.ofReal (1 + (pairThreeProb p)⁻¹ * mu + 96000000 * mu ^ 2) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let P := holdP p hp0' hp1'
  have hmgf : TaoCollatz.tiltZ P
      (fun d => ENNReal.ofReal (Real.exp ((d.1 : ℝ) / 1000))) ≤ ENNReal.ofReal 6 := by
    change TaoCollatz.tiltZ (holdP p hp0' hp1') _ ≤ _
    have hbox := tiltZ_holdP_le_box_window hp0 hp1
      (l1 := (1 / 1000 : ℝ)) (l2 := 0) (by norm_num) (by norm_num)
    change TaoCollatz.tiltZ (holdP p hp0' hp1')
      (TaoCollatz.expW2 (1 / 1000) 0) ≤ ENNReal.ofReal 6 at hbox
    calc
      TaoCollatz.tiltZ (holdP p hp0' hp1')
          (fun d => ENNReal.ofReal (Real.exp ((d.1 : ℝ) / 1000))) =
          TaoCollatz.tiltZ (holdP p hp0' hp1')
            (TaoCollatz.expW2 (1 / 1000) 0) := by
        congr 1
        funext d
        simp only [TaoCollatz.expW2, zero_mul, add_zero]
        congr 2
        ring
      _ ≤ ENNReal.ofReal 6 := hbox
  have h := tiltZ_natCoord_le_quad P Prod.fst (pairThreeProb p)⁻¹
    (inv_nonneg.mpr (pairThreeProb_pos p hp0' hp1').le)
    (holdP_mean_fst_ennreal p hp0' hp1') hmgf hmulo muhi
  change TaoCollatz.tiltZ (holdP p hp0' hp1') _ ≤ _ at h
  change TaoCollatz.tiltZ (holdP p hp0' hp1') (TaoCollatz.expW2 mu 0) ≤ _
  calc
    TaoCollatz.tiltZ (holdP p hp0' hp1') (TaoCollatz.expW2 mu 0) =
        TaoCollatz.tiltZ (holdP p hp0' hp1')
          (fun d => ENNReal.ofReal (Real.exp (mu * (d.1 : ℝ)))) := by
      congr 1
      funext d
      simp only [TaoCollatz.expW2, zero_mul, add_zero]
    _ ≤ _ := h

/-- On the support of `holdP`, the second coordinate is nonnegative, so its
integer cast agrees with the cast of `Int.toNat`. -/
theorem tiltZ_holdP_snd_toNat (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (mu : ℝ) :
    TaoCollatz.tiltZ (holdP p hp0 hp1)
        (fun d => ENNReal.ofReal (Real.exp (mu * (d.2.toNat : ℝ)))) =
      TaoCollatz.tiltZ (holdP p hp0 hp1) (TaoCollatz.expW2 0 mu) := by
  rw [TaoCollatz.tiltZ, TaoCollatz.tiltZ]
  refine tsum_congr fun d => ?_
  by_cases hd : holdP p hp0 hp1 d = 0
  · simp [hd]
  · have hmem : d ∈ (holdP p hp0 hp1).support := by
      rw [PMF.mem_support_iff]
      exact hd
    have hd2 : 0 ≤ d.2 := by
      have := holdP_support_snd_ge p hp0 hp1 d hmem
      omega
    have hcast : ((d.2.toNat : ℕ) : ℝ) = (d.2 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hd2
    congr 1
    simp only [TaoCollatz.expW2, zero_mul, zero_add]
    rw [hcast]

/-- Second-coordinate quadratic MGF bound, uniform on the campaign window. -/
theorem tiltZ_holdP_snd_le_quad_window {p mu : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (hmulo : -(1 / 2000) ≤ mu) (muhi : mu ≤ 1 / 2000) :
    TaoCollatz.tiltZ (holdP p (by linarith) (by linarith))
        (TaoCollatz.expW2 0 mu) ≤
      ENNReal.ofReal
        (1 + (pairThreeProb p)⁻¹ * (2 / p) * mu + 96000000 * mu ^ 2) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let P := holdP p hp0' hp1'
  have hmgf : TaoCollatz.tiltZ P
      (fun d => ENNReal.ofReal (Real.exp ((d.2.toNat : ℝ) / 1000))) ≤
        ENNReal.ofReal 6 := by
    dsimp only [P]
    have heq := tiltZ_holdP_snd_toNat p hp0' hp1' (1 / 1000)
    rw [show (fun d : ℕ × ℤ => ENNReal.ofReal (Real.exp ((d.2.toNat : ℝ) / 1000))) =
        fun d => ENNReal.ofReal (Real.exp ((1 / 1000 : ℝ) * (d.2.toNat : ℝ))) by
      funext d
      congr 2
      ring,
      heq]
    convert tiltZ_holdP_le_box_window hp0 hp1
      (l1 := 0) (l2 := (1 / 1000 : ℝ)) (by norm_num) (by norm_num)
  have h := tiltZ_natCoord_le_quad P (fun d => d.2.toNat)
    ((pairThreeProb p)⁻¹ * (2 / p))
    (mul_nonneg (inv_nonneg.mpr (pairThreeProb_pos p hp0' hp1').le)
      (div_nonneg (by norm_num) hp0'.le))
    (holdP_mean_snd_ennreal p hp0' hp1') hmgf hmulo muhi
  rw [tiltZ_holdP_snd_toNat p hp0' hp1'] at h
  exact h

/-- The two-dimensional quadratic MGF estimate around the p-dependent drift,
with a constant chosen uniformly before `p`. -/
theorem tiltZ_holdP_le_quad_window {p l1 l2 : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (h1lo : -(1 / 4000) ≤ l1) (h1hi : l1 ≤ 1 / 4000)
    (h2lo : -(1 / 4000) ≤ l2) (h2hi : l2 ≤ 1 / 4000) :
    TaoCollatz.tiltZ (holdP p (by linarith) (by linarith))
        (TaoCollatz.expW2 l1 l2) ≤
      ENNReal.ofReal (1 + (pairThreeProb p)⁻¹ * l1 +
        ((pairThreeProb p)⁻¹ * (2 / p)) * l2 +
          1000000000 * (l1 ^ 2 + l2 ^ 2)) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let P := holdP p hp0' hp1'
  let m1 : ℝ := (pairThreeProb p)⁻¹
  let m2 : ℝ := (pairThreeProb p)⁻¹ * (2 / p)
  have hq := pairThreeProb_mem_window hp0 hp1
  have hqpos : 0 < pairThreeProb p := by linarith
  have hm10 : 0 ≤ m1 := inv_nonneg.mpr hqpos.le
  have hm20 : 0 ≤ m2 := mul_nonneg hm10 (div_nonneg (by norm_num) hp0'.le)
  have hm1hi : m1 ≤ 125 / 8 := by
    dsimp [m1]
    rw [inv_le_comm₀ hqpos (by norm_num : (0 : ℝ) < 125 / 8)]
    norm_num
    exact hq.1
  have h2phi : 2 / p ≤ 10 := by
    rw [div_le_iff₀ hp0']
    nlinarith [hp0]
  have hm2hi : m2 ≤ 625 / 4 := by
    dsimp [m2]
    nlinarith [mul_le_mul hm1hi h2phi (div_nonneg (by norm_num) hp0'.le)
      (by norm_num : (0 : ℝ) ≤ 125 / 8)]
  set Q : ℝ := 1 + m1 * l1 + m2 * l2 +
    1000000000 * (l1 ^ 2 + l2 ^ 2) with hQ
  have hQ0 : 0 ≤ Q := by
    have hb1 : 0 ≤ l1 + 1 / 4000 := by linarith
    have hb2 : 0 ≤ l2 + 1 / 4000 := by linarith
    nlinarith [mul_nonneg hm10 hb1, mul_nonneg hm20 hb2,
      sq_nonneg l1, sq_nonneg l2]
  refine TaoCollatz.ennreal_le_of_sq_le_sq ?_
  have hf := tiltZ_holdP_fst_le_quad_window hp0 hp1
    (mu := 2 * l1) (by linarith) (by linarith)
  have hs := tiltZ_holdP_snd_le_quad_window hp0 hp1
    (mu := 2 * l2) (by linarith) (by linarith)
  change TaoCollatz.tiltZ P (TaoCollatz.expW2 (2 * l1) 0) ≤
      ENNReal.ofReal (1 + m1 * (2 * l1) + 96000000 * (2 * l1) ^ 2) at hf
  change TaoCollatz.tiltZ P (TaoCollatz.expW2 0 (2 * l2)) ≤
      ENNReal.ofReal (1 + m2 * (2 * l2) + 96000000 * (2 * l2) ^ 2) at hs
  have hA0 : 0 ≤ 1 + m1 * (2 * l1) + 96000000 * (2 * l1) ^ 2 := by
    have hb : 0 ≤ l1 + 1 / 4000 := by linarith
    nlinarith [mul_nonneg hm10 hb, sq_nonneg l1]
  calc
    TaoCollatz.tiltZ P (TaoCollatz.expW2 l1 l2) ^ 2 ≤
        TaoCollatz.tiltZ P (TaoCollatz.expW2 (2 * l1) 0) *
          TaoCollatz.tiltZ P (TaoCollatz.expW2 0 (2 * l2)) :=
      TaoCollatz.tiltZ_expW2_sq_le P l1 l2
    _ ≤ ENNReal.ofReal (1 + m1 * (2 * l1) + 96000000 * (2 * l1) ^ 2) *
        ENNReal.ofReal (1 + m2 * (2 * l2) + 96000000 * (2 * l2) ^ 2) := by
      gcongr
    _ = ENNReal.ofReal ((1 + m1 * (2 * l1) + 96000000 * (2 * l1) ^ 2) *
        (1 + m2 * (2 * l2) + 96000000 * (2 * l2) ^ 2)) :=
      (ENNReal.ofReal_mul hA0).symm
    _ ≤ ENNReal.ofReal (Q ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hQ]
      let a := m1 * l1
      let b := m2 * l2
      let u := l1 ^ 2 + l2 ^ 2
      let r : ℝ := 384000000
      let K : ℝ := 1000000000
      have haLo : -(1 / 256 : ℝ) ≤ a := by
        dsimp [a]
        nlinarith [mul_nonneg hm10 (show 0 ≤ l1 + 1 / 4000 by linarith)]
      have haHi : a ≤ 1 / 256 := by
        dsimp [a]
        nlinarith [mul_nonneg hm10 (show 0 ≤ 1 / 4000 - l1 by linarith)]
      have hbLo : -(5 / 128 : ℝ) ≤ b := by
        dsimp [b]
        nlinarith [mul_nonneg hm20 (show 0 ≤ l2 + 1 / 4000 by linarith)]
      have hbHi : b ≤ 5 / 128 := by
        dsimp [b]
        nlinarith [mul_nonneg hm20 (show 0 ≤ 1 / 4000 - l2 by linarith)]
      have ht : (245 / 256 : ℝ) ≤ 1 + a + b := by linarith
      have hA0 : 0 ≤ 1 + 2 * a := by linarith
      have hB0 : 0 ≤ 1 + 2 * b := by linarith
      have hA2 : 1 + 2 * a ≤ 2 := by linarith
      have hB2 : 1 + 2 * b ≤ 2 := by linarith
      have hu0 : 0 ≤ u := by dsimp [u]; positivity
      have hr0 : 0 ≤ r := by norm_num [r]
      have hK0 : 0 ≤ K := by norm_num [K]
      have hrK : r ≤ K * (1 + a + b) := by
        calc
          r ≤ K * (245 / 256 : ℝ) := by norm_num [r, K]
          _ ≤ K * (1 + a + b) := mul_le_mul_of_nonneg_left ht hK0
      have h2hrK : 2 * r ≤ 2 * K * (1 + a + b) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hrK (by norm_num : (0 : ℝ) ≤ 2)
      have hmiddle :
          r * l1 ^ 2 * (1 + 2 * b) + r * l2 ^ 2 * (1 + 2 * a) ≤
            2 * K * u * (1 + a + b) := by
        calc
          r * l1 ^ 2 * (1 + 2 * b) + r * l2 ^ 2 * (1 + 2 * a) ≤
              r * l1 ^ 2 * 2 + r * l2 ^ 2 * 2 := by
            gcongr
          _ = 2 * r * u := by dsimp [u]; ring
          _ ≤ 2 * K * (1 + a + b) * u := by
            exact mul_le_mul_of_nonneg_right h2hrK hu0
          _ = 2 * K * u * (1 + a + b) := by ring
      have hrK' : r ≤ K := by
        norm_num [r, K]
      have hrsq : r ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hr0 hrK' 2
      have hxy : l1 ^ 2 * l2 ^ 2 ≤ u ^ 2 := by
        dsimp [u]
        nlinarith [sq_nonneg (l1 ^ 2), sq_nonneg (l2 ^ 2)]
      have hlast : r ^ 2 * (l1 ^ 2 * l2 ^ 2) ≤ K ^ 2 * u ^ 2 :=
        mul_le_mul hrsq hxy (mul_nonneg (sq_nonneg l1) (sq_nonneg l2)) (sq_nonneg K)
      have hpoly : (1 + 2 * a + r * l1 ^ 2) * (1 + 2 * b + r * l2 ^ 2) ≤
          (1 + a + b + K * u) ^ 2 := by
        calc
          (1 + 2 * a + r * l1 ^ 2) * (1 + 2 * b + r * l2 ^ 2) =
              (1 + a + b) ^ 2 - (a - b) ^ 2 +
                (r * l1 ^ 2 * (1 + 2 * b) + r * l2 ^ 2 * (1 + 2 * a)) +
                  r ^ 2 * (l1 ^ 2 * l2 ^ 2) := by ring
          _ ≤ (1 + a + b) ^ 2 + 2 * K * u * (1 + a + b) + K ^ 2 * u ^ 2 := by
            nlinarith [sq_nonneg (a - b), hmiddle, hlast]
          _ = (1 + a + b + K * u) ^ 2 := by ring
      convert hpoly using 1
      all_goals (dsimp [a, b, u, r, K]; ring)
    _ = ENNReal.ofReal Q ^ 2 := ENNReal.ofReal_pow hQ0 2

/-- A uniform Chernoff bound for the parameterized holding sum on the small tilt box. -/
theorem holdSumP_apply_le_chernoff_window {p l1 l2 : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (h1lo : -(1 / 4000) ≤ l1) (h1hi : l1 ≤ 1 / 4000)
    (h2lo : -(1 / 4000) ≤ l2) (h2hi : l2 ≤ 1 / 4000)
    (n j : ℕ) (l : ℤ) :
    ((holdSumP p (by linarith) (by linarith) n) (j, l)).toReal ≤
      (32 * 312500000 : ℝ) ^ 2 / (1 + (n : ℝ)) *
        Real.exp ((n : ℝ) * ((pairThreeProb p)⁻¹ * l1 +
          ((pairThreeProb p)⁻¹ * (2 / p)) * l2 +
            1000000000 * (l1 ^ 2 + l2 ^ 2)) - (l1 * j + l2 * l)) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let P := holdP p hp0' hp1'
  let m1 : ℝ := (pairThreeProb p)⁻¹
  let m2 : ℝ := (pairThreeProb p)⁻¹ * (2 / p)
  have h1lo' : -(1 / 1000) ≤ l1 := by linarith
  have h1hi' : l1 ≤ 1 / 1000 := by linarith
  have h2lo' : -(1 / 1000) ≤ l2 := by linarith
  have h2hi' : l2 ≤ 1 / 1000 := by linarith
  have hZ0 := tiltZ_holdP_ne_zero p hp0' hp1' l1 l2
  have hZt := tiltZ_holdP_ne_top_window hp0 hp1 h1hi' h2hi'
  set u : ℝ := m1 * l1 + m2 * l2 + 1000000000 * (l1 ^ 2 + l2 ^ 2) with hu
  set theta : ℝ := l1 * j + l2 * l with htheta
  have hwv0 : TaoCollatz.expW2 l1 l2 (j, l) ≠ 0 := by
    simp only [TaoCollatz.expW2]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hwvt : TaoCollatz.expW2 l1 l2 (j, l) ≠ ∞ := by
    simp only [TaoCollatz.expW2]
    exact ENNReal.ofReal_ne_top
  have key := TaoCollatz.iidSum_apply_eq_tilt P
    (TaoCollatz.expW2_zero l1 l2) (TaoCollatz.expW2_add l1 l2)
    hZ0 hZt n (j, l) hwv0 hwvt
  have hZle : TaoCollatz.tiltZ P (TaoCollatz.expW2 l1 l2) ≤
      ENNReal.ofReal (Real.exp u) := by
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal (Real.add_one_le_exp u))
    change TaoCollatz.tiltZ (holdP p hp0' hp1') (TaoCollatz.expW2 l1 l2) ≤ _
    have hquad := tiltZ_holdP_le_quad_window hp0 hp1 h1lo h1hi h2lo h2hi
    calc
      TaoCollatz.tiltZ (holdP p hp0' hp1') (TaoCollatz.expW2 l1 l2) ≤
          ENNReal.ofReal (1 + m1 * l1 + m2 * l2 +
            1000000000 * (l1 ^ 2 + l2 ^ 2)) := hquad
      _ = ENNReal.ofReal (u + 1) := by
        congr 1
        dsimp [u]
        ring
  have hBpow : TaoCollatz.tiltZ P (TaoCollatz.expW2 l1 l2) ^ n ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by
    calc
      TaoCollatz.tiltZ P (TaoCollatz.expW2 l1 l2) ^ n ≤
          ENNReal.ofReal (Real.exp u) ^ n := by gcongr
      _ = ENNReal.ofReal (Real.exp u ^ n) :=
        (ENNReal.ofReal_pow (Real.exp_pos _).le n).symm
      _ = ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by rw [← Real.exp_nat_mul]
  have hB : (TaoCollatz.tiltZ P (TaoCollatz.expW2 l1 l2) ^ n).toReal ≤
      Real.exp ((n : ℝ) * u) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBpow
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
  have hCeq : ((TaoCollatz.expW2 l1 l2 (j, l))⁻¹).toReal =
      Real.exp (-theta) := by
    simp only [TaoCollatz.expW2]
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, htheta]
  have hA := tiltHoldP_apply_le_center_window hp0 hp1
    h1lo' h1hi' h2lo' h2hi' n (j, l)
  dsimp only at hA
  rw [holdSumP_eq_iidSum p hp0' hp1' n, key,
    ENNReal.toReal_mul, ENNReal.toReal_mul, hCeq]
  calc
    ((TaoCollatz.iidSum
      (TaoCollatz.tilt P (TaoCollatz.expW2 l1 l2) hZ0 hZt) n) (j, l)).toReal *
        (TaoCollatz.tiltZ P (TaoCollatz.expW2 l1 l2) ^ n).toReal * Real.exp (-theta) ≤
      ((32 * 312500000 : ℝ) ^ 2 / (1 + (n : ℝ)) *
        Real.exp ((n : ℝ) * u)) * Real.exp (-theta) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      exact mul_le_mul hA hB ENNReal.toReal_nonneg (by positivity)
    _ = (32 * 312500000 : ℝ) ^ 2 / (1 + (n : ℝ)) *
        Real.exp ((n : ℝ) * u - theta) := by
      rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]

/-! ### Uniform optimization of the Chernoff bound -/

/-- The clipped-tilt optimization for the campaign's quadratic coefficient.
For `K = 10⁹` and the available box `|λ| ≤ 1/4000`, the central optimizer is
`λ = dev/(2Kn)` and the saturated optimizer gives the linear tail. -/
theorem chernoff_clipP_le {n : ℕ} (hn : 1 ≤ n) (dev : ℝ) :
    ∃ lam : ℝ, -(1 / 4000) ≤ lam ∧ lam ≤ 1 / 4000 ∧
      1000000000 * (n : ℝ) * lam ^ 2 - lam * dev ≤
        -min (dev ^ 2 / (4000000000 * n)) (|dev| / 8000) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hne : (n : ℝ) ≠ 0 := hnpos.ne'
  by_cases hc : |dev| ≤ 500000 * n
  · have habs : |dev / (2000000000 * n)| ≤ 1 / 4000 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2000000000 * n),
        div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg dev]
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    refine ⟨dev / (2000000000 * n), hlo, hhi, ?_⟩
    have heq :
        1000000000 * (n : ℝ) * (dev / (2000000000 * n)) ^ 2 -
            dev / (2000000000 * n) * dev =
          -(dev ^ 2 / (4000000000 * n)) := by
      field_simp
      ring
    rw [heq, neg_le_neg_iff]
    exact min_le_left _ _
  · push Not at hc
    refine ⟨if 0 ≤ dev then (1 / 4000 : ℝ) else -(1 / 4000), ?_, ?_, ?_⟩
    · split_ifs <;> norm_num
    · split_ifs <;> norm_num
    · have habs : (if 0 ≤ dev then (1 / 4000 : ℝ) else -(1 / 4000)) * dev =
          |dev| / 4000 := by
        split_ifs with h
        · rw [abs_of_nonneg h]
          ring
        · rw [abs_of_neg (lt_of_not_ge h)]
          ring
      have hsq : (if 0 ≤ dev then (1 / 4000 : ℝ) else -(1 / 4000)) ^ 2 =
          1 / 16000000 := by
        split_ifs <;> norm_num
      rw [habs, hsq]
      refine le_trans ?_
        (neg_le_neg (min_le_right (dev ^ 2 / (4000000000 * n)) (|dev| / 8000)))
      linarith

/-- The optimized exponent from `chernoff_clipP_le` fits Tao's two-branch
`Gweight`, with a constant independent of `p`. -/
theorem exp_neg_minP_le_Gweight {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-min (x ^ 2 / (4000000000 * n)) (x / 8000)) ≤
      TaoCollatz.Gweight (1 + n) (1 / 100000 * x) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  rcases min_cases (x ^ 2 / (4000000000 * (n : ℝ))) (x / 8000) with
    ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm]
    have hbr : Real.exp (-(x ^ 2 / (4000000000 * n))) ≤
        Real.exp (-((1 / 100000 * x) ^ 2) / (1 + (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_le_neg_iff,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) hnpos.le]
    exact le_trans hbr (le_add_of_nonneg_right (Real.exp_pos _).le)
  · rw [hm]
    have harg : -(x / 8000) ≤ -|1 / 100000 * x| := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 100000 * x)]
      nlinarith
    exact le_trans (Real.exp_le_exp.mpr harg)
      (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- The uniform spatial scale in the local bound for `holdP`. -/
noncomputable def c_holdLocalP : ℝ := 1 / 100000

/-- The uniform center-bound constant in the local bound for `holdP`. -/
noncomputable def C_holdLocalP : ℝ := (32 * 312500000) ^ 2

theorem c_holdLocalP_pos : 0 < c_holdLocalP := by
  unfold c_holdLocalP
  norm_num

theorem C_holdLocalP_pos : 0 < C_holdLocalP := by
  unfold C_holdLocalP
  positivity

/-- Tao's Lemma 2.2(i) for the parameterized holding walk, with constants
chosen uniformly before `p`.  The center is the exact drift
`n q(p)⁻¹ (1, 2/p)`. -/
theorem holdP_local_bound_explicitC (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (n j : ℕ) (l : ℤ) :
    ((holdSumP p (by linarith) (by linarith) n) (j, l)).toReal ≤
      C_holdLocalP / (1 + n) *
        TaoCollatz.Gweight (1 + n)
          (c_holdLocalP *
            ‖(((j : ℝ) - (pairThreeProb p)⁻¹ * n,
              (l : ℝ) - ((pairThreeProb p)⁻¹ * (2 / p)) * n) : ℝ × ℝ)‖) := by
  unfold c_holdLocalP C_holdLocalP
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [holdSumP_eq_iidSum p hp0' hp1' 0, TaoCollatz.iidSum_zero,
      PMF.pure_apply]
    split_ifs with h
    · have hj : j = 0 := congrArg Prod.fst h
      have hl : l = 0 := congrArg Prod.snd h
      subst hj
      subst hl
      rw [ENNReal.toReal_one]
      norm_num [TaoCollatz.Gweight, Prod.norm_def, Real.norm_eq_abs,
        Real.exp_zero]
    · rw [ENNReal.toReal_zero]
      exact mul_nonneg (by positivity) (TaoCollatz.Gweight_nonneg _ _)
  · have hn1 : 1 ≤ n := hn
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := by linarith
    let m1 : ℝ := (pairThreeProb p)⁻¹
    let m2 : ℝ := (pairThreeProb p)⁻¹ * (2 / p)
    set d1 : ℝ := (j : ℝ) - m1 * n with hd1
    set d2 : ℝ := (l : ℝ) - m2 * n with hd2
    obtain ⟨l1, h1lo, h1hi, hE1⟩ := chernoff_clipP_le hn1 d1
    obtain ⟨l2, h2lo, h2hi, hE2⟩ := chernoff_clipP_le hn1 d2
    have hch := holdSumP_apply_le_chernoff_window hp0 hp1
      h1lo h1hi h2lo h2hi n j l
    change ((holdSumP p hp0' hp1' n) (j, l)).toReal ≤
      (32 * 312500000 : ℝ) ^ 2 / (1 + (n : ℝ)) *
        Real.exp ((n : ℝ) * (m1 * l1 + m2 * l2 +
          1000000000 * (l1 ^ 2 + l2 ^ 2)) - (l1 * j + l2 * l)) at hch
    have hEeq :
        (n : ℝ) * (m1 * l1 + m2 * l2 +
            1000000000 * (l1 ^ 2 + l2 ^ 2)) - (l1 * j + l2 * l) =
          (1000000000 * n * l1 ^ 2 - l1 * d1) +
            (1000000000 * n * l2 ^ 2 - l2 * d2) := by
      rw [hd1, hd2]
      ring
    rw [hEeq] at hch
    set M : ℝ := max |d1| |d2| with hM
    have hnorm : ‖((d1, d2) : ℝ × ℝ)‖ = M := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have hM0 : 0 ≤ M := le_trans (abs_nonneg d1) (le_max_left _ _)
    have hmin_nonneg : ∀ x : ℝ,
        0 ≤ min (x ^ 2 / (4000000000 * n)) (|x| / 8000) := fun x =>
      le_min (by positivity) (by positivity)
    have hEle :
        (1000000000 * n * l1 ^ 2 - l1 * d1) +
            (1000000000 * n * l2 ^ 2 - l2 * d2) ≤
          -min (M ^ 2 / (4000000000 * n)) (M / 8000) := by
      rcases max_cases |d1| |d2| with ⟨hMe, _⟩ | ⟨hMe, _⟩
      · have h2np : 1000000000 * n * l2 ^ 2 - l2 * d2 ≤ 0 :=
          le_trans hE2 (neg_nonpos.mpr (hmin_nonneg d2))
        have hsq : M ^ 2 = d1 ^ 2 := by rw [hM, hMe, sq_abs]
        have habs : M = |d1| := by rw [hM, hMe]
        calc
          (1000000000 * n * l1 ^ 2 - l1 * d1) +
              (1000000000 * n * l2 ^ 2 - l2 * d2) ≤
              -min (d1 ^ 2 / (4000000000 * n)) (|d1| / 8000) + 0 :=
            add_le_add hE1 h2np
          _ = -min (M ^ 2 / (4000000000 * n)) (M / 8000) := by
            rw [add_zero, hsq, habs]
      · have h1np : 1000000000 * n * l1 ^ 2 - l1 * d1 ≤ 0 :=
          le_trans hE1 (neg_nonpos.mpr (hmin_nonneg d1))
        have hsq : M ^ 2 = d2 ^ 2 := by rw [hM, hMe, sq_abs]
        have habs : M = |d2| := by rw [hM, hMe]
        calc
          (1000000000 * n * l1 ^ 2 - l1 * d1) +
              (1000000000 * n * l2 ^ 2 - l2 * d2) ≤
              0 + -min (d2 ^ 2 / (4000000000 * n)) (|d2| / 8000) :=
            add_le_add h1np hE2
          _ = -min (M ^ 2 / (4000000000 * n)) (M / 8000) := by
            rw [zero_add, hsq, habs]
    have hGw :
        Real.exp ((1000000000 * n * l1 ^ 2 - l1 * d1) +
          (1000000000 * n * l2 ^ 2 - l2 * d2)) ≤
            TaoCollatz.Gweight (1 + n) (1 / 100000 * M) :=
      le_trans (Real.exp_le_exp.mpr hEle) (exp_neg_minP_le_Gweight hn1 hM0)
    calc
      ((holdSumP p hp0' hp1' n) (j, l)).toReal ≤
          (32 * 312500000 : ℝ) ^ 2 / (1 + (n : ℝ)) *
            Real.exp ((1000000000 * n * l1 ^ 2 - l1 * d1) +
              (1000000000 * n * l2 ^ 2 - l2 * d2)) := hch
      _ ≤ (32 * 312500000 : ℝ) ^ 2 / (1 + (n : ℝ)) *
          TaoCollatz.Gweight (1 + n) (1 / 100000 * M) :=
        mul_le_mul_of_nonneg_left hGw (by positivity)
      _ = (32 * 312500000 : ℝ) ^ 2 / (1 + (n : ℝ)) *
          TaoCollatz.Gweight (1 + n)
            (1 / 100000 * ‖((d1, d2) : ℝ × ℝ)‖) := by rw [hnorm]

/-- Existential interface for the uniform local bound.  The quantifier order
records that both constants are chosen before the tilt parameter `p`. -/
theorem holdP_local_bound_window :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ (n j : ℕ) (l : ℤ),
        ((holdSumP p (by linarith) (by linarith) n) (j, l)).toReal ≤
          C / (1 + n) *
            TaoCollatz.Gweight (1 + n)
              (c * ‖(((j : ℝ) - (pairThreeProb p)⁻¹ * n,
                (l : ℝ) - ((pairThreeProb p)⁻¹ * (2 / p)) * n) : ℝ × ℝ)‖) :=
  ⟨c_holdLocalP, c_holdLocalP_pos, C_holdLocalP, C_holdLocalP_pos,
    holdP_local_bound_explicitC⟩
end TaoCollatz.Sec7P
