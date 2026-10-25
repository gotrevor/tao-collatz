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

end TaoCollatz.Sec7P
