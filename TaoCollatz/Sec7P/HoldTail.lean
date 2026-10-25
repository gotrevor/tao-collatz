/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.HoldBasics
import TaoCollatz.Prob.Mgf

/-!
# Uniform exponential tail of the tilted holding law

This file completes the probability layer for Tao's tilted §7 argument.  It computes
the moment generating functions of `Geom(p)`, `Pascal(p)`, the law conditioned away
from `3`, and `HoldP`.  The deletion of the `3` atom leaves a uniform geometric-series
ratio at most `19/20` on `p ∈ [1/5,3/5]`.  Consequently the `HoldP` MGF at the fixed
positive tilt `(1/1000, 1/1000)` is at most `6`, giving a window-uniform exponential
tail with rate `1/1000`.
-/

open scoped ENNReal NNReal

namespace TaoCollatz.Sec7P

/-- Exact MGF of the positive geometric law. -/
theorem tiltZ_geomP (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (lam : ℝ) :
    TaoCollatz.tiltZ (geomP p hp0 hp1) (TaoCollatz.expW lam) =
      ENNReal.ofReal (p * Real.exp lam) *
        (1 - ENNReal.ofReal ((1 - p) * Real.exp lam))⁻¹ := by
  let r : ℝ≥0∞ := ENNReal.ofReal ((1 - p) * Real.exp lam)
  have hr0 : 0 ≤ (1 - p) * Real.exp lam :=
    mul_nonneg (sub_nonneg.mpr hp1) (Real.exp_pos _).le
  have hterm : ∀ a : ℕ,
      geomP p hp0 hp1 a * TaoCollatz.expW lam a =
        if a = 0 then 0 else ENNReal.ofReal (p * Real.exp lam) * r ^ (a - 1) := by
    intro a
    rw [geomP_apply, TaoCollatz.expW]
    split_ifs with ha
    · simp
    · rw [← ENNReal.ofReal_mul (by positivity [sub_nonneg.mpr hp1])]
      rw [show p * (1 - p) ^ (a - 1) * Real.exp (lam * a) =
          (p * Real.exp lam) * (((1 - p) * Real.exp lam) ^ (a - 1)) by
        obtain ⟨j, rfl⟩ : ∃ j, a = j + 1 := ⟨a - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [mul_pow]
        push_cast
        rw [mul_add, Real.exp_add, mul_one]
        have hexp : Real.exp (lam * (j : ℝ)) = Real.exp lam ^ j := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        rw [hexp]
        ring]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr0]
  rw [TaoCollatz.tiltZ, tsum_congr hterm,
    tsum_ite_zero_eq_succ (fun a => ENNReal.ofReal (p * Real.exp lam) * r ^ (a - 1))]
  simp only [Nat.add_sub_cancel]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- A scaled geometric MGF is at most one when its numerator plus geometric
ratio is at most one.  This is the one-dimensional supermartingale test used
below for the transverse coordinate. -/
theorem tiltZ_geomP_scaled_le_one (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (lam mu : ℝ)
    (hmix : p * Real.exp (mu + lam) + (1 - p) * Real.exp lam ≤ 1) :
    ENNReal.ofReal (Real.exp mu) *
      TaoCollatz.tiltZ (geomP p hp0 hp1) (TaoCollatz.expW lam) ≤ 1 := by
  rw [tiltZ_geomP]
  set N : ℝ≥0∞ := ENNReal.ofReal (p * Real.exp (mu + lam)) with hNdef
  set R : ℝ≥0∞ := ENNReal.ofReal ((1 - p) * Real.exp lam) with hRdef
  have hfront : ENNReal.ofReal (Real.exp mu) *
      ENNReal.ofReal (p * Real.exp lam) = N := by
    rw [hNdef, ← ENNReal.ofReal_mul (Real.exp_pos mu).le]
    congr 1
    rw [Real.exp_add]
    ring
  rw [← mul_assoc, hfront]
  have hN0 : 0 ≤ p * Real.exp (mu + lam) := by positivity
  have hR0 : 0 ≤ (1 - p) * Real.exp lam :=
    mul_nonneg (sub_nonneg.mpr hp1) (Real.exp_pos _).le
  have hNR : N + R ≤ 1 := by
    rw [hNdef, hRdef, ← ENNReal.ofReal_add hN0 hR0,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal hmix
  have hRtop : R ≠ ∞ := by simp [hRdef]
  have hNsub : N ≤ 1 - R := ENNReal.le_sub_of_add_le_right hRtop hNR
  calc
    N * (1 - R)⁻¹ ≤ (1 - R) * (1 - R)⁻¹ := by
      simpa [mul_comm] using mul_le_mul_right hNsub ((1 - R)⁻¹)
    _ ≤ 1 := ENNReal.mul_inv_le_one _

/-- The tilted geometric MGF is nonzero. -/
theorem tiltZ_geomP_ne_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (lam : ℝ) :
    TaoCollatz.tiltZ (geomP p hp0 hp1) (TaoCollatz.expW lam) ≠ 0 := by
  intro h0
  have hle : geomP p hp0 hp1 1 * TaoCollatz.expW lam 1 ≤
      TaoCollatz.tiltZ (geomP p hp0 hp1) (TaoCollatz.expW lam) := ENNReal.le_tsum 1
  rw [h0, le_zero_iff, mul_eq_zero] at hle
  rcases hle with h | h
  · have hr := congrArg ENNReal.toReal h
    rw [geomP_toReal] at hr
    norm_num at hr
    exact hp0.ne' hr
  · rw [TaoCollatz.expW, ENNReal.ofReal_eq_zero] at h
    exact (not_le.mpr (Real.exp_pos _)) h

/-- Finiteness strip for the tilted geometric MGF. -/
theorem tiltZ_geomP_ne_top (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) {lam : ℝ}
    (hstrip : (1 - p) * Real.exp lam < 1) :
    TaoCollatz.tiltZ (geomP p hp0 hp1) (TaoCollatz.expW lam) ≠ ∞ := by
  rw [tiltZ_geomP]
  have hr1 : ENNReal.ofReal ((1 - p) * Real.exp lam) < 1 :=
    ENNReal.ofReal_lt_one.mpr hstrip
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (by
      rw [Ne, tsub_eq_zero_iff_le, not_le]
      exact hr1))

/-- MGF of `Pascal(p)` as the square of the geometric MGF. -/
theorem tiltZ_pascalP (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) {lam : ℝ}
    (hstrip : (1 - p) * Real.exp lam < 1) :
    TaoCollatz.tiltZ (pascalP p hp0 hp1) (TaoCollatz.expW lam) =
      (TaoCollatz.tiltZ (geomP p hp0 hp1) (TaoCollatz.expW lam)) ^ 2 := by
  rw [pascalP_eq_iidSum]
  exact TaoCollatz.tiltZ_iidSum (geomP p hp0 hp1) (TaoCollatz.expW_zero lam)
    (TaoCollatz.expW_add lam) (tiltZ_geomP_ne_zero p hp0 hp1 lam)
    (tiltZ_geomP_ne_top p hp0 hp1 hstrip) 2

/-- Atom-split identity for `Pascal(p)` conditioned away from `3`. -/
theorem tiltZ_pascalNe3P_add (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (lam : ℝ) :
    ENNReal.ofReal (1 - pairThreeProb p) *
        TaoCollatz.tiltZ (pascalNe3P p hp0 hp1) (TaoCollatz.expW lam) +
      ENNReal.ofReal (pairThreeProb p) * TaoCollatz.expW lam 3 =
        TaoCollatz.tiltZ (pascalP p hp0 hp1) (TaoCollatz.expW lam) := by
  classical
  let q := pairThreeProb p
  let pp := pascalP p hp0 hp1
  let pn := pascalNe3P p hp0 hp1
  have hq := pairThreeProb_basic_bounds p hp0 hp1
  have hden : 0 < 1 - q := by dsimp [q]; linarith
  have hscale : ∀ b : ℕ, ENNReal.ofReal (1 - q) * pn b =
      if b = 3 then 0 else pp b := by
    intro b
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (pn.apply_ne_top b))
      (by split_ifs; exact ENNReal.zero_ne_top; exact pp.apply_ne_top b)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hden.le]
    by_cases hb : b = 3
    · subst b
      rw [if_pos rfl]
      dsimp [pn]
      rw [pascalNe3P_apply_three]
      simp
    · rw [if_neg hb]
      dsimp [pn, pp, q]
      rw [pascalNe3P_toReal, if_neg hb]
      dsimp [q] at hden
      rw [← mul_assoc, mul_inv_cancel₀ hden.ne', one_mul]
  have hp3 : pp 3 = ENNReal.ofReal q := by
    dsimp [pp, q]
    rw [pascalP_apply]
    norm_num [pairThreeProb]
  change ENNReal.ofReal (1 - q) *
        (∑' b : ℕ, pn b * TaoCollatz.expW lam b) +
      ENNReal.ofReal q * TaoCollatz.expW lam 3 =
        ∑' b : ℕ, pp b * TaoCollatz.expW lam b
  rw [← ENNReal.tsum_mul_left]
  rw [tsum_congr fun b => by rw [← mul_assoc, hscale]]
  rw [← hp3]
  convert (ENNReal.tsum_eq_add_tsum_ite
    (f := fun b : ℕ => pp b * TaoCollatz.expW lam b) 3).symm using 1
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro b
  by_cases hb : b = 3 <;> simp [hb]

/-- The conditioned MGF is bounded by the unconditioned one divided by the
conditioning mass. -/
theorem tiltZ_pascalNe3P_le (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (lam : ℝ) :
    TaoCollatz.tiltZ (pascalNe3P p hp0 hp1) (TaoCollatz.expW lam) ≤
      ENNReal.ofReal (1 - pairThreeProb p)⁻¹ *
        TaoCollatz.tiltZ (pascalP p hp0 hp1) (TaoCollatz.expW lam) := by
  classical
  have hq := pairThreeProb_basic_bounds p hp0 hp1
  have hden : 0 < 1 - pairThreeProb p := by linarith
  rw [TaoCollatz.tiltZ, TaoCollatz.tiltZ, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun b => ?_
  have hmass : pascalNe3P p hp0 hp1 b =
      ENNReal.ofReal (1 - pairThreeProb p)⁻¹ *
        (if b = 3 then 0 else pascalP p hp0 hp1 b) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      ((pascalNe3P p hp0 hp1).apply_ne_top b)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by split_ifs
        <;> simp only [ne_eq, ENNReal.zero_ne_top, not_false_eq_true,
          (pascalP p hp0 hp1).apply_ne_top b]))).mp
    by_cases hb : b = 3
    · subst b
      rw [if_pos rfl, pascalNe3P_apply_three]
      simp
    · rw [if_neg hb, pascalNe3P_toReal, if_neg hb, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (inv_nonneg.mpr hden.le)]
  rw [hmass, mul_assoc]
  gcongr
  split_ifs <;> simp

/-- Finiteness of the conditioned MGF inside the geometric strip. -/
theorem tiltZ_pascalNe3P_ne_top (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) {lam : ℝ}
    (hstrip : (1 - p) * Real.exp lam < 1) :
    TaoCollatz.tiltZ (pascalNe3P p hp0 hp1) (TaoCollatz.expW lam) ≠ ∞ := by
  have hpTop : TaoCollatz.tiltZ (pascalP p hp0 hp1) (TaoCollatz.expW lam) ≠ ∞ := by
    rw [tiltZ_pascalP p hp0 hp1 hstrip]
    exact ENNReal.pow_ne_top (tiltZ_geomP_ne_top p hp0 hp1 hstrip)
  have htop : ENNReal.ofReal (1 - pairThreeProb p)⁻¹ *
      TaoCollatz.tiltZ (pascalP p hp0 hp1) (TaoCollatz.expW lam) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpTop
  apply ne_top_of_le_ne_top htop
  exact tiltZ_pascalNe3P_le p hp0 hp1 lam

/-- The conditioned Pascal MGF is nonzero. -/
theorem tiltZ_pascalNe3P_ne_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (lam : ℝ) :
    TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le) (TaoCollatz.expW lam) ≠ 0 := by
  intro h0
  have hle : pascalNe3P p hp0 hp1.le 2 * TaoCollatz.expW lam 2 ≤
      TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le) (TaoCollatz.expW lam) :=
    ENNReal.le_tsum 2
  rw [h0, le_zero_iff, mul_eq_zero] at hle
  rcases hle with h | h
  · have hs := pascalNe3P_mem_support p hp0 hp1 2 le_rfl (by norm_num)
    rw [PMF.mem_support_iff] at hs
    exact hs h
  · rw [TaoCollatz.expW, ENNReal.ofReal_eq_zero] at h
    exact (not_le.mpr (Real.exp_pos _)) h

/-- The MGF of the tilted holding law, conditioned on its first coordinate. -/
theorem tiltZ_holdP_factor (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (l1 l2 : ℝ)
    (hZ0 : TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le) (TaoCollatz.expW l2) ≠ 0)
    (hZt : TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le) (TaoCollatz.expW l2) ≠ ∞) :
    TaoCollatz.tiltZ (holdP p hp0 hp1) (TaoCollatz.expW2 l1 l2) =
      ∑' k : ℕ, geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
          (pairThreeProb_le_one p hp0 hp1) k *
        (ENNReal.ofReal (Real.exp (l1 * k + 3 * l2)) *
          (TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le)
            (TaoCollatz.expW l2)) ^ (k - 1)) := by
  rw [TaoCollatz.tiltZ]
  unfold holdP
  rw [PMF.tsum_bind_mul]
  refine tsum_congr fun k => ?_
  congr 1
  rw [PMF.tsum_map_mul]
  have hterm : ∀ v : Fin (k - 1) → ℕ,
      ((pascalNe3P p hp0 hp1.le).iid (k - 1)) v *
          TaoCollatz.expW2 l1 l2 ((k : ℕ), ((3 : ℤ) + ∑ i, (v i : ℤ))) =
        ENNReal.ofReal (Real.exp (l1 * k + 3 * l2)) *
          (((pascalNe3P p hp0 hp1.le).iid (k - 1)) v *
            TaoCollatz.expW l2 (∑ i, v i)) := by
    intro v
    simp only [TaoCollatz.expW2, TaoCollatz.expW]
    rw [show l1 * (((k : ℕ), ((3 : ℤ) + ∑ i, (v i : ℤ))).1 : ℕ) +
          l2 * ((((k : ℕ), ((3 : ℤ) + ∑ i, (v i : ℤ))).2 : ℤ) : ℝ) =
        (l1 * k + 3 * l2) + l2 * ((∑ i, v i : ℕ) : ℝ) by
      push_cast
      ring]
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  congr 1
  have hiid : ∑' v, ((pascalNe3P p hp0 hp1.le).iid (k - 1)) v *
        TaoCollatz.expW l2 (∑ i, v i) =
      TaoCollatz.tiltZ (TaoCollatz.iidSum (pascalNe3P p hp0 hp1.le) (k - 1))
        (TaoCollatz.expW l2) := by
    rw [TaoCollatz.tiltZ, TaoCollatz.iidSum, PMF.tsum_map_mul]
  rw [hiid, TaoCollatz.tiltZ_iidSum (pascalNe3P p hp0 hp1.le)
    (TaoCollatz.expW_zero l2) (TaoCollatz.expW_add l2) hZ0 hZt]

/-- Closed form of the tilted holding-law MGF. -/
theorem tiltZ_holdP_closed (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (l1 l2 : ℝ)
    (hZt : TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le) (TaoCollatz.expW l2) ≠ ∞) :
    TaoCollatz.tiltZ (holdP p hp0 hp1) (TaoCollatz.expW2 l1 l2) =
      ENNReal.ofReal (pairThreeProb p * Real.exp (l1 + 3 * l2)) *
        (1 - ENNReal.ofReal ((1 - pairThreeProb p) * Real.exp l1) *
          TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le) (TaoCollatz.expW l2))⁻¹ := by
  have hZ0 := tiltZ_pascalNe3P_ne_zero p hp0 hp1 l2
  rw [tiltZ_holdP_factor p hp0 hp1 l1 l2 hZ0 hZt]
  let q := pairThreeProb p
  let Z := TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le) (TaoCollatz.expW l2)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact (pairThreeProb_basic_bounds p hp0 hp1.le).1
  have hq1 : q ≤ 1 := (pairThreeProb_le_one p hp0 hp1)
  have hterm : ∀ k : ℕ,
      geomP q (pairThreeProb_pos p hp0 hp1) hq1 k *
          (ENNReal.ofReal (Real.exp (l1 * k + 3 * l2)) * Z ^ (k - 1)) =
        if k = 0 then 0 else
          ENNReal.ofReal (q * Real.exp (l1 + 3 * l2)) *
            (ENNReal.ofReal ((1 - q) * Real.exp l1) * Z) ^ (k - 1) := by
    intro k
    match k with
    | 0 =>
      rw [geomP_apply]
      simp
    | (j + 1) =>
      rw [if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, geomP_apply,
        if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
      have hsplit : ENNReal.ofReal (Real.exp (l1 * (j + 1 : ℕ) + 3 * l2)) =
          ENNReal.ofReal (Real.exp (l1 + 3 * l2)) *
            ENNReal.ofReal (Real.exp l1) ^ j := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 2
        push_cast
        ring
      rw [hsplit, ENNReal.ofReal_mul hq0,
        ENNReal.ofReal_pow (sub_nonneg.mpr hq1),
        ENNReal.ofReal_mul (sub_nonneg.mpr hq1)]
      have hbase : ENNReal.ofReal (q * Real.exp (l1 + 3 * l2)) =
          ENNReal.ofReal q * ENNReal.ofReal (Real.exp (l1 + 3 * l2)) := by
        rw [ENNReal.ofReal_mul hq0]
      rw [hbase]
      rw [mul_pow, mul_pow]
      ring
  rw [tsum_congr hterm, tsum_ite_zero_eq_succ
    (fun k => ENNReal.ofReal (q * Real.exp (l1 + 3 * l2)) *
      (ENNReal.ofReal ((1 - q) * Real.exp l1) * Z) ^ (k - 1))]
  simp only [Nat.add_sub_cancel]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- The stopped holding-law MGF is at most one whenever the underlying
unconditioned Pascal increment has the corresponding supermartingale tilt.
The deleted `3` atom cancels exactly between the numerator and the geometric
ratio, so no geometric-series loss remains. -/
theorem tiltZ_holdP_le_one_of_pascalP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (l1 l2 : ℝ) (hstrip : (1 - p) * Real.exp l2 < 1)
    (hpascal : ENNReal.ofReal (Real.exp l1) *
      TaoCollatz.tiltZ (pascalP p hp0 hp1.le) (TaoCollatz.expW l2) ≤ 1) :
    TaoCollatz.tiltZ (holdP p hp0 hp1) (TaoCollatz.expW2 l1 l2) ≤ 1 := by
  have hq := pairThreeProb_basic_bounds p hp0 hp1.le
  have hZt := tiltZ_pascalNe3P_ne_top p hp0 hp1.le hstrip
  rw [tiltZ_holdP_closed p hp0 hp1 l1 l2 hZt]
  set N : ℝ≥0∞ := ENNReal.ofReal
    (pairThreeProb p * Real.exp (l1 + 3 * l2)) with hNdef
  set R : ℝ≥0∞ := ENNReal.ofReal
      ((1 - pairThreeProb p) * Real.exp l1) *
        TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le) (TaoCollatz.expW l2) with hRdef
  have hN : N = ENNReal.ofReal (Real.exp l1) *
      (ENNReal.ofReal (pairThreeProb p) * TaoCollatz.expW l2 3) := by
    rw [hNdef, TaoCollatz.expW]
    have hexp : Real.exp (l1 + 3 * l2) =
        Real.exp l1 * Real.exp (l2 * (3 : ℕ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp, ENNReal.ofReal_mul hq.1,
      ENNReal.ofReal_mul (Real.exp_pos l1).le]
    ring
  have hR : R = ENNReal.ofReal (Real.exp l1) *
      (ENNReal.ofReal (1 - pairThreeProb p) *
        TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le) (TaoCollatz.expW l2)) := by
    have hq1 : pairThreeProb p ≤ 1 := hq.2.trans (by norm_num)
    rw [hRdef, ENNReal.ofReal_mul (sub_nonneg.mpr hq1)]
    ring
  have hNR : N + R ≤ 1 := by
    calc
      N + R = ENNReal.ofReal (Real.exp l1) *
          (ENNReal.ofReal (1 - pairThreeProb p) *
              TaoCollatz.tiltZ (pascalNe3P p hp0 hp1.le) (TaoCollatz.expW l2) +
            ENNReal.ofReal (pairThreeProb p) * TaoCollatz.expW l2 3) := by
              rw [hN, hR]
              ring
      _ = ENNReal.ofReal (Real.exp l1) *
          TaoCollatz.tiltZ (pascalP p hp0 hp1.le) (TaoCollatz.expW l2) := by
            rw [tiltZ_pascalNe3P_add]
      _ ≤ 1 := hpascal
  have hRtop : R ≠ ∞ := ne_top_of_le_ne_top (by simp)
    (le_trans (le_add_left (le_refl R)) hNR)
  have hNsub : N ≤ 1 - R := ENNReal.le_sub_of_add_le_right hRtop hNR
  calc
    N * (1 - R)⁻¹ ≤ (1 - R) * (1 - R)⁻¹ := by
      simpa [mul_comm] using mul_le_mul_right hNsub ((1 - R)⁻¹)
    _ ≤ 1 := ENNReal.mul_inv_le_one _

/-- The scalar inequality behind the campaign's transverse supermartingale:
at `θ = 1/100`, the worst parameter is `p = 3/5`, and even there
`p e^(3θ) + (1-p)e^(-5θ) < 1`. -/
theorem transverse_mix_le_one {p : ℝ} (_hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    p * Real.exp (3 / 100) + (1 - p) * Real.exp (-1 / 20) ≤ 1 := by
  have hepos : Real.exp (3 / 100) ≤ 103046 / 100000 := by
    have h := Real.exp_bound (x := 3 / 100)
      (by rw [abs_le]; constructor <;> norm_num) (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [Nat.factorial] at h
    rw [abs_le] at h
    nlinarith [h.1, h.2]
  have heneg : Real.exp (-1 / 20) ≤ 95123 / 100000 := by
    have h := Real.exp_bound (x := -1 / 20)
      (by rw [abs_le]; constructor <;> norm_num) (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [Nat.factorial] at h
    rw [abs_le] at h
    nlinarith [h.1, h.2]
  have hmono : Real.exp (-1 / 20) ≤ Real.exp (3 / 100) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hprod : 0 ≤ (3 / 5 - p) *
      (Real.exp (3 / 100) - Real.exp (-1 / 20)) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hmono)
  calc
    p * Real.exp (3 / 100) + (1 - p) * Real.exp (-1 / 20) ≤
        (3 / 5) * Real.exp (3 / 100) + (2 / 5) * Real.exp (-1 / 20) := by
          nlinarith
    _ ≤ (3 / 5) * (103046 / 100000) + (2 / 5) * (95123 / 100000) := by
          gcongr
    _ ≤ 1 := by norm_num

/-- The unconditioned Pascal increment is a transverse supermartingale at
`θ = 1/100`, uniformly throughout the campaign window. -/
theorem tiltZ_pascalP_transverse_le_one {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    ENNReal.ofReal (Real.exp (4 / 25)) *
      TaoCollatz.tiltZ (pascalP p (by linarith) (by linarith))
        (TaoCollatz.expW (-1 / 20)) ≤ 1 := by
  let hp0' : 0 < p := by linarith
  let hp1' : p ≤ 1 := by linarith
  have hmix : p * Real.exp ((2 / 25 : ℝ) + (-1 / 20)) +
      (1 - p) * Real.exp (-1 / 20) ≤ 1 := by
    norm_num
    convert transverse_mix_le_one hp0 hp1 using 1
    all_goals norm_num
  have hgeom := tiltZ_geomP_scaled_le_one p hp0' hp1'
    (-1 / 20) (2 / 25) hmix
  have hstrip : (1 - p) * Real.exp (-1 / 20) < 1 := by
    have he : Real.exp (-1 / 20) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hm : (1 - p) * Real.exp (-1 / 20) ≤ 1 - p :=
      mul_le_of_le_one_right (by linarith) he
    linarith
  rw [tiltZ_pascalP p hp0' hp1' hstrip]
  have hscale : ENNReal.ofReal (Real.exp (4 / 25)) =
      ENNReal.ofReal (Real.exp (2 / 25)) ^ 2 := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    norm_num
  rw [hscale, ← mul_pow]
  exact (pow_le_pow_left' hgeom 2).trans_eq (one_pow 2)

/-- The tilted holding increment has transverse MGF at most one at
`θ = 1/100`, uniformly in `p ∈ [1/5,3/5]`. -/
theorem tiltZ_holdP_transverse_le_one {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    TaoCollatz.tiltZ (holdP p (by linarith) (by linarith))
      (TaoCollatz.expW2 (4 / 25) (-1 / 20)) ≤ 1 := by
  have hstrip : (1 - p) * Real.exp (-1 / 20) < 1 := by
    have he : Real.exp (-1 / 20) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hm : (1 - p) * Real.exp (-1 / 20) ≤ 1 - p :=
      mul_le_of_le_one_right (by linarith) he
    linarith
  exact tiltZ_holdP_le_one_of_pascalP p (by linarith) (by linarith)
    (4 / 25) (-1 / 20) hstrip (tiltZ_pascalP_transverse_le_one hp0 hp1)

/-- At the fixed campaign tilt `1/1000`, the geometric MGF is bounded
uniformly on `p ∈ [1/5,3/5]`. -/
theorem tiltZ_geomP_le_window {p : ℝ} (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    TaoCollatz.tiltZ (geomP p (by linarith) (by linarith))
        (TaoCollatz.expW (1 / 1000)) ≤ ENNReal.ofReal (200 / 199) := by
  have hp_pos : 0 < p := by linarith
  have hp_one : p ≤ 1 := by linarith
  have he : Real.exp (1 / 1000) ≤ 1000 / 999 := by
    calc
      Real.exp (1 / 1000) ≤ (1 - 1 / 1000)⁻¹ :=
        TaoCollatz.exp_le_inv_one_sub (by norm_num)
      _ = 1000 / 999 := by norm_num
  have hstrip : (1 - p) * Real.exp (1 / 1000) < 1 := by
    have hm : (1 - p) * Real.exp (1 / 1000) ≤ (4 / 5) * (1000 / 999) :=
      mul_le_mul (by linarith) he (Real.exp_pos _).le (by norm_num)
    norm_num at hm ⊢
    linarith
  have hden : 0 < 1 - (1 - p) * Real.exp (1 / 1000) := sub_pos.mpr hstrip
  rw [tiltZ_geomP]
  rw [show (1 : ℝ≥0∞) - ENNReal.ofReal ((1 - p) * Real.exp (1 / 1000)) =
      ENNReal.ofReal (1 - (1 - p) * Real.exp (1 / 1000)) by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub 1 (mul_nonneg (sub_nonneg.mpr hp_one) (Real.exp_pos _).le)]]
  rw [← ENNReal.ofReal_inv_of_pos hden,
    ← ENNReal.ofReal_mul (mul_nonneg hp_pos.le (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ hden).2
  have hcoef0 : 0 ≤ 200 - p := by linarith
  have hcoef : 200 - p ≤ 999 / 5 := by linarith
  have hmul : (200 - p) * Real.exp (1 / 1000) ≤
      (999 / 5) * (1000 / 999) :=
    mul_le_mul hcoef he (Real.exp_pos _).le (by norm_num)
  norm_num at hmul
  nlinarith

/-- The geometric-series ratio in the holding MGF is uniformly below `19/20`.
The deleted `b = 3` atom supplies the strict margin. -/
theorem holdP_mgf_ratio_le_window {p : ℝ} (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    ENNReal.ofReal (Real.exp (1 / 1000)) *
        (ENNReal.ofReal (1 - pairThreeProb p) *
          TaoCollatz.tiltZ (pascalNe3P p (by linarith) (by linarith))
            (TaoCollatz.expW (1 / 1000))) ≤ ENNReal.ofReal (19 / 20) := by
  have hp_pos : 0 < p := by linarith
  have hp_one : p ≤ 1 := by linarith
  have hp_lt_one : p < 1 := by linarith
  have hq := pairThreeProb_mem_window hp0 hp1
  have he : Real.exp (1 / 1000) ≤ 1000 / 999 := by
    calc
      Real.exp (1 / 1000) ≤ (1 - 1 / 1000)⁻¹ :=
        TaoCollatz.exp_le_inv_one_sub (by norm_num)
      _ = 1000 / 999 := by norm_num
  have hstrip : (1 - p) * Real.exp (1 / 1000) < 1 := by
    have hm : (1 - p) * Real.exp (1 / 1000) ≤ (4 / 5) * (1000 / 999) :=
      mul_le_mul (by linarith) he (Real.exp_pos _).le (by norm_num)
    norm_num at hm ⊢
    linarith
  have hZp : TaoCollatz.tiltZ (pascalP p hp_pos hp_one)
        (TaoCollatz.expW (1 / 1000)) ≤ ENNReal.ofReal (40000 / 39601) := by
    rw [tiltZ_pascalP p hp_pos hp_one hstrip]
    calc
      TaoCollatz.tiltZ (geomP p hp_pos hp_one) (TaoCollatz.expW (1 / 1000)) ^ 2 ≤
          ENNReal.ofReal (200 / 199) ^ 2 :=
        pow_le_pow_left' (tiltZ_geomP_le_window hp0 hp1) 2
      _ = ENNReal.ofReal (40000 / 39601) := by
        rw [← ENNReal.ofReal_pow (by norm_num)]
        norm_num
  have hrem : ENNReal.ofReal (8024 / 125000) ≤
      ENNReal.ofReal (pairThreeProb p) * TaoCollatz.expW (1 / 1000) 3 := by
    rw [TaoCollatz.expW]
    rw [← ENNReal.ofReal_mul (by linarith [hq.1] : 0 ≤ pairThreeProb p)]
    apply ENNReal.ofReal_le_ofReal
    have hexp : 1003 / 1000 ≤ Real.exp ((1 / 1000) * (3 : ℕ)) := by
      have := Real.add_one_le_exp ((1 / 1000) * (3 : ℕ))
      norm_num at this ⊢
      exact this
    have hm := mul_le_mul hq.1 hexp (by norm_num : (0 : ℝ) ≤ 1003 / 1000)
      (by linarith [hq.1] : 0 ≤ pairThreeProb p)
    norm_num at hm ⊢
    exact hm
  let A : ℝ≥0∞ := ENNReal.ofReal (1 - pairThreeProb p) *
    TaoCollatz.tiltZ (pascalNe3P p hp_pos hp_one) (TaoCollatz.expW (1 / 1000))
  have hAB : A + ENNReal.ofReal (8024 / 125000) ≤ ENNReal.ofReal (40000 / 39601) := by
    calc
      A + ENNReal.ofReal (8024 / 125000) ≤
          A + ENNReal.ofReal (pairThreeProb p) * TaoCollatz.expW (1 / 1000) 3 :=
        by simpa [add_comm] using add_le_add_left hrem A
      _ = TaoCollatz.tiltZ (pascalP p hp_pos hp_one)
          (TaoCollatz.expW (1 / 1000)) :=
        tiltZ_pascalNe3P_add p hp_pos hp_one (1 / 1000)
      _ ≤ ENNReal.ofReal (40000 / 39601) := hZp
  have hA : A ≤ ENNReal.ofReal (40000 / 39601 - 8024 / 125000) := by
    have := ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top hAB
    rwa [← ENNReal.ofReal_sub (40000 / 39601) (by norm_num : (0 : ℝ) ≤ 8024 / 125000)] at this
  change ENNReal.ofReal (Real.exp (1 / 1000)) * A ≤ ENNReal.ofReal (19 / 20)
  calc
    ENNReal.ofReal (Real.exp (1 / 1000)) * A ≤
        ENNReal.ofReal (1000 / 999) *
          ENNReal.ofReal (40000 / 39601 - 8024 / 125000) := by
      gcongr
    _ = ENNReal.ofReal ((1000 / 999) *
          (40000 / 39601 - 8024 / 125000)) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1000 / 999)]
    _ ≤ ENNReal.ofReal (19 / 20) := ENNReal.ofReal_le_ofReal (by norm_num)

/-- A positive exponential moment of `holdP` is bounded by one constant chosen
before `p`, uniformly on the campaign window. -/
theorem tiltZ_holdP_le_window {p : ℝ} (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    TaoCollatz.tiltZ (holdP p (by linarith) (by linarith))
        (TaoCollatz.expW2 (1 / 1000) (1 / 1000)) ≤ ENNReal.ofReal 6 := by
  have hp_pos : 0 < p := by linarith
  have hp_one : p ≤ 1 := by linarith
  have hp_lt_one : p < 1 := by linarith
  have hq := pairThreeProb_mem_window hp0 hp1
  have he : Real.exp (1 / 1000) ≤ 1000 / 999 := by
    calc
      Real.exp (1 / 1000) ≤ (1 - 1 / 1000)⁻¹ :=
        TaoCollatz.exp_le_inv_one_sub (by norm_num)
      _ = 1000 / 999 := by norm_num
  have hstrip : (1 - p) * Real.exp (1 / 1000) < 1 := by
    have hm : (1 - p) * Real.exp (1 / 1000) ≤ (4 / 5) * (1000 / 999) :=
      mul_le_mul (by linarith) he (Real.exp_pos _).le (by norm_num)
    norm_num at hm ⊢
    linarith
  have hZt := tiltZ_pascalNe3P_ne_top p hp_pos hp_one hstrip
  rw [tiltZ_holdP_closed p hp_pos hp_lt_one (1 / 1000) (1 / 1000) hZt]
  have hexp4 : Real.exp ((1 / 1000) + 3 * (1 / 1000)) ≤ 250 / 249 := by
    have harg : (1 / 1000 : ℝ) + 3 * (1 / 1000) = 4 / 1000 := by norm_num
    rw [harg]
    calc
      Real.exp (4 / 1000) ≤ (1 - 4 / 1000)⁻¹ :=
        TaoCollatz.exp_le_inv_one_sub (by norm_num)
      _ = 250 / 249 := by norm_num
  have hnum : ENNReal.ofReal
      (pairThreeProb p * Real.exp ((1 / 1000) + 3 * (1 / 1000))) ≤
        ENNReal.ofReal (24 / 83) := by
    apply ENNReal.ofReal_le_ofReal
    have hm := mul_le_mul hq.2 hexp4 (Real.exp_pos _).le
      (by norm_num : (0 : ℝ) ≤ 36 / 125)
    norm_num at hm ⊢
    exact hm
  have hratio : ENNReal.ofReal ((1 - pairThreeProb p) * Real.exp (1 / 1000)) *
        TaoCollatz.tiltZ (pascalNe3P p hp_pos hp_one) (TaoCollatz.expW (1 / 1000)) ≤
      ENNReal.ofReal (19 / 20) := by
    rw [ENNReal.ofReal_mul (by linarith [hq.2] : 0 ≤ 1 - pairThreeProb p)]
    calc
      ENNReal.ofReal (1 - pairThreeProb p) * ENNReal.ofReal (Real.exp (1 / 1000)) *
          TaoCollatz.tiltZ (pascalNe3P p hp_pos hp_one) (TaoCollatz.expW (1 / 1000)) =
        ENNReal.ofReal (Real.exp (1 / 1000)) *
          (ENNReal.ofReal (1 - pairThreeProb p) *
            TaoCollatz.tiltZ (pascalNe3P p hp_pos hp_one)
              (TaoCollatz.expW (1 / 1000))) := by ring
      _ ≤ ENNReal.ofReal (19 / 20) := holdP_mgf_ratio_le_window hp0 hp1
  have hinv :
      (1 - ENNReal.ofReal ((1 - pairThreeProb p) * Real.exp (1 / 1000)) *
          TaoCollatz.tiltZ (pascalNe3P p hp_pos hp_one)
            (TaoCollatz.expW (1 / 1000)))⁻¹ ≤
        (1 - ENNReal.ofReal (19 / 20))⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    exact tsub_le_tsub_left hratio 1
  calc
    ENNReal.ofReal (pairThreeProb p * Real.exp ((1 / 1000) + 3 * (1 / 1000))) *
          (1 - ENNReal.ofReal ((1 - pairThreeProb p) * Real.exp (1 / 1000)) *
            TaoCollatz.tiltZ (pascalNe3P p hp_pos hp_one)
              (TaoCollatz.expW (1 / 1000)))⁻¹ ≤
        ENNReal.ofReal (24 / 83) * (1 - ENNReal.ofReal (19 / 20))⁻¹ :=
      mul_le_mul' hnum hinv
    _ = ENNReal.ofReal (480 / 83) := by
      rw [show (1 : ℝ≥0∞) - ENNReal.ofReal (19 / 20) = ENNReal.ofReal (1 / 20) by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
          ← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 19 / 20)]
        norm_num,
        ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 20),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 24 / 83)]
      norm_num
    _ ≤ ENNReal.ofReal 6 := ENNReal.ofReal_le_ofReal (by norm_num)

/-- Window-uniform exponential tail of the tilted holding law.  Both coordinates
are nonnegative on the support, so `d₁ + d₂` controls its size. -/
theorem holdP_exponential_tail {p : ℝ} (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (R : ℕ) :
    (∑' d : ℕ × ℤ, if R ≤ d.1 + d.2.toNat then
        holdP p (by linarith) (by linarith) d else 0) ≤
      ENNReal.ofReal (6 * Real.exp (-(R : ℝ) / 1000)) := by
  have hp_pos : 0 < p := by linarith
  have hp_lt_one : p < 1 := by linarith
  let P := holdP p hp_pos hp_lt_one
  let a : ℝ := (R : ℝ) / 1000
  have hM : (∑' d : ℕ × ℤ, if R ≤ d.1 + d.2.toNat then P d else 0) ≤
      ENNReal.ofReal (Real.exp (-a)) *
        TaoCollatz.tiltZ P (TaoCollatz.expW2 (1 / 1000) (1 / 1000)) := by
    rw [TaoCollatz.tiltZ, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun d => ?_
    split_ifs with hd
    · by_cases hzero : P d = 0
      · rw [hzero]
        simp
      · have hmem : d ∈ P.support := by
          rw [PMF.mem_support_iff]
          exact hzero
        have hsnd : 3 ≤ d.2 := by
          dsimp [P] at hmem
          exact holdP_support_snd_ge p hp_pos hp_lt_one d hmem
        have hcast : ((d.2.toNat : ℕ) : ℝ) = (d.2 : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ d.2)
        have hlin : a ≤ (1 / 1000 : ℝ) * d.1 + (1 / 1000) * d.2 := by
          dsimp [a]
          rw [← hcast]
          have hdR : (R : ℝ) ≤ (d.1 : ℝ) + (d.2.toNat : ℝ) := by
            exact_mod_cast hd
          nlinarith
        have hw : ENNReal.ofReal (Real.exp a) ≤
            TaoCollatz.expW2 (1 / 1000) (1 / 1000) d := by
          rw [TaoCollatz.expW2]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hlin)
        calc
          P d = ENNReal.ofReal (Real.exp (-a)) *
              (ENNReal.ofReal (Real.exp a) * P d) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
              ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one,
              one_mul]
          _ ≤ ENNReal.ofReal (Real.exp (-a)) *
              (P d * TaoCollatz.expW2 (1 / 1000) (1 / 1000) d) := by
            rw [mul_comm (ENNReal.ofReal (Real.exp a))]
            gcongr
    · exact bot_le
  calc
    (∑' d : ℕ × ℤ, if R ≤ d.1 + d.2.toNat then
        holdP p hp_pos hp_lt_one d else 0) ≤
        ENNReal.ofReal (Real.exp (-a)) *
          TaoCollatz.tiltZ P (TaoCollatz.expW2 (1 / 1000) (1 / 1000)) := hM
    _ ≤ ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal 6 := by
      gcongr
      exact tiltZ_holdP_le_window hp0 hp1
    _ = ENNReal.ofReal (Real.exp (-a) * 6) :=
      (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ = ENNReal.ofReal (6 * Real.exp (-(R : ℝ) / 1000)) := by
      congr 1
      dsimp [a]
      ring

end TaoCollatz.Sec7P
