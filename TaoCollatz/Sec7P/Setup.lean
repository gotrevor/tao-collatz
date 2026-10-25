/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7.Reduction
import TaoCollatz.Sec7P.HoldTail

/-!
# The finer black/white scale for the tilted Pascal campaign

At the lower endpoint `p = 1/5`, the holding-height overshoot is too broad for
the localization box attached to `TaoCollatz.epsBW = 10^-1000`.  The Sec7P
directive therefore permits choosing a smaller epsilon.  This file makes that
choice and supplies the part of Lemma 7.2 that must change with it.

Nothing here changes the phase or pair-factor conventions.  The only new
objects are the finer black/white dichotomy and the corresponding damping
product.  The deterministic triangle argument can consequently be copied at
the larger separation scale without touching the proved p-free library.
-/

namespace TaoCollatz.Sec7P

-- The rational powers below have 100001 decimal digits.  This is still small,
-- but lies beyond the default normalization threshold.
set_option exponentiation.threshold 200000

/-- The Sec7P black/white scale.  Its Lemma-7.4 separation radius is
`(1/10) log(1/epsP) = 10000 log 10 > 20000`.  This leaves room for the
coarse `1/1000`-tilt overshoot radius uniformly at `p = 1/5`. -/
def epsP : ℚ := 1 / 10 ^ 100000

/-- A point is Sec7P-black when its phase is within `epsP` of an integer. -/
def blackP (n ξ : ℕ) (j : ℕ) (l : ℤ) : Prop :=
  |TaoCollatz.θq n ξ j l| ≤ epsP

/-- The complement of the finer Sec7P black set. -/
def whiteP (n ξ : ℕ) (j : ℕ) (l : ℤ) : Prop := ¬ blackP n ξ j l

theorem epsP_pos : (0 : ℚ) < epsP := by
  unfold epsP
  positivity

/-- The finer Sec7P black set is contained in Tao's original black set. -/
theorem blackP_imp_black {n ξ j : ℕ} {l : ℤ} (h : blackP n ξ j l) :
    TaoCollatz.black n ξ j l := by
  unfold blackP at h
  unfold TaoCollatz.black
  refine h.trans ?_
  unfold epsP TaoCollatz.epsBW
  norm_num [div_le_div_iff₀]

/-- The finer epsilon enlarges the Lemma-7.4 separation scale past 20000.
This is the numerical gate that the old `epsBW` localization failed. -/
theorem twenty_thousand_lt_sepP :
    (20000 : ℝ) < (1 / 10 : ℝ) * Real.log (1 / (epsP : ℝ)) := by
  have hε : (epsP : ℝ) = 1 / 10 ^ 100000 := by
    norm_num [epsP]
  have hone : (1 : ℝ) / (epsP : ℝ) = 10 ^ 100000 := by
    rw [hε]
    norm_num
  have hp : (2 : ℝ) ^ 30 < 10 ^ 10 := by norm_num
  have hlog := Real.strictMonoOn_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ 30)
    (by positivity : (0 : ℝ) < (10 : ℝ) ^ 10) hp
  rw [Real.log_pow, Real.log_pow] at hlog
  rw [hone, Real.log_pow]
  push_cast at hlog ⊢
  nlinarith [Real.log_two_gt_d9]

/-- The coarse tilted localization radii fit inside the new separation scale.
`Y = 12000` is sized for the already-proved uniform `1/1000` holding-law
exponential moment; `B = 300` is the transverse half-space threshold, and
`X = 3769` is the least convenient integer satisfying `5Y+B ≤ 16X`.

This is exactly the numerical inequality that fails for the old `epsBW` scale. -/
theorem localization_boxP_numeric :
    (5 : ℝ) * 12000 + 300 ≤ 16 * 3769 ∧
      (3769 : ℝ) ^ 2 + (12000 : ℝ) ^ 2 <
        ((1 / 10 : ℝ) * Real.log (1 / (epsP : ℝ))) ^ 2 := by
  constructor
  · norm_num
  · have hsep := twenty_thousand_lt_sepP
    have hsep0 : (0 : ℝ) < (1 / 10 : ℝ) * Real.log (1 / (epsP : ℝ)) := by
      linarith
    nlinarith [sq_nonneg
      ((1 / 10 : ℝ) * Real.log (1 / (epsP : ℝ)) - 20000)]

/-- The coarse renewal-level calculation at the uniform positive tilt
`1/1000` closes with radius `Y = 12000`.  Once the standard strictly-increasing
height renewal decomposition is instantiated for `holdP`, its bad mass is
bounded by the left-hand side below. -/
theorem height_radiusP_numeric :
    6 * (Real.exp (-(1 / 1000 : ℝ) * 12000) /
      (1 - Real.exp (-(1 / 1000 : ℝ)))) ≤ 1 / 16 := by
  have hc : (0 : ℝ) < 1 / 1000 := by norm_num
  have hdenpos : (0 : ℝ) < 1 - Real.exp (-(1 / 1000 : ℝ)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    norm_num
  have hgeom : 1 / (1 - Real.exp (-(1 / 1000 : ℝ))) ≤ 1001 := by
    have hratio : Real.exp (-(1 / 1000 : ℝ)) /
        (1 - Real.exp (-(1 / 1000 : ℝ))) ≤ 1000 := by
      have he1 : 1 < Real.exp (1 / 1000 : ℝ) := (Real.one_lt_exp_iff).2 hc
      have hbase : (1 / 1000 : ℝ) ≤ Real.exp (1 / 1000 : ℝ) - 1 := by
        linarith [Real.add_one_le_exp (1 / 1000 : ℝ)]
      have heq : Real.exp (-(1 / 1000 : ℝ)) /
          (1 - Real.exp (-(1 / 1000 : ℝ))) =
            1 / (Real.exp (1 / 1000 : ℝ) - 1) := by
        rw [Real.exp_neg]
        field_simp [ne_of_gt (Real.exp_pos (1 / 1000 : ℝ)),
          ne_of_gt (by linarith : 0 < Real.exp (1 / 1000 : ℝ) - 1)]
      rw [heq]
      have := one_div_le_one_div_of_le hc hbase
      norm_num at this ⊢
      exact this
    calc
      1 / (1 - Real.exp (-(1 / 1000 : ℝ))) =
          1 + Real.exp (-(1 / 1000 : ℝ)) /
            (1 - Real.exp (-(1 / 1000 : ℝ))) := by
              field_simp
              ring
      _ ≤ 1001 := by linarith
  have he8 : Real.exp (-1) ≤ 3 / 8 := by
    have he : (8 : ℝ) / 3 ≤ Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      linarith
    have hid : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (-1), he, hid,
      mul_nonneg (Real.exp_pos (-1)).le
        (by linarith : (0 : ℝ) ≤ Real.exp 1 - 8 / 3)]
  have he12 : Real.exp (-(1 / 1000 : ℝ) * 12000) ≤ (3 / 8 : ℝ) ^ 12 := by
    calc
      Real.exp (-(1 / 1000 : ℝ) * 12000) = Real.exp (-1) ^ 12 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ ≤ (3 / 8 : ℝ) ^ 12 :=
        pow_le_pow_left₀ (Real.exp_pos (-1)).le he8 12
  calc
    6 * (Real.exp (-(1 / 1000 : ℝ) * 12000) /
        (1 - Real.exp (-(1 / 1000 : ℝ)))) =
        6 * Real.exp (-(1 / 1000 : ℝ) * 12000) *
          (1 / (1 - Real.exp (-(1 / 1000 : ℝ)))) := by ring
    _ ≤ 6 * (3 / 8 : ℝ) ^ 12 * 1001 := by gcongr
    _ ≤ 1 / 16 := by norm_num

/-- The second-coordinate holding-step tail needed by the renewal overshoot
argument.  It is a direct consequence of the already-proved joint uniform
tail, since supported holding increments have nonnegative coordinates. -/
theorem holdP_snd_tail {p : ℝ} (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) (T : ℕ) :
    (∑' d : ℕ × ℤ, if (T : ℤ) ≤ d.2 then
        holdP p (by linarith) (by linarith) d else 0) ≤
      ENNReal.ofReal (6 * Real.exp (-(T : ℝ) / 1000)) := by
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  refine (ENNReal.tsum_le_tsum (fun d => ?_)).trans
    (holdP_exponential_tail hp0 hp1 T)
  by_cases hT : (T : ℤ) ≤ d.2
  · rw [if_pos hT]
    by_cases hd : holdP p hp0' hp1' d = 0
    · rw [hd]
      exact bot_le
    · have hmem : d ∈ (holdP p hp0' hp1').support := by
        rw [PMF.mem_support_iff]
        exact hd
      have hsnd : 3 ≤ d.2 := holdP_support_snd_ge p hp0' hp1' d hmem
      have hnat : T ≤ d.2.toNat := by
        have hcast : (d.2.toNat : ℤ) = d.2 := Int.toNat_of_nonneg (by omega)
        omega
      rw [if_pos (by omega : T ≤ d.1 + d.2.toNat)]
  · rw [if_neg hT]
    exact bot_le

/-- Lemma 7.2 at the finer Sec7P scale.  The proof is the p-free cosine
argument with `epsP` in place of `epsBW`; no holding-law input is involved. -/
theorem whiteP_cos_bound (n ξ : ℕ) (j : ℕ) (l : ℤ) (hw : whiteP n ξ j l) :
    |TaoCollatz.cosπθ n ξ j l| ≤ Real.exp (-(epsP : ℝ) ^ 3) := by
  set t : ℝ := ((TaoCollatz.θq n ξ j l : ℚ) : ℝ) with ht
  have htq : |TaoCollatz.θq n ξ j l| ≤ 1 / 2 := by
    rw [TaoCollatz.θq, TaoCollatz.sfrac]
    exact abs_sub_round _
  have ht2 : |t| ≤ 1 / 2 := by
    rw [ht, ← Rat.cast_abs]
    calc
      ((|TaoCollatz.θq n ξ j l| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
        Rat.cast_le.mpr htq
      _ = 1 / 2 := by norm_num
  have hεq : epsP < |TaoCollatz.θq n ξ j l| := by
    unfold whiteP blackP at hw
    exact lt_of_not_ge hw
  have hε : ((epsP : ℚ) : ℝ) < |t| := by
    rw [ht, ← Rat.cast_abs]
    exact Rat.cast_lt.mpr hεq
  have hεval : ((epsP : ℚ) : ℝ) = 1 / 10 ^ 100000 := by
    rw [show epsP = 1 / 10 ^ 100000 from rfl]
    push_cast
    norm_num
  have hπ := Real.pi_gt_three
  have habs : |Real.pi * t| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
    nlinarith [abs_nonneg t]
  have hnn : 0 ≤ Real.cos (Real.pi * t) := by
    refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · nlinarith [abs_le.mp ht2]
    · nlinarith [abs_le.mp ht2]
  have hquad : Real.cos (Real.pi * t) ≤ 1 - 2 * t ^ 2 := by
    have hb := Real.cos_le_one_sub_mul_cos_sq habs
    have hπt : 2 / Real.pi ^ 2 * (Real.pi * t) ^ 2 = 2 * t ^ 2 := by
      field_simp
    rw [hπt] at hb
    exact hb
  have hsq : ((epsP : ℚ) : ℝ) ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    have h0 : (0 : ℝ) ≤ ((epsP : ℚ) : ℝ) := by rw [hεval]; norm_num
    nlinarith [hε]
  calc
    |TaoCollatz.cosπθ n ξ j l| = Real.cos (Real.pi * t) := by
      rw [TaoCollatz.cosπθ, ht, abs_of_nonneg hnn]
    _ ≤ 1 - 2 * t ^ 2 := hquad
    _ ≤ 1 + -((epsP : ℚ) : ℝ) ^ 3 := by
      rw [hεval] at hsq ⊢
      nlinarith
    _ ≤ Real.exp (-((epsP : ℚ) : ℝ) ^ 3) := by
      rw [add_comm]
      exact Real.add_one_le_exp _

open Classical in
/-- The (7.5) factor product dominated by encounters with the finer Sec7P
white set.  This is the replacement for `prod_fCond_le_damping` when the
larger tilted localization box is used. -/
theorem prod_fCond_le_dampingP (n ξ : ℕ) (b : Fin (n / 2) → ℕ) :
    ∏ j : Fin (n / 2), ‖TaoCollatz.fCond n ξ
        (TaoCollatz.xArg n (j : ℕ) (TaoCollatz.pre b ((j : ℕ) + 1))) (b j)‖
      ≤ Real.exp (-((epsP : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ whiteP n ξ (j : ℕ)
              ((TaoCollatz.pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)) := by
  have hstep : ∏ j : Fin (n / 2), ‖TaoCollatz.fCond n ξ
        (TaoCollatz.xArg n (j : ℕ) (TaoCollatz.pre b ((j : ℕ) + 1))) (b j)‖
      ≤ ∏ j : Fin (n / 2),
        (if b j = 3 ∧ whiteP n ξ (j : ℕ)
            ((TaoCollatz.pre b ((j : ℕ) + 1) : ℤ))
          then Real.exp (-((epsP : ℝ) ^ 3)) else 1) := by
    refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
    by_cases h : b j = 3 ∧ whiteP n ξ (j : ℕ)
        ((TaoCollatz.pre b ((j : ℕ) + 1) : ℤ))
    · rw [if_pos h, h.1, TaoCollatz.fCond_three_norm]
      exact whiteP_cos_bound n ξ (j : ℕ)
        ((TaoCollatz.pre b ((j : ℕ) + 1) : ℤ)) h.2
    · rw [if_neg h]
      exact TaoCollatz.fCond_norm_le_one n ξ _ _
  refine le_trans hstep (le_of_eq ?_)
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one,
    ← Real.exp_nat_mul]
  congr 1
  ring

end TaoCollatz.Sec7P
