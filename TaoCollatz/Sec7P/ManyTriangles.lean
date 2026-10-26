/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.Localization
import TaoCollatz.Sec7.ManyTriangles

/-!
# Finer-scale many-triangle geometry for the tilted holding law

This module starts the `Pascal(p)` port of Tao's Case-2 white-exit argument.  It
connects the explicit first-passage localization box to the `epsP` triangle
family: a supported endpoint captured by the family cannot remain inside both
the height and transverse radii, because the start triangle contributes no
endpoint and every other triangle is farther away than the box diagonal.
-/

namespace TaoCollatz.Sec7P

open scoped ENNReal

/-! ### The post-first-passage tilted walk -/

/-- The tilted counterpart of Tao's `fpDistPlus`: first pass the height budget
with law `fpDistP`, then append `k` independent `holdP` increments.  This is the
law of the endpoint used by Lemma 7.10 after `k` further renewal steps. -/
noncomputable def fpDistPlusP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (s k : ℕ) : PMF (ℕ × ℤ) :=
  (fpDistP p hp0 hp1 s).bind fun e =>
    (holdSumP p hp0 hp1 k).map fun w => e + w

/-- With no appended holding increments, `fpDistPlusP` is just `fpDistP`. -/
theorem fpDistPlusP_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (s : ℕ) :
    fpDistPlusP p hp0 hp1 s 0 = fpDistP p hp0 hp1 s := by
  have h : (fun e : ℕ × ℤ =>
      (holdSumP p hp0 hp1 0).map fun w => e + w) =
      fun e : ℕ × ℤ => PMF.pure e := by
    funext e
    rw [holdSumP_eq_iidSum, TaoCollatz.iidSum_zero, PMF.pure_map, add_zero]
  rw [fpDistPlusP, h, PMF.bind_pure]

/-- The real masses of `fpDistPlusP` sum to one. -/
theorem fpDistPlusP_tsum_toReal (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (s k : ℕ) :
    ∑' e : ℕ × ℤ, (fpDistPlusP p hp0 hp1 s k e).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun e => PMF.apply_ne_top _ _),
    (fpDistPlusP p hp0 hp1 s k).tsum_coe, ENNReal.toReal_one]

/-- Any event under `fpDistPlusP` has real mass at most one. -/
theorem fpDistPlusP_indicator_sum_le_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (s k : ℕ) (S : Set (ℕ × ℤ)) (f : ℕ × ℤ → ℕ × ℤ) :
    ∑' e : ℕ × ℤ, (fpDistPlusP p hp0 hp1 s k e).toReal *
      Set.indicator S 1 (f e) ≤ 1 := by
  have hsum : Summable (fun e : ℕ × ℤ =>
      (fpDistPlusP p hp0 hp1 s k e).toReal) :=
    ENNReal.summable_toReal (by
      rw [(fpDistPlusP p hp0 hp1 s k).tsum_coe]
      exact ENNReal.one_ne_top)
  have hle : ∀ e : ℕ × ℤ,
      (fpDistPlusP p hp0 hp1 s k e).toReal * Set.indicator S 1 (f e)
        ≤ (fpDistPlusP p hp0 hp1 s k e).toReal := by
    intro e
    refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
    by_cases h : f e ∈ S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hsumL : Summable (fun e : ℕ × ℤ =>
      (fpDistPlusP p hp0 hp1 s k e).toReal * Set.indicator S 1 (f e)) :=
    Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) hle hsum
  calc
    ∑' e : ℕ × ℤ, (fpDistPlusP p hp0 hp1 s k e).toReal *
        Set.indicator S 1 (f e)
        ≤ ∑' e : ℕ × ℤ, (fpDistPlusP p hp0 hp1 s k e).toReal :=
          Summable.tsum_le_tsum hle hsumL hsum
    _ = 1 := fpDistPlusP_tsum_toReal p hp0 hp1 s k

/-! ### Uniform tails for the appended tilted holding walk -/

/-- Markov's inequality for a half-space of `holdSumP`, with an arbitrary
finite exponential-moment bound.  Keeping this lemma separate lets all later
Case-3 tails use the same window-uniform moment `tiltZ_holdP_le_window`. -/
theorem holdSumP_halfspace_le_of_mgf {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {l1 l2 M : ℝ}
    (hZle : TaoCollatz.tiltZ (holdP p hp0 hp1)
      (TaoCollatz.expW2 l1 l2) ≤ ENNReal.ofReal M)
    (k : ℕ) (cond : ℕ × ℤ → Prop) [DecidablePred cond] (a : ℝ)
    (hcond : ∀ d : ℕ × ℤ, cond d → a ≤ l1 * d.1 + l2 * d.2) :
    (∑' d : ℕ × ℤ, if cond d then holdSumP p hp0 hp1 k d else 0)
      ≤ ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal M ^ k := by
  rw [holdSumP_eq_iidSum]
  have hZ0 := tiltZ_holdP_ne_zero p hp0 hp1 l1 l2
  have hZt : TaoCollatz.tiltZ (holdP p hp0 hp1)
      (TaoCollatz.expW2 l1 l2) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZle
  have hM :
      (∑' d : ℕ × ℤ,
          if cond d then TaoCollatz.iidSum (holdP p hp0 hp1) k d else 0)
        ≤ ENNReal.ofReal (Real.exp (-a)) *
          TaoCollatz.tiltZ (holdP p hp0 hp1) (TaoCollatz.expW2 l1 l2) ^ k := by
    rw [← TaoCollatz.tiltZ_iidSum (holdP p hp0 hp1)
      (TaoCollatz.expW2_zero l1 l2) (TaoCollatz.expW2_add l1 l2)
      hZ0 hZt k, TaoCollatz.tiltZ, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun d => ?_
    split_ifs with h
    · have hw : ENNReal.ofReal (Real.exp a) ≤ TaoCollatz.expW2 l1 l2 d := by
        rw [TaoCollatz.expW2]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hcond d h))
      calc
        TaoCollatz.iidSum (holdP p hp0 hp1) k d =
            ENNReal.ofReal (Real.exp (-a)) *
              (ENNReal.ofReal (Real.exp a) *
                TaoCollatz.iidSum (holdP p hp0 hp1) k d) := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
                ← Real.exp_add, neg_add_cancel, Real.exp_zero,
                ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (Real.exp (-a)) *
              (TaoCollatz.iidSum (holdP p hp0 hp1) k d *
                TaoCollatz.expW2 l1 l2 d) := by
              rw [mul_comm (ENNReal.ofReal (Real.exp a))]
              gcongr
    · exact bot_le
  refine hM.trans ?_
  gcongr

/-- The second-coordinate tail of `k` tilted holding increments.  The constant
and rate are uniform on `p ∈ [1/5,3/5]`; no centering estimate is needed. -/
theorem holdSumP_snd_tail_window {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) (k : ℕ) (y : ℝ) :
    (∑' d : ℕ × ℤ,
      if y ≤ (d.2 : ℝ) then holdSumP p (by linarith) (by linarith) k d else 0)
      ≤ ENNReal.ofReal ((6 : ℝ) ^ k * Real.exp (-y / 1000)) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  have h := holdSumP_halfspace_le_of_mgf hp0' hp1'
    (tiltZ_holdP_le_box_window (p := p) (l1 := 0) (l2 := 1 / 1000)
      hp0 hp1 (by norm_num) (by norm_num))
    k (fun d => y ≤ (d.2 : ℝ))
    (y / 1000) (fun d hd => by
      have : y / 1000 ≤ (d.2 : ℝ) / 1000 := by linarith
      norm_num
      linarith)
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 6),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  ring

/-- The first-coordinate counterpart of `holdSumP_snd_tail_window`. -/
theorem holdSumP_fst_tail_window {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) (k : ℕ) (y : ℝ) :
    (∑' d : ℕ × ℤ,
      if y ≤ (d.1 : ℝ) then holdSumP p (by linarith) (by linarith) k d else 0)
      ≤ ENNReal.ofReal ((6 : ℝ) ^ k * Real.exp (-y / 1000)) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  have h := holdSumP_halfspace_le_of_mgf hp0' hp1'
    (tiltZ_holdP_le_box_window (p := p) (l1 := 1 / 1000) (l2 := 0)
      hp0 hp1 (by norm_num) (by norm_num))
    k (fun d => y ≤ (d.1 : ℝ))
    (y / 1000) (fun d hd => by
      have : y / 1000 ≤ (d.1 : ℝ) / 1000 := by linarith
      norm_num
      linarith)
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 6),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  ring

/-! ### Uniform first-passage height tail -/

/-- Sum the tilted Lemma-7.7 envelope over both endpoint coordinates.  The
horizontal centre `p s / 2` is harmless because Tao's row-sum engine is
uniform in its real centre; the height factor supplies exponential overshoot
decay exactly as in the fixed-law proof. -/
theorem fpDistP_height_tail_core {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (cL CL K : ℝ) (hcL : 0 < cL) (hCL : 0 < CL) (hK : 0 < K)
    (hbd : ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (fpDistP p (by linarith) (by linarith) s (j, l)).toReal
        ≤ CL * (Real.exp (-cL * ((l : ℝ) - s)) / Real.sqrt (1 + s))
            * TaoCollatz.Gweight (1 + s) (cL * ((j : ℝ) - p / 2 * s)))
    (hrow : ∀ t : ℝ, 1 ≤ t → ∀ μ : ℝ, ∀ N : ℕ,
      ∑ j ∈ Finset.range N, TaoCollatz.Gweight t (cL * ((j : ℝ) - μ))
        ≤ K * Real.sqrt t) :
    ∀ s : ℕ, ∀ y : ℝ, 0 ≤ y →
      ∑' e : ℕ × ℤ,
        (if (s : ℝ) + y ≤ (e.2 : ℝ) then
          fpDistP p (by linarith) (by linarith) s e else 0)
        ≤ ENNReal.ofReal
            (CL * K * (Real.exp (-(cL / 2)) / (1 - Real.exp (-(cL / 2))))
              * Real.exp (-(cL / 2) * y)) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let fpLaw := fpDistP p hp0' hp1'
  have hc2 : (0 : ℝ) < cL / 2 := by positivity
  have he1 : Real.exp (-(cL / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hgd : (0 : ℝ) < 1 - Real.exp (-(cL / 2)) := by
    linarith [Real.exp_pos (-(cL / 2))]
  set geo : ℝ := Real.exp (-(cL / 2)) / (1 - Real.exp (-(cL / 2))) with hgeo
  have hgeo0 : 0 < geo := div_pos (Real.exp_pos _) hgd
  intro s y hy
  have h1s : (0 : ℝ) < 1 + (s : ℝ) := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr h1s
  set A : ℕ → ℝ := fun j =>
    CL * TaoCollatz.Gweight (1 + (s : ℝ))
        (cL * ((j : ℝ) - p / 2 * (s : ℝ))) /
      Real.sqrt (1 + (s : ℝ)) with hA
  set B : ℤ → ℝ := fun l =>
    if (s : ℤ) < l then
      Real.exp (-(cL / 2) * ((l : ℝ) - (s : ℝ))) else 0 with hB
  have hAnn : ∀ j, 0 ≤ A j := fun j =>
    div_nonneg (mul_nonneg hCL.le (TaoCollatz.Gweight_nonneg _ _)) hsq.le
  have hBnn : ∀ l, 0 ≤ B l := by
    intro l
    rw [hB]
    dsimp only
    split_ifs
    exacts [(Real.exp_pos _).le, le_rfl]
  have hpt : ∀ e : ℕ × ℤ,
      (if (s : ℝ) + y ≤ (e.2 : ℝ) then fpLaw s e else 0)
        ≤ ENNReal.ofReal (Real.exp (-(cL / 2) * y)) *
          (ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2)) := by
    intro e
    obtain ⟨j, l⟩ := e
    by_cases hyl : (s : ℝ) + y ≤ (((j, l) : ℕ × ℤ).2 : ℝ)
    · rw [if_pos hyl]
      by_cases hsl : (s : ℤ) < l
      · have hls : y ≤ (l : ℝ) - (s : ℝ) := by linarith
        have hfac : (0 : ℝ) ≤ CL * TaoCollatz.Gweight (1 + (s : ℝ))
            (cL * ((j : ℝ) - p / 2 * (s : ℝ))) /
              Real.sqrt (1 + (s : ℝ)) :=
          div_nonneg (mul_nonneg hCL.le (TaoCollatz.Gweight_nonneg _ _)) hsq.le
        have hsplit : Real.exp (-cL * ((l : ℝ) - (s : ℝ))) ≤
            Real.exp (-(cL / 2) * y) *
              Real.exp (-(cL / 2) * ((l : ℝ) - (s : ℝ))) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith
        have hRe : (fpLaw s (j, l)).toReal ≤
            Real.exp (-(cL / 2) * y) * (A j * B l) := by
          rw [hA, hB]
          dsimp only
          rw [if_pos hsl]
          calc
            (fpLaw s (j, l)).toReal ≤
                CL * (Real.exp (-cL * ((l : ℝ) - (s : ℝ))) /
                    Real.sqrt (1 + (s : ℝ))) *
                  TaoCollatz.Gweight (1 + (s : ℝ))
                    (cL * ((j : ℝ) - p / 2 * (s : ℝ))) := hbd s j l
            _ = Real.exp (-cL * ((l : ℝ) - (s : ℝ))) *
                  (CL * TaoCollatz.Gweight (1 + (s : ℝ))
                    (cL * ((j : ℝ) - p / 2 * (s : ℝ))) /
                      Real.sqrt (1 + (s : ℝ))) := by ring
            _ ≤ (Real.exp (-(cL / 2) * y) *
                    Real.exp (-(cL / 2) * ((l : ℝ) - (s : ℝ)))) *
                  (CL * TaoCollatz.Gweight (1 + (s : ℝ))
                    (cL * ((j : ℝ) - p / 2 * (s : ℝ))) /
                      Real.sqrt (1 + (s : ℝ))) :=
                mul_le_mul_of_nonneg_right hsplit hfac
            _ = Real.exp (-(cL / 2) * y) *
                  (CL * TaoCollatz.Gweight (1 + (s : ℝ))
                    (cL * ((j : ℝ) - p / 2 * (s : ℝ))) /
                      Real.sqrt (1 + (s : ℝ)) *
                    Real.exp (-(cL / 2) * ((l : ℝ) - (s : ℝ)))) := by ring
        calc
          fpLaw s (j, l) = ENNReal.ofReal ((fpLaw s (j, l)).toReal) :=
            (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal (Real.exp (-(cL / 2) * y) * (A j * B l)) :=
            ENNReal.ofReal_le_ofReal hRe
          _ = ENNReal.ofReal (Real.exp (-(cL / 2) * y)) *
                (ENNReal.ofReal (A j) * ENNReal.ofReal (B l)) := by
            rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
              ENNReal.ofReal_mul (hAnn j)]
      · have h0 : fpLaw s (j, l) = 0 := by
          by_contra h
          exact hsl (fpDistP_support_snd_gt p hp0' hp1' s (j, l)
            (by rwa [PMF.mem_support_iff]))
        rw [h0]
        exact zero_le
    · rw [if_neg hyl]
      exact zero_le
  have hfact :
      (∑' e : ℕ × ℤ, ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2)) =
        (∑' j : ℕ, ENNReal.ofReal (A j)) *
          (∑' l : ℤ, ENNReal.ofReal (B l)) := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right]
  have hAle : (∑' j : ℕ, ENNReal.ofReal (A j)) ≤ ENNReal.ofReal (CL * K) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    set M : ℕ := F.sup id + 1 with hM
    have hFsub : F ⊆ Finset.range M := fun j hj =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
    have hreal : ∑ j ∈ Finset.range M, A j ≤ CL * K := by
      have hrw := hrow (1 + (s : ℝ))
        (by linarith [Nat.cast_nonneg (α := ℝ) s])
        (p / 2 * (s : ℝ)) M
      calc
        ∑ j ∈ Finset.range M, A j =
            CL / Real.sqrt (1 + (s : ℝ)) *
              ∑ j ∈ Finset.range M, TaoCollatz.Gweight (1 + (s : ℝ))
                (cL * ((j : ℝ) - p / 2 * (s : ℝ))) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by rw [hA]; ring
        _ ≤ CL / Real.sqrt (1 + (s : ℝ)) *
              (K * Real.sqrt (1 + (s : ℝ))) :=
            mul_le_mul_of_nonneg_left hrw (by positivity)
        _ = CL * K := by field_simp
    calc
      ∑ j ∈ F, ENNReal.ofReal (A j) ≤
          ∑ j ∈ Finset.range M, ENNReal.ofReal (A j) :=
        Finset.sum_le_sum_of_subset hFsub
      _ = ENNReal.ofReal (∑ j ∈ Finset.range M, A j) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => hAnn j).symm
      _ ≤ ENNReal.ofReal (CL * K) := ENNReal.ofReal_le_ofReal hreal
  have hBsum := TaoCollatz.hasSum_int_shift_exp hc2 s
  have hBle : (∑' l : ℤ, ENNReal.ofReal (B l)) = ENNReal.ofReal geo := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hBnn hBsum.summable, hBsum.tsum_eq]
  calc
    ∑' e : ℕ × ℤ, (if (s : ℝ) + y ≤ (e.2 : ℝ) then fpLaw s e else 0)
        ≤ ∑' e : ℕ × ℤ, ENNReal.ofReal (Real.exp (-(cL / 2) * y)) *
            (ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2)) :=
          ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (Real.exp (-(cL / 2) * y)) *
          ((∑' j : ℕ, ENNReal.ofReal (A j)) *
            (∑' l : ℤ, ENNReal.ofReal (B l))) := by
        rw [ENNReal.tsum_mul_left, hfact]
    _ ≤ ENNReal.ofReal (Real.exp (-(cL / 2) * y)) *
          (ENNReal.ofReal (CL * K) * ENNReal.ofReal geo) := by
        exact mul_le_mul_right (mul_le_mul' hAle (le_of_eq hBle)) _
    _ = ENNReal.ofReal (CL * K * geo * Real.exp (-(cL / 2) * y)) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ CL * K),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        ring

/-- Uniform decay rate for the tilted first-passage height overshoot. -/
noncomputable def c_fpHeightP : ℝ := c_fpLocationP / 2

/-- Uniform multiplicative constant for the tilted first-passage height tail. -/
noncomputable def C_fpHeightP : ℝ :=
  C_fpLocationP * TaoCollatz.K_rowG c_fpLocationP *
    (Real.exp (-(c_fpLocationP / 2)) /
      (1 - Real.exp (-(c_fpLocationP / 2))))

theorem c_fpHeightP_pos : 0 < c_fpHeightP := by
  unfold c_fpHeightP
  exact div_pos c_fpLocationP_pos two_pos

theorem C_fpHeightP_pos : 0 < C_fpHeightP := by
  have hc := c_fpLocationP_pos
  have he1 : Real.exp (-(c_fpLocationP / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  unfold C_fpHeightP
  exact mul_pos (mul_pos C_fpLocationP_pos (TaoCollatz.K_rowG_pos hc))
    (div_pos (Real.exp_pos _) (by linarith))

/-- Window-uniform first-passage height tail with explicit shared constants. -/
theorem fpDistP_height_tail_explicitC :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ s : ℕ, ∀ y : ℝ, 0 ≤ y →
      ∑' e : ℕ × ℤ,
        (if (s : ℝ) + y ≤ (e.2 : ℝ) then
          fpDistP p (by linarith) (by linarith) s e else 0)
        ≤ ENNReal.ofReal (C_fpHeightP * Real.exp (-c_fpHeightP * y)) := by
  intro p hp0 hp1
  have h := fpDistP_height_tail_core hp0 hp1
    c_fpLocationP C_fpLocationP (TaoCollatz.K_rowG c_fpLocationP)
    c_fpLocationP_pos C_fpLocationP_pos
    (TaoCollatz.K_rowG_pos c_fpLocationP_pos)
    (fpDistP_location_bound_explicitC p (by linarith) (by linarith) hp0 hp1)
    (TaoCollatz.sum_range_Gweight_le_explicitC c_fpLocationP_pos)
  intro s y hy
  have hs := h s y hy
  unfold C_fpHeightP c_fpHeightP
  exact hs

/-- Existential interface for the tilted first-passage height tail. -/
theorem fpDistP_height_tail :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ s : ℕ, ∀ y : ℝ, 0 ≤ y →
      ∑' e : ℕ × ℤ,
        (if (s : ℝ) + y ≤ (e.2 : ℝ) then
          fpDistP p (by linarith) (by linarith) s e else 0)
        ≤ ENNReal.ofReal (C * Real.exp (-c * y)) :=
  ⟨c_fpHeightP, c_fpHeightP_pos, C_fpHeightP, C_fpHeightP_pos,
    fpDistP_height_tail_explicitC⟩

/-- Phase points beyond the right edge of the half strip. -/
def outStripSetP (n : ℕ) : Set (ℕ × ℤ) := {q : ℕ × ℤ | n / 2 < q.1}

/-- Finer-scale white points in renewal coordinates.  The phase coordinate is
one column behind the renewal coordinate, exactly as in Tao's `whiteSet`. -/
def whiteSetP (n ξ : ℕ) : Set (ℕ × ℤ) :=
  {q : ℕ × ℤ | 1 ≤ q.1 ∧ whiteP n ξ (q.1 - 1) q.2}

/-- Finer-scale white renewal points which have not crossed the right edge of
the half strip. -/
def whiteStripP (n ξ : ℕ) : Set (ℕ × ℤ) :=
  {q : ℕ × ℤ | q.1 ≤ n / 2 ∧ q ∈ whiteSetP n ξ}

/-- Phase points whose predecessor column lies in a finer-scale family triangle. -/
def phaseInFamilyP {n ξ : ℕ} (F : TriangleFamilyP n ξ) : Set (ℕ × ℤ) :=
  {q : ℕ × ℤ | ∃ t ∈ F.T,
    ((q.1 - 1, q.2) : ℕ × ℤ) ∈ triangle t.1 t.2.1 t.2.2}

/-- A first-passage endpoint clears the apex of its starting triangle. -/
theorem endpoint_notMem_start_triangleP {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {s : ℕ} {l lΔ : ℤ} (hs : (s : ℤ) = lΔ - l)
    {e : ℕ × ℤ} (he : e ∈ (fpDistP p hp0 hp1 s).support)
    {j₀ a : ℕ} {sΔ : ℝ} :
    ((a, l + e.2) : ℕ × ℤ) ∉ triangle j₀ lΔ sΔ := by
  intro hmem
  have hgt := fpDistP_support_snd_gt p hp0 hp1 s e he
  have h2 : l + e.2 ≤ lΔ := hmem.2.1
  omega

/-- Deterministic half of the tilted white-exit localization.  If a supported
endpoint is captured by some finer-scale family triangle, it must violate the
height radius `Y` or the fixed transverse radius `300`, provided the resulting
`X × Y` box fits inside the `epsP` separation scale. -/
theorem phaseInFamilyP_support_imp_localization_bad {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) {n ξ X Y : ℕ}
    (F : TriangleFamilyP n ξ) {m : ℕ} (hmn : m ≤ n / 2)
    {l : ℤ} (hl : 1 ≤ n / 2 - m)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ F.T)
    (hmem : (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2)
    {s : ℕ} (hs : (s : ℤ) = t.2.1 - l)
    (hXY : (5 : ℝ) * Y + 300 ≤ 16 * X)
    (hsepXY : (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 <
      ((1 / 10 : ℝ) * Real.log (1 / (epsP : ℝ))) ^ 2)
    {e : ℕ × ℤ}
    (he : e ∈ (fpDistP p (by linarith) (by linarith) s).support)
    (hphase : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ phaseInFamilyP F) :
    (s : ℝ) + Y ≤ (e.2 : ℝ) ∨
      (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ) := by
  by_contra hgood
  push Not at hgood
  obtain ⟨t', ht', hmem'⟩ := hphase
  have hcolEq : n / 2 - m + e.1 - 1 = n / 2 - m - 1 + e.1 := by omega
  have hmemPhase : ((n / 2 - m - 1 + e.1, l + e.2) : ℕ × ℤ) ∈
      triangle t'.1 t'.2.1 t'.2.2 := by
    simpa only [hcolEq] using hmem'
  have hne : t ≠ t' := by
    intro heq
    subst t'
    exact endpoint_notMem_start_triangleP (p := p) (by linarith) (by linarith)
      hs he hmemPhase
  set a : ℕ := e.1 - X with ha
  have ha_le : a ≤ e.1 := by omega
  have he_le : e.1 ≤ a + X := by omega
  have hsR : (s : ℝ) = (t.2.1 : ℝ) - (l : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hs
    push_cast at h
    exact h
  have he2R : (e.2 : ℝ) < (s : ℝ) + Y := hgood.1
  have hfaceRat : (16 : ℝ) * a ≤ 5 * s := by
    by_cases heX : e.1 ≤ X
    · have ha0 : a = 0 := by omega
      rw [ha0]
      norm_num
    · have hacast : (a : ℝ) = (e.1 : ℝ) - X := by
        rw [ha, Nat.cast_sub (by omega : X ≤ e.1)]
      rw [hacast]
      have hXY' : (5 : ℝ) * Y + 300 ≤ 16 * X := hXY
      nlinarith [hgood.2]
  have hlogSlope : 5 * Real.log 9 < 16 * Real.log 2 := by
    have hp : (9 : ℝ) ^ 5 < (2 : ℝ) ^ 16 := by norm_num
    have hl' := Real.log_lt_log (by positivity : (0 : ℝ) < (9 : ℝ) ^ 5) hp
    rw [Real.log_pow, Real.log_pow] at hl'
    norm_num at hl' ⊢
    exact hl'
  have hface : (a : ℝ) * Real.log 9 ≤ (s : ℝ) * Real.log 2 := by
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hlog9 : (0 : ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
    have hslack : (0 : ℝ) ≤ (s : ℝ) * (16 * Real.log 2 - 5 * Real.log 9) :=
      mul_nonneg hs0 (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hfaceRat hlog9
    nlinarith
  have hproj := triangle_top_mem_add hmem hs hface
  have hsep := F.separated t ht t' ht' hne
    ((n / 2 - m - 1 + a, t.2.1) : ℕ × ℤ) hproj
    ((n / 2 - m - 1 + e.1, l + e.2) : ℕ × ℤ) hmemPhase
  have hjlo : -(X : ℝ) ≤
      ((n / 2 - m - 1 + a : ℕ) : ℝ) - (n / 2 - m - 1 + e.1 : ℕ) := by
    have heR : (e.1 : ℝ) ≤ (a : ℝ) + X := by exact_mod_cast he_le
    push_cast
    linarith
  have hjhi :
      ((n / 2 - m - 1 + a : ℕ) : ℝ) - (n / 2 - m - 1 + e.1 : ℕ)
        ≤ X := by
    have haR : (a : ℝ) ≤ (e.1 : ℝ) := by exact_mod_cast ha_le
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) X]
  have hjsq :
      (((n / 2 - m - 1 + a : ℕ) : ℝ) - (n / 2 - m - 1 + e.1 : ℕ)) ^ 2
        ≤ (X : ℝ) ^ 2 := by nlinarith
  have hegt : (s : ℤ) < e.2 :=
    fpDistP_support_snd_gt p (by linarith) (by linarith) s e he
  have hvlo : -(Y : ℝ) ≤ (t.2.1 : ℝ) - ((l + e.2 : ℤ) : ℝ) := by
    push_cast
    linarith
  have hvhi : (t.2.1 : ℝ) - ((l + e.2 : ℤ) : ℝ) ≤ Y := by
    have hlo : (s : ℝ) < (e.2 : ℝ) := by exact_mod_cast hegt
    push_cast
    linarith
  have hvsq : ((t.2.1 : ℝ) - ((l + e.2 : ℤ) : ℝ)) ^ 2 ≤ (Y : ℝ) ^ 2 := by
    nlinarith
  linarith

/-- The deterministic capture implication at the explicit campaign box. -/
theorem phaseInFamilyP_support_imp_localization_bad_explicit {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) {n ξ : ℕ}
    (F : TriangleFamilyP n ξ) {m : ℕ} (hmn : m ≤ n / 2)
    {l : ℤ} (hl : 1 ≤ n / 2 - m)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ F.T)
    (hmem : (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2)
    {s : ℕ} (hs : (s : ℤ) = t.2.1 - l)
    {e : ℕ × ℤ}
    (he : e ∈ (fpDistP p (by linarith) (by linarith) s).support)
    (hphase : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ phaseInFamilyP F) :
    (s : ℝ) + 12000 ≤ (e.2 : ℝ) ∨
      (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ) := by
  exact phaseInFamilyP_support_imp_localization_bad hp0 hp1 F hmn hl ht hmem hs
    localization_boxP_numeric.1 localization_boxP_numeric.2 he hphase

/-- The first-passage mass captured by the finer-scale triangle family is at
most `1/8`, uniformly over the Pascal window.  The start triangle has zero
mass, while capture by a foreign triangle implies the explicit localization
bad event. -/
theorem fpDistP_any_triangle_le :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ∀ F : TriangleFamilyP n ξ, ∀ m : ℕ, m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      ∑' e : ℕ × ℤ,
        (fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e).toReal *
          Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2) ≤ 1 / 8 := by
  classical
  intro p hp0 hp1 n ξ F m hmn l hl t ht hmem s hs
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let fpLaw := fpDistP p hp0' hp1' s
  let bad : ℕ × ℤ → Prop := fun e =>
    (s : ℝ) + 12000 ≤ (e.2 : ℝ) ∨
      (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
  let captured : ℕ × ℤ → Prop := fun e =>
    ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ phaseInFamilyP F
  set P : ℝ≥0∞ := ∑' e : ℕ × ℤ, if captured e then fpLaw e else 0 with hP
  set B : ℝ≥0∞ := ∑' e : ℕ × ℤ, if bad e then fpLaw e else 0 with hB
  have hPB : P ≤ B := by
    rw [hP, hB]
    refine ENNReal.tsum_le_tsum fun e => ?_
    by_cases hc : captured e
    · rw [if_pos hc]
      by_cases hz : fpLaw e = 0
      · rw [hz]
        exact bot_le
      · have he : e ∈ fpLaw.support := by rwa [PMF.mem_support_iff]
        have hb := phaseInFamilyP_support_imp_localization_bad_explicit hp0 hp1 F
          hmn hl ht hmem hs he hc
        rw [if_pos hb]
    · rw [if_neg hc]
      exact bot_le
  have hBle : B ≤ (1 : ℝ≥0∞) / 8 := by
    rw [hB]
    exact fpDistP_localization_le_eighth hp0 hp1 s
  have hPtop : P ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) (hPB.trans hBle)
  have hLHS :
      (∑' e : ℕ × ℤ, (fpLaw e).toReal *
        Set.indicator (phaseInFamilyP F) 1
          (n / 2 - m + e.1, l + e.2)) = P.toReal := by
    rw [hP, ENNReal.tsum_toReal_eq (fun e => by
      split_ifs
      exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top])]
    refine tsum_congr fun e => ?_
    by_cases hc : captured e
    · rw [if_pos hc, Set.indicator_of_mem hc, Pi.one_apply, mul_one]
    · rw [if_neg hc, Set.indicator_of_notMem hc, mul_zero, ENNReal.toReal_zero]
  change (∑' e : ℕ × ℤ, (fpLaw e).toReal *
    Set.indicator (phaseInFamilyP F) 1
      (n / 2 - m + e.1, l + e.2)) ≤ 1 / 8
  rw [hLHS]
  have hto : P.toReal ≤ ((1 : ℝ≥0∞) / 8).toReal :=
    ENNReal.toReal_mono (by finiteness) (hPB.trans hBle)
  norm_num at hto ⊢
  exact hto

/-- The Case-2 first-passage endpoint crosses the right edge with mass at most
`1/8`, uniformly in the Pascal parameter.  This is an immediate consequence of
the stronger fixed-tilt tail `fpDistP_fst_tail_le`, whose event `m < 4e₁`
contains the actual overshoot event `m < e₁`. -/
theorem fpDistP_out_of_strip_le :
    ∃ Cthr : ℕ, ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, ∀ s : ℕ, (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ,
        (fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e).toReal *
          Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2) ≤ 1 / 8 := by
  obtain ⟨C, hC⟩ := fpDistP_fst_tail_le (1 : ℝ) (by norm_num)
    (1 / 8 : ℝ) (by norm_num)
  refine ⟨max C 1, ?_⟩
  intro p hp0 hp1 n m hm hmn l s hs
  let fpLaw := fpDistP p (by linarith [hp0]) (by linarith [hp1]) s
  have htail := hC p hp0 hp1 m (le_trans (le_max_left C 1) hm) s hs
  have hm1 : 1 ≤ m := le_trans (le_max_right C 1) hm
  have hind : ∀ e : ℕ × ℤ,
      Set.indicator (outStripSetP n) 1
          (n / 2 - m + e.1, l + e.2) =
        (if m < e.1 then (1 : ℝ) else 0) := by
    intro e
    have hiff : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ outStripSetP n ↔
        m < e.1 := by
      simp only [outStripSetP, Set.mem_ofPred_eq]
      omega
    by_cases h : m < e.1
    · rw [Set.indicator_of_mem (hiff.mpr h), Pi.one_apply, if_pos h]
    · rw [Set.indicator_of_notMem (fun he => h (hiff.mp he)), if_neg h]
  simp_rw [hind]
  have hmass : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal) :=
    ENNReal.summable_toReal (by rw [fpLaw.tsum_coe]; exact ENNReal.one_ne_top)
  have hsmall : Summable (fun e : ℕ × ℤ =>
      (fpLaw e).toReal * (if m < e.1 then (1 : ℝ) else 0)) := by
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num))
      (fun e => ?_) hmass
    by_cases he : m < e.1 <;> simp [he, ENNReal.toReal_nonneg]
  have hlarge : Summable (fun e : ℕ × ℤ =>
      (fpLaw e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)) := by
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num))
      (fun e => ?_) hmass
    by_cases he : m < 4 * e.1 <;> simp [he, ENNReal.toReal_nonneg]
  have hsub : (∑' e : ℕ × ℤ,
      (fpLaw e).toReal * (if m < e.1 then (1 : ℝ) else 0)) ≤
      ∑' e : ℕ × ℤ,
        (fpLaw e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0) := by
    refine hsmall.tsum_le_tsum (fun e => ?_) hlarge
    by_cases he : m < e.1
    · rw [if_pos he, if_pos (by omega : m < 4 * e.1)]
    · rw [if_neg he]
      by_cases he4 : m < 4 * e.1 <;> simp [he4, ENNReal.toReal_nonneg]
  have hrpow : (m : ℝ) ^ (-(1 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1) (by norm_num)
  change (∑' e : ℕ × ℤ,
      (fpLaw e).toReal * (if m < e.1 then (1 : ℝ) else 0)) ≤ 1 / 8
  calc
    _ ≤ ∑' e : ℕ × ℤ,
        (fpLaw e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0) := hsub
    _ ≤ (1 / 8 : ℝ) * (m : ℝ) ^ (-(1 : ℝ)) := htail
    _ ≤ 1 / 8 := by nlinarith

/-- Tao's Case-2 white-exit estimate at the finer Sec7P scale.  Outside an
exceptional mass `1/8 + 1/8`, an endpoint is in the strip and outside every
finer family triangle; the exact cover then makes its predecessor phase point
`whiteP`.  All constants are chosen before `p`. -/
theorem fpDistP_white_exit :
    ∃ p₀ > (0 : ℝ), ∃ Cthr : ℕ,
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamilyP n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      p₀ ≤ ∑' e : ℕ × ℤ,
        (fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e).toReal *
          Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2) := by
  obtain ⟨Cthr, hOut⟩ := fpDistP_out_of_strip_le
  refine ⟨3 / 4, by norm_num, Cthr, ?_⟩
  intro p hp0 hp1 n ξ hξ F m hm hmn l hl t ht htmem s hs hbudget
  let fpLaw := fpDistP p (by linarith [hp0]) (by linarith [hp1]) s
  have hout := hOut p hp0 hp1 n m hm hmn l s hbudget
  have htri := fpDistP_any_triangle_le p hp0 hp1 n ξ F m hmn l hl t ht htmem s hs
  have hmass : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal) :=
    ENNReal.summable_toReal (by rw [fpLaw.tsum_coe]; exact ENNReal.one_ne_top)
  have hsummand : ∀ (S : Set (ℕ × ℤ)),
      Summable (fun e : ℕ × ℤ => (fpLaw e).toReal *
        Set.indicator S 1 (n / 2 - m + e.1, l + e.2)) := by
    intro S
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (fun e => ?_) hmass
    refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
    by_cases he : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ S
    · simp [Set.indicator_of_mem he]
    · simp [Set.indicator_of_notMem he]
  have hptw : ∀ e : ℕ × ℤ,
      (1 : ℝ) - Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2)
          - Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2)
        ≤ Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2) := by
    intro e
    have hWnn : (0 : ℝ) ≤ Set.indicator (whiteStripP n ξ) 1
        (n / 2 - m + e.1, l + e.2) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hOnn : (0 : ℝ) ≤ Set.indicator (outStripSetP n) 1
        (n / 2 - m + e.1, l + e.2) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hPnn : (0 : ℝ) ≤ Set.indicator (phaseInFamilyP F) 1
        (n / 2 - m + e.1, l + e.2) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hq1 : 1 ≤ n / 2 - m + e.1 := by omega
    by_cases hO : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ outStripSetP n
    · rw [Set.indicator_of_mem hO]
      simp only [Pi.one_apply]
      linarith
    · by_cases hP : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ phaseInFamilyP F
      · rw [Set.indicator_of_mem hP]
        simp only [Pi.one_apply]
        linarith
      · have hle : n / 2 - m + e.1 ≤ n / 2 := by
          simp only [outStripSetP, Set.mem_ofPred_eq, not_lt] at hO
          exact hO
        have hWmem : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈
            whiteStripP n ξ := by
          refine ⟨hle, hq1, ?_⟩
          intro hblack
          apply hP
          have hcov : ((n / 2 - m + e.1 - 1, l + e.2) : ℕ × ℤ) ∈
              {q : ℕ × ℤ | q.1 + 1 ≤ n / 2 ∧ blackP n ξ q.1 q.2} :=
            ⟨by omega, hblack⟩
          rw [F.cover] at hcov
          simp only [Set.mem_iUnion, exists_prop] at hcov
          obtain ⟨t', ht', hmem'⟩ := hcov
          exact ⟨t', ht', hmem'⟩
        rw [Set.indicator_of_mem hWmem, Set.indicator_of_notMem hO,
          Set.indicator_of_notMem hP]
        simp
  have hsumLHS : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal *
      ((1 : ℝ) - Set.indicator (outStripSetP n) 1
          (n / 2 - m + e.1, l + e.2)
        - Set.indicator (phaseInFamilyP F) 1
          (n / 2 - m + e.1, l + e.2))) :=
    ((hmass.sub (hsummand (outStripSetP n))).sub (hsummand (phaseInFamilyP F))).congr
      (fun e => by ring)
  have hexpand : (∑' e : ℕ × ℤ, (fpLaw e).toReal *
      ((1 : ℝ) - Set.indicator (outStripSetP n) 1
          (n / 2 - m + e.1, l + e.2)
        - Set.indicator (phaseInFamilyP F) 1
          (n / 2 - m + e.1, l + e.2))) =
      1 - (∑' e : ℕ × ℤ, (fpLaw e).toReal *
        Set.indicator (outStripSetP n) 1
          (n / 2 - m + e.1, l + e.2))
        - (∑' e : ℕ × ℤ, (fpLaw e).toReal *
          Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2)) := by
    have h1 : ∀ e : ℕ × ℤ, (fpLaw e).toReal *
        ((1 : ℝ) - Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2)
          - Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2)) =
        (fpLaw e).toReal
          - (fpLaw e).toReal * Set.indicator (outStripSetP n) 1
              (n / 2 - m + e.1, l + e.2)
          - (fpLaw e).toReal * Set.indicator (phaseInFamilyP F) 1
              (n / 2 - m + e.1, l + e.2) := by
      intro e
      ring
    simp_rw [h1]
    rw [Summable.tsum_sub (hmass.sub (hsummand (outStripSetP n)))
        (hsummand (phaseInFamilyP F)),
      Summable.tsum_sub hmass (hsummand (outStripSetP n)),
      ← ENNReal.tsum_toReal_eq (fun e => PMF.apply_ne_top fpLaw e),
      fpLaw.tsum_coe, ENNReal.toReal_one]
  change (3 : ℝ) / 4 ≤ ∑' e : ℕ × ℤ, (fpLaw e).toReal *
    Set.indicator (whiteStripP n ξ) 1
      (n / 2 - m + e.1, l + e.2)
  calc
    (3 : ℝ) / 4 = 1 - 1 / 8 - 1 / 8 := by norm_num
    _ ≤ 1 - (∑' e : ℕ × ℤ, (fpLaw e).toReal *
          Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2))
        - (∑' e : ℕ × ℤ, (fpLaw e).toReal *
          Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2)) := by linarith
    _ = ∑' e : ℕ × ℤ, (fpLaw e).toReal *
        ((1 : ℝ) - Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2)
          - Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2)) := hexpand.symm
    _ ≤ ∑' e : ℕ × ℤ, (fpLaw e).toReal *
        Set.indicator (whiteStripP n ξ) 1
          (n / 2 - m + e.1, l + e.2) :=
      Summable.tsum_le_tsum
        (fun e => mul_le_mul_of_nonneg_left (hptw e) ENNReal.toReal_nonneg)
        hsumLHS (hsummand (whiteStripP n ξ))

end TaoCollatz.Sec7P
