/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.ManyTriangles

/-!
# Tilted Case-2 black-edge assembly

This module combines the `Pascal(p)` endpoint recurrence with the finer-scale
white exit and the window-uniform edge-weight estimate.  It is the analogue of
Tao's (7.46)--(7.51), with every threshold chosen before `p`.
-/

namespace TaoCollatz.Sec7P

open scoped ENNReal

/-- **Case 2 of Proposition 7.8 for `Pascal(p)`.**  At the finer `epsP`
scale, a black-edge start with triangle-top budget `s ≤ m/log²m` contracts by
`m⁻ᴬ` against the preceding arbitrary-set depth supremum, uniformly for
`p ∈ [1/5,3/5]`.

The proof is the subtraction-free (7.47) assembly: the endpoint recurrence
exposes the white damping, `fpDistP_white_exit` supplies fixed positive white
mass, and `fpDistP_edgeWeight_le` spends half of that gain. -/
theorem QP_black_edge_case2 (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ,
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      QP p (by linarith [hp0]) (by linarith [hp1])
          (n / 2) (whiteSetP n ξ) (epsP : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) *
          QPmFor p (by linarith [hp0]) (by linarith [hp1])
            (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) := by
  classical
  have hε0 : (0 : ℝ) ≤ (epsP : ℝ) := by
    exact_mod_cast epsP_pos.le
  have hεpos : (0 : ℝ) < (epsP : ℝ) := by
    exact_mod_cast epsP_pos
  have hc_pos : 0 < 1 - Real.exp (-(epsP : ℝ) ^ 3) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (pow_pos hεpos 3))
  have hc_le : 1 - Real.exp (-(epsP : ℝ) ^ 3) ≤ 1 := by
    linarith [Real.exp_pos (-(epsP : ℝ) ^ 3)]
  obtain ⟨pExit, hpExit, Cw, hWhite⟩ := fpDistP_white_exit
  obtain ⟨Ce, hEdge⟩ := fpDistP_edgeWeight_le A hA
    ((1 - Real.exp (-(epsP : ℝ) ^ 3)) * pExit / 2)
    (div_pos (mul_pos hc_pos hpExit) (by norm_num))
  refine ⟨max (max Cw Ce) 2, ?_⟩
  intro p hp0 hp1 n ξ hξ F m hm hmn l hl t ht htmem s hs hbudget
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  have hmCw : Cw ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmCe : Ce ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
  have hm1 : 1 ≤ m := by omega
  have hwhite := hWhite p hp0 hp1 n ξ hξ F m hmCw hmn l hl t ht htmem s hs hbudget
  have hedge := hEdge p hp0 hp1 m hmCe s hbudget
  have hendpt : ∀ e : ℕ × ℤ,
      QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
          (n / 2 - m + e.1) (l + e.2)
        ≤ (1 - (1 - Real.exp (-(epsP : ℝ) ^ 3))
              * Set.indicator (whiteStripP n ξ) 1
                  (n / 2 - m + e.1, l + e.2))
          * (edgeWeightP p hp0' hp1' A m e *
            QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ)
              (epsP : ℝ) A (m - 1)) := by
    intro e
    simpa only [stripFor, whiteStripP] using
      QP_fp_endpoint_le_for p hp0' hp1' (n / 2) (whiteSetP n ξ)
        (epsP : ℝ) A hA.le hε0 m hm1 hmn l e
  have hstart_enn := QP_le_fpDistP_expect p hp0' hp1' (n / 2)
    (whiteSetP n ξ) (epsP : ℝ) hε0 s (n / 2 - m) l
  let fpLaw := fpDistP p hp0' hp1' s
  have hRne : (∑' e : ℕ × ℤ, fpLaw e *
        ENNReal.ofReal (QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
          (n / 2 - m + e.1) (l + e.2))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.tsum_mul_ofReal_le_one fpLaw _
        (fun e => QP_le_one p hp0' hp1' _ _ _ hε0 _ _))
  have hRtoReal : (∑' e : ℕ × ℤ, fpLaw e *
        ENNReal.ofReal (QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
          (n / 2 - m + e.1) (l + e.2))).toReal
      = ∑' e : ℕ × ℤ, (fpLaw e).toReal *
          QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
            (n / 2 - m + e.1) (l + e.2) :=
    PMF.toReal_tsum_mul_ofReal fpLaw _
      (fun e => QP_nonneg p hp0' hp1' _ _ _ _ _)
  have hstep1 : QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
        (n / 2 - m) l
      ≤ ∑' e : ℕ × ℤ, (fpLaw e).toReal *
          QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
            (n / 2 - m + e.1) (l + e.2) := by
    have h := ENNReal.toReal_mono hRne hstart_enn
    rwa [ENNReal.toReal_ofReal (QP_nonneg p hp0' hp1' _ _ _ _ _), hRtoReal] at h
  set c : ℝ := 1 - Real.exp (-(epsP : ℝ) ^ 3) with hc
  set QM : ℝ := QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ)
    (epsP : ℝ) A (m - 1) with hQMdef
  set mA : ℝ := (m : ℝ) ^ (-A) with hmAdef
  have hQM0 : 0 ≤ QM := QPmFor_nonneg p hp0' hp1' _ _ _ _ _
  have hmA0 : 0 ≤ mA := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmA_le1 : mA ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1) (by linarith)
  have hf_nonneg : ∀ e : ℕ × ℤ, 0 ≤ (fpLaw e).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hf_summable : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal) :=
    ENNReal.summable_toReal (by rw [fpLaw.tsum_coe]; exact ENNReal.one_ne_top)
  have hind0 : ∀ e : ℕ × ℤ,
      0 ≤ Set.indicator (whiteStripP n ξ) (1 : ℕ × ℤ → ℝ)
        (n / 2 - m + e.1, l + e.2) :=
    fun e => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hind1 : ∀ e : ℕ × ℤ,
      Set.indicator (whiteStripP n ξ) (1 : ℕ × ℤ → ℝ)
        (n / 2 - m + e.1, l + e.2) ≤ 1 := by
    intro e
    by_cases h : (n / 2 - m + e.1, l + e.2) ∈ whiteStripP n ξ
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hew_ge : ∀ e : ℕ × ℤ, mA ≤ edgeWeightP p hp0' hp1' A m e :=
    fun e => rpow_neg_le_edgeWeightP p hp0' hp1' hA.le hm1 e
  have hbound : ∀ g : ℕ × ℤ → ℝ, (∀ e, 0 ≤ g e) → (∀ e, g e ≤ 1) →
      Summable (fun e : ℕ × ℤ => (fpLaw e).toReal * g e) := by
    intro g hg0 hg1
    exact Summable.of_nonneg_of_le
      (fun e => mul_nonneg (hf_nonneg e) (hg0 e))
      (fun e => mul_le_of_le_one_right (hf_nonneg e) (hg1 e)) hf_summable
  have hsum_ew : Summable (fun e : ℕ × ℤ =>
      (fpLaw e).toReal * edgeWeightP p hp0' hp1' A m e) :=
    hbound _ (fun e => edgeWeightP_nonneg p hp0' hp1' A m e)
      (fun e => edgeWeightP_le_one p hp0' hp1' hA.le m e)
  have hsum_Qe : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal *
      QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
        (n / 2 - m + e.1) (l + e.2)) :=
    hbound _ (fun e => QP_nonneg p hp0' hp1' _ _ _ _ _)
      (fun e => QP_le_one p hp0' hp1' _ _ _ hε0 _ _)
  have hsum_indew : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal *
      (Set.indicator (whiteStripP n ξ) 1 (n / 2 - m + e.1, l + e.2) *
        edgeWeightP p hp0' hp1' A m e)) :=
    hbound _
      (fun e => mul_nonneg (hind0 e) (edgeWeightP_nonneg p hp0' hp1' A m e))
      (fun e => mul_le_one₀ (hind1 e) (edgeWeightP_nonneg p hp0' hp1' A m e)
        (edgeWeightP_le_one p hp0' hp1' hA.le m e))
  have hsum_indmA : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal *
      (Set.indicator (whiteStripP n ξ) 1 (n / 2 - m + e.1, l + e.2) * mA)) :=
    hbound _ (fun e => mul_nonneg (hind0 e) hmA0)
      (fun e => mul_le_one₀ (hind1 e) hmA0 hmA_le1)
  have hsum_main : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal *
      ((1 - c * Set.indicator (whiteStripP n ξ) 1
          (n / 2 - m + e.1, l + e.2)) * edgeWeightP p hp0' hp1' A m e)) :=
    (hsum_ew.sub (hsum_indew.mul_left c)).congr (fun e => by ring)
  have hindew_ge : pExit * mA ≤ ∑' e : ℕ × ℤ, (fpLaw e).toReal *
      (Set.indicator (whiteStripP n ξ) 1 (n / 2 - m + e.1, l + e.2) *
        edgeWeightP p hp0' hp1' A m e) := by
    have hge : ∀ e : ℕ × ℤ,
        (fpLaw e).toReal *
            (Set.indicator (whiteStripP n ξ) 1
              (n / 2 - m + e.1, l + e.2) * mA)
          ≤ (fpLaw e).toReal *
            (Set.indicator (whiteStripP n ξ) 1
              (n / 2 - m + e.1, l + e.2) *
                edgeWeightP p hp0' hp1' A m e) :=
      fun e => mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hew_ge e) (hind0 e)) (hf_nonneg e)
    calc
      pExit * mA ≤ (∑' e : ℕ × ℤ, (fpLaw e).toReal *
          Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2)) * mA :=
        mul_le_mul_of_nonneg_right hwhite hmA0
      _ = ∑' e : ℕ × ℤ, (fpLaw e).toReal *
          (Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2) * mA) := by
        rw [← tsum_mul_right]
        exact tsum_congr (fun e => by ring)
      _ ≤ _ := hsum_indmA.tsum_le_tsum hge hsum_indew
  have hSmain : ∑' e : ℕ × ℤ, (fpLaw e).toReal *
      ((1 - c * Set.indicator (whiteStripP n ξ) 1
          (n / 2 - m + e.1, l + e.2)) * edgeWeightP p hp0' hp1' A m e) ≤ mA := by
    have hcong : ∀ e : ℕ × ℤ,
        (fpLaw e).toReal *
            ((1 - c * Set.indicator (whiteStripP n ξ) 1
              (n / 2 - m + e.1, l + e.2)) * edgeWeightP p hp0' hp1' A m e)
          = (fpLaw e).toReal * edgeWeightP p hp0' hp1' A m e
            - c * ((fpLaw e).toReal *
              (Set.indicator (whiteStripP n ξ) 1
                (n / 2 - m + e.1, l + e.2) * edgeWeightP p hp0' hp1' A m e)) :=
      fun e => by ring
    rw [tsum_congr hcong,
      Summable.tsum_sub hsum_ew (hsum_indew.mul_left c), tsum_mul_left]
    nlinarith [hedge, mul_le_mul_of_nonneg_left hindew_ge hc_pos.le, hmA0,
      mul_nonneg (mul_nonneg hc_pos.le hpExit.le) hmA0]
  have hpt : ∀ e : ℕ × ℤ,
      (fpLaw e).toReal *
          QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
            (n / 2 - m + e.1) (l + e.2)
        ≤ QM * ((fpLaw e).toReal *
          ((1 - c * Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2)) * edgeWeightP p hp0' hp1' A m e)) := by
    intro e
    calc
      (fpLaw e).toReal * QP p hp0' hp1' (n / 2) (whiteSetP n ξ)
          (epsP : ℝ) (n / 2 - m + e.1) (l + e.2)
        ≤ (fpLaw e).toReal *
            ((1 - c * Set.indicator (whiteStripP n ξ) 1
              (n / 2 - m + e.1, l + e.2)) *
                (edgeWeightP p hp0' hp1' A m e * QM)) :=
          mul_le_mul_of_nonneg_left (by simpa [hc, hQMdef] using hendpt e) (hf_nonneg e)
      _ = QM * ((fpLaw e).toReal *
          ((1 - c * Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2)) * edgeWeightP p hp0' hp1' A m e)) := by ring
  calc
    QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) (n / 2 - m) l
      ≤ ∑' e : ℕ × ℤ, (fpLaw e).toReal *
          QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
            (n / 2 - m + e.1) (l + e.2) := hstep1
    _ ≤ ∑' e : ℕ × ℤ, QM * ((fpLaw e).toReal *
          ((1 - c * Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2)) * edgeWeightP p hp0' hp1' A m e)) :=
      hsum_Qe.tsum_le_tsum hpt (hsum_main.mul_left QM)
    _ = QM * ∑' e : ℕ × ℤ, (fpLaw e).toReal *
          ((1 - c * Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2)) * edgeWeightP p hp0' hp1' A m e) :=
      tsum_mul_left
    _ ≤ QM * mA := mul_le_mul_of_nonneg_left hSmain hQM0
    _ = mA * QM := mul_comm _ _

end TaoCollatz.Sec7P
