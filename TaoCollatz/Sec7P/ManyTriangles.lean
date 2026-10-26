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

/-- A reusable union bound for events under the post-first-passage convolution.
If an event at `f + w` forces an event of the first-passage endpoint `f` or of
the appended holding walk `w`, its mass is bounded by the two marginal event
masses.  This is the common probabilistic glue in both parts of Tao's (7.61). -/
theorem fpDistPlusP_event_le_add (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (s k : ℕ) (E Ef Ew : ℕ × ℤ → Prop)
    [DecidablePred E] [DecidablePred Ef] [DecidablePred Ew]
    (hsplit : ∀ f w : ℕ × ℤ, E (f + w) → Ef f ∨ Ew w) :
    (∑' e : ℕ × ℤ, if E e then fpDistPlusP p hp0 hp1 s k e else 0) ≤
      (∑' f : ℕ × ℤ, if Ef f then fpDistP p hp0 hp1 s f else 0) +
        ∑' w : ℕ × ℤ, if Ew w then holdSumP p hp0 hp1 k w else 0 := by
  classical
  have hexp :
      (∑' e : ℕ × ℤ, if E e then fpDistPlusP p hp0 hp1 s k e else 0) =
        ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
          if E (f + w) then
            fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0 := by
    have h1 : ∀ e : ℕ × ℤ,
        (if E e then fpDistPlusP p hp0 hp1 s k e else 0) =
          ∑' (f : ℕ × ℤ) (w : ℕ × ℤ), if e = f + w then
            (if E e then
              fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0)
            else 0 := by
      intro e
      by_cases he : E e
      · rw [if_pos he, fpDistPlusP, PMF.bind_apply]
        refine tsum_congr fun f => ?_
        rw [PMF.map_apply, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun w => ?_
        by_cases hew : e = f + w
        · rw [if_pos hew, if_pos hew, if_pos he]
        · rw [if_neg hew, if_neg hew, mul_zero]
      · rw [if_neg he]
        have hz : ∀ f w : ℕ × ℤ, (if e = f + w then
            (if E e then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0)
          else 0) = 0 := by
          intro f w
          rw [if_neg he]
          exact ite_self 0
        symm
        simp only [hz, tsum_zero]
    calc
      (∑' e : ℕ × ℤ, if E e then fpDistPlusP p hp0 hp1 s k e else 0) =
          ∑' (e : ℕ × ℤ) (f : ℕ × ℤ) (w : ℕ × ℤ), if e = f + w then
            (if E e then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0)
          else 0 := tsum_congr h1
      _ = ∑' (f : ℕ × ℤ) (e : ℕ × ℤ) (w : ℕ × ℤ), if e = f + w then
            (if E e then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0)
          else 0 := ENNReal.tsum_comm
      _ = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ) (e : ℕ × ℤ), if e = f + w then
            (if E e then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0)
          else 0 := tsum_congr fun f => ENNReal.tsum_comm
      _ = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ), if E (f + w) then
            fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0 := by
          refine tsum_congr fun f => tsum_congr fun w => ?_
          rw [tsum_eq_single (f + w) (fun e he => if_neg he), if_pos rfl]
  have hpt : ∀ f w : ℕ × ℤ,
      (if E (f + w) then
          fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0) ≤
        (if Ef f then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0) +
          (if Ew w then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0) := by
    intro f w
    by_cases he : E (f + w)
    · rw [if_pos he]
      rcases hsplit f w he with hf | hw
      · rw [if_pos hf]
        exact le_self_add
      · rw [if_pos hw]
        exact le_add_self
    · rw [if_neg he]
      exact zero_le
  have hfirst : ∀ f : ℕ × ℤ,
      (∑' w : ℕ × ℤ,
        if Ef f then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0) =
          if Ef f then fpDistP p hp0 hp1 s f else 0 := by
    intro f
    by_cases hf : Ef f
    · simp only [if_pos hf]
      rw [ENNReal.tsum_mul_left, (holdSumP p hp0 hp1 k).tsum_coe, mul_one]
    · simp only [if_neg hf, tsum_zero]
  have hsecond :
      (∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
        if Ew w then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0) =
          ∑' w : ℕ × ℤ, if Ew w then holdSumP p hp0 hp1 k w else 0 := by
    have h1 : ∀ f w : ℕ × ℤ,
        (if Ew w then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0) =
          fpDistP p hp0 hp1 s f *
            (if Ew w then holdSumP p hp0 hp1 k w else 0) := by
      intro f w
      rw [mul_ite, mul_zero]
    calc
      (∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
          if Ew w then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0) =
          ∑' f : ℕ × ℤ, fpDistP p hp0 hp1 s f *
            ∑' w : ℕ × ℤ, if Ew w then holdSumP p hp0 hp1 k w else 0 := by
              refine tsum_congr fun f => ?_
              simp only [h1]
              exact ENNReal.tsum_mul_left
      _ = (∑' f : ℕ × ℤ, fpDistP p hp0 hp1 s f) *
            ∑' w : ℕ × ℤ, if Ew w then holdSumP p hp0 hp1 k w else 0 :=
          ENNReal.tsum_mul_right
      _ = ∑' w : ℕ × ℤ, if Ew w then holdSumP p hp0 hp1 k w else 0 := by
          rw [(fpDistP p hp0 hp1 s).tsum_coe, one_mul]
  rw [hexp]
  calc
    (∑' (f : ℕ × ℤ) (w : ℕ × ℤ), if E (f + w) then
        fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0) ≤
        ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
          ((if Ef f then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0) +
            (if Ew w then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0)) :=
      ENNReal.tsum_le_tsum fun f => ENNReal.tsum_le_tsum (hpt f)
    _ = (∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
          if Ef f then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0) +
        ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
          if Ew w then fpDistP p hp0 hp1 s f * holdSumP p hp0 hp1 k w else 0 := by
        rw [← ENNReal.tsum_add]
        exact tsum_congr fun f => ENNReal.tsum_add
    _ = (∑' f : ℕ × ℤ, if Ef f then fpDistP p hp0 hp1 s f else 0) +
        ∑' w : ℕ × ℤ, if Ew w then holdSumP p hp0 hp1 k w else 0 := by
      rw [hsecond, tsum_congr hfirst]

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

/-! ### Uniform first-passage column tail -/

/-- Column deviation for the tilted first-passage endpoint.  The proof is the
same row-summation argument as the fixed-law engine, but its centre is the
moving value `p s / 2`; the Gaussian row estimate is uniform in that centre. -/
theorem fpDistP_col_dev_core {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (cL CL K : ℝ) (hcL : 0 < cL) (hCL : 0 < CL) (hK : 0 < K)
    (hbd : ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (fpDistP p (by linarith) (by linarith) s (j, l)).toReal
        ≤ CL * (Real.exp (-cL * ((l : ℝ) - s)) / Real.sqrt (1 + s))
            * TaoCollatz.Gweight (1 + s)
              (cL * ((j : ℝ) - p / 2 * s)))
    (hrow : ∀ t : ℝ, 1 ≤ t → ∀ μ : ℝ, ∀ N : ℕ,
      ∑ j ∈ Finset.range N,
          TaoCollatz.Gweight t (cL / 2 * ((j : ℝ) - μ))
        ≤ K * Real.sqrt t) :
    ∀ s : ℕ, ∀ D : ℝ, 0 ≤ D →
      ∑' e : ℕ × ℤ,
        (if D ≤ |(e.1 : ℝ) - p / 2 * (s : ℝ)| then
          fpDistP p (by linarith) (by linarith) s e else 0)
        ≤ ENNReal.ofReal
            (CL * K * (Real.exp (-cL) / (1 - Real.exp (-cL)))
              * (Real.exp (-min (cL ^ 2 / 2) (cL / 2) * D ^ 2 /
                    (1 + (s : ℝ)))
                + Real.exp (-min (cL ^ 2 / 2) (cL / 2) * D))) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let fpLaw := fpDistP p hp0' hp1'
  have he1 : Real.exp (-cL) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hgd : (0 : ℝ) < 1 - Real.exp (-cL) := by
    linarith [Real.exp_pos (-cL)]
  set geo : ℝ := Real.exp (-cL) / (1 - Real.exp (-cL)) with hgeo
  have hgeo0 : 0 < geo := div_pos (Real.exp_pos _) hgd
  set cc : ℝ := min (cL ^ 2 / 2) (cL / 2) with hcc
  have hcc0 : 0 < cc := lt_min (by positivity) (by positivity)
  intro s D hD
  have h1s : (0 : ℝ) < 1 + (s : ℝ) := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (1 + (s : ℝ)) :=
    Real.sqrt_pos.mpr h1s
  set t : ℝ := 1 + (s : ℝ) with ht
  set pref : ℝ :=
    Real.exp (-(cL * D) ^ 2 / (2 * t)) + Real.exp (-(cL * D) / 2)
    with hpref
  have hpref0 : 0 < pref := by positivity
  set A : ℕ → ℝ := fun j =>
    CL * TaoCollatz.Gweight t
      (cL / 2 * ((j : ℝ) - p / 2 * (s : ℝ))) / Real.sqrt t with hA
  set B : ℤ → ℝ := fun l =>
    if (s : ℤ) < l then
      Real.exp (-cL * ((l : ℝ) - (s : ℝ))) else 0 with hB
  have hAnn : ∀ j, 0 ≤ A j := fun j =>
    div_nonneg (mul_nonneg hCL.le (TaoCollatz.Gweight_nonneg _ _)) hsq.le
  have hBnn : ∀ l, 0 ≤ B l := by
    intro l
    rw [hB]
    dsimp only
    split_ifs
    exacts [(Real.exp_pos _).le, le_rfl]
  have hGw : ∀ x : ℝ, cL * D ≤ |x| →
      TaoCollatz.Gweight t x ≤ pref * TaoCollatz.Gweight t (x / 2) := by
    intro x hx
    have ht0 : (0 : ℝ) < t := h1s
    have hx2 : (cL * D) ^ 2 ≤ x ^ 2 := by
      have h0 : 0 ≤ cL * D := by positivity
      nlinarith [abs_nonneg x, sq_abs x]
    have hg1 : Real.exp (-x ^ 2 / t)
        ≤ Real.exp (-(cL * D) ^ 2 / (2 * t)) *
            Real.exp (-(x / 2) ^ 2 / t) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [div_add_div _ _ (by positivity : (2 : ℝ) * t ≠ 0)
        (by positivity : t ≠ 0)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (mul_pos ht0 ht0).le,
        sq_nonneg x, mul_pos ht0 ht0]
    have hg2 : Real.exp (-|x|)
        ≤ Real.exp (-(cL * D) / 2) * Real.exp (-|x / 2|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [abs_div]
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]
      linarith
    have hGnn1 : (0 : ℝ) ≤ Real.exp (-(x / 2) ^ 2 / t) :=
      (Real.exp_pos _).le
    have hGnn2 : (0 : ℝ) ≤ Real.exp (-|x / 2|) :=
      (Real.exp_pos _).le
    have hp1 : Real.exp (-(cL * D) ^ 2 / (2 * t)) ≤ pref := by
      rw [hpref]
      linarith [Real.exp_pos (-(cL * D) / 2)]
    have hp2 : Real.exp (-(cL * D) / 2) ≤ pref := by
      rw [hpref]
      linarith [Real.exp_pos (-(cL * D) ^ 2 / (2 * t))]
    unfold TaoCollatz.Gweight
    calc
      Real.exp (-x ^ 2 / t) + Real.exp (-|x|)
          ≤ Real.exp (-(cL * D) ^ 2 / (2 * t)) *
              Real.exp (-(x / 2) ^ 2 / t)
            + Real.exp (-(cL * D) / 2) * Real.exp (-|x / 2|) :=
              add_le_add hg1 hg2
      _ ≤ pref * Real.exp (-(x / 2) ^ 2 / t) +
            pref * Real.exp (-|x / 2|) :=
          add_le_add (mul_le_mul_of_nonneg_right hp1 hGnn1)
            (mul_le_mul_of_nonneg_right hp2 hGnn2)
      _ = pref * (Real.exp (-(x / 2) ^ 2 / t) +
            Real.exp (-|x / 2|)) := by ring
  have hpt : ∀ e : ℕ × ℤ,
      (if D ≤ |(e.1 : ℝ) - p / 2 * (s : ℝ)| then fpLaw s e else 0)
        ≤ ENNReal.ofReal pref *
          (ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2)) := by
    intro e
    obtain ⟨j, l⟩ := e
    by_cases hDj : D ≤ |(j : ℝ) - p / 2 * (s : ℝ)|
    · rw [if_pos hDj]
      by_cases hsl : (s : ℤ) < l
      · have hxD : cL * D ≤
            |cL * ((j : ℝ) - p / 2 * (s : ℝ))| := by
          rw [abs_mul, abs_of_pos hcL]
          exact mul_le_mul_of_nonneg_left hDj hcL.le
        have hGle := hGw (cL * ((j : ℝ) - p / 2 * (s : ℝ))) hxD
        have hhalf : cL * ((j : ℝ) - p / 2 * (s : ℝ)) / 2 =
            cL / 2 * ((j : ℝ) - p / 2 * (s : ℝ)) := by ring
        rw [hhalf] at hGle
        have hfac : (0 : ℝ) ≤
            CL * (Real.exp (-cL * ((l : ℝ) - (s : ℝ))) /
              Real.sqrt t) :=
          mul_nonneg hCL.le (div_nonneg (Real.exp_pos _).le hsq.le)
        have hRe : (fpLaw s (j, l)).toReal ≤ pref * (A j * B l) := by
          rw [hA, hB]
          dsimp only
          rw [if_pos hsl]
          calc
            (fpLaw s (j, l)).toReal ≤
                CL * (Real.exp (-cL * ((l : ℝ) - (s : ℝ))) /
                    Real.sqrt t) *
                  TaoCollatz.Gweight t
                    (cL * ((j : ℝ) - p / 2 * (s : ℝ))) := hbd s j l
            _ ≤ CL * (Real.exp (-cL * ((l : ℝ) - (s : ℝ))) /
                    Real.sqrt t) *
                  (pref * TaoCollatz.Gweight t
                    (cL / 2 * ((j : ℝ) - p / 2 * (s : ℝ)))) :=
                mul_le_mul_of_nonneg_left hGle hfac
            _ = pref * (CL * TaoCollatz.Gweight t
                    (cL / 2 * ((j : ℝ) - p / 2 * (s : ℝ))) /
                  Real.sqrt t *
                    Real.exp (-cL * ((l : ℝ) - (s : ℝ)))) := by ring
        calc
          fpLaw s (j, l) = ENNReal.ofReal ((fpLaw s (j, l)).toReal) :=
            (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal (pref * (A j * B l)) :=
            ENNReal.ofReal_le_ofReal hRe
          _ = ENNReal.ofReal pref *
                (ENNReal.ofReal (A j) * ENNReal.ofReal (B l)) := by
            rw [ENNReal.ofReal_mul hpref0.le,
              ENNReal.ofReal_mul (hAnn j)]
      · have h0 : fpLaw s (j, l) = 0 := by
          by_contra h
          exact hsl (fpDistP_support_snd_gt p hp0' hp1' s (j, l)
            (by rwa [PMF.mem_support_iff]))
        rw [h0]
        exact zero_le
    · rw [if_neg hDj]
      exact zero_le
  have hfact :
      (∑' e : ℕ × ℤ, ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2)) =
        (∑' j : ℕ, ENNReal.ofReal (A j)) *
          (∑' l : ℤ, ENNReal.ofReal (B l)) := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right]
  have hAle : (∑' j : ℕ, ENNReal.ofReal (A j)) ≤
      ENNReal.ofReal (CL * K) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    set M : ℕ := F.sup id + 1 with hM
    have hFsub : F ⊆ Finset.range M := fun j hj =>
      Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
    have hreal : ∑ j ∈ Finset.range M, A j ≤ CL * K := by
      have hrw := hrow t
        (by rw [ht]; linarith [Nat.cast_nonneg (α := ℝ) s])
        (p / 2 * (s : ℝ)) M
      calc
        ∑ j ∈ Finset.range M, A j =
            CL / Real.sqrt t *
              ∑ j ∈ Finset.range M, TaoCollatz.Gweight t
                (cL / 2 * ((j : ℝ) - p / 2 * (s : ℝ))) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by rw [hA]; ring
        _ ≤ CL / Real.sqrt t * (K * Real.sqrt t) :=
          mul_le_mul_of_nonneg_left hrw (by positivity)
        _ = CL * K := by field_simp
    calc
      ∑ j ∈ F, ENNReal.ofReal (A j) ≤
          ∑ j ∈ Finset.range M, ENNReal.ofReal (A j) :=
        Finset.sum_le_sum_of_subset hFsub
      _ = ENNReal.ofReal (∑ j ∈ Finset.range M, A j) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => hAnn j).symm
      _ ≤ ENNReal.ofReal (CL * K) := ENNReal.ofReal_le_ofReal hreal
  have hBsum := TaoCollatz.hasSum_int_shift_exp hcL s
  have hBle : (∑' l : ℤ, ENNReal.ofReal (B l)) = ENNReal.ofReal geo := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hBnn hBsum.summable,
      hBsum.tsum_eq]
  have hprefle : pref ≤
      Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) +
        Real.exp (-cc * D) := by
    have h1 : Real.exp (-(cL * D) ^ 2 / (2 * t)) ≤
        Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [ht, div_le_div_iff₀ (by positivity) (by positivity)]
      have hcc1 : cc ≤ cL ^ 2 / 2 := min_le_left _ _
      nlinarith [sq_nonneg D, sq_nonneg (cL * D),
        Nat.cast_nonneg (α := ℝ) s,
        mul_le_mul_of_nonneg_right hcc1 (sq_nonneg D)]
    have h2 : Real.exp (-(cL * D) / 2) ≤ Real.exp (-cc * D) := by
      apply Real.exp_le_exp.mpr
      have hcc2 : cc ≤ cL / 2 := min_le_right _ _
      nlinarith [mul_le_mul_of_nonneg_right hcc2 hD]
    rw [hpref]
    exact add_le_add h1 h2
  calc
    ∑' e : ℕ × ℤ,
        (if D ≤ |(e.1 : ℝ) - p / 2 * (s : ℝ)| then fpLaw s e else 0)
        ≤ ∑' e : ℕ × ℤ, ENNReal.ofReal pref *
            (ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2)) :=
          ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal pref *
          ((∑' j : ℕ, ENNReal.ofReal (A j)) *
            (∑' l : ℤ, ENNReal.ofReal (B l))) := by
        rw [ENNReal.tsum_mul_left, hfact]
    _ ≤ ENNReal.ofReal pref *
          (ENNReal.ofReal (CL * K) * ENNReal.ofReal geo) := by
        exact mul_le_mul_right (mul_le_mul' hAle (le_of_eq hBle)) _
    _ = ENNReal.ofReal (CL * K * geo * pref) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ CL * K),
          ← ENNReal.ofReal_mul hpref0.le]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (CL * K * geo *
          (Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) +
            Real.exp (-cc * D))) := by
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hprefle (by positivity))

/-- Uniform decay rate for the tilted first-passage column deviation. -/
noncomputable def c_fpColDevP : ℝ :=
  min (c_fpLocationP ^ 2 / 2) (c_fpLocationP / 2)

/-- Uniform multiplicative constant for the tilted first-passage column tail. -/
noncomputable def C_fpColDevP : ℝ :=
  C_fpLocationP * TaoCollatz.K_rowG (c_fpLocationP / 2) *
    (Real.exp (-c_fpLocationP) / (1 - Real.exp (-c_fpLocationP)))

theorem c_fpColDevP_pos : 0 < c_fpColDevP := by
  have hc := c_fpLocationP_pos
  unfold c_fpColDevP
  exact lt_min (by positivity) (by positivity)

theorem C_fpColDevP_pos : 0 < C_fpColDevP := by
  have hc := c_fpLocationP_pos
  have he1 : Real.exp (-c_fpLocationP) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hK := TaoCollatz.K_rowG_pos
    (c := c_fpLocationP / 2) (by positivity)
  unfold C_fpColDevP
  exact mul_pos (mul_pos C_fpLocationP_pos hK)
    (div_pos (Real.exp_pos _) (by linarith))

/-- Window-uniform first-passage column deviation with explicit constants. -/
theorem fpDistP_col_dev_explicitC :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ s : ℕ, ∀ D : ℝ, 0 ≤ D →
      ∑' e : ℕ × ℤ,
        (if D ≤ |(e.1 : ℝ) - p / 2 * (s : ℝ)| then
          fpDistP p (by linarith) (by linarith) s e else 0)
        ≤ ENNReal.ofReal
            (C_fpColDevP *
              (Real.exp (-c_fpColDevP * D ^ 2 / (1 + (s : ℝ))) +
                Real.exp (-c_fpColDevP * D))) := by
  intro p hp0 hp1
  have h := fpDistP_col_dev_core hp0 hp1 c_fpLocationP C_fpLocationP
    (TaoCollatz.K_rowG (c_fpLocationP / 2))
    c_fpLocationP_pos C_fpLocationP_pos
    (TaoCollatz.K_rowG_pos (div_pos c_fpLocationP_pos two_pos))
    (fpDistP_location_bound_explicitC p (by linarith) (by linarith) hp0 hp1)
    (TaoCollatz.sum_range_Gweight_le_explicitC
      (div_pos c_fpLocationP_pos two_pos))
  intro s D hD
  have hs := h s D hD
  unfold C_fpColDevP c_fpColDevP
  exact hs

/-- Existential interface for the tilted first-passage column deviation. -/
theorem fpDistP_col_dev :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ s : ℕ, ∀ D : ℝ, 0 ≤ D →
      ∑' e : ℕ × ℤ,
        (if D ≤ |(e.1 : ℝ) - p / 2 * (s : ℝ)| then
          fpDistP p (by linarith) (by linarith) s e else 0)
        ≤ ENNReal.ofReal
            (C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) +
              Real.exp (-c * D))) :=
  ⟨c_fpColDevP, c_fpColDevP_pos, C_fpColDevP, C_fpColDevP_pos,
    fpDistP_col_dev_explicitC⟩

/-! ### Uniform tails after appended tilted holding steps -/

/-- The coarse estimate `6^k ≤ exp(2k)` used to absorb the uniform holding-law
moment bound.  Its deliberately generous exponent keeps the downstream (7.61)
threshold linear and independent of `p`. -/
theorem six_pow_le_exp_two_mul (k : ℕ) :
    (6 : ℝ) ^ k ≤ Real.exp (2 * (k : ℝ)) := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h6 : (6 : ℝ) ≤ Real.exp 2 := by
    rw [he2]
    nlinarith
  calc
    (6 : ℝ) ^ k ≤ (Real.exp 2) ^ k :=
      pow_le_pow_left₀ (by norm_num) h6 k
    _ = Real.exp ((k : ℝ) * 2) := (Real.exp_nat_mul 2 k).symm
    _ = Real.exp (2 * (k : ℝ)) := by ring_nf

/-- Uniform decay rate for the tilted post-passage height tail. -/
noncomputable def c_fpHeightTailP : ℝ := min (c_fpHeightP / 2) (1 / 5000)

/-- Uniform multiplicative constant for the tilted post-passage height tail. -/
noncomputable def C_fpHeightTailP : ℝ := C_fpHeightP + 1

theorem c_fpHeightTailP_pos : 0 < c_fpHeightTailP := by
  unfold c_fpHeightTailP
  exact lt_min (div_pos c_fpHeightP_pos two_pos) (by norm_num)

theorem C_fpHeightTailP_pos : 0 < C_fpHeightTailP := by
  unfold C_fpHeightTailP
  linarith [C_fpHeightP_pos]

/-- The height part of Tao's (7.61), uniformly for the tilted law.  The
first-passage overshoot and appended holding walk are split at `H/2`; the
margin `10000(1+k) ≤ H` absorbs the latter's uniform `6^k` moment factor. -/
theorem fpDistPlusP_height_tail_explicitC :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ s k : ℕ, ∀ H : ℝ, 10000 * (1 + (k : ℝ)) ≤ H →
      ∑' e : ℕ × ℤ, (fpDistPlusP p (by linarith) (by linarith) s k e).toReal *
          Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} 1 e
        ≤ C_fpHeightTailP * Real.exp (-c_fpHeightTailP * H) := by
  classical
  intro p hp0 hp1 s k H hH
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  set cst : ℝ := min (c_fpHeightP / 2) (1 / 5000) with hcst
  have hcst0 : 0 < cst :=
    lt_min (div_pos c_fpHeightP_pos two_pos) (by norm_num)
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  set T : ℝ≥0∞ :=
    ∑' e : ℕ × ℤ, if (s : ℝ) + H ≤ (e.2 : ℝ) then
      fpDistPlusP p hp0' hp1' s k e else 0 with hT
  have hLHS :
      (∑' e : ℕ × ℤ, (fpDistPlusP p hp0' hp1' s k e).toReal *
        Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} 1 e) =
          T.toReal := by
    rw [hT, ENNReal.tsum_toReal_eq (fun e => by
      split_ifs
      exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top])]
    refine tsum_congr fun e => ?_
    by_cases he : (s : ℝ) + H ≤ (e.2 : ℝ)
    · rw [if_pos he, Set.indicator_apply,
        if_pos (show e ∈ {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} from he),
        Pi.one_apply, mul_one]
    · rw [if_neg he, Set.indicator_apply,
        if_neg (show e ∉ {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} from he),
        mul_zero, ENNReal.toReal_zero]
  have hsplit : ∀ f w : ℕ × ℤ,
      (s : ℝ) + H ≤ ((f + w).2 : ℝ) →
        (s : ℝ) + H / 2 ≤ (f.2 : ℝ) ∨ H / 2 ≤ (w.2 : ℝ) := by
    intro f w hfw
    have hcast : ((f + w).2 : ℝ) = (f.2 : ℝ) + (w.2 : ℝ) := by
      rw [Prod.snd_add]
      push_cast
      ring
    rw [hcast] at hfw
    by_cases hf : (s : ℝ) + H / 2 ≤ (f.2 : ℝ)
    · exact Or.inl hf
    · right
      push Not at hf
      linarith
  have hconv := fpDistPlusP_event_le_add p hp0' hp1' s k
    (fun e => (s : ℝ) + H ≤ (e.2 : ℝ))
    (fun f => (s : ℝ) + H / 2 ≤ (f.2 : ℝ))
    (fun w => H / 2 ≤ (w.2 : ℝ)) hsplit
  have hfp := fpDistP_height_tail_explicitC p hp0 hp1 s (H / 2) (by linarith)
  have hhold := holdSumP_snd_tail_window hp0 hp1 k (H / 2)
  have hTle : T ≤
      ENNReal.ofReal (C_fpHeightP * Real.exp (-c_fpHeightP * (H / 2))) +
        ENNReal.ofReal ((6 : ℝ) ^ k * Real.exp (-(H / 2) / 1000)) := by
    rw [hT]
    exact hconv.trans (add_le_add hfp hhold)
  have hholdReal :
      (6 : ℝ) ^ k * Real.exp (-(H / 2) / 1000) ≤
        Real.exp (-(1 / 5000 : ℝ) * H) := by
    calc
      (6 : ℝ) ^ k * Real.exp (-(H / 2) / 1000) ≤
          Real.exp (2 * (k : ℝ)) * Real.exp (-(H / 2) / 1000) :=
        mul_le_mul_of_nonneg_right (six_pow_le_exp_two_mul k) (Real.exp_pos _).le
      _ = Real.exp (2 * (k : ℝ) - H / 2000) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(1 / 5000 : ℝ) * H) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hreal :
      C_fpHeightP * Real.exp (-c_fpHeightP * (H / 2)) +
          (6 : ℝ) ^ k * Real.exp (-(H / 2) / 1000) ≤
        (C_fpHeightP + 1) * Real.exp (-cst * H) := by
    have hc1 : cst ≤ c_fpHeightP / 2 := min_le_left _ _
    have hc2 : cst ≤ 1 / 5000 := min_le_right _ _
    have h1 : Real.exp (-c_fpHeightP * (H / 2)) ≤ Real.exp (-cst * H) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have h2 : Real.exp (-(1 / 5000 : ℝ) * H) ≤ Real.exp (-cst * H) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      C_fpHeightP * Real.exp (-c_fpHeightP * (H / 2)) +
          (6 : ℝ) ^ k * Real.exp (-(H / 2) / 1000) ≤
          C_fpHeightP * Real.exp (-cst * H) + Real.exp (-cst * H) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 C_fpHeightP_pos.le)
          (hholdReal.trans h2)
      _ = (C_fpHeightP + 1) * Real.exp (-cst * H) := by ring
  rw [hLHS]
  refine ENNReal.toReal_le_of_le_ofReal
    (mul_pos C_fpHeightTailP_pos (Real.exp_pos _)).le ?_
  calc
    T ≤ _ := hTle
    _ ≤ ENNReal.ofReal ((C_fpHeightP + 1) * Real.exp (-cst * H)) := by
      rw [← ENNReal.ofReal_add
        (mul_nonneg C_fpHeightP_pos.le (Real.exp_pos _).le)
        (mul_nonneg (pow_nonneg (by norm_num) _) (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (C_fpHeightTailP *
        Real.exp (-c_fpHeightTailP * H)) := by
      unfold C_fpHeightTailP c_fpHeightTailP
      rw [← hcst]

/-- Existential interface for the tilted post-passage height tail. -/
theorem fpDistPlusP_height_tail :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ s k : ℕ, ∀ H : ℝ, 10000 * (1 + (k : ℝ)) ≤ H →
      ∑' e : ℕ × ℤ, (fpDistPlusP p (by linarith) (by linarith) s k e).toReal *
          Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} 1 e
        ≤ C * Real.exp (-c * H) :=
  ⟨c_fpHeightTailP, c_fpHeightTailP_pos,
    C_fpHeightTailP, C_fpHeightTailP_pos, fpDistPlusP_height_tail_explicitC⟩

/-- Uniform decay rate for the tilted post-passage column tail. -/
noncomputable def c_fpColTailP : ℝ := min c_fpColDevP (1 / 2000)

/-- Uniform multiplicative constant for the tilted post-passage column tail. -/
noncomputable def C_fpColTailP : ℝ := C_fpColDevP + 1

theorem c_fpColTailP_pos : 0 < c_fpColTailP := by
  unfold c_fpColTailP
  exact lt_min c_fpColDevP_pos (by norm_num)

theorem C_fpColTailP_pos : 0 < C_fpColTailP := by
  unfold C_fpColTailP
  linarith [C_fpColDevP_pos]

/-- The column part of Tao's (7.61), with the first-passage centre moved from
`s/4` to the correct tilted value `p s/2`.  The event is split between a
deviation of the first-passage endpoint by `D` and a holding-walk displacement
by `D`; the same uniform linear margin absorbs the latter's `6^k` factor. -/
theorem fpDistPlusP_col_tail_explicitC :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ s k : ℕ, ∀ D : ℝ, 10000 * (1 + (k : ℝ)) ≤ D →
      ∑' e : ℕ × ℤ, (fpDistPlusP p (by linarith) (by linarith) s k e).toReal *
          Set.indicator {q : ℕ × ℤ |
            2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} 1 e
        ≤ C_fpColTailP *
          (Real.exp (-c_fpColTailP * D ^ 2 / (1 + (s : ℝ))) +
            Real.exp (-c_fpColTailP * D)) := by
  classical
  intro p hp0 hp1 s k D hD
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  set cst : ℝ := min c_fpColDevP (1 / 2000) with hcst
  have hcst0 : 0 < cst := lt_min c_fpColDevP_pos (by norm_num)
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  set T : ℝ≥0∞ :=
    ∑' e : ℕ × ℤ, if 2 * D ≤ |(e.1 : ℝ) - p / 2 * (s : ℝ)| then
      fpDistPlusP p hp0' hp1' s k e else 0 with hT
  have hLHS :
      (∑' e : ℕ × ℤ, (fpDistPlusP p hp0' hp1' s k e).toReal *
        Set.indicator {q : ℕ × ℤ |
          2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} 1 e) = T.toReal := by
    rw [hT, ENNReal.tsum_toReal_eq (fun e => by
      split_ifs
      exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top])]
    refine tsum_congr fun e => ?_
    by_cases he : 2 * D ≤ |(e.1 : ℝ) - p / 2 * (s : ℝ)|
    · rw [if_pos he, Set.indicator_apply,
        if_pos (show e ∈ {q : ℕ × ℤ |
          2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} from he),
        Pi.one_apply, mul_one]
    · rw [if_neg he, Set.indicator_apply,
        if_neg (show e ∉ {q : ℕ × ℤ |
          2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} from he),
        mul_zero, ENNReal.toReal_zero]
  have hsplit : ∀ f w : ℕ × ℤ,
      2 * D ≤ |((f + w).1 : ℝ) - p / 2 * (s : ℝ)| →
        D ≤ |(f.1 : ℝ) - p / 2 * (s : ℝ)| ∨ D ≤ (w.1 : ℝ) := by
    intro f w hfw
    have hcast : ((f + w).1 : ℝ) = (f.1 : ℝ) + (w.1 : ℝ) := by
      rw [Prod.fst_add]
      push_cast
      ring
    by_cases hf : D ≤ |(f.1 : ℝ) - p / 2 * (s : ℝ)|
    · exact Or.inl hf
    · right
      push Not at hf
      rw [hcast] at hfw
      have htri : |(f.1 : ℝ) + (w.1 : ℝ) - p / 2 * (s : ℝ)| ≤
          |(f.1 : ℝ) - p / 2 * (s : ℝ)| + (w.1 : ℝ) := by
        have heq : (f.1 : ℝ) + (w.1 : ℝ) - p / 2 * (s : ℝ) =
            ((f.1 : ℝ) - p / 2 * (s : ℝ)) + (w.1 : ℝ) := by ring
        rw [heq]
        calc
          |((f.1 : ℝ) - p / 2 * (s : ℝ)) + (w.1 : ℝ)| ≤
              |(f.1 : ℝ) - p / 2 * (s : ℝ)| + |(w.1 : ℝ)| := abs_add_le _ _
          _ = |(f.1 : ℝ) - p / 2 * (s : ℝ)| + (w.1 : ℝ) := by
            rw [Nat.abs_cast]
      linarith
  have hconv := fpDistPlusP_event_le_add p hp0' hp1' s k
    (fun e => 2 * D ≤ |(e.1 : ℝ) - p / 2 * (s : ℝ)|)
    (fun f => D ≤ |(f.1 : ℝ) - p / 2 * (s : ℝ)|)
    (fun w => D ≤ (w.1 : ℝ)) hsplit
  have hfp := fpDistP_col_dev_explicitC p hp0 hp1 s D hD0.le
  have hhold := holdSumP_fst_tail_window hp0 hp1 k D
  have hTle : T ≤ ENNReal.ofReal
        (C_fpColDevP * (Real.exp (-c_fpColDevP * D ^ 2 / (1 + (s : ℝ))) +
          Real.exp (-c_fpColDevP * D))) +
      ENNReal.ofReal ((6 : ℝ) ^ k * Real.exp (-D / 1000)) := by
    rw [hT]
    exact hconv.trans (add_le_add hfp hhold)
  have hholdReal : (6 : ℝ) ^ k * Real.exp (-D / 1000) ≤
      Real.exp (-(1 / 2000 : ℝ) * D) := by
    calc
      (6 : ℝ) ^ k * Real.exp (-D / 1000) ≤
          Real.exp (2 * (k : ℝ)) * Real.exp (-D / 1000) :=
        mul_le_mul_of_nonneg_right (six_pow_le_exp_two_mul k) (Real.exp_pos _).le
      _ = Real.exp (2 * (k : ℝ) - D / 1000) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(1 / 2000 : ℝ) * D) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hreal :
      C_fpColDevP * (Real.exp (-c_fpColDevP * D ^ 2 / (1 + (s : ℝ))) +
          Real.exp (-c_fpColDevP * D)) +
          (6 : ℝ) ^ k * Real.exp (-D / 1000) ≤
        (C_fpColDevP + 1) *
          (Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) +
            Real.exp (-cst * D)) := by
    have hc1 : cst ≤ c_fpColDevP := min_le_left _ _
    have hc2 : cst ≤ 1 / 2000 := min_le_right _ _
    have hden : 0 < 1 + (s : ℝ) := by positivity
    have h1 : Real.exp (-c_fpColDevP * D ^ 2 / (1 + (s : ℝ))) ≤
        Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right ?_ hden.le
      nlinarith [sq_nonneg D,
        mul_le_mul_of_nonneg_right hc1 (sq_nonneg D)]
    have h2 : Real.exp (-c_fpColDevP * D) ≤ Real.exp (-cst * D) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have h3 : Real.exp (-(1 / 2000 : ℝ) * D) ≤ Real.exp (-cst * D) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have he1 : 0 ≤ Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) :=
      (Real.exp_pos _).le
    have he2 : 0 ≤ Real.exp (-cst * D) := (Real.exp_pos _).le
    calc
      C_fpColDevP * (Real.exp (-c_fpColDevP * D ^ 2 / (1 + (s : ℝ))) +
          Real.exp (-c_fpColDevP * D)) +
          (6 : ℝ) ^ k * Real.exp (-D / 1000) ≤
          C_fpColDevP * (Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) +
            Real.exp (-cst * D)) + Real.exp (-cst * D) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add h1 h2) C_fpColDevP_pos.le)
          (hholdReal.trans h3)
      _ ≤ (C_fpColDevP + 1) *
          (Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) +
            Real.exp (-cst * D)) := by nlinarith
  rw [hLHS]
  refine ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg C_fpColTailP_pos.le
      (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) ?_
  calc
    T ≤ _ := hTle
    _ ≤ ENNReal.ofReal ((C_fpColDevP + 1) *
        (Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) +
          Real.exp (-cst * D))) := by
      rw [← ENNReal.ofReal_add
        (mul_nonneg C_fpColDevP_pos.le
          (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
        (mul_nonneg (pow_nonneg (by norm_num) _) (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (C_fpColTailP *
        (Real.exp (-c_fpColTailP * D ^ 2 / (1 + (s : ℝ))) +
          Real.exp (-c_fpColTailP * D))) := by
      unfold C_fpColTailP c_fpColTailP
      rw [← hcst]

/-- Existential interface for the tilted post-passage column tail. -/
theorem fpDistPlusP_col_tail :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ s k : ℕ, ∀ D : ℝ, 10000 * (1 + (k : ℝ)) ≤ D →
      ∑' e : ℕ × ℤ, (fpDistPlusP p (by linarith) (by linarith) s k e).toReal *
          Set.indicator {q : ℕ × ℤ |
            2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} 1 e
        ≤ C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) +
          Real.exp (-c * D)) :=
  ⟨c_fpColTailP, c_fpColTailP_pos,
    C_fpColTailP, C_fpColTailP_pos, fpDistPlusP_col_tail_explicitC⟩

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
