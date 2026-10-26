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

/-- Every finer-scale black strip point lies in a unique family triangle. -/
theorem TriangleFamilyP.existsUnique_cover {n ξ : ℕ} (F : TriangleFamilyP n ξ)
    {q : ℕ × ℤ} (hq : q.1 + 1 ≤ n / 2 ∧ blackP n ξ q.1 q.2) :
    ∃! t : ℕ × ℤ × ℝ, t ∈ F.T ∧ q ∈ triangle t.1 t.2.1 t.2.2 := by
  have hmem : q ∈ {p : ℕ × ℤ | p.1 + 1 ≤ n / 2 ∧ blackP n ξ p.1 p.2} := hq
  rw [F.cover] at hmem
  simp only [Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨t, ht, hqt⟩ := hmem
  refine ⟨t, ⟨ht, hqt⟩, ?_⟩
  rintro t' ⟨ht', hqt'⟩
  by_contra hne
  exact F.not_mem_two ht' ht hne hqt' hqt

/-- The unique finer-scale family triangle covering a black strip point. -/
noncomputable def TriangleFamilyP.coveringTriangle {n ξ : ℕ}
    (F : TriangleFamilyP n ξ) (q : ℕ × ℤ)
    (hq : q.1 + 1 ≤ n / 2 ∧ blackP n ξ q.1 q.2) : ℕ × ℤ × ℝ :=
  (F.existsUnique_cover hq).exists.choose

theorem TriangleFamilyP.coveringTriangle_mem {n ξ : ℕ} (F : TriangleFamilyP n ξ)
    {q : ℕ × ℤ} (hq : q.1 + 1 ≤ n / 2 ∧ blackP n ξ q.1 q.2) :
    F.coveringTriangle q hq ∈ F.T :=
  (F.existsUnique_cover hq).exists.choose_spec.1

theorem TriangleFamilyP.coveringTriangle_covers {n ξ : ℕ} (F : TriangleFamilyP n ξ)
    {q : ℕ × ℤ} (hq : q.1 + 1 ≤ n / 2 ∧ blackP n ξ q.1 q.2) :
    q ∈ triangle (F.coveringTriangle q hq).1 (F.coveringTriangle q hq).2.1
      (F.coveringTriangle q hq).2.2 :=
  (F.existsUnique_cover hq).exists.choose_spec.2

theorem TriangleFamilyP.eq_coveringTriangle {n ξ : ℕ} (F : TriangleFamilyP n ξ)
    {q : ℕ × ℤ} (hq : q.1 + 1 ≤ n / 2 ∧ blackP n ξ q.1 q.2)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ F.T) (hqt : q ∈ triangle t.1 t.2.1 t.2.2) :
    t = F.coveringTriangle q hq :=
  (F.existsUnique_cover hq).unique ⟨ht, hqt⟩
    ⟨F.coveringTriangle_mem hq, F.coveringTriangle_covers hq⟩

/-- The finer-family version of Tao's (7.52) triangle budget.  A triangle
point at horizontal depth at most `m+1` below the strip edge has vertical
budget `O(m)`.  This deterministic estimate is independent of the holding
law; it is restated for `TriangleFamilyP` because the campaign keeps the
finer triangle family separate from the frozen Sec7 family. -/
theorem budgetP_le_of_mem_triangle {n ξ : ℕ} (F : TriangleFamilyP n ξ)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ F.T) {j : ℕ} {l : ℤ}
    (hmem : (j, l) ∈ triangle t.1 t.2.1 t.2.2) {m : ℕ}
    (hjm : n / 2 ≤ j + 1 + m) :
    ((t.2.1 - l).toNat : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 := by
  obtain ⟨hj0, hl0, hlin⟩ := hmem
  have hsz0 : 0 ≤ t.2.2 := F.size_nonneg t ht
  have hlog9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℕ := ⌊t.2.2 / Real.log 9⌋₊ with hK
  have hKle : (K : ℝ) * Real.log 9 ≤ t.2.2 := by
    have hfl : (K : ℝ) ≤ t.2.2 / Real.log 9 := Nat.floor_le (by positivity)
    calc
      (K : ℝ) * Real.log 9 ≤ t.2.2 / Real.log 9 * Real.log 9 :=
        mul_le_mul_of_nonneg_right hfl hlog9.le
      _ = t.2.2 := div_mul_cancel₀ _ hlog9.ne'
  have hqmem : ((t.1 + K, t.2.1) : ℕ × ℤ) ∈ triangle t.1 t.2.1 t.2.2 := by
    refine ⟨Nat.le_add_right _ _, le_rfl, ?_⟩
    push_cast
    have h : ((t.1 : ℝ) + K - t.1) * Real.log 9 = (K : ℝ) * Real.log 9 := by ring
    rw [h]
    simpa using hKle
  have hconf := F.confined t ht _ hqmem
  have hsep : (0 : ℝ) ≤ (1 / 10 : ℝ) * Real.log (1 / (epsP : ℝ)) :=
    (lt_trans (by norm_num) twenty_thousand_lt_sepP).le
  have h3 : (t.1 : ℝ) + K + 1 ≤ (n : ℝ) / 2 := by
    push_cast at hconf
    linarith
  have h4 : (n : ℝ) / 2 ≤ ((n / 2 : ℕ) : ℝ) + 1 / 2 := by
    have hn : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hn
    linarith
  have h5 : ((n / 2 : ℕ) : ℝ) ≤ (j : ℝ) + 1 + m := by exact_mod_cast hjm
  have hK1 : t.2.2 < ((K : ℝ) + 1) * Real.log 9 := by
    have hlt : t.2.2 / Real.log 9 < (K : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (t.2.2 / Real.log 9)
      exact_mod_cast this
    calc
      t.2.2 = t.2.2 / Real.log 9 * Real.log 9 := (div_mul_cancel₀ _ hlog9.ne').symm
      _ < ((K : ℝ) + 1) * Real.log 9 := mul_lt_mul_of_pos_right hlt hlog9
  have htn : (((t.2.1 - l).toNat : ℕ) : ℝ) = (t.2.1 : ℝ) - l := by
    have h := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ t.2.1 - l)
    have : (((t.2.1 - l).toNat : ℕ) : ℤ) = t.2.1 - l := h
    exact_mod_cast this
  have hj0R : (t.1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
  have h6 : (K : ℝ) + 1 - j + t.1 ≤ (m : ℝ) + 2 := by linarith
  calc
    ((t.2.1 - l).toNat : ℝ) * Real.log 2
        = ((t.2.1 : ℝ) - l) * Real.log 2 := by rw [htn]
    _ ≤ t.2.2 - ((j : ℝ) - t.1) * Real.log 9 := by linarith [hlin]
    _ ≤ ((K : ℝ) + 1) * Real.log 9 - ((j : ℝ) - t.1) * Real.log 9 := by
      linarith
    _ = ((K : ℝ) + 1 - j + t.1) * Real.log 9 := by ring
    _ ≤ ((m : ℝ) + 2) * Real.log 9 :=
      mul_le_mul_of_nonneg_right h6 hlog9.le

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

/-- The deep-regime counterpart of `fpDistP_out_of_strip_le`, uniform over
the Pascal window.  Triangle membership gives Tao's linear budget (7.52).
The strict inequality `5 log 9 < 16 log 2` then shows that, sufficiently deep
in the strip, every endpoint crossing the right edge lies in the fixed bad
localization event from `fpDistP_localization_le_eighth`.  This is the fourth
slope-sensitive site in the tilted transfer of Lemma 7.9. -/
theorem fpDistP_out_of_strip_deep_le :
    ∃ Cthr : ℕ, ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamilyP n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      ∑' e : ℕ × ℤ,
        (fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e).toReal *
          Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2) ≤ 1 / 8 := by
  refine ⟨500000, ?_⟩
  intro p hp0 hp1 n ξ hξ F m hm hmn l hl t ht htmem s hs
  classical
  let fpLaw := fpDistP p (by linarith [hp0]) (by linarith [hp1]) s
  let escaped : ℕ × ℤ → Prop := fun e =>
    ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ outStripSetP n
  let bad : ℕ × ℤ → Prop := fun e =>
    (s : ℝ) + 12000 ≤ (e.2 : ℝ) ∨
      (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
  have hbudget : (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 := by
    have hb := budgetP_le_of_mem_triangle F ht htmem (m := m) (by omega)
    have hcast : ((t.2.1 - l).toNat : ℝ) = (s : ℝ) := by
      have : (t.2.1 - l).toNat = s := by omega
      exact_mod_cast this
    rwa [hcast] at hb
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 40 * Real.log 9 ≤ 127 * Real.log 2 := by
    have hp : (9 : ℝ) ^ (40 : ℕ) ≤ (2 : ℝ) ^ (127 : ℕ) := by norm_num
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (9 : ℝ) ^ (40 : ℕ)) hp
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    exact h
  have hslope : 40 * (s : ℝ) ≤ 127 * ((m : ℝ) + 2) := by
    have h1 : 40 * (s : ℝ) * Real.log 2 ≤
        40 * ((m : ℝ) + 2) * Real.log 9 := by nlinarith
    have h2 : 40 * ((m : ℝ) + 2) * Real.log 9 ≤
        127 * ((m : ℝ) + 2) * Real.log 2 := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hlog hm0]
    nlinarith
  have hmR : (500000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hescape_bad : ∀ e : ℕ × ℤ, escaped e → bad e := by
    intro e he
    by_cases hv : (s : ℝ) + 12000 ≤ (e.2 : ℝ)
    · exact Or.inl hv
    · right
      have he1 : m < e.1 := by
        simp only [escaped, outStripSetP, Set.mem_ofPred_eq] at he
        omega
      have he1R : (m : ℝ) + 1 ≤ (e.1 : ℝ) := by exact_mod_cast he1
      push Not at hv
      nlinarith
  set P : ℝ≥0∞ := ∑' e : ℕ × ℤ, if escaped e then fpLaw e else 0 with hP
  set B : ℝ≥0∞ := ∑' e : ℕ × ℤ, if bad e then fpLaw e else 0 with hB
  have hPB : P ≤ B := by
    rw [hP, hB]
    refine ENNReal.tsum_le_tsum fun e => ?_
    by_cases he : escaped e
    · rw [if_pos he, if_pos (hescape_bad e he)]
    · rw [if_neg he]
      exact bot_le
  have hBle : B ≤ (1 : ℝ≥0∞) / 8 := by
    rw [hB]
    exact fpDistP_localization_le_eighth hp0 hp1 s
  have hLHS :
      (∑' e : ℕ × ℤ, (fpLaw e).toReal *
        Set.indicator (outStripSetP n) 1
          (n / 2 - m + e.1, l + e.2)) = P.toReal := by
    rw [hP, ENNReal.tsum_toReal_eq (fun e => by
      split_ifs
      exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top])]
    refine tsum_congr fun e => ?_
    by_cases he : escaped e
    · rw [if_pos he, Set.indicator_of_mem he, Pi.one_apply, mul_one]
    · rw [if_neg he, Set.indicator_of_notMem he, mul_zero, ENNReal.toReal_zero]
  change (∑' e : ℕ × ℤ, (fpLaw e).toReal *
    Set.indicator (outStripSetP n) 1
      (n / 2 - m + e.1, l + e.2)) ≤ 1 / 8
  rw [hLHS]
  have hto : P.toReal ≤ ((1 : ℝ≥0∞) / 8).toReal :=
    ENNReal.toReal_mono (by finiteness) (hPB.trans hBle)
  norm_num at hto ⊢
  exact hto

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

/-- The deep-regime white-exit estimate required by tilted Lemma 7.9.  Unlike
`fpDistP_white_exit`, this statement has no `s ≤ m/log²m` hypothesis: triangle
membership itself supplies the linear (7.52) budget, and
`fpDistP_out_of_strip_deep_le` uses the strict tilted slope margin.  The mass
`3/4` and depth threshold are uniform over `p ∈ [1/5,3/5]`. -/
theorem fpDistP_white_exit_deep :
    ∃ p₀ : ℝ, 51 / 100 ≤ p₀ ∧ ∃ Cthr : ℕ,
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamilyP n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      p₀ ≤ ∑' e : ℕ × ℤ,
        (fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e).toReal *
          Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2) := by
  obtain ⟨Cthr, hOut⟩ := fpDistP_out_of_strip_deep_le
  refine ⟨3 / 4, by norm_num, Cthr, ?_⟩
  intro p hp0 hp1 n ξ hξ F m hm hmn l hl t ht htmem s hs
  let fpLaw := fpDistP p (by linarith [hp0]) (by linarith [hp1]) s
  have hout := hOut p hp0 hp1 n ξ hξ F m hm hmn l hl t ht htmem s hs
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

/-! ### Tilted Lemma 7.9: finite encounter fold -/

open scoped Classical in
/-- One step of Tao's finite Lemma-7.9 encounter fold for the finer triangle
family.  The state and terminal value are law-independent, so this port reuses
`TaoCollatz.EncState` and `TaoCollatz.encVal`; only the color, cover, and step
law change. -/
noncomputable def encStepP {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (σ : TaoCollatz.EncState) (d : ℕ × ℤ) : TaoCollatz.EncState :=
  if hq : 1 ≤ (σ.pos + d).1 ∧ (σ.pos + d).1 + g ≤ n / 2
      ∧ blackP n ξ ((σ.pos + d).1 - 1) (σ.pos + d).2
      ∧ σ.barrier < (σ.pos + d).2 then
    { pos := σ.pos + d
      barrier := (F.coveringTriangle ((σ.pos + d).1 - 1, (σ.pos + d).2)
        ⟨show (σ.pos + d).1 - 1 + 1 ≤ n / 2 by omega, hq.2.2.1⟩).2.1
      count := σ.count + 1
      cumWhite := σ.cumWhite + (if σ.pos + d ∈ whiteStripP n ξ then 1 else 0)
      banked := if σ.count < R then
          σ.cumWhite + (if σ.pos + d ∈ whiteStripP n ξ then 1 else 0)
        else σ.banked }
  else
    { pos := σ.pos + d, barrier := σ.barrier, count := σ.count,
      cumWhite := σ.cumWhite + (if σ.pos + d ∈ whiteStripP n ξ then 1 else 0),
      banked := σ.banked }

/-- Initial state of the tilted encounter fold. -/
def encInitP (j' : ℕ) (l' : ℤ) : TaoCollatz.EncState :=
  ⟨(j', l'), l', 0, 0, 0⟩

/-- The finite-horizon (7.57) expectation driven by `holdP p`. -/
noncomputable def encExpectP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ) (ε : ℝ)
    (T : ℕ) (σ : TaoCollatz.EncState) : ℝ :=
  ((holdP p hp0 hp1).iid T).expect fun v =>
    TaoCollatz.encVal ε R ((List.ofFn v).foldl (encStepP F R g) σ)

theorem encExpectP_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ) (ε : ℝ)
    (σ : TaoCollatz.EncState) :
    encExpectP p hp0 hp1 F R g ε 0 σ = TaoCollatz.encVal ε R σ := by
  rw [encExpectP, PMF.expect_iid_zero]
  simp

/-- Head-peel recursion for the tilted finite encounter fold. -/
theorem encExpectP_succ (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (σ : TaoCollatz.EncState) :
    encExpectP p hp0 hp1 F R g ε (T + 1) σ =
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
        encExpectP p hp0 hp1 F R g ε T (encStepP F R g σ d) := by
  set c : ℝ := Real.exp (ε * R) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hkey : ∀ (m : ℕ) (τ : TaoCollatz.EncState),
      encExpectP p hp0 hp1 F R g ε m τ * c⁻¹ =
        ((holdP p hp0 hp1).iid m).expect fun v =>
          TaoCollatz.encVal ε R ((List.ofFn v).foldl (encStepP F R g) τ) * c⁻¹ := by
    intro m τ
    rw [encExpectP, PMF.expect, PMF.expect, ← tsum_mul_right]
    exact tsum_congr fun v => by ring
  have h0 : ∀ (m : ℕ) (τ : TaoCollatz.EncState) (v : Fin m → ℕ × ℤ),
      0 ≤ TaoCollatz.encVal ε R ((List.ofFn v).foldl (encStepP F R g) τ) * c⁻¹ :=
    fun m τ v => mul_nonneg (TaoCollatz.encVal_pos ε R _).le (by positivity)
  have h1 : ∀ (m : ℕ) (τ : TaoCollatz.EncState) (v : Fin m → ℕ × ℤ),
      TaoCollatz.encVal ε R ((List.ofFn v).foldl (encStepP F R g) τ) * c⁻¹ ≤ 1 := by
    intro m τ v
    rw [← mul_inv_cancel₀ hc0.ne']
    exact mul_le_mul_of_nonneg_right (TaoCollatz.encVal_le ε hε R _) (by positivity)
  have hmain : encExpectP p hp0 hp1 F R g ε (T + 1) σ * c⁻¹ =
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
        (encExpectP p hp0 hp1 F R g ε T (encStepP F R g σ d) * c⁻¹) := by
    rw [hkey (T + 1) σ,
      PMF.expect_iid_succ (holdP p hp0 hp1) T _ (h0 (T + 1) σ) (h1 (T + 1) σ)]
    refine tsum_congr fun d => ?_
    rw [hkey T (encStepP F R g σ d)]
    congr 1
    refine congrArg _ (funext fun w => ?_)
    have hlist : List.ofFn (Fin.cons d w : Fin (T + 1) → ℕ × ℤ) =
        d :: List.ofFn w := by
      rw [List.ofFn_succ]
      congr 1
    rw [hlist, List.foldl_cons]
  have hfin := congrArg (· * c) hmain
  simp only [mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one] at hfin
  rw [hfin, ← tsum_mul_right]
  exact tsum_congr fun d => by
    rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one]

/-- Trivial `exp(εR)` envelope for the tilted fold expectation. -/
theorem encExpectP_le (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (σ : TaoCollatz.EncState) :
    encExpectP p hp0 hp1 F R g ε T σ ≤ Real.exp (ε * R) := by
  have hsum : Summable (fun v : Fin T → ℕ × ℤ =>
      (((holdP p hp0 hp1).iid T) v).toReal) :=
    ENNReal.summable_toReal (by
      rw [((holdP p hp0 hp1).iid T).tsum_coe]
      exact ENNReal.one_ne_top)
  have hle : ∀ v : Fin T → ℕ × ℤ,
      (((holdP p hp0 hp1).iid T) v).toReal *
          TaoCollatz.encVal ε R ((List.ofFn v).foldl (encStepP F R g) σ) ≤
        (((holdP p hp0 hp1).iid T) v).toReal * Real.exp (ε * R) :=
    fun v => mul_le_mul_of_nonneg_left (TaoCollatz.encVal_le ε hε R _)
      ENNReal.toReal_nonneg
  have hsumR : Summable (fun v : Fin T → ℕ × ℤ =>
      (((holdP p hp0 hp1).iid T) v).toReal * Real.exp (ε * R)) := hsum.mul_right _
  have hsumL : Summable (fun v : Fin T → ℕ × ℤ =>
      (((holdP p hp0 hp1).iid T) v).toReal *
        TaoCollatz.encVal ε R ((List.ofFn v).foldl (encStepP F R g) σ)) :=
    Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (TaoCollatz.encVal_pos ε R _).le)
      hle hsumR
  calc
    encExpectP p hp0 hp1 F R g ε T σ ≤
        ∑' v : Fin T → ℕ × ℤ,
          (((holdP p hp0 hp1).iid T) v).toReal * Real.exp (ε * R) :=
      Summable.tsum_le_tsum hle hsumL hsumR
    _ = Real.exp (ε * R) := by
      rw [tsum_mul_right,
        ← ENNReal.tsum_toReal_eq (fun v => PMF.apply_ne_top _ _),
        ((holdP p hp0 hp1).iid T).tsum_coe, ENNReal.toReal_one, one_mul]

theorem encExpectP_nonneg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ) (ε : ℝ)
    (T : ℕ) (σ : TaoCollatz.EncState) :
    0 ≤ encExpectP p hp0 hp1 F R g ε T σ :=
  tsum_nonneg fun _ =>
    mul_nonneg ENNReal.toReal_nonneg (TaoCollatz.encVal_pos ε R _).le

theorem encStepP_count_le {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (σ : TaoCollatz.EncState) (d : ℕ × ℤ) :
    σ.count ≤ (encStepP F R g σ d).count := by
  unfold encStepP
  split <;> dsimp only <;> omega

/-! ### The moving-centre slope budget in Lemma 7.10 -/

/-- The tilted counterpart of Tao's numerical inequality (7.64).  At every
`p ≤ 3/5`, the moving first-passage centre `(p/2)s`, together with its
`2s^0.6` localization error, remains inside the triangle face budget
`s log 2` once `s ≥ 10^8`.  This is the thin slope-sensitive input to the
apex-confinement argument; `slope_margin` supplies the uniform `24/25`
main-term bound and the remaining `1/25` absorbs the localization error. -/
theorem tilted_apex_face_budget {p : ℝ} (hp1 : p ≤ 3 / 5) {s : ℕ}
    (hs : 10 ^ 8 ≤ s) :
    (p / 2 * (s : ℝ) + 2 * (s : ℝ) ^ (0.6 : ℝ)) * Real.log 9 ≤
      (s : ℝ) * Real.log 2 := by
  have hsR : ((10 ^ 8 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hsR' : (100000000 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < (s : ℝ) := lt_of_lt_of_le (by norm_num) hsR'
  have hs04 : (1000 : ℝ) ≤ (s : ℝ) ^ (0.4 : ℝ) := by
    have h1 : ((10 : ℝ) ^ (8 : ℕ)) ^ (0.4 : ℝ) ≤
        (s : ℝ) ^ (0.4 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      exact_mod_cast hsR
    have h2 : ((10 : ℝ) ^ (8 : ℕ)) ^ (0.4 : ℝ) =
        (10 : ℝ) ^ (3.2 : ℝ) := by
      rw [← Real.rpow_natCast 10 8,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    have h3 : (1000 : ℝ) = (10 : ℝ) ^ ((3 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    rw [h3]
    refine le_trans ?_ h1
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hs06nn : (0 : ℝ) ≤ (s : ℝ) ^ (0.6 : ℝ) :=
    Real.rpow_nonneg hs0.le _
  have hs06 : 1000 * (s : ℝ) ^ (0.6 : ℝ) ≤ (s : ℝ) := by
    have hsplit : (s : ℝ) ^ (0.4 : ℝ) * (s : ℝ) ^ (0.6 : ℝ) =
        (s : ℝ) := by
      rw [← Real.rpow_add hs0]
      norm_num
    calc
      1000 * (s : ℝ) ^ (0.6 : ℝ) ≤
          (s : ℝ) ^ (0.4 : ℝ) * (s : ℝ) ^ (0.6 : ℝ) :=
        mul_le_mul_of_nonneg_right hs04 hs06nn
      _ = (s : ℝ) := hsplit
  have hlog9 : Real.log 9 ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    linarith
  have hlog9nn : (0 : ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have herr :
      2 * (s : ℝ) ^ (0.6 : ℝ) * Real.log 9 ≤
        (1 / 25 : ℝ) * (s : ℝ) * Real.log 2 := by
    have h1 : 2 * (s : ℝ) ^ (0.6 : ℝ) * Real.log 9 ≤
        16 * (s : ℝ) ^ (0.6 : ℝ) := by
      nlinarith [mul_nonneg hs06nn (by linarith : (0 : ℝ) ≤ 8 - Real.log 9)]
    have hsnn : (0 : ℝ) ≤ (s : ℝ) := hs0.le
    have h2 : 16 * (s : ℝ) ^ (0.6 : ℝ) ≤ (1 / 50 : ℝ) * s := by
      linarith
    have h3 : (1 / 50 : ℝ) * s ≤ (1 / 25 : ℝ) * s * Real.log 2 := by
      nlinarith
    exact h1.trans (h2.trans h3)
  have hmain := (slope_margin hp1).1
  have hmain' :
      p / 2 * (s : ℝ) * Real.log 9 ≤
        (24 / 25 : ℝ) * (s : ℝ) * Real.log 2 := by
    have hsnn : (0 : ℝ) ≤ (s : ℝ) := hs0.le
    nlinarith [mul_nonneg hsnn
      (sub_nonneg.mpr hmain)]
  nlinarith

/-- In the deep-triangle regime, the encounter scale `A²(1+k)` is at most
one hundredth of the passage height.  This sharper form of the size budget is
needed at the smallest tilted drift `p=1/5`; the fixed-law proof's coarse
`3s/25` bound would consume more than the available moving-centre distance. -/
theorem apex_size_budget_of_deep {m s : ℕ} (hm : 1 ≤ m)
    (hdeep : (m : ℝ) ^ (0.8 : ℝ) < (s : ℝ))
    {A : ℝ} {k s' : ℕ}
    (hs'm : (s' : ℝ) ≤ (m : ℝ) ^ (0.4 : ℝ))
    (hbig : 100 * A ^ 2 * (1 + (k : ℝ)) ≤ (s' : ℝ)) :
    A ^ 2 * (1 + (k : ℝ)) ≤ (s : ℝ) / 100 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpow : (m : ℝ) ^ (0.4 : ℝ) ≤
      (m : ℝ) ^ (0.8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmR (by norm_num)
  have hchain : 100 * (A ^ 2 * (1 + (k : ℝ))) < (s : ℝ) := by
    calc
      100 * (A ^ 2 * (1 + (k : ℝ))) =
          100 * A ^ 2 * (1 + (k : ℝ)) := by ring
      _ ≤ (s' : ℝ) := hbig
      _ ≤ (m : ℝ) ^ (0.4 : ℝ) := hs'm
      _ ≤ (m : ℝ) ^ (0.8 : ℝ) := hpow
      _ < (s : ℝ) := hdeep
  linarith

/-- The moving first-passage centre has enough horizontal room for both the
`2s^0.6` localization error and the encounter-scale error, uniformly down to
`p=1/5`.  Together with `tilted_apex_face_budget`, this supplies the two
slope-dependent substitutions in the tilted apex-confinement proof. -/
theorem tilted_apex_horizontal_room {p : ℝ} (hp0 : 1 / 5 ≤ p) {s : ℕ}
    (hs : 10 ^ 8 ≤ s) {A : ℝ} {k : ℕ}
    (hAk : A ^ 2 * (1 + (k : ℝ)) ≤ (s : ℝ) / 100) :
    2 * (s : ℝ) ^ (0.6 : ℝ) +
        2 * A ^ 2 * (1 + (k : ℝ)) + 1 ≤
      p / 2 * (s : ℝ) := by
  have hsR : ((10 ^ 8 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hsR' : (100000000 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < (s : ℝ) := lt_of_lt_of_le (by norm_num) hsR'
  have hs04 : (1000 : ℝ) ≤ (s : ℝ) ^ (0.4 : ℝ) := by
    have h1 : ((10 : ℝ) ^ (8 : ℕ)) ^ (0.4 : ℝ) ≤
        (s : ℝ) ^ (0.4 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      exact_mod_cast hsR
    have h2 : ((10 : ℝ) ^ (8 : ℕ)) ^ (0.4 : ℝ) =
        (10 : ℝ) ^ (3.2 : ℝ) := by
      rw [← Real.rpow_natCast 10 8,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    have h3 : (1000 : ℝ) = (10 : ℝ) ^ ((3 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    rw [h3]
    refine le_trans ?_ h1
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hs06nn : (0 : ℝ) ≤ (s : ℝ) ^ (0.6 : ℝ) :=
    Real.rpow_nonneg hs0.le _
  have hs06 : 1000 * (s : ℝ) ^ (0.6 : ℝ) ≤ (s : ℝ) := by
    have hsplit : (s : ℝ) ^ (0.4 : ℝ) * (s : ℝ) ^ (0.6 : ℝ) =
        (s : ℝ) := by
      rw [← Real.rpow_add hs0]
      norm_num
    calc
      1000 * (s : ℝ) ^ (0.6 : ℝ) ≤
          (s : ℝ) ^ (0.4 : ℝ) * (s : ℝ) ^ (0.6 : ℝ) :=
        mul_le_mul_of_nonneg_right hs04 hs06nn
      _ = (s : ℝ) := hsplit
  have hpcentre : (1 / 10 : ℝ) * s ≤ p / 2 * s := by
    nlinarith [hs0.le]
  have hone : (1 : ℝ) ≤ (1 / 1000 : ℝ) * s := by
    nlinarith
  calc
    2 * (s : ℝ) ^ (0.6 : ℝ) +
          2 * A ^ 2 * (1 + (k : ℝ)) + 1
        ≤ (2 / 1000 : ℝ) * s + (2 / 100 : ℝ) * s +
            (1 / 1000 : ℝ) * s := by
          nlinarith
    _ ≤ (1 / 10 : ℝ) * s := by nlinarith [hs0.le]
    _ ≤ p / 2 * s := hpcentre

-- HEARTBEAT: this direct geometric port follows two long nested contradiction
-- arguments from Tao's Lemma 7.10 and needs the same budget as the fixed-law proof.
set_option maxHeartbeats 1600000 in
/-- **Tilted X10a — apex confinement** (paper (7.63)–(7.65)).
This ports the deterministic intersection argument to the finer triangle family
and the moving first-passage centre `(p/2)s`.  The only new slope inputs are
`tilted_apex_horizontal_room` and `tilted_apex_face_budget`, both uniform
on `p ∈ [1/5,3/5]`. -/
theorem encounter_apex_proximityP_rpow_at :
    ∀ (p : ℝ), 1 / 5 ≤ p → p ≤ 3 / 5 → ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l → S_apexProx ≤ s →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (A : ℝ), 5 ≤ A → ∀ (k s' : ℕ),
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
        100 * A ^ 2 * (1 + (k : ℝ)) ≤ (s' : ℝ) →
      ∀ e : ℕ × ℤ, (s : ℤ) < e.2 →
        (e.2 : ℝ) ≤ (s : ℝ) + 2 * A ^ 2 * (1 + (k : ℝ)) →
        |(e.1 : ℝ) - p / 2 * (s : ℝ)| ≤ 2 * (s : ℝ) ^ (0.6 : ℝ) →
      ∀ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2 →
        ((j + e.1, l + e.2) : ℕ × ℤ) ∈ triangle t'.1 t'.2.1 t'.2.2 →
      (t'.1 : ℝ) ≤ (j : ℝ) + e.1
        ∧ (j : ℝ) + e.1 - t'.1 ≤ C_apexProx * A ^ 2 * (1 + (k : ℝ))
        ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)|
            ≤ C_apexProx * A ^ 2 * (1 + (k : ℝ)) := by
  unfold C_apexProx S_apexProx
  intro p hp0 hp1 n ξ hξ F t₀ ht₀ j l hmem s hs hS₀ hdeep A hA k s' hs'm hbig e he2 hh hc
    t' ht' hsize hmem'
  obtain ⟨hjΔj, hllΔ, hbud⟩ := hmem
  obtain ⟨hj₁P, hhl₁, hbud'⟩ := hmem'
  -- logarithm facts
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  have hlog29 : Real.log 2 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
  have hlog9le : Real.log 9 ≤ 8 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
    linarith
  have hlog49 : 2 * Real.log 2 ≤ Real.log 9 := by
    have h4 : Real.log 4 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
    have h4eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hlog169 : (7 : ℝ) / 16 ≤ 4 * Real.log 2 - Real.log 9 := by
    have h1 : 4 * Real.log 2 = Real.log 16 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      push_cast
      ring
    have h3 : Real.log (9 / 16 : ℝ) ≤ 9 / 16 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h4 : Real.log (9 / 16 : ℝ) = Real.log 9 - Real.log 16 :=
      Real.log_div (by norm_num) (by norm_num)
    linarith
  -- size-threshold facts
  have hsR : ((10 ^ 8 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hS₀
  have hsR' : (100000000 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hS₀
  have hs0 : (0 : ℝ) < (s : ℝ) := lt_of_lt_of_le (by norm_num) hsR'
  have hs04 : (1000 : ℝ) ≤ (s : ℝ) ^ (0.4 : ℝ) := by
    have h1 : ((10 : ℝ) ^ (8 : ℕ)) ^ (0.4 : ℝ) ≤ (s : ℝ) ^ (0.4 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      exact_mod_cast hsR
    have h2 : ((10 : ℝ) ^ (8 : ℕ)) ^ (0.4 : ℝ) = (10 : ℝ) ^ (3.2 : ℝ) := by
      rw [← Real.rpow_natCast 10 8, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    have h3 : (1000 : ℝ) = (10 : ℝ) ^ ((3 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    rw [h3]
    refine le_trans ?_ h1
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hs06_nn : (0 : ℝ) ≤ (s : ℝ) ^ (0.6 : ℝ) := Real.rpow_nonneg hs0.le _
  have hs06_le : 1000 * (s : ℝ) ^ (0.6 : ℝ) ≤ (s : ℝ) := by
    have hsplit : (s : ℝ) ^ (0.4 : ℝ) * (s : ℝ) ^ (0.6 : ℝ) = (s : ℝ) := by
      rw [← Real.rpow_add hs0]
      norm_num
    calc 1000 * (s : ℝ) ^ (0.6 : ℝ)
        ≤ (s : ℝ) ^ (0.4 : ℝ) * (s : ℝ) ^ (0.6 : ℝ) :=
          mul_le_mul_of_nonneg_right hs04 hs06_nn
      _ = (s : ℝ) := hsplit
  -- the sharper A²(1+k) ≤ s/100 chain through the deep-regime hypotheses
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hA25 : (25 : ℝ) ≤ A ^ 2 := by nlinarith
  have hAp : (25 : ℝ) * (1 + (k : ℝ)) ≤ A ^ 2 * (1 + (k : ℝ)) := by nlinarith
  have hAp25 : (25 : ℝ) ≤ A ^ 2 * (1 + (k : ℝ)) := by nlinarith
  have hAle : A ^ 2 * (1 + (k : ℝ)) ≤ (s : ℝ) / 100 := by
    obtain ⟨m, hm⟩ : ∃ m, n / 2 - j = m := ⟨_, rfl⟩
    rw [hm] at hdeep hs'm
    have hm2 : (2 : ℕ) ≤ m := by
      by_contra hlt
      push Not at hlt
      have hmR : ((m : ℕ) : ℝ) ≤ 1 := by
        have : m ≤ 1 := by omega
        exact_mod_cast this
      have h04 : ((m : ℕ) : ℝ) ^ (0.4 : ℝ) ≤ 1 :=
        Real.rpow_le_one (Nat.cast_nonneg m) hmR (by norm_num)
      have hcon : 100 * A ^ 2 * (1 + (k : ℝ)) ≤ 1 :=
        le_trans hbig (le_trans hs'm h04)
      nlinarith
    exact apex_size_budget_of_deep (by omega : 1 ≤ m) hdeep hs'm hbig
  -- cast bookkeeping
  have hsRl : ((s : ℕ) : ℝ) = (t₀.2.1 : ℝ) - (l : ℝ) := by
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) hs
    push_cast at h2
    linarith only [h2]
  obtain ⟨hclow, hchigh⟩ := abs_le.mp hc
  have hPj₁ : (t'.1 : ℝ) ≤ (j : ℝ) + (e.1 : ℝ) := by
    have h := hj₁P
    have h2 : (t'.1 : ℝ) ≤ ((j + e.1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h2
    linarith
  have hbud'R : (((j : ℝ) + (e.1 : ℝ)) - (t'.1 : ℝ)) * Real.log 9
      + ((t'.2.1 : ℝ) - ((l : ℝ) + (e.2 : ℝ))) * Real.log 2 ≤ t'.2.2 := by
    have h := hbud'
    push_cast at h
    linarith
  have hbudR : ((j : ℝ) - (t₀.1 : ℝ)) * Real.log 9 + (s : ℝ) * Real.log 2 ≤ t₀.2.2 := by
    have h := hbud
    push_cast at h
    rw [hsRl]
    linarith
  have hhR : (l : ℝ) + (e.2 : ℝ) ≤ (t₀.2.1 : ℝ) + 2 * A ^ 2 * (1 + (k : ℝ)) := by
    linarith only [hh, hsRl]
  have hgt : (t₀.2.1 : ℤ) < l + e.2 := by omega
  have hgtR : (t₀.2.1 : ℝ) < (l : ℝ) + (e.2 : ℝ) := by exact_mod_cast hgt
  set tip : ℝ := (t'.2.1 : ℝ) - t'.2.2 / Real.log 2 with htip
  have htiple : tip ≤ (l : ℝ) + (e.2 : ℝ) := by
    have h1 : ((t'.2.1 : ℝ) - ((l : ℝ) + (e.2 : ℝ))) * Real.log 2 ≤ t'.2.2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hPj₁) hlog9.le, hbud'R]
    rw [htip]
    have h2 : (t'.2.1 : ℝ) - ((l : ℝ) + (e.2 : ℝ)) ≤ t'.2.2 / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr h1
    linarith only [h2]
  have hup : tip ≤ (t₀.2.1 : ℝ) + 2 * A ^ 2 * (1 + (k : ℝ)) := le_trans htiple hhR
  -- the (7.65) lower bound, by the p.53 intersection contradiction
  have hlow : (t₀.2.1 : ℝ) - 10 < tip := by
    by_contra hcase
    push Not at hcase
    have hne : t' ≠ t₀ := by
      intro heq
      rw [heq] at hhl₁
      omega
    have hlΔl₁ : (t₀.2.1 : ℤ) ≤ t'.2.1 := le_of_lt (lt_of_lt_of_le hgt hhl₁)
    have hlΔl₁R : (t₀.2.1 : ℝ) ≤ (t'.2.1 : ℝ) := by exact_mod_cast hlΔl₁
    set bud : ℝ := t'.2.2 - ((t'.2.1 : ℝ) - (t₀.2.1 : ℝ)) * Real.log 2 with hbudd
    have hbudeq : ((t₀.2.1 : ℝ) - tip) * Real.log 2 = bud := by
      rw [htip, hbudd]
      field_simp
      ring
    have hbudpos : 10 * Real.log 2 ≤ bud := by
      rw [← hbudeq]
      nlinarith
    have hbud0 : (0 : ℝ) ≤ bud := by nlinarith
    set K : ℕ := ⌊bud / Real.log 9⌋₊ with hK
    set jst : ℕ := min (j + e.1) (t'.1 + K) with hjst
    -- jst is in t'
    have hmem'2 : ((jst, t₀.2.1) : ℕ × ℤ) ∈ triangle t'.1 t'.2.1 t'.2.2 := by
      refine ⟨le_min hj₁P (Nat.le_add_right _ _), hlΔl₁, ?_⟩
      have h1 : jst ≤ t'.1 + K := min_le_right _ _
      have h2 : ((jst : ℕ) : ℝ) - (t'.1 : ℝ) ≤ (K : ℝ) := by
        have : ((jst : ℕ) : ℝ) ≤ ((t'.1 + K : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at this
        linarith
      have h3 : (K : ℝ) ≤ bud / Real.log 9 := Nat.floor_le (by positivity)
      have h4 : (((jst : ℕ) : ℝ) - (t'.1 : ℝ)) * Real.log 9 ≤ bud := by
        calc (((jst : ℕ) : ℝ) - (t'.1 : ℝ)) * Real.log 9
            ≤ (bud / Real.log 9) * Real.log 9 :=
              mul_le_mul_of_nonneg_right (le_trans h2 h3) hlog9.le
          _ = bud := by field_simp
      rw [hbudd] at h4
      linarith
    -- jst is in t₀
    have hjst_le : ((jst : ℕ) : ℝ) ≤ (j : ℝ) + (e.1 : ℝ) := by
      have : jst ≤ j + e.1 := min_le_left _ _
      have h2 : ((jst : ℕ) : ℝ) ≤ ((j + e.1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h2
      linarith
    have hj_le_jst : j ≤ jst := by
      have hKlow : bud / Real.log 9 - 1 < (K : ℝ) := by
        have := Nat.lt_floor_add_one (bud / Real.log 9)
        linarith
      -- (P − j₁)·log9 ≤ bud + (h − lΔ)·log2
      have hPup : (((j : ℝ) + (e.1 : ℝ)) - (t'.1 : ℝ)) * Real.log 9
          ≤ bud + (((l : ℝ) + (e.2 : ℝ)) - (t₀.2.1 : ℝ)) * Real.log 2 := by
        rw [hbudd]
        nlinarith
      have hhml : ((l : ℝ) + (e.2 : ℝ)) - (t₀.2.1 : ℝ) ≤ 2 * A ^ 2 * (1 + (k : ℝ)) := by
        linarith
      have hhml0 : (0 : ℝ) ≤ ((l : ℝ) + (e.2 : ℝ)) - (t₀.2.1 : ℝ) := by linarith
      -- P ≤ j₁ + bud/log9 + 2A²(1+k)
      have hApnn : (0 : ℝ) ≤ 2 * A ^ 2 * (1 + (k : ℝ)) := by
        linarith only [hAp25]
      have hP2 : (j : ℝ) + (e.1 : ℝ)
          ≤ (t'.1 : ℝ) + bud / Real.log 9 + 2 * A ^ 2 * (1 + (k : ℝ)) := by
        have h5 : (((j : ℝ) + (e.1 : ℝ)) - (t'.1 : ℝ)) * Real.log 9
            ≤ bud + 2 * A ^ 2 * (1 + (k : ℝ)) * Real.log 9 := by
          have hstep : (((l : ℝ) + (e.2 : ℝ)) - (t₀.2.1 : ℝ)) * Real.log 2
              ≤ 2 * A ^ 2 * (1 + (k : ℝ)) * Real.log 9 :=
            mul_le_mul hhml hlog29 hlog2.le hApnn
          linarith only [hPup, hstep]
        have h6 : ((j : ℝ) + (e.1 : ℝ)) - (t'.1 : ℝ)
            ≤ (bud + 2 * A ^ 2 * (1 + (k : ℝ)) * Real.log 9) / Real.log 9 :=
          (le_div_iff₀ hlog9).mpr h5
        have h7 : (bud + 2 * A ^ 2 * (1 + (k : ℝ)) * Real.log 9) / Real.log 9
            = bud / Real.log 9 + 2 * A ^ 2 * (1 + (k : ℝ)) := by
          field_simp
        rw [h7] at h6
        linarith only [h6]
      -- e.1 ≥ (p/2)s − 2s^{0.6} pushes P far right of j
      have hjR : (j : ℝ) ≤ (t'.1 : ℝ) + (K : ℝ) := by
        have hsmall : 2 * (s : ℝ) ^ (0.6 : ℝ) + 2 * A ^ 2 * (1 + (k : ℝ)) + 1
            ≤ p / 2 * (s : ℝ) :=
          tilted_apex_horizontal_room hp0 hS₀ hAle
        linarith only [hKlow, hP2, hclow, hsmall]
      have : (j : ℝ) ≤ ((t'.1 + K : ℕ) : ℝ) := by push_cast; linarith
      have hj2 : j ≤ t'.1 + K := by exact_mod_cast this
      omega
    have hmem2 : ((jst, t₀.2.1) : ℕ × ℤ) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 := by
      refine ⟨le_trans hjΔj hj_le_jst, le_refl _, ?_⟩
      have h1 : ((jst : ℕ) : ℝ) - (j : ℝ) ≤ (e.1 : ℝ) := by
        linarith only [hjst_le]
      have hR2 : (p / 2 * (s : ℝ) + 2 * (s : ℝ) ^ (0.6 : ℝ)) * Real.log 9
          ≤ (s : ℝ) * Real.log 2 :=
        tilted_apex_face_budget hp1 hS₀
      have h2 : (((jst : ℕ) : ℝ) - (j : ℝ)) * Real.log 9 ≤ (s : ℝ) * Real.log 2 := by
        have hjstj0 : (0 : ℝ) ≤ ((jst : ℕ) : ℝ) - (j : ℝ) := by
          have : (j : ℝ) ≤ ((jst : ℕ) : ℝ) := by exact_mod_cast hj_le_jst
          linarith
        calc (((jst : ℕ) : ℝ) - (j : ℝ)) * Real.log 9
            ≤ (e.1 : ℝ) * Real.log 9 := mul_le_mul_of_nonneg_right h1 hlog9.le
          _ ≤ (p / 2 * (s : ℝ) + 2 * (s : ℝ) ^ (0.6 : ℝ)) * Real.log 9 :=
              mul_le_mul_of_nonneg_right (by linarith only [hchigh]) hlog9.le
          _ ≤ (s : ℝ) * Real.log 2 := hR2
      push_cast
      linarith only [h2, hbudR]
    exact F.not_mem_two ht' ht₀ hne hmem'2 hmem2
  -- conclusions
  refine ⟨hPj₁, ?_, ?_⟩
  · -- column proximity
    have h1 : (((j : ℝ) + (e.1 : ℝ)) - (t'.1 : ℝ)) * Real.log 9
        ≤ (((l : ℝ) + (e.2 : ℝ)) - tip) * Real.log 2 := by
      rw [htip]
      have hexp : (((l : ℝ) + (e.2 : ℝ)) - ((t'.2.1 : ℝ) - t'.2.2 / Real.log 2))
          * Real.log 2
          = (((l : ℝ) + (e.2 : ℝ)) - (t'.2.1 : ℝ)) * Real.log 2 + t'.2.2 := by
        field_simp
        ring
      rw [hexp]
      linarith
    have h2 : ((l : ℝ) + (e.2 : ℝ)) - tip < 10 + 2 * A ^ 2 * (1 + (k : ℝ)) := by
      linarith
    have h3 : (10 : ℝ) + 2 * A ^ 2 * (1 + (k : ℝ))
        ≤ (12 / 5) * (A ^ 2 * (1 + (k : ℝ))) := by
      linarith only [hAp25]
    have h4 : (12 / 5 : ℝ) * Real.log 2 ≤ 2 * Real.log 9 := by
      linarith only [hlog49, hlog9]
    have hApnn : (0 : ℝ) ≤ A ^ 2 * (1 + (k : ℝ)) := by linarith only [hAp25]
    have h5 : (((j : ℝ) + (e.1 : ℝ)) - (t'.1 : ℝ)) * Real.log 9
        ≤ (2 * (A ^ 2 * (1 + (k : ℝ)))) * Real.log 9 := by
      calc (((j : ℝ) + (e.1 : ℝ)) - (t'.1 : ℝ)) * Real.log 9
          ≤ (((l : ℝ) + (e.2 : ℝ)) - tip) * Real.log 2 := h1
        _ ≤ ((12 / 5) * (A ^ 2 * (1 + (k : ℝ)))) * Real.log 2 :=
            mul_le_mul_of_nonneg_right (by linarith only [h2, h3]) hlog2.le
        _ = (A ^ 2 * (1 + (k : ℝ))) * ((12 / 5) * Real.log 2) := by ring
        _ ≤ (A ^ 2 * (1 + (k : ℝ))) * (2 * Real.log 9) :=
            mul_le_mul_of_nonneg_left h4 hApnn
        _ = (2 * (A ^ 2 * (1 + (k : ℝ)))) * Real.log 9 := by ring
    have h6 := le_of_mul_le_mul_right h5 hlog9
    linarith only [h6]
  · rw [abs_le]
    constructor
    · linarith only [hlow, hAp25]
    · linarith only [hup]

/-- Existential interface to tilted apex confinement.  Both constants are
chosen before the Pascal parameter `p`. -/
theorem encounter_apex_proximityP_rpow :
    ∃ C₂ ≥ (1 : ℝ), ∃ S₀ : ℕ,
      ∀ (p : ℝ), 1 / 5 ≤ p → p ≤ 3 / 5 → ∀ (n ξ : ℕ), ¬ 3 ∣ ξ →
      ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l → S₀ ≤ s →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (A : ℝ), 5 ≤ A → ∀ (k s' : ℕ),
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
        100 * A ^ 2 * (1 + (k : ℝ)) ≤ (s' : ℝ) →
      ∀ e : ℕ × ℤ, (s : ℤ) < e.2 →
        (e.2 : ℝ) ≤ (s : ℝ) + 2 * A ^ 2 * (1 + (k : ℝ)) →
        |(e.1 : ℝ) - p / 2 * (s : ℝ)| ≤ 2 * (s : ℝ) ^ (0.6 : ℝ) →
      ∀ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2 →
        ((j + e.1, l + e.2) : ℕ × ℤ) ∈ triangle t'.1 t'.2.1 t'.2.2 →
      (t'.1 : ℝ) ≤ (j : ℝ) + e.1
        ∧ (j : ℝ) + e.1 - t'.1 ≤ C₂ * A ^ 2 * (1 + (k : ℝ))
        ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)|
            ≤ C₂ * A ^ 2 * (1 + (k : ℝ)) :=
  ⟨C_apexProx, C_apexProx_ge_one, S_apexProx,
    encounter_apex_proximityP_rpow_at⟩

/-! ### Tilted X10b: separated apex bands -/

/-- The apex-gap inequality for the finer triangle family.  This is the
law-independent geometric core of Tao's (7.65): a lattice point belonging to
one family triangle cannot also belong to a distinct family triangle. -/
theorem apex_gapP {n ξ : ℕ} (F : TriangleFamilyP n ξ) {t' t'' : ℕ × ℤ × ℝ}
    (ht' : t' ∈ F.T) (ht'' : t'' ∈ F.T) (hne : t' ≠ t'')
    (hj : t'.1 ≤ t''.1) {lstar : ℤ} (hl' : lstar ≤ t'.2.1)
    (hmem'' : ((t''.1, lstar) : ℕ × ℤ) ∈ triangle t''.1 t''.2.1 t''.2.2) :
    t'.2.2 < ((t''.1 : ℝ) - t'.1) * Real.log 9 +
      ((t'.2.1 : ℝ) - lstar) * Real.log 2 := by
  have hnot : ((t''.1, lstar) : ℕ × ℤ) ∉ triangle t'.1 t'.2.1 t'.2.2 :=
    fun hmem' => F.not_mem_two ht' ht'' hne hmem' hmem''
  rw [triangle, Set.mem_ofPred_eq] at hnot
  push Not at hnot
  exact hnot hj hl'

/-- The (7.65) apex-separation inequality for `TriangleFamilyP`.  Its proof is
identical to the fixed-scale argument because the finer scale enters only
through `TriangleFamilyP.not_mem_two`. -/
theorem apex_separationP {n ξ : ℕ} (F : TriangleFamilyP n ξ)
    {t' t'' : ℕ × ℤ × ℝ}
    (ht' : t' ∈ F.T) (ht'' : t'' ∈ F.T) (hne : t' ≠ t'') (hj : t'.1 ≤ t''.1)
    {lZ : ℤ} {δ : ℝ} {s' : ℕ}
    (h765 : (t'.2.1 : ℝ) - lZ ≤ t'.2.2 / Real.log 2 + δ)
    (hl' : lZ + ((s' / 2 : ℕ) : ℤ) ≤ t'.2.1)
    (hmem'' : ((t''.1, lZ + ((s' / 2 : ℕ) : ℤ)) : ℕ × ℤ)
      ∈ triangle t''.1 t''.2.1 t''.2.2) :
    (((s' / 2 : ℕ) : ℝ) - δ) * Real.log 2 <
      ((t''.1 : ℝ) - t'.1) * Real.log 9 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hgap := apex_gapP F ht' ht'' hne hj hl' hmem''
  have hcast : ((lZ + ((s' / 2 : ℕ) : ℤ) : ℤ) : ℝ) =
      (lZ : ℝ) + ((s' / 2 : ℕ) : ℝ) := by
    rw [Int.cast_add, Int.cast_natCast]
  rw [hcast] at hgap
  have hexp : ((t'.2.1 : ℝ) - ((lZ : ℝ) + ((s' / 2 : ℕ) : ℝ))) * Real.log 2
      = ((t'.2.1 : ℝ) - lZ) * Real.log 2 -
        ((s' / 2 : ℕ) : ℝ) * Real.log 2 := by ring
  rw [hexp] at hgap
  have h765' : ((t'.2.1 : ℝ) - lZ) * Real.log 2 ≤
      t'.2.2 + δ * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right h765 hlog2.le
    rwa [add_mul, div_mul_cancel₀ _ hlog2.ne'] at h
  have hgoal : (((s' / 2 : ℕ) : ℝ) - δ) * Real.log 2 =
      ((s' / 2 : ℕ) : ℝ) * Real.log 2 - δ * Real.log 2 := by ring
  rw [hgoal]
  linarith [hgap, h765']

/-- Qualifying apexes in the finer family are `s'/10`-separated.  The witness
row is `lΔ + ⌊s'/2⌋`; the quantitative extraction is independent of the
Pascal parameter and of the finer cutoff. -/
theorem qualifying_apex_separatedP {n ξ : ℕ} (F : TriangleFamilyP n ξ)
    (lΔ : ℤ) (s' : ℕ) (W : ℝ) (hW : 1 ≤ W) (hWs : 100 * W ≤ (s' : ℝ)) :
    ∀ t' ∈ F.T, ∀ t'' ∈ F.T, t' ≠ t'' →
      (s' : ℝ) ≤ t'.2.2 → |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (lΔ : ℝ)| ≤ W →
      (s' : ℝ) ≤ t''.2.2 → |(t''.2.1 : ℝ) - t''.2.2 / Real.log 2 - (lΔ : ℝ)| ≤ W →
      (s' : ℝ) / 10 ≤ |(t'.1 : ℝ) - (t''.1 : ℝ)| := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog9hi : Real.log 9 < 2.4 := by
    have h32 : Real.log (3 / 2) ≤ 3 / 2 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have h9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [h9, h3]
    linarith
  have hlog9pos : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  have core : ∀ t' ∈ F.T, ∀ t'' ∈ F.T, t' ≠ t'' → t'.1 ≤ t''.1 →
      (s' : ℝ) ≤ t'.2.2 → |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (lΔ : ℝ)| ≤ W →
      (s' : ℝ) ≤ t''.2.2 → |(t''.2.1 : ℝ) - t''.2.2 / Real.log 2 - (lΔ : ℝ)| ≤ W →
      (s' : ℝ) / 10 ≤ (t''.1 : ℝ) - (t'.1 : ℝ) := by
    intro t' ht' t'' ht'' hne hj hs' hw' hs'' hw''
    have hs'100 : (100 : ℝ) ≤ (s' : ℝ) := le_trans (by linarith) hWs
    have hfl_le : ((s' / 2 : ℕ) : ℝ) ≤ (s' : ℝ) / 2 := by
      have := Nat.cast_div_le (m := s') (n := 2) (α := ℝ)
      push_cast at this
      linarith
    have hfl_ge : (s' : ℝ) / 2 - 1 ≤ ((s' / 2 : ℕ) : ℝ) := by
      have h1 : s' / 2 + s' / 2 + 1 ≥ s' := by omega
      have h2 : (s' : ℝ) ≤ ((s' / 2 : ℕ) : ℝ) + ((s' / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast h1
      linarith
    have htip : ∀ u : ℕ × ℤ × ℝ, (s' : ℝ) ≤ u.2.2 →
        |(u.2.1 : ℝ) - u.2.2 / Real.log 2 - (lΔ : ℝ)| ≤ W →
        (lΔ : ℤ) + ((s' / 2 : ℕ) : ℤ) ≤ u.2.1 := by
      intro u hsu hwu
      have h1 : (lΔ : ℝ) + u.2.2 / Real.log 2 - W ≤ (u.2.1 : ℝ) := by
        have := (abs_le.mp hwu).1
        linarith
      have h2 : (s' : ℝ) / Real.log 2 ≤ u.2.2 / Real.log 2 := by gcongr
      have h3 : (s' : ℝ) * 1.4 ≤ (s' : ℝ) / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        nlinarith [Nat.cast_nonneg (α := ℝ) s', hlog2hi]
      have h4 : ((lΔ : ℝ) + ((s' / 2 : ℕ) : ℝ)) ≤ (u.2.1 : ℝ) := by
        nlinarith [hfl_le]
      have h5 : ((lΔ + ((s' / 2 : ℕ) : ℤ) : ℤ) : ℝ) ≤ (u.2.1 : ℝ) := by
        rw [Int.cast_add, Int.cast_natCast]
        linarith
      exact_mod_cast h5
    have hWfl : W ≤ ((s' / 2 : ℕ) : ℝ) := by linarith [hfl_ge]
    have hmem'' : ((t''.1, lΔ + ((s' / 2 : ℕ) : ℤ)) : ℕ × ℤ)
        ∈ triangle t''.1 t''.2.1 t''.2.2 := by
      refine ⟨le_refl _, htip t'' hs'' hw'', ?_⟩
      have hup : (t''.2.1 : ℝ) ≤ (lΔ : ℝ) + t''.2.2 / Real.log 2 + W := by
        have := (abs_le.mp hw'').2
        linarith
      have hdiff : (t''.2.1 : ℝ) - ((lΔ : ℝ) + ((s' / 2 : ℕ) : ℝ))
          ≤ t''.2.2 / Real.log 2 := by linarith
      have hkey : ((t''.2.1 : ℝ) - ((lΔ : ℝ) + ((s' / 2 : ℕ) : ℝ))) * Real.log 2
          ≤ t''.2.2 := by
        calc
          ((t''.2.1 : ℝ) - ((lΔ : ℝ) + ((s' / 2 : ℕ) : ℝ))) * Real.log 2
              ≤ (t''.2.2 / Real.log 2) * Real.log 2 :=
                mul_le_mul_of_nonneg_right hdiff hlog2.le
          _ = t''.2.2 := div_mul_cancel₀ _ hlog2.ne'
      show ((t''.1 : ℝ) - (t''.1 : ℝ)) * Real.log 9
          + ((t''.2.1 : ℝ) - ((lΔ + ((s' / 2 : ℕ) : ℤ) : ℤ) : ℝ)) * Real.log 2
          ≤ t''.2.2
      rw [Int.cast_add, Int.cast_natCast]
      have hzero : ((t''.1 : ℝ) - (t''.1 : ℝ)) * Real.log 9 = 0 := by ring
      linarith [hkey, hzero]
    have h765 : (t'.2.1 : ℝ) - ((lΔ : ℤ) : ℝ) ≤ t'.2.2 / Real.log 2 + W := by
      have := (abs_le.mp hw').2
      linarith
    have hgap := apex_separationP F ht' ht'' hne hj
      (lZ := lΔ) (δ := W) (s' := s') h765 (htip t' hs' hw') hmem''
    have hs'0 : (0 : ℝ) ≤ (s' : ℝ) := Nat.cast_nonneg _
    have hcoef : 0.48 * (s' : ℝ) ≤ ((s' / 2 : ℕ) : ℝ) - W := by
      linarith [hfl_ge]
    have hB : (s' : ℝ) * 0.33 ≤ (((s' / 2 : ℕ) : ℝ) - W) * Real.log 2 := by
      have h1 : (0.48 * (s' : ℝ)) * 0.6931471803
          ≤ (((s' / 2 : ℕ) : ℝ) - W) * Real.log 2 :=
        mul_le_mul hcoef hlog2lo.le (by norm_num) (by linarith)
      nlinarith
    have hA : (s' : ℝ) / 10 * Real.log 9 ≤ (s' : ℝ) * 0.24 := by
      have h1 : (s' : ℝ) / 10 * Real.log 9 ≤ (s' : ℝ) / 10 * 2.4 :=
        mul_le_mul_of_nonneg_left hlog9hi.le (by positivity)
      linarith
    have hfinal : (s' : ℝ) / 10 * Real.log 9 ≤
        ((t''.1 : ℝ) - (t'.1 : ℝ)) * Real.log 9 := by
      have := hgap
      nlinarith
    have := le_of_mul_le_mul_right
      (by linarith [hfinal] :
        (s' : ℝ) / 10 * Real.log 9 ≤ ((t''.1 : ℝ) - (t'.1 : ℝ)) * Real.log 9)
      hlog9pos
    linarith
  intro t' ht' t'' ht'' hne hs' hw' hs'' hw''
  rcases le_total t'.1 t''.1 with hj | hj
  · have h := core t' ht' t'' ht'' hne hj hs' hw' hs'' hw''
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h := core t'' ht'' t' ht' (Ne.symm hne) hj hs'' hw'' hs' hw'
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **Tilted X10b — the separated-band sum.**  This is the
fixed-law summation kernel with exactly two law-dependent substitutions:
the first-passage marginal is centred at `tilt * s / 2`, and the appended
walk has law `holdSumP tilt k`.  The integer-row and banded-`Gweight`
engines remain p-free. -/
theorem encounter_separated_sumP_core (cB C' K : ℝ)
    (_hcB : 0 < cB) (hC' : 0 < C') (hK : 0 < K)
    (hcol : ∀ (tilt : ℝ) (hp0 : 1 / 5 ≤ tilt) (hp1 : tilt ≤ 3 / 5), ∀ (s j : ℕ),
      ∑' l : ℤ, (fpDistP tilt (by linarith) (by linarith) s (j, l)).toReal
        ≤ C' * (TaoCollatz.Gweight (1 + (s : ℝ)) (cB * ((j : ℝ) - tilt / 2 * (s : ℝ)))
                  / Real.sqrt (1 + (s : ℝ))))
    (hband : ∀ t : ℝ, 1 ≤ t → ∀ μ : ℝ, ∀ D : ℝ, 2 ≤ D → ∀ W : ℝ, 1 ≤ W →
      ∀ S : Set ℤ, (∀ σ ∈ S, ∀ σ' ∈ S, σ ≠ σ' → D ≤ |(σ : ℝ) - (σ' : ℝ)|) →
      ∑' x : {x : ℤ | ∃ σ ∈ S, |(x : ℝ) - (σ : ℝ)| ≤ W},
          ENNReal.ofReal (TaoCollatz.Gweight t (cB * (((x : ℤ) : ℝ) - μ)))
        ≤ ENNReal.ofReal ((2 * W + 1)
            * (4 + K * Real.sqrt t / (⌊D / 2⌋₊ : ℝ)))) :
    ∀ (tilt : ℝ) (hp0 : 1 / 5 ≤ tilt) (hp1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ →
      ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l → 0 ≤ s →
      ∀ (k s' : ℕ) (W : ℝ), 1 ≤ W → 100 * W ≤ (s' : ℝ) →
      ((s' : ℝ)) ^ 2 ≤ 1 + (s : ℝ) →
      ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
          * Set.indicator {q : ℕ × ℤ | ∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
              ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
              ∧ |(q.1 : ℝ) - (t'.1 : ℝ)| ≤ W} 1 (j + e.1, l + e.2)
        ≤ (12 * C' + 120 * C' * K) * W / (s' : ℝ) := by
  classical
  intro tilt hp0 hp1 n ξ hξ F t₀ ht₀ j l hmemt₀ s hs _ k s' W hW hWs hreg
  set Event : Set (ℕ × ℤ) := {q : ℕ × ℤ | ∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
      ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
      ∧ |(q.1 : ℝ) - (t'.1 : ℝ)| ≤ W} with hEvent
  -- basic numerics
  have hs'100 : (100 : ℝ) ≤ (s' : ℝ) := le_trans (by linarith) hWs
  have hs'0 : (0 : ℝ) < (s' : ℝ) := by linarith
  have hsq1 : (1 : ℝ) ≤ 1 + (s : ℝ) := by
    have : (0 : ℝ) ≤ (s : ℕ) := Nat.cast_nonneg _
    linarith
  have hsqpos : (0 : ℝ) < Real.sqrt (1 + (s : ℝ)) :=
    Real.sqrt_pos.mpr (by linarith)
  have hs'sqrt : (s' : ℝ) ≤ Real.sqrt (1 + (s : ℝ)) := by
    rw [show (s' : ℝ) = Real.sqrt ((s' : ℝ) ^ 2) from (Real.sqrt_sq hs'0.le).symm]
    exact Real.sqrt_le_sqrt hreg
  -- the s'/10 separation constant and its floor bound
  set D : ℝ := (s' : ℝ) / 10 with hD
  have hD2 : (2 : ℝ) ≤ D := by rw [hD]; linarith
  have hfl40 : (s' : ℝ) / 40 ≤ (⌊D / 2⌋₊ : ℝ) := by
    have h1 : D / 2 - 1 < (⌊D / 2⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    rw [hD] at h1
    linarith
  have hfl0 : (0 : ℝ) < (⌊D / 2⌋₊ : ℝ) := by linarith
  -- the per-column envelope, ℝ≥0∞ form
  set G : ℕ → ℝ≥0∞ := fun x => ENNReal.ofReal (C' *
      (TaoCollatz.Gweight (1 + (s : ℝ)) (cB * ((x : ℝ) - tilt / 2 * (s : ℝ)))
        / Real.sqrt (1 + (s : ℝ)))) with hG
  have hcolE : ∀ x : ℕ, ∑' y : ℤ, fpDistP tilt (by linarith) (by linarith) s (x, y) ≤ G x := by
    intro x
    have hne : ∑' y : ℤ, fpDistP tilt (by linarith) (by linarith) s (x, y) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
      calc ∑' y : ℤ, fpDistP tilt (by linarith) (by linarith) s (x, y)
          ≤ ∑' e : ℕ × ℤ, fpDistP tilt (by linarith) (by linarith) s e :=
            ENNReal.tsum_comp_le_tsum_of_injective
              (fun a b hab => (Prod.mk.injEq _ _ _ _).mp hab |>.2 ▸ by
                cases hab; rfl) _
        _ = 1 := (fpDistP tilt (by linarith) (by linarith) s).tsum_coe
    rw [← ENNReal.ofReal_toReal hne]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [ENNReal.tsum_toReal_eq (fun y => PMF.apply_ne_top _ _)]
    exact hcol tilt hp0 hp1 s x
  -- the T ∈ ℝ≥0∞ reformulation of the LHS
  set T : ℝ≥0∞ :=
    ∑' e : ℕ × ℤ, (if (j + e.1, l + e.2) ∈ Event then fpDistPlusP tilt (by linarith) (by linarith) s k e else 0)
    with hT
  have hLHS : ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
      * Set.indicator Event 1 (j + e.1, l + e.2) = T.toReal := by
    rw [hT, ENNReal.tsum_toReal_eq (fun e => by
      split_ifs
      exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top])]
    refine tsum_congr fun e => ?_
    by_cases he : (j + e.1, l + e.2) ∈ Event
    · rw [if_pos he, Set.indicator_apply, if_pos he, Pi.one_apply, mul_one]
    · rw [if_neg he, Set.indicator_apply, if_neg he, mul_zero, ENNReal.toReal_zero]
  -- expand the convolution (the fpDistPlus_col_tail glue pattern)
  have hexp : T = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
      (if (j + (f + w).1, l + (f + w).2) ∈ Event
        then fpDistP tilt (by linarith) (by linarith) s f * holdSumP tilt (by linarith) (by linarith) k w else 0) := by
    rw [hT]
    have h1 : ∀ e : ℕ × ℤ,
        (if (j + e.1, l + e.2) ∈ Event then fpDistPlusP tilt (by linarith) (by linarith) s k e else 0)
        = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ), (if e = f + w then
            (if (j + e.1, l + e.2) ∈ Event
              then fpDistP tilt (by linarith) (by linarith) s f * holdSumP tilt (by linarith) (by linarith) k w else 0)
          else 0) := by
      intro e
      by_cases he : (j + e.1, l + e.2) ∈ Event
      · rw [if_pos he, fpDistPlusP, PMF.bind_apply]
        refine tsum_congr fun f => ?_
        rw [PMF.map_apply, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun w => ?_
        by_cases hew : e = f + w
        · rw [if_pos hew, if_pos hew, if_pos he]
        · rw [if_neg hew, if_neg hew, mul_zero]
      · rw [if_neg he]
        have hz : ∀ f w : ℕ × ℤ, (if e = f + w then
            (if (j + e.1, l + e.2) ∈ Event
              then fpDistP tilt (by linarith) (by linarith) s f * holdSumP tilt (by linarith) (by linarith) k w else 0)
          else 0) = 0 := by
          intro f w
          rw [if_neg he]
          exact ite_self 0
        symm
        simp only [hz, tsum_zero]
    calc ∑' e : ℕ × ℤ,
        (if (j + e.1, l + e.2) ∈ Event then fpDistPlusP tilt (by linarith) (by linarith) s k e else 0)
        = ∑' (e : ℕ × ℤ) (f : ℕ × ℤ) (w : ℕ × ℤ), (if e = f + w then
            (if (j + e.1, l + e.2) ∈ Event
              then fpDistP tilt (by linarith) (by linarith) s f * holdSumP tilt (by linarith) (by linarith) k w else 0)
          else 0) := tsum_congr h1
      _ = ∑' (f : ℕ × ℤ) (e : ℕ × ℤ) (w : ℕ × ℤ), (if e = f + w then
            (if (j + e.1, l + e.2) ∈ Event
              then fpDistP tilt (by linarith) (by linarith) s f * holdSumP tilt (by linarith) (by linarith) k w else 0)
          else 0) := ENNReal.tsum_comm
      _ = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ) (e : ℕ × ℤ), (if e = f + w then
            (if (j + e.1, l + e.2) ∈ Event
              then fpDistP tilt (by linarith) (by linarith) s f * holdSumP tilt (by linarith) (by linarith) k w else 0)
          else 0) := tsum_congr fun f => ENNReal.tsum_comm
      _ = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
            (if (j + (f + w).1, l + (f + w).2) ∈ Event
              then fpDistP tilt (by linarith) (by linarith) s f * holdSumP tilt (by linarith) (by linarith) k w else 0) := by
          refine tsum_congr fun f => tsum_congr fun w => ?_
          rw [tsum_eq_single (f + w) (fun e he => if_neg he), if_pos rfl]
  -- per Hold displacement w: the first-passage column mass over the band union
  have hinner : ∀ w : ℕ × ℤ,
      ∑' f : ℕ × ℤ, (if (j + (f + w).1, l + (f + w).2) ∈ Event
          then fpDistP tilt (by linarith) (by linarith) s f * holdSumP tilt (by linarith) (by linarith) k w else 0)
      ≤ holdSumP tilt (by linarith) (by linarith) k w * ENNReal.ofReal ((C' / Real.sqrt (1 + (s : ℝ)))
          * ((2 * W + 1) * (4 + K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)))) := by
    intro w
    -- membership depends on the column only
    have hmem_iff : ∀ f : ℕ × ℤ, ((j + (f + w).1, l + (f + w).2) ∈ Event
        ↔ (∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
            ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
            ∧ |((j + f.1 + w.1 : ℕ) : ℝ) - (t'.1 : ℝ)| ≤ W)) := by
      intro f
      rw [hEvent]
      constructor
      · rintro ⟨t', ht', h1, h2, h3⟩
        exact ⟨t', ht', h1, h2, by
          simpa [Prod.fst_add, Nat.add_assoc] using h3⟩
      · rintro ⟨t', ht', h1, h2, h3⟩
        exact ⟨t', ht', h1, h2, by
          simpa [Prod.fst_add, Nat.add_assoc] using h3⟩
    -- the qualifying-apex set, shifted by j + w.1
    set S : Set ℤ := {σ : ℤ | ∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
        ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
        ∧ (t'.1 : ℤ) - (j : ℤ) - (w.1 : ℤ) = σ} with hS
    have hSsep : ∀ σ ∈ S, ∀ σ' ∈ S, σ ≠ σ' → D ≤ |(σ : ℝ) - (σ' : ℝ)| := by
      rintro σ ⟨t', ht', h1, h2, hσ⟩ σ' ⟨t'', ht'', h1', h2', hσ'⟩ hne
      have hcolne : t'.1 ≠ t''.1 := by
        intro hcc
        apply hne
        omega
      have htne : t' ≠ t'' := fun hcc => hcolne (by rw [hcc])
      have := qualifying_apex_separatedP F t₀.2.1 s' W hW hWs
        t' ht' t'' ht'' htne h1 h2 h1' h2'
      have hval : (σ : ℝ) - (σ' : ℝ) = (t'.1 : ℝ) - (t''.1 : ℝ) := by
        have h4 : ((σ - σ' : ℤ) : ℝ) = (((t'.1 : ℤ) - (t''.1 : ℤ) : ℤ) : ℝ) := by
          congr 1
          omega
        push_cast at h4
        linarith
      rw [hD, hval]
      linarith
    -- the column condition puts the (integer) column in the W-band union of S
    have hcond_mem : ∀ x : ℕ,
        (∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
            ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
            ∧ |((j + x + w.1 : ℕ) : ℝ) - (t'.1 : ℝ)| ≤ W) →
        ((x : ℤ) ∈ {y : ℤ | ∃ σ ∈ S, |(y : ℝ) - (σ : ℝ)| ≤ W}) := by
      rintro x ⟨t', ht', h1, h2, h3⟩
      refine ⟨(t'.1 : ℤ) - (j : ℤ) - (w.1 : ℤ), ⟨t', ht', h1, h2, rfl⟩, ?_⟩
      have hcast : ((x : ℤ) : ℝ) - (((t'.1 : ℤ) - (j : ℤ) - (w.1 : ℤ) : ℤ) : ℝ)
          = ((j + x + w.1 : ℕ) : ℝ) - (t'.1 : ℝ) := by
        push_cast
        ring
      rw [hcast]
      exact h3
    -- pull the iid factor out and marginalise the first-passage law column-wise
    have hsum1 : ∑' f : ℕ × ℤ, (if (j + (f + w).1, l + (f + w).2) ∈ Event
        then fpDistP tilt (by linarith) (by linarith) s f * holdSumP tilt (by linarith) (by linarith) k w else 0)
        = holdSumP tilt (by linarith) (by linarith) k w * ∑' f : ℕ × ℤ,
            (if (j + (f + w).1, l + (f + w).2) ∈ Event then fpDistP tilt (by linarith) (by linarith) s f else 0) := by
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun f => ?_
      split_ifs
      · ring
      · rw [mul_zero]
    rw [hsum1]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    -- column marginal
    have hsum2 : ∑' f : ℕ × ℤ,
        (if (j + (f + w).1, l + (f + w).2) ∈ Event then fpDistP tilt (by linarith) (by linarith) s f else 0)
        ≤ ∑' x : ℕ, (if (x : ℤ) ∈ {y : ℤ | ∃ σ ∈ S, |(y : ℝ) - (σ : ℝ)| ≤ W}
            then G x else 0) := by
      rw [ENNReal.tsum_prod']
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : (∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
          ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
          ∧ |((j + x + w.1 : ℕ) : ℝ) - (t'.1 : ℝ)| ≤ W)
      · rw [if_pos (hcond_mem x hx)]
        calc ∑' y : ℤ, (if (j + ((x, y) + w).1, l + ((x, y) + w).2) ∈ Event
              then fpDistP tilt (by linarith) (by linarith) s (x, y) else 0)
            ≤ ∑' y : ℤ, fpDistP tilt (by linarith) (by linarith) s (x, y) :=
              ENNReal.tsum_le_tsum fun y => by
                split_ifs
                exacts [le_rfl, zero_le]
          _ ≤ G x := hcolE x
      · have hz : ∀ y : ℤ, (if (j + ((x, y) + w).1, l + ((x, y) + w).2) ∈ Event
            then fpDistP tilt (by linarith) (by linarith) s (x, y) else 0) = 0 := by
          intro y
          rw [if_neg (fun hc => hx ((hmem_iff (x, y)).mp hc))]
        rw [tsum_congr hz, tsum_zero]
        exact zero_le
    refine hsum2.trans ?_
    -- indicator → subtype over the band union, then the banded engine
    have hsub : ∑' x : ℕ, (if (x : ℤ) ∈ {y : ℤ | ∃ σ ∈ S, |(y : ℝ) - (σ : ℝ)| ≤ W}
        then G x else 0)
        ≤ ∑' u : {y : ℤ | ∃ σ ∈ S, |(y : ℝ) - (σ : ℝ)| ≤ W},
            ENNReal.ofReal (C' / Real.sqrt (1 + (s : ℝ)))
              * ENNReal.ofReal (TaoCollatz.Gweight (1 + (s : ℝ))
                  (cB * (((u : ℤ) : ℝ) - tilt / 2 * (s : ℝ)))) := by
      set A : Set ℕ := {x : ℕ | (x : ℤ) ∈ {y : ℤ | ∃ σ ∈ S, |(y : ℝ) - (σ : ℝ)| ≤ W}}
        with hA
      have hstep : ∑' x : ℕ, (if (x : ℤ) ∈ {y : ℤ | ∃ σ ∈ S, |(y : ℝ) - (σ : ℝ)| ≤ W}
          then G x else 0) = ∑' a : A, G a.1 := by
        rw [tsum_subtype A G]
        exact tsum_congr fun x => by
          rw [Set.indicator_apply]
          exact if_congr Iff.rfl rfl rfl
      rw [hstep]
      set φ : A → {y : ℤ | ∃ σ ∈ S, |(y : ℝ) - (σ : ℝ)| ≤ W} :=
        fun a => ⟨(a.1 : ℤ), a.2⟩ with hφ
      have hφinj : Function.Injective φ := by
        intro a b hab
        have : (a.1 : ℤ) = (b.1 : ℤ) := congrArg Subtype.val hab
        exact Subtype.ext (by exact_mod_cast this)
      have hval : ∀ a : A, G a.1
          = ENNReal.ofReal (C' / Real.sqrt (1 + (s : ℝ)))
            * ENNReal.ofReal (TaoCollatz.Gweight (1 + (s : ℝ))
                (cB * ((((φ a) : ℤ) : ℝ) - tilt / 2 * (s : ℝ)))) := by
        intro a
        rw [hG, ← ENNReal.ofReal_mul (by positivity)]
        have : (((φ a) : ℤ) : ℝ) = ((a.1 : ℕ) : ℝ) := by
          simp [hφ]
        rw [this]
        ring_nf
      calc ∑' a : A, G a.1
          = ∑' a : A, (ENNReal.ofReal (C' / Real.sqrt (1 + (s : ℝ)))
              * ENNReal.ofReal (TaoCollatz.Gweight (1 + (s : ℝ))
                  (cB * ((((φ a) : ℤ) : ℝ) - tilt / 2 * (s : ℝ))))) := tsum_congr hval
        _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hφinj _
    refine hsub.trans ?_
    rw [ENNReal.tsum_mul_left]
    calc ENNReal.ofReal (C' / Real.sqrt (1 + (s : ℝ)))
        * ∑' u : {y : ℤ | ∃ σ ∈ S, |(y : ℝ) - (σ : ℝ)| ≤ W},
            ENNReal.ofReal (TaoCollatz.Gweight (1 + (s : ℝ)) (cB * (((u : ℤ) : ℝ) - tilt / 2 * (s : ℝ))))
        ≤ ENNReal.ofReal (C' / Real.sqrt (1 + (s : ℝ)))
          * ENNReal.ofReal ((2 * W + 1)
              * (4 + K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          exact hband (1 + (s : ℝ)) hsq1 (tilt / 2 * (s : ℝ)) D hD2 W hW S hSsep
      _ = ENNReal.ofReal ((C' / Real.sqrt (1 + (s : ℝ)))
          * ((2 * W + 1) * (4 + K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  -- sum over the Hold displacement: total iid mass is 1
  have hTle : T ≤ ENNReal.ofReal ((C' / Real.sqrt (1 + (s : ℝ)))
      * ((2 * W + 1) * (4 + K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)))) := by
    rw [hexp, ENNReal.tsum_comm]
    calc ∑' (w : ℕ × ℤ) (f : ℕ × ℤ),
        (if (j + (f + w).1, l + (f + w).2) ∈ Event
          then fpDistP tilt (by linarith) (by linarith) s f * holdSumP tilt (by linarith) (by linarith) k w else 0)
        ≤ ∑' w : ℕ × ℤ, holdSumP tilt (by linarith) (by linarith) k w
            * ENNReal.ofReal ((C' / Real.sqrt (1 + (s : ℝ)))
              * ((2 * W + 1) * (4 + K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)))) :=
          ENNReal.tsum_le_tsum hinner
      _ = (∑' w : ℕ × ℤ, holdSumP tilt (by linarith) (by linarith) k w)
            * ENNReal.ofReal ((C' / Real.sqrt (1 + (s : ℝ)))
              * ((2 * W + 1) * (4 + K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)))) :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal ((C' / Real.sqrt (1 + (s : ℝ)))
            * ((2 * W + 1) * (4 + K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)))) := by
          rw [(holdSumP tilt (by linarith) (by linarith) k).tsum_coe, one_mul]
  -- final numeric bookkeeping
  have hnum : (C' / Real.sqrt (1 + (s : ℝ)))
      * ((2 * W + 1) * (4 + K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)))
      ≤ (12 * C' + 120 * C' * K) * W / (s' : ℝ) := by
    have h2W : 2 * W + 1 ≤ 3 * W := by linarith
    have hinv : 1 / Real.sqrt (1 + (s : ℝ)) ≤ 1 / (s' : ℝ) :=
      one_div_le_one_div_of_le hs'0 hs'sqrt
    have hfli : K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)
        ≤ 40 * K * Real.sqrt (1 + (s : ℝ)) / (s' : ℝ) := by
      rw [div_le_div_iff₀ hfl0 hs'0]
      have := mul_le_mul_of_nonneg_left hfl40
        (by positivity : (0 : ℝ) ≤ 40 * (K * Real.sqrt (1 + (s : ℝ))))
      nlinarith [hfl40, mul_nonneg hK.le hsqpos.le]
    -- expand: LHS ≤ (C'/√)·3W·4 + (C'/√)·3W·(40K√/s')
    have hsqinv : C' / Real.sqrt (1 + (s : ℝ)) ≤ C' / (s' : ℝ) := by
      rw [div_le_div_iff₀ hsqpos hs'0]
      nlinarith [hs'sqrt, hC'.le]
    have hterm1 : (C' / Real.sqrt (1 + (s : ℝ))) * ((2 * W + 1) * 4)
        ≤ 12 * C' * W / (s' : ℝ) := by
      have h1 : (C' / Real.sqrt (1 + (s : ℝ))) * ((2 * W + 1) * 4)
          ≤ (C' / (s' : ℝ)) * (3 * W * 4) := by
        refine mul_le_mul hsqinv (by linarith) (by positivity) (by positivity)
      calc (C' / Real.sqrt (1 + (s : ℝ))) * ((2 * W + 1) * 4)
          ≤ (C' / (s' : ℝ)) * (3 * W * 4) := h1
        _ = 12 * C' * W / (s' : ℝ) := by ring
    have hterm2 : (C' / Real.sqrt (1 + (s : ℝ)))
        * ((2 * W + 1) * (K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)))
        ≤ 120 * C' * K * W / (s' : ℝ) := by
      have h1 : (2 * W + 1) * (K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ))
          ≤ 3 * W * (40 * K * Real.sqrt (1 + (s : ℝ)) / (s' : ℝ)) := by
        refine mul_le_mul h2W hfli (by positivity) (by positivity)
      have h2 : (C' / Real.sqrt (1 + (s : ℝ)))
          * (3 * W * (40 * K * Real.sqrt (1 + (s : ℝ)) / (s' : ℝ)))
          = 120 * C' * K * W / (s' : ℝ)
            * (Real.sqrt (1 + (s : ℝ)) / Real.sqrt (1 + (s : ℝ))) := by
        field_simp
        ring
      calc (C' / Real.sqrt (1 + (s : ℝ)))
          * ((2 * W + 1) * (K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)))
          ≤ (C' / Real.sqrt (1 + (s : ℝ)))
            * (3 * W * (40 * K * Real.sqrt (1 + (s : ℝ)) / (s' : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 120 * C' * K * W / (s' : ℝ)
            * (Real.sqrt (1 + (s : ℝ)) / Real.sqrt (1 + (s : ℝ))) := h2
        _ = 120 * C' * K * W / (s' : ℝ) := by
            rw [div_self hsqpos.ne', mul_one]
    calc (C' / Real.sqrt (1 + (s : ℝ)))
        * ((2 * W + 1) * (4 + K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ)))
        = (C' / Real.sqrt (1 + (s : ℝ))) * ((2 * W + 1) * 4)
          + (C' / Real.sqrt (1 + (s : ℝ)))
            * ((2 * W + 1) * (K * Real.sqrt (1 + (s : ℝ)) / (⌊D / 2⌋₊ : ℝ))) := by
          ring
      _ ≤ 12 * C' * W / (s' : ℝ) + 120 * C' * K * W / (s' : ℝ) :=
          add_le_add hterm1 hterm2
      _ = (12 * C' + 120 * C' * K) * W / (s' : ℝ) := by ring
  rw [hLHS]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  exact hTle.trans (ENNReal.ofReal_le_ofReal hnum)

/-- Uniform constant for the tilted separated-band estimate. -/
noncomputable def C_encSepP : ℝ :=
  12 * C_fpColP +
    120 * C_fpColP * TaoCollatz.K_intG c_fpLocationP

theorem C_encSepP_pos : 0 < C_encSepP := by
  have h1 := C_fpColP_pos
  have h2 := TaoCollatz.K_intG_pos c_fpLocationP_pos
  unfold C_encSepP
  nlinarith

/-- Explicit-constant interface for tilted X10b.  Its constants are selected
before the Pascal parameter. -/
theorem encounter_separated_sumP_explicitC :
    ∀ (tilt : ℝ) (hp0 : 1 / 5 ≤ tilt) (hp1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l → 0 ≤ s →
      ∀ (k s' : ℕ) (W : ℝ), 1 ≤ W → 100 * W ≤ (s' : ℝ) →
      ((s' : ℝ)) ^ 2 ≤ 1 + (s : ℝ) →
      ∑' e : ℕ × ℤ,
          (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
            * Set.indicator {q : ℕ × ℤ | ∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
                ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
                ∧ |(q.1 : ℝ) - (t'.1 : ℝ)| ≤ W} 1 (j + e.1, l + e.2)
        ≤ C_encSepP * W / (s' : ℝ) := by
  have h := encounter_separated_sumP_core
    c_fpLocationP C_fpColP (TaoCollatz.K_intG c_fpLocationP)
    c_fpLocationP_pos C_fpColP_pos
    (TaoCollatz.K_intG_pos c_fpLocationP_pos)
    (fun tilt hp0 hp1 =>
      fpDistP_col_le_explicitC tilt (by linarith) (by linarith) hp0 hp1)
    (TaoCollatz.banded_Gweight_tsum_le_explicitC c_fpLocationP_pos)
  unfold C_encSepP
  exact h

/-- **Tilted X10b — separated encounter bands.**  Uniformly over the Pascal
window, the endpoint mass in qualifying `W`-bands is `O(W/s')`. -/
theorem encounter_separated_sumP :
    ∃ C₃ > (0 : ℝ), ∃ S₀ : ℕ,
      ∀ (tilt : ℝ) (hp0 : 1 / 5 ≤ tilt) (hp1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l → S₀ ≤ s →
      ∀ (k s' : ℕ) (W : ℝ), 1 ≤ W → 100 * W ≤ (s' : ℝ) →
      ((s' : ℝ)) ^ 2 ≤ 1 + (s : ℝ) →
      ∑' e : ℕ × ℤ,
          (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
            * Set.indicator {q : ℕ × ℤ | ∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
                ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
                ∧ |(q.1 : ℝ) - (t'.1 : ℝ)| ≤ W} 1 (j + e.1, l + e.2)
        ≤ C₃ * W / (s' : ℝ) :=
  ⟨C_encSepP, C_encSepP_pos, 0, encounter_separated_sumP_explicitC⟩

/-! ### Tilted Lemma 7.10 assembly -/

/-- The union of the finer-family triangles whose size is at least `s'`. -/
def bigTriangleSetP {n ξ : ℕ} (F : TriangleFamilyP n ξ) (s' : ℕ) :
    Set (ℕ × ℤ) :=
  {q | ∃ t ∈ F.T, (s' : ℝ) ≤ t.2.2 ∧ q ∈ triangle t.1 t.2.1 t.2.2}

/-- Endpoints of the tilted post-first-passage law sit strictly above the
budget row.  The first-passage endpoint overshoots `s`, and every appended
holding increment has nonnegative height. -/
theorem fpDistPlusP_support_snd_gt (tilt : ℝ) (htilt0 : 0 < tilt)
    (htilt1 : tilt < 1) (s k : ℕ) (e : ℕ × ℤ)
    (he : fpDistPlusP tilt htilt0 htilt1 s k e ≠ 0) : (s : ℤ) < e.2 := by
  have hmem : e ∈ (fpDistPlusP tilt htilt0 htilt1 s k).support := by
    rwa [PMF.mem_support_iff]
  rw [fpDistPlusP, PMF.mem_support_bind_iff] at hmem
  obtain ⟨f, hf, hfe⟩ := hmem
  rw [PMF.mem_support_map_iff] at hfe
  obtain ⟨w, hw, hwe⟩ := hfe
  have h1 : (s : ℤ) < f.2 := fpDistP_support_snd_gt tilt htilt0 htilt1 s f hf
  have h2 : 0 ≤ w.2 := by
    rw [holdSumP_eq_iidSum, TaoCollatz.iidSum, PMF.mem_support_map_iff] at hw
    obtain ⟨v, hv, hvw⟩ := hw
    have hco : ∀ i, 3 ≤ (v i).2 := fun i =>
      holdP_support_snd_ge tilt htilt0 htilt1 (v i)
        (PMF.iid_support_coord (holdP tilt htilt0 htilt1) k v hv i)
    have hsnd : w.2 = ∑ i, (v i).2 := by
      rw [← hvw, Prod.snd_sum]
    rw [hsnd]
    exact Finset.sum_nonneg fun i _ => le_trans (by norm_num) (hco i)
  have h3 : e.2 = f.2 + w.2 := by rw [← hwe]; rfl
  omega

-- HEARTBEAT: the direct tilted port retains the fixed-law proof's long
-- indicator split and real-exponential bookkeeping.
set_option maxHeartbeats 2000000 in
/-- **Tilted Lemma 7.10, rpow-form assembly.**  The constants are
uniform over the Pascal window.  Relative to the fixed-law kernel, the escape
tails require the stronger admissibility margin `10000 * (1+k)`; the uniform
choice `A₀ = 100` supplies it for both height and column escapes. -/
theorem triangle_encounter_le_rpowP_core
    (ch Ch cc Cc C₂ C₃ : ℝ) (S₀a S₀b : ℕ)
    (hch : 0 < ch) (hCh : 0 < Ch) (hcc : 0 < cc) (hCc : 0 < Cc)
    (hC₂ : 1 ≤ C₂) (hC₃ : 0 < C₃)
    (hheight : ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ s k : ℕ, ∀ H : ℝ, 10000 * (1 + (k : ℝ)) ≤ H →
      ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
          * Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} 1 e
        ≤ Ch * Real.exp (-ch * H))
    (hcolT : ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ s k : ℕ, ∀ D : ℝ, 10000 * (1 + (k : ℝ)) ≤ D →
      ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
          * Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - tilt / 2 * (s : ℝ)|} 1 e
        ≤ Cc * (Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cc * D)))
    (hX10a : ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l → S₀a ≤ s →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (A : ℝ), 5 ≤ A → ∀ (k s' : ℕ),
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
        100 * A ^ 2 * (1 + (k : ℝ)) ≤ (s' : ℝ) →
      ∀ e : ℕ × ℤ, (s : ℤ) < e.2 →
        (e.2 : ℝ) ≤ (s : ℝ) + 2 * A ^ 2 * (1 + (k : ℝ)) →
        |(e.1 : ℝ) - tilt / 2 * (s : ℝ)| ≤ 2 * (s : ℝ) ^ (0.6 : ℝ) →
      ∀ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2 →
        ((j + e.1, l + e.2) : ℕ × ℤ) ∈ triangle t'.1 t'.2.1 t'.2.2 →
      (t'.1 : ℝ) ≤ (j : ℝ) + e.1
        ∧ (j : ℝ) + e.1 - t'.1 ≤ C₂ * A ^ 2 * (1 + (k : ℝ))
        ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)|
            ≤ C₂ * A ^ 2 * (1 + (k : ℝ)))
    (hX10b : ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l → S₀b ≤ s →
      ∀ (k s' : ℕ) (W : ℝ), 1 ≤ W → 100 * W ≤ (s' : ℝ) →
      ((s' : ℝ)) ^ 2 ≤ 1 + (s : ℝ) →
      ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
          * Set.indicator {q : ℕ × ℤ | ∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
              ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
              ∧ |(q.1 : ℝ) - (t'.1 : ℝ)| ≤ W} 1 (j + e.1, l + e.2)
        ≤ C₃ * W / (s' : ℝ)) :
    ∀ (A : ℝ), 100 ≤ A →
      ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (k s' : ℕ), 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
      ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
          * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (j + e.1, l + e.2)
        ≤ (100 * C₂
            + Real.exp (ch * ((max (10 ^ 27) ((S₀a + S₀b + 1) ^ 2) : ℕ) : ℝ)) + Ch
            + 432 * Cc / cc ^ 3 + C₃ * C₂) * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
          + (100 * C₂
            + Real.exp (ch * ((max (10 ^ 27) ((S₀a + S₀b + 1) ^ 2) : ℕ) : ℝ)) + Ch
            + 432 * Cc / cc ^ 3 + C₃ * C₂)
            * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ))) := by
  classical
  set Mth : ℕ := max (10 ^ 27) ((S₀a + S₀b + 1) ^ 2) with hMth
  set C : ℝ := 100 * C₂ + Real.exp (ch * (Mth : ℝ)) + Ch
      + 432 * Cc / cc ^ 3 + C₃ * C₂ with hC
  intro A hA tilt htilt0 htilt1 n ξ hξ F t₀ ht₀ j l hmemt₀ s hs hdeep k s' hs'1 hs'm
  -- shared numerics
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hAp25 : (25 : ℝ) ≤ A ^ 2 * (1 + (k : ℝ)) := by nlinarith
  have hAp0 : (0 : ℝ) < A ^ 2 * (1 + (k : ℝ)) := by nlinarith
  have hs'0 : (0 : ℝ) < (s' : ℝ) := by exact_mod_cast hs'1
  have hexp_pos : (0 : ℝ) < Real.exp (-ch * A ^ 2 * (1 + (k : ℝ))) := Real.exp_pos _
  have hLHS1 : ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
      * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (j + e.1, l + e.2)
      ≤ 1 := fpDistPlusP_indicator_sum_le_one tilt (by linarith) (by linarith) s k _ _
  -- Branch 1: s' below the working threshold — the 1/s' term is ≥ 1
  by_cases hbr1 : (s' : ℝ) < 100 * C₂ * (A ^ 2 * (1 + (k : ℝ)))
  · have h1 : (1 : ℝ) ≤ C * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ) := by
      rw [le_div_iff₀ hs'0]
      have hCge : 100 * C₂ ≤ C := by
        have := Real.exp_pos (ch * (Mth : ℝ))
        have h2 : (0 : ℝ) < 432 * Cc / cc ^ 3 := by positivity
        nlinarith [mul_pos hC₃ (lt_of_lt_of_le one_pos hC₂)]
      nlinarith [hbr1, hAp0, mul_le_mul_of_nonneg_right hCge hAp0.le]
    have h2 : (0 : ℝ) ≤ C * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ))) := by positivity
    linarith [hLHS1]
  push Not at hbr1
  -- from here on: 100·C₂·A²(1+k) ≤ s'
  have hbigA : 100 * A ^ 2 * (1 + (k : ℝ)) ≤ (s' : ℝ) := by
    have h1 : 100 * (A ^ 2 * (1 + (k : ℝ))) ≤ 100 * C₂ * (A ^ 2 * (1 + (k : ℝ))) := by
      nlinarith [hAp0]
    linarith
  set m : ℕ := n / 2 - j with hm
  have hm1 : 1 ≤ m := by
    by_contra hlt
    push Not at hlt
    have hm0 : m = 0 := by omega
    have : (s' : ℝ) ≤ 0 := by
      rw [hm0] at hs'm
      simpa [Real.zero_rpow (by norm_num : (0.4 : ℝ) ≠ 0)] using hs'm
    linarith
  have hm0R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  -- Branch 2: shallow m — the exp term is ≥ 1
  by_cases hbr2 : m < Mth
  · have hApM : A ^ 2 * (1 + (k : ℝ)) ≤ (Mth : ℝ) := by
      have h1 : A ^ 2 * (1 + (k : ℝ)) ≤ (s' : ℝ) / 100 := by linarith
      have h2 : (m : ℝ) ^ (0.4 : ℝ) ≤ (m : ℝ) := by
        calc (m : ℝ) ^ (0.4 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hm1R (by norm_num)
          _ = (m : ℝ) := Real.rpow_one _
      have h3 : (m : ℝ) ≤ (Mth : ℝ) := by
        have : m ≤ Mth := le_of_lt hbr2
        exact_mod_cast this
      have h4 : (s' : ℝ) / 100 ≤ (s' : ℝ) := by linarith
      linarith [hs'm]
    have h1 : (1 : ℝ) ≤ C * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ))) := by
      have hCge : Real.exp (ch * (Mth : ℝ)) ≤ C := by
        have h2 : (0 : ℝ) < 432 * Cc / cc ^ 3 := by positivity
        nlinarith [mul_pos hC₃ (lt_of_lt_of_le one_pos hC₂),
          mul_pos (lt_of_lt_of_le one_pos hC₂) (by norm_num : (0:ℝ) < 100)]
      have h2 : Real.exp (ch * (Mth : ℝ)) * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ)))
          = Real.exp (ch * ((Mth : ℝ) - A ^ 2 * (1 + (k : ℝ)))) := by
        rw [← Real.exp_add]
        ring_nf
      have h3 : (1 : ℝ) ≤ Real.exp (ch * ((Mth : ℝ) - A ^ 2 * (1 + (k : ℝ)))) := by
        calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp (ch * ((Mth : ℝ) - A ^ 2 * (1 + (k : ℝ)))) :=
              Real.exp_le_exp.mpr (by nlinarith [hApM])
      calc (1 : ℝ) ≤ Real.exp (ch * ((Mth : ℝ) - A ^ 2 * (1 + (k : ℝ)))) := h3
        _ = Real.exp (ch * (Mth : ℝ)) * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ))) :=
            h2.symm
        _ ≤ C * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ))) :=
            mul_le_mul_of_nonneg_right hCge hexp_pos.le
    have h2 : (0 : ℝ) ≤ C * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ) := by positivity
    linarith [hLHS1]
  push Not at hbr2
  -- MAIN BRANCH: m ≥ Mth ≥ 10²⁷ — the deep regime
  have hM27 : (10 : ℝ) ^ (27 : ℕ) ≤ (m : ℝ) := by
    have h1 : (10 : ℕ) ^ 27 ≤ Mth := le_max_left _ _
    have h2 : Mth ≤ m := hbr2
    have : (10 : ℕ) ^ 27 ≤ m := le_trans h1 h2
    exact_mod_cast this
  have hsdeep : (m : ℝ) ^ (0.8 : ℝ) < (s : ℝ) := hdeep
  have hs0 : (0 : ℝ) < (s : ℝ) := by
    have : (0 : ℝ) < (m : ℝ) ^ (0.8 : ℝ) := Real.rpow_pos_of_pos hm0R _
    linarith
  have hm08ge1 : (1 : ℝ) ≤ (m : ℝ) ^ (0.8 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (0.8 : ℝ) := (Real.one_rpow _).symm
      _ ≤ (m : ℝ) ^ (0.8 : ℝ) := Real.rpow_le_rpow (by norm_num) hm1R (by norm_num)
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := le_trans hm08ge1 hsdeep.le
  -- s dominates both abstract thresholds S₀a, S₀b
  have hk2 : ((S₀a + S₀b + 1 : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) := by
    have h1 : (S₀a + S₀b + 1) ^ 2 ≤ Mth := le_max_right _ _
    have h2 : (S₀a + S₀b + 1) ^ 2 ≤ m := le_trans h1 hbr2
    exact_mod_cast h2
  have hk_le_s : ((S₀a + S₀b + 1 : ℕ) : ℝ) ≤ (s : ℝ) := by
    set k : ℝ := ((S₀a + S₀b + 1 : ℕ) : ℝ) with hk
    have hk1 : (1 : ℝ) ≤ k := by
      rw [hk]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have h1 : k ^ 2 ≤ (m : ℝ) := hk2
    have h2 : (k ^ 2 : ℝ) ^ (0.8 : ℝ) ≤ (m : ℝ) ^ (0.8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : k ≤ (k ^ 2 : ℝ) ^ (0.8 : ℝ) := by
      have h4 : (k ^ 2 : ℝ) ^ (0.8 : ℝ) = k ^ (1.6 : ℝ) := by
        rw [← Real.rpow_natCast k 2, ← Real.rpow_mul (by linarith)]
        norm_num
      rw [h4]
      calc k = k ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ k ^ (1.6 : ℝ) := Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
    linarith [hsdeep]
  have hS₀a_le : S₀a ≤ s := by
    have h1 : ((S₀a : ℕ) : ℝ) ≤ (s : ℝ) := by
      have : ((S₀a : ℕ) : ℝ) ≤ ((S₀a + S₀b + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right _ _ |>.trans (Nat.le_succ _)
      linarith [hk_le_s]
    exact_mod_cast h1
  have hS₀b_le : S₀b ≤ s := by
    have h1 : ((S₀b : ℕ) : ℝ) ≤ (s : ℝ) := by
      have : ((S₀b : ℕ) : ℝ) ≤ ((S₀a + S₀b + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_add_left _ _).trans (Nat.le_succ _)
      linarith [hk_le_s]
    exact_mod_cast h1
  -- the X10b regime: s'² ≤ 1 + s
  have hreg : (s' : ℝ) ^ 2 ≤ 1 + (s : ℝ) := by
    have h1 : (s' : ℝ) ^ 2 ≤ ((m : ℝ) ^ (0.4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hs'm 2
    have h2 : ((m : ℝ) ^ (0.4 : ℝ)) ^ 2 = (m : ℝ) ^ (0.8 : ℝ) := by
      rw [← Real.rpow_natCast ((m : ℝ) ^ (0.4 : ℝ)) 2, ← Real.rpow_mul hm0R.le]
      norm_num
    linarith [hsdeep]
  -- the col-tail admissibility: 10000(1+k) ≤ s^{0.6}
  have hm048 : (m : ℝ) ^ (0.4 : ℝ) ≤ (s : ℝ) ^ (0.6 : ℝ) := by
    have h1 : (m : ℝ) ^ (0.4 : ℝ) ≤ (m : ℝ) ^ (0.48 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hm1R (by norm_num)
    have h2 : (m : ℝ) ^ (0.48 : ℝ) = ((m : ℝ) ^ (0.8 : ℝ)) ^ (0.6 : ℝ) := by
      rw [← Real.rpow_mul hm0R.le]
      norm_num
    have h3 : ((m : ℝ) ^ (0.8 : ℝ)) ^ (0.6 : ℝ) ≤ (s : ℝ) ^ (0.6 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hm0R.le _) hsdeep.le (by norm_num)
    linarith
  have h10000A : (10000 : ℝ) ≤ A ^ 2 := by
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hA 2
    norm_num at hsq
    exact hsq
  have h10000k : 10000 * (1 + (k : ℝ)) ≤ (s : ℝ) ^ (0.6 : ℝ) := by
    have hfac : (0 : ℝ) ≤ 1 + (k : ℝ) := by linarith
    have h1 : 10000 * (1 + (k : ℝ)) ≤ A ^ 2 * (1 + (k : ℝ)) :=
      mul_le_mul_of_nonneg_right h10000A hfac
    have hscale : A ^ 2 * (1 + (k : ℝ)) ≤
        100 * (A ^ 2 * (1 + (k : ℝ))) := by
      nlinarith [hAp0]
    have h2 : 100 * (A ^ 2 * (1 + (k : ℝ))) ≤ (s' : ℝ) := by
      linarith only [hbigA]
    have h3 : (s' : ℝ) ≤ (s : ℝ) ^ (0.6 : ℝ) := le_trans hs'm hm048
    exact h1.trans (hscale.trans (h2.trans h3))
  -- the working window
  set W : ℝ := C₂ * A ^ 2 * (1 + (k : ℝ)) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hWdef, mul_assoc]
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ C₂ * (A ^ 2 * (1 + (k : ℝ))) :=
          mul_le_mul hC₂ (by linarith only [hAp25]) (by norm_num)
            (by linarith only [hC₂])
  have h100W : 100 * W ≤ (s' : ℝ) := by
    rw [hWdef]
    calc 100 * (C₂ * A ^ 2 * (1 + (k : ℝ)))
        = 100 * C₂ * (A ^ 2 * (1 + (k : ℝ))) := by ring
      _ ≤ (s' : ℝ) := hbr1
  -- the three events
  set hEsc : Set (ℕ × ℤ) := {q : ℕ × ℤ | (s : ℝ) + 2 * A ^ 2 * (1 + (k : ℝ)) ≤ (q.2 : ℝ)}
    with hhEsc
  set cEsc : Set (ℕ × ℤ) := {q : ℕ × ℤ | 2 * (s : ℝ) ^ (0.6 : ℝ) ≤ |(q.1 : ℝ) - tilt / 2 * (s : ℝ)|}
    with hcEsc
  set Ev : Set (ℕ × ℤ) := {q : ℕ × ℤ | ∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
      ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
      ∧ |(q.1 : ℝ) - (t'.1 : ℝ)| ≤ W} with hEv
  -- the pointwise indicator split (uses the support fact and X10a)
  have hsplit : ∀ e : ℕ × ℤ,
      (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
        * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (j + e.1, l + e.2)
      ≤ (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator hEsc 1 e
        + (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator cEsc 1 e
        + (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator Ev 1 (j + e.1, l + e.2) := by
    intro e
    set μe : ℝ := (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal with hμe
    have hμe0 : 0 ≤ μe := ENNReal.toReal_nonneg
    have hind_nonneg : ∀ (S : Set (ℕ × ℤ)) (q : ℕ × ℤ),
        (0 : ℝ) ≤ Set.indicator S (1 : ℕ × ℤ → ℝ) q :=
      fun S q => Set.indicator_nonneg (fun _ _ => zero_le_one) q
    by_cases hz : fpDistPlusP tilt (by linarith) (by linarith) s k e = 0
    · have hμz : μe = 0 := by rw [hμe, hz, ENNReal.toReal_zero]
      rw [hμz]
      simp
    by_cases hbig : (j + e.1, l + e.2) ∈ bigTriangleSetP F s'
    swap
    · rw [Set.indicator_of_notMem hbig, mul_zero]
      have h2 := mul_nonneg hμe0 (hind_nonneg hEsc e)
      have h3 := mul_nonneg hμe0 (hind_nonneg cEsc e)
      have h4 := mul_nonneg hμe0 (hind_nonneg Ev (j + e.1, l + e.2))
      linarith
    by_cases hH : (s : ℝ) + 2 * A ^ 2 * (1 + (k : ℝ)) ≤ ((e.2 : ℤ) : ℝ)
    · have h1 : e ∈ hEsc := hH
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem hbig]
      have h2 : (0 : ℝ) ≤ μe * Set.indicator cEsc 1 e :=
        mul_nonneg hμe0 (hind_nonneg _ _)
      have h3 : (0 : ℝ) ≤ μe * Set.indicator Ev 1 (j + e.1, l + e.2) :=
        mul_nonneg hμe0 (hind_nonneg _ _)
      simp only [Pi.one_apply]
      linarith
    by_cases hCc : 2 * (s : ℝ) ^ (0.6 : ℝ) ≤ |((e.1 : ℕ) : ℝ) - tilt / 2 * (s : ℝ)|
    · have h1 : e ∈ cEsc := hCc
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem hbig]
      have h2 : (0 : ℝ) ≤ μe * Set.indicator hEsc 1 e :=
        mul_nonneg hμe0 (hind_nonneg _ _)
      have h3 : (0 : ℝ) ≤ μe * Set.indicator Ev 1 (j + e.1, l + e.2) :=
        mul_nonneg hμe0 (hind_nonneg _ _)
      simp only [Pi.one_apply]
      linarith
    -- X10a: confinement to the proximity event
    push Not at hH hCc
    have hbigmem := hbig
    obtain ⟨t', ht', hsize, hmem'⟩ := hbig
    have he2 : (s : ℤ) < e.2 := fpDistPlusP_support_snd_gt tilt (by linarith) (by linarith) s k e hz
    have hprox := hX10a tilt htilt0 htilt1 n ξ hξ F t₀ ht₀ j l hmemt₀ s hs hS₀a_le hdeep A
      (by linarith : 5 ≤ A) k s' hs'm hbigA e he2 hH.le hCc.le t' ht' hsize hmem'
    obtain ⟨hp1, hp2, hp3⟩ := hprox
    have hmemEv : (j + e.1, l + e.2) ∈ Ev := by
      refine ⟨t', ht', hsize, hp3, ?_⟩
      have hcast : (((j + e.1 : ℕ)) : ℝ) = (j : ℝ) + (e.1 : ℝ) := by push_cast; ring
      rw [show ((j + e.1, l + e.2) : ℕ × ℤ).1 = j + e.1 from rfl, hcast,
        abs_of_nonneg (by linarith)]
      exact hp2
    rw [Set.indicator_of_mem hmemEv, Set.indicator_of_mem hbigmem]
    have h2 : (0 : ℝ) ≤ μe * Set.indicator hEsc 1 e :=
      mul_nonneg hμe0 (hind_nonneg _ _)
    have h3 : (0 : ℝ) ≤ μe * Set.indicator cEsc 1 e :=
      mul_nonneg hμe0 (hind_nonneg _ _)
    simp only [Pi.one_apply]
    linarith
  -- summabilities (all four indicator sums are dominated by the PMF mass)
  have hsummable : ∀ (S : Set (ℕ × ℤ)) (f : ℕ × ℤ → ℕ × ℤ),
      Summable (fun e : ℕ × ℤ => (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
        * Set.indicator S (1 : ℕ × ℤ → ℝ) (f e)) := by
    intro S f
    have hsum : Summable (fun e : ℕ × ℤ => (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal) :=
      ENNReal.summable_toReal
        (by rw [(fpDistPlusP tilt (by linarith) (by linarith) s k).tsum_coe]; exact ENNReal.one_ne_top)
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (fun e => ?_) hsum
    refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
    by_cases h : f e ∈ S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  -- the three tail bounds
  have hbound1 : ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator hEsc 1 e
      ≤ Ch * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ))) := by
    have h1 := hheight tilt htilt0 htilt1 s k (2 * A ^ 2 * (1 + (k : ℝ))) (by nlinarith)
    refine le_trans h1 ?_
    have h2 : ch * (A ^ 2 * (1 + (k : ℝ))) ≤ ch * (2 * A ^ 2 * (1 + (k : ℝ))) := by
      nlinarith
    have h3 : Real.exp (-(ch * (2 * A ^ 2 * (1 + (k : ℝ)))))
        ≤ Real.exp (-(ch * (A ^ 2 * (1 + (k : ℝ))))) :=
      Real.exp_le_exp.mpr (by linarith)
    calc Ch * Real.exp (-ch * (2 * A ^ 2 * (1 + (k : ℝ))))
        = Ch * Real.exp (-(ch * (2 * A ^ 2 * (1 + (k : ℝ))))) := by ring_nf
      _ ≤ Ch * Real.exp (-(ch * (A ^ 2 * (1 + (k : ℝ))))) :=
          mul_le_mul_of_nonneg_left h3 hCh.le
      _ = Ch * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ))) := by ring_nf
  have hbound2 : ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator cEsc 1 e
      ≤ (432 * Cc / cc ^ 3) * (A ^ 2 * (1 + (k : ℝ))) / (s' : ℝ) := by
    have h1 := hcolT tilt htilt0 htilt1 s k ((s : ℝ) ^ (0.6 : ℝ)) h10000k
    refine le_trans h1 ?_
    -- both exponential terms are ≤ exp(−(cc/2)·s^{0.2})
    have hs02pos : (0 : ℝ) < (s : ℝ) ^ (0.2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    have hs06pos : (0 : ℝ) < (s : ℝ) ^ (0.6 : ℝ) := Real.rpow_pos_of_pos hs0 _
    have hterm1 : Real.exp (-cc * ((s : ℝ) ^ (0.6 : ℝ)) ^ 2 / (1 + (s : ℝ)))
        ≤ Real.exp (-(cc / 2 * (s : ℝ) ^ (0.2 : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      have h12 : ((s : ℝ) ^ (0.6 : ℝ)) ^ 2 = (s : ℝ) ^ (0.2 : ℝ) * (s : ℝ) := by
        have ha : ((s : ℝ) ^ (0.6 : ℝ)) ^ 2 = (s : ℝ) ^ (1.2 : ℝ) := by
          rw [← Real.rpow_natCast ((s : ℝ) ^ (0.6 : ℝ)) 2, ← Real.rpow_mul hs0.le]
          norm_num
        have hb : (s : ℝ) ^ (1.2 : ℝ) = (s : ℝ) ^ (0.2 : ℝ) * (s : ℝ) ^ (1 : ℝ) := by
          rw [← Real.rpow_add hs0]
          norm_num
        rw [ha, hb, Real.rpow_one]
      have h2s : 1 + (s : ℝ) ≤ 2 * (s : ℝ) := by linarith
      have hkey : cc / 2 * (s : ℝ) ^ (0.2 : ℝ)
          ≤ cc * ((s : ℝ) ^ (0.6 : ℝ)) ^ 2 / (1 + (s : ℝ)) := by
        rw [h12, le_div_iff₀ (by linarith : (0 : ℝ) < 1 + (s : ℝ))]
        calc cc / 2 * (s : ℝ) ^ (0.2 : ℝ) * (1 + (s : ℝ))
            ≤ cc / 2 * (s : ℝ) ^ (0.2 : ℝ) * (2 * (s : ℝ)) :=
              mul_le_mul_of_nonneg_left h2s (by positivity)
          _ = cc * ((s : ℝ) ^ (0.2 : ℝ) * (s : ℝ)) := by ring
      calc -cc * ((s : ℝ) ^ (0.6 : ℝ)) ^ 2 / (1 + (s : ℝ))
          = -(cc * ((s : ℝ) ^ (0.6 : ℝ)) ^ 2 / (1 + (s : ℝ))) := by ring
        _ ≤ -(cc / 2 * (s : ℝ) ^ (0.2 : ℝ)) := neg_le_neg hkey
    have hterm2 : Real.exp (-cc * (s : ℝ) ^ (0.6 : ℝ))
        ≤ Real.exp (-(cc / 2 * (s : ℝ) ^ (0.2 : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      have h1' : (s : ℝ) ^ (0.2 : ℝ) ≤ (s : ℝ) ^ (0.6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
      nlinarith
    have hcube : Real.exp (-(cc / 2 * (s : ℝ) ^ (0.2 : ℝ)))
        ≤ 216 / (cc ^ 3 * (s : ℝ) ^ (0.6 : ℝ)) := by
      have h1' := exp_neg_le_cube (y := cc / 2 * (s : ℝ) ^ (0.2 : ℝ)) (by positivity)
      have h2' : (cc / 2 * (s : ℝ) ^ (0.2 : ℝ)) ^ 3
          = cc ^ 3 / 8 * ((s : ℝ) ^ (0.2 : ℝ)) ^ 3 := by ring
      have h3' : ((s : ℝ) ^ (0.2 : ℝ)) ^ 3 = (s : ℝ) ^ (0.6 : ℝ) := by
        rw [← Real.rpow_natCast ((s : ℝ) ^ (0.2 : ℝ)) 3, ← Real.rpow_mul hs0.le]
        norm_num
      calc Real.exp (-(cc / 2 * (s : ℝ) ^ (0.2 : ℝ)))
          ≤ 27 / (cc / 2 * (s : ℝ) ^ (0.2 : ℝ)) ^ 3 := h1'
        _ = 27 / (cc ^ 3 / 8 * (s : ℝ) ^ (0.6 : ℝ)) := by rw [h2', h3']
        _ = 216 / (cc ^ 3 * (s : ℝ) ^ (0.6 : ℝ)) := by
            rw [div_eq_div_iff (by positivity) (by positivity)]
            ring
    have hfinal : 216 / (cc ^ 3 * (s : ℝ) ^ (0.6 : ℝ)) ≤ 216 / (cc ^ 3 * (s' : ℝ)) := by
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact le_trans hs'm hm048
    have hAP1 : (1 : ℝ) ≤ A ^ 2 * (1 + (k : ℝ)) := by nlinarith
    calc Cc * (Real.exp (-cc * ((s : ℝ) ^ (0.6 : ℝ)) ^ 2 / (1 + (s : ℝ)))
          + Real.exp (-cc * (s : ℝ) ^ (0.6 : ℝ)))
        ≤ Cc * (216 / (cc ^ 3 * (s' : ℝ)) + 216 / (cc ^ 3 * (s' : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCc.le
          have := le_trans hterm1 (le_trans hcube hfinal)
          have := le_trans hterm2 (le_trans hcube hfinal)
          linarith [le_trans hterm1 (le_trans hcube hfinal),
            le_trans hterm2 (le_trans hcube hfinal)]
      _ = (432 * Cc / cc ^ 3) / (s' : ℝ) := by
          field_simp
          ring
      _ ≤ (432 * Cc / cc ^ 3) * (A ^ 2 * (1 + (k : ℝ))) / (s' : ℝ) := by
          rw [div_le_div_iff₀ hs'0 hs'0]
          have hpos : (0 : ℝ) ≤ 432 * Cc / cc ^ 3 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hAP1 hpos]
  have hbound3 : ∑' e : ℕ × ℤ,
      (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator Ev 1 (j + e.1, l + e.2)
      ≤ C₃ * C₂ * (A ^ 2 * (1 + (k : ℝ))) / (s' : ℝ) := by
    have h1 := hX10b tilt htilt0 htilt1 n ξ hξ F t₀ ht₀ j l hmemt₀ s hs hS₀b_le k s' W hW1 h100W hreg
    refine le_trans h1 ?_
    rw [hWdef]
    rw [div_le_div_iff₀ hs'0 hs'0]
    ring_nf
    nlinarith [hC₃, hs'0]
  -- assemble
  calc ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
      * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (j + e.1, l + e.2)
      ≤ ∑' e : ℕ × ℤ, ((fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator hEsc 1 e
        + (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator cEsc 1 e
        + (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator Ev 1 (j + e.1, l + e.2)) := by
        have hsA : Summable (fun e : ℕ × ℤ =>
            (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator hEsc 1 e) :=
          hsummable hEsc (fun q => q)
        have hsB : Summable (fun e : ℕ × ℤ =>
            (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator cEsc 1 e) :=
          hsummable cEsc (fun q => q)
        have hsC : Summable (fun e : ℕ × ℤ =>
            (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator Ev 1 (j + e.1, l + e.2)) :=
          hsummable Ev (fun e => (j + e.1, l + e.2))
        exact Summable.tsum_le_tsum hsplit
          (hsummable (bigTriangleSetP F s') (fun e => (j + e.1, l + e.2)))
          ((hsA.add hsB).add hsC)
    _ = (∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator hEsc 1 e)
        + (∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator cEsc 1 e)
        + ∑' e : ℕ × ℤ,
            (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator Ev 1 (j + e.1, l + e.2) := by
        have hsA : Summable (fun e : ℕ × ℤ =>
            (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator hEsc 1 e) :=
          hsummable hEsc (fun q => q)
        have hsB : Summable (fun e : ℕ × ℤ =>
            (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator cEsc 1 e) :=
          hsummable cEsc (fun q => q)
        have hsC : Summable (fun e : ℕ × ℤ =>
            (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal * Set.indicator Ev 1 (j + e.1, l + e.2)) :=
          hsummable Ev (fun e => (j + e.1, l + e.2))
        rw [Summable.tsum_add (hsA.add hsB) hsC, Summable.tsum_add hsA hsB]
    _ ≤ Ch * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ)))
        + (432 * Cc / cc ^ 3) * (A ^ 2 * (1 + (k : ℝ))) / (s' : ℝ)
        + C₃ * C₂ * (A ^ 2 * (1 + (k : ℝ))) / (s' : ℝ) :=
        add_le_add (add_le_add hbound1 hbound2) hbound3
    _ ≤ C * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
        + C * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ))) := by
        have h1 : Ch ≤ C := by
          have := Real.exp_pos (ch * (Mth : ℝ))
          have h2 : (0 : ℝ) < 432 * Cc / cc ^ 3 := by positivity
          nlinarith [mul_pos hC₃ (lt_of_lt_of_le one_pos hC₂),
            mul_pos (lt_of_lt_of_le one_pos hC₂) (by norm_num : (0:ℝ) < 100)]
        have h2 : 432 * Cc / cc ^ 3 + C₃ * C₂ ≤ C := by
          have := Real.exp_pos (ch * (Mth : ℝ))
          nlinarith [mul_pos (lt_of_lt_of_le one_pos hC₂) (by norm_num : (0:ℝ) < 100)]
        have h3 : (432 * Cc / cc ^ 3) * (A ^ 2 * (1 + (k : ℝ))) / (s' : ℝ)
            + C₃ * C₂ * (A ^ 2 * (1 + (k : ℝ))) / (s' : ℝ)
            ≤ C * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ) := by
          rw [← add_div, div_le_div_iff₀ hs'0 hs'0]
          nlinarith [mul_le_mul_of_nonneg_right h2 hAp0.le, hs'0]
        have h4 : Ch * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ)))
            ≤ C * Real.exp (-ch * A ^ 2 * (1 + (k : ℝ))) :=
          mul_le_mul_of_nonneg_right h1 hexp_pos.le
        linarith

/-- Regime threshold for the tilted rpow-form Lemma 7.10. -/
def M_encTriP : ℕ := max (10 ^ 27) ((S_apexProx + 0 + 1) ^ 2)

/-- Uniform exponential rate in the tilted Lemma 7.10 bound. -/
noncomputable def c_encTriP : ℝ := c_fpHeightTailP

/-- Uniform multiplicative constant in the tilted Lemma 7.10 bound. -/
noncomputable def C_encTriP : ℝ :=
  100 * C_apexProx + Real.exp (c_fpHeightTailP * (M_encTriP : ℝ))
    + C_fpHeightTailP + 432 * C_fpColTailP / c_fpColTailP ^ 3
    + C_encSepP * C_apexProx

theorem c_encTriP_pos : 0 < c_encTriP := by
  unfold c_encTriP
  exact c_fpHeightTailP_pos

theorem C_encTriP_pos : 0 < C_encTriP := by
  have h1 := C_apexProx_ge_one
  have h2 := Real.exp_pos (c_fpHeightTailP * (M_encTriP : ℝ))
  have h3 := C_fpHeightTailP_pos
  have h4 : (0 : ℝ) < 432 * C_fpColTailP / c_fpColTailP ^ 3 := by
    have hc := c_fpColTailP_pos
    have hC := C_fpColTailP_pos
    positivity
  have h5 := C_encSepP_pos
  unfold C_encTriP
  nlinarith [mul_pos h5 (lt_of_lt_of_le one_pos h1)]

/-- Explicit-constant tilted Lemma 7.10 in the rpow deep regime. -/
theorem triangle_encounter_le_rpowP_explicitC :
    ∀ (A : ℝ), 100 ≤ A →
      ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (k s' : ℕ), 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
      ∑' e : ℕ × ℤ,
          (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
            * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ)
              (j + e.1, l + e.2)
        ≤ C_encTriP * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
          + C_encTriP * Real.exp (-c_encTriP * A ^ 2 * (1 + (k : ℝ))) := by
  have h := triangle_encounter_le_rpowP_core
    c_fpHeightTailP C_fpHeightTailP c_fpColTailP C_fpColTailP
    C_apexProx C_encSepP S_apexProx 0
    c_fpHeightTailP_pos C_fpHeightTailP_pos c_fpColTailP_pos C_fpColTailP_pos
    C_apexProx_ge_one C_encSepP_pos
    fpDistPlusP_height_tail_explicitC fpDistPlusP_col_tail_explicitC
    encounter_apex_proximityP_rpow_at encounter_separated_sumP_explicitC
  unfold C_encTriP c_encTriP M_encTriP
  exact h

/-- **Tilted Lemma 7.10 (rpow form).**  All constants, including the
large-exponent threshold, are uniform over `tilt ∈ [1/5,3/5]`. -/
theorem triangle_encounter_le_rpowP :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ (A : ℝ), A₀ ≤ A →
      ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (k s' : ℕ), 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
      ∑' e : ℕ × ℤ,
          (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
            * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ)
              (j + e.1, l + e.2)
        ≤ C * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
          + C * Real.exp (-c * A ^ 2 * (1 + (k : ℝ))) :=
  ⟨C_encTriP, C_encTriP_pos, c_encTriP, c_encTriP_pos, 100, by norm_num,
    triangle_encounter_le_rpowP_explicitC⟩

-- HEARTBEAT: the logarithmic-to-rpow regime bridge retains the fixed-law
-- proof's nonlinear shallow/deep split.
set_option maxHeartbeats 800000 in
/-- Convert the tilted rpow-form encounter estimate to Tao's original
`m / log² m < s` deep-regime interface. -/
theorem triangle_encounter_leP_core (C c A₀ : ℝ)
    (hC : 0 < C) (_hc : 0 < c) (hA₀ : 1 ≤ A₀)
    (hEng : ∀ (A : ℝ), A₀ ≤ A →
      ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (k s' : ℕ), 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
      ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
          * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (j + e.1, l + e.2)
        ≤ C * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
          + C * Real.exp (-c * A ^ 2 * (1 + (k : ℝ)))) :
    ∀ (A : ℝ), A₀ ≤ A →
      ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) / Real.log ((n / 2 - j : ℕ) : ℝ) ^ 2 < (s : ℝ) →
      ∀ (k s' : ℕ), 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
      ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
          * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (j + e.1, l + e.2)
        ≤ max C ((10 : ℝ) ^ (11 : ℕ)) * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
          + max C ((10 : ℝ) ^ (11 : ℕ))
              * Real.exp (-c * A ^ 2 * (1 + (k : ℝ))) := by
  classical
  intro A hA tilt htilt0 htilt1 n ξ hξ F t₀ ht₀ j l hmem s hs hdeep k s' hs'1 hs'm
  set m : ℕ := n / 2 - j with hmdef
  have hs'0 : (0 : ℝ) < (s' : ℝ) := by exact_mod_cast hs'1
  have hCle : C ≤ max C ((10 : ℝ) ^ (11 : ℕ)) := le_max_left _ _
  have h11le : (10 : ℝ) ^ (11 : ℕ) ≤ max C ((10 : ℝ) ^ (11 : ℕ)) := le_max_right _ _
  have hmaxC0 : (0 : ℝ) < max C ((10 : ℝ) ^ (11 : ℕ)) := lt_of_lt_of_le hC hCle
  by_cases hM27 : ((10 : ℝ) ^ (27 : ℕ)) ≤ (m : ℝ)
  · -- deep regime: bridge `m/log²m < s ⟹ m^{0.8} < s`, then apply the engine
    have hm0R : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by norm_num) hM27
    have hlogsq : Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) ^ (0.2 : ℝ) := TaoCollatz.log_sq_le_rpow hM27
    have hlogpos : (0 : ℝ) < Real.log (m : ℝ) := by
      refine Real.log_pos ?_
      calc (1 : ℝ) < 10 ^ (27 : ℕ) := by norm_num
        _ ≤ (m : ℝ) := hM27
    have hm08 : (m : ℝ) ^ (0.8 : ℝ) ≤ (m : ℝ) / Real.log (m : ℝ) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hlogpos 2)]
      calc (m : ℝ) ^ (0.8 : ℝ) * Real.log (m : ℝ) ^ 2
          ≤ (m : ℝ) ^ (0.8 : ℝ) * (m : ℝ) ^ (0.2 : ℝ) :=
            mul_le_mul_of_nonneg_left hlogsq (Real.rpow_nonneg hm0R.le _)
        _ = (m : ℝ) := by rw [← Real.rpow_add hm0R]; norm_num
    have hbridge : (m : ℝ) ^ (0.8 : ℝ) < (s : ℝ) := lt_of_le_of_lt hm08 hdeep
    have heng := hEng A hA tilt htilt0 htilt1 n ξ hξ F t₀ ht₀ j l hmem s hs hbridge k s' hs'1 hs'm
    refine le_trans heng ?_
    have hd : (0 : ℝ) ≤ A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ) := div_nonneg (by positivity) hs'0.le
    have he : (0 : ℝ) ≤ Real.exp (-c * A ^ 2 * (1 + (k : ℝ))) := (Real.exp_pos _).le
    have t1 : C * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
        = C * (A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)) := by ring
    have t2 : max C ((10 : ℝ) ^ (11 : ℕ)) * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
        = max C ((10 : ℝ) ^ (11 : ℕ)) * (A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)) := by ring
    rw [t1, t2]
    exact add_le_add (mul_le_mul_of_nonneg_right hCle hd)
      (mul_le_mul_of_nonneg_right hCle he)
  · -- shallow regime: `m < 10²⁷`, LHS ≤ 1 ≤ RHS
    push Not at hM27
    have hLHS1 : ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
        * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (j + e.1, l + e.2)
        ≤ 1 := fpDistPlusP_indicator_sum_le_one tilt (by linarith) (by linarith) s k _ _
    have hAge1 : (1 : ℝ) ≤ A := le_trans hA₀ hA
    have hp1 : (1 : ℝ) ≤ 1 + (k : ℝ) := by
      have hpp : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hAsq1 : (1 : ℝ) ≤ A ^ 2 := by nlinarith [hAge1, sq_nonneg (A - 1)]
    have hA1 : (1 : ℝ) ≤ A ^ 2 * (1 + (k : ℝ)) := by
      nlinarith [hAsq1, hp1,
        mul_nonneg (sub_nonneg.mpr hAsq1) (by linarith [hp1] : (0 : ℝ) ≤ 1 + (k : ℝ))]
    have hs'lt : (s' : ℝ) < (10 : ℝ) ^ (11 : ℕ) := by
      have h1 : (m : ℝ) ^ (0.4 : ℝ) ≤ ((10 : ℝ) ^ (27 : ℕ)) ^ (0.4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hM27.le (by norm_num)
      have h2 : ((10 : ℝ) ^ (27 : ℕ)) ^ (0.4 : ℝ) = (10 : ℝ) ^ (10.8 : ℝ) := by
        rw [← Real.rpow_natCast (10 : ℝ) 27, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
        norm_num
      have h3 : (10 : ℝ) ^ (10.8 : ℝ) < (10 : ℝ) ^ ((11 : ℕ) : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      have h4 : (10 : ℝ) ^ ((11 : ℕ) : ℝ) = (10 : ℝ) ^ (11 : ℕ) := Real.rpow_natCast (10 : ℝ) 11
      calc (s' : ℝ) ≤ (m : ℝ) ^ (0.4 : ℝ) := hs'm
        _ ≤ ((10 : ℝ) ^ (27 : ℕ)) ^ (0.4 : ℝ) := h1
        _ = (10 : ℝ) ^ (10.8 : ℝ) := h2
        _ < (10 : ℝ) ^ ((11 : ℕ) : ℝ) := h3
        _ = (10 : ℝ) ^ (11 : ℕ) := h4
    have hs'maxC : (s' : ℝ) ≤ max C ((10 : ℝ) ^ (11 : ℕ)) :=
      le_of_lt (lt_of_lt_of_le hs'lt h11le)
    have hfrac : (1 : ℝ) ≤ max C ((10 : ℝ) ^ (11 : ℕ)) * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ) := by
      have hnum : (s' : ℝ) ≤ max C ((10 : ℝ) ^ (11 : ℕ)) * A ^ 2 * (1 + (k : ℝ)) := by
        nlinarith [hs'maxC, hA1, hmaxC0.le,
          mul_nonneg hmaxC0.le (sub_nonneg.mpr hA1)]
      rw [le_div_iff₀ hs'0]
      linarith [hnum]
    have hexp_nn : (0 : ℝ) ≤ max C ((10 : ℝ) ^ (11 : ℕ))
        * Real.exp (-c * A ^ 2 * (1 + (k : ℝ))) :=
      mul_nonneg hmaxC0.le (Real.exp_pos _).le
    calc ∑' e : ℕ × ℤ, (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
            * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (j + e.1, l + e.2)
          ≤ 1 := hLHS1
      _ ≤ max C ((10 : ℝ) ^ (11 : ℕ)) * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ) := hfrac
      _ ≤ max C ((10 : ℝ) ^ (11 : ℕ)) * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
            + max C ((10 : ℝ) ^ (11 : ℕ)) * Real.exp (-c * A ^ 2 * (1 + (k : ℝ))) :=
          le_add_of_nonneg_right hexp_nn

/-- Constant for the tilted Lemma 7.10 interface in Tao's original
`m / log² m < s` regime. -/
noncomputable def C_triEncP : ℝ := max C_encTriP ((10 : ℝ) ^ (11 : ℕ))

theorem C_triEncP_pos : 0 < C_triEncP := by
  unfold C_triEncP
  exact lt_of_lt_of_le C_encTriP_pos (le_max_left _ _)

/-- Explicit-constant tilted Lemma 7.10 in the paper's deep regime. -/
theorem triangle_encounter_leP_explicitC :
    ∀ (A : ℝ), 100 ≤ A →
      ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) /
            Real.log ((n / 2 - j : ℕ) : ℝ) ^ 2 < (s : ℝ) →
      ∀ (k s' : ℕ), 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
      ∑' e : ℕ × ℤ,
          (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
            * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ)
              (j + e.1, l + e.2)
        ≤ C_triEncP * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
          + C_triEncP * Real.exp (-c_encTriP * A ^ 2 * (1 + (k : ℝ))) := by
  have h := triangle_encounter_leP_core C_encTriP c_encTriP 100
    C_encTriP_pos c_encTriP_pos (by norm_num)
    triangle_encounter_le_rpowP_explicitC
  unfold C_triEncP
  exact h

/-- **Tilted Lemma 7.10 (paper form).**  Uniformly over the Pascal window,
large finer-scale triangles are rarely encountered after a deep crossing. -/
theorem triangle_encounter_leP :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ (A : ℝ), A₀ ≤ A →
      ∀ (tilt : ℝ) (htilt0 : 1 / 5 ≤ tilt) (htilt1 : tilt ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) /
            Real.log ((n / 2 - j : ℕ) : ℝ) ^ 2 < (s : ℝ) →
      ∀ (k s' : ℕ), 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
      ∑' e : ℕ × ℤ,
          (fpDistPlusP tilt (by linarith) (by linarith) s k e).toReal
            * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ)
              (j + e.1, l + e.2)
        ≤ C * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
          + C * Real.exp (-c * A ^ 2 * (1 + (k : ℝ))) :=
  ⟨C_triEncP, C_triEncP_pos, c_encTriP, c_encTriP_pos, 100, by norm_num,
    triangle_encounter_leP_explicitC⟩

end TaoCollatz.Sec7P
