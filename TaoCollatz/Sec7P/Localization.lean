/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.Triangles
import TaoCollatz.Sec7P.BlackEdge

/-!
# Explicit first-passage localization for the tilted holding law

This module supplies the vertical half of the finer-scale Case-2 localization box.
Every `holdP` step raises the second coordinate by at least three, so the renewal mass
on each fixed height level is at most one.  Grouping the first-passage convolution by
that height and applying the uniform one-step exponential tail gives

`P(fpDistP(s).snd >= s + 12000) <= 1/16`

uniformly for `p in [1/5, 3/5]`.  The radius and mass are the values certified in
`height_radiusP_numeric`; no constant depends on `p`.
-/

open scoped ENNReal

namespace TaoCollatz.Sec7P

section RenewalLevel

variable (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)

local notation "holdLaw" => holdP p hp0 hp1
local notation "holdSndLaw" => PMF.map Prod.snd holdLaw
local notation "renewalMassLaw" => renewalMassP p hp0 hp1

/-- The second-coordinate marginal of `holdP` is supported on heights at least three. -/
theorem holdPSnd_support_ge {a : ℤ} (ha : holdSndLaw a ≠ 0) : 3 ≤ a := by
  rw [← PMF.mem_support_iff, PMF.mem_support_map_iff] at ha
  obtain ⟨d, hd, rfl⟩ := ha
  exact holdP_support_snd_ge p hp0 hp1 d hd

/-- The one-dimensional renewal density for the height marginal of `holdP`. -/
noncomputable def renewalHeightP (u : ℤ) : ℝ≥0∞ :=
  ∑' k : ℕ, TaoCollatz.iidSum holdSndLaw k u

/-- The height marginal after `k` steps is the sum over first-coordinate fibres. -/
theorem iidSum_holdPSnd_apply (k : ℕ) (u : ℤ) :
    TaoCollatz.iidSum holdSndLaw k u =
      ∑' j : ℕ, TaoCollatz.iidSum holdLaw k (j, u) := by
  rw [← TaoCollatz.iidSum_map holdLaw Prod.snd rfl (fun _ _ => rfl) k,
    PMF.map_apply, ENNReal.tsum_prod']
  refine tsum_congr fun j => ?_
  refine (tsum_eq_single u (fun l hl => if_neg (fun h => ?_))).trans ?_
  · exact hl h.symm
  · rw [if_pos rfl]

/-- Negative heights carry no tilted height-renewal mass. -/
theorem renewalHeightP_zero_of_neg {u : ℤ} (hu : u < 0) :
    renewalHeightP p hp0 hp1 u = 0 := by
  show (∑' k : ℕ, TaoCollatz.iidSum holdSndLaw k u) = 0
  refine ENNReal.tsum_eq_zero.mpr fun k => ?_
  rw [iidSum_holdPSnd_apply]
  refine ENNReal.tsum_eq_zero.mpr fun j => ?_
  refine iidSum_holdP_snd_zero p hp0 hp1 k (j, u) ?_
  have : (0 : ℤ) ≤ 3 * (k : ℤ) := by positivity
  omega

/-- Renewal equation for the one-dimensional tilted height density. -/
theorem renewalHeightP_eq (u : ℤ) :
    renewalHeightP p hp0 hp1 u =
      (if u = 0 then 1 else 0) +
        ∑' a : ℤ, holdSndLaw a * renewalHeightP p hp0 hp1 (u - a) := by
  have hstep : ∀ k : ℕ, TaoCollatz.iidSum holdSndLaw (k + 1) u =
      ∑' a : ℤ, holdSndLaw a *
        TaoCollatz.iidSum holdSndLaw k (u - a) := by
    intro k
    rw [TaoCollatz.iidSum_succ, PMF.bind_apply]
    exact tsum_congr fun a => by rw [TaoCollatz.pmf_map_add_apply]
  have htail : (∑' k : ℕ, TaoCollatz.iidSum holdSndLaw (k + 1) u) =
      ∑' a : ℤ, holdSndLaw a * renewalHeightP p hp0 hp1 (u - a) := by
    calc
      (∑' k : ℕ, TaoCollatz.iidSum holdSndLaw (k + 1) u) =
          ∑' k : ℕ, ∑' a : ℤ, holdSndLaw a *
            TaoCollatz.iidSum holdSndLaw k (u - a) := tsum_congr hstep
      _ = ∑' a : ℤ, ∑' k : ℕ, holdSndLaw a *
            TaoCollatz.iidSum holdSndLaw k (u - a) := ENNReal.tsum_comm
      _ = ∑' a : ℤ, holdSndLaw a * renewalHeightP p hp0 hp1 (u - a) := by
          refine tsum_congr fun a => ?_
          rw [show renewalHeightP p hp0 hp1 (u - a) =
              ∑' k : ℕ, TaoCollatz.iidSum holdSndLaw k (u - a) from rfl]
          exact ENNReal.tsum_mul_left
  rw [show renewalHeightP p hp0 hp1 u =
      ∑' k : ℕ, TaoCollatz.iidSum holdSndLaw k u from rfl,
    tsum_eq_zero_add' ENNReal.summable, TaoCollatz.iidSum_zero, PMF.pure_apply]
  exact congr_arg₂ (· + ·) (by congr) htail

/-- Strictly increasing heights make the tilted renewal density at each level at most one. -/
theorem renewalHeightP_le_one (u : ℤ) : renewalHeightP p hp0 hp1 u ≤ 1 := by
  rcases lt_or_ge u 0 with hu | hu
  · rw [renewalHeightP_zero_of_neg p hp0 hp1 hu]
    exact zero_le_one
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, u = (n : ℤ) :=
    ⟨u.toNat, (Int.toNat_of_nonneg hu).symm⟩
  clear hu
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rw [renewalHeightP_eq]
    have hbody : ∀ a : ℤ,
        holdSndLaw a * renewalHeightP p hp0 hp1 ((n : ℤ) - a) ≤
          holdSndLaw a := by
      intro a
      by_cases hFa : holdSndLaw a = 0
      · simp [hFa]
      · have ha3 : 3 ≤ a := holdPSnd_support_ge p hp0 hp1 hFa
        have hrec : renewalHeightP p hp0 hp1 ((n : ℤ) - a) ≤ 1 := by
          rcases lt_or_ge ((n : ℤ) - a) 0 with hneg | hpos
          · rw [renewalHeightP_zero_of_neg p hp0 hp1 hneg]
            exact zero_le_one
          · obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℤ) - a = (m : ℤ) :=
              ⟨((n : ℤ) - a).toNat, (Int.toNat_of_nonneg hpos).symm⟩
            have hmn : m < n := by omega
            rw [hm]
            exact IH m hmn
        calc
          holdSndLaw a * renewalHeightP p hp0 hp1 ((n : ℤ) - a)
              ≤ holdSndLaw a * 1 := by gcongr
          _ = holdSndLaw a := mul_one _
    have hsum : (∑' a : ℤ,
        holdSndLaw a * renewalHeightP p hp0 hp1 ((n : ℤ) - a)) ≤ 1 := by
      calc
        (∑' a : ℤ, holdSndLaw a * renewalHeightP p hp0 hp1 ((n : ℤ) - a))
            ≤ ∑' a : ℤ, holdSndLaw a := ENNReal.tsum_le_tsum hbody
        _ = 1 := (PMF.map Prod.snd holdLaw).tsum_coe
    by_cases hn0 : (n : ℤ) = 0
    · rw [if_pos hn0]
      have hz : (∑' a : ℤ,
          holdSndLaw a * renewalHeightP p hp0 hp1 ((n : ℤ) - a)) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun a => ?_
        by_cases hFa : holdSndLaw a = 0
        · rw [hFa, zero_mul]
        · have ha3 : 3 ≤ a := holdPSnd_support_ge p hp0 hp1 hFa
          rw [renewalHeightP_zero_of_neg p hp0 hp1 (by omega), mul_zero]
      rw [hz, add_zero]
    · rw [if_neg hn0, zero_add]
      exact hsum

/-- The two-dimensional tilted renewal mass, summed over one height level, is at most one. -/
theorem renewal_levelP_le_one (u : ℤ) :
    (∑' j : ℕ, renewalMassLaw (j, u)) ≤ 1 := by
  have hrw : (∑' j : ℕ, renewalMassLaw (j, u)) = renewalHeightP p hp0 hp1 u := by
    show (∑' j : ℕ, renewalMassLaw (j, u)) =
      ∑' k : ℕ, TaoCollatz.iidSum holdSndLaw k u
    calc
      (∑' j : ℕ, renewalMassLaw (j, u)) =
          ∑' j : ℕ, ∑' k : ℕ, TaoCollatz.iidSum holdLaw k (j, u) := by
            refine tsum_congr fun j => ?_
            rw [renewalMassP]
      _ = ∑' k : ℕ, ∑' j : ℕ, TaoCollatz.iidSum holdLaw k (j, u) := ENNReal.tsum_comm
      _ = ∑' k : ℕ, TaoCollatz.iidSum holdSndLaw k u :=
        tsum_congr fun k => (iidSum_holdPSnd_apply p hp0 hp1 k u).symm
  rw [hrw]
  exact renewalHeightP_le_one p hp0 hp1 u

end RenewalLevel

/-! ### Uniform geometric tail at radius `12000` -/

/-- Integer-threshold form of `holdP_snd_tail`, convenient for a renewal convolution. -/
theorem holdP_snd_tail_int {p : ℝ} (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (T : ℤ) (hT : 0 ≤ T) :
    (∑' d : ℕ × ℤ, if T ≤ d.2 then
        holdP p (by linarith) (by linarith) d else 0) ≤
      ENNReal.ofReal (6 * Real.exp (-(1 / 1000 : ℝ) * (T : ℝ))) := by
  have hcast : ((T.toNat : ℕ) : ℤ) = T := Int.toNat_of_nonneg hT
  have h := holdP_snd_tail hp0 hp1 T.toNat
  convert h using 1
  · refine tsum_congr fun d => ?_
    congr 2
    omega
  · congr 2
    have hcastR : ((T.toNat : ℕ) : ℝ) = (T : ℝ) := by exact_mod_cast hcast
    rw [hcastR]
    congr 1
    ring

/-- Summing the fixed exponential tail over all renewal levels below `s` gives
the explicit geometric series used by the vertical localization bound. -/
theorem hasSum_int_level_geomP (s : ℕ) :
    HasSum (fun u : ℤ =>
        if u ≤ (s : ℤ) then
          Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (u : ℝ))) else 0)
      (Real.exp (-(1 / 1000 : ℝ) * 12000) /
        (1 - Real.exp (-(1 / 1000 : ℝ)))) := by
  have he0 : (0 : ℝ) < Real.exp (-(1 / 1000 : ℝ)) := Real.exp_pos _
  have he1 : Real.exp (-(1 / 1000 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  rw [← (Equiv.subLeft (s : ℤ)).hasSum_iff]
  have hfun : ((fun u : ℤ =>
        if u ≤ (s : ℤ) then
          Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (u : ℝ))) else 0)
        ∘ (Equiv.subLeft (s : ℤ))) =
      fun k : ℤ => if 0 ≤ k then
        Real.exp (-(1 / 1000 : ℝ) * (12000 + (k : ℝ))) else 0 := by
    funext k
    simp only [Function.comp_apply, Equiv.subLeft_apply]
    by_cases hk : 0 ≤ k
    · rw [if_pos (by omega), if_pos hk]
      congr 1
      push_cast
      ring
    · rw [if_neg (by omega), if_neg hk]
  rw [hfun]
  have hnat : HasSum (fun n : ℕ =>
        if 0 ≤ ((n : ℤ)) then
          Real.exp (-(1 / 1000 : ℝ) * (12000 + (((n : ℤ)) : ℝ))) else 0)
      (Real.exp (-(1 / 1000 : ℝ) * 12000) /
        (1 - Real.exp (-(1 / 1000 : ℝ)))) := by
    have hgeo := (hasSum_geometric_of_lt_one he0.le he1).mul_left
      (Real.exp (-(1 / 1000 : ℝ) * 12000))
    rw [← div_eq_mul_inv] at hgeo
    have hrw : (fun n : ℕ =>
          if 0 ≤ ((n : ℤ)) then
            Real.exp (-(1 / 1000 : ℝ) * (12000 + (((n : ℤ)) : ℝ))) else 0) =
        fun n : ℕ => Real.exp (-(1 / 1000 : ℝ) * 12000) *
          Real.exp (-(1 / 1000 : ℝ)) ^ n := by
      funext n
      rw [if_pos (by positivity), ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hrw]
    exact hgeo
  have hneg : HasSum (fun n : ℕ =>
        if 0 ≤ (-((n : ℤ) + 1)) then
          Real.exp (-(1 / 1000 : ℝ) * (12000 + ((-((n : ℤ) + 1)) : ℝ))) else 0) 0 := by
    have hz : (fun n : ℕ =>
          if 0 ≤ (-((n : ℤ) + 1)) then
            Real.exp (-(1 / 1000 : ℝ) * (12000 + ((-((n : ℤ) + 1)) : ℝ))) else 0) =
        fun _ : ℕ => (0 : ℝ) := by
      funext n
      rw [if_neg (by omega)]
    rw [hz]
    exact hasSum_zero
  have hcombine := HasSum.of_nat_of_neg_add_one
    (f := fun k : ℤ => if 0 ≤ k then
      Real.exp (-(1 / 1000 : ℝ) * (12000 + (k : ℝ))) else 0) hnat hneg
  rwa [add_zero] at hcombine

/-- `ENNReal` form of `hasSum_int_level_geomP`. -/
theorem geom_level_sumP_le (s : ℕ) :
    (∑' u : ℤ, if u ≤ (s : ℤ) then
        ENNReal.ofReal
          (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (u : ℝ)))) else 0) ≤
      ENNReal.ofReal (Real.exp (-(1 / 1000 : ℝ) * 12000) /
        (1 - Real.exp (-(1 / 1000 : ℝ)))) := by
  have hsum := hasSum_int_level_geomP s
  have hnn : ∀ u : ℤ, 0 ≤ (if u ≤ (s : ℤ) then
      Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (u : ℝ))) else 0) := by
    intro u
    split <;> [positivity; rfl]
  refine le_of_eq ?_
  rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable]
  refine tsum_congr fun u => ?_
  split_ifs
  · rfl
  · exact (ENNReal.ofReal_zero).symm

/-- Uniform vertical localization for the tilted first-passage endpoint.  Apart from
mass `1/16`, the endpoint overshoots its height budget by less than `12000`. -/
theorem fpDistP_height_tail_le_sixteenth {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) (s : ℕ) :
    (∑' e : ℕ × ℤ, if (s : ℝ) + 12000 ≤ (e.2 : ℝ) then
        fpDistP p (by linarith) (by linarith) s e else 0) ≤ (1 : ℝ≥0∞) / 16 := by
  classical
  have hp : 0 < p := by linarith
  have hp' : p < 1 := by linarith
  let holdLaw : PMF (ℕ × ℤ) := holdP p hp hp'
  let fpLaw : ℕ → PMF (ℕ × ℤ) := fpDistP p hp hp'
  let renewalLaw : ℕ × ℤ → ℝ≥0∞ := renewalMassP p hp hp'
  change (∑' e : ℕ × ℤ, if (s : ℝ) + 12000 ≤ (e.2 : ℝ) then fpLaw s e else 0) ≤ _
  have hpred : ∀ e : ℕ × ℤ,
      ((s : ℝ) + 12000 ≤ (e.2 : ℝ)) ↔ ((s : ℤ) + 12000 ≤ e.2) := by
    intro e
    constructor <;> intro h <;> exact_mod_cast h
  simp only [hpred]
  set C : ℝ≥0∞ := ENNReal.ofReal 6 with hC
  -- First passage is dominated by a below-budget renewal point followed by one step.
  have hstep1 : (∑' e : ℕ × ℤ,
      if (s : ℤ) + 12000 ≤ e.2 then fpLaw s e else 0) ≤
      ∑' e : ℕ × ℤ, if (s : ℤ) + 12000 ≤ e.2 then
        (∑' q : ℕ × ℤ, (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
          ∑' d : ℕ × ℤ, (if e = q + d then holdLaw d else 0)) else 0 := by
    refine ENNReal.tsum_le_tsum fun e => ?_
    by_cases he : (s : ℤ) + 12000 ≤ e.2
    · rw [if_pos he, if_pos he]
      exact fpDistP_le_renewal_conv p hp hp' s e
    · rw [if_neg he, if_neg he]
  -- Swap the endpoint sum inward and collapse its delta constraint.
  have hswap : (∑' e : ℕ × ℤ, if (s : ℤ) + 12000 ≤ e.2 then
        (∑' q : ℕ × ℤ, (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
          ∑' d : ℕ × ℤ, (if e = q + d then holdLaw d else 0)) else 0) =
      ∑' q : ℕ × ℤ, (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
        ∑' d : ℕ × ℤ, (if (s : ℤ) + 12000 ≤ (q + d).2 then holdLaw d else 0) := by
    have e1 : (∑' e : ℕ × ℤ, if (s : ℤ) + 12000 ≤ e.2 then
          (∑' q : ℕ × ℤ, (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
            ∑' d : ℕ × ℤ, (if e = q + d then holdLaw d else 0)) else 0) =
        ∑' e : ℕ × ℤ, ∑' q : ℕ × ℤ, ∑' d : ℕ × ℤ,
          (if (s : ℤ) + 12000 ≤ e.2 then
            (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
              (if e = q + d then holdLaw d else 0) else 0) := by
      refine tsum_congr fun e => ?_
      by_cases he : (s : ℤ) + 12000 ≤ e.2
      · rw [if_pos he]
        refine tsum_congr fun q => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun d => (if_pos he).symm
      · simp only [if_neg he, tsum_zero]
    have e2 : (∑' e : ℕ × ℤ, ∑' q : ℕ × ℤ, ∑' d : ℕ × ℤ,
          (if (s : ℤ) + 12000 ≤ e.2 then
            (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
              (if e = q + d then holdLaw d else 0) else 0)) =
        ∑' q : ℕ × ℤ, ∑' d : ℕ × ℤ, ∑' e : ℕ × ℤ,
          (if (s : ℤ) + 12000 ≤ e.2 then
            (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
              (if e = q + d then holdLaw d else 0) else 0) := by
      rw [ENNReal.tsum_comm]
      exact tsum_congr fun q => ENNReal.tsum_comm
    have e3 : (∑' q : ℕ × ℤ, ∑' d : ℕ × ℤ, ∑' e : ℕ × ℤ,
          (if (s : ℤ) + 12000 ≤ e.2 then
            (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
              (if e = q + d then holdLaw d else 0) else 0)) =
        ∑' q : ℕ × ℤ, (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
          ∑' d : ℕ × ℤ,
            (if (s : ℤ) + 12000 ≤ (q + d).2 then holdLaw d else 0) := by
      refine tsum_congr fun q => ?_
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun d => ?_
      rw [tsum_eq_single (q + d) (fun e' he' => by
          rw [if_neg he', mul_zero, ite_self]), if_pos rfl, mul_ite, mul_zero]
    rw [e1, e2, e3]
  refine le_trans (hstep1.trans_eq hswap) ?_
  -- Apply the one-step tail at the remaining height gap.
  have hstep3 : (∑' q : ℕ × ℤ,
      (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
        ∑' d : ℕ × ℤ, (if (s : ℤ) + 12000 ≤ (q + d).2 then holdLaw d else 0)) ≤
      ∑' q : ℕ × ℤ, (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
        (ENNReal.ofReal
          (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (q.2 : ℝ)))) * C) := by
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : q.2 ≤ (s : ℤ)
    · rw [if_pos hq]
      gcongr
      have hcond : (∑' d : ℕ × ℤ,
          if (s : ℤ) + 12000 ≤ (q + d).2 then holdLaw d else 0) =
          ∑' d : ℕ × ℤ,
            if (s : ℤ) + 12000 - q.2 ≤ d.2 then holdLaw d else 0 := by
        refine tsum_congr fun d => ?_
        by_cases hc : (s : ℤ) + 12000 ≤ (q + d).2
        · rw [if_pos hc, if_pos (by simp only [Prod.snd_add] at hc ⊢; omega)]
        · rw [if_neg hc, if_neg (by simp only [Prod.snd_add] at hc ⊢; omega)]
      rw [hcond, hC]
      have htail := holdP_snd_tail_int hp0 hp1 ((s : ℤ) + 12000 - q.2) (by omega)
      refine htail.trans_eq ?_
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      push_cast
      ring
    · rw [if_neg hq, zero_mul, zero_mul]
  refine le_trans hstep3 ?_
  -- Pull out the constant six.
  have hstep4 : (∑' q : ℕ × ℤ,
      (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
        (ENNReal.ofReal
          (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (q.2 : ℝ)))) * C)) =
      C * ∑' q : ℕ × ℤ, (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
        ENNReal.ofReal
          (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (q.2 : ℝ)))) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun q => by ring
  rw [hstep4]
  -- Group by height and use the at-most-one renewal mass on each level.
  have hstep5 : (∑' q : ℕ × ℤ,
      (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
        ENNReal.ofReal
          (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (q.2 : ℝ))))) ≤
      ∑' u : ℤ, if u ≤ (s : ℤ) then
        ENNReal.ofReal
          (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (u : ℝ)))) else 0 := by
    have hgroup : (∑' q : ℕ × ℤ,
        (if q.2 ≤ (s : ℤ) then renewalLaw q else 0) *
          ENNReal.ofReal
            (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (q.2 : ℝ))))) =
        ∑' u : ℤ, ∑' j : ℕ,
          (if ((j, u) : ℕ × ℤ).2 ≤ (s : ℤ) then renewalLaw (j, u) else 0) *
            ENNReal.ofReal
              (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (u : ℝ)))) := by
      rw [ENNReal.tsum_prod']
      exact ENNReal.tsum_comm
    rw [hgroup]
    refine ENNReal.tsum_le_tsum fun u => ?_
    rw [ENNReal.tsum_mul_right]
    by_cases hu : u ≤ (s : ℤ)
    · have hle : (∑' j : ℕ,
          if ((j, u) : ℕ × ℤ).2 ≤ (s : ℤ) then renewalLaw (j, u) else 0) ≤ 1 := by
        simp only [if_pos hu]
        exact renewal_levelP_le_one p hp hp' u
      calc
        (∑' j : ℕ, if ((j, u) : ℕ × ℤ).2 ≤ (s : ℤ) then renewalLaw (j, u) else 0) *
              ENNReal.ofReal
                (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (u : ℝ))))
            ≤ 1 * ENNReal.ofReal
                (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (u : ℝ)))) := by gcongr
        _ = ENNReal.ofReal
              (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (u : ℝ)))) := one_mul _
        _ = if u ≤ (s : ℤ) then
              ENNReal.ofReal
                (Real.exp (-(1 / 1000 : ℝ) * ((s : ℝ) + 12000 - (u : ℝ)))) else 0 :=
          (if_pos hu).symm
    · simp only [if_neg hu, tsum_zero, zero_mul, le_refl]
  refine le_trans (mul_le_mul_right hstep5 C) ?_
  refine le_trans (mul_le_mul_right (geom_level_sumP_le s) C) ?_
  rw [hC, ← ENNReal.ofReal_mul (by norm_num),
    show (1 : ℝ≥0∞) / 16 = ENNReal.ofReal (1 / 16) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num]
  exact ENNReal.ofReal_le_ofReal height_radiusP_numeric

/-- Uniform two-sided localization at the radii used by the finer triangle
geometry.  Outside mass `1/8`, a tilted first-passage endpoint has vertical
overshoot below `12000` and remains in the transverse half-space
`16*e₁ - 5*e₂ < 300`. -/
theorem fpDistP_localization_le_eighth {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) (s : ℕ) :
    (∑' e : ℕ × ℤ,
      if (s : ℝ) + 12000 ≤ (e.2 : ℝ) ∨
          (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
        then fpDistP p (by linarith) (by linarith) s e else 0) ≤
      (1 : ℝ≥0∞) / 8 := by
  calc
    (∑' e : ℕ × ℤ,
      if (s : ℝ) + 12000 ≤ (e.2 : ℝ) ∨
          (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
        then fpDistP p (by linarith) (by linarith) s e else 0) ≤
      (∑' e : ℕ × ℤ,
        if (s : ℝ) + 12000 ≤ (e.2 : ℝ)
          then fpDistP p (by linarith) (by linarith) s e else 0) +
        ∑' e : ℕ × ℤ,
          if (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
            then fpDistP p (by linarith) (by linarith) s e else 0 := by
      rw [← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun e => ?_
      by_cases hv : (s : ℝ) + 12000 ≤ (e.2 : ℝ)
      · simp [hv]
      · by_cases hh : (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
        · simp [hv, hh]
        · simp [hv, hh]
    _ ≤ (1 : ℝ≥0∞) / 16 + (1 : ℝ≥0∞) / 16 :=
      add_le_add (fpDistP_height_tail_le_sixteenth hp0 hp1 s)
        (fpDistP_transverse_tail_le_sixteenth hp0 hp1 s)
    _ = (1 : ℝ≥0∞) / 8 := by
      have h16 : ENNReal.ofReal (1 / 16 : ℝ) = (1 : ℝ≥0∞) / 16 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16)]
        norm_num
      have h8 : ENNReal.ofReal (1 / 8 : ℝ) = (1 : ℝ≥0∞) / 8 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8)]
        norm_num
      have hadd : ENNReal.ofReal (1 / 16 : ℝ) + ENNReal.ofReal (1 / 16 : ℝ) =
          ENNReal.ofReal (1 / 8 : ℝ) := by
        rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1 / 16)
          (by positivity : (0 : ℝ) ≤ 1 / 16)]
        congr 1
        norm_num
      simpa only [h16, h8] using hadd

/-- The explicit finer-scale localization box, with both the analytic mass
bound and the deterministic inequalities consumed by triangle separation. -/
theorem exists_fpDistP_localization_box :
    ∃ X Y : ℕ,
      (5 : ℝ) * Y + 300 ≤ 16 * X ∧
      (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 <
        ((1 / 10 : ℝ) * Real.log (1 / (epsP : ℝ))) ^ 2 ∧
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) (s : ℕ),
        (∑' e : ℕ × ℤ,
          if (s : ℝ) + Y ≤ (e.2 : ℝ) ∨
              (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
            then fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e else 0) ≤
          (1 : ℝ≥0∞) / 8 := by
  refine ⟨3769, 12000, localization_boxP_numeric.1,
    localization_boxP_numeric.2, ?_⟩
  intro p hp0 hp1 s
  exact fpDistP_localization_le_eighth hp0 hp1 s

end TaoCollatz.Sec7P
