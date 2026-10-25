/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.Prob

/-!
# The tilted holding distribution

This is Tao's §7.3 holding law with the pair-sum distribution changed from
`Pascal(1/2)` to `Pascal(p)`.  Write `q(p) = P(Pascal(p) = 3)`.  A holding
increment draws `k ~ Geom(q(p))`, then `k - 1` iid copies of `Pascal(p)`
conditioned away from `3`, and returns `(k, 3 + sum increments)`.

The construction is stated for the natural open parameter range `0 < p < 1`.
Every campaign use has the stronger compact-window hypotheses
`p ∈ [1/5, 3/5]`.
-/

open scoped ENNReal

namespace TaoCollatz.Sec7P

/-- The distinguished-atom probability is positive away from the endpoints. -/
theorem pairThreeProb_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < pairThreeProb p := by
  unfold pairThreeProb
  positivity

/-- The distinguished-atom probability is itself a valid geometric parameter. -/
theorem pairThreeProb_le_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    pairThreeProb p ≤ 1 :=
  (pairThreeProb_basic_bounds p hp0 hp1.le).2.trans (by norm_num)

/-- The distinguished-atom probability is strictly below one. -/
theorem pairThreeProb_lt_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    pairThreeProb p < 1 :=
  (pairThreeProb_basic_bounds p hp0 hp1.le).2.trans_lt (by norm_num)

/-- The tilted holding distribution.  This is (7.20)--(7.22) with
`Geom(1/2) + Geom(1/2)` replaced by the pair-sum law `Pascal(p)`. -/
noncomputable def holdP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : PMF (ℕ × ℤ) :=
  (geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
      (pairThreeProb_le_one p hp0 hp1)).bind fun k =>
    ((pascalNe3P p hp0 hp1.le).iid (k - 1)).map fun v =>
      (k, (3 + ∑ i, v i : ℤ))

/-- The first coordinate of every tilted holding atom is positive. -/
theorem holdP_support_fst_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d : ℕ × ℤ) (hd : d ∈ (holdP p hp0 hp1).support) : 1 ≤ d.1 := by
  rw [holdP, PMF.mem_support_bind_iff] at hd
  obtain ⟨k, hk, hkd⟩ := hd
  rw [PMF.mem_support_map_iff] at hkd
  obtain ⟨v, _, hv⟩ := hkd
  have hk0 : k ≠ 0 := by
    intro h
    rw [PMF.mem_support_iff] at hk
    apply hk
    rw [h, geomP_apply]
    simp
  rw [← hv]
  exact Nat.one_le_iff_ne_zero.mpr hk0

/-- `holdP` puts zero mass wherever the first coordinate is zero. -/
theorem holdP_zero_of_fst_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {d : ℕ × ℤ} (h0 : d.1 = 0) : holdP p hp0 hp1 d = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro hd
  exact absurd (holdP_support_fst_pos p hp0 hp1 d hd) (by omega)

/-- The second coordinate of every tilted holding atom is at least `3`. -/
theorem holdP_support_snd_ge (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d : ℕ × ℤ) (hd : d ∈ (holdP p hp0 hp1).support) : 3 ≤ d.2 := by
  rw [holdP, PMF.mem_support_bind_iff] at hd
  obtain ⟨k, _, hkd⟩ := hd
  rw [PMF.mem_support_map_iff] at hkd
  obtain ⟨v, _, hv⟩ := hkd
  rw [← hv]
  have h0 : (0 : ℤ) ≤ ∑ i, (v i : ℤ) :=
    Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
  show (3 : ℤ) ≤ 3 + ∑ i, (v i : ℤ)
  linarith

/-- `holdP` has zero mass below height `3`. -/
theorem holdP_zero_of_snd_lt (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {d : ℕ × ℤ} (h2 : d.2 < 3) : holdP p hp0 hp1 d = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro hd
  exact absurd (holdP_support_snd_ge p hp0 hp1 d hd) (by omega)

/-- The first marginal of `holdP` is `Geom(q(p))`. -/
theorem holdP_map_fst (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (holdP p hp0 hp1).map Prod.fst =
      geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
        (pairThreeProb_le_one p hp0 hp1) := by
  rw [holdP, PMF.map_bind]
  have h : ∀ k : ℕ,
      ((((pascalNe3P p hp0 hp1.le).iid (k - 1)).map fun v =>
          (k, (3 + ∑ i, v i : ℤ))).map Prod.fst) = PMF.pure k := by
    intro k
    rw [PMF.map_comp]
    exact PMF.map_const _ _
  simp only [h]
  exact PMF.bind_pure _

/-- Pinning the first coordinate of a tilted holding atom leaves the pushed-forward
increment law, multiplied by the corresponding geometric mass. -/
theorem holdP_apply_pin (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (k₀ : ℕ) (y : ℤ) :
    holdP p hp0 hp1 (k₀, y) =
      geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
          (pairThreeProb_le_one p hp0 hp1) k₀ *
        (((pascalNe3P p hp0 hp1.le).iid (k₀ - 1)).map fun v =>
          ((3 : ℤ) + ∑ i, (v i : ℤ))) y := by
  classical
  rw [holdP, PMF.bind_apply]
  rw [tsum_eq_single k₀ (fun k hk => by
    have hz : (((pascalNe3P p hp0 hp1.le).iid (k - 1)).map fun v =>
        ((k : ℕ), ((3 : ℤ) + ∑ i, (v i : ℤ)))) (k₀, y) = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.mpr fun v => ?_
      rw [if_neg (fun h => hk ((congrArg Prod.fst h).symm : k = k₀))]
    rw [hz, mul_zero])]
  congr 1
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun v => ?_
  congr 1
  rw [Prod.ext_iff]
  simp

/-- The one-step atom `(1,3)` has mass `q(p)`. -/
theorem holdP_apply_one_three (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (holdP p hp0 hp1 (1, 3)).toReal = pairThreeProb p := by
  rw [holdP_apply_pin]
  have h0 : (pascalNe3P p hp0 hp1.le).iid (1 - 1) =
      PMF.pure (fun i : Fin 0 => i.elim0) := rfl
  rw [h0, PMF.pure_map]
  have hval : ((3 : ℤ) + ∑ i : Fin 0,
      (((fun i : Fin 0 => i.elim0) i : ℕ) : ℤ)) = 3 := by simp
  rw [hval, PMF.pure_apply, if_pos rfl, mul_one, geomP_toReal]
  simp

/-- At first coordinate `2`, `holdP` consists of one conditioned Pascal increment. -/
theorem holdP_apply_two (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (b : ℕ) :
    holdP p hp0 hp1 (2, 3 + (b : ℤ)) =
      geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
          (pairThreeProb_le_one p hp0 hp1) 2 *
        pascalNe3P p hp0 hp1.le b := by
  classical
  rw [holdP_apply_pin]
  congr 1
  have hiid1 : (pascalNe3P p hp0 hp1.le).iid (2 - 1) =
      (pascalNe3P p hp0 hp1.le).map fun a =>
        Fin.cons (α := fun _ => ℕ) a (fun i : Fin 0 => i.elim0) := by
    show (pascalNe3P p hp0 hp1.le).bind
        (fun a => (PMF.pure (fun i : Fin 0 => i.elim0)).map
          (Fin.cons (α := fun _ => ℕ) a)) = _
    rw [PMF.map]
    refine congrArg _ (funext fun a => ?_)
    rw [PMF.pure_map]
    rfl
  rw [hiid1, PMF.map_comp, PMF.map_apply]
  rw [tsum_eq_single b (fun a ha => by
    rw [if_neg (fun h => ha (by
      simp only [Function.comp_apply] at h
      have h' : (3 : ℤ) + b = 3 + a := by simpa using h
      omega))]),
    if_pos (by
      simp only [Function.comp_apply]
      simp)]

end TaoCollatz.Sec7P
