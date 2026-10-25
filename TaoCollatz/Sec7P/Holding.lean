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

/-! ### The tilted renewal recursion

The renewal recursion itself only uses that the first coordinate of `holdP` is
positive.  This is the `Pascal(p)` version of Tao's (7.34)--(7.35); keeping `p`
and its endpoint hypotheses explicit lets every downstream estimate retain the
uniformity discipline of the campaign.
-/

/-- Slicing `holdP` at a fixed first coordinate recovers its geometric first
marginal. -/
theorem holdP_fst_marginal (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (k : ℕ) :
    ∑' l : ℤ, holdP p hp0 hp1 (k, l) =
      geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
        (pairThreeProb_le_one p hp0 hp1) k := by
  have h1 : (holdP p hp0 hp1).map Prod.fst k =
      ∑' l : ℤ, holdP p hp0 hp1 (k, l) := by
    rw [PMF.map_apply, ENNReal.tsum_prod']
    rw [tsum_eq_single k (fun k' hk' => by simp [Ne.symm hk'])]
    exact tsum_congr fun l => by simp
  rw [← h1, holdP_map_fst]

/-- Expectations depending only on the first holding coordinate reduce to the
geometric first marginal. -/
theorem holdP_tsum_fst (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal * f d.1 =
      ∑' k : ℕ,
        (geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
          (pairThreeProb_le_one p hp0 hp1) k).toReal * f k := by
  let g := geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
    (pairThreeProb_le_one p hp0 hp1)
  have hEN : ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * ENNReal.ofReal (f d.1) =
      ∑' k : ℕ, g k * ENNReal.ofReal (f k) := by
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun k => ?_
    have h : ∀ l : ℤ,
        holdP p hp0 hp1 (k, l) * ENNReal.ofReal (f (k, l).1) =
          holdP p hp0 hp1 (k, l) * ENNReal.ofReal (f k) := fun l => rfl
    rw [tsum_congr h, ENNReal.tsum_mul_right, holdP_fst_marginal]
  calc
    ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal * f d.1
        = ∑' d : ℕ × ℤ,
            (holdP p hp0 hp1 d * ENNReal.ofReal (f d.1)).toReal :=
          tsum_congr fun d => by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _)]
    _ = (∑' d : ℕ × ℤ,
          holdP p hp0 hp1 d * ENNReal.ofReal (f d.1)).toReal :=
      (ENNReal.tsum_toReal_eq fun d =>
        ENNReal.mul_ne_top ((holdP p hp0 hp1).apply_ne_top d)
          ENNReal.ofReal_ne_top).symm
    _ = (∑' k : ℕ, g k * ENNReal.ofReal (f k)).toReal := by rw [hEN]
    _ = ∑' k : ℕ, (g k * ENNReal.ofReal (f k)).toReal :=
      ENNReal.tsum_toReal_eq fun k =>
        ENNReal.mul_ne_top (g.apply_ne_top k) ENNReal.ofReal_ne_top
    _ = ∑' k : ℕ, (g k).toReal * f k :=
      tsum_congr fun k => by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _)]

/-- The real masses of `holdP` sum to one. -/
theorem holdP_tsum_toReal (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun d => (holdP p hp0 hp1).apply_ne_top d),
    (holdP p hp0 hp1).tsum_coe, ENNReal.toReal_one]

/-- The real mass function of `holdP` is summable. -/
theorem holdP_summable_toReal (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Summable fun d : ℕ × ℤ => (holdP p hp0 hp1 d).toReal :=
  ENNReal.summable_toReal (holdP p hp0 hp1).tsum_coe_ne_top

/-- The renewal value for the tilted holding law.  This is Tao's (7.34)--(7.35)
with `hold` replaced by `holdP p`; well-foundedness is uniform in `p` because
every supported increment moves at least one column to the right. -/
noncomputable def QP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) : ℕ → ℤ → ℝ
  | j, l =>
    if half < j then 1
    else Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) *
      ∑' d : ℕ × ℤ,
        if hd : d.1 = 0 then 0
        else (holdP p hp0 hp1 d).toReal *
          QP p hp0 hp1 half W ε (j + d.1) (l + d.2)
  termination_by j _ => half + 1 - j
  decreasing_by omega

/-- Boundary equation for the tilted renewal value. -/
theorem QP_boundary (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (j : ℕ) (l : ℤ) (hj : half < j) :
    QP p hp0 hp1 half W ε j l = 1 := by
  rw [QP]
  simp [hj]

/-- Tao's renewal equation (7.35) for the tilted holding law. -/
theorem QP_rec (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (j : ℕ) (l : ℤ) (hj : j ≤ half) :
    QP p hp0 hp1 half W ε j l =
      Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) *
        ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
          QP p hp0 hp1 half W ε (j + d.1) (l + d.2) := by
  rw [QP]
  rw [if_neg (by omega : ¬ half < j)]
  congr 1
  apply tsum_congr
  intro d
  by_cases h0 : d.1 = 0
  · rw [dif_pos h0, holdP_zero_of_fst_zero p hp0 hp1 h0,
      ENNReal.toReal_zero, zero_mul]
  · rw [dif_neg h0]

/-- The tilted renewal value is nonnegative. -/
theorem QP_nonneg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) :
    ∀ j l, 0 ≤ QP p hp0 hp1 half W ε j l := by
  have key : ∀ n j l, half + 1 - j = n → 0 ≤ QP p hp0 hp1 half W ε j l := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro j l hn
      rcases Nat.lt_or_ge half j with hj | hj
      · rw [QP_boundary p hp0 hp1 half W ε j l hj]
        exact zero_le_one
      · rw [QP_rec p hp0 hp1 half W ε j l hj]
        refine mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun d => ?_)
        rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
        · rw [holdP_zero_of_fst_zero p hp0 hp1 h0, ENNReal.toReal_zero, zero_mul]
        · exact mul_nonneg ENNReal.toReal_nonneg
            (IH (half + 1 - (j + d.1)) (by omega) _ _ rfl)
  exact fun j l => key _ j l rfl

/-- The tilted renewal value is at most one when the damping parameter is
nonnegative. -/
theorem QP_le_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ j l, QP p hp0 hp1 half W ε j l ≤ 1 := by
  have key : ∀ n j l, half + 1 - j = n → QP p hp0 hp1 half W ε j l ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro j l hn
      rcases Nat.lt_or_ge half j with hj | hj
      · rw [QP_boundary p hp0 hp1 half W ε j l hj]
      · rw [QP_rec p hp0 hp1 half W ε j l hj]
        have hexp : Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) ≤ 1 := by
          rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
          exact mul_nonneg (pow_nonneg hε 3)
            (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        have hterm : ∀ d : ℕ × ℤ,
            (holdP p hp0 hp1 d).toReal *
                QP p hp0 hp1 half W ε (j + d.1) (l + d.2)
              ≤ (holdP p hp0 hp1 d).toReal := by
          intro d
          rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
          · rw [holdP_zero_of_fst_zero p hp0 hp1 h0, ENNReal.toReal_zero, zero_mul]
          · calc
              (holdP p hp0 hp1 d).toReal *
                    QP p hp0 hp1 half W ε (j + d.1) (l + d.2)
                  ≤ (holdP p hp0 hp1 d).toReal * 1 :=
                    mul_le_mul_of_nonneg_left
                      (IH (half + 1 - (j + d.1)) (by omega) _ _ rfl)
                      ENNReal.toReal_nonneg
              _ = (holdP p hp0 hp1 d).toReal := mul_one _
        have hterm_nonneg : ∀ d : ℕ × ℤ,
            0 ≤ (holdP p hp0 hp1 d).toReal *
              QP p hp0 hp1 half W ε (j + d.1) (l + d.2) :=
          fun d => mul_nonneg ENNReal.toReal_nonneg
            (QP_nonneg p hp0 hp1 half W ε _ _)
        have hsum_f : Summable fun d : ℕ × ℤ =>
            (holdP p hp0 hp1 d).toReal *
              QP p hp0 hp1 half W ε (j + d.1) (l + d.2) :=
          Summable.of_nonneg_of_le hterm_nonneg hterm
            (holdP_summable_toReal p hp0 hp1)
        have htsum :
            ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
                QP p hp0 hp1 half W ε (j + d.1) (l + d.2) ≤ 1 :=
          le_trans (Summable.tsum_le_tsum hterm hsum_f
              (holdP_summable_toReal p hp0 hp1))
            (holdP_tsum_toReal p hp0 hp1).le
        calc
          Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) *
                ∑' d, (holdP p hp0 hp1 d).toReal *
                  QP p hp0 hp1 half W ε (j + d.1) (l + d.2)
              ≤ 1 * 1 := mul_le_mul hexp htsum (tsum_nonneg hterm_nonneg) zero_le_one
          _ = 1 := mul_one 1
  exact fun j l => key _ j l rfl

end TaoCollatz.Sec7P
