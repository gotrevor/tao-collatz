/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7.HoldBasics
import TaoCollatz.Sec7P.Holding

/-!
# Basic moments of the tilted holding law

This file generalizes the probability-only part of Tao's Lemma 7.6.  It begins
with exact means for `Geom(p)` and its two-draw sum `Pascal(p)`; these are the
inputs for the conditioned increment and holding-law means.
-/

open scoped ENNReal NNReal

namespace TaoCollatz.Sec7P

/-- The mean of the positive geometric law is `1/p`. -/
theorem geomP_mean (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' a : ℕ, geomP p hp0 hp1 a * (a : ℝ≥0∞) = ENNReal.ofReal p⁻¹ := by
  let q : ℝ := 1 - p
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := q) (by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1)
  have hg := hasSum_geometric_of_lt_one hq0 hq1
  have hbase : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * p * q ^ n) p⁻¹ := by
    have hadd := hn.add hg
    have hscaled := hadd.mul_left p
    have hval : p * (q / (1 - q) ^ 2 + (1 - q)⁻¹) = p⁻¹ := by
      dsimp [q]
      field_simp [hp0.ne']
      ring
    rw [hval] at hscaled
    refine hscaled.congr_fun ?_
    intro n
    push_cast
    ring
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    exact Nat.add_right_cancel h
  have hmean : HasSum (fun a : ℕ => (geomP p hp0 hp1 a).toReal * (a : ℝ)) p⁻¹ := by
    apply (hinj.hasSum_iff ?_).mp
    · refine hbase.congr_fun ?_
      intro n
      simp only [Function.comp_apply]
      rw [geomP_toReal, if_neg (by omega)]
      dsimp [q]
      push_cast
      ring
    · intro a ha
      cases a with
      | zero => simp
      | succ a => exact (ha ⟨a, by simp⟩).elim
  have h := TaoCollatz.tsum_mul_ofReal_eq (geomP p hp0 hp1) (fun a => (a : ℝ))
    (fun a => Nat.cast_nonneg a) hmean
  calc
    (∑' a : ℕ, geomP p hp0 hp1 a * (a : ℝ≥0∞)) =
        ∑' a : ℕ, geomP p hp0 hp1 a * ENNReal.ofReal (a : ℝ) := by
          exact tsum_congr fun a => by rw [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal p⁻¹ := h

/-- The shifted positive-geometric mean is `(1-p)/p`. -/
theorem geomP_mean_sub_one (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' k : ℕ, geomP p hp0 hp1 k * ((k - 1 : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal ((1 - p) / p) := by
  have hsplit : (1 : ℝ≥0∞) +
      ∑' k : ℕ, geomP p hp0 hp1 k * ((k - 1 : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal p⁻¹ := by
    have h1 : (1 : ℝ≥0∞) = ∑' k : ℕ, geomP p hp0 hp1 k * 1 := by
      rw [tsum_congr fun k => mul_one (geomP p hp0 hp1 k),
        (geomP p hp0 hp1).tsum_coe]
    calc
      (1 : ℝ≥0∞) + ∑' k : ℕ, geomP p hp0 hp1 k * ((k - 1 : ℕ) : ℝ≥0∞) =
          (∑' k : ℕ, geomP p hp0 hp1 k * 1) +
            ∑' k : ℕ, geomP p hp0 hp1 k * ((k - 1 : ℕ) : ℝ≥0∞) := by rw [← h1]
      _ = ∑' k : ℕ, (geomP p hp0 hp1 k * 1 +
          geomP p hp0 hp1 k * ((k - 1 : ℕ) : ℝ≥0∞)) := ENNReal.tsum_add.symm
      _ = ∑' k : ℕ, geomP p hp0 hp1 k * (k : ℝ≥0∞) := by
        refine tsum_congr fun k => ?_
        rcases Nat.eq_zero_or_pos k with h0 | h1
        · subst k
          rw [geomP_apply]
          simp
        · rw [← mul_add]
          congr 1
          norm_cast
          omega
      _ = ENNReal.ofReal p⁻¹ := geomP_mean p hp0 hp1
  have hratio : 0 ≤ (1 - p) / p := div_nonneg (sub_nonneg.mpr hp1) hp0.le
  have hval : (1 : ℝ≥0∞) + ENNReal.ofReal ((1 - p) / p) =
      ENNReal.ofReal p⁻¹ := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by norm_num,
      ← ENNReal.ofReal_add (by norm_num) hratio]
    congr 1
    field_simp [hp0.ne']
    ring
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).mp (hsplit.trans hval.symm)

/-- The mean of the pair-sum law is `2/p`, obtained from the two-draw
convolution identity rather than recomputing the closed mass. -/
theorem pascalP_mean (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' b : ℕ, pascalP p hp0 hp1 b * (b : ℝ≥0∞) = ENNReal.ofReal (2 / p) := by
  rw [pascalP_eq_iidSum, TaoCollatz.iidSum, PMF.tsum_map_mul]
  have hfun : ∀ v : Fin 2 → ℕ, ((∑ i, v i : ℕ) : ℝ≥0∞) =
      ∑ i, ((v i : ℝ≥0∞)) := by
    intro v
    push_cast
    rfl
  rw [tsum_congr fun v => by rw [hfun]]
  rw [TaoCollatz.tsum_iid_sum_mul (geomP p hp0 hp1)
    (fun a => (a : ℝ≥0∞)) 2, geomP_mean]
  rw [show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1

/-- The mean of `Pascal(p)` conditioned away from `3`.  This is the exact
conditional-expectation identity `(2/p - 3q)/(1-q)`, where
`q = P(Pascal(p)=3)`. -/
theorem pascalNe3P_mean (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∑' b : ℕ, pascalNe3P p hp0 hp1.le b * (b : ℝ≥0∞) =
      ENNReal.ofReal ((2 / p - 3 * pairThreeProb p) / (1 - pairThreeProb p)) := by
  let pp := pascalP p hp0 hp1.le
  let pn := pascalNe3P p hp0 hp1.le
  let q := pairThreeProb p
  have hq := pairThreeProb_basic_bounds p hp0 hp1.le
  have hq_lt : q < 1 := by dsimp [q]; linarith
  have hden_pos : 0 < 1 - q := sub_pos.mpr hq_lt
  have hdiff_pos : 0 < 2 / p - 3 * q := by
    have hinv : 1 ≤ p⁻¹ := (one_le_inv₀ hp0).mpr hp1.le
    rw [div_eq_mul_inv]
    dsimp [q] at hq ⊢
    nlinarith
  have hp3 : pp 3 = ENNReal.ofReal q := by
    dsimp [pp, q]
    rw [pascalP_apply]
    norm_num [pairThreeProb]
  have hsum0 :=
    (ENNReal.tsum_eq_add_tsum_ite
      (f := fun b : ℕ => pp b * (b : ℝ≥0∞)) 3).symm.trans
      (pascalP_mean p hp0 hp1.le)
  have hsum : pp 3 * ((3 : ℕ) : ℝ≥0∞) +
      ∑' b : ℕ, (if b = 3 then 0 else pp b * (b : ℝ≥0∞)) =
        ENNReal.ofReal (2 / p) := by
    convert hsum0 using 1
    congr 1
    apply tsum_congr
    intro b
    by_cases hb : b = 3 <;> simp [hb]
  have hg3 : pp 3 * ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (3 * q) := by
    rw [hp3, show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul hq.1]
    congr 1
    ring
  have hrest : (∑' b : ℕ, if b = 3 then 0 else pp b * (b : ℝ≥0∞)) =
      ENNReal.ofReal (2 / p - 3 * q) := by
    rw [hg3] at hsum
    have hval : ENNReal.ofReal (3 * q) + ENNReal.ofReal (2 / p - 3 * q) =
        ENNReal.ofReal (2 / p) := by
      rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hq.1) hdiff_pos.le]
      congr 1
      ring
    exact (ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp (hsum.trans hval.symm)
  have hfun : ∀ b : ℕ, pn b * (b : ℝ≥0∞) =
      (ENNReal.ofReal (1 - q))⁻¹ *
        (if b = 3 then 0 else pp b * (b : ℝ≥0∞)) := by
    intro b
    by_cases hb : b = 3
    · subst b
      dsimp [pn]
      rw [pascalNe3P_apply_three]
      simp
    · rw [if_neg hb]
      have hmass : pn b = (ENNReal.ofReal (1 - q))⁻¹ * pp b := by
        apply (ENNReal.toReal_eq_toReal_iff'
          ((pascalNe3P p hp0 hp1.le).apply_ne_top b)
          (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by positivity))
            ((pascalP p hp0 hp1.le).apply_ne_top b))).mp
        dsimp [pn, pp, q]
        rw [pascalNe3P_toReal, if_neg hb, ENNReal.toReal_mul, ENNReal.toReal_inv,
          ENNReal.toReal_ofReal hden_pos.le]
      rw [hmass]
      ring
  rw [tsum_congr hfun, ENNReal.tsum_mul_left, hrest]
  rw [← ENNReal.ofReal_inv_of_pos hden_pos,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hden_pos.le)]
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- First-coordinate mean of the tilted holding law: `E Hold₁ = 1/q(p)`. -/
theorem holdP_mean_fst_ennreal (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * (d.1 : ℝ≥0∞) =
      ENNReal.ofReal (pairThreeProb p)⁻¹ := by
  rw [show (fun d : ℕ × ℤ => holdP p hp0 hp1 d * (d.1 : ℝ≥0∞)) =
    fun d : ℕ × ℤ => holdP p hp0 hp1 d *
      ((fun k : ℕ => (k : ℝ≥0∞)) (Prod.fst d)) from rfl,
    ← PMF.tsum_map_mul (holdP p hp0 hp1) Prod.fst (fun k : ℕ => (k : ℝ≥0∞)),
    holdP_map_fst]
  exact geomP_mean (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
    (pairThreeProb_le_one p hp0 hp1)

/-- Second-coordinate mean of the tilted holding law:
`E Hold₂ = q(p)⁻¹ · (2/p)`.  The cancellation of the conditioning factor
`1-q(p)` is the general-`p` form of Tao's calculation `E Hold₂ = 16`. -/
theorem holdP_mean_snd_ennreal (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * ((d.2.toNat : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal ((pairThreeProb p)⁻¹ * (2 / p)) := by
  let q := pairThreeProb p
  have hq0 : 0 < q := pairThreeProb_pos p hp0 hp1
  have hq1 : q ≤ 1 := pairThreeProb_le_one p hp0 hp1
  let meanNe3 := (2 / p - 3 * q) / (1 - q)
  have hqhalf := pairThreeProb_basic_bounds p hp0 hp1.le
  have hq_lt : q < 1 := by dsimp [q]; linarith
  have hmeanNe3 : 0 ≤ meanNe3 := by
    dsimp [meanNe3]
    apply div_nonneg
    · have hinv : 1 ≤ p⁻¹ := (one_le_inv₀ hp0).mpr hp1.le
      rw [div_eq_mul_inv]
      dsimp [q] at hqhalf ⊢
      nlinarith
    · exact sub_nonneg.mpr hq_lt.le
  rw [holdP, PMF.tsum_bind_mul]
  have hinner : ∀ k : ℕ,
      ∑' d : ℕ × ℤ,
          (((pascalNe3P p hp0 hp1.le).iid (k - 1)).map fun v =>
            (k, (3 + ∑ i, v i : ℤ))) d * ((d.2.toNat : ℕ) : ℝ≥0∞) =
        3 + ((k - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal meanNe3 := by
    intro k
    rw [PMF.tsum_map_mul ((pascalNe3P p hp0 hp1.le).iid (k - 1))
      (fun v => ((k, 3 + ∑ i, (v i : ℤ)) : ℕ × ℤ))
      (fun d : ℕ × ℤ => ((d.2.toNat : ℕ) : ℝ≥0∞))]
    have hval : ∀ v : Fin (k - 1) → ℕ,
        ((((3 + ∑ i, (v i : ℤ)) : ℤ).toNat : ℕ) : ℝ≥0∞) =
          3 + ∑ i, ((v i : ℝ≥0∞)) := by
      intro v
      have hnat : ((3 + ∑ i, (v i : ℤ)) : ℤ) = ((3 + ∑ i, v i : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hnat, Int.toNat_natCast]
      push_cast
      ring
    calc
      (∑' v : Fin (k - 1) → ℕ, ((pascalNe3P p hp0 hp1.le).iid (k - 1)) v *
          ((((3 + ∑ i, (v i : ℤ)) : ℤ).toNat : ℕ) : ℝ≥0∞)) =
          ∑' v : Fin (k - 1) → ℕ,
            (((pascalNe3P p hp0 hp1.le).iid (k - 1)) v * 3 +
              ((pascalNe3P p hp0 hp1.le).iid (k - 1)) v *
                ∑ i, ((v i : ℝ≥0∞))) := tsum_congr fun v => by rw [hval, mul_add]
      _ = (∑' v : Fin (k - 1) → ℕ,
            ((pascalNe3P p hp0 hp1.le).iid (k - 1)) v * 3) +
          ∑' v : Fin (k - 1) → ℕ,
            ((pascalNe3P p hp0 hp1.le).iid (k - 1)) v *
              ∑ i, ((v i : ℝ≥0∞)) := ENNReal.tsum_add
      _ = 3 + ((k - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal meanNe3 := by
        rw [ENNReal.tsum_mul_right,
          ((pascalNe3P p hp0 hp1.le).iid (k - 1)).tsum_coe, one_mul,
          TaoCollatz.tsum_iid_sum_mul (pascalNe3P p hp0 hp1.le)
            (fun a => (a : ℝ≥0∞)) (k - 1),
          show (∑' b : ℕ, pascalNe3P p hp0 hp1.le b * (b : ℝ≥0∞)) =
            ENNReal.ofReal meanNe3 by
              dsimp [meanNe3, q]
              exact pascalNe3P_mean p hp0 hp1]
  rw [tsum_congr fun k => by rw [hinner k]]
  calc
    (∑' k : ℕ,
        geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
            (pairThreeProb_le_one p hp0 hp1) k *
          (3 + ((k - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal meanNe3)) =
        (∑' k : ℕ,
          geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
              (pairThreeProb_le_one p hp0 hp1) k * 3) +
          ∑' k : ℕ,
            geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
                (pairThreeProb_le_one p hp0 hp1) k *
              ((k - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal meanNe3 := by
          rw [← ENNReal.tsum_add]
          exact tsum_congr fun k => by rw [mul_add, mul_assoc]
    _ = 3 + ENNReal.ofReal ((1 - q) / q) * ENNReal.ofReal meanNe3 := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
        (geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
          (pairThreeProb_le_one p hp0 hp1)).tsum_coe,
        one_mul, geomP_mean_sub_one]
    _ = ENNReal.ofReal (q⁻¹ * (2 / p)) := by
      have hshift : 0 ≤ (1 - q) / q := div_nonneg (sub_nonneg.mpr hq1) hq0.le
      rw [← ENNReal.ofReal_mul hshift,
        show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
        ← ENNReal.ofReal_add (by norm_num) (mul_nonneg hshift hmeanNe3)]
      congr 1
      dsimp [meanNe3]
      field_simp [hq0.ne', hp0.ne', (sub_pos.mpr hq_lt).ne']
      ring
    _ = ENNReal.ofReal ((pairThreeProb p)⁻¹ * (2 / p)) := by rfl

/-- Real form of the first-coordinate holding mean. -/
theorem holdP_mean_fst (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal * (d.1 : ℝ) =
      (pairThreeProb p)⁻¹ := by
  have h := holdP_mean_fst_ennreal p hp0 hp1
  have hconv : ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * ((d.1 : ℕ) : ℝ≥0∞) =
      ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * ENNReal.ofReal ((d.1 : ℕ) : ℝ) :=
    tsum_congr fun d => by rw [ENNReal.ofReal_natCast]
  rw [hconv] at h
  have hreal := congrArg ENNReal.toReal h
  rw [PMF.toReal_tsum_mul_ofReal (holdP p hp0 hp1)
    (fun d => ((d.1 : ℕ) : ℝ)) (fun d => Nat.cast_nonneg _)] at hreal
  simpa [ENNReal.toReal_ofReal (inv_nonneg.mpr (pairThreeProb_pos p hp0 hp1).le)] using hreal

/-- Real form of the second-coordinate holding mean. -/
theorem holdP_mean_snd (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal * (d.2 : ℝ) =
      (pairThreeProb p)⁻¹ * (2 / p) := by
  have h := holdP_mean_snd_ennreal p hp0 hp1
  have hconv :
      ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * ((d.2.toNat : ℕ) : ℝ≥0∞) =
        ∑' d : ℕ × ℤ, holdP p hp0 hp1 d *
          ENNReal.ofReal ((d.2.toNat : ℕ) : ℝ) :=
    tsum_congr fun d => by rw [ENNReal.ofReal_natCast]
  rw [hconv] at h
  have hreal := congrArg ENNReal.toReal h
  rw [PMF.toReal_tsum_mul_ofReal (holdP p hp0 hp1)
    (fun d => ((d.2.toNat : ℕ) : ℝ)) (fun d => Nat.cast_nonneg _)] at hreal
  have hterm : ∀ d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal * (d.2 : ℝ) =
      (holdP p hp0 hp1 d).toReal * ((d.2.toNat : ℕ) : ℝ) := by
    intro d
    by_cases hd : d ∈ (holdP p hp0 hp1).support
    · have h3 := holdP_support_snd_ge p hp0 hp1 d hd
      have h4 : ((d.2.toNat : ℕ) : ℝ) = (d.2 : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ d.2)
      rw [h4]
    · rw [PMF.mem_support_iff, not_not] at hd
      rw [hd]
      simp
  rw [tsum_congr hterm, hreal]
  exact ENNReal.toReal_ofReal (mul_nonneg
    (inv_nonneg.mpr (pairThreeProb_pos p hp0 hp1).le)
    (div_nonneg (by norm_num) hp0.le))

/-- `(1,3)` belongs to the support of every tilted holding law. -/
theorem holdP_mem_support_one_three (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ((1, 3) : ℕ × ℤ) ∈ (holdP p hp0 hp1).support := by
  rw [holdP, PMF.mem_support_bind_iff]
  refine ⟨1, ?_, ?_⟩
  · exact geomP_mem_support (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
      (pairThreeProb_lt_one p hp0 hp1) 1 le_rfl
  · rw [PMF.mem_support_map_iff]
    refine ⟨fun i => i.elim0, ?_, by simp⟩
    exact TaoCollatz.iid_mem_support (pascalNe3P p hp0 hp1.le) 0 _
      (fun i => i.elim0)

/-- `(2,3+b)` belongs to the tilted holding support for every admissible
Pascal increment `b ≥ 2`, `b ≠ 3`. -/
theorem holdP_mem_support_two (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (b : ℕ) (hb2 : 2 ≤ b) (hb3 : b ≠ 3) :
    ((2, (3 + b : ℤ)) : ℕ × ℤ) ∈ (holdP p hp0 hp1).support := by
  rw [holdP, PMF.mem_support_bind_iff]
  refine ⟨2, ?_, ?_⟩
  · exact geomP_mem_support (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
      (pairThreeProb_lt_one p hp0 hp1) 2 (by norm_num)
  · rw [PMF.mem_support_map_iff]
    refine ⟨fun _ => b, ?_, ?_⟩
    · exact TaoCollatz.iid_mem_support (pascalNe3P p hp0 hp1.le) (2 - 1) _
        (fun _ => pascalNe3P_mem_support p hp0 hp1 b hb2 hb3)
    · simp

/-- The tilted holding law is aperiodic for every `0 < p < 1`: its support is
not contained in a coset of a proper subgroup of `ℤ²`.  The proof uses exactly
Tao's four atoms `(1,3)`, `(2,5)`, `(2,7)`, `(2,8)`. -/
theorem holdP_aperiodic (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (H : AddSubgroup (ℤ × ℤ)) (x : ℤ × ℤ)
    (hsub : ∀ d ∈ (holdP p hp0 hp1).support, ((d.1 : ℤ), d.2) - x ∈ H) : H = ⊤ := by
  have e0 : ((1, 3) : ℤ × ℤ) - x ∈ H :=
    hsub _ (holdP_mem_support_one_three p hp0 hp1)
  have e2 : ((2, 5) : ℤ × ℤ) - x ∈ H := by
    have := hsub _ (holdP_mem_support_two p hp0 hp1 2 le_rfl (by norm_num))
    exact_mod_cast this
  have e4 : ((2, 7) : ℤ × ℤ) - x ∈ H := by
    have := hsub _ (holdP_mem_support_two p hp0 hp1 4 (by norm_num) (by norm_num))
    exact_mod_cast this
  have e5 : ((2, 8) : ℤ × ℤ) - x ∈ H := by
    have := hsub _ (holdP_mem_support_two p hp0 hp1 5 (by norm_num) (by norm_num))
    exact_mod_cast this
  have d2 : ((1, 2) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem e2 e0
    simpa using this
  have d4 : ((1, 4) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem e4 e0
    simpa using this
  have d5 : ((1, 5) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem e5 e0
    simpa using this
  have g01 : ((0, 1) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem d5 d4
    simpa using this
  have g02 : ((0, 2) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem d4 d2
    simpa using this
  have g10 : ((1, 0) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem d2 g02
    simpa using this
  rw [AddSubgroup.eq_top_iff']
  intro z
  have hz : z = z.1 • ((1, 0) : ℤ × ℤ) + z.2 • ((0, 1) : ℤ × ℤ) := by
    have h1 : z.1 • ((1, 0) : ℤ × ℤ) = (z.1, 0) := by
      rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul, mul_one, mul_zero]
    have h2 : z.2 • ((0, 1) : ℤ × ℤ) = (0, z.2) := by
      rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul, mul_one, mul_zero]
    rw [h1, h2, Prod.mk_add_mk, add_zero, zero_add]
  rw [hz]
  exact H.add_mem (H.zsmul_mem g10 z.1) (H.zsmul_mem g01 z.2)

end TaoCollatz.Sec7P
