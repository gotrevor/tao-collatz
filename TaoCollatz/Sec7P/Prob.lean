/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Prob.LocalBound

/-!
# The tilted geometric and Pascal laws

This file supplies the probability laws used by the uniform-`p` version of Tao's §7.
For `0 < p ≤ 1`, `geomP p` is the geometric law on `{1,2,…}` with mass
`p(1-p)^(a-1)`, and `pascalP p` is the sum-of-two law with mass
`(b-1)p²(1-p)^(b-2)`.  The latter is definitionally presented by its closed mass so
that the bridge to the frozen `pascalWeight` pin is exact and transparent.

The probability-range hypotheses are explicit arguments.  All campaign uses have the
stronger window hypotheses `p ∈ [1/5,3/5]`, and proof irrelevance makes the resulting
PMFs independent of the particular proofs supplied.
-/

open scoped ENNReal NNReal

namespace TaoCollatz.Sec7P

/-- Real geometric masses on the positive naturals sum to one. -/
theorem geomP_real_hasSum (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun a : ℕ => if a = 0 then 0 else p * (1 - p) ^ (a - 1)) 1 := by
  have hgeo := hasSum_geometric_of_lt_one (r := 1 - p)
    (sub_nonneg.mpr hp1) (sub_lt_self 1 hp0)
  have hscaled := hgeo.mul_left p
  have hval : p * (1 - (1 - p))⁻¹ = (1 : ℝ) := by
    rw [show 1 - (1 - p) = p by ring, mul_inv_cancel₀ hp0.ne']
  rw [hval] at hscaled
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    exact Nat.add_right_cancel h
  apply (hinj.hasSum_iff ?_).mp
  · refine hscaled.congr_fun ?_
    intro n
    simp [Function.comp_apply]
  · intro a ha
    cases a with
    | zero => simp
    | succ a => exact (ha ⟨a, by simp⟩).elim

/-- The `Geom(p)` law on `{1,2,…}`. -/
noncomputable def geomP (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) : PMF ℕ :=
  ⟨fun a => ENNReal.ofReal (if a = 0 then 0 else p * (1 - p) ^ (a - 1)), by
    apply ENNReal.hasSum_coe.mpr
    simpa using (geomP_real_hasSum p hp0 hp1).toNNReal (fun a => by
      split_ifs
      · exact le_rfl
      · positivity [sub_nonneg.mpr hp1])⟩

/-- Pointwise `ℝ≥0∞` mass of `geomP`. -/
theorem geomP_apply (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (a : ℕ) :
    geomP p hp0 hp1 a = ENNReal.ofReal
      (if a = 0 then 0 else p * (1 - p) ^ (a - 1)) := rfl

/-- Pointwise real mass of `geomP`. -/
theorem geomP_toReal (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (a : ℕ) :
    (geomP p hp0 hp1 a).toReal = if a = 0 then 0 else p * (1 - p) ^ (a - 1) := by
  rw [geomP]
  exact ENNReal.toReal_ofReal (by
    split_ifs
    · exact le_rfl
    · positivity [sub_nonneg.mpr hp1])

/-- Every positive atom of `Geom(p)` has positive mass when `0 < p < 1`. -/
theorem geomP_mem_support (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (a : ℕ) (ha : 1 ≤ a) : a ∈ (geomP p hp0 hp1.le).support := by
  rw [PMF.mem_support_iff]
  intro hzero
  have hreal := congrArg ENNReal.toReal hzero
  rw [geomP_toReal, if_neg (by omega)] at hreal
  have hpos : 0 < p * (1 - p) ^ (a - 1) := by positivity
  have hzeroReal : p * (1 - p) ^ (a - 1) = 0 := by
    simpa only [ENNReal.toReal_zero] using hreal
  linarith

/-- Real `Pascal(p)` masses (the sum of two positive geometric variables) sum to one. -/
theorem pascalP_real_hasSum (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun b : ℕ => if b < 2 then 0
      else ((b - 1 : ℕ) : ℝ) * p ^ 2 * (1 - p) ^ (b - 2)) 1 := by
  let q : ℝ := 1 - p
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := q) (by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1)
  have hg := hasSum_geometric_of_lt_one hq0 hq1
  have hadd := hn.add hg
  have hbase : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * p ^ 2 * q ^ n) 1 := by
    have hscaled := hadd.mul_left (p ^ 2)
    have hval : p ^ 2 * (q / (1 - q) ^ 2 + (1 - q)⁻¹) = (1 : ℝ) := by
      dsimp [q]
      field_simp [hp0.ne']
      ring
    rw [hval] at hscaled
    refine hscaled.congr_fun ?_
    intro n
    push_cast
    ring
  have hinj : Function.Injective (fun n : ℕ => n + 2) := by
    intro a b h
    exact Nat.add_right_cancel h
  apply (hinj.hasSum_iff ?_).mp
  · refine hbase.congr_fun ?_
    intro n
    simp [Function.comp_apply, q]
  · intro b hb
    rcases b with _ | _ | b
    · simp
    · simp
    · exact (hb ⟨b, by simp⟩).elim

/-- The pair-sum law `Pascal(p)` on `{2,3,…}`. -/
noncomputable def pascalP (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) : PMF ℕ :=
  ⟨fun b => ENNReal.ofReal (if b < 2 then 0
      else ((b - 1 : ℕ) : ℝ) * p ^ 2 * (1 - p) ^ (b - 2)), by
    apply ENNReal.hasSum_coe.mpr
    simpa using (pascalP_real_hasSum p hp0 hp1).toNNReal (fun b => by
      split_ifs
      · exact le_rfl
      · positivity [sub_nonneg.mpr hp1])⟩

/-- Pointwise `ℝ≥0∞` mass of `pascalP`. -/
theorem pascalP_apply (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (b : ℕ) :
    pascalP p hp0 hp1 b = ENNReal.ofReal
      (if b < 2 then 0 else ((b - 1 : ℕ) : ℝ) * p ^ 2 * (1 - p) ^ (b - 2)) := rfl

/-- Pointwise real mass of `pascalP`. -/
theorem pascalP_toReal (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (b : ℕ) :
    (pascalP p hp0 hp1 b).toReal = if b < 2 then 0
      else ((b - 1 : ℕ) : ℝ) * p ^ 2 * (1 - p) ^ (b - 2) := by
  rw [pascalP]
  exact ENNReal.toReal_ofReal (by
    split_ifs
    · exact le_rfl
    · positivity [sub_nonneg.mpr hp1])

/-- `pascalP` is genuinely the law of the sum of two independent `geomP` draws.
The closed mass used in its definition is therefore compatible with the iid-sum
machinery used later for moments and exponential tails. -/
theorem pascalP_eq_iidSum (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    pascalP p hp0 hp1 = TaoCollatz.iidSum (geomP p hp0 hp1) 2 := by
  let g := geomP p hp0 hp1
  have hg1 : TaoCollatz.iidSum g 1 = g := by
    rw [show 1 = 0 + 1 by omega, TaoCollatz.iidSum_succ, TaoCollatz.iidSum_zero]
    simp only [PMF.pure_map, add_zero]
    exact PMF.bind_pure g
  refine PMF.ext fun b => ?_
  rw [show 2 = 1 + 1 by omega, TaoCollatz.iidSum_succ, hg1, PMF.bind_apply]
  have hmap : ∀ a : ℕ, (g.map (a + ·)) b = if a ≤ b then g (b - a) else 0 := by
    intro a
    rw [PMF.map_apply]
    by_cases hab : a ≤ b
    · rw [if_pos hab, tsum_eq_single (b - a)]
      · rw [if_pos (by omega)]
      · intro x hx
        rw [if_neg (by omega)]
    · rw [if_neg hab]
      exact ENNReal.tsum_eq_zero.mpr fun x => by rw [if_neg (by omega)]
  simp_rw [hmap]
  have hterm : ∀ a : ℕ, g a * (if a ≤ b then g (b - a) else 0) =
      if a ∈ Finset.Ico 1 b then
        ENNReal.ofReal (p ^ 2 * (1 - p) ^ (b - 2)) else 0 := by
    intro a
    by_cases ha : a ∈ Finset.Ico 1 b
    · rw [if_pos ha]
      have ha1 : 1 ≤ a := (Finset.mem_Ico.mp ha).1
      have hablt : a < b := (Finset.mem_Ico.mp ha).2
      have hab : a ≤ b := Nat.le_of_lt hablt
      have hba1 : 1 ≤ b - a := Nat.sub_pos_iff_lt.mpr hablt
      rw [if_pos hab]
      rw [show g a = ENNReal.ofReal (p * (1 - p) ^ (a - 1)) by
        dsimp [g]
        rw [geomP_apply, if_neg (by omega : a ≠ 0)]]
      rw [show g (b - a) = ENNReal.ofReal (p * (1 - p) ^ (b - a - 1)) by
        dsimp [g]
        rw [geomP_apply, if_neg (by omega : b - a ≠ 0)]]
      rw [← ENNReal.ofReal_mul (by positivity [sub_nonneg.mpr hp1])]
      congr 1
      have hexp : (a - 1) + (b - a - 1) = b - 2 := by omega
      calc
        p * (1 - p) ^ (a - 1) * (p * (1 - p) ^ (b - a - 1)) =
            p ^ 2 * ((1 - p) ^ (a - 1) * (1 - p) ^ (b - a - 1)) := by ring
        _ = p ^ 2 * (1 - p) ^ (b - 2) := by rw [← pow_add, hexp]
    · rw [if_neg ha]
      by_cases hab : a ≤ b
      · rw [if_pos hab]
        have hz : g a = 0 ∨ g (b - a) = 0 := by
          rw [Finset.mem_Ico, not_and_or] at ha
          rcases ha with ha | ha
          · left
            have : a = 0 := by omega
            subst a
            dsimp [g]
            rw [geomP_apply]
            simp
          · right
            have : b - a = 0 := by omega
            rw [this]
            dsimp [g]
            rw [geomP_apply]
            simp
        rcases hz with hz | hz <;> rw [hz] <;> simp
      · rw [if_neg hab, mul_zero]
  rw [tsum_congr hterm, tsum_eq_sum (s := Finset.Ico 1 b) (fun a ha => if_neg ha)]
  simp only [Finset.sum_ite_mem, Finset.inter_self]
  rw [pascalP_apply]
  by_cases hb : b < 2
  · rw [if_pos hb]
    have : Finset.Ico 1 b = ∅ := by ext x; simp; omega
    simp [this]
  · rw [if_neg hb]
    rw [show ((b - 1 : ℕ) : ℝ) * p ^ 2 * (1 - p) ^ (b - 2) =
      ((b - 1 : ℕ) : ℝ) * (p ^ 2 * (1 - p) ^ (b - 2)) by ring]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (b - 1 : ℕ))]
    rw [Finset.sum_const]
    simp

/-- General-`p` probability bridge: the frozen damping weight is exactly the real
point mass of `pascalP`. -/
theorem pascalWeight_eq_pascalP_toReal (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (b : ℕ) :
    (if 2 ≤ b then ((b : ℝ) - 1) * p ^ 2 * (1 - p) ^ (b - 2) else 0) =
      (pascalP p hp0 hp1 b).toReal := by
  rw [pascalP_toReal]
  by_cases hb : b < 2
  · rw [if_pos hb, if_neg (by omega)]
  · rw [if_neg hb, if_pos (by omega)]
    push_cast [Nat.cast_sub (by omega : 1 ≤ b)]
    rfl

/-- The distinguished `b = 3` atom has probability `q(p) = 2p²(1-p)`. -/
theorem pascalP_apply_three (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (pascalP p hp0 hp1 3).toReal = 2 * p ^ 2 * (1 - p) := by
  rw [pascalP_toReal]
  norm_num

/-- The probability that a `Pascal(p)` draw is the distinguished value `3`. -/
def pairThreeProb (p : ℝ) : ℝ := 2 * p ^ 2 * (1 - p)

/-- On the full probability range, the distinguished atom has mass at most `1/2`.
This coarse bound is enough to keep conditioning away from `3` uniformly non-singular. -/
theorem pairThreeProb_basic_bounds (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ pairThreeProb p ∧ pairThreeProb p ≤ 1 / 2 := by
  have hpnonneg : 0 ≤ p := hp0.le
  have hqnonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hpsq : p ^ 2 ≤ p := by nlinarith [mul_nonneg hpnonneg hqnonneg]
  have hprod : p * (1 - p) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (p - 1 / 2)]
  unfold pairThreeProb
  constructor
  · positivity
  · calc
      2 * p ^ 2 * (1 - p) ≤ 2 * p * (1 - p) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpsq (by norm_num)) hqnonneg
      _ ≤ 1 / 2 := by linarith

/-- On the campaign window, the distinguished-atom probability has the uniform
bounds `8/125 ≤ q(p) ≤ 36/125`. -/
theorem pairThreeProb_mem_window {p : ℝ} (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    8 / 125 ≤ pairThreeProb p ∧ pairThreeProb p ≤ 36 / 125 := by
  have hp_nonneg : 0 ≤ p := by linarith
  have hp_le_one : p ≤ 1 := by linarith
  have hsq : (1 / 5 : ℝ) ^ 2 ≤ p ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp0) (by linarith : 0 ≤ p + 1 / 5)]
  have hone_lo : 2 / 5 ≤ 1 - p := by linarith
  have hone_hi : 1 - p ≤ 4 / 5 := by linarith
  constructor
  · unfold pairThreeProb
    have hmul1 : (1 / 5 : ℝ) ^ 2 * (1 - p) ≤ p ^ 2 * (1 - p) :=
      mul_le_mul_of_nonneg_right hsq (sub_nonneg.mpr hp_le_one)
    have hmul2 : (1 / 5 : ℝ) ^ 2 * (2 / 5) ≤ (1 / 5) ^ 2 * (1 - p) :=
      mul_le_mul_of_nonneg_left hone_lo (sq_nonneg (1 / 5 : ℝ))
    nlinarith
  · unfold pairThreeProb
    have hp_sq_le : p ^ 2 ≤ (3 / 5 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (by linarith : 0 ≤ 3 / 5 + p)]
    have hmul1 : p ^ 2 * (1 - p) ≤ (3 / 5 : ℝ) ^ 2 * (1 - p) :=
      mul_le_mul_of_nonneg_right hp_sq_le (sub_nonneg.mpr hp_le_one)
    have hmul2 : (3 / 5 : ℝ) ^ 2 * (1 - p) ≤ (3 / 5) ^ 2 * (4 / 5) :=
      mul_le_mul_of_nonneg_left hone_hi (sq_nonneg (3 / 5 : ℝ))
    nlinarith

/-- The atom `2` belongs to the support of every `pascalP`; this supplies a
canonical witness for conditioning away from `3`. -/
theorem pascalP_two_mem_support (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    2 ∈ (pascalP p hp0 hp1).support := by
  rw [PMF.mem_support_iff]
  intro hzero
  have hreal := congrArg ENNReal.toReal hzero
  rw [pascalP_toReal] at hreal
  norm_num at hreal
  nlinarith [sq_pos_of_pos hp0]

/-- The unnormalized mass away from `3` is exactly `1 - q(p)`. -/
theorem pascalP_ne_three_mass (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∑' b : ℕ, {b | b ≠ 3}.indicator (pascalP p hp0 hp1) b =
      ENNReal.ofReal (1 - pairThreeProb p) := by
  classical
  let pp := pascalP p hp0 hp1
  have hsplit := ENNReal.tsum_eq_add_tsum_ite (f := fun b : ℕ => pp b) 3
  rw [pp.tsum_coe] at hsplit
  have hind : ∀ b : ℕ, {b | b ≠ 3}.indicator pp b =
      if b = 3 then 0 else pp b := by
    intro b
    by_cases hb : b = 3
    · subst b
      simp
    · simp [hb]
  rw [tsum_congr hind]
  have hsplit' : 1 = pp 3 + (∑' b : ℕ, if b = 3 then 0 else pp b) := by
    convert hsplit using 1
    congr 1
    apply tsum_congr
    intro b
    by_cases hb : b = 3 <;> simp [hb]
  have hrest : (∑' b : ℕ, if b = 3 then 0 else pp b) = 1 - pp 3 := by
    apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
    rw [add_comm]
    exact hsplit'.symm
  rw [hrest]
  have hp3 : pp 3 = ENNReal.ofReal (pairThreeProb p) := by
    dsimp [pp]
    rw [pascalP_apply]
    norm_num [pairThreeProb]
  rw [hp3]
  simpa using (ENNReal.ofReal_sub 1 (pairThreeProb_basic_bounds p hp0 hp1).1).symm

/-- `Pascal(p)` conditioned to avoid the distinguished value `3`. -/
noncomputable def pascalNe3P (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) : PMF ℕ :=
  (pascalP p hp0 hp1).filter {b | b ≠ 3} ⟨2, by norm_num, pascalP_two_mem_support p hp0 hp1⟩

/-- The conditioned law has no atom at `3`. -/
theorem pascalNe3P_apply_three (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    pascalNe3P p hp0 hp1 3 = 0 := by
  unfold pascalNe3P
  exact PMF.filter_apply_eq_zero_of_notMem _ (by simp)

/-- Exact real mass of the conditioned law: delete the `3` atom and divide by
`1 - q(p)`.  In particular the normalizer is explicit and uniformly bounded away
from zero on the campaign window. -/
theorem pascalNe3P_toReal (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (b : ℕ) :
    (pascalNe3P p hp0 hp1 b).toReal =
      if b = 3 then 0 else
        (1 - pairThreeProb p)⁻¹ * (pascalP p hp0 hp1 b).toReal := by
  classical
  have hq := pairThreeProb_basic_bounds p hp0 hp1
  unfold pascalNe3P
  rw [PMF.filter_apply]
  by_cases hb : b = 3
  · subst b
    simp
  · rw [if_neg hb, Set.indicator_of_mem (by simpa), pascalP_ne_three_mass]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (hq.2.trans (by norm_num)))]
    ring

/-- Every admissible positive Pascal atom other than `3` remains in the
conditioned support. -/
theorem pascalNe3P_mem_support (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (b : ℕ) (hb2 : 2 ≤ b) (hb3 : b ≠ 3) :
    b ∈ (pascalNe3P p hp0 hp1.le).support := by
  rw [PMF.mem_support_iff]
  intro hzero
  have hreal := congrArg ENNReal.toReal hzero
  rw [pascalNe3P_toReal, if_neg hb3, pascalP_toReal, if_neg (by omega)] at hreal
  have hq_lt : pairThreeProb p < 1 := by
    have hq := pairThreeProb_basic_bounds p hp0 hp1.le
    linarith
  have hbpos : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_iff_lt.mpr (by omega : 1 < b))
  have hone : 0 < 1 - p := sub_pos.mpr hp1
  have hden : 0 < 1 - pairThreeProb p := sub_pos.mpr hq_lt
  have hpos : 0 < (1 - pairThreeProb p)⁻¹ *
      (((b - 1 : ℕ) : ℝ) * p ^ 2 * (1 - p) ^ (b - 2)) := by
    positivity
  have hzeroReal : (1 - pairThreeProb p)⁻¹ *
      (((b - 1 : ℕ) : ℝ) * p ^ 2 * (1 - p) ^ (b - 2)) = 0 := by
    simpa only [ENNReal.toReal_zero] using hreal
  linarith

end TaoCollatz.Sec7P
