/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Prob.Geometric

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

/-- Pointwise real mass of `geomP`. -/
theorem geomP_toReal (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (a : ℕ) :
    (geomP p hp0 hp1 a).toReal = if a = 0 then 0 else p * (1 - p) ^ (a - 1) := by
  rw [geomP]
  exact ENNReal.toReal_ofReal (by
    split_ifs
    · exact le_rfl
    · positivity [sub_nonneg.mpr hp1])

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

/-- Pointwise real mass of `pascalP`. -/
theorem pascalP_toReal (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (b : ℕ) :
    (pascalP p hp0 hp1 b).toReal = if b < 2 then 0
      else ((b - 1 : ℕ) : ℝ) * p ^ 2 * (1 - p) ^ (b - 2) := by
  rw [pascalP]
  exact ENNReal.toReal_ofReal (by
    split_ifs
    · exact le_rfl
    · positivity [sub_nonneg.mpr hp1])

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

/-- `Pascal(p)` conditioned to avoid the distinguished value `3`. -/
noncomputable def pascalNe3P (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) : PMF ℕ :=
  (pascalP p hp0 hp1).filter {b | b ≠ 3} ⟨2, by norm_num, pascalP_two_mem_support p hp0 hp1⟩

/-- The conditioned law has no atom at `3`. -/
theorem pascalNe3P_apply_three (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    pascalNe3P p hp0 hp1 3 = 0 := by
  unfold pascalNe3P
  exact PMF.filter_apply_eq_zero_of_notMem _ (by simp)

end TaoCollatz.Sec7P
