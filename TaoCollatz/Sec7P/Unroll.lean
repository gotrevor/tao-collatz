/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.Monotone

/-!
# First-passage unrolling for the tilted renewal walk

This is the `Pascal(p)` version of the probability-law-dependent front of
`Sec7/Unroll.lean`.  It proves Tao's (7.45) by the same finite height-budget
recursion, now driven by `holdP p`.  No quantitative estimate enters yet, so the
construction works throughout the natural range `0 < p < 1`.
-/

open scoped ENNReal

namespace TaoCollatz.Sec7P

/-- The stopped tilted renewal value: recurse while the remaining height budget
lasts, and land on `QP` when the next increment overshoots. -/
noncomputable def QPstop (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) : ℕ → ℕ → ℤ → ℝ
  | s, j, l =>
    if half < j then QP p hp0 hp1 half W ε j l
    else Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) *
      ∑' d : ℕ × ℤ,
        if _hd : 1 ≤ d.2 ∧ d.2 ≤ (s : ℤ) then
          (holdP p hp0 hp1 d).toReal *
            QPstop p hp0 hp1 half W ε (s - d.2.toNat) (j + d.1) (l + d.2)
        else (holdP p hp0 hp1 d).toReal *
          QP p hp0 hp1 half W ε (j + d.1) (l + d.2)
  termination_by s _ _ => s
  decreasing_by omega

/-- Tao's first-passage identity (7.45): stopping at any height budget leaves
the tilted renewal value unchanged. -/
theorem QPstop_eq (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) :
    ∀ s (j : ℕ) (l : ℤ),
      QPstop p hp0 hp1 half W ε s j l = QP p hp0 hp1 half W ε j l := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro j l
    rw [QPstop]
    rcases Nat.lt_or_ge half j with hj | hj
    · rw [if_pos hj]
    · rw [if_neg (by omega), QP_rec p hp0 hp1 half W ε j l hj]
      congr 1
      apply tsum_congr
      intro d
      split_ifs with hd
      · rw [IH (s - d.2.toNat) (by omega) (j + d.1) (l + d.2)]
      · rfl

/-- First-passage displacement for the tilted holding walk. -/
noncomputable def fpDistP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ℕ → PMF (ℕ × ℤ)
  | s =>
    (holdP p hp0 hp1).bind fun d =>
      if _h : d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
      else (fpDistP p hp0 hp1 (s - d.2.toNat)).map fun e =>
        (d.1 + e.1, d.2 + e.2)
  termination_by s => s
  decreasing_by
    push Not at _h
    omega

/-- Every tilted first-passage endpoint has positive first coordinate. -/
theorem fpDistP_support_fst_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ s, ∀ e ∈ (fpDistP p hp0 hp1 s).support, 1 ≤ e.1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro e he
    rw [fpDistP, PMF.mem_support_bind_iff] at he
    obtain ⟨d, hd, hde⟩ := he
    have hd1 := holdP_support_fst_pos p hp0 hp1 d hd
    split_ifs at hde with hcond
    · rw [PMF.support_pure, Set.mem_singleton_iff] at hde
      subst hde
      exact hd1
    · rw [PMF.mem_support_map_iff] at hde
      obtain ⟨e', _, he'⟩ := hde
      rw [← he']
      show 1 ≤ d.1 + e'.1
      omega

/-- Every tilted first-passage endpoint overshoots its height budget. -/
theorem fpDistP_support_snd_gt (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ s, ∀ e ∈ (fpDistP p hp0 hp1 s).support, (s : ℤ) < e.2 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro e he
    rw [fpDistP, PMF.mem_support_bind_iff] at he
    obtain ⟨d, hd, hde⟩ := he
    have hd2 := holdP_support_snd_ge p hp0 hp1 d hd
    split_ifs at hde with hcond
    · rw [PMF.support_pure, Set.mem_singleton_iff] at hde
      subst hde
      rcases hcond with h | h
      · omega
      · exact h
    · push Not at hcond
      rw [PMF.mem_support_map_iff] at hde
      obtain ⟨e', he's, he'⟩ := hde
      have hrec := IH (s - d.2.toNat) (by omega) e' he's
      rw [← he']
      show (s : ℤ) < d.2 + e'.2
      have : ((s - d.2.toNat : ℕ) : ℤ) = (s : ℤ) - d.2 := by omega
      omega

/-- Dropping the accumulated damping bounds `QP` by its expectation at the
tilted first-passage endpoint.  This is the inequality form of (7.45) used by
Cases 2 and 3. -/
theorem QP_le_fpDistP_expect (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      ENNReal.ofReal (QP p hp0 hp1 half W ε j l) ≤
        ∑' e : ℕ × ℤ, fpDistP p hp0 hp1 s e *
          ENNReal.ofReal (QP p hp0 hp1 half W ε (j + e.1) (l + e.2)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro j l
    rcases Nat.lt_or_ge half j with hj | hj
    · rw [QP_boundary p hp0 hp1 half W ε j l hj]
      have hRHS :
          ∑' e : ℕ × ℤ, fpDistP p hp0 hp1 s e *
              ENNReal.ofReal (QP p hp0 hp1 half W ε (j + e.1) (l + e.2)) = 1 := by
        rw [← (fpDistP p hp0 hp1 s).tsum_coe]
        refine tsum_congr fun e => ?_
        by_cases h0 : fpDistP p hp0 hp1 s e = 0
        · rw [h0, zero_mul]
        · have h1 := fpDistP_support_fst_pos p hp0 hp1 s e
              (by rwa [PMF.mem_support_iff])
          rw [QP_boundary p hp0 hp1 half W ε (j + e.1) (l + e.2) (by omega),
            ENNReal.ofReal_one, mul_one]
      rw [hRHS, ENNReal.ofReal_one]
    · rw [QP_rec p hp0 hp1 half W ε j l hj]
      have hexp1 : Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        exact mul_nonneg (pow_nonneg hε 3)
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      have hS0 : 0 ≤ ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
          QP p hp0 hp1 half W ε (j + d.1) (l + d.2) :=
        tsum_nonneg fun d => mul_nonneg ENNReal.toReal_nonneg
          (QP_nonneg p hp0 hp1 _ _ _ _ _)
      have hdrop :
          ENNReal.ofReal (Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) *
            ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
              QP p hp0 hp1 half W ε (j + d.1) (l + d.2))
            ≤ ENNReal.ofReal
              (∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
                QP p hp0 hp1 half W ε (j + d.1) (l + d.2)) :=
        ENNReal.ofReal_le_ofReal (by
          calc
            Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) * _
                ≤ 1 * (∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
                  QP p hp0 hp1 half W ε (j + d.1) (l + d.2)) :=
                    mul_le_mul_of_nonneg_right hexp1 hS0
            _ = _ := one_mul _)
      refine le_trans hdrop ?_
      have hlift :
          ENNReal.ofReal
              (∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
                QP p hp0 hp1 half W ε (j + d.1) (l + d.2))
            = ∑' d : ℕ × ℤ, holdP p hp0 hp1 d *
                ENNReal.ofReal (QP p hp0 hp1 half W ε (j + d.1) (l + d.2)) := by
        rw [← PMF.toReal_tsum_mul_ofReal (holdP p hp0 hp1) _
            (fun d => QP_nonneg p hp0 hp1 _ _ _ _ _),
          ENNReal.ofReal_toReal]
        exact ne_top_of_le_ne_top (by simp)
          (PMF.tsum_mul_ofReal_le_one (holdP p hp0 hp1) _
            (fun d => QP_le_one p hp0 hp1 _ _ _ hε _ _))
      rw [hlift, fpDistP, PMF.tsum_bind_mul]
      refine ENNReal.tsum_le_tsum fun d => ?_
      by_cases h0 : holdP p hp0 hp1 d = 0
      · rw [h0, zero_mul, zero_mul]
      · have hd2 := holdP_support_snd_ge p hp0 hp1 d
            (by rwa [PMF.mem_support_iff])
        refine mul_le_mul_right ?_ _
        split_ifs with hcond
        · refine le_of_eq ?_
          rw [tsum_eq_single d (fun e he => by
            rw [PMF.pure_apply, if_neg he, zero_mul])]
          rw [PMF.pure_apply, if_pos rfl, one_mul]
        · push Not at hcond
          rw [PMF.tsum_map_mul]
          have hIH := IH (s - d.2.toNat) (by omega) (j + d.1) (l + d.2)
          refine le_trans hIH (le_of_eq (tsum_congr fun e => ?_))
          rw [show (j + d.1) + e.1 = j + (d.1 + e.1) from by omega,
            show (l + d.2) + e.2 = l + (d.2 + e.2) from by ring]

end TaoCollatz.Sec7P
