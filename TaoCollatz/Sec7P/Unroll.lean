/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.Monotone
import TaoCollatz.Sec7.Unroll
import TaoCollatz.Prob.Tilt

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

/-- Optional-stopping bound for the finitized first-passage law.  If a
multiplicative weight has one-step expectation at most one, then its
expectation at the first endpoint above any height budget is also at most one.

This formulation is deliberately law-local: it avoids expanding the stopped
walk into a renewal series, whose geometric prefactor is too lossy for the
moving-centre white-exit estimate. -/
theorem fpDistP_tiltZ_le_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (w : ℕ × ℤ → ℝ≥0∞) (hwadd : ∀ a b, w (a + b) = w a * w b)
    (hstep : TaoCollatz.tiltZ (holdP p hp0 hp1) w ≤ 1) :
    ∀ s, TaoCollatz.tiltZ (fpDistP p hp0 hp1 s) w ≤ 1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    rw [TaoCollatz.tiltZ, fpDistP, PMF.tsum_bind_mul]
    refine le_trans (ENNReal.tsum_le_tsum fun d => ?_) hstep
    refine mul_le_mul_right ?_ _
    split_ifs with hcond
    · rw [tsum_eq_single d (fun e he => by
        rw [PMF.pure_apply, if_neg he, zero_mul])]
      rw [PMF.pure_apply, if_pos rfl, one_mul]
    · push Not at hcond
      rw [PMF.tsum_map_mul]
      calc
        (∑' e, fpDistP p hp0 hp1 (s - d.2.toNat) e *
              w (d.1 + e.1, d.2 + e.2)) =
            w d * TaoCollatz.tiltZ (fpDistP p hp0 hp1 (s - d.2.toNat)) w := by
              rw [TaoCollatz.tiltZ, ← ENNReal.tsum_mul_left]
              refine tsum_congr fun e => ?_
              rw [show (d.1 + e.1, d.2 + e.2) = d + e by
                ext <;> rfl, hwadd]
              ring
        _ ≤ w d * 1 := by
          simpa [mul_comm] using
            mul_le_mul_right (IH (s - d.2.toNat) (by omega)) (w d)
        _ = w d := mul_one _

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

/-! ### Uniform circle-method entry -/

/-- The law of the sum of `n` iid tilted holding increments.  This is the
`Pascal(p)` counterpart of `Sec7.holdSum`. -/
noncomputable def holdSumP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n : ℕ) : PMF (ℕ × ℤ) :=
  ((holdP p hp0 hp1).iid n).map fun v => (∑ i, (v i).1, ∑ i, (v i).2)

/-- `holdSumP` is the generic iid sum in the additive monoid `ℕ × ℤ`. -/
theorem holdSumP_eq_iidSum (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    holdSumP p hp0 hp1 n = TaoCollatz.iidSum (holdP p hp0 hp1) n := by
  rw [holdSumP, TaoCollatz.iidSum]
  have hf : (fun v : Fin n → ℕ × ℤ =>
      ((∑ i, (v i).1, ∑ i, (v i).2) : ℕ × ℤ)) =
        fun v : Fin n → ℕ × ℤ => ∑ i, v i := by
    funext v
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
    · rw [Prod.snd_sum]
  rw [hf]

/-- Reduction modulo `N` can only merge masses of the tilted holding sum. -/
theorem holdSumP_le_modPair (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n N : ℕ) (v : ℕ × ℤ) :
    holdSumP p hp0 hp1 n v ≤
      TaoCollatz.iidSum ((holdP p hp0 hp1).map (TaoCollatz.modPair N)) n
        (TaoCollatz.modPair N v) := by
  rw [holdSumP_eq_iidSum]
  calc
    TaoCollatz.iidSum (holdP p hp0 hp1) n v ≤
        ((TaoCollatz.iidSum (holdP p hp0 hp1) n).map (TaoCollatz.modPair N))
          (TaoCollatz.modPair N v) := PMF.apply_le_map_apply _ _ _
    _ = TaoCollatz.iidSum ((holdP p hp0 hp1).map (TaoCollatz.modPair N)) n
          (TaoCollatz.modPair N v) := by
        rw [TaoCollatz.iidSum_map (holdP p hp0 hp1) (TaoCollatz.modPair N)
          (by simp [TaoCollatz.modPair])
          (fun _ _ => by simp [TaoCollatz.modPair])]

/-- The finite circle-method bound for the tilted holding sum. -/
theorem holdSumP_toReal_le_charFn (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n N : ℕ) [NeZero N] (v : ℕ × ℤ) :
    (holdSumP p hp0 hp1 n v).toReal ≤
      ((N : ℝ) ^ 2)⁻¹ * ∑ ξ : ZMod N × ZMod N,
        ‖TaoCollatz.charFn ((holdP p hp0 hp1).map (TaoCollatz.modPair N)) ξ‖ ^ n := by
  refine le_trans (ENNReal.toReal_mono
    ((TaoCollatz.iidSum ((holdP p hp0 hp1).map (TaoCollatz.modPair N)) n).apply_ne_top _)
    (holdSumP_le_modPair p hp0 hp1 n N v)) ?_
  exact TaoCollatz.iidSum_apply_toReal_le
    ((holdP p hp0 hp1).map (TaoCollatz.modPair N)) n (TaoCollatz.modPair N v)

/-- At first coordinate two, conditioning away from `3` cancels the geometric
survival factor.  This exposes the atom masses used by the circle method. -/
theorem holdP_apply_two_toReal (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (b : ℕ) (hb3 : b ≠ 3) :
    (holdP p hp0 hp1 (2, 3 + (b : ℤ))).toReal =
      pairThreeProb p * (pascalP p hp0 hp1.le b).toReal := by
  rw [holdP_apply_two, ENNReal.toReal_mul, geomP_toReal,
    pascalNe3P_toReal, if_neg hb3]
  simp only [OfNat.ofNat, reduceCtorEq, ↓reduceIte, Nat.reduceSub, pow_one]
  have hne : 1 - pairThreeProb p ≠ 0 := by
    have := pairThreeProb_lt_one p hp0 hp1
    linarith
  calc
    pairThreeProb p * (1 - pairThreeProb p) *
          ((1 - pairThreeProb p)⁻¹ * (pascalP p hp0 hp1.le b).toReal)
        = pairThreeProb p * ((1 - pairThreeProb p) *
            (1 - pairThreeProb p)⁻¹) * (pascalP p hp0 hp1.le b).toReal := by ring
    _ = pairThreeProb p * (pascalP p hp0 hp1.le b).toReal := by
      rw [mul_inv_cancel₀ hne, mul_one]

/-- All four aperiodicity atoms retain a common mass `1/4000` throughout the
campaign window.  The deliberately coarse rational floor is independent of `p`. -/
theorem holdP_four_atoms_lower_window {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    let hp0' : 0 < p := by linarith
    let hp1' : p < 1 := by linarith
    (1 / 4000 : ℝ) ≤ (holdP p hp0' hp1' (1, 3)).toReal ∧
    (1 / 4000 : ℝ) ≤ (holdP p hp0' hp1' (2, 5)).toReal ∧
    (1 / 4000 : ℝ) ≤ (holdP p hp0' hp1' (2, 7)).toReal ∧
    (1 / 4000 : ℝ) ≤ (holdP p hp0' hp1' (2, 8)).toReal := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  dsimp only
  have hp_nonneg : 0 ≤ p := hp0'.le
  have hpm : 0 ≤ p - 1 / 5 := sub_nonneg.mpr hp0
  have hsp : 0 ≤ 3 / 5 - p := sub_nonneg.mpr hp1
  have hqlo := (pairThreeProb_mem_window hp0 hp1).1
  have hp2lo : (1 / 5 : ℝ) ^ 2 ≤ p ^ 2 := by nlinarith
  have hp4lo : (1 / 5 : ℝ) ^ 4 ≤ p ^ 4 := by nlinarith [sq_nonneg (p ^ 2 - (1 / 5 : ℝ) ^ 2)]
  have hp40 : 0 ≤ p ^ 4 := pow_nonneg hp_nonneg 4
  have hone : 2 / 5 ≤ 1 - p := by linarith
  have hone0 : 0 ≤ 1 - p := by linarith
  rw [holdP_apply_one_three]
  constructor
  · linarith
  constructor
  · rw [show (5 : ℤ) = 3 + (2 : ℕ) from by norm_num,
      holdP_apply_two_toReal p hp0' hp1' 2 (by norm_num), pascalP_toReal]
    norm_num [pairThreeProb]
    nlinarith [mul_nonneg hp40 hone0,
      mul_le_mul_of_nonneg_left hone (sq_nonneg (p ^ 2))]
  constructor
  · rw [show (7 : ℤ) = 3 + (4 : ℕ) from by norm_num,
      holdP_apply_two_toReal p hp0' hp1' 4 (by norm_num), pascalP_toReal]
    norm_num [pairThreeProb]
    nlinarith [mul_nonneg hp40 (pow_nonneg hone0 3),
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 5) hone 3]
  · rw [show (8 : ℤ) = 3 + (5 : ℕ) from by norm_num,
      holdP_apply_two_toReal p hp0' hp1' 5 (by norm_num), pascalP_toReal]
    norm_num [pairThreeProb]
    nlinarith [mul_nonneg hp40 (pow_nonneg hone0 4),
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 5) hone 4]

/-- Uniform quadratic characteristic-function decay for the tilted holding law.
This is the p-parametrized nondegeneracy input to Tao's Lemma 2.2(i). -/
theorem charFn_holdP_decay_window {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    {N : ℕ} [NeZero N] (hN : 4 ≤ N) (ξ : ZMod N × ZMod N) :
    let hp0' : 0 < p := by linarith
    let hp1' : p < 1 := by linarith
    ‖TaoCollatz.charFn
        ((holdP p hp0' hp1').map (TaoCollatz.modPair N)) ξ‖ ^ 2 ≤
      1 - (((TaoCollatz.nd ξ.1 : ℝ) / N) ^ 2 +
        ((TaoCollatz.nd ξ.2 : ℝ) / N) ^ 2) / 8000000 := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  dsimp only
  set r := (holdP p hp0' hp1').map (TaoCollatz.modPair N) with hr
  have hmass : ∀ d : ℕ × ℤ,
      (holdP p hp0' hp1' d).toReal ≤ (r (TaoCollatz.modPair N d)).toReal := fun d =>
    ENNReal.toReal_mono (r.apply_ne_top _)
      (PMF.apply_le_map_apply (holdP p hp0' hp1') (TaoCollatz.modPair N) d)
  obtain ⟨h13, h25, h27, h28⟩ := holdP_four_atoms_lower_window hp0 hp1
  have h := TaoCollatz.charFn_decay_of_atoms hN r (μ := (1 / 4000 : ℝ))
    (by norm_num)
    (h13.trans (hmass (1, 3))) (h25.trans (hmass (2, 5)))
    (h27.trans (hmass (2, 7))) (h28.trans (hmass (2, 8))) ξ
  simpa only [one_div, one_mul,
    show (8000000 : ℝ)⁻¹ = 2 * (4000 : ℝ)⁻¹ ^ 2 by norm_num,
    div_eq_mul_inv, mul_comm] using h

/-- Uniform center-regime local bound for sums of tilted holding increments. -/
theorem holdSumP_apply_le_center_window {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) (n : ℕ) (v : ℕ × ℤ) :
    let hp0' : 0 < p := by linarith
    let hp1' : p < 1 := by linarith
    (holdSumP p hp0' hp1' n v).toReal ≤
      (32 * 8000000 : ℝ) ^ 2 / (1 + (n : ℝ)) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  dsimp only
  rw [holdSumP_eq_iidSum]
  exact TaoCollatz.iidSum_apply_le_center_of_decay
    (holdP p hp0' hp1') (c := 8000000) (by norm_num)
    (by intro N _ hN ξ; exact charFn_holdP_decay_window hp0 hp1 hN ξ) n v

end TaoCollatz.Sec7P
