/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.BlackEdgeQ
import TaoCollatz.Sec7.Case3

/-!
# Tilted Case 3 of Proposition 7.8 — the X11 assembly at `Pascal(p)`

This module generalizes `Sec7/Case3.lean` ((7.53)–(7.67)) to the tilted holding
law `holdP p`, the finer triangle family `TriangleFamilyP`, the finer white set
`whiteSetP` at scale `epsP`, and the tilted first-passage laws `fpDistP` /
`fpDistPlusP`, uniformly on the Pascal window `p ∈ [1/5, 3/5]`.

The law-independent pieces (`pathSum` arithmetic, the (7.67) window iterate
`encWindowIter`, the convergent-series helpers, the base-4 scaled numeric
`estar_scaled_numeric_at`) are imported from the fixed-law module unchanged.

## How `p` enters (operator addendum, 2026-10-25)

* The first passage to height `s` lands at column `≈ (p/2)·s`, and the triangle
  budget (7.52) gives `s ≤ 3.2(m+2)`; at `p ≤ 3/5` this is `≤ 0.96(m+2)`.  So the
  bad-column threshold is `t₂ = 49/50` (Tao's `0.9`), and the column weight on
  the good column is `≤ 50^A·m^{-A}` (Tao's `10^A`).
* Consequently every `10^{-A-k}` probability target becomes `50^{-A-k}`, and the
  E∗ union must be scaled so that `4^{c}` beats `50`: this module re-uses the
  fixed-law base-16 numeric at a rescaled exponent `A₁ = log₁₀50·(A+3) − 3`, which
  turns `10^{-A₁-3}` into exactly `50^{-A-3}`.
* The encounter-depth gate `g` must fit under `(1 − t₂)·m = m/50` (Tao: `m/10`).
-/

namespace TaoCollatz.Sec7P

open scoped ENNReal

/-! ### Encounter-fold invariants (interface to the tilted X9 fold `encStepP`) -/

/-- `encStepP` always advances the position by the step. -/
theorem encStepP_pos {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (σ : EncState) (d : ℕ × ℤ) : (encStepP F R g σ d).pos = σ.pos + d := by
  rw [encStepP]
  split <;> rfl

/-- The fold's position is the start plus the sum of the steps taken. -/
theorem encFoldP_pos {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ) :
    ∀ (L : List (ℕ × ℤ)) (σ : EncState),
      (L.foldl (encStepP F R g) σ).pos = σ.pos + L.sum := by
  intro L
  induction L with
  | nil => intro σ; simp
  | cons d L IH =>
    intro σ
    rw [List.foldl_cons, IH, encStepP_pos, List.sum_cons, add_assoc]

/-- The fold's count is monotone in the path prefix. -/
theorem encFoldP_count_le {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ) :
    ∀ (L : List (ℕ × ℤ)) (σ : EncState),
      σ.count ≤ (L.foldl (encStepP F R g) σ).count := by
  intro L
  induction L with
  | nil => intro σ; simp
  | cons d L IH =>
    intro σ
    exact le_trans (encStepP_count_le F R g σ d) (IH _)

/-- `encStepP` preserves `banked ≤ cumWhite`. -/
theorem encStepP_banked_le {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (σ : EncState) (d : ℕ × ℤ) (h : σ.banked ≤ σ.cumWhite) :
    (encStepP F R g σ d).banked ≤ (encStepP F R g σ d).cumWhite := by
  rw [encStepP]
  split <;> dsimp only <;> split_ifs <;> omega

/-- Fold invariant: `banked ≤ cumWhite` propagates along any path. -/
theorem encFoldP_banked_le {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ) :
    ∀ (L : List (ℕ × ℤ)) (σ : EncState), σ.banked ≤ σ.cumWhite →
      (L.foldl (encStepP F R g) σ).banked ≤ (L.foldl (encStepP F R g) σ).cumWhite := by
  intro L
  induction L with
  | nil => intro σ h; simpa using h
  | cons d L IH =>
    intro σ h
    exact IH _ (encStepP_banked_le F R g σ d h)

open scoped Classical in
/-- `encStepP` adds exactly the new position's finer white-strip indicator to the
running white count. -/
theorem encStepP_cumWhite {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (σ : EncState) (d : ℕ × ℤ) :
    (encStepP F R g σ d).cumWhite
      = σ.cumWhite + (if σ.pos + d ∈ whiteStripP n ξ then 1 else 0) := by
  rw [encStepP]
  split <;> rfl

open scoped Classical in
/-- The fold's running white count is the start count plus the number of finer
white-strip positions visited (the positions AFTER each step). -/
theorem encFoldP_cumWhite {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ) :
    ∀ (T : ℕ) (v : Fin T → ℕ × ℤ) (σ : EncState),
      ((List.ofFn v).foldl (encStepP F R g) σ).cumWhite
        = σ.cumWhite + (Finset.range T).sum
            (fun p => if σ.pos + pathSum v (p + 1) ∈ whiteStripP n ξ then 1 else 0) := by
  intro T
  induction T with
  | zero => intro v σ; simp
  | succ T IH =>
    intro v σ
    rw [List.ofFn_succ, List.foldl_cons,
      IH (fun i : Fin T => v i.succ) (encStepP F R g σ (v 0)),
      encStepP_cumWhite, encStepP_pos, Finset.sum_range_succ']
    have h0 : pathSum v 1 = v 0 := by
      simpa using pathSum_head v 0
    have hstep : ∀ p : ℕ,
        pathSum v (p + 1 + 1) = v 0 + pathSum (fun i : Fin T => v i.succ) (p + 1) :=
      fun p => pathSum_head v (p + 1)
    rw [h0]
    have hsum : ∀ p ∈ Finset.range T,
        (if σ.pos + v 0 + pathSum (fun i : Fin T => v i.succ) (p + 1) ∈ whiteStripP n ξ
          then (1 : ℕ) else 0)
        = (if σ.pos + pathSum v (p + 1 + 1) ∈ whiteStripP n ξ then 1 else 0) := by
      intro p _
      rw [hstep p, add_assoc]
    rw [Finset.sum_congr rfl hsum]
    omega

/-! ### The tilted (7.53) master iterate -/

/-- **Iterated (7.35) with retained damping — the walk half**, for the tilted
holding law: for ANY start, the renewal value is bounded by the `P`-step average
of the accumulated in-strip white damping times the value at the end position. -/
theorem QP_le_walk_damped (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (P : ℕ) (j : ℕ) (l : ℤ),
      ENNReal.ofReal (QP p hp0 hp1 half W ε j l)
        ≤ ∑' v : Fin P → ℕ × ℤ, (holdP p hp0 hp1).iid P v *
            ENNReal.ofReal (
              Real.exp (-(ε ^ 3) * ∑ p' ∈ Finset.range P,
                Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                  (j + (pathSum v p').1, l + (pathSum v p').2)) *
              QP p hp0 hp1 half W ε (j + (pathSum v P).1) (l + (pathSum v P).2)) := by
  set hold := holdP p hp0 hp1 with hholddef
  intro P
  induction P with
  | zero =>
    intro j l
    rw [PMF.tsum_iid_zero_mul hold
      (fun v : Fin 0 → ℕ × ℤ => ENNReal.ofReal (
        Real.exp (-(ε ^ 3) * ∑ p' ∈ Finset.range 0,
          Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
            (j + (pathSum v p').1, l + (pathSum v p').2)) *
        QP p hp0 hp1 half W ε (j + (pathSum v 0).1) (l + (pathSum v 0).2)))]
    simp
  | succ P IH =>
    intro j l
    rw [PMF.tsum_iid_succ_mul hold P]
    rcases Nat.lt_or_ge half j with hout | hin
    · rw [QP_boundary p hp0 hp1 _ _ _ _ _ hout, ENNReal.ofReal_one]
      have hone : ∀ (d : ℕ × ℤ) (w : Fin P → ℕ × ℤ),
          ENNReal.ofReal (
            Real.exp (-(ε ^ 3) * ∑ p' ∈ Finset.range (P + 1),
              Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (j + (pathSum (Fin.cons d w) p').1,
                  l + (pathSum (Fin.cons d w) p').2)) *
            QP p hp0 hp1 half W ε (j + (pathSum (Fin.cons d w) (P + 1)).1)
              (l + (pathSum (Fin.cons d w) (P + 1)).2)) = 1 := by
        intro d w
        have hind : ∀ p' : ℕ,
            Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) (1 : ℕ × ℤ → ℝ)
              (j + (pathSum (Fin.cons d w) p').1,
                l + (pathSum (Fin.cons d w) p').2) = 0 := by
          intro p'
          refine Set.indicator_of_notMem (fun hmem => ?_) 1
          have := hmem.2
          simp only [Set.mem_ofPred_eq] at this
          omega
        have hQ : QP p hp0 hp1 half W ε (j + (pathSum (Fin.cons d w) (P + 1)).1)
            (l + (pathSum (Fin.cons d w) (P + 1)).2) = 1 :=
          QP_boundary p hp0 hp1 _ _ _ _ _ (by omega)
        rw [hQ, mul_one, Finset.sum_congr rfl (fun p' _ => hind p')]
        simp
      refine le_of_eq ?_
      have hin1 : (∑' w : Fin P → ℕ × ℤ, hold.iid P w * 1) = 1 := by
        rw [tsum_congr fun w : Fin P → ℕ × ℤ => mul_one (hold.iid P w),
          (hold.iid P).tsum_coe]
      have h1 : (1 : ℝ≥0∞) = ∑' d : ℕ × ℤ, hold d * ∑' w : Fin P → ℕ × ℤ,
          hold.iid P w * 1 :=
        (hold.tsum_coe.symm).trans
          (tsum_congr fun d => by rw [hin1, mul_one])
      refine h1.trans (tsum_congr fun d => ?_)
      refine congrArg (hold d * ·) (tsum_congr fun w => ?_)
      rw [hone d w]
    · rw [QP_rec p hp0 hp1 _ _ _ _ _ hin]
      have hQS0 : 0 ≤ ∑' d : ℕ × ℤ, (hold d).toReal * QP p hp0 hp1 half W ε (j + d.1) (l + d.2) :=
        tsum_nonneg fun d => mul_nonneg ENNReal.toReal_nonneg (QP_nonneg p hp0 hp1 _ _ _ _ _)
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hlift : ENNReal.ofReal
            (∑' d : ℕ × ℤ, (hold d).toReal * QP p hp0 hp1 half W ε (j + d.1) (l + d.2))
          = ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (QP p hp0 hp1 half W ε (j + d.1) (l + d.2)) := by
        rw [← PMF.toReal_tsum_mul_ofReal hold _ (fun d => QP_nonneg p hp0 hp1 _ _ _ _ _),
          ENNReal.ofReal_toReal]
        exact ne_top_of_le_ne_top (by simp)
          (PMF.tsum_mul_ofReal_le_one hold _ (fun d => QP_le_one p hp0 hp1 _ _ _ hε _ _))
      rw [hlift, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun d => ?_
      rw [← mul_assoc, mul_comm (ENNReal.ofReal (Real.exp _)) (hold d), mul_assoc]
      refine mul_le_mul_right ?_ (hold d)
      have hIH := IH (j + d.1) (l + d.2)
      calc ENNReal.ofReal (Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)))
            * ENNReal.ofReal (QP p hp0 hp1 half W ε (j + d.1) (l + d.2))
          ≤ ENNReal.ofReal (Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)))
            * ∑' w : Fin P → ℕ × ℤ, hold.iid P w *
              ENNReal.ofReal (
                Real.exp (-(ε ^ 3) * ∑ p' ∈ Finset.range P,
                  Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                    (j + d.1 + (pathSum w p').1, l + d.2 + (pathSum w p').2)) *
                QP p hp0 hp1 half W ε (j + d.1 + (pathSum w P).1) (l + d.2 + (pathSum w P).2)) :=
            mul_le_mul_right hIH _
        _ = _ := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun w => ?_
            rw [← mul_assoc, mul_comm (ENNReal.ofReal (Real.exp _)) (hold.iid P w),
              mul_assoc]
            refine congrArg _ ?_
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc,
              ← Real.exp_add]
            have hend : pathSum (Fin.cons d w) (P + 1) = d + pathSum w P :=
              pathSum_cons d w P
            have hexp : -(ε ^ 3) * Set.indicator W 1 (j, l)
                  + -(ε ^ 3) * ∑ p' ∈ Finset.range P,
                    Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                      (j + d.1 + (pathSum w p').1, l + d.2 + (pathSum w p').2)
                = -(ε ^ 3) * ∑ p' ∈ Finset.range (P + 1),
                    Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                      (j + (pathSum (Fin.cons d w) p').1,
                        l + (pathSum (Fin.cons d w) p').2) := by
              rw [Finset.sum_range_succ']
              have h0 : Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) (1 : ℕ × ℤ → ℝ)
                  (j + (pathSum (Fin.cons d w) 0).1, l + (pathSum (Fin.cons d w) 0).2)
                  = Set.indicator W 1 (j, l) := by
                rw [pathSum_zero]
                simp only [Prod.fst_zero, Prod.snd_zero, add_zero]
                by_cases hW : (j, l) ∈ W
                · have hmem : (j, l) ∈ W ∩ {q : ℕ × ℤ | q.1 ≤ half} :=
                    ⟨hW, by simpa using hin⟩
                  rw [Set.indicator_of_mem hW, Set.indicator_of_mem hmem]
                · rw [Set.indicator_of_notMem hW,
                    Set.indicator_of_notMem (fun hmem => hW hmem.1)]
              have hstep : ∀ p' ∈ Finset.range P,
                  Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) (1 : ℕ × ℤ → ℝ)
                    (j + (pathSum (Fin.cons d w) (p' + 1)).1,
                      l + (pathSum (Fin.cons d w) (p' + 1)).2)
                  = Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                    (j + d.1 + (pathSum w p').1, l + d.2 + (pathSum w p').2) := by
                intro p' _
                rw [pathSum_cons]
                congr 2
                · show j + (d.1 + (pathSum w p').1) = j + d.1 + (pathSum w p').1
                  omega
                · show l + (d.2 + (pathSum w p').2) = l + d.2 + (pathSum w p').2
                  ring
              rw [Finset.sum_congr rfl hstep, h0]
              ring
            rw [hexp, hend]
            congr 3
            · show j + d.1 + (pathSum w P).1 = j + (d.1 + (pathSum w P).1)
              omega
            · show l + d.2 + (pathSum w P).2 = l + (d.2 + (pathSum w P).2)
              ring

/-- **The tilted (7.53) master iterate**: through the first passage at budget `s`
and `P` further `holdP p` steps, the renewal value is bounded by the joint average
of the accumulated white-strip damping times the end value. -/
theorem QP_le_damped_iter (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε)
    (s P : ℕ) (j : ℕ) (l : ℤ) :
    ENNReal.ofReal (QP p hp0 hp1 half W ε j l)
      ≤ ∑' e : ℕ × ℤ, fpDistP p hp0 hp1 s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p hp0 hp1).iid P v *
          ENNReal.ofReal (
            Real.exp (-(ε ^ 3) * ∑ p' ∈ Finset.range P,
              Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (j + e.1 + (pathSum v p').1, l + e.2 + (pathSum v p').2)) *
            QP p hp0 hp1 half W ε (j + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)) := by
  refine le_trans (QP_le_fpDistP_expect p hp0 hp1 half W ε hε s j l) ?_
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
  exact QP_le_walk_damped p hp0 hp1 half W ε hε P (j + e.1) (l + e.2)

/-! ### The prefix-marginal law: post-passage positions are `fpDistPlusP` -/

/-- **Prefix marginal of the tilted iid walk**: integrating an observable of the
`k`-step partial sum over the `T`-step walk (`k ≤ T`) is integrating it against
the `k`-fold iid sum. -/
theorem iid_pathSum_lawP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ (T k : ℕ), k ≤ T → ∀ (f : ℕ × ℤ → ℝ≥0∞),
      ∑' v : Fin T → ℕ × ℤ, (holdP p hp0 hp1).iid T v * f (pathSum v k)
        = ∑' d : ℕ × ℤ, iidSum (holdP p hp0 hp1) k d * f d := by
  set hold := holdP p hp0 hp1 with hholddef
  intro T
  induction T with
  | zero =>
    intro k hk f
    rw [Nat.le_zero.mp hk]
    rw [PMF.tsum_iid_zero_mul hold (fun v : Fin 0 → ℕ × ℤ => f (pathSum v 0))]
    rw [iidSum_zero]
    rw [tsum_eq_single (0 : ℕ × ℤ) (fun d hd => by
      rw [PMF.pure_apply, if_neg hd, zero_mul])]
    rw [PMF.pure_apply, if_pos rfl, one_mul, pathSum_zero]
  | succ T IH =>
    intro k hk f
    rw [PMF.tsum_iid_succ_mul hold T (fun v => f (pathSum v k))]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hinner : ∀ d : ℕ × ℤ,
          ∑' w : Fin T → ℕ × ℤ, hold.iid T w * f (pathSum (Fin.cons d w) 0)
            = f 0 := by
        intro d
        rw [tsum_congr fun w : Fin T → ℕ × ℤ => by rw [pathSum_zero],
          ENNReal.tsum_mul_right, (hold.iid T).tsum_coe, one_mul]
      rw [tsum_congr fun d => by rw [hinner d]]
      rw [ENNReal.tsum_mul_right, hold.tsum_coe, one_mul, iidSum_zero]
      rw [tsum_eq_single (0 : ℕ × ℤ) (fun d hd => by
        rw [PMF.pure_apply, if_neg hd, zero_mul])]
      rw [PMF.pure_apply, if_pos rfl, one_mul]
    · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hkpos
      rw [tsum_congr fun d : ℕ × ℤ => by
        rw [tsum_congr fun w : Fin T → ℕ × ℤ => by
          rw [show 1 + q = q + 1 from by omega, pathSum_cons]]]
      have hIH : ∀ d : ℕ × ℤ,
          ∑' w : Fin T → ℕ × ℤ, hold.iid T w * f (d + pathSum w q)
            = ∑' x : ℕ × ℤ, iidSum hold q x * f (d + x) :=
        fun d => IH q (by omega) (fun x => f (d + x))
      rw [tsum_congr fun d => by rw [hIH d]]
      rw [show 1 + q = q + 1 from by omega, iidSum_succ, PMF.tsum_bind_mul]
      exact tsum_congr fun d => by rw [PMF.tsum_map_mul]

/-- **The `fpDistPlusP` prefix marginal, in walk form**: integrating an observable
`g` of the position `e + pathSum v k` against `fpDistP s ⊗ holdP.iid T` (`k ≤ T`)
equals integrating `g` against the convolution marginal `fpDistPlusP s k`. -/
theorem fpDistP_walk_eq_fpDistPlusP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (s : ℕ) {T k : ℕ} (hk : k ≤ T) (g : ℕ × ℤ → ℝ≥0∞) :
    ∑' e : ℕ × ℤ, fpDistP p hp0 hp1 s e *
        ∑' v : Fin T → ℕ × ℤ, (holdP p hp0 hp1).iid T v * g (e + pathSum v k)
      = ∑' x : ℕ × ℤ, fpDistPlusP p hp0 hp1 s k x * g x := by
  have hRHS : ∑' x : ℕ × ℤ, fpDistPlusP p hp0 hp1 s k x * g x
      = ∑' e : ℕ × ℤ, fpDistP p hp0 hp1 s e *
          ∑' d : ℕ × ℤ, iidSum (holdP p hp0 hp1) k d * g (e + d) := by
    have hdef : (∑' x : ℕ × ℤ, fpDistPlusP p hp0 hp1 s k x * g x)
        = ∑' x : ℕ × ℤ,
            ((fpDistP p hp0 hp1 s).bind
              (fun e => (iidSum (holdP p hp0 hp1) k).map fun w => e + w)) x * g x := by
      simp only [fpDistPlusP, holdSumP_eq_iidSum]
    rw [hdef, PMF.tsum_bind_mul]
    exact tsum_congr fun e => by rw [PMF.tsum_map_mul]
  rw [hRHS]
  refine tsum_congr fun e => ?_
  congr 1
  simpa only [] using iid_pathSum_lawP p hp0 hp1 T k hk (fun d => g (e + d))

/-! ### The per-`k` big-triangle walk mass bound (tilted X10 in walk form) -/

/-- **The per-`k` big-triangle walk mass bound** at `Pascal(p)`, explicit-constant
form at `C_encTriP`/`c_encTriP`, threshold `A ≥ 100`: the chance that the `T`-step
walk's position at time `k` (`k ≤ T`, started at `(j,l)` after the first passage)
lands in a size-`≥ s'` finer triangle is bounded by tilted Lemma 7.10. -/
theorem bigTriangle_walk_le_rpowP_explicitC :
    ∀ (A : ℝ), 100 ≤ A →
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ), (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (T k s' : ℕ), k ≤ T → 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
        (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin T → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid T v *
          Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ≥0∞)
            (j + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)).toReal
          ≤ C_encTriP * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
            + C_encTriP * Real.exp (-c_encTriP * A ^ 2 * (1 + (k : ℝ))) := by
  intro A hA p hp0 hp1 n ξ hξ F t₀ ht₀ j l hmem s hs hdeep T k s' hkT hs'1 hs'm
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  have hind_eq : ∀ y : ℕ × ℤ,
      Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ≥0∞) y
        = ENNReal.ofReal (Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) y) := by
    intro y
    by_cases h : y ∈ bigTriangleSetP F s'
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp
  have hpos : ∀ (e : ℕ × ℤ) (v : Fin T → ℕ × ℤ),
      ((j + e.1 + (pathSum v k).1 : ℕ), (l + e.2 + (pathSum v k).2 : ℤ))
        = ((j : ℕ), (l : ℤ)) + (e + pathSum v k) := by
    intro e v; ext <;> simp [add_assoc]
  have hwalk : (∑' e : ℕ × ℤ, fpDistP p hp0' hp1' s e *
        ∑' v : Fin T → ℕ × ℤ, (holdP p hp0' hp1').iid T v *
        Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ≥0∞)
          (j + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
      = ∑' x : ℕ × ℤ, fpDistPlusP p hp0' hp1' s k x *
          Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ≥0∞) (((j : ℕ), (l : ℤ)) + x) := by
    have hconv : (∑' e : ℕ × ℤ, fpDistP p hp0' hp1' s e *
          ∑' v : Fin T → ℕ × ℤ, (holdP p hp0' hp1').iid T v *
          Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ≥0∞)
            (j + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
        = ∑' e : ℕ × ℤ, fpDistP p hp0' hp1' s e *
            ∑' v : Fin T → ℕ × ℤ, (holdP p hp0' hp1').iid T v *
            Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ≥0∞)
              (((j : ℕ), (l : ℤ)) + (e + pathSum v k)) := by
      refine tsum_congr fun e => ?_
      congr 1
      refine tsum_congr fun v => ?_
      congr 1
      exact congrArg _ (hpos e v)
    rw [hconv]
    exact fpDistP_walk_eq_fpDistPlusP p hp0' hp1' s hkT
      (fun x : ℕ × ℤ => Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ≥0∞)
        (((j : ℕ), (l : ℤ)) + x))
  have hstep : ∑' x : ℕ × ℤ, fpDistPlusP p hp0' hp1' s k x *
        Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ≥0∞) (((j : ℕ), (l : ℤ)) + x)
      = ∑' x : ℕ × ℤ, fpDistPlusP p hp0' hp1' s k x *
          ENNReal.ofReal
            (Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (((j : ℕ), (l : ℤ)) + x)) :=
    tsum_congr fun x => by rw [hind_eq]
  have heq : (∑' e : ℕ × ℤ, fpDistP p hp0' hp1' s e *
        ∑' v : Fin T → ℕ × ℤ, (holdP p hp0' hp1').iid T v *
        Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ≥0∞)
          (j + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)).toReal
      = ∑' x : ℕ × ℤ, (fpDistPlusP p hp0' hp1' s k x).toReal
          * Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (((j : ℕ), (l : ℤ)) + x) := by
    rw [hwalk, hstep]
    exact PMF.toReal_tsum_mul_ofReal (fpDistPlusP p hp0' hp1' s k)
      (fun x => Set.indicator (bigTriangleSetP F s') (1 : ℕ × ℤ → ℝ) (((j : ℕ), (l : ℤ)) + x))
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  rw [heq]
  exact triangle_encounter_le_rpowP_explicitC A hA p hp0 hp1 n ξ hξ F t₀ ht₀ j l hmem s hs
    hdeep k s' hs'1 hs'm

/-! ### The tilted (7.56) Markov bound -/

open scoped Classical in
/-- **The `F∗` Markov bound** for the tilted fold: under Lemma 7.9's conclusion
(`hbound`), the chance that the (7.57) integrand `encVal` exceeds `lam` is
`≤ e^{2ε}/lam`. -/
theorem fstar_markovP_le (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (q₀ : ℕ × ℤ)
    (hbound : encExpectP p hp0 hp1 F R g ε T (encInitP q₀.1 q₀.2) ≤ Real.exp (2 * ε))
    (lam : ℝ) (hlam : 0 < lam) :
    ∑' v : Fin T → ℕ × ℤ, ((holdP p hp0 hp1).iid T v).toReal *
      (if lam ≤ encVal ε R ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2))
        then (1 : ℝ) else 0)
    ≤ Real.exp (2 * ε) / lam := by
  set hold := holdP p hp0 hp1 with hholddef
  set X : (Fin T → ℕ × ℤ) → ℝ :=
    fun v => encVal ε R ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2))
    with hX
  have hX0 : ∀ v, 0 < X v := fun v => encVal_pos _ _ _
  have hXle : ∀ v, X v ≤ Real.exp (ε * R) := fun v => encVal_le ε hε R _
  have hind : ∀ v : Fin T → ℕ × ℤ,
      (hold.iid T v).toReal * (if lam ≤ X v then (1 : ℝ) else 0)
        ≤ (hold.iid T v).toReal * X v / lam := by
    intro v
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    split_ifs with h
    · rw [le_div_iff₀ hlam, one_mul]; exact h
    · exact div_nonneg (hX0 v).le hlam.le
  have hsumIid : Summable fun v : Fin T → ℕ × ℤ => (hold.iid T v).toReal :=
    ENNReal.summable_toReal
      (by rw [(hold.iid T).tsum_coe]; exact ENNReal.one_ne_top)
  have hsumX : Summable fun v : Fin T → ℕ × ℤ => (hold.iid T v).toReal * X v :=
    Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (hX0 v).le)
      (fun v => mul_le_mul_of_nonneg_left (hXle v) ENNReal.toReal_nonneg)
      (hsumIid.mul_right (Real.exp (ε * R)))
  have hsumXd : Summable fun v : Fin T → ℕ × ℤ =>
      (hold.iid T v).toReal * X v / lam := hsumX.div_const lam
  have hsumL : Summable fun v : Fin T → ℕ × ℤ =>
      (hold.iid T v).toReal * (if lam ≤ X v then (1 : ℝ) else 0) :=
    Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num))
      hind hsumXd
  have hEE : (∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal * X v)
      = encExpectP p hp0 hp1 F R g ε T (encInitP q₀.1 q₀.2) := rfl
  calc ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
        (if lam ≤ X v then (1 : ℝ) else 0)
      ≤ ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal * X v / lam :=
        hsumL.tsum_le_tsum hind hsumXd
    _ = (∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal * X v) / lam :=
        tsum_div_const
    _ ≤ Real.exp (2 * ε) / lam := by
        rw [hEE]
        gcongr

/-- **The tilted (7.56) `F∗` Markov bound, X9-discharged**: the tilt cap `ε₀` and
the depth gate `g` come from `many_triangles_whiteP`, chosen before `p`. -/
theorem fstar_markovP :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 100 ∧ ∃ g : ℕ,
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (lam : ℝ), 0 < lam →
        ∑' v : Fin T → ℕ × ℤ, ((holdP p (by linarith) (by linarith)).iid T v).toReal *
          (if lam ≤ encVal ε R ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2))
            then (1 : ℝ) else 0)
        ≤ Real.exp (2 * ε) / lam := by
  obtain ⟨ε₀, hε₀, hε₀le, g, hX9⟩ := many_triangles_whiteP
  refine ⟨ε₀, hε₀, hε₀le, g, ?_⟩
  intro ε hε hεε₀ p hp0 hp1 n ξ hξ F R hR T q₀ lam hlam
  exact fstar_markovP_le p (by linarith) (by linarith) F R g ε hε.le T q₀
    (hX9 ε hε hεε₀ p hp0 hp1 n ξ hξ F R hR T q₀.1 q₀.2) lam hlam

/-! ### Machinery for the deterministic claim (7.67), tilted law -/

/-- The first coordinate of any `holdP`-atom is at least `1`. -/
theorem holdP_support_fst_ge (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d : ℕ × ℤ) (hd : d ∈ (holdP p hp0 hp1).support) : 1 ≤ d.1 :=
  holdP_support_fst_pos p hp0 hp1 d hd

/-- The fold state after the first `k` steps of the walk `v`. -/
noncomputable def encFoldAtP {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) (k : ℕ) : EncState :=
  ((List.ofFn v).take k).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)

theorem encFoldAtP_zero {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) :
    encFoldAtP F R g q₀ v 0 = encInitP q₀.1 q₀.2 := rfl

/-- Stepping the stopped state. -/
theorem encFoldAtP_succ {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) {k : ℕ} (hk : k < T) :
    encFoldAtP F R g q₀ v (k + 1)
      = encStepP F R g (encFoldAtP F R g q₀ v k) (v ⟨k, hk⟩) := by
  rw [encFoldAtP, encFoldAtP, List.take_add_one,
    List.getElem?_eq_getElem (by simpa using hk)]
  simp [List.foldl_append]

/-- At the horizon, the stopped state is the full fold. -/
theorem encFoldAtP_top {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) :
    encFoldAtP F R g q₀ v T
      = (List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2) := by
  rw [encFoldAtP, List.take_of_length_le (by simp)]

/-- The stopped state's position is the start plus the partial sum. -/
theorem encFoldAtP_pos {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) (k : ℕ) :
    (encFoldAtP F R g q₀ v k).pos = q₀ + pathSum v k := by
  rw [encFoldAtP, encFoldP_pos, pathSum]
  show (q₀.1, q₀.2) + _ = _
  rfl

/-- The stopped count is monotone in time. -/
theorem encFoldAtP_count_mono {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) {k k' : ℕ} (h : k ≤ k') (hk' : k' ≤ T) :
    (encFoldAtP F R g q₀ v k).count ≤ (encFoldAtP F R g q₀ v k').count := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction i with
  | zero => simp
  | succ i IH =>
    rw [show k + (i + 1) = (k + i) + 1 from rfl,
      encFoldAtP_succ F R g q₀ v (show k + i < T by omega)]
    exact le_trans (IH (by omega)) (encStepP_count_le F R g _ _)

/-- If a step does not change the count, it does not change the barrier. -/
theorem encStepP_barrier_of_count_eq {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (σ : EncState) (d : ℕ × ℤ)
    (h : (encStepP F R g σ d).count = σ.count) :
    (encStepP F R g σ d).barrier = σ.barrier := by
  rw [encStepP] at h ⊢
  split at h
  · exfalso
    dsimp only at h
    omega
  · rename_i hq
    rw [dif_neg hq]

/-- If the count is flat over a time window, the barrier is flat too. -/
theorem encFoldAtP_barrier_of_count_eq {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) {k k' : ℕ} (h : k ≤ k') (hk' : k' ≤ T)
    (hcnt : (encFoldAtP F R g q₀ v k').count = (encFoldAtP F R g q₀ v k).count) :
    (encFoldAtP F R g q₀ v k').barrier = (encFoldAtP F R g q₀ v k).barrier := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction i with
  | zero => rfl
  | succ i IH =>
    have hki : k + i < T := by omega
    have hmono1 := encFoldAtP_count_mono F R g q₀ v (show k ≤ k + i by omega)
      (show k + i ≤ T by omega)
    have hstep := encStepP_count_le F R g (encFoldAtP F R g q₀ v (k + i)) (v ⟨k + i, hki⟩)
    rw [show k + (i + 1) = (k + i) + 1 from rfl, encFoldAtP_succ F R g q₀ v hki] at hcnt ⊢
    have hflat : (encStepP F R g (encFoldAtP F R g q₀ v (k + i)) (v ⟨k + i, hki⟩)).count
        = (encFoldAtP F R g q₀ v (k + i)).count := by omega
    rw [encStepP_barrier_of_count_eq F R g _ _ hflat]
    exact IH (by omega) (by omega : (encFoldAtP F R g q₀ v (k + i)).count
      = (encFoldAtP F R g q₀ v k).count)

/-- On-support tilted walks advance the column by at least one per step. -/
theorem pathSum_fst_geP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {T : ℕ} (v : Fin T → ℕ × ℤ) (hv : ∀ i, v i ∈ (holdP p hp0 hp1).support) :
    ∀ (k i : ℕ), k + i ≤ T → (pathSum v k).1 + i ≤ (pathSum v (k + i)).1 := by
  intro k i
  induction i with
  | zero => intro _; simp
  | succ i IH =>
    intro hi
    have hki : k + i < T := by omega
    rw [show k + (i + 1) = (k + i) + 1 from rfl, pathSum_succ_of_lt v hki]
    have h1 := holdP_support_fst_ge p hp0 hp1 _ (hv ⟨k + i, hki⟩)
    have h2 := IH (by omega)
    show (pathSum v k).1 + (i + 1) ≤ (pathSum v (k + i)).1 + (v ⟨k + i, hki⟩).1
    omega

/-- On-support tilted walks gain at least `3` height per step. -/
theorem pathSum_snd_geP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {T : ℕ} (v : Fin T → ℕ × ℤ) (hv : ∀ i, v i ∈ (holdP p hp0 hp1).support) :
    ∀ (k i : ℕ), k + i ≤ T → (pathSum v k).2 + 3 * i ≤ (pathSum v (k + i)).2 := by
  intro k i
  induction i with
  | zero => intro _; simp
  | succ i IH =>
    intro hi
    have hki : k + i < T := by omega
    rw [show k + (i + 1) = (k + i) + 1 from rfl, pathSum_succ_of_lt v hki]
    have h1 := holdP_support_snd_ge p hp0 hp1 _ (hv ⟨k + i, hki⟩)
    have h2 := IH (by omega)
    show (pathSum v k).2 + 3 * ((i : ℤ) + 1) ≤ (pathSum v (k + i)).2 + (v ⟨k + i, hki⟩).2
    linarith

/-- An in-strip position (`1 ≤ q₁ ≤ n/2`) outside the finer white strip is
`blackP` at its phase point. -/
theorem blackP_of_notMem_whiteStripP {n ξ : ℕ} {q : ℕ × ℤ} (h1 : 1 ≤ q.1)
    (h2 : q.1 ≤ n / 2) (h : q ∉ whiteStripP n ξ) : blackP n ξ (q.1 - 1) q.2 := by
  by_contra hb
  exact h ⟨h2, h1, hb⟩

open scoped Classical in
/-- **The barrier envelope** for the tilted fold: along a path satisfying the
depth and small-size hypotheses, the fold's barrier never exceeds the current
height by more than `2·4^A(1+k)³`. -/
theorem encFoldAtP_barrier_le (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) (hv : ∀ i, v i ∈ (holdP p hp0 hp1).support)
    (A : ℝ) (hA : 0 ≤ A)
    (hsmall : ∀ k, k ≤ T → ∀ t ∈ F.T,
      ((q₀ + pathSum v k).1 - 1, (q₀ + pathSum v k).2) ∈ triangle t.1 t.2.1 t.2.2 →
      t.2.2 < (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3) :
    ∀ k, k ≤ T →
      (((encFoldAtP F R g q₀ v k).barrier : ℝ))
        ≤ ((q₀.2 + (pathSum v k).2 : ℤ) : ℝ) + 2 * (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 := by
  have h4A : (1 : ℝ) ≤ (4 : ℝ) ^ A := Real.one_le_rpow (by norm_num) hA
  intro k
  induction k with
  | zero =>
    intro _
    have hb : (encFoldAtP F R g q₀ v 0).barrier = q₀.2 := rfl
    have hz : (pathSum v 0).2 = 0 := by simp
    rw [hb, hz]
    push_cast
    nlinarith
  | succ k IH =>
    intro hk1
    have hk : k ≤ T := by omega
    have hklt : k < T := by omega
    rw [encFoldAtP_succ F R g q₀ v hklt]
    have hgrow : ((q₀.2 + (pathSum v k).2 : ℤ) : ℝ) + 2 * (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3
        ≤ ((q₀.2 + (pathSum v (k + 1)).2 : ℤ) : ℝ)
          + 2 * (4 : ℝ) ^ A * (1 + ((k + 1 : ℕ) : ℝ)) ^ 3 := by
      have hht := pathSum_snd_geP p hp0 hp1 v hv k 1 (by omega)
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hcube : (1 + (k : ℝ)) ^ 3 ≤ (1 + ((k + 1 : ℕ) : ℝ)) ^ 3 := by
        push_cast
        nlinarith
      have h2A : (0 : ℝ) ≤ 2 * (4 : ℝ) ^ A := by linarith
      have := mul_le_mul_of_nonneg_left hcube h2A
      have hht' : ((pathSum v k).2 : ℝ) + 3 ≤ ((pathSum v (k + 1)).2 : ℝ) := by
        exact_mod_cast hht
      have hhtR : ((q₀.2 + (pathSum v k).2 : ℤ) : ℝ)
          ≤ ((q₀.2 + (pathSum v (k + 1)).2 : ℤ) : ℝ) := by
        push_cast
        linarith
      calc ((q₀.2 + (pathSum v k).2 : ℤ) : ℝ) + 2 * (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3
          ≤ ((q₀.2 + (pathSum v (k + 1)).2 : ℤ) : ℝ)
            + 2 * (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 := by linarith
        _ ≤ _ := by linarith [this]
    rw [encStepP]
    split
    case isTrue hcond =>
      dsimp only
      set q : ℕ × ℤ := (encFoldAtP F R g q₀ v k).pos + v ⟨k, hklt⟩ with hq
      have hqpos : q = q₀ + pathSum v (k + 1) := by
        rw [hq, encFoldAtP_pos, pathSum_succ_of_lt v hklt, add_assoc]
      set t := F.coveringTriangle (q.1 - 1, q.2)
        ⟨show q.1 - 1 + 1 ≤ n / 2 by omega, hcond.2.2.1⟩ with ht
      have htmem := F.coveringTriangle_mem
        (q := (q.1 - 1, q.2)) ⟨show q.1 - 1 + 1 ≤ n / 2 by omega, hcond.2.2.1⟩
      have htcov := F.coveringTriangle_covers
        (q := (q.1 - 1, q.2)) ⟨show q.1 - 1 + 1 ≤ n / 2 by omega, hcond.2.2.1⟩
      have htcov' : ((q.1 - 1, q.2) : ℕ × ℤ) ∈ triangle t.1 t.2.1 t.2.2 := htcov
      have hsize : t.2.2 < (4 : ℝ) ^ A * (1 + ((k : ℝ) + 1)) ^ 3 := by
        have := hsmall (k + 1) hk1 t htmem (by rw [← hqpos]; exact htcov')
        push_cast at this ⊢
        linarith
      have hext : ((t.2.1 - q.2 : ℤ) : ℝ) * Real.log 2 ≤ t.2.2 :=
        triangle_top_le (q := (q.1 - 1, q.2)) htcov'
      have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      have htop : ((t.2.1 : ℤ) : ℝ) ≤ (q.2 : ℝ) + 2 * t.2.2 := by
        rcases le_or_gt t.2.1 q.2 with hle | hgt
        · have h0 : (0 : ℝ) ≤ t.2.2 := F.size_nonneg t htmem
          have : ((t.2.1 : ℤ) : ℝ) ≤ ((q.2 : ℤ) : ℝ) := by exact_mod_cast hle
          linarith
        · have hpos : (0 : ℝ) < ((t.2.1 - q.2 : ℤ) : ℝ) := by
            have : (0 : ℤ) < t.2.1 - q.2 := by omega
            exact_mod_cast this
          have hkey := mul_lt_mul_of_pos_left hlog2 hpos
          push_cast at hext hpos hkey ⊢
          nlinarith
      have hq2 : (q.2 : ℝ) = ((q₀.2 + (pathSum v (k + 1)).2 : ℤ) : ℝ) := by
        rw [hqpos]
        simp only [Prod.snd_add]
      have h4Ak : (0 : ℝ) ≤ (4 : ℝ) ^ A * (1 + ((k : ℝ) + 1)) ^ 3 := by positivity
      calc ((t.2.1 : ℤ) : ℝ) ≤ (q.2 : ℝ) + 2 * t.2.2 := htop
        _ ≤ (q.2 : ℝ) + 2 * ((4 : ℝ) ^ A * (1 + ((k : ℝ) + 1)) ^ 3) := by linarith
        _ = ((q₀.2 + (pathSum v (k + 1)).2 : ℤ) : ℝ)
            + 2 * (4 : ℝ) ^ A * (1 + ((k : ℝ) + 1)) ^ 3 := by rw [hq2]; ring
        _ ≤ _ := by
            push_cast
            linarith
    case isFalse hcond =>
      exact le_trans (IH hk) hgrow

open scoped Classical in
/-- **The (7.67) window step** for the tilted fold: from any time `k` with room
for one window `W(k) = ⌈4^A(1+k)³⌉ + K + 2`, the fold's count strictly increases by
the end of the window. -/
theorem encFoldAtP_count_step (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) (hq₀ : 1 ≤ q₀.1) {T : ℕ} (v : Fin T → ℕ × ℤ)
    (hv : ∀ i, v i ∈ (holdP p hp0 hp1).support) (A : ℝ) (hA : 0 ≤ A) (K : ℕ)
    (hdepth : ∀ k, k ≤ T → (q₀ + pathSum v k).1 + g ≤ n / 2)
    (hsmall : ∀ k, k ≤ T → ∀ t ∈ F.T,
      ((q₀ + pathSum v k).1 - 1, (q₀ + pathSum v k).2) ∈ triangle t.1 t.2.1 t.2.2 →
      t.2.2 < (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3)
    (hfew : (Finset.range T).sum
      (fun k => if q₀ + pathSum v (k + 1) ∈ whiteStripP n ξ then 1 else 0) ≤ K)
    {k : ℕ} (hk : k + (⌈(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌉₊ + K + 2) ≤ T) :
    (encFoldAtP F R g q₀ v k).count + 1
      ≤ (encFoldAtP F R g q₀ v (k + (⌈(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌉₊ + K + 2))).count := by
  set D : ℕ := ⌈(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌉₊ with hD
  set W : ℕ := D + K + 2 with hW
  by_contra hcon
  push Not at hcon
  have hflat : ∀ r, k ≤ r → r ≤ k + W →
      (encFoldAtP F R g q₀ v r).count = (encFoldAtP F R g q₀ v k).count := by
    intro r h1 h2
    have hmono1 := encFoldAtP_count_mono F R g q₀ v h1 (by omega)
    have hmono2 := encFoldAtP_count_mono F R g q₀ v h2 (by omega)
    omega
  have hbar : ∀ r, k ≤ r → r ≤ k + W →
      (encFoldAtP F R g q₀ v r).barrier = (encFoldAtP F R g q₀ v k).barrier := by
    intro r h1 h2
    exact encFoldAtP_barrier_of_count_eq F R g q₀ v h1 (by omega) (hflat r h1 h2)
  have henv := encFoldAtP_barrier_le p hp0 hp1 F R g q₀ v hv A hA hsmall k (by omega)
  have hclear : ∀ r, k + D + 1 ≤ r → r ≤ k + W →
      (encFoldAtP F R g q₀ v k).barrier < (q₀ + pathSum v r).2 := by
    intro r h1 h2
    have hht := pathSum_snd_geP p hp0 hp1 v hv k (r - k) (by omega)
    rw [show k + (r - k) = r from by omega] at hht
    have hDge : ((4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3) ≤ (D : ℝ) :=
      Nat.le_ceil _
    have h4Apos : (0 : ℝ) ≤ (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 := by positivity
    have hstrict : (((encFoldAtP F R g q₀ v k).barrier : ℤ) : ℝ)
        < (((q₀ + pathSum v r).2 : ℤ) : ℝ) := by
      have hrk : (D : ℝ) + 1 ≤ ((r - k : ℕ) : ℝ) := by
        have : D + 1 ≤ r - k := by omega
        exact_mod_cast this
      have hht' : ((pathSum v k).2 : ℝ) + 3 * ((r - k : ℕ) : ℝ)
          ≤ ((pathSum v r).2 : ℝ) := by exact_mod_cast hht
      have hh2 : ((q₀.2 + (pathSum v k).2 : ℤ) : ℝ) + 3 * ((r - k : ℕ) : ℝ)
          ≤ (((q₀ + pathSum v r).2 : ℤ) : ℝ) := by
        have hr2 : (q₀ + pathSum v r).2 = q₀.2 + (pathSum v r).2 := rfl
        rw [hr2]
        push_cast
        linarith
      calc (((encFoldAtP F R g q₀ v k).barrier : ℤ) : ℝ)
          ≤ ((q₀.2 + (pathSum v k).2 : ℤ) : ℝ)
            + 2 * (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 := henv
        _ < ((q₀.2 + (pathSum v k).2 : ℤ) : ℝ) + 3 * ((D : ℝ) + 1) := by nlinarith
        _ ≤ ((q₀.2 + (pathSum v k).2 : ℤ) : ℝ) + 3 * ((r - k : ℕ) : ℝ) := by linarith
        _ ≤ _ := hh2
    exact_mod_cast hstrict
  have hpigeon : ∃ r, k + D + 1 ≤ r ∧ r ≤ k + D + K + 1 ∧
      q₀ + pathSum v r ∉ whiteStripP n ξ := by
    by_contra hall
    push Not at hall
    have hone : ∀ i ∈ Finset.range (K + 1),
        (if q₀ + pathSum v (k + D + i + 1) ∈ whiteStripP n ξ then 1 else 0) = 1 := by
      intro i hi
      simp only [Finset.mem_range] at hi
      exact if_pos (hall (k + D + i + 1) (by omega) (by omega))
    have hsub : (Finset.range (K + 1)).sum
        (fun i => if q₀ + pathSum v (k + D + i + 1) ∈ whiteStripP n ξ then 1 else 0)
        = K + 1 := by
      rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_range]
    have hinj : (Finset.range (K + 1)).sum
        (fun i => if q₀ + pathSum v (k + D + i + 1) ∈ whiteStripP n ξ then 1 else 0)
        ≤ (Finset.range T).sum
          (fun r => if q₀ + pathSum v (r + 1) ∈ whiteStripP n ξ then 1 else 0) := by
      have hmap : (Finset.range (K + 1)).sum
          (fun i => if q₀ + pathSum v (k + D + i + 1) ∈ whiteStripP n ξ then 1 else 0)
          = ((Finset.range (K + 1)).image (fun i => k + D + i)).sum
            (fun r => if q₀ + pathSum v (r + 1) ∈ whiteStripP n ξ then 1 else 0) := by
        rw [Finset.sum_image (by intro a _ b _ h; simp only [] at h; omega)]
      rw [hmap]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro r hr
      simp only [Finset.mem_image, Finset.mem_range] at hr ⊢
      obtain ⟨i, hi, rfl⟩ := hr
      show k + D + i < T
      omega
    omega
  obtain ⟨r, hr1, hr2, hrblack⟩ := hpigeon
  have hr0 : 1 ≤ r := by omega
  have hrT : r ≤ T := by omega
  have hcol : 1 ≤ (q₀ + pathSum v r).1 := by
    show 1 ≤ q₀.1 + (pathSum v r).1
    omega
  have hdeep := hdepth r hrT
  have hblack : blackP n ξ ((q₀ + pathSum v r).1 - 1) (q₀ + pathSum v r).2 :=
    blackP_of_notMem_whiteStripP hcol (by omega) hrblack
  have hbarrier : (encFoldAtP F R g q₀ v (r - 1)).barrier < (q₀ + pathSum v r).2 := by
    rw [hbar (r - 1) (by omega) (by omega)]
    exact hclear r (by omega) (by omega)
  have hrstep : r - 1 < T := by omega
  have hposr : (encFoldAtP F R g q₀ v (r - 1)).pos + v ⟨r - 1, hrstep⟩
      = q₀ + pathSum v r := by
    rw [encFoldAtP_pos, add_assoc]
    congr 1
    rw [← pathSum_succ_of_lt v hrstep]
    congr 1
    omega
  have hcount : (encFoldAtP F R g q₀ v r).count
      = (encFoldAtP F R g q₀ v (r - 1)).count + 1 := by
    have hstep : encFoldAtP F R g q₀ v r
        = encStepP F R g (encFoldAtP F R g q₀ v (r - 1)) (v ⟨r - 1, hrstep⟩) := by
      rw [← encFoldAtP_succ F R g q₀ v hrstep]
      congr 1
      omega
    rw [hstep, encStepP]
    rw [dif_pos (by
      rw [hposr]
      exact ⟨hcol, hdeep, hblack, hbarrier⟩)]
  have hflat1 := hflat (r - 1) (by omega) (by omega)
  have hflat2 := hflat r (by omega) (by omega)
  omega

open scoped Classical in
/-- **The deterministic claim (7.67)** for the tilted fold, explicit-horizon form:
a deep in-strip path that never meets a `≥ 4^A(1+k)³`-sized finer triangle and visits
at most `K` finer white-strip points drives the encounter count to `R` within
`encWindowIter A K R` steps.  The horizon is law-independent. -/
theorem deterministic_encounter_claimP_at (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (n ξ : ℕ) (F : TriangleFamilyP n ξ)
    (g R K : ℕ) (A : ℝ) (hA : 1 ≤ A) (T : ℕ) (hT : encWindowIter A K R ≤ T)
    (q₀ : ℕ × ℤ) (hq₀ : 1 ≤ q₀.1) (v : Fin T → ℕ × ℤ)
    (hv : ∀ i, v i ∈ (holdP p hp0 hp1).support)
    (hdepth : ∀ k, k ≤ T → (q₀ + pathSum v k).1 + g ≤ n / 2)
    (hsmall : ∀ k, k ≤ T → ∀ t ∈ F.T,
        ((q₀ + pathSum v k).1 - 1, (q₀ + pathSum v k).2) ∈ triangle t.1 t.2.1 t.2.2 →
        t.2.2 < (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3)
    (hfew : (Finset.range T).sum
        (fun k => if q₀ + pathSum v (k + 1) ∈ whiteStripP n ξ then 1 else 0) ≤ K) :
    R ≤ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).count := by
  classical
  have key : ∀ i, i ≤ R → i ≤ (encFoldAtP F R g q₀ v (encWindowIter A K i)).count := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i IH =>
      intro hiR
      have hle : encWindowIter A K (i + 1) ≤ T :=
        le_trans (encWindowIter_mono A K hiR) hT
      have hstep := encFoldAtP_count_step p hp0 hp1 (F := F) (R := R) (g := g) q₀ hq₀ v hv A
        (by linarith) K hdepth hsmall hfew
        (k := encWindowIter A K i) (by rw [← encWindowIter_succ]; exact hle)
      rw [← encWindowIter_succ] at hstep
      exact le_trans (Nat.succ_le_succ (IH (by omega))) hstep
  have hmono := encFoldAtP_count_mono F R g q₀ v hT (le_refl T)
  rw [encFoldAtP_top] at hmono
  exact le_trans (key R (le_refl R)) hmono

end TaoCollatz.Sec7P
