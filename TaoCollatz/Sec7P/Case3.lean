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

/-! ### X11a: the E∗ union bound at `Pascal(p)` -/

/-- **E∗ union threshold** for the tilted bound: the tilted X10 threshold `100`
joined with the `r = exp(−c·A²) ≤ ½` regime `A ≥ √(log2/c)`. -/
noncomputable def A0_estarUnionP : ℝ := max 100 (Real.sqrt (Real.log 2 / c_encTriP))

theorem one_le_A0_estarUnionP : 1 ≤ A0_estarUnionP := by
  unfold A0_estarUnionP; exact le_trans (by norm_num) (le_max_left _ _)

/-- **E∗ union constant** for the tilted bound. -/
noncomputable def C_estarUnionP : ℝ := 4 * C_encTriP

theorem C_estarUnionP_pos : 0 < C_estarUnionP := by
  have := C_encTriP_pos; unfold C_estarUnionP; linarith

open scoped Classical in
/-- **X11a E∗ union bound `_core`** at `Pascal(p)`: the per-`k` big-triangle walk
bound abstracted over its constant `C`, rate `c`, and threshold `A₀`, yielding
`4·C·A²·4^{−A} + 4·C·exp(−c·A²)` for `A ≥ max A₀ √(log2/c)`, uniformly in `p`. -/
theorem estar_union_le_rpowP_core (C c A₀ : ℝ) (hC : 0 < C) (hc : 0 < c) (hA₀ : 1 ≤ A₀)
    (hX10 : ∀ (A : ℝ), A₀ ≤ A →
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
          ≤ C * A ^ 2 * (1 + (k : ℝ)) / (s' : ℝ)
            + C * Real.exp (-c * A ^ 2 * (1 + (k : ℝ)))) :
    ∀ (A : ℝ), max A₀ (Real.sqrt (Real.log 2 / c)) ≤ A →
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ), (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (T : ℕ),
        (∀ k, k ≤ T →
          ((⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ)) →
        (Finset.range (T + 1)).sum (fun k =>
          (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
            ∑' v : Fin T → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid T v *
            Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (j + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)).toReal)
          ≤ 4 * C * A ^ 2 * (4 : ℝ) ^ (-A) + 4 * C * Real.exp (-c * A ^ 2) := by
  intro A hA p hp0 hp1 n ξ hξ F t₀ ht₀ j l hmem s hs hdeep T hreg
  have hA0 : A₀ ≤ A := le_trans (le_max_left _ _) hA
  have hA1 : (1 : ℝ) ≤ A := le_trans hA₀ hA0
  have hAsqrt : Real.sqrt (Real.log 2 / c) ≤ A := le_trans (le_max_right _ _) hA
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv_nonneg : (0 : ℝ) ≤ Real.log 2 / c := le_of_lt (div_pos hlog2 hc)
  have hAsq : Real.log 2 / c ≤ A ^ 2 := by
    have h1 : Real.sqrt (Real.log 2 / c) ^ 2 = Real.log 2 / c := Real.sq_sqrt hdiv_nonneg
    have h3 : (0 : ℝ) ≤ Real.sqrt (Real.log 2 / c) := Real.sqrt_nonneg _
    nlinarith [h1, hAsqrt, h3]
  have hcA2 : Real.log 2 ≤ c * A ^ 2 := by
    have := mul_le_mul_of_nonneg_left hAsq (le_of_lt hc)
    rwa [mul_div_cancel₀ _ (ne_of_gt hc)] at this
  have hr : Real.exp (-c * A ^ 2) ≤ 1 / 2 := by
    have hle : Real.exp (-c * A ^ 2) ≤ Real.exp (-Real.log 2) := by
      apply Real.exp_le_exp.mpr; nlinarith [hcA2]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hle
    linarith [hle, (by norm_num : (2 : ℝ)⁻¹ = 1 / 2)]
  have hxfour : ∀ k : ℕ, (4 : ℝ) ≤ (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 := by
    intro k
    have h4A : (4 : ℝ) ≤ (4 : ℝ) ^ A := by
      calc (4 : ℝ) = (4 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 4).symm
        _ ≤ (4 : ℝ) ^ A := Real.rpow_le_rpow_of_exponent_le (by norm_num) hA1
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h13 : (1 : ℝ) ≤ (1 + (k : ℝ)) ^ 3 := by
      nlinarith [hk0, mul_nonneg hk0 hk0, mul_nonneg (mul_nonneg hk0 hk0) hk0]
    nlinarith [h4A, h13]
  have hbig : ∀ k ∈ Finset.range (T + 1),
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
        ∑' v : Fin T → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid T v *
        Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊)
          (1 : ℕ × ℤ → ℝ≥0∞)
          (j + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)).toReal
        ≤ C * A ^ 2 * (1 + (k : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
          + C * Real.exp (-c * A ^ 2 * (1 + (k : ℝ))) := by
    intro k hk
    have hkT : k ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1s' : 1 ≤ ⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ := by
      apply Nat.le_floor
      push_cast
      linarith [hxfour k]
    exact hX10 A hA0 p hp0 hp1 n ξ hξ F t₀ ht₀ j l hmem s hs hdeep T k _ hkT h1s' (hreg k hkT)
  refine le_trans (Finset.sum_le_sum hbig) ?_
  rw [Finset.sum_add_distrib]
  apply add_le_add
  · have hpoly : ∀ k ∈ Finset.range (T + 1),
        C * A ^ 2 * (1 + (k : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
          ≤ 2 * C * A ^ 2 * (4 : ℝ) ^ (-A) * (1 / (1 + (k : ℝ)) ^ 2) := by
      intro k _
      have hq : (0 : ℝ) < 1 + (k : ℝ) := by positivity
      have hPpos : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
      have hx4 : (4 : ℝ) ≤ (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 := hxfour k
      have hfloor : (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 / 2
          ≤ ((⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) := by
        have hlt := Nat.lt_floor_add_one ((4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3)
        linarith [hlt, hx4]
      have step1 : (1 + (k : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
          ≤ (1 + (k : ℝ)) / ((4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 / 2) := by
        gcongr
      have step2 : (1 + (k : ℝ)) / ((4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 / 2)
          = 2 * (4 : ℝ) ^ (-A) * (1 / (1 + (k : ℝ)) ^ 2) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
        have hPne : (4 : ℝ) ^ A ≠ 0 := ne_of_gt hPpos
        have hqne : (1 + (k : ℝ)) ≠ 0 := ne_of_gt hq
        field_simp
      calc C * A ^ 2 * (1 + (k : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
          = C * A ^ 2 * ((1 + (k : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)) := by
            ring
        _ ≤ C * A ^ 2 * ((1 + (k : ℝ)) / ((4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 / 2)) :=
            mul_le_mul_of_nonneg_left step1 (mul_nonneg hC.le (sq_nonneg A))
        _ = C * A ^ 2 * (2 * (4 : ℝ) ^ (-A) * (1 / (1 + (k : ℝ)) ^ 2)) := by rw [step2]
        _ = 2 * C * A ^ 2 * (4 : ℝ) ^ (-A) * (1 / (1 + (k : ℝ)) ^ 2) := by ring
    calc (Finset.range (T + 1)).sum (fun k =>
            C * A ^ 2 * (1 + (k : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ))
        ≤ (Finset.range (T + 1)).sum (fun k =>
            2 * C * A ^ 2 * (4 : ℝ) ^ (-A) * (1 / (1 + (k : ℝ)) ^ 2)) := Finset.sum_le_sum hpoly
      _ = 2 * C * A ^ 2 * (4 : ℝ) ^ (-A)
            * (Finset.range (T + 1)).sum (fun k => 1 / (1 + (k : ℝ)) ^ 2) := by
          rw [← Finset.mul_sum]
      _ ≤ 2 * C * A ^ 2 * (4 : ℝ) ^ (-A) * 2 :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_le_two T)
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.le) (sq_nonneg A))
              (Real.rpow_nonneg (by norm_num) _))
      _ = 4 * C * A ^ 2 * (4 : ℝ) ^ (-A) := by ring
  · have hexp : ∀ k ∈ Finset.range (T + 1),
        C * Real.exp (-c * A ^ 2 * (1 + (k : ℝ)))
          = C * Real.exp (-c * A ^ 2) ^ (1 + k) := by
      intro k _
      have h : Real.exp (-c * A ^ 2 * (1 + (k : ℝ))) = Real.exp (-c * A ^ 2) ^ (1 + k) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast; ring
      rw [h]
    calc (Finset.range (T + 1)).sum (fun k => C * Real.exp (-c * A ^ 2 * (1 + (k : ℝ))))
        = (Finset.range (T + 1)).sum (fun k => C * Real.exp (-c * A ^ 2) ^ (1 + k)) :=
          Finset.sum_congr rfl hexp
      _ = C * (Finset.range (T + 1)).sum (fun k => Real.exp (-c * A ^ 2) ^ (1 + k)) := by
          rw [← Finset.mul_sum]
      _ ≤ C * (2 * Real.exp (-c * A ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (sum_geom_pow_le (Real.exp (-c * A ^ 2)) (le_of_lt (Real.exp_pos _)) hr T) hC.le
      _ ≤ 4 * C * Real.exp (-c * A ^ 2) := by nlinarith [hC.le, Real.exp_pos (-c * A ^ 2)]

open scoped Classical in
/-- **X11a E∗ union bound** at `Pascal(p)`, explicit constants
`C_estarUnionP`/`c_encTriP`, threshold `A0_estarUnionP`; uniform on the window. -/
theorem estar_union_le_rpowP_explicitC :
    ∀ (A : ℝ), A0_estarUnionP ≤ A →
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ), (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (T : ℕ),
        (∀ k, k ≤ T →
          ((⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ)) →
        (Finset.range (T + 1)).sum (fun k =>
          (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
            ∑' v : Fin T → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid T v *
            Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (j + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)).toReal)
          ≤ C_estarUnionP * A ^ 2 * (4 : ℝ) ^ (-A)
            + C_estarUnionP * Real.exp (-c_encTriP * A ^ 2) := by
  have h := estar_union_le_rpowP_core C_encTriP c_encTriP 100 C_encTriP_pos c_encTriP_pos
    (by norm_num) bigTriangle_walk_le_rpowP_explicitC
  unfold C_estarUnionP A0_estarUnionP
  exact h

/-! ### X11c ingredients — the reaches-`R` / few-white → F∗ join, base `50` -/

/-- **The `encVal` lower bound on the reaches-`R` few-white event** for the tilted fold. -/
theorem encVal_ge_of_reachesP {n ξ : ℕ} (F : TriangleFamilyP n ξ) (R g K : ℕ) (ε : ℝ)
    (q₀ : ℕ × ℤ) (L : List (ℕ × ℤ))
    (hreach : R ≤ (L.foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).count)
    (hwhite : (L.foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).cumWhite ≤ K) :
    Real.exp (-(K : ℝ) + ε * R)
      ≤ encVal ε R (L.foldl (encStepP F R g) (encInitP q₀.1 q₀.2)) := by
  set σ := L.foldl (encStepP F R g) (encInitP q₀.1 q₀.2) with hσ
  rw [encVal]
  apply Real.exp_le_exp.mpr
  have hbank : σ.banked ≤ σ.cumWhite := by
    rw [hσ]; exact encFoldP_banked_le F R g L (encInitP q₀.1 q₀.2) (by simp [encInitP])
  have hbk : (σ.banked : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_trans hbank hwhite
  have hmin : min σ.count R = R := min_eq_right hreach
  rw [hmin]
  linarith [hbk]

open scoped Classical in
/-- **The reaches-`R` few-white mass bound** (the Markov join) for the tilted fold. -/
theorem reaches_fewWhite_mass_leP_core (ε₀ : ℝ) (g : ℕ)
    (hmark : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (lam : ℝ), 0 < lam →
        ∑' v : Fin T → ℕ × ℤ, ((holdP p (by linarith) (by linarith)).iid T v).toReal *
          (if lam ≤ encVal ε R ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2))
            then (1 : ℝ) else 0)
        ≤ Real.exp (2 * ε) / lam) :
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (K : ℕ),
        ∑' v : Fin T → ℕ × ℤ, ((holdP p (by linarith) (by linarith)).iid T v).toReal *
          (if R ≤ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).count
              ∧ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).cumWhite ≤ K
            then (1 : ℝ) else 0)
          ≤ Real.exp (2 * ε) / Real.exp (-(K : ℝ) + ε * R) := by
  intro ε hεpos hεle p hp0 hp1 n ξ hξ F R hR T q₀ K
  set hold := holdP p (by linarith) (by linarith) with hholddef
  have hlam : (0 : ℝ) < Real.exp (-(K : ℝ) + ε * R) := Real.exp_pos _
  have hsum : Summable (fun v : Fin T → ℕ × ℤ => (hold.iid T v).toReal) :=
    ENNReal.summable_toReal (by rw [(hold.iid T).tsum_coe]; exact ENNReal.one_ne_top)
  have hle : ∀ v : Fin T → ℕ × ℤ,
      (hold.iid T v).toReal *
        (if R ≤ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).count
            ∧ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).cumWhite ≤ K
          then (1 : ℝ) else 0)
        ≤ (hold.iid T v).toReal *
          (if Real.exp (-(K : ℝ) + ε * R)
              ≤ encVal ε R ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2))
            then (1 : ℝ) else 0) := by
    intro v
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    by_cases hev : R ≤ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).count
        ∧ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).cumWhite ≤ K
    · rw [if_pos hev]
      split_ifs with henc
      · exact le_refl 1
      · exact absurd (encVal_ge_of_reachesP F R g K ε q₀ (List.ofFn v) hev.1 hev.2) henc
    · rw [if_neg hev]; positivity
  have hbound : ∀ v : Fin T → ℕ × ℤ,
      (hold.iid T v).toReal *
        (if Real.exp (-(K : ℝ) + ε * R)
            ≤ encVal ε R ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2))
          then (1 : ℝ) else 0) ≤ (hold.iid T v).toReal := by
    intro v
    calc (hold.iid T v).toReal * (if Real.exp (-(K : ℝ) + ε * R)
            ≤ encVal ε R ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2))
          then (1 : ℝ) else 0)
        ≤ (hold.iid T v).toReal * 1 := by
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          split_ifs <;> norm_num
      _ = (hold.iid T v).toReal := mul_one _
  have hsumR : Summable (fun v : Fin T → ℕ × ℤ => (hold.iid T v).toReal *
      (if Real.exp (-(K : ℝ) + ε * R)
          ≤ encVal ε R ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2))
        then (1 : ℝ) else 0)) :=
    Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (by positivity)) hbound hsum
  have hsumL : Summable (fun v : Fin T → ℕ × ℤ => (hold.iid T v).toReal *
      (if R ≤ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).count
          ∧ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).cumWhite ≤ K
        then (1 : ℝ) else 0)) :=
    Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (by positivity))
      (fun v => le_trans (hle v) (hbound v)) hsum
  exact le_trans (Summable.tsum_le_tsum hle hsumL hsumR)
    (hmark ε hεpos hεle p hp0 hp1 n ξ hξ F R hR T q₀ (Real.exp (-(K : ℝ) + ε * R)) hlam)

/-- **The (7.56) numerical closure at base `50`** (operator addendum: `(1 − t₂)^{A+k}`
targets at `t₂ = 49/50`): with `εR ≥ K + (A+3)·log 50 + 2`, the Markov ratio
`e^{2ε}/e^{−K+εR} ≤ 50^{−(A+1)}`. -/
theorem fewWhite_num_closureP (A ε : ℝ) (hε1 : ε ≤ 1) (K R : ℕ)
    (hRbound : (K : ℝ) + (A + 3) * Real.log 50 + 2 ≤ ε * R) :
    Real.exp (2 * ε) / Real.exp (-(K : ℝ) + ε * R) ≤ (50 : ℝ) ^ (-(A + 1)) := by
  rw [← Real.exp_sub]
  have hlog : (0 : ℝ) < Real.log 50 := Real.log_pos (by norm_num)
  have h1 : (A + 3) * Real.log 50 = (A + 1) * Real.log 50 + 2 * Real.log 50 := by ring
  have hstep : 2 * ε - (-(K : ℝ) + ε * R) ≤ -(A + 1) * Real.log 50 := by
    nlinarith [hRbound, hε1, hlog, h1]
  calc Real.exp (2 * ε - (-(K : ℝ) + ε * R))
      ≤ Real.exp (-(A + 1) * Real.log 50) := Real.exp_le_exp.mpr hstep
    _ = (50 : ℝ) ^ (-(A + 1)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 50)]
        congr 1; ring

open scoped Classical in
/-- **The full (7.56) reaches-`R`/few-white bound** at `Pascal(p)`, base `50`: the tilt
cap `ε₀` and depth gate `g` are those of `fstar_markovP`, chosen before `p`. -/
theorem reaches_fewWhite_mass_le_fiftyP :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 100 ∧ ∃ g : ℕ,
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ,
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (K : ℕ),
        (K : ℝ) + (A + 3) * Real.log 50 + 2 ≤ ε * R →
        ∑' v : Fin T → ℕ × ℤ, ((holdP p (by linarith) (by linarith)).iid T v).toReal *
          (if R ≤ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).count
              ∧ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).cumWhite ≤ K
            then (1 : ℝ) else 0)
          ≤ (50 : ℝ) ^ (-(A + 1)) := by
  obtain ⟨ε₀, hε₀, hε₀le, g, hmark⟩ := fstar_markovP
  refine ⟨ε₀, hε₀, hε₀le, g, ?_⟩
  intro ε hεpos hεle A p hp0 hp1 n ξ hξ F R hR T q₀ K hRbound
  exact le_trans
    (reaches_fewWhite_mass_leP_core ε₀ g hmark ε hεpos hεle p hp0 hp1 n ξ hξ F R hR T q₀ K)
    (fewWhite_num_closureP A ε (by linarith) K R hRbound)

/-- **E∗ containment** (the floor bridge) for the finer family. -/
theorem bigTriangle_of_encounterP {n ξ : ℕ} (F : TriangleFamilyP n ξ) (A : ℝ) (k : ℕ)
    (q : ℕ × ℤ) (t : ℕ × ℤ × ℝ) (ht : t ∈ F.T) (hmem : q ∈ triangle t.1 t.2.1 t.2.2)
    (hbig : (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 ≤ t.2.2) :
    q ∈ bigTriangleSetP F ⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ := by
  refine ⟨t, ht, ?_, hmem⟩
  calc ((⌊(4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
      ≤ (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 := Nat.floor_le (by positivity)
    _ ≤ t.2.2 := hbig

open scoped Classical in
/-- **The pointwise dichotomy for the (7.56) white-count split**, tilted fold: for a
deep in-strip walk whose forward white count is `≤ K`, EITHER the fold reaches `R`
(with `cumWhite ≤ K+1`) OR the path hits a big finer triangle (E∗). -/
theorem few_white_pointwise_dichotomyP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {n ξ : ℕ} (F : TriangleFamilyP n ξ)
    (g R K : ℕ) (A : ℝ) (hA : 1 ≤ A) (P : ℕ) (hP : encWindowIter A (K + 1) R ≤ P)
    (q₀ : ℕ × ℤ) (hq₀ : 1 ≤ q₀.1) (v : Fin P → ℕ × ℤ)
    (hv : ∀ i, v i ∈ (holdP p hp0 hp1).support)
    (hdepth : ∀ k, k ≤ P → (q₀ + pathSum v k).1 + g ≤ n / 2)
    (hmyNw : (∑ k ∈ Finset.range P,
        (if q₀ + pathSum v k ∈ whiteStripP n ξ then (1 : ℕ) else 0)) ≤ K) :
    (R ≤ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).count
        ∧ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).cumWhite ≤ K + 1)
    ∨ (∃ k, k ≤ P ∧ ∃ t ∈ F.T,
        ((q₀ + pathSum v k).1 - 1, (q₀ + pathSum v k).2) ∈ triangle t.1 t.2.1 t.2.2
        ∧ (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3 ≤ t.2.2) := by
  classical
  have hpos : (encInitP q₀.1 q₀.2).pos = q₀ := rfl
  have hcum : ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).cumWhite
      = ∑ k ∈ Finset.range P,
          (if q₀ + pathSum v (k + 1) ∈ whiteStripP n ξ then (1 : ℕ) else 0) := by
    rw [encFoldP_cumWhite F R g P v (encInitP q₀.1 q₀.2), hpos]
    simp only [encInitP, zero_add]
  have hSple : (∑ k ∈ Finset.range P,
      (if q₀ + pathSum v (k + 1) ∈ whiteStripP n ξ then (1 : ℕ) else 0)) ≤ K + 1 := by
    have e1 : (∑ k ∈ Finset.range (P + 1),
          (if q₀ + pathSum v k ∈ whiteStripP n ξ then (1 : ℕ) else 0))
        = (∑ k ∈ Finset.range P,
            (if q₀ + pathSum v (k + 1) ∈ whiteStripP n ξ then (1 : ℕ) else 0))
          + (if q₀ + pathSum v 0 ∈ whiteStripP n ξ then (1 : ℕ) else 0) :=
      Finset.sum_range_succ' _ P
    have e2 : (∑ k ∈ Finset.range (P + 1),
          (if q₀ + pathSum v k ∈ whiteStripP n ξ then (1 : ℕ) else 0))
        = (∑ k ∈ Finset.range P,
            (if q₀ + pathSum v k ∈ whiteStripP n ξ then (1 : ℕ) else 0))
          + (if q₀ + pathSum v P ∈ whiteStripP n ξ then (1 : ℕ) else 0) :=
      Finset.sum_range_succ _ P
    have hb : (if q₀ + pathSum v P ∈ whiteStripP n ξ then (1 : ℕ) else 0) ≤ 1 := by
      split_ifs <;> omega
    omega
  have hcumK : ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).cumWhite ≤ K + 1 := by
    rw [hcum]; exact hSple
  by_cases hE : ∀ k, k ≤ P → ∀ t ∈ F.T,
      ((q₀ + pathSum v k).1 - 1, (q₀ + pathSum v k).2) ∈ triangle t.1 t.2.1 t.2.2 →
      t.2.2 < (4 : ℝ) ^ A * (1 + (k : ℝ)) ^ 3
  · exact Or.inl ⟨deterministic_encounter_claimP_at p hp0 hp1 n ξ F g R (K + 1) A hA P hP q₀
      hq₀ v hv hdepth hE hSple, hcumK⟩
  · refine Or.inr ?_
    push Not at hE
    obtain ⟨k, hk, t, ht, hmem, hbig⟩ := hE
    exact ⟨k, hk, t, ht, hmem, hbig⟩

open scoped Classical in
/-- **The pointwise THREE-way split for (7.56)** at `Pascal(p)`, with the operator's
bad-column threshold `t₂ = 49/50` and depth gate `g ≤ m/50`: the few-white indicator
is dominated by the reach-`R` indicator, the E∗ union, and the bad-column indicator
`{(49/50)·m ≤ e.1 + (pathSum v P).1}`. -/
theorem few_white_pointwise_splitP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {n ξ : ℕ} (F : TriangleFamilyP n ξ)
    (m : ℕ) (hmn : m ≤ n / 2) (hpos : 1 ≤ n / 2 - m) (l : ℤ)
    (g R K : ℕ) (A' : ℝ) (hA' : 1 ≤ A') (P : ℕ) (hP : encWindowIter A' (K + 1) R ≤ P)
    (hg : (g : ℝ) ≤ (1 / 50 : ℝ) * (m : ℝ))
    (e : ℕ × ℤ) (v : Fin P → ℕ × ℤ) (hv : ∀ i, v i ∈ (holdP p hp0 hp1).support) :
    ENNReal.ofReal (if (∑ k ∈ Finset.range P,
          Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
            (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
        ≤ (K : ℝ)
      then (1 : ℝ) else 0)
    ≤ ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStepP F R g)
            (encInitP (n / 2 - m + e.1) (l + e.2))).count
          ∧ ((List.ofFn v).foldl (encStepP F R g)
            (encInitP (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
        then (1 : ℝ) else 0)
      + (∑ k ∈ Finset.range (P + 1),
          Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
      + ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
          then (1 : ℝ) else 0) := by
  classical
  set q₀ : ℕ × ℤ := (n / 2 - m + e.1, l + e.2) with hq₀def
  have hq1 : q₀.1 = n / 2 - m + e.1 := rfl
  set Nw : ℝ := ∑ k ∈ Finset.range P,
      Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
        (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) with hNwdef
  set T1 : ℝ≥0∞ := ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStepP F R g)
        (encInitP (n / 2 - m + e.1) (l + e.2))).count
      ∧ ((List.ofFn v).foldl (encStepP F R g)
        (encInitP (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1 then (1 : ℝ) else 0) with hT1def
  set T2 : ℝ≥0∞ := ∑ k ∈ Finset.range (P + 1),
      Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
        (1 : ℕ × ℤ → ℝ≥0∞)
        (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) with hT2def
  set T3 : ℝ≥0∞ := ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
      then (1 : ℝ) else 0) with hT3def
  by_cases hfew : Nw ≤ (K : ℝ)
  · rw [if_pos hfew, ENNReal.ofReal_one]
    by_cases hcol : (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
    · have hT3one : T3 = 1 := by rw [hT3def, if_pos hcol, ENNReal.ofReal_one]
      calc (1 : ℝ≥0∞) = T3 := hT3one.symm
        _ ≤ T1 + T2 + T3 := self_le_add_left _ _
    · have hset : whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2} = whiteStripP n ξ := by
        ext q; simp only [whiteStripP, Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
      have hcast : Nw = ((∑ k ∈ Finset.range P,
              (if q₀ + pathSum v k ∈ whiteStripP n ξ then (1 : ℕ) else 0) : ℕ) : ℝ) := by
        rw [hNwdef, Nat.cast_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hpt : (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)
            = q₀ + pathSum v k := rfl
        rw [hpt, hset, Set.indicator_apply, Pi.one_apply, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero]
      have hNatK : (∑ k ∈ Finset.range P,
          (if q₀ + pathSum v k ∈ whiteStripP n ξ then (1 : ℕ) else 0)) ≤ K := by
        have h := hfew; rw [hcast] at h; exact_mod_cast h
      have hadv : (e.1 + (pathSum v P).1 : ℕ) + g ≤ m := by
        have hlt : ((e.1 + (pathSum v P).1 : ℕ) : ℝ) < 49 / 50 * (m : ℝ) := not_le.mp hcol
        have hsum : ((e.1 + (pathSum v P).1 : ℕ) : ℝ) + (g : ℝ) ≤ (m : ℝ) := by
          nlinarith [hlt, hg]
        exact_mod_cast hsum
      have hqone : 1 ≤ q₀.1 := by rw [hq1]; omega
      have hendpt : q₀.1 + (pathSum v P).1 + g ≤ n / 2 := by rw [hq1]; omega
      have hdepth : ∀ k, k ≤ P → (q₀ + pathSum v k).1 + g ≤ n / 2 :=
        pathSum_depth_le v q₀ g (n / 2) hendpt
      have hdich := few_white_pointwise_dichotomyP p hp0 hp1 F g R K A' hA' P hP q₀ hqone v hv
        hdepth hNatK
      rcases hdich with ⟨hreach, hcw⟩ | ⟨k, hk, t, ht, hmem, hbig⟩
      · have hT1one : T1 = 1 := by
          rw [hT1def, if_pos ⟨hreach, hcw⟩, ENNReal.ofReal_one]
        calc (1 : ℝ≥0∞) = T1 := hT1one.symm
          _ ≤ T1 + T2 := self_le_add_right _ _
          _ ≤ T1 + T2 + T3 := self_le_add_right _ _
      · have hpt : ((q₀ + pathSum v k).1 - 1, (q₀ + pathSum v k).2)
            = (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) := by
          have h1 : (q₀ + pathSum v k).1 = n / 2 - m + e.1 + (pathSum v k).1 := rfl
          have h2 : (q₀ + pathSum v k).2 = l + e.2 + (pathSum v k).2 := rfl
          refine Prod.ext_iff.mpr ⟨?_, h2⟩
          rw [h1]; omega
        have hbigmem : (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)
            ∈ bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊ := by
          rw [← hpt]; exact bigTriangle_of_encounterP F A' k _ t ht hmem hbig
        have hone : Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) = 1 := by
          rw [Set.indicator_of_mem hbigmem]; rfl
        have hT2ge : (1 : ℝ≥0∞) ≤ T2 := by
          have hsingle := Finset.single_le_sum (f := fun k : ℕ =>
            Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
            (fun i _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
          rw [hone] at hsingle
          rw [hT2def]; exact hsingle
        calc (1 : ℝ≥0∞) ≤ T2 := hT2ge
          _ ≤ T1 + T2 := self_le_add_left _ _
          _ ≤ T1 + T2 + T3 := self_le_add_right _ _
  · rw [if_neg hfew, ENNReal.ofReal_zero]
    exact zero_le

/-! ### The three (7.56) mass terms at `Pascal(p)` -/

open scoped Classical in
/-- **(7.56) reach-`R` mass term** at `Pascal(p)`, constants abstracted: given the
base-`50` reaches bound at tilt `ε₀` and gate `g`, the first-passage ⊗ walk mass of the
reach-`R`/few-white event `{R ≤ count ∧ cumWhite ≤ K+1}` is `≤ 50^{−A−3}`. -/
theorem few_white_reach_mass_leP_core (ε₀ : ℝ) (g : ℕ)
    (hten : ∀ A : ℝ,
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (K : ℕ),
        (K : ℝ) + (A + 3) * Real.log 50 + 2 ≤ ε₀ * R →
        ∑' v : Fin T → ℕ × ℤ, ((holdP p (by linarith) (by linarith)).iid T v).toReal *
          (if R ≤ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).count
              ∧ ((List.ofFn v).foldl (encStepP F R g) (encInitP q₀.1 q₀.2)).cumWhite ≤ K
            then (1 : ℝ) else 0)
          ≤ (50 : ℝ) ^ (-(A + 1)))
    (A : ℝ) :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
    ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ (m : ℕ) (l : ℤ) (R : ℕ), 1 ≤ R → ∀ (K P : ℕ),
      ((K : ℝ) + 1) + (A + 5) * Real.log 50 + 2 ≤ ε₀ * R → ∀ s : ℕ,
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStepP F R g)
                (encInitP (n / 2 - m + e.1) (l + e.2))).count
              ∧ ((List.ofFn v).foldl (encStepP F R g)
                (encInitP (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) := by
  intro p hp0 hp1 n ξ hξ F m l R hR K P hRbound s
  set hold := holdP p (by linarith) (by linarith) with hholddef
  have hval : (0 : ℝ) ≤ (50 : ℝ) ^ (-A - 3) := Real.rpow_nonneg (by norm_num) _
  have hexp : (50 : ℝ) ^ (-((A + 2) + 1)) = (50 : ℝ) ^ (-A - 3) := by
    congr 1; ring
  have hinner : ∀ e : ℕ × ℤ,
      (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStepP F R g)
                (encInitP (n / 2 - m + e.1) (l + e.2))).count
              ∧ ((List.ofFn v).foldl (encStepP F R g)
                (encInitP (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) := by
    intro e
    set S : ℝ≥0∞ := ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStepP F R g)
              (encInitP (n / 2 - m + e.1) (l + e.2))).count
            ∧ ((List.ofFn v).foldl (encStepP F R g)
              (encInitP (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
          then (1 : ℝ) else 0) with hSdef
    have hSle1 : S ≤ 1 := by
      rw [hSdef]
      exact PMF.tsum_mul_ofReal_le_one (hold.iid P) _ (fun v => by split_ifs <;> norm_num)
    have hSne : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hSle1
    have hbridge : S.toReal = ∑' v : Fin P → ℕ × ℤ, (hold.iid P v).toReal *
        (if R ≤ ((List.ofFn v).foldl (encStepP F R g)
              (encInitP (n / 2 - m + e.1) (l + e.2))).count
            ∧ ((List.ofFn v).foldl (encStepP F R g)
              (encInitP (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
          then (1 : ℝ) else 0) := by
      rw [hSdef]
      exact PMF.toReal_tsum_mul_ofReal (hold.iid P) _ (fun v => by split_ifs <;> norm_num)
    have hr := hten (A + 2) p hp0 hp1 n ξ hξ F R hR P (n / 2 - m + e.1, l + e.2) (K + 1)
      (by push_cast; nlinarith [hRbound])
    rw [ENNReal.le_ofReal_iff_toReal_le hSne hval, hbridge, ← hexp]
    exact hr
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right (hinner e) _) ?_
  rw [ENNReal.tsum_mul_right, (fpDistP p (by linarith) (by linarith) s).tsum_coe, one_mul]

/-! #### The E∗ term: the base-16 numeric rescaled to base `50` -/

/-- The exponent at which the fixed-law base-16 numeric is invoked: `10^{−A₁−3}` at
`A₁ = log₁₀50·(A+3) − 3` is exactly `50^{−A−3}`. -/
noncomputable def A1_scaleP (A : ℝ) : ℝ := Real.log 50 / Real.log 10 * (A + 3) - 3

theorem A1_scaleP_pos {A : ℝ} (hA : 0 < A) : 0 < A1_scaleP A := by
  unfold A1_scaleP
  have hl10 : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num)
  have hlt : Real.log 10 < Real.log 50 := Real.log_lt_log (by norm_num) (by norm_num)
  have hdiv : (1 : ℝ) < Real.log 50 / Real.log 10 := by
    rw [lt_div_iff₀ hl10]; linarith
  nlinarith

theorem ten_rpow_A1_scaleP (A : ℝ) :
    (10 : ℝ) ^ (-A1_scaleP A - 3) = (50 : ℝ) ^ (-A - 3) := by
  unfold A1_scaleP
  have hl10 : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 10)).ne'
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 50)]
  congr 1
  field_simp
  ring

/-- The additive E∗ exponent constant at the tilted E∗-union constants. -/
noncomputable def A0_fewEstarP : ℝ := A0_estarScaled C_estarUnionP c_encTriP A0_estarUnionP

/-- The scaled E∗ exponent `A' = 2·A₁ + A0` used in the tilted (7.56) E∗ term. -/
noncomputable def Ascaled_fewEstarP (A : ℝ) : ℝ := 2 * A1_scaleP A + A0_fewEstarP

theorem one_le_A0_fewEstarP : 1 ≤ A0_fewEstarP :=
  (estar_scaled_numeric_at C_estarUnionP c_encTriP A0_estarUnionP
    C_estarUnionP_pos c_encTriP_pos one_le_A0_estarUnionP).2.1

theorem one_le_Ascaled_fewEstarP {A : ℝ} (hA : 0 < A) : 1 ≤ Ascaled_fewEstarP A := by
  unfold Ascaled_fewEstarP
  linarith [one_le_A0_fewEstarP, A1_scaleP_pos hA]

open scoped Classical in
/-- **(7.56) E∗ mass term** at `Pascal(p)`: the first-passage ⊗ walk mass of the
union-over-`k` big-triangle event is `≤ 50^{−A−3}`, at the scaled exponent
`Ascaled_fewEstarP A`.  Uniform on the window. -/
theorem few_white_estar_mass_leP_at (A : ℝ) (hA : 0 < A) :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, (10 : ℕ) ^ 30 ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      ∀ P : ℕ, (∀ k, k ≤ P →
          ((⌊(4 : ℝ) ^ (Ascaled_fewEstarP A) * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
            ≤ ((m + 1 : ℕ) : ℝ) ^ (0.4 : ℝ)) →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          (∑ k ∈ Finset.range (P + 1),
            Set.indicator (bigTriangleSetP F
                ⌊(4 : ℝ) ^ (Ascaled_fewEstarP A) * (1 + (k : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))
        ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) := by
  have hestar := estar_union_le_rpowP_explicitC
  have hA₀ge : A0_estarUnionP ≤ A0_fewEstarP :=
    (estar_scaled_numeric_at C_estarUnionP c_encTriP A0_estarUnionP
      C_estarUnionP_pos c_encTriP_pos one_le_A0_estarUnionP).1
  have hnum : C_estarUnionP * (Ascaled_fewEstarP A) ^ 2 * (4 : ℝ) ^ (-(Ascaled_fewEstarP A))
      + C_estarUnionP * Real.exp (-c_encTriP * (Ascaled_fewEstarP A) ^ 2)
      ≤ (50 : ℝ) ^ (-A - 3) := by
    have h := (estar_scaled_numeric_at C_estarUnionP c_encTriP A0_estarUnionP
      C_estarUnionP_pos c_encTriP_pos one_le_A0_estarUnionP).2.2 (A1_scaleP A) (A1_scaleP_pos hA)
    rw [ten_rpow_A1_scaleP] at h
    exact h
  set A' : ℝ := Ascaled_fewEstarP A with hA'def
  have hA'eq : A' = 2 * A1_scaleP A + A0_fewEstarP := rfl
  have hA'ge : A0_estarUnionP ≤ A' := by
    rw [hA'eq]; linarith [hA₀ge, A1_scaleP_pos hA]
  intro p hp0 hp1 n ξ hξ F m hmCthr hmn l hpos t ht hmem s hs hreg_s P hreg
  set fp := fpDistP p (by linarith) (by linarith) s with hfpdef
  set hold := holdP p (by linarith) (by linarith) with hholddef
  set G : ℕ → ℝ≥0∞ := fun k => ∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ,
      hold.iid P v * Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
        (1 : ℕ × ℤ → ℝ≥0∞)
        (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) with hGdef
  have hind_le1 : ∀ (k : ℕ) (y : ℕ × ℤ),
      Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
        (1 : ℕ × ℤ → ℝ≥0∞) y ≤ 1 := by
    intro k y; rw [Set.indicator_apply]; split_ifs with h
    · simp
    · simp
  have hGle1 : ∀ k, G k ≤ 1 := by
    intro k
    rw [hGdef]
    calc (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            Set.indicator _ (1 : ℕ × ℤ → ℝ≥0∞) _)
        ≤ ∑' e : ℕ × ℤ, fp e * 1 := by
          refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
          calc (∑' v : Fin P → ℕ × ℤ, hold.iid P v * Set.indicator _ (1 : ℕ × ℤ → ℝ≥0∞) _)
              ≤ ∑' v : Fin P → ℕ × ℤ, hold.iid P v * 1 :=
                ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hind_le1 _ _) _
            _ = 1 := by rw [ENNReal.tsum_mul_right, (hold.iid P).tsum_coe, one_mul]
      _ = 1 := by rw [ENNReal.tsum_mul_right, fp.tsum_coe, one_mul]
  have hGne : ∀ k, G k ≠ ⊤ := fun k => ne_top_of_le_ne_top ENNReal.one_ne_top (hGle1 k)
  have hstep1 : ∀ e : ℕ × ℤ, (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (∑ k ∈ Finset.range (P + 1),
          Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))
      = ∑ k ∈ Finset.range (P + 1), ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) := by
    intro e
    rw [show (∑' v : Fin P → ℕ × ℤ, hold.iid P v * (∑ k ∈ Finset.range (P + 1), _))
        = ∑' v : Fin P → ℕ × ℤ, ∑ k ∈ Finset.range (P + 1), hold.iid P v *
            Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) from
        tsum_congr fun v => by rw [Finset.mul_sum]]
    exact Summable.tsum_finsetSum (fun k _ => ENNReal.summable)
  have hswap : (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (∑ k ∈ Finset.range (P + 1),
          Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))
      = ∑ k ∈ Finset.range (P + 1), G k := by
    rw [show (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          (∑ k ∈ Finset.range (P + 1), _))
        = ∑' e : ℕ × ℤ, ∑ k ∈ Finset.range (P + 1), fp e *
            ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
              Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
                (1 : ℕ × ℤ → ℝ≥0∞)
                (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) from
        tsum_congr fun e => by rw [hstep1 e, Finset.mul_sum]]
    rw [Summable.tsum_finsetSum (fun k _ => ENNReal.summable)]
  rw [hswap]
  have hmC : (10 : ℝ) ^ (30 : ℕ) ≤ (m : ℝ) := by exact_mod_cast hmCthr
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := le_trans (by norm_num) hmC
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hbridge : ((m + 1 : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) := by
    have hlogsqpos : (0 : ℝ) < Real.log (m : ℝ) ^ 2 := by positivity
    have h08 : ((m + 1 : ℕ) : ℝ) ^ (0.8 : ℝ) ≤ 2 * (m : ℝ) ^ (0.8 : ℝ) := by
      have hle : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by push_cast; linarith
      calc ((m + 1 : ℕ) : ℝ) ^ (0.8 : ℝ) ≤ (2 * (m : ℝ)) ^ (0.8 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hle (by norm_num)
        _ = (2 : ℝ) ^ (0.8 : ℝ) * (m : ℝ) ^ (0.8 : ℝ) := Real.mul_rpow (by norm_num) hmpos.le
        _ ≤ 2 * (m : ℝ) ^ (0.8 : ℝ) := by
            have h2 : (2 : ℝ) ^ (0.8 : ℝ) ≤ 2 := by
              calc (2 : ℝ) ^ (0.8 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one _
            nlinarith [Real.rpow_nonneg hmpos.le (0.8 : ℝ)]
    have hlog : Real.log (m : ℝ) ≤ 20 * (m : ℝ) ^ (0.05 : ℝ) := by
      have hld := Real.log_le_rpow_div hmpos.le (by norm_num : (0 : ℝ) < 0.05)
      have heq : (m : ℝ) ^ (0.05 : ℝ) / 0.05 = 20 * (m : ℝ) ^ (0.05 : ℝ) := by ring
      linarith [hld, heq.ge, heq.le]
    have hm01 : (m : ℝ) ^ (0.05 : ℝ) * (m : ℝ) ^ (0.05 : ℝ) = (m : ℝ) ^ (0.1 : ℝ) := by
      rw [← Real.rpow_add hmpos]; norm_num
    have hlogsq : Real.log (m : ℝ) ^ 2 ≤ 400 * (m : ℝ) ^ (0.1 : ℝ) := by
      have hlognn : (0 : ℝ) ≤ Real.log (m : ℝ) := hlogpos.le
      have hmul := mul_le_mul hlog hlog hlognn (by positivity)
      calc Real.log (m : ℝ) ^ 2 = Real.log (m : ℝ) * Real.log (m : ℝ) := by ring
        _ ≤ (20 * (m : ℝ) ^ (0.05 : ℝ)) * (20 * (m : ℝ) ^ (0.05 : ℝ)) := hmul
        _ = 400 * (m : ℝ) ^ (0.1 : ℝ) := by rw [← hm01]; ring
    have hm89 : (m : ℝ) ^ (0.8 : ℝ) * (m : ℝ) ^ (0.1 : ℝ) = (m : ℝ) ^ (0.9 : ℝ) := by
      rw [← Real.rpow_add hmpos]; norm_num
    have hm91 : (m : ℝ) ^ (0.9 : ℝ) * (m : ℝ) ^ (0.1 : ℝ) = (m : ℝ) := by
      rw [← Real.rpow_add hmpos]; norm_num
    have hm01ge : (800 : ℝ) ≤ (m : ℝ) ^ (0.1 : ℝ) := by
      calc (800 : ℝ) ≤ (1000 : ℝ) := by norm_num
        _ = ((10 : ℝ) ^ (30 : ℕ)) ^ (0.1 : ℝ) := by
            rw [← Real.rpow_natCast (10 : ℝ) 30, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ (m : ℝ) ^ (0.1 : ℝ) := Real.rpow_le_rpow (by positivity) hmC (by norm_num)
    have hm08nn : (0 : ℝ) ≤ (m : ℝ) ^ (0.8 : ℝ) := Real.rpow_nonneg hmpos.le _
    have hm09nn : (0 : ℝ) ≤ (m : ℝ) ^ (0.9 : ℝ) := Real.rpow_nonneg hmpos.le _
    have hprod : ((m + 1 : ℕ) : ℝ) ^ (0.8 : ℝ) * Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) := by
      calc ((m + 1 : ℕ) : ℝ) ^ (0.8 : ℝ) * Real.log (m : ℝ) ^ 2
          ≤ (2 * (m : ℝ) ^ (0.8 : ℝ)) * (400 * (m : ℝ) ^ (0.1 : ℝ)) := by
            apply mul_le_mul h08 hlogsq (by positivity) (by positivity)
        _ = 800 * ((m : ℝ) ^ (0.8 : ℝ) * (m : ℝ) ^ (0.1 : ℝ)) := by ring
        _ = 800 * (m : ℝ) ^ (0.9 : ℝ) := by rw [hm89]
        _ ≤ (m : ℝ) := by
            have hstep : (800 : ℝ) * (m : ℝ) ^ (0.9 : ℝ)
                ≤ (m : ℝ) ^ (0.1 : ℝ) * (m : ℝ) ^ (0.9 : ℝ) :=
              mul_le_mul_of_nonneg_right hm01ge hm09nn
            rw [mul_comm ((m : ℝ) ^ (0.1 : ℝ)) ((m : ℝ) ^ (0.9 : ℝ)), hm91] at hstep
            exact hstep
    have hle : ((m + 1 : ℕ) : ℝ) ^ (0.8 : ℝ) ≤ (m : ℝ) / Real.log (m : ℝ) ^ 2 := by
      rw [le_div_iff₀ hlogsqpos]; exact hprod
    exact lt_of_le_of_lt hle hreg_s
  have hdd : n / 2 - (n / 2 - m - 1) = m + 1 := by omega
  have hdeep' : ((n / 2 - (n / 2 - m - 1) : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) := by
    rw [hdd]; exact hbridge
  have hreg' : ∀ k, k ≤ P →
      ((⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
        ≤ ((n / 2 - (n / 2 - m - 1) : ℕ) : ℝ) ^ (0.4 : ℝ) := by
    intro k hk; rw [hdd]; exact hreg k hk
  have hest := hestar A' hA'ge p hp0 hp1 n ξ hξ F t ht (n / 2 - m - 1) l hmem s hs hdeep' P hreg'
  have hSne : (∑ k ∈ Finset.range (P + 1), G k) ≠ ⊤ :=
    (ENNReal.sum_ne_top).mpr (fun k _ => hGne k)
  have hStoreal : (∑ k ∈ Finset.range (P + 1), G k).toReal ≤ (50 : ℝ) ^ (-A - 3) := by
    rw [ENNReal.toReal_sum (fun k _ => hGne k)]
    exact le_trans hest hnum
  rw [ENNReal.le_ofReal_iff_toReal_le hSne (Real.rpow_nonneg (by norm_num) _)]
  exact hStoreal

/-! #### The bad-column tail at `t₂ = 49/50` -/

open scoped Classical in
/-- **(7.54) bad-column tail** at `Pascal(p)`: the mass that the `P`-step walk after
first passage advances past `(49/50)·m` is `≤ m^{−A}/2` for `m` past an explicit
threshold.  The moving centre `(p/2)·s ≤ 0.96(m+2)` leaves the deviation `D = m/200`
(Tao: `0.9` vs `0.8`, `D = m/40`).  Constants abstracted. -/
theorem col_tail_mass_leP_core (A : ℝ) (_hA : 0 < A) (P : ℕ) (hP1 : 1 ≤ P)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (htail : ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ s k : ℕ, ∀ D : ℝ, 10000 * (1 + (k : ℝ)) ≤ D →
      ∑' e : ℕ × ℤ, (fpDistPlusP p (by linarith) (by linarith) s k e).toReal *
          Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} 1 e
        ≤ C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D)))
    (Nexp : ℕ)
    (hNexp : ∀ m : ℕ, Nexp ≤ m →
      Real.exp (-(c / 424000) * (m : ℝ)) ≤ 1 / (4 * C) * (m : ℝ) ^ (-A)) :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, 2000000 * (P + 1) + 200 + Nexp ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) / 2) := by
  classical
  intro p hp0 hp1 n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  set D : ℝ := (m : ℝ) / 200 with hDdef
  have hDbound : 10000 * (1 + (P : ℝ)) ≤ D := by
    rw [hDdef]
    have : (2000000 * (P + 1) : ℕ) ≤ m := by omega
    have hcast : (2000000 : ℝ) * ((P : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast this
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog93 : Real.log 9 < 3.2 * Real.log 2 := by
    have hll := Real.log_lt_log (by positivity) (by norm_num : (9 : ℝ) ^ 5 < (2 : ℝ) ^ 16)
    rw [Real.log_pow, Real.log_pow] at hll
    push_cast at hll; linarith
  have hsbound : (s : ℝ) < 3.2 * ((m : ℝ) + 2) := by
    have h2 : ((m : ℝ) + 2) * Real.log 9 < ((m : ℝ) + 2) * (3.2 * Real.log 2) :=
      mul_lt_mul_of_pos_left hlog93 (by positivity)
    have h3 : (s : ℝ) * Real.log 2 < (3.2 * ((m : ℝ) + 2)) * Real.log 2 := by nlinarith [hs2, h2]
    exact lt_of_mul_lt_mul_right h3 hlog2pos.le
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hps : p / 2 * (s : ℝ) ≤ 3 / 10 * (s : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hs0
    linarith
  set g : ℕ × ℤ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((x.1 : ℕ) : ℝ) then (1 : ℝ) else 0) with hgdef
  have hbridge : (∑' e : ℕ × ℤ, fpDistP p hp0' hp1' s e *
        ∑' v : Fin P → ℕ × ℤ, (holdP p hp0' hp1').iid P v *
        ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
          then (1 : ℝ) else 0))
      = ∑' x : ℕ × ℤ, fpDistPlusP p hp0' hp1' s P x * g x :=
    fpDistP_walk_eq_fpDistPlusP p hp0' hp1' s (le_refl P) g
  rw [hbridge]
  have hcont : ∀ x : ℕ × ℤ,
      (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((x.1 : ℕ) : ℝ) then (1 : ℝ) else 0)
      ≤ Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} 1 x := by
    intro x
    by_cases h : (49 / 50 : ℝ) * (m : ℝ) ≤ ((x.1 : ℕ) : ℝ)
    · rw [if_pos h]
      have hmem2 : x ∈ {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} := by
        show 2 * D ≤ |((x.1 : ℕ) : ℝ) - p / 2 * (s : ℝ)|
        have hstep : 2 * D ≤ ((x.1 : ℕ) : ℝ) - p / 2 * (s : ℝ) := by
          rw [hDdef]
          have hm200 : (200 : ℝ) ≤ (m : ℝ) := by
            have : (200 : ℕ) ≤ m := by omega
            exact_mod_cast this
          nlinarith [hsbound, h, hm200, hps]
        exact le_trans hstep (le_abs_self _)
      rw [Set.indicator_of_mem hmem2, Pi.one_apply]
    · rw [if_neg h]
      rw [Set.indicator_apply]; split_ifs <;> norm_num
  set RHS : ℝ≥0∞ := ∑' x : ℕ × ℤ, fpDistPlusP p hp0' hp1' s P x *
      ENNReal.ofReal (Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} 1 x)
    with hRHSdef
  have hUB : (∑' x : ℕ × ℤ, fpDistPlusP p hp0' hp1' s P x * g x) ≤ RHS := by
    rw [hRHSdef]
    refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
    rw [hgdef]; exact ENNReal.ofReal_le_ofReal (hcont x)
  have hRHSle1 : RHS ≤ 1 := by
    rw [hRHSdef]
    calc (∑' x : ℕ × ℤ, fpDistPlusP p hp0' hp1' s P x *
          ENNReal.ofReal (Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} 1 x))
        ≤ ∑' x : ℕ × ℤ, fpDistPlusP p hp0' hp1' s P x * 1 := by
          refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
          refine ENNReal.ofReal_le_one.mpr ?_
          rw [Set.indicator_apply]; split_ifs <;> norm_num
      _ = 1 := by rw [ENNReal.tsum_mul_right, (fpDistPlusP p hp0' hp1' s P).tsum_coe, one_mul]
  have hRHSne : RHS ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hRHSle1
  have hne : (∑' x : ℕ × ℤ, fpDistPlusP p hp0' hp1' s P x * g x) ≠ ⊤ :=
    ne_top_of_le_ne_top hRHSne hUB
  rw [ENNReal.le_ofReal_iff_toReal_le hne (by positivity)]
  have hRHSreal : RHS.toReal = ∑' x : ℕ × ℤ, (fpDistPlusP p hp0' hp1' s P x).toReal *
      Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} 1 x := by
    rw [hRHSdef]
    exact PMF.toReal_tsum_mul_ofReal (fpDistPlusP p hp0' hp1' s P) _
      (fun x => by rw [Set.indicator_apply]; split_ifs <;> norm_num)
  have h1s : (1 : ℝ) + (s : ℝ) ≤ 10.6 * (m : ℝ) := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      have : (1 : ℕ) ≤ m := by omega
      exact_mod_cast this
    nlinarith [hsbound, hm1]
  have hexp1 : Real.exp (-c * D ^ 2 / (1 + (s : ℝ)))
      ≤ Real.exp (-(c / 424000) * (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + (s : ℝ)), hDdef]
    nlinarith [mul_nonneg (by linarith [h1s] : (0 : ℝ) ≤ 10.6 * (m : ℝ) - (1 + (s : ℝ)))
      (by positivity : (0 : ℝ) ≤ c * (m : ℝ)), hc.le, hmpos.le]
  have hexp2 : Real.exp (-c * D) ≤ Real.exp (-(c / 424000) * (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [hDdef]; nlinarith [mul_pos hc hmpos]
  have hfinal : C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D))
      ≤ (m : ℝ) ^ (-A) / 2 := by
    have hCne : C ≠ 0 := ne_of_gt hC
    have h3 : (2 : ℝ) * C * ((1 / (4 * C)) * (m : ℝ) ^ (-A)) = (m : ℝ) ^ (-A) / 2 := by
      field_simp; ring
    calc C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D))
        ≤ C * (Real.exp (-(c / 424000) * (m : ℝ)) + Real.exp (-(c / 424000) * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left (add_le_add hexp1 hexp2) hC.le
      _ = 2 * C * Real.exp (-(c / 424000) * (m : ℝ)) := by ring
      _ ≤ 2 * C * ((1 / (4 * C)) * (m : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_left (hNexp m (by omega)) (by positivity)
      _ = (m : ℝ) ^ (-A) / 2 := h3
  calc (∑' x : ℕ × ℤ, fpDistPlusP p hp0' hp1' s P x * g x).toReal
      ≤ RHS.toReal := ENNReal.toReal_mono hRHSne hUB
    _ = ∑' x : ℕ × ℤ, (fpDistPlusP p hp0' hp1' s P x).toReal *
          Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - p / 2 * (s : ℝ)|} 1 x := hRHSreal
    _ ≤ C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D)) :=
        htail p hp0 hp1 s P D hDbound
    _ ≤ (m : ℝ) ^ (-A) / 2 := hfinal

/-! ### (7.56) — the few-white mass bound at `Pascal(p)` -/

open scoped Classical in
/-- **(7.56) few-white mass bound `_core`** at `Pascal(p)`: the three-term assembly with
all constants `∀`-bound and the three proved mass terms supplied as hypotheses.  The
combined threshold carries the depth gate as `50·g` (so `g ≤ m/50 = (1−t₂)·m`) and the
bad-column numeric `⌈50·62500^{1/A}⌉` (so `m^{−A}/2 ≤ 50^{−A−3}`). -/
theorem few_white_mass_leP_core (A : ℝ) (hA : 0 < A)
    (A' : ℝ) (hA'1 : 1 ≤ A') (ε₀ : ℝ) (g : ℕ) (Cthr_e : ℕ)
    (hestar : ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr_e ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      ∀ P : ℕ, (∀ k, k ≤ P →
          ((⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (0.4 : ℝ)) →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          (∑ k ∈ Finset.range (P + 1),
            Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))
        ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)))
    (hreach : ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamilyP n ξ),
      ∀ (m : ℕ) (l : ℤ) (R : ℕ), 1 ≤ R → ∀ (K P : ℕ),
      ((K : ℝ) + 1) + (A + 5) * Real.log 50 + 2 ≤ ε₀ * R → ∀ s : ℕ,
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStepP F R g)
                (encInitP (n / 2 - m + e.1) (l + e.2))).count
              ∧ ((List.ofFn v).foldl (encStepP F R g)
                (encInitP (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)))
    (K R : ℕ) (hR1 : 1 ≤ R)
    (hRbound : ((K : ℝ) + 1) + (A + 5) * Real.log 50 + 2 ≤ ε₀ * (R : ℝ))
    (P : ℕ) (hP1 : 1 ≤ P) (hPeq : encWindowIter A' (K + 1) R ≤ P)
    (Cthr_c : ℕ)
    (hcol : ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr_c ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) / 2))
    (B : ℝ) (hBdef : B = (4 : ℝ) ^ A' * (1 + (P : ℝ)) ^ 3) :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, max (max Cthr_e Cthr_c) (max (50 * g) (max ⌈B ^ (2.5 : ℝ)⌉₊
        ⌈50 * (62500 : ℝ) ^ (1 / A)⌉₊)) ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (if (∑ k ∈ Finset.range P,
                Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
              ≤ ((K : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 2)) := by
  classical
  have hBnn : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  intro p hp0 hp1 n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  set fp := fpDistP p hp0' hp1' s with hfpdef
  set hold := holdP p hp0' hp1' with hholddef
  have hmCe : Cthr_e ≤ m := by omega
  have hmCc : Cthr_c ≤ m := by omega
  have hm50g : 50 * g ≤ m := by omega
  have hmreg : ⌈B ^ (2.5 : ℝ)⌉₊ ≤ m := by omega
  have hmnum : ⌈50 * (62500 : ℝ) ^ (1 / A)⌉₊ ≤ m := by omega
  have hg : (g : ℝ) ≤ (1 / 50 : ℝ) * (m : ℝ) := by
    have : (50 * g : ℕ) ≤ (m : ℕ) := hm50g
    have hcast : (50 : ℝ) * (g : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
    linarith
  have hreg : ∀ k, k ≤ P →
      ((⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (0.4 : ℝ) := by
    intro k hk
    have hkP : (k : ℝ) ≤ (P : ℝ) := by exact_mod_cast hk
    have hfloor : ((⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
        ≤ (4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3 := Nat.floor_le (by positivity)
    have hmono : (4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3 ≤ B := by
      rw [hBdef]
      have hcube : (1 + (k : ℝ)) ^ 3 ≤ (1 + (P : ℝ)) ^ 3 := by gcongr
      exact mul_le_mul_of_nonneg_left hcube (by positivity)
    have hBle : B ≤ ((m + 1 : ℕ) : ℝ) ^ (0.4 : ℝ) := by
      have h1 : B ^ (2.5 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
        have hce : B ^ (2.5 : ℝ) ≤ ((⌈B ^ (2.5 : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        have hcm : ((⌈B ^ (2.5 : ℝ)⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmreg
        push_cast; linarith
      calc B = (B ^ (2.5 : ℝ)) ^ (0.4 : ℝ) := by
            rw [← Real.rpow_mul hBnn, show (2.5 : ℝ) * (0.4 : ℝ) = 1 by norm_num, Real.rpow_one]
        _ ≤ ((m + 1 : ℕ) : ℝ) ^ (0.4 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    linarith
  have hcolnum : (m : ℝ) ^ (-A) / 2 ≤ (50 : ℝ) ^ (-A - 3) := by
    have hm0 : 0 < m := lt_of_lt_of_le
      (Nat.ceil_pos.mpr (show (0 : ℝ) < 50 * (62500 : ℝ) ^ (1 / A) by positivity)) hmnum
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    have hm50ge : (62500 : ℝ) ^ (1 / A) ≤ (m : ℝ) / 50 := by
      have hc : ((⌈50 * (62500 : ℝ) ^ (1 / A)⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmnum
      have hce : 50 * (62500 : ℝ) ^ (1 / A) ≤ ((⌈50 * (62500 : ℝ) ^ (1 / A)⌉₊ : ℕ) : ℝ) :=
        Nat.le_ceil _
      linarith
    have hpow : (62500 : ℝ) ≤ ((m : ℝ) / 50) ^ A := by
      have heq : (62500 : ℝ) = ((62500 : ℝ) ^ (1 / A)) ^ A := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 62500), one_div,
          inv_mul_cancel₀ (ne_of_gt hA), Real.rpow_one]
      rw [heq]
      exact Real.rpow_le_rpow (by positivity) hm50ge hA.le
    have hkey : ((m : ℝ) / 50) ^ (-A) ≤ 1 / 62500 := by
      rw [Real.rpow_neg (show (0 : ℝ) ≤ (m : ℝ) / 50 by positivity)]
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 62500) hpow
      rwa [one_div] at h
    have hmm : (50 : ℝ) * ((m : ℝ) / 50) = (m : ℝ) := by ring
    have hm_eq : (50 : ℝ) ^ (-A) * ((m : ℝ) / 50) ^ (-A) = (m : ℝ) ^ (-A) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity), hmm]
    have h50 : (0 : ℝ) ≤ (50 : ℝ) ^ (-A) := Real.rpow_nonneg (by norm_num) _
    have e2 : (50 : ℝ) ^ (-A - 3) = (50 : ℝ) ^ (-A) * (50 : ℝ) ^ (-3 : ℝ) := by
      rw [← Real.rpow_add (by norm_num), show (-A : ℝ) + (-3 : ℝ) = -A - 3 by ring]
    have e3 : (50 : ℝ) ^ (-3 : ℝ) = 1 / 125000 := by
      rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
    have hstep : (50 : ℝ) ^ (-A) * ((m : ℝ) / 50) ^ (-A)
        ≤ (50 : ℝ) ^ (-A) * (1 / 62500) := mul_le_mul_of_nonneg_left hkey h50
    rw [hm_eq] at hstep
    rw [e2, e3]; linarith
  set I1 : (ℕ × ℤ) → (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun e v =>
    ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStepP F R g)
          (encInitP (n / 2 - m + e.1) (l + e.2))).count
        ∧ ((List.ofFn v).foldl (encStepP F R g)
          (encInitP (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
      then (1 : ℝ) else 0) with hI1
  set I2 : (ℕ × ℤ) → (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun e v =>
    ∑ k ∈ Finset.range (P + 1),
      Set.indicator (bigTriangleSetP F ⌊(4 : ℝ) ^ A' * (1 + (k : ℝ)) ^ 3⌋₊)
        (1 : ℕ × ℤ → ℝ≥0∞)
        (n / 2 - m - 1 + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) with hI2
  set I3 : (ℕ × ℤ) → (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun e v =>
    ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
      then (1 : ℝ) else 0) with hI3
  have hle : (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        ENNReal.ofReal (if (∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
            ≤ (K : ℝ) then (1 : ℝ) else 0))
      ≤ ∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ,
          hold.iid P v * (I1 e v + I2 e v + I3 e v) := by
    refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
    refine ENNReal.tsum_le_tsum fun v => ?_
    by_cases hv0 : hold.iid P v = 0
    · simp [hv0]
    · have hvsupp : v ∈ (hold.iid P).support := by rw [PMF.mem_support_iff]; exact hv0
      have hvcoord : ∀ i, v i ∈ hold.support := PMF.iid_support_coord hold P v hvsupp
      exact mul_le_mul_right
        (few_white_pointwise_splitP p hp0' hp1' F m hmn hpos l g R K A' hA'1 P hPeq hg e v
          hvcoord) _
  have key : (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ,
        hold.iid P v * (I1 e v + I2 e v + I3 e v))
      = (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I1 e v)
      + (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I2 e v)
      + (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I3 e v) := by
    have inner : ∀ e : ℕ × ℤ, (∑' v : Fin P → ℕ × ℤ, hold.iid P v * (I1 e v + I2 e v + I3 e v))
        = (∑' v : Fin P → ℕ × ℤ, hold.iid P v * I1 e v)
        + (∑' v : Fin P → ℕ × ℤ, hold.iid P v * I2 e v)
        + (∑' v : Fin P → ℕ × ℤ, hold.iid P v * I3 e v) := by
      intro e
      rw [tsum_congr fun v => by rw [mul_add, mul_add], ENNReal.tsum_add, ENNReal.tsum_add]
    rw [tsum_congr fun e => by rw [inner e, mul_add, mul_add], ENNReal.tsum_add, ENNReal.tsum_add]
  refine le_trans hle ?_
  rw [key]
  have hEle : (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I2 e v)
      ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) :=
    hestar p hp0 hp1 n ξ hξ F m hmCe hmn l hpos t ht hmem s hs hs1 P hreg
  have hRle : (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I1 e v)
      ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) :=
    hreach p hp0 hp1 n ξ hξ F m l R hR1 K P hRbound s
  have hCle : (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I3 e v)
      ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) :=
    le_trans (hcol p hp0 hp1 n ξ hξ F m hmCc hmn l hpos t ht hmem s hs hs1 hs2)
      (ENNReal.ofReal_le_ofReal hcolnum)
  have hnum3 : (50 : ℝ) ^ (-A - 3) + (50 : ℝ) ^ (-A - 3) + (50 : ℝ) ^ (-A - 3)
      ≤ (50 : ℝ) ^ (-A - 2) := by
    have e1 : (50 : ℝ) ^ (-A - 3) = (50 : ℝ) ^ (-A - 2) * (50 : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have h1 : (50 : ℝ) ^ (-1 : ℝ) = 1 / 50 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    have hb : (0 : ℝ) ≤ (50 : ℝ) ^ (-A - 2) := Real.rpow_nonneg (by norm_num) _
    rw [e1, h1]; nlinarith [hb]
  calc (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I1 e v)
        + (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I2 e v)
        + (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I3 e v)
      ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) + ENNReal.ofReal ((50 : ℝ) ^ (-A - 3))
          + ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) := add_le_add (add_le_add hRle hEle) hCle
    _ = ENNReal.ofReal ((50 : ℝ) ^ (-A - 3) + (50 : ℝ) ^ (-A - 3) + (50 : ℝ) ^ (-A - 3)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 2)) := ENNReal.ofReal_le_ofReal hnum3

/-! ### (7.55), (7.54), and the Case-3 gate -/

open scoped Classical in
/-- **(7.55) — the pure damping expectation** at `Pascal(p)`: from the few-white bound
at `K ≥ (A+3)·log 50/epsP³`, the count split `exp(−ε³Nw) ≤ 1_{Nw≤K} + 50^{−(A+3)}` gives
`E exp(−epsP³·Nw) ≤ 50^{−A−1}`. -/
theorem damping_expectation_leP_core (A : ℝ) (_hA : 0 < A) (P Cthr K : ℕ)
    (hKge : ((A + 3) * Real.log 50) / (epsP : ℝ) ^ 3 ≤ (K : ℝ))
    (hfew : ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (if (∑ k ∈ Finset.range P,
                Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
              ≤ ((K : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 2))) :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
            Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
              (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))))
        ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 1)) := by
  intro p hp0 hp1 n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  set fp := fpDistP p hp0' hp1' s with hfpdef
  set hold := holdP p hp0' hp1' with hholddef
  have hεpos : (0 : ℝ) < (epsP : ℝ) := by exact_mod_cast epsP_pos
  have hε3pos : (0 : ℝ) < (epsP : ℝ) ^ 3 := by positivity
  have hε3nn : (0 : ℝ) ≤ (epsP : ℝ) ^ 3 := hε3pos.le
  have hpoint : ∀ (e : ℕ × ℤ) (v : Fin P → ℕ × ℤ),
      ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
          Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
            (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))
      ≤ ENNReal.ofReal (if (∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
            ≤ ((K : ℕ) : ℝ)
          then (1 : ℝ) else 0)
        + ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) := by
    intro e v
    set NwE : ℝ := ∑ k ∈ Finset.range P,
        Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
          (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) with hNwEdef
    have hNw0 : (0 : ℝ) ≤ NwE := by
      rw [hNwEdef]; exact Finset.sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => by norm_num) _
    have hind0 : (0 : ℝ) ≤ (if NwE ≤ ((K : ℕ) : ℝ) then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    rw [← ENNReal.ofReal_add hind0 (Real.rpow_nonneg (by norm_num) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases h : NwE ≤ ((K : ℕ) : ℝ)
    · rw [if_pos h]
      have hle1 : Real.exp (-((epsP : ℝ) ^ 3) * NwE) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hε3nn hNw0]
      linarith [hle1, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 50) (-A - 3)]
    · rw [if_neg h]
      have hbig : (A + 3) * Real.log 50 < NwE * (epsP : ℝ) ^ 3 :=
        (div_lt_iff₀ hε3pos).mp (lt_of_le_of_lt hKge (not_le.mp h))
      have hexp : Real.exp (-((epsP : ℝ) ^ 3) * NwE) ≤ (50 : ℝ) ^ (-A - 3) := by
        rw [show (50 : ℝ) ^ (-A - 3) = Real.exp (Real.log 50 * (-A - 3)) from
          Real.rpow_def_of_pos (by norm_num) _]
        exact Real.exp_le_exp.mpr (by nlinarith [hbig])
      linarith [hexp]
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hpoint e v) _) _) ?_
  have key :
      (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (ENNReal.ofReal (if (∑ k ∈ Finset.range P,
                Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
              ≤ ((K : ℕ) : ℝ)
            then (1 : ℝ) else 0)
          + ENNReal.ofReal ((50 : ℝ) ^ (-A - 3))))
      = (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (∑ k ∈ Finset.range P,
                Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
              ≤ ((K : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        + ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) := by
    have inner : ∀ e : ℕ × ℤ,
        (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          (ENNReal.ofReal (if (∑ k ∈ Finset.range P,
                  Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                    (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
                ≤ ((K : ℕ) : ℝ)
              then (1 : ℝ) else 0)
            + ENNReal.ofReal ((50 : ℝ) ^ (-A - 3))))
        = (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (if (∑ k ∈ Finset.range P,
                  Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                    (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
                ≤ ((K : ℕ) : ℝ)
              then (1 : ℝ) else 0))
          + ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) := by
      intro e
      rw [tsum_congr fun v => mul_add (hold.iid P v) _ _, ENNReal.tsum_add,
        ENNReal.tsum_mul_right, (hold.iid P).tsum_coe, one_mul]
    rw [tsum_congr fun e => by rw [inner e, mul_add (fp e)], ENNReal.tsum_add,
      ENNReal.tsum_mul_right, fp.tsum_coe, one_mul]
  rw [key]
  have hfew_app := hfew p hp0 hp1 n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hnum : (50 : ℝ) ^ (-A - 2) + (50 : ℝ) ^ (-A - 3) ≤ (50 : ℝ) ^ (-A - 1) := by
    have hb : (0 : ℝ) ≤ (50 : ℝ) ^ (-A - 1) := Real.rpow_nonneg (by norm_num) _
    have e1 : (50 : ℝ) ^ (-A - 2) = (50 : ℝ) ^ (-A - 1) * (50 : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have e2 : (50 : ℝ) ^ (-A - 3) = (50 : ℝ) ^ (-A - 1) * (50 : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have h1 : (50 : ℝ) ^ (-1 : ℝ) = 1 / 50 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    have h2 : (50 : ℝ) ^ (-2 : ℝ) = 1 / 2500 := by
      rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
    rw [e1, e2, h1, h2]; nlinarith [hb]
  calc (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (∑ k ∈ Finset.range P,
                Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))
              ≤ ((K : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        + ENNReal.ofReal ((50 : ℝ) ^ (-A - 3))
      ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 2)) + ENNReal.ofReal ((50 : ℝ) ^ (-A - 3)) :=
        add_le_add hfew_app le_rfl
    _ = ENNReal.ofReal ((50 : ℝ) ^ (-A - 2) + (50 : ℝ) ^ (-A - 3)) :=
        (ENNReal.ofReal_add (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)).symm
    _ ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 1)) := ENNReal.ofReal_le_ofReal hnum

open scoped Classical in
/-- **(7.54) — the damping × column mass estimate** at `Pascal(p)`: the damping factor
times the end-column weight, integrated against `fpDistP s ⊗ holdP.iid P`, is `≤ m^{−A}`.
On the good column `adv < (49/50)·m` the weight is `≤ 50^A·m^{−A}` and the damping
expectation is `≤ 50^{−A−1}`; the bad column has mass `≤ m^{−A}/2`. -/
theorem damping_column_mass_leP_core (A : ℝ) (hA : 0 < A) (P Cthr_d Cthr_c : ℕ)
    (hdamp : ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr_d ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
            Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
              (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))))
        ≤ ENNReal.ofReal ((50 : ℝ) ^ (-A - 1)))
    (htail : ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr_c ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) / 2)) :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, max (max Cthr_d Cthr_c) 50 ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (
            Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
            ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A)) := by
  intro p hp0 hp1 n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  set fp := fpDistP p hp0' hp1' s with hfpdef
  set hold := holdP p hp0' hp1' with hholddef
  have hmC : Cthr_d ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmT : Cthr_c ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm50 : 50 ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hm0R : (0 : ℝ) ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg hmR.le _
  have h50A0 : (0 : ℝ) ≤ (50 : ℝ) ^ A := Real.rpow_nonneg (by norm_num) _
  have hC50nn : (0 : ℝ) ≤ (50 : ℝ) ^ A * (m : ℝ) ^ (-A) := mul_nonneg h50A0 hm0R
  have hconst50 : (50 : ℝ) ^ A * (m : ℝ) ^ (-A) * (50 : ℝ) ^ (-A - 1) = (m : ℝ) ^ (-A) / 50 := by
    have h1 : (50 : ℝ) ^ A * (50 : ℝ) ^ (-A - 1) = (50 : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 50)]; congr 1; ring
    have h2 : (50 : ℝ) ^ (-1 : ℝ) = 1 / 50 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 50), Real.rpow_one]; norm_num
    calc (50 : ℝ) ^ A * (m : ℝ) ^ (-A) * (50 : ℝ) ^ (-A - 1)
        = (m : ℝ) ^ (-A) * ((50 : ℝ) ^ A * (50 : ℝ) ^ (-A - 1)) := by ring
      _ = (m : ℝ) ^ (-A) * (1 / 50) := by rw [h1, h2]
      _ = (m : ℝ) ^ (-A) / 50 := by ring
  have hpoint : ∀ (e : ℕ × ℤ) (v : Fin P → ℕ × ℤ),
      ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
          Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
            (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
        ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A))
      ≤ ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0)
        + ENNReal.ofReal ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
          ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
            Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
              (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))) := by
    intro e v
    set EXPV : ℝ := Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
        Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
          (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) with hEXVdef
    have hEXPV0 : (0 : ℝ) ≤ EXPV := (Real.exp_pos _).le
    have hEXPV1 : EXPV ≤ 1 := by
      rw [hEXVdef, Real.exp_le_one_iff]
      have hsum0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range P,
          Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
            (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2) :=
        Finset.sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => by norm_num) _
      have hεnn : (0 : ℝ) ≤ (epsP : ℝ) := by exact_mod_cast epsP_pos.le
      have hε30 : (0 : ℝ) ≤ (epsP : ℝ) ^ 3 := by positivity
      nlinarith [hsum0, hε30]
    set WT : ℝ := ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)
      with hWTdef
    have hWT0 : (0 : ℝ) ≤ WT := by rw [hWTdef]; exact Real.rpow_nonneg (by positivity) _
    have hind0 : (0 : ℝ) ≤ (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
        then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    rw [← ENNReal.ofReal_mul hC50nn, ← ENNReal.ofReal_add hind0 (mul_nonneg hC50nn hEXPV0)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hcol : (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
    · rw [if_pos hcol]
      have hWT1 : WT ≤ 1 := by
        rw [hWTdef]
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
        have : (1 : ℕ) ≤ max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 := le_max_right _ _
        exact_mod_cast this
      have hmul : EXPV * WT ≤ 1 := by
        have := mul_le_mul hEXPV1 hWT1 hWT0 (by norm_num : (0 : ℝ) ≤ 1)
        linarith
      nlinarith [hmul, mul_nonneg hC50nn hEXPV0]
    · rw [if_neg hcol]
      have hadvm : e.1 + (pathSum v P).1 < m := by
        have h49 : (49 / 50 : ℝ) * (m : ℝ) ≤ (m : ℝ) := by nlinarith [hmR.le]
        have : ((e.1 + (pathSum v P).1 : ℕ) : ℝ) < (m : ℝ) :=
          lt_of_lt_of_le (not_le.mp hcol) h49
        exact_mod_cast this
      have hdcol_eq : n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)
          = m - (e.1 + (pathSum v P).1) := by omega
      have hcast : ((n / 2 - (n / 2 - m + e.1 + (pathSum v P).1) : ℕ) : ℝ)
          = (m : ℝ) - ((e.1 + (pathSum v P).1 : ℕ) : ℝ) := by
        rw [hdcol_eq, Nat.cast_sub (le_of_lt hadvm)]
      have hmaxge : (1 / 50 : ℝ) * (m : ℝ)
          ≤ ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) := by
        have hbase : (1 / 50 : ℝ) * (m : ℝ)
            ≤ ((n / 2 - (n / 2 - m + e.1 + (pathSum v P).1) : ℕ) : ℝ) := by
          rw [hcast]; have := not_le.mp hcol; linarith
        have hle : ((n / 2 - (n / 2 - m + e.1 + (pathSum v P).1) : ℕ) : ℝ)
            ≤ ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_max_left _ _
        linarith
      have h50m_pos : (0 : ℝ) < 1 / 50 * (m : ℝ) := by positivity
      have hconstEq : (1 / 50 * (m : ℝ)) ^ (-A) = (50 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
        rw [Real.mul_rpow (by norm_num) hmR.le]
        congr 1
        rw [show (1 / 50 : ℝ) = (50 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num) (-A),
          Real.rpow_neg (by norm_num) A, inv_inv]
      have hWTbound : WT ≤ (50 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
        rw [hWTdef, ← hconstEq]
        exact Real.rpow_le_rpow_of_nonpos h50m_pos hmaxge (by linarith)
      calc EXPV * WT ≤ EXPV * ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)) :=
            mul_le_mul_of_nonneg_left hWTbound hEXPV0
        _ = 0 + (50 : ℝ) ^ A * (m : ℝ) ^ (-A) * EXPV := by ring
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hpoint e v) _) _) ?_
  have heq :
      (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
              then (1 : ℝ) else 0)
          + ENNReal.ofReal ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
            ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))))
      = (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        + ENNReal.ofReal ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
          ∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))) := by
    have inner : ∀ e : ℕ × ℤ,
        (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          (ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
                then (1 : ℝ) else 0)
            + ENNReal.ofReal ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
              ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
                Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))))
        = (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
              then (1 : ℝ) else 0))
          + ENNReal.ofReal ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
            ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
              ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
                Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2))) := by
      intro e
      rw [tsum_congr fun v => mul_add (hold.iid P v)
          (ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
          (ENNReal.ofReal ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
            ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))),
        ENNReal.tsum_add]
      congr 1
      rw [tsum_congr fun v => mul_left_comm (hold.iid P v)
          (ENNReal.ofReal ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)))
          (ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
            Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
              (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))),
        ENNReal.tsum_mul_left]
    rw [tsum_congr fun e => by
      rw [inner e, mul_add (fp e)], ENNReal.tsum_add]
    congr 1
    rw [tsum_congr fun e => mul_left_comm (fp e)
        (ENNReal.ofReal ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)))
        (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
            Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
              (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))),
      ENNReal.tsum_mul_left]
  rw [heq]
  have hb1 := htail p hp0 hp1 n ξ hξ F m hmT hmn l hpos t ht hmem s hs hs1 hs2
  have hb2 := hdamp p hp0 hp1 n ξ hξ F m hmC hmn l hpos t ht hmem s hs hs1 hs2
  calc (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (49 / 50 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        + ENNReal.ofReal ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
          ∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)))
      ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) / 2)
        + ENNReal.ofReal ((50 : ℝ) ^ A * (m : ℝ) ^ (-A)) * ENNReal.ofReal ((50 : ℝ) ^ (-A - 1)) :=
        add_le_add hb1 (mul_le_mul_right hb2 _)
    _ = ENNReal.ofReal ((m : ℝ) ^ (-A) / 2) + ENNReal.ofReal ((m : ℝ) ^ (-A) / 50) := by
        rw [← ENNReal.ofReal_mul hC50nn, hconst50]
    _ ≤ ENNReal.ofReal ((m : ℝ) ^ (-A)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hm0R])

open scoped Classical in
/-- **The damped-walk expectation bound** at `Pascal(p)`: peel `QP(end) ≤
max(n/2−j_end,1)^{−A}·QPmFor(m−1)` and apply the damping × column mass estimate. -/
theorem damped_iter_expectation_leP_core (A : ℝ) (hA : 0 < A) (P Cthr : ℕ) (hP1 : 1 ≤ P)
    (hmass : ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (
            Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
            ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A))) :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (
            Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
            QP p (by linarith) (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ)
              (n / 2 - m + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) *
            QPmFor p (by linarith) (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1)) := by
  intro p hp0 hp1 n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  set fp := fpDistP p hp0' hp1' s with hfpdef
  set hold := holdP p hp0' hp1' with hholddef
  have hε0 : (0 : ℝ) ≤ (epsP : ℝ) := by exact_mod_cast epsP_pos.le
  set QM : ℝ := QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) with hQMdef
  have hQM0 : (0 : ℝ) ≤ QM := QPmFor_nonneg p hp0' hp1' _ _ _ _ _
  have step1 :
      (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (
            Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
            QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
              (n / 2 - m + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)))
        ≤ ∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            (ENNReal.ofReal QM *
              ENNReal.ofReal (
                Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
                  Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                    (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
                ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A))) := by
    refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
    refine ENNReal.tsum_le_tsum fun v => ?_
    by_cases hv0 : hold.iid P v = 0
    · simp [hv0]
    · refine mul_le_mul_right ?_ _
      rw [← ENNReal.ofReal_mul hQM0]
      refine ENNReal.ofReal_le_ofReal ?_
      have hvsupp : v ∈ (hold.iid P).support := by
        rw [PMF.mem_support_iff]; exact hv0
      have hvcoord : ∀ i, v i ∈ hold.support := PMF.iid_support_coord hold P v hvsupp
      have hadv : P ≤ (pathSum v P).1 := by
        have h := pathSum_fst_geP p hp0' hp1' v hvcoord 0 P (by omega)
        simpa [pathSum_zero] using h
      have h1 : 1 ≤ n / 2 - m + e.1 + (pathSum v P).1 := by omega
      have h2 : n / 2 - (m - 1) ≤ n / 2 - m + e.1 + (pathSum v P).1 := by omega
      have hQle := QP_le_QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) A hA.le hε0 (m - 1)
        (l := l + e.2 + (pathSum v P).2) h1 h2
      have hEXP0 : (0 : ℝ) ≤ Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
          Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
            (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) := (Real.exp_pos _).le
      calc Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
            QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ)
              (n / 2 - m + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)
          ≤ Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
            (((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
            mul_le_mul_of_nonneg_left hQle hEXP0
        _ = QM *
            (Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
              ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)) := by ring
  have inner_eq : ∀ e : ℕ × ℤ,
      (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (ENNReal.ofReal QM *
          ENNReal.ofReal (
            Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
            ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A))))
        = ENNReal.ofReal QM *
          ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (
              Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
                Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
              ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)) := by
    intro e
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun v => by rw [mul_left_comm]
  have outer_eq :
      (∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (ENNReal.ofReal QM *
          ENNReal.ofReal (
            Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
            ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A))))
        = ENNReal.ofReal QM *
          ∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (
              Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
                Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
              ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)) := by
    simp only [inner_eq]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun e => by rw [mul_left_comm]
  refine le_trans step1 ?_
  rw [outer_eq]
  calc ENNReal.ofReal QM *
        ∑' e : ℕ × ℤ, fp e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (
            Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
            ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A))
      ≤ ENNReal.ofReal QM * ENNReal.ofReal ((m : ℝ) ^ (-A)) :=
        mul_le_mul_right (hmass p hp0 hp1 n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2) _
    _ = ENNReal.ofReal ((m : ℝ) ^ (-A) * QM) := by
        rw [← ENNReal.ofReal_mul hQM0]; congr 1; ring

/-- **Case 3 of Proposition 7.8 at `Pascal(p)`, core**: the (7.53) iterate feeds the
damped-walk expectation bound. -/
theorem QP_black_edge_case3_core (A : ℝ) (_hA : 0 < A) (P Cthr : ℕ)
    (hbound : ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDistP p (by linarith) (by linarith) s e *
          ∑' v : Fin P → ℕ × ℤ, (holdP p (by linarith) (by linarith)).iid P v *
          ENNReal.ofReal (
            Real.exp (-((epsP : ℝ) ^ 3) * ∑ k ∈ Finset.range P,
              Set.indicator (whiteSetP n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v k).1, l + e.2 + (pathSum v k).2)) *
            QP p (by linarith) (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ)
              (n / 2 - m + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) *
            QPmFor p (by linarith) (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1))) :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      QP p (by linarith) (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) *
          QPmFor p (by linarith) (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) := by
  intro p hp0 hp1 n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  have hε0 : (0 : ℝ) ≤ (epsP : ℝ) := by exact_mod_cast epsP_pos.le
  have hentry := QP_le_damped_iter p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) hε0 s P
    (n / 2 - m) l
  have hexp := hbound p hp0 hp1 n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hchain : ENNReal.ofReal (QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) (n / 2 - m) l)
      ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) *
          QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1)) :=
    le_trans hentry hexp
  have hRHSnn : (0 : ℝ) ≤ (m : ℝ) ^ (-A) *
      QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) (QPmFor_nonneg p hp0' hp1' _ _ _ _ _)
  exact (ENNReal.ofReal_le_ofReal_iff hRHSnn).mp hchain

/-- **Case 3 of Proposition 7.8 for `Pascal(p)`** ((7.53)–(7.67) at the finer `epsP`
scale): a deep black-edge start, `m/log²m < s ≤ O(m)`, contracts by `m^{−A}` against
the preceding arbitrary-set depth supremum, uniformly for `p ∈ [1/5, 3/5]`.  Every
constant — the X9 tilt cap and depth gate, the white-count threshold `K`, the
encounter budget `R`, the walk horizon `P`, the E∗ exponent, and the bad-column
threshold — is chosen before `p`.  The statement mirrors `QP_black_edge_case2`. -/
theorem QP_black_edge_case3 (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ,
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamilyP n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      QP p (by linarith [hp0]) (by linarith [hp1])
          (n / 2) (whiteSetP n ξ) (epsP : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) *
          QPmFor p (by linarith [hp0]) (by linarith [hp1])
            (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) := by
  classical
  -- X9 tilt cap and depth gate, from the base-50 reaches bound.
  obtain ⟨ε₀, hε₀, hε₀le, g, hten⟩ := reaches_fewWhite_mass_le_fiftyP
  -- the scaled E∗ exponent
  have hA'1 : (1 : ℝ) ≤ Ascaled_fewEstarP A := one_le_Ascaled_fewEstarP hA
  -- the white-count threshold `K`
  obtain ⟨K, hKge⟩ : ∃ K : ℕ, ((A + 3) * Real.log 50) / (epsP : ℝ) ^ 3 ≤ (K : ℝ) :=
    ⟨⌈((A + 3) * Real.log 50) / (epsP : ℝ) ^ 3⌉₊, Nat.le_ceil _⟩
  -- the encounter budget `R`
  have hlog50 : (0 : ℝ) < Real.log 50 := Real.log_pos (by norm_num)
  obtain ⟨R, hR1, hRbound⟩ : ∃ R : ℕ, 1 ≤ R ∧
      ((K : ℝ) + 1) + (A + 5) * Real.log 50 + 2 ≤ ε₀ * (R : ℝ) := by
    have hnum : (0 : ℝ) < ((K : ℝ) + 1) + (A + 5) * Real.log 50 + 2 := by
      have h1 : (0 : ℝ) < (A + 5) * Real.log 50 := mul_pos (by linarith) hlog50
      have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
      linarith
    refine ⟨⌈(((K : ℝ) + 1) + (A + 5) * Real.log 50 + 2) / ε₀⌉₊,
      Nat.ceil_pos.mpr (div_pos hnum hε₀), ?_⟩
    have hce := Nat.le_ceil ((((K : ℝ) + 1) + (A + 5) * Real.log 50 + 2) / ε₀)
    rw [div_le_iff₀ hε₀] at hce
    linarith
  -- the walk horizon `P`
  obtain ⟨P, hP1, hPeq⟩ : ∃ P : ℕ, 1 ≤ P ∧ encWindowIter (Ascaled_fewEstarP A) (K + 1) R ≤ P := by
    refine ⟨encWindowIter (Ascaled_fewEstarP A) (K + 1) R, ?_, le_rfl⟩
    have h1 : (1 : ℕ) ≤ encWindowIter (Ascaled_fewEstarP A) (K + 1) 1 := by
      rw [encWindowIter_succ]
      have h0 : encWindowIter (Ascaled_fewEstarP A) (K + 1) 0 = 0 := rfl
      omega
    exact le_trans h1 (encWindowIter_mono (Ascaled_fewEstarP A) (K + 1) hR1)
  -- the bad-column tail at horizon `P`
  obtain ⟨Nexp, hNexp⟩ : ∃ Nexp : ℕ, ∀ m : ℕ, Nexp ≤ m →
      Real.exp (-(c_fpColTailP / 424000) * (m : ℝ)) ≤ 1 / (4 * C_fpColTailP) * (m : ℝ) ^ (-A) :=
    ⟨T_expRpow A (c_fpColTailP / 424000) (1 / (4 * C_fpColTailP)),
      exp_neg_mul_le_rpow_neg_at A hA (c_fpColTailP / 424000)
        (div_pos c_fpColTailP_pos (by norm_num)) (1 / (4 * C_fpColTailP))
        (one_div_pos.mpr (mul_pos four_pos C_fpColTailP_pos))⟩
  have hcol := col_tail_mass_leP_core A hA P hP1 c_fpColTailP C_fpColTailP
    c_fpColTailP_pos C_fpColTailP_pos fpDistPlusP_col_tail_explicitC Nexp hNexp
  -- the (7.56) few-white bound
  have hfew := few_white_mass_leP_core A hA (Ascaled_fewEstarP A) hA'1 ε₀ g (10 ^ 30)
    (few_white_estar_mass_leP_at A hA)
    (few_white_reach_mass_leP_core ε₀ g (fun A' => hten ε₀ hε₀ le_rfl A') A)
    K R hR1 hRbound P hP1 hPeq (2000000 * (P + 1) + 200 + Nexp) hcol
    ((4 : ℝ) ^ (Ascaled_fewEstarP A) * (1 + (P : ℝ)) ^ 3) rfl
  -- (7.55), (7.54), the damped iterate, and the gate
  have hdamp := damping_expectation_leP_core A hA P _ K hKge hfew
  have hmass := damping_column_mass_leP_core A hA P _ _ hdamp hcol
  have hiter := damped_iter_expectation_leP_core A hA P _ hP1 hmass
  exact ⟨_, QP_black_edge_case3_core A hA P _ hiter⟩

end TaoCollatz.Sec7P
