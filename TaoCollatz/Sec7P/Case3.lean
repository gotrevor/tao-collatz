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

end TaoCollatz.Sec7P
