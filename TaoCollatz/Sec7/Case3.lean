import TaoCollatz.Sec7.BlackEdgeQ

/-!
# §7.4 Case 3 of Proposition 7.8 — the X11 assembly ((7.53)–(7.67), pp.48–49, 54–55)

The deep-triangle branch `m/log²m < s ≤ O(m)` of the black-edge bound
`Q_black_edge_case3`. This downstream module holds the checked reusable
machinery that consumes Lemma 7.9 (`many_triangles_white`, X9) and Lemma 7.10
(`triangle_encounter_le`, X10), followed by the sole unresolved X11 conclusion
and its proved connection to the public Proposition 7.8 chain.

Paper chain, D6-finitized:

1. **(7.53)** `Q_le_damped_iter`: iterate (7.35) through the first passage and
   `P` further steps, keeping the accumulated white damping
   `exp(−ε³ Σ_{p<P} 1_W((j,l)+v_{[1,k+p]}))` (the entry point
   `Q_le_fpDist_expect` = the `P = 0` case dropped it). Damping is only
   generated in-strip, so the indicator is `whiteStrip`.
2. **(7.54)–(7.55)** (glue inside the final assembly): (7.38)/`Q_le_Qm` at the
   final position turns `Q(end)` into `m^{-A}·Q_{m-1}·max(1−j_{[1,k+P]}/m,1/m)^{-A}`;
   the event `j_{[1,k+P]} ≥ 0.9m` has probability `O_P(e^{−cm})`
   (`fpDistPlus_col_tail` at deviation `≍ m`, since `s/4 ≤ 0.79(m+2)` by (7.52));
   on its complement the weight is `≤ 10^A`, so it suffices that
   `E exp(−ε³ Σ 1_W) ≤ 10^{−A−1}`, which follows from the split at the
   white-count threshold `K = ⌈10A/ε³⌉` and (7.56).
3. **(7.56)** The reusable parts are proved here: the Markov bound
   `fstar_markov_le` over Lemma 7.9 and the deterministic claim (7.67)
   `deterministic_encounter_claim`. The remaining finite union and numerical
   closure are intentionally kept inside the single authoritative X11 gate
   `Q_black_edge_case3` at the end of this module.

Throughout, the joint law is `e ~ fpDist s` (the `k` first-passage steps)
followed by `v ~ hold.iid T` (the post-passage steps), positions
`(j,l) + e + pathSum v p`; per-`p` marginals are `fpDistPlus s p`
(`iid_pathSum_law`), which is exactly the law Lemma 7.10 speaks about.

## X11 risk boundary

This module previously duplicated the unresolved gate with three additional
`sorry` declarations (`estar_union_le`, `few_whites_le`, and
`Q_black_edge_case3_assembled`). None was consumed by the theorem graph: the
downstream chain used the separate declaration in `BlackEdge.lean`. Those
shadow interfaces made X11 look decomposed without reducing its axiom trail.
They have been replaced by one gate after the checked reusable machinery.
`BlackEdge.lean` now exposes parameterized, proved assembly functions, so the
gate here is on an acyclic path to every downstream consumer.
-/

namespace TaoCollatz

open scoped ENNReal

/-! ### Walk partial sums -/

/-- The sum of the first `p` steps of a `T`-step walk (paper `v_{[1,p]}`). For
`p ≥ T` it is the full sum. -/
def pathSum {T : ℕ} (v : Fin T → ℕ × ℤ) (p : ℕ) : ℕ × ℤ :=
  ((List.ofFn v).take p).sum

@[simp] theorem pathSum_zero {T : ℕ} (v : Fin T → ℕ × ℤ) : pathSum v 0 = 0 := rfl

/-- Head-peel of a partial sum: `v_{[1,p+1]}` of `cons d w` is `d + w_{[1,p]}`. -/
theorem pathSum_cons {T : ℕ} (d : ℕ × ℤ) (w : Fin T → ℕ × ℤ) (p : ℕ) :
    pathSum (Fin.cons d w) (p + 1) = d + pathSum w p := by
  rw [pathSum, pathSum, List.ofFn_succ]
  simp [Fin.cons_succ]

/-- One-step extension of a partial sum inside the horizon. -/
theorem pathSum_succ_of_lt {T : ℕ} (v : Fin T → ℕ × ℤ) {p : ℕ} (hp : p < T) :
    pathSum v (p + 1) = pathSum v p + v ⟨p, hp⟩ := by
  rw [pathSum, pathSum, List.take_add_one, List.sum_append]
  congr 1
  have h : (List.ofFn v)[p]? = some (v ⟨p, hp⟩) := by
    rw [List.getElem?_eq_getElem (by simpa using hp)]
    simp
  rw [h]
  simp

/-- Head-peel of a partial sum of a `(T+1)`-vector along its own head/tail
split (no `Fin.cons` in the statement, so it rewrites without motive issues). -/
theorem pathSum_head {T : ℕ} (v : Fin (T + 1) → ℕ × ℤ) (p : ℕ) :
    pathSum v (p + 1) = v 0 + pathSum (fun i : Fin T => v i.succ) p := by
  rw [pathSum, pathSum, List.ofFn_succ]
  simp

/-- Past the horizon the partial sum saturates at the full sum. -/
theorem pathSum_of_ge {T : ℕ} (v : Fin T → ℕ × ℤ) {p : ℕ} (hp : T ≤ p) :
    pathSum v p = pathSum v T := by
  rw [pathSum, pathSum, List.take_of_length_le (by simpa using hp),
    List.take_of_length_le (by simp)]

/-- The partial sum's **first coordinate is monotone** in `p` (the first coordinate of
each `ℕ × ℤ` step is a `ℕ`, hence `≥ 0`). This sources the good-column depth bound in
X11d: on `{adv := e.1+(pathSum v P).1 < 0.9m}` every intermediate position
`(pathSum v p).1 ≤ (pathSum v P).1` stays deep in the strip. -/
theorem pathSum_fst_le {T : ℕ} (v : Fin T → ℕ × ℤ) {p q : ℕ} (hpq : p ≤ q) :
    (pathSum v p).1 ≤ (pathSum v q).1 := by
  have hsplit : (List.ofFn v).take q
      = (List.ofFn v).take p ++ ((List.ofFn v).take q).drop p := by
    conv_lhs => rw [← List.take_append_drop p ((List.ofFn v).take q)]
    rw [List.take_take, Nat.min_eq_left hpq]
  have hq : pathSum v q = pathSum v p + (((List.ofFn v).take q).drop p).sum := by
    conv_lhs => rw [pathSum, hsplit, List.sum_append]
    rw [pathSum]
  rw [hq, Prod.fst_add]
  exact Nat.le_add_right _ _

/-- **Good-column depth sourcing.** If the walk's endpoint stays deep
(`q₀.1 + (pathSum v T).1 + g ≤ half`) then EVERY intermediate position does too, by
`pathSum_fst_le`. This discharges the depth hypothesis of
`few_white_pointwise_dichotomy` on the good column `{adv := e.1+(pathSum v P).1 < 0.9m}`
(with `q₀.1 = n/2−m+e.1`, `half = n/2`: the endpoint bound is `adv + g ≤ m`, which holds
for `g ≤ 0.1m` i.e. `Cthr ≥ 10g`). -/
theorem pathSum_depth_le {T : ℕ} (v : Fin T → ℕ × ℤ) (q₀ : ℕ × ℤ) (g half : ℕ)
    (hend : q₀.1 + (pathSum v T).1 + g ≤ half) :
    ∀ p, p ≤ T → (q₀ + pathSum v p).1 + g ≤ half := by
  intro p hp
  have hmono : (pathSum v p).1 ≤ (pathSum v T).1 := pathSum_fst_le v hp
  have hfst : (q₀ + pathSum v p).1 = q₀.1 + (pathSum v p).1 := rfl
  omega

/-! ### Encounter-fold invariants (interface to X9's `encStep`) -/

/-- `encStep` always advances the position by the step. -/
theorem encStep_pos {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (σ : EncState) (d : ℕ × ℤ) : (encStep F R g σ d).pos = σ.pos + d := by
  rw [encStep]
  split <;> rfl

/-- The fold's position is the start plus the sum of the steps taken. -/
theorem encFold_pos {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) :
    ∀ (L : List (ℕ × ℤ)) (σ : EncState),
      (L.foldl (encStep F R g) σ).pos = σ.pos + L.sum := by
  intro L
  induction L with
  | nil => intro σ; simp
  | cons d L IH =>
    intro σ
    rw [List.foldl_cons, IH, encStep_pos, List.sum_cons, add_assoc]

/-- The fold's count is monotone in the path prefix (`encStep_count_le` is
proved in `ManyTriangles.lean`). -/
theorem encFold_count_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) :
    ∀ (L : List (ℕ × ℤ)) (σ : EncState),
      σ.count ≤ (L.foldl (encStep F R g) σ).count := by
  intro L
  induction L with
  | nil => intro σ; simp
  | cons d L IH =>
    intro σ
    exact le_trans (encStep_count_le F R g σ d) (IH _)

/-- `encStep` preserves `banked ≤ cumWhite` (banking freezes a PAST value of the
running white count, which is itself monotone). -/
theorem encStep_banked_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (σ : EncState) (d : ℕ × ℤ) (h : σ.banked ≤ σ.cumWhite) :
    (encStep F R g σ d).banked ≤ (encStep F R g σ d).cumWhite := by
  rw [encStep]
  split <;> dsimp only <;> split_ifs <;> omega

/-- Fold invariant: `banked ≤ cumWhite` propagates along any path. -/
theorem encFold_banked_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) :
    ∀ (L : List (ℕ × ℤ)) (σ : EncState), σ.banked ≤ σ.cumWhite →
      (L.foldl (encStep F R g) σ).banked ≤ (L.foldl (encStep F R g) σ).cumWhite := by
  intro L
  induction L with
  | nil => intro σ h; simpa using h
  | cons d L IH =>
    intro σ h
    exact IH _ (encStep_banked_le F R g σ d h)

open scoped Classical in
/-- `encStep` adds exactly the new position's white-strip indicator to the
running white count. -/
theorem encStep_cumWhite {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (σ : EncState) (d : ℕ × ℤ) :
    (encStep F R g σ d).cumWhite
      = σ.cumWhite + (if σ.pos + d ∈ whiteStrip n ξ then 1 else 0) := by
  rw [encStep]
  split <;> rfl

open scoped Classical in
/-- The fold's running white count is the start count plus the number of
white-strip positions visited (the positions AFTER each step,
`σ.pos + v_{[1,p+1]}` for `p < T`). -/
theorem encFold_cumWhite {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) :
    ∀ (T : ℕ) (v : Fin T → ℕ × ℤ) (σ : EncState),
      ((List.ofFn v).foldl (encStep F R g) σ).cumWhite
        = σ.cumWhite + (Finset.range T).sum
            (fun p => if σ.pos + pathSum v (p + 1) ∈ whiteStrip n ξ then 1 else 0) := by
  intro T
  induction T with
  | zero => intro v σ; simp
  | succ T IH =>
    intro v σ
    rw [List.ofFn_succ, List.foldl_cons,
      IH (fun i : Fin T => v i.succ) (encStep F R g σ (v 0)),
      encStep_cumWhite, encStep_pos, Finset.sum_range_succ']
    have h0 : pathSum v 1 = v 0 := by
      simpa using pathSum_head v 0
    have hstep : ∀ p : ℕ,
        pathSum v (p + 1 + 1) = v 0 + pathSum (fun i : Fin T => v i.succ) (p + 1) :=
      fun p => pathSum_head v (p + 1)
    rw [h0]
    have hsum : ∀ p ∈ Finset.range T,
        (if σ.pos + v 0 + pathSum (fun i : Fin T => v i.succ) (p + 1) ∈ whiteStrip n ξ
          then (1 : ℕ) else 0)
        = (if σ.pos + pathSum v (p + 1 + 1) ∈ whiteStrip n ξ then 1 else 0) := by
      intro p _
      rw [hstep p, add_assoc]
    rw [Finset.sum_congr rfl hsum]
    omega

/-! ### The (7.53) master iterate -/

/-- **Iterated (7.35) with retained damping — the walk half** (paper (7.53) with
the first-passage prefix stripped): for ANY start, the renewal value is bounded
by the `P`-step average of the accumulated in-strip white damping times the
value at the end position. Damping is only generated inside the strip (the
recursion `Q_rec` applies only at `j ≤ half`; past the edge `Q ≡ 1` emits no
factor), hence the `W ∩ strip` indicator. -/
theorem Q_le_walk_damped (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (P : ℕ) (j : ℕ) (l : ℤ),
      ENNReal.ofReal (Q half W ε j l)
        ≤ ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (
              Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
                Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                  (j + (pathSum v p).1, l + (pathSum v p).2)) *
              Q half W ε (j + (pathSum v P).1) (l + (pathSum v P).2)) := by
  intro P
  induction P with
  | zero =>
    intro j l
    rw [PMF.tsum_iid_zero_mul hold
      (fun v : Fin 0 → ℕ × ℤ => ENNReal.ofReal (
        Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range 0,
          Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
            (j + (pathSum v p).1, l + (pathSum v p).2)) *
        Q half W ε (j + (pathSum v 0).1) (l + (pathSum v 0).2)))]
    simp
  | succ P IH =>
    intro j l
    -- peel the head step off the RHS
    rw [PMF.tsum_iid_succ_mul hold P]
    rcases Nat.lt_or_ge half j with hout | hin
    · -- boundary: every position is past the edge, integrand ≡ 1
      rw [Q_boundary _ _ _ _ _ hout, ENNReal.ofReal_one]
      have hone : ∀ (d : ℕ × ℤ) (w : Fin P → ℕ × ℤ),
          ENNReal.ofReal (
            Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range (P + 1),
              Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (j + (pathSum (Fin.cons d w) p).1,
                  l + (pathSum (Fin.cons d w) p).2)) *
            Q half W ε (j + (pathSum (Fin.cons d w) (P + 1)).1)
              (l + (pathSum (Fin.cons d w) (P + 1)).2)) = 1 := by
        intro d w
        have hind : ∀ p : ℕ,
            Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) (1 : ℕ × ℤ → ℝ)
              (j + (pathSum (Fin.cons d w) p).1,
                l + (pathSum (Fin.cons d w) p).2) = 0 := by
          intro p
          refine Set.indicator_of_notMem (fun hmem => ?_) 1
          have := hmem.2
          simp only [Set.mem_setOf_eq] at this
          omega
        have hQ : Q half W ε (j + (pathSum (Fin.cons d w) (P + 1)).1)
            (l + (pathSum (Fin.cons d w) (P + 1)).2) = 1 :=
          Q_boundary _ _ _ _ _ (by omega)
        rw [hQ, mul_one, Finset.sum_congr rfl (fun p _ => hind p)]
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
    · -- interior: one Q_rec step, then the inductive hypothesis at (j+d₁, l+d₂)
      rw [Q_rec _ _ _ _ _ hin]
      have hQS0 : 0 ≤ ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2) :=
        tsum_nonneg fun d => mul_nonneg ENNReal.toReal_nonneg (Q_nonneg _ _ _ _ _)
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      -- lift the hold-average to ℝ≥0∞
      have hlift : ENNReal.ofReal
            (∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2))
          = ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (Q half W ε (j + d.1) (l + d.2)) := by
        rw [← PMF.toReal_tsum_mul_ofReal hold _ (fun d => Q_nonneg _ _ _ _ _),
          ENNReal.ofReal_toReal]
        exact ne_top_of_le_ne_top (by simp)
          (PMF.tsum_mul_ofReal_le_one hold _ (fun d => Q_le_one _ _ _ hε _ _))
      rw [hlift, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun d => ?_
      -- reorder the constant damping factor inside
      rw [← mul_assoc, mul_comm (ENNReal.ofReal (Real.exp _)) (hold d), mul_assoc]
      refine mul_le_mul_right ?_ (hold d)
      -- apply the IH at the shifted start, then push the head factor inside
      have hIH := IH (j + d.1) (l + d.2)
      calc ENNReal.ofReal (Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)))
            * ENNReal.ofReal (Q half W ε (j + d.1) (l + d.2))
          ≤ ENNReal.ofReal (Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)))
            * ∑' w : Fin P → ℕ × ℤ, hold.iid P w *
              ENNReal.ofReal (
                Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
                  Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                    (j + d.1 + (pathSum w p).1, l + d.2 + (pathSum w p).2)) *
                Q half W ε (j + d.1 + (pathSum w P).1) (l + d.2 + (pathSum w P).2)) :=
            mul_le_mul_right hIH _
        _ = _ := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun w => ?_
            rw [← mul_assoc, mul_comm (ENNReal.ofReal (Real.exp _)) (hold.iid P w),
              mul_assoc]
            refine congrArg _ ?_
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc,
              ← Real.exp_add]
            -- the exponents and end positions match under the head-peel
            have hend : pathSum (Fin.cons d w) (P + 1) = d + pathSum w P :=
              pathSum_cons d w P
            have hexp : -(ε ^ 3) * Set.indicator W 1 (j, l)
                  + -(ε ^ 3) * ∑ p ∈ Finset.range P,
                    Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                      (j + d.1 + (pathSum w p).1, l + d.2 + (pathSum w p).2)
                = -(ε ^ 3) * ∑ p ∈ Finset.range (P + 1),
                    Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                      (j + (pathSum (Fin.cons d w) p).1,
                        l + (pathSum (Fin.cons d w) p).2) := by
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
              have hstep : ∀ p ∈ Finset.range P,
                  Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) (1 : ℕ × ℤ → ℝ)
                    (j + (pathSum (Fin.cons d w) (p + 1)).1,
                      l + (pathSum (Fin.cons d w) (p + 1)).2)
                  = Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                    (j + d.1 + (pathSum w p).1, l + d.2 + (pathSum w p).2) := by
                intro p _
                rw [pathSum_cons]
                congr 2
                · show j + (d.1 + (pathSum w p).1) = j + d.1 + (pathSum w p).1
                  omega
                · show l + (d.2 + (pathSum w p).2) = l + d.2 + (pathSum w p).2
                  ring
              rw [Finset.sum_congr rfl hstep, h0]
              ring
            rw [hexp, hend]
            congr 3
            · show j + d.1 + (pathSum w P).1 = j + (d.1 + (pathSum w P).1)
              omega
            · show l + d.2 + (pathSum w P).2 = l + (d.2 + (pathSum w P).2)
              ring

/-- **The (7.53) master iterate** (paper p.48): through the first passage at
budget `s` and `P` further `Hold` steps, the renewal value is bounded by the
joint average of the accumulated white-strip damping times the end value. The
`p = 0` term of the damping sum sits at the first-passage endpoint itself
(paper `v_{[1,k+0]}`), and the end value sits at `v_{[1,k+P]}`. -/
theorem Q_le_damped_iter (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε)
    (s P : ℕ) (j : ℕ) (l : ℤ) :
    ENNReal.ofReal (Q half W ε j l)
      ≤ ∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (
            Real.exp (-(ε ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (W ∩ {q : ℕ × ℤ | q.1 ≤ half}) 1
                (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            Q half W ε (j + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)) := by
  refine le_trans (Q_le_fpDist_expect half W ε hε s j l) ?_
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
  exact Q_le_walk_damped half W ε hε P (j + e.1) (l + e.2)

/-! ### The prefix-marginal law: post-passage positions are `fpDistPlus` -/

/-- **Prefix marginal of the iid walk**: integrating an observable of the
`p`-step partial sum over the `T`-step walk (`p ≤ T`) is integrating it against
the `p`-fold iid sum. Composed with `fpDist s` this identifies the law of the
position `(j,l) + e + v_{[1,p]}` with `fpDistPlus s p` — the marginal Lemma
7.10 (`triangle_encounter_le`) bounds. -/
theorem iid_pathSum_law :
    ∀ (T p : ℕ), p ≤ T → ∀ (f : ℕ × ℤ → ℝ≥0∞),
      ∑' v : Fin T → ℕ × ℤ, hold.iid T v * f (pathSum v p)
        = ∑' d : ℕ × ℤ, iidSum hold p d * f d := by
  intro T
  induction T with
  | zero =>
    intro p hp f
    rw [Nat.le_zero.mp hp]
    rw [PMF.tsum_iid_zero_mul hold (fun v : Fin 0 → ℕ × ℤ => f (pathSum v 0))]
    rw [iidSum_zero]
    rw [tsum_eq_single (0 : ℕ × ℤ) (fun d hd => by
      rw [PMF.pure_apply, if_neg hd, zero_mul])]
    rw [PMF.pure_apply, if_pos rfl, one_mul, pathSum_zero]
  | succ T IH =>
    intro p hp f
    rw [PMF.tsum_iid_succ_mul hold T (fun v => f (pathSum v p))]
    rcases Nat.eq_zero_or_pos p with rfl | hppos
    · -- p = 0: both sides are f 0
      have hinner : ∀ d : ℕ × ℤ,
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
    · -- p = q+1: head-peel both sides
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hppos
      rw [tsum_congr fun d : ℕ × ℤ => by
        rw [tsum_congr fun w : Fin T → ℕ × ℤ => by
          rw [show 1 + q = q + 1 from by omega, pathSum_cons]]]
      have hIH : ∀ d : ℕ × ℤ,
          ∑' w : Fin T → ℕ × ℤ, hold.iid T w * f (d + pathSum w q)
            = ∑' x : ℕ × ℤ, iidSum hold q x * f (d + x) :=
        fun d => IH q (by omega) (fun x => f (d + x))
      rw [tsum_congr fun d => by rw [hIH d]]
      -- reassemble via iidSum_succ
      rw [show 1 + q = q + 1 from by omega, iidSum_succ, PMF.tsum_bind_mul]
      exact tsum_congr fun d => by rw [PMF.tsum_map_mul]

/-- **The `fpDistPlus` prefix marginal, in walk form** (paper (7.53)→(7.54) bridge):
integrating an observable `g` of the position `e + (pathSum v p)` against
`fpDist s ⊗ hold.iid T` (the first-passage endpoint `e` plus the `p`-step prefix of
the `T`-step Hold walk, `p ≤ T`) equals integrating `g` against the convolution
marginal `fpDistPlus s p`. This is precisely the law whose big-triangle-hitting
probability `triangle_encounter_le` (X10) bounds, so it is the conversion that turns
the `Q_le_damped_iter` walk expectation into `fpDistPlus`-form for the (7.54)–(7.55)
E∗ union bound. Composes `iid_pathSum_law` (prefix marginal = `iidSum hold p`) with
the `bind`/`map` unfolding of `fpDistPlus`. -/
theorem fpDist_walk_eq_fpDistPlus (s : ℕ) {T p : ℕ} (hp : p ≤ T) (g : ℕ × ℤ → ℝ≥0∞) :
    ∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v * g (e + pathSum v p)
      = ∑' x : ℕ × ℤ, fpDistPlus s p x * g x := by
  have hRHS : ∑' x : ℕ × ℤ, fpDistPlus s p x * g x
      = ∑' e : ℕ × ℤ, fpDist s e * ∑' d : ℕ × ℤ, iidSum hold p d * g (e + d) := by
    have hdef : (∑' x : ℕ × ℤ, fpDistPlus s p x * g x)
        = ∑' x : ℕ × ℤ,
            ((fpDist s).bind (fun e => (iidSum hold p).map fun w => e + w)) x * g x := rfl
    rw [hdef, PMF.tsum_bind_mul]
    exact tsum_congr fun e => by rw [PMF.tsum_map_mul]
  rw [hRHS]
  refine tsum_congr fun e => ?_
  congr 1
  simpa only [] using iid_pathSum_law T p hp (fun d => g (e + d))

/-- **The per-`p` big-triangle walk mass bound**, `_explicitC` sibling at
`C_encTri`/`c_encTri`, `A₀ = 5` (the X10 explicit threshold). Same body as the `∃`-form
below, closing on `triangle_encounter_le_rpow_explicitC` instead of the obtained witness. -/
theorem bigTriangle_walk_le_rpow_explicitC :
    ∀ (A : ℝ), 5 ≤ A →
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ), (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (T p s' : ℕ), p ≤ T → 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
        (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
          Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞)
            (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)).toReal
          ≤ C_encTri * A ^ 2 * (1 + (p : ℝ)) / (s' : ℝ)
            + C_encTri * Real.exp (-c_encTri * A ^ 2 * (1 + (p : ℝ))) := by
  intro A hA n ξ hξ F t₀ ht₀ j l hmem s hs hdeep T p s' hpT hs'1 hs'm
  have hind_eq : ∀ y : ℕ × ℤ,
      Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞) y
        = ENNReal.ofReal (Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ) y) := by
    intro y
    by_cases h : y ∈ bigTriangleSet F s'
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp
  have hpos : ∀ (e : ℕ × ℤ) (v : Fin T → ℕ × ℤ),
      ((j + e.1 + (pathSum v p).1 : ℕ), (l + e.2 + (pathSum v p).2 : ℤ))
        = ((j : ℕ), (l : ℤ)) + (e + pathSum v p) := by
    intro e v; ext <;> simp [add_assoc]
  -- convert the ℝ≥0∞ walk sum to `fpDistPlus` marginal form
  have hwalk : (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
        Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞)
          (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
      = ∑' x : ℕ × ℤ, fpDistPlus s p x *
          Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞) (((j : ℕ), (l : ℤ)) + x) := by
    have hconv : (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
          Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞)
            (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
        = ∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
            Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞)
              (((j : ℕ), (l : ℤ)) + (e + pathSum v p)) := by
      refine tsum_congr fun e => ?_
      congr 1
      refine tsum_congr fun v => ?_
      congr 1
      exact congrArg _ (hpos e v)
    rw [hconv]
    exact fpDist_walk_eq_fpDistPlus s hpT
      (fun x : ℕ × ℤ => Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞)
        (((j : ℕ), (l : ℤ)) + x))
  have hstep : ∑' x : ℕ × ℤ, fpDistPlus s p x *
        Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞) (((j : ℕ), (l : ℤ)) + x)
      = ∑' x : ℕ × ℤ, fpDistPlus s p x *
          ENNReal.ofReal
            (Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ) (((j : ℕ), (l : ℤ)) + x)) :=
    tsum_congr fun x => by rw [hind_eq]
  have heq : (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
        Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞)
          (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)).toReal
      = ∑' x : ℕ × ℤ, (fpDistPlus s p x).toReal
          * Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ) (((j : ℕ), (l : ℤ)) + x) := by
    rw [hwalk, hstep]
    exact PMF.toReal_tsum_mul_ofReal (fpDistPlus s p)
      (fun x => Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ) (((j : ℕ), (l : ℤ)) + x))
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  rw [heq]
  exact triangle_encounter_le_rpow_explicitC A hA n ξ hξ F t₀ ht₀ j l hmem s hs hdeep p s' hs'1 hs'm

/-- **The per-`p` big-triangle walk mass bound** (paper (7.54)–(7.55), one term of
the E∗ union): the chance the `T`-step walk's position at time `p` (`p ≤ T`, started
at `(j,l)` after the first passage `e`) lands in a size-`≥ s'` triangle is bounded by
Lemma 7.10 (`triangle_encounter_le`, X10) at that `s'`, provided `s'` fits the X10
regime `1 ≤ s' ≤ (n/2−j)^{0.4}`. Composes `fpDist_walk_eq_fpDistPlus` (walk →
`fpDistPlus` marginal) with X10; the `ℝ≥0∞` walk sum is pushed to `ℝ` in one step via
`PMF.toReal_tsum_mul_ofReal`. This is the summand of the X11a `estar_union_le` union
bound. -/
theorem bigTriangle_walk_le_rpow :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (A : ℝ), A₀ ≤ A →
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ), (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (T p s' : ℕ), p ≤ T → 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
        (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
          Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞)
            (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)).toReal
          ≤ C * A ^ 2 * (1 + (p : ℝ)) / (s' : ℝ)
            + C * Real.exp (-c * A ^ 2 * (1 + (p : ℝ))) :=
  ⟨C_encTri, C_encTri_pos, c_encTri, c_encTri_pos, 5, by norm_num,
    bigTriangle_walk_le_rpow_explicitC⟩

/-! ### The proved (7.56) ingredients -/

open scoped Classical in
/-- **The `F∗` Markov bound** (paper p.55 top): under Lemma 7.9's conclusion
(supplied as the hypothesis `hbound`, from `many_triangles_white`), the chance
that the encounter fold's (7.57) integrand `encVal` exceeds `lam` is
`≤ e^{2ε}/lam` — Markov's inequality over the `T`-step walk, uniform in the
start `q₀`. -/
theorem fstar_markov_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (q₀ : ℕ × ℤ)
    (hbound : encExpect F R g ε T (encInit q₀.1 q₀.2) ≤ Real.exp (2 * ε))
    (lam : ℝ) (hlam : 0 < lam) :
    ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
      (if lam ≤ encVal ε R ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2))
        then (1 : ℝ) else 0)
    ≤ Real.exp (2 * ε) / lam := by
  set X : (Fin T → ℕ × ℤ) → ℝ :=
    fun v => encVal ε R ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2))
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
      = encExpect F R g ε T (encInit q₀.1 q₀.2) := rfl
  calc ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
        (if lam ≤ X v then (1 : ℝ) else 0)
      ≤ ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal * X v / lam :=
        hsumL.tsum_le_tsum hind hsumXd
    _ = (∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal * X v) / lam :=
        tsum_div_const
    _ ≤ Real.exp (2 * ε) / lam := by
        rw [hEE]
        gcongr

/-- **The (7.56) `F∗` Markov bound, X9-discharged** (paper p.55): the `encExpect ≤
e^{2ε}` hypothesis of `fstar_markov_le` is exactly Lemma 7.9's conclusion, now a
theorem (`many_triangles_white`). Composing them fixes the encoding gate `g` (from
`many_triangles_white`) and eliminates the hypothesis, giving the self-contained
probabilistic input to the Case-3 assembly: for any tilt `ε ≤ ε₀`, encounter
budget `R ≥ 1`, horizon `T` and start `q₀`, the walk-mass on which the (7.57)
integrand `encVal` reaches `lam` is `≤ e^{2ε}/lam`. This is the (7.56) half of the
`Q_black_edge_case3` join (the deterministic (7.67) claim supplies the other).
`_at` sibling at `eps0_manyTri`/`g_manyTri` (big-C campaign, step 2). -/
theorem fstar_markov_at :
    ∀ ε : ℝ, 0 < ε → ε ≤ eps0_manyTri →
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (lam : ℝ), 0 < lam →
        ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
          (if lam ≤ encVal ε R
              ((List.ofFn v).foldl (encStep F R g_manyTri) (encInit q₀.1 q₀.2))
            then (1 : ℝ) else 0)
        ≤ Real.exp (2 * ε) / lam := by
  intro ε hε hεε₀ n ξ hξ F R hR T q₀ lam hlam
  exact fstar_markov_le F R g_manyTri ε hε.le T q₀
    (many_triangles_white_at ε hε hεε₀ n ξ hξ F R hR T q₀.1 q₀.2) lam hlam

/-- `fstar_markov`, original `∃`-form: delegates to the `_at` sibling. -/
theorem fstar_markov :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 100 ∧ ∃ g : ℕ,
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (lam : ℝ), 0 < lam →
        ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
          (if lam ≤ encVal ε R ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2))
            then (1 : ℝ) else 0)
        ≤ Real.exp (2 * ε) / lam :=
  ⟨eps0_manyTri, eps0_manyTri_pos, eps0_manyTri_le, g_manyTri, fstar_markov_at⟩

/-! ### Machinery for the deterministic claim (7.67) -/

/-- The first coordinate of any `hold`-atom is at least `1` (support form of
`hold_zero_of_fst_zero`): the walk's column strictly advances every step. -/
theorem hold_support_fst_ge (d : ℕ × ℤ) (hd : d ∈ hold.support) : 1 ≤ d.1 := by
  by_contra h
  exact (PMF.mem_support_iff _ _).mp hd (hold_zero_of_fst_zero (by omega))

/-- The fold state after the first `p` steps of the walk `v` (the paper's
stopped state at time `p`). -/
noncomputable def encFoldAt {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) (p : ℕ) : EncState :=
  ((List.ofFn v).take p).foldl (encStep F R g) (encInit q₀.1 q₀.2)

theorem encFoldAt_zero {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) :
    encFoldAt F R g q₀ v 0 = encInit q₀.1 q₀.2 := rfl

/-- Stepping the stopped state: one more `encStep` at the `p`-th walk step. -/
theorem encFoldAt_succ {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) {p : ℕ} (hp : p < T) :
    encFoldAt F R g q₀ v (p + 1)
      = encStep F R g (encFoldAt F R g q₀ v p) (v ⟨p, hp⟩) := by
  rw [encFoldAt, encFoldAt, List.take_add_one,
    List.getElem?_eq_getElem (by simpa using hp)]
  simp [List.foldl_append]

/-- At the horizon, the stopped state is the full fold. -/
theorem encFoldAt_top {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) :
    encFoldAt F R g q₀ v T
      = (List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2) := by
  rw [encFoldAt, List.take_of_length_le (by simp)]

/-- The stopped state's position is the start plus the partial sum. -/
theorem encFoldAt_pos {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) (p : ℕ) :
    (encFoldAt F R g q₀ v p).pos = q₀ + pathSum v p := by
  rw [encFoldAt, encFold_pos, pathSum]
  show (q₀.1, q₀.2) + _ = _
  rfl

/-- The stopped count is monotone in time. -/
theorem encFoldAt_count_mono {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) {p p' : ℕ} (h : p ≤ p') (hp' : p' ≤ T) :
    (encFoldAt F R g q₀ v p).count ≤ (encFoldAt F R g q₀ v p').count := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simp
  | succ k IH =>
    rw [show p + (k + 1) = (p + k) + 1 from rfl,
      encFoldAt_succ F R g q₀ v (show p + k < T by omega)]
    exact le_trans (IH (by omega)) (encStep_count_le F R g _ _)

/-- If a step does not change the count, it does not change the barrier
(the barrier only moves at encounters). -/
theorem encStep_barrier_of_count_eq {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (σ : EncState) (d : ℕ × ℤ)
    (h : (encStep F R g σ d).count = σ.count) :
    (encStep F R g σ d).barrier = σ.barrier := by
  rw [encStep] at h ⊢
  split at h
  · exfalso
    dsimp only at h
    omega
  · rename_i hq
    rw [dif_neg hq]

/-- If the count is flat over a time window, the barrier is flat too. -/
theorem encFoldAt_barrier_of_count_eq {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) {p p' : ℕ} (h : p ≤ p') (hp' : p' ≤ T)
    (hcnt : (encFoldAt F R g q₀ v p').count = (encFoldAt F R g q₀ v p).count) :
    (encFoldAt F R g q₀ v p').barrier = (encFoldAt F R g q₀ v p).barrier := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => rfl
  | succ k IH =>
    have hpk : p + k < T := by omega
    have hmono1 := encFoldAt_count_mono F R g q₀ v (show p ≤ p + k by omega)
      (show p + k ≤ T by omega)
    have hstep := encStep_count_le F R g (encFoldAt F R g q₀ v (p + k)) (v ⟨p + k, hpk⟩)
    rw [show p + (k + 1) = (p + k) + 1 from rfl, encFoldAt_succ F R g q₀ v hpk] at hcnt ⊢
    have hflat : (encStep F R g (encFoldAt F R g q₀ v (p + k)) (v ⟨p + k, hpk⟩)).count
        = (encFoldAt F R g q₀ v (p + k)).count := by omega
    rw [encStep_barrier_of_count_eq F R g _ _ hflat]
    exact IH (by omega) (by omega : (encFoldAt F R g q₀ v (p + k)).count
      = (encFoldAt F R g q₀ v p).count)

/-- On-support walks advance the column by at least one per step. -/
theorem pathSum_fst_ge {T : ℕ} (v : Fin T → ℕ × ℤ) (hv : ∀ i, v i ∈ hold.support) :
    ∀ (p k : ℕ), p + k ≤ T → (pathSum v p).1 + k ≤ (pathSum v (p + k)).1 := by
  intro p k
  induction k with
  | zero => intro _; simp
  | succ k IH =>
    intro hk
    have hpk : p + k < T := by omega
    rw [show p + (k + 1) = (p + k) + 1 from rfl, pathSum_succ_of_lt v hpk]
    have h1 := hold_support_fst_ge _ (hv ⟨p + k, hpk⟩)
    have h2 := IH (by omega)
    show (pathSum v p).1 + (k + 1) ≤ (pathSum v (p + k)).1 + (v ⟨p + k, hpk⟩).1
    omega

/-- On-support walks gain at least `3` height per step. -/
theorem pathSum_snd_ge {T : ℕ} (v : Fin T → ℕ × ℤ) (hv : ∀ i, v i ∈ hold.support) :
    ∀ (p k : ℕ), p + k ≤ T → (pathSum v p).2 + 3 * k ≤ (pathSum v (p + k)).2 := by
  intro p k
  induction k with
  | zero => intro _; simp
  | succ k IH =>
    intro hk
    have hpk : p + k < T := by omega
    rw [show p + (k + 1) = (p + k) + 1 from rfl, pathSum_succ_of_lt v hpk]
    have h1 := hold_support_snd_ge _ (hv ⟨p + k, hpk⟩)
    have h2 := IH (by omega)
    show (pathSum v p).2 + 3 * ((k : ℤ) + 1) ≤ (pathSum v (p + k)).2 + (v ⟨p + k, hpk⟩).2
    linarith

/-- An in-strip position (`1 ≤ q₁ ≤ n/2`) outside the white strip is black at
its phase point (`white = ¬ black` complementarity). -/
theorem black_of_notMem_whiteStrip {n ξ : ℕ} {q : ℕ × ℤ} (h1 : 1 ≤ q.1)
    (h2 : q.1 ≤ n / 2) (h : q ∉ whiteStrip n ξ) : black n ξ (q.1 - 1) q.2 := by
  by_contra hb
  exact h ⟨h2, h1, hb⟩

/-- The (7.11) height extent of a triangle: any member sits within `s/log 2`
of the top (drop the nonnegative column term of the defining inequality). -/
theorem triangle_top_le {j₀ : ℕ} {l₀ : ℤ} {s : ℝ} {q : ℕ × ℤ}
    (hq : q ∈ triangle j₀ l₀ s) : ((l₀ - q.2 : ℤ) : ℝ) * Real.log 2 ≤ s := by
  obtain ⟨hj, hl, hlin⟩ := hq
  have hj' : (j₀ : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast hj
  have hcol : (0 : ℝ) ≤ ((q.1 : ℝ) - j₀) * Real.log 9 :=
    mul_nonneg (by linarith) (Real.log_nonneg (by norm_num))
  push_cast
  linarith

open scoped Classical in
/-- **The barrier envelope**: along a path satisfying the depth and small-size
hypotheses, the fold's barrier never exceeds the current height by more than
`2·4^A(1+p)³` — the barrier is either the vacuous start height or the top of a
small triangle containing a recent position ((7.11) extent + `log 2 > 1/2`). -/
theorem encFoldAt_barrier_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {T : ℕ} (v : Fin T → ℕ × ℤ) (hv : ∀ i, v i ∈ hold.support)
    (A : ℝ) (hA : 0 ≤ A)
    (hsmall : ∀ p, p ≤ T → ∀ t ∈ F.T,
      ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ triangle t.1 t.2.1 t.2.2 →
      t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3) :
    ∀ p, p ≤ T →
      (((encFoldAt F R g q₀ v p).barrier : ℝ))
        ≤ ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 2 * (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := by
  have h4A : (1 : ℝ) ≤ (4 : ℝ) ^ A := Real.one_le_rpow (by norm_num) hA
  intro p
  induction p with
  | zero =>
    intro _
    have hb : (encFoldAt F R g q₀ v 0).barrier = q₀.2 := rfl
    have hz : (pathSum v 0).2 = 0 := by simp
    rw [hb, hz]
    push_cast
    nlinarith
  | succ p IH =>
    intro hp1
    have hp : p ≤ T := by omega
    have hplt : p < T := by omega
    rw [encFoldAt_succ F R g q₀ v hplt]
    -- height grows, and the (1+p)³ envelope grows
    have hgrow : ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 2 * (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3
        ≤ ((q₀.2 + (pathSum v (p + 1)).2 : ℤ) : ℝ)
          + 2 * (4 : ℝ) ^ A * (1 + ((p + 1 : ℕ) : ℝ)) ^ 3 := by
      have hht := pathSum_snd_ge v hv p 1 (by omega)
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      have hcube : (1 + (p : ℝ)) ^ 3 ≤ (1 + ((p + 1 : ℕ) : ℝ)) ^ 3 := by
        push_cast
        nlinarith
      have h2A : (0 : ℝ) ≤ 2 * (4 : ℝ) ^ A := by linarith
      have := mul_le_mul_of_nonneg_left hcube h2A
      have hht' : ((pathSum v p).2 : ℝ) + 3 ≤ ((pathSum v (p + 1)).2 : ℝ) := by
        exact_mod_cast hht
      have hhtR : ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ)
          ≤ ((q₀.2 + (pathSum v (p + 1)).2 : ℤ) : ℝ) := by
        push_cast
        linarith
      calc ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 2 * (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3
          ≤ ((q₀.2 + (pathSum v (p + 1)).2 : ℤ) : ℝ)
            + 2 * (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := by linarith
        _ ≤ _ := by linarith [this]
    rw [encStep]
    split
    case isTrue hcond =>
      -- encounter: the new barrier is the covering triangle's top
      dsimp only
      set q : ℕ × ℤ := (encFoldAt F R g q₀ v p).pos + v ⟨p, hplt⟩ with hq
      have hqpos : q = q₀ + pathSum v (p + 1) := by
        rw [hq, encFoldAt_pos, pathSum_succ_of_lt v hplt, add_assoc]
      set t := F.coveringTriangle (q.1 - 1, q.2)
        ⟨show q.1 - 1 + 1 ≤ n / 2 by omega, hcond.2.2.1⟩ with ht
      have htmem := F.coveringTriangle_mem
        (q := (q.1 - 1, q.2)) ⟨show q.1 - 1 + 1 ≤ n / 2 by omega, hcond.2.2.1⟩
      have htcov := F.coveringTriangle_covers
        (q := (q.1 - 1, q.2)) ⟨show q.1 - 1 + 1 ≤ n / 2 by omega, hcond.2.2.1⟩
      have htcov' : ((q.1 - 1, q.2) : ℕ × ℤ) ∈ triangle t.1 t.2.1 t.2.2 := htcov
      have hsize : t.2.2 < (4 : ℝ) ^ A * (1 + ((p : ℝ) + 1)) ^ 3 := by
        have := hsmall (p + 1) hp1 t htmem (by rw [← hqpos]; exact htcov')
        push_cast at this ⊢
        linarith
      -- (7.11) extent: t.2.1 - q.2 ≤ t.2.2 / log 2 ≤ 2 t.2.2
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
      have hq2 : (q.2 : ℝ) = ((q₀.2 + (pathSum v (p + 1)).2 : ℤ) : ℝ) := by
        rw [hqpos]
        simp only [Prod.snd_add]
      have h4Ap : (0 : ℝ) ≤ (4 : ℝ) ^ A * (1 + ((p : ℝ) + 1)) ^ 3 := by positivity
      calc ((t.2.1 : ℤ) : ℝ) ≤ (q.2 : ℝ) + 2 * t.2.2 := htop
        _ ≤ (q.2 : ℝ) + 2 * ((4 : ℝ) ^ A * (1 + ((p : ℝ) + 1)) ^ 3) := by linarith
        _ = ((q₀.2 + (pathSum v (p + 1)).2 : ℤ) : ℝ)
            + 2 * (4 : ℝ) ^ A * (1 + ((p : ℝ) + 1)) ^ 3 := by rw [hq2]; ring
        _ ≤ _ := by
            push_cast
            linarith
    case isFalse hcond =>
      -- no encounter: barrier unchanged, envelope grows
      exact le_trans (IH hp) hgrow

open scoped Classical in
/-- **The (7.67) window step**: from any time `p` with room for one window
`W(p) = ⌈4^A(1+p)³⌉ + K + 2`, the fold's count strictly increases by the end of
the window — after `⌈4^A(1+p)³⌉ + 1` steps the height has cleared the barrier
envelope (heights rise ≥ 3/step), and among the following `K+1` positions at
least one is black (few whites), triggering an encounter. -/
theorem encFoldAt_count_step {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (q₀ : ℕ × ℤ) (hq₀ : 1 ≤ q₀.1) {T : ℕ} (v : Fin T → ℕ × ℤ)
    (hv : ∀ i, v i ∈ hold.support) (A : ℝ) (hA : 0 ≤ A) (K : ℕ)
    (hdepth : ∀ p, p ≤ T → (q₀ + pathSum v p).1 + g ≤ n / 2)
    (hsmall : ∀ p, p ≤ T → ∀ t ∈ F.T,
      ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ triangle t.1 t.2.1 t.2.2 →
      t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3)
    (hfew : (Finset.range T).sum
      (fun p => if q₀ + pathSum v (p + 1) ∈ whiteStrip n ξ then 1 else 0) ≤ K)
    {p : ℕ} (hp : p + (⌈(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌉₊ + K + 2) ≤ T) :
    (encFoldAt F R g q₀ v p).count + 1
      ≤ (encFoldAt F R g q₀ v (p + (⌈(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌉₊ + K + 2))).count := by
  set D : ℕ := ⌈(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌉₊ with hD
  set W : ℕ := D + K + 2 with hW
  by_contra hcon
  push Not at hcon
  -- the count is flat on the whole window
  have hflat : ∀ r, p ≤ r → r ≤ p + W →
      (encFoldAt F R g q₀ v r).count = (encFoldAt F R g q₀ v p).count := by
    intro r h1 h2
    have hmono1 := encFoldAt_count_mono F R g q₀ v h1 (by omega)
    have hmono2 := encFoldAt_count_mono F R g q₀ v h2 (by omega)
    omega
  -- hence the barrier is frozen at its time-p value
  have hbar : ∀ r, p ≤ r → r ≤ p + W →
      (encFoldAt F R g q₀ v r).barrier = (encFoldAt F R g q₀ v p).barrier := by
    intro r h1 h2
    exact encFoldAt_barrier_of_count_eq F R g q₀ v h1 (by omega) (hflat r h1 h2)
  -- the barrier envelope at time p
  have henv := encFoldAt_barrier_le F R g q₀ v hv A hA hsmall p (by omega)
  -- heights beyond p + D clear the barrier
  have hclear : ∀ r, p + D + 1 ≤ r → r ≤ p + W →
      (encFoldAt F R g q₀ v p).barrier < (q₀ + pathSum v r).2 := by
    intro r h1 h2
    have hht := pathSum_snd_ge v hv p (r - p) (by omega)
    rw [show p + (r - p) = r from by omega] at hht
    have hDge : ((4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3) ≤ (D : ℝ) :=
      Nat.le_ceil _
    have h4Apos : (0 : ℝ) ≤ (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := by positivity
    -- real comparison, then descend to ℤ
    have hstrict : (((encFoldAt F R g q₀ v p).barrier : ℤ) : ℝ)
        < (((q₀ + pathSum v r).2 : ℤ) : ℝ) := by
      have hrp : (D : ℝ) + 1 ≤ ((r - p : ℕ) : ℝ) := by
        have : D + 1 ≤ r - p := by omega
        exact_mod_cast this
      have hht' : ((pathSum v p).2 : ℝ) + 3 * ((r - p : ℕ) : ℝ)
          ≤ ((pathSum v r).2 : ℝ) := by exact_mod_cast hht
      have hh2 : ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 3 * ((r - p : ℕ) : ℝ)
          ≤ (((q₀ + pathSum v r).2 : ℤ) : ℝ) := by
        have hr2 : (q₀ + pathSum v r).2 = q₀.2 + (pathSum v r).2 := rfl
        rw [hr2]
        push_cast
        linarith
      calc (((encFoldAt F R g q₀ v p).barrier : ℤ) : ℝ)
          ≤ ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ)
            + 2 * (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := henv
        _ < ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 3 * ((D : ℝ) + 1) := by nlinarith
        _ ≤ ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 3 * ((r - p : ℕ) : ℝ) := by linarith
        _ ≤ _ := hh2
    exact_mod_cast hstrict
  -- among the K+1 window positions p+D+1 .. p+D+K+1 one is non-white
  have hpigeon : ∃ r, p + D + 1 ≤ r ∧ r ≤ p + D + K + 1 ∧
      q₀ + pathSum v r ∉ whiteStrip n ξ := by
    by_contra hall
    push Not at hall
    -- all K+1 positions white ⇒ the total white count exceeds K
    have hone : ∀ i ∈ Finset.range (K + 1),
        (if q₀ + pathSum v (p + D + i + 1) ∈ whiteStrip n ξ then 1 else 0) = 1 := by
      intro i hi
      simp only [Finset.mem_range] at hi
      exact if_pos (hall (p + D + i + 1) (by omega) (by omega))
    have hsub : (Finset.range (K + 1)).sum
        (fun i => if q₀ + pathSum v (p + D + i + 1) ∈ whiteStrip n ξ then 1 else 0)
        = K + 1 := by
      rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_range]
    have hinj : (Finset.range (K + 1)).sum
        (fun i => if q₀ + pathSum v (p + D + i + 1) ∈ whiteStrip n ξ then 1 else 0)
        ≤ (Finset.range T).sum
          (fun r => if q₀ + pathSum v (r + 1) ∈ whiteStrip n ξ then 1 else 0) := by
      have hmap : (Finset.range (K + 1)).sum
          (fun i => if q₀ + pathSum v (p + D + i + 1) ∈ whiteStrip n ξ then 1 else 0)
          = ((Finset.range (K + 1)).image (fun i => p + D + i)).sum
            (fun r => if q₀ + pathSum v (r + 1) ∈ whiteStrip n ξ then 1 else 0) := by
        rw [Finset.sum_image (by intro a _ b _ h; simp only [] at h; omega)]
      rw [hmap]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro r hr
      simp only [Finset.mem_image, Finset.mem_range] at hr ⊢
      obtain ⟨i, hi, rfl⟩ := hr
      show p + D + i < T
      omega
    omega
  obtain ⟨r, hr1, hr2, hrblack⟩ := hpigeon
  -- position r is deep, in-strip, black, above the frozen barrier: encounter
  have hr0 : 1 ≤ r := by omega
  have hrT : r ≤ T := by omega
  have hcol : 1 ≤ (q₀ + pathSum v r).1 := by
    show 1 ≤ q₀.1 + (pathSum v r).1
    omega
  have hdeep := hdepth r hrT
  have hblack : black n ξ ((q₀ + pathSum v r).1 - 1) (q₀ + pathSum v r).2 :=
    black_of_notMem_whiteStrip hcol (by omega) hrblack
  have hbarrier : (encFoldAt F R g q₀ v (r - 1)).barrier < (q₀ + pathSum v r).2 := by
    rw [hbar (r - 1) (by omega) (by omega)]
    exact hclear r (by omega) (by omega)
  -- the encounter fires at step r
  have hrstep : r - 1 < T := by omega
  have hposr : (encFoldAt F R g q₀ v (r - 1)).pos + v ⟨r - 1, hrstep⟩
      = q₀ + pathSum v r := by
    rw [encFoldAt_pos, add_assoc]
    congr 1
    rw [← pathSum_succ_of_lt v hrstep]
    congr 1
    omega
  have hcount : (encFoldAt F R g q₀ v r).count
      = (encFoldAt F R g q₀ v (r - 1)).count + 1 := by
    have hstep : encFoldAt F R g q₀ v r
        = encStep F R g (encFoldAt F R g q₀ v (r - 1)) (v ⟨r - 1, hrstep⟩) := by
      rw [← encFoldAt_succ F R g q₀ v hrstep]
      congr 1
      omega
    rw [hstep, encStep]
    rw [dif_pos (by
      rw [hposr]
      exact ⟨hcol, hdeep, hblack, hbarrier⟩)]
  have hflat1 := hflat (r - 1) (by omega) (by omega)
  have hflat2 := hflat r (by omega) (by omega)
  omega

/-- The (7.67) window-length iterate: `encWindowIter A K i` is an upper bound on
the time needed for the fold's count to reach `i` — each window costs
`⌈4^A(1+p)³⌉ + K + 2` steps starting from its own left endpoint `p`. This is the
paper's `P = O_{A,ε,R}(1)` horizon threshold. -/
noncomputable def encWindowIter (A : ℝ) (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => encWindowIter A K i
      + (⌈(4 : ℝ) ^ A * (1 + (encWindowIter A K i : ℝ)) ^ 3⌉₊ + K + 2)

theorem encWindowIter_succ (A : ℝ) (K i : ℕ) :
    encWindowIter A K (i + 1) = encWindowIter A K i
      + (⌈(4 : ℝ) ^ A * (1 + (encWindowIter A K i : ℝ)) ^ 3⌉₊ + K + 2) := rfl

theorem encWindowIter_mono (A : ℝ) (K : ℕ) {i j : ℕ} (h : i ≤ j) :
    encWindowIter A K i ≤ encWindowIter A K j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simp
  | succ k IH =>
    rw [show i + (k + 1) = (i + k) + 1 from rfl, encWindowIter_succ]
    omega

open scoped Classical in
/-- **The deterministic claim (7.67)** (paper p.55): a path that (i) stays deep
in the strip, (ii) never meets a `≥ 4^A(1+p)³`-sized triangle at any time
`p ≤ T` (outside `E∗`), and (iii) visits at most `K` white-strip points, must
drive the encounter fold's count to `R` — small triangles are exited within
`O(4^A(1+p)³)` steps (heights rise ≥ 3 per step against the (7.11) extent
`l_Δ − l ≤ s_Δ/log 2`), and within any `K+1` consecutive in-strip steps a
non-white (= black, phase-shifted) point occurs, triggering a new encounter
(count increments at the first black point above the barrier). The horizon
threshold `P₀` is the `R`-fold iterate of `p ↦ p + ⌈2·4^A(1+p)³⌉ + K + 2`,
an `O_{A,ε,R}(1)` quantity.

OPEN (X11b — THE crux of the Case-3 assembly): pure fold combinatorics, no
probability. Proof plan: strengthen to an induction on the number of
encounters: define `p_i` = the time of the `i`-th encounter (fold count first
reaches `i`); show `p_{i+1} ≤ p_i + ⌈2·4^A(1+p_i)³⌉ + K + 2` while `p_i` is
within horizon, via (a) the barrier after encounter `i` is the top `l_Δ` of a
triangle of size `< 4^A(1+p_i)³` containing the position at `p_i`, so
`l_Δ − height(p_i) ≤ s_Δ/log 2 ≤ 2·4^A(1+p_i)³`; (b) heights strictly rise
(`hold_support_snd_ge`, ≥ 3/step), so after `⌈2·4^A(1+p_i)³/3⌉` steps the
barrier is cleared; (c) among the following `K+2` positions one is black
(≤ K whites total on the whole path, and every deep in-strip position is
white-or-black via `whiteSet`/`black` complementarity at the phase point);
(d) the first such position triggers `encStep`'s encounter branch (all four
conditions hold), incrementing the count.

**Explicit-threshold form** (exposes the concrete horizon witness `encWindowIter A K R`);
the `∃ P₀` version `deterministic_encounter_claim` delegates to this. X11d's
`few_white_mass_le` needs the explicit `P₀` so it can pick a *uniform* horizon `P`
(chosen before `∀ n ξ F`, since `encWindowIter A K R` depends only on `A, K, R`). -/
theorem deterministic_encounter_claim_at (n ξ : ℕ) (F : TriangleFamily n ξ)
    (g R K : ℕ) (A : ℝ) (hA : 1 ≤ A) (T : ℕ) (hT : encWindowIter A K R ≤ T)
    (q₀ : ℕ × ℤ) (hq₀ : 1 ≤ q₀.1) (v : Fin T → ℕ × ℤ) (hv : ∀ i, v i ∈ hold.support)
    (hdepth : ∀ p, p ≤ T → (q₀ + pathSum v p).1 + g ≤ n / 2)
    (hsmall : ∀ p, p ≤ T → ∀ t ∈ F.T,
        ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ triangle t.1 t.2.1 t.2.2 →
        t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3)
    (hfew : (Finset.range T).sum
        (fun p => if q₀ + pathSum v (p + 1) ∈ whiteStrip n ξ then 1 else 0) ≤ K) :
    R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count := by
  classical
  -- the iterated window bound reaches count i by time encWindowIter A K i
  have key : ∀ i, i ≤ R → i ≤ (encFoldAt F R g q₀ v (encWindowIter A K i)).count := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i IH =>
      intro hiR
      have hle : encWindowIter A K (i + 1) ≤ T :=
        le_trans (encWindowIter_mono A K hiR) hT
      have hstep := encFoldAt_count_step (F := F) (R := R) (g := g) q₀ hq₀ v hv A
        (by linarith) K hdepth hsmall hfew
        (p := encWindowIter A K i) (by rw [← encWindowIter_succ]; exact hle)
      rw [← encWindowIter_succ] at hstep
      exact le_trans (Nat.succ_le_succ (IH (by omega))) hstep
  have hmono := encFoldAt_count_mono F R g q₀ v hT (le_refl T)
  rw [encFoldAt_top] at hmono
  exact le_trans (key R (le_refl R)) hmono

open scoped Classical in
/-- The (7.67) deterministic-encounter claim, `∃ P₀` form (delegates to
`deterministic_encounter_claim_at` at the explicit witness `encWindowIter A K R`). -/
theorem deterministic_encounter_claim (n ξ : ℕ) (F : TriangleFamily n ξ)
    (g R K : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ P₀ : ℕ, ∀ T : ℕ, P₀ ≤ T → ∀ q₀ : ℕ × ℤ, 1 ≤ q₀.1 →
      ∀ v : Fin T → ℕ × ℤ, (∀ i, v i ∈ hold.support) →
      (∀ p, p ≤ T → (q₀ + pathSum v p).1 + g ≤ n / 2) →
      (∀ p, p ≤ T → ∀ t ∈ F.T,
        ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ triangle t.1 t.2.1 t.2.2 →
        t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3) →
      ((Finset.range T).sum
        (fun p => if q₀ + pathSum v (p + 1) ∈ whiteStrip n ξ then 1 else 0) ≤ K) →
      R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count :=
  ⟨encWindowIter A K R, fun T hT q₀ hq₀ v hv hdepth hsmall hfew =>
    deterministic_encounter_claim_at n ξ F g R K A hA T hT q₀ hq₀ v hv hdepth hsmall hfew⟩

/-! ### X11a analytic helpers — the two convergent series behind the E∗ union -/

/-- **Telescoping bound** `Σ_{p<T+1} 1/(1+p)² ≤ 2` — the convergent series that
tames the `1/s'` first-passage terms in the X11a E∗ union (since
`s' = ⌈4^A(1+p)³⌉ ≥ 4^A(1+p)³` makes `A²(1+p)/s' ≤ A²·4^{-A}(1+p)^{-2}`). Proved
by the sharper `≤ 2 − 1/(T+1)` induction with the step `1/(k+2)² ≤ 1/(k+1)−1/(k+2)`. -/
theorem sum_inv_sq_le_two (T : ℕ) :
    (Finset.range (T + 1)).sum (fun p => 1 / (1 + (p : ℝ)) ^ 2) ≤ 2 := by
  have h : ∀ N : ℕ, (Finset.range (N + 1)).sum (fun p => 1 / (1 + (p : ℝ)) ^ 2)
      ≤ 2 - 1 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => norm_num
    | succ k IH =>
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have hcast1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_range_succ, hcast1]
      have hterm : (1 : ℝ) / (1 + ((k : ℝ) + 1)) ^ 2 = 1 / ((k : ℝ) + 2) ^ 2 := by ring_nf
      have hrhs : (2 : ℝ) - 1 / (((k : ℝ) + 1) + 1) = 2 - 1 / ((k : ℝ) + 2) := by ring_nf
      rw [hterm, hrhs]
      have hkey : 1 / ((k : ℝ) + 2) ^ 2 + 1 / ((k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 1) := by
        rw [div_add_div _ _ (by positivity) (ne_of_gt hk2), div_le_div_iff₀ (by positivity) hk1]
        nlinarith [hk1, hk2]
      linarith [IH, hkey]
  have hbound := h T
  have : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
  linarith [hbound, this]

/-- **Geometric bound** `Σ_{p<T+1} r^{1+p} ≤ 2r` for `0 ≤ r ≤ 1/2` — the geometric
series that tames the `exp(−c·A²(1+p))` renewal-tail terms in the X11a E∗ union
(with `r = exp(−c·A²) ≤ 1/2` for `A ≥ A₀`). Partial sum `≤` the geometric tsum. -/
theorem sum_geom_pow_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (T : ℕ) :
    (Finset.range (T + 1)).sum (fun p => r ^ (1 + p)) ≤ 2 * r := by
  have hr1 : r < 1 := by linarith
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hsum : Summable (fun p : ℕ => r ^ p) := summable_geometric_of_lt_one hr0 hr1
  have hpartial : (Finset.range (T + 1)).sum (fun p => r ^ p) ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact hsum.sum_le_tsum _ (fun i _ => by positivity)
  have hfactor : (Finset.range (T + 1)).sum (fun p => r ^ (1 + p))
      = r * (Finset.range (T + 1)).sum (fun p => r ^ p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by rw [pow_add, pow_one])
  have hinvpos : (0 : ℝ) < (1 - r)⁻¹ := inv_pos.mpr h1r
  have hcancel : (1 - r) * (1 - r)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h1r)
  have hinv : (1 - r)⁻¹ ≤ 2 := by nlinarith [hcancel, h1r, hinvpos, hr]
  rw [hfactor]
  calc r * (Finset.range (T + 1)).sum (fun p => r ^ p)
      ≤ r * (1 - r)⁻¹ := by gcongr
    _ ≤ r * 2 := by gcongr
    _ = 2 * r := by ring

/-- **E∗ union constant** (X11a): `4·C_encTri`, from summing the per-`p` big-triangle
mass (factor 4 = 2·2 from the `1/s'`-telescope and geometric-tail `≤ 2` bounds).
Ladder-negligible (super-polynomial decay in `A`). -/
noncomputable def C_estarUnion : ℝ := 4 * C_encTri

theorem C_estarUnion_pos : 0 < C_estarUnion := by
  have := C_encTri_pos; unfold C_estarUnion; linarith

/-- **E∗ union rate**: inherits `c_encTri` (X10's exponential rate). -/
noncomputable def c_estarUnion : ℝ := c_encTri

theorem c_estarUnion_pos : 0 < c_estarUnion := c_encTri_pos

/-- **E∗ union threshold**: `max 5 √(log2 / c_encTri)` — the X10 threshold `5` joined with
the `r = exp(−c·A²) ≤ ½` regime `A ≥ √(log2/c)`. -/
noncomputable def A0_estarUnion : ℝ := max 5 (Real.sqrt (Real.log 2 / c_encTri))

theorem one_le_A0_estarUnion : 1 ≤ A0_estarUnion := by
  unfold A0_estarUnion; exact le_trans (by norm_num) (le_max_left _ _)

open scoped Classical in
/-- **X11a E∗ union bound `_core`**: the per-`p` `bigTriangle_walk` bound abstracted over
its constant `C` and rate `c` (as `hX10`), yielding `4·C·A²·4^{−A} + 4·C·exp(−c·A²)` for
`A ≥ max 5 √(log2/c)`. Body verbatim from the `∃`-form; `C`/`c` opaque so no def leaks into
`nlinarith`. -/
theorem estar_union_le_rpow_core (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hX10 : ∀ (A : ℝ), 5 ≤ A →
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ), (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (T p s' : ℕ), p ≤ T → 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
        (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
          Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ≥0∞)
            (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)).toReal
          ≤ C * A ^ 2 * (1 + (p : ℝ)) / (s' : ℝ)
            + C * Real.exp (-c * A ^ 2 * (1 + (p : ℝ)))) :
    ∀ (A : ℝ), max 5 (Real.sqrt (Real.log 2 / c)) ≤ A →
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ), (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (T : ℕ),
        (∀ p, p ≤ T →
          ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ)) →
        (Finset.range (T + 1)).sum (fun p =>
          (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
            Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊) (1 : ℕ × ℤ → ℝ≥0∞)
              (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)).toReal)
          ≤ 4 * C * A ^ 2 * (4 : ℝ) ^ (-A) + 4 * C * Real.exp (-c * A ^ 2) := by
  intro A hA n ξ hξ F t₀ ht₀ j l hmem s hs hdeep T hreg
  have hA0 : (5 : ℝ) ≤ A := le_trans (le_max_left _ _) hA
  have hA1 : (1 : ℝ) ≤ A := by linarith [hA0]
  have hAsqrt : Real.sqrt (Real.log 2 / c) ≤ A := le_trans (le_max_right _ _) hA
  -- r = exp(-c·A²) ≤ 1/2 for A ≥ sqrt(log 2 / c)
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
  have hCA2nn : (0 : ℝ) ≤ C * A ^ 2 * (4 : ℝ) ^ (-A) :=
    mul_nonneg (mul_nonneg hC.le (sq_nonneg A)) (Real.rpow_nonneg (by norm_num) _)
  -- 4 ≤ 4^A·(1+p)³ for A ≥ 1 (used for the floor lower bound and `1 ≤ s'`)
  have hxfour : ∀ p : ℕ, (4 : ℝ) ≤ (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := by
    intro p
    have h4A : (4 : ℝ) ≤ (4 : ℝ) ^ A := by
      calc (4 : ℝ) = (4 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 4).symm
        _ ≤ (4 : ℝ) ^ A := Real.rpow_le_rpow_of_exponent_le (by norm_num) hA1
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have h13 : (1 : ℝ) ≤ (1 + (p : ℝ)) ^ 3 := by
      nlinarith [hp0, mul_nonneg hp0 hp0, mul_nonneg (mul_nonneg hp0 hp0) hp0]
    nlinarith [h4A, h13]
  -- per-p bound from bigTriangle_walk_le (X10) at s' = ⌊4^A(1+p)³⌋
  have hbig : ∀ p ∈ Finset.range (T + 1),
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
        Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊) (1 : ℕ × ℤ → ℝ≥0∞)
          (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)).toReal
        ≤ C * A ^ 2 * (1 + (p : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
          + C * Real.exp (-c * A ^ 2 * (1 + (p : ℝ))) := by
    intro p hp
    have hpT : p ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    have h1s' : 1 ≤ ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ := by
      apply Nat.le_floor
      push_cast
      linarith [hxfour p]
    exact hX10 A hA0 n ξ hξ F t₀ ht₀ j l hmem s hs hdeep T p _ hpT h1s' (hreg p hpT)
  refine le_trans (Finset.sum_le_sum hbig) ?_
  rw [Finset.sum_add_distrib]
  apply add_le_add
  · -- polynomial (first-passage) terms
    have hpoly : ∀ p ∈ Finset.range (T + 1),
        C * A ^ 2 * (1 + (p : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
          ≤ 2 * C * A ^ 2 * (4 : ℝ) ^ (-A) * (1 / (1 + (p : ℝ)) ^ 2) := by
      intro p _
      have hq : (0 : ℝ) < 1 + (p : ℝ) := by positivity
      have hPpos : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
      have hx4 : (4 : ℝ) ≤ (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := hxfour p
      -- floor lower bound: ½·x ≤ ⌊x⌋ (since x ≥ 4 ⟹ x/2 ≤ x−1 < ⌊x⌋)
      have hfloor : (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 / 2
          ≤ ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) := by
        have hlt := Nat.lt_floor_add_one ((4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3)
        linarith [hlt, hx4]
      have step1 : (1 + (p : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
          ≤ (1 + (p : ℝ)) / ((4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 / 2) := by
        gcongr
      have step2 : (1 + (p : ℝ)) / ((4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 / 2)
          = 2 * (4 : ℝ) ^ (-A) * (1 / (1 + (p : ℝ)) ^ 2) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
        have hPne : (4 : ℝ) ^ A ≠ 0 := ne_of_gt hPpos
        have hqne : (1 + (p : ℝ)) ≠ 0 := ne_of_gt hq
        field_simp
      calc C * A ^ 2 * (1 + (p : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
          = C * A ^ 2 * ((1 + (p : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)) := by
            ring
        _ ≤ C * A ^ 2 * ((1 + (p : ℝ)) / ((4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 / 2)) :=
            mul_le_mul_of_nonneg_left step1 (mul_nonneg hC.le (sq_nonneg A))
        _ = C * A ^ 2 * (2 * (4 : ℝ) ^ (-A) * (1 / (1 + (p : ℝ)) ^ 2)) := by rw [step2]
        _ = 2 * C * A ^ 2 * (4 : ℝ) ^ (-A) * (1 / (1 + (p : ℝ)) ^ 2) := by ring
    calc (Finset.range (T + 1)).sum (fun p =>
            C * A ^ 2 * (1 + (p : ℝ)) / ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ))
        ≤ (Finset.range (T + 1)).sum (fun p =>
            2 * C * A ^ 2 * (4 : ℝ) ^ (-A) * (1 / (1 + (p : ℝ)) ^ 2)) := Finset.sum_le_sum hpoly
      _ = 2 * C * A ^ 2 * (4 : ℝ) ^ (-A)
            * (Finset.range (T + 1)).sum (fun p => 1 / (1 + (p : ℝ)) ^ 2) := by
          rw [← Finset.mul_sum]
      _ ≤ 2 * C * A ^ 2 * (4 : ℝ) ^ (-A) * 2 :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_le_two T)
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.le) (sq_nonneg A))
              (Real.rpow_nonneg (by norm_num) _))
      _ = 4 * C * A ^ 2 * (4 : ℝ) ^ (-A) := by ring
  · -- renewal-tail (geometric) terms
    have hexp : ∀ p ∈ Finset.range (T + 1),
        C * Real.exp (-c * A ^ 2 * (1 + (p : ℝ)))
          = C * Real.exp (-c * A ^ 2) ^ (1 + p) := by
      intro p _
      have h : Real.exp (-c * A ^ 2 * (1 + (p : ℝ))) = Real.exp (-c * A ^ 2) ^ (1 + p) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast; ring
      rw [h]
    calc (Finset.range (T + 1)).sum (fun p => C * Real.exp (-c * A ^ 2 * (1 + (p : ℝ))))
        = (Finset.range (T + 1)).sum (fun p => C * Real.exp (-c * A ^ 2) ^ (1 + p)) :=
          Finset.sum_congr rfl hexp
      _ = C * (Finset.range (T + 1)).sum (fun p => Real.exp (-c * A ^ 2) ^ (1 + p)) := by
          rw [← Finset.mul_sum]
      _ ≤ C * (2 * Real.exp (-c * A ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (sum_geom_pow_le (Real.exp (-c * A ^ 2)) (le_of_lt (Real.exp_pos _)) hr T) hC.le
      _ ≤ 4 * C * Real.exp (-c * A ^ 2) := by nlinarith [hC.le, Real.exp_pos (-c * A ^ 2)]

open scoped Classical in
/-- **X11a E∗ union bound**, `_explicitC` sibling at `C_estarUnion`/`c_estarUnion`,
`A₀ = A0_estarUnion`. Delegates to `estar_union_le_rpow_core` at `C_encTri`/`c_encTri`
over `bigTriangle_walk_le_rpow_explicitC`. -/
theorem estar_union_le_rpow_explicitC :
    ∀ (A : ℝ), A0_estarUnion ≤ A →
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ), (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (T : ℕ),
        (∀ p, p ≤ T →
          ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ)) →
        (Finset.range (T + 1)).sum (fun p =>
          (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
            Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊) (1 : ℕ × ℤ → ℝ≥0∞)
              (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)).toReal)
          ≤ C_estarUnion * A ^ 2 * (4 : ℝ) ^ (-A) + C_estarUnion * Real.exp (-c_estarUnion * A ^ 2) := by
  have h := estar_union_le_rpow_core C_encTri c_encTri C_encTri_pos c_encTri_pos
    bigTriangle_walk_le_rpow_explicitC
  unfold C_estarUnion c_estarUnion A0_estarUnion
  exact h

open scoped Classical in
/-- **X11a: the E∗ union bound** (paper (7.54)–(7.56)): summing the per-`p`
`bigTriangle_walk_le` mass over the horizon `p ∈ range(T+1)` at
`s' = ⌊4^A(1+p)³⌋`, the total big-triangle (E∗) mass is
`≤ C'·A²·4^{-A} + C'·exp(−c·A²)`. **FLOOR** (not ceil) so `s' ≤ 4^A(1+p)³ ≤ t.2.2`:
this is what makes `bigTriangleSet F s'` CONTAIN the geometry-join E∗ event (whose
threshold is the real `4^A(1+p)³`), see `deterministic_encounter_or_bigTriangle`. The
`1/s'` first-passage terms telescope (`sum_inv_sq_le_two`, using `s' = ⌊4^A(1+p)³⌋ ≥
½·4^A(1+p)³` so `A²(1+p)/s' ≤ 2·A²·4^{-A}(1+p)^{-2}`); the renewal-tail `exp(−c·A²(1+p))`
terms sum geometrically (`sum_geom_pow_le`, `r = exp(−c·A²) ≤ 1/2` for `A ≥ A₀`). Both
decay super-polynomially, so E∗ is negligible in the X11d damping assembly. -/
theorem estar_union_le_rpow :
    ∃ C' > (0 : ℝ), ∃ c > (0 : ℝ), ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (A : ℝ), A₀ ≤ A →
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ), (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) →
      ∀ (T : ℕ),
        (∀ p, p ≤ T →
          ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ)) →
        (Finset.range (T + 1)).sum (fun p =>
          (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin T → ℕ × ℤ, hold.iid T v *
            Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊) (1 : ℕ × ℤ → ℝ≥0∞)
              (j + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)).toReal)
          ≤ C' * A ^ 2 * (4 : ℝ) ^ (-A) + C' * Real.exp (-c * A ^ 2) :=
  ⟨C_estarUnion, C_estarUnion_pos, c_estarUnion, c_estarUnion_pos, A0_estarUnion,
    one_le_A0_estarUnion, estar_union_le_rpow_explicitC⟩

/-! ### X11c ingredients — the reaches-`R` / few-white → F∗ join -/

/-- **The `encVal` lower bound on the reaches-`R` few-white event** (paper (7.57)):
if the fold reaches `R` encounters (`R ≤ count`) with few whites (`cumWhite ≤ K`),
then the (7.57) integrand `encVal ε R = exp(−banked + ε·min(count,R))` is
`≥ exp(−K + ε·R)`, since `banked ≤ cumWhite ≤ K` (`encFold_banked_le`, banking freezes
a past white count) and `min(count,R) = R`. This is the containment `{reaches R} ∩
{few white} ⊆ F∗ = {encVal ≥ e^{−K+εR}}` that `fstar_markov` bounds. -/
theorem encVal_ge_of_reaches {n ξ : ℕ} (F : TriangleFamily n ξ) (R g K : ℕ) (ε : ℝ)
    (q₀ : ℕ × ℤ) (L : List (ℕ × ℤ))
    (hreach : R ≤ (L.foldl (encStep F R g) (encInit q₀.1 q₀.2)).count)
    (hwhite : (L.foldl (encStep F R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K) :
    Real.exp (-(K : ℝ) + ε * R)
      ≤ encVal ε R (L.foldl (encStep F R g) (encInit q₀.1 q₀.2)) := by
  set σ := L.foldl (encStep F R g) (encInit q₀.1 q₀.2) with hσ
  rw [encVal]
  apply Real.exp_le_exp.mpr
  have hbank : σ.banked ≤ σ.cumWhite := by
    rw [hσ]; exact encFold_banked_le F R g L (encInit q₀.1 q₀.2) (by simp [encInit])
  have hbk : (σ.banked : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_trans hbank hwhite
  have hmin : min σ.count R = R := min_eq_right hreach
  rw [hmin]
  linarith [hbk]

open scoped Classical in
/-- **The reaches-`R` few-white mass bound** (paper (7.56), the Markov join):
the joint-walk mass of the event {fold reaches `R` encounters ∧ ≤ `K` whites} is
`≤ e^{2ε}/e^{−K+εR}`. Since that event is contained in `F∗ = {encVal ≥ e^{−K+εR}}`
(`encVal_ge_of_reaches`), the bound is `fstar_markov` at `lam = e^{−K+εR}`. The X11d
choice `R := ⌈(K+(A+3)log10+2)/ε⌉` makes the RHS `≤ 10^{−A−1}`. -/
theorem reaches_fewWhite_mass_le_core (ε₀ : ℝ) (g : ℕ)
    (hmark : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (lam : ℝ), 0 < lam →
        ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
          (if lam ≤ encVal ε R ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2))
            then (1 : ℝ) else 0)
        ≤ Real.exp (2 * ε) / lam) :
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (K : ℕ),
        ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
          (if R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count
              ∧ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K
            then (1 : ℝ) else 0)
          ≤ Real.exp (2 * ε) / Real.exp (-(K : ℝ) + ε * R) := by
  intro ε hεpos hεle n ξ hξ F R hR T q₀ K
  have hlam : (0 : ℝ) < Real.exp (-(K : ℝ) + ε * R) := Real.exp_pos _
  have hsum : Summable (fun v : Fin T → ℕ × ℤ => (hold.iid T v).toReal) :=
    ENNReal.summable_toReal (by rw [(hold.iid T).tsum_coe]; exact ENNReal.one_ne_top)
  -- termwise: {reaches R ∧ few white} indicator ≤ {lam ≤ encVal} indicator
  have hle : ∀ v : Fin T → ℕ × ℤ,
      (hold.iid T v).toReal *
        (if R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count
            ∧ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K
          then (1 : ℝ) else 0)
        ≤ (hold.iid T v).toReal *
          (if Real.exp (-(K : ℝ) + ε * R)
              ≤ encVal ε R ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2))
            then (1 : ℝ) else 0) := by
    intro v
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    by_cases hev : R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count
        ∧ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K
    · rw [if_pos hev]
      split_ifs with henc
      · exact le_refl 1
      · exact absurd (encVal_ge_of_reaches F R g K ε q₀ (List.ofFn v) hev.1 hev.2) henc
    · rw [if_neg hev]; positivity
  -- both series dominated by the PMF mass, hence summable
  have hbound : ∀ v : Fin T → ℕ × ℤ,
      (hold.iid T v).toReal *
        (if Real.exp (-(K : ℝ) + ε * R)
            ≤ encVal ε R ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2))
          then (1 : ℝ) else 0) ≤ (hold.iid T v).toReal := by
    intro v
    calc (hold.iid T v).toReal * (if Real.exp (-(K : ℝ) + ε * R)
            ≤ encVal ε R ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2))
          then (1 : ℝ) else 0)
        ≤ (hold.iid T v).toReal * 1 := by
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          split_ifs <;> norm_num
      _ = (hold.iid T v).toReal := mul_one _
  have hsumR : Summable (fun v : Fin T → ℕ × ℤ => (hold.iid T v).toReal *
      (if Real.exp (-(K : ℝ) + ε * R)
          ≤ encVal ε R ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2))
        then (1 : ℝ) else 0)) :=
    Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (by positivity)) hbound hsum
  have hsumL : Summable (fun v : Fin T → ℕ × ℤ => (hold.iid T v).toReal *
      (if R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count
          ∧ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K
        then (1 : ℝ) else 0)) :=
    Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (by positivity))
      (fun v => le_trans (hle v) (hbound v)) hsum
  exact le_trans (Summable.tsum_le_tsum hle hsumL hsumR)
    (hmark ε hεpos hεle n ξ hξ F R hR T q₀ (Real.exp (-(K : ℝ) + ε * R)) hlam)

/-- `reaches_fewWhite_mass_le`, `_at` sibling at `eps0_manyTri`/`g_manyTri`. -/
theorem reaches_fewWhite_mass_le_at :
    ∀ ε : ℝ, 0 < ε → ε ≤ eps0_manyTri →
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (K : ℕ),
        ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
          (if R ≤ ((List.ofFn v).foldl (encStep F R g_manyTri)
                (encInit q₀.1 q₀.2)).count
              ∧ ((List.ofFn v).foldl (encStep F R g_manyTri)
                (encInit q₀.1 q₀.2)).cumWhite ≤ K
            then (1 : ℝ) else 0)
          ≤ Real.exp (2 * ε) / Real.exp (-(K : ℝ) + ε * R) :=
  reaches_fewWhite_mass_le_core eps0_manyTri g_manyTri fstar_markov_at

/-- `reaches_fewWhite_mass_le`, original `∃`-form: delegates to the `_at`
sibling. -/
theorem reaches_fewWhite_mass_le :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 100 ∧ ∃ g : ℕ,
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (K : ℕ),
        ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
          (if R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count
              ∧ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K
            then (1 : ℝ) else 0)
          ≤ Real.exp (2 * ε) / Real.exp (-(K : ℝ) + ε * R) :=
  ⟨eps0_manyTri, eps0_manyTri_pos, eps0_manyTri_le, g_manyTri,
    reaches_fewWhite_mass_le_at⟩

/-- **The (7.56) numerical closure**: with the X11d block count
`R := ⌈(K+(A+3)log10+2)/ε⌉` (encoded as the hypothesis `εR ≥ K+(A+3)log10+2`), the
Markov ratio `e^{2ε}/e^{−K+εR} ≤ 10^{−(A+1)}`. Uses `e^a/e^b = e^{a−b}` and
`10^x = e^{x·log10}`; the slack `2ε−2 ≤ 0 ≤ 2log10` (from `ε ≤ 1`) absorbs the `e^{2ε}`. -/
theorem fewWhite_num_closure (A ε : ℝ) (hε1 : ε ≤ 1) (K R : ℕ)
    (hRbound : (K : ℝ) + (A + 3) * Real.log 10 + 2 ≤ ε * R) :
    Real.exp (2 * ε) / Real.exp (-(K : ℝ) + ε * R) ≤ (10 : ℝ) ^ (-(A + 1)) := by
  rw [← Real.exp_sub]
  have hlog : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num)
  have h1 : (A + 3) * Real.log 10 = (A + 1) * Real.log 10 + 2 * Real.log 10 := by ring
  have hstep : 2 * ε - (-(K : ℝ) + ε * R) ≤ -(A + 1) * Real.log 10 := by
    nlinarith [hRbound, hε1, hlog, h1]
  calc Real.exp (2 * ε - (-(K : ℝ) + ε * R))
      ≤ Real.exp (-(A + 1) * Real.log 10) := Real.exp_le_exp.mpr hstep
    _ = (10 : ℝ) ^ (-(A + 1)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
        congr 1; ring

open scoped Classical in
/-- **The full (7.56) reaches-`R`/few-white bound**: with `R := ⌈(K+(A+3)log10+2)/ε⌉`
(as `εR ≥ K+(A+3)log10+2`), the joint-walk mass of {fold reaches `R` ∧ ≤ `K` whites}
is `≤ 10^{−(A+1)}`. Composes `reaches_fewWhite_mass_le` (the Markov join) with
`fewWhite_num_closure` (the numerical `R`-choice). This is the F∗ term X11d subtracts
from the (7.56) white-count split. -/
theorem reaches_fewWhite_mass_le_ten_at :
    ∀ ε : ℝ, 0 < ε → ε ≤ eps0_manyTri → ∀ A : ℝ,
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (K : ℕ),
        (K : ℝ) + (A + 3) * Real.log 10 + 2 ≤ ε * R →
        ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
          (if R ≤ ((List.ofFn v).foldl (encStep F R g_manyTri)
                (encInit q₀.1 q₀.2)).count
              ∧ ((List.ofFn v).foldl (encStep F R g_manyTri)
                (encInit q₀.1 q₀.2)).cumWhite ≤ K
            then (1 : ℝ) else 0)
          ≤ (10 : ℝ) ^ (-(A + 1)) := by
  intro ε hεpos hεle A n ξ hξ F R hR T q₀ K hRbound
  exact le_trans (reaches_fewWhite_mass_le_at ε hεpos hεle n ξ hξ F R hR T q₀ K)
    (fewWhite_num_closure A ε (by linarith [hεle, eps0_manyTri_le]) K R hRbound)

/-- `reaches_fewWhite_mass_le_ten`, original `∃`-form: delegates to the `_at`
sibling. -/
theorem reaches_fewWhite_mass_le_ten :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 100 ∧ ∃ g : ℕ,
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ,
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (q₀ : ℕ × ℤ) (K : ℕ),
        (K : ℝ) + (A + 3) * Real.log 10 + 2 ≤ ε * R →
        ∑' v : Fin T → ℕ × ℤ, (hold.iid T v).toReal *
          (if R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count
              ∧ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K
            then (1 : ℝ) else 0)
          ≤ (10 : ℝ) ^ (-(A + 1)) :=
  ⟨eps0_manyTri, eps0_manyTri_pos, eps0_manyTri_le, g_manyTri,
    reaches_fewWhite_mass_le_ten_at⟩

open scoped Classical in
/-- **The X11c geometry join** (contrapositive of `deterministic_encounter_claim`):
for a deep in-strip few-white path, EITHER the fold reaches `R` encounters OR the path
hits a big triangle (E∗) — i.e. at some `p ≤ T` the phase point `((pos p).1−1, (pos p).2)`
lies in a family triangle of size `≥ 4^A(1+p)³`. This is the pointwise dichotomy the X11d
white-count split rides on: {few white} ⊆ {reach R} ∪ {E∗}, given depth. The `∨`'s right
disjunct is what `estar_union_le` bounds (up to X11d's phase/ceil reconciliation). -/
theorem deterministic_encounter_or_bigTriangle {n ξ : ℕ} (F : TriangleFamily n ξ)
    (g R K : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ P₀ : ℕ, ∀ T : ℕ, P₀ ≤ T → ∀ q₀ : ℕ × ℤ, 1 ≤ q₀.1 →
      ∀ v : Fin T → ℕ × ℤ, (∀ i, v i ∈ hold.support) →
      (∀ p, p ≤ T → (q₀ + pathSum v p).1 + g ≤ n / 2) →
      ((Finset.range T).sum
        (fun p => if q₀ + pathSum v (p + 1) ∈ whiteStrip n ξ then 1 else 0) ≤ K) →
      R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count
      ∨ (∃ p, p ≤ T ∧ ∃ t ∈ F.T,
          ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ triangle t.1 t.2.1 t.2.2
          ∧ (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 ≤ t.2.2) := by
  obtain ⟨P₀, hP₀⟩ := deterministic_encounter_claim n ξ F g R K A hA
  refine ⟨P₀, ?_⟩
  intro T hT q₀ hq₀ v hv hdepth hfew
  by_cases hE : ∀ p, p ≤ T → ∀ t ∈ F.T,
      ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ triangle t.1 t.2.1 t.2.2 →
      t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3
  · exact Or.inl (hP₀ T hT q₀ hq₀ v hv hdepth hE hfew)
  · refine Or.inr ?_
    push Not at hE
    obtain ⟨p, hp, t, ht, hmem, hbig⟩ := hE
    exact ⟨p, hp, t, ht, hmem, hbig⟩

/-- **E∗ containment** (the floor bridge): a point in a family triangle of real size
`≥ 4^A(1+p)³` lies in `bigTriangleSet F ⌊4^A(1+p)³⌋` — because `⌊x⌋ ≤ x ≤ t.2.2`. This
turns the `deterministic_encounter_or_bigTriangle` right disjunct (real threshold, phase
point) into a `bigTriangleSet` membership that `estar_union_le` bounds; the phase −1 shift
is handled by X11d instantiating `estar_union_le` at `j−1`. -/
theorem bigTriangle_of_encounter {n ξ : ℕ} (F : TriangleFamily n ξ) (A : ℝ) (p : ℕ)
    (q : ℕ × ℤ) (t : ℕ × ℤ × ℝ) (ht : t ∈ F.T) (hmem : q ∈ triangle t.1 t.2.1 t.2.2)
    (hbig : (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 ≤ t.2.2) :
    q ∈ bigTriangleSet F ⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ := by
  refine ⟨t, ht, ?_, hmem⟩
  calc ((⌊(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
      ≤ (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := Nat.floor_le (by positivity)
    _ ≤ t.2.2 := hbig

open scoped Classical in
/-- **The pointwise dichotomy for the (7.56) white-count split** (the index-shift
reconciliation). For a deep in-strip walk whose *`P`-step forward* white count
`myNw := Σ_{p<P} 1_{q₀+pathSum v p ∈ whiteStrip}` is `≤ K`, EITHER the encounter fold
reaches `R` (with its running white count `cumWhite ≤ K+1`) OR the path hits a big
triangle (E∗). The `+1` slack absorbs the shift between `myNw` (positions `pathSum 0..P−1`,
including the start `q₀`) and the fold's `cumWhite = Σ_{p<P} 1_{q₀+pathSum v (p+1)∈whiteStrip}`
(positions `pathSum 1..P`, `encFold_cumWhite`): the two counts differ only in the boundary
terms `1_{q₀∈WS}` (dropped) and `1_{q₀+pathSum P∈WS}` (added), so `cumWhite ≤ myNw + 1`. This
is exactly the reconciliation X11d's `few_white_mass_le` needs to feed
`reaches_fewWhite_mass_le_ten` (`cumWhite ≤ K+1`) and `estar_union_le` (the E∗ branch).
Stated at the **explicit uniform horizon** `encWindowIter A (K+1) R ≤ P` (not `∃ P₀`) so
`few_white_mass_le` can fix one `P` before `∀ n ξ F`. -/
theorem few_white_pointwise_dichotomy {n ξ : ℕ} (F : TriangleFamily n ξ)
    (g R K : ℕ) (A : ℝ) (hA : 1 ≤ A) (P : ℕ) (hP : encWindowIter A (K + 1) R ≤ P)
    (q₀ : ℕ × ℤ) (hq₀ : 1 ≤ q₀.1) (v : Fin P → ℕ × ℤ) (hv : ∀ i, v i ∈ hold.support)
    (hdepth : ∀ p, p ≤ P → (q₀ + pathSum v p).1 + g ≤ n / 2)
    (hmyNw : (∑ p ∈ Finset.range P,
        (if q₀ + pathSum v p ∈ whiteStrip n ξ then (1 : ℕ) else 0)) ≤ K) :
    (R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count
        ∧ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K + 1)
    ∨ (∃ p, p ≤ P ∧ ∃ t ∈ F.T,
        ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ triangle t.1 t.2.1 t.2.2
        ∧ (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 ≤ t.2.2) := by
  classical
  -- `cumWhite = Σ_{p<P} 1_{q₀+pathSum v (p+1)∈whiteStrip}` (start count 0, position `q₀`).
  have hpos : (encInit q₀.1 q₀.2).pos = q₀ := rfl
  have hcum : ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).cumWhite
      = ∑ p ∈ Finset.range P,
          (if q₀ + pathSum v (p + 1) ∈ whiteStrip n ξ then (1 : ℕ) else 0) := by
    rw [encFold_cumWhite F R g P v (encInit q₀.1 q₀.2), hpos]
    simp only [encInit, zero_add]
  -- The `S_P ≤ myNw + 1` count reconciliation via the two range-succ splits.
  have hSple : (∑ p ∈ Finset.range P,
      (if q₀ + pathSum v (p + 1) ∈ whiteStrip n ξ then (1 : ℕ) else 0)) ≤ K + 1 := by
    have e1 : (∑ p ∈ Finset.range (P + 1),
          (if q₀ + pathSum v p ∈ whiteStrip n ξ then (1 : ℕ) else 0))
        = (∑ p ∈ Finset.range P,
            (if q₀ + pathSum v (p + 1) ∈ whiteStrip n ξ then (1 : ℕ) else 0))
          + (if q₀ + pathSum v 0 ∈ whiteStrip n ξ then (1 : ℕ) else 0) :=
      Finset.sum_range_succ' _ P
    have e2 : (∑ p ∈ Finset.range (P + 1),
          (if q₀ + pathSum v p ∈ whiteStrip n ξ then (1 : ℕ) else 0))
        = (∑ p ∈ Finset.range P,
            (if q₀ + pathSum v p ∈ whiteStrip n ξ then (1 : ℕ) else 0))
          + (if q₀ + pathSum v P ∈ whiteStrip n ξ then (1 : ℕ) else 0) :=
      Finset.sum_range_succ _ P
    have hb : (if q₀ + pathSum v P ∈ whiteStrip n ξ then (1 : ℕ) else 0) ≤ 1 := by
      split_ifs <;> omega
    omega
  have hcumK : ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K + 1 := by
    rw [hcum]; exact hSple
  -- Dichotomy: either all covering triangles are small (⟹ reach `R`) or one is big (E∗).
  by_cases hE : ∀ p, p ≤ P → ∀ t ∈ F.T,
      ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ triangle t.1 t.2.1 t.2.2 →
      t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3
  · exact Or.inl ⟨deterministic_encounter_claim_at n ξ F g R (K + 1) A hA P hP q₀ hq₀ v hv
      hdepth hE hSple, hcumK⟩
  · refine Or.inr ?_
    push Not at hE
    obtain ⟨p, hp, t, ht, hmem, hbig⟩ := hE
    exact ⟨p, hp, t, ht, hmem, hbig⟩

open scoped Classical in
/-- **The pointwise THREE-way split for (7.56)** (the assembly glue). For a fixed
first-passage displacement `e` and walk `v`, the few-white indicator `1_{myNw≤K}` is
dominated by the sum of three indicators: the **reach-`R`** event (fold reaches `R` with
`cumWhite ≤ K+1`), the **E∗** union `Σ_{p≤P} 1_{phase pt ∈ bigTriangleSet ⌊4^{A'}(1+p)³⌋}`,
and the **bad-column** event `{0.9m ≤ e.1+(pathSum v P).1}`. Proof by cases on `myNw>K`
(⟹ LHS 0), then the bad column (⟹ third term 1), then on the good column the depth holds
(`pathSum_depth_le`, `adv+g<m` from `adv<0.9m` and `g≤0.1m`) so
`few_white_pointwise_dichotomy` gives reach (first term 1) or E∗
(`bigTriangle_of_encounter` ⟹ one middle summand 1). This is exactly the pointwise bound
`few_white_mass_le` integrates, its three terms bounded by `reaches_fewWhite_mass_le_ten`,
`estar_union_le`, and `col_tail`. -/
theorem few_white_pointwise_split {n ξ : ℕ} (F : TriangleFamily n ξ)
    (m : ℕ) (hmn : m ≤ n / 2) (hpos : 1 ≤ n / 2 - m) (l : ℤ)
    (g R K : ℕ) (A' : ℝ) (hA' : 1 ≤ A') (P : ℕ) (hP : encWindowIter A' (K + 1) R ≤ P)
    (hg : (g : ℝ) ≤ (1 / 10 : ℝ) * (m : ℝ))
    (e : ℕ × ℤ) (v : Fin P → ℕ × ℤ) (hv : ∀ i, v i ∈ hold.support) :
    ENNReal.ofReal (if (∑ p ∈ Finset.range P,
          Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
            (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
        ≤ (K : ℝ)
      then (1 : ℝ) else 0)
    ≤ ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F R g)
            (encInit (n / 2 - m + e.1) (l + e.2))).count
          ∧ ((List.ofFn v).foldl (encStep F R g)
            (encInit (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
        then (1 : ℝ) else 0)
      + (∑ p ∈ Finset.range (P + 1),
          Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
      + ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
          then (1 : ℝ) else 0) := by
  classical
  set q₀ : ℕ × ℤ := (n / 2 - m + e.1, l + e.2) with hq₀def
  have hq1 : q₀.1 = n / 2 - m + e.1 := rfl
  set Nw : ℝ := ∑ p ∈ Finset.range P,
      Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
        (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) with hNwdef
  set T1 : ℝ≥0∞ := ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F R g)
        (encInit (n / 2 - m + e.1) (l + e.2))).count
      ∧ ((List.ofFn v).foldl (encStep F R g)
        (encInit (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1 then (1 : ℝ) else 0) with hT1def
  set T2 : ℝ≥0∞ := ∑ p ∈ Finset.range (P + 1),
      Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
        (1 : ℕ × ℤ → ℝ≥0∞)
        (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) with hT2def
  set T3 : ℝ≥0∞ := ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
      then (1 : ℝ) else 0) with hT3def
  by_cases hfew : Nw ≤ (K : ℝ)
  · rw [if_pos hfew, ENNReal.ofReal_one]
    by_cases hcol : (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
    · -- bad column: `T3 = 1`.
      have hT3one : T3 = 1 := by rw [hT3def, if_pos hcol, ENNReal.ofReal_one]
      calc (1 : ℝ≥0∞) = T3 := hT3one.symm
        _ ≤ T1 + T2 + T3 := self_le_add_left _ _
    · -- good column: depth holds, apply the dichotomy.
      have hset : whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2} = whiteStrip n ξ := by
        ext q; simp only [whiteStrip, Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
      have hcast : Nw = ((∑ p ∈ Finset.range P,
              (if q₀ + pathSum v p ∈ whiteStrip n ξ then (1 : ℕ) else 0) : ℕ) : ℝ) := by
        rw [hNwdef, Nat.cast_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        have hpt : (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)
            = q₀ + pathSum v p := rfl
        rw [hpt, hset, Set.indicator_apply, Pi.one_apply, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero]
      have hNatK : (∑ p ∈ Finset.range P,
          (if q₀ + pathSum v p ∈ whiteStrip n ξ then (1 : ℕ) else 0)) ≤ K := by
        have h := hfew; rw [hcast] at h; exact_mod_cast h
      -- depth: adv + g ≤ m, hence every intermediate position stays deep.
      have hadv : (e.1 + (pathSum v P).1 : ℕ) + g ≤ m := by
        have hlt : ((e.1 + (pathSum v P).1 : ℕ) : ℝ) < 0.9 * (m : ℝ) := not_le.mp hcol
        have hsum : ((e.1 + (pathSum v P).1 : ℕ) : ℝ) + (g : ℝ) ≤ (m : ℝ) := by
          nlinarith [hlt, hg]
        exact_mod_cast hsum
      have hqone : 1 ≤ q₀.1 := by rw [hq1]; omega
      have hendpt : q₀.1 + (pathSum v P).1 + g ≤ n / 2 := by rw [hq1]; omega
      have hdepth : ∀ p, p ≤ P → (q₀ + pathSum v p).1 + g ≤ n / 2 :=
        pathSum_depth_le v q₀ g (n / 2) hendpt
      have hdich := few_white_pointwise_dichotomy F g R K A' hA' P hP q₀ hqone v hv hdepth hNatK
      rcases hdich with ⟨hreach, hcw⟩ | ⟨p, hp, t, ht, hmem, hbig⟩
      · -- reach: `T1 = 1`.
        have hT1one : T1 = 1 := by
          rw [hT1def, if_pos ⟨hreach, hcw⟩, ENNReal.ofReal_one]
        calc (1 : ℝ≥0∞) = T1 := hT1one.symm
          _ ≤ T1 + T2 := self_le_add_right _ _
          _ ≤ T1 + T2 + T3 := self_le_add_right _ _
      · -- E∗: one middle summand of `T2` is 1.
        have hpt : ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2)
            = (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) := by
          have h1 : (q₀ + pathSum v p).1 = n / 2 - m + e.1 + (pathSum v p).1 := rfl
          have h2 : (q₀ + pathSum v p).2 = l + e.2 + (pathSum v p).2 := rfl
          refine Prod.ext_iff.mpr ⟨?_, h2⟩
          rw [h1]; omega
        have hbigmem : (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)
            ∈ bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊ := by
          rw [← hpt]; exact bigTriangle_of_encounter F A' p _ t ht hmem hbig
        have hone : Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) = 1 := by
          rw [Set.indicator_of_mem hbigmem]; rfl
        have hT2ge : (1 : ℝ≥0∞) ≤ T2 := by
          have hsingle := Finset.single_le_sum (f := fun p : ℕ =>
            Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
            (fun i _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hp))
          rw [hone] at hsingle
          rw [hT2def]; exact hsingle
        calc (1 : ℝ≥0∞) ≤ T2 := hT2ge
          _ ≤ T1 + T2 := self_le_add_left _ _
          _ ≤ T1 + T2 + T3 := self_le_add_right _ _
  · rw [if_neg hfew, ENNReal.ofReal_zero]
    exact zero_le

open scoped Classical in
/-- **(7.56) reach-`R` mass term**, `_at` sibling at `eps0_manyTri`/`g_manyTri`. Same body
as the `∃`-form below, with the shared gate `ε₀ = eps0_manyTri` and `g = g_manyTri` supplied
by `reaches_fewWhite_mass_le_ten_at`. -/
theorem few_white_reach_mass_le_at (A : ℝ) :
    ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ (m : ℕ) (l : ℤ) (R : ℕ), 1 ≤ R → ∀ (K P : ℕ),
      ((K : ℝ) + 1) + (A + 5) * Real.log 10 + 2 ≤ eps0_manyTri * R → ∀ s : ℕ,
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F R g_manyTri)
                (encInit (n / 2 - m + e.1) (l + e.2))).count
              ∧ ((List.ofFn v).foldl (encStep F R g_manyTri)
                (encInit (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) := by
  intro n ξ hξ F m l R hR K P hRbound s
  have hval : (0 : ℝ) ≤ (10 : ℝ) ^ (-A - 3) := Real.rpow_nonneg (by norm_num) _
  have hexp : (10 : ℝ) ^ (-((A + 2) + 1)) = (10 : ℝ) ^ (-A - 3) := by
    congr 1; ring
  have hinner : ∀ e : ℕ × ℤ,
      (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F R g_manyTri)
                (encInit (n / 2 - m + e.1) (l + e.2))).count
              ∧ ((List.ofFn v).foldl (encStep F R g_manyTri)
                (encInit (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) := by
    intro e
    set S : ℝ≥0∞ := ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F R g_manyTri)
              (encInit (n / 2 - m + e.1) (l + e.2))).count
            ∧ ((List.ofFn v).foldl (encStep F R g_manyTri)
              (encInit (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
          then (1 : ℝ) else 0) with hSdef
    have hSle1 : S ≤ 1 := by
      rw [hSdef]
      exact PMF.tsum_mul_ofReal_le_one (hold.iid P) _ (fun v => by split_ifs <;> norm_num)
    have hSne : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hSle1
    have hbridge : S.toReal = ∑' v : Fin P → ℕ × ℤ, (hold.iid P v).toReal *
        (if R ≤ ((List.ofFn v).foldl (encStep F R g_manyTri)
              (encInit (n / 2 - m + e.1) (l + e.2))).count
            ∧ ((List.ofFn v).foldl (encStep F R g_manyTri)
              (encInit (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
          then (1 : ℝ) else 0) := by
      rw [hSdef]; exact PMF.toReal_tsum_mul_ofReal (hold.iid P) _ (fun v => by split_ifs <;> norm_num)
    have hr := reaches_fewWhite_mass_le_ten_at eps0_manyTri eps0_manyTri_pos le_rfl (A + 2) n ξ hξ F R hR P (n / 2 - m + e.1, l + e.2) (K + 1)
      (by push_cast; nlinarith [hRbound])
    rw [ENNReal.le_ofReal_iff_toReal_le hSne hval, hbridge, ← hexp]
    exact hr
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right (hinner e) _) ?_
  rw [ENNReal.tsum_mul_right, (fpDist s).tsum_coe, one_mul]

open scoped Classical in
/-- **(7.56) reach-`R` mass term.** The first-passage⊗walk mass of the reach-`R`/few-white
event `{R ≤ count ∧ cumWhite ≤ K+1}` is `≤ 10^{−A−3}`. Wraps `reaches_fewWhite_mass_le_ten`
(applied per-`e` at reaches-exponent `A+2` ⟹ `10^{−(A+3)}`, `K'=K+1`) with the `ℝ≥0∞`→`ℝ`
bridge `PMF.toReal_tsum_mul_ofReal` and the `fpDist`-averaging (`Σ fpDist = 1`). Exposes the
shared `ε₀, g` (from reaches) that X11d also feeds into `few_white_pointwise_split`. -/
theorem few_white_reach_mass_le (A : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ g : ℕ, ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ (m : ℕ) (l : ℤ) (R : ℕ), 1 ≤ R → ∀ (K P : ℕ),
      ((K : ℝ) + 1) + (A + 5) * Real.log 10 + 2 ≤ ε₀ * R → ∀ s : ℕ,
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F R g)
                (encInit (n / 2 - m + e.1) (l + e.2))).count
              ∧ ((List.ofFn v).foldl (encStep F R g)
                (encInit (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) :=
  ⟨eps0_manyTri, eps0_manyTri_pos, g_manyTri, few_white_reach_mass_le_at A⟩

/-- Poly·geom domination: `x²·exp(−bx) ≤ 4/b²` for `x ≥ 0`, `b > 0` (from `exp(bx) ≥ (bx)²/4`). -/
theorem sq_mul_exp_neg_le (b : ℝ) (hb : 0 < b) (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-b * x) ≤ 4 / b ^ 2 := by
  have hquad : (b * x) ^ 2 / 4 ≤ Real.exp (b * x) := by
    have h1 : 1 + b * x / 2 ≤ Real.exp (b * x / 2) := by
      have := Real.add_one_le_exp (b * x / 2); linarith
    have hnn : (0 : ℝ) ≤ 1 + b * x / 2 := by positivity
    have h2 : (1 + b * x / 2) ^ 2 ≤ Real.exp (b * x / 2) ^ 2 :=
      pow_le_pow_left₀ hnn h1 2
    have h3 : Real.exp (b * x / 2) ^ 2 = Real.exp (b * x) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h5 : (1 + b * x / 2) ^ 2 ≤ Real.exp (b * x) := h3 ▸ h2
    nlinarith [h5]
  have hexppos : (0 : ℝ) < Real.exp (b * x) := Real.exp_pos _
  have hexpneg : Real.exp (-b * x) = 1 / Real.exp (b * x) := by
    rw [neg_mul, Real.exp_neg, one_div]
  rw [hexpneg, mul_one_div, div_le_div_iff₀ hexppos (by positivity : (0:ℝ) < b ^ 2)]
  nlinarith [hquad, Real.exp_pos (b * x)]

/-- Cubic poly·geom domination: `x²·exp(−bx) ≤ 27/(b³x)` for `x > 0`, `b > 0`
(from `exp(bx) ≥ (bx)³/27`), giving the `A₀ → 0` decay of `A₀²·4^{−A₀}`. -/
theorem sq_mul_exp_neg_le_inv (b : ℝ) (hb : 0 < b) (x : ℝ) (hx : 0 < x) :
    x ^ 2 * Real.exp (-b * x) ≤ 27 / (b ^ 3 * x) := by
  have hbx : (0 : ℝ) < b * x := by positivity
  have hcube : (b * x) ^ 3 / 27 ≤ Real.exp (b * x) := by
    have h1 : 1 + b * x / 3 ≤ Real.exp (b * x / 3) := by
      have := Real.add_one_le_exp (b * x / 3); linarith
    have hnn : (0 : ℝ) ≤ 1 + b * x / 3 := by positivity
    have h2 : (1 + b * x / 3) ^ 3 ≤ Real.exp (b * x / 3) ^ 3 :=
      pow_le_pow_left₀ hnn h1 3
    have h3 : Real.exp (b * x / 3) ^ 3 = Real.exp (b * x) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h5 : (1 + b * x / 3) ^ 3 ≤ Real.exp (b * x) := h3 ▸ h2
    nlinarith [h5, hbx.le]
  have hexppos : (0 : ℝ) < Real.exp (b * x) := Real.exp_pos _
  have hexpneg : Real.exp (-b * x) = 1 / Real.exp (b * x) := by
    rw [neg_mul, Real.exp_neg, one_div]
  rw [hexpneg, mul_one_div, div_le_div_iff₀ hexppos (by positivity : (0:ℝ) < b ^ 3 * x)]
  nlinarith [hcube, hexppos, hx, hb]

/-- **E∗-scaled cleared-denominator threshold** (X11b): the `A₀ ≥ Kthr` requirement that makes
both linear-in-`A₀` term-1 bounds fit `1/4000`. -/
noncomputable def Kthr_estarScaled (C' : ℝ) : ℝ :=
  3456000 * C' / ((2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3)
    + 216000 * C' / (Real.log 4) ^ 3

/-- **E∗-scaled complete-the-square argument** (X11b): the `A₀² ≥ Warg` requirement for term 2. -/
noncomputable def Warg_estarScaled (C' c : ℝ) : ℝ :=
  (16 * c * Real.log (2000 * C') + (Real.log 10) ^ 2) / (16 * c ^ 2)

/-- **E∗-scaled threshold** `A₀` (X11b): `max A₀e (max 1 (max Kthr √(max 0 Warg)))` — the
`estar_scaled_numeric` witness, joining the E∗ threshold `A₀e`, the floor `1`, the term-1
cleared-denominator bound `Kthr`, and the term-2 completing-the-square bound `√Warg`. -/
noncomputable def A0_estarScaled (C' c A₀e : ℝ) : ℝ :=
  max A₀e (max 1 (max (Kthr_estarScaled C') (Real.sqrt (max 0 (Warg_estarScaled C' c)))))

-- HEARTBEAT: large single-shot constant-chase (two poly·geom dominations + complete-the-square
-- over the base-16-vs-10 comparison); the `Real.log 4`/`Real.log 10` denominators make the calc
-- defeq checks heavy. Pure real inequality, no `native_decide`.
set_option maxHeartbeats 1600000 in
/-- **Numeric closure for the E∗ term.** With the base-4 geometry lemmas instantiated at the
scaled exponent `A' := 2A + A₀`, the `estar_union_le` bound `C'·A'²·4^{−A'} + C'·exp(−c·A'²)`
fits the target `10^{−A−3}` for ALL `A > 0`, provided `A₀` is a large enough constant. The
scaling `2A` makes the effective base `4² = 16 > 10`, so `4^{−A'} = 4^{−A₀}·16^{−A}` beats
`10^{−A}`; the leftover poly·geom `(2A+A₀)²·(10/16)^A` is dominated (`x²·r^x ≤ 4/log(1/r)²`)
and the `exp(−c·A'²)` term closed by completing the square. `A₀` is chosen `≥ A₀e` (the E∗
threshold) and `≥ 1`. -/
theorem estar_scaled_numeric_at (C' c A₀e : ℝ) (hC' : 0 < C') (hc : 0 < c) (hA₀e : 1 ≤ A₀e) :
    A₀e ≤ A0_estarScaled C' c A₀e ∧ 1 ≤ A0_estarScaled C' c A₀e ∧ ∀ A : ℝ, 0 < A →
      C' * (2 * A + A0_estarScaled C' c A₀e) ^ 2 * (4 : ℝ) ^ (-(2 * A + A0_estarScaled C' c A₀e))
        + C' * Real.exp (-c * (2 * A + A0_estarScaled C' c A₀e) ^ 2)
        ≤ (10 : ℝ) ^ (-A - 3) := by
  unfold A0_estarScaled Kthr_estarScaled Warg_estarScaled
  have hL4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hL10 : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num)
  have hL85 : (0 : ℝ) < 2 * Real.log 4 - Real.log 10 := by
    have h16eq : Real.log 16 = 2 * Real.log 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    have h16 : Real.log 10 < Real.log 16 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith [h16, h16eq]
  -- cleared-denominator threshold (avoids nested fractions in `nlinarith`/`field_simp`)
  set Kthr : ℝ := 3456000 * C' / ((2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3)
    + 216000 * C' / (Real.log 4) ^ 3 with hKthrdef
  set Warg : ℝ := (16 * c * Real.log (2000 * C') + (Real.log 10) ^ 2) / (16 * c ^ 2) with hWdef
  set X2 : ℝ := max 0 Warg with hX2def
  have hX2nn : 0 ≤ X2 := le_max_left _ _
  set A₀ : ℝ := max A₀e (max 1 (max Kthr (Real.sqrt X2))) with hA₀def
  have hA₀e_le : A₀e ≤ A₀ := le_max_left _ _
  have hA₀1 : (1 : ℝ) ≤ A₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hA₀pos : (0 : ℝ) < A₀ := by linarith
  have hA₀Kthr : Kthr ≤ A₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hA₀sqrt : Real.sqrt X2 ≤ A₀ :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨hA₀e_le, hA₀1, ?_⟩
  intro A hA
  -- rpow → exp conversions
  have h4y : (4 : ℝ) ^ (-(2 * A + A₀))
      = Real.exp (-(2 * Real.log 4 - Real.log 10) * A) * Real.exp (-Real.log 4 * A₀)
        * Real.exp (-Real.log 10 * A) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hRval : (10 : ℝ) ^ (-A - 3) = Real.exp (-Real.log 10 * A) / 1000 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
    have h3 : Real.exp (Real.log 10 * (-A - 3))
        = Real.exp (-Real.log 10 * A) * Real.exp (-3 * Real.log 10) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h3]
    have h1000 : Real.exp (-3 * Real.log 10) = 1 / 1000 := by
      rw [show (-3 : ℝ) * Real.log 10 = -(Real.log 1000) by
        rw [show (1000 : ℝ) = 10 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring]
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 1000)]; norm_num
    rw [h1000]; ring
  set E85 : ℝ := Real.exp (-(2 * Real.log 4 - Real.log 10) * A) with hE85def
  set E4 : ℝ := Real.exp (-Real.log 4 * A₀) with hE4def
  set E10 : ℝ := Real.exp (-Real.log 10 * A) with hE10def
  have hE85pos : 0 < E85 := Real.exp_pos _
  have hE4pos : 0 < E4 := Real.exp_pos _
  have hE10pos : 0 < E10 := Real.exp_pos _
  have hE85_1 : E85 ≤ 1 := by rw [hE85def, Real.exp_le_one_iff]; nlinarith [hL85, hA]
  have hAE85 : A ^ 2 * E85 ≤ 4 / (2 * Real.log 4 - Real.log 10) ^ 2 :=
    sq_mul_exp_neg_le (2 * Real.log 4 - Real.log 10) hL85 A hA.le
  have hA0E4 : A₀ ^ 2 * E4 ≤ 27 / ((Real.log 4) ^ 3 * A₀) :=
    sq_mul_exp_neg_le_inv (Real.log 4) hL4 A₀ hA₀pos
  have hE4dom : E4 ≤ 27 / ((Real.log 4) ^ 3 * A₀ ^ 3) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log 4) ^ 3 * A₀ ^ 3)]
    have h := hA0E4
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log 4) ^ 3 * A₀)] at h
    nlinarith [h, hE4pos]
  -- **term 1**: `C'·y²·4^{−y} ≤ (1/2)·10^{−A−3}`.
  have hterm1 : C' * (2 * A + A₀) ^ 2 * (4 : ℝ) ^ (-(2 * A + A₀)) ≤ (1 / 2) * (10 : ℝ) ^ (-A - 3) := by
    rw [h4y, hRval]
    rw [show C' * (2 * A + A₀) ^ 2 * (E85 * E4 * E10)
        = (C' * (2 * A + A₀) ^ 2 * E85 * E4) * E10 by ring,
      show (1 / 2 : ℝ) * (E10 / 1000) = (1 / 2000) * E10 by ring]
    refine mul_le_mul_of_nonneg_right ?_ hE10pos.le
    -- reduced target: `C'·y²·E85·E4 ≤ 1/2000`.
    have hy2 : (2 * A + A₀) ^ 2 ≤ 8 * A ^ 2 + 2 * A₀ ^ 2 := by nlinarith [sq_nonneg (2 * A - A₀)]
    have hsplit : C' * (8 * A ^ 2 + 2 * A₀ ^ 2) * E85 * E4
        = 8 * (C' * (A ^ 2 * E85) * E4) + 2 * (C' * (A₀ ^ 2 * E4) * E85) := by ring
    have hb1 : 8 * (C' * (A ^ 2 * E85) * E4)
        ≤ 8 * (C' * (4 / (2 * Real.log 4 - Real.log 10) ^ 2) * (27 / ((Real.log 4) ^ 3 * A₀ ^ 3))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have t1 : C' * (A ^ 2 * E85) * E4 ≤ C' * (4 / (2 * Real.log 4 - Real.log 10) ^ 2) * E4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAE85 hC'.le) hE4pos.le
      have t2 : C' * (4 / (2 * Real.log 4 - Real.log 10) ^ 2) * E4
          ≤ C' * (4 / (2 * Real.log 4 - Real.log 10) ^ 2) * (27 / ((Real.log 4) ^ 3 * A₀ ^ 3)) :=
        mul_le_mul_of_nonneg_left hE4dom (by positivity)
      exact le_trans t1 t2
    have hb2 : 2 * (C' * (A₀ ^ 2 * E4) * E85)
        ≤ 2 * (C' * (27 / ((Real.log 4) ^ 3 * A₀)) * 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have t1 : C' * (A₀ ^ 2 * E4) * E85 ≤ C' * (27 / ((Real.log 4) ^ 3 * A₀)) * E85 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA0E4 hC'.le) hE85pos.le
      have t2 : C' * (27 / ((Real.log 4) ^ 3 * A₀)) * E85 ≤ C' * (27 / ((Real.log 4) ^ 3 * A₀)) * 1 :=
        mul_le_mul_of_nonneg_left hE85_1 (by positivity)
      exact le_trans t1 t2
    have hchain : C' * (2 * A + A₀) ^ 2 * E85 * E4
        ≤ 864 * C' / ((2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3 * A₀ ^ 3)
          + 54 * C' / ((Real.log 4) ^ 3 * A₀) := by
      have hle1 : C' * (2 * A + A₀) ^ 2 * E85 * E4 ≤ C' * (8 * A ^ 2 + 2 * A₀ ^ 2) * E85 * E4 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy2 hC'.le) hE85pos.le) hE4pos.le
      rw [hsplit] at hle1
      have hcombine := add_le_add hb1 hb2
      have heq : 8 * (C' * (4 / (2 * Real.log 4 - Real.log 10) ^ 2) * (27 / ((Real.log 4) ^ 3 * A₀ ^ 3)))
          + 2 * (C' * (27 / ((Real.log 4) ^ 3 * A₀)) * 1)
          = 864 * C' / ((2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3 * A₀ ^ 3)
            + 54 * C' / ((Real.log 4) ^ 3 * A₀) := by
        field_simp; ring
      linarith [hle1, hcombine, heq.le, heq.ge]
    -- clear denominators: `A₀ ≥ Kthr` gives the two linear-in-`A₀` bounds.
    have hden1 : (0 : ℝ) < (2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3 := by positivity
    have hA0_i : 3456000 * C' ≤ (2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3 * A₀ := by
      have hle : 3456000 * C' / ((2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3) ≤ A₀ :=
        le_trans (le_add_of_nonneg_right (by positivity)) hA₀Kthr
      calc 3456000 * C'
          = (2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3
              * (3456000 * C' / ((2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3)) := by
            field_simp
        _ ≤ (2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3 * A₀ :=
            mul_le_mul_of_nonneg_left hle hden1.le
    have hA0_ii : 216000 * C' ≤ (Real.log 4) ^ 3 * A₀ := by
      have hle : 216000 * C' / (Real.log 4) ^ 3 ≤ A₀ :=
        le_trans (le_add_of_nonneg_left (by positivity)) hA₀Kthr
      calc 216000 * C'
          = (Real.log 4) ^ 3 * (216000 * C' / (Real.log 4) ^ 3) := by field_simp
        _ ≤ (Real.log 4) ^ 3 * A₀ := mul_le_mul_of_nonneg_left hle (by positivity)
    have hbnd1 : 864 * C' / ((2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3 * A₀ ^ 3)
        ≤ 1 / 4000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hA03 : A₀ ≤ A₀ ^ 3 := by nlinarith [hA₀1, hA₀pos]
      nlinarith [hA0_i, mul_le_mul_of_nonneg_left hA03 hden1.le]
    have hbnd2 : 54 * C' / ((Real.log 4) ^ 3 * A₀) ≤ 1 / 4000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hA0_ii]
    calc C' * (2 * A + A₀) ^ 2 * E85 * E4
        ≤ 864 * C' / ((2 * Real.log 4 - Real.log 10) ^ 2 * (Real.log 4) ^ 3 * A₀ ^ 3)
          + 54 * C' / ((Real.log 4) ^ 3 * A₀) := hchain
      _ ≤ 1 / 4000 + 1 / 4000 := add_le_add hbnd1 hbnd2
      _ ≤ 1 / 2000 := by norm_num
  -- **term 2**: `C'·exp(−c·y²) ≤ (1/2)·10^{−A−3}` (complete the square).
  have hterm2 : C' * Real.exp (-c * (2 * A + A₀) ^ 2) ≤ (1 / 2) * (10 : ℝ) ^ (-A - 3) := by
    rw [hRval]
    -- reduce to `2000·C'·exp(−c y²) ≤ E10` then to the quadratic in exponents.
    have hquad2 : A * Real.log 10 + Real.log (2000 * C') ≤ c * (2 * A + A₀) ^ 2 := by
      have hy2ge : 4 * A ^ 2 + A₀ ^ 2 ≤ (2 * A + A₀) ^ 2 := by nlinarith [hA.le, hA₀pos.le]
      have hA0X2 : X2 ≤ A₀ ^ 2 := by
        have h1 : Real.sqrt X2 ^ 2 ≤ A₀ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hA₀sqrt 2
        rwa [Real.sq_sqrt hX2nn] at h1
      have hWle : Warg ≤ X2 := le_max_right _ _
      have hA0sq : 16 * c * Real.log (2000 * C') + (Real.log 10) ^ 2 ≤ 16 * c ^ 2 * A₀ ^ 2 := by
        have hWval : 16 * c ^ 2 * Warg = 16 * c * Real.log (2000 * C') + (Real.log 10) ^ 2 := by
          rw [hWdef]; field_simp
        have h2 : 16 * c ^ 2 * Warg ≤ 16 * c ^ 2 * A₀ ^ 2 :=
          mul_le_mul_of_nonneg_left (le_trans hWle hA0X2) (by positivity)
        linarith [h2, hWval.le, hWval.ge]
      have hmul : 16 * c * (A * Real.log 10 + Real.log (2000 * C'))
          ≤ 16 * c * (c * (2 * A + A₀) ^ 2) := by
        nlinarith [hA0sq, sq_nonneg (8 * c * A - Real.log 10),
          mul_le_mul_of_nonneg_left hy2ge (by positivity : (0 : ℝ) ≤ 16 * c ^ 2)]
      exact le_of_mul_le_mul_left hmul (by positivity : (0 : ℝ) < 16 * c)
    -- from the quadratic bound, `C'·exp(−c y²) ≤ E10/2000`.
    rw [show (1 / 2 : ℝ) * (E10 / 1000) = E10 / 2000 by ring]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2000)]
    have hlhs : 2000 * C' = Real.exp (Real.log (2000 * C')) := by
      rw [Real.exp_log (by positivity)]
    have hexp_le : Real.exp (Real.log (2000 * C') + -c * (2 * A + A₀) ^ 2) ≤ E10 := by
      rw [hE10def]
      apply Real.exp_le_exp.mpr
      nlinarith [hquad2]
    calc C' * Real.exp (-c * (2 * A + A₀) ^ 2) * 2000
        = Real.exp (Real.log (2000 * C')) * Real.exp (-c * (2 * A + A₀) ^ 2) := by
          rw [← hlhs]; ring
      _ = Real.exp (Real.log (2000 * C') + -c * (2 * A + A₀) ^ 2) := by rw [← Real.exp_add]
      _ ≤ E10 := hexp_le
  -- combine the two terms.
  calc C' * (2 * A + A₀) ^ 2 * (4 : ℝ) ^ (-(2 * A + A₀)) + C' * Real.exp (-c * (2 * A + A₀) ^ 2)
      ≤ (1 / 2) * (10 : ℝ) ^ (-A - 3) + (1 / 2) * (10 : ℝ) ^ (-A - 3) := add_le_add hterm1 hterm2
    _ = (10 : ℝ) ^ (-A - 3) := by ring

/-- **Numeric closure for the E∗ term**, original `∃`-form: delegates to
`estar_scaled_numeric_at` at the named witness `A0_estarScaled C' c A₀e`. -/
theorem estar_scaled_numeric (C' c A₀e : ℝ) (hC' : 0 < C') (hc : 0 < c) (hA₀e : 1 ≤ A₀e) :
    ∃ A₀ : ℝ, A₀e ≤ A₀ ∧ 1 ≤ A₀ ∧ ∀ A : ℝ, 0 < A →
      C' * (2 * A + A₀) ^ 2 * (4 : ℝ) ^ (-(2 * A + A₀))
        + C' * Real.exp (-c * (2 * A + A₀) ^ 2)
        ≤ (10 : ℝ) ^ (-A - 3) :=
  ⟨A0_estarScaled C' c A₀e, estar_scaled_numeric_at C' c A₀e hC' hc hA₀e⟩

/-- **E∗ scaled-exponent constant** (X11b): `A0_estarScaled` at the E∗-union constants —
the additive `A₀` in the `few_white_estar_mass_le` exponent `A' = 2A + A0_fewEstar`. -/
noncomputable def A0_fewEstar : ℝ := A0_estarScaled C_estarUnion c_estarUnion A0_estarUnion

open scoped Classical in
/-- **(7.56) E∗ mass term.** The first-passage⊗walk mass of the union-over-`p` big-triangle
event (the middle term of `few_white_pointwise_split`) is `≤ 10^{−A−3}`. Wraps
`estar_union_le` at the scaled exponent `A' := 2A + A₀` (`estar_scaled_numeric`), after the
`ℝ≥0∞` tsum↔finite-sum swap (`Summable.tsum_finsetSum`) that turns the inner `Σ_p` into the
outer union `estar_union_le` bounds. The deep hyp `(m+1)^0.8 < s` is bridged from the regime
`m/log²m < s` via `(m+1)^0.8 ≤ 2m^0.8 ≤ m/log²m`. -/
theorem few_white_estar_mass_le_at (A : ℝ) (hA : 0 < A) :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, (10 : ℕ) ^ 30 ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      ∀ P : ℕ, (∀ p, p ≤ P →
          ((⌊(4 : ℝ) ^ (2 * A + A0_fewEstar) * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
            ≤ ((m + 1 : ℕ) : ℝ) ^ (0.4 : ℝ)) →
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          (∑ p ∈ Finset.range (P + 1),
            Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ (2 * A + A0_fewEstar) * (1 + (p : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))
        ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) := by
  have hestar := estar_union_le_rpow_explicitC
  have hA₀ge : A0_estarUnion ≤ A0_fewEstar :=
    (estar_scaled_numeric_at C_estarUnion c_estarUnion A0_estarUnion
      C_estarUnion_pos c_estarUnion_pos one_le_A0_estarUnion).1
  have hnum := (estar_scaled_numeric_at C_estarUnion c_estarUnion A0_estarUnion
    C_estarUnion_pos c_estarUnion_pos one_le_A0_estarUnion).2.2
  set A' : ℝ := 2 * A + A0_fewEstar with hA'def
  have hA'ge : A0_estarUnion ≤ A' := by rw [hA'def]; linarith [hA₀ge, hA]
  intro n ξ hξ F m hmCthr hmn l hpos t ht hmem s hs hreg_s P hreg
  -- the E∗ summand, per `p`, matching `estar_union_le`'s form at `j = n/2-m-1`, `T = P`.
  set G : ℕ → ℝ≥0∞ := fun p => ∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ,
      hold.iid P v * Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
        (1 : ℕ × ℤ → ℝ≥0∞)
        (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) with hGdef
  -- each summand indicator ≤ 1, so each `G p ≤ 1` (finite).
  have hind_le1 : ∀ (p : ℕ) (y : ℕ × ℤ),
      Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
        (1 : ℕ × ℤ → ℝ≥0∞) y ≤ 1 := by
    intro p y; rw [Set.indicator_apply]; split_ifs with h
    · simp
    · simp
  have hGle1 : ∀ p, G p ≤ 1 := by
    intro p
    rw [hGdef]
    calc (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            Set.indicator _ (1 : ℕ × ℤ → ℝ≥0∞) _)
        ≤ ∑' e : ℕ × ℤ, fpDist s e * 1 := by
          refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
          calc (∑' v : Fin P → ℕ × ℤ, hold.iid P v * Set.indicator _ (1 : ℕ × ℤ → ℝ≥0∞) _)
              ≤ ∑' v : Fin P → ℕ × ℤ, hold.iid P v * 1 :=
                ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hind_le1 _ _) _
            _ = 1 := by rw [ENNReal.tsum_mul_right, (hold.iid P).tsum_coe, one_mul]
      _ = 1 := by rw [ENNReal.tsum_mul_right, (fpDist s).tsum_coe, one_mul]
  have hGne : ∀ p, G p ≠ ⊤ := fun p => ne_top_of_le_ne_top ENNReal.one_ne_top (hGle1 p)
  -- **tsum ↔ finite-sum swap**: the goal LHS equals `∑_{p<P+1} G p`.
  have hstep1 : ∀ e : ℕ × ℤ, (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (∑ p ∈ Finset.range (P + 1),
          Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))
      = ∑ p ∈ Finset.range (P + 1), ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) := by
    intro e
    rw [show (∑' v : Fin P → ℕ × ℤ, hold.iid P v * (∑ p ∈ Finset.range (P + 1), _))
        = ∑' v : Fin P → ℕ × ℤ, ∑ p ∈ Finset.range (P + 1), hold.iid P v *
            Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) from
        tsum_congr fun v => by rw [Finset.mul_sum]]
    exact Summable.tsum_finsetSum (fun p _ => ENNReal.summable)
  have hswap : (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (∑ p ∈ Finset.range (P + 1),
          Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
            (1 : ℕ × ℤ → ℝ≥0∞)
            (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))
      = ∑ p ∈ Finset.range (P + 1), G p := by
    rw [show (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          (∑ p ∈ Finset.range (P + 1), _))
        = ∑' e : ℕ × ℤ, ∑ p ∈ Finset.range (P + 1), fpDist s e *
            ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
              Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
                (1 : ℕ × ℤ → ℝ≥0∞)
                (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) from
        tsum_congr fun e => by rw [hstep1 e, Finset.mul_sum]]
    rw [Summable.tsum_finsetSum (fun p _ => ENNReal.summable)]
  rw [hswap]
  -- the deep-hyp bridge `(m+1)^0.8 < s` and the ℕ depth identity `n/2-(n/2-m-1) = m+1`.
  have hmC : (10 : ℝ) ^ (30 : ℕ) ≤ (m : ℝ) := by exact_mod_cast hmCthr
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := le_trans (by norm_num) hmC
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hbridge : ((m + 1 : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ) := by
    have hlogsqpos : (0 : ℝ) < Real.log (m : ℝ) ^ 2 := by positivity
    -- (m+1)^0.8 ≤ 2·m^0.8
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
    -- log m ≤ 20·m^0.05, hence log²m ≤ 400·m^0.1
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
    -- (m+1)^0.8 · log²m ≤ 800·m^0.9 ≤ m
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
  have hreg' : ∀ p, p ≤ P →
      ((⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
        ≤ ((n / 2 - (n / 2 - m - 1) : ℕ) : ℝ) ^ (0.4 : ℝ) := by
    intro p hp; rw [hdd]; exact hreg p hp
  -- apply `estar_union_le` at `A' = 2A+A₀`, `j = n/2-m-1`, `T = P`.
  have hest := hestar A' hA'ge n ξ hξ F t ht (n / 2 - m - 1) l hmem s hs hdeep' P hreg'
  -- `(∑_p G p).toReal = ∑_p (G p).toReal ≤ estar bound ≤ 10^{−A−3}`.
  have hSne : (∑ p ∈ Finset.range (P + 1), G p) ≠ ⊤ :=
    (ENNReal.sum_ne_top).mpr (fun p _ => hGne p)
  have hStoreal : (∑ p ∈ Finset.range (P + 1), G p).toReal ≤ (10 : ℝ) ^ (-A - 3) := by
    rw [ENNReal.toReal_sum (fun p _ => hGne p)]
    exact le_trans hest (hnum A hA)
  rw [ENNReal.le_ofReal_iff_toReal_le hSne (Real.rpow_nonneg (by norm_num) _)]
  exact hStoreal

open scoped Classical in
/-- **(7.56) E∗ mass term**, original `∃`-form: delegates to `few_white_estar_mass_le_at` at
the named witness `A' = 2A + A0_fewEstar`, `Cthr = 10^30`. -/
theorem few_white_estar_mass_le (A : ℝ) (hA : 0 < A) :
    ∃ A' : ℝ, 1 ≤ A' ∧ ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      ∀ P : ℕ, (∀ p, p ≤ P →
          ((⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (0.4 : ℝ)) →
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          (∑ p ∈ Finset.range (P + 1),
            Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
              (1 : ℕ × ℤ → ℝ≥0∞)
              (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))
        ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) :=
  ⟨2 * A + A0_fewEstar, by
    have h1 : (1 : ℝ) ≤ A0_fewEstar :=
      (estar_scaled_numeric_at C_estarUnion c_estarUnion A0_estarUnion
        C_estarUnion_pos c_estarUnion_pos one_le_A0_estarUnion).2.1
    linarith [hA], 10 ^ 30, few_white_estar_mass_le_at A hA⟩

/-! ### The sole X11 gate and the checked downstream assembly -/

/-- Explicit threshold past which `exp(−ρm) ≤ δ·m^{−A}` (witness of
`exp_neg_mul_le_rpow_neg`, reified — big-C campaign step 2). -/
noncomputable def T_expRpow (A ρ δ : ℝ) : ℕ := 1 + T_logLin (ρ / (2 * A)) + T_expNeg (ρ / 2) δ

/-- **Super-exponential beats polynomial** (explicit-threshold form): `exp(−ρm) ≤ δ·m^{−A}`
for `m ≥ T_expRpow A ρ δ`. Extracted from `hold_fst_tail_le`'s `hclose`; combines
`log_le_eps_mul_at` (`log m ≤ (ρ/2A)m`) with `exp_neg_mul_le_at` (final tail). -/
theorem exp_neg_mul_le_rpow_neg_at (A : ℝ) (hA : 0 < A) (ρ : ℝ) (hρ : 0 < ρ)
    (δ : ℝ) (hδ : 0 < δ) : ∀ m : ℕ, T_expRpow A ρ δ ≤ m →
      Real.exp (-ρ * (m : ℝ)) ≤ δ * (m : ℝ) ^ (-A) := by
  have hNlog := log_le_eps_mul_at (ρ / (2 * A)) (by positivity)
  have hNexp := exp_neg_mul_le_at (ρ / 2) (by positivity) δ hδ
  intro m hm
  unfold T_expRpow at hm
  set Nlog := T_logLin (ρ / (2 * A)) with hNlogdef
  set Nexp := T_expNeg (ρ / 2) δ with hNexpdef
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [Real.rpow_neg hmpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hmpos A),
    Real.rpow_def_of_pos hmpos A, ← Real.exp_add]
  have hAlog : A * Real.log m ≤ ρ / 2 * m := by
    have h := hNlog m (by omega)
    have h2 : A * Real.log m ≤ A * (ρ / (2 * A) * (m : ℝ)) := mul_le_mul_of_nonneg_left h hA.le
    have h3 : A * (ρ / (2 * A) * (m : ℝ)) = ρ / 2 * m := by field_simp
    linarith [h2, h3.le, h3.ge]
  have hexparg : -ρ * (m : ℝ) + Real.log m * A ≤ -(ρ / 2) * m := by nlinarith [hAlog]
  exact le_trans (Real.exp_le_exp.mpr hexparg) (hNexp m (by omega))

/-- `exp_neg_mul_le_rpow_neg`, original `∃`-form: delegates to the `_at` sibling. -/
theorem exp_neg_mul_le_rpow_neg (A : ℝ) (hA : 0 < A) (ρ : ℝ) (hρ : 0 < ρ)
    (δ : ℝ) (hδ : 0 < δ) : ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Real.exp (-ρ * (m : ℝ)) ≤ δ * (m : ℝ) ^ (-A) :=
  ⟨T_expRpow A ρ δ, exp_neg_mul_le_rpow_neg_at A hA ρ hρ δ hδ⟩

/-- **(7.54) bad-column tail** (paper: the `j_end ≥ 0.9m` contribution). The mass that the
`P`-step walk after first passage advances past `0.9m` is `O(e^{−cm})` (Lemma 7.7 + Lemma 2.2:
first passage `≥ 0.8m` and the extra `P` Geom(4) steps `≥ 0.1m` each have mass `e^{−cm}`),
absorbed here into `≤ m^{−A}/2` for `m ≥ Cthr`. Bridged to `fpDistPlus_col_tail` via
`fpDist_walk_eq_fpDistPlus`; the deviation scale uses `budget_le_of_mem_triangle`
(`s·log2 ≤ (m+2)log9`). Stated for any horizon `P ≥ 1` (`Cthr` absorbs the `P`-dependence).
Placed above `few_white_mass_le` so the (7.56) assembly can consume its bad-column term.
**Core, constants abstracted** (big-C campaign, step 2): given the column tail at
`(c, C)` and an exponential-vs-rpow threshold `Nexp` at rate `c/16960` and target
`1/(4C)`, the bound holds past the threshold `400(P+1) + 32 + Nexp`. -/
theorem col_tail_mass_le_core (A : ℝ) (_hA : 0 < A) (P : ℕ) (hP1 : 1 ≤ P)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (htail : ∀ s p : ℕ, ∀ D : ℝ, 10 * (1 + (p : ℝ)) ≤ D →
      ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal
          * Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} 1 e
        ≤ C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D)))
    (Nexp : ℕ)
    (hNexp : ∀ m : ℕ, Nexp ≤ m →
      Real.exp (-(c / 16960) * (m : ℝ)) ≤ 1 / (4 * C) * (m : ℝ) ^ (-A)) :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, 400 * (P + 1) + 32 + Nexp ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) / 2) := by
  classical
  intro n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  set D : ℝ := (m : ℝ) / 40 with hDdef
  -- the fpDistPlus tail hypothesis `10(1+P) ≤ D`.
  have hDbound : 10 * (1 + (P : ℝ)) ≤ D := by
    rw [hDdef]
    have : (400 * (P + 1) : ℕ) ≤ m := by omega
    have hcast : (400 : ℝ) * ((P : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast this
    linarith
  -- budget bound `s < 3.2(m+2)` from `s·log2 ≤ (m+2)log9` and `log9 < 3.2 log2` (`9^5 < 2^16`).
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
  -- the marginal function.
  set g : ℕ × ℤ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((x.1 : ℕ) : ℝ) then (1 : ℝ) else 0) with hgdef
  -- walk → fpDistPlus marginal.
  have hbridge : (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
          then (1 : ℝ) else 0))
      = ∑' x : ℕ × ℤ, fpDistPlus s P x * g x := fpDist_walk_eq_fpDistPlus s (le_refl P) g
  rw [hbridge]
  -- pointwise real containment: `{0.9m ≤ x.1} ⊆ {2D ≤ |x.1 − s/4|}`.
  have hcont : ∀ x : ℕ × ℤ,
      (if (0.9 : ℝ) * (m : ℝ) ≤ ((x.1 : ℕ) : ℝ) then (1 : ℝ) else 0)
      ≤ Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} 1 x := by
    intro x
    by_cases h : (0.9 : ℝ) * (m : ℝ) ≤ ((x.1 : ℕ) : ℝ)
    · rw [if_pos h]
      have hmem2 : x ∈ {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} := by
        show 2 * D ≤ |((x.1 : ℕ) : ℝ) - (s : ℝ) / 4|
        have hstep : 2 * D ≤ ((x.1 : ℕ) : ℝ) - (s : ℝ) / 4 := by
          rw [hDdef]
          have hm32 : (32 : ℝ) ≤ (m : ℝ) := by
            have : (32 : ℕ) ≤ m := by omega
            exact_mod_cast this
          nlinarith [hsbound, h, hm32]
        exact le_trans hstep (le_abs_self _)
      rw [Set.indicator_of_mem hmem2, Pi.one_apply]
    · rw [if_neg h]
      rw [Set.indicator_apply]; split_ifs <;> norm_num
  -- lift the containment through `fpDistPlus`, then compare via `fpDistPlus_col_tail`.
  set RHS : ℝ≥0∞ := ∑' x : ℕ × ℤ, fpDistPlus s P x *
      ENNReal.ofReal (Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} 1 x)
    with hRHSdef
  have hUB : (∑' x : ℕ × ℤ, fpDistPlus s P x * g x) ≤ RHS := by
    rw [hRHSdef]
    refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
    rw [hgdef]; exact ENNReal.ofReal_le_ofReal (hcont x)
  have hRHSle1 : RHS ≤ 1 := by
    rw [hRHSdef]
    calc (∑' x : ℕ × ℤ, fpDistPlus s P x *
          ENNReal.ofReal (Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} 1 x))
        ≤ ∑' x : ℕ × ℤ, fpDistPlus s P x * 1 := by
          refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
          refine ENNReal.ofReal_le_one.mpr ?_
          rw [Set.indicator_apply]; split_ifs <;> norm_num
      _ = 1 := by rw [ENNReal.tsum_mul_right, (fpDistPlus s P).tsum_coe, one_mul]
  have hRHSne : RHS ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hRHSle1
  have hne : (∑' x : ℕ × ℤ, fpDistPlus s P x * g x) ≠ ⊤ := ne_top_of_le_ne_top hRHSne hUB
  rw [ENNReal.le_ofReal_iff_toReal_le hne (by positivity)]
  have hRHSreal : RHS.toReal = ∑' x : ℕ × ℤ, (fpDistPlus s P x).toReal *
      Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} 1 x := by
    rw [hRHSdef]
    exact PMF.toReal_tsum_mul_ofReal (fpDistPlus s P) _
      (fun x => by rw [Set.indicator_apply]; split_ifs <;> norm_num)
  -- final numeric closure: `C(exp(−cD²/(1+s))+exp(−cD)) ≤ m^{−A}/2`.
  have h1s : (1 : ℝ) + (s : ℝ) ≤ 10.6 * (m : ℝ) := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      have : (1 : ℕ) ≤ m := by omega
      exact_mod_cast this
    nlinarith [hsbound, hm1]
  have hexp1 : Real.exp (-c * D ^ 2 / (1 + (s : ℝ)))
      ≤ Real.exp (-(c / 16960) * (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + (s : ℝ)), hDdef]
    nlinarith [mul_nonneg (by linarith [h1s] : (0 : ℝ) ≤ 10.6 * (m : ℝ) - (1 + (s : ℝ)))
      (by positivity : (0 : ℝ) ≤ c * (m : ℝ)), hc.le, hmpos.le]
  have hexp2 : Real.exp (-c * D) ≤ Real.exp (-(c / 16960) * (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [hDdef]; nlinarith [mul_pos hc hmpos]
  have hfinal : C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D))
      ≤ (m : ℝ) ^ (-A) / 2 := by
    have hCne : C ≠ 0 := ne_of_gt hC
    have h3 : (2 : ℝ) * C * ((1 / (4 * C)) * (m : ℝ) ^ (-A)) = (m : ℝ) ^ (-A) / 2 := by
      field_simp; ring
    calc C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D))
        ≤ C * (Real.exp (-(c / 16960) * (m : ℝ)) + Real.exp (-(c / 16960) * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left (add_le_add hexp1 hexp2) hC.le
      _ = 2 * C * Real.exp (-(c / 16960) * (m : ℝ)) := by ring
      _ ≤ 2 * C * ((1 / (4 * C)) * (m : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_left (hNexp m (by omega)) (by positivity)
      _ = (m : ℝ) ^ (-A) / 2 := h3
  calc (∑' x : ℕ × ℤ, fpDistPlus s P x * g x).toReal
      ≤ RHS.toReal := ENNReal.toReal_mono hRHSne hUB
    _ = ∑' x : ℕ × ℤ, (fpDistPlus s P x).toReal *
          Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} 1 x := hRHSreal
    _ ≤ C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D)) := htail s P D hDbound
    _ ≤ (m : ℝ) ^ (-A) / 2 := hfinal

/-- The threshold of `col_tail_mass_le`, symbolic (big-C campaign, step 2):
`400(P+1) + 32 + T_expRpow A (c_fpColTail/16960) (1/(4·C_fpColTail))`. -/
noncomputable def T_colTail (A : ℝ) (P : ℕ) : ℕ :=
  400 * (P + 1) + 32 + T_expRpow A (c_fpColTail / 16960) (1 / (4 * C_fpColTail))

/-- `col_tail_mass_le`, `_at` sibling: `col_tail_mass_le_core` at
(`c_fpColTail`, `C_fpColTail`) and the `T_expRpow` threshold, folded into
`T_colTail A P`. -/
theorem col_tail_mass_le_at (A : ℝ) (hA : 0 < A) (P : ℕ) (hP1 : 1 ≤ P) :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, T_colTail A P ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) / 2) := by
  have h := col_tail_mass_le_core A hA P hP1 c_fpColTail C_fpColTail
    c_fpColTail_pos C_fpColTail_pos fpDistPlus_col_tail_explicitC
    (T_expRpow A (c_fpColTail / 16960) (1 / (4 * C_fpColTail)))
    (exp_neg_mul_le_rpow_neg_at A hA (c_fpColTail / 16960)
      (div_pos c_fpColTail_pos (by norm_num)) (1 / (4 * C_fpColTail))
      (one_div_pos.mpr (mul_pos four_pos C_fpColTail_pos)))
  unfold T_colTail
  exact h

/-- `col_tail_mass_le`, original `∃`-form: delegates to the `_at` sibling at
`T_colTail A P`. -/
theorem col_tail_mass_le (A : ℝ) (hA : 0 < A) (P : ℕ) (hP1 : 1 ≤ P) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) / 2) :=
  ⟨T_colTail A P, col_tail_mass_le_at A hA P hP1⟩

/-- **(7.56) — the few-white mass bound (THE deep leaf).** The renewal walk after first
passage encounters at most `K := ⌈(A+3)·log10/ε³⌉` whites with probability `≤ 10^{−(A+2)}`.
This is where the proved X11c machinery plugs in: `{Nw≤K} ⊆ {reach R} ∪ {E∗}`
(`deterministic_encounter_or_bigTriangle`, `cumWhite=Nw` via `encFold_cumWhite`), and
`P(reach R ∧ Nw≤K) + P(E∗) ≤ 10^{−(A+2)}` via `reaches_fewWhite_mass_le_ten` +
`estar_union_le ∘ bigTriangle_of_encounter`.

**Route (PENDING decomp-3 finding): the base-4 lemmas are used at a SCALED `A' := κ·A`**
(`4^{κA}=(4^κ)^A`, effective base `4^κ ≈ 10^6`) so `P(E∗) ≤ 10^{−(A+3)}`, and
`reaches_fewWhite_mass_le_ten` is applied at `A+2` giving `10^{−(A+3)}`; no reproving. Shared
gate `g` obtained from `reaches_fewWhite_mass_le_ten` and passed into the geometry lemma. -/
theorem few_white_mass_le (A : ℝ) (hA : 0 < A) :
    ∃ P : ℕ, 1 ≤ P ∧ ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (∑ p ∈ Finset.range P,
                Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
              ≤ ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 2)) := by
  classical
  -- the three proved terms of the pointwise split (7.56): E∗, reach-R, bad-column.
  obtain ⟨A', hA'1, Cthr_e, hestar⟩ := few_white_estar_mass_le A hA
  obtain ⟨ε₀, hε₀pos, g, hreach⟩ := few_white_reach_mass_le A
  have hlog10 : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num)
  -- the goal threshold `K`, the horizon `R`, `P`, all functions of `A` (chosen before `∀ n ξ`).
  set K : ℕ := ⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ with hKdef
  set R : ℕ := ⌈(((K : ℝ) + 1) + (A + 5) * Real.log 10 + 2) / ε₀⌉₊ with hRdef
  have hRnum_pos : (0 : ℝ) < ((K : ℝ) + 1) + (A + 5) * Real.log 10 + 2 := by
    have : (0 : ℝ) < (A + 5) * Real.log 10 := mul_pos (by linarith) hlog10
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  have hR1 : 1 ≤ R := by
    rw [hRdef]; exact Nat.ceil_pos.mpr (div_pos hRnum_pos hε₀pos)
  set P : ℕ := encWindowIter A' (K + 1) R with hPdef
  have hP1 : 1 ≤ P := by
    rw [hPdef]
    have h1 : (1 : ℕ) ≤ encWindowIter A' (K + 1) 1 := by
      rw [encWindowIter_succ]
      have : encWindowIter A' (K + 1) 0 = 0 := rfl
      omega
    exact le_trans h1 (encWindowIter_mono A' (K + 1) hR1)
  have hPeq : encWindowIter A' (K + 1) R ≤ P := le_of_eq hPdef.symm
  obtain ⟨Cthr_c, hcol⟩ := col_tail_mass_le A hA P hP1
  set B : ℝ := (4 : ℝ) ^ A' * (1 + (P : ℝ)) ^ 3 with hBdef
  have hBnn : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  refine ⟨P, hP1, max (max Cthr_e Cthr_c) (max (10 * g) (max ⌈B ^ (2.5 : ℝ)⌉₊
    ⌈10 * (500 : ℝ) ^ (1 / A)⌉₊)), ?_⟩
  intro n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  -- extract the five threshold facts from `Cthr ≤ m`.
  have hmCe : Cthr_e ≤ m := by omega
  have hmCc : Cthr_c ≤ m := by omega
  have hm10g : 10 * g ≤ m := by omega
  have hmreg : ⌈B ^ (2.5 : ℝ)⌉₊ ≤ m := by omega
  have hmnum : ⌈10 * (500 : ℝ) ^ (1 / A)⌉₊ ≤ m := by omega
  -- the shared gate bound `g ≤ 0.1 m`.
  have hg : (g : ℝ) ≤ (1 / 10 : ℝ) * (m : ℝ) := by
    have : (10 * g : ℕ) ≤ (m : ℕ) := hm10g
    have hcast : (10 : ℝ) * (g : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
    linarith
  -- the reach-`R` R-bound hypothesis.
  have hRbound : ((K : ℝ) + 1) + (A + 5) * Real.log 10 + 2 ≤ ε₀ * (R : ℝ) := by
    have hce : (((K : ℝ) + 1) + (A + 5) * Real.log 10 + 2) / ε₀ ≤ (R : ℝ) := by
      rw [hRdef]; exact Nat.le_ceil _
    rw [div_le_iff₀ hε₀pos] at hce; linarith
  -- the E∗ regularity hyp `⌊4^{A'}(1+p)³⌋₊ ≤ (m+1)^0.4` for all `p ≤ P`.
  have hreg : ∀ p, p ≤ P →
      ((⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (0.4 : ℝ) := by
    intro p hp
    have hpP : (p : ℝ) ≤ (P : ℝ) := by exact_mod_cast hp
    have hfloor : ((⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊ : ℕ) : ℝ)
        ≤ (4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3 := Nat.floor_le (by positivity)
    have hmono : (4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3 ≤ B := by
      rw [hBdef]
      have hcube : (1 + (p : ℝ)) ^ 3 ≤ (1 + (P : ℝ)) ^ 3 := by gcongr
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
  -- the bad-column numeric: `m^{-A}/2 ≤ 10^{-A-3}` for `m ≥ ⌈10·500^{1/A}⌉₊`.
  have hcolnum : (m : ℝ) ^ (-A) / 2 ≤ (10 : ℝ) ^ (-A - 3) := by
    have hm0 : 0 < m := lt_of_lt_of_le
      (Nat.ceil_pos.mpr (show (0 : ℝ) < 10 * (500 : ℝ) ^ (1 / A) by positivity)) hmnum
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    have hm10ge : (500 : ℝ) ^ (1 / A) ≤ (m : ℝ) / 10 := by
      have hc : ((⌈10 * (500 : ℝ) ^ (1 / A)⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmnum
      have hce : 10 * (500 : ℝ) ^ (1 / A) ≤ ((⌈10 * (500 : ℝ) ^ (1 / A)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      linarith
    have hpow : (500 : ℝ) ≤ ((m : ℝ) / 10) ^ A := by
      have heq : (500 : ℝ) = ((500 : ℝ) ^ (1 / A)) ^ A := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 500), one_div,
          inv_mul_cancel₀ (ne_of_gt hA), Real.rpow_one]
      rw [heq]
      exact Real.rpow_le_rpow (by positivity) hm10ge hA.le
    have hkey : ((m : ℝ) / 10) ^ (-A) ≤ 1 / 500 := by
      rw [Real.rpow_neg (show (0 : ℝ) ≤ (m : ℝ) / 10 by positivity)]
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 500) hpow
      rwa [one_div] at h
    have hmm : (10 : ℝ) * ((m : ℝ) / 10) = (m : ℝ) := by ring
    have hm_eq : (10 : ℝ) ^ (-A) * ((m : ℝ) / 10) ^ (-A) = (m : ℝ) ^ (-A) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity), hmm]
    have h10 : (0 : ℝ) ≤ (10 : ℝ) ^ (-A) := Real.rpow_nonneg (by norm_num) _
    have e2 : (10 : ℝ) ^ (-A - 3) = (10 : ℝ) ^ (-A) * (10 : ℝ) ^ (-3 : ℝ) := by
      rw [← Real.rpow_add (by norm_num), show (-A : ℝ) + (-3 : ℝ) = -A - 3 by ring]
    have e3 : (10 : ℝ) ^ (-3 : ℝ) = 1 / 1000 := by
      rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
    have hstep : (10 : ℝ) ^ (-A) * ((m : ℝ) / 10) ^ (-A)
        ≤ (10 : ℝ) ^ (-A) * (1 / 500) := mul_le_mul_of_nonneg_left hkey h10
    rw [hm_eq] at hstep
    rw [e2, e3]; linarith
  -- abbreviate the three pointwise terms of the split.
  set I1 : (ℕ × ℤ) → (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun e v =>
    ENNReal.ofReal (if R ≤ ((List.ofFn v).foldl (encStep F R g)
          (encInit (n / 2 - m + e.1) (l + e.2))).count
        ∧ ((List.ofFn v).foldl (encStep F R g)
          (encInit (n / 2 - m + e.1) (l + e.2))).cumWhite ≤ K + 1
      then (1 : ℝ) else 0) with hI1
  set I2 : (ℕ × ℤ) → (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun e v =>
    ∑ p ∈ Finset.range (P + 1),
      Set.indicator (bigTriangleSet F ⌊(4 : ℝ) ^ A' * (1 + (p : ℝ)) ^ 3⌋₊)
        (1 : ℕ × ℤ → ℝ≥0∞)
        (n / 2 - m - 1 + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) with hI2
  set I3 : (ℕ × ℤ) → (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun e v =>
    ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
      then (1 : ℝ) else 0) with hI3
  -- the pointwise split, integrated (v∉support ⟹ hold.iid = 0).
  have hle : (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        ENNReal.ofReal (if (∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
            ≤ (K : ℝ) then (1 : ℝ) else 0))
      ≤ ∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ,
          hold.iid P v * (I1 e v + I2 e v + I3 e v) := by
    refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
    refine ENNReal.tsum_le_tsum fun v => ?_
    by_cases hv0 : hold.iid P v = 0
    · simp [hv0]
    · have hvsupp : v ∈ (hold.iid P).support := by rw [PMF.mem_support_iff]; exact hv0
      have hvcoord : ∀ i, v i ∈ hold.support := PMF.iid_support_coord hold P v hvsupp
      exact mul_le_mul_right
        (few_white_pointwise_split F m hmn hpos l g R K A' hA'1 P hPeq hg e v hvcoord) _
  -- linearity: split the integral into the three terms.
  have key : (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ,
        hold.iid P v * (I1 e v + I2 e v + I3 e v))
      = (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I1 e v)
      + (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I2 e v)
      + (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I3 e v) := by
    have inner : ∀ e : ℕ × ℤ, (∑' v : Fin P → ℕ × ℤ, hold.iid P v * (I1 e v + I2 e v + I3 e v))
        = (∑' v : Fin P → ℕ × ℤ, hold.iid P v * I1 e v)
        + (∑' v : Fin P → ℕ × ℤ, hold.iid P v * I2 e v)
        + (∑' v : Fin P → ℕ × ℤ, hold.iid P v * I3 e v) := by
      intro e
      rw [tsum_congr fun v => by rw [mul_add, mul_add], ENNReal.tsum_add, ENNReal.tsum_add]
    rw [tsum_congr fun e => by rw [inner e, mul_add, mul_add], ENNReal.tsum_add, ENNReal.tsum_add]
  refine le_trans hle ?_
  rw [key]
  -- the three terms, each `≤ 10^{−A−3}`.
  have hEle : (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I2 e v)
      ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) := hestar n ξ hξ F m hmCe hmn l hpos t ht hmem s hs hs1 P hreg
  have hRle : (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I1 e v)
      ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) := hreach n ξ hξ F m l R hR1 K P hRbound s
  have hCle : (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I3 e v)
      ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) :=
    le_trans (hcol n ξ hξ F m hmCc hmn l hpos t ht hmem s hs hs1 hs2)
      (ENNReal.ofReal_le_ofReal hcolnum)
  have hnum3 : (10 : ℝ) ^ (-A - 3) + (10 : ℝ) ^ (-A - 3) + (10 : ℝ) ^ (-A - 3)
      ≤ (10 : ℝ) ^ (-A - 2) := by
    have e1 : (10 : ℝ) ^ (-A - 3) = (10 : ℝ) ^ (-A - 2) * (10 : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have h1 : (10 : ℝ) ^ (-1 : ℝ) = 1 / 10 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    have hb : (0 : ℝ) ≤ (10 : ℝ) ^ (-A - 2) := Real.rpow_nonneg (by norm_num) _
    rw [e1, h1]; nlinarith [hb]
  calc (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I1 e v)
        + (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I2 e v)
        + (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v * I3 e v)
      ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) + ENNReal.ofReal ((10 : ℝ) ^ (-A - 3))
          + ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) := add_le_add (add_le_add hRle hEle) hCle
    _ = ENNReal.ofReal ((10 : ℝ) ^ (-A - 3) + (10 : ℝ) ^ (-A - 3) + (10 : ℝ) ^ (-A - 3)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 2)) := ENNReal.ofReal_le_ofReal hnum3

/-- **(7.55) — the pure damping expectation.** After the (7.54) column split it suffices to
bound `E[exp(−ε³Nw)] ≤ 10^{−A−1}`. Proved here from `few_white_mass_le` (7.56) by the paper's
count split `exp(−ε³Nw) ≤ 1_{Nw≤K} + 10^{−(A+3)}` (with `K=⌈(A+3)log10/ε³⌉`, so a white excess
`Nw>K` damps below `10^{−(A+3)}`), then `PMF`-averaging the constant tail (`Σfpdist=Σhold=1`)
and the numeric `10^{−(A+2)} + 10^{−(A+3)} ≤ 10^{−(A+1)}`. -/
theorem damping_expectation_le (A : ℝ) (hA : 0 < A) :
    ∃ P : ℕ, 1 ≤ P ∧ ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
            Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
              (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))))
        ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 1)) := by
  obtain ⟨P, hP1, Cthr, hfew⟩ := few_white_mass_le A hA
  refine ⟨P, hP1, Cthr, ?_⟩
  intro n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hεnn : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  have hεpos : (0 : ℝ) < (epsBW : ℝ) := by
    have h0 : (0 : ℚ) < epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  have hε3pos : (0 : ℝ) < (epsBW : ℝ) ^ 3 := by positivity
  have hε3nn : (0 : ℝ) ≤ (epsBW : ℝ) ^ 3 := hε3pos.le
  -- **(7.55) count split**, pointwise.
  have hpoint : ∀ (e : ℕ × ℤ) (v : Fin P → ℕ × ℤ),
      ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
          Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
            (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))
      ≤ ENNReal.ofReal (if (∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
            ≤ ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ)
          then (1 : ℝ) else 0)
        + ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) := by
    intro e v
    set NwE : ℝ := ∑ p ∈ Finset.range P,
        Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
          (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) with hNwEdef
    have hNw0 : (0 : ℝ) ≤ NwE := by
      rw [hNwEdef]; exact Finset.sum_nonneg fun p _ => Set.indicator_nonneg (fun _ _ => by norm_num) _
    have hind0 : (0 : ℝ) ≤ (if NwE ≤ ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ)
        then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    rw [← ENNReal.ofReal_add hind0 (Real.rpow_nonneg (by norm_num) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases h : NwE ≤ ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ)
    · rw [if_pos h]
      have hle1 : Real.exp (-((epsBW : ℝ) ^ 3) * NwE) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hε3nn hNw0]
      linarith [hle1, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) (-A - 3)]
    · rw [if_neg h]
      have hKge : ((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3
          ≤ ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have hbig : (A + 3) * Real.log 10 < NwE * (epsBW : ℝ) ^ 3 :=
        (div_lt_iff₀ hε3pos).mp (lt_of_le_of_lt hKge (not_le.mp h))
      have hexp : Real.exp (-((epsBW : ℝ) ^ 3) * NwE) ≤ (10 : ℝ) ^ (-A - 3) := by
        rw [show (10 : ℝ) ^ (-A - 3) = Real.exp (Real.log 10 * (-A - 3)) from
          Real.rpow_def_of_pos (by norm_num) _]
        exact Real.exp_le_exp.mpr (by nlinarith [hbig])
      linarith [hexp]
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hpoint e v) _) _) ?_
  -- Split the sum: few-white part + the (PMF-averaged) constant tail.
  have key :
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (ENNReal.ofReal (if (∑ p ∈ Finset.range P,
                Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
              ≤ ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ)
            then (1 : ℝ) else 0)
          + ENNReal.ofReal ((10 : ℝ) ^ (-A - 3))))
      = (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (∑ p ∈ Finset.range P,
                Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
              ≤ ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        + ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) := by
    have inner : ∀ e : ℕ × ℤ,
        (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          (ENNReal.ofReal (if (∑ p ∈ Finset.range P,
                  Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                    (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
                ≤ ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ)
              then (1 : ℝ) else 0)
            + ENNReal.ofReal ((10 : ℝ) ^ (-A - 3))))
        = (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (if (∑ p ∈ Finset.range P,
                  Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                    (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
                ≤ ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ)
              then (1 : ℝ) else 0))
          + ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) := by
      intro e
      rw [tsum_congr fun v => mul_add (hold.iid P v) _ _, ENNReal.tsum_add,
        ENNReal.tsum_mul_right, (hold.iid P).tsum_coe, one_mul]
    rw [tsum_congr fun e => by rw [inner e, mul_add (fpDist s e)], ENNReal.tsum_add,
      ENNReal.tsum_mul_right, (fpDist s).tsum_coe, one_mul]
  rw [key]
  have hfew_app := hfew n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hnum : (10 : ℝ) ^ (-A - 2) + (10 : ℝ) ^ (-A - 3) ≤ (10 : ℝ) ^ (-A - 1) := by
    have hb : (0 : ℝ) ≤ (10 : ℝ) ^ (-A - 1) := Real.rpow_nonneg (by norm_num) _
    have e1 : (10 : ℝ) ^ (-A - 2) = (10 : ℝ) ^ (-A - 1) * (10 : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have e2 : (10 : ℝ) ^ (-A - 3) = (10 : ℝ) ^ (-A - 1) * (10 : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have h1 : (10 : ℝ) ^ (-1 : ℝ) = 1 / 10 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
    have h2 : (10 : ℝ) ^ (-2 : ℝ) = 1 / 100 := by
      rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
    rw [e1, e2, h1, h2]; nlinarith [hb]
  calc (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (∑ p ∈ Finset.range P,
                Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))
              ≤ ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        + ENNReal.ofReal ((10 : ℝ) ^ (-A - 3))
      ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 2)) + ENNReal.ofReal ((10 : ℝ) ^ (-A - 3)) :=
        add_le_add hfew_app le_rfl
    _ = ENNReal.ofReal ((10 : ℝ) ^ (-A - 2) + (10 : ℝ) ^ (-A - 3)) :=
        (ENNReal.ofReal_add (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)).symm
    _ ≤ ENNReal.ofReal ((10 : ℝ) ^ (-A - 1)) := ENNReal.ofReal_le_ofReal hnum

/-- **X11d crux (post-(7.54)) — the damping × column mass estimate.** Once the end
value `Q(end)` has been peeled by (7.54) (`Q_le_Qm`: `Q(end) ≤ max(n/2−j_end,1)^{−A}·Q_{m−1}`)
and the constant `Q_{m−1}` factored out, what remains is this pure first-passage ⊗ Hold-walk
mass bound: the damping factor `exp(−ε³·Nw)` times the column weight `max(n/2−j_end,1)^{−A}`,
integrated against `fpDist s ⊗ hold.iid P`, is `≤ m^{−A}`.

The remaining obligation is the (7.55)–(7.67) numerical closure:
- **damping split by white count** `K=⌈10A/ε³⌉`: on `{Nw>K}` the exp factor is `≤ e^{−10A}`;
- **few-white geometry** `{Nw≤K} ⊆ {reach R} ∪ {E∗}`
  (`deterministic_encounter_or_bigTriangle`, `cumWhite=Nw` via `encFold_cumWhite`), the two
  masses bounded by `reaches_fewWhite_mass_le_ten` and `estar_union_le ∘ bigTriangle_of_encounter`
  (latter at the `j−1` phase shift), with `R=⌈(K+(A+3)log10+2)/ε⌉`;
- the column weight `max(n/2−j_end,1)^{−A} ≤ 10^A` off the bad column `j_end ≥ 0.9m` whose
  mass is `O(e^{−cm})` (`fpDistPlus_col_tail`, `budget_le_of_mem_triangle`).

Horizon `P = deterministic_encounter_or_bigTriangle`'s `P₀`; `Cthr` large enough for the
regime plumbing (⌊4^A(1+p)³⌋ ≤ m^{0.4} for p≤P, X10 deep hyp at `j−1`). -/
theorem damping_column_mass_le (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∃ P : ℕ, 1 ≤ P ∧ ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (
            Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A)) := by
  obtain ⟨P, hP1, Cdamp, hdamp⟩ := damping_expectation_le A hA
  obtain ⟨Ctail, htail⟩ := col_tail_mass_le A hA P hP1
  refine ⟨max (max Cdamp Ctail) 10, P, hP1, ?_⟩
  intro n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hmC : Cdamp ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmT : Ctail ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm10 : 10 ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hm0R : (0 : ℝ) ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg hmR.le _
  have h10A0 : (0 : ℝ) ≤ (10 : ℝ) ^ A := Real.rpow_nonneg (by norm_num) _
  have hC10nn : (0 : ℝ) ≤ (10 : ℝ) ^ A * (m : ℝ) ^ (-A) := mul_nonneg h10A0 hm0R
  -- Constant-collapse `10^A · m^{−A} · 10^{−A−1} = m^{−A}/10`.
  have hconst10 : (10 : ℝ) ^ A * (m : ℝ) ^ (-A) * (10 : ℝ) ^ (-A - 1) = (m : ℝ) ^ (-A) / 10 := by
    have h1 : (10 : ℝ) ^ A * (10 : ℝ) ^ (-A - 1) = (10 : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]; congr 1; ring
    have h2 : (10 : ℝ) ^ (-1 : ℝ) = 1 / 10 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10), Real.rpow_one]; norm_num
    calc (10 : ℝ) ^ A * (m : ℝ) ^ (-A) * (10 : ℝ) ^ (-A - 1)
        = (m : ℝ) ^ (-A) * ((10 : ℝ) ^ A * (10 : ℝ) ^ (-A - 1)) := by ring
      _ = (m : ℝ) ^ (-A) * (1 / 10) := by rw [h1, h2]
      _ = (m : ℝ) ^ (-A) / 10 := by ring
  -- **Step 1 — the pointwise (7.54) column-weight split.**
  have hpoint : ∀ (e : ℕ × ℤ) (v : Fin P → ℕ × ℤ),
      ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
          Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
            (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
        ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A))
      ≤ ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0)
        + ENNReal.ofReal ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
          ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
            Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
              (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))) := by
    intro e v
    set EXPV : ℝ := Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
        Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
          (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) with hEXVdef
    have hEXPV0 : (0 : ℝ) ≤ EXPV := (Real.exp_pos _).le
    have hEXPV1 : EXPV ≤ 1 := by
      rw [hEXVdef, Real.exp_le_one_iff]
      have hsum0 : (0 : ℝ) ≤ ∑ p ∈ Finset.range P,
          Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
            (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2) :=
        Finset.sum_nonneg fun p _ => Set.indicator_nonneg (fun _ _ => by norm_num) _
      have hεnn : (0 : ℝ) ≤ (epsBW : ℝ) := by
        have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
        exact_mod_cast h0
      have hε30 : (0 : ℝ) ≤ (epsBW : ℝ) ^ 3 := by positivity
      nlinarith [hsum0, hε30]
    set WT : ℝ := ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)
      with hWTdef
    have hWT0 : (0 : ℝ) ≤ WT := by rw [hWTdef]; exact Real.rpow_nonneg (by positivity) _
    have hind0 : (0 : ℝ) ≤ (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
        then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    rw [← ENNReal.ofReal_mul hC10nn, ← ENNReal.ofReal_add hind0 (mul_nonneg hC10nn hEXPV0)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hcol : (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
    · rw [if_pos hcol]
      have hWT1 : WT ≤ 1 := by
        rw [hWTdef]
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
        have : (1 : ℕ) ≤ max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 := le_max_right _ _
        exact_mod_cast this
      have hmul : EXPV * WT ≤ 1 := by
        have := mul_le_mul hEXPV1 hWT1 hWT0 (by norm_num : (0 : ℝ) ≤ 1)
        linarith
      nlinarith [hmul, mul_nonneg hC10nn hEXPV0]
    · rw [if_neg hcol]
      have hadvm : e.1 + (pathSum v P).1 < m := by
        have h09 : (0.9 : ℝ) * (m : ℝ) ≤ (m : ℝ) := by nlinarith [hmR.le]
        have : ((e.1 + (pathSum v P).1 : ℕ) : ℝ) < (m : ℝ) :=
          lt_of_lt_of_le (not_le.mp hcol) h09
        exact_mod_cast this
      have hdcol_eq : n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)
          = m - (e.1 + (pathSum v P).1) := by omega
      have hcast : ((n / 2 - (n / 2 - m + e.1 + (pathSum v P).1) : ℕ) : ℝ)
          = (m : ℝ) - ((e.1 + (pathSum v P).1 : ℕ) : ℝ) := by
        rw [hdcol_eq, Nat.cast_sub (le_of_lt hadvm)]
      have hmaxge : (0.1 : ℝ) * (m : ℝ)
          ≤ ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) := by
        have hbase : (0.1 : ℝ) * (m : ℝ)
            ≤ ((n / 2 - (n / 2 - m + e.1 + (pathSum v P).1) : ℕ) : ℝ) := by
          rw [hcast]; have := not_le.mp hcol; linarith
        have hle : ((n / 2 - (n / 2 - m + e.1 + (pathSum v P).1) : ℕ) : ℝ)
            ≤ ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_max_left _ _
        linarith
      have h01m_pos : (0 : ℝ) < 0.1 * (m : ℝ) := by positivity
      have hconstEq : (0.1 * (m : ℝ)) ^ (-A) = (10 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
        rw [Real.mul_rpow (by norm_num) hmR.le]
        congr 1
        rw [show (0.1 : ℝ) = (10 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num) (-A),
          Real.rpow_neg (by norm_num) A, inv_inv]
      have hWTbound : WT ≤ (10 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
        rw [hWTdef, ← hconstEq]
        exact Real.rpow_le_rpow_of_nonpos h01m_pos hmaxge (by linarith)
      calc EXPV * WT ≤ EXPV * ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)) :=
            mul_le_mul_of_nonneg_left hWTbound hEXPV0
        _ = 0 + (10 : ℝ) ^ A * (m : ℝ) ^ (-A) * EXPV := by ring
  -- **Step 2 — apply the pointwise bound under the double sum.**
  refine le_trans (ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hpoint e v) _) _) ?_
  -- **Step 3 — split the sum and factor the constant `10^A·m^{−A}` out of the damping part.**
  have heq :
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
              then (1 : ℝ) else 0)
          + ENNReal.ofReal ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
            ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))))
      = (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        + ENNReal.ofReal ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
          ∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))) := by
    have inner : ∀ e : ℕ × ℤ,
        (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          (ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
                then (1 : ℝ) else 0)
            + ENNReal.ofReal ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
              ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
                Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))))
        = (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
              then (1 : ℝ) else 0))
          + ENNReal.ofReal ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
            ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
              ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
                Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2))) := by
      intro e
      rw [tsum_congr fun v => mul_add (hold.iid P v)
          (ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
          (ENNReal.ofReal ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
            ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))),
        ENNReal.tsum_add]
      congr 1
      rw [tsum_congr fun v => mul_left_comm (hold.iid P v)
          (ENNReal.ofReal ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)))
          (ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
            Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
              (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))),
        ENNReal.tsum_mul_left]
    rw [tsum_congr fun e => by
      rw [inner e, mul_add (fpDist s e)], ENNReal.tsum_add]
    congr 1
    rw [tsum_congr fun e => mul_left_comm (fpDist s e)
        (ENNReal.ofReal ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)))
        (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
            Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
              (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))),
      ENNReal.tsum_mul_left]
  rw [heq]
  -- **Step 4 — bound the two parts by `col_tail_mass_le` and `damping_expectation_le`.**
  have hb1 := htail n ξ hξ F m hmT hmn l hpos t ht hmem s hs hs1 hs2
  have hb2 := hdamp n ξ hξ F m hmC hmn l hpos t ht hmem s hs hs1 hs2
  calc (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (if (0.9 : ℝ) * (m : ℝ) ≤ ((e.1 + (pathSum v P).1 : ℕ) : ℝ)
            then (1 : ℝ) else 0))
        + ENNReal.ofReal ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)) *
          ∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)))
      ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) / 2)
        + ENNReal.ofReal ((10 : ℝ) ^ A * (m : ℝ) ^ (-A)) * ENNReal.ofReal ((10 : ℝ) ^ (-A - 1)) :=
        add_le_add hb1 (mul_le_mul_right hb2 _)
    _ = ENNReal.ofReal ((m : ℝ) ^ (-A) / 2) + ENNReal.ofReal ((m : ℝ) ^ (-A) / 10) := by
        rw [← ENNReal.ofReal_mul hC10nn, hconst10]
    _ ≤ ENNReal.ofReal ((m : ℝ) ^ (-A)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hm0R])

/-- **X11d crux — the damped-walk expectation bound** (paper (7.54)–(7.67)).
This is the pure integral estimate that remains once `Q_le_damped_iter` (7.53) has
converted `Q` at the black edge into a first-passage ⊗ Hold-walk expectation. It states:
for a suitable threshold `Cthr` and horizon `P` (both `A`-explicit, `n`-uniform), the
damped walk expectation over the `P`-step Hold walk after first passage is
`≤ m^{−A}·Q_{m−1}`.

The remaining obligation decomposes (next laps) into the three attack-path pieces:
- **(7.54) column split** — the end value `Q(end)` weight `max(1−j_end/m,1/m)^{−A}` and the
  `O(e^{−cm})` mass of the bad column `j_end ≥ 0.9m` (`fpDistPlus_col_tail`,
  `budget_le_of_mem_triangle`);
- **damping split by white count** `K=⌈10A/ε³⌉`: on `{Nw>K}` the integrand is `≤ e^{−10A}`;
- **few-white geometry** `{Nw≤K} ⊆ {reach R} ∪ {E∗}`
  (`deterministic_encounter_or_bigTriangle`, `encFold_cumWhite`), the two masses bounded by
  `reaches_fewWhite_mass_le_ten` and `estar_union_le ∘ bigTriangle_of_encounter`
  (the latter at the `j−1` phase shift), with `R=⌈(K+(A+3)log10+2)/ε⌉`.

Kept in `ENNReal.ofReal`/tsum form so it composes verbatim with the RHS of
`Q_le_damped_iter` at `half = n/2`, `W = whiteSet n ξ`, `ε = epsBW`, `j = n/2−m`. -/
theorem damped_iter_expectation_le (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∃ P : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (
            Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            Q (n / 2) (whiteSet n ξ) (epsBW : ℝ)
              (n / 2 - m + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)))
        ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) := by
  obtain ⟨Cthr, P, hP1, hmass⟩ := damping_column_mass_le A hA
  refine ⟨Cthr, P, ?_⟩
  intro n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hε0 : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  have hQM0 : (0 : ℝ) ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := Qm_nonneg _ _ _ _ _ _
  -- (7.54) pointwise: peel `Q(end) ≤ max(n/2−j_end,1)^{−A}·Q_{m−1}` and factor `Q_{m−1}` out.
  have step1 :
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (
            Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            Q (n / 2) (whiteSet n ξ) (epsBW : ℝ)
              (n / 2 - m + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)))
        ≤ ∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            (ENNReal.ofReal (Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) *
              ENNReal.ofReal (
                Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
                  Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                    (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
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
        have h := pathSum_fst_ge v hvcoord 0 P (by omega)
        simpa [pathSum_zero] using h
      have h1 : 1 ≤ n / 2 - m + e.1 + (pathSum v P).1 := by omega
      have h2 : n / 2 - (m - 1) ≤ n / 2 - m + e.1 + (pathSum v P).1 := by omega
      have hQle := Q_le_Qm (n / 2) n ξ (epsBW : ℝ) A hA.le hε0 (m - 1)
        (l := l + e.2 + (pathSum v P).2) h1 h2
      have hEXP0 : (0 : ℝ) ≤ Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
          Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
            (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) := (Real.exp_pos _).le
      calc Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            Q (n / 2) (whiteSet n ξ) (epsBW : ℝ)
              (n / 2 - m + e.1 + (pathSum v P).1) (l + e.2 + (pathSum v P).2)
          ≤ Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            (((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A) *
              Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :=
            mul_le_mul_of_nonneg_left hQle hEXP0
        _ = Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) *
            (Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
              ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)) := by ring
  -- factor the constant `ofReal Q_{m−1}` out of the double sum
  have inner_eq : ∀ e : ℕ × ℤ,
      (∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (ENNReal.ofReal (Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) *
          ENNReal.ofReal (
            Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A))))
        = ENNReal.ofReal (Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) *
          ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (
              Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
                Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
              ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)) := by
    intro e
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun v => by rw [mul_left_comm]
  have outer_eq :
      (∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
        (ENNReal.ofReal (Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) *
          ENNReal.ofReal (
            Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A))))
        = ENNReal.ofReal (Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) *
          ∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
            ENNReal.ofReal (
              Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
                Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                  (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
              ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A)) := by
    simp only [inner_eq]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun e => by rw [mul_left_comm]
  refine le_trans step1 ?_
  rw [outer_eq]
  calc ENNReal.ofReal (Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) *
        ∑' e : ℕ × ℤ, fpDist s e * ∑' v : Fin P → ℕ × ℤ, hold.iid P v *
          ENNReal.ofReal (
            Real.exp (-((epsBW : ℝ) ^ 3) * ∑ p ∈ Finset.range P,
              Set.indicator (whiteSet n ξ ∩ {q : ℕ × ℤ | q.1 ≤ n / 2}) 1
                (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)) *
            ((max (n / 2 - (n / 2 - m + e.1 + (pathSum v P).1)) 1 : ℕ) : ℝ) ^ (-A))
      ≤ ENNReal.ofReal (Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) * ENNReal.ofReal ((m : ℝ) ^ (-A)) :=
        mul_le_mul_right (hmass n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2) _
    _ = ENNReal.ofReal ((m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) := by
        rw [← ENNReal.ofReal_mul hQM0]; congr 1; ring

/-- **Case 3 of Proposition 7.8** ((7.53)–(7.67), paper pp.48–49 + Lemmas
7.9/7.10 pp.50–54): deep triangle start, `m/log²m < s ≤ O(m)`.

This is the sole authoritative X11 gate. Everything above it in this module is
checked: the damped iterate (7.53), the iid marginal bridge, the Markov bound,
and the deterministic encounter claim (7.67). The remaining proof obligation
is the finite-union/numerical closure of (7.54)–(7.56), with the single upstream
geometry dependency `fpDist_any_triangle_le` through `many_triangles_white`. -/
theorem Q_black_edge_case3 (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  -- (7.53) entry via `Q_le_damped_iter`, then the crux expectation bound, then strip `ofReal`.
  obtain ⟨Cthr, P, hbound⟩ := damped_iter_expectation_le A hA
  refine ⟨Cthr, ?_⟩
  intro n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hε0 : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  have hentry := Q_le_damped_iter (n / 2) (whiteSet n ξ) (epsBW : ℝ) hε0 s P (n / 2 - m) l
  have hexp := hbound n ξ hξ F m hm hmn l hpos t ht hmem s hs hs1 hs2
  have hchain : ENNReal.ofReal (Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l)
      ≤ ENNReal.ofReal ((m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :=
    le_trans hentry hexp
  have hRHSnn : (0 : ℝ) ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) (Qm_nonneg _ _ _ _ _ _)
  exact (ENNReal.ofReal_le_ofReal_iff hRHSnn).mp hchain

/-- The black-edge case split, now fed by the sole downstream X11 gate. -/
theorem Q_black_edge (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ,
      1 ≤ n / 2 - m → (n / 2 - m, l) ∉ whiteSet n ξ →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) :=
  Q_black_edge_of_case3 A hA (Q_black_edge_case3 A hA)

/-- **Proposition 7.8 (Monotonicity)**, assembled from the black-edge bound. -/
theorem prop_7_8 (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      Qm (n / 2) n ξ (epsBW : ℝ) A m ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) :=
  prop_7_8_of_black_edge A hA (Q_black_edge A hA)

/-- Paper (7.37), assembled from Proposition 7.8. -/
theorem Q_polynomial_decay (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ (j : ℕ) (l : ℤ), 1 ≤ j →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l
        ≤ C * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) :=
  Q_polynomial_decay_of_prop_7_8 A hA (prop_7_8 A hA)

end TaoCollatz
