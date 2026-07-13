import TaoCollatz.Sec7.ManyTriangles

/-!
# §7.4 Case 3 of Proposition 7.8 — the X11 assembly ((7.53)–(7.67), pp.48–49, 54–55)

The deep-triangle branch `m/log²m < s ≤ O(m)` of the black-edge bound
`Q_black_edge_case3` (statement pinned in `BlackEdge.lean`; the PROOF must live
here, downstream of `ManyTriangles.lean`, because it consumes Lemma 7.9
(`many_triangles_white`, X9) and Lemma 7.10 (`triangle_encounter_le`, X10)).

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
3. **(7.56)** `few_whites_le`: `P(Σ_{p<P} 1_W ≤ K) ≤ 10^{−A−2}`, from
   `E∗ ∪ F∗` (the union bound `estar_union_le` over Lemma 7.10, the Markov
   bound `fstar_markov_le` over Lemma 7.9) plus the deterministic claim (7.67)
   `deterministic_encounter_claim`: outside `E∗`, few whites force the
   encounter fold to reach `count ≥ R` within `P` steps, putting the path
   inside `F∗`.

Throughout, the joint law is `e ~ fpDist s` (the `k` first-passage steps)
followed by `v ~ hold.iid T` (the post-passage steps), positions
`(j,l) + e + pathSum v p`; per-`p` marginals are `fpDistPlus s p`
(`iid_pathSum_law`), which is exactly the law Lemma 7.10 speaks about.
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
  rw [pathSum, pathSum, List.take_succ, List.sum_append]
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
      refine mul_le_mul_left' ?_ (hold d)
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
            mul_le_mul_left' hIH _
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
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_left' ?_ _
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

/-! ### The three (7.56) ingredients -/

/-- **The `E∗` union bound** (paper p.54 bottom): summing Lemma 7.10 at
`s' = ⌈4^A(1+p)³⌉` over `0 ≤ p ≤ T` gives `P(E∗) ≤ C·A²·4^{−A}`, provided the
largest threshold still satisfies Lemma 7.10's regime `s' ≤ m^{0.4}` (the
consumer takes `T = O_{A,ε}(1)` fixed and then `m ≥ C_{A,ε}`). The `1/s'` terms
sum via `Σ (1+p)^{−2} ≤ 2`; the exponential terms via a geometric series
dominated by `e^{−cA²(1+p)} ≤ e^{−cA²}·e^{−c(1+p)+c}` and `A ≥ A₀` pushes
`A² e^{−cA²}`-type factors below `4^{−A}` (up to the constant).

OPEN (X11a): assembly of `triangle_encounter_le` (PROVED) through
`iid_pathSum_law`; no new analytic content. -/
theorem estar_union_le :
    ∃ C > (0 : ℝ), ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (A : ℝ), A₀ ≤ A →
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) / Real.log ((n / 2 - j : ℕ) : ℝ) ^ 2 < (s : ℝ) →
      ∀ (T : ℕ),
        ((4 : ℝ) ^ A * (1 + (T : ℝ)) ^ 3 ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ)) →
      ∑ p ∈ Finset.range (T + 1),
        ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal *
          Set.indicator (bigTriangleSet F ⌈(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌉₊)
            (1 : ℕ × ℤ → ℝ) (j + e.1, l + e.2)
      ≤ C * A ^ 2 * (4 : ℝ) ^ (-A) := by
  sorry

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
conditions hold), incrementing the count. -/
theorem deterministic_encounter_claim (n ξ : ℕ) (F : TriangleFamily n ξ)
    (g R K : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ P₀ : ℕ, ∀ T : ℕ, P₀ ≤ T → ∀ q₀ : ℕ × ℤ, 1 ≤ q₀.1 →
      ∀ v : Fin T → ℕ × ℤ, (∀ i, v i ∈ hold.support) →
      -- (i) depth: every visited position is ≥ g-deep in the strip, col ≥ 1
      (∀ p, p ≤ T → (q₀ + pathSum v p).1 + g ≤ n / 2) →
      -- (ii) outside E∗: every covering triangle met at time p is small
      (∀ p, p ≤ T → ∀ t ∈ F.T,
        ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ triangle t.1 t.2.1 t.2.2 →
        t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3) →
      -- (iii) few whites along the path
      ((Finset.range T).sum
        (fun p => if q₀ + pathSum v (p + 1) ∈ whiteStrip n ξ then 1 else 0) ≤ K) →
      R ≤ ((List.ofFn v).foldl (encStep F R g) (encInit q₀.1 q₀.2)).count := by
  sorry

open scoped Classical in
/-- **The (7.56) core**: over the joint law (first passage at budget `s`, then
`T` further Hold steps), the chance that fewer than `K_A := ⌈10·A/epsBW³⌉` of
the `T+1` post-passage positions are white-strip is `≤ 10^{−A−2}`, once
`m ≥ Cthr(A)` (with `T = T(A)` fixed first). Split the failure event into
`E∗` (`estar_union_le`), the fold-reaches-`R` branch (which by
`deterministic_encounter_claim` + `encFold_banked_le` forces
`encVal ≥ e^{εR − K − 1}`, i.e. membership in `F∗`, improbable by
`fstar_markov_le` with `R := ⌈(K + (A+3)·log 10 + 2)/ε⌉`), and the depth
hypothesis failure (contained in the `0.9m` column event, handled by the
CALLER — the depth hypothesis is passed in here as a path property through
the column bound).

OPEN (X11c): the join; consumes `many_triangles_white` (X9) for `hbound`.
NOTE: the failure-probability bookkeeping keeps every event as an explicit
indicator tsum over the joint law; no measure theory (D6). -/
theorem few_whites_le :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (A : ℝ), A₀ ≤ A → ∃ T : ℕ, ∃ Cthr : ℕ,
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ (m : ℕ), Cthr ≤ m → m ≤ n / 2 → ∀ (l : ℤ), 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal * ∑' v : Fin T → ℕ × ℤ,
        (hold.iid T v).toReal *
        (if ((Finset.range (T + 1)).sum (fun p =>
              if (n / 2 - m + e.1 + (pathSum v p).1, l + e.2 + (pathSum v p).2)
                  ∈ whiteStrip n ξ then 1 else 0)
            ≤ ⌈10 * A / (epsBW : ℝ) ^ 3⌉₊)
          ∧ ((pathSum v T).1 + e.1 : ℝ) < 0.9 * m
          then (1 : ℝ) else 0)
      ≤ (10 : ℝ) ^ (-A - 2) := by
  sorry

/-- **Case 3 of Proposition 7.8, assembled** ((7.53)–(7.67), pp.48–49, 54–55):
same statement as `Q_black_edge_case3` (BlackEdge.lean), proved here downstream
of Lemmas 7.9/7.10. Glue plan: `Q_le_damped_iter` at `P := T + 1`; at the end
position apply `Q_le_Qm` (the (7.38) rearrangement); split the resulting
weighted average into (a) the column event `j_{[1,k+P]} ≥ 0.9m` — weight
`≤ m^A`, probability `≤ C_P e^{−cm}` (`fpDistPlus_col_tail` at
`D ≈ 0.05m`, using `s/4 ≤ 0.79(m+2)` from the budget hypothesis) — and (b) its
complement, where the weight is `≤ 10^A` and the damping average is
`≤ e^{−ε³K}·10^A + 10^A·P(few whites)` `≤ 10^{−A−1}` by `few_whites_le`.
Total `≤ m^{−A}·Qm_{m−1}` once `m ≥ Cthr`.

OPEN (X11d): mechanical `ℝ≥0∞`→`ℝ` bookkeeping once X11a–c land. -/
theorem Q_black_edge_case3_assembled (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  sorry

end TaoCollatz
