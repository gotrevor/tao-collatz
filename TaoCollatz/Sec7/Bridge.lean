import TaoCollatz.Sec7.Case3

/-!
# §7.3→§7.4 seam: the (7.36) bridge and Proposition 7.3 (node X5)

Paper anchors: Tao 2019 pp.41–44, (7.25)–(7.36). The b-vector damping expectation
(Prop 7.3's LHS, after the §7.1 reduction) is rewritten through the renewal process:
```
E_{b iid Pascal} exp(-ε³ #{j : b_j = 3, (j, b_{[1,j]}) ∈ W})
  = E ∏_{k≥1} exp(-ε³ 1_W(v_{[1,k]}))          (renewal identity (7.26) ≡ (7.27))
  = E Q(Hold)                                   ((7.28) → (7.36) seam)
  ≪_A n^{-A}                                    (Q_polynomial_decay + Geom(4) tail)
```
**D6 finitization**: the middle object is the column recursion `Rcol` (one Pascal
draw per column, damping only at renewal points `b = 3` landing in `W`), which is
finite by construction. The two seam identities become:
* `bridge_vector` — iid-vector expectation = `Rcol` (induction on the vector length,
  peeling `Fin.cons`);
* `bridge_renewal` — `Rcol j l = ∑' d, hold(d) · Q((j,l)+d)` (induction on `half - j`
  through `hold_tsum_step`, the one-column self-similarity of `Hold`).
Both are validated numerically end-to-end by `tools/check_blueprint.py::check12`
(agreement ~1e-11 incl. amplified damping).

`renewal_white_encounters` (Proposition 7.3, moved here from `Holding.lean`) is then
PROVED from the two bridge identities + `Q_polynomial_decay` + `hold_weight_expect`.
-/

open scoped ENNReal

namespace TaoCollatz

open Classical in
/-- **The column recursion** (D6 form of the paper's (7.28) product, resolved one
Pascal column at a time): from column `j` with prefix sum `l`, draw `b ~ Pascal` for
column `j+1`; a renewal point (`b = 3`) landing in `W` contributes the `exp(-ε³)`
damping. `1` past the strip. -/
noncomputable def Rcol (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) : ℕ → ℤ → ℝ
  | j, l =>
    if half ≤ j then 1
    else ∑' b : ℕ,
      (pascal b).toReal
        * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W then Real.exp (-(ε ^ 3)) else 1)
        * Rcol half W ε (j + 1) (l + b)
  termination_by j _ => half - j
  decreasing_by omega

/-- Prefix sums peel through `Fin.cons`: the head contributes once to every
nonempty prefix. -/
theorem pre_cons {n : ℕ} (a : ℕ) (w : Fin n → ℕ) (m : ℕ) :
    pre (Fin.cons a w) (m + 1) = a + pre w m := by
  unfold pre
  rw [Finset.sum_range_succ']
  have h0 : (if h : 0 < n + 1 then (Fin.cons a w : Fin (n + 1) → ℕ) ⟨0, h⟩ else 0)
      = a := by
    rw [dif_pos (Nat.succ_pos n)]
    rfl
  have hi : ∀ i, (if h : i + 1 < n + 1 then (Fin.cons a w : Fin (n + 1) → ℕ) ⟨i + 1, h⟩
        else 0)
      = if h : i < n then w ⟨i, h⟩ else 0 := by
    intro i
    by_cases h : i < n
    · rw [dif_pos (by omega : i + 1 < n + 1), dif_pos h]
      rfl
    · rw [dif_neg (by omega), dif_neg h]
  rw [h0, Finset.sum_congr rfl fun i _ => hi i]
  exact Nat.add_comm _ _

open Classical in
/-- **Bridge, vector side, generalized** for the induction: from column `j` with
prefix sum `l` and `half - j` remaining columns, the iid Pascal expectation of the
damped `W`-encounter count equals `Rcol`. Induction on the number of remaining
columns, peeling `Fin.cons` through `PMF.expect_iid_succ`. -/
theorem bridge_vector_gen (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (m half j : ℕ) (l : ℤ), half - j = m →
      (PMF.iid pascal m).expect (fun v =>
          Real.exp (-(ε ^ 3) *
            ((Finset.univ.filter fun i : Fin m =>
              v i = 3 ∧ ((j + (i : ℕ) + 1 : ℕ), l + (pre v ((i : ℕ) + 1) : ℤ)) ∈ W).card
              : ℝ)))
        = Rcol half W ε j l := by
  intro m
  induction m with
  | zero =>
    intro half j l hm
    rw [PMF.expect_iid_zero, Rcol, if_pos (by omega : half ≤ j)]
    simp
  | succ m IH =>
    intro half j l hm
    rw [PMF.expect_iid_succ pascal m _ (fun v => (Real.exp_pos _).le)
      (fun v => by
        rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        exact mul_nonneg (pow_nonneg hε 3) (Nat.cast_nonneg _))]
    -- transform the inner expectation at each head draw a
    have hinner : ∀ a : ℕ,
        ((PMF.iid pascal m).expect fun w =>
          Real.exp (-(ε ^ 3) *
            ((Finset.univ.filter fun i : Fin (m + 1) =>
              (Fin.cons a w : Fin (m + 1) → ℕ) i = 3
                ∧ ((j + (i : ℕ) + 1 : ℕ),
                    l + (pre (Fin.cons a w) ((i : ℕ) + 1) : ℤ)) ∈ W).card : ℝ)))
        = (if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W
            then Real.exp (-(ε ^ 3)) else 1)
          * Rcol half W ε (j + 1) (l + (a : ℤ)) := by
      intro a
      rw [← IH half (j + 1) (l + (a : ℤ)) (by omega)]
      -- the count splits: head encounter + shifted tail count
      have hcount : ∀ w : Fin m → ℕ,
          ((Finset.univ.filter fun i : Fin (m + 1) =>
            (Fin.cons a w : Fin (m + 1) → ℕ) i = 3
              ∧ ((j + (i : ℕ) + 1 : ℕ),
                  l + (pre (Fin.cons a w) ((i : ℕ) + 1) : ℤ)) ∈ W).card
          = (if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W then 1 else 0)
            + (Finset.univ.filter fun i : Fin m =>
                w i = 3 ∧ ((j + 1 + (i : ℕ) + 1 : ℕ),
                  (l + (a : ℤ)) + (pre w ((i : ℕ) + 1) : ℤ)) ∈ W).card) := by
        intro w
        rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
        congr 1
        -- (the head term at i = 0 closes definitionally under congr)
        refine Finset.sum_congr rfl fun i _ => ?_
        have h2 : (j + ((i.succ : Fin (m + 1)) : ℕ) + 1 : ℕ)
            = j + 1 + (i : ℕ) + 1 := by
          rw [Fin.val_succ]; omega
        have h3 : l + (pre (Fin.cons a w) (((i.succ : Fin (m + 1)) : ℕ) + 1) : ℤ)
            = (l + (a : ℤ)) + (pre w ((i : ℕ) + 1) : ℤ) := by
          rw [Fin.val_succ, pre_cons]
          push_cast
          ring
        have hiff : ((Fin.cons a w : Fin (m + 1) → ℕ) i.succ = 3
            ∧ ((j + ((i.succ : Fin (m + 1)) : ℕ) + 1 : ℕ),
                l + (pre (Fin.cons a w) (((i.succ : Fin (m + 1)) : ℕ) + 1) : ℤ)) ∈ W)
            ↔ (w i = 3 ∧ ((j + 1 + (i : ℕ) + 1 : ℕ),
                (l + (a : ℤ)) + (pre w ((i : ℕ) + 1) : ℤ)) ∈ W) := by
          rw [show ((Fin.cons a w : Fin (m + 1) → ℕ) i.succ) = w i
            from Fin.cons_succ (α := fun _ => ℕ) a w i, h2, h3]
        exact if_congr hiff rfl rfl
      -- exp of the split count = damping · shifted observable; pull the constant out
      unfold PMF.expect
      dsimp only
      rw [← tsum_mul_left]
      refine tsum_congr fun w => ?_
      rw [hcount w]
      push_cast
      rw [mul_add, Real.exp_add]
      have hhead : Real.exp (-(ε ^ 3) *
            ((if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W then (1 : ℝ) else 0)))
          = (if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W
              then Real.exp (-(ε ^ 3)) else 1) := by
        split_ifs
        · rw [mul_one]
        · rw [mul_zero, Real.exp_zero]
      rw [hhead]
      ring
    rw [tsum_congr fun a => by rw [hinner a]]
    rw [Rcol, if_neg (by omega : ¬ half ≤ j)]
    exact tsum_congr fun a => (mul_assoc _ _ _).symm

open Classical in
/-- **Bridge, vector side** (the (7.26)/(7.28) rewriting, D6 form): the iid Pascal
vector expectation of the damped white-encounter count equals the column recursion.
PROVED (X5): instance of `bridge_vector_gen` at `(m, j, l) = (n/2, 0, 0)`, with the
`whiteSet` membership unfolding to the 0-based `white` test. -/
theorem bridge_vector (n ξ : ℕ) :
    (PMF.iid pascal (n / 2)).expect (fun b =>
        Real.exp (-((epsBW : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)))
      = Rcol (n / 2) (whiteSet n ξ) (epsBW : ℝ) 0 0 := by
  classical
  have hε : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  rw [← bridge_vector_gen (whiteSet n ξ) (epsBW : ℝ) hε (n / 2) (n / 2) 0 0
    (by omega)]
  refine congrArg _ (funext fun v => ?_)
  have hcard : (Finset.univ.filter fun i : Fin (n / 2) =>
        v i = 3 ∧ white n ξ (i : ℕ) ((pre v ((i : ℕ) + 1) : ℤ))).card
      = (Finset.univ.filter fun i : Fin (n / 2) =>
        v i = 3 ∧ ((0 + (i : ℕ) + 1 : ℕ),
          (0 : ℤ) + (pre v ((i : ℕ) + 1) : ℤ)) ∈ whiteSet n ξ).card := by
    refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
    refine and_congr_right fun _ => ?_
    rw [show (0 : ℤ) + (pre v ((i : ℕ) + 1) : ℤ) = (pre v ((i : ℕ) + 1) : ℤ)
      from zero_add _]
    unfold whiteSet
    rw [Set.mem_setOf_eq, show (0 + (i : ℕ) + 1) - 1 = (i : ℕ) from by omega]
    constructor
    · exact fun h => ⟨by omega, h⟩
    · exact fun h => h.2
  rw [hcard]

/-- Generic expansion of a `hold`-expectation through the `bind`/`map` structure. -/
theorem hold_tsum_expand (G : ℕ × ℤ → ℝ≥0∞) :
    ∑' d : ℕ × ℤ, hold d * G d
      = ∑' k : ℕ, geomQuarter k * ∑' v : Fin (k - 1) → ℕ,
          (pascalNe3.iid (k - 1)) v * G (k, (3 : ℤ) + ∑ i, (v i : ℤ)) := by
  rw [hold, PMF.tsum_bind_mul]
  exact tsum_congr fun k => by rw [PMF.tsum_map_mul]

/-- One-column self-similarity of `Hold` (paper (7.29), tsum form over `ℝ≥0∞`):
a `Hold` draw is `(1,3)` with probability `1/4` (the first column is already a
renewal), else the first column contributes `(1, b)` with `b ~ Pascal` conditioned
`≠ 3` and the draw restarts. The `b ≠ 3` Pascal mass is `(3/4)·pascalNe3` exactly.
PROVED: split the `geomQuarter` draw at `k = 1` (memorylessness
`geomQuarter (k+2) = (3/4)·geomQuarter (k+1)`) and peel the first `pascalNe3`
increment off `PMF.iid` (`PMF.tsum_iid_succ_mul`). -/
theorem hold_tsum_step (g : ℕ × ℤ → ℝ≥0∞) :
    ∑' d : ℕ × ℤ, hold d * g d
      = 4⁻¹ * g (1, 3)
        + ∑' b : ℕ, (if b = 3 then 0 else pascal b)
            * ∑' d : ℕ × ℤ, hold d * g (d.1 + 1, d.2 + b) := by
  classical
  have hgq1 : geomQuarter 1 = 4⁻¹ := by
    show (if (1 : ℕ) = 0 then (0 : ℝ≥0∞) else 4⁻¹ * (3 * 4⁻¹) ^ (1 - 1)) = 4⁻¹
    norm_num
  have hgqs : ∀ k : ℕ, geomQuarter (k + 2) = 3 * 4⁻¹ * geomQuarter (k + 1) := by
    intro k
    show (if k + 2 = 0 then (0 : ℝ≥0∞) else 4⁻¹ * (3 * 4⁻¹) ^ (k + 2 - 1))
      = 3 * 4⁻¹ * (if k + 1 = 0 then (0 : ℝ≥0∞) else 4⁻¹ * (3 * 4⁻¹) ^ (k + 1 - 1))
    rw [if_neg (by omega), if_neg (by omega),
      show k + 2 - 1 = (k + 1 - 1) + 1 from by omega, pow_succ]
    ring
  have hpas : ∀ b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pascal b)
      = 3 * 4⁻¹ * pascalNe3 b := by
    intro b
    have h1 : pascal b = if b < 2 then 0 else ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b := rfl
    have h2 : pascalNe3 b = if b < 2 ∨ b = 3 then 0
        else 4 / 3 * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b) := rfl
    rw [h1, h2]
    by_cases hb3 : b = 3
    · simp [hb3]
    · by_cases hb2 : b < 2
      · simp [hb2, hb3]
      · rw [if_neg hb3, if_neg hb2, if_neg (by tauto)]
        have hone : (3 : ℝ≥0∞) * 4⁻¹ * (4 / 3) = 1 := by
          rw [div_eq_mul_inv,
            show (3 : ℝ≥0∞) * 4⁻¹ * (4 * 3⁻¹) = 3 * 3⁻¹ * (4⁻¹ * 4) from by ring,
            ENNReal.mul_inv_cancel (by norm_num) (by finiteness),
            ENNReal.inv_mul_cancel (by norm_num) (by finiteness), one_mul]
        calc ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b
            = 3 * 4⁻¹ * (4 / 3) * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b) := by
              rw [hone, one_mul]
          _ = 3 * 4⁻¹ * (4 / 3 * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b)) := by ring
  -- LHS: expand hold, peel k = 1 and k ≥ 2
  have hL1 : ∑' d : ℕ × ℤ, hold d * g d
      = 4⁻¹ * g (1, 3)
        + ∑' k : ℕ, geomQuarter (k + 2) * ∑' v : Fin (k + 1) → ℕ,
            (pascalNe3.iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, (v i : ℤ)) := by
    rw [hold_tsum_expand g, tsum_eq_zero_add' ENNReal.summable,
      show geomQuarter 0 = 0 from rfl, zero_mul, zero_add,
      tsum_eq_zero_add' ENNReal.summable]
    congr 1
    · rw [hgq1]
      congr 1
      exact (PMF.tsum_iid_zero_mul pascalNe3
        (fun v => g (1, (3 : ℤ) + ∑ i, (v i : ℤ)))).trans (by simp)
  -- RHS inner sums, in the same normal form
  have hR : ∀ b : ℕ, ∑' d : ℕ × ℤ, hold d * g (d.1 + 1, d.2 + (b : ℤ))
      = ∑' k : ℕ, geomQuarter (k + 1) * ∑' w : Fin k → ℕ,
          (pascalNe3.iid k) w * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (b : ℤ)) := by
    intro b
    rw [hold_tsum_expand fun d => g (d.1 + 1, d.2 + (b : ℤ)),
      tsum_eq_zero_add' ENNReal.summable,
      show geomQuarter 0 = 0 from rfl, zero_mul, zero_add]
    rfl
  -- the tail of hL1 equals the b-sum of hR through one iid-peel + Fubini
  have hL2 : ∑' k : ℕ, geomQuarter (k + 2) * ∑' v : Fin (k + 1) → ℕ,
        (pascalNe3.iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, (v i : ℤ))
      = ∑' b : ℕ, 3 * 4⁻¹ * pascalNe3 b
          * ∑' k : ℕ, geomQuarter (k + 1) * ∑' w : Fin k → ℕ,
              (pascalNe3.iid k) w
                * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (b : ℤ)) := by
    have hpeel : ∀ k : ℕ, ∑' v : Fin (k + 1) → ℕ,
          (pascalNe3.iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, (v i : ℤ))
        = ∑' a : ℕ, pascalNe3 a * ∑' w : Fin k → ℕ,
            (pascalNe3.iid k) w
              * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (a : ℤ)) := by
      intro k
      rw [PMF.tsum_iid_succ_mul pascalNe3 k
        (fun v => g (k + 2, (3 : ℤ) + ∑ i, (v i : ℤ)))]
      refine tsum_congr fun a => ?_
      congr 1
      refine tsum_congr fun w => ?_
      congr 1
      rw [show ((3 : ℤ) + ∑ i : Fin (k + 1), ((Fin.cons a w : Fin (k + 1) → ℕ) i : ℤ))
          = (3 : ℤ) + (∑ i, (w i : ℤ)) + (a : ℤ) from by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        ring]
    calc ∑' k : ℕ, geomQuarter (k + 2) * ∑' v : Fin (k + 1) → ℕ,
          (pascalNe3.iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, (v i : ℤ))
        = ∑' k : ℕ, ∑' a : ℕ, 3 * 4⁻¹ * pascalNe3 a
            * (geomQuarter (k + 1) * ∑' w : Fin k → ℕ,
                (pascalNe3.iid k) w
                  * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (a : ℤ))) := by
          refine tsum_congr fun k => ?_
          rw [hpeel k, hgqs k, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun a => by ring
      _ = ∑' a : ℕ, ∑' k : ℕ, 3 * 4⁻¹ * pascalNe3 a
            * (geomQuarter (k + 1) * ∑' w : Fin k → ℕ,
                (pascalNe3.iid k) w
                  * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (a : ℤ))) :=
          ENNReal.tsum_comm
      _ = ∑' a : ℕ, 3 * 4⁻¹ * pascalNe3 a
            * ∑' k : ℕ, geomQuarter (k + 1) * ∑' w : Fin k → ℕ,
                (pascalNe3.iid k) w
                  * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (a : ℤ)) :=
          tsum_congr fun a => ENNReal.tsum_mul_left
  rw [hL1, hL2]
  congr 1
  exact tsum_congr fun b => by rw [hpas b, hR b]

/-- Real-valued corollary of `hold_tsum_step` for `[0,1]`-valued observables (all the
`toReal` bookkeeping done once; the `ℝ≥0∞` sums are finite because `f ≤ 1`). -/
theorem hold_tsum_step_real (f : ℕ × ℤ → ℝ) (hf0 : ∀ d, 0 ≤ f d) (hf1 : ∀ d, f d ≤ 1) :
    ∑' d : ℕ × ℤ, (hold d).toReal * f d
      = 4⁻¹ * f (1, 3)
        + ∑' b : ℕ, (if b = 3 then 0 else (pascal b).toReal)
            * ∑' d : ℕ × ℤ, (hold d).toReal * f (d.1 + 1, d.2 + b) := by
  classical
  have hstep := hold_tsum_step fun d => ENNReal.ofReal (f d)
  -- toReal of a hold-weighted ofReal-sum is the corresponding real sum
  have hcv : ∀ F : ℕ × ℤ → ℕ × ℤ,
      (∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (F d))).toReal
        = ∑' d : ℕ × ℤ, (hold d).toReal * f (F d) := by
    intro F
    rw [ENNReal.tsum_toReal_eq
      (fun d => ENNReal.mul_ne_top (hold.apply_ne_top d) ENNReal.ofReal_ne_top)]
    exact tsum_congr fun d => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf0 _)]
  have hcv0 : (∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f d)).toReal
      = ∑' d : ℕ × ℤ, (hold d).toReal * f d := hcv id
  have hcvb : ∀ b : ℕ,
      (∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))).toReal
        = ∑' d : ℕ × ℤ, (hold d).toReal * f (d.1 + 1, d.2 + (b : ℤ)) :=
    fun b => hcv fun d => (d.1 + 1, d.2 + (b : ℤ))
  -- the shifted inner sums are ≤ 1, hence finite
  have hTle : ∀ b : ℕ,
      ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ))) ≤ 1 := by
    intro b
    calc ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))
        ≤ ∑' d : ℕ × ℤ, hold d * 1 :=
          ENNReal.tsum_le_tsum fun d => mul_le_mul_right
            (ENNReal.ofReal_le_one.mpr (hf1 _)) _
      _ = 1 := by rw [tsum_congr fun d => mul_one (hold d), hold.tsum_coe]
  have hcb : ∀ b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pascal b) ≤ pascal b := by
    intro b; split_ifs <;> simp
  have htail_ne : (∑' b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pascal b)
      * ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))) ≠ ∞ := by
    refine ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) ?_
    calc ∑' b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pascal b)
          * ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))
        ≤ ∑' b : ℕ, pascal b * 1 :=
          ENNReal.tsum_le_tsum fun b => mul_le_mul' (hcb b) (hTle b)
      _ = 1 := by rw [tsum_congr fun b => mul_one (pascal b), pascal.tsum_coe]
  -- take toReal of hstep
  have h := congrArg ENNReal.toReal hstep
  rw [hcv0, ENNReal.toReal_add
      (ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top) htail_ne,
    ENNReal.toReal_mul, ENNReal.tsum_toReal_eq (fun b => ENNReal.mul_ne_top
      (ne_top_of_le_ne_top (PMF.apply_ne_top _ _) (hcb b))
      (ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) (hTle b)))] at h
  rw [h, ENNReal.toReal_ofReal (hf0 _)]
  congr 1
  · norm_num [ENNReal.toReal_inv]
  · refine tsum_congr fun b => ?_
    rw [ENNReal.toReal_mul, hcvb b]
    congr 1
    split_ifs <;> simp

/-- **Bridge, renewal side** ((7.27) ≡ (7.28), D6 form): the column recursion equals
the holding-jump average of `Q` — the walk from `(j,l)` to its first renewal point is
one `Hold` draw, and `Q` at that point self-applies the damping (`Q_rec`).
PROVED (X5): downward induction on `half - j`; the inductive step is
`hold_tsum_step_real` matched against `Rcol`'s one-column unfolding and `Q_rec` at the
renewal landing `b = 3`; boundary `half ≤ j` pushes every `hold`-atom past the strip. -/
theorem bridge_renewal (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) (l : ℤ) :
    Rcol half W ε j l
      = ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2) := by
  classical
  -- uniform facts about the hold-averaged Q sums
  have hQ0 := Q_nonneg half W ε
  have hQ1 := Q_le_one half W ε hε
  have hSterm : ∀ (j' : ℕ) (l' : ℤ) (d : ℕ × ℤ),
      (hold d).toReal * Q half W ε (j' + d.1) (l' + d.2) ≤ (hold d).toReal := by
    intro j' l' d
    calc (hold d).toReal * Q half W ε (j' + d.1) (l' + d.2)
        ≤ (hold d).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hQ1 _ _) ENNReal.toReal_nonneg
      _ = (hold d).toReal := mul_one _
  have hSnn : ∀ (j' : ℕ) (l' : ℤ) (d : ℕ × ℤ),
      0 ≤ (hold d).toReal * Q half W ε (j' + d.1) (l' + d.2) :=
    fun j' l' d => mul_nonneg ENNReal.toReal_nonneg (hQ0 _ _)
  have hSsum : ∀ (j' : ℕ) (l' : ℤ),
      Summable fun d : ℕ × ℤ => (hold d).toReal * Q half W ε (j' + d.1) (l' + d.2) :=
    fun j' l' => Summable.of_nonneg_of_le (hSnn j' l') (hSterm j' l') hold_summable_toReal
  have hSle : ∀ (j' : ℕ) (l' : ℤ),
      ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j' + d.1) (l' + d.2) ≤ 1 :=
    fun j' l' => le_trans
      ((hSsum j' l').tsum_le_tsum (hSterm j' l') hold_summable_toReal)
      hold_tsum_toReal.le
  have hSnn' : ∀ (j' : ℕ) (l' : ℤ),
      0 ≤ ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j' + d.1) (l' + d.2) :=
    fun j' l' => tsum_nonneg (hSnn j' l')
  have hp3 : (pascal 3).toReal = 4⁻¹ := by
    have h3 : pascal 3 = ((2 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 3 := rfl
    rw [h3, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
    norm_num
  have hdamp01 : ∀ (P : Prop) [Decidable P],
      0 ≤ (if P then Real.exp (-(ε ^ 3)) else 1)
        ∧ (if P then Real.exp (-(ε ^ 3)) else 1) ≤ 1 := by
    intro P _
    constructor
    · split_ifs <;> [exact (Real.exp_pos _).le; exact zero_le_one]
    · split_ifs
      · rw [Real.exp_le_one_iff, neg_nonpos]; positivity
      · exact le_refl 1
  -- main downward induction on half - j
  have key : ∀ n j l, half - j = n → Rcol half W ε j l
      = ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro j l hn
      rcases Nat.lt_or_ge j half with hj | hj
      · -- interior: j < half
        rw [Rcol, if_neg (by omega : ¬ half ≤ j)]
        -- rewrite each Rcol (j+1) (l+b) via the inductive hypothesis
        have hIH : ∀ b : ℕ, Rcol half W ε (j + 1) (l + (b : ℤ))
            = ∑' d : ℕ × ℤ, (hold d).toReal
                * Q half W ε (j + 1 + d.1) (l + (b : ℤ) + d.2) :=
          fun b => IH (half - (j + 1)) (by omega) _ _ rfl
        -- the real self-similarity at f d := Q (j + d.1) (l + d.2)
        have hfr := hold_tsum_step_real
          (fun d => Q half W ε (j + d.1) (l + d.2))
          (fun d => hQ0 _ _) (fun d => hQ1 _ _)
        rw [hfr]
        -- LHS: split off the b = 3 renewal landing
        have hterm_eq : ∀ b : ℕ,
            (pascal b).toReal
              * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W
                  then Real.exp (-(ε ^ 3)) else 1)
              * Rcol half W ε (j + 1) (l + (b : ℤ))
            = (pascal b).toReal
              * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W
                  then Real.exp (-(ε ^ 3)) else 1)
              * ∑' d : ℕ × ℤ, (hold d).toReal
                  * Q half W ε (j + 1 + d.1) (l + (b : ℤ) + d.2) :=
          fun b => by rw [hIH b]
        rw [tsum_congr hterm_eq]
        have hsummable : Summable fun b : ℕ =>
            (pascal b).toReal
              * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W
                  then Real.exp (-(ε ^ 3)) else 1)
              * ∑' d : ℕ × ℤ, (hold d).toReal
                  * Q half W ε (j + 1 + d.1) (l + (b : ℤ) + d.2) := by
          refine Summable.of_nonneg_of_le
            (fun b => mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (hdamp01 _).1)
              (hSnn' _ _))
            (fun b => ?_)
            (ENNReal.summable_toReal pascal.tsum_coe_ne_top)
          calc (pascal b).toReal * _ * _
              ≤ (pascal b).toReal * 1 * 1 :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hdamp01 _).2
                  ENNReal.toReal_nonneg) (hSle _ _) (hSnn' _ _)
                  (by positivity)
            _ = (pascal b).toReal := by ring
        rw [hsummable.tsum_eq_add_tsum_ite 3]
        congr 1
        · -- the b = 3 head equals 4⁻¹ · Q (j+1) (l+3) via Q_rec
          simp only [Nat.cast_ofNat]
          have hrec := Q_rec half W ε (j + 1) (l + 3) (by omega)
          by_cases hW : ((j + 1 : ℕ), l + (3 : ℤ)) ∈ W
          · rw [hp3, if_pos ⟨trivial, hW⟩, hrec, Set.indicator_of_mem hW,
              Pi.one_apply, mul_one, mul_assoc]
          · rw [hp3, if_neg (fun h => hW h.2), hrec, Set.indicator_of_notMem hW,
              mul_zero, Real.exp_zero, one_mul, mul_assoc, one_mul]
        · -- the b ≠ 3 tail matches the hold_tsum_step_real tail
          refine tsum_congr fun b => ?_
          by_cases hb3 : b = 3
          · rw [if_pos hb3, if_pos hb3, zero_mul]
          · rw [if_neg hb3, if_neg hb3,
              if_neg (fun h => hb3 h.1), mul_one]
            congr 1
            refine tsum_congr fun d => ?_
            congr 2
            · omega
            · ring
      · -- boundary: half ≤ j — every hold-atom exits the strip
        rw [Rcol, if_pos hj]
        symm
        calc ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2)
            = ∑' d : ℕ × ℤ, (hold d).toReal := by
              refine tsum_congr fun d => ?_
              rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
              · rw [hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul]
              · rw [Q_boundary _ _ _ _ _ (by omega), mul_one]
          _ = 1 := hold_tsum_toReal
  exact key _ j l rfl

/-- **The Proposition 7.3 constant**, symbolic (big-C campaign, step 2): the
`renewal_white_encounters` witness `max (n₀^A) (C0·e^{ε³/2}·3^A)` at
`n₀ = 2·C_hold A + 2`, `C0 = C_polyDecay A`. ⚠️ C0-arm dominated — see check19 /
the lap-8 JUDGE-FLAG in PENDING_WORK.md. -/
noncomputable def C_renewalWhite (A : ℝ) : ℝ :=
  max (((2 * C_hold A + 2 : ℕ) : ℝ) ^ A)
    (C_polyDecay A * Real.exp ((epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A)

theorem C_renewalWhite_pos (A : ℝ) : 0 < C_renewalWhite A := by
  unfold C_renewalWhite
  exact lt_max_iff.mpr (Or.inl (Real.rpow_pos_of_pos (by positivity) A))

open Classical in
/-- **Proposition 7.3** (finitized, D6 form; moved from `Holding.lean` 2026-07-10):
the expected damping factor `exp(-ε³ · #white encounters)` over the paired valuation
vector `b ~ Pascal^{⌊n/2⌋}` decays super-polynomially: `≤ C·n^{-A}` for every `A`.
PROVED from `bridge_vector` + `bridge_renewal` (the two open X5 seams) +
`Q_polynomial_decay` + `hold_weight_expect`.

`_at` sibling (big-C campaign, step 2): the two `obtain`s replaced by the explicit
siblings, constant names re-bound via `set`, body verbatim. -/
theorem renewal_white_encounters_at (A : ℝ) (hA : 0 < A) :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → 1 ≤ n →
      (PMF.iid pascal (n / 2)).expect (fun b =>
        Real.exp (-((epsBW : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)))
        ≤ C_renewalWhite A * (n : ℝ) ^ (-A) := by
  have hC00 : (0 : ℝ) < C_polyDecay A := C_polyDecay_pos A
  have hC0 := Q_polynomial_decay_explicitC A hA
  have hC11 : 1 ≤ C_hold A := one_le_C_hold A
  have hC1 := hold_weight_expect_explicitC A hA
  unfold C_renewalWhite
  set C0 : ℝ := C_polyDecay A with hC0def
  set C1 : ℕ := C_hold A with hC1def
  -- constants: below n₀ := 2·C1 + 2 use the trivial bound E ≤ 1 ≤ n₀^A·n^{-A};
  -- above, the chain gives C0·exp(ε³/2)·3^A·n^{-A}.
  set n0 : ℕ := 2 * C1 + 2 with hn0
  intro n ξ hξ hn
  have hε0 : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- the expectation is ≤ 1 always (damping factors ≤ 1, mass 1)
  have hE1 : (PMF.iid pascal (n / 2)).expect (fun b =>
      Real.exp (-((epsBW : ℝ) ^ 3) *
        ((Finset.univ.filter fun j : Fin (n / 2) =>
          b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ))) ≤ 1 := by
    unfold PMF.expect
    have hterm : ∀ b : Fin (n / 2) → ℕ,
        ((PMF.iid pascal (n / 2)) b).toReal *
          Real.exp (-((epsBW : ℝ) ^ 3) *
            ((Finset.univ.filter fun j : Fin (n / 2) =>
              b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ))
          ≤ ((PMF.iid pascal (n / 2)) b).toReal := by
      intro b
      have hle1 : Real.exp (-((epsBW : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        positivity
      calc ((PMF.iid pascal (n / 2)) b).toReal * _ ≤ _ * 1 :=
            mul_le_mul_of_nonneg_left hle1 ENNReal.toReal_nonneg
        _ = ((PMF.iid pascal (n / 2)) b).toReal := mul_one _
    have hsum : Summable fun b : Fin (n / 2) → ℕ => ((PMF.iid pascal (n / 2)) b).toReal :=
      ENNReal.summable_toReal (PMF.iid pascal (n / 2)).tsum_coe_ne_top
    have hsumf : Summable fun b : Fin (n / 2) → ℕ =>
        ((PMF.iid pascal (n / 2)) b).toReal *
          Real.exp (-((epsBW : ℝ) ^ 3) *
            ((Finset.univ.filter fun j : Fin (n / 2) =>
              b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)) :=
      Summable.of_nonneg_of_le
        (fun b => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hterm hsum
    calc ∑' b, ((PMF.iid pascal (n / 2)) b).toReal * _
        ≤ ∑' b, ((PMF.iid pascal (n / 2)) b).toReal := hsumf.tsum_le_tsum hterm hsum
      _ = 1 := by
          rw [← ENNReal.tsum_toReal_eq (fun b => ((PMF.iid pascal (n / 2)).apply_ne_top b)),
            (PMF.iid pascal (n / 2)).tsum_coe, ENNReal.toReal_one]
  rcases lt_or_ge n n0 with hsmall | hbig
  · -- small n: trivial bound
    calc (PMF.iid pascal (n / 2)).expect _ ≤ 1 := hE1
      _ ≤ (n0 : ℝ) ^ A * (n : ℝ) ^ (-A) := by
          have h1 : (n : ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hsmall.le
          have h2 : (1 : ℝ) = (n : ℝ) ^ A * (n : ℝ) ^ (-A) := by
            rw [← Real.rpow_add hn0R, add_neg_cancel, Real.rpow_zero]
          rw [h2]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hn0R.le h1 hA.le) (Real.rpow_nonneg hn0R.le _)
      _ ≤ max ((n0 : ℝ) ^ A) (C0 * Real.exp ((epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A)
            * (n : ℝ) ^ (-A) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hn0R.le _)
  · -- large n: bridge + polynomial decay + Geom(4) tail
    have hhalf1 : C1 ≤ n / 2 := by omega
    have hhalfpos : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by
      have h : 1 ≤ n / 2 := le_trans hC11 hhalf1
      exact_mod_cast h
    -- Step 1: the two bridges
    rw [bridge_vector n ξ, bridge_renewal (n / 2) (whiteSet n ξ) (epsBW : ℝ) hε0 0 0]
    -- Step 2: Q_polynomial_decay pointwise (hold-support has d₁ ≥ 1)
    have hpt : ∀ d : ℕ × ℤ,
        (hold d).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (0 + d.1) (0 + d.2)
          ≤ (hold d).toReal * (C0 * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)) := by
      intro d
      rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
      · rw [hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul, zero_mul]
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have h := hC0 n ξ hξ (0 + d.1) (0 + d.2) (by omega)
        simpa using h
    have hnn : ∀ d : ℕ × ℤ,
        0 ≤ (hold d).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (0 + d.1) (0 + d.2) :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (Q_nonneg _ _ _ _ _)
    have hwle : ∀ d : ℕ × ℤ, ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 := fun d =>
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast Nat.le_max_right (n / 2 - d.1) 1) (by linarith)
    have hsumw : Summable fun d : ℕ × ℤ =>
        (hold d).toReal * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (fun d => by
          calc (hold d).toReal * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)
              ≤ (hold d).toReal * 1 :=
                mul_le_mul_of_nonneg_left (hwle d) ENNReal.toReal_nonneg
            _ = (hold d).toReal := mul_one _)
        hold_summable_toReal
    have hsumCw : Summable fun d : ℕ × ℤ =>
        (hold d).toReal * (C0 * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
      (hsumw.mul_left C0).congr fun d => by ring
    have hsumQ : Summable fun d : ℕ × ℤ =>
        (hold d).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (0 + d.1) (0 + d.2) :=
      Summable.of_nonneg_of_le hnn
        (fun d => by
          calc (hold d).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (0 + d.1) (0 + d.2)
              ≤ (hold d).toReal * 1 :=
                mul_le_mul_of_nonneg_left (Q_le_one _ _ _ hε0 _ _) ENNReal.toReal_nonneg
            _ = (hold d).toReal := mul_one _)
        hold_summable_toReal
    -- Step 3: the Geom(4)-tail expectation (hold_weight_expect at m := n/2)
    have htail := hC1 (n / 2) hhalf1
    -- assemble
    calc ∑' d : ℕ × ℤ,
          (hold d).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (0 + d.1) (0 + d.2)
        ≤ ∑' d : ℕ × ℤ,
            (hold d).toReal * (C0 * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
          hsumQ.tsum_le_tsum hpt hsumCw
      _ = C0 * ∑' d : ℕ × ℤ,
            (hold d).toReal * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A) := by
          rw [← tsum_mul_left]
          exact tsum_congr fun d => by ring
      _ ≤ C0 * (Real.exp ((epsBW : ℝ) ^ 3 / 2) * ((n / 2 : ℕ) : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_left htail hC00.le
      _ ≤ C0 * Real.exp ((epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A * (n : ℝ) ^ (-A) := by
          -- (n/2)^{-A} ≤ 3^A · n^{-A} since n ≤ 3·(n/2) for n ≥ 2
          have h3 : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
            have h : n ≤ 3 * (n / 2) := by omega
            exact_mod_cast h
          have hstep : ((n / 2 : ℕ) : ℝ) ^ (-A) ≤ (3 : ℝ) ^ A * (n : ℝ) ^ (-A) := by
            have h1 : (n : ℝ) ^ (-A) ≥ (3 * ((n / 2 : ℕ) : ℝ)) ^ (-A) :=
              Real.rpow_le_rpow_of_nonpos hn0R h3 (by linarith)
            have h2 : (3 * ((n / 2 : ℕ) : ℝ)) ^ (-A)
                = (3 : ℝ) ^ (-A) * ((n / 2 : ℕ) : ℝ) ^ (-A) :=
              Real.mul_rpow (by norm_num) hhalfpos.le
            have h4 : ((n / 2 : ℕ) : ℝ) ^ (-A)
                = (3 : ℝ) ^ A * ((3 : ℝ) ^ (-A) * ((n / 2 : ℕ) : ℝ) ^ (-A)) := by
              rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 3),
                add_neg_cancel, Real.rpow_zero, one_mul]
            rw [h4]
            calc (3 : ℝ) ^ A * ((3 : ℝ) ^ (-A) * ((n / 2 : ℕ) : ℝ) ^ (-A))
                = (3 : ℝ) ^ A * (3 * ((n / 2 : ℕ) : ℝ)) ^ (-A) := by rw [h2]
              _ ≤ (3 : ℝ) ^ A * (n : ℝ) ^ (-A) :=
                  mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)
          calc C0 * (Real.exp ((epsBW : ℝ) ^ 3 / 2) * ((n / 2 : ℕ) : ℝ) ^ (-A))
              = C0 * Real.exp ((epsBW : ℝ) ^ 3 / 2) * ((n / 2 : ℕ) : ℝ) ^ (-A) := by ring
            _ ≤ C0 * Real.exp ((epsBW : ℝ) ^ 3 / 2) * ((3 : ℝ) ^ A * (n : ℝ) ^ (-A)) :=
                mul_le_mul_of_nonneg_left hstep (by positivity)
            _ = C0 * Real.exp ((epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A * (n : ℝ) ^ (-A) := by
                ring
      _ ≤ max ((n0 : ℝ) ^ A) (C0 * Real.exp ((epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A)
            * (n : ℝ) ^ (-A) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hn0R.le _)

open Classical in
/-- **Proposition 7.3**, original `∃`-form: delegates to the `_at` sibling at
`C_renewalWhite A`. -/
theorem renewal_white_encounters (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → 1 ≤ n →
      (PMF.iid pascal (n / 2)).expect (fun b =>
        Real.exp (-((epsBW : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)))
        ≤ C * (n : ℝ) ^ (-A) :=
  ⟨C_renewalWhite A, C_renewalWhite_pos A, renewal_white_encounters_at A hA⟩

/-- The **tight** Proposition 7.3 constant (big-C campaign, Option B; RESIZED lap 13): the
head arm `2·n₀^A = 2·(2·C_hold A + 2)^A`, DROPPING the vacuous `C_polyDecay` tower.

**Lap-13 sizing correction** (see PENDING_WORK): the lap-12 value `n₀^A` with
`C_Qtight ≈ (n₀/3)^A` sits BELOW the `(C_hold A)^A` floor that any proof through the
`Qm`-monotone machinery can deliver (`Q_polynomial_decay_at`'s constant is the
trivial-regime crossover `(max C0 1)^A`, and its Prop-7.8 threshold `C0` is `≥ C_hold A`
intrinsically via `hold_weight_expect`) — the lap-12 statement was plausibly true but
unprovable without abandoning the entire Prop-7.8 apparatus.  Fix: take
`C_Qtight = (max (C_hold A) 1)^A` (the machinery floor), sharpen the crude `n ≤ 3·(n/2)`
bridge to `n ≤ 2·(n/2)+1` (so `C_hold·n ≤ (2·C_hold+2)·(n/2)` exactly, using
`n/2 ≥ C_hold+1` in the large-`n` arm), and absorb `exp(ε³/2) ≤ 2` into a factor `2`.
Numerically `2·n₀^A ≈ 10^(9.36×10¹⁰ + 0.3) < CTao = 10^(10¹¹)` — the extra factor `2`
costs 0.3 digits of the ≈6×10⁹-digit check17 headroom. -/
noncomputable def C_renewalWhite_tight (A : ℝ) : ℝ := 2 * ((2 * C_hold A + 2 : ℕ) : ℝ) ^ A

theorem C_renewalWhite_tight_pos (A : ℝ) : 0 < C_renewalWhite_tight A := by
  have h : (0 : ℝ) < ((2 * C_hold A + 2 : ℕ) : ℝ) ^ A :=
    Real.rpow_pos_of_pos (by positivity) A
  unfold C_renewalWhite_tight; linarith

/-- The tight-`Q` constant (Option B; RESIZED lap 13): the `Qm`-machinery floor
`(max (C_hold A) 1)^A` — exactly what `Q_polynomial_decay_at` yields when the Prop-7.8
threshold is brought down to `C_hold A`, i.e. when the black-edge estimate holds at a poly
threshold `≤ C_hold A` (the campaign crux `Q_black_edge_tight`). -/
noncomputable def C_Qtight (A : ℝ) : ℝ := ((max (C_hold A) 1 : ℕ) : ℝ) ^ A

theorem C_Qtight_pos (A : ℝ) : 0 < C_Qtight A := by
  unfold C_Qtight
  refine Real.rpow_pos_of_pos ?_ A
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)

set_option warningAsError false in
open Classical in
/-- **THE campaign crux** (Option B, lap 13): the black-edge estimate (paper (7.39)) at the
POLY threshold `C_hold A ≈ 10³⁰¹⁶`, replacing the tower threshold `Cthr_dampingCol A`
(whose `P_fewWhite = encWindowIter…` horizon is a `≈10³⁰¹⁰`-fold iterated cubing map).
From a black point `(n/2−m, l)`, the renewal value contracts by `m^{-A}` against the
depth-`(m−1)` envelope `Qm` — statement shape verbatim from `prop_7_8_at`'s `hC2` slot.
Lap-12 sizing: the true white-frequency threshold is `~10³⁰⁰⁸ < C_hold A ~10³⁰¹⁶`
(8 orders of room), so the statement is believed TRUE, but it IS Tao's §7 decorrelation
done with a poly horizon — the genuinely uncertain frontier.  The deterministic run-length
shortcut is REFUTED (PENDING_WORK, lap 12): a whole walk can be one black run, so the
content is genuinely probabilistic/equidistributional. -/
theorem Q_black_edge_tight (A : ℝ) (hA : 0 < A) :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, C_hold A ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m → (n / 2 - m, l) ∉ whiteSet n ξ →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  sorry

open Classical in
/-- **Tight `Q` polynomial decay** (Option B): the SAME statement as `Q_polynomial_decay`
(Case3) but with the machinery-floor constant `C_Qtight A = (max (C_hold A) 1)^A` in place
of the `C_polyDecay` tower.  DERIVED from the crux `Q_black_edge_tight` by the existing
Prop-7.8 machinery (`prop_7_8_at` + `Q_polynomial_decay_at`) — no residual `sorry` of its
own. -/
theorem Q_polynomial_decay_tight (A : ℝ) (hA : 0 < A) :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ (j : ℕ) (l : ℤ), 1 ≤ j →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l
        ≤ C_Qtight A * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
  have h78 := prop_7_8_at A hA (C_hold A) (Q_black_edge_tight A hA)
  have hmax : max (max (C_hold A) (C_hold A)) 1 = max (C_hold A) 1 := by omega
  rw [hmax] at h78
  have h := Q_polynomial_decay_at A hA (max (C_hold A) 1) h78
  have hmax2 : max (max (C_hold A) 1) 1 = max (C_hold A) 1 := by omega
  unfold C_Qtight
  rw [hmax2] at h
  exact h

set_option warningAsError false in
open Classical in
/-- **Proposition 7.3, TIGHT form** (Option B, lap 12 — ADDITIVE; the clean-headline
`renewal_white_encounters` is deliberately left UNTOUCHED, since it feeds the axiom-clean
headlines and a sorry-backed witness there would poison their axiom base).  Same
expected-damping bound as `renewal_white_encounters_at`, but with the head-only constant
`C_renewalWhite_tight A`, no `C_polyDecay` tower.

Route rationale (DIRECTION.md RESOLVED banner, 2026-07-17): the `n^{-A}` decay is supplied by
`hold_weight_expect`; the tower `C0 = C_polyDecay A` in `renewal_white_encounters_at` enters
only as a multiplicative constant via the `Q_polynomial_decay` bound, where `Q ≤ 1` already
holds in the applied range — it is vacuous slop.  Discharging this bound at the head constant
is what lets the head-route ladder clear `CTao`.

The small-`n` arm (`n < n₀`, trivial `E ≤ 1 ≤ n₀^A·n^{-A}`) is PROVED.  The large-`n` arm is
the campaign **crux** `renewal_tail_tight`: a `#white` lower-tail / decorrelation estimate
beating `few_white_mass_le`'s (7.67) tower horizon — the Option-B frontier (PENDING_WORK
Reflection 2026-07-17 lap 12).  Left as a named `sorry`; chip it. -/
theorem renewal_white_encounters_tight (A : ℝ) (hA : 0 < A) :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → 1 ≤ n →
      (PMF.iid pascal (n / 2)).expect (fun b =>
        Real.exp (-((epsBW : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)))
        ≤ C_renewalWhite_tight A * (n : ℝ) ^ (-A) := by
  intro n ξ hξ hn
  set C1 : ℕ := C_hold A with hC1def
  set n0 : ℕ := 2 * C1 + 2 with hn0
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hε0 : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  -- E ≤ 1 always: each damping factor exp(-ε³·#white) ≤ 1, total mass 1.
  -- (verbatim from `renewal_white_encounters_at`, self-contained.)
  have hE1 : (PMF.iid pascal (n / 2)).expect (fun b =>
      Real.exp (-((epsBW : ℝ) ^ 3) *
        ((Finset.univ.filter fun j : Fin (n / 2) =>
          b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ))) ≤ 1 := by
    unfold PMF.expect
    have hterm : ∀ b : Fin (n / 2) → ℕ,
        ((PMF.iid pascal (n / 2)) b).toReal *
          Real.exp (-((epsBW : ℝ) ^ 3) *
            ((Finset.univ.filter fun j : Fin (n / 2) =>
              b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ))
          ≤ ((PMF.iid pascal (n / 2)) b).toReal := by
      intro b
      have hle1 : Real.exp (-((epsBW : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        positivity
      calc ((PMF.iid pascal (n / 2)) b).toReal * _ ≤ _ * 1 :=
            mul_le_mul_of_nonneg_left hle1 ENNReal.toReal_nonneg
        _ = ((PMF.iid pascal (n / 2)) b).toReal := mul_one _
    have hsum : Summable fun b : Fin (n / 2) → ℕ => ((PMF.iid pascal (n / 2)) b).toReal :=
      ENNReal.summable_toReal (PMF.iid pascal (n / 2)).tsum_coe_ne_top
    have hsumf : Summable fun b : Fin (n / 2) → ℕ =>
        ((PMF.iid pascal (n / 2)) b).toReal *
          Real.exp (-((epsBW : ℝ) ^ 3) *
            ((Finset.univ.filter fun j : Fin (n / 2) =>
              b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)) :=
      Summable.of_nonneg_of_le
        (fun b => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hterm hsum
    calc ∑' b, ((PMF.iid pascal (n / 2)) b).toReal * _
        ≤ ∑' b, ((PMF.iid pascal (n / 2)) b).toReal := hsumf.tsum_le_tsum hterm hsum
      _ = 1 := by
          rw [← ENNReal.tsum_toReal_eq (fun b => ((PMF.iid pascal (n / 2)).apply_ne_top b)),
            (PMF.iid pascal (n / 2)).tsum_coe, ENNReal.toReal_one]
  rcases lt_or_ge n n0 with hsmall | hbig
  · -- small n: trivial head bound  E ≤ 1 ≤ n₀^A·n^{-A}  (shape from renewal_white_encounters_at).
    calc (PMF.iid pascal (n / 2)).expect _ ≤ 1 := hE1
      _ ≤ (n0 : ℝ) ^ A * (n : ℝ) ^ (-A) := by
          have h1 : (n : ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hsmall.le
          have h2 : (1 : ℝ) = (n : ℝ) ^ A * (n : ℝ) ^ (-A) := by
            rw [← Real.rpow_add hn0R, add_neg_cancel, Real.rpow_zero]
          rw [h2]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hn0R.le h1 hA.le) (Real.rpow_nonneg hn0R.le _)
      _ ≤ C_renewalWhite_tight A * (n : ℝ) ^ (-A) := by
          unfold C_renewalWhite_tight
          rw [hn0, hC1def]
          have hpos : (0 : ℝ) ≤ ((2 * C_hold A + 2 : ℕ) : ℝ) ^ A * (n : ℝ) ^ (-A) :=
            mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              (Real.rpow_nonneg hn0R.le _)
          nlinarith [hpos]
  · -- large n (n ≥ n₀): bridge + TIGHT polynomial decay + Geom(4) tail.  Same assembly as
    -- `renewal_white_encounters_at`, but the pointwise `Q` bound uses `Q_polynomial_decay_tight`
    -- (constant `C_Qtight A`) instead of the tower `C_polyDecay`, landing at `n₀^A·n^{-A}` via
    -- `C_Qtight_glue` — no `max`.  The only residual obligation is `Q_polynomial_decay_tight`.
    have hC00 : (0 : ℝ) < C_Qtight A := C_Qtight_pos A
    have hC0 := Q_polynomial_decay_tight A hA
    have hC11 : 1 ≤ C_hold A := one_le_C_hold A
    have hC1 := hold_weight_expect_explicitC A hA
    have hhalf1 : C1 ≤ n / 2 := by omega
    have hhalfpos : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by
      have h : 1 ≤ n / 2 := le_trans hC11 hhalf1
      exact_mod_cast h
    rw [bridge_vector n ξ, bridge_renewal (n / 2) (whiteSet n ξ) (epsBW : ℝ) hε0 0 0]
    have hpt : ∀ d : ℕ × ℤ,
        (hold d).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (0 + d.1) (0 + d.2)
          ≤ (hold d).toReal * (C_Qtight A * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)) := by
      intro d
      rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
      · rw [hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul, zero_mul]
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have h := hC0 n ξ hξ (0 + d.1) (0 + d.2) (by omega)
        simpa using h
    have hnn : ∀ d : ℕ × ℤ,
        0 ≤ (hold d).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (0 + d.1) (0 + d.2) :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (Q_nonneg _ _ _ _ _)
    have hwle : ∀ d : ℕ × ℤ, ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 := fun d =>
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast Nat.le_max_right (n / 2 - d.1) 1) (by linarith)
    have hsumw : Summable fun d : ℕ × ℤ =>
        (hold d).toReal * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (fun d => by
          calc (hold d).toReal * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)
              ≤ (hold d).toReal * 1 :=
                mul_le_mul_of_nonneg_left (hwle d) ENNReal.toReal_nonneg
            _ = (hold d).toReal := mul_one _)
        hold_summable_toReal
    have hsumCw : Summable fun d : ℕ × ℤ =>
        (hold d).toReal * (C_Qtight A * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
      (hsumw.mul_left (C_Qtight A)).congr fun d => by ring
    have hsumQ : Summable fun d : ℕ × ℤ =>
        (hold d).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (0 + d.1) (0 + d.2) :=
      Summable.of_nonneg_of_le hnn
        (fun d => by
          calc (hold d).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (0 + d.1) (0 + d.2)
              ≤ (hold d).toReal * 1 :=
                mul_le_mul_of_nonneg_left (Q_le_one _ _ _ hε0 _ _) ENNReal.toReal_nonneg
            _ = (hold d).toReal := mul_one _)
        hold_summable_toReal
    have htail := hC1 (n / 2) hhalf1
    calc ∑' d : ℕ × ℤ,
          (hold d).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (0 + d.1) (0 + d.2)
        ≤ ∑' d : ℕ × ℤ,
            (hold d).toReal * (C_Qtight A * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
          hsumQ.tsum_le_tsum hpt hsumCw
      _ = C_Qtight A * ∑' d : ℕ × ℤ,
            (hold d).toReal * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A) := by
          rw [← tsum_mul_left]
          exact tsum_congr fun d => by ring
      _ ≤ C_Qtight A * (Real.exp ((epsBW : ℝ) ^ 3 / 2) * ((n / 2 : ℕ) : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_left htail hC00.le
      _ ≤ 2 * (((n0 : ℕ) : ℝ) ^ A * (n : ℝ) ^ (-A)) := by
          -- sharp bridge (lap 13): C1·n ≤ n₀·(n/2) exactly (uses n ≤ 2·(n/2)+1 and
          -- C1 ≤ n/2), plus exp(ε³/2) ≤ exp(1/2) ≤ 2.
          have hCQ : C_Qtight A = ((C1 : ℕ) : ℝ) ^ A := by
            rw [hC1def]
            unfold C_Qtight
            rw [Nat.max_eq_left (one_le_C_hold A)]
          have hkey : C1 * n ≤ n0 * (n / 2) := by
            have hn2 : n ≤ 2 * (n / 2) + 1 := by omega
            calc C1 * n ≤ C1 * (2 * (n / 2) + 1) := Nat.mul_le_mul_left _ hn2
              _ = 2 * C1 * (n / 2) + C1 := by ring
              _ ≤ 2 * C1 * (n / 2) + 2 * (n / 2) := by omega
              _ = n0 * (n / 2) := by rw [hn0]; ring
          have hn0pos : (0 : ℝ) < ((n0 : ℕ) : ℝ) := by
            have h : 0 < n0 := by omega
            exact_mod_cast h
          have hdiv : ((C1 : ℕ) : ℝ) / ((n / 2 : ℕ) : ℝ) ≤ ((n0 : ℕ) : ℝ) / (n : ℝ) := by
            rw [div_le_div_iff₀ hhalfpos hn0R]
            exact_mod_cast hkey
          have hrp : (((C1 : ℕ) : ℝ) / ((n / 2 : ℕ) : ℝ)) ^ A
              ≤ (((n0 : ℕ) : ℝ) / (n : ℝ)) ^ A :=
            Real.rpow_le_rpow (by positivity) hdiv hA.le
          rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
            Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hrp
          have hmain : ((C1 : ℕ) : ℝ) ^ A * ((n / 2 : ℕ) : ℝ) ^ (-A)
              ≤ ((n0 : ℕ) : ℝ) ^ A * (n : ℝ) ^ (-A) := by
            rw [Real.rpow_neg hhalfpos.le, Real.rpow_neg hn0R.le,
              ← div_eq_mul_inv, ← div_eq_mul_inv]
            exact hrp
          have hexp2 : Real.exp ((epsBW : ℝ) ^ 3 / 2) ≤ 2 := by
            have hε1 : (epsBW : ℝ) ≤ 1 := by
              unfold epsBW
              push_cast
              rw [one_div]
              exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
            have hεcube : (epsBW : ℝ) ^ 3 / 2 ≤ 1 / 2 := by
              have h := pow_le_one₀ hε0 hε1 (n := 3)
              linarith
            have h1 : Real.exp ((epsBW : ℝ) ^ 3 / 2) ≤ Real.exp (1 / 2) :=
              Real.exp_le_exp.mpr hεcube
            have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
              rw [← Real.exp_add]; norm_num
            nlinarith [Real.exp_pos ((1 : ℝ) / 2), Real.exp_one_lt_d9]
          calc C_Qtight A * (Real.exp ((epsBW : ℝ) ^ 3 / 2) * ((n / 2 : ℕ) : ℝ) ^ (-A))
              = Real.exp ((epsBW : ℝ) ^ 3 / 2)
                  * (((C1 : ℕ) : ℝ) ^ A * ((n / 2 : ℕ) : ℝ) ^ (-A)) := by
                rw [hCQ]; ring
            _ ≤ Real.exp ((epsBW : ℝ) ^ 3 / 2) * (((n0 : ℕ) : ℝ) ^ A * (n : ℝ) ^ (-A)) :=
                mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
            _ ≤ 2 * (((n0 : ℕ) : ℝ) ^ A * (n : ℝ) ^ (-A)) :=
                mul_le_mul_of_nonneg_right hexp2
                  (mul_nonneg (Real.rpow_nonneg hn0pos.le _) (Real.rpow_nonneg hn0R.le _))
      _ = C_renewalWhite_tight A * (n : ℝ) ^ (-A) := by
          unfold C_renewalWhite_tight
          rw [hn0, hC1def]
          ring

end TaoCollatz
