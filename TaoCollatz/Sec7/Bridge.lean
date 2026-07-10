import TaoCollatz.Sec7.Monotone

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

open Classical in
/-- **Bridge, vector side** (the (7.26)/(7.28) rewriting, D6 form): the iid Pascal
vector expectation of the damped white-encounter count equals the column recursion.
OPEN (X5): induction on `m` peeling `Fin.cons` through `PMF.iid`/`expect`, with
`pre (Fin.cons a v) (i+1) = a + pre v i` and the `Fin.succ` filter reindex. -/
theorem bridge_vector (n ξ : ℕ) :
    (PMF.iid pascal (n / 2)).expect (fun b =>
        Real.exp (-((epsBW : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)))
      = Rcol (n / 2) (whiteSet n ξ) (epsBW : ℝ) 0 0 := by
  sorry

/-- One-column self-similarity of `Hold` (paper (7.29), tsum form over `ℝ≥0∞`):
a `Hold` draw is `(1,3)` with probability `1/4` (the first column is already a
renewal), else the first column contributes `(1, b)` with `b ~ Pascal` conditioned
`≠ 3` and the draw restarts. The `b ≠ 3` Pascal mass is `(3/4)·pascalNe3` exactly.
OPEN (X5): from `hold`'s definition by splitting the `geomQuarter` draw at `k = 1`
and peeling the first `pascalNe3` increment off `PMF.iid`. -/
theorem hold_tsum_step (g : ℕ × ℤ → ℝ≥0∞) :
    ∑' d : ℕ × ℤ, hold d * g d
      = 4⁻¹ * g (1, 3)
        + ∑' b : ℕ, (if b = 3 then 0 else pascal b)
            * ∑' d : ℕ × ℤ, hold d * g (d.1 + 1, d.2 + b) := by
  sorry

/-- **Bridge, renewal side** ((7.27) ≡ (7.28), D6 form): the column recursion equals
the holding-jump average of `Q` — the walk from `(j,l)` to its first renewal point is
one `Hold` draw, and `Q` at that point self-applies the damping (`Q_rec`).
OPEN (X5): downward induction on `half - j`; the inductive step is `hold_tsum_step`
matched against `Rcol`'s one-column unfolding and `Q_rec` at renewal landings. -/
theorem bridge_renewal (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (j : ℕ) (l : ℤ) :
    Rcol half W ε j l
      = ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2) := by
  sorry

open Classical in
/-- **Proposition 7.3** (finitized, D6 form; moved from `Holding.lean` 2026-07-10):
the expected damping factor `exp(-ε³ · #white encounters)` over the paired valuation
vector `b ~ Pascal^{⌊n/2⌋}` decays super-polynomially: `≤ C·n^{-A}` for every `A`.
PROVED from `bridge_vector` + `bridge_renewal` (the two open X5 seams) +
`Q_polynomial_decay` + `hold_weight_expect`. -/
theorem renewal_white_encounters (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → 1 ≤ n →
      (PMF.iid pascal (n / 2)).expect (fun b =>
        Real.exp (-((epsBW : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)))
        ≤ C * (n : ℝ) ^ (-A) := by
  obtain ⟨C0, hC00, hC0⟩ := Q_polynomial_decay A hA
  obtain ⟨C1, hC11, hC1⟩ := hold_weight_expect A hA
  -- constants: below n₀ := 2·C1 + 2 use the trivial bound E ≤ 1 ≤ n₀^A·n^{-A};
  -- above, the chain gives C0·exp(ε³/2)·3^A·n^{-A}.
  set n0 : ℕ := 2 * C1 + 2 with hn0
  refine ⟨max ((n0 : ℝ) ^ A) (C0 * Real.exp ((epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A),
    lt_max_iff.mpr (Or.inl (Real.rpow_pos_of_pos (by positivity) A)), fun n ξ hξ hn => ?_⟩
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
    rw [bridge_vector n ξ, bridge_renewal (n / 2) (whiteSet n ξ) (epsBW : ℝ) 0 0]
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

end TaoCollatz
