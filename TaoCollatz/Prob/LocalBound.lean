import TaoCollatz.Prob.Geometric

/-!
# Lemma 2.2: local 2-D Gaussian-type bounds (node S3)

Paper anchors: Tao 2019, (2.2) p.14 (the Gaussian-type weights `G_n`), Lemma 2.2
(Chernoff type bound) pp.14–16, instantiated per design decision D5 at the four
distributions the argument consumes — `Geom(2)` (= `geomHalf`), `Geom(4)`-shaped
(= `geomQuarter`), `Pascal` (= `pascal`), and (in `Sec7/Unroll.lean`, where `hold`
lives) the 2-D `Hold` walk. The paper proves Lemma 2.2 for a general nondegenerate
`v : Zᵈ` with exponential tails via complexified MGF + contour shifting; per D5 we
avoid contour integration and will prove each instance by exponential tilting plus
the finite (`ZMod`) circle method, using the exact point masses available here
(`negBinomial_apply` for `Geom(2)` sums).

* `Gweight t x = exp(-x²/t) + exp(-|x|)` — paper (2.2), factored here from
  `Sec7/Unroll.lean` (Lemma 7.7 consumes it).
* `iidSum p n` — the law of `p`-iid `v₁ + ⋯ + vₙ` (paper `v_{[1,n]}`, (1.6)).
* `*_local_bound` — Lemma 2.2(i) at each d=1 distribution.
* `*_tail_bound` — Lemma 2.2(ii) at each d=1 distribution.

-- RATIFY-DRIFT (G-weight index): the paper's display uses `G_n`; we state every
-- bound with `Gweight (1 + n)`. Since `Gweight` is antitone in `x²/t`,
-- `G_n(x) ≤ G_{1+n}(x)` pointwise, so our conclusions are (very slightly) weaker
-- upper bounds, still of Gaussian type at the same scale — and this is exactly the
-- form Lemma 7.7 (`fpDist_location_bound`) consumes. It also sidesteps Lean's
-- `x/0 = 0` convention, under which `Gweight 0 x = 1 + exp(-|x|)` would NOT be the
-- paper's `G_0(x) = exp(-|x|)` (paper convention `exp(-∞) = 0`). The `n = 0` cases
-- are trivial point masses either way.
-- RATIFY-DRIFT (index set): sums of our ℕ-valued variables are stated over `L : ℕ`;
-- the paper's `L ∈ ℤ` adds only zero-mass points (all masses vanish for `L < n`).
-- Means: `geomHalf` has mean 2 (paper: `E|Geom(2)| = 2`, §1.4), `geomQuarter` and
-- `pascal` have mean 4 (§7.3; `pascal = Geom(2) + Geom(2)`).
-/

open scoped ENNReal

namespace TaoCollatz

/-- The Gaussian-type weight `G_t(x) = exp(-x²/t) + exp(-|x|)` (paper (2.2)). -/
noncomputable def Gweight (t x : ℝ) : ℝ := Real.exp (-(x ^ 2) / t) + Real.exp (-|x|)

theorem Gweight_pos (t x : ℝ) : 0 < Gweight t x :=
  add_pos (Real.exp_pos _) (Real.exp_pos _)

theorem Gweight_nonneg (t x : ℝ) : 0 ≤ Gweight t x := (Gweight_pos t x).le

theorem Gweight_le_two (t x : ℝ) (ht : 0 ≤ t) : Gweight t x ≤ 2 := by
  have h1 : Real.exp (-(x ^ 2) / t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, div_zero]
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) ht |>.trans_eq rfl
  have h2 : Real.exp (-|x|) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))
  calc Gweight t x ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- The law of the sum `v₁ + ⋯ + vₙ` of `n` iid copies of `p` (paper `v_{[1,n]}`). -/
noncomputable def iidSum (p : PMF ℕ) (n : ℕ) : PMF ℕ :=
  (p.iid n).map fun v => ∑ i, v i

/-- **Lemma 2.2(i) for `Geom(2)`** (paper p.15, displayed instance):
`P(|Geom(2)_n| = L) ≪ (n+1)^{-1/2} · G_n(c(L − 2n))`. -/
theorem geomHalf_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum geomHalf n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - 2 * n)) := by
  sorry

/-- **Lemma 2.2(ii) for `Geom(2)`** (paper p.15, displayed instance):
`P(||Geom(2)_n| − 2n| ≥ λ) ≪ G_n(cλ)`. -/
theorem geomHalf_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 2 * n| then ((iidSum geomHalf n) L).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  sorry

/-- **Lemma 2.2(i) for `Geom(4)`-shaped `geomQuarter`** (mean 4; §7.3 consumes this
through `Hold`'s first coordinate). -/
theorem geomQuarter_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum geomQuarter n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - 4 * n)) := by
  sorry

/-- **Lemma 2.2(ii) for `geomQuarter`**. -/
theorem geomQuarter_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 4 * n| then ((iidSum geomQuarter n) L).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  sorry

/-- **Lemma 2.2(i) for `Pascal`** (mean 4). Via `pascal_eq_map_iid`, `iidSum pascal n`
is the law of `|Geom(2)_{2n}|`, so this reduces to the exact negative-binomial point
mass `C(L-1, 2n-1)·2^{-L}` (`negBinomial_apply`) plus Stirling-type estimates. -/
theorem pascal_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum pascal n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - 4 * n)) := by
  sorry

/-- **Lemma 2.2(ii) for `Pascal`**. -/
theorem pascal_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 4 * n| then ((iidSum pascal n) L).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  sorry

end TaoCollatz
