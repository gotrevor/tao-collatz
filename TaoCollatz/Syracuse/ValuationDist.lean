import TaoCollatz.Syracuse.SyracRV
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §4: valuation distribution ≈ `Geom(2)ⁿ` (node C5) — statements only

Paper anchors: Tao 2019 §4, Lemma 4.1, Proposition 1.9.

`valuation_dist` is Prop 1.9 (the `n`-Syracuse valuation vector is close in total
variation to `Geom(2)ⁿ`, with geometric error), and `valuation_tail` is Lemma 4.1
(the total valuation rarely exceeds `n'`). Both carry `sorry`.
-/

open scoped ENNReal

namespace TaoCollatz

-- RATIFY-DRIFT: `PMF.uniformOfFinset` is absent in mathlib v4.31; `unifOddMod` is built
-- with `PMF.ofFinset` over the odd residues.
-- JUDGE DECISION (2026-07-09 pass, queue item 2): the `n' = 0` degeneracy is junk-guarded
-- (`PMF.pure 0` on the trivial `ZMod 1`) rather than threaded as a `1 ≤ n'` hypothesis
-- through `valuation_dist`/`valuation_tail` — the pre-fix def carried a FALSE `sorry`
-- (normalization over an empty odd-residue set). The remaining normalization `sorry` is
-- now TRUE and grindable: for `n' ≥ 1`, `2 ≤ 2 ^ n'` so `(1 : ZMod (2 ^ n')).val = 1` is
-- odd → the filter is nonempty → the sum is `card • card⁻¹ = 1` (card ≠ 0, ≠ ⊤).
/-- Uniform distribution on the odd residues mod `2ⁿ'` (junk `PMF.pure 0` at `n' = 0`,
where there are no odd residues). -/
noncomputable def unifOddMod (n' : ℕ) : PMF (ZMod (2 ^ n')) :=
  if _h : n' = 0 then PMF.pure 0
  else PMF.ofFinset
    (fun z => if z.val % 2 = 1 then
        ((Finset.univ.filter fun w : ZMod (2 ^ n') => w.val % 2 = 1).card : ℝ≥0∞)⁻¹ else 0)
    (Finset.univ.filter fun z : ZMod (2 ^ n') => z.val % 2 = 1)
    (by sorry)
    (by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [if_neg ha])

/-- **Proposition 1.9.** If `X` is a distribution on odd numbers whose reduction mod `2ⁿ'`
is close to uniform (with `n' ≥ (2 + c₀)n`), then the valuation vector `valVec · n` is
close in total variation to `Geom(2)ⁿ`, with error `2^{-c₁ n}`. -/
theorem valuation_dist (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 0 < K) :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧ ∀ (n n' : ℕ) (X : PMF ℕ),
      (2 + c₀) * n ≤ (n' : ℝ) →
      (∀ N ∈ X.support, N % 2 = 1) →
      PMF.dTV (X.map fun N => (N : ZMod (2 ^ n'))) (unifOddMod n') ≤ K * (2 : ℝ) ^ (-(n' : ℝ)) →
      PMF.dTV (X.map fun N => valVec N n) (PMF.iid geomHalf n)
        ≤ C * (2 : ℝ) ^ (-c₁ * (n : ℝ)) := by
  sorry

/-- **Lemma 4.1** (tail bound): under the same hypotheses, the total valuation
`|a⁽ⁿ⁾(N)|` rarely exceeds `n'`. -/
theorem valuation_tail (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 0 < K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n n' : ℕ) (X : PMF ℕ),
      (2 + c₀) * n ≤ (n' : ℝ) →
      (∀ N ∈ X.support, N % 2 = 1) →
      PMF.dTV (X.map fun N => (N : ZMod (2 ^ n'))) (unifOddMod n') ≤ K * (2 : ℝ) ^ (-(n' : ℝ)) →
      (X.map fun N => pre (valVec N n) n).expect (Set.indicator {L | n' ≤ L} 1)
        ≤ C * (2 : ℝ) ^ (-c * (n : ℝ)) := by
  sorry

end TaoCollatz
