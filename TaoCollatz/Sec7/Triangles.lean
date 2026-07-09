import TaoCollatz.Sec7.Setup
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# §7.2: the black set is a union of separated triangles (node X3)

Paper anchors: Tao 2019 §7.2, (7.11)–(7.15), Lemma 7.4.

`triangle` is the upper-left corner triangle (7.11) in the `(j,l)` lattice under the
`(log 9, log 2)` metric. `black_structure` (Lemma 7.4) — statement only (`sorry`).
-/

open scoped Real

namespace TaoCollatz

/-- The corner triangle with apex `(j₀, l₀)` and size `s` (paper (7.11)): points to the
lower-right of the apex within `(log 9)·Δj + (log 2)·Δl ≤ s`. -/
def triangle (j₀ : ℕ) (l₀ : ℤ) (s : ℝ) : Set (ℕ × ℤ) :=
  {p | j₀ ≤ p.1 ∧ p.2 ≤ l₀ ∧
    ((p.1 : ℝ) - j₀) * Real.log 9 + ((l₀ : ℝ) - p.2) * Real.log 2 ≤ s}

-- RATIFY-5: the three Lemma 7.4 claims (partition into triangles, `(1/10)log(1/ε)`
-- pairwise separation, and confinement to the strip `j+1 ≤ n/2 - (1/10)log(1/ε)`) spelled
-- as an explicit conjunction; separation is stated squared to avoid `Real.sqrt`. Judge
-- against §7.2 pp.36–41.
/-- **Lemma 7.4.** For `ξ` not divisible by 3, the black set (within the strip
`j+1 ≤ n/2`) is a finite union of corner triangles that are pairwise Euclidean-separated
by `≥ (1/10)·log(1/ε)` and confined to `j+1 ≤ n/2 - (1/10)·log(1/ε)`. -/
theorem black_structure (n ξ : ℕ) (hξ : ¬ 3 ∣ ξ) (hn : 1 ≤ n) :
    ∃ T : Set (ℕ × ℤ × ℝ),
      (∀ t ∈ T, 0 ≤ t.2.2) ∧
      {p : ℕ × ℤ | p.1 + 1 ≤ n / 2 ∧ black n ξ p.1 p.2}
        = ⋃ t ∈ T, triangle t.1 t.2.1 t.2.2 ∧
      (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
        ((1 / 10 : ℝ) * Real.log (1 / (epsBW : ℝ))) ^ 2
          ≤ ((t.1 : ℝ) - t'.1) ^ 2 + ((t.2.1 : ℝ) - t'.2.1) ^ 2) ∧
      (∀ t ∈ T, ∀ p ∈ triangle t.1 t.2.1 t.2.2,
        (p.1 : ℝ) + 1 ≤ (n : ℝ) / 2 - (1 / 10 : ℝ) * Real.log (1 / (epsBW : ℝ))) := by
  sorry

end TaoCollatz
