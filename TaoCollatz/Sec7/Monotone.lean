import TaoCollatz.Sec7.Holding
import TaoCollatz.Sec7.Triangles
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §7.4: the monotone quantity `Q_m` and Proposition 7.8 (node X7)

Paper anchors: Tao 2019 §7.4, (7.38), Proposition 7.8, Case 1 (7.42)–(7.43).

* `Qm` — the worst-case renewal value at depth `m` (paper (7.38)): the sup of
  `Q` over starting points at least `m` columns deep into the strip.
* `prop_7_8` — the key decay estimate `Q_m ≤ (1 - ε⁸)^{⌊m/C⌋}`-shaped statement,
  reified with explicit constants per D3/D7. Statement only (`sorry`).

The white set fed to `Q` is the §7.1 white set of `(n, ξ)` (paper (7.9)); `Q`'s `W`
parameter is the set where the `exp(-ε³)` damping applies — i.e. the WHITE points.
-/

open scoped ENNReal

namespace TaoCollatz

/-- The white set of `(n, ξ)` as a subset of the `(j,l)` lattice (the damping set for
the renewal value `Q`). -/
def whiteSet (n ξ : ℕ) : Set (ℕ × ℤ) := {p | white n ξ p.1 p.2}

-- RATIFY-7: (7.38) is a supremum over starting locations `(j,l)` with `j ≥ m`. We use
-- `⨆` over the subtype with `Real.iSup` semantics (bounded by `Q_le_one`, nonempty).
-- Judge the paper's exact indexing (depth measured from strip start) against §7.4 p.45.
/-- The worst-case renewal value at depth `m` (paper (7.38)):
`Q_m = sup {Q (j,l) : j ≥ m}`. -/
noncomputable def Qm (half : ℕ) (n ξ : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  ⨆ p : {p : ℕ × ℤ // m ≤ p.1}, Q half (whiteSet n ξ) ε p.1.1 p.1.2

/-- **Proposition 7.8** (skeleton): for suitable `C_{A,ε}`, once `n` is large the
worst-case renewal value decays geometrically in depth: `Q_0 ≤ C·n^{-A}`-shaped decay
through the strip. Reified with explicit constants (D3/D7). -/
theorem prop_7_8 (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∃ n₀ : ℕ, ∀ n ξ : ℕ, n₀ ≤ n → ¬ 3 ∣ ξ →
      Qm (n / 2) n ξ (epsBW : ℝ) 0 ≤ C * (n : ℝ) ^ (-A) := by
  sorry

/-- **Case 1** of Prop 7.8 ((7.42)–(7.43)): if the starting point is white, one step of
the recursion (7.35) already contracts by `exp(-ε³)`:
`Q (j,l) ≤ exp(-ε³) · sup_{d ∈ supp Hold} Q ((j,l)+d)`-shaped bound via the tsum. -/
theorem Q_white_contract (half : ℕ) (n ξ : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) (l : ℤ)
    (hj : j ≤ half) (hw : white n ξ j l) :
    Q half (whiteSet n ξ) ε j l ≤ Real.exp (-(ε ^ 3)) := by
  sorry

end TaoCollatz
