import TaoCollatz.Syracuse.ValuationDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §5 first-passage machinery (nodes C7/C8 defs)

Paper anchors: Tao 2019 §1.3, §5, (1.18), Proposition 1.11.

Definitions for the first passage of the Syracuse orbit below `x`: `passes`,
`passTime`, `passLoc` (paper `Pass_x`, with the `Syr^∞ := 1` convention), the
log-uniform window `logUnifOdd`, and the constant `alpha` (1.18). The stabilization
proposition (Prop 1.11 — the spine's key input) carries `sorry`.
-/

open scoped ENNReal

namespace TaoCollatz

/-- `T_x(N) < ∞`: the Syracuse orbit of `N` eventually drops to `≤ x`. -/
def passes (x N : ℕ) : Prop := ∃ n, syr^[n] N ≤ x

/-- First passage time `T_x(N)` below `x` (junk `0` if it never passes). -/
noncomputable def passTime (x N : ℕ) : ℕ := sInf {n | syr^[n] N ≤ x}

open Classical in
/-- First passage location `Pass_x(N)`, with the paper's `Syr^∞ := 1` convention. -/
noncomputable def passLoc (x N : ℕ) : ℕ := if passes x N then syr^[passTime x N] N else 1

/-- The odd numbers in `[lo, hi]`, as a `Finset` (window support). -/
noncomputable def logWindow (lo hi : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil hi + 1)).filter fun N => N % 2 = 1 ∧ lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi

/-- Log-uniform distribution on the odd numbers in `[lo, hi]` (mass `∝ 1/N`);
falls back to `pure 1` when the window is empty. -/
noncomputable def logUnifOdd (lo hi : ℝ) : PMF ℕ :=
  if (logWindow lo hi).Nonempty then
    PMF.ofFinset
      (fun N => if N ∈ logWindow lo hi then
          (N : ℝ≥0∞)⁻¹ / ∑ M ∈ logWindow lo hi, (M : ℝ≥0∞)⁻¹ else 0)
      (logWindow lo hi)
      (by sorry)
      (by intro a ha; rw [if_neg ha])
  else PMF.pure 1

/-- Paper (1.18): the scaling exponent `α = 1.001`. -/
def alpha : ℝ := 1.001

-- RATIFY-3: window endpoints spelled per the spec's guidance as `[x^α, x^{α²}]` and
-- `[x^{α²}, x^{α³}]` (using `alpha^2`, `alpha^3`), which the SKELETON-SPEC flagged as the
-- intended reading of its nested-pow shorthand. Judge against §5 pp.25–28.
/-- **Proposition 1.11** (stabilization): the passage-location law is stable across the
two nearby log-windows, and non-passage is rare. The spine's key input. -/
theorem stabilization :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      (∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1)
          ≤ C * x ^ (-c)) ∧
      PMF.dTV ((logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).map (passLoc ⌊x⌋₊))
              ((logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).map (passLoc ⌊x⌋₊))
        ≤ C * (Real.log x) ^ (-c) := by
  sorry

end TaoCollatz
