import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.OrderClosed

/-!
# Logarithmic density (node C3)

Tao 2019 uses *logarithmic density* to define "almost all" Collatz orbits
(his Def. 1.2). For finite non-empty `R ⊂ ℕ+`, the logarithmically uniform
distribution `Log(R)` on `R` is

```
P(Log(R) ∈ A) = (Σ_{N ∈ A ∩ R} 1/N) / (Σ_{N ∈ R} 1/N)
```

and the logarithmic density of `A ⊂ ℕ+` is the `x → ∞` limit of
`P(Log(ℕ+ ∩ [1, x]) ∈ A)` (when it exists). A property holds for *almost all*
`N` if `{N | P N}` has log density `1`.

Ported from `~/src/collatz-cryptid/lean/Collatz/LogDensity.lean` (v4.29 → v4.31),
with the odd-window forms (`oddInterval`, `AlmostAllOdd`) added for §1.2.
-/

namespace TaoCollatz

open Filter Topology

-- The finite-set log-uniform "score": Σ_{N ∈ A ∩ R} 1/N for the
-- fragment of A lying in finite R ⊂ ℕ+.
open Classical in
/-- Σ_{N ∈ A ∩ R} 1/N, the log-uniform score of `A` on the finite window `R`. -/
noncomputable def logSum (A : Set ℕ) (R : Finset ℕ) : ℝ :=
  ∑ N ∈ R.filter (· ∈ A), (1 : ℝ) / N

/-- Probability mass of `A` under `Log(R)`. -/
noncomputable def logProb (A : Set ℕ) (R : Finset ℕ) : ℝ :=
  logSum A R / logSum Set.univ R

/-- Logarithmic density of `A ⊂ ℕ+`, as the limit (if it exists) of
`logProb A (Finset.Icc 1 x)` as `x → ∞`. Predicate form so it makes sense even
when the limit does not exist; assert a specific value `d` via `HasLogDensity A d`. -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun x => logProb A (Finset.Icc 1 x)) atTop (𝓝 d)

/-- A property `P` holds for *almost all* `N ∈ ℕ+` (logarithmic density) if
`{N | P N}` has log density `1`. -/
def AlmostAllPos (P : ℕ → Prop) : Prop :=
  HasLogDensity {N | P N} 1

/-- The "odd window" `(2ℕ+1) ∩ [1, x]` as a `Finset`. -/
noncomputable def oddInterval (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (fun N => N % 2 = 1)

/-- A property `P` holds for *almost all odd* `N` (logarithmic density on the
odd window). Paper §1.2, "almost all `N ∈ 2ℕ+1`". -/
def AlmostAllOdd (P : ℕ → Prop) : Prop :=
  Filter.Tendsto (fun x => logProb {N | P N} (oddInterval x)) Filter.atTop (nhds 1)

end TaoCollatz
