/-
Comparator CHALLENGE for TaoCollatz — trusted vocabulary + non-vacuity anchors.

Imports ONLY Mathlib. Re-declares the development's trusted-base DEFINITIONS
(`col`, `colMin`, `logSum`, `logProb`, `posInterval`, `HasLogDensity`,
`AlmostAllPos`) under their real fully-qualified names, with their real bodies,
so `leanprover/comparator` can certify they are byte-identical to the ones the
project actually uses.

The theorems below are the project's proved *non-vacuity anchors*; comparator
checks the SOLUTION discharges each one against these very definitions.

⚠️ The two headline theorems (`TaoCollatz.tao_collatz`,
`TaoCollatz.tao_collatz_quantitative`, Tao's Thm 1.3 / 3.1) are deliberately NOT
here: they are still `sorry` in the development, and a challenge may contain only
theorems the solution actually proves. This harness certifies the trusted
VOCABULARY today (so a reader can confirm `Colmin`, log density, "almost all" mean
what Tao means); the headlines join the challenge when they are discharged.

This file is the human audit surface. Read the DEFINITIONS against Tao 2019
(arXiv:1909.03562): (1.1) for `col`, and Def. 1.2 for logarithmic density. The
anchors exist to rule out a vacuous reading — see each docstring.
-/
import Mathlib

set_option warningAsError false

namespace TaoCollatz

open Filter Topology

/-- The Collatz map (Tao (1.1)): `3N+1` on odds, `N/2` on evens. -/
def col (N : ℕ) : ℕ := if N % 2 = 1 then 3 * N + 1 else N / 2

/-- `Colmin(N)`, the least value attained by the Collatz orbit of `N`. -/
noncomputable def colMin (N : ℕ) : ℕ := sInf (Set.range fun k => col^[k] N)

open Classical in
/-- Σ_{N ∈ A ∩ R} 1/N, the log-uniform score of `A` on the finite window `R`. -/
noncomputable def logSum (A : Set ℕ) (R : Finset ℕ) : ℝ :=
  ∑ N ∈ R.filter (· ∈ A), (1 : ℝ) / N

/-- Probability mass of `A` under the log-uniform law `Log(R)`. -/
noncomputable def logProb (A : Set ℕ) (R : Finset ℕ) : ℝ :=
  logSum A R / logSum Set.univ R

/-- The window `ℕ+ ∩ [1, x]` as a `Finset`. -/
noncomputable def posInterval (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (· ≥ 1)

/-- `A ⊂ ℕ+` has logarithmic density `d` (Tao Def. 1.2): the `x → ∞` limit of
`logProb A (posInterval x)`. -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun x => logProb A (posInterval x)) atTop (𝓝 d)

/-- `P` holds for *almost all* `N ∈ ℕ+`, i.e. `{N | P N}` has log density `1`. -/
def AlmostAllPos (P : ℕ → Prop) : Prop :=
  HasLogDensity {N | P N} 1

/-! ### Non-vacuity anchors

Proved in the development (`TaoCollatz/Basic/Anchors.lean`); the solution
discharges them. Each rules out a degenerate reading of the definitions above. -/

/-- `colMin` is not constantly `1`: the orbit of `0` is `{0}`. -/
theorem colMin_zero : colMin 0 = 0 := sorry

/-- The famous `27` orbit really reaches `1` and `colMin` really is its minimum. -/
theorem colMin_twentyseven : colMin 27 = 1 := sorry

/-- The density machinery is not vacuously strict: the trivial property has log
density `1`. -/
theorem almostAllPos_true : AlmostAllPos fun _ => True := sorry

/-- ...and it can *distinguish*: the empty property does not have log density `1`.
Together with `almostAllPos_true`, this rules out a degenerate `AlmostAllPos`. -/
theorem not_almostAllPos_false : ¬ AlmostAllPos fun _ => False := sorry

/-- The `1/N` weights are genuine: on `{1, 2}` the odds carry mass `2/3`. A
natural-density impostor would give `1/2`, so this separates logarithmic from
natural density — the axis Tao's Thm 1.3 lives on. -/
theorem logProb_odd_window_two :
    logProb {N : ℕ | N % 2 = 1} (posInterval 2) = 2 / 3 := sorry

end TaoCollatz
