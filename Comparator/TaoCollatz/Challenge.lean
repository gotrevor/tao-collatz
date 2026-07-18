/-
Comparator CHALLENGE for TaoCollatz — trusted vocabulary + non-vacuity anchors.

Imports ONLY Mathlib. Re-declares the development's trusted-base DEFINITIONS
(`col`, `colMin`, `logSum`, `logProb`, `HasLogDensity`, `AlmostAllPos`) under
their real fully-qualified names, with their real bodies, so
`leanprover/comparator` can certify they are byte-identical to the ones the
project actually uses.

The theorems below are the project's proved *non-vacuity anchors*; comparator
checks the SOLUTION discharges each one against these very definitions.

The two HEADLINE theorems (`TaoCollatz.tao_collatz`,
`TaoCollatz.tao_collatz_quantitative` — Tao's Thm 1.3 and the Thm 3.1 Colmin
form) joined the challenge 2026-07-15, the day the development discharged them.
Their statements are rendered below over THIS file's Mathlib-only vocabulary;
comparator certifies the solution proves byte-identical statements under the
axiom whitelist, replayed through Lean's kernel and independently through nanoda.

This file is the human audit surface. Read the DEFINITIONS against Tao 2019
(arXiv:1909.03562): (1.1) for `col`, and Def. 1.2 for logarithmic density. The
anchors exist to rule out a vacuous reading — see each docstring.
-/
import Mathlib

-- Load-bearing, despite looking like a no-op: the package turns warnings into errors
-- (lakefile.toml) and the statements below are `sorry` by design. Removing this line
-- fails the Comparator build.
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

/-- `A ⊂ ℕ+` has logarithmic density `d` (Tao Def. 1.2). -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun x => logProb A (Finset.Icc 1 x)) atTop (𝓝 d)

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
    logProb {N : ℕ | N % 2 = 1} (Finset.Icc 1 2) = 2 / 3 := sorry

/-! ### The headlines (Tao 2019: Theorem 1.3, and Theorem 3.1 in `Colmin` form)

Discharged in the development 2026-07-15. Statements match
`TaoCollatz/Statement.lean` over the vocabulary declared above. -/

/-- **Theorem 1.3** (Tao 2019): for any `f : ℕ → ℝ` with `f(N) → ∞`, almost all
`N` (in logarithmic density) satisfy `Colmin(N) < f(N)`. -/
theorem tao_collatz (f : ℕ → ℝ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    AlmostAllPos fun N => (colMin N : ℝ) < f N := sorry

/-- **Theorem 3.1** (Tao 2019, `Colmin` form): the log-probability that
`Colmin(N) ≤ N₀` on the window `[1, x]` is at least `1 - C/(log N₀)^c`. -/
theorem tao_collatz_quantitative :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ c ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := sorry

/-! ### The explicit augmentation (beyond the paper: Tao 2019 proves only `∃ c C`) -/

/-- The explicit exponent — OUR augmentation, beyond the paper. -/
noncomputable def cTao : ℝ := 1 / (640_000_000 * Real.log 2)

/-- The concrete constant: `hyperoperation 4 10 63` is `10↑↑63`, a right-associated
tower of exactly 63 tens. -/
noncomputable def CTao : ℝ := (hyperoperation 4 10 63 : ℝ)

/-- **Theorem 3.1, fully-explicit form** (our augmentation): Theorem 3.1 holds with BOTH
parameters concrete — one may take `c = cTao = 1/(640_000_000 log 2)` and
`C = CTao = 10↑↑63`. -/
theorem tao_collatz_quantitative_fully_explicit :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - CTao / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := sorry

end TaoCollatz
