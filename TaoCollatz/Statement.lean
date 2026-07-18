import TaoCollatz.Basic.Collatz
import TaoCollatz.Basic.LogDensity
import TaoCollatz.Basic.ExplicitConstants
import TaoCollatz.BigCTower
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# TRUSTED BASE — the main theorem statements

This file is the only trusted surface of the library (BLUEPRINT §3), a four-statement
surface: Theorem 1.3 and Theorem 3.1 of Tao 2019 (arXiv:1909.03562) are the paper's,
stated from first principles; `tao_collatz_quantitative_fully_explicit` (with the
concrete exponent `cTao` and the concrete constant `CTao`, plus its `∃`-form
`tao_collatz_quantitative_explicit`) is OUR augmentation beyond the paper — the paper
proves `∃ c C` and Remark 1.4 gives only a shape, never a value.  The MEANING of every
statement here rests only on the elementary leaf files `Basic.Collatz` +
`Basic.LogDensity` (`col`, `colMin`, log density via Finset sums and `Tendsto`) and
`Basic.ExplicitConstants` (`cTao`; `CTao`'s own vocabulary is Mathlib's
`hyperoperation` — native tetration); the remaining
imports bring only proofs, and the mathlib `Pow.Real` import supplies just the `rpow`
notation used in Theorem 3.1's error term.

Axiom gate: `#print axioms tao_collatz` must be exactly
`[propext, Classical.choice, Quot.sound]` at campaign end.
-/

namespace TaoCollatz

/-- **Theorem 1.3** (Tao 2019): for any `f : ℕ → ℝ` with `f(N) → ∞`, almost all `N`
(in logarithmic density) satisfy `Colmin(N) < f(N)`. -/
theorem tao_collatz (f : ℕ → ℝ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    AlmostAllPos fun N => (colMin N : ℝ) < f N := by
  exact tao_collatz_spine f hf

/-- **Theorem 3.1** (Tao 2019, `Colmin` form): quantitative version — the log-probability
that `Colmin(N) ≤ N₀` on the window `[1, x]` is at least `1 - C/(log N₀)^c`. -/
theorem tao_collatz_quantitative :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ c ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
  exact tao_collatz_quantitative_spine

/-- The concrete constant — Mathlib's native tetration: `hyperoperation 4 10 10` is
`10↑↑10`, a right-associated tower of exactly 10 tens.

⚠️ **CAMPAIGN PIN (planted 2026-07-18, judge-owned).**  The previous, *proved* value was
`10↑↑63` (main at `4dde699`); the Tier-1 tower-tightening campaign
(`TIER1-TOWER-TIGHTENING-PLAN.md` + `DIRECTION.md`) re-pins it at `10↑↑10` and re-proves
`tao_collatz_quantitative_fully_explicit` by tightening the `BigCTower.lean` ceiling to
`C_tao_assembled ≤ tenTower 9` — with the honest height ≈ 3 (plan §1), there is ample
room.  Laps write the PROOF, never this statement. -/
noncomputable def CTao : ℝ := (hyperoperation 4 10 10 : ℝ)

theorem CTao_pos : 0 < CTao := by
  rw [show CTao = ((hyperoperation 4 10 10 : ℕ) : ℝ) from rfl,
    ← tenTower_nine_eq_hyperoperation]
  exact tenTower_pos 9

set_option warningAsError false in
/-- **Theorem 3.1, fully-explicit form** (our augmentation): Theorem 3.1 holds with BOTH
parameters concrete — one may take `c = cTao = 1/(640_000_000 log 2)` and
`C = CTao = 10↑↑10` — the explicit values asked for by
[MO 341570](https://mathoverflow.net/questions/341570).

⚠️ **CAMPAIGN PIN — `sorry` until the Tier-1 tower tightening discharges it.**  The
statement is true with room to spare: main (`4dde699`) proves it at `10↑↑63`, and the
assembled constant's honest height is ≈ `10↑↑4`.  Route: batched level-budget calculus →
`C_tao_assembled ≤ tenTower 9` (tighter is the goal; the ceiling theorem records the
honest height) → `tenTower_nine_eq_hyperoperation`.  Discharge this LAST, after `check28`
asserts the honest height — the run's `--done-when sorry-free:TaoCollatz` gate fires on
this discharge.  The `warningAsError` shield covers exactly this planted `sorry`; remove
both together at discharge. -/
theorem tao_collatz_quantitative_fully_explicit :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - CTao / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) :=
  sorry

/-- **Theorem 3.1, explicit-exponent form** (our augmentation): Theorem 3.1 holds with the
concrete exponent `cTao` — the explicit value asked for by
[MO 341570](https://mathoverflow.net/questions/341570). -/
theorem tao_collatz_quantitative_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) :=
  ⟨CTao, CTao_pos, tao_collatz_quantitative_fully_explicit⟩

/- **The `CTao` pin was RETIRED 2026-07-17** (judge ruling, Trevor's call).

`CTao := 10 ^ (10¹¹)` and `tao_collatz_quantitative_fully_explicit` lived here as a
sorry-by-design campaign pin: a guess that some round numeral bounds this development's
multiplicative constant. **The guess was wrong, and not by a little.** The constant §7
actually assembles is a *tower* — `C_renewalWhite` embeds `C_polyDecay = Cthr_prop78^A`,
whose `encWindowIter` cubic recurrence runs ~10^3010 steps — so no fixed-exponent numeral
can bound it, and the natural rescue (a tight renewal bound) has no route we could find.
Keeping an aspirational `sorry` on a statement we had evidence was unreachable would have
been a claim we could not back, so it is gone rather than parked.

Its successor is honest about the size instead of guessing at it: see `ExplicitBigC.lean`
for `C_tao_assembled` — a *closed term* for the constant, assembled from the proof as
written, with no smallness claim whatsoever. That converts "effective in principle" (Tao's
methods are effective; nobody computed the constant) into "effective in fact,
kernel-certified" — which is what [MO 341570](https://mathoverflow.net/questions/341570)
actually asks for.  `BigCTower.lean` then proves the closed term fits under `tenTower 62`,
which is how the fully-explicit form returned to this file (`CTao` +
`tao_collatz_quantitative_fully_explicit` above) — proved at `10↑↑63`, an honest value:
a tower, not a guessed numeral.

2026-07-18: the Tier-1 tower-tightening campaign re-pinned `CTao` at `10↑↑10` (planted
`sorry` above).  Unlike the retired `10^(10¹¹)` pin, this one carries machine-checked
evidence of reachability: check19's height floor + the plan's §1 slop census say the
honest ceiling is ≈ `10↑↑4`, so `10↑↑10` has five spare tower levels.

History: `git log --follow` this file; the full route map, the machine-checked evidence,
and the judge rulings are in `PENDING_WORK.md` + `DIRECTION.md`. -/

end TaoCollatz
