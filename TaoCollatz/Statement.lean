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

/-- The concrete constant: `10^(10^(10^3053))`, the honest closed-form ceiling the
Tier-1 tower-tightening campaign proved for the assembled Tao constant (base-free
record `log log log C ≲ 3053`, `BigCTower.lean`'s `C_tao_assembled_le_ten3_3053`).

This is the tightest value the development bounds `C_tao_assembled` by, and it is
*strictly smaller* than any clean tower `10↑↑k` that holds (`10↑↑4` is false; `10↑↑5`
holds but overshoots by a full tower level, since its level-3 exponent is `10^10`
against this value's `3053`).  Pin history — `10↑↑63` (main at `4dde699`) → `10↑↑10`
(campaign target) → this tight value on discharge — is in the note below. -/
noncomputable def CTao : ℝ := (10 : ℝ) ^ ((10 : ℝ) ^ ((10 : ℝ) ^ (3053 : ℕ)))

theorem CTao_pos : 0 < CTao := by
  unfold CTao; positivity

/-- **Theorem 3.1, fully-explicit form** (our augmentation): Theorem 3.1 holds with BOTH
parameters concrete — one may take `c = cTao = 1/(640_000_000 log 2)` and
`C = CTao = 10^(10^(10^3053))` — the explicit values asked for by
[MO 341570](https://mathoverflow.net/questions/341570).

Discharged 2026-07-18 (Tier-1 tower-tightening campaign): `CTao` is *exactly* the honest
closed-form ceiling `C_tao_assembled ≤ 10^(10^(10^3053))` (`BigCTower.lean`'s
`C_tao_assembled_le_ten3_3053`; base-free record `log log log C ≲ 3053`, top-exponent
provenance `epsBW⁻³ = 10^3000`), so `hC` is that theorem directly. -/
theorem tao_collatz_quantitative_fully_explicit :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - CTao / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
  intro N₀ x hN₀ hx
  have hbase := tao_collatz_quantitative_assembled N₀ x hN₀ hx
  have hN₀real : (1 : ℝ) < N₀ := by exact_mod_cast (show 1 < N₀ by omega)
  have hden : 0 < (Real.log N₀) ^ cTao :=
    Real.rpow_pos_of_pos (Real.log_pos hN₀real) _
  have hC : C_tao_assembled ≤ CTao := by
    unfold CTao; exact C_tao_assembled_le_ten3_3053
  have hfrac : C_tao_assembled / (Real.log N₀) ^ cTao ≤
      CTao / (Real.log N₀) ^ cTao :=
    (div_le_div_iff_of_pos_right hden).2 hC
  linarith

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
`sorry` above).  Unlike the retired `10^(10¹¹)` pin, this one carried machine-checked
evidence of reachability: check19's height floor + the plan's §1 slop census said the
honest ceiling is ≈ `10↑↑4`, so `10↑↑10` had five spare tower levels.  On discharge the
pin was then tightened past `10↑↑10` to the literal honest ceiling `10^(10^(10^3053))`
(`C_tao_assembled_le_ten3_3053`) — *strictly smaller* than `10↑↑5`, the tightest value
`BigCTower.lean` proves.  No reason to ship the looser round tower once the tight bound
was in hand: the explicit form answers MO 341570, which asks for the smallest honest `C`.

History: `git log --follow` this file; the full route map, the machine-checked evidence,
and the judge rulings are in `PENDING_WORK.md` + `DIRECTION.md`. -/

end TaoCollatz
