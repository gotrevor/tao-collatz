# PENDING WORK (kept current per lap; newest on top)

## After lap 11 (2026-07-10, third box session): `hold_weight_expect` PROVED

**Done** (axiom-clean): the (7.43) Case-1 geometric-expectation leaf
`hold_weight_expect` — `E[max(m-d₁,1)^{-A}] ≤ exp(ε³/2)·m^{-A}` for `m ≥ C_A`.
Chain: `hold_map_fst` (first marginal of `hold` is `geomQuarter`, by PMF monad laws) →
`hold_fst_marginal`/`hold_tsum_fst` (ℕ×ℤ-tsum marginalization via `ENNReal.tsum_prod'`)
in `Sec7/Holding.lean`; `geomQuarter_toReal`/`_tsum_toReal`/`_summable_toReal`/
`geomQuarter_tail` (exact tail `(3/4)^t`, injective-shift `hasSum`) in
`Prob/Geometric.lean`; then in `Monotone.lean` the three-region split
(head `k ≤ K` weight `(m-K)^{-A} ≤ (1+δ/3)m^{-A}` via `c := (1+δ/3)^{1/A}`;
middle `K < k ≤ m/2` mass `(3/4)^K ≤ (δ/3)2^{-A}` and weight `≤ 2^A m^{-A}`;
tail `k > m/2` mass `(3/4)^{m/2} ≤ (δ/3)m^{-A}` via
`summable_norm_pow_mul_geometric_of_norm_lt_one` → tendsto → threshold `T`).

**Lap 12 addendum**: `Q_white_case1` (Case 1 proper, (7.41)–(7.43)) PROVED,
axiom-clean — one `Q_rec` step at the white start pulls `exp(-ε³)`, `Q_le_Qm` at
depth `m-1` bounds each hold-atom landing (`half - (half-m+d₁) = m - d₁` by omega),
`hold_weight_expect` gives the `exp(ε³/2)m^{-A}` expectation, and
`exp(-ε³)·exp(ε³/2) = exp(-ε³/2)`. X7's remaining open pieces: Case 2 (black start,
paper (7.44) — needs the triangle/renewal input), the `prop_7_8` assembly from the
two cases, then `Q_polynomial_decay` by induction on `m` from (7.39) + Prop 7.8.

**Original route note (superseded)**: consume `Q_rec` + `Q_le_Qm` +
`hold_weight_expect`. Route: one step of `Q_rec` at the white start `(n/2 - m, l)`
pulls `exp(-ε³)`; each hold-atom `d` lands at `j = n/2 - m + d₁` with
`n/2 - (m-1) ≤ j` (d₁ ≥ 1), so `Q_le_Qm` (depth `m-1`) bounds the landed value by
`max(n/2 - j, 1)^{-A}·Q_{m-1}`; note `n/2 - (n/2 - m + d₁) = m - d₁` (ℕ, m ≤ n/2),
matching `hold_weight_expect`'s weight; needs `Qm_nonneg` to pull the constant
`Q_{m-1}` out of the tsum. Combine: `exp(-ε³)·exp(ε³/2) = exp(-ε³/2)`.
Then Case 2 (paper (7.44), black start) and the Prop 7.8 induction (X9).
Judge follow-up (b) DONE (lap 13): `check12` in `tools/check_blueprint.py` — the
(7.36)-bridge. Pascal-column DP (mirrors `renewal_white_encounters` LHS) vs
hold-jump DP (mirrors `E Q(Hold)` with the D6 recursion + `whiteSet` adapter);
agreement 1e-11 at n=14/16, incl. amplified damping (1/e, 0.5) where any
coordinate off-by-one would show at O(1). Renewal identity (7.26)≡(7.27) and the
paper-vs-0-based seam are pinned end-to-end. All judge follow-ups now closed.

## Lap 14 (2026-07-10): (7.45) unrolling — `Qstop`/`Qstop_eq` PROVED (X8/X9 entry)

New `Sec7/Unroll.lean` (axiom-clean): `hold_support_snd_ge`/`hold_zero_of_snd_lt`
(second coord of `hold` ≥ 3), `Qstop half W ε s j l` — the D6 stopped value (well-
founded on the height budget `s`; a step with `d₂ > s` = the paper's first passage
`l_{[1,k]} > s` lands on plain `Q`), and `Qstop_eq : Qstop s j l = Q j l` (∀ s) —
paper (7.45) verbatim, by strong induction on `s` over `Q_rec`. No stopping-time
measure theory needed. Case 2 (X8) and Lemma 7.9 (X9) both enter through this:
pick `s := l_Δ - l` per triangle; the overshoot branch's endpoint is what the
white-exit bound (7.50)/(7.51) + `Q_le_Qm` control.

**X8 next steps**: (a) a `Qstop_le` bound isolating the overshoot-branch endpoint
expectation (Case 2's (7.46)); (b) the endpoint-distribution facts need Lemma 7.7
(Chernoff for the 2D renewal walk) — the genuinely hard probabilistic kernel;
(c) the white-exit constant (7.50)/(7.51) consumes Lemma 7.4's structure
(`black_structure` proved) + 7.7. **X9**: `Z R j l` recursion on `R` over `Qstop`.

## Lap 15 (2026-07-10): `prop_7_8` ASSEMBLED — open core narrowed to `Q_black_edge`

`prop_7_8` (Prop 7.8, Q_m ≤ Q_{m-1}) is now PROVED modulo one named sorry:
`Q_black_edge` (Monotone.lean) — the (7.41) edge bound for black starts
(Cases 2–3, paper (7.44)–(7.67)). The assembly: `Real.iSup_le` over the `Qm m`
sup; interior points (`p₁ > half - m`) drop to `Q_{m-1}` via `le_Qm` at depth
`m-1` (same weight); edge points (`p₁ = half - m`, weight `m^A`) use
`Q_white_case1` (white) or `Q_black_edge` (black), with the `m^A·m^{-A}` rpow
cancellation. Gotcha: the sup-subtype projections `(⟨(p1,l),_⟩).1` block omega —
normalize with defeq `have`/`show` bridges first.

**The X7→X11 chain now rests entirely on `Q_black_edge`**, whose route is:
`Qstop_eq` (proved) + Lemma 7.7 Chernoff (X6, the hard probabilistic kernel) +
white-exit (7.50)/(7.51) (consumes `black_structure`, proved) for Case 2; +
Lemma 7.9 induction (X9) for Case 3. Next: state Lemma 7.7 (D6 form) and the
Case 2/3 split of `Q_black_edge`; then `Q_polynomial_decay` from `prop_7_8` +
`Qm_le_rpow` by forward induction on m (tractable now).

## After laps 6–10 (2026-07-10, second box session): **X3 HEAD CLOSED — Lemma 7.4 PROVED**

`black_structure` is now a theorem, `#print axioms` = `[propext, Classical.choice,
Quot.sound]`. The whole chain, all in `Sec7/Triangles.lean`:
`θq_left_run` → `θq_fibre_eq` (exact ℚ fibre identity `θ(j,l) = 9^{j-j*}2^{l*-l}θ*`)
→ `fibre_le_eps`/`corner_phase_pos`/`black_mem_corner_triangle` (Δ*-membership) →
`wb_row_left/right` + `white_row_above` (Claim (*) Cases 2–3 engine) + `lstar_eq_of`/
`jstar_eq_of` (Nat.find corner characterization) → `black_of_mem_corner_triangle`
(Δ* black) + `corner_triangle_confined`/`_strip` (confinement, log numerics) →
`corner_eq` (corner invariance = fibre equality) → assembly via `cornerTriple` image,
`lattice_sq_dist_ge_one`, `sep_const_sq_le_one` (`10¹² ≤ 2⁴⁰` trick for
`(1/10)log(10⁴) < 1`). Note: at ε = 10⁻⁴ the separation conjunct reduces to lattice
disjointness — Case 1 proper was not needed for Lemma 7.4 itself (our fibre identity is
exact where the paper's (7.18) is an inequality). Also done: `unifOddMod` normalization
(judge follow-up a).

**Judge follow-ups still open**: (b) the (7.36)-bridge harness check in
`tools/check_blueprint.py` (judge item 9); (c) Case 1 proper statement per judge item 8
spec (needed for the Q-recursion / Lemma 7.9 series, NOT for Lemma 7.4 — see above).

**Next hardest open obligations** (X3 done → move up the chain): Lemma 7.9 induction
skeleton over `Q_rec` (X9) consuming `Q_white_contract`/Case 1; the (7.45) unrolling
statement design (X8); S3's d=1 negative-binomial half; `renewal_white_encounters`
(Prop 7.3) probabilistic side.

## After lap 5 (2026-07-10)

**Done** (axiom-clean): (a) (7.18) inequality forms — `sfrac_mem`/`sfrac_eq_self`/
`sfrac_idem`, `θq_succ_j_abs_le`, `θq_pred_l_abs_le`, `θq_iterate_abs_le`
(`|θ(j+a,l-b)| ≤ 9^a 2^b |θ(j,l)|` unconditional); (b) the corner map:
`exists_white_above` (via `black_run_le` + archimedean), defs `upRun`/`lstar`/
`leftRun`/`jstar` (Nat.find, classical), spec lemmas `black_of_le_lstar`, `le_lstar`,
`white_above_lstar`, `leftRun_pos`, `black_of_jstar_le`, `jstar_maximal`.
NOTE: our `sfrac` range is `[-1/2, 1/2)` (mirror of the paper's `(-1/2, 1/2]`);
only `|sfrac|` is used and denominators are odd, so no discrepancy — documented at
`sfrac_mem`.

**X3 next**: the corner triangle fibre. Key lemma to state and prove next
(paper (7.17)–(7.18) + Claim (*) — the heart of Lemma 7.4):
  `theorem mem_corner_triangle`: for black (j,l) in the strip, with (j*,l*) its corner
  and s* := log(ε/|θ(j*,l*)|) ≥ 0: `9^(j-j*)·2^(l*-l)·|θ*| ≤ ε` (i.e. (j,l) ∈ Δ* as a
  ℚ-inequality — the ℝ-log triangle membership is monotone algebra on top).
  Route: |θ(j,l)| ≤ ε (black) and θ(j,l) = 9^(j-j*)2^(l*-l)θ* by θq_iterate_exact
  — but the iterate goes from the corner DOWN to (j,l): need the scale < 1/2 premise,
  which needs Claim (*) Case-1-style reasoning (if the scaled value exceeded ε it
  wraps...). Careful: the correct paper route is (7.18) with equality "whenever the
  RHS is strictly less than 1/2". Plan: prove by strong induction down the run using
  the run lemmas (each step black keeps values ≤ ε ≤ 1/4, so exact steps apply and the
  product never wraps). Concretely: (j,l) black, everything between (j,l*)..(j,l) black
  (black_of_le_lstar column) and (j*,l*)..(j,l*) black (row) — then iterate exact steps
  along row then column, all values staying ≤ ε.
  CAUTION: intermediate points of Δ* are NOT all on the row/column path; but the paper's
  Δ* membership only needs the (j,l)↔corner relation, and the run lemmas give exactly
  the path needed. |θ(j,l)| = 2^(l*-l)|θ(j,l*)| (θq_up_run) and
  |θ(j,l*)| = 9^(j-j*)|θ(j*,l*)| (row version of up_run — NEEDS a leftward run-exact
  lemma `θq_left_run`, same proof shape as θq_up_run using θq_succ_j_exact on black row
  points: TO WRITE).
  Then fibre equality Δ* = {p : black, corner p = (j*,l*)} and Claim (*) cases.

## After lap 4 (2026-07-10)

**Done** (axiom-clean): `θq_iterate_j`, `θq_iterate_l`, `θq_iterate_exact` — the (7.18)
equality-case scaling `θ(j+a, l-b) = 9^a·2^b·θ(j,l)` when the final scale is < 1/2 (the
triangle-fibre engine); `θq_up_run` (upward black run ⇒ exact doubling downward) and
`black_run_le` (`2^t ≤ ε·3^{n-2j}` caps upward black runs ⇒ paper's l* exists).

**X3 remaining for `black_structure`**: (a) leftward run at l* (j*-existence — runs
hit j=0 or a white point; finite by construction, no analytic input needed);
(b) DEFINE the corner map + triangle size (`s* := log(ε/|θ*|)` — lives in ℝ, ties ℚ-θ
to the ℝ-triangle (7.11)); (c) fibre equivalence via `θq_iterate_exact` both directions
(Claim (*) Cases 1–3 using claims (i)–(iii)); (d) assemble. This is now bounded work but
a lot of it — decompose into named sorries inside Triangles.lean when starting assembly.

## After lap 3 (2026-07-10)

**Done**: (7.16) formalized — `θq_lower_bound` (`3^{-(n-2j)} ≤ |θ(j,l)|` for ξ coprime
to 3, `2j+1 ≤ n`, via the ±1/3-mod-ℤ 3-adic argument: `sfrac_phase_absorb` +
`abs_sfrac_le` + argRel scaling) and `black_nine_le` (black ⇒ `n - 2j ≥ 9`). All
axiom-clean. This is the strip-confinement input to Lemma 7.4's conjunct 4.

**Next attack on X3 (`black_structure`)**: with (7.16) + claims (i)–(iii) in hand, the
remaining Lemma 7.4 ingredients are (a) l*-existence: an upward black run from a black
point terminates (uses `black_nine_le` at growing powers via `θq_pred_l_exact` doubling:
|θ(j,l')| = 2^{l-l'}|θ(j,l)| forces whiteness once above ε... paper argument p.38 uses
3^{n+1-2j}2^{l-l'}ε ≥ 1/3 — formalize as: black run upward of length > log₂(3^{n-2j}ε)
impossible); (b) j*-existence (leftward run hits j=1); (c) the Δ* fibre equivalence
(7.17)/(7.18) — the equality case identity |θ(j',l')| = 9^{Δj}2^{Δl}|θ*| when RHS < 1/2,
provable by induction from the two exact lemmas.

## After lap 2 (2026-07-10)

**Done this lap** (all `#print axioms`-clean, build green):
- `Sec7/Triangles.lean`: θ-identity exactness (`θq_succ_j_exact`, `θq_pred_l_exact` —
  no-wraparound forms of (7.13)/(7.14)) and the paper-p.38 weakly-black claims
  (i) j-form + l-form, (ii), (iii) (`black_of_weaklyBlack_succ_j/pred_l`,
  `weaklyBlack_of_succ_j_pred_l`, `weaklyBlack_of_pred_j_pred_l`). These are the engine
  of every case of Lemma 7.4's Claim (*).
- `Sec7/Monotone.lean`: `Q_white_contract` (Case 1 warm-up) and `Qm_le_rpow` (7.39,
  the Prop 7.8 induction base) proved.

**Crux state / next attack** (hardest-first):
1. **X3 — Lemma 7.4 `black_structure`**: claims (i)–(iii) now proved. Next: formalize
   (7.16)-strip confinement (`black → j ≤ n/2 - (1/10)log(1/ε)`; needs the "ξ·3^{n-1}·…
   is 1/3 or 2/3 mod 1" 3-adic step), then l*/j* existence (finite runs: the check-8
   argument — upward black runs terminate since 3^{n+1-2j}2^{l-l'}ε ≥ 1/3 fails), then
   the (7.17)/(7.18) triangle-fibre equivalence. Decompose into named sub-sorries in
   Triangles.lean next lap.
2. **X8 Case 2 / X9 Lemma 7.9 skeleton**: (7.45) iterate of `Q_rec` (unrolling along the
   first-passage time) is the next structural lemma; needs a finitized stopping-time
   unrolling over `Q` — statement design work.
3. **S3 (Lemma 2.2)**: untouched; awaits D5 tilting route. Consider starting the d=1
   exact-formula half (negative binomial Gaussian bounds) as an independent thread.

**Notes / traps recorded**: triangle sizes are NOT O(log 1/ε) (giant triangles exist,
harness check 8); Lemma 7.4 separation is between point SETS (statement fixed lap 1).
