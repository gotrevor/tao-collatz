# PENDING WORK (kept current per lap; newest on top)

## Lap 24 (2026-07-10, fifth box session): circle-method probe — iidSum generic + mod-N entry PROVED

`iidSum` GENERALIZED to any `AddCommMonoid` (same proofs, omega→add_assoc);
`iidSum_map` (additive pushforward commutes with iid sums), `PMF.apply_le_map_apply`
(pushforward merges mass — the free-truncation observation: upper bounds via mod-N
reduction need NO tail argument), `holdSum_eq_iidSum` (Prod.fst_sum/snd_sum bridge),
`modPair`, and **`holdSum_le_modPair`** — circle-method step 1 for `hold_local_bound`:
`P(Hold_[1,n] = v) ≤ P(iid walk on ZMod N × ZMod N = v mod N)` for EVERY `N`. All
axiom-clean.

**Remaining S3 decomposition for `hold_local_bound`** (route now concrete):
(C2) finite Fourier inversion bound on `ZMod N × ZMod N`: `(r x).toReal ≤ N⁻² ∑_ξ
‖charFn r ξ‖` with `charFn r ξ := ∑_y (r y).toReal • eC((ξ₁ y₁ + ξ₂ y₂)/N)` (finite
sums; orthogonality of roots of unity — check mathlib `ZMod.dft`/`AddChar` inversion
or prove directly from geometric sums of `eC`);
(C3) `charFn (iidSum r n) ξ = (charFn r ξ)^n` (convolution multiplicativity via
`iidSum_succ` + cexpect product splitting);
(D) character decay `‖charFn (hold.map (modPair N)) ξ‖ ≤ exp(-c ‖ξ/N‖²)` for ξ ≠ 0
(the analytic crux; from hold's explicit mass: `hold (1, 3) = 1/4`, `hold (2, b)`
atoms give nondegeneracy in both directions — two-atom |φ|² identity);
(E) Gaussian summation `N⁻² ∑_ξ exp(-cn‖ξ/N‖²) ≤ C/n` with `N ≈ ⌈√n⌉`;
(F) exponential tilting wrapper for the off-center/exp regime + Hold MGF finiteness
on a strip (= Lemma 7.6 engine, (7.30)).
Choose N per (j,l)? No — N only enters (E); pick `N = ⌈√n⌉ + 1` uniformly.

## Lap 23 (2026-07-10, fifth box session): d=1 warm-up PROVED — negBinomial_apply + pascal_eq_map_iid

**Done (axiom-clean)**: `negBinomial_apply` — exact negative-binomial point mass
`P(|Geom(2)_n| = L) = C(L-1, n-1)·2^{-L}` by induction on `n` over the iid peel
(`tsum_iid_succ_mul`), convolution step = reindexed hockey stick
(`sum_range_choose_col`, `sum_Ico_choose_shift`); `pascal_eq_map_iid` — `pascal` IS
the 2-fold `Geom(2)` sum, immediate from `negBinomial_apply` at `n = 2` plus a
sum-zero support argument (`iid_geomHalf_sum_zero`, generic `PMF.iid_support_coord`
added to Prob/Basic). These give S3's Pascal instance an exact formula to work from:
`iidSum pascal n` = law of `|Geom(2)_{2n}|`, mass `C(L-1, 2n-1)·2^{-L}`.

**NEXT (S3 continued, per session mission)**: (a) the `iidSum pascal n =
iidSum geomHalf (2n)` splice (iid concat lemma) so `pascal_local_bound` reduces to
binomial estimates on `C(L-1, 2n-1)·2^{-L}` (Stirling recipe in corpus:
2026-06-19-mathlib-stirling-factorial-bounds.md); (b) probe the ZMod circle-method
decomposition for `hold_local_bound` (finite Fourier inversion on `ZMod N × ZMod N`,
exponential-tail truncation replaces the paper's `[-π,π]²` integral — no measure
theory); state the key intermediate lemmas.

## Lap 22 (2026-07-10, fifth box session): S3 front OPENED — Lemma 2.2 statements pinned

`Prob/LocalBound.lean` NEW: `Gweight` (2.2) factored from Unroll + `Gweight_pos/
_nonneg/_le_two`, `iidSum`, and Lemma 2.2(i)(ii) STATED (sorries) for `geomHalf`
(mean 2), `geomQuarter` (mean 4), `pascal` (mean 4): `*_local_bound` =
`C/√(1+n)·Gweight(1+n)(c(L-μn))`, `*_tail_bound` = indicator-tsum `≤ C·Gweight(1+n)(cλ)`.
`Sec7/Unroll.lean`: `holdSum` + `hold_local_bound`/`hold_tail_bound` (d=2, mean (4,16),
sup-norm; RATIFY-DRIFT notes: Gweight(1+n) vs G_n, ℕ index set, sup vs Euclidean norm).
Judge should ratify these vs paper pp.14-16 + p.42.

## Lap 21 (2026-07-10, fourth box session): Lemma 7.7 D6 layer — `fpDist` + (7.45) inequality

`Sec7/Unroll.lean` extended (all proved, axiom-clean, except the one named sorry):
* `fpDist : ℕ → PMF (ℕ × ℤ)` — the first-passage endpoint distribution (paper
  `v_{[1,k]}`, (7.44)) by budget recursion mirroring `Qstop`; normalization free
  from PMF combinators. Junk guard `d.2 ≤ 0` fires only on hold-null atoms.
* `fpDist_support_fst_pos`, `fpDist_support_snd_gt` — endpoints move right and
  overshoot the budget (`s < e₂`).
* `Q_le_fpDist_expect` — the (7.45) inequality in ℝ≥0∞ form:
  `ofReal (Q j l) ≤ Σ' e, fpDist s e · ofReal (Q (j+e₁) (l+e₂))` for every budget s.
  Strong induction over `Q_rec`, damping dropped (each factor ≤ 1). This is Case 2's
  (7.46) entry and Case 3's (7.53) at P = 0.
* `Gweight t x = exp(-x²/t) + exp(-|x|)` (paper (2.2)) and
  **`fpDist_location_bound` — Lemma 7.7 stated as the NEW NAMED SORRY** (X6):
  `(fpDist s (j,l)).toReal ≤ C·(e^{-c(l-s)}/√(1+s))·Gweight (1+s) (c(j-s/4))`,
  unconditional (LHS vanishes for l ≤ s by the support lemma).
  Numeric sanity: MC at s=40 → mode j ∈ {10,11,12} ≈ s/4+1, l ∈ {41,42,43} ✓.

**Attack routes for `fpDist_location_bound`** (the paper's pp.43–44 proof):
union bound over the last step (mirror: one `fpDist` unfold), `Hold` exponential
tail (Lemma 7.6 — provable from geomQuarter/pascalNe3 MGFs, finite products), and
the 2-D local bound Lemma 2.2 for iid `Hold` sums (node S3, the real wall; D5:
exponential tilting + circle method — `P(S_k = v) = (2π)^{-2} M(λ)^k e^{-λ·v} ∫|φ_λ|^k`).
NOTE: `fpDist` has no k-index — the D6 route needs a k-free reformulation of the
union bound, e.g. induction on s with the Gaussian weight as the induction invariant
(the paper's (7.33) reduction is already k-summed, which suits this form).

## Laps 18–20 (2026-07-10, fourth box session): X5 FULLY CLOSED — all three bridge sorries PROVED

**Done (axiom-clean)**: `hold_tsum_step` (7.29), `bridge_renewal` (7.27)≡(7.28),
`bridge_vector` (7.26)/(7.28). `Sec7/Bridge.lean` is now sorry-free;
**Proposition 7.3 (`renewal_white_encounters`) is fully proved modulo the single
Q-side sorry `Q_black_edge`** (its `#print axioms` sorryAx traces only through
`Q_polynomial_decay` → `prop_7_8` → `Q_black_edge`).

Infrastructure added (reusable): `PMF.tsum_bind_mul`/`tsum_map_mul`/
`tsum_iid_succ_mul`/`tsum_iid_zero_mul` (ℝ≥0∞ change-of-variables calculus),
`PMF.toReal_tsum_mul_ofReal`/`tsum_mul_ofReal_le_one`/`expect_iid_zero`/
`expect_iid_succ` (real expectation peeling for [0,1] observables) in
`Prob/Basic.lean`; `hold_tsum_expand`, `hold_tsum_step_real`, `pre_cons`,
`bridge_vector_gen` in `Sec7/Bridge.lean`. `bridge_renewal` gained a `0 ≤ ε`
hypothesis (Q_le_one summability).

Gotchas: `(3 + ∑ i, v i : ℤ)` elaborates cast-of-sum OR sum-of-casts depending on
context — spell `(3 : ℤ) + ∑ i, (v i : ℤ)` explicitly to match `hold`'s def;
`Fin.cons_succ` needs `(α := fun _ => ℕ)`; `congr 1` after `Fin.sum_univ_succ`
closes the i=0 head definitionally (don't bullet it); `if_congr` with `refine ?_`
holes gets stuck on Decidable instances — build the `Iff` in a `have` first;
`unfold PMF.expect; dsimp only` to beta-reduce before `rw [← tsum_mul_left]`.

**NEXT (the wall): `Q_black_edge` (Monotone.lean) — Lemma 7.7 D6 statement design.**
Handoff item 4: state the Chernoff/Gaussian first-passage endpoint bound over the
`Qstop` recursion (no infinite sequences; mirror the `Qstop` branch structure).
Paper Lemma 7.7 p.42–44, (7.30)–(7.33), Gaussian-type upper bound `G_k`. Then the
(7.50)/(7.51) white-exit constant (consumes proved `black_structure`) and Lemma
7.9's induction (X9) for the deep case. Parallel threads if blocked:
`key_fourier_decay` X1/X2 chain; S3 negative-binomial in Geometric.lean.

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

## Lap 16 (2026-07-10): `Q_polynomial_decay` PROVED (from prop_7_8)

(7.37) closed: forward induction on `m` — below the threshold `Cb := max C0 1`
use `Qm_le_rpow` ((7.39)); above, `prop_7_8` steps down; gives the uniform bound
`Q_m ≤ Cb^A`, then `Q_le_Qm` at depth `n/2 - j` (strip interior) or `Q_le_one`
(past the edge, weight 1). Constant `C := Cb^A`. Depends on `Q_black_edge` via
`prop_7_8` — the whole §7.4 chain is now a cone over that single sorry.
Gotcha: standalone `have h := Q_le_Qm ...` needs `(l := l)` (implicit `l`
unconstrained). Next: the (7.36) seam in Decay.lean (E Q(Hold) ≪ n^{-A} from
`Q_polynomial_decay` + `hold_tsum_fst`-style Geom(4) tail), or start Lemma 7.7's
D6 statement for `Q_black_edge`.

## Lap 17 (2026-07-10): Prop 7.3 (`renewal_white_encounters`) ASSEMBLED — X5 seam named

New `Sec7/Bridge.lean`: `Rcol` (the per-column D6 form of the (7.28) product) and
`renewal_white_encounters` (MOVED from Holding.lean) now PROVED modulo three named
X5 sorries, all numerically pre-validated by harness check12:
- `bridge_vector` — iid-Pascal-vector expectation = `Rcol 0 0` (induction on length
  peeling `Fin.cons`; `pre (cons a v) (i+1) = a + pre v i`, `Fin.succ` filter reindex);
- `hold_tsum_step` — the (7.29) one-column self-similarity of `hold` in tsum/ℝ≥0∞ form
  (split `geomQuarter` at `k = 1`, peel one `pascalNe3` off `PMF.iid`);
- `bridge_renewal` — `Rcol j l = Σ' d, hold(d)·Q((j,l)+d)` (downward induction on
  `half - j` via `hold_tsum_step` + `Q_rec`; boundary `j ≥ half` needs `d₁ ≥ 1`).
The analytic assembly (trivial small-n bound; `Q_polynomial_decay` pointwise +
`hold_weight_expect` at `m = n/2` + `(n/2)^{-A} ≤ 3^A n^{-A}`) is fully proved.

**Open ledger for the §7 probability side is now**: `Q_black_edge` (X8/X10 kernel) +
the three X5 bridge sorries + `key_fourier_decay`'s reduction chain (X1/X2, Fourier
side) + upstream S-chain. Next: prove `hold_tsum_step` (most mechanical of the three),
then `bridge_renewal`, then `bridge_vector`.

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
