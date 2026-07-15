# Handoff: C8 (5.16) integral test PROVED axiom-clean; C8 down to 2 leaves

**Date**: 2026-07-15. **Branch** `main`, **HEAD `80153bc`**. Build 🟢 green (full `lake build`, 3322
jobs; pre-commit verified each commit). Tree clean, nothing uncommitted.
**Read `DIRECTION.md` first** — its CURRENT DIRECTIVE (deep-reflection block 2026-07-15) outranks this.
Campaign: C10 ✅ → C8 (pin ✅) → C7 (prove ✅) → **C8 close (IN PROGRESS)** → C9.

## What this lap did (C8 close leg — the (5.16) window term)

The previous lap PROVED the route-decisive reindex crux (`approxMainTerm_eq_steppedMid`). This lap
attacked the (5.16) window term of C8, which was one opaque `sorry` (`passtime_window_inner`).

1. **Decomposed `passtime_window_inner` (5.16)** into a **proved reduction skeleton** + two named
   source-backed leaves: the event `{passes ∧ T_x ∉ I_y}` ⊆ `{¬odd} ∪ {¬good tuple} ∪ Edge` (mod the
   even-support null set), bounded via `approx_good_tuple_whp` (5.12, proved) + the edge mass.
2. **PROVED `passtime_edge_mass`** — the (5.16) integral test — **fully, axiom-clean**
   (`[propext, Classical.choice, Quot.sound]`): `ℙ(N_y ∈ Edge) ≤ 20000·log^{-1/5}x`. Six reusable
   axiom-clean bricks landed en route (all in `Sec5/ApproxFormula.lean`):
   - `logUnifOdd_expect_indicator_eq` — `expect(𝟙_S) = (∑_{W∩S} 1/N)/windowMass` (the reduction plumbing);
   - `logWindow_odd_ap` + `windowMass_eq_ap_sum` — the odd-AP decomposition of the window, factored
     out of `intTest_D_lower`'s inlined setup;
   - `windowMass_ge_clog` — denominator `windowMass y (y^α) ≥ (1/10000)·log x` (via
     `harmonic_ap_integral_bound`, the log-growth lower bound, sharper than `intTest_D_lower`'s `≥1/8`);
   - `windowMass_le_half_log` — integral-test upper bound `windowMass lo hi ≤ ½·log(hi/lo)+2/lo`;
   - `mem_logWindow_iff` — clean window membership.

   The numerator bound routes each edge slab `W∩{N≤y·eˢ}`, `W∩{y^α·e⁻ˢ≤N}` (`s = log^{0.8}x`) into a
   sub-window via `mem_logWindow_iff`, bounds each mass by `½·s+O(1/y)`, giving numerator `≤ 2·log^{0.8}x`
   (using `2eˢ ≤ y^α`). Ratio = `2·log^{0.8}/((1/10000)log x) = 20000·log^{-0.2}x`.

## State: 5 sorries + 0 orange nodes

- `Statement.lean:24,31` — the two headline stubs (Thm 1.3 / Thm 3.1), frozen; discharge when C8/C9/C6 land.
- `Sec5/FirstPassage.lean:1399` — C9 `stabilization` (Prop 1.11), consumes C10 ✅ + C8.
- `Sec5/ApproxFormula.lean:826` — **`passtime_edge_of_good`** (the (5.15) POINTWISE inclusion) — C8.
- `Sec5/ApproxFormula.lean:1887` — **`first_passage_stepback_reduce`** (5.17) event reduction — C8.

`fine_scale_mixing` (C10), `first_passage_nonescape` (C7), `approxMainTerm_eq_steppedMid`,
`passtime_edge_mass` all `#print axioms` = trust base only. `first_passage_approx` (C8) =
trust base + `sorryAx` (the 2 leaves above + `passtime_edge_of_good`, via the assembly triangle).

## Next steps (in the CURRENT DIRECTIVE's scope — close C8, then C9)

1. **`passtime_edge_of_good` (`:806`)** — the LAST piece of (5.16). The (5.15) pointwise inclusion:
   on the good-tuple event, `passes ∧ T_x ∉ I_y ⟹ N ∈ Edge x y` (within `exp(±log^{0.8}x)` of a
   window endpoint). **Verified TRUE by hand** (see the lemma docstring): the orbit estimate (proved,
   `syr_iterate_good_bracket'`) gives `T_x(N) ≥ (log(N/x)−log2·log^{0.6}x)/log(4/3)` (lower orbit bound)
   and `T_x(N) ≤ n*` for explicit `n* ≤ nZero x` (upper orbit bound, absorb `+3^{n*}` since `3^{n*} ≤ x/2`);
   rearrange against `IyLo`/`IyHi` (`log(4/3)>0`), using `log(4/3)·log^{0.8}x + O(log^{0.6}x) ≤ log^{0.8}x`.
   Closing this makes `passtime_window_inner` (and hence `approx_passtime_window`, the C7 consumer) go
   axiom-clean. **Watch the `linarith only` gotcha below.**
2. **`first_passage_stepback_reduce` (`:1887`)** — the (5.17) event reduction. Forward inclusion is
   EXACT (`firstPass_event_stepback_subset` ✅); remaining = reverse inclusion + the `E'` size window
   `exp(±log^{0.7}x)(4/3)^{m₀}x` (orbit estimate `syr_iterate_good_bracket'` + `two_rpow_slack_le_exp`
   PROVED — missing piece is the `IyLo/IyHi` interval algebra) + nested `𝒜⁽ⁿ⁰⁾ ⊂ 𝒜⁽ⁿ⁻ᵐ⁰⁾`.
3. Then **C9 `stabilization`** (`FirstPassage.lean:1399`), then C6 → the two `Statement.lean` headlines.

## Rails / notes
- **Do NOT edit ratified pins** (`Eprime`, `Iy`, `firstPassMid`, `steppedMid`, the C8 statements, the
  `approxMainTerm` RATIFY-C8-v2 re-pin). Watched: `fine_scale_mixing`, `first_passage_nonescape`,
  `stabilization`, all ratified pins.
- **`linarith` gotcha hit this lap**: with `hMy : ↑(2^(3*nZero x)) ≤ y` in context (a big symbolic
  ℕ→ℝ cast), plain `linarith [h]` FAILS to find a trivial contradiction — its cast preprocessing chokes
  on the `2^(3*nZero x)` atom. Fix: use **`linarith only [...]`** to exclude the poison hypothesis.
  This bit twice; both slab-bound and final-ratio steps needed `only`.
- `Real.log_two_gt_d9` / `Real.log_two_lt_d9` are the numeric bounds on `log 2` for the `x ≥ 2^2000 ⇒
  log x ≥ 1386` type steps. `Finset.sum_union_inter` has implicit args `s₁ s₂` (not `s t`).
- Numeric-trap hygiene still owed: add a `tools/check_blueprint.py` entry for RATIFY-C8-v2 (probe at
  `tools/sandbox/tao_c8_truncation_probe.py`) — per blueprint_rules "numeric trap" rule.
- `git-safe` at `/Users/gotrevor/personal/bin/git-safe` (`export PATH="$HOME/personal/bin:$PATH"`).
  Axiom-check recipe: write `TaoCollatz/ZZ_ax.lean` with `#print axioms`, `lake env lean` it, `rm -f`.
- **Work report: 5 sorries + 0 orange nodes** (2 headline, C9, `passtime_edge_of_good`,
  `first_passage_stepback_reduce`). The (5.16) integral test is CLOSED; C8 has 2 leaves left.
