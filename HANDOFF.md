# HANDOFF — big-C campaign, laps 2–3 (2026-07-17)

**Read `DIRECTION.md` first — it outranks this file.** Judge re-pin `CTao = 10^(10¹¹)`
is live; step 2 (sibling+delegate, bottom-up) is in progress. Then read the lap-2/2b/3
entries in `PENDING_WORK.md`.

## State (branch `explicit-big-c`, all committed, build green)

- HEAD: lap-4 series through `67c580f` (X10b). Always diff vs re-pin commit `fabea6f`. Differ `tools/tao_stmt_diff.py fabea6f HEAD`:
  35/35 character-identical (always diff vs the re-pin commit `fabea6f`, not the tool's
  default). check_blueprint.py all green incl. check18 (mirrors the new symbolic defs).
- **Done so far (Sec7 ≈ 21 of 22+thresholds — see PENDING_WORK.md lap-4 for the new defs):**
  - `hold_weight_expect` (ladder-dominant node): `deltaBW/cHold/K_geom/T_powGeom/
    K_hold/M1_hold/T_hold/C_hold` + core + `_explicitC` + delegation (Monotone.lean).
  - `Q_white_case1_explicitC` (at `C_hold A`); combinator cores `prop_7_8_at`
    (threshold `max (max (C_hold A) C2) 1`) and `Q_polynomial_decay_at` (constant
    `(max C0 1)^A`) in BlackEdgeQ.lean — the decay spine goes fully symbolic the moment
    Case3's black-edge threshold `C2` is reified.
  - Threshold leaves `T_logSq/T_expNeg/T_logLin` (BlackEdge.lean), `T_expRpow` (Case3).
  - X6 chain complete: `c_holdLocal=1/400`, `C_holdLocal=6.5536e12` (HoldLocal.lean),
    `gamma_holdStep/C_holdStep`, `K_sqrtExp`, `C_renewalWeight`, `c_renewalMass/
    C_renewalMass`, `c_fpLocation/C_fpLocation` via `fpDist_location_bound_core`
    (FpLocation.lean).

## Method rails (learned, binding on cost grounds)

- Statements stay byte-identical: original `∃`-form is re-proved as a one-line
  delegation to the `_explicitC` sibling. Never touch a watched statement.
- **For >100-line proof bodies use the `_core` pattern** (constants as ∀-bound
  variables + hypothesis bundle, body verbatim, sibling = core @ defs + `unfold` +
  `exact`). `set x := def` + `clear_value` leaks def-bodies into `linarith`/`whnf`
  and times out at default heartbeats — refuted, don't retry.
- Small bodies: `unfold defs; intro …` then body verbatim works.
- Never evaluate big numerals; log-arithmetic only. Extend check18 when a new def's
  value matters to the ladder.

## Next steps (bottom-up continuation)

1. `fpDist_col_le` (FpLocation.lean:~2760): witness `(c, C·e^{-c}/(1-e^{-c}))` over
   `fpDist_location_bound` — small body, unfold pattern suffices.
2. ManyTriangles.lean: `fpDist_col_dev` (witness from `fpDist_location_bound` +
   `sum_range_Gweight_le`), `holdSum_col_tail`, `fpDistPlus_col_tail`
   (witness `min cd (1/2000)`, `Cd+1`).
3. Case3.lean `col_tail_mass_le`: threshold `400(P+1)+32+T_expRpow A (c/16960) (1/(4C))`.
4. Then upward: `few_white_mass_le` (+ its leaves `estar_union_le_rpow`,
   `reaches_fewWhite_mass_le(_ten)`, `fstar_markov`, `few_white_estar_mass_le`,
   `few_white_reach_mass_le`, geometry leaves `triangle_encounter_le_rpow`,
   `many_triangles_white`, `bigTriangle_walk_le_rpow`) → `damping_expectation_le` →
   `damping_column_mass_le` → `damped_iter_expectation_le` → `Q_black_edge_case3`
   → wire `C2` into `prop_7_8_at` → `Q_polynomial_decay` constant symbolic.
5. Then `renewal_white_encounters` (Bridge.lean:507: `n0 := 2·C_hold+2`, witness max)
   and the Fourier passthrough (`key_fourier_decay` → `charFn_decay`), then Sec6.
6. Report census per lap: Sec7 n/22, Sec6 n/8, Sec5 n/37, Sec3 n/7.

## Watchouts

- Comparator/ + formalization.yaml are judge-owned; comparator CI red-until-done is
  the design. `lean-sorry -c TaoCollatz` = 1 (the Statement.lean pin) is correct.
- Docstring placement: inserting defs above a theorem strands its docstring — move it
  onto the delegating theorem (two build failures this lap were exactly this).
- `git-safe` for all git; bare git is hook-blocked (except `git show` for reads).
