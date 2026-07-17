# HANDOFF — big-C campaign, laps 4–5 (2026-07-17)

**Read `DIRECTION.md` first — it outranks this file.** Judge re-pin `CTao = 10^(10¹¹)`
is live; step 2 (sibling+delegate, bottom-up) is in progress. Then read the lap-4/5
entries in `PENDING_WORK.md` (and lap-2/2b/3 for the earlier defs).

## State (branch `explicit-big-c`, all committed, build green)

- HEAD `98bcf6b` (Lemma 7.9 + F* chain). **Always diff vs the re-pin commit:**
  `tools/tao_stmt_diff.py fabea6f HEAD` → 35/35 character-identical at every commit
  this lap. `check_blueprint.py` all green (17 = ladder GO, 18 = symbolic-def mirror).
- **Sec7 ≈ 26 of 22+thresholds sites done** (the census over-counts because thresholds
  and sub-engines got their own defs). Fully explicit now:
  - X6 chain (laps 2–3): `C_hold`-tower, `c/C_fpLocation` etc. (Monotone/HoldLocal/
    FpLocation).
  - (7.61) tails (lap 4): `C_fpCol`, `K_rowG`, `c/C_fpColDev`, `c/C_fpColTail`,
    `c/C_fpHeight`, `c/C_fpHeightTail` (FpLocation + ManyTriangles);
    `T_colTail A P` (Case3 `col_tail_mass_le`).
  - X10 (laps 4–5): `C_apexProx=2`/`S_apexProx=1e8` (X10a), `K_intG` (Gweight-ℤ
    engines), `C_encSep` (X10b), `M_encTri=1e27`/`c_encTri`/`C_encTri`
    (`triangle_encounter_le_rpow`, 420-line core), `C_triEnc = max C_encTri 1e11`
    (the pinned `triangle_encounter_le`).
  - X9 white-exit (lap 5): `T_gaussColTail c C'`, `T_outStrip`,
    `fpDist_any_triangle_le_at` (thr 0), `p_whiteExit=3/4`/`T_whiteExitDeep`
    (`fpDist_white_exit_deep`), `eps0_manyTri=1/100`/`g_manyTri`
    (`many_triangles_white` → `fstar_markov` → `reaches_fewWhite_mass_le(_ten)`).

## Key finding (lap 5) — the e^{ch·Mth} scare is benign

`C_encTri` contains `exp(c_fpHeightTail·10²⁷)` (log₁₀ ≈ 8.5×10²¹ ≫ ladder head
9.39×10¹⁰). Traced consumption: every downstream hop (few_white → Q_black_edge_case3
→ prop_7_8 → Q_polynomial_decay → renewal_white_encounters C0-arm) converts constants
into THRESHOLDS via `T_expRpow`-style lemmas — logarithmic collapse — so the C0-arm
lands at log₁₀ ~10⁸–10⁹ and check17's GO stands. **When Q_polynomial_decay's C0 is
fully explicit, extend check18 to assert C0-arm < head numerically.**

## Method rails (binding, learned)

- `_core` pattern for any body >100 lines: constants as ∀-bound vars + hypothesis
  bundle, body verbatim, sibling = core @ defs + `unfold` + `exact`. (`set+clear_value`
  refuted — times out.)
- Unused hypothesis binders in cores → `_h` prefix or the build errors
  (warningAsError). Docstrings strand when defs are inserted above a theorem — move
  them onto the delegating sibling.
- Statements byte-identical; never touch a watched pin (differ per commit).
- Never evaluate big numerals; log-arithmetic only.

## Next steps (bottom-up continuation, in order)

1. Case3.lean `few_white_reach_mass_le` (≈1700): ε₀/g passthrough from
   `reaches_fewWhite_mass_le_ten_at` — same core/`_at` pattern as the fstar chain.
2. `bigTriangle_walk_le_rpow` (Case3:467) and `estar_union_le_rpow` (Case3:~1200):
   over `triangle_encounter_le_rpow_explicitC` (already explicit).
3. `few_white_estar_mass_le` (∃A' ∃Cthr) → `few_white_mass_le` (∃P ∃Cthr; consumes
   `T_colTail`) → `damping_expectation_le` → `damping_column_mass_le` →
   `damped_iter_expectation_le` → `Q_black_edge_case3` — this reifies `C2`, then
   wire it into `prop_7_8_at` (BlackEdgeQ.lean) → `Q_polynomial_decay` constant
   fully symbolic → extend check18 with the C0-arm assert (see key finding).
4. Then `renewal_white_encounters` (Bridge.lean:507, `n0 := 2·C_hold+2`, witness
   max) + Fourier passthrough (`key_fourier_decay` → `charFn_decay`), then Sec6
   (8 slots), Sec5 (37), Sec3 (7), then STEP 3 (the `C_ladder ≤ CTao` inequality
   and the Statement.lean discharge).

## Watchouts

- Comparator/ + formalization.yaml judge-owned; comparator CI red-until-done is by
  design. `lean-sorry -c TaoCollatz` = 1 (Statement.lean pin) is correct.
- `git-safe` for all git writes (bare `git show` OK for reads).
