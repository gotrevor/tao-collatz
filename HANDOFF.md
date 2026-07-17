# HANDOFF — big-C campaign, lap 7 (2026-07-17)

## Lap 7 progress (in flight)

- **`few_white_mass_le` explicit (DONE, `f24aa11`)**: defs `K_fewWhite/R_fewWhite/P_fewWhite/
  B_fewWhite/Cthr_fewWhite` + `one_le_R/P_fewWhite`, `R_fewWhite_bound`; `_core` rail
  (`A',ε₀,g,K,R,P,B,Cthr_e,Cthr_c` ∀-bound, the three mass terms as hypotheses, threshold
  max-expr explicit in statement); `_at` instantiates at the explicit constants (delegation
  via defeq — `le_of_eq rfl`/`rfl` close `hPeq`/`hBdef` through the defs); watched ∃-form
  delegates. Differ 35/35, 18/18 checks, full build green.
- **Damping chain explicit (DONE, next commit)**: def `Cthr_dampingCol A =
  max (max (Cthr_fewWhite A) (T_colTail A (P_fewWhite A))) 10` — **this is the reified C2**.
  `_at` siblings for `damping_expectation_le`, `damping_column_mass_le`,
  `damped_iter_expectation_le`, `Q_black_edge_case3` (watched; delegate byte-identical).
  New rail: **revert+generalize** — `have h := <upstream_at>; revert h; generalize
  P_fewWhite A = P; intro h ...` then original body verbatim (avoids set/motive issues in
  `Fin P` positions; remember to also revert `one_le_P_fewWhite` when the body's omegas
  need `1 ≤ P`; repo linter wants merged `intro` lists).
- **Next: STEP-2 wiring of C2 into `prop_7_8_at`** (BlackEdgeQ.lean): threshold
  `max (max (C_hold A) (Cthr_dampingCol A)) 1` → `Q_polynomial_decay` C0 symbolic → extend
  check18 with the C0-arm assert. Then `renewal_white_encounters` (Bridge.lean) + Fourier,
  Sec6/Sec5/Sec3, then STEP 3.

---

# (lap 6 baton below — still the reference for method rails)

**Read `DIRECTION.md` first — it outranks this file.** STEP 2 (sibling+delegate, bottom-up)
is live against the judge re-pin `CTao = 10^(10¹¹)`. Then read the lap-6* entries in
`PENDING_WORK.md`, and `STATUS.md` for the durable overview.

## State (branch `explicit-big-c`, all committed, build green)

- HEAD `937f407`. Full `lake build` green (3327 jobs). Differ vs re-pin baseline:
  `tools/tao_stmt_diff.py fabea6f HEAD` → **35/35 character-identical** every commit.
  `check_blueprint.py` all 18 pass (17 = ladder GO 9.39×10¹⁰ < 10¹¹, 18 = symbolic mirror).
- **Exactly 1 real `sorry`** in `TaoCollatz/`: `Statement.lean:68`
  (`tao_collatz_quantitative_fully_explicit`, the campaign pin). The 3 merged headlines
  are `#print axioms`-clean (trust base only). Everything else is docstring history.

## What lap 6 did (review + Case3 E∗/few_white cluster)

- **Review lap (6):** validated direction (sound + current, no route-trigger fired),
  created durable `STATUS.md`, left operator-owned CURRENT DIRECTIVE untouched.
- **Forward-trace of C2 (6c):** `Q_black_edge_case3` exposes ONLY a threshold `Cthr : ℕ`
  (no free multiplicative constant); it passes UNCHANGED up through the damping chain and
  combines only at `few_white_mass_le`. C2 feeds the ladder as `Cthr^A` in
  `Q_polynomial_decay`'s C0-arm (dominated by the `n₀^B` head — lap-5 audit). **So the
  whole damping chain above `few_white_mass_le` is a threshold passthrough.**
- **Nodes made explicit this lap** (Case3.lean, all ∃-forms delegate byte-identically):
  - `few_white_reach_mass_le` → `_at` at `eps0_manyTri`/`g_manyTri`.
  - `bigTriangle_walk_le_rpow` → `_explicitC` at `C_encTri`/`c_encTri`, A₀=5.
  - `estar_union_le_rpow` → defs `C_estarUnion=4·C_encTri`, `c_estarUnion`, `A0_estarUnion`
    (via `_core` rail); `_pos`/`one_le_` lemmas.
  - `estar_scaled_numeric` → defs `Kthr_estarScaled`, `Warg_estarScaled`,
    `A0_estarScaled C' c A₀e`; `_at` via `unfold`-prefix + verbatim body.
  - `few_white_estar_mass_le` → def `A0_fewEstar`; `_at` at `A'=2A+A0_fewEstar`,
    `Cthr=10^30`.

## Next steps (bottom-up continuation, in order)

1. **`few_white_mass_le`** (Case3:~2505, **WATCHED** — keep ∃-form byte-identical, differ
   must stay 35/35). It combines all thresholds (line ~2545):
   `Cthr = max (max 10^30 (T_colTail A P)) (max (10·g_manyTri) (max ⌈B^2.5⌉ ⌈10·500^(1/A)⌉))`,
   `P = encWindowIter (2A+A0_fewEstar) (K+1) R`, `K = ⌈(A+3)log10/epsBW³⌉₊`,
   `R = ⌈((K+1)+(A+5)log10+2)/eps0_manyTri⌉₊`, `B = 4^{2A+A0_fewEstar}(1+P)^3`.
   **All inputs are now explicit** — name `P_fewWhite A`, `K_fewWhite A`, `R_fewWhite A`,
   `Cthr_fewWhite A` as defs, write `_explicitC` sibling, delegate. Watch: `col_tail_mass_le`
   is called with `P := P_fewWhite A`, so `T_colTail A P_fewWhite` appears.
2. **Damping passthrough** (Case3): `damping_expectation_le` → `damping_column_mass_le`
   (obtains `Cthr, P` from few_white; may combine with `col_tail`) → `damped_iter_expectation_le`
   → `Q_black_edge_case3` (this reifies **C2** = the final Cthr). Each currently carries
   `Cthr`/`P` unchanged — mostly `obtain … refine ⟨Cthr, …⟩` passthroughs; make each an `_at`.
3. **Wire C2 into `prop_7_8_at`** (BlackEdgeQ.lean): threshold `max (max (C_hold A) C2) 1`
   → `Q_polynomial_decay` C0 fully symbolic → extend check18 with the C0-arm assert
   (assert C0-arm < head numerically; see lap-5 finding — the `e^{ch·Mth}` term collapses
   logarithmically through threshold conversions).
4. Then `renewal_white_encounters` (Bridge.lean:~507) + Fourier passthrough
   (`key_fourier_decay` → `charFn_decay`), then Sec6 (8 slots), Sec5 (37), Sec3 (7),
   then STEP 3 (`C_ladder ≤ CTao` + Statement.lean discharge).

## Method rails (binding, learned)

- `_core` for bodies >100 lines: constants as ∀-bound vars + hypothesis bundle, body
  verbatim, sibling = core @ defs + `unfold` + `exact`. (`set+clear_value` refuted — times out.)
- **For a `set`-based witness** (like `estar_scaled_numeric`): `unfold <defs>` at the body
  head, keep the original `set`-lines verbatim; they re-abstract the unfolded formulas cleanly.
- **Delegate through a def by defeq:** `le_trans hest (hnum A hA)` closes even when `hnum`
  mentions `A0_estarScaled …` and the goal mentions `A0_fewEstar` (its def) — `le_trans`
  unifies by defeq. But `linarith` does NOT unfold defs: give it the fact ascribed to the
  def-atom (`have h : … ≤ A0_fewEstar := (…).1`).
- Statements byte-identical; never touch a watched pin (differ per commit).
- Never evaluate big numerals; log-arithmetic only. `git-safe` for git writes.

## Watchouts

- Comparator/ + formalization.yaml judge-owned; comparator CI red-until-done by design.
- `lean-sorry -c TaoCollatz` = 1 (Statement.lean pin) is correct.
