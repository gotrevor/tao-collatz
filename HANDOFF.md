# HANDOFF — big-C campaign, lap 8 in progress (2026-07-17)

## 🚨 JUDGE-FLAG (lap 8): C0-arm NO-GO — read PENDING_WORK.md lap-8 entry

The now-reified C0-arm (`C_polyDecay A = (max (Cthr_prop78 A) 1)^A` →
`renewal_white_encounters`' witness) EXCEEDS the live pin `10^(10¹¹)` robustly
(`log₁₀ ≥ 4.5×10³²` independent of unresolved constants; honest trace far larger).
check19 is the machine-checked trace; check17's GO covered only the head arm.
STEP 3 is unprovable over the current tower. Per the never-inflate/STOP rule the
discharge thread is STOPPED pending an operator ruling; step-2 transcription
continues (next: `renewal_white_encounters` explicit, Fourier passthrough, Sec6).

## Lap 8 progress so far

- **`Q_black_edge_case2` → `Q_black_edge` → `prop_7_8` all explicit (`eae7e15`)**:
  `fpDist_white_exit_at` wrapper (deep `_at`, budget hypothesis dropped); defs
  `delta_case2 = (1-e^{-epsBW³})·p_whiteExit/2`, `Cthr_case2 A = max (max T_whiteExitDeep
  (T_edgeWeight A delta_case2)) 2` (BlackEdgeQ.lean); `Cthr_blackEdge A = max (Cthr_case2 A)
  (Cthr_dampingCol A)`, `Cthr_prop78 A = max (max (C_hold A) (Cthr_blackEdge A)) 1`
  (Case3.lean). `Q_black_edge_at` inlines the `Q_black_edge_of_case3` combinator body;
  `prop_7_8_explicitC` = `prop_7_8_at` @ explicit args + unfold. ∃-forms delegate.
  Differ 35/35, checks 18/18, full build green.
- **Sec7 spine COMPLETE (`8b8fc5b`)**: `C_renewalWhite A = max ((2·C_hold A+2)^A)
  (C_polyDecay A·e^{ε³/2}·3^A)` (Bridge.lean); `renewal_white_encounters_at`,
  `key_fourier_decay_at` (Reduction.lean), `charFn_decay_at` (Decay.lean) — the whole
  §7 chain from the fpDist kernels to Prop 1.17 is now constant-explicit. Watch: the
  delegating ∃-forms need `open Classical in` (the filter's DecidablePred).
- **Sec6 head+main explicit (`f74bbfc`, `4ad9985`)**: MixingCore trio
  (`tail_factor_norm_le`/`head_factor_norm_le_charFn`/`dft_condDens_norm_le` at
  `C_renewalWhite`), `head_uniform_highFreq_of_margin_at`; cutoffs `N_caWindow A`,
  `N_condWindowB C` (both via the existing `T_logLin`); `C_oscMainHigh A =
  3·C_renewalWhite(mainDecayExponent A)·40^(mainDecayExponent A)`, `N_oscMainHigh A`,
  `osc_mainHigh_bound_at`. Rail note: when the original docstring precedes the spot
  where the new def goes, MOVE the def+its docstring ABOVE the original docstring
  (two adjacent docstrings = parse error).
- **Sec6 COMPLETE (`e5f102c`, `fa489fb`)**: MixingError fully explicit (cutoffs
  `N_logGe/N_rpowAbsorb/N_caThrNonneg/N_g1/N_g2/N_g3/N_probGlobalGood`, error constant
  = numeral 6); `S_zeta2` + parameterized telescope `osc_syracZ_regime_telescope_at`
  (MixingRegime); `C_oscHigh A = 2·max (C_oscMainHigh A) 6`, `N_oscHigh`,
  `C_fineScale A = 2·(max 9 (N_oscHigh (A+2)))^A + C_oscHigh (A+2)·S_zeta2`;
  watched `fine_scale_mixing` delegates. Rail reminder: adjacent docstrings = parse
  error — put the new def+docstring ABOVE the original docstring, or merge into one.
- **Sec5 C10 seam explicit (`0fbaa14`)**: leaves `X_twoMZero = e^100000`
  (ApproxFormula), `X_mZeroLin = e^200000`, `X_cnBound = e^1024` (const 4);
  `C_mainZbridge = 4·C_fineScale 1.7·(1/200000)^{-1.7}`, `X_mainZbridge`;
  `harmZfine_to_mainZ_at`; the c-campaign `_explicit` ∃-form delegates. Sec5 slot
  census: ApproxFormula 23, FirstPassage 16, Stabilization 17 (mostly `∃ C x₀` pairs).
- **Next (Sec5 continuation, bottom-up)**: `perNHarmonic_eq_harmZfine_approx_explicit`
  (B1) and its inputs, then `harmonic_to_Z_explicit` (combines B1+B2, Stabilization
  ~2200), up through `perNTerm_eval` → `stabilization`. Then FirstPassage,
  ApproxFormula leaves, Sec3 (7), Syracuse 1, Prob 1.
  STEP 3 remains STOPPED on the lap-8 JUDGE-FLAG.

---

# (lap 7 baton below)

## State at lap end (branch `explicit-big-c`, all committed, build green)

- HEAD `95cd52f`. Full `lake build` green (3327 jobs) at every commit; differ
  `tools/tao_stmt_diff.py fabea6f HEAD` 35/35 character-identical; `check_blueprint.py`
  18/18. Still exactly 1 real `sorry` (`Statement.lean:68`, the campaign pin).

## Lap 7 progress (complete)

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
- **Case-2 edgeWeight subtree explicit (DONE, `95cd52f`)**, BlackEdge.lean: defs
  `T_mgfNumeric A δ c C'` (= 25+N₁+N₃+N₈₅+N₄ over `T_logSq`/`T_expNeg`),
  `T_fstMgf A δ = T_mgfNumeric A δ c_fpLocation C_fpCol`, `T_fstTail A δ`,
  `T_holdTail A δ`, `T_edgeWeight A δ` (at `ε = min(δ/8,2)`); `_at` siblings, ∃-forms
  delegate. **Rail refinement:** after `unfold T_*`, `set c : ℝ := c_fpLocation with hcdef`
  re-binds the ∃-obtained constant NAMES the body already uses → bodies port verbatim
  with zero textual edits (set also rewrites earlier hyps like `hcol`). Keep the original
  `set_option maxHeartbeats` + docstring ON the `_at` (moving the statement leaves them
  orphaned before the def — parse error).

## Next steps (bottom-up, in order)

1. **`Q_black_edge_case2` explicit** (BlackEdgeQ.lean:~117): witness is
   `max (max Cw Ce) 2` with `Cw` from `fpDist_white_exit` (= `T_whiteExitDeep`, via
   `fpDist_white_exit_deep_at`; the wrapper `fpDist_white_exit` in BlackEdgeQ.lean:40
   delegates — give it an `_at` too) and `Ce = T_edgeWeight A δ*` at whatever `δ` the
   case2 body instantiates (read the body around BlackEdgeQ.lean:117-142; the obtain is
   `fpDist_edgeWeight_le A hA` — find the δ argument). Name `Cthr_case2 A`.
2. **`Q_black_edge` explicit** (Case3.lean end): witness `max (Cthr_case2 A)
   (Cthr_dampingCol A)` via `Q_black_edge_of_case3` — that combinator itself does the
   max; either make an `_at` of the combinator in BlackEdgeQ.lean or inline in Case3.
3. **`prop_7_8` explicit**: `prop_7_8_at` already takes `C2` as an arg (BlackEdgeQ:337);
   witness `max (max (C_hold A) C2) 1` with `C2 = max (Cthr_case2 A) (Cthr_dampingCol A)`.
   Then `Q_polynomial_decay` C0-arm fully symbolic (Monotone.lean consumer) → extend
   check18 with the C0-arm assert (lap-5 finding: C0-arm ≪ `n₀^B` head).
4. Then `renewal_white_encounters` (Bridge.lean:~507) + Fourier passthrough, Sec6 (8),
   Sec5 (37), Sec3 (7), then STEP 3 (`C_ladder ≤ CTao` + Statement.lean discharge).

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
