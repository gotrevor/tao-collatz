# PENDING_WORK — effective-constants campaign

*Lap scratchpad + JUDGE-FLAG landing zone. DIRECTION.md outranks everything here.*

## Campaign state (2026-07-16, campaign start)

- ✅ **Pre-campaign fix landed on this branch**: `hold_weight_expect` (`Sec7/Monotone.lean`)
  no longer mints its witness from rate-free limits — explicit-threshold private lemmas
  added, statement byte-identical, full build green (3327 jobs),
  `lean-axiom-gate --exact` ✓ on `tao_collatz_quantitative` + `hold_weight_expect`
  (2026-07-16). This was the `C`-side blocker documented in PR #6.
- ✅ STEP 1 — c8/cs branches traced to numerals (2026-07-16, this lap). Result: **no branch
  is below the note's value**; `c₀ = 1/(640000000 · Real.log 2)` lower-bounds every branch.
  JUDGE-FLAG below has the per-hop trace. Awaiting operator sign-off before step 3's def.
- ✅ STEP 2 — sibling+delegate de-existentialization of the `c`-path COMPLETE (2026-07-16,
  laps 1–2). Every `c`-carrying hop from the spine to the leaves is now a named
  `noncomputable def` with an explicit-`c` sibling; all ratified originals byte-identical
  (differ ✓ each commit), delegating. The def tree:
  - c7 chain: `c_geomTail := 1/400` → `c_valuationDist c₀` → `c_valSumGeom` →
    `c_valSumTail := c_valSumGeom/20` (= `1/(640000000·log 2)`) → `first_passage_nonescape_explicit`.
  - c8 chain (`Sec5/ApproxFormula.lean`): `c_goodTupleDev := 1`, `c_edgeMass := 1/5`,
    `c_passtimeInner`, `c_passtimeWindow := min c_valSumTail c_passtimeInner` (wires c7→c8),
    `c_windowReduce`, `c_earlyReturn := 1`, `c_steppedMid`, `c_truncation := 1`,
    `c_affineReindex`, `c_fpApprox` → `first_passage_approx_explicit` (WATCHED orig intact).
  - cs chain (`Sec5/Stabilization.lean`): `c_perNHarm := 0.3`, `c_harmZfine := 0.3`,
    `c_mainZbridge := 1`, `c_harmonicZ`, `c_perNTermEval`, `c_IyRatio := 0.2`,
    `c_approxToZ` → `c_stab := min (min c_valSumTail c_fpApprox) c_approxToZ` →
    `stabilization_explicit` (WATCHED orig intact).
  - Sec3 glue: `c_ladder := min c_valSumTail c_stab` → `..._explicit` siblings through
    `tao_collatz_quantitative_spine_explicit` (the lemma step 3 consumes).
  Axiom gate exact throughout. *(Unratified new siblings: judge to read; they are
  statement-copies of ratified originals with a def in the c-slot.)*
- ⬜ STEP 3 — append to `TaoCollatz/Statement.lean` (ONE trusted file = one audit surface):
  `cTao` + `tao_collatz_quantitative_explicit`; existing headlines byte-identical.
- ⬜ STEP 4 — OPERATOR-GATED: comparator additions + PR #6 note update.

## JUDGE-FLAGs

### JUDGE-FLAG: step-1 branch trace complete — propose `cTao := 1 / (640000000 * Real.log 2)` (2026-07-16)

Source-level trace of every `c`-carrying hop from the spine down. All three `stabilization`
branches and the Sec3 glue are now traced to numerals; **the c7 value is the global minimum**
and the note's proposed value is confirmed. Operator sign-off requested on the `cTao` def.

**c7 branch (`first_passage_nonescape`)** = `1/(640000000·ln 2)` ≈ 2.2547e-9:
- `geomHalf_tail_bound` witness `ct = 1/400` — `Prob/LocalInstances.lean:544`
- `valSum_lower_geom` (`Sec5/FirstPassage.lean:1211-1217`): `d := ct·0.1 = 1/4000`;
  `cg := finalDecay d / log 2` with `linearDecay d = min(d²/2, d) = 1/32000000`
  (`Syracuse/ValuationDist.lean:921`), `finalDecay = min(log 2, ·) = 1/32000000` (`:965`)
  → `cg = 1/(32000000·ln 2)`; `cd` from `valuation_dist 1 K` (`ValuationDist.lean:999`,
  internal `d = 1/400·1`, so `cd = 1/(320000·ln 2)`); witness `c := min cd cg = cg`.
- `valSum_lower_tail` (`FirstPassage.lean:1295`): `c' = c/20` via `two_rpow_neg_nZero_le`
  (witness `⟨c/20, …⟩`, `:1185`) → `1/(640000000·ln 2)`.
- `first_passage_nonescape` (`:1484-1486`): passes `c` through unchanged.

**c8 branch (`first_passage_approx`, `Sec5/ApproxFormula.lean:3218`)** = `c7` exactly —
it **contains c7 as a sub-branch**: `c8 = min(window_reduce, affine_reindex)` where
- `window_reduce = min(cg', cw)` (`:1823`): `cg' = 1` (`goodTuple_prefix_dev_sum` witness
  `⟨1, …⟩`, `:600`, via `approx_good_tuple_whp` `:756` passthrough); `cw =
  approx_passtime_window = min(c₁, c₂)` (`:1741`) with `c₁` obtained from
  **`first_passage_nonescape`** (`:1739`) `= c7`, and `c₂ = passtime_window_inner =
  min(1, 1/5)` (`:1636`; `passtime_edge_mass` witness `⟨1/5, …⟩`, `:1466`).
- `affine_reindex = min(1, 1)` (`:3187`; `reverse_early_return_whp` `⟨1,1,…⟩` `:2850`;
  `truncation_error_bound` `⟨1,1,…⟩` `:3129`).
So `c8 = min(min(1, min(c7, 1/5)), 1) = c7`. Every non-c7 leaf is `≥ 1/5 ≫ c7`.

**cs branch (`approxMainTerm_window_stable`, `Sec5/Stabilization.lean:2725`)** = `1/5`:
passthrough of `approxMainTerm_to_Z = min(c1, c2)` (`:2633`) with `c1 = 0.2`
(`Iy_count_ratio` witness `⟨0.2, 6000, …⟩`, `:2547`) and `c2 = perNTerm_eval = min(cA, cB)`
(`:2495`), `cA = 0.3` (`perNTerm_harmonic_approx` `:1500`), `cB = harmonic_to_Z =
min(0.3, 1)` (`:2145`; `perNHarmonic_eq_harmZfine_approx` `⟨0.3, …⟩` `:2027`;
`harmZfine_to_mainZ` `⟨1, …⟩` `:2090`) → `cs = min(0.2, 0.3) = 1/5`.

**Sec3 glue** — `c` passes through unchanged at every hop:
`descentProb_base` obtains `first_passage_nonescape`, passes `c` (`Sec3/Reduction.lean:279-280`);
`descentProb_step` obtains `stabilization`, passes `c` (`:186-187`);
`descentProb_ladder` `c := min cb cs = min(c7, min(min(c7,c8),cs)) = c7` (`:310`);
`descent_whp` (`:396,410`), `window_bad_sum` (`:564,571`),
`tao_syracuse_quantitative_sum` (`:673,690`), `tao_collatz_quantitative_spine`
(`:1334-1335`) all reuse `c` verbatim.

**Conclusion**: `stabilization`'s witness `min (min c7 c8) cs = c7`, the ladder min is `c7`,
so the headline's `c` *is* `1/(640000000 · Real.log 2)`, and
`c₀ := 1/(640000000 · Real.log 2)` satisfies `c₀ ≤ branch` for **every** branch (smallest
competing leaf: `cd = 1/(320000·ln 2)`; smallest numeral leaf: `1/5`). Proposed def for
step 3, per DIRECTION (symbolic, lower-bound-only):

```lean
noncomputable def cTao : ℝ := 1 / (640000000 * Real.log 2)
```

**Do-not-proceed gate honored**: step 3's def is NOT written; step 2 sibling+delegate work
(value-independent) proceeds meanwhile.
