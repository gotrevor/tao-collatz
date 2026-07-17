# HANDOFF — big-C campaign, lap 14 — FEASIBILITY MAP EXACT (check22): ONE DOOR REMAINS 🚪

**Read `DIRECTION.md` RESOLVED banner FIRST.** State: build green (3327), 2 sorries (pin +
`Q_black_edge_tight`), differ 35/35, checks **22/22**. Laps 13/13b/14 (same day): pin
resized to the machinery floor (lap 13, `e21a7a7`); Case-3 architecture floor found
(lap 13b, `8348028`); X10 read + exact feasibility map (lap 14, `499a6ab`).

**The map (check22, machine-checked):** budget `log₁₀ Cthr ≤ 3053`; floors — union
15041/12033, dilated single-hit 7542/6033 (all dead under X10b's √-spacing cap
`s'² ≤ 1+s`); **dilated + LINEAR spacing fits at 3019 (34 orders margin)**. Hold steps
have `d.1 ≥ 1` AND `d.2 ≥ 3` (both coordinates strictly monotone) — that is what makes
the dilated single-hit replace Tao's P-fold union (sweep `4P ≪ s`).

**NEXT (lap 15, decisive):** read `many_triangles_white` + the X10b proof chain
(`fpDist_any_triangle_le`) + paper Lemma 7.10/(7.11) (PDF in `papers/`): is the
√-spacing cap intrinsic triangle geometry, or is phase-matched size-`s'` triangle
spacing linear (`s' ≲ s/polylog` valid)? If LINEAR → build the dilated-hit lemma
(monotone coordinates; phase window dilates only linearly per `hX10a`) and Option B
proceeds at current `A`. If INTRINSIC → Option B at current `A` is dead; fire the
conditional JUDGE-FLAG (PENDING_WORK Lap 14: the `caConst` lever conflicts with the
judge's out-of-scope ruling; evidence = check22). Details: PENDING_WORK Laps 13b/14.

---

# HANDOFF — big-C campaign, lap 13 — TIGHT PIN RESIZED TO MACHINERY FLOOR; CRUX = `Q_black_edge_tight` 🎯

**Read `DIRECTION.md` RESOLVED banner FIRST** (Option B is the live route; the note there
mandating the constant "`(2·C_hold A + 2)^A`, no max" is amended by this lap's sizing
correction — see below and PENDING_WORK "Lap 13").

## State (branch `explicit-big-c`, all committed, build green)

`lake build` green (3327 jobs). Exactly **2 real sorries**: the pin (`Statement.lean:65`)
and the campaign crux **`Q_black_edge_tight`** (`Sec7/Bridge.lean:~737`). Differ
`tools/tao_stmt_diff.py fabea6f HEAD` 35/35; `blueprint_audit` clean;
`check_blueprint.py` **21/21** (check21 is new, lap 13). Headlines untouched.

## What lap 13 did (sizing correction on the lap-12 pin — my own unratified addition)

1. **Caught a born-wrong-by-tightness pin.** Lap-12's `C_Qtight ≈ (n₀/3)^A` is BELOW the
   `(C_hold A)^A` floor that `Q_polynomial_decay_at` can deliver (its constant is the
   trivial-regime crossover `(max C0 1)^A`, threshold `C0 ≥ C_hold A` intrinsic via
   `hold_weight_expect`): `(2C+2)/3 < C`. Plausibly true, but unprovable through the
   Prop-7.8 apparatus. Full argument: PENDING_WORK "Lap 13".
2. **Resized (Bridge.lean):** `C_Qtight := (max (C_hold A) 1)^A` (the floor);
   `C_renewalWhite_tight := 2·(2·C_hold A+2)^A` (sharp bridge `C_hold·n ≤ n₀·(n/2)` — an
   exact ℕ inequality replacing the `3^A` hop — plus `exp(ε³/2) ≤ 2`; costs +0.30 digits
   of the ~6.4e9-digit headroom; check21 asserts the GO at 9.3858e10 < 0.95e11).
3. **`Q_polynomial_decay_tight` is now DERIVED** (zero own sorries) from the single new
   crux via `prop_7_8_at` + `Q_polynomial_decay_at`. `C_Qtight_glue` deleted (obsolete).
4. **check21** added: floor argument, exact boundary/parity sweep of the sharp bridge,
   resized GO, crux feasibility window (`K_fewWhite 10^3007.9 ≪ C_hold 10^3016.1`).

## Next actions

1. **THE frontier: `Q_black_edge_tight`** (`Bridge.lean:~737`): black-edge (7.39) at poly
   threshold `C_hold A`, statement verbatim `prop_7_8_at`'s `hC2` slot. The tower in the
   existing proof (`Q_black_edge_case3` chain) is the HORIZON `P_fewWhite =
   encWindowIter…(R ~ 10³⁰¹⁰)`, not the estimate. **Smallest next probe**: read
   `Q_black_edge_case3`'s assembly — which of the three (7.56) mass terms forces the
   horizon to iterate, and can the K-white budget run at `K_fewWhite ~ 10³⁰⁰⁸` with a
   horizon POLY in `K`? Fallback: split into single-window estimate (poly horizon) +
   window-chaining induction. Multi-lap 🟡 — chip, never retreat to transcription.
2. **Never re-prove / touch `renewal_white_encounters`** (clean headlines depend on it).
3. **No X-chase / tower transcription** (deprecated lap 12).

---

# HANDOFF — big-C campaign, lap 12 (DEEP REFLECTION) — ROUTE RESOLVED → OPTION B 🧘

**Read `DIRECTION.md` RESOLVED banner (top) FIRST — it outranks this file.** The 3-lap
"transcription-only, awaiting operator" holding pattern is OVER. Route resolved this lap to
**Option B** (autonomous altitude authority; operator unavailable). Below is superseded lap-11
transcription detail — kept for method rails, NOT for its "continue X-chase" orders.

## State (branch `explicit-big-c`, all committed, build green)

HEAD after this lap's synthesis commit. `lake build` green (3327 jobs). `#print axioms`
re-run lap 12: 3 merged headlines `[propext, Classical.choice, Quot.sound]`; pin adds
`sorryAx`. Exactly **1 real `sorry`** (`Statement.lean:65`, the pin). Differ unaffected
(no watched statement touched). Hole #4 (C8) confirmed resolved in-tree.

## What lap 12 decided (the whole point)

- **RESOLVED the fired route trigger → Option B.** Full rationale in DIRECTION.md RESOLVED
  banner + PENDING_WORK `## Reflection — 2026-07-17 (lap 12, deep)`. Short: Option A edits the
  watched judge-owned pin (out of scope); B keeps `CTao`, is a proof over frozen statements,
  and is where the real §7 math is. Core destination (Tao's theorem) already reached — the pin
  is a stretch goal.
- **Localized the tower** to `Q_polynomial_decay` in `renewal_white_encounters_at`
  (Bridge.lean:522–691): decay from `hold_weight_expect`, tower `C0=C_polyDecay` is vacuous
  multiplicative slop (`Q ≤ 1` in range).

## Next actions (Option B — ADDITIVE, do NOT touch the clean headlines)

1. ✅ **DONE this lap**: `renewal_white_encounters_tight` PINNED (`548dfc5`) then **PROVED
   modulo one clean sorry** (`3a2ead9`). Added `C_Qtight` (head-sized), `C_Qtight_pos`,
   `C_Qtight_glue` (proved), `Q_polynomial_decay_tight` (sorry); the large-`n` arm reuses the
   `renewal_white_encounters_at` bridge assembly with `C_Qtight` in place of the tower, landing
   at `n₀^A·n^{-A}`. The `renewal_tail_tight` plumbing is all proven — the crux is now the SINGLE
   analytic target `Q_polynomial_decay_tight`. Build green (3327), headlines axiom-clean, differ 35/35.
2. **NEXT — the frontier: prove `Q_polynomial_decay_tight`** (`Bridge.lean:~730`):
   `Q (n/2) (whiteSet n ξ) ε j l ≤ C_Qtight A · (max(n/2−j) 1)^{-A}`, the poly-horizon `#white`
   lower-tail estimate. This IS Tao §7 decorrelation done tighter (true threshold ~10³⁰⁰⁸ <
   applied n₀ ~10³⁰¹⁶ — feasibility confirmed, deterministic shortcut refuted; PENDING_WORK
   Lap-12 grind). **Smallest first probe**: source-read `few_white_mass_le` (Case3) + how its
   horizon `P = encWindowIter…` is built — find where the tower is forced and whether the
   applied `m−j ≥ n₀` regime admits a poly bound. A genuine multi-lap 🟡 frontier — chip it.
3. **Never re-prove the existing `renewal_white_encounters`** (clean headlines depend on it).
4. **Do NOT** continue the X-chase or any tower-ladder transcription (deprecated this lap).

---

# HANDOFF — big-C campaign, lap 11 COMPLETE (C-SURFACE DONE + X-CHASE STARTED, 2026-07-17)

## State (branch `explicit-big-c`, all committed, build green)

HEAD `967f462`. Full `lake build` green at every commit (pre-commit gate); differ
`tools/tao_stmt_diff.py fabea6f HEAD` 35/35; `check_blueprint.py` **20/20** (check20 is
new). Still exactly 1 real `sorry` (`Statement.lean:65`, the pin). Route status
unchanged: STEP 3 STOPPED (operator ruling owed, `ROUTE-ESCALATION-2026-07-17.md`).

## Lap 11 second half (4 commits after the `6e7e627` milestone)

- **`28cf7e9`** — handoff/ledger for the C-surface milestone.
- **`d209f9a`** — **check20**: Sec5/Sec3 glue recomputed from the Lean def bodies —
  leaves exact (C_fpApprox=20178, C_perNHarm=384008), glue = 31.3 orders (additive noise
  vs the 9.39e10 head; check17's coarse "+15.2" was ~16 orders low, immaterial),
  head-route `C_spine` matches check17's GO, as-written max picks the C0-arm (check19
  conclusion unchanged).
- **`0d93e29`** — PENDING_WORK addendum: **step-2 scope correction** — the "feeding
  thresholds" half = the **X-chase** (de-existentialize the Sec5/Sec3 cutoffs; `C_syrSum X`
  is the one place a threshold feeds CTao). Probe: ALL cutoff leaves are explicit
  (`2^11`, `2^2000`, `exp(2000^5)`, `(1/ε)^(1/(1-θ))`; max/rpow builders only — no
  tendsto-opaque leaf). Key simplification: step 3 only needs `(log X)^c ≤ log X` (c ≤ 1)
  + `log X ≤ 10^17`-ish — numeral log-arithmetic, no tower rpow.
- **`2873233`, `967f462`** — **X-chase begun** (FirstPassage bottom, 10 nodes):
  `X_nZeroPos = 2^11`, `X_windowBase = max X_nZeroPos 2^2000` (shared by 4 nodes),
  `X_intTestDev`, `X_intTestErr`, `X_intTestLogUnif`, `X_valSumGeom`,
  `X_rpowNZero = 2^20`, `X_valSumTail`. **Rail**: convert each `_atC` to an `_atCX`
  ∀-form (`∀ x, X_foo ≤ x → …`) via `have h := upstream_atCX; set x₀u := X_upstream;
  rw [show X_foo = <witness max-tree over set-names> from rfl]; intro x hx …` then body
  VERBATIM; keep the old ∃-form as a one-line delegate `⟨X_foo, foo_atCX⟩` (byte-identical
  statement). Watch the adjacent-docstring parse error when inserting defs (bit twice).

## Next (X-chase continuation, bottom-up)

1. **FirstPassage remainder**: `rpow_le_eps_mul_of_lt_one` (witness
   `max 1 ((1/ε)^(1/(1-θ)))` → def `X_rpowEps θ ε`), `descent_pow_bounds` (`2^30`),
   `descent_passes` (`max (max xa xb) (max xc 2)` at the two rpowEps instances + descPow),
   then **`first_passage_nonescape_atCX`** (`max X_valSumTail X_descPasses`).
2. **ApproxFormula** (C8 chain, ~16 cutoffs), **Stabilization** (C9 chain — includes the
   `exp(2000^5)` leaf in `mainZ_bound_atC`/`Iy_card_bracket`, `X_mainZbridge`,
   `X_twoMZero=e^100000` etc. already defs), **Sec3** (7: step/base/ladder/whp/windowBad —
   ends at `X_syrSum := max xw (exp 1)`, the `X` of `C_syrSum`).
3. Then `log X_syrSum ≤ 10^17`-ish bound lemma (numeral log-arithmetic; see memory
   `lean-linarith-decimal-rpow-poison` for the rpow-atom rail) — completes step 2's
   threshold half. STEP 3 stays STOPPED (operator A/B ruling owed).
4. When resuming, also mirror new X defs in check_blueprint (extend check20 or add
   check21: assert `log10(log X_syrSum) < 17`).

## Lap 11 (6 commits) — **STEP-2 TRANSCRIPTION COMPLETE: spine fully constant-explicit**

1. **`85c4ce9`** — (5.21) C9 chain: `C_mainZ := C_perNHarm + C_harmonicZ +
   1000·(1+C_fpApprox)`; `C_approxToZ := (2/log(4/3)+6000)·C_perNTermEval + C_mainZ·6000`;
   `C_windowStable := 2·C_approxToZ`. All three `_atC` + byte-identical delegates.
2. **`c89cc1a`** — **Sec5 spine capstone**: `stabilization_atC`, `C_stab := C_valSumGeom +
   4·C_fpApprox + 2·C_windowStable` (watched ∃-form delegates byte-identical).
3. **`040fd20`** — Sec3 legs 1–3: `C_descStep := 2·C_stab`; base passthrough
   `C_valSumGeom`; `C_descLadder := max C_valSumGeom C_descStep`.
4. **`dad4885`** — Sec3 legs 4–5: `C_descWhp := C_descLadder·(1+(1−α^{−c_ladder})⁻¹)·α^c_ladder`;
   `C_windowBad := 2·C_descWhp`.
5. **`a6fd9f6`** — **the cutoff→constant absorption seam**: `C_syrSum (X : ℝ) :=
   max (C_windowBad·α/(α−1)) (4·max 1 ((log X)^c_ladder))` — first CUTOFF-PARAMETERIZED
   constant (the pin has no x₀, so the Sec3 top absorbs the Sec5 existential cutoffs into
   the constant; this is the `n₀^B` head of the traced ladder, now symbolic).
   `tao_syracuse_quantitative_sum_atC : ∃ X, ∀ N₀ x, … ≤ C_syrSum X · …`.
6. **`6e7e627`** — spine top: `C_syrProb X := 8·C_syrSum X`, `C_spine X := 16·C_syrSum X`;
   `tao_syracuse_quantitative_atC`, `tao_collatz_quantitative_spine_atC`.
   `#print axioms` on both spine forms: `[propext, Classical.choice, Quot.sound]`
   (believed clean, judge to verify).

**Step-2 completion audit:** every ∃cC slot on the spine path has an `_atC` sibling
(verified by name-sweep over FirstPassage/ApproxFormula/Stabilization/Sec3; Sec6/Sec7/
Prob/Syracuse done laps 7–10). `valuation_tail` (Lemma 4.1) has NO consumers outside its
file — off-path, left ∃-form. The Prob quarter/pascal bounds feed only LocalBound `_at`
forms (done lap 7–8).

**Discharge shape now:** exhibit the cutoff `X` (chases the existential cutoffs — top is
`max xw (exp 1)` from `window_bad_sum_atC`) and prove `C_spine X ≤ CTao`. That is STEP 3,
which remains **STOPPED** pending the operator ruling (Option A re-pin vs Option B
`renewal_large_n_tight`). Both options consume exactly this symbolic surface.

## Next (grind orders)

- **Nothing left in step-2.** Until the operator rules on A/B: candidate useful work is
  (i) numeric-trap extension: mirror the new lap-11 constant defs (`C_mainZ`…`C_spine`)
  in `check_blueprint.py`'s symbolic ladder (check18) so the Lean defs and the Python
  trace can't drift; (ii) tighten `STATUS.md`; (iii) if idle beyond that, pre-derive the
  cutoff-chase (`X` as an explicit tower through the Sec5 cutoffs) — it is needed by BOTH
  options and is pure transcription, not the banned Option-B re-proof.

---

# (lap 10 baton below)

# HANDOFF — big-C campaign, lap 10 COMPLETE (C7 + C8 reified, 2026-07-17)

## State (branch `explicit-big-c`, all committed, build green)

HEAD `250e4ed`. Full `lake build` green (3327 jobs) at every commit; differ
`tools/tao_stmt_diff.py fabea6f HEAD` 35/35; `check_blueprint.py` 19/19. Still exactly
1 real `sorry` (`Statement.lean:65`, the pin). Route status unchanged: STEP 3 STOPPED
(operator ruling owed, see `ROUTE-ESCALATION-2026-07-17.md`); step-2 transcription
continues and is what this lap advanced.

## Lap 10 progress (9 commits) — **C7 and C8 constants fully reified**

1. **`13d622f`** — `harmonic_to_Z_atC`: `C_harmonicZ := C_harmZfine + C_mainZbridge`.
2. **`ac405c7`** — leaf-A inputs: `windowMass_estimate_atC` (C=3), `windowMass_ge_clog_at`
   (c=1/10000, cutoff `2^2000`, fully explicit), `perNHarmonic_le_at` (C=4).
3. **`2db3ae6`** — leaf A + per-n eval: `C_perNHarm := C_epsPerNHarm·4`
   (`C_epsPerNHarm = 2+3·(3/(1/10000))+2·3/(α−1)`), `C_perNTermEval := C_perNHarm +
   C_harmonicZ`. **Rail:** `set Cw := 3`/`set CH := 4` BEFORE obtaining
   `Nstar_mem_logWindow` (its `4/3` literals must not be abstracted).
4. **`c4b03de`** — `Iy_count_ratio_atC` (C=6000).
5. **`d88cb62`** — integral-test chain: `intTest_class_dev_atC` (c=2),
   `intTest_D_lower_atC` (D₀=1/8), `K_intTest := 2/(1/8)` (=16), `intTest_error_atC`,
   `integral_test_logUnif_atC`.
6. **`bb97151`** — **C7 REIFIED**: `valuation_dist_atC` (`C_valuationDistC K := 2K +
   4·C_geomTail`, ValuationDist.lean), `C_valSumGeom := C_valuationDistC K_intTest +
   2·C_geomTail` (=44), `valSum_lower_geom/tail_atC`, `first_passage_nonescape_atC`.
7. **`7daed64`** — C8 leaf: `C_goodTupleDev := 2·C_geomTail + C_valuationDistC K_intTest`
   (=44), `goodTuple_prefix_dev_sum_atC`, `approx_good_tuple_whp_atC`.
8. **`a099d0f`** — `C_windowReduce := C_goodTupleDev + C_passtimeWindow`
   (`C_edgeMass := 2/(1/10000)`, `C_passtimeInner`, `C_passtimeWindow := C_valSumGeom +
   C_passtimeInner` — C7 wired into C8).
9. **`250e4ed`** — **C8 REIFIED**: `C_fpApprox := C_windowReduce + C_affineReindex`
   (`C_steppedMid := C_goodTupleDev + 1`, `C_affineReindex := C_steppedMid + 1`;
   early-return and truncation constants are the numeral 1). `first_passage_approx_atC`.

**Rails re-proven this lap:** (i) the `set`-rebind port works at scale (300-line bodies,
zero textual edits beyond the head); (ii) adjacent docstrings = parse error — MERGE into
one when inserting a def above an existing docstring; (iii) `rw [show C_foo = <set-names>
from rfl]` closes by zeta+delta defeq through `set` fvars.

## Next (grind orders, bottom-up — step-2 only until the operator ruling)

1. **`mainZ_bound` C-slot** (Stabilization.lean ~2620): witness `CA + CB + 1000·(1+C8)`
   — all three inputs now pinned (`C_perNHarm`, `C_harmonicZ`, `C_fpApprox`). Obtains are
   ∃c∃C-forms; swap to `_atC`s + set-rail. Name `C_mainZ`.
2. **`approxMainTerm_to_Z_atC`**: `(2/log(4/3) + 6000)·C_perNTermEval + C_mainZ·6000`
   (pattern at Stabilization.lean:2977 — the c-form already has the shape).
3. **`approxMainTerm_window_stable_atC`**: `2×` that.
4. **`stabilization_atC`** (WATCHED — keep ∃-form byte-identical, differ must stay 35/35):
   `C_valSumGeom + 4·C_fpApprox + 2·C_windowStable`. **This completes the Sec5 spine.**
5. Then remaining slot sweeps: FirstPassage leftovers, ApproxFormula leftovers,
   Sec3 (7), Syracuse (1), Prob (1). Then all constants feeding `C_ladder` are symbolic
   — ready for whichever option the operator picks (A re-pin / B tighten).

---

# (lap 9 baton below)

## State at lap 9 end (branch `explicit-big-c`, all committed, build green)

HEAD `281eee7`. Full `lake build` green (3327 jobs) at every commit; differ
`tools/tao_stmt_diff.py fabea6f HEAD` 35/35 (no watched statement touched);
`check_blueprint.py` 19/19. Still exactly 1 real `sorry` (`Statement.lean:65`, the pin).

## 🚨 ROUTE BLOCKED — operator ruling owed (read `ROUTE-ESCALATION-2026-07-17.md` FIRST)

STEP 3 (discharge via `C_ladder ≤ CTao`) is STOPPED: the fully-reified `C_ladder` is a
tower ≫ pin (lap-8 C0-arm flag, machine-checked check19). Lap-9 review sharpened it —
**transcription route dead, but the pin is dischargeable in truth** (true renewal constant
≈ head `10^(9.36×10¹⁰) < CTao`; the C0-arm is vacuous-`Q` slop). Two operator options in the
escalation doc: **A** re-pin `CTao` tower-form (cheap), **B** tighten via `renewal_large_n_tight`
(keeps CTao, research). **Do NOT edit the pin; do NOT start Option B without a ruling.**

## Lap 9 progress (5 commits, all green)

1. **`8f25699` — REVIEW + escalation.** Sharpened the C0-arm NO-GO (source-read the renewal
   proof / `Q_polynomial_decay` / `encWindowIter` / `white`); wrote `ROUTE-ESCALATION-2026-07-17.md`,
   crux decomposition (`renewal_large_n_tight`) in PENDING_WORK lap-9, DIRECTION route-banner,
   STATUS refresh.
2. **`a235201` — `geomHalf_tail_bound` C-slot** (`LocalInstances.lean`): `C_geomTail := 2`,
   `geomHalf_tail_bound_atC` (pins c=1/400 + C=2); `_cExplicit` + ratified form delegate.
3. **`b8f4ccb` — `good_tuple_whp_iid` C-slot**: `C_goodWhp := 2·C_geomTail` (=4),
   `good_tuple_whp_iid_atC` (C-pinned, cutoff ∃). Rail: `set ct/Ct` re-bind names → 120-line
   union-bound body ports verbatim after a `show`.
4. **`281eee7` — B1 rib fully big-C**: `C_syracZsub := C_goodWhp` (=4),
   `syracZ_sub_perNGoodMass_bound_atC` (passthrough); `C_harmZfine := 4·C_syracZsub` (=16),
   `perNHarmonic_eq_harmZfine_approx_atC` (`set Ccn/Cw` rail). **Sec5 (5.20) B1 rib now fully
   constant-explicit; B2/`C_mainZbridge` was lap 8.**

## Next (grind orders, bottom-up — continue ONLY step-2 transcription until the ruling)

- **`harmonic_to_Z` big-C sibling** — combine B1 (`C_harmZfine`=16) + B2 (`C_mainZbridge`) via
  the triangle through `harmZfine`. See `harmonic_to_Z_explicit` (~Stab:2247, the c-form
  combining the two `_explicit`s). Constant `= C_harmZfine + C_mainZbridge` (triangle ineq),
  cutoff `max`. Then `perNTerm_eval` (combines A `perNTerm_harmonic_approx` + B), then
  `stabilization`. Then FirstPassage (16) / ApproxFormula (23) / Sec3 (7) / Syracuse (1) /
  Prob (1). **Method rail (proven this lap):** for a passthrough/scale node, `set` the
  ∃-obtained constant NAMES to the pinned defs (`set Ccn := 4`, `set Cw := C_foo`) then the
  body ports verbatim; pin the C-slot, keep the cutoff `∃` (cutoffs feed the x₀-threshold, not
  CTao); make ratified ∃-form + any c-form `_explicit` delegate.

---

# (lap 9 review baton below — superseded by the state above; kept for the escalation detail)

## 🔬 Lap 9 (REVIEW): C0-arm NO-GO SHARPENED + escalated — read `ROUTE-ESCALATION-2026-07-17.md`

Fresh-mind review. **The lap-8 route trigger has FIRED; I confirmed it and sharpened it.**
Source-read the renewal proof (Bridge.lean:522–691), `Q_polynomial_decay` (Case3.lean:3531),
`encWindowIter` (Case3.lean:1020), and `white` (Setup.lean:100–103). Findings:

- **Transcription route DEAD (lap-8 upheld):** `C_renewalWhite`'s large-n arm is a cubic
  tower (`C_polyDecay = Cthr_prop78^A`, `Cthr_prop78` ⊇ `encWindowIter` tower). check19 solid.
- **But the pin is DISCHARGEABLE IN TRUTH** (lap-8 over-read "STEP 3 dead" as "pin dead"):
  the C0-arm multiplies `Q_polynomial_decay` at `m = n/2 ≈ 10³⁰¹⁶ ≪ Cthr_prop78`, i.e. in
  Q's **vacuous** regime → tower is insurance slop. `white ⟺ |θq|>10⁻¹⁰⁰⁰` is frequent ⟹
  `#white ≈ p·n/2` ⟹ `E(n) ≈ exp(-ε³p·n/2)`, peak at `n*≈10³⁰⁰⁸ < n₀` (the HEAD arm, forced
  floor `10^(9.36×10¹⁰) < CTao`). True large-n contribution ≈ 0 ⟹ **true renewal constant
  ≈ head < CTao** (6% room, check17). The development can't reach it because its only
  `#white` lower-tail control (`few_white_mass_le`) uses the crude (7.67) **tower** horizon,
  not the true ~poly(1/ε) decorrelation.
- **Escalated to operator** (owns the pin): `ROUTE-ESCALATION-2026-07-17.md` — Option A re-pin
  `CTao` tower-form (cheap), Option B tighten via `renewal_large_n_tight` (research, keeps
  CTao). Crux decomposed in PENDING_WORK lap-9. STATUS + DIRECTION route-note refreshed.
- **Grind orders until the ruling:** STEP 3 STOPPED; continue step-2 transcription (Sec5 B1
  `perNHarmonic_eq_harmZfine_approx_explicit` → `harmonic_to_Z` → stabilization, then
  FirstPassage/ApproxFormula/Sec3/Syracuse/Prob). It is prereq for BOTH options. Do NOT edit
  the pin or any watched statement; do NOT start Option B without an operator ruling.
- Docs-only lap (no Lean touched) → build unchanged green at `ada7ad3`; `check_blueprint.py`
  19/19 pass; differ unchanged 35/35.

---

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
