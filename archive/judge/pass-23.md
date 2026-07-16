# Judge pass 23 (2026-07-13, Ren/Fable — external contribution cross-check, working tree) — D4 CHANGE + REAL LEMMA-7.4 SEPARATION EXECUTED ✅; SECOND ALTITUDE-CLASS ESCALATION ⚠️

Scope: uncommitted working-tree changes by an external **OpenAI Codex** session —
8 Sec7 files, +1,171/−196 (Setup, Triangles, White, BlackEdge, Case3, FpLocation,
ManyTriangles, Bridge) + STATUS.md. This executed steps 2–3 of the altitude
ruling's order (D4 change, real separation) plus an explicit localization attack
on the blocked foreign-triangle tail. The 🗂️ ManyTriangles split was NOT done
(still queued; the file grew again, now ~5,200 lines).

## The D4 change: `epsBW = 1/10⁹⁰` landed; ε-sweep tripwire FIRED and DISCHARGED ✅

Setup.lean carries exactly the ruled numeral. The pass-18 sweep list, item by item:
1. `sep_const_sq_le_one` dead ✓ (deleted; replaced by `twenty_lt_sep_const` +
   `sep_const_lt_twenty_six` — 20 < 9·ln 10 < 26, both judge-run clean).
2. Gap numeral ✓ — `white_gap_above_run_top` statement untouched, proof re-ran,
   re-verified clean (13 rows holds a fortiori at 10⁻⁹⁰).
3. Deep pin's `51/100 ≤ p₀` ✓ statement untouched (truth question folds into the
   new escalation below).
4. ε₀-floor ✓ (White.lean numeral repair; floor easier at smaller ε).
5. X2's `exp(−ε³)` consumers ✓ — X2's four theorems re-verified clean
   (constants existential as designed).
6. Out-of-strip / budget thresholds ✓ — `fpDist_out_of_strip_le` untouched +
   re-verified.
7. Confinement margin ✓ — full X10 chain re-verified clean.

**Re-verification runs (2026-07-13, post-D4, all exactly the clean triple)**:
X3 `black_structure`, X2 (`fCond_three_norm`, `white_cos_bound`, `θq_succ_j`,
`θq_pred_l`), X10 (`triangle_encounter_le`, `encounter_apex_proximity`,
`encounter_separated_sum`), `white_gap_above_run_top`, `fpDist_out_of_strip_le` —
the verified-node ledger survives the D4 change intact.

## Real Lemma-7.4 separation: the pass-18 vacuity is RESOLVED ✅

Triangles.lean (+509) formalizes Claim (*) Cases 1–3 as genuine Euclidean
separation at sep ≈ 20.7 (corner/weakly-black machinery:
`weaklyBlack_of_corner_scale_near`, `corner_top_white_gap`,
`black_near_black_mem_corner`, `lattice_close_of_sq_dist_lt_sep`, …).
**`black_structure`'s statement changed — additively only** (judge-diffed): one new
conjunct `∀ t ∈ T, ∃ p, black p ∧ t = cornerTriple n ξ p` (every family triangle
arises at a black corner — the paper's own Lemma-7.4 construction, needed by the
separation argument). **Re-RATIFIED as strengthened** vs pp.39–41/46–48;
re-verified clean. The separation clause now carries real content — the
escalation's "proves the clause by vacuity" is closed for good.

## Statement integrity across the reorganization ✅

Character-diffed every pinned statement in the touched files: `Q_black_edge_case3`
(moved BlackEdge → Case3), `Q_black_edge`, `prop_7_8`, `Q_polynomial_decay`
(moved to Case3, `:= by sorry`-style replaced by term-mode delegation through
proved `_of_` engines — statements identical modulo one whitespace line-wrap),
`fpDist_edgeWeight_le`, `fpDist_white_exit`, `Q_black_edge_case2`,
`fpDist_white_exit_deep` (SUSPENDED pin — untouched ✓), `triangle_encounter_le`,
`white_gap_above_run_top`, `fpDist_out_of_strip_le` — ALL character-identical.
Deleted: `estar_union_le`, `few_whites_le`, `Q_black_edge_case3_assembled` — the
OLD 10⁻⁴-era white-count route (⌈10A/ε³⌉ whites), already route-withdrawn at
pass 18; deletion consistent with the ruling. Bridge.lean: import retarget only.

**Sorry trail unchanged in content**: the same 5 crux statements
(`fpDist_edgeWeight_le`, `fpDist_white_exit`, `Q_black_edge_case2` in BlackEdge;
`Q_black_edge_case3` now in Case3; `fpDist_any_triangle_le` in ManyTriangles).
Repo total 17 → 14 (the conditionalized spine pieces no longer carry their own
sorries). Conditional spine verified to carry sorryAx as expected:
`fpDist_white_exit_deep`, `many_triangles_white`, `Q_black_edge`, `prop_7_8`,
`Q_polynomial_decay`, `Q_black_edge_case3`.

## ⚠️ SECOND ALTITUDE-CLASS ESCALATION: quantifier order (the pass's headline risk)

Codex reduced the blocked tail to explicit geometry — honestly. New proved chain
(all judge-run clean): `fpDist_le_stepMass`, `fpDist_linear_tail(_le_sixteenth)`,
`fpDist_height_tail_le_sixteenth`, `fpDist_localization_le_eighth`,
`exists_fpDist_localization_box` (an X6-localization box (X, Y) with bad mass
≤ 1/8), `endpoint_notMem_start_triangle`, `phaseInFamily_support_imp_*`,
`fpDist_any_triangle_le_of_localization_box` (the tail FOLLOWS whenever Lemma-7.4
separation > √(X²+Y²)). **But the box is X = ⌈(5Y + 4·10⁷)/16⌉ ≈ 2.6·10⁶ —
against sep ≈ 20.7.** The 4·10⁷ threshold comes from a very lossy negative-drift
Chernoff on `16j − 5l` (MGF exponent −39/400000 per step). No feasible frozen
power-of-ten ε closes this (log₁₀(1/ε) ~ 10⁷ digits — exact-ℚ tactics die).
The paper chooses ε AFTER its localization constants; our frozen D4 sits upstream.
Honest exits: (a) tighten the localization (the paper's O(1) is overshoot-based,
not drift-box-based — needs a fresh judge read of p.48 before any re-ruling), or
(b) re-open D4 as a parameter (quantifier-order redesign, re-values everything).
`fpDist_any_triangle_le` remains sorried (correctly — its docstring states the
obligation plainly); `fpDist_white_exit_deep`'s ratification REMAINS SUSPENDED on
these new grounds. **Recommendation: judge re-read of p.48's localization before
asking for any new ruling — option (a) looks live and much cheaper.**

## Hygiene (/lean-review, ~1,171 added lines)

✅ No 🔴/🟡: no `maxHeartbeats`, no `native_decide`, no `axiom`/`unsafe`/`partial`/
`opaque`, no silenced linters, no Prop-def laundering. 🔵 build noise in changed
files (new `push_neg` deprecation hits, unused simp args, one no-op `push_cast` —
Triangles/Holding); STATUS.md's self-log reuses lap numbers 58/59 (collides with
treadmill lap numbering — cosmetic, but the next box session should renumber).

## State after this pass

- Ruling execution: steps 2 (D4) + 3 (separation) DONE out of order; step 1
  (🗂️ split) still queued and MORE urgent (ManyTriangles ~5,200 lines); step 4
  (kernel) blocked on the new escalation.
- X9 badge: 13–28/medium/70% → **4–12 (kernel only) / high / 60%**.
- Verified ledger intact at ε = 10⁻⁹⁰ (X2/X3/X10 re-verified this pass;
  C2/C5/S3/X1/X5/X6 live below the ε-dependent layer).
- Committed by the judge (external session; boxes/agents can't push). Credit:
  D4 execution, separation formalization, and localization chain authored by
  OpenAI Codex; judge-verified.
