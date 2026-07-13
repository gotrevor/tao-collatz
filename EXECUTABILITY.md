# Executability verdict — can the Opus treadmill drive this to 0 sorries / 0 axioms? 🎯

*Author: Ren (Fable 5 session, 2026-07-08). Companion to `BLUEPRINT.md` (node ledger) and
`SKELETON-SPEC.md` (ratified statements). Finalized after the Phase-A skeleton run; see §5.*

## 1. Verdict

**Yes, conditionally — 65% confidence of full discharge** (kernel-clean
`[propext, Classical.choice, Quot.sound]` on `tao_collatz`) **within a ~250–450-lap
campaign (multi-month at g-i lap throughput)**, provided the preconditions in §3 are
met before firing. Confidence outside the three hard kernels: **>90%** — that material
(counting, harmonic sums, ZMod arithmetic, PMF calculus) is exactly what the treadmill
has repeatedly finished (erdos-880, binomial-thresholds, goodstein Series 1–5 rungs).

Risk is concentrated, not diffuse:

| kernel | what | conf | why it's the risk | fallback |
|--------|------|------|-------------------|----------|
| S3 | local 2-D Gaussian bound (paper Lem 2.2 for `Hold`) | 70% | real analysis: tilting + circle method, uniform constants | classical material; can also weaken to box-probabilities at 2 of 3 call sites |
| X3 | Lem 7.4 black-set = separated triangles | 70% | delicate finite case analysis ((7.12)–(7.24), Cases 1–3 + Fig 4) | fully elementary + finite; numeric harness can pin every sub-claim before grinding |
| X8/X10 | renewal process vs triangles (Cases 2–3, Lem 7.9/7.10) | 60% | the paper's pinnacle; longest constant chains | D6 finitization already turns stopping times into recursion-unrolling; judge-gated series |

Compound over kernels ≈ 0.70·0.70·0.60 ≈ 0.29 *if independent and unaidable* — but they are
neither: in-session de-risking already validated the two biggest design bets (§5), each kernel
has a documented fallback that trades constants for tractability without touching the theorem
statement, and hard-kernel series get judge gates + Fable/Ren assists rather than blind grinding.
Hence 65% overall, not 30%. The honest tail risk: **X10 needs real proof-engineering
architecture** (like goodstein's operator calculus did) — if it stalls, that's the monument-fork
moment, and the fallback is a Fable-assisted design series, not abandonment.

## 2. Why this is treadmill-shaped at all (the design wins)

1. **D1 — all probability is PMF/tsum arithmetic.** No measurability side conditions,
   no filtrations, no conditional-expectation API. Every probabilistic step is a sum
   manipulation — the treadmill's best event class.
2. **D2 — ℤ[1/2] eliminated**; the core dynamical identity lives in ℕ
   (`2^|a|·syrⁿ N = 3ⁿN + Fnat`), *proved this session*.
3. **D6 — no infinite renewal process.** `Q` is a well-founded recursion; §7.4's
   stopping-time arguments become strong inductions. *Recursion + (7.35) proved this session.*
4. **D8 — numeric harness kills statement traps before laps.** The g-i failure mode
   (110 laps of false summits from statement freedom) is structurally blocked: statements
   are ratified against exact finite instances (Syrac ℤ/9 table, Fnat identity, triangle scans).
5. **Uniform density of citations**: every node names its paper anchor; the treadmill never
   has to *find* the math, only formalize it.

## 3. Preconditions before Trevor fires the treadmill

1. **Judge pass over all `RATIFY-*` markers** (grep the tree) against the paper PDF —
   one Ren+PDF session. Statement bugs found after laps start are 10× costlier (g-i doctrine).
2. **Blueprint audit machinery transplanted** (g-i `BlueprintAttr.lean` + `BlueprintAudit.lean`,
   built repo-agnostic with EDIT-ON-TRANSPLANT constants) + CI `lean-axiom-gate --exact` on
   `tao_collatz` — status machine-derived from day one.
3. **Harness extended per-kernel**: before the X3 series, add exact-instance checks for each
   Lemma 7.4 sub-claim (weakly-black claims (i)–(iii), Case (*) at concrete (n,ξ)); before S3,
   numeric check of the tilted-MGF inequalities at sample λ.
4. **PMF lemma bank first** (S1/S2 series before anything else): expect/indicator calculus,
   bind/map/expect commutation, iid marginals. Friction here taxes every later node.

## 4. Recommended campaign structure (Trevor fires; g-i cadence)

- **Series α (foundations)**: S1, S2, C1, C2-completion, C3, C4 — target green, sorry-free.
  ~40–70 laps. High confidence; also builds the lemma bank.
- **Series β (spine)**: C5, C7, C6 (§4, (1.19), §3) — the quantitative bootstrap becomes
  real: at its end, `Syrmin(N) ≤ N^θ a.a.` (Remark 5.1) falls out as a milestone theorem
  worth having even if the campaign later stalls. ~50–80 laps.
- **Series γ (bookkeeping)**: C8, C9, C10 skeleton (§5 + §6 modulo Prop 1.17). ~60–100 laps.
- **Series δ (kernels, judge-gated every ≤4 laps)**: S3 → X3 → X4–X7 → X8 → X9/X10 → X11.
  ~100–200 laps. Fable/Ren judge passes at series boundaries; any statement surgery here
  goes back through the harness.
- Fire shape per series: `lean-treadmill tao-collatz --max-laps 12 --max-duration 10h
  --review-every 4 --allow-stop` (model/effort per Trevor's preference; g-i evidence:
  gates are model-agnostic).

**Milestone insurance**: even a stall after Series β leaves a publishable artifact —
the FIRST formalized theorem of the "a.a. orbits dip below N^θ" class (unformalized
anywhere), worth a lean-gallery entry. ⚠️ **Label it honestly** (statement-faithfulness
audit, 2026-07-12): what falls out of Remark 5.1 is `Syrmin(N) ≤ N^θ` a.a. in
**logarithmic density** at the UN-optimized exponent `θ > 1/α` — Terras-type-plus. It is
NOT Korec 1994: Korec is **natural density** (Tao p.2 says so explicitly of
Terras/Allouche/Korec) at the optimized `θ > log3/log4 ≈ 0.7924`, and log-density-1 does
not imply natural-density-1. Never register it against ccchallenge's Korec entry — that
would be the Idris competitor's density-notion error in mirror image.

## 5. Session de-risk evidence (2026-07-08)

- Harness (6/6 checks): Fnat identity, (1.2), Syrac ℤ/9 table in BOTH (1.21)/(1.26) forms
  (footnote-6 reversal trap encoded), negative binomial, Lemma 1.12 recursion, Lemma 7.4 scan.
- Proved in-session (Phase-A agent): see §"Phase-A results" appended below after the run.
- Full paper read + 26-node DAG extracted; no prior formalization found (greenfield first).

## Campaign log — index 🗂️

History lives in [`judge/`](judge/), one file per entry; this root stays lean (same
fractal rule as the KB). Full text preserved verbatim — nothing was summarized away.

- [Phase-A results](judge/phase-a-results.md) — 2026-07-09, Opus skeleton run: 26-node skeleton landed + Monotone ratification fix.
- [Kernel de-risk lap](judge/kernel-derisk-lap.md) — 2026-07-10, first box lap: risk-kernel probes.
- [Pass 1](judge/pass-01.md) — 2026-07-09: RATIFY queue verdicts (Q-cluster (7.34)–(7.35), Prop 7.3 count, X4 bindings).
- [Pass 2](judge/pass-02.md) — 2026-07-10, pp.42–46: Lemma 7.6 mean, Lemma 7.7/`fpDist` pin, Prop 7.8 cluster.
- [Pass 3](judge/pass-03.md) — 2026-07-12, pp.14–15: Lemma 2.2 instances ratified (S3 statements).
- [Pass 4](judge/pass-04.md) — 2026-07-12: treadmill lap-1 boundary — first boundary pass + axiom checks.
- [Pass 5](judge/pass-05.md) — 2026-07-12: **NODE S3 COMPLETE** ✅ (risk kernel 1 closed, 10 axiom checks).
- [Pass 6](judge/pass-06.md) — 2026-07-12, pp.46–49: X8 pinned + ratified; moved-statement audit.
- [Pass 7](judge/pass-07.md) — 2026-07-12: **NODE X6 COMPLETE** ✅ (Lemma 7.7; Case-2 kernels unblocked).
- [Pass 8](judge/pass-08.md) — 2026-07-12, pp.50–54: **X10 + X9 pinned + ratified** (zero un-pinned crux nodes); apex core proved; graph-semantics audit; density spot-check.
- [Pass 9](judge/pass-09.md) — 2026-07-12: **PAPER GAP in Lemma 7.9 CONFIRMED** 🕳️ (p.51 display banks damping through k₁; true sum stops at t₁); X9 re-ratified at exp(2ε); 10 axiom checks (encounter fold + block bridge) clean; KB literature-holes entry #5.
- [Pass 10](judge/pass-10.md) — 2026-07-12, pp.33–35: **X1 pinned + ratified** (`cexpect_pairing` = (7.5) verbatim; Lemma 7.2 exact value proved; `key_fourier_decay` + `charFn_decay` drift-free moves/derivations); un-pinned down to C8 + X5; ladder-vs-graph color vocabulary clarified.
- [Pass 11](judge/pass-11.md) — 2026-07-12: **NODE X1 COMPLETE** ✅ (fourth verified node; `cexpect_pairing` clean, drift-free); box's "axiom-clean" mislabel on `prod_fCond_le_damping` caught (sorryAx via X2); Prop 1.17 trail machine-mapped; definition-badge tint rule shipped.
- [Pass 12](judge/pass-12.md) — 2026-07-12, lap 54 (5 commits + handoff): **X5 + X2 COMPLETE** ✅✅ (Lemma 7.6 ratified vs p.42, 15 decls clean; `white_cos_bound` clean → `prod_fCond_le_damping` closed, trail map confirmed); X9 ledger core verified (chain cap + LP vertex + normalize/wander/edge gluing, 10 decls); **`fpDist_white_exit_deep` pinned + ratified vs (7.59)** — the watched-for variant, p₀ > 1/2 burden embodied. ⚠️ near-edge tripwire: widening the deep pin's statement revokes its ratification.
- [Pass 13](judge/pass-13.md) — 2026-07-12, lap-55 reflection (docs-only): **X9 RATIFICATION SUSPENDED** ⚠️ — box's near-edge truth challenge to the pinned exp(2ε) judge-concurred (~85%; adversarial edge-strip families extract e^{ε·Cthr} uncompensated); **literature hole #6** (paper's all-starts Lemma 7.9 inherits it via "(7.59) by repeating (7.51)"); both proposed fixes pre-assessed with re-ratification checklists; deep-pin ratification stands (statement untouched).
- [Pass 14](judge/pass-14.md) — 2026-07-12, lap 55 cont: **X9 RE-RATIFIED** ✅ — depth-gated fold passes the pass-13 checklist (gate conjunct exact, `∃g` quantifier order right, `g=0` degenerates to prior encoding); 13 gated fold/chain lemmas re-verified axiom-clean; deep pin untouched. Suspension lasted one commit.
- [Pass 15](judge/pass-15.md) — 2026-07-12, consumer pages pp.48–49 + 54–56 read (Trevor-prompted): **BOTH X9 RIDERS DISCHARGED** ✅ — R := ⌊A²/ε⁴⌋ explicit on p.55 (after ε; the −O(A) Markov slack absorbs exp(2ε) or any absolute constant); (7.54)'s 0.9m split + (7.67)'s in-window iteration keep every counted encounter deep (gate-safe). Residual: **X9's proof must exhibit ε₀ ≥ epsBW = 10⁻⁴** (consumer instantiates at the fixed dichotomy ε). Bonus: X10's ∀A-uniform form confirmed at its p.54 union-bound site. All of §7 now judge-read; §5 (C8) is the only unread front.
- [Pass 16](judge/pass-16.md) — 2026-07-12, lap-55 boundary: **LEMMA 7.9 CLOSED MOD KERNEL** ✅ — `many_triangles_white` proved, Y-induction axiom-clean, sorryAx trail = exactly {`fpDist_white_exit_deep`} (machine-checked). ⚠️ **ε₀-floor LEAK caught**: exhibited ε₀ = min(1/100, (2p₁−1)/2) with p₁ from the pin's bare `1/2 < p₀` — does NOT certify ε₀ ≥ 10⁻⁴. **Kernel demand: re-pin mass to `51/100 ≤ p₀`** (pre-authorized as ratification-preserving strengthening; numerics ≈ 0.99).
- [Pass 17](judge/pass-17.md) — 2026-07-12, lap-56 boundary + lap-57 re-pin: **MASS DEMAND SATISFIED** ✅ (`3c95898` character-exact to the pre-authorization; ε₀-floor discharged by arithmetic; steering item retired). **Kernel DERIVED** via (7.50)-geometry decomposition: `fpDist_col_le` + `fpDist_out_of_strip_le` PROVED clean; one tail left — **`fpDist_any_triangle_le`** (≤ 1/8 family-triangle mass; NEW PIN, ratified as route decomposition ~85%). `/lean-review` on the full range: ✅ CLEAN (0 registry hits over 335 added lines). When the tail lands, X9 completes end-to-end.
- [Pass 18](judge/pass-18.md) — 2026-07-12, lap-57 boundary: **ROUTE ESCALATION CONCURRED** ⚠️ — `F.separated` is VACUOUS at the frozen ε ((0.921)² < 1 = lattice minimum; X3 proves the clause by exactly that vacuity; p.48's whiteness step consumes real separation). NOT a paper error — the D4 numeral is too large. `fpDist_any_triangle_le` route ratification WITHDRAWN; **`fpDist_white_exit_deep` ratification SUSPENDED** pending the altitude ruling (remedy A vs hybrid B+A-small). Remedy-B vertical half **PROVED + verified** (`white_gap_above_run_top`: 13 white rows above any run top, exact-ℚ). **X10 A-quantifier bug concurred** (∀A>0 was false vs the 16/step height drift): old ratification revoked, `∃A₀ ≥ 1, ∀A ≥ A₀` re-pin + both (7.61) tail pins **RATIFIED**. Dated runs: 5 new proofs clean. `/lean-review`: ✅ CLEAN (372 added lines). D4-change ε-sweep tripwire armed.
- [Pass 19](judge/pass-19.md) — 2026-07-12, lap-58 boundary: **BOTH (7.61) TAILS + X10a PROVED & VERIFIED** ✅ — `fpDistPlus_height_tail`/`fpDistPlus_col_tail` now ratified+proved+clean; `encounter_apex_proximity` (X10a, the (7.63)→(7.65) confinement) **ratified vs p.53** + clean; engines (`fpDist_height_tail`, `fpDist_col_dev`, `holdSum_col_tail`) clean. **X10b pinned; committed form NOT ratified** — the lap-59 regime hypothesis `(s')² ≤ 1+s` is **pre-authorized** (pin false without it for s' ≫ √s; consumer-safe via `s' ≤ m^0.4` + `s > m/log²m`). X10 badge high/70% → **medium/80%**; headline = X10b + glue. `/lean-review`: 🟡 1 flag — X10a's local `maxHeartbeats 1600000` lacks the SKELETON-SPEC-required `-- HEARTBEAT:` comment (box's to fix). Also: **statement-faithfulness audit CLOSED** (Math Inc agrees on Thm 1.3; Thm 3.1 verbatim; Series β "Korec" label fixed — see endgame section).
- **⚖️ Altitude ruling** (2026-07-12, Trevor, post-pass-20): **Remedy A at `epsBW = 10⁻⁹⁰`** — paper-faithful route restored; execution order + judge protocol in BLUEPRINT §2 and Live judge state below. X9 badge blocked/60% → 13–28 laps/70%.
- [Pass 22](judge/pass-22.md) — 2026-07-13, external-contribution cross-check (working tree, not a lap): **C5 / PROP 1.9 + LEMMA 4.1 COMPLETE** ✅ — `valuation_dist` + `valuation_tail` proved by an **OpenAI Codex** session (+1,183 lines across ValuationDist/Valuation). Pinned statements character-untouched incl. constituent `unifOddMod`; fresh faithfulness read vs Prop 1.9 p.7 + Lemma 4.1 p.22 confirms the `∀c₀ K ∃c₁ C ∀n n' X` shape. **Dated run caught a laundered hole**: `valuation_tail` initially depended on `sorryAx` via the long-parked (1.10) `PMF.abs_expect_indicator_sub_le_dTV` (Prob/Basic.lean:154) — textually sorry-free file, transitively conditional; judge proved (1.10) same pass (tsum triangle inequality + summability bookkeeping). Re-run: all 7 decls exactly the clean triple. Route note: Lemma 4.1 *derived from* Prop 1.9 + geometric tail (reverse of the paper's order; sound, non-circular). `/lean-review` (1,183 added lines): ✅ CLEAN. **Ninth verified node**; pass-21's `valVec_pos` nit resolved by codex unprompted. Repo sorries 21 → 17.
- [Pass 21](judge/pass-21.md) — 2026-07-13, external-contribution cross-check (working tree, not a lap): **C2 / LEMMA 2.1 COMPLETE** ✅ — `valVec_unique` proved by an **OpenAI Codex** session (uncommitted; judge committed after verification). Statement untouched by the proof landing AND newly **RATIFIED vs p.14** (the node's open RATIFY-2 resolved); route = the paper's own last-entry induction; dated runs (`syr_iterate_key`, `valVec_unique`, new `syr_iterate_odd`) all clean; `/lean-review` (148 added lines): ✅ CLEAN. Eighth verified node, first of the C-series. Nit armed: the paper's membership half (valVec entries ≥ 1) has no companion lemma — one-liner if a consumer needs it.
- [Pass 20](judge/pass-20.md) — 2026-07-12/13, lap-59 boundary: **X10 / LEMMA 7.10 COMPLETE END-TO-END** 🏆 — the campaign's highest-uncertainty node is a theorem. X10b `encounter_separated_sum` PROVED (statement survived the proof landing character-identically); glue `triangle_encounter_le` PROVED same lap, with the pinned headline relocated below its engines **character-identically** (judge-diffed across the move). Dated runs on all nine lap-59 decls (headline, X10b, both `G`-weight engines, banded/qualifying steps, three glue helpers) — all exactly the clean triple. Blueprint X10 → proof-leanok, badge dropped; §7 sorry trail now BlackEdge ×4 + ManyTriangles ×1 (⛔blocked). `/lean-review` (1,372 added lines): 🟡 2 flags — two more local `maxHeartbeats` bumps (1M on `log_sq_le_rpow`, 2M on the assembly) without `-- HEARTBEAT:` comments (nit now ×3). Treadmill stopped after this lap (Trevor-directed evening wrap); 🗂️ ManyTriangles split directive queued for the next run's first lap.

## Live judge state 📍 (update each pass)

**Verified complete** (dated judge-run `#print axioms`, all exactly
`[propext, Classical.choice, Quot.sound]`): **X3** (2026-07-10), **S3** (pass 5),
**X6** (pass 7), **X1** (pass 11), **X5** (pass 12 — Lemma 7.6, 15 decls),
**X2** (pass 12 — both halves; damping consumer closed with it),
**X10** (pass 20 — Lemma 7.10 end-to-end: headline `triangle_encounter_le` +
the full engine chain, the first of the two pinnacle kernels),
**C2** (pass 21 — Lemma 2.1 uniqueness `valVec_unique` proved by an external
Codex session, judge-ratified vs p.14 + verified; RATIFY-2 resolved),
**C5** (pass 22 — Prop 1.9 `valuation_dist` + Lemma 4.1 `valuation_tail`,
external Codex session; judge discharged the parked (1.10) PMF lemma the tail
consumed).

**Statements pinned + ratified**: every ledger node except **C8** (no pinned Lean
statement yet — the last un-pinned node). Latest: X10 `∃A₀` re-pin + the two (7.61)
tail pins (pass 18), X9 depth-gated re-pin (pass 14). ⚠️ **SUSPENDED**:
`fpDist_white_exit_deep` (pass 18 — see the escalation bullet; the pin's text is
unchanged, but its truth at the frozen ε is no longer judge-believed).

**Open riders / queued fronts**:
- **⚖️ ALTITUDE RULING LANDED (Trevor, 2026-07-12): Remedy A at `epsBW = 10⁻⁹⁰`**
  — resolves the pass-18 escalation (`F.separated` vacuous at 10⁻⁴: (0.921)² <
  1 = min lattice distance²; the paper's (7.50) consumes real separation; NOT a
  paper error). New separation = 9·ln 10 ≈ 20.7; rational power of ten keeps
  exact-ℚ; hybrid rejected for route-risk (novel kernel argument + thin margin +
  double-sweep tail). Execution order in BLUEPRINT §2: split → dedicated
  D4-change lap (numeral + mechanical repairs only; `sep_const_sq_le_one` dies;
  X3's separation clause re-opens) → real Lemma-7.4 separation (pp.46–48) →
  kernel per p.48. Suspensions (`fpDist_white_exit_deep` ratification,
  `fpDist_any_triangle_le` route) lift ONLY via post-sweep re-ratification.
  ⚠️ X3 and X2 lose verified status when the D4 change lands, until judge
  re-runs post-sweep. Unaffected: X10's apex route (disjointness-based),
  `fpDist_out_of_strip_le`, the other verified nodes.
- **🔔 D4-CHANGE TRIPWIRE (armed, pass 18)**: any `epsBW` change re-values every
  `black`/`white`-dependent theorem with NO textual diff — a semantic statement
  edit repo-wide. Judge sweep list on the ruling landing: `sep_const_sq_le_one`
  (must die), the 13-row gap numeral (`⌊log₂((1−ε)/ε)⌋`), the deep pin's `51/100`
  vs new p₀ numerics, the ε₀-floor vs new epsBW (easier), X2's `exp(−ε³)` gain
  (weaker → `C_{A,ε}` inflates), (7.52)-budget + out-of-strip thresholds,
  confinement margin. The p₀-softening tripwire is superseded while the
  suspension lasts and re-arms verbatim on the post-remedy re-pin.
- **ε₀-floor: DISCHARGED at the statement level** (pass 17; demand pass 16): the
  kernel pin carries `51/100 ≤ p₀`, so `ε₀ = min(1/100, ·) ≥ 1/100 ≥ 10⁻⁴` by
  arithmetic. Survives the escalation as a statement property (whatever proves
  the pin post-remedy inherits the numeral); re-check p₀ numerics on a D4 change.
- **Axiom-check queue**: cleared (pass 20 — nine lap-59 decls verified clean,
  including the X10 headline). Prop 1.17's whole remaining sorry trail =
  BlackEdge ×4 (`fpDist_edgeWeight_le`, `fpDist_white_exit`,
  `Q_black_edge_case2`, `Q_black_edge_case3`) + ManyTriangles ×1
  (`fpDist_any_triangle_le` ⛔blocked on the altitude ruling).
- **X10 COMPLETE (pass 20)**: X10b's pre-authorization discharged character-exact
  (`ae0918c`, pass-19 addendum), X10b proved + verified; glue proved + verified;
  the pinned headline was relocated below its engines character-identically
  (judge-diffed). Blueprint node → proof-leanok. X10's completion means the
  Case-3 chain to Prop 1.17 now waits only on the white-exit kernel (X9,
  ⛔altitude ruling) and BlackEdge assembly.
- **Box docstring nits** (box's to fix): `White.lean:11` + `Reduction.lean:12`
  stale "carries sorry" claims (pass 12); `triangle_encounter_le` DEVIATION NOTE
  says "≈ 4p mean height drift" — height mean is 16/step, 4 is the column mean
  (pass 18); `-- HEARTBEAT:` justification comments missing on all three local
  bumps (X10a 1.6M pass 19; `log_sq_le_rpow` 1M + assembly 2M pass 20 — the 2M
  on the completed assembly is also a mathlib-bump brittleness ledger item).
  ~~Lemma 2.1's membership half needs a companion lemma~~ RESOLVED pass 22:
  codex added `valVec_pos` (ValuationDist.lean) unprompted.
- **🗂️ Split directive queued (steering `12515c4`)**: ManyTriangles.lean
  (now 4,782 lines) splits into 4 dependency-ordered files on the NEXT
  treadmill run's first lap — pure moves, names verbatim, thin re-export shim;
  judge verifies via sorry census + name-based axiom runs. Treadmill stopped
  2026-07-12 evening after lap 59 (`stop --after-lap`, Trevor-directed).
- **Judge recipe amendment** (pass 18): each pass diffs the event range AND
  checks `git log <range-end>..HEAD` before publishing assessments — the box
  commits concurrently, and pass 17's 85% badge went out with the escalation
  already in-tree.
- **X9 consumer checks: JUDGE-VERIFIED pass 15** (pp.48–49 + 54–56 read: (7.54)'s
  0.9m split and (7.67)'s in-window iteration keep every counted encounter at
  depth ≥ 0.1m ≥ g once `C_{A,ε} ≥ 10g`); X10's p.54 consumption is at a single
  large A — safe for the `∃A₀` re-pin (pass 18).
- **Paper-gap ledger** (both document-don't-announce, per Trevor 2026-07-12):
  entry #5 = Lemma 7.9 p.51 conditioning display (pass 9, ~90%); entry #6 =
  near-edge overreach in all-starts Lemma 7.9 (pass 13). KB
  `formalization-literature-holes.md`. No public post leads with these; author
  note is Trevor's call only. (The pass-18 escalation is NOT entry material —
  formalization-internal.)
- **Unread paper fronts**: §5 first-passage (C8) only. All of §7 (pp.33–56) is
  judge-read: pp.41–43 pass 12, pp.48–49 + 54–56 pass 15, pp.48 + 51–52
  re-read pass 18.
- **Trust-surface notes**: `fpDist` / `fpDistPlus` encode stopped-walk laws at the
  design level (strong Markov absorbed — D1, ratified passes 2 & 8);
  `fpDist_white_exit` (X8) and `fpDist_white_exit_deep` (X9 input) are the two
  load-bearing white-exit kernels — same geometry, different budget regimes, and
  the kernel-merge plan derives the X8 twin from the deep one post-remedy.

## Endgame — announcement plan (on full discharge) 📣

Recorded 2026-07-12 (Trevor). **Primary venue: Lean Zulip** — the
[dreams-of-big-projects thread](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/dreams.20of.20big.20projects/near/547102616)
contains a standing request for exactly this proof; answer it in-thread.
**Secondary (completeness): ccchallenge.org submission** (Tao2022; mirror the audited
exemplar `tcosmo/BohmSontacchi1978_lean`). Post both. Ren drafts, **Trevor posts**.
The announcement is about the formalization — the Lemma 7.9 deviation stays in the
repo docs and is NOT led with or bragged about (Trevor, 2026-07-12).
Pre-announce tripwires: `curl -s https://ccchallenge.org/api/papers/Tao2022` still
`not_started`, and `git-safe -C ~/src/clone/tao_collatz_idris2_formalization fetch`
for competitor movement. Also before going public: the repo needs the pre-public
PDF-expunge sweep (committed paper PDFs → history rewrite).
✅ **Statement-faithfulness audit CLOSED (2026-07-12, judge)**: (1) `Statement.lean`'s
`tao_collatz` diffed against Math Inc's independent rendering
([math-inc/FormalQualBench](https://github.com/math-inc/FormalQualBench)
`CollatzMapAlmostBoundedValues/Main.lean`) — **the two agree**: same log-density notion
(their `1/log N` normalizer ⟺ our Def-1.2-exact `Σ 1/n` ratio; their
exceptional-set-density-0 ⟺ our good-set-density-1; their `∃k, orbit < f n` ⟺ our
`colMin N < f N` with `colMin = sInf` over the k=0-inclusive orbit); our `f : ℕ → ℝ` is
the paper-exact form (theirs is the narrower `ℕ → ℕ`). (2) `tao_collatz_quantitative`
verified verbatim against Theorem 3.1 p.16 — including the `∀ x ≥ 2` uniformity, which
is Tao's own "for all x ≥ 2", and the ℙ-ratio Col_min display. (3) Series β density
wording FIXED (§4 above): Remark 5.1 = log density, un-optimized θ — never "Korec".

## Judge loop — standing ops while the treadmill runs (2026-07-12)

The treadmill (fable/low grind laps) produces; the HOST session judges. This section is
the self-contained recipe — a fresh/compacted session should be able to run the loop
from here alone.

**Trigger**: each new `handoff:` commit (= a lap ended). A host Monitor emits on these;
also fine to sweep ad hoc.

**Per pass:**
1. `git-safe -C ~/src/tao-collatz log --oneline <last-judged>..HEAD` — read the lap's
   commits. Identify NEW or CHANGED *statements* (new `sorry`d theorems, new defs bound
   for blueprint nodes, any edit to an already-ratified statement — diff those verbatim).
2. Ratify vs `papers/tao-2019-almost-all-orbits.pdf`. Already-ratified ground is
   indexed in the Campaign log above (per-pass files in `judge/`); the still-unread
   fronts are in Live judge state.
3. Blueprint flips in `blueprint/src/content.tex`: statement-`\leanok` ONLY when landed
   + compiled + judge-ratified (add `\lean{...}` bindings, RAW names — `\_` escapes
   break plasTeX). Proof-`\leanok` ONLY on a judge-run `#print axioms` (host
   `lake env lean` on a scratch file; expect [propext, Classical.choice, Quot.sound]).
   Re-rate `\lapsrisk` when the evidence moves; mirror the BLUEPRINT.md §2 ledger row.
4. Rebuild: `cd blueprint && ./build.sh` (never bare `leanblueprint web`). Verify via
   the extracted DOT if suspicious (tools: sandbox extract_depgraph_dot.py).
5. Commit `--no-verify` scoped to `blueprint/ judge/ EXECUTABILITY.md BLUEPRINT.md`
   (never sweep the box's in-flight Lean files); push (boxes cannot).
6. Record the pass as `judge/pass-NN.md`, add its index line to the Campaign log, and
   refresh the Live judge state section.

**Cautions**: boxes MISLABEL ledger ids (session 4 called Prop 7.3 work "X5") — ratify
by declaration, never by label. A statement edit to an already-green node REVOKES its
`\leanok` until re-ratified. Worker claims of axiom-cleanliness are hypotheses until the
judge reruns `#print axioms`.
