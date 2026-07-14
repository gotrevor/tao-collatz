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
- [Pass 23](judge/pass-23.md) — 2026-07-13, external-contribution cross-check (working tree, not a lap): **D4 CHANGE + REAL LEMMA-7.4 SEPARATION EXECUTED** ✅ + **SECOND ALTITUDE-CLASS ESCALATION** ⚠️ — **OpenAI Codex** landed `epsBW = 10⁻⁹⁰` with all mechanical repairs; the armed ε-sweep FIRED and all seven items discharged (X2/X3/X10 re-verified clean at the new ε); Lemma 7.4 Claim (*) Cases 1–3 formalized as REAL separation (pass-18 vacuity closed for good; `black_structure` gained one additive construction conjunct — re-ratified). Every pinned statement character-preserved across a BlackEdge→Case3 reorganization; old 10⁻⁴-era white-count route lemmas deleted (consistent with the pass-18 withdrawal). **New escalation**: the blocked tail was reduced to `sep > √(X²+Y²)` for an explicit localization box — but X ≈ 2.6·10⁶ vs sep ≈ 20.7 (lossy `16j−5l` Chernoff); no feasible frozen ε closes it. Exits: tighten the localization (judge p.48 re-read first — recommended) or re-open D4 as a parameter. Suspensions persist. Sorry trail: same 5 crux statements; repo 17 → 14. Split still queued (ManyTriangles now ~5,200 lines).
- [Pass 25](judge/pass-25.md) — 2026-07-13, lap boundary (treadmill laps 1–3, opus medium→high, 16 commits): 🏆 **X9 / LEMMA 7.9 COMPLETE** — the second pinnacle kernel is a theorem; **both are now done**. The tail blocked since pass 18 and escalated at pass 23, `fpDist_any_triangle_le`, is **PROVED axiom-clean**, and with it `fpDist_white_exit_deep` + `many_triangles_white`; `ManyTriangles.lean` has **zero sorries**. Pass-24's two constants landed inside the judge's envelope: `B` = **64** (exact `Hold` MGF, tilt freed 1/20000 → 1/16, **no `native_decide`**), `Y` = **150** (`renewal_level_le_one`, X6 left existential). Box `√(51²+150²) ≈ 158.4` < `sep ≈ 230.26` at the pre-authorized `epsBW = 10⁻¹⁰⁰⁰`. The D4 lap was dedicated and **all 12 pinned statements byte-identical** across it. 🔔 **ε-sweep FIRED + DISCHARGED** (X3/X2/X10 + 2 consumers re-verified clean at the new ε — ledger survives a 910-OOM drop; tripwire RE-ARMS). 🔓 **Zero open suspensions** for the first time since pass 13. Remaining trail = Case-2/Case-3 assembly (5 crux, all in BlackEdge/Case3).
- [Pass 26](judge/pass-26.md) — 2026-07-14, **overnight boundary, judged mid-run** (laps 4–8, 47 commits, `e08871e..61f8e80`; run in a worktree pinned at `61f8e80` because the box was still live in the shared tree): 🏆 **X8 / CASE-2 COMPLETE** — the twelfth verified node (`Q_black_edge_case2`, `fpDist_white_exit`, `fpDist_edgeWeight_le`, `fpDist_fst_mgf_le` all clean; the review lap's "judge to ratify" is now ratified). **20 decls axiom-clean**; the §7 crux collapsed **5 → 2** (`few_white_mass_le` (7.56) + `col_tail_mass_le`); sorries **14 → 11**, all by *proving*. X9 re-verified clean under the change below. Hard rails 2/3/4 honored (`Statement.lean` untouched, `epsBW` frozen, zero `native_decide`, nothing parked in `wip/`); `fpDist_white_exit` + `Q_black_edge_case2` relocated to a new `BlackEdgeQ.lean` **character-identically**. 🚨 **BUT `61f8e80` EDITED FOUR RATIFIED STATEMENTS** — it swapped the deep hypothesis `m/log²m < s` → `m^0.8 < s` in `triangle_encounter_le` (**X10 = Lemma 7.10**), `encounter_apex_proximity` (**X10a**), `bigTriangle_walk_le`, `estar_union_le`. **The route reasoning is RIGHT and concurred**: the frozen `Q_black_edge_case3` sits at depth `m+1`, and `m/log²m < s ⟹ (m+1)/log²(m+1) < s` genuinely FAILS (`x/log²x` increasing; fractional-part counterexample — judge-verified). **But it is not the "generalization" the commit claims**: the hypotheses are *incomparable* (`m^0.8 ≤ m/log²m` only for `m ≳ 10^15.5`; below that the new form covers **fewer** `s` — a silent restriction that compiles green), and **Tao p.51 states Lemma 7.10 with `s > m/log²m` verbatim**, so X10 no longer formalizes it. ⚖️ **X10 + X10a ratifications REVOKED** (blueprint `\leanok` down). **Repair mandated — split, don't revert**: keep the four proved lemmas as `*_rpow` engines, restore the two pins at their `e08871e` statements as corollaries (`m ≥ 10^27` via `log_sq_le_rpow`; `m < 10^27` trivial since LHS ≤ 1 ≤ `C·A²(1+p)/s'` for `C ≥ 10^11`), and thread `Cthr ≥ 10^27` so the depth-`m+1` bridge actually closes (still unproved, inside the two sorries). 🔧 **Two system fixes**: the differ's PINNED list **was the blind spot** (X10a's rewrite went unreported — it wasn't in the dict; X10 was caught by luck) → rewritten to 19 names, cross-file (moves ≠ deletions), argv revs; and **new HARD RAIL 6**: *never EDIT a ratified pin — not to weaken, not to strengthen, not to generalize; flag the judge.*
- [Pass 27](judge/pass-27.md) — 2026-07-14, **overnight-run-#2 boundary, judged mid-run** (laps 1–6, **53 commits**, `4f51542..8505bd4`; worktree pinned at `8505bd4`, build green 3285): 🏆 **§7 IS COMPLETE AND JUDGE-VERIFIED — the campaign's 65–75% risk concentration is retired.** **24 decls axiom-clean**, incl. the whole §7 spine (`prop_7_8`, `Q_black_edge`, `Q_black_edge_case3`, `Q_polynomial_decay`), both Case-3 leaves (`few_white_mass_le` (7.56), `col_tail_mass_le` (7.54)), both §7 exports (`charFn_decay`, `key_fourier_decay`), the reduction floor (`colMin_eq_syrMin_oddPart` = paper (1.2), + SyracRV 1.12/(1.21)/(1.22)), and the C10 machinery (density-general `osc_le_sqrt_highfreq`, `fnat_split`, `syracZ_offset_split`, `char_offset_split`, `PMF.cexpect_iid_append`, `cond_char_factor`, `dft_cond_density`). **Sorries 11 → 4** (C10 + C9 + 2 headline stubs), all by *proving* — nothing parked in `wip/`. 🔓 **THE `Cthr` BRIDGE IS DISCHARGED** — pass 26's one unverified step, the depth-`m+1` gap where `m/log²m < s ⟹ (m+1)/log²(m+1) < s` genuinely fails, is now **kernel-checked in Lean** (`Case3.lean:2011–2068`: `(m+1)^0.8 ≤ 2m^0.8`, `log²m ≤ 400·m^0.1`, hence `(m+1)^0.8·log²m ≤ 800·m^0.9 ≤ m`, then `< s`). 🔎 **And the judge's own numeral was wrong**: the largeness is consumed at `800 ≤ m^0.1`, which at pass-26's `Cthr = 10^27` gives `m^0.1 ≈ 501 < 800` — *the route fails*. The box independently baked **`10^30`** (`m^0.1 = 1000`), and **the worker's constant is what carried the proof**. A judge-supplied numeral is a hypothesis too. **Statement erosion: 28/29 byte-identical** across 53 unattended commits (the one hit — `colMin_eq_syrMin_oddPart`'s `(_hN` → `(hN` — is an identical `Prop`, benign, ratified). **HARD RAIL 6 held**; zero `JUDGE-FLAG:`s. `/lean-review`: 🔴 tier **empty** (no new heartbeats/`native_decide`/`axiom`/trust-escapes/**Prop-defs**); 8 🔵 `mul_le_mul_left'` deprecations in `Case3.lean`. 🔧 **System fix — the differ was aimed at the finished half of the proof**: its 19 names were §7 + `Statement` *only*, so **`fine_scale_mixing` (C10) and `stabilization` (C9) — the repo's two live sorries — were UNWATCHED** (their files weren't even searched). *A lap weakening the very statement it is trying to prove is the highest-value silent failure available*, and nothing would have seen it. Grown to **29 names / 13 files**, with a new documented distinction: **WATCHED ≠ RATIFIED** (watching an un-ratified statement is how we *see* the frontier move). Both crux statements verified byte-identical for the night. **Standing rule generalized: ratify ⟹ watch (pass 26); and when the frontier moves, MOVE THE GUARD WITH IT (pass 27).** Objective scorecard: §7 sorries ✅, X10 repair ✅, fruit ⚠️ 1-of-3 (spine stubs eaten; `ManyTriangles` split skipped an **8th** lap → **dropped from the directive** rather than fake-ordered a ninth time; C8 still unpinned → now blocking, must be pinned before C9).
- [Pass 28](judge/pass-28.md) — 2026-07-14, **ruling pass** (no new axiom runs; pass 27's pin stands): the overnight run raised a `JUDGE-FLAG` asking the judge to ratify a deviation from Tao's **Cor 6.3 window (6.8)**. ✅ **RATIFIED** — and explicitly **not** a pass-26-class event: pass 26 was a *ratified pin* swapped for an **incomparable** statement (X10 stopped formalizing Lemma 7.10); this is an *internal lemma* whose hypothesis was **restricted** (our window ⊂ the paper's) ⟹ strictly **weaker** ⟹ **cannot introduce unsoundness**, and `fine_scale_mixing`'s statement is byte-identical. *A restriction costs sufficiency, never soundness* — so the risk lives at the **call site**, and that is where the judge looked. 🚨 **And the forward plan was IMPOSSIBLE ON BOTH COUNTS.** The proved kernel `fnat_lt_of_suffix_window` takes `hbudget` as a hypothesis and runs AM-GM at **ε=1/5** (cost `0.601·C² + 0.693·C` per `ln n`). Judge-recomputed (`tools/tao_hbudget_check.py`): **(6.8) can NEVER discharge it — for ANY `C`** (budget − cost has a **negative `C²` coefficient**, `0.347 − 0.601 = −0.254`; the sign is wrong, not the size), and the tight window closes **only for `C_A ≥ 23`**. Yet `DIRECTION.md` (review lap) ordered the next lap to *"discharge `hbudget` from the **(6.8)** l-range + `Cₐ≥10`"* — **the very window its own reflection had just refuted**, at a constant **2.3× too small**. The stale `≥10` came from a *pre-proof* ε=1/4 estimate and had propagated into DIRECTION + the reflection block + `literature-review.md`; **the correct number (`C ≳ 23`) was sitting in the proved lemma's own docstring the whole time.** 📌 **Lesson — pass 27's, mirrored**: pass 27 learned *a judge-supplied numeral is a hypothesis too* (my `10^27` was wrong; the box's `10^30` carried the proof). Pass 28: **a WORKER-supplied numeral is a hypothesis too, and when two disagree, the one bolted to the machine-checked artifact wins.** Nothing was unsound and nothing was going to become unsound on its own — the danger was second-order and it is the one this apparatus exists for: **a lap grinding at an impossible target is a lap under pressure.** 🔧 DIRECTION got a binding correction block (tight window only; `C_A ≥ 23`; or re-prove the kernel at ε=1/4 to buy back `C ≳ 10` — a strengthening of an unwatched internal lemma, allowed). 🔔 **Tripwire: `hbudget` is now the campaign's single load-bearing undischarged number** — and ⚠️ `C_A = 23` worsens the single-point mass to `n^{O(C_A²)}·3^{-n}`; "absorbed by taking `A′` large" is an **assertion, not a proof** — make the lap show it, and if it does not absorb, `JUDGE-FLAG:` rather than shaving `C_A` back.
- [Pass 24](judge/pass-24.md) — 2026-07-13, judge homework (p.48 localization re-read; no worker output): **SECOND ESCALATION DOWNGRADED — NOT altitude-class** ✅. The paper's (7.50) O(1) is a distance **from Δ**, not from the start (drift slope 1/4 < edge slope log2/log9, so the walk drifts *along* Δ), and is explicitly ε-free; Codex's geometry already renders exactly that (top-projection into Δ + `F.separated`) — the route is sound. The entire blocker is **one lossy constant**: `fpDist_linear_tail` replaces the step law's exact MGF (`geomQuarter` × `pascalNe3`, mean (4,16), drift −16/step) with a quadratic bound that near-cancels the drift and caps the tilt at 1/20000 (true ceiling 0.213), shipping `B = 4·10⁷` where the honest optimum is **B ≈ 42** (~10⁶×; and 4·10⁷ is 167× above even its own bound's need). The *real* blocker is the other constant: `fpDist_height_tail`'s `Y` is **existential** (it sums X6's envelope), so the box is not a number at all — fixed without re-opening X6 by renewal-conv + **strictly increasing heights** (`Δl ≥ 3` ⟹ each level visited at most once ⟹ renewal mass per level ≤ 1) + `Δl`'s exact MGF ⟹ **`Y = 139`**. Box `= √(47²+139²) ≈ 147` **vs sep ≈ 20.72 — does not fit**, so ⚖️ **one cheap ruling is needed**: numeral re-freeze `10⁻⁹⁰ → 10⁻¹⁰⁰⁰` (sep ≈ 230; 1000-digit rational, `norm_num`-trivial; fires the armed ε-sweep, all 7 items monotone-good at smaller ε). Pass-23's "no feasible ε" (11-million-digit numeral) was an artifact of the garbage `B` — off by four orders of magnitude in the exponent. **D4-as-a-parameter is OFF the table.** Both lemmas are ε-free: land them first, then pick `d` from the constants actually proved. Two worker tasks issued (BLUEPRINT §2); numerics in `tools/tao_linear_tail.py` + `tools/tao_height_tail.py`.
- [Pass 22](judge/pass-22.md) — 2026-07-13, external-contribution cross-check (working tree, not a lap): **C5 / PROP 1.9 + LEMMA 4.1 COMPLETE** ✅ — `valuation_dist` + `valuation_tail` proved by an **OpenAI Codex** session (+1,183 lines across ValuationDist/Valuation). Pinned statements character-untouched incl. constituent `unifOddMod`; fresh faithfulness read vs Prop 1.9 p.7 + Lemma 4.1 p.22 confirms the `∀c₀ K ∃c₁ C ∀n n' X` shape. **Dated run caught a laundered hole**: `valuation_tail` initially depended on `sorryAx` via the long-parked (1.10) `PMF.abs_expect_indicator_sub_le_dTV` (Prob/Basic.lean:154) — textually sorry-free file, transitively conditional; judge proved (1.10) same pass (tsum triangle inequality + summability bookkeeping). Re-run: all 7 decls exactly the clean triple. Route note: Lemma 4.1 *derived from* Prop 1.9 + geometric tail (reverse of the paper's order; sound, non-circular). `/lean-review` (1,183 added lines): ✅ CLEAN. **Ninth verified node**; pass-21's `valVec_pos` nit resolved by codex unprompted. Repo sorries 21 → 17.
- [Pass 21](judge/pass-21.md) — 2026-07-13, external-contribution cross-check (working tree, not a lap): **C2 / LEMMA 2.1 COMPLETE** ✅ — `valVec_unique` proved by an **OpenAI Codex** session (uncommitted; judge committed after verification). Statement untouched by the proof landing AND newly **RATIFIED vs p.14** (the node's open RATIFY-2 resolved); route = the paper's own last-entry induction; dated runs (`syr_iterate_key`, `valVec_unique`, new `syr_iterate_odd`) all clean; `/lean-review` (148 added lines): ✅ CLEAN. Eighth verified node, first of the C-series. Nit armed: the paper's membership half (valVec entries ≥ 1) has no companion lemma — one-liner if a consumer needs it.
- [Pass 20](judge/pass-20.md) — 2026-07-12/13, lap-59 boundary: **X10 / LEMMA 7.10 COMPLETE END-TO-END** 🏆 — the campaign's highest-uncertainty node is a theorem. X10b `encounter_separated_sum` PROVED (statement survived the proof landing character-identically); glue `triangle_encounter_le` PROVED same lap, with the pinned headline relocated below its engines **character-identically** (judge-diffed across the move). Dated runs on all nine lap-59 decls (headline, X10b, both `G`-weight engines, banded/qualifying steps, three glue helpers) — all exactly the clean triple. Blueprint X10 → proof-leanok, badge dropped; §7 sorry trail now BlackEdge ×4 + ManyTriangles ×1 (⛔blocked). `/lean-review` (1,372 added lines): 🟡 2 flags — two more local `maxHeartbeats` bumps (1M on `log_sq_le_rpow`, 2M on the assembly) without `-- HEARTBEAT:` comments (nit now ×3). Treadmill stopped after this lap (Trevor-directed evening wrap); 🗂️ ManyTriangles split directive queued for the next run's first lap.

- [Pass 29](judge/pass-29.md) — 2026-07-14, **boundary pass** (`8505bd4..7ff033b`, **70 commits**, two workers: treadmill boxes + an external **Codex** session; judged in the shared tree, treadmill idle, build cached green). **The range is ACCEPTED — the best since §7 closed, and all three of pass 28's open questions resolve in the work's favour.** 🔓 **BOTH TRIPWIRES DISCHARGED.** #1 `hbudget`: `lRange_hbudget` axiom-clean **and no longer floating** — it is *consumed inside* a proved theorem (`osc_mainHigh_bound`); a discharge nothing consumes is a claim, a discharge a proved theorem depends on is a fact. #2 the **`A′`-absorption at `C_A = 30`**: pass 28 said *"that is an assertion, not a proof — make the lap show it."* **The lap showed it** — `osc_mainHigh_bound` is axiom-clean and carries the absorption via head decay at the **shifted exponent** `A' = A + C_A²·log2` (≈ A+624 at C=30), which is exactly what pays for the `n^{O(C_A²)}` single-point mass that `C_A = 30` bought (`charFn_decay` holds for every A′, so the shift is free). 🔴 **Q1 — "is C10 closed, or was the sorry relocated to launder the census?" NEITHER: it is an honest decomposition, and an unusually good one.** The hole moved to a *named* lemma whose statement is exactly the obligation that remains. *The census was right to be distrusted, and `#print axioms` is what settled it — exactly as pass 28 predicted.* 🎯 **C10 is now ONE probabilistic statement.** Two machine-checked identities collapse it: `mainHigh_eq_restrictedDensity` (`mainHigh` **is** the restricted Syracuse pushforward) and `sum_abs_syracZ_sub_mainHigh_eq` (`∑|syracZ − mainHigh|` **=** `P(¬mainEvent)` — an *equality*). So `error_l1_high_bound` is precisely **`P(¬mainEvent) ≤ (C/2)·m^{-A}`**: a tail estimate, no structure, no novel kernel, no constant risk left. ⚖️ **RULING on Codex's requested judge attention** (`condWindow` is an *enlargement* of Tao's `Eₖ`, not literally all of it): **✅ safe, and it works in our favour** — a bigger good event ⟹ a smaller complement ⟹ an *easier* tail bound, and the osc bound is proved *from* the enlarged event. The events are **internal** (absent from the pinned statement), so **a wrong event choice cannot make the theorem false — only `error_l1_high_bound` unprovable. It costs provability, never soundness.** (Pass 28's principle, mirrored: there an internal window was *restricted*, and the risk lived at the call site.) Two binding demands follow: never document `condWindow` as EQUAL to the paper's `Eₖ`, and **PROVE `globalGood ⊆ mainEvent` explicitly** — that inclusion *is* the remaining content. 🐛 **A genuine faithfulness bug, found + fixed by Codex, nearly lost to a five-word commit message**: the tail block is stored **reversed** `(a_{k+1},…,a₁)`, so Tao's `a[1,k]` is `pre vt p − pre vt 1`, **not** `pre vt (p−1)` — the old `stopEvent` removed `a₁` instead of `a_{k+1}` and **did not produce the claimed stopping-time partition**. It compiles green either way. Now *proved* disjoint (`mainPieceEvent_cut_unique`), which is the form the fix takes when it cannot regress. 📌 **New standing rule — a convention that has bitten TWICE is a HAZARD, not a convention.** The D2 reversed-coordinate trap was already known well enough to be encoded in the numeric harness, and it bit anyway, in the one definition whose entire job was to be a partition. **The guard is not vigilance, it is a proved lemma: every event definition claiming to be a partition owes a proved disjointness lemma beside it. An unproved partition claim is a SEAM WEARING A DEFINITION'S CLOTHES** — zero sorries, and load-bearing (the same disease C7/C8 have, one level down; the census cannot see either). **Statement erosion: 29/29 character-identical** across all 70 commits — HARD RAIL 6 held through a **two-worker** range. `blueprint_audit`: 13 nodes proved + axiom-clean, 0 drift, 0 false-green, 2 seams. Baseline **4 sorries + 2 seams**. 🧭 **Campaign re-aimed (Trevor): C10 → C8 → C9** — an order *forced by the dependency graph* (C9 consumes both; C8 is a seam with nothing behind it), not a preference.

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
consumed),
🏆 **X9** (pass 25, 2026-07-13 — **Lemma 7.9 end-to-end**: `many_triangles_white` +
the kernel `fpDist_white_exit_deep` + the long-blocked tail `fpDist_any_triangle_le`,
all clean; `ManyTriangles.lean` now has ZERO sorries. **The second pinnacle kernel —
both are now complete.**),
🏆 **X8** (pass 26, 2026-07-14 — **Case-2 end-to-end**: `Q_black_edge_case2` +
`fpDist_white_exit` + `fpDist_edgeWeight_le` + `fpDist_fst_mgf_le`, all clean. The
twelfth verified node; the last Case-2 obligation),
🏆🏆 **§7 COMPLETE — X11 / Case-3 + the whole §7 spine** (pass 27, 2026-07-14):
`Q_black_edge_case3`, `Q_black_edge`, `prop_7_8`, `Q_polynomial_decay`, and both Case-3
leaves `few_white_mass_le` (7.56) + `col_tail_mass_le` (7.54) — all clean. **`prop_7_8` no
longer carries `sorryAx`. The campaign's stated 65–75% risk concentration is RETIRED.**
Plus the **reduction floor**: `colMin_eq_syrMin_oddPart` (paper (1.2)) + the SyracRV
identities (Lemma 1.12, (1.21), (1.22)), and §7's two exports `charFn_decay` (Prop 1.17) +
`key_fourier_decay` (Prop 7.1).

🔬 **C10 — verified DOWN TO ONE TAIL BOUND** (pass 29, 2026-07-14): `lRange_hbudget`,
`osc_mainHigh_bound` (**the `A′`-absorption at `C_A = 30` is SHOWN, not asserted**),
`mainHigh_eq_restrictedDensity`, `sum_abs_syracZ_sub_mainHigh_eq`, `tailDensW_condWindowB_le`
— all clean. `fine_scale_mixing` still carries `sorryAx`, through **exactly one** named lemma:
`error_l1_high_bound` = **`P(¬mainEvent) ≤ (C/2)·m^{-A}`**. Both pass-28 tripwires discharged.

**Statements pinned + ratified**: every ledger node except **C8** (no pinned Lean
statement yet — the last un-pinned node; **it is a SEAM: zero theorems, zero sorries,
invisible to the census, and it BLOCKS C9**). Latest: X10 `∃A₀` re-pin + the two (7.61)
tail pins (pass 18), X9 depth-gated re-pin (pass 14). 🔓 **ZERO OPEN SUSPENSIONS**:
`fpDist_white_exit_deep`'s suspension (pass 18, re-grounded pass 23) is **lifted by
proof** — it is now a theorem, axiom-clean (pass 25). A proof settles truth; nothing is
left to believe.

✅ **X10 + X10a REVOCATION DISCHARGED SAME DAY (pass-26 addendum, `4f51542`).** The repair
landed as overnight-run-#2's opening move: the four weaker-hypothesis lemmas are kept as
`*_rpow` **engines**, and both pins were **restored character-identically** and re-proved as
corollaries. Machine-checked: the differ reports **19/19 pinned statements byte-identical**
to the pre-deviation baseline, and dated runs on both restored pins *and* all four engines
(plus X9/X8, which survive the refactor) are exactly `[propext, Classical.choice, Quot.sound]`.
`ManyTriangles.lean` has **zero** sorries — restored by *proving*. **Ratifications RESTORED;
blueprint `\leanok` back up.** Net: a strictly stronger engine layer *and* a faithful Lemma
7.10. ✅ **The `Cthr` bridge is now DISCHARGED (pass 27)** — kernel-checked in Lean at
`Case3.lean:2011–2068`, and it needed **`10^30`, not the judge's `10^27`** (the largeness is
consumed at `800 ≤ m^0.1`; at `10^27` that reads `501 < 800` and the route *fails*). The box's
own constant carried it. **A judge-supplied numeral is a hypothesis too — check it like any other.**

🔧 **The differ now watches the FRONTIER, not just the finished half (pass 27).** Its 19 names
were §7 + `Statement` only, so the two live sorries — `fine_scale_mixing` (C10) and
`stabilization` (C9) — were **unwatched, in unsearched files**. A lap weakening the statement it
is trying to prove is the highest-value silent failure available, and no instrument was looking.
Now **29 names / 13 files**, with **WATCHED ≠ RATIFIED** written into the tool: a name in the
list means the differ *reports changes*; ratification stays the judge's reading against the PDF.
**Ratify ⟹ watch (pass 26). And when the frontier moves, move the guard with it (pass 27).**

*(Historical — the finding that produced the repair:)* ⚠️ **TWO RATIFICATIONS REVOKED
(pass 26) — X10 `triangle_encounter_le` + X10a
`encounter_apex_proximity`.** `61f8e80` rewrote their deep hypothesis
`m/log²m < s` → `m^0.8 < s`. Both are still **proved and axiom-clean** — the mathematics
is not in doubt — but **Tao p.51 states Lemma 7.10 with `s > m/log²m` verbatim**, and the
two hypotheses are *incomparable* (`m^0.8 ≤ m/log²m` only for `m ≳ 10^15.5`; below that the
new form covers **fewer** `s`). So X10 no longer formalizes Lemma 7.10 and its blueprint
binding is false. **This is a repair task, not a suspension.** Fix mandated in DIRECTION:
keep the four new lemmas as `*_rpow` engines, restore the two pins at their `e08871e`
statements as corollaries (`m ≥ 10^27` via `log_sq_le_rpow`; `m < 10^27` trivial, LHS ≤ 1 ≤
RHS for `C ≥ 10^11`), and thread `Cthr ≥ 10^27` so the depth-`m+1` bridge closes. Full
analysis: `judge/pass-26.md` §2.

**Open riders / queued fronts**:
- **🚨 X10/X10a REPAIR (pass 26) — the one open obligation outside the two sorries.**
  See above + DIRECTION's mandated 3-step repair. Until it lands, X10 is
  COMPLETE-but-UNRATIFIED (the only node in that state) and the blueprint's Lemma 7.10
  binding must stay un-`\leanok`'d.
- **🔒 HARD RAIL 6 (new, pass 26)**: *never EDIT a ratified pin — not to weaken, not to
  strengthen, not to generalize.* The old rail said only "never weaken", and lap 8
  sincerely believed it was *strengthening* (its commit says "generalize"), so it shipped
  a statement edit to four ratified lemmas without a flag. Adding a lemma beside a pin is
  always allowed; changing a pin is the judge's call. The 19-name pinned set is listed
  inline in DIRECTION and enforced by `tools/tao_stmt_diff.py`.
- **🔧 The differ WAS the blind spot (pass 26)**: `encounter_apex_proximity`'s rewrite went
  **unreported** because the name wasn't in the tool's PINNED dict; `triangle_encounter_le`
  was caught only because it happened to be listed. Rewritten: 19 pinned names (incl. X10a,
  the frozen Case-3 spine, and `Statement.lean`'s two headlines), searched **across all
  files** so relocations report as moves, revs via argv. **Ratify a statement ⟹ add it to
  that list in the same pass.**
- **Judging a live treadmill (pass 26)**: the box bind-mounts the repo and commits with
  `git add -A` — it swept pass-25's docs into its own commit `19ea98d`. Judge from a
  worktree pinned at the range end (`lean-create-worktree`, CoW `.lake`), never from the
  shared tree the box is editing.
- **⚖️ ALTITUDE RULING (Trevor, 2026-07-12): Remedy A at `epsBW = 10⁻⁹⁰` —
  EXECUTED (pass 23, Codex)**: D4 numeral + mechanical repairs landed; ε-sweep
  fired and discharged (all 7 items); X2/X3/X10 **re-verified clean at 10⁻⁹⁰**;
  real Lemma-7.4 separation formalized (sep ≈ 20.7 genuine, vacuity closed;
  `black_structure` + additive construction conjunct, re-ratified). The 🗂️
  split (step 1) was skipped — still queued, more urgent (~5,200 lines).
- **🏆 X9 COMPLETE + ε-SWEEP DISCHARGED (pass 25, 2026-07-13)**: pass-24's diagnosis
  executed in three laps. `B`: 4·10⁷ → **64** (exact `Hold` MGF closed form
  `tiltZ_hold_closed`; tilt freed 1/20000 → 1/16; **no `native_decide`**, as predicted).
  `Y`: existential → **150** (`renewal_level_le_one` — strictly-increasing heights ⟹
  renewal mass per level ≤ 1; **X6 NOT re-opened**). Box `√(51²+150²) ≈ 158.4` vs
  `sep ≈ 230.26` at the pre-authorized `epsBW = 10⁻¹⁰⁰⁰` — fits, ~45% margin. The
  D4-change lap was **dedicated** and **all 12 pinned statements are byte-identical
  across it** (judge character-diff; `Triangles.lean`'s 120 changed lines are pure
  proof-body arithmetic). 🔔 **ε-sweep FIRED and DISCHARGED**: X3/X2/X10 +
  `white_gap_above_run_top` + `fpDist_out_of_strip_le` all re-verified exactly clean at
  10⁻¹⁰⁰⁰ — the ledger survives a 910-order-of-magnitude ε drop. **Tripwire RE-ARMS**
  for any future `epsBW` change. Sorry trail: `ManyTriangles.lean` **0**; the 5 crux are
  now all Case-2/Case-3 assembly (`fpDist_fst_mgf_le` NEW, `fpDist_edgeWeight_le`,
  `fpDist_white_exit`, `Q_black_edge_case2`, `Q_black_edge_case3`). Full record:
  `judge/pass-25.md`.
- **✅ SECOND ESCALATION DOWNGRADED (pass 24) — NOT altitude-class**: the p.48
  re-read settles it. The paper's localization is a distance **from Δ**, not from
  the start point (the drift slope 1/4 is shallower than the edge slope
  log2/log9, so the walk drifts *along* Δ), and its O(1) is explicitly ε-free —
  and Codex's geometry already renders exactly that (top-projection into Δ via
  `triangle_top_mem_add`, then `F.separated`). The route is sound. The whole
  blocker is **one lossy constant**: `fpDist_linear_tail`'s `B = 4·10⁷`, which
  replaces the step law's *exact* MGF (`geomQuarter` ¼(¾)^{k−1} × `pascalNe3`,
  mean (4,16), drift −16/step) with a quadratic bound whose `1000(λ₁²+λ₂²)`
  penalty near-cancels the drift and caps the tilt at 1/20000 (exact ceiling:
  0.213). At the optimal tilt the honest threshold is **B ≈ 42** (~10⁶× smaller;
  and the shipped 4·10⁷ is 167× above even its own bound's requirement). The
  *real* blocker is the OTHER constant: **`fpDist_height_tail`'s `Y` is
  existential** (it sums X6's envelope, whose `(cL,CL)` are `∃`-bound), so the box
  is not a number at all. Fix without re-opening X6: renewal-conv + **heights
  strictly increase** (`Δl ≥ 3`, so each level is visited at most once ⟹ renewal
  mass per level ≤ 1 — no renewal theorem) + `Δl`'s exact MGF ⟹ **`Y = 139`**.
  Box: `X = ⌈(5·139+42)/16⌉ = 47`, `√(47²+139²) ≈ 147` **vs sep ≈ 20.72 — does NOT
  fit**. ⚖️ **ONE CHEAP RULING NEEDED (Trevor)**: numeral re-freeze
  `epsBW 10⁻⁹⁰ → 10⁻¹⁰⁰⁰` (sep ≈ 230, ~1.6× margin; 1000-digit rational,
  `norm_num`-trivial; fires the armed ε-sweep, all 7 items monotone-good at
  smaller ε per pass 23). **Sequencing**: both lemmas are ε-free — land them
  FIRST, read the real box, then pick `d` once (guessing fires the sweep twice).
  Priced honestly: Case 3's `10A/ε³` and `R = ⌊A²/ε⁴⌋` inflate with `d` (existential
  in every pin we hold, so free today). Suspensions STAND until both constants are
  numerals and the box inequality is proved: `fpDist_white_exit_deep` ratification
  SUSPENDED, `fpDist_any_triangle_le` sorried. Numerics:
  `tools/tao_linear_tail.py`, `tools/tao_height_tail.py`; full analysis
  `judge/pass-24.md`. Two worker tasks issued (BLUEPRINT §2).
- **🔔 D4-CHANGE TRIPWIRE: FIRED + DISCHARGED (pass 23)**: the `epsBW = 10⁻⁹⁰`
  change landed and the full sweep ran clean — `sep_const_sq_le_one` deleted as
  designed (now `twenty_lt_sep_const`/`sep_const_lt_twenty_six`), gap numeral
  re-ran, ε₀-floor easier, X2's gain consumers existential (re-verified), strip/
  budget thresholds and confinement re-verified. The tripwire RE-ARMS for any
  FUTURE epsBW change (same sweep list, judge/pass-18.md). The p₀-softening
  tripwire still re-arms verbatim on the post-remedy kernel re-pin.
- **ε₀-floor: DISCHARGED at the statement level** (pass 17; demand pass 16): the
  kernel pin carries `51/100 ≤ p₀`, so `ε₀ = min(1/100, ·) ≥ 1/100 ≥ 10⁻⁴` by
  arithmetic. Survives the escalation as a statement property (whatever proves
  the pin post-remedy inherits the numeral); re-check p₀ numerics on a D4 change.
- **Axiom-check queue**: cleared (pass 23 — 25-decl suite: 19 unconditional
  clean, 6 conditional-spine sorryAx-as-expected). Prop 1.17's whole remaining
  sorry trail = the same 5 crux statements: BlackEdge ×3 (`fpDist_edgeWeight_le`,
  `fpDist_white_exit`, `Q_black_edge_case2`) + Case3 ×1 (`Q_black_edge_case3`,
  relocated) + ManyTriangles ×1 (`fpDist_any_triangle_le` ⛔quantifier-order
  escalation). Repo-wide: 14 sorries (5 crux + 9 spine stubs).
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
  re-read pass 18, **p.48 localization re-read pass 24** (the (7.50) O(1) is a
  distance *from Δ* and is explicitly ε-independent — see the downgrade above).
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
