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

**Milestone insurance**: even a stall after Series β leaves a publishable artifact
(first Lean proof of the Terras/Allouche/Korec-strength "a.a. orbits dip below N^θ" — itself
unformalized anywhere, worth a lean-gallery entry).

## 5. Session de-risk evidence (2026-07-08)

- Harness (6/6 checks): Fnat identity, (1.2), Syrac ℤ/9 table in BOTH (1.21)/(1.26) forms
  (footnote-6 reversal trap encoded), negative binomial, Lemma 1.12 recursion, Lemma 7.4 scan.
- Proved in-session (Phase-A agent): see §"Phase-A results" appended below after the run.
- Full paper read + 26-node DAG extracted; no prior formalization found (greenfield first).

## Phase-A results (2026-07-09, Opus skeleton run — commits `3d65587`/`33e7438` + Monotone ratification fix)

**18 files, ~1200 lines, `lake build` green. 23 sorry tokens = exactly the spec'd statement
chain. Zero axioms / native_decide / heartbeat bumps. All proved items `#print axioms`-clean.**

Every mandatory "prove now" item PROVED — including both design-bet validators:
- **D2 validated**: `syr_iterate_key` (paper (1.7)×2^|a|, the ℕ-only dynamical identity) proved.
- **D6 validated**: the `Q` well-founded recursion compiles and `Q_boundary`, `Q_rec` (= paper
  (7.35)), `Q_nonneg`, `Q_le_one` are proved — §7.4's stopping-time machinery is now
  demonstrably expressible as recursion-unrolling, no infinite product measure.
- Also proved: all four PMF normalizations (geomHalf/geomQuarter/pascal/pascalNe3),
  `θq_succ_j`/`θq_pred_l` (paper (7.13)/(7.14) via a reusable ZMod→ℚ-phase bridge),
  dTV basics, Collatz/oddPart basics.

**Judge-pass queue before treadmill fire** (all greppable as `RATIFY`; see also the skeleton
agent's report in git history):
1. ✅ RESOLVED in-session: `Qm`/`prop_7_8` — agent's guessed shape was inverted (depth from
   strip start, no weight); rewritten to paper (7.38)/(7.39)/Prop 7.8/(7.37) forms.
2. `unifOddMod` degenerate at `n' = 0` (normalization genuinely false there) — thread `1 ≤ n'`
   through `valuation_dist` or junk-guard the def.
3. `renewal_white_encounters` count coordinate `(j, pre b (j+1))` — footnote-6-style trap
   candidate; add a D8 harness check before the §7 series.
4. `stabilization` window endpoints (`x^α, x^{α²}, x^{α³}`) + real-vs-floor threshold semantics.
5. `Q_white_contract` is a warm-up form of Case 1, not (7.43) itself — fine as a lemma, but
   Case 1 proper needs the `m^{-A}·Q_{m-1}` form against the corrected `Qm`.
6. Lemma 7.4 conjunct spelling (RATIFY-5, separation stated squared) and Lemma 2.1 shape
   (RATIFY-2) — read against paper pp.36–41 / p.14.

## Kernel de-risk lap (2026-07-10, first box lap)

Harness extended with §7 kernel checks 7–11 (`tools/check_blueprint.py`), all passing:

1. **Check 7 — Prop 7.3 coordinate convention RATIFIED** (queue item 3 retired). Validated
   end-to-end: (a) the p.33 pairing identity (exact ℚ); (b) (7.7)
   `χ(3^{2j-2}2^{-l+1}) = e^{-2πiθ(j,l)}`; (c) `|f(3^{2j-2}2^{-b_{[1,j]}}, 3)| = |cos(πθ(j, b_{[1,j]}))|`
   — the white point tested at index `j` is exactly `(j, b_{[1,j]})` = Lean
   `(j_lean, pre b (j_lean+1))`, so `renewal_white_encounters`' coordinates are correct as
   stated; (d) `|S_χ(n)| ≤ E exp(-ε³·#white)` verified by direct summation (n=4, four ξ).
   No footnote-6-style trap present.
2. **Check 8 — Lemma 7.4 validated far beyond the old qualitative scan**: the paper's
   l*/j* construction implemented in EXACT rational arithmetic; partition-into-triangles,
   the (7.18) equality case `|θ(j,l)| = 9^{Δj}2^{Δl}|θ*|` (when < 1/2), pairwise
   point-SET separation ≥ (1/10)log(1/ε), and strip confinement all hold at
   (n,ξ,ε) = (30,7,9/1000) [291 triangles], (26,101,1/101) [286], (30,1,1e-4) [5, sizes
   to 23.7]. Note the ξ=7/n=30 instance has a **giant triangle** (s* ≈ 26 ≈ n·log3·…)
   from the tiny corner phase θ(1,1)=7/3³⁰ — sizes are NOT bounded by log(1/ε); any Lean
   lemma bounding s_Δ by O(log(1/ε)) would be FALSE. (7.52) `s ≤ (log9/log2)·m` is the
   correct shape.
3. **STATEMENT BUG FOUND & FIXED (RATIFY-5 resolved)**: `black_structure` separated only
   triangle *corners*; the paper separates the triangle *point sets* (and Case 2's
   white-ring + Lemma 7.10's Σ-counting consume set-separation). Fixed in
   `Sec7/Triangles.lean`; also parenthesized the union equality (the un-parenthesized
   `= ⋃ t ∈ T, S t ∧ P` form risks the `∧` parsing into the `⋃` body).
4. **Check 9 — Case 2 white-exit (7.50)/(7.51)**: Monte Carlo over the real triangle
   inventory (shallow starts, iid Hold walk to first passage): P(exit ∈ W) ≈ 0.987.
   The paper's "≫ 1" is comfortably an absolute constant; the Lemma 7.9 ε-site needs
   only c₀ ≥ (1-e^{-ε})/(1-1/e) ≈ 1.6e-4.
5. **Check 10 — Lemma 7.10 deterministic core**: row j-intervals of distinct triangles
   are disjoint at every level (the "no common integer point" mechanism, p.54), and
   aligned big-triangle pairs (the (7.65) configuration) obey the Σ j-separation
   `gap ≥ (log2/(2log9))s' - O(alignment)` on the real inventory.
6. **Check 11 — D4 ratified**: ε = 1/10⁴ survives every §7 usage site as concrete
   numeric inequalities: Lemma 7.2 Taylor (`cos(πθ) ≤ exp(-ε³)` for |θ|>ε), Claim (*)
   Cases 1–3 exponents (`ε^{1-log18/10} ∈ (ε, 1/2)`, `ε^{1-log2/10}, ε^{1-log9/10},
   ε^{1-log18/10} ≤ 1/100`), weakly-black constants (i)–(iii), the (7.16) strip constant,
   (7.47)'s `exp(-ε³/2) ≤ 1-ε³/4`, and the slope room `4 > log9/log2`.

**Confidence moves**: X3 70→75%, X8 65→70%, X10 60→65% (ledger + content.tex updated).
The residual X8/X10 risk is now purely proof-engineering (making Lemma 7.7/2.2-type
Gaussian bounds and the stopping-time unrollings go through in Lean), not
statement-fidelity or hidden-falsity risk.

**Verdict update**: Phase-A outcome *raises* confidence at the margins (65% stands, with the
D6 risk now retired): the two structural bets that could have invalidated the blueprint are
kernel-checked, the statement chain compiles, and the remaining risk is exactly where §1
predicted (S3 analysis kernel, X3/X8/X10 case analyses) plus statement-fidelity items now
enumerated above rather than latent.
