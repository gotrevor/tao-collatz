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

## Phase-A results

*(appended post-run)*
