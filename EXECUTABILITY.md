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

## Live judge state 📍 (update each pass)

**Verified complete** (dated judge-run `#print axioms`, all exactly
`[propext, Classical.choice, Quot.sound]`): **X3** (2026-07-10), **S3** (pass 5),
**X6** (pass 7), **X1** (pass 11), **X5** (pass 12 — Lemma 7.6, 15 decls),
**X2** (pass 12 — both halves; damping consumer closed with it).

**Statements pinned + ratified**: every ledger node except **C8** (no pinned Lean
statement yet — the last un-pinned node). Latest: X1 (pass 10), X5 (pass 12),
`fpDist_white_exit_deep` (pass 12, bound at X9).

**Open riders / queued fronts**:
- **X11 ε-rider** (pass 8): when ratifying X11 against pp.55–56 (UNREAD), verify the
  (7.66)–(7.67) consumption chooses `R` after ε, as ManyTriangles' docstring claims;
  otherwise X9's proof must additionally exhibit ε₀ ≥ 10⁻⁴. The exp(2ε) correction
  (pass 9) rides the same check — any absolute exponent constant must wash out there.
- **p₀ > 1/2 certification burden — now EMBODIED** (pass 12): the burden lives in
  the pinned `fpDist_white_exit_deep` (demands `1/2 < p₀`; ratified as a documented
  deviation from the paper's `≫ 1`). The box must certify it there (Monte Carlo
  ≈ 0.99, harness check 9); X8's Case-2 twin stays `∃p₀ > 0` and needs no retrofit.
- **Axiom-check queue**: cleared (pass 12). Prop 1.17's whole remaining trail =
  the Prop 7.8 chain: BlackEdge ×4 (`fpDist_edgeWeight_le`, `fpDist_white_exit`,
  `Q_black_edge_case2`, `Q_black_edge_case3`) + ManyTriangles ×3
  (`triangle_encounter_le` X10, `fpDist_white_exit_deep`, `many_triangles_white` X9).
- **Box docstring nits** (pass 12, box's to fix): `White.lean:11` + `Reduction.lean:12`
  still describe their (now proved) cruxes as carrying `sorry`.
- **Near-edge tripwire** (pass 12 addendum): the box may resolve the
  `m < Cthr` fresh-state gap by widening `fpDist_white_exit_deep`'s statement —
  any such edit REVOKES its (7.59) ratification until judge re-ratifies.
- **Unread paper fronts**: §5 first-passage (C8), §7.5 assembly pp.55–56 (X11).
  pp.41–43 (Lemma 7.6) read + ratified pass 12.
- **Trust-surface notes**: `fpDist` / `fpDistPlus` encode stopped-walk laws at the
  design level (strong Markov absorbed — D1, ratified passes 2 & 8);
  `fpDist_white_exit` (X8) and `fpDist_white_exit_deep` (X9 input) are the two
  load-bearing white-exit kernels — same geometry, different budget regimes.
- **Paper-gap ledger**: Lemma 7.9 p.51 conditioning display (pass 9, confirmed ~90%) —
  KB `formalization-literature-holes.md` entry #5. **Per Trevor (2026-07-12): NOT
  announcement material.** It stays documented in-repo (docstring + judge log +
  README-level docs) because reproducers need it; no public post leads with it, and an
  author note is Trevor's call only — "little benefit bragging about finding someone
  else's error, especially a trivially patchable one."

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
for competitor movement. Also before going public: the statement-faithfulness audit
(Math Inc bridge + Series β density wording) must be closed, and the repo needs the
pre-public PDF-expunge sweep (committed paper PDFs → history rewrite).

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
