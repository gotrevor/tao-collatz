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

## Judge pass (2026-07-09 evening, Ren/Fable + PDF) — RATIFY queue verdicts ⚖️

Independent statement ratification against the paper (pp. 8–14, 33–37, 42–46 read this
pass). One statement bug found and fixed; every queue item now ratified, fixed, or spec'd.

1. **RATIFY-2 (`valVec_unique`, Lemma 2.1 p.14) — RATIFIED.** The divisibility-guarded iff
   is exactly "unique tuple in `(ℕ+1)ⁿ` making `Aff_a(N)` an odd natural": the paper's
   `Aff_a(N) ∈ 2ℕ+1` (a `ℤ[1/2]` membership) is precisely
   `2^{a[1,n]} ∣ 3ⁿN + Fnat ∧ quotient odd`. `n = 0` edge agrees (both sides trivially true).
2. **RATIFY-3 (`stabilization`, Prop 1.11 pp.8–9) — RATIFIED.** Windows `[x^α, x^{α²}]` /
   `[x^{α²}, x^{α³}]` are the paper's `[y, y^α]` at `y = x^α, x^{α²}` verbatim; the `⌊x⌋₊`
   threshold is equivalent to the paper's real-`x` threshold (orbit values are naturals);
   (1.19)/(1.20) shapes and the single shared constant `c` match.
3. **RATIFY-4 (`θq`) — RATIFIED**, one doc fix: mathlib `round` puts `sfrac` in
   `[-1/2, 1/2)`, not the paper's `(-1/2, 1/2]`; they differ only at half-integers, which
   phases with odd denominator `3ⁿ` never attain. Docstring corrected, no statement change.
4. **Prop 7.3 count (`renewal_white_encounters`) — RATIFIED independently** (agrees with
   harness check 7): `(j : Fin (n/2), pre b (j+1))` = paper `(j, b_{[1,j]})`; the `b j = 3`
   conjunct per p.35; `pascal` (p.34), `pascalNe3` (7.29), `geomQuarter` (7.30 coefficient
   `(1/4)(3/4)^{j-1}`), and `hold` (p.42 description) all match the paper exactly.
5. **RATIFY-5 (`black_structure` set-separation fix) — CONFIRMED** vs Lemma 7.4 p.36: the
   paper separates triangle POINT SETS in the Euclidean metric; disjointness follows from
   positive separation; `triangle` = (7.11) verbatim; strip (`⌊n/2⌋`) and confinement
   (real `n/2`) conjuncts both as in the paper.
6. **RATIFY-6/7 (Q cluster) — STATEMENT BUG FOUND & FIXED (off-by-one).**
   `Q`/`Qm`/`prop_7_8`/`Q_polynomial_decay` are paper-1-based (boundary `⌊n/2⌋ < j`, weight
   `⌊n/2⌋ − j` — correct vs (7.34)/(7.38)/(7.40)/(7.37)), but `whiteSet` fed the 0-based
   `white` (RATIFY-4) unshifted, so `Q`'s indicator read the phase one column RIGHT of
   (7.34). Fixes (commit this pass): `whiteSet := {p | 1 ≤ p.1 ∧ white n ξ (p.1-1) p.2}`
   (the coordinate adapter); `Q_white_contract` hypothesis is now `whiteSet` membership;
   `Qm`'s sup restricted to `1 ≤ j` (paper `(ℕ+1)×ℤ` — the old sup admitted the
   nonexistent column 0, which could break `prop_7_8` at `m = ⌊n/2⌋`); `Q_polynomial_decay`
   takes `1 ≤ j` ((7.37) is only asserted on `(ℕ+1)×ℤ`). `Q_rec`/`Q_boundary`/`Q_nonneg`/
   `Q_le_one`/`Qm_le_rpow` are generic in `W` — untouched, still proved.
7. **Queue 2 (`unifOddMod` n'=0) — DECIDED: junk-guard.** The def carried a FALSE `sorry`
   (normalization over an empty odd-residue set at `n' = 0`) — a latent campaign-killer.
   Now `PMF.pure 0` at `n' = 0`; the `n' ≥ 1` normalization `sorry` is TRUE and grindable
   (witness `(1 : ZMod (2^n')).val = 1` odd; sum = `card • card⁻¹`). Statements unchanged.
8. **Queue 5 (Case 1 proper) — SPEC for the box.** (7.43), at `j = ⌊n/2⌋ − m` (paper
   coords, p.45 (7.41)):
   `∀ A > 0, ∃ Cthr, ∀ n ξ, ¬3∣ξ → ∀ m, Cthr ≤ m → m ≤ n/2 → ∀ l, ((n/2 - m : ℕ), l) ∈ whiteSet n ξ →`
   `  Q (n/2) (whiteSet n ξ) epsBW (n/2 - m) l ≤ Real.exp (-(epsBW:ℝ)^3/2) * (m:ℝ)^(-A) * Qm (n/2) n ξ epsBW A (m-1)`
   (`Q_white_contract` stays as the warm-up lemma).
9. **Directive to next lap**: extend the harness with a (7.36)-bridge check against the
   FIXED `whiteSet` — small-`n` comparison of `E Q(Hold)` vs
   `E exp(-ε³ #{j : b_j = 3, (j, b_{[1,j]}) ∈ W})` (paper p.44 derivation; exact via
   truncation + tail bound, or high-precision Monte Carlo). This pins the Q ↔ count seam
   end-to-end and would have caught the off-by-one mechanically.

**Series α is judge-cleared.** Preconditions §3 remaining: audit-machinery transplant + CI
gate (item 2) and the PMF lemma bank ordering (item 4).

## Judge pass 2 (2026-07-10 afternoon, Ren/Fable + PDF pp.42-46)

Scope: the statement surface landed by box sessions 3-4 (laps 11-21).

1. **Lemma 7.7 / X6 — RATIFIED.** `fpDist_location_bound` matches the p.43 display
   verbatim: `fpDist s (j,l) ≤ C · e^{-c(l-s)}/√(1+s) · G_{1+s}(c(j - s/4))`, with
   `Gweight t x = exp(-x²/t) + exp(-|x|)` exactly the paper's `G` (restated inline in
   Lemma 7.7 itself). Lean is unconditional in `l` where the paper takes `l > s` —
   sound, since `fpDist_support_snd_gt` (proved) kills the LHS for `l ≤ s`. The
   `fpDist` budget recursion is exactly `v_{[1,k]}` at the first passage `l_{[1,k]} > s`
   ((7.44)); support facts proved. Its `∃ c > 0` form is the faithful reading of the
   paper's `≪` with absolute constants.
2. **Prop 7.8 cluster / X7 — RATIFIED** vs pp.45-46: (7.37)→`Q_polynomial_decay`
   (the `1 ≤ j` is the paper's own domain `(ℕ+1)×ℤ`), (7.38)→`Qm` (re-confirmed),
   (7.39)→`Qm_le_rpow`, (7.40)→`prop_7_8` (∃-threshold = "sufficiently large C_{A,ε}",
   ε fixed by D4), (7.41)-restricted-to-black→`Q_black_edge` (stated, the open X8/X10
   kernel; `1 ≤ n/2 - m` is the paper's `j ∈ ℕ+1`), (7.43)→`Q_white_case1` verbatim
   including the `e^{-ε³/2}` constant. The `prop_7_8` assembly (edge split white/black +
   interior via `le_Qm`) mirrors the paper's proof frame on p.45.
3. **Lemma 7.6 mean vector — arithmetic CONFIRMED** (p.42-43): `E Hold = (4,16)` via
   `E Pascal = 4`; consistent with `fpDist_location_bound`'s `j ≈ s/4` centering and
   the (7.29)/(7.30) checks already in the harness.
4. **`Qstop`/`Q_le_fpDist_expect` (Unroll.lean) — design SOUND, machine-proved**, so
   no statement-trap surface: `Qstop_eq` certifies the D6 unrolling is literally `Q`,
   and `Q_le_fpDist_expect` (the (7.46)-entry inequality) drops the accumulated
   damping factors (each ≤ 1) — valid for an upper bound; Case 2's gain must then come
   from the endpoint's whiteness ((7.50)/(7.51)), matching the paper's route.
5. **⚠️ Box label drift.** Box commits/handoffs use "X5" for the Prop 7.3 bridge seams
   (`bridge_vector`/`bridge_renewal`/`hold_tsum_step`, now proved in `Bridge.lean`) —
   those are **X4** content in the ledger/blueprint. Ledger X5 = **Lemma 7.6 basics**
   (joint exponential tail, aperiodicity, mean (4,16) as Lean decls) and is genuinely
   OPEN — nothing landed under that scope. Read box labels with suspicion; ratify by
   declaration.
6. **`renewal_white_encounters` — statement re-confirmed** after its move to
   `Bridge.lean` (only a harmless `1 ≤ n` guard added). Now proved modulo
   `Q_black_edge` only.

Blueprint statuses flipped accordingly: X6, X7 statement-`\leanok` (18 green / 7 orange:
S3 C8 X1 X5 X8 X9 X10). Proof-`\leanok` unchanged (X3 only) — everything downstream of
`Q_black_edge` inherits its `sorryAx`.

## Judge pass 3 (2026-07-12, Ren/Fable + PDF pp.14-15)

Scope: the S3 statement surface from box session 5 (laps 22-28).

1. **Lemma 2.2(i)(ii) instances — ALL RATIFIED** vs the pp.14-15 statement + p.15
   displayed Geom(2) instance. Scalar instances (`Prob/LocalBound.lean`):
   `geomHalf_*` (mean 2n), `geomQuarter_*` / `pascal_*` (mean 4n) — each pairs
   (i) point mass `≤ C/√(1+n)·G(c(L-nμ))` with (ii) the tail bound as an
   indicator-tsum (which IS `P(|S_n - nμ| ≥ λ)`). The d=2 Hold pair
   (`Sec7/Unroll.lean`): correct `(n+1)^{-d/2} = C/(1+n)` prefactor, mean `n(4,16)`
   (confirmed at Lemma 7.6, p.42-43), Euclidean norm fed to the scalar `G` — faithful
   since the paper's `G_n(x)` for `x ∈ ℝ^d` depends only on `|x|`.
2. **The `G_{1+n}`-for-`G_n` index is constants-equivalent** (`G_{1+n}/G_n ≤ e` on the
   Gaussian regime, both `≍ e^{-|x|}` beyond) and dodges the paper's `exp(-∞) = 0`
   convention at `n = 0`; the paper itself states Lemma 7.7 with `G_{1+s}`. Accepted.
3. **Domain ℕ (resp. ℕ×ℤ) for the paper's ℤ (resp. ℤ²)** — sound: the summands are
   supported there, missing lattice points carry zero mass on the LHS.
4. **D5 route machinery (proved, no statement risk)**: `iidSum` calculus,
   `negBinomial_apply` exact point mass, circle-method core (`Prob/CharFn.lean`
   finite Fourier inversion on `ZMod N × ZMod N`), `hold` nondegeneracy atoms,
   `charFn_hold_decay`. All machine-checked; they are proof plumbing for the six
   `sorry`d instance statements above.

Blueprint: S3 statement-`\leanok` (19 green / 6 orange: C8 X1 X5 X8 X9 X10). Risk
tint/lapsrisk unchanged — S3's PROOF remains risk kernel 1.

### Ops note (2026-07-12): battery + clamshell beats caffeinate
Box session 6 (`2d245fb5dac5`) sat ~40h in suspended animation because the MacBook
went to battery + lid-closed (caffeinate cannot assert through clamshell-on-battery;
nothing userland can). Unlike the 07-10 mid-stream API kill, this stall was a clean
PAUSE: the container and its 90k context survived, and the lap resumed by itself on
wake. Distinct failure modes: sleep mid-API-stream = dead turn needing relaunch;
sleep between requests = free pause. No tooling change warranted — the fix is
operational (leave the lid open / on AC for overnight runs).
