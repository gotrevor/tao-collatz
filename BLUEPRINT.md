# Blueprint: Tao 2019 — "Almost all orbits of the Collatz map attain almost bounded values" 🎯

**Target**: full Lean 4 formalization of Theorem 1.3 of arXiv:1909.03562 (v5), with
**zero sorries and zero axioms beyond `[propext, Classical.choice, Quot.sound]`**
(`lean-axiom-gate --exact` clean). First formalization anywhere, in any prover
(checked 2026-07-08: no prior art on GitHub / arXiv / Zulip-visible projects).

**Source of truth for statements**: the paper PDF (`papers/tao-2019-almost-all-orbits.pdf`,
= `~/src/collatz-cryptid/data/refs/tao-2019-almost-all-orbits.pdf`, arXiv v5 2022-02-15).
Every node below cites its paper anchor. Statements are **copy-not-compose**: the Lean
statement is ratified against the paper equation verbatim, then frozen (g-i statement-trap
doctrine — 10 traps died at statement time there, 0 at grind time).

**Main theorem** (paper Thm 1.3): for any `f : ℕ → ℝ` with `f(N) → ∞`,
`Colmin(N) < f(N)` for almost all `N` in logarithmic density.

---

## 0. Global design decisions (read before touching any node)

**D1 — Probability = PMF on countable types. No measure theory.**
Every random variable in the paper is discrete: `Geom(2)`, `Geom(4)`, `Pascal`,
`Log(R)` (finite), `Unif` (finite), `Syrac(ℤ/3ⁿℤ)` (finite), `Hold` (countable).
We use `PMF` + `tsum` throughout. Expectation of a bounded `f : α → ℝ` (or `ℂ`):
`∑' a, (p a).toReal * f a`. Total variation `dTV p q := ∑' a, |(p a).toReal - (q a).toReal|`.
Rationale: zero measurability side conditions; every probabilistic lemma becomes
arithmetic of sums — maximally treadmill-friendly. mathlib's measure-based
Chernoff/Hoeffding is NOT used (our distributions have exact formulas; see D5).

**D2 — ℤ[1/2] is eliminated.** The paper's offset map `F_n : (ℕ+1)ⁿ → ℤ[1/2]` (eq. 1.5)
is replaced by its 2-power multiple, which is a natural number:
```
Fnat n a := ∑ m ∈ Finset.range n, 3^(n-1-m) * 2^(a[0]+⋯+a[m-1])   -- = 2^|a| · F_n(a) ∈ ℕ
```
Key identity (paper (1.7) × 2^|a|), **entirely in ℕ**:
```
2^|a| * syr^[n] N = 3^n * N + Fnat n a      where a = the n-Syracuse valuation of N
```
Mod-3^k statements use `(2 : ZMod (3^k))⁻¹` (2 is a unit mod 3^k). No localization ring.

**D3 — Asymptotic notation is reified as explicit existential constants.**
Paper `X ≪ Y` ⇒ `∃ C > 0, ∀ …, X ≤ C * Y`. Paper `≪_A` ⇒ `∀ A > 0, ∃ C > 0, …`.
"Sufficiently large x" ⇒ `∃ x₀, ∀ x ≥ x₀`. **No `IsBigO`/filters in load-bearing
statements** (uniformity in `n, ξ` is exactly what filter-O obscures, and Prop 1.17's
uniformity is load-bearing — the paper says so explicitly on p.12).

**D4 — §7's small constant ε is a fixed numeral.** The paper takes `0 < ε < 1/100`
"sufficiently small absolute". We fix `ε := 1/10^4` (candidate; sandbox-validate against
every usage site before ratifying — Lemma 7.2's Taylor step, Lemma 7.4's `(1/10)log(1/ε)`
separation, Case 2/3 room). If a site fails, shrink and re-validate; the choice appears
in finitely many inequalities, all checkable numerically first.

**D5 — Chernoff/local bounds (paper Lemma 2.2) via explicit formulas + tilting, not
contour integration.** The paper proves Lemma 2.2 by complexified MGF + Morera + contour
shift. We need it only for specific distributions:
  - d=1, `Geom(2)` sums: **exact formula** `P(|Geom(2)ⁿ| = L) = C(L-1, n-1)·2^{-L}`
    (compositions of L into n positive parts). Gaussian-regime bounds follow from
    binomial estimates (Stirling exists in mathlib). Upper tails: Markov on `e^{λS}`
    with explicit geometric-series MGF.
  - d=2, `Hold` sums (§7 only): real-variable **exponential tilting + circle method**:
    `P(S_k = v) = (2π)^{-2}·M(λ)^k·e^{-λ·v}·∫_{[-π,π]²} |φ_λ(t)|^k …` with φ, M explicit
    rational functions of `e^{λ+it}`. No contour shifting; interval integrals only.
  This cluster (node S3) is one of the three hard kernels. Fallback: it is classical
  local-CLT material, self-contained, and CAN be weakened at several call sites
  (documented per-node below) at the cost of constant bloat.

**D6 — §7.4's infinite renewal process is finitized by recursion.** The paper extends
`b_1, …, b_{⌊n/2⌋}` to an infinite iid sequence and defines `Q(j,l) = E ∏_{k∈ℕ} exp(-ε³1_W((j,l)+v_{[1,k]}))`
(7.34). We instead **define** `Q : ℕ × ℤ → ℝ` by the recursion the paper derives (7.35):
```
Q (j,l) = 1                                            for j > ⌊n/2⌋
Q (j,l) = exp(-ε³·1_W(j,l)) * E[Q((j,l) + Hold)]       for j ≤ ⌊n/2⌋
```
well-founded by downward recursion on `⌊n/2⌋ - j` (Hold's first coordinate is ≥ 1;
`E[·]` is a `tsum` against Hold's explicit PMF). All stopping-time manipulations in
§7.4 (7.44–7.67, Lemmas 7.9/7.10) become finite unrollings / strong inductions over
this recursion. **No infinite product measure, no Ionescu–Tulcea.** This is the single
most important de-risking decision; validated in-session (see `TaoCollatz/Sec7/Holding.lean`).

**D7 — Constant-dependency ledger.** §6–§7 thread constants `A → C_A → (ε) → C_{A,ε} → P → m ≥ C_{A,ε}`.
Every node statement names its constants explicitly; the chain is:
`A` (target exponent) → `C_A` (§6 event E, (6.2)) → `A'` (§6 large-exponent appeal to 1.17)
→ `ε` (fixed, D4) → `C_{A,ε}` (Prop 7.8 threshold) → `P = O_{A,ε}(1)` (Case 3) → `R = ⌊A²/ε⁴⌋`.
No constant may be "chosen later" in Lean; each is an explicit function of its parents.

**D8 — Numeric sanity harness.** `tools/check_blueprint.py` (sandbox) brute-force-verifies
finite instances of every delicate statement BEFORE it is ratified: the `Syrac(ℤ/9ℤ)`
distribution table (paper p.10: probabilities `0, 8/63, 16/63, 0, 11/63, 4/63, 0, 2/63, 22/63`),
the negative-binomial point formula, Lemma 7.4's triangle decomposition at concrete `(n, ξ, ε)`,
Fnat/Syrac orientation (the paper REVERSES variable order between (1.5) and (1.26) —
footnote 6, a classic trap).

---

## 1. Module map

```
TaoCollatz/
├── Statement.lean          -- TRUSTED BASE: Thm 1.3 + Thm 3.1, elementary defs only
├── Basic/
│   ├── Collatz.lean        -- col, colMin, syr, syrMin, ν₂, (1.1), (1.2)
│   ├── Valuation.lean      -- a⃗⁽ⁿ⁾(N) (1.8), Aff/Fnat algebra (1.3)(1.5)(1.7), Lem 2.1
│   └── LogDensity.lean     -- Log(R), logProb, HasLogDensity, AlmostAllPos/Odd, harmonic sums
├── Prob/
│   ├── Basic.lean          -- dTV, (1.10), expectations, PMF products / iid vectors
│   ├── Geometric.lean      -- Geom(2), Geom(4), Pascal; negative binomial exact formula
│   ├── Chernoff.lean       -- S3: G_n weights (2.2); Lemma 2.2 (i)(ii) for our cases
│   └── Renewal.lean        -- Hold (§7.3), Lemma 7.6, Lemma 7.7
├── Syracuse/
│   ├── SyracRV.lean        -- Syrac(ℤ/3ⁿℤ) (1.21)(1.26), projection (1.22), Lem 1.12
│   └── ValuationDist.lean  -- §4: Lemma 4.1, Prop 1.9
├── Fourier/
│   └── ZMod3.lean          -- e(θ), characters, Parseval on ZMod (3^n), Osc (1.24)
├── Sec3/Bootstrap.lean     -- Thm 3.1 ← Prop 1.11; Thm 1.6; Thm 1.3
├── Sec5/
│   ├── FirstPassage.lean   -- T_x, Pass_x (§1.3), proof of (1.19)
│   ├── ApproxFormula.lean  -- Prop 5.2 (events 𝒜, E', I_y bookkeeping)
│   └── Stabilization.lean  -- Lemma 5.3, (5.20)–(5.21), Prop 1.11 assembly
├── Sec6/MixingFromDecay.lean -- Lem 6.2, Cor 6.3, Prop 1.14 ← Prop 1.17
└── Sec7/
    ├── Setup.lean          -- χ, θ (7.7)(7.8), pairing b_j, f/g factorization (7.4)(7.5)
    ├── White.lean          -- white/black (7.9), Lemma 7.2, Prop 7.1 → Prop 7.3 reduction
    ├── Triangles.lean      -- triangle def (7.11), θ identities (7.12)–(7.15), Lemma 7.4
    ├── Holding.lean        -- D6 finitization: Q recursion, (7.34)–(7.36) bridge
    ├── Monotone.lean       -- Q_m (7.38), Prop 7.8 skeleton, Case 1 (7.42)–(7.43)
    ├── CaseTwo.lean        -- Case 2 (7.44)–(7.51)
    ├── CaseThree.lean      -- Case 3, Lemma 7.9, Lemma 7.10, (7.52)–(7.67)
    └── Decay.lean          -- Prop 7.3 → 7.1 → Prop 1.17
```

---

## 2. Node ledger

Legend: **Difficulty** 1–5 (5 = summit). **Laps** = estimated Opus-treadmill laps
(g-i lap conventions). **Conf** = confidence the node completes as stated without
statement surgery. Depends lists node ids. Paper anchors in parens.

**Campaign steering rule (Trevor, 2026-07-10): de-risk breadth-first.** The expedition
verdict is binary (full-discharge-or-abandon), so laps buy the most when they reduce the
odds of a late fatal wall — spend them turning **red nodes yellow** (statement pinned +
ratified, route validated, hardest sub-lemma stated or probed) before polishing yellow
or green nodes to completion. Priority order: red → yellow everywhere, then yellow →
light green, completion polish last. Two carve-outs: (a) **dependency order gates
assessability** — a red node whose risk can't be probed without upstream machinery
(X8 needed X3's triangles + X6's Lemma 7.7) waits for that machinery, not for its turn;
(b) **finish-when-downhill** — a node mid-flight whose completion is clearly ≤ a few
laps gets finished, because a completed axiom-clean proof is ground truth that re-rates
its neighbors (X3's exact fibre identity re-rated X8), and abandoning cheap completions
buys nothing. A completed node is the *only* estimate that can't be wrong.

**⚡ Active statement demands (judge → grind laps; check here before working the
named target).**

**🎯 UNBLOCK THE X9 KERNEL — two explicit constants (judge pass 24, 2026-07-13).**
The p.48 re-read cleared the second escalation: the route is right, the geometry in
`phaseInFamily_support_imp_localization_bad` is the paper's, and the *only* thing
between us and `fpDist_any_triangle_le` is that the localization box is built from a
throwaway constant. Two independent, ε-free tasks — neither needs a ruling, neither
touches any pinned statement:

1. **Sharpen `fpDist_linear_tail`** (FpLocation.lean:366). It currently bounds the
   `16j − 5l` MGF with a quadratic `1000·(λ₁²+λ₂²)` penalty, which near-cancels the
   −16/step drift (net exponent −39/400000) and forces the tilt to `θ = 1/20000`,
   hence the shipped threshold `B = 4·10⁷`. **The step law has an exact MGF**:
   `k ~ geomQuarter` is `¼(¾)^{k−1}` (mean 4) and `Δl = 3 + Σ^{k−1} v` with
   `v ~ pascalNe3` (mean 13/3) — so
   `E[e^{θZ}] = e^{−15θ}·¼e^{16θ} / (1 − ¾ e^{16θ} φ(θ))`, `φ(θ) = E[e^{−5θv}] ≤ 1`,
   convergent for `¾e^{16θ}φ(θ) < 1` (ceiling `θ_c ≈ 0.213`). At `θ* ≈ 0.11` the
   threshold for tail ≤ 1/16 is **`B ≈ 42`**. Any `B ≤ 250` is enough. Keep the
   lemma's existing shape (`e^{−θB} · M/(1−M)`) — only the MGF input changes.
2. **Re-prove `fpDist_height_tail` (ManyTriangles.lean:2522) OFF X6, with an explicit
   radius.** It currently sums X6's `fpDist_location_bound`, whose constants `(cL, CL)`
   are **existential** — so `Y` is not a numeral and `√(X²+Y²) < sep` can never be
   discharged, however good `B` is. **This is the real blocker, not `B`.** Do not make
   X6's constants explicit (that re-opens a completed node); take the elementary route
   instead, whose three ingredients are all in-repo:
   (i) `fpDist_le_renewal_conv` — the endpoint is a pre-passage point below the budget
   line plus **one** `hold` step;
   (ii) `hold`'s height increment is `Δl = 3 + Σ v` with `v ≥ 2`, so `Δl ≥ 3 > 0`: heights
   **strictly increase**, hence the walk visits each level **at most once** and the renewal
   mass at any level is `≤ 1` — no renewal theorem, no local limit law;
   (iii) `Δl` has an exact MGF (tilt ceiling `μ_c = 0.0640`).
   Chain: `P(height ≥ s+Y) ≤ Σ_{u≥0} P(Δl ≥ Y+u) ≤ E[e^{μΔl}]·e^{−μY}/(1−e^{−μ})`.
   At `μ* = 0.0575` this yields **`Y = 139`** for tail ≤ 1/16.

Then `X = ⌈(5Y + B)/16⌉ = 47` is a numeral and the box is `√(47²+139²) ≈ 147`, and
`fpDist_any_triangle_le` follows by feeding `exists_fpDist_localization_box` +
`√(X²+Y²) < sep` into the already-proved `fpDist_any_triangle_le_of_localization_box`.

⚠️ **The box does NOT fit at the ruled `epsBW = 10⁻⁹⁰`** (`sep = 9·ln10 ≈ 20.72`), so a
**numeral re-freeze is required** — recommended `10⁻¹⁰⁰⁰` (`sep ≈ 230`, ~1.6× margin).
**That is Trevor's ruling, not a worker's**: land both lemmas first (they are ε-free and
need no ruling), report the constants you actually proved, and the judge takes the real
box to Trevor. Do **not** change `epsBW` on your own initiative, do **not** re-open it as
a parameter, and do **not** introduce a `Real.exp`-valued ε (the rational power of ten is
doctrine). Numerics: `tools/tao_linear_tail.py`, `tools/tao_height_tail.py`; full analysis
`judge/pass-24.md`.

**🗂️ SPLIT `ManyTriangles.lean` (operator directive, 2026-07-13; do this FIRST
next lap, before proof work).** The file is 3,934 lines (2× the next-largest, ⅓ of
Sec7) and every edit-iteration re-elaborates all of it, including the
1.6M-heartbeat X10a decl. Split into four dependency-ordered files, **pure moves
only — zero statement/proof edits in the same lap, keep every decl name
verbatim** (the blueprint `\lean{}` bindings + judge axiom runs are name-based
and must be unaffected):
1. `Sec7/FpPlus.lean` — `fpDistPlus` def/basics + the (7.61) tails + their
   engines (`fpDist_height_tail`, `fpDist_col_dev`, `holdSum_col_tail`,
   `hasSum_nat_tail_exp`, `tsum_int_Gweight_le`, …).
2. `Sec7/Encounter.lean` (X10) — `bigTriangleSet`, `apex_gap`/`apex_separation`,
   `encounter_apex_proximity`, `encounter_separated_sum`,
   `triangle_encounter_le`. Imports FpPlus.
3. `Sec7/WhiteExit.lean` (X9 kernel) — `fpDist_col_le`, `gaussian_col_tail`,
   `outStripSet`/`phaseInFamily` glue, `fpDist_out_of_strip_le`,
   `fpDist_any_triangle_le`, `fpDist_white_exit_deep`. Imports FpPlus.
4. `Sec7/EncounterFold.lean` (X9 fold) — `EncState` … `many_triangles_white`.
   Imports WhiteExit.
Keep a thin `ManyTriangles.lean` that just imports all four (downstream imports
unbroken). Build green, update HANDOFF file references, then resume proof work.
Judge verifies at the boundary via sorry census + name-based axiom runs; a
split lap that also edits proofs forfeits the cheap verification.

**⚖️ ALTITUDE RULING (Trevor, 2026-07-12): Remedy A at `epsBW = 10⁻⁹⁰`.** The
pass-18 escalation is resolved. Execute in this order, one concern per lap:

1. **Split first** (the 🗂️ directive above — pure moves, lap of its own).
2. **Dedicated D4-change lap**: change the D4 numeral `epsBW` from `1/10^4` to
   `1/10^90` and make ONLY the mechanical numeral repairs needed to get the build
   green (gap-lemma arithmetic re-runs at the new numeral — the 13-row statement
   stays true a fortiori; `norm_num`/exact-ℚ throughout, the numeral is a rational
   power of ten ON PURPOSE — never introduce `Real.exp`-valued ε). NO route work in
   this lap; a mixed lap forfeits the judge's cheap sweep verification. Expect
   `sep_const_sq_le_one` to fail — that is the point; it dies (X3's separation
   clause re-opens as real content, park it as the next item, sorry is acceptable
   ONLY in that one clause during this lap, documented in the handoff).
3. **Real Lemma-7.4 separation**: formalize the paper's separation argument
   (pp.46–48) to discharge X3's re-opened clause at sep = 9·ln 10 ≈ 20.7. The run
   machinery (run tops, wrap-integer dichotomy, phase-halving) in Triangles.lean
   is the toolbox. Keep `white_gap_above_run_top` — it holds a fortiori
   (≈ 299 rows) and stays useful.
4. **White-exit kernel as-routed per p.48** (`fpDist_any_triangle_le` →
   `fpDist_white_exit_deep`): the paper is the map again — "at a distance O(1)
   from Δ, hence … white by Lemma 7.4" now has real separation behind it.

Judge protocol on the D4 change landing: the armed ε-sweep re-ratification list
(EXECUTABILITY live state) runs at the first post-change boundary — including the
p₀ `51/100` numerics direction check and confirming every consumer of X2's
(now astronomically weaker) `exp(−ε³)` gain stays existential-C. X3 and X2 lose
their verified status until re-run post-change. The `fpDist_white_exit_deep`
suspension and `fpDist_any_triangle_le` withdrawal lift ONLY via post-sweep
re-ratification; the p₀-softening tripwire re-arms on the re-pin (pass 18).

*(History: the pass-18 informational position, kept for the record — escalation
CONCURRED on all three steps: vacuity machine-verified at `Triangles.lean:1333`;
p.48 consumption confirmed; adversarial families interface-legal. Ruling
tradeoffs: hybrid B+A-small was rejected for route-risk — it makes the kernel a
novel argument ratified without a PDF, with a thin sep 5–10 margin against an
unextracted O(1) and a double-sweep tail; Remedy A's overshoot is nearly free
while any undershoot pays the full sweep twice.)*

- ~~`fpDist_white_exit_deep`: pin the mass at `51/100 ≤ p₀`~~ **RETIRED
  (satisfied lap 57 `3c95898`, re-ratified judge pass 17)** — the ε₀-floor is
  now provable by arithmetic from the pin. History: judge/pass-16.md (the
  demand + why anonymous existentials made it statement-level), pass-17.md
  (the discharge).

**Color vocabulary — ladder vs graph (clarified 2026-07-12, after an operator/box
mismatch).** The RED/YELLOW/GREEN above is the *de-risk ladder*: RED = no pinned Lean
statement (pure paper-risk; renders as an **orange border** on the dep graph's
`\notready` nodes), YELLOW = statement pinned + ratified + route validated, GREEN =
proved. This is a different axis from the dep graph's **risk tint** on the `\lapsrisk`
badges (risk word `high` renders reddish) — a node can be ladder-YELLOW (pinned) yet
badge-red (high proof risk), e.g. X8/X10 after their pins. When reporting, name the
axis: "un-pinned" vs "high-risk", not bare "red".

### Support layer

| id | node | paper | diff | laps | conf | depends |
|----|------|-------|------|------|------|---------|
| S1 | PMF basics: `dTV`, (1.10), expectation calculus, finite products / iid vectors | §1.4, (1.9)(1.10) | 2 | 8–15 | 90% | — |
| S2 | Geom/Pascal PMFs, exact negative-binomial point mass `C(L-1,n-1)2^{-L}`, MGFs, 1-D Chernoff tails | Def 1.7, §2 | 2 | 6–12 | 90% | S1 |
| S3 | ✅ **COMPLETE (laps 22–45; judge pass 5, 2026-07-12)** — Local 2-D Gaussian-type bound, Lemma 2.2(i)(ii) for `Geom(2)`, `Geom(4)`, `Pascal`, `Hold` + `G_n` weights (2.2). All 8 obligations + 2 generic engines judge-verified `[propext, Classical.choice, Quot.sound]`. Risk kernel 1 CLOSED | Lem 2.2 | 4 | done | — | S2 |
| S4 | Fourier on `ZMod (3^n)`: `e(θ)`, `ZMod.dft` Parseval, `Osc` (1.24); Remark 1.18 triangle inequality | §6, (1.24) | 2 | 4–8 | 85% | — |

### Core spine (§1–§5)

| id | node | paper | diff | laps | conf | depends |
|----|------|-------|------|------|------|---------|
| C1 | `col`, `colMin`, `syr`, `syrMin`, `Colmin = Syrmin(oddPart)` (1.2); Conj statements for reference | §1.1–1.2 | 1 | 3–6 | 95% | — |
| C2 | Valuation vector (1.8); **Fnat integerification** (D2); iteration identity (1.7); Lemma 2.1 (uniqueness) | (1.3)–(1.8), Lem 2.1 | 2 | 5–10 | 90% | C1 |
| C3 | Log density defs; `AlmostAllPos`/`AlmostAllOdd`; harmonic-sum integral tests (5.25)(5.26); Thm 1.6 ⟹ Thm 1.3 splitting | Def 1.2, §1.2, (5.25) | 2 | 6–12 | 85% | C1 |
| C4 | `Syrac(ℤ/3ⁿℤ)` via (1.26) reversed form; projection compat (1.22); recursion Lemma 1.12 (Euler's theorem + geometric series) | (1.21)(1.22)(1.26), Lem 1.12 | 2 | 5–10 | 85% | C2, S1 |
| C5 | §4: tail bound Lemma 4.1; **Prop 1.9** (valuation ≈ Geom(2)ⁿ, error `2^{-c₁n}`) | §4, Prop 1.9 | 3 | 10–18 | 80% | C2, S2 |
| C6 | §3: **Thm 3.1** (quantitative main thm) ← Prop 1.11 by scale iteration; Thm 1.6; **Thm 1.3** | §3 | 3 | 8–15 | 85% | C3, C7–C9 |
| C7 | (1.19): `P(T_x(N_y) = ∞) ≪ x^{-c}` | §5 pp.20–21 | 2 | 5–10 | 85% | C5, S2 |
| C8 | **Prop 5.2** approximate formula (5.8): events `𝒜^{(n')}` (5.11), `E'` (5.10), `I_y` (5.9), the B_{n,y} equivalence chain | §5 pp.22–25 | 4 | 15–30 | 75% | C2, C5, C7 |
| C9 | Lemma 5.3 (`c_n(X) ≪ 1`), (5.18)–(5.21), **Prop 1.11** assembly (applies Prop 1.14 at scale m₀) | §5 pp.25–28 | 4 | 10–20 | 75% | C8, C10 |
| C10 | §6: Lemma 6.2 (F_n injective), **Cor 6.3** (3-adic separation), event E (6.2), stopping time k, Plancherel step, **Prop 1.14 ← Prop 1.17** | §6 | 3 | 15–30 | 75% | C4, S2, S4, X-chain |

### Crux (§7) — Prop 1.17

| id | node | paper | diff | laps | conf | depends |
|----|------|-------|------|------|------|---------|
| X1 | ✅ **COMPLETE (lap 53; judge pass 11, 2026-07-12)** — §7.1 setup + (7.4)/(7.5) factorization; `cexpect_pairing` PROVED (via `cexpect_pairing_gen` pair-peel, statement drift-free) and judge-verified `[propext, Classical.choice, Quot.sound]`; Prop 1.17 trail now only white_cos_bound (X2) + Prop 7.8 chain | §7.1 pp.33–35 | 3 | done | — | C4, S2 |
| X2 | ✅ **COMPLETE (laps 53–54; judge pass 12, 2026-07-12)** — θ(j,l) + **Lemma 7.2** both halves: `fCond_three_norm` (exact value) + `white_cos_bound` (Taylor half via mathlib `cos_le_one_sub_mul_cos_sq`); judge-verified clean; `prod_fCond_le_damping` closed with it | pp.34–35 | 2 | done | — | X1 |
| X3 | ✅ **COMPLETE (judge-verified 2026-07-12)** — Lemma 7.4 black set = disjoint separated triangles: θ identities (7.12)–(7.15), weakly-black claims (i)–(iii), l*/j* construction, Claim (*) Cases 1–3 | §7.2 pp.36–41 | 4 | done | — | X2 |
| X4 | §7.3 + D6: `Hold` def, `Q` recursion, bridge (7.28)/(7.34)–(7.36): `EQ(Hold) ≪_A n^{-A}` ⟺ Prop 7.3 | §7.3–7.4 pp.41–44 | 3 | 8–15 | 80% | S2, X2 |
| X5 | ✅ **COMPLETE (lap 54; judge pass 12, 2026-07-12)** — **Lemma 7.6** Hold basics ratified vs p.42: mean (4,16) (`hold_mean_fst/snd`, 𝔼Pascal′=13/3 per (7.29)), aperiodicity (`hold_aperiodic`, coset formulation), tail clause = S3 engine; 15 HoldBasics decls judge-verified clean | p.42 | 2 | done | — | X4 |
| X6 | ✅ **COMPLETE (laps 46–50; judge pass 7, 2026-07-12)** — Lemma 7.7 first-passage location distribution; `fpDist_location_bound` + `renewalMass_bound` judge-verified `[propext, Classical.choice, Quot.sound]`; FpLocation.lean sorry-free | p.43 | 4 | done | — | S3, X5 |
| X7 | `Q_m` (7.38); Prop 7.8 skeleton; **Case 1** (white point) (7.42)–(7.43) | §7.4 pp.45–46 | 2 | 4–8 | 85% | X4 |
| X8 | **Case 2** (shallow in triangle): (7.44)–(7.51) — statements pinned + ratified (judge pass 6); endpoint step + budget PROVED; open: weight degradation + white-exit (both consume X6) | pp.46–48 | 5 | 8–16 | 75% | X3, X6, X7 |
| X9 | **Lemma 7.9** many-triangles ⟹ many-white-points — pinned at **exp(2ε)**: the paper's exp(ε) rests on a judge-CONFIRMED proof gap (p.51 display banks white damping through k₁, true sum stops at t₁ on stopped chains — see judge/pass-09.md + KB literature-holes #5); encounter-fold encoding ratified (pass 8), re-ratified at 2ε (pass 9); head-peel + block bridge `encExpect_block_le` + coupling PROVED axiom-clean; **Y/Z induction CLOSED lap 55 (judge pass 16)** — `many_triangles_white` proved DEPTH-GATED (second deviation: encounters count only at depth ≥ g; near-edge truth challenge = literature hole #6, judge-concurred), sorryAx trail machine-checked = exactly {`fpDist_white_exit_deep`}; consumer geometry judge-verified vs pp.48–49+54–56 (pass 15: R after ε, −O(A) slack, (7.54) 0.9m split); ⚠️ kernel re-pin must certify `51/100 ≤ p₀` (ε₀-floor, pass 16); **pass 24: second escalation DOWNGRADED — route sound (p.48's O(1) is a distance *from* Δ and is ε-free; the committed geometry already renders it), blocker = two throwaway constants — `B` (exact step-law MGF ⟹ 42, not 4·10⁷) and `Y` (existential via X6 ⟹ explicit 139 via strictly-increasing heights); box ≈ 147 vs sep ≈ 20.7 ⟹ one cheap numeral re-freeze `10⁻⁹⁰ → 10⁻¹⁰⁰⁰`, Trevor's call. D4-as-a-parameter off the table** | pp.50–51 | 4 | 6–14 | 75% | X4, X8 |
| X10 | **Lemma 7.10** large triangles rarely encountered ((7.60)–(7.65), separated-Σ counting) — statement pinned + ratified (judge pass 8, 2026-07-12): `triangle_encounter_le` over `fpDistPlus = fpDist ⋆ iidSum hold p` (D1 encoding, strong-Markov absorbed); (7.65) disjointness step (not_mem_two) PROVED; open: escape event E′ + separated-Σ summation | pp.51–54 | 5 | 10–20 | 70% | X3, X6, S3 |
| X11 | **Case 3** assembly (E_*, F_*, R = ⌊A²/ε⁴⌋, deterministic claim (7.67)); **Prop 7.8 → 7.3 → 7.1 → Prop 1.17** | pp.48–49, 54–56 | 4 | 10–20 | 70% | X9, X10 |

**Totals**: ~17k–28k lines, **~250–450 laps**. With g-i-calibrated lap throughput this is a
**multi-month campaign** (larger than the g-i rebuild; comparable to the monument estimate).

### Critical path & risk concentration

```
S3 → X6 → {X8, X10} → X11 → C10 → C9 → C6 → Statement
```
Three hard kernels hold ~all the completion risk:
1. **S3** (local 2-D bound): classical analysis, elementary route designed (D5), but long. 70%.
2. **X3** (Lemma 7.4 triangles): finite, elementary, delicate case analysis; Fable-validated
   statement layer in-session; exact-arithmetic decomposition validated (harness check 8,
   2026-07-10, incl. giant triangles). 75%.
3. **X8/X10** (renewal vs. triangles): the paper's pinnacle. The D6 finitization makes these
   inductions over an explicit recursion rather than stopping-time measure theory. 65–70%
   (2026-07-10: white-exit ≈0.99 MC, Σ-separation + ε-sites numerically verified, checks 9–11).

Everything OUTSIDE these kernels is standard treadmill fare (counting, harmonic sums,
ZMod arithmetic, PMF calculus) at 75–95% confidence.

---

## 3. Faithfulness anchors

- `Statement.lean` is the only trusted surface: `col`, `colMin`, log density from first
  principles (Finset sums, `Tendsto`), Thm 1.3 + Thm 3.1. Everything else may refactor.
- `#print axioms tao_collatz` gate = exactly `[propext, Classical.choice, Quot.sound]`
  (`lean-axiom-gate --exact`, CI-wired).
- D8 numeric harness runs against defs, not prose.
- The paper's footnote-6 variable-order reversal between (1.5) and (1.26) is encoded as
  an explicit lemma (`syracZ_eq_rev_fnat`, node C4) rather than a silent convention.

## 4. What is deliberately NOT formalized

- Remark 1.4 (equivalence with `∃ C_δ` form), Remark 5.1 (Korec recovery, periodic-orbit
  density) — bonus nodes, cheap after C6/C7, not on the critical path.
- Remarks 1.10 (2-adic Haar), 1.13 (3-adic limit), 1.15/1.16, 7.5 — expository.
- Natural-density upgrade (Remark 1.16) — out of scope.
