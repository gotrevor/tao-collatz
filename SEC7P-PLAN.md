# SEC7P-PLAN — Tao §7 at `Pascal(p)`, uniform on `[1/5, 3/5]` 🌀

*Campaign spec for `DIRECTION.md` (operator, 2026-10-25).  The math in §1 is a paper-level
transfer read off Tao 2019 §7 (full text: `tmp/ren-tao/tao.txt`, gitignored, a pdftotext of the arXiv v5 PDF — §7 ≈ lines 1700–2800; never commit it) and
the moonshot research note §13; it has not been checked line by line.  §4 is the lap-owned
node table.*

## 0. Why

`gotrevor/collatz-moonshot` reduces `BiasDecays` (the 3-adic side of its conjugacy route)
to slice character decay, and slice character decay to the node `PascalDampingDecay`: Tao's
(7.5) damping bound with the gap law tilted from `Geom(1/2)` to `Geom(p)`, uniformly on a
window.  The tilt is forced: a slice of `a` ones among `j` positions looks like iid `Geom(p)`
gaps at `p = a/j`, and the relevant `a/j` range covers `[1/5, 3/5]`.  `Sec7P/Statement.lean`
copies that node verbatim, so this repo's discharge is the moonshot node's proof.

Measured (moonshot `experiments/conjugacy/pascal_damping.py`, exact DP checked against brute
force): `sup_ξ pascalDamping` at `n = 4, 8, 12, 14` is `0.655, 0.546, 0.478, 0.452` at
`p = 0.6`, `0.310 … 0.071` at `p = 0.35`; the per-2-step ratio is steady for `p ≤ 0.65`
(`0.945` at `p = 0.6`) and drifts toward `1` at `p = 0.7, 0.8`.  So the window's top end
`3/5` is close to where the mechanism weakens — expect the margin there to be thin.

## 1. The transfer, step by step (claims to check)

Write `q := P(b = 3) = 2p²(1-p)`.  On the window, `q ∈ [0.064, 0.288]` and the slope
`2/p ∈ [10/3, 10]` (Tao: `q = 1/4`, slope `4`).

1. **Deterministic half — p-free.**  `θ(j, l)` (7.8), black/white (7.9), Lemma 7.4's
   triangles (`Triangles.lean`), `White.lean`.  Import unchanged.
2. **Lemma 7.2 — p-free.**  `|f(x, 3)| = |cos πθ|` (`fCond_three_norm`) and
   `prod_fCond_le_damping`: given `b_j`, the pair split is uniform for every `p`.
3. **Pairing (7.5) at `p`.**  Two iid `Geom(p)` gaps, conditioned on their sum `b`, are
   uniform on the `b - 1` splits; the sum has law `pascalWeight p`.  Tao's
   `cexpect_pairing_gen` with `geomHalf ↦ geomP p`, `pascal ↦ pascalP p`.  (Only needed if
   the bridge goes through the raw-valuation form; the target is already the paired form,
   so step 4 of the directive may skip this entirely — check first.)
4. **Holding time (7.20)–(7.22).**  `Hold = (1, 3) + Σ_{i < K-1} (1, b'_i)`, `K ~ Geom(q)`,
   `b' ~ pascalNe3P p` (`pascalP p` conditioned `≠ 3`).  `E Hold = (1/q)·(1, 2/p)` (Tao
   `(4, 16)`).  Support contains `(1, 3)` and `(2, 3 + b)` for `b ≥ 2, b ≠ 3` — Tao's
   aperiodicity proof (`hold_aperiodic`) needs only these atoms, so it transfers verbatim
   with p-dependent positive masses.  Exponential tail: `K` geometric, `b'` has a
   `(1-p)^b`-tail; uniform on the window.
5. **Local limit / Chernoff (`HoldLocal`, `Prob/Mgf`, `Prob/LocalInstances`).**  Tao's atom
   masses (`1/400`), `|λ| ≤ 1/50`, the Chernoff `4λ₁ + 16λ₂ + 1000|λ|²` are `p = 1/2`
   numerals.  Replace by window-uniform versions: atom masses are continuous positive
   functions of `p` on a compact window (take their min); the mgf expansion constant is
   uniform for `|λ| ≤ λ₀` with `λ₀` chosen from the window's worst tail.
6. **First-passage location (Lemma 7.7, `FpLocation`).**  Mean drift `(1, 2/p)`, so first
   passage to a line at height `s` lands at `j ≈ s·p/2` (Tao `s/4`).  The localization box
   (Tao `51 × 150`) scales with the drift; if it grows past Lemma 7.4's separation
   `(1/10)·log(1/ε)`, shrink `ε` (DIRECTION ruling: `blackP`/`whiteP` at a new `ε`).
7. **Slope-sensitive steps — the one real condition.**  Every place Tao uses the drift's
   slope against `log 9 / log 2` reduces to **`p·log₂ 3 < 1`** (`≤ 0.951` at `p = 3/5`):
   - Case 2, after (7.50): "`¼ log 9 < log 2`" ↦ `(p/2) log 9 < log 2`.
   - Case 3, after (7.52): "`0.8 > ¼ log 9 / log 2`" ↦ a threshold `t₁` with
     `p log₂ 3 < t₁ < 1`; Tao's `0.8, 0.9` ↦ `t₁ < t₂` strictly in `(0.951, 1)` uniform on
     the window, e.g. `t₁ = 0.96`, `t₂ = 0.98`.
   - The line after (7.64): "`¼ log 9 < log 2`" ↦ same as Case 2.
   Grep `Case3.lean`, `ManyTriangles.lean`, `BlackEdge*.lean` for `0.8`, `0.9`, `4/5`,
   `9/10`, `log 9`, `/ 4` to find them all.  **The margin `1 - 0.951` is thin**; any
   step that secretly needs more than `p log₂ 3 < 1` is the likeliest failure — record it.
8. **Renewal + Q recursion (`Holding`, `Monotone`, `Unroll`, `Bridge`)** — `Q`'s recursion
   (`Q_rec`) is over `hold`; generalize to `holdP p`.  `Q_polynomial_decay` and
   `hold_weight_expect` at `p`, then `renewal_white_encounters` at `p`.

## 2. Window-uniformity discipline

`∃ C` comes before `∀ p`.  Every lemma that feeds the target takes `(hp : p ∈ Set.Icc (1/5)
(3/5))` (or a sub-window it states) and returns constants independent of `p`.  Pattern: prove
the `p`-pointwise bound with explicit dependence through a few monotone quantities (`q`,
`1-p`, `p log₂ 3`), then bound those on the window once, in one lemma each:
`q_mem_window : 0.064 ≤ q p ∧ q p ≤ 0.288`, `slope_margin : p * Real.logb 2 3 ≤ 0.952`, …

## 3. Module order (copy-and-generalize; sizes = p = ½ originals, lines)

Following the existing import DAG.  `≈ 20k` p-dependent lines in total; expect
generalization to share most proof text.

| # | Sec7P module | from | lines | p enters via |
|---|---|---|---|---|
| 0 | `Bridge` (convention) | — | new | calibration gate |
| 1 | `Prob` | `Prob/Geometric` | 380 | `geomP`, `pascalP`, `pascalNe3P` |
| 2 | `Holding` | `Sec7/Holding` | 294 | `holdP` = `geomQ.bind … pascalNe3P` |
| 3 | `HoldBasics` | `Sec7/HoldBasics` | 446 | means `(1/q)(1, 2/p)`, aperiodicity |
| 4 | `Monotone`, `Unroll` | `Sec7/…` | 706, 625 | `Q` over `holdP` |
| 5 | `Mgf`, `LocalInstances`, `HoldLocal` | `Prob/…`, `Sec7/HoldLocal` | 1077, 665, 516 | atom masses, Chernoff |
| 6 | `FpLocation` | `Sec7/FpLocation` | 3082 | drift, localization box |
| 7 | `BlackEdge`, `ManyTriangles`, `BlackEdgeQ` | `Sec7/…` | 1604, 6266, 524 | slope steps |
| 8 | `Case3` | `Sec7/Case3` | 3542 | `t₁, t₂` thresholds |
| 9 | `Prop73` | `Sec7/Bridge` | 717 | `renewal_white_encounters` at `p` |
| 10 | assembly in `Statement.lean` | `Sec7/Reduction` | — | discharge LAST |

Modules that never mention the gap law (`Prob/Basic`, `CharFn`, `CharFn1`, `LocalBound`,
`Tilt`, `Setup`, `Triangles`, `White`) are imported, not copied — confirm per module.

## 4. Node table (lap-owned: add a row when a load-bearing `sorry` is coined)

| node | Lean name | file | state |
|---|---|---|---|
| SEC7P-HALF | `pascalDamping_half_decay` | `Sec7P/Statement.lean` | proof landed; trust-base axioms evidence, judge to verify |
| SEC7P | `pascal_damping_decay` | `Sec7P/Statement.lean` | proof landed 2026-10-26 (`eb2e5e9`); trust-base axioms evidence, judge to verify |
| SEC7P-C2 | `QP_black_edge_case2` | `Sec7P/BlackEdgeQ.lean` | proved (Case 2 at `whiteSetP`/`epsP`) |
| SEC7P-X9 | `many_triangles_whiteP` | `Sec7P/ManyTriangles.lean` | proved (tilted Lemma 7.9) |
| SEC7P-X10 | `triangle_encounter_leP` | `Sec7P/ManyTriangles.lean` | proved (tilted Lemma 7.10) |
| SEC7P-C3 | `QP_black_edge_case3` | `Sec7P/Case3.lean` | proved (Case 3 at `t₂ = 49/50`, base-50 targets) |
| SEC7P-78 | `prop_7_8P` | `Sec7P/Prop73.lean` | proved (Prop 7.8 at `whiteSetP`/`epsP`/`QPmFor`) |
| SEC7P-737 | `QP_polynomial_decayP` | `Sec7P/Prop73.lean` | proved ((7.37) at `Pascal(p)`) |
| SEC7P-73 | `renewal_white_encountersP` | `Sec7P/Prop73.lean` | proved (Prop 7.3 at `Pascal(p)`, constant before `p`) |
