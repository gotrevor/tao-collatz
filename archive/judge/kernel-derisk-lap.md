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

