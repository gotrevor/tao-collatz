# Literature review — route-facing synthesis (created lap 55, 2026-07-12)

The corpus is a single source: Tao 2019 (arXiv:1909.03562v5, `tao-2019-almost-all-orbits.pdf`;
per-PDF summary in `tao-2019-almost-all-orbits.md`). This file is the ROUTE-oriented read:
what the source actually says at the open strategic points, including where the formal
campaign has found it to deviate from what it claims. Update on every reflection lap that
shifts the strategic picture.

## Prior art (destination check)

No formalization of Thm 1.3 exists in any prover (re-checked by web search 2026-07-12;
earlier check 2026-07-08). Public Lean-Collatz artifacts are either full-conjecture
attempts conditional on axioms equivalent to the conjecture, or unrelated. First-anywhere
status stands.

## What the source says at each open route question

### Lemma 7.9 (X9) — pp.50–51

- **The statement (7.57)** claims `E exp(−Σ_{p≤t_min(r,R)} 1_W + ε·min(r,R)) ≤ exp(ε)`,
  for ALL `(j',l') ∈ (ℕ+1)×ℤ` and ALL positive integers `R`.
- **Confirmed hole #1 (banking display, judge pass 9, ~90% confidence)**: the p.51
  conditional-expectation display banks white damping through the END of the first block
  (`k₁`) but the true (7.57) sum stops at `t₁ < k₁` on stopped chains — false as an
  equality in the load-bearing direction. Corrected ledger gives chain value
  `e^ε·p₀/(1−(1−p₀)e^ε) ≈ exp(ε/p₀)`; our pin is `exp(2ε)` (valid for `p₀ > 1/2`).
- **Hole #2 (near-edge, found lap 55)**: the proof's (7.59) step reads, verbatim, "By
  repeating the proof of (7.51), one has `P((j'',l'') + v_{[1,k'']} ∈ W | E) ≫ 1`" — but
  (7.51)'s geometry (endpoint stays in the strip, lands outside all other triangles)
  needs the encountered triangle DEEP (depth ≥ Cthr); near the edge `j = ⌊n/2⌋` the
  endpoint exits the strip with mass that does not vanish, and `W`-mass genuinely fails.
  The paper's only acknowledgment of the edge is "r is finite since the process
  eventually exits the strip" (p.50) — finiteness, not a ledger for the uncompensated
  `e^ε` payments near the edge. Since (7.57) quantifies over all starts, the constant
  `exp(ε)` — and even our corrected `exp(2ε)` — is at risk of being FALSE as stated for
  adversarial families/starts in the edge strip.
- **What the consumer actually needs (p.55, read in full)**: Lemma 7.9 is consumed ONCE,
  at `(j',l') := (j,l)+v_{[1,k]}`, via Markov at threshold `10^A`, then `R := ⌊A²/ε⁴⌋`
  gives `Σ 1_W ≫ A²/ε³` outside `F_*` with `P(F_*) ≤ 10^{−A−2}`. Consequences verified
  lap 55:
  1. Any ABSOLUTE constant `C` in place of `exp(ε)` is absorbed (`P(F_*) ≤ C·10^{−A−2}`,
     and Prop 7.3 quantifies over all `A`).
  2. The encounters produced by the deterministic claim (7.67) all occur at depth
     `≥ 0.1m ≥ Cthr` on the surviving branch of the (7.54) split (`j_{[1,k+P]} < 0.9m`,
     Case 3 has `m ≥ C_{A,ε}`), so a DEPTH-GATED encounter count (only depth-≥-Cthr
     encounters increment `r`) still satisfies the consumer with the sharp `exp(2ε)`.
  These are the two consumable fixes for hole #2; the campaign takes the depth gate as
  primary, `∃C` as fallback (DIRECTION.md lap-55 directive).
- **White-exit mass**: the paper claims only `≫ 1` at (7.59) — never a numeric constant.
  Our `p₀ > 1/2` pin buys the clean `exp(2ε)`; any certified `c₀ > ~ε` yields
  `exp(O(ε/c₀))`, still consumable. The 1/2 is a quality target, not a feasibility gate.

### Lemma 7.10 (X10) — pp.51–54

Proof structure, in the paper's own steps: (7.60) triviality reduction (`s' ≥ CA²(1+p)`
or the claim is trivial); escape event `E′` (7.61) from Lemma 7.7 + Lemma 2.2 tails
applied to the endpoint law (`fpDist ⋆ p` iid Hold steps); outside `E′`, the geometry
(7.63)–(7.65) pins any encountered big triangle's apex to within `O(A²(1+p))` of a
determined point; distinct qualifying apexes are ≫s′-separated because their (7.11)
apex intervals "cannot have any integer point in common" **by Lemma 7.4** (this is the
actual source of separation — Lemma 7.4's disjointness, not the `(1/10)log(1/ε) ≈ 0.92`
constant; T2 is therefore unlikely to fire); the final mass sum is
`(A²(1+p)/s′) · Σ_{j'∈ℤ} s^{−1/2} G_{1+s}(c(j'−j−s/4)) ≪ A²(1+p)/s′` — a plain
Gaussian AP sum. Lean state: apex separation core PROVED (`apex_gap`,
`apex_separation`, `not_mem_two`); Gaussian AP engine exists (S3/X6); the one missing
prerequisite is the **fpDistPlus location bound** ("(7.48) as before" + Lemma 2.2 for
the extra `p` steps). Assessment: assembly volume, no unprecedented machinery.

### Case 3 assembly / X11 — pp.48–49, 54–56

(7.53)→(7.54) Chernoff split at `j_{[1,k+P]} ≥ 0.9m` (Lemma 7.7 + Lemma 2.2, noting
`0.8 > (1/4)(log9/log2)`); (7.55)→(7.56) reduction with `exp(−10A)` slack; union event
`E_*` over `p ≤ m^{0.1}` from Lemma 7.10 at `s' = 4^A(1+p)³` (`P(E_*) ≪ A²4^{−A}`);
Markov event `F_*` from Lemma 7.9; the deterministic claim (7.67): few white points ⟹
by Lemma 7.4 the walk repeatedly sits in triangles, outside `E_*` those are small
(`s_{Δ'} < 4^A(1+p)³`), and (7.11) forces exit within `10·4^A(1+p)³` steps, so `r ≥ R`
— contradiction outside `E_* ∪ F_*`. All inputs are the already-pinned/proved nodes;
the assembly lives inside the `Q_black_edge_case3` sorry.

### Corollary 6.3 / the §6 window bound (C10) — pp.31–33 (read 2026-07-14 deep reflection)

- **The §6 architecture is confirmed** and the repo's conditioning route renders it faithfully:
  event E (6.2) → stopping time k (6.5)/(6.6) → Eₖ/Bₖ/Cₖ,ₗ → density g (6.9) → CS (6.10) →
  Plancherel → independent split (1.5)/(1.26) → tail factor via Prop 1.17, head factor via
  Lemma 6.2/Cor 6.3 Rényi count. Repo block orientation (head = decay block over
  `j = n−k−1 ≈ 0.2075n` coords; tail = Rényi block over `p = k+1 ≈ 0.7925n` coords carrying
  the conditioning) re-verified against pp.30–31.
- **Confirmed hole #3 (Cor 6.3 window constant, found 2026-07-14, ~95% confidence — numerical)**:
  Cor 6.3 hypothesizes l in the window (6.8), whose upper end is
  `n·log3/log2 − (1/2)·C_A²·log n`. The proof's (6.14)→(6.15) upgrade needs
  `Σ_j 3^(j-1)·2^(l−a_{[1,j]}) < 3^n`; with (6.12) the minimum possible Young cost is
  `(ln2)²/(4·ln(4/3))·C_A² = 0.4176·C_A²` per log n in the e-exponent, but the ½-window's
  budget is only `(ln2/2)·C_A² = 0.3466·C_A²`. **The display does not close as stated**, and an
  extremal tuple (prefix deficit maxed at `j* = 1.45·C_A²·log n`, l at the ½-window top; checked
  consistent with (6.12)) makes the intermediate `< 3^n` claim genuinely false, exceeding `3^n`
  by `n^{0.07·C_A²}`. The paper's own "for a sufficiently small ε > 0" Young phrasing makes the
  cost strictly worse — no ε works against the ½-budget.
- **The fix is already implicit in the paper's event stack** (so Prop 1.14 is unaffected): the
  §6 proof only ever invokes Cor 6.3 with `l = a_{[1,k+1]} ≤ T + a_{k+1}` where
  `T = n·log3/log2 − C_A²·log n` is the stopping threshold and `a_{k+1} ≤ 2 + 2·C_A·log n` on
  Eₖ — the TIGHT window `l ≤ n·log3/log2 − (C_A²−2C_A)·log n − O(1)`, budget
  `ln2·(C_A²−2C_A) = 0.693·(C_A²−2C_A)`. Against Young at `ε = 1/4` (cost
  `(ln2)²·C_A² = 0.4805·C_A²`, geometric rate `ln(4/3)−1/4 = 0.0377`, sum ≤ 28) this closes for
  `C_A ≥ 10` with margin `0.213·C_A²·log n`. The Lean Cor-6.3 analogue therefore carries the
  tight l-hypothesis, and the estimate is run in SUFFIX form
  (`fnat = Σ_r 3^(r-1)·2^(l−suffix_r)`, suffix windows from (6.12)) — the prefix-indexed
  factoring the repo briefly targeted (`fnat_lt_of_prefix_bound`'s hypothesis) is unsatisfiable
  in-regime (its m=0 instance `3^(p-1)·2^p < 3^n` fails at `p ≈ 0.7925n`).
- Consumability: unchanged downstream — the single-point mass uses the LOWER l-bound
  (`2^{-l} = n^{O(C_A²)}·3^{-n}`), absorbed by taking A′ large exactly as the paper does.

## Standing deviations of the formalization from the source (fidelity ledger)

| where | paper | ours | why | ratified |
|---|---|---|---|---|
| Cor 6.3 l-window | (6.8): `l ≤ nlog3/log2 − ½C_A²log n` | tight: `l ≤ nlog3/log2 − (C_A²−2C_A)log n − O(1)` | hole #3 above (½-window provably too lossy) | **JUDGE-FLAG pending, pass 28** |
| Lemma 7.9 constant | `exp(ε)` | `exp(2ε)` (depth-gated fold pending, lap-55 directive) | holes #1, #2 above | pass 9; re-ratification due after gate |
| Lemma 7.9 form | infinite renewal process, stopping times | finite-horizon encounter fold (D6) | D1 no measure theory | pass 8 |
| white-exit mass | `≫ 1` | explicit `p₀ > 1/2` (may weaken to numeral `c₀`) | corrected ledger constant | pass 12 (pin) |
| §7 ε | "sufficiently small absolute" | `ε := 10⁻⁴` (D4) + `∃ε₀` shells | reified constants (D3/D4) | blueprint |
| asymptotics | `≪`, `≪_A` | explicit ∃-constants | D3 | blueprint |

Both literature holes are documented as findings (judge/pass-09.md, PENDING_WORK
Reflection 2026-07-12); the theorem itself is unaffected — the fixes are local to the
proof of Lemma 7.9 and strictly consumable by p.55.
