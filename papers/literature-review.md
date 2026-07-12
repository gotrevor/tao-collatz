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

## Standing deviations of the formalization from the source (fidelity ledger)

| where | paper | ours | why | ratified |
|---|---|---|---|---|
| Lemma 7.9 constant | `exp(ε)` | `exp(2ε)` (depth-gated fold pending, lap-55 directive) | holes #1, #2 above | pass 9; re-ratification due after gate |
| Lemma 7.9 form | infinite renewal process, stopping times | finite-horizon encounter fold (D6) | D1 no measure theory | pass 8 |
| white-exit mass | `≫ 1` | explicit `p₀ > 1/2` (may weaken to numeral `c₀`) | corrected ledger constant | pass 12 (pin) |
| §7 ε | "sufficiently small absolute" | `ε := 10⁻⁴` (D4) + `∃ε₀` shells | reified constants (D3/D4) | blueprint |
| asymptotics | `≪`, `≪_A` | explicit ∃-constants | D3 | blueprint |

Both literature holes are documented as findings (judge/pass-09.md, PENDING_WORK
Reflection 2026-07-12); the theorem itself is unaffected — the fixes are local to the
proof of Lemma 7.9 and strictly consumable by p.55.
