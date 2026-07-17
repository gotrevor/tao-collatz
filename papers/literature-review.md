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
  `ln2·(C_A²−2C_A) = 0.693·C_A² − 1.386·C_A`.
  ⚠️ **CORRECTED BY JUDGE PASS 28 — the `C_A ≥ 10` figure this bullet used to carry was WRONG.**
  It came from a *pre-proof* Young estimate at `ε = 1/4` (cost `(ln2)²·C_A² = 0.481·C_A²`). The
  kernel that was actually **proved** (`fnat_lt_of_suffix_window`) runs AM-GM at **`ε = 1/5`**,
  whose cost is `C_A·ln2 + (5/4)(C_A·ln2)² = 0.601·C_A² + 0.693·C_A`. Against the tight budget
  that closes iff `0.0926·C_A² > 2.079·C_A`, i.e. **`C_A > 22.46` ⟹ `C_A ≥ 23`** — at `C_A = 10`
  the cost is `66.99` vs a budget of `55.45` and it **fails**. The proved lemma's own docstring
  says `C ≳ 23`; that is the correct number. (Judge-recomputed independently:
  `tools/sandbox/tao_hbudget_check.py`.) An ε=1/4 re-proof would restore `C_A ≳ 10` if the larger
  constant ever proves inconvenient downstream.
  📌 **Also strengthened**: (6.8) does not merely lose to the Young cost at small `C_A` — for the
  proved kernel, `budget − cost` has a **negative `C_A²` coefficient** (`0.347 − 0.601 = −0.254`),
  so **no `C_A` whatsoever** rescues the ½-window. The sign is wrong, not the size.
  The Lean Cor-6.3 analogue therefore carries the
  tight l-hypothesis, and the estimate is run in SUFFIX form
  (`fnat = Σ_r 3^(r-1)·2^(l−suffix_r)`, suffix windows from (6.12)) — the prefix-indexed
  factoring the repo briefly targeted (`fnat_lt_of_prefix_bound`'s hypothesis) is unsatisfiable
  in-regime (its m=0 instance `3^(p-1)·2^p < 3^n` fails at `p ≈ 0.7925n`).
- Consumability: unchanged downstream — the single-point mass uses the LOWER l-bound
  (`2^{-l} = n^{O(C_A²)}·3^{-n}`), absorbed by taking A′ large exactly as the paper does.

### §7 renewal constant — the tower vs the true constant (big-C route re-cost, added lap 12, 2026-07-17)

*Added by the big-C campaign's deep-reflection lap 12. Route-decisive for the explicit-`C`
stretch pin `tao_collatz_quantitative_fully_explicit` (`CTao = 10^(10¹¹)`); orthogonal to the
3 merged headlines, which are axiom-clean and DONE.*

- **Prop 7.3 (`renewal_white_encounters`, Bridge.lean) proves `E[exp(-ε³·#white)] ≤ C·n^{-A}`
  with `C = C_renewalWhite A = max(n₀^A, C_polyDecay A·e^{ε³/2}·3^A)`.** The head arm `n₀^A ≈
  10^(9.36×10¹⁰) < CTao` (check17 GO). The second arm is a **triple-exponential tower**:
  `C_polyDecay A = (Cthr_prop78 A)^A`, `Cthr_prop78 ⊇ Cthr_fewWhite ⊇ B_fewWhite^{2.5}`,
  `B_fewWhite = 4^{2A+A0}(1+P)³`, `P = encWindowIter(…)` a cubic recurrence over ~10³⁰¹⁰ steps
  (check19). So the honestly-transcribed constant cannot fit under any single-exponential pin.
- **The tower is provably slop, not a floor** (lap-12 source read of `renewal_white_encounters_at`,
  Bridge.lean:522–691): the `n^{-A}` decay comes ENTIRELY from `hold_weight_expect` (Geom(4)
  hold-tail at `m=n/2`); `C_polyDecay` enters ONLY as a multiplicative constant via the
  `Q_polynomial_decay` pointwise bound, where `Q ≤ 1` already holds in the applied range
  (`m ≈ 10³⁰¹⁶ ≪ Cthr_prop78`, so Q is vacuous). Tao's Prop 7.3 has a small constant; the
  tower is an artifact of the formalization's crude `few_white_mass_le` (7.67) horizon.
- **Route (operator options A/B from `ROUTE-ESCALATION-2026-07-17.md`) RESOLVED lap 12 →
  Option B.** A (re-pin `CTao` tower-form) edits the watched judge-owned pin — out of scope.
  B keeps `CTao` and re-proves the bound with a tight constant (statement-faithful,
  differ-neutral, ADDITIVE — a new `renewal_white_encounters_tight`, leaving the clean-headline
  `renewal_white_encounters` untouched). Crux = a `#white` lower-tail estimate beating the
  (7.67) tower horizon.
- **What the source supports (feasibility, honest).** The heuristic: black = `|θq| ≤ ε =
  10⁻¹⁰⁰⁰` is measure-~2ε rare ⟹ `#white ≈ p·n/2` (ε-independent Pascal `b_j=3` rate) ⟹
  `E(n) ≈ exp(-ε³p·n/2)`, peak of `n^A E(n)` at `n* ≈ 2A/(ε³p) ≈ 10³⁰⁰⁸ < n₀` (head arm). Tao
  §7 proves the decorrelation via triangle encounters (Lemmas 7.4/7.9/7.10) — which inherently
  build the tower horizon to accumulate enough independent encounters. A tight route needs the
  few-white mass shown exp-small from `n ≈ n₀` (not `n ≈ P`). **This is genuinely uncertain**
  and is a real quantitative improvement to §7, NOT a transcription; the "white frequent"
  claim asserts the hard part is easy and must be TESTED, not assumed. This is the campaign's
  live 🟡 frontier.

## Standing deviations of the formalization from the source (fidelity ledger)

| where | paper | ours | why | ratified |
|---|---|---|---|---|
| Cor 6.3 l-window | (6.8): `l ≤ nlog3/log2 − ½C_A²log n` | tight: `l ≤ nlog3/log2 − (C_A²−2C_A)log n − O(1)`, with **`C_A ≥ 23`** | hole #3 above (½-window can NEVER close the proved kernel's budget — negative `C_A²` coefficient) | ✅ **RATIFIED pass 28.** A *restriction* (our window ⊂ paper's) ⟹ our Cor-6.3 is strictly **weaker** than the paper's ⟹ sound. Prop 1.14's statement is untouched. ⚠️ Tripwire: `hbudget` must be discharged from the tight window at `C_A ≥ 23` — undischarged, load-bearing. |
| Lemma 7.9 constant | `exp(ε)` | `exp(2ε)` (depth-gated fold pending, lap-55 directive) | holes #1, #2 above | pass 9; re-ratification due after gate |
| Lemma 7.9 form | infinite renewal process, stopping times | finite-horizon encounter fold (D6) | D1 no measure theory | pass 8 |
| white-exit mass | `≫ 1` | explicit `p₀ > 1/2` (may weaken to numeral `c₀`) | corrected ledger constant | pass 12 (pin) |
| §7 ε | "sufficiently small absolute" | `ε := 10⁻⁴` (D4) + `∃ε₀` shells | reified constants (D3/D4) | blueprint |
| asymptotics | `≪`, `≪_A` | explicit ∃-constants | D3 | blueprint |

Both literature holes are documented as findings (judge/pass-09.md, PENDING_WORK
Reflection 2026-07-12); the theorem itself is unaffected — the fixes are local to the
proof of Lemma 7.9 and strictly consumable by p.55.

### §5 Approximate formula / Prop 5.2 (C8) — pp.22–25 (read 2026-07-15 deep reflection)

*This section was absent until the 2026-07-15 reflection — §5 is the live frontier (C8) yet had
zero route-facing source synthesis. Added because the reflection's source read surfaced a
**route-decisive pin defect**.*

- **The (5.8) reindex is EXACT, driven by the (5.18) congruence.** Prop 5.2 (5.8) writes
  `ℙ(Pass_x(N_y)∈E) = Σ_{n∈I_y} Σ_{ā∈𝒜^{(n−m₀)}} Σ_{M∈E'} ℙ(Aff_ā(N_y)=M) + O(log^{-c}x)`.
  On p.25 Tao computes the RHS: by (1.3) the event `Aff_ā(N_y)=M` is **non-empty only when**
  `M ≡ F_{n−m₀}(ā) (mod 3^{n−m₀})` **(5.18)**, and then (5.19) pins `N_y` to the **single** value
  `2^{|ā|}(M−F_{n−m₀}(ā))/3^{n−m₀}`. So for each `(ā,M)` there is **at most one** `N_y`, and via
  Lemma 2.1 the triples `(N,valVec) ↔ (ā,M)` are in **bijection** on the good/`E'` set. The `O(3^{n−m₀})`
  / `O(x^{-c})` errors on p.25 are **value-rounding of a single probability term** (`M − F = (1+O(x^{-c}))M`),
  **NOT** a count-multiplicity over `ā`. The window `E'` (5.10) is `exp(±log^{0.7}x)(4/3)^{m₀}x`; the
  orbit slack (5.13)/(5.14) `exp(O(log^{0.6}x))` fits inside it (proved: `two_rpow_slack_le_exp`).
  The `(α−1)/2·log y` factor on p.25 is the **log-uniform normalization** (partition function of
  `Log(2ℕ+1∩[y,y^α])`), i.e. the probability's denominator — **not** a widening of the `M`-window.
  ⟹ the "y^{α−1} spread looks wider than the window" worry in `HANDOFF-2026-07-15-C8-reindex-mechanized.md`
  is a **misread** (that factor is the normalizer, cleared).

- **🚩 CONFIRMED HOLE #4 (C8 `approxMainTerm` pin defect, found 2026-07-15, ~90% confidence —
  source + numeric).** The Lean pin `approxMainTerm` (`Sec5/ApproxFormula.lean`, RATIFY-C8) renders
  `ℙ(Aff_ā(N_y)=M)` with the **ℕ-truncating** `Aff N k ā = ⌊(3^k N + fnat k ā)/2^{a_{[1,k]}}⌋`
  (`Basic/Valuation.lean:154`), **dropping the (5.18) congruence.** Under truncation `Aff` depends on
  `ā` essentially only through `|ā| = a_{[1,k]}` (the `fnat/2^{|ā|}` term is an `O(1)` additive shift
  to a value of size `~x`), so **exponentially many good tuples collapse into `E'`**, not just the
  true valuation vector. The closing hole `truncation_error_bound` claims the excess
  `approxMainTerm − steppedMid = E_N[#{good ā ≠ valVec : Aff N k ā ∈ E'}] ≤ C·log^{-c}x`; this is
  **FALSE**. Numeric probe (`tools/sandbox/tao_c8_truncation_probe.py`, direct enumeration over the
  Lean `fnat`/`Aff` defs): for a fixed odd `N` the truncating count is **hundreds–thousands and
  grows with `k`** (e.g. `k=8, N=101`: 19 135 good `ā` in a window of multiplicative half-width 4,
  collapsing to ~4 distinct `Aff` values), whereas adding the exact guard `2^{|ā|} ∣ (3^k N + fnat)`
  collapses it to **0–3** (→ 1 in the asymptotic Lemma-2.1 regime). The window `E'` is
  multiplicatively *wider* asymptotically (`exp(log^{0.7}x)→∞`), so the regime is worse, not better;
  log-uniform `N`-averaging does not rescue a per-`N` count of thousands.
- **The campaign KNEW the count "can exceed 1" (`ApproxFormula.lean` docstring ~:237) and bet it is
  "absorbed in `O(log^{-c}x)` as Tao does."** That bet conflates Tao's *value-rounding* error with a
  *count-multiplicity* introduced by the ℕ-floor; Tao's reindex has **no** such error term (it is
  exact). The bet is refuted.
- **The fix (faithful to (5.8)):** guard the `approxMainTerm` pushforward by the exact affine relation
  `3^{n−m₀}N + fnat (n−m₀) ā = M·2^{a_{[1,n−m₀]}}` (equivalently the (5.18) congruence
  `M ≡ F_{n−m₀}(ā) mod 3^{n−m₀}` + integrality). Then Lemma 2.1 makes the reindex **exact**,
  `approxMainTerm = steppedMid` up to the genuine (5.19) value-rounding, and `truncation_error_bound`
  **disappears**. This is a STATEMENT-level (pin) change → **JUDGE-FLAG** (see DIRECTION.md CURRENT
  DIRECTIVE 2026-07-15 + PENDING_WORK Reflection 2026-07-15). Salvage: the mechanical layer
  (`map_mask_tsum`, `goodTuple_finite`, `approxMainTerm_eq_source`, `syr_iterate_good_bracket'`,
  `two_rpow_slack_le_exp`, the step-back kernels) is **reusable** against the guarded pin.

**Fidelity-ledger row (add on re-pin):** `| (5.8) main term | exact `Aff_ā` (1.3) + congruence (5.18) |
current pin: ℕ-truncating `Aff`, unguarded | over-counts by super-polylog factor — `truncation_error_bound`
false | ❌ RE-PIN OWED (RATIFY-C8-v2, guarded pushforward) |`.
