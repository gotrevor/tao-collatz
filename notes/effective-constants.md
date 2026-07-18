# Effective constants of Theorem 3.1 🔢

The quantitative headline `tao_collatz_quantitative` (Theorem 3.1, Colmin form) is

```
∃ c C, ∀ N₀ x, 2 ≤ N₀ → 2 ≤ x →
    1 - C / (log N₀)^c ≤ logProb {N | colMin N ≤ N₀} [1,x]
```

**Short answer:** the headline holds with the explicit exponent
**`cTao = 1/(640000000 · ln 2) ≈ 2.25 × 10⁻⁹`, and that is now kernel-certified** —
`Statement.lean` defines `cTao` and proves `tao_collatz_quantitative_explicit` (PR
[#9](https://github.com/gotrevor/tao-collatz/pull/9)).
**`C` has no certified upper bound yet.** The rate-free step that made one unreadable from
the proof was removed in PR [#8](https://github.com/gotrevor/tao-collatz/pull/8), so an
upper bound is now traceable; branch `explicit-big-c` carries the certification attempt
(pin `CTao = 10^(10^9)`, a deliberately round upper bound). Don't expect `C` to be
small — the witness carries a `40^𝔡` factor with `𝔡 ≈ 3 × 10⁷`,
evaluating to `≳ 10^(7 × 10⁷)`, not the `~10³⁰` an earlier draft of this note claimed.

> 🧭 **This note began as a side expedition — a hand-trace of proof text.** The `c` half has
> since graduated: `cTao` is a def in `Statement.lean` and the kernel certifies the headline
> at that exponent, so nothing about `c` rests on this note anymore. What is still
> hand-traced: everything about `C` — the floor, the glue table, the vacuity arithmetic.
> Those stay out of `Statement.lean` until the big-`C` campaign certifies them. Read the `C`
> half as a map for that campaign — not as a claim the repo stands behind.

## Prior art: the values are not published, and Tao's methods *are* effective 📚

- **Tao's paper, p.3** (after Remark 1.4), pointing at Theorem 3.1 — the very theorem formalized
  here: *"in fact (see Theorem 3.1) our arguments give a constant of the form `C_δ ≪ exp(δ^{-O(1)})`
  … it is possible in principle that a **sufficiently explicit version** of the arguments here …
  can be used to show that the Collatz conjecture holds for a set of `N` of positive logarithmic
  density."* He gives the *shape*, not the value. (Amusingly, that `O(1)` is essentially our
  `1/c ≈ 4.4 × 10⁸`.)
- **Tao, [blog comment, 22 Sep 2024](https://terrytao.wordpress.com/2019/09/10/almost-all-collatz-orbits-attain-almost-bounded-values/comment-page-4/#comment-685839)**:
  *"The methods in my paper **are effective** and would in principle provide such a function,
  **though I did not attempt to explicitly compute this** as the arguments are rather inefficient."*
- **[MO 341570](https://mathoverflow.net/questions/341570/explicit-bounds-from-taos-result-on-collatz-conjecture)**
  (Sep 2019) asks exactly this. Its Q1 — *"Are there any values of `δ < 1` for which an explicit
  upper bound for `C_δ` is known?"* — **is still open**. The one answer notes only that arXiv v2
  has "fairly explicit dependence on `δ`."

📌 **The non-effectivity was ours, not Tao's — and it is now fixed.** Tao states his methods
are effective; he simply never computed the constants. This formalization *introduced* a
rate-free step (`hold_weight_expect`, `Sec7/Monotone.lean`) that the paper does not have — a
defect in the rendering, not something inherited from the mathematics. PR #8 repaired it with
`⌈…⌉₊`-explicit thresholds; the account below is kept because it documents what the defect
was, how it flowed to the spine, and why it could only be fixed at the lemma that minted it.

## ⚠️ What "effective" does and does not mean here

When this note was first written, every constant-carrying lemma on the path was stated
`∃ c C x₀ : ℝ, …`, and every proof `obtain`ed the witness from below, then `refine`d a new
one:

```lean
obtain ⟨c, Ca, hc, hCa, hsum⟩ := tao_syracuse_quantitative_sum
refine ⟨c, 16 * Ca, hc, by linarith, fun N₀ x hN₀2 hx2 => ?_⟩
```

`Exists` is a `Prop`, so its witness cannot be projected back out. **There is no way to
retrieve a constant from a compiled proof** — not by `#reduce`, not by `#eval`, not by any
tactic. If you tried and failed, that is why: it is structural, not an oversight.

That is also why the durable repair was never "extract harder": it was to
**de-existentialize** — name the constants as defs and re-prove the `∃`-forms by delegation.
PR #9 did exactly that for the `c` side (`c_geomTail → c_valSumGeom → c_valSumTail →
c_ladder → cTao`). The `C` side is still existential, so everything said about `C` below
remains a **source-level trace**: a human reading `refine ⟨…⟩` expressions up the tower —
*inspectable*, not *extractable*. Nothing in CI checks the `C` figures, and
`tools/tao_effective_constants.py` is an independent re-implementation of the arithmetic
that can silently drift from the Lean. Treat them as "traced by hand," one evidence tier
below anything the kernel certifies.

## `c` — pinned and kernel-certified ✅ (PR #9)

| | value |
|---|---|
| **cTao** | **`1 / (640000000 · ln 2)`** ≈ **2.25 × 10⁻⁹** |

`Statement.lean` defines the constant and proves the headline at it:

```lean
noncomputable def cTao : ℝ := 1 / (640000000 * Real.log 2)

theorem tao_collatz_quantitative_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
  exact tao_collatz_quantitative_spine_of_le c_ladder_lower
```

Axiom-gated in PR #9: exactly `propext`, `Classical.choice`, `Quot.sound`. The witness
tower is no longer opaque existentials but named defs — `c_geomTail = 1/400`
(`Prob/LocalInstances.lean`) → `c_valSumGeom` → `c_valSumTail = c_valSumGeom / 20`
(`Sec5/FirstPassage.lean`) → `c_ladder = min c_valSumTail c_stab` (`Sec3/Reduction.lean`),
with `c_stab = min (min c_valSumTail c_fpApprox) c_approxToZ` (`Sec5/Stabilization.lean`) —
and `c_ladder_lower : cTao ≤ c_ladder` is the certified collapse of the min-tree.
(`tools/check_blueprint.py` check 16 mirrors the tree in exact `Fraction` arithmetic as a
mutation trap.)

The value's provenance — the branch this note originally traced by hand, now readable as
defs (`linearDecay`/`finalDecay` in `Syracuse/ValuationDist.lean`):

```
geomHalf tail const  1/400        c_geomTail
  · 0.1  (scaling)                 c_valSumGeom's argument
  → linearDecay = min(d²/2, d)     ← the d²/2 floor is what makes it ~1e-9, not ~1e-6
  → finalDecay = min(ln2, ·)
  / ln 2                           the finalDecay division
  / 20   (nZero step)              c_valSumTail, via two_rpow_neg_nZero_le_explicit
= 1/(640000000 · ln 2)
```

### The `≤`-vs-`=` caveat, retired by the kernel

Earlier versions of this note first stated the value as `=` (an overclaim), then retreated
to `≤` — the trace covered only one branch of the min-tree, and `c8 ≥ c7`, `cs ≥ c7` were
"two numeric facts nobody has established." **They are established now**: they are exactly
what `c_ladder_lower` proves, so the question is closed by the kernel, not by this note.
The theorem only ever needed the `≥ cTao` direction (the statement is monotone in the
exponent), which is why the pin is stated as a lower-bound collapse rather than an equality.

(A historical footnote that mattered at the time: the `c` tree never touched the §6/§7
subtree where the `C` blocker lived — `mainZ_bound` reaches `fine_scale_mixing` for a bare
`C`, no `c`. That is what made `c` the actionable half first.)

## `C` — was blocked on a rate-free limit; unblocked by PR #8 🔧

An earlier version of this note reported `C ≈ 5.6 × 10³⁰` from `C ≈ 1.4×10²⁸ + 5.6×10³⁰·Cfsm`
**evaluated at `Cfsm := 1`**, and described `Cfsm` as "the one §6 kernel leaf not further
reduced — pin it if you want an exact figure." Both halves are wrong: `Cfsm := 1` was a
placeholder nobody derived, and pinning it was not bookkeeping — the rate it needed was, at
the time, not in the proof.

### The blocker (removed in PR #8)

`hold_weight_expect` (`Sec7/Monotone.lean`) used to build its threshold like this:

```lean
obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one …            -- limit-derived, no rate
…
obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
  (htend.eventually_lt_const …)
refine ⟨K + M1 + 2 * T + 4, by omega, fun m hm => ?_⟩
```

`T` came from `Tendsto (fun t => t^⌈A⌉ * (3/4)^t) atTop (nhds 0)` with **no rate**, and landed
directly in the witness. That constant flows to the spine — which is why this one lemma
blocked the headline `C`:

```
hold_weight_expect          Sec7/Monotone.lean       ⟨K + M1 + 2*T + 4, …⟩
  → renewal_white_encounters  Sec7/Bridge.lean
      obtain ⟨C1, …⟩ := hold_weight_expect
      set n0 : ℕ := 2 * C1 + 2
      refine ⟨max ((n0:ℝ)^A) (C0 * exp(ε³/2) * 3^A), …⟩    ← n0 is IN the constant
  → key_fourier_decay        Sec7/Reduction.lean
  → charFn_decay             Sec7/Decay.lean
  → head_factor_norm_le_charFn → head_uniform_highFreq_of_margin
  → osc_mainHigh_bound       Sec6/MixingMain.lean
  → osc_syracZ_high_regime → osc_syracZ_regime_telescope
  → fine_scale_mixing        Sec6/MixingFromDecay.lean
  → stabilization → … → spine
```

**PR #8 applied the fix this note prescribed, as written**: both rate-free extractions
replaced with `⌈…⌉₊`-explicit threshold lemmas (`geom_three_quarters_lt`,
`pow_mul_geom_lt_of_large` — private copies of the two BlackEdge tools, which live
*downstream* of `Monotone.lean` and could not be imported), so the witness
`Cthr = K + M1 + 2T + 4` is now traceable to a formula. The statement did not change by a
byte; `lean-axiom-gate --exact` stayed clean on both headlines.

### 🚩 D3 was not violated. D3 was never enough.

An earlier version of this note said this step made blueprint decision **D3** "not hold." That
was wrong, and it was refuting a claim D3 never made. D3 says:

> **D3 — Asymptotic notation is reified as explicit existential constants.** […] **No
> `IsBigO`/filters in load-bearing statements** (uniformity in `n, ξ` is exactly what filter-O
> obscures…)

D3 constrains **statements**. `hold_weight_expect`'s statement is
`∃ Cthr : ℕ, 1 ≤ Cthr ∧ ∀ m ≥ Cthr, …` — reified, uniform, filter-free. **D3 held**, here and
everywhere on the path (and there is no `IsBigO` anywhere in the repo). The filter was in the
*proof*.

**The real defect is more interesting: D3 buys a reified statement, not an effective witness.**
Nothing in it constrains how the witness is *produced*, so a proof can `obtain` its constant from
a rate-free limit while honoring every letter of the rule. "D3 ⟹ the constants are explicit ⟹
you can read them off the tower" is a **non-sequitur**, and it is the inference this note was
originally built on. `Exists` being a `Prop` is what makes the gap unrecoverable: an inexplicit
witness cannot be fixed downstream, only at the lemma that minted it.

⚠️ **Be precise about what that did and didn't mean.** The *mathematics* was always perfectly
effective: `t^⌈A⌉·(3/4)^t → 0` has an elementary explicit rate, and nothing in Tao's argument
is non-constructive. What was non-effective was **that proof text**, which threw the rate away
by routing through `Filter.eventually_atTop`. There was no barrier in principle — only a lemma
someone had to write, and PR #8 wrote it. "`C` is not effective" was a statement about the
Lean of the time, never about Theorem 3.1.

**And an upper bound was the only direction blocked.** A *lower* bound never needed the fix:
`hold_weight_expect` states `1 ≤ Cthr`, so `C1 ≥ 1`, `n0 = 2·C1 + 2 ≥ 4`, and the floor below
goes through against either version of the proof. It was the upper bound — the one that makes
a constant "effective" — that waited on `T`.

### And `fine_scale_mixing` is not a leaf

It has **30 constant-carrying lemmas below it** (8 in Sec6, 22 in Sec7 — `Sec6/MixingCore.lean`
imports `Sec7.Decay`). It is the largest subtree on the path, not a leaf.

### The true size

Reading the definitions:

- `caConst A = 1000 * (max A 0 + 3)` — `Sec6/MixingCore.lean`
- `mainDecayExponent A = A + (caConst A)^2 * Real.log 2 + 3` — `Sec6/MixingMain.lean`
- `osc_mainHigh_bound` witness is `3 * C * (40:ℝ)^B`, `B := mainDecayExponent A` — same file
- the telescope calls the high regime at `A + 2` — `Sec6/MixingRegime.lean`
- and `obtain … := fine_scale_mixing 1.7` is what Stabilization consumes —
  `Sec5/Stabilization.lean`

So `B = mainDecayExponent(3.7) = 3.7 + 6700²·ln 2 + 3 ≈ 3.11 × 10⁷`, and the constant carries a
factor `40^(3.11×10⁷) ≈ 10^(4.98×10⁷)`.

The full floor argument, which needs **no** unblocking — every input is a stated hypothesis or a
`refine` witness read off the source:

```
hold_weight_expect            ∃ Cthr : ℕ, 1 ≤ Cthr ∧ …        Sec7/Monotone.lean
  ⟹ C1 ≥ 1  ⟹  n0 = 2·C1 + 2 ≥ 4                             Sec7/Bridge.lean
renewal_white_encounters      ⟨max ((n0:ℝ)^A) (…), …⟩ ≥ 4^A     Sec7/Bridge.lean
  ⟹ passthrough ×4 (key_fourier_decay → charFn_decay →
      head_factor_norm_le_charFn → head_uniform_highFreq_of_margin:
      each is literally `obtain ⟨C, …⟩; refine ⟨C, …⟩`)
  ⟹ C_head(𝔡) ≥ 4^𝔡
osc_mainHigh_bound            ⟨3 · C_head(𝔡) · 40^𝔡, …⟩         Sec6/MixingMain.lean
osc_syracZ_high_regime        ⟨2 · max Cm Ce, …⟩ ≥ 2·Cm         Sec6/MixingFromDecay.lean
osc_syracZ_regime_telescope   ⟨2·N^A + C_high·ζ(2), …⟩ ≥ C_high·π²/6   Sec6/MixingRegime.lean

  ⟹ Cfsm ≥ 6 · (π²/6) · 4^𝔡 · 40^𝔡 = 6 · (π²/6) · 160^𝔡 ≈ 10^(6.86 × 10⁷)
```

**`Cfsm ≳ 10^(6.86 × 10⁷)`.** (A weaker floor of `10^(4.98 × 10⁷)` follows from the `40^𝔡` factor
alone, dropping `C_head`; both are far above 1, and neither touches the `(2·C1+2)^𝔡` term at
its true `C1` — a value that post-#8 is finally readable, and whose evaluation is the big-`C`
campaign's job.) `Cfsm` enters `C` linearly, so:

**`C ≳ 10^(7 × 10⁷)`, not `10³⁰`.** The old headline was the formula with an unknown set to a
placeholder, understating `C` by ~70 million orders of magnitude. For `Cfsm` to have been ≈ 1 you
would need `C_head ≈ 10^(-5×10⁷)`, when it is provably `≥ 4^𝔡 = 10^(1.87×10⁷)`.

### A second transcendental — `π`, and it rolls up cleanly

`osc_syracZ_regime_telescope` (`Sec6/MixingRegime.lean:42`) witnesses `2 * (N:ℝ)^A + C * S`
with

```lean
let S : ℝ := ∑' k : ℕ, (k : ℝ) ^ (-(2 : ℝ))     -- Sec6/MixingRegime.lean:50
```

That is ζ(2), so **`S = π²/6`** — the Basel problem, and Mathlib already has it:
`hasSum_zeta_two : HasSum (fun n : ℕ => (1:ℝ) / (n:ℝ) ^ 2) (π ^ 2 / 6)`
(`Mathlib/NumberTheory/ZetaValues.lean:452`). Bridging to the form used here needs only
`rpow` ↔ `pow` (`Real.rpow_neg`, `Real.rpow_natCast`); the `k = 0` term is `0` on both sides
under Lean's conventions, so they agree.

So "the only transcendental is `ln 2`" was wrong, but this is **not** an obstruction — it is a
second *named* constant. `C`'s closed form is symbolic in `π` and `ln 2`, which is the right way
to carry it: `π²/6` says where the constant came from in a way that `1.6449…` does not.

### The other volume driver: thresholds move `C` here

`N := max 9 n₀`, where `n₀` is the high-regime *threshold* existential, enters the constant as
`2·N^A`. So the Sec6/Sec7 `n₀` chain must be extracted too — "`x₀` thresholds don't move `C`"
is true up top and false exactly where `C` is biggest.

## From "unblocked" to a certified pin 🔧

With #8 landed, `C` is a closed-form composite — symbolic in `π` and `ln 2`, with every
constant traceable to the lemma that minted it:

```
C_fsm(A)  = 2·(max 9 n₀)^A + C_high(A+2)·π²/6       ← π²/6 = ζ(2), the telescope's tail sum
C_high(B) = 2·max( 3·C_char(𝔡(B))·40^𝔡(B) , 6 )     where 𝔡(B) = B + (1000(B+3))²·ln2 + 3
C_char(D) = max( (2·C₁+2)^D , C₀·exp(ε³/2)·3^D )    where ε = epsBW = 1/10^1000
C₁        = K + ⌈K·c/(c−1)⌉₊ + 2·T + 4               ← T explicit since #8
```

That form is the useful artifact: it says *where* the size comes from (`(1000(B+3))²` squared
into an exponent, then `40^𝔡`). Its *value* is a tower with tens of millions of digits — worth
knowing, but the symbolic form is what anyone would actually want to read.

Good news for whoever evaluates it: **the telescope does not compound the constant.** It calls
the high regime once at a shifted exponent, and the induction yields a ζ(2)-dominated sum that
is flat in the iteration count. There is no recursive blow-up — only volume: the census below
counts 107 carriers once thresholds are included, and for `C` they must be.

**The certification attempt is in flight.** Branch `explicit-big-c` pins
`CTao := 10^(10^9)` — a deliberately round upper bound with ~3× exponent headroom over the
estimated `10^(2–3×10⁸)` ladder; the statement *weakens* as `C` grows, so a generous upper
bound is the discharge-friendly direction — and states
`tao_collatz_quantitative_fully_explicit`, sorry-by-design until the ladder discharges. Until
that lands, no upper bound on `C` is certified, and the figures in this note remain the
hand-traced state of knowledge.

## The glue constants up top (unchanged, and still correct)

These are the multipliers `Cfsm` gets multiplied *by*. The analytic kernels are tiny —
`C_fpne = 44` is a genuine literal, traced to `intTest_class_dev` (`Sec5/FirstPassage.lean`,
witness `⟨2, …⟩`) and `intTest_D_lower` (same file, witness `⟨1/8, …⟩`) giving `K = 16`, then
`valuation_dist` `C = 2K + 4Ct = 40` and `valSum_lower_geom` `C = Cd + 2Ct = 44`.

| factor | value | origin |
|---|---|---|
| `(1 − α^(−c))⁻¹` | 4.4 × 10¹¹ | tiny `c` × `α ≈ 1`: it's `≈ 1/(c·ln α)` |
| `α/(α−1)` | 1001 | `α = 1.001` |
| `M = 2·C_stab` | 4.0 × 10¹⁴·Cfsm | §5/§6 kernel (`200000^1.7`, and a `90000 = 3·Cw'/cD` in `Cε`) |
| `2` (window) · `16` (spine) | 32 | |

`90000 = 3·Cw'/cD` verified: `windowMass_estimate` `C=3`, `windowMass_ge_clog` `c=1/10000`,
`Cε := 2 + 3*(Cw/cD) + 2*Cw/(alpha-1)` (`set Cε` in `Sec5/Stabilization.lean`).

## 🚩 α is not a free tuning parameter

An earlier version of this note called `α` "a genuinely free tuning parameter — edit
`Sec5/FirstPassage.lean` and re-verify," and tabulated a sweep down to `α = 4.0`. **That
sweep is arithmetic on the shape of the bound, not a property of the formalization.** `α`'s
exact value is welded into load-bearing lemmas, which become *false* — not merely
unprovable — if it moves. The exact sites drift as §5 is refactored (the first table here
went stale within a week); the *pattern* is what to grep for —
`grep -rn "unfold alpha" TaoCollatz/Sec5` finds a dozen-plus welds, e.g.:

| claim in the proof | at α = 4 |
|---|---|
| `1000 * (alpha - 1) = 1` (`Sec5/FirstPassage.lean`) | `3000 = 1` ✗ |
| `alpha - 1 = 0.001` (`Sec5/Stabilization.lean`, `Sec5/ApproxFormula.lean`) | `3 = 0.001` ✗ |
| `(alpha - 1) / 100 = 1/100000` (`Sec5/Stabilization.lean`, `Sec5/ApproxFormula.lean`) | ✗ |

The proof genuinely exploits `α ≈ 1` (the window `[x, x^α]` must be narrow), which is why Tao
fixes `α = 1.001` at (1.18). It is a structural choice, not a knob. Raising it means redoing the
analysis, not re-running `norm_num`.

## Where this leaves things

- **`c` is done.** This note's design brief — de-existentialize mechanically (no proof body
  on the path uses the constants' opacity), collapse the min-tree via `le_min` using only
  **lower** bounds `c₀ ≤ c` (the statement is monotone in the exponent for `log N₀ ≥ 1`;
  `N₀ = 2` is trivial since `C` is astronomical and `logProb ≥ 0`), and keep the constant
  symbolic in `ln 2` rather than rounding it away — was executed as written in PR #9. The
  `ln 2` is not an inconvenience to be eliminated: it is the `finalDecay` division, and
  carrying it says so; Mathlib's `Real.log_two_gt_d9` / `log_two_lt_d9` discharge the
  comparisons. Nothing about `c` rests on this note anymore.
- **`C` is unblocked (PR #8) and mid-certification** (branch `explicit-big-c`, pin
  `CTao = 10^(10^9)`). Until that lands, the honest state is: floor `C ≳ 10^(7×10⁷)`
  (hand-traced, above), no certified upper bound, and MO 341570's Q1 — an explicit upper
  bound on `C_δ` — still has no published answer.
- **Effective ≠ tight**, and here not even close. These are upper bounds read off a proof
  never optimised for size. Taking `cTao` and the `C` floor at face value, the bound is
  vacuous until `N₀ > exp(exp(7.01 × 10¹⁶))` — the figure `tools/tao_effective_constants.py`
  computes from the strengthened `C_head ≥ 4^𝔡` floor. (An earlier version of this note said
  `5 × 10¹⁶`, taken from the weaker `40^𝔡`-only floor; the note and its own tool had
  drifted.) Tao does not optimise these either.

## Census

The tower table above lists 7 lemmas. The real path from the spine carries **76 constant-carrying
existentials** (Sec5 37, Sec7 22, Sec6 8, Sec3 7, Syracuse 1, Prob 1), plus 31 threshold-only ones
— 107 if the thresholds must be extracted too, which for `C` they must. (PR #9's sibling lemmas
pin only the `c`-slots; the `C`-slots on that path stay existential, so this census is still the
big-`C` campaign's workload.)

## References 📚

What the literature says about these constants. Short version: the shape is published, the
numbers are not, and Tao says why. Quotes below were read off the source pages, not recalled.

**The paper.** Tao, *Almost all orbits of the Collatz map attain almost bounded values*,
[arXiv:1909.03562](https://arxiv.org/abs/1909.03562); Forum of Mathematics Pi 10 (2022).
Remark 1.4 (p.3) gives the shape and stops there:

> our arguments give a constant of the form `C_δ ≪ exp(δ^{-O(1)})`

The `O(1)` is never pinned. ⚠️ This repo pins **v5** (`AGENTS.md`); v6 landed 2026-07-06.

**Tao, [11 Sep 2019](https://terrytao.wordpress.com/2019/09/10/almost-all-collatz-orbits-attain-almost-bounded-values/comment-page-1/#comment-521963)** — states Theorem 3.1 in exactly the shape
formalized here (`Colmin(N) ≤ C₀` on a set of logarithmic density `1 - O(log^{-c} C₀)`), then:

> in principle, this could be combined with a numerical verification of cases up to `C₀` to
> obtain the result that the Collatz conjecture held for a set of positive logarithmic density.
> (Thanks to Ben Green for pointing out this possibility to me.) Unfortunately the value of
> `C₀` produced by the arguments in my paper, **while in principle explicit, are almost
> certainly too enormous for this strategy to be easily implemented**

The `C` floor above is the quantitative form of "too enormous": `C ≳ 10^(7 × 10⁷)`.

**Tao, [29 Jan 2020](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/#comment-537882)** — hedges even on the shape:

> the arguments give an in principle explicit relation between `C` and `δ`, **which I believe
> to be** of the form `C = exp(δ^{-O(1)})`

**Tao, [22 Sep 2024](https://terrytao.wordpress.com/2019/09/10/almost-all-collatz-orbits-attain-almost-bounded-values/comment-page-4/#comment-685839)** — the closest thing to a direct answer:

> The methods in my paper are effective and would in principle provide such a function, though
> **I did not attempt to explicitly compute this as the arguments are rather inefficient.**

**Tao, [29 Apr 2025](https://terrytao.wordpress.com/2019/09/10/almost-all-collatz-orbits-attain-almost-bounded-values/comment-page-4/#comment-687865)** — on the payoff, and its ceiling:

> The arguments in my paper do show that a positive density fraction of orbits must fall below
> some explicit finite threshold `C` … But even then this would fall short of the claim that a
> density 1 set of orbits do not diverge.

**[MathOverflow 341570](https://mathoverflow.net/questions/341570/explicit-bounds-from-taos-result-on-collatz-conjecture)**, Wojowu, 14 Sep 2019 — asks this note's question directly:

> Are there any values of `δ<1` for which an explicit upper bound for `C_δ` is known?

**Open since 2019.** The accepted answer points at v2's fuller `δ`-dependence, which answers a
different question; its top comment (scoring above the answer) is `"more detail" -- for instance?`.

### So what would be new here

Nothing about `c`'s *value* is deep — it is arithmetic anyone could redo. What was unclaimed
is that nobody had redone it. Two concrete things this note pointed at, and where they stand:

1. **Pin the `O(1)`.** Inverting Theorem 3.1 (`δ = C/(log N₀)^c`) gives
   `C_δ = exp(C^{1/c} · δ^{-1/c})`, so the exponent in Remark 1.4's `exp(δ^{-O(1)})` is `1/c`,
   needing **no `C`** — and `1/cTao = 640000000 · ln 2 ≈ 4.4 × 10⁸`.
   ⚠️ The inversion is unverified algebra, not machine-checked. Check before quoting.
2. **Formalize the bounds**, so they are kernel-certified rather than hand-read — the only
   version of this note worth citing. ✅ Done for `c` (PR #9, `tao_collatz_quantitative_explicit`);
   in flight for `C` (branch `explicit-big-c`).
