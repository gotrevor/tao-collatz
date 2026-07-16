# Effective constants of Theorem 3.1 🔢

The quantitative headline `tao_collatz_quantitative` (Theorem 3.1, Colmin form) is

```
∃ c C, ∀ N₀ x, 2 ≤ N₀ → 2 ≤ x →
    1 - C / (log N₀)^c ≤ logProb {N | colMin N ≤ N₀} [1,x]
```

**Short answer:** `c` is traceable and is `1/(640_000_000 · ln 2) ≈ 2.25 × 10⁻⁹`.
**`C` is not currently effective** — one step on the load-bearing path produces its
constant from a rate-free limit — and once that step is fixed, `C` is not `~10³⁰` but a
tower of at least `10^(5 × 10⁷)`. Details and the one-line fix below.

> 🧭 **This is a side expedition, and nothing here is part of the result.** The theorem is
> what `TaoCollatz/Statement.lean` says; these constants are hand-traced from proof *text*,
> which is a weaker kind of evidence than anything else in this repo, and `C` is not effective
> at all. So they stay out of `Statement.lean`, out of the theorem, and out of the blueprint
> until someone formalizes them. Read this as a map for whoever does — not as a claim the
> repo stands behind.

## ⚠️ First: what "effective" does and does not mean here

Every constant-carrying lemma on the path is stated `∃ c C x₀ : ℝ, …`, and every proof
`obtain`s the witness from below, then `refine`s a new one:

```lean
obtain ⟨c, Ca, hc, hCa, hsum⟩ := tao_syracuse_quantitative_sum
refine ⟨c, 16 * Ca, hc, by linarith, fun N₀ x hN₀2 hx2 => ?_⟩
```

`Exists` is a `Prop`, so its witness cannot be projected back out. **There is no way to
retrieve `c` or `C` from the compiled proof** — not by `#reduce`, not by `#eval`, not by any
tactic. If you tried and failed, that is why: it is structural, not an oversight.

Everything below is therefore a **source-level trace**: a human reading `refine ⟨…⟩`
expressions up the tower. It is *inspectable*, not *extractable*. Nothing in CI checks these
numbers, and `tools/tao_effective_constants.py` is an independent re-implementation of the
arithmetic that can silently drift from the Lean. Treat the figures here as "traced by hand,"
one evidence tier below anything the kernel certifies.

## `c` — traceable, and the trace checks out ✅

| | value |
|---|---|
| **c** | `1 / (640_000_000 · ln 2)` ≈ **2.25 × 10⁻⁹** |

Built from (each `file:line` verified):

```
geomHalf tail const  1/400        Prob/LocalInstances.lean:540  (witness at :544)
  · 0.1  (scaling)                 valSum_lower_geom, FirstPassage.lean:1211
  → linearDecay = min(d²/2, d)     Syracuse/ValuationDist.lean:921   ← d²/2 floor = the ~1e-9
  → finalDecay = min(ln2, ·)       Syracuse/ValuationDist.lean:965
  / ln 2                           FirstPassage.lean:1213
  / 20   (nZero step)              two_rpow_neg_nZero_le, FirstPassage.lean:1182
= 1/(640_000_000 · ln 2)
```

`valSum_lower_geom` sets `c := min cd cg` (`FirstPassage.lean:1215`), where
`cd = 1/(320_000·ln 2)` comes from `valuation_dist` and `cg = 1/(32_000_000·ln 2)` from the
`geomHalf` branch. `cg` is ~100× smaller, so the `min` is `cg`, and the `/20` gives the figure
above.

### 🚩 The `c` tree is a min over more branches than a "loopback"

An earlier version of this note claimed both `c` branches bottom out at the same §5 kernel, so
`c_fpne = c_stab`. **That is false.** `descentProb_ladder` (`Sec3/Reduction.lean:303`) sets
`c := min cb cs` from two *separately obtained* opaque variables, and `stabilization`
(`Sec5/Stabilization.lean:2752`) is a **three-way** min:

```lean
refine ⟨min (min c7 c8) cs, C7 + 4 * C8 + 2 * Cs, …⟩
```

So `c_stab = min (min c7 c8) cs ≤ c7 = c_fpne`, with equality only if `c8 ≥ c7` **and**
`cs ≥ c7` — two numeric facts this note never established. The proof does not need them (it
uses only `min ≤ each` plus rpow-exponent antitonicity), which is why the `min` design is
robust. But the *rationale* was wrong.

### The `c` tree is clear of the `C` blocker

Worth recording, because it is what makes `c` actionable: **no `c` on the path depends on the
§6/§7 subtree.** `Sec5/ApproxFormula.lean` imports only `Sec5.FirstPassage` and
`Basic.Valuation`. `mainZ_bound` (`Stabilization.lean:2346`) — the one branch reaching
`fine_scale_mixing` — returns `∃ C x₀`, with **no `c`**. `approxMainTerm_to_Z` (`:2620`) takes
its `c` as `min c1 c2` from `Iy_count_ratio` (`:2541`) and `perNTerm_eval` (`:2487`), consuming
`mainZ_bound` only for a bare `C`. The blocker below is entirely on the `C` side.

## `C` — 🚩 not currently effective

An earlier version of this note reported `C ≈ 5.6 × 10³⁰` from `C ≈ 1.4×10²⁸ + 5.6×10³⁰·Cfsm`
**evaluated at `Cfsm := 1`**, and described `Cfsm` as "the one §6 kernel leaf not further
reduced — pin it if you want an exact figure." Both halves are wrong.

### It is blocked on a rate-free limit

`hold_weight_expect` (`Sec7/Monotone.lean:127`) builds its threshold like this:

```lean
obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one …            -- :142, limit-derived, no rate
…
obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp           -- :163
  (htend.eventually_lt_const …)
refine ⟨K + M1 + 2 * T + 4, by omega, fun m hm => ?_⟩  -- :165
```

`T` comes from `Tendsto (fun t => t^⌈A⌉ * (3/4)^t) atTop (nhds 0)` with **no rate**, and lands
directly in the witness. That constant then flows to the spine:

```
hold_weight_expect          Sec7/Monotone.lean:127   ⟨K + M1 + 2*T + 4, …⟩
  → renewal_white_encounters  Sec7/Bridge.lean:507
      obtain ⟨C1, …⟩ := hold_weight_expect                 :515
      set n0 : ℕ := 2 * C1 + 2                             :517
      refine ⟨max ((n0:ℝ)^A) (C0 * exp(ε³/2) * 3^A), …⟩    ← n0 is IN the constant
  → key_fourier_decay        Sec7/Reduction.lean:930  (obtains it at :937)
  → charFn_decay             Sec7/Decay.lean:18       (obtains it at :22)
  → head_factor_norm_le_charFn → head_uniform_highFreq_of_margin
  → osc_mainHigh_bound       Sec6/MixingMain.lean:460
  → osc_syracZ_high_regime → osc_syracZ_regime_telescope
  → fine_scale_mixing        Sec6/MixingFromDecay.lean:29
  → stabilization → … → spine
```

So the blueprint-D3 claim ("no `IsBigO`, no filters, no non-constructive choice on the
load-bearing path") **does not hold**. It holds everywhere else — this is the only such step on
the whole path, and there is no `IsBigO` anywhere in the repo — but this one carries a constant.

⚠️ **Be precise about what that does and doesn't mean.** The *mathematics* here is perfectly
effective: `t^⌈A⌉·(3/4)^t → 0` has an elementary explicit rate, and nothing in Tao's argument is
non-constructive. What is non-effective is **this proof text**, which throws the rate away by
routing through `Filter.eventually_atTop`. There is no barrier in principle — only a lemma
someone has to write. "`C` is not effective" is a statement about the current Lean, not about
Theorem 3.1.

**And an upper bound is the only direction that's blocked.** A *lower* bound needs nothing at
all: `hold_weight_expect` states `1 ≤ Cthr`, so `C1 ≥ 1`, `n0 = 2·C1 + 2 ≥ 4`, and the floor
below goes through with no edits. It is the upper bound — the one that makes a constant
"effective" — that waits on `T`.

### And `fine_scale_mixing` is not a leaf

It has **30 constant-carrying lemmas below it** (8 in Sec6, 22 in Sec7 — `Sec6/MixingCore.lean`
imports `Sec7.Decay`). It is the largest subtree on the path, not a leaf.

### The true size

Reading the definitions:

- `caConst A = 1000 * (max A 0 + 3)` — `Sec6/MixingCore.lean:2327`
- `mainDecayExponent A = A + (caConst A)^2 * Real.log 2 + 3` — `Sec6/MixingMain.lean:142`
- `osc_mainHigh_bound` witness is `3 * C * (40:ℝ)^B`, `B := mainDecayExponent A` — `:469`
- the telescope calls the high regime at `A + 2` — `Sec6/MixingRegime.lean:48`
- and `fine_scale_mixing 1.7` is what Stabilization consumes — `Sec5/Stabilization.lean:2088`

So `B = mainDecayExponent(3.7) = 3.7 + 6700²·ln 2 + 3 ≈ 3.11 × 10⁷`, and the constant carries a
factor `40^(3.11×10⁷) ≈ 10^(4.98×10⁷)`.

The full floor argument, which needs **no** unblocking — every input is a stated hypothesis or a
`refine` witness read off the source:

```
hold_weight_expect            ∃ Cthr : ℕ, 1 ≤ Cthr ∧ …        Sec7/Monotone.lean:127
  ⟹ C1 ≥ 1  ⟹  n0 = 2·C1 + 2 ≥ 4                             Sec7/Bridge.lean:517
renewal_white_encounters      ⟨max ((n0:ℝ)^A) (…), …⟩ ≥ 4^A     Sec7/Bridge.lean:518
  ⟹ passthrough ×4 (key_fourier_decay → charFn_decay →
      head_factor_norm_le_charFn → head_uniform_highFreq_of_margin:
      each is literally `obtain ⟨C, …⟩; refine ⟨C, …⟩`)
  ⟹ C_head(𝔡) ≥ 4^𝔡
osc_mainHigh_bound            ⟨3 · C_head(𝔡) · 40^𝔡, …⟩         Sec6/MixingMain.lean:469
osc_syracZ_high_regime        ⟨2 · max Cm Ce, …⟩ ≥ 2·Cm         Sec6/MixingFromDecay.lean:16
osc_syracZ_regime_telescope   ⟨2·N^A + C_high·ζ(2), …⟩ ≥ C_high·π²/6   Sec6/MixingRegime.lean:55

  ⟹ Cfsm ≥ 6 · (π²/6) · 4^𝔡 · 40^𝔡 = 6 · (π²/6) · 160^𝔡 ≈ 10^(6.86 × 10⁷)
```

**`Cfsm ≳ 10^(6.86 × 10⁷)`.** (A weaker floor of `10^(4.98 × 10⁷)` follows from the `40^𝔡` factor
alone, dropping `C_head`; both are far above 1, and neither touches the `(2·C1+2)^𝔡` term at its
true `C1`, which the blocker hides.) `Cfsm` enters `C` linearly, so:

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

### One real obstruction besides `T`: thresholds move `C` here

`N := max 9 n₀`, where `n₀` is the high-regime *threshold* existential, enters the constant as
`2·N^A`. So the Sec6/Sec7 `n₀` chain must be extracted too — "`x₀` thresholds don't move `C`" is
true up top and false exactly where `C` is biggest.

## What would make `C` effective 🔧

**One surgical fix.** Replace the two rate-free extractions at `Sec7/Monotone.lean:142,163` with
explicit witnesses. The repo already contains the right tools and uses this pattern throughout
§7:

- `T` bounds `t^⌈A⌉·(3/4)^t < δ/3·3^(-A)` → `exp_neg_mul_le_of_large`
  (`Sec7/BlackEdge.lean:302`, witness `⟨⌈log b⁻¹/ρ⌉₊, …⟩`) + `log_le_eps_mul_of_large`
  (`:316`, witness `⟨⌈(2/ε)^2⌉₊ + 1, …⟩`).
- `K` → `⌈log(δ/3·2^(-A))/log(3/4)⌉₊`.

Good news for anyone attempting it: **the telescope does not compound the constant.** It calls
the high regime once at a shifted exponent, and the induction yields a ζ(2)-dominated sum that
is flat in the iteration count. There is no recursive blow-up — only volume.

Afterwards `C` is a closed-form composite — symbolic in `π` and `ln 2`, with every constant
traceable to the lemma that minted it:

```
C_fsm(A)  = 2·(max 9 n₀)^A + C_high(A+2)·π²/6       ← π²/6 = ζ(2), the telescope's tail sum
C_high(B) = 2·max( 3·C_char(𝔡(B))·40^𝔡(B) , 6 )     where 𝔡(B) = B + (1000(B+3))²·ln2 + 3
C_char(D) = max( (2·C₁+2)^D , C₀·exp(ε³/2)·3^D )    where ε = epsBW = 1/10^1000
C₁        = K + ⌈K·c/(c−1)⌉₊ + 2·T + 4               ← T is the only unpinned symbol
```

That form is the useful artifact: it says *where* the size comes from (`(1000(B+3))²` squared
into an exponent, then `40^𝔡`). Its *value* is a tower with tens of millions of digits — worth
knowing, but the symbolic form is what anyone would actually want to read.

## The glue constants up top (unchanged, and still correct)

These are the multipliers `Cfsm` gets multiplied *by*. The analytic kernels are tiny —
`C_fpne = 44` is a genuine literal, traced to `intTest_class_dev` (`FirstPassage.lean:689`,
witness `⟨2, …⟩`) and `intTest_D_lower` (`:765`, witness `⟨1/8, …⟩`) giving `K = 16`, then
`valuation_dist` `C = 2K + 4Ct = 40` and `valSum_lower_geom` `C = Cd + 2Ct = 44`.

| factor | value | origin |
|---|---|---|
| `(1 − α^(−c))⁻¹` | 4.4 × 10¹¹ | tiny `c` × `α ≈ 1`: it's `≈ 1/(c·ln α)` |
| `α/(α−1)` | 1001 | `α = 1.001` |
| `M = 2·C_stab` | 4.0 × 10¹⁴·Cfsm | §5/§6 kernel (`200000^1.7`, and a `90000 = 3·Cw'/cD` in `Cε`) |
| `2` (window) · `16` (spine) | 32 | |

`90000 = 3·Cw'/cD` verified: `windowMass_estimate` `C=3`, `windowMass_ge_clog` `c=1/10000`,
`Cε := 2 + 3*(Cw/cD) + 2*Cw/(alpha-1)` (`Stabilization.lean:1498`).

## 🚩 α is not a free tuning parameter

An earlier version of this note called `α` "a genuinely free tuning parameter — edit
`Sec5/FirstPassage.lean:116` and re-verify," and tabulated a sweep down to `α = 4.0`. **That
sweep is arithmetic on the shape of the bound, not a property of the formalization.** `α`'s exact
value is welded into load-bearing lemmas, which become *false* — not merely unprovable — if it
moves:

| site | claim | at α = 4 |
|---|---|---|
| `Sec5/FirstPassage.lean:507` | `1000 * (alpha - 1) = 1` | `3000 = 1` ✗ |
| `Sec5/FirstPassage.lean:1365` | `alpha ^ 3 ≤ 1.01` | `64 ≤ 1.01` ✗ |
| `Sec5/ApproxFormula.lean:931` | `alpha ^ 3 ≤ 1004/1000` | ✗ |
| `Sec5/Stabilization.lean:731` | `(alpha - 1) / 100 = 1/100000` | ✗ |
| `Sec5/Stabilization.lean:2605` | `alpha - 1 = 0.001` | ✗ |

The proof genuinely exploits `α ≈ 1` (the window `[x, x^α]` must be narrow), which is why Tao
fixes `α = 1.001` at (1.18). It is a structural choice, not a knob. Raising it means redoing the
analysis, not re-running `norm_num`.

## Where this leaves things

- **`c` is the tractable half.** It is clear of the blocker, and de-existentialising it is
  mechanical: **no proof body anywhere on the path uses the constants' opacity** — they are
  consumed only as positivity facts, rpow-exponent monotonicity, and passthrough arithmetic. The
  repo already proves the pattern with `alpha : ℝ := 1.001` (`FirstPassage.lean:116`, ~290 uses).
  Scope is Sec5's ~37 constant-carriers. Note you only ever need **lower** bounds `c₀ ≤ c` (the
  statement is monotone in `c` for `log N₀ ≥ 1`; `N₀ = 2` is trivial since `C` is astronomical and
  `logProb ≥ 0`), so the min-tree collapses via `le_min` and the `c_fpne = c_stab` question never
  arises. Keep the constant symbolic —

  ```lean
  noncomputable def cTao : ℝ := 1 / (640000000 * Real.log 2)
  ```

  — rather than rounding to a rational under it. The `ln 2` is not an inconvenience to be
  eliminated: it is the `finalDecay` division at `FirstPassage.lean:1213`, and carrying it says
  so. Mathlib's `Real.log_two_gt_d9` / `log_two_lt_d9` (already used ~20× in this repo) discharge
  the comparisons.
- **`C` needs the `Monotone.lean:163` fix first**, and the honest answer afterwards is a tower.
- **Effective ≠ tight**, and here not even close. These are upper bounds read off a proof never
  optimised for size. Taking the traced `c` and the `C` floor at face value, the bound is vacuous
  until `N₀ > exp(exp(5 × 10¹⁶))`. Tao does not optimise these either.

## Census

The tower table above lists 7 lemmas. The real path from the spine carries **76 constant-carrying
existentials** (Sec5 37, Sec7 22, Sec6 8, Sec3 7, Syracuse 1, Prob 1), plus 31 threshold-only ones
— 107 if the thresholds must be extracted too, which for `C` they must.
