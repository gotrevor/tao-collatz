# Effective constants of Theorem 3.1 🔢

The quantitative headline `tao_collatz_quantitative` (Theorem 3.1, Colmin form) is

```
∃ c C, ∀ N₀ x, 2 ≤ N₀ → 2 ≤ x →
    1 - C / (log N₀)^c ≤ logProb {N | colMin N ≤ N₀} [1,x]
```

Every existential on the load-bearing path is witnessed by an **explicit closed-form
real term** (blueprint decision D3: no `IsBigO`, no filters, no non-constructive choice).
So `c` and `C` are *effective* — you can read them straight off the witness tower. This
note records what they are, where the (enormous) size comes from, and which knobs to
turn to drive them down. It's a curiosity, not part of the proof; Tao doesn't optimize
these either.

Companion calculator: [`tools/tao_effective_constants.py`](../tools/tao_effective_constants.py)
(`--sweep` for the sensitivity tables). Extracted 2026-07-16 by tracing the `refine ⟨…⟩`
witnesses through the whole tower.

## The two numbers

| | value | |
|---|---|---|
| **c** | `1 / (640_000_000 · ln 2)` ≈ **2.25 × 10⁻⁹** | exact (only transcendental is `ln 2`) |
| **C** | ≈ **5.6 × 10³⁰** (at `α = 1.001`, `Cfsm = 1`) | ≈ `1.4×10²⁸ + 5.6×10³⁰·Cfsm` |

`Cfsm = fine_scale_mixing(1.7)` (Prop 1.14, `Sec6/MixingFromDecay.lean:29`) is the one
§6 kernel leaf not further reduced here — it enters **linearly**, so `C` scales with it.
Everything else is literals.

## The witness tower (top → bottom)

`c` is just threaded/divided (a scalar); `C` accumulates multipliers. `α := 1.001`
(`Sec5/FirstPassage.lean:116`).

| layer | file:line | transform to `c` | transform to `C` |
|---|---|---|---|
| `…_spine` (headline) | Sec3/Reduction.lean:1335 | passthrough | `16 · Ca` |
| `tao_syracuse_quantitative_sum` | Sec3/Reduction.lean:690 | passthrough | `max(Cw·α/(α−1), 4·max(1,(log X)^c))` |
| `window_bad_sum` | Sec3/Reduction.lean:571 | passthrough | `2 · C_dw` |
| `descent_whp` | Sec3/Reduction.lean:410 | passthrough | `M · (1 + (1−α^(−c))⁻¹) · α^c` |
| `descentProb_ladder` | Sec3/Reduction.lean:314 | `min(c_fpne, c_stab)` | `max(C_fpne, 2·C_stab)` |
| `first_passage_nonescape` (base) | Sec5/FirstPassage.lean:1478 | → `c_fpne` | → `C_fpne = 44` |
| `stabilization` (step) | Sec5/Stabilization.lean:2752 | → `c_stab` | → `C_stab ≈ 2×10¹⁴·Cfsm` |

Both `c` branches bottom out at the **same** §5 kernel (the `stabilization` c-tree loops
back into `first_passage_nonescape`), so `c_fpne = c_stab = c`. It is built from:

```
geomHalf tail const  1/400        Prob/LocalInstances.lean:540
  · 0.1  (scaling)                 valSum_lower_geom
  → linearDecay = min(d²/2, d)     Syracuse/ValuationDist.lean:921   ← d²/2 floor = the ~1e-9
  → finalDecay = min(ln2, ·)       Syracuse/ValuationDist.lean:965
  / ln 2
  / 20   (nZero step)              two_rpow_neg_nZero_le, FirstPassage.lean:1186
= 1/(640_000_000 · ln 2)
```

## Where the 10³⁰ comes from

The analytic kernels are **tiny** — `C_fpne = 44`, and `Cfsm` enters only linearly. The
size is manufactured almost entirely by glue constants stacked at the top (numbers from
the calculator, `α = 1.001`, `Cfsm = 1`):

| factor | value | origin |
|---|---|---|
| `(1 − α^(−c))⁻¹` | **4.4 × 10¹¹** | 💥 tiny `c` × `α ≈ 1`: it's `≈ 1/(c·ln α)` |
| `α/(α−1)` | **1001** | 💥 `α = 1.001` again |
| `M = 2·C_stab` | 4.0 × 10¹⁴ | §5/§6 kernel (`200000^1.7`, and a `90000` in `Cε`) |
| `2` (window) · `16` (spine) | 32 | |

Two ~1000× factors fall straight out of `α = 1.001`, and a ~10⁹× factor out of the
`c ≈ 10⁻⁹` reciprocal. `C_stab ≈ 2×10¹⁴·Cfsm` carries the rest (the `90000 = 3·Cw'/cD`
in `Cε` is α-independent, so it's a floor).

## Knobs to poke 🔧

Run `tools/tao_effective_constants.py --sweep`. What it shows:

**α (biggest lever).** `α` sits in *three* blow-up factors at once. Raising it collapses
the top of the tower:

| α | C |
|---|---|
| 1.001 (frozen) | 5.6 × 10³⁰ |
| 1.01 | 5.7 × 10²⁸ |
| 1.1 | 6.5 × 10²⁶ |
| 2.0 | 1.6 × 10²⁵ |
| 4.0 | 5.4 × 10²⁴ |

`α` appears only in *statements* (window sets `{x^α, x^α²}`) and inequalities, never in a
correctness-critical place — it's a genuinely free tuning parameter. Edit
`Sec5/FirstPassage.lean:116` and re-verify; most downstream `norm_num`/`nlinarith` steps
that need `1 < α` or `α − 1 > 0` should still close (the delicate ones are Lemma 7.2's
Taylor step and Lemma 7.4's separation — blueprint D4).

**c (throttled by two cheap choices).** The `d²/2` branch of `linearDecay` at the small
`d = 1/4000` is what turns `1/4000` into `1/32_000_000`; plus a bare `÷20`. Neither is a
deep barrier — a sharper local-limit estimate that reached the *linear* branch would lift
`c` ~1000× and shrink `C` accordingly (calculator: linear branch + no ÷20 → `c ≈ 3.6×10⁻⁴`,
`C ≈ 3.5×10²⁵`). A hypothetical `c = 1/2` gets `C` to ≈ `2.5×10²²`.

**C_stab floor.** Even with generous `α` and `c`, `C` stays ≳ 10²²–10²⁴ because of
`C_stab`: the `90000` in `Cε` (`= 3·Cw'/cD`, `Cw'=3`, `cD=1/10000`) and `200000^1.7 ≈ 10⁹`.
Those are numeric convenience choices in §5–§6 (`windowMass_estimate`, `windowMass_ge_clog`,
the mixing regime split), tunable without touching the analysis.

## Caveats

- **Effective ≠ tight.** These are honest upper bounds read off the proof, wildly
  pessimistic by design. The point of the formalization was "a constant exists and is
  explicit," not smallness.
- **`Cfsm` not extracted.** The §6 `fine_scale_mixing(1.7)` constant is left symbolic
  (linear in `C`); pin it if you want an exact figure instead of `·Cfsm`.
- **`x₀` thresholds not extracted.** The "sufficiently large `x`" scales feed only the
  *dominated* `term2 = 4·max(1,(log X)^c)` (≈ 4, since `c ≈ 10⁻⁹`), so they don't move `C`.
- Changing a knob means **editing the Lean and re-verifying** — the script only evaluates
  the current frozen witnesses.
