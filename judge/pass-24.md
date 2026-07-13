# Judge pass 24 (2026-07-13, Ren/Opus — p.48 localization re-read) — SECOND ESCALATION **DOWNGRADED**: not altitude-class ✅

Scope: no new worker output (working tree clean at `6aec271`). This is the judge
homework pass-23 asked for: **read p.48's localization argument before asking
Trevor for any new ruling.** Verdict: the escalation dissolves. The blocked tail
is not a quantifier-order problem with the route — it is **one lossy constant in
one lemma**, and the constant is ~10⁶× larger than the mathematics requires.

## What the paper actually does (p.48, verbatim structure)

(7.50): with probability ≫ 1 the first-passage location is
`(j + s/4 + O((1+s)^{1/2}), l_Δ + O(1))` — "for a suitable choice of implied
constants **independent of ε**". Then, from (7.11) and `0 < ¼log9 < log2`:

> `−O(1) ≤ (j′ − j_Δ) log 9 ≤ s_Δ + O(1)` … "with implied constants independent
> of ε. We conclude that with probability ≫ 1, the first passage location lies
> **outside of Δ, but at a distance O(1) from Δ**, hence is white by Lemma 7.4."

Two facts settle the escalation:

1. **The relevant distance is endpoint-to-Δ, not endpoint-to-start.** The walk
   drifts a long way (`s/4` horizontally) but it drifts *along* Δ, because the
   drift slope `1/4` is strictly shallower than the triangle's edge slope
   `log2/log9 ≈ 0.3155`. The overhang past Δ's edge is an **absolute constant**.
2. **That constant is ε-free** (the paper says so twice), and ε is chosen after
   it. Our `epsBW` is frozen upstream — but that is only a problem if the
   constant is bigger than `sep`, and the constant's *size* is ours to control.

**Codex's geometry is already the paper's.** `phaseInFamily_support_imp_localization_bad`
sets `a := e.1 − X`, proves `a·log9 ≤ s·log2` from the half-space (the
`5/16 < log2/log9` inner approximation, `9⁵ < 2¹⁶` — the paper's own slope
remark), pushes the endpoint back onto Δ at the top via `triangle_top_mem_add`,
and applies `F.separated` **between that point of Δ and the endpoint**. That is
p.48 rendered faithfully. Nothing about the route is wrong.

## The actual defect: `fpDist_linear_tail`'s Chernoff throws away an exact MGF

The box is `X = ⌈(5Y + B)/16⌉` with `B = 4·10⁷` the additive threshold in
`P(16j − 5l ≥ B) ≤ 1/16` (FpLocation.lean:366). `B` is the *only* reason
`X ≈ 2.6·10⁶`. And `B` is enormous for two independent, both-avoidable reasons:

**(i) A crude quadratic MGF bound caps the tilt.** The step law is *exactly*
`k ~ geomQuarter` (`P(k) = ¼(¾)^{k−1}`, mean 4) and `Δl = 3 + Σ^{k−1} v`,
`v ~ pascalNe3` (Pascal(2,½) minus the `b=3` atom, mean 13/3) — mean vector
`(4,16)`, so `Z = 16j − 5l` has drift **−16 per step** and an elementary closed-form
MGF. The lemma instead uses a quadratic bound with a `1000·(λ₁²+λ₂²)` penalty,
which near-cancels the drift (`8·10⁻⁴ − 7.03·10⁻⁴ = 9.75·10⁻⁵`) and forces the
tilt down to `θ = 1/20000`. With the exact MGF the tilt ceiling is
`θ_c = 0.213` and the optimum is `θ* = 0.110` — **~2000× more tilt**.

**(ii) The shipped `B` is 167× larger than even its own bound needs.** At
`θ = 1/20000`, `B ≥ 240,164` suffices; the lemma ships `4·10⁷`.

Numerics (`tools/tao_linear_tail.py`, exact step law):

| tilt | per-step MGF `M` | minimal `B` for tail ≤ 1/16 |
|---|---|---|
| `1/20000` (shipped, quadratic bound) | 0.99990250 | 240,164 → **ships 4·10⁷** |
| `1/20000`, exact MGF | 0.99920126 | 198,085 |
| `θ* = 0.1096`, exact MGF | 0.860335 | **41.9** |

**`B` drops from 4·10⁷ to ≈ 42 — a factor of ~10⁶.**

## The other constant: `Y` is existential today — but it is cheaply explicit

`fpDist_height_tail` (the overshoot radius) routes through X6's
`fpDist_location_bound`, whose envelope constants `(cL, CL)` are **existential**.
So `Y` is not a numeral, and `√(X²+Y²) < sep` cannot be discharged no matter what
`B` is. **This — not `B` — is the genuine residue of pass-23's quantifier-order
worry.** Making X6's constants explicit would re-open a completed node; happily,
it isn't necessary. `Y` is explicit by an elementary route whose three ingredients
are already in the repo:

1. `fpDist_le_renewal_conv` — the endpoint is a pre-passage point *below* the
   budget line plus **one** `hold` step.
2. **Heights strictly increase**: `Δl = 3 + Σ v` with `v ≥ 2`, so `Δl ≥ 3 > 0` and
   the walk visits each height level **at most once** ⟹ the renewal mass at any
   level is `≤ 1`, with no renewal theorem and no local limit law.
3. `Δl` has an exact MGF (Pascal(2,½)-minus-the-`b=3`-atom, ceiling `μ_c = 0.0640`).

Chaining them: `P(height ≥ s+Y) ≤ Σ_{u≥0} P(Δl ≥ Y+u) ≤ E[e^{μΔl}]·e^{−μY}/(1−e^{−μ})`.
At the optimal `μ* = 0.0575` this gives **`Y = 139`** for tail ≤ 1/16
(`tools/tao_height_tail.py`; the script's mean check reproduces `E[Δl] = 16` and
`E[v] = 13/3` exactly, which validates the step-law model against `HoldBasics`).

## The box, with both constants explicit

`B = 42`, `Y = 139` ⟹ `X = ⌈(5·139 + 42)/16⌉ = 47` ⟹ **box `= √(47² + 139²) ≈ 146.7`**.

`sep = (1/10)·ln(1/ε) = 9·ln10 ≈ **20.72**` at the ruled `epsBW = 10⁻⁹⁰`. So the box
does **not** fit at the current numeral: `146.7 > 20.72`. The smallest power of ten
that clears it is `10⁻⁶³⁸` (`sep ≈ 146.9`).

**Therefore a D4 numeral re-freeze IS required — but it is the cheap kind.**
`10⁻⁹⁰ → 10⁻¹⁰⁰⁰` gives `sep ≈ 230`, a ~1.6× margin over the box, on a 1000-digit
rational that `norm_num` eats without noticing. It stays inside the ruling's own
doctrine (*"the numeral is a rational power of ten ON PURPOSE — never introduce a
`Real.exp`-valued ε"*). Compare the exit pass 23 thought was forced:
`10^(−1.09·10⁷)`, an 11-million-digit numeral. **That figure was an artifact of the
garbage `B`, not of the mathematics** — it overstated the required ε by four orders
of magnitude in the exponent.

⚠️ **Honest cost of a smaller ε, for the record**: Case 3's white-count threshold
scales as `10A/ε³` and `R = ⌊A²/ε⁴⌋` (pp.49, 55), so `d = 1000` inflates those to
`~10³⁰⁰⁰`–`10⁴⁰⁰⁰`. They are **existential** in every pin we hold today, so this
costs nothing now; it would bite only if a future Case-3 proof had to exhibit them
as numerals. Worth pricing into the choice of `d` — which is why the recommendation
is the *smallest* `d` with sane margin, not the safest-looking large one.

## Verdict

- **The second escalation is NOT altitude-class.** Pass 23's exits were (a)
  tighten the localization, or (b) **re-open D4 as a parameter** — a
  quantifier-order redesign that "re-values everything". **(b) is off the table.**
  The route is right, the geometry is right, `epsBW` stays a frozen rational power
  of ten, and nothing gets re-valued. Option (a) is the whole job, and it is two
  self-contained lemmas.
- **One ruling IS needed, and it is the cheap kind**: a D4 **numeral** re-freeze
  `10⁻⁹⁰ → 10⁻¹⁰⁰⁰` (recommended), because the explicit box (≈147) does not fit
  under today's `sep` (≈20.7). This fires the armed ε-sweep — whose seven items
  were each verified monotone-good at smaller ε in pass 23 — and changes no
  statement. **Trevor's call; prepared, not taken.**
- **Sequencing (matters).** The two lemmas are **ε-free**: they can land *before*
  any ruling, and their proved constants are what should set `d`. Land them, read
  the real box, then pick the numeral once. Guessing `d` first risks firing the
  sweep twice.
- **Suspensions stand** (`fpDist_white_exit_deep`, `fpDist_any_triangle_le`
  sorried) until both constants are numerals and the box inequality is a proved
  fact. **Nothing here is verified Lean** — the numbers above are floating-point
  optimizations over the exact step law, i.e. *targets a worker must hit*, not
  certificates. A Lean proof will likely ship somewhat lossier constants; the
  recommended `d = 1000` carries ~1.6× margin for exactly that reason.

## Directive issued (BLUEPRINT §2)

Two worker tasks, both ε-free and independent of everything else in flight:
1. **Sharpen `fpDist_linear_tail`** to the exact `geomQuarter`/`pascalNe3` MGF
   (target `B ≈ 42`; the lemma's `e^{−θB}·M/(1−M)` shape is kept — only the MGF
   input changes).
2. **Re-prove `fpDist_height_tail` off X6** via renewal-conv + strictly-increasing
   heights + the exact `Δl` MGF, yielding an explicit `Y` (target `139`). This is
   the one that unblocks the box; it also *decouples* the kernel from X6's
   existential envelope, which is worth having on its own.
Then discharge `fpDist_any_triangle_le` by instantiating
`fpDist_any_triangle_le_of_localization_box`, and the X9 kernel closes.

## Housekeeping

- 🗂️ **ManyTriangles split still queued** and now the most urgent hygiene item
  (~5,200 lines). The two lemmas above live in FpLocation/ManyTriangles.
- Paper fronts: p.48 now read three times (passes 15, 18, 24). §5 (C8) remains
  the only unread front.
- Ledger unchanged: ten verified nodes. No axiom runs this pass (no new Lean).
