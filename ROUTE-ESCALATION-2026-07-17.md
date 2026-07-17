# ROUTE-ESCALATION — big-C campaign, 2026-07-17 (review lap 9) 🚨

**For the operator/judge layer. Sharpens the lap-8 C0-arm JUDGE-FLAG. The pin value and
the route pivot are operator-owned; this doc gives you the decision, grounded in source.**

## TL;DR

The lap-8 flag is **correct that the transcription route is dead**, but it **over-reads
that as "the pin `CTao = 10^(10¹¹)` is unprovable."** Those are different claims, and the
difference is the whole decision:

- **Transcription route (STEP 3 as directed): DEAD.** The honestly-assembled `C_ladder`
  is a *tower* ≫ CTao. Machine-checked (check19). Not fixable by re-choosing witnesses
  within the current *proofs*.
- **The pin itself: DISCHARGEABLE IN TRUTH.** The true renewal constant `sup_n n^A·E(n)`
  is ≈ the head `10^(9.36×10¹⁰) < CTao` (6% headroom, check17). The C0-arm's tower value
  is **slop**, not a floor.
- **Gap:** discharging the pin needs a lower-tail bound on `#white` at `n ≥ n₀` that beats
  `few_white_mass_le`'s crude (7.67) triangle-exit **tower horizon**. That is a genuine
  quantitative improvement to Tao §7 — the banked "tighten-C" work — not transcription.

**Two operator options (§ Decision). Grind laps: STEP 3 stays STOPPED; continue step-2
transcription (banked value for either option). Do NOT touch the pin or any watched statement.**

## Where lap-8 was right, and where it slipped

Lap-8 reified the C0-arm and proved (check19) that
`C_renewalWhite A = max(n₀^A, C_polyDecay A · e^{ε³/2} · 3^A)` (Bridge.lean:505) has a
second arm that is a tower: `C_polyDecay A = (max (Cthr_prop78 A) 1)^A` (Case3.lean:3511),
`Cthr_prop78` ⊇ `Cthr_fewWhite` ⊇ `B_fewWhite^2.5`, `B_fewWhite = 4^{2A+A0}(1+P)³`
(Case3.lean:2532), `P = encWindowIter (2A+A0_fewEstar) (K+1) R` with the **cubic recurrence**
`encWindowIter A K (i+1) = encWindowIter A K i + ⌈4^A(1+·)³⌉ + K + 2` (Case3.lean:1020) over
`R ≈ 10³⁰¹⁰` steps. So `log₁₀ C_polyDecay` is a triple-exponential tower. **This arithmetic
is solid.** The transcription route cannot fit under any single-exponential pin.

Lap-8's forcedness argument, however, is **witness-propagation** ("A0 is linear in
`C_encTri`, re-enters as `Cthr^A`"). That bounds the *specific proof's witness*, not the
*true minimal C the statement admits*. Lap-1's head floor was a genuine statement floor
(`E(n) ≥ exp(-ε³n/2)` ⟹ `C ≥ sup n^A e^{-ε³n/2}`); lap-8 has **no analogous direct floor
on the final renewal constant near the tower.** The gap between "this proof's witness is a
tower" and "every proof's witness is a tower" is exactly what decides the pin.

## The sharpened structural read (this lap, all source-grounded)

1. **The C0-arm is the constant on the LARGE-n branch** (`n ≥ n₀ = 2·C_hold+2 ≈ 10³⁰¹⁶`;
   Bridge.lean:592–679). It multiplies `Q_polynomial_decay` evaluated at `m = n/2 ≈ 10³⁰¹⁶`.
   But `Q_polynomial_decay`'s constant only *bites* for `m − j > Cthr_prop78^{...} = P`,
   the tower. Since `m ≈ 10³⁰¹⁶ ≪ P`, **`Q_polynomial_decay` is VACUOUS in the entire
   applied range** — `Q ≤ 1 ≤ C_polyDecay·(m−j)^{-A}` holds only because `C_polyDecay` is a
   tower. The renewal proof is dressing up `Q ≤ 1` with a tower constant. This is the slop.

2. **`white` is frequent.** `white n ξ j l := ¬(|θq n ξ j l| ≤ epsBW)` (Setup.lean:100–103),
   `epsBW = 10⁻¹⁰⁰⁰`. A point is non-white (black) only if its angle lands within `10⁻¹⁰⁰⁰`
   of an integer — "probability" `≈ 2ε ≈ 0`. So `#white ≈ p·(n/2)` with `p` an **ε-independent**
   fraction (the `b_j = 3` Pascal rate). Hence `E(n) = E[exp(-ε³·#white)] ≈ exp(-ε³·p·n/2)`.

3. **True constant ≈ head < CTao.** `n^A·E(n)` peaks at `n* ≈ 2A/(ε³p) ≈ 10³⁰⁰⁸ < n₀`
   (inside the `n₀^A` head arm; forced floor `10^(9.36×10¹⁰)`, check17 GO). For `n ≥ n₀` the
   *true* `n^A·E(n) ≤ n₀^A·exp(-ε³p·n₀/2) ≈ 10^(9.4×10¹⁰)·exp(-10¹⁶) ≈ 0`. So the true
   large-n contribution is negligible and `sup_n n^A E(n) ≈ 10^(9.4×10¹⁰) < CTao`.

4. **Why the development can't reach it.** The only rigorous lower-tail control on `#white`
   is `few_white_mass_le`, whose horizon `P` comes from the (7.67) triangle-exit combinatorics
   (`encWindowIter`, a cubic tower). The *true* decorrelation of `θq` is ~poly(1/ε) (black
   runs of length L have mass ≈ (2ε)^L, super-exponentially rare), vastly tighter than the
   tower. The development proves `E(n)` small only for `n ≳ P`; the true smallness starts at
   `n ≳ n₀`. The `[n₀, P)` window is where the tower slop lives.

## Decision (operator-owned)

**Option A — re-pin `CTao` to a tower-form upper bound (cheap; precedent = lap-1).**
The directive states `CTao` is "a deliberate ROUND UPPER BOUND, not the assembled value,"
and the statement only *weakens* as `C` grows. Re-pinning `CTao` to clear the fully-traced
ladder (a symbolic tower, e.g. keyed to `Cthr_prop78 3.7`) makes STEP 2's transcription
discharge STEP 3 immediately. Lap-1 already set this precedent (10⁹ → 10¹¹). **Cost:** near
zero. **Downside:** the "explicit constant" is astronomically large (a tower) — may be
unacceptable for the comparator/challenge entry's spirit; a judge call.

**Option B — tighten the tower away (research; keeps `CTao = 10^(10¹¹)`, even smaller).**
Prove `E(n) ≤ CTao·n^{-A}` for `n ≥ n₀` via a decorrelation/lower-tail estimate for
`#white` beating `few_white_mass_le`'s horizon — i.e. show the few-white mass is
exp-small from `n ≈ n₀` rather than from `n ≈ P`. This is the banked "tighten-C" campaign;
it is **in scope for a proof** (it re-proves existing `∃`-statements with tighter witnesses,
no statement surgery) but it is **genuine new mathematics** improving Tao §7's constants,
and it must land inside the head's **6% exponent window** (the head `10^(9.36×10¹⁰)` is a
hard forced floor; the pin allows up to `10^(10¹¹)`). The large-n side has enormous room
(true value ≈ 0), so the only tight constraint is not re-inflating the head. Feasible but
hard; decomposition in `PENDING_WORK.md` (lap-9 entry).

**Recommendation:** A is the safe unblock and costs nothing; B is where the real mathematics
is and is the honest "small explicit constant" outcome. If the comparator tolerates a
tower-form constant, do A now and bank B; otherwise B is the only route and should be
green-lit as a scope expansion of this campaign (it stays statement-faithful).

## What grind laps should do until you rule

STEP 3 (`prove C_ladder ≤ CTao`) stays **STOPPED** (never-inflate rule; the trace exceeds
the pin). Continue **step-2 transcription bottom-up** — it is prerequisite for *both* options
(A needs the assembled ladder to state the tower pin against; B needs the scaffolding to see
exactly where to tighten). Do not edit the pin, do not edit any watched statement, do not
start B's statement-adjacent re-proofs without a ruling (they are the banked scope-expansion).
