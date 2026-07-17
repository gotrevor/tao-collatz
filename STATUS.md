# STATUS — tao-collatz-explicit-big-c 📊

**Big-C campaign: discharge the explicit-constant pin `tao_collatz_quantitative_fully_explicit`.** · **Build**: 🟢 green (3327 jobs) · **Updated**: lap 12 (deep reflection) · 2026-07-17 · `548dfc5` · **ROUTE RESOLVED → Option B; crux PINNED in src (see DIRECTION)**

## Where it stands

The **core destination is already reached**: the three merged headlines (`tao_collatz`,
`tao_collatz_quantitative`, `tao_collatz_quantitative_explicit`) are proven and
**axiom-clean** — `#print axioms` re-run this lap shows `[propext, Classical.choice,
Quot.sound]` on all three. Tao 2019's theorem (qualitative Thm 1.3 + quantitative Thm 3.1
with explicit exponent `cTao`) **is formalized.** The core stretch obligation is the pin
`tao_collatz_quantitative_fully_explicit` (`Statement.lean:65`) — Thm 3.1 with the
multiplicative constant *also* pinned, at `CTao = 10^(10¹¹)`. `src/` now carries **2 real
`sorry`s**: the pin, and the Option-B crux `renewal_white_encounters_tight` (`Bridge.lean`,
pinned this lap — the tight-renewal decomposition; this is PROGRESS, the crux is now a
visible attackable hole). The 3 merged headlines remain axiom-clean.

**Route history:** STEP-2 transcription (re-express every constant as an explicit `def`) is
**complete** — the spine is constant-explicit up to `C_spine X = 16·C_syrSum X`. But the
honestly-assembled `C_spine` is a **tower ≫ CTao** (lap-8/9 route trigger, machine-checked
check19): its `C_renewalWhite` embeds `C_polyDecay = Cthr_prop78^A`, whose `encWindowIter`
cubic recurrence over ~10³⁰¹⁰ steps is a triple-exponential. So the pin **cannot** be
discharged by transcription-then-`C_spine ≤ CTao`.

**Route resolution (this lap):** the lap-9 escalation was handed to an operator who, in the
autonomous run, is unavailable; laps 10–11 spun on low-value X-chase transcription that
served only the cop-out. This deep-reflection lap **resolves the escalation → Option B.**
Option A (re-pin `CTao` to a tower) is out of scope for any lap — it edits the WATCHED,
judge-owned pin and would gut the "explicit constant" deliverable. Option B keeps `CTao`
and is a proof over frozen statements: prove a **tight** renewal bound
(`renewal_white_encounters_tight`, head-only constant `≈ n₀^A < CTao`, no tower), thread it
up a tight copy of the ladder, discharge the pin. **The tower is pure slop** — the `n^{-A}`
decay already comes from `hold_weight_expect`; `C_polyDecay` enters only as a vacuous
multiplicative factor via `Q_polynomial_decay` (where `Q ≤ 1` already holds in range). The
one genuinely new brick is a `#white` lower-tail / decorrelation estimate beating
`few_white_mass_le`'s (7.67) tower horizon. That is real §7 mathematics — the active frontier.

## What's happened (newest first)

- **2026-07-17 (lap 12, deep reflection)**: altitude pass. Re-ran `#print axioms` (3 headlines
  clean, pin `sorryAx`); term-grep confirms exactly 1 real `sorry`; Hole #4 (C8) confirmed
  **resolved in-tree**. **Diagnosed a 3-lap spin** (laps 9→10→11 grinding X-chase transcription
  behind a fired-but-unresolved route trigger). **RESOLVED the escalation → Option B** and set
  it as the binding directive. Localized the tower to `Q_polynomial_decay`/`few_white_mass_le`
  (decay is from `hold_weight_expect`; tower is vacuous slop). Crux re-decomposed and **PINNED**
  as an ADDITIVE `renewal_white_encounters_tight` (`Bridge.lean`, `548dfc5`): small-`n` arm
  proved, large-`n` arm = the named crux `sorry`; clean headlines untouched (re-verified clean);
  src `sorry` 1→2 (progress).
- **2026-07-17 (lap 11)**: STEP-2 transcription COMPLETE — spine fully constant-explicit
  (`C_spine X = 16·C_syrSum X`); check20 added; X-chase (threshold half) begun (10 FirstPassage
  cutoffs pinned). All within the now-superseded "transcription-only" holding pattern.
- **2026-07-17 (lap 10)**: C7 + C8 constants fully reified (`C_valSumGeom`, `C_fpApprox`, …).
- **2026-07-17 (lap 9, review)**: route trigger CONFIRMED FIRED + sharpened; escalated
  (`ROUTE-ESCALATION-2026-07-17.md`); crux decomposed (`renewal_large_n_tight`). ← now resolved.
- **2026-07-17 (lap 8)**: C0-arm NO-GO discovered (check19) — reified `C_polyDecay` tower
  exceeds the re-pinned CTao; discharge thread stopped, JUDGE-FLAGGED.
- **2026-07-17 (lap 6, review)**: confirmed 1 real `sorry`, headlines clean; created STATUS.md.
- **2026-07-17 (lap 1)**: STEP-1 map — `log₁₀ C_ladder ≈ 9.39×10¹⁰`; JUDGE re-pinned
  `CTao = 10^(10¹¹)`.

## Outstanding

### Short-term (Option B, in scope now — ADDITIVE, never touch the clean headlines)
- ✅ **DONE lap 12**: `renewal_white_encounters_tight` PROVED modulo one clean sorry.
  Head-only `C_renewalWhite_tight A := n₀^A`; small-`n` arm + large-`n` bridge assembly (with
  `C_Qtight`/`C_Qtight_glue`, `n₀^A·n^{-A}`, no tower) all proven. Clean headlines untouched.
- **NEXT — the frontier: prove `Q_polynomial_decay_tight`** (`Bridge.lean:~730`) — the sole
  remaining Option-B sorry: `Q ≤ C_Qtight A·(max(n/2−j) 1)^{-A}`, a poly-horizon `#white`
  lower-tail estimate beating `few_white_mass_le`'s tower horizon. Feasibility confirmed (true
  threshold ~10³⁰⁰⁸ < applied n₀ ~10³⁰¹⁶). Smallest first probe: source-read `few_white_mass_le`
  (Case3) + how its `encWindowIter` horizon is forced. Genuine multi-lap §7 decorrelation.
- Do NOT re-prove the *existing* `renewal_white_encounters` (the clean headlines consume it —
  a sorry-backed witness there would poison their axiom base). Option B is a parallel, tight copy.

### Long-term (Option B crux — the frontier)
- The tight large-n `#white` lower-tail estimate: black points `|θq|≤10⁻¹⁰⁰⁰` are measure-~2ε
  rare ⟹ `#white` frequent ⟹ `E(n)≈exp(-ε³p·n/2)` head-dominated. Rigorizing this is a
  quantitative improvement to Tao §7 decorrelation beating `few_white_mass_le`'s tower horizon.
  ⚠️ Feasibility genuinely uncertain — the "white is frequent" heuristic asserts the hard part
  is easy; test it with a compiler/source-grounded probe, don't assume it.

### To completion
- Thread `C_renewalWhite_tight` up a tight `_atC` ladder (mostly monotone reuse of the
  transcription); prove `C_spine_tight ≤ CTao` (check17 head-route GO); discharge the pin;
  remove the `warningAsError` shield with the `sorry`; confirm `#print axioms
  tao_collatz_quantitative_fully_explicit` = trust base only.

## Axiom ledger (per headline theorem — real `#print axioms`, re-run lap 12)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `tao_collatz` | Thm 1.3 (uncond) | `[propext, Classical.choice, Quot.sound]` | 🟢 clean, 0 math axioms |
| `tao_collatz_quantitative` | Thm 3.1 ∃c,C (uncond) | `[propext, Classical.choice, Quot.sound]` | 🟢 clean, 0 math axioms |
| `tao_collatz_quantitative_explicit` | Thm 3.1 w/ explicit `cTao` | `[propext, Classical.choice, Quot.sound]` | 🟢 clean, 0 math axioms |
| `tao_collatz_quantitative_fully_explicit` | Thm 3.1 w/ explicit `cTao`+`CTao` | `[propext, sorryAx, Classical.choice, Quot.sound]` | 🟡 1 `sorry` — stretch-goal target; route = **Option B** (tight renewal bound; frontier = §7 decorrelation) |

Math-axiom count: **0** across all headlines. The three core headlines are trust-base-clean —
**Tao's theorem is formalized.** The lone open item is a `sorry` (not an axiom) on the
explicit-constant stretch pin; it becomes trust-base-clean when Option B's tight renewal
bound is proven and the head-route ladder discharges it.

## Pointers: DIRECTION (CURRENT DIRECTIVE — Option B) · newest HANDOFF.md · PENDING_WORK.md (Reflection 2026-07-17 lap 12) · ROUTE-ESCALATION-2026-07-17.md (now resolved)
