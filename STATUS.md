# STATUS — tao-collatz-explicit-big-c 📊

**Big-C campaign: transcribe the constant ladder into explicit defs, discharge `tao_collatz_quantitative_fully_explicit`.** · **Build**: 🟢 green (3327 jobs) · **Updated**: lap 9 (review) · 2026-07-17 · `ada7ad3` · **⚠️ ROUTE BLOCKED — see below**

## Where it stands

The three merged headlines (`tao_collatz`, `tao_collatz_quantitative`,
`tao_collatz_quantitative_explicit`) are **proven and axiom-clean** (trust base only).
The single open obligation in all of `TaoCollatz/` is the pre-planted judge pin
`tao_collatz_quantitative_fully_explicit` (`Statement.lean:68`, `sorry`) — Theorem 3.1 with
`CTao = 10^(10¹¹)`.

**⚠️ The directed discharge route is blocked (lap-8 flag, lap-9 sharpened —
`ROUTE-ESCALATION-2026-07-17.md`, awaiting an operator ruling).** STEP 1's ladder estimate
`10^(9.39×10¹⁰)` covered only the HEAD arm of `renewal_white_encounters`'s witness; lap-8
reified the second (C0-)arm and it is a **tower** ≫ CTao (`C_polyDecay = Cthr_prop78^A`,
`Cthr_prop78` ⊇ the `encWindowIter` cubic tower; machine-checked check19). So the honestly
**transcribed** `C_ladder` cannot fit under any single-exponential pin — the transcription
route is dead. **But the pin is dischargeable in truth:** the true renewal constant
`sup_n n^A·E(n)` ≈ the head `10^(9.36×10¹⁰) < CTao` (white ⟺ `|θq|>10⁻¹⁰⁰⁰` is frequent ⟹
`E(n)≈exp(-ε³·p·n/2)`, peak inside the head arm; large-n true contribution ≈ 0). The tower
is vacuous-`Q_polynomial_decay` slop. Closing it needs either (A) an operator re-pin of
`CTao` to a tower-form bound, or (B) a tighter `#white` decorrelation estimate than
`few_white_mass_le`'s (7.67) horizon (the banked "tighten-C" work). STEP 3 STOPPED; step-2
transcription continues as the prerequisite for both.

## What's happened (newest first)

- **2026-07-17 (lap 9, review)**: fresh-mind review. **Route trigger CONFIRMED FIRED** and
  sharpened: transcription route dead (C0-arm tower, check19), **but pin true** (true
  constant ≈ head < CTao; C0-arm is vacuous-`Q` slop; `white` frequent). Crux decomposed
  (`renewal_large_n_tight`, PENDING_WORK lap-9); escalated to operator
  (`ROUTE-ESCALATION-2026-07-17.md`). STATUS + DIRECTION route-note refreshed.
- **2026-07-17 (lap 8)**: case2/blackEdge/`prop_7_8`/`Q_polynomial_decay` explicit + Sec6
  complete + Sec5 C10 seam; **C0-arm NO-GO discovered** (check19) — the reified `C_polyDecay`
  tower exceeds the re-pinned CTao; discharge thread stopped, JUDGE-FLAGGED.
- **2026-07-17 (lap 6, review)**: fresh-mind review. Confirmed 1 real `sorry` (the pin),
  headlines axiom-clean, differ 35/35, all blueprint checks pass. Direction validated as
  sound/current; created this STATUS.md. No route-trigger fired **(ladder estimate then
  covered the head arm only — the C0-arm was not yet reified; superseded by lap 8/9)**.
- **2026-07-17 (lap 5b)**: pinned (7.60) `triangle_encounter_le` (`C_triEnc=max C_encTri 1e11`),
  X9 white-exit chain (`T_gaussColTail`, `T_outStrip`, `p_whiteExit=3/4`, `T_whiteExitDeep`),
  Lemma 7.9 / F* Markov chain (`eps0_manyTri=1/100`, `g_manyTri`) explicit.
- **2026-07-17 (lap 5)**: `triangle_encounter_le_rpow` (X10/Lemma 7.10) explicit via 420-line
  core (`M_encTri=1e27`, `c_encTri`, `C_encTri`); audited the `e^{ch·Mth}` term as benign
  (logarithmic collapse through threshold conversions downstream).
- **2026-07-17 (lap 4)**: (7.61) tails (`C_fpCol`, `K_rowG`, `c/C_fpColDev/Tail/Height`),
  X10a (`C_apexProx=2`), X10b (`C_encSep`), Gweight-ℤ engines (`K_intG`) explicit.
- **2026-07-17 (lap 3)**: X6 (Lemma 7.7) chain explicit (`c/C_holdLocal`, `C_fpLocation`, …);
  threshold leaves (`T_logSq`/`T_expNeg`/`T_logLin`/`T_expRpow`); coined the `_core` rail.
- **2026-07-17 (lap 2b)**: Q-decay spine explicit up to the Case3 gate (`prop_7_8_at`,
  `Q_polynomial_decay_at`; C2 still ∃ from Case3).
- **2026-07-17 (lap 2)**: bottom carrier `hold_weight_expect` de-existentialized
  (`C_hold = K+M1+2T+4`, the `1/δ≈2×10³⁰⁰⁰`-dominant term); check18 added.
- **2026-07-17 (lap 1)**: STEP 1 map — `log₁₀ C_ladder ≈ 9.39×10¹⁰`; JUDGE-FLAG (old pin
  `10⁹` exceeded ×94); **judge re-pinned `CTao = 10^(10¹¹)`**, steps 2/3 LIVE.

## Outstanding

### BLOCKER (route-level, awaiting operator ruling)
- **The pin's discharge route is decided by the operator.** STEP 3 (`C_ladder ≤ CTao`) is
  STOPPED — the transcribed `C_ladder` is a tower ≫ CTao. Options in
  `ROUTE-ESCALATION-2026-07-17.md`: **(A)** re-pin `CTao` tower-form (cheap, transcription
  then discharges), or **(B)** prove `renewal_large_n_tight` via a tighter `#white`
  decorrelation estimate than `few_white_mass_le`'s (7.67) tower horizon (keeps CTao, hard,
  in-scope-for-a-proof but banked scope-expansion). Do not start B without a ruling.

### Short-term (grind, in scope now — step-2 transcription, prereq for both options)
- Sec5 B1 `perNHarmonic_eq_harmZfine_approx_explicit` → `harmonic_to_Z_explicit` →
  `perNTerm_eval` → `stabilization`; then FirstPassage (16), ApproxFormula leaves (23),
  Sec3 (7), Syracuse (1), Prob (1). Sec7/Sec6 C-slots already explicit.

### To completion (STEP 3, after the operator ruling)
- Option A: assemble `C_ladder`, prove `C_ladder ≤ CTao_tower`, discharge the sorry.
- Option B: prove `renewal_large_n_tight`, shrink `C_renewalWhite`'s C0-arm below CTao,
  then the head-dominated ladder discharges at the current pin.
- Either way: remove the `warningAsError` shield with the sorry; confirm
  `#print axioms tao_collatz_quantitative_fully_explicit` = trust base only.

## Axiom ledger (per headline theorem)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `tao_collatz` | Thm 1.3 (uncond) | `[propext, Classical.choice, Quot.sound]` | 🟢 clean, 0 math axioms |
| `tao_collatz_quantitative` | Thm 3.1 ∃c,C (uncond) | `[propext, Classical.choice, Quot.sound]` | 🟢 clean, 0 math axioms |
| `tao_collatz_quantitative_explicit` | Thm 3.1 w/ explicit `cTao` | `[propext, Classical.choice, Quot.sound]` | 🟢 clean, 0 math axioms |
| `tao_collatz_quantitative_fully_explicit` | Thm 3.1 w/ explicit `cTao`+`CTao` | `[propext, sorryAx, Classical.choice, Quot.sound]` | 🟡 1 `sorry` — campaign target; **route BLOCKED** (transcribed `C_ladder` is a tower > CTao; pin true but needs operator ruling A/B — see ROUTE-ESCALATION) |

Math-axiom count: **0** across all headlines (the trust base is `propext`/`choice`/`Quot.sound`;
no `native_decide` artifacts, no cited math axioms). The lone open item is a `sorry`, not an
axiom — it becomes trust-base-clean at STEP 3, once the operator picks a discharge route.

## Pointers: DIRECTION (CURRENT DIRECTIVE, operator-owned) · newest HANDOFF.md · PENDING_WORK.md
