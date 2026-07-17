# PENDING_WORK — big-C campaign ledger 📒

*Lap scratchpad + JUDGE-FLAG landing zone. DIRECTION.md outranks everything here. Append;
don't rewrite history. JUDGE-FLAG: lines are for the operator and must survive verbatim
until acknowledged in DIRECTION.md. (The predecessor c-campaign's ledger lives in git
history of this file.)*

## Step ledger

- [x] **Step 1 — check17 numeric mirror + the full C-ladder map** (value + file:line per
      node; report estimated `log₁₀ C_ladder` vs the pin's `10⁹`) — **DONE lap 1:
      `log₁₀ C_ladder ≈ 9.39×10¹⁰ > 10⁹` ⟹ NO-GO, JUDGE-FLAGGED below; steps 2/3 halted
      per DIRECTION's never-inflate rule** — *resolved by the JUDGE RULING below
      (re-pin `10^(10¹¹)`); steps 2/3 LIVE against the new pin*
- [ ] **Step 2 — de-existentialize the C-slots + feeding thresholds, bottom-up**
      (Sec7 22 + thresholds → Sec6 8 → Sec5 37 → Sec3 7 → Syracuse 1 → Prob 1)
- [ ] **Step 3 — `C_ladder ≤ CTao` discharge, Statement.lean sorry closed, axiom gate
      exact-3, self-stop**

## Trace / notes (append below)

*(campaign start — nothing yet; the setup commit plants the pins, the differ guard, and
this ledger. The pin: `CTao := 10 ^ (1000000000 : ℕ)`, operator-sized 2026-07-16 with ~3×
exponent headroom over the estimated `10^(2–3×10⁸)` ladder.)*

### Lap 1 (2026-07-17) — STEP 1 MAP DONE, and it is a NO-GO 🚨

**`log₁₀ C_ladder ≈ 9.39 × 10¹⁰` vs the pin's `10⁹` — the traced ladder EXCEEDS
`CTao = 10^(10⁹)` by a factor ≈ 94 in the exponent.** check17 in
`tools/check_blueprint.py` is the machine-checked trace (runs green; it asserts the
overflow, not `≤ pin`). Per DIRECTION ("if the traced ladder threatens to EXCEED CTao:
STOP that thread and JUDGE-FLAG with the trace"), step 2/3 are NOT started.

**The trace** (every hop read off the Lean source this lap):

```
Stabilization.lean:2118      consumes fine_scale_mixing 1.7
MixingRegime.lean:48         telescope calls high regime at A+2 = 3.7
                             telescope witness 2·N^A + C_high·ζ(2)   (:55)
MixingFromDecay.lean:16      osc_syracZ_high_regime witness 2·max(Cm,Ce)
MixingMain.lean:465          osc_mainHigh_bound obtains the head chain at
                             B := mainDecayExponent 3.7 = 3.7 + 6700²·ln2 + 3
                             ≈ 3.11154×10⁷;  witness 3·C_head·40^B   (:469)
MixingMain.lean:240 → MixingCore.lean:1076 → Sec7/Decay.lean:18 →
Sec7/Reduction.lean:930 → Sec7/Bridge.lean:507     pure passthrough at exponent B
Sec7/Bridge.lean:515-518     obtains C1 := hold_weight_expect B;  n0 := 2·C1+2;
                             witness  max(n0^B, C0·exp(ε³/2)·3^B)  ≥ n0^B
Sec7/Monotone.lean:246       hold_weight_expect witness Cthr = K + M1 + 2T + 4, with
                             δ := exp(epsBW³/2) − 1 ≈ 0.5×10⁻³⁰⁰⁰   (epsBW = 10⁻¹⁰⁰⁰,
                             Sec7/Setup.lean:97):
      K  = ⌈(ln(6/δ) + B·ln2)/ln(4/3)⌉                ≈ 7.50×10⁷    (:180, :331)
      M1 = ⌈K·c/(c−1)⌉,  c = (1+δ/3)^(1/B)            ≈ 10^3016.15  (:283, :341)
           — c/(c−1) ≈ 3B/δ carries the 1/δ ≈ 2×10³⁰⁰⁰ factor
      T  = 1+⌈(4(B+1)/ln(4/3))²⌉+⌈(ln(6/δ)+B·ln3)/(ln(4/3)/2)⌉ ≈ 1.87×10¹⁷ (:196, :345)
⟹ n0 ≈ 10^3016.45,  n0^B ≈ 10^(9.386×10¹⁰),  ×3·40^B×glue ⟹ C_ladder ≈ 10^(9.391×10¹⁰)
```

**Why this is not witness slop (the decisive part):** any constant `C` satisfying the
FROZEN statement of `renewal_white_encounters` at `A = B` obeys
`C ≥ sup_n exp(−ε³·n/2)·n^B` (the white-count is ≤ n/2, so the damping expectation is
`≥ exp(−ε³n/2)`); at `n = 2B/ε³` that floor is `10^(9.36×10¹⁰) > CTao`. And the frozen
proofs of `osc_mainHigh_bound`/`charFn_decay` fix the invocation at `A = B`. So NO
transcription of the existing statement+proof tower fits under the pin — the overflow is
structural, not a loose `refine`.

**Diagnosis of the sizing miss:** the operator's `10^(2–3×10⁸)` estimate is exactly what
one gets if `C1` is `T`-dominated (check17 part (c): that variant lands at `10^(6×10⁸)`,
under the pin). The missed term is `M1`'s `1/δ` — the head-region requirement
`(m−K)^{−B} ≤ (1+δ/3)m^{−B}` genuinely needs `m ≳ K·B/δ`, and with the RHS constant
pinned at `exp(epsBW³/2)` (needed so the per-step loss compounds under the
`exp(−ε³·#white)` damping), `1/δ ≈ 2×10³⁰⁰⁰` is inherent to the STATEMENT of
`hold_weight_expect`, not its proof.

**JUDGE-FLAG: the pin `CTao = 10^(10^9)` cannot be discharged over the existing
statement tower — traced ladder `≈ 10^(9.39×10¹⁰)` (check17), statement-forced floor
`≈ 10^(9.36×10¹⁰)`. Never-inflate rule honored; campaign step 2 not started. Options are
judge-owned; for sizing reference: the floor scales as `(3000 + log₁₀(2B))·B` with
`B = mainDecayExponent 3.7 ≈ 3.11×10⁷`, so (i) re-pinning CTao at `10^(10^11)` clears the
traced ladder with ~6% exponent headroom (tight; `10^(10^12)` is safe); (ii) shrinking
`epsBW` (ε = 10⁻¹⁰ would give floor ≈ 10^(1.2×10⁹), still > 10⁹) or (iii) lowering
`caConst`/`mainDecayExponent` are statement/def surgery, i.e. re-ratification territory.**

### JUDGE RULING (2026-07-16 late evening) — flag ACKNOWLEDGED; re-pin `10^(10¹¹)`; steps 2/3 LIVE ✅

The lap-1 flag is **upheld and answered**. Host-side verification was independent of
check17: the ladder and floor arithmetic re-derived from scratch (agrees to 4 digits:
ladder exponent 9.3908×10¹⁰, floor 9.3575×10¹⁰, ×93.9 over the old pin), and the
load-bearing hops read against source (`epsBW` Setup.lean:97; `M1 = ⌈K·c/(c−1)⌉` with
`c = (1+δ/3)^{1/A}` Monotone.lean; the `Fin (n/2)` white-count bound behind the floor,
Bridge.lean:507). The miss was the PIN'S VALUE (operator sizing that modeled `C1` as
`T`-dominated — check17 part (c)), not the tower or the campaign design.

**Resolution: `CTao := 10^(10¹¹)`** in `Statement.lean` + `Challenge.lean` (the JUDGE
re-pin commit; differ baseline advances to it). check17 flipped to assert the GO
(`ladder < 0.95×10¹¹`) while keeping the lap-1 finding as machine-checked record. Why
`10^(10¹¹)` and not more: exponent headroom over the traced ladder is ≈ 6.1×10⁹ ≈ 195
digits of slack on `n₀` (slack on `log₁₀ n₀` amplifies ×B), versus single-digit expected
slack from 9-decimal log bounds and ceiling roundups — and any overflow is caught
numerically by check17's exact final assert before Lean grinding, so the tight-pin
failure mode is one cheap flag round-trip, not wasted proof work. Why not options
(ii)/(iii): `epsBW`/`hold_weight_expect`/`caConst` surgery is re-ratification of the
proven tower (and `ε = 10⁻¹⁰` still floors at 10^(1.16×10⁹), over the OLD pin anyway) —
banked as a candidate follow-up "tighten-C" campaign for after discharge, which step 2's
symbolic-def scaffolding directly enables. The two optimization observations below stay
open for that campaign.

### Lap 2 (2026-07-17) — step 2 STARTED: `hold_weight_expect` de-existentialized ✅

First (and dominant) carrier done, bottom of the Sec7 chain (`Sec7/Monotone.lean`):

- **Defs planted**: `deltaBW` (= `exp(epsBW³/2) − 1`), `cHold`, `K_geom`, `T_powGeom`,
  `K_hold`, `M1_hold` (the `1/δ ≈ 2×10³⁰⁰⁰` ladder-dominant term), `T_hold`,
  `C_hold = K + M1 + 2T + 4`; `deltaBW_pos`/`one_lt_cHold`/`cHold_rpow`/`one_le_C_hold`.
- The three private `∃`-threshold lemmas reworked to threshold-explicit `_at` forms
  (witness formulas now named by `K_geom`/`T_powGeom`).
- `hold_weight_expect_core` (cutoffs abstracted) + `hold_weight_expect_explicitC`
  (at `C_hold A`); the ORIGINAL `hold_weight_expect` re-proved by pure delegation —
  statement byte-identical, differ 35/35 green vs re-pin commit `fabea6f`.
- **check18** added to `tools/check_blueprint.py`: recomputes the def bodies as written
  (b/2 inside `K_geom`'s log, `(2/ε)²` shape in `T_powGeom`, …) and cross-asserts against
  check17's simplified ladder — `log₁₀ C_hold ≈ 3016.15` confirmed.
- Census: **Sec7 1 of 22 C-slots explicit** (+ thresholds `K/M1/T/Cthr` at this node).

**Next attack (bottom-up per DIRECTION):** `Sec7/Bridge.lean:507`
`renewal_white_encounters` — name `C1 := C_hold A` consumption, `n0 := 2·C1 + 2`, and the
witness `max (n0^A) (C0·exp(ε³/2)·3^A)` as defs (`n0_renewal A`, `C_renewal A`), sibling
`renewal_white_encounters_explicitC`, delegate. Then up the Fourier passthrough
(`key_fourier_decay` → `charFn_decay`), which is pure `obtain⟨C⟩;refine⟨C,…⟩`.

## Optimization observations

- `hold_weight_expect` (`Sec7/Monotone.lean:246`): the statement demands
  `E[weight] ≤ exp(ε³/2)·m^{−A}` with `ε = epsBW = 10⁻¹⁰⁰⁰`. Since the true expectation is
  `≈ m^{−A}(1 + A/(3m))` (Geom(4) mean 1/3), a threshold `≳ A/(3δ) ≈ 10^3007` is forced by
  the statement's `1+δ`-tightness — the entire 94× overflow lives in this one statement's
  shape (site, effect: ladder exponent `~3016·B`; a shape carrying the per-step loss
  differently would give `~18·B ≈ 5.6×10⁸`). Structural; flagged above.
- `epsBW = 1/10^1000` (`Sec7/Setup.lean:97`): nothing traced so far needs it below
  ~`10⁻¹⁰`; its cube's reciprocal is the single largest number in the ladder (effect:
  `ε = 10⁻¹⁰` ⟹ ladder exponent ≈ 1.2×10⁹ — a 78× reduction, still marginally over the
  current pin).
