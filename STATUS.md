# STATUS — tao-collatz-explicit-big-c 📊

**Big-C campaign: transcribe the constant ladder into explicit defs, discharge `tao_collatz_quantitative_fully_explicit`.** · **Build**: 🟢 green (3327 jobs) · **Updated**: lap 6 (review) · 2026-07-17 · `b6f5680`

## Where it stands

The three merged headlines (`tao_collatz`, `tao_collatz_quantitative`,
`tao_collatz_quantitative_explicit`) are **proven and axiom-clean** (trust base only).
The single open obligation in all of `TaoCollatz/` is the pre-planted judge pin
`tao_collatz_quantitative_fully_explicit` (`Statement.lean:68`, `sorry`), which asserts
Theorem 3.1 with the concrete constant `CTao = 10^(10¹¹)`. Discharging it needs an explicit
upper bound `C_ladder ≤ CTao` on the spine's assembled constant — so the campaign is a
bottom-up transcription of every constant-carrying existential into a named symbolic `def`
(`_explicitC` sibling + delegate), all fully proven (they add **no** sorries). STEP 1
(feasibility) is closed: the traced ladder is `≈10^(9.39×10¹⁰)`, and the judge re-pinned
`CTao` from `10^(10⁹)` to `10^(10¹¹)` to clear it (6.1% exponent headroom, check17 GO).

## What's happened (newest first)

- **2026-07-17 (lap 6, review)**: fresh-mind review. Confirmed 1 real `sorry` (the pin),
  headlines axiom-clean, differ 35/35, all blueprint checks pass. Direction validated as
  sound/current; created this STATUS.md. No route-trigger fired (ladder < pin).
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

### Short-term (mirror PENDING_WORK top)
- Case3 few_white cluster: `few_white_reach_mass_le` → `bigTriangle_walk_le_rpow` +
  `estar_union_le_rpow` → `few_white_estar_mass_le` → `few_white_mass_le`.
- Damping chain → `Q_black_edge_case3` (reifies **C2**) → wire C2 into `prop_7_8_at`.

### Long-term
- `renewal_white_encounters` (Bridge.lean) + Fourier passthrough (`key_fourier_decay` →
  `charFn_decay`); then Sec6 (8 slots), Sec5 (37), Sec3 (7).
- Extend check18 with the C0-arm numeric assert once `Q_polynomial_decay`'s C0 is explicit.

### To completion (STEP 3)
- Assemble `C_ladder` def, prove `C_ladder ≤ CTao` (one log-arithmetic inequality),
  discharge the `Statement.lean` sorry by delegation, remove the warningAsError shield,
  confirm `#print axioms tao_collatz_quantitative_fully_explicit` = trust base only.

## Axiom ledger (per headline theorem)

| headline theorem | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `tao_collatz` | Thm 1.3 (uncond) | `[propext, Classical.choice, Quot.sound]` | 🟢 clean, 0 math axioms |
| `tao_collatz_quantitative` | Thm 3.1 ∃c,C (uncond) | `[propext, Classical.choice, Quot.sound]` | 🟢 clean, 0 math axioms |
| `tao_collatz_quantitative_explicit` | Thm 3.1 w/ explicit `cTao` | `[propext, Classical.choice, Quot.sound]` | 🟢 clean, 0 math axioms |
| `tao_collatz_quantitative_fully_explicit` | Thm 3.1 w/ explicit `cTao`+`CTao` | `[propext, sorryAx, Classical.choice, Quot.sound]` | 🟡 1 `sorry` — the campaign target; discharged when `C_ladder ≤ CTao` lands |

Math-axiom count: **0** across all headlines (the trust base is `propext`/`choice`/`Quot.sound`;
no `native_decide` artifacts, no cited math axioms). The lone open item is a `sorry`, not an
axiom — it becomes trust-base-clean at STEP 3.

## Pointers: DIRECTION (CURRENT DIRECTIVE, operator-owned) · newest HANDOFF.md · PENDING_WORK.md
