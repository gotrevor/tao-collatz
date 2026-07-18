# Handoff: the closed form of `C_tao_assembled` (Trevor's question)

**Date**: 2026-07-17 13:14 EDT · **Branch**: `explicit-big-c` · **HEAD**: `282474f` (pushed) · **Author**: judge session

## 🎯 The question

Trevor asked: **"What is the closed form of CTao?"** — meaning `C_tao_assembled`, the constant the
assembled campaign actually landed (the old `CTao = 10^(10¹¹)` pin was retired; `C_tao_assembled`
is its honest successor). This doc hands off a **partially-traced** answer: the top of the tree is
verbatim-confirmed, the tower is confirmed present, but the **numeric size is NOT independently
re-derived** — that is the open work.

## ✅ What is VERIFIED this session (trust these; I read the def bodies)

**Top-level (verbatim from source):**
```
C_tao_assembled            = max (C_spine X_spine)  ((Real.log 2) ^ cTao)        -- ExplicitBigC.lean:73
  X_spine                  = X_syrSum                                            -- ExplicitBigC.lean:19
  X_syrSum                 = max X_windowBad (Real.exp 1)                         -- Sec3/Reduction.lean:920
  C_spine X                = 16 * C_syrSum X                                      -- Sec3/Reduction.lean:1654
  C_syrSum X               = max (C_windowBad * α/(α-1)) (4 * max 1 ((log X)^c_ladder))  -- :908
  C_windowBad              = 2 * C_descWhp                                        -- :748
  C_descWhp                = C_descLadder * (1 + (1 - α^(-c_ladder))⁻¹) * α^c_ladder -- :533
  C_descLadder             = max C_valSumGeom C_descStep                          -- :390
  C_descStep               = 2 * C_stab                                          -- Sec3/Reduction.lean
  C_valSumGeom             = C_valuationDistC K_intTest + 2 * C_geomTail          -- Sec5/FirstPassage.lean
  C_stab                   = C_valSumGeom + 4 * C_fpApprox + 2 * C_windowStable   -- Sec5/Stabilization.lean
```
(`α = alpha`, a fixed rational > 1; `c_ladder ≈ 2.25e-9` = `cTao`'s ladder; `cTao` = the pinned exponent.)

**The tower is genuinely in the closure — "tower-valued" is NOT a docstring boast.**
I dumped the full definitional closure of `C_tao_assembled` (a Lean `getUsedConstants` walk,
seed = `TaoCollatz.C_tao_assembled`): **311 project defs** (incl. `_proof`/`.match` auxiliaries;
the audit's `ExplicitnessClosure.lean` counts **209** by its recurse-into-value rule). The closure
**contains** `encWindowIter` (+ `._f`, `.match_1`), `C_polyDecay`, `Cthr_prop78`, `Cthr_fewWhite`,
`B_fewWhite`, `C_renewalWhite`. So the tower is reachable and real.

**How the tower enters (the bridge, traced):**
`C_descStep = 2·C_stab` and `C_stab = C_valSumGeom + 4·C_fpApprox + 2·C_windowStable`; the closure
edge `C_stab → C_fineScale → … → C_renewalWhite` is present. **`C_renewalWhite` enters
MULTIPLICATIVELY** — every use site is `… ≤ C_renewalWhite A * (n)^(-A)` (Sec7/Decay.lean:21,
Sec7/Bridge.lean:528, Sec6/MixingCore.lean:946/1097/1881, Sec6/MixingMain.lean:262/529). So it is a
**full-height multiplicative factor**, NOT reduced under a `log`. That means `C_spine(X_spine)` is a
**product of tower-sized factors** → the constant is a genuine tower, not merely "very large."

**The tower's own body (from `ROUTE-ESCALATION-2026-07-17.md` + check19, box-derived, spot-checked):**
```
C_renewalWhite A = max (n₀^A) (C_polyDecay A · e^{ε³/2} · 3^A)      -- Bridge.lean:~505
  C_polyDecay A  = (max (Cthr_prop78 A) 1)^A                        -- Case3.lean:~3511
  Cthr_prop78 ⊇ Cthr_fewWhite ⊇ B_fewWhite^2.5,  B_fewWhite = 4^{2A+A0}·(1+P)³   -- Case3.lean:~2532
  P = encWindowIter (2A+A0) (K+1) R,  encWindowIter cubes per step  -- Case3.lean:~1020
       encWindowIter A K (i+1) = encWindowIter A K i + ⌈4^A(1+·)³⌉ + K + 2       over R ≈ 10³⁰¹⁰ steps
  exponent A = mainDecayExponent 3.7 = A + caConst(A)²·log 2 + 3 ≈ 3.11e7          -- MixingMain.lean:157
```
So `log₁₀ C_polyDecay` is a **triple-exponential tower** (a cubic recurrence over ~10³⁰¹⁰ steps,
then `(·)^A` at `A ≈ 3.11e7`). check19 sized the `C_renewalWhite` tower at
**`log₁₀(log₁₀ C0-arm) ≈ 10^3009.5`** (fully-iterated `P`) — i.e. `C_renewalWhite` ≈ `10^(10^(10^3009.5))`-ish.

## ❓ What is OPEN (the actual deliverable Trevor wants)

1. **The SIZE of `C_tao_assembled` itself, independently re-derived.** check19 sized
   `C_renewalWhite` (the tower factor), NOT `C_spine(X_spine)`. Because `C_renewalWhite` enters
   multiplicatively (not under a log), `C_spine(X_spine)` should inherit the **full** tower height
   ≈ check19's `log₁₀log₁₀ ≈ 10^3009.5` — **but confirm this**: trace `C_stab`'s value to check the
   `C_fineScale`→`C_renewalWhite` factor is at exponent `A ≈ 3.11e7` (not a smaller `A`), and that no
   intervening `log` (e.g. the `(log X_spine)^c_ladder` term in `C_syrSum`, or `C_windowStable`'s
   internals) is the actual max-arm. ⚠️ **Do NOT assume** — `C_syrSum` is a `max`, and it is possible
   the `4·(log X_spine)^c_ladder` arm dominates instead, in which case the height is *reduced*
   (log kills a level). **Which arm of each `max` wins is the whole question.** Resolve by evaluating
   each `max` in log-space (never in Lean — the numerals hang; log-arithmetic only, as check17/19 do).
2. **What "closed form" should even mean as a deliverable.** The fully-unfolded term is 209–311
   defs — unwriteable on a page. Options: (a) the **dominant-term characterization** (a tower of
   stated height, which arm wins each max), (b) a **`check_blueprint` "check28"** that mirrors the
   `C_tao_assembled` max-tree in log/log-log space and prints its height (the natural home — extends
   check17's ladder mirror), (c) a rendered def-tree (the 311-node DAG). **Ask Trevor which he wants**
   before building — likely (a)+(b).

## 🎬 Next actions

1. Re-read this session's top-level trace above against source (it's verbatim, but verify at HEAD).
2. Decide the winning arm of each `max` in **log-space** down the spine
   `C_tao_assembled → C_spine → C_syrSum → {C_windowBad-arm vs (log X_spine)^c arm}` and, on the
   `C_windowBad` side, down through `C_stab → C_fineScale → C_renewalWhite`. This gives the height.
3. Add **check28** to `tools/check_blueprint.py`: a log/log-log mirror of the `C_tao_assembled`
   max-tree (reuse check17/19 machinery — `check19` already has the `C_renewalWhite` tower in
   log-log space; you're extending it up through the Sec3 spine). Print `log₁₀ C_tao_assembled` (or
   `log₁₀log₁₀` if it overflows) with a mutation trap. This makes the size a **machine-checked record**
   rather than a hand-claim — the same discipline the campaign used throughout.
4. Report the answer to Trevor as: dominant term + height + which max-arm wins, with the check28 line
   as evidence. **Do not** state a size you did not derive in log-space (fabrication zone).

## ⚠️ Gotchas

- **Never evaluate the numerals in Lean** (`norm_num`/`decide` hangs a billion-digit numeral) — log-arithmetic only.
- The closure-dump script I used was `tools/DumpClosure.lean` (trashed after use); re-create it from the
  `ExplicitnessClosure.lean` pattern if you want the node list again (seed `TaoCollatz.C_tao_assembled`).
- `C_renewalWhite` (the tower) vs `C_renewalWhite_tight` (deleted with the Option-B island) — the tight
  one is GONE; only the real tower-valued `C_renewalWhite` remains, and it's what `C_tao_assembled` uses.
- The campaign itself is **COMPLETE and ratified** (see `DIRECTION.md` top banner + "JUDGE RATIFICATION",
  `PENDING_WORK.md` tail). This closed-form question is a **post-completion analysis**, not reopened work —
  it changes nothing about the ratified theorem, which is axiom-clean regardless of the constant's size.

## 📁 Key files
- `TaoCollatz/ExplicitBigC.lean` — `C_tao_assembled`, `X_spine`, the theorem.
- `TaoCollatz/Sec3/Reduction.lean` — the Sec3 spine (`C_spine`, `C_syrSum`, `C_windowBad`, `C_descWhp`, `C_descLadder`, `X_syrSum`, `X_windowBad`).
- `TaoCollatz/Sec5/{FirstPassage,Stabilization}.lean` — `C_valSumGeom`, `C_stab`, `C_fpApprox`, `C_windowStable`.
- `TaoCollatz/Sec7/Bridge.lean` + `Case3.lean` — `C_renewalWhite`, `C_polyDecay`, `Cthr_prop78`, `encWindowIter` (the tower).
- `tools/check_blueprint.py` checks 17/19 — the log/log-log mirrors to extend for check28.
- `ROUTE-ESCALATION-2026-07-17.md` — the box's source-grounded tower diagnosis (the sizing to build on).
