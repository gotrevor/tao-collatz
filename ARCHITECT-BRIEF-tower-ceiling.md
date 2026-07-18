# Handoff: prove an explicit TOWER CEILING on `C_tao_assembled` in Lean

**Date**: 2026-07-17 13:28 EDT · **Branch**: `explicit-big-c` · **HEAD**: `f4fc186` (pushed) · **From**: judge session
**Builds on**: `ARCHITECT-BRIEF-closed-form-of-CTao.md` (the closed-form trace — read it first, it has the def spine).

## 🎯 The goal (Trevor's ask)

Prove, in Lean, an **explicit tower-numeral upper bound** on the ratified constant:
```lean
theorem C_tao_assembled_le : C_tao_assembled ≤ (10:ℝ) ^ ((10:ℝ) ^ ((10:ℝ) ^ (3010:ℝ))) := …
```
(exponent `3010` is a PLACEHOLDER — see "the number" below; prove whatever height the induction
honestly yields, rounded up.) This converts the ratified-but-opaque constant into a **crisp,
citable headline**: *"Tao Thm 3.1, kernel-certified, with explicit `C ≤ 10^(10^(10^3010))"* — the
clean answer to MO 341570. It is **additive** on the complete, ratified campaign; it changes nothing
about the axiom-clean theorem, only *reports its constant*.

## ✅ Feasibility verdict: ~85% it lands (~90% for a generous ceiling)

**Why it's tractable where the pin campaign was not.** The pin campaign tried to squeeze the tower
*under* a fixed SMALL numeral `10^(10¹¹)` — impossible, the tower is bigger. This is the OPPOSITE: a
tower ceiling *above* the tower, i.e. an upper bound with **generous slack in every step**. No new
mathematics; it is careful constant-chasing plus one real induction. The favorable direction is the
whole reason to believe the 85%.

**The height is real and correct-shaped.** check19: `log₁₀log₁₀ C_renewalWhite ≈ 10^3009.5` ⟹
`C_renewalWhite ≈ 10^(10^(10^3009.5))`. This session confirmed `C_tao_assembled` inherits the FULL
height (the tower factor `C_renewalWhite` enters **multiplicatively** — `≤ C_renewalWhite A · n^(-A)`
at every use site — NOT under a `log`). So Trevor's `10^(10^(10^3009.5))` is the right ballpark.

## ⚠️ Two honest caveats (do not skip)

1. **The numeral is SYMBOLIC, never a literal.** `10^(10^(10^3010))` has ~`10^(10^3010)` digits —
   it cannot be a Lean numeral, and `norm_num`/`decide`/`native_decide` will hang on it forever
   (standing repo gotcha). Write it as `(10:ℝ) ^ ((10:ℝ) ^ ((10:ℝ) ^ K))` with `Real.rpow`, and do
   ALL size reasoning in `Real.log`/log-space (as `check17`/`check19` do). Never materialize it.
2. **The exponent `3009.5`/`3010` is NOT yet independently pinned.** The closed-form brief flagged that
   which `max`-arm wins is unresolved. **Good news: this proof SETTLES that rigorously** — the
   induction yields the honest height as output. So do NOT hardcode `3010` and try to hit it; prove
   `C_tao_assembled ≤ 10^(10^(10^K))` for whatever `K` falls out, **rounded up generously**.
   Tightness is NOT the goal — a *stated explicit tower* is, and slack makes every inequality easier.
   A safe over-estimate (e.g. `K = 10^3010`, or even looser) is a perfectly good, honest, reportable
   result. Only chase a tight `K` if it's cheap.

## 🔨 The work

### The crux (ONE real lemma) — CONFIRMED it does not exist yet
`encWindowIter` (`Sec7/Case3.lean:1020`) is the tower engine:
```lean
noncomputable def encWindowIter (A : ℝ) (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => encWindowIter A K i + (⌈(4:ℝ)^A * (1 + (encWindowIter A K i : ℝ))^3⌉₊ + K + 2)
```
Cubic-additive: `enc(i+1) ≈ 4^A · enc(i)³`. The repo has `encWindowIter_mono` (`:1029`) but **NO
closed-form upper bound** — you must prove one. Target shape (by induction on `i`):
```
encWindowIter A K i  ≤  B ^ (3 ^ i)        for an explicit base B = B(A,K)   -- e.g. B = 5·4^A·(K+3)
```
Induction step: `enc(i+1) ≤ enc(i) + 5·4^A·(1+enc(i))³ ≤ 5·4^A·(B^(3^i))³ · c = (…)^(3^(i+1))`, with
the base chosen so the `+K+2` and the `⌈·⌉₊` slack absorb (pick `B` large enough that `5·4^A·… ≤ B²`,
giving room). Moderate difficulty; the shape is standard "super-exponential recurrence → tower bound."
At `i = R ≈ 100·K_fewWhite ≈ 10^3010`, this gives `enc(R) ≤ B^(3^(10^3010))` ⟹ `log₁₀log₁₀ ≈ 10^3010`.
⚠️ `encWindowIter` returns `ℕ`; state the bound over `ℝ` (cast) or as `⌈B^(3^i)⌉₊`.

### The propagation (mechanical, ~15–30 lemmas) — walk the bound UP the tree
Each node is a `max` / product / power / `⌈·⌉₊` / `log` / `exp` of tower-bounded things — all
monotone. Chain (from the closed-form brief, verbatim spine):
```
encWindowIter ≤ B^(3^R)
 → B_fewWhite = 4^{2A+A0}(1+P)³            (P = encWindowIter…, so P ≤ tower)
 → Cthr_fewWhite ⊇ B_fewWhite^2.5
 → Cthr_prop78
 → C_polyDecay = (max (Cthr_prop78 A) 1)^A     ← the `(·)^A` at A≈3.11e7 is where the 3rd tower level lands
 → C_renewalWhite = max (n₀^A) (C_polyDecay·e^{ε³/2}·3^A)
 → [Sec6 mixing] C_fineScale → C_stab
 → [Sec3 spine] C_descStep=2·C_stab → C_descLadder → C_descWhp → C_windowBad → C_syrSum → C_spine=16·C_syrSum
 → C_tao_assembled = max (C_spine X_spine) ((log 2)^cTao)
```
Each step: `positivity` + `mul_le_mul`/`rpow_le_rpow`/`max_le` + the child's bound. Numerous but each
is short. **Resolved max-arm** (settles a closed-form-brief open question): in `C_syrSum X = max(C_windowBad·α/(α−1),
4·max(1,(log X)^c_ladder))`, the second arm is **negligible** — `X_spine` is a tower, `log(tower)` is
one level down, and `^c_ladder` (c ≈ 2.25e−9) crushes it to ~1. So the `C_windowBad` arm wins, and
`C_tao_assembled`'s height = `C_windowBad`'s height = the `C_renewalWhite` tower height. Prove this
arm inequality explicitly rather than assuming it.

### The assembly + the machine-checked record
- State `C_tao_assembled_le` with the symbolic rpow tower; discharge by the propagation chain.
- Add **`check28`** to `tools/check_blueprint.py`: a log/log-log mirror of the whole `C_tao_assembled`
  max-tree (extend `check19`, which already has the `C_renewalWhite` tower in log-log space) that
  prints `log₁₀log₁₀ C_tao_assembled` and asserts it `≤ K` with a mutation trap. This makes the
  height a machine-checked claim, not a hand-assertion — the discipline the campaign used throughout.
- **Ratify** on completion: `#print axioms C_tao_assembled_le` = the standard three (it will be — it's
  a real-analysis inequality over the already-clean constant); add `C_tao_assembled_le` to the
  `tao_stmt_diff.py` watch list (and `TaoCollatz/ExplicitBigC.lean` is already in `SEARCH_FILES`); if
  it goes in a new file, add that file too (I hit exactly this inert-guard trap this session).

## 🎬 Next actions (in order)
1. Prove the `encWindowIter` closed-form bound (the crux). De-risk FIRST — if it lands, the rest is
   mechanical and the 85% becomes ~95%. If it fights you, `JUDGE-FLAG` before spending laps downstream.
2. Propagate up the tree (the ~15–30 lemmas), bottom-up, one commit per node or small cluster.
3. State + prove `C_tao_assembled_le`; add `check28`; ratify + differ-watch.
4. Report to Trevor: the theorem statement + the explicit `K` + `#print axioms` + the check28 line.

## 🚦 How to run it
This is a bounded, well-posed campaign (~1–3 days fleet time). It is **NOT yet spec'd as a DIRECTIVE**
— `DIRECTION.md` currently reads CAMPAIGN COMPLETE. To run it: the operator/judge writes a new
`BIG_C_CEILING_PLAN.md` + a fresh DIRECTIVE (one-owner rules still apply — see DIRECTION.md banner),
then **Trevor fires**. Suggested `--done-when` cannot be a sorry-count (library is already 0 and stays
0 — this adds a theorem, not removes a sorry); gate on a `check_blueprint`/audit predicate or just
`--max-duration` + operator stop. (`--done-when` accepts ONLY `sorry-free:<path>`; see
`todos/open/lean-treadmill-help-contradicts-itself.md`.) Self-stop can't fire here anyway (8 comparator
stubs at repo root), so no `--forever`; keep `box stuck` alive as the escalate lane.

## ⚠️ Gotchas
- Log-arithmetic ONLY; never materialize the tower numeral (hangs).
- The bound is over `ℝ`; `encWindowIter : ℕ → ℕ` — cast carefully.
- Confirm the induction base `B` absorbs the `⌈·⌉₊` (`Nat.ceil ≤ x+1`) and `+K+2` slack — that's where
  a naive induction stalls.
- The campaign is COMPLETE/ratified; this is ADDITIVE reporting work, not reopened proof. Do not touch
  the 36 watched statements (differ must stay `c0c8327 HEAD` = clean; `fabea6f HEAD` = 33/33 paper pins).

## 📁 Key files
- `TaoCollatz/Sec7/Case3.lean` — `encWindowIter` (:1020), `encWindowIter_mono` (:1029), `B_fewWhite`, `Cthr_fewWhite`, `Cthr_prop78` (the tower; grep them).
- `TaoCollatz/Sec7/Bridge.lean` — `C_renewalWhite`, `C_polyDecay`.
- `TaoCollatz/Sec3/Reduction.lean`, `Sec5/{FirstPassage,Stabilization}.lean` — the spine (see the closed-form brief).
- `TaoCollatz/ExplicitBigC.lean` — `C_tao_assembled`; where `C_tao_assembled_le` likely belongs.
- `tools/check_blueprint.py` checks 17/19 — the log/log-log mirrors to extend for check28.
- `ROUTE-ESCALATION-2026-07-17.md` — the box's tower sizing (the arithmetic to formalize).
