# DIRECTION — big-C campaign 🔢

*Grind laps READ and OBEY this file; it outranks any handoff. The operator layer (host-side)
is the only writer of the CURRENT DIRECTIVE. Keep reports as "N of M carriers explicit."
`blueprint_rules.md` remains BINDING. Predecessor campaign (pin `c`, PR #9, merged): its
methods are this campaign's playbook; its DIRECTION lives in git history (`git log
--follow DIRECTION.md`).*

---

## JUDGE RULING (2026-07-16 late evening) — lap-1 JUDGE-FLAG acknowledged; `CTao` re-pinned at `10^(10¹¹)`; steps 2/3 are LIVE 🟢

The lap-1 flag is **upheld**: the trace and the statement-forced floor were verified
independently host-side (arithmetic re-derived from scratch; the `epsBW`/`hold_weight_expect`/
`renewal_white_encounters`/`mainDecayExponent` hops read against source; check17 green).
The original pin's exponent sizing missed `M1`'s `1/δ ≈ 2×10³⁰⁰⁰` factor, and the floor
argument shows no proof over the frozen tower fits under `10^(10⁹)` — the miss was in the
pin's VALUE (operator sizing), not in the tower or the campaign design. Resolution:

- **`CTao := 10 ^ (100000000000 : ℕ)` (= `10^(10¹¹)`) in BOTH pin files** — done in the
  re-pin commit (`git log --grep 'JUDGE re-pin'`). Exponent headroom over the traced
  ladder ≈ 6.1×10⁹ (~6.5%), i.e. ~195 digits of slack on `n₀` (slack on `log₁₀ n₀`
  amplifies by `×B`) — orders beyond any plausible log-arithmetic proof slop.
- **check17 now asserts the GO** (`ladder < 0.95 × 10¹¹`) and keeps the lap-1 finding
  (ladder and floor vs the old pin) as machine-checked record.
- **Differ baseline advances to the re-pin commit** — see the hard-rails note below.
- Options (ii)/(iii) — shrinking `epsBW`, reshaping `hold_weight_expect`, lowering
  `caConst` — are statement/def surgery on the proven tower: **out of scope for this
  campaign**, banked as a candidate follow-up ("tighten-C") for after discharge. Step 2's
  symbolic-def scaffolding is exactly what such a campaign would build on, so nothing is
  lost by transcribing first. Keep reporting optimization observations.

**Steps 2 and 3 are unblocked. Resume at step 2, bottom-up, per the directive below**
(read `10^(10¹¹)` wherever it says the pin; the never-inflate/STOP rule applies to the
NEW value exactly as it did to the old).

---

## CURRENT DIRECTIVE (campaign start, 2026-07-16 evening; pin value updated by the ruling above) — **pin `C` in Lean: discharge `tao_collatz_quantitative_fully_explicit`**

### 🎯 The objective, in one sentence

Discharge the `sorry` on the PRE-PLANTED, JUDGE-OWNED pin (already in
`TaoCollatz/Statement.lean` AND `Comparator/TaoCollatz/Challenge.lean` + `config.json`;
you write the PROOF, never the statement):

```lean
noncomputable def CTao : ℝ := 10 ^ (100000000000 : ℕ)

theorem tao_collatz_quantitative_fully_explicit :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - CTao / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x)
```

`CTao` is a deliberate ROUND UPPER BOUND, not the assembled value. The statement WEAKENS as
`C` grows (`1 - C/(log N₀)^c` only shrinks), so any `C_ladder ≤ CTao` inequality over the
development's assembled constant discharges it. Sizing (post-ruling, step-1-traced): the
assembled constant is `≈ 10^(9.39×10¹⁰)` — dominated by `n₀^𝔡` with `𝔡 = mainDecayExponent
3.7 ≈ 3.11×10⁷` and `n₀ ≈ 10^3016` (the `1/δ` in `hold_weight_expect`'s witness) — so
`10^(10¹¹)` has ≈ 6.1×10⁹ exponent headroom (~195 digits of slack on `n₀`).
**If the traced ladder threatens to EXCEED `CTao`: STOP that thread and `JUDGE-FLAG:` with
the trace. Never inflate the pin — it is not yours to edit, in either file.**

### 🥇 STEP 1 — map before you mine: the numeric mirror

Before any Lean def, extend `tools/check_blueprint.py` with a **check17**: a float/exact
mirror of the `C`-ladder (mirror check16's style; float is fine for the map, exact-`Fraction`
for the final pin check). Walk the actual Lean witnesses (file:line per hop) — NOT from
memory. The known skeleton (verify every line against source; trust Lean over this sketch):

- `caConst A = 1000·(max A 0 + 3)` — `Sec6/MixingCore.lean` (`caConst 3.7 = 6700`)
- `mainDecayExponent A = A + (caConst A)²·log 2 + 3` — `Sec6/MixingMain.lean`
- `osc_mainHigh_bound` witness `3·C·40^B`, `B = mainDecayExponent A` — `Sec6/MixingMain.lean`
- telescope calls the high regime at `A + 2`; `fine_scale_mixing 1.7` is what Stabilization
  consumes → `B = mainDecayExponent 3.7`
- `osc_syracZ_regime_telescope` witness carries `2·N^A + C_high·S` with `N = max 9 n₀`,
  `S = ∑' k, k^(-2) = ζ(2) = π²/6` — `Sec6/MixingRegime.lean`
- the Sec7 chain: `hold_weight_expect`'s `Cthr = K + M1 + 2·T + 4` (explicit post-#8) →
  `C1` → `n0 = 2·C1 + 2` → `renewal_white_encounters`'s `max ((n0)^A) (…)` →
  the Fourier passthrough (`key_fourier_decay` → `charFn_decay` → …) — `Sec7/`
- Sec5/Sec3: the `C`-slots of the same lemmas the `c` campaign already gave `_explicit`
  siblings; the glue chain `descentProb_ladder → … → tao_collatz_quantitative_spine`

Deliverable: PENDING_WORK.md gets the full tree (value + file:line per node) and check17
passes. Report the estimated `log₁₀ C_ladder` — this is the go/no-go against the pin.

### 🥈 STEP 2 — sibling + delegate, bottom-up, `C`-slots AND thresholds

Census (from the hand-trace; re-verify): **76 constant-carrying existentials** (Sec5 37,
Sec7 22, Sec6 8, Sec3 7, Syracuse 1, Prob 1) **+ 31 threshold-only = 107 sites**. Thresholds
are IN SCOPE this time: `N := max 9 n₀` enters the constant as `2·N^A`, so the Sec6/Sec7
`n₀`/`x₀` chain must be extracted where (and only where) it feeds `C`.

Per carrier, the proven pattern: (1) name the witness as a symbolic `noncomputable def`
(`C_foo`, `T_foo`); (2) sibling `foo_explicitC` with the def in the `C`/threshold slot;
(3) re-prove the ORIGINAL `∃`-form by delegation — **original statements byte-identical,
the differ checks**. Where a `_explicit` sibling already exists from the `c` campaign,
extend or sibling it — don't fork a third naming scheme.

You only ever need **UPPER bounds `C_ladder ≤ C₀`** (mirror of the `c` campaign's
lower-bounds-only): sums/products/maxes collapse via `add_le_add`/`mul_le_mul`/`max_le`,
monotonicity of `rpow`/`pow` in base and exponent. Numeric comparisons stay in LOG form:
`Real.log_two_gt_d9`/`log_two_lt_d9` (ln 2), `Real.pi_gt_3141592`/`Real.pi_lt_3141593`
(π, via ζ(2) — `hasSum_zeta_two` in `Mathlib/NumberTheory/ZetaValues.lean` bridges the
`∑' k, k^(-2)` form; mind `rpow` vs `pow` casts).

**Cost-center rails** (learned the cheap way last campaign):
- One `_pos` lemma per def; never let laps grind `positivity` on opaque defs site by site.
- 🚨 **NEVER evaluate the big numerals.** `10 ^ (1000000000 : ℕ)` type-checks as a term but
  any tactic that normalizes it (`norm_num [CTao]`, `decide`, kernel reduction of the
  numeral) will hang the build — a billion-digit numeral. Same for `40^𝔡`-shaped terms.
  ALL comparisons via log-arithmetic and monotonicity lemmas; `norm_num` only on small
  rationals and exponent arithmetic.
- Local `set_option maxHeartbeats` bumps only, justified in a comment, on one declaration.

### 🥉 STEP 3 — discharge and stop

When the spine's `C`-chain is explicit: prove `C_ladder ≤ CTao` (one log-arithmetic
inequality, mirrored exactly by check17's final assert), discharge the Statement.lean
`sorry` by delegation, confirm `#print axioms tao_collatz_quantitative_fully_explicit` =
exactly the standard three. `TaoCollatz/` then greps 0 sorries → the self-stop gate closes
the run. The comparator CI check going green IS the external "done" (its challenge entry
was pre-planted; `Solution.lean` needs no edit — it imports the development).

### 🔒 Hard rails

- **Never edit a ratified statement.** `tools/tao_stmt_diff.py` per commit; the WATCHED set
  now includes `cTao`, `CTao` (def VALUES are pinned, not just types), both `explicit`
  theorems, and `Comparator/TaoCollatz/Challenge.lean` is in its search scope. ⚠️ `CTao`'s
  value was changed ONCE, by the judge (the re-pin commit:
  `git log --grep 'JUDGE re-pin' -1`) — run the differ against that commit or later
  (vs the setup commit it reports the `CTao` value change, vs `origin/main` the pins are
  "missing in old"; both are expected).
- **Comparator/ and `formalization.yaml` are judge-owned. Do not touch them.** The
  challenge entry is already planted; there is nothing for a lap to do there.
- **`comparator` CI is red until done — that is the design.** It flips green exactly when
  the campaign succeeds; don't "fix" it. `build` stays green throughout: the Statement.lean
  pin carries a local `set_option warningAsError false in` shield (repo-wide
  `weak.warningAsError` would otherwise error the sorry and jam the pre-commit green-gate).
  Remove the shield together with the `sorry` at discharge — never widen it.
- No `native_decide` (mints axioms; the gate is `--exact`). No new `axiom`. No linter
  silencing without a why-comment.
- **Do NOT optimize constants — but DO report optimizations you notice.** This campaign
  transcribes the proof's constants; the pin has headroom precisely so you never NEED a
  smaller `C`. But extraction walks every witness with the lights on, and if you SEE slack —
  a factor that cancels, a threshold far cruder than its use, a `max` whose second arm is
  never the binder, a lemma invoked with a constant orders looser than what its proof gives —
  that is potentially REAL MATHEMATICS (nobody has ever traced these constants before).
  Write it up in PENDING_WORK.md under `## Optimization observations` (site, file:line, what
  the slack is, estimated effect on `log₁₀ C`), flag `JUDGE-FLAG:` if it looks structural,
  and move on WITHOUT implementing: statements stay frozen, the pin stays, the transcription
  stays faithful. Observations are free; edits are not.
- **A failure to prove `bound ≤` is INFORMATION** — report it (the ladder is bigger than
  mapped, or the map is wrong); `JUDGE-FLAG:`, don't weaken statements and don't inflate
  defs.

### 📌 Orientation for a fresh box

- `c` is DONE and merged (PR #9): `cTao`, `tao_collatz_quantitative_explicit`, and the
  whole `c`-side sibling chain (`c_ladder`, `c_ladder_lower`,
  `tao_collatz_quantitative_spine_of_le`) are in-tree — study them; this campaign is their
  `C`-side mirror.
- The hand-traced map of the tower: `notes/effective-constants.md` on branch
  `effective-constants` (PR #6) — read once with
  `git show origin/effective-constants:notes/effective-constants.md` (bare `git` is correct
  in the box). Trust Lean source over the note wherever they disagree.
- Build: `lake build` (mathlib oleans shared via lake-base; project modules only).
- Report per lap: "step-1 map {done/estimated log₁₀C}; Sec7 n of 22+thresholds, Sec6 n of 8,
  Sec5 n of 37, Sec3 n of 7 C-slots explicit; blockers".
