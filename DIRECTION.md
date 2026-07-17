# DIRECTION — big-C campaign 🔢

*Grind laps READ and OBEY this file; it outranks any handoff. The operator layer (host-side)
is the only writer of the CURRENT DIRECTIVE. Keep reports as "N of M carriers explicit."
`blueprint_rules.md` remains BINDING. Predecessor campaign (pin `c`, PR #9, merged): its
methods are this campaign's playbook; its DIRECTION lives in git history (`git log
--follow DIRECTION.md`).*

---

## CURRENT DIRECTIVE (campaign start, 2026-07-16 evening) — **pin `C` in Lean: discharge `tao_collatz_quantitative_fully_explicit`**

### 🎯 The objective, in one sentence

Discharge the `sorry` on the PRE-PLANTED, JUDGE-OWNED pin (already in
`TaoCollatz/Statement.lean` AND `Comparator/TaoCollatz/Challenge.lean` + `config.json`;
you write the PROOF, never the statement):

```lean
noncomputable def CTao : ℝ := 10 ^ (1000000000 : ℕ)

theorem tao_collatz_quantitative_fully_explicit :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - CTao / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x)
```

`CTao` is a deliberate ROUND UPPER BOUND, not the assembled value. The statement WEAKENS as
`C` grows (`1 - C/(log N₀)^c` only shrinks), so any `C_ladder ≤ CTao` inequality over the
development's assembled constant discharges it. Operator's sizing: the assembled constant is
estimated `≈ 10^(2–3×10⁸)` — dominated by `(2·C1+2)^𝔡 · 40^𝔡` with `𝔡 = mainDecayExponent 3.7
= 3.7 + 6700²·ln 2 + 3 ≈ 3.11×10⁷` — so `10^(10⁹)` has ~3× headroom in the exponent.
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
  theorems, and `Comparator/TaoCollatz/Challenge.lean` is in its search scope. ⚠️ The two
  newest pins were born in this campaign's setup commit — run the differ against that
  commit or later (vs `origin/main` they report "missing in old", which is expected).
- **Comparator/ and `formalization.yaml` are judge-owned. Do not touch them.** The
  challenge entry is already planted; there is nothing for a lap to do there.
- **`comparator` CI is red until done — that is the design.** It flips green exactly when
  the campaign succeeds; don't "fix" it. `build` stays green throughout: the Statement.lean
  pin carries a local `set_option warningAsError false in` shield (repo-wide
  `weak.warningAsError` would otherwise error the sorry and jam the pre-commit green-gate).
  Remove the shield together with the `sorry` at discharge — never widen it.
- No `native_decide` (mints axioms; the gate is `--exact`). No new `axiom`. No linter
  silencing without a why-comment.
- **Do NOT optimize constants.** This campaign transcribes the proof's constants; a smaller
  `C` is explicitly out of scope (the pin has headroom precisely so you never need to).
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
