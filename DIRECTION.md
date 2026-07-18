# DIRECTION — Tier-1 tower tightening 🗼 (`10↑↑63 → 10↑↑10` pin; honest ceiling `~10↑↑4`)

*Grind laps READ and OBEY this file; it outranks any handoff.  `blueprint_rules.md` remains
BINDING.  `TIER1-TOWER-TIGHTENING-PLAN.md` (this branch) is the campaign spec — read it in
full before any lap-1 work; where this file is terse, the plan governs.  The predecessor
campaign (assembled big-C, ratified 2026-07-17, merged as PR #10) is done; its DIRECTION
lives in git history (`git log --follow DIRECTION.md`).*

> **🔒 ONE OWNER (standing ruling, 2026-07-17).**  This file has exactly one writer: the
> operator/judge layer (host-side).  No lap — grind, review, reflection, or altitude — may
> write DIRECTION.md.  The treadmill governor's general "altitude laps own DIRECTION.md"
> rule is **overridden here** and does not apply to this repo.  A lap that believes the
> directive is wrong records the argument in `PENDING_WORK.md` as a `JUDGE-FLAG:` and
> stops the loop with `box stuck`.

---

## 🎯 CURRENT DIRECTIVE (operator, 2026-07-18) — discharge the planted `10↑↑10` pin at the honest height; Design B only

**The pin is already planted (judge, 2026-07-18).**  `Statement.lean` carries
`CTao := hyperoperation 4 10 10` (= `10↑↑10`) with `tao_collatz_quantitative_fully_explicit`
as a shielded `sorry`, and `Comparator/TaoCollatz/Challenge.lean` carries the same value in
lockstep.  **Comparator CI is RED until the pin is discharged — that is the design; never
"fix" it and never touch `Comparator/`.**  You write the PROOF, never these statements.

**Objective**: prove `C_tao_assembled ≤ tenTower 9` — and the *honest* target is
`tenTower 4` (take `3` if it falls out) — via the plan's **Design B batched level-budget
calculus**, then discharge the pin.  Its `10↑↑63` predecessor proof is on main at
`4dde699`; the ceiling climb you are tightening is `BigCTower.lean`.

**Work order (the discharge is LAST — this is load-bearing, see Stop discipline):**

1. **Calculus bank** in `Basic/ExplicitConstants.lean`: `prod_le_tenTower_succ`,
   `sum_le_tenTower_succ`, `rpow_batch`, `max` passthrough (plan §2 Design B).
2. **POC gate (binding)**: re-prove `C_fpLocation ≤ tenTower 2` (or `3`)
   (`BigCTower.lean:244`, currently climbs to `tenTower 8`).  Green POC unlocks step 3.
   If it fights: `JUDGE-FLAG:` + `box stuck` — never grind downstream on a failed gate.
3. **Convert bottom-up**, cluster by cluster, one commit per node/cluster, in the plan §3
   order (Sec5 leaves → cubic-recurrence node `+6 → +2` → Sec6/Sec3 climb → the ceiling
   theorem restated at the proved height).
4. **`check28`** in `tools/check_blueprint.py`: log/log-log mirror of the full
   `C_tao_assembled` max-tree, prints the height, asserts it, mutation-trapped (extend
   check19; resolve which arm of each `max` wins in log-space — never assume).
5. **Discharge the pin**: remove the `sorry` AND its `warningAsError` shield together in
   the final commit.  The host's `--done-when sorry-free:TaoCollatz` gate then ends the
   run.  Discharging early at a slop height (e.g. a quick `≤ tenTower 8` proof) is a
   DIRECTIVE violation: it halts the run with the honest height unreached.

**Operator rulings, recorded — do not relitigate in-lap:**

- **Design B only this run.**  Design A (`tenTowerR` real-topped carrier, the tight
  `10^(10^(10^3010))` headline) is a banked follow-on.
- **`CTao` does not move again.**  It stays `10↑↑10` (the comparator-pinned public bound);
  the *ceiling theorem* + `check28` + docstrings record the tighter honest height.  Any
  later re-pin tighter is a judge call after this campaign, not lap work.
- **Base stays 10.**  The height is the base-free content; a smaller base spends more
  levels on the same value; the top exponent's `3 × 1000` provenance (`epsBW⁻³`,
  `epsBW = 10⁻¹⁰⁰⁰`) is decimal-shaped.  On completion, record the base-free form
  **`log log log C ≲ 3010`** + the `epsBW⁻³` provenance in the ceiling docstrings (plan §6).
- **Legibility is a requirement, not a nicety** (Dvořák, Zulip 2026-07-18: *"I love
  reading Lean code that is well-organized and elegant"*).  The calculus bank and the
  converted climb are human-read surfaces.  Named lemmas, clean statements, docstrings on
  the bank, no copy-paste sprawl.

## 🔒 Hard rails (plan §4 governs; the differ adjudicates)

- **FROZEN**: every paper pin (the 24 numbered claims / §7 lemmas), `C_tao_assembled`
  (the **definition**), `X_spine`, `tao_collatz_quantitative_assembled`, `tao_collatz`,
  `tao_collatz_quantitative`, `cTao`, `tao_collatz_quantitative_explicit`, **and the
  planted pin itself** (`CTao`'s new value + the `fully_explicit` statement, both files).
- **Differ**: run `tools/tao_stmt_diff.py <plant-commit> HEAD` every commit (the plant
  commit is the one titled "plant the Tier-1 campaign pin"; `git log --grep 'plant the
  Tier-1'`).  It must print **39/39 character-identical** for the entire campaign — the
  engine lemmas you tighten in `BigCTower.lean` are not on the watched surface; nothing
  watched moves again.
- **`TaoCollatz/` carries exactly ONE `sorry`** (the planted pin) until the final commit,
  which takes it to 0.  Never add another; never weaken a statement.  A cluster that
  cannot be tightened keeps its old bound — worst case the final height is looser, never
  broken.
- **Never evaluate a tower numeral** (`norm_num [CTao]`, `decide`, kernel reduction of the
  numeral — hangs; `native_decide` — mints axioms, banned).  Log-arithmetic + monotonicity
  only, as check17/check19 do.  Local justified `maxHeartbeats` bumps on one declaration
  only.
- **Axioms**: at discharge, `#print axioms` on `tao_collatz_quantitative_fully_explicit`
  (and spot-check the headlines) = exactly `[propext, Classical.choice, Quot.sound]`.
- **This branch merges via PR only** (main is protected; `build` + `comparator` required).
  Commit + push on `tier1-tower-tightening`; the PR flips green exactly when you are done.

## 🛑 Stop discipline

- **Primary: `--done-when sorry-free:TaoCollatz`** — the host checks it after every lap
  and halts the run when the pin is discharged.  Combined with "discharge LAST", the gate
  fires exactly at campaign completion.
- The box-side repo-root sorry gate stays blocked by the Comparator challenge stubs
  (sorry-by-design) — irrelevant here; the host-side `--done-when` is scoped to
  `TaoCollatz/` and independent of it.
- `box stuck` is the escalate lane (POC failure, unanswered `JUDGE-FLAG`).  `--forever`
  must NOT be passed.  `--max-duration` is the backstop.

## 📝 Report per lap

"tier1: calculus {n lemmas}/POC {state}; clusters {k}/{total} converted; proved ceiling
tenTower {h}; differ 39/39 {yes/no}; sorries {1|0}; blockers".
