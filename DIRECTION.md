# DIRECTION — Tier-1 tower tightening 🗼 (`10↑↑63 → ~10↑↑5`)

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

## 🎯 CURRENT DIRECTIVE (operator, 2026-07-18) — burn the ceiling `10↑↑63 → 10↑↑5`; Design B only

**Objective**: re-pin the reported ceiling on the already axiom-clean `C_tao_assembled` at
its honest tower height, using the plan's **Design B batched level-budget calculus**.  End
state: `C_tao_assembled ≤ tenTower 4` proved (take `tenTower 3` if it falls out; report
loudly and settle for `tenTower 5` only after a real fight, blocker written up), `CTao`
re-pinned to `hyperoperation 4 10 (h+1)` at the proved height `h`,
`tao_collatz_quantitative_fully_explicit` re-derived at the new pin, and the comparator
`Challenge.lean` updated in lockstep.

**Operator rulings, recorded — do not relitigate in-lap:**

- **Design B only this run.**  Design A (`tenTowerR` real-topped carrier, the tight
  `10^(10^(10^3010))` headline) is a banked follow-on, not this campaign.  Speed-to-merge
  is the point.
- **Base stays 10.**  Plan §1's bonus-finding analysis is ratified: the tower HEIGHT is the
  base-free content; a smaller base (2, e, ln 4) spends *more* levels to express the same
  value, which polishes slop instead of removing it; and the top exponent's `3 × 1000`
  provenance (`epsBW⁻³` with `epsBW = 10⁻¹⁰⁰⁰`) is decimal-shaped, so base 10 keeps it
  legible.  On completion, record the base-free form **`log log log C ≲ 3010`** + the
  `epsBW⁻³` provenance in the `CTao`/ceiling docstrings (plan §6).

**Phase gate (binding, plan §2)**: build the batched lemma bank in
`Basic/ExplicitConstants.lean` (`prod_le_tenTower_succ`, `sum_le_tenTower_succ`,
`rpow_batch`, `max` passthrough), then the **POC** — re-prove `C_fpLocation ≤ tenTower 2`
(or `3`) (`BigCTower.lean:244`, currently climbs to `tenTower 8`).  A green POC unlocks
Phase 2.  If the POC fights, `JUDGE-FLAG:` with the specific obstruction + `box stuck` —
never grind downstream clusters on a failed gate.

**Phase 2 (plan §3)**: convert bottom-up, cluster by cluster, one commit per node or small
cluster, in the plan's order: Sec5 leaves + first-passage cluster → the cubic-recurrence
node (`encWindowIter_le_tenTower_add_six`: retighten `+6 → +2`) → the Sec6/Sec3 climb
(lines ~740–3256) → `C_tao_assembled_le` restated + the re-pin.  **`check28`** in
`tools/check_blueprint.py` (log/log-log mirror of the full `C_tao_assembled` max-tree,
prints the height, asserts it, mutation-trapped; extend check19; resolve which arm of each
`max` wins in log-space — never assume) lands no later than the ceiling restatement.

## 🔒 Hard rails (plan §4 governs; the differ adjudicates)

- **FROZEN**: every paper pin (the 24 numbered claims / §7 lemmas), `C_tao_assembled`
  (the **definition**), `X_spine`, `tao_collatz_quantitative_assembled`, `tao_collatz`,
  `tao_collatz_quantitative`, `cTao`, `tao_collatz_quantitative_explicit`.
- **INTENTIONALLY MOVED — the only expected differ hits**: `CTao`'s value, the ceiling
  theorem's RHS (`tenTower 62 → tenTower 4`), the constant inside
  `tao_collatz_quantitative_fully_explicit`, and the lockstep `Challenge.lean` copies of
  exactly those.  Run `tools/tao_stmt_diff.py 4dde699 HEAD` every commit: everything else
  character-identical.  The move is monotone-safe (smaller `C` ⟹ strictly stronger
  theorem) — that licenses these surfaces and nothing else.
- **`TaoCollatz/` stays sorry-clean (0) on every commit.**  This campaign tightens; it
  never adds a `sorry` and never weakens a statement.  A cluster that cannot be tightened
  keeps its old bound (the old lemmas remain valid) — worst case the final height is
  looser, never broken.
- **Never evaluate a tower numeral** (`norm_num [CTao]`, `decide`, kernel reduction of the
  numeral — hangs; `native_decide` — mints axioms, banned).  Log-arithmetic + monotonicity
  only, as check17/check19 do.  Local justified `maxHeartbeats` bumps on one declaration
  only.
- **Axioms**: `#print axioms` on both headlines + `fully_explicit` = exactly
  `[propext, Classical.choice, Quot.sound]` at every report point.
- **Comparator**: update `Challenge.lean` in lockstep with the re-pin; run
  `scripts/comparator-probe` locally and require a **non-zero printed closure size** (an
  empty walk passing green is the known failure mode).  `build` + `comparator` CI green
  before the campaign reports done.

## 🛑 Stop discipline

Self-stop cannot fire on this repo (the 8 comparator `Challenge.lean` stubs at the root
are sorry-by-design), and `--forever` is not passed — **`box stuck` is the governed exit
and must stay alive**.  The operator stops the run when the end state above is green
(report it loudly in the lap log + HANDOFF), or on a `JUDGE-FLAG`.  `--max-duration` is
the backstop.

## 📝 Report per lap

"tier1: calculus {n lemmas}/POC {state}; clusters {k}/{total} converted; proved ceiling
tenTower {h}; differ {clean/expected-hits-only}; sorries 0; blockers".
