# JUDGE HANDOFF — Tier-1 tower tightening 🗼⚖️ (written 2026-07-18 15:40 EDT, run live)

*For the operator/judge seat (a HOST session — Ren or any successor model).  This doc is the
judge's entry point; laps never read or need it.  It was written UNTRACKED while lap 1 was
mid-flight (host commits into a shared live tree risk staging/lock contention) — commit it
to the branch at the next quiet boundary (run halted or between laps).*

## The campaign in three sentences

`BigCTower.lean` proves `C_tao_assembled ≤ tenTower 62` with ~59 levels of per-operation
rounding slop; the honest height is ≈ 3.  A campaign pin `CTao := hyperoperation 4 10 10`
(= `10↑↑10`) was planted as a shielded `sorry` in `Statement.lean` (Challenge.lean in
lockstep), and the treadmill is grinding the Design-B batched calculus to prove
`C_tao_assembled ≤ tenTower 4`-ish and discharge it.  The run self-stops via the host's
`--done-when sorry-free:TaoCollatz` gate the lap after discharge; comparator CI (required
check) flips green at exactly that moment, which is what makes PR #11 mergeable.

## State at handoff

- **Run**: launched by Trevor 2026-07-18 ~15:33 EDT —
  `lean-treadmill tao-collatz-tier1 --done-when sorry-free:TaoCollatz --max-duration 12h
  --review-every 0` (+ reflect 0; status line shows `review/reflect:0/0`, pure grind,
  fable/low — the new grind defaults, `bin` `d234c31`).  Backstop expires ~03:34 EDT.
- **Worktree**: `~/src/tao-collatz-tier1`, branch `tier1-tower-tightening`, HEAD `b7825fc`
  (the plant).  Main checkout `~/src/tao-collatz` is on `main` @ `4dde699` for Trevor's
  parallel work — never point the treadmill there.
- **PR**: [#11](https://github.com/gotrevor/tao-collatz/pull/11), **draft**, comparator
  RED by design until discharge.
- **Binding docs on the branch**: `DIRECTION.md` (the directive; ONE OWNER = this seat,
  host-side — laps may not write it), `TIER1-TOWER-TIGHTENING-PLAN.md` (the spec),
  `HANDOFF.md` (lap-0 orientation).
- **Baseline facts**: differ vs `4dde699` = exactly one watched change (`CTao` value, the
  judge-made plant); `tools/tao_stmt_diff.py b7825fc HEAD` must print **39/39** for the
  entire campaign.  `TaoCollatz/` census = 1 (the pin).  Build green at plant (8600 jobs).
- **Standing rulings** (recorded in DIRECTION; do not relitigate): Design B only; base
  stays 10; `CTao` never moves again this campaign (ceiling theorem carries the honest
  height); discharge happens LAST, after `check28`; legibility ruling (Dvořák 16:30) — the
  calculus bank is a human-read surface.

## Mid-run duties

- **Watch**: `lean-treadmill status tao-collatz-tier1` (read-only, allowlisted).  The
  reaper handles idle-hung boxes.  Trevor stops/extends runs, not you.
- **`box stuck` / `JUDGE-FLAG:`** (expected causes: the POC gate fights; a cluster
  resists; something in the plan is wrong): read `PENDING_WORK.md`'s flag + the lap log
  (`~/.local/state/lean-treadmill/tao-collatz-tier1.jsonl`), rule on it, update
  `DIRECTION.md` (yours to write — commit at a quiet moment), Trevor relaunches.
- **Early discharge** (run halts, ceiling still > `tenTower 4`, no blocker write-up):
  a DIRECTIVE violation, treat as a JUDGE-FLAG — the artifact is still valid (see below),
  but the honest-height work was skipped; decide accept-vs-relaunch with Trevor.
- **Height stalls above 4 but ≤ 9, WITH a blocker write-up**: acceptable quick-burn
  outcome (`10↑↑10` still merges); judge decides accept vs extend.

## Ratification checklist (the run has halted itself)

1. `lean-sorry -c TaoCollatz` = **0**, and Statement.lean's `set_option warningAsError
   false in` shield is GONE (removed together with the sorry; Challenge.lean's file-level
   one stays — it covers the 8 sorry-by-design stubs).
2. `tools/tao_stmt_diff.py b7825fc HEAD` = **39/39**.
3. Axioms: `tao_collatz_quantitative_fully_explicit` + spot-check both headlines =
   exactly `[propext, Classical.choice, Quot.sound]`.  Gotcha: `lean-axiom-gate` needs
   `-i TaoCollatz.Statement` (the sourceless `Comparator` lib name chokes the default).
4. `tools/check_blueprint.py`: ALL checks incl. the new **check28** (log/log-log mirror of
   the `C_tao_assembled` max-tree, asserts the height, mutation-trapped).  Read check28's
   ASSERT line, not its prose — the assert IS the claim.
5. The ceiling theorem records the honest height; the base-free docstring landed
   (`log log log C ≲ 3010` + `epsBW⁻³` provenance, plan §6).
6. **Legibility read** of the calculus bank + a sample converted cluster (the Dvořák
   ruling): named lemmas, docstrings, no copy-paste sprawl.  This is a human read, not
   a grep.
7. Comparator CI green on PR #11 (the external "done"); `build` green.
8. Then: un-draft #11 → **Trevor merges** (squash; auto-merge on green is enabled repo-
   wide).  Draft the Zulip follow-up (constants story: `10↑↑63 → 10↑↑10` pinned, honest
   ceiling `10^(10^(10^3010))`) — **Ren drafts, Trevor posts.**  Update the KB todo line
   (`todos/README.md`, "Pin `c`/`C`" entry) + `projects/tao-collatz.md`.  Worktree
   cleanup after merge is Trevor's call.

## Context pointers

- KB: `projects/tao-collatz.md` (reception + campaign history), `projects/lean-tooling.md`
  (treadmill mechanics incl. `--done-when`), todo `open/tao-collatz-pin-constants-lean.md`.
- The retired predecessor campaigns (big-C pin → assembled big-C) and their rulings:
  `git log --follow DIRECTION.md` on this branch — read before inventing any new doctrine;
  most traps (numeral evaluation, statement erosion, false-green instruments) already have
  rulings.
- Related open todos that touch this repo: arXiv v6/v7 re-pin decision (Lemma 7.9!),
  backfill pin provenance, post-public follow-ups — none block this campaign.
