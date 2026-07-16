# HANDOFF — effective-constants campaign, lap 1–2 (2026-07-16)

**Read `DIRECTION.md` first — it is the directive.** `PENDING_WORK.md` has the step ledger
and the step-1 JUDGE-FLAG.

## State

- Branch `explicit-rate-hold-weight`, all work committed, full build green (3327 jobs),
  `tao_stmt_diff.py` ✓ on every commit (31/31 watched statements byte-identical),
  `lean-axiom-gate --exact` ✓ on headline + new siblings.
- ✅ **STEP 1 done** — c8/cs branches traced to numerals (JUDGE-FLAG in PENDING_WORK.md).
  Finding: c8 *contains* c7 as a sub-branch (via `approx_passtime_window` obtaining
  `first_passage_nonescape`), every other leaf is ≥ 1/5, so the headline's `c` IS
  `1/(640000000·log 2)` exactly. Proposed `cTao := 1 / (640000000 * Real.log 2)` —
  **awaiting operator sign-off** (DIRECTION's do-not-proceed gate for step 3).
- ✅ **STEP 2 done** — the whole `c`-path is de-existentialized, sibling + delegate,
  bottom-up: Prob/Syracuse leaves → Sec5 (c7, c8, cs chains) → Sec3 glue. Def tree in
  PENDING_WORK.md. Top of the tower: `tao_collatz_quantitative_spine_explicit`
  (`Sec3/Reduction.lean`) with witness `c_ladder`.

## Next lap

1. If the operator has signed off the JUDGE-FLAG: **STEP 3** — append to
   `TaoCollatz/Statement.lean` (append-only; two existing headlines byte-identical):
   `noncomputable def cTao : ℝ := 1 / (640000000 * Real.log 2)` + the
   `tao_collatz_quantitative_explicit` theorem per DIRECTION's shape, proved by delegation
   to `tao_collatz_quantitative_spine_explicit`. The work needed: `cTao ≤ c_ladder`
   (chain of `le_min` + `norm_num` + `Real.log_two_gt_d9`/`log_two_lt_d9`; every leaf ≥
   `1/(640000000·log 2)`, mins collapse), then rpow-exponent antitonicity to move the bound
   (statement is monotone in `c` for `log N₀ ≥ 1`; the window `2 ≤ N₀ < 3` is absorbed by
   `C ≥ 1` so the bound is `≤ 0 ≤ logProb` — see DIRECTION). `#print axioms` must be the
   standard three.
2. If not signed off: prove the comparison lemma `cTao_le_c_ladder` as a standalone
   (named per step 1's value) WITHOUT touching Statement.lean, so step 3 becomes a
   5-minute append; also pre-verify `c_valSumTail = 1/(640000000·Real.log 2)` as a lemma
   (`unfold` chain + `norm_num [Real.log_pos]` on the min collapses — needs
   `finalDecay`/`linearDecay` min-collapse facts `1/32000000 ≤ Real.log 2` etc. via
   `Real.log_two_gt_d9`).
3. STEP 4 stays OPERATOR-GATED (comparator + PR #6 note) — flag readiness only.

## Gotchas hit (so you don't re-hit them)

- `set_option maxHeartbeats ... in` and `open Classical in` bind the NEXT declaration only —
  inserting a def between them and their theorem silently reassigns them (build breaks at
  200k heartbeats or on `Decidable ¬goodTuple`). Keep such modifiers glued to their theorem.
- A `/-- docstring -/` must immediately precede its declaration (`set_option` in between is
  a parse error); two doc comments in a row is a parse error too.
- Delegations must be inserted AFTER the sibling's body but BEFORE the next consumer —
  in-file consumers (`tao_syracuse` at `Reduction.lean`) reference the original names.
- `rw [show c_def = <value> from rfl]` right after `:= by` is the cheap way to reduce a
  def-carrying goal to the original literal goal; `set x := c_def with h` converts obtained
  explicit hypotheses back to the original opaque-variable names so bodies stay verbatim.
- `noncomputable` is required even for `def c : ℝ := 1/400` (Real division).
