# DIRECTION — effective-constants campaign 🔢

*Grind laps READ and OBEY this file; it outranks any handoff. The operator layer (host-side)
is the only writer of the CURRENT DIRECTIVE. Keep reports as "N of M carriers explicit."
Context: `notes/effective-constants.md` on the `effective-constants` branch (PR #6) is the
hand-traced map this campaign formalizes. `blueprint_rules.md` remains BINDING.*

---

## CURRENT DIRECTIVE (campaign start, 2026-07-16) — **pin `c` in Lean: kernel-certify an explicit exponent for Theorem 3.1**

### 🎯 The objective, in one sentence

Produce a theorem

```lean
theorem tao_collatz_quantitative_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x)
```

**appended to `TaoCollatz/Statement.lean`** — ONE trusted file, because the trusted base is
whatever a stranger must read in full, and one small file is the smallest honest version of
that (the same logic that puts anchors and headlines in a single `Challenge.lean`). Provenance
is a docstring's job, not a file boundary's. `cTao : ℝ` is an explicit `noncomputable def` in
that same file (symbolic in
`Real.log 2` — e.g. `1 / (640000000 * Real.log 2)` if step 1 confirms it), axiom-clean
(`[propext, Classical.choice, Quot.sound]`), with `C` still existential. The docstrings carry
the provenance split: the two existing headlines are the paper's (Thm 1.3 / Thm 3.1); the
explicit theorem + `cTao` are OUR augmentation — the paper gives `∃ c` and Remark 1.4 only a
shape. Say that plainly in the docstring. Nobody has ever published an explicit exponent for
Tao 2019 Thm 3.1 (MO 341570, open since 2019). `C` is NOT in scope for this campaign (blocked
history: `notes/effective-constants.md`; the rate-free lemma is already fixed on this branch).

### 🥇 STEP 1 — route-decisive, do FIRST: lower-bound the `c8` and `cs` branches

The headline's `c` is `min (min c7 c8) cs` (`stabilization`, `Sec5/Stabilization.lean:2752`)
then `min cb cs` again at `descentProb_ladder` (`Sec3/Reduction.lean:303`). The traced value
`1/(640_000_000·ln 2)` is the **c7 branch only**. Before ANY def is written, trace the c8
branch (`first_passage_approx`, `Sec5/ApproxFormula.lean:3218`) and the cs branch
(`approxMainTerm_to_Z` ← `Iy_count_ratio`/`perNTerm_eval`, `Stabilization.lean:2487–2620`)
down to numerals, and determine a rational/symbolic `c₀` with `c₀ ≤` **every** branch.
**The final `cTao` value is chosen from this step's output, not from the note.** If either
branch comes out below `1/(640_000_000·ln 2)`, the smaller value wins — report it, don't
force the note's number. Deliverable: a `JUDGE-FLAG:` in PENDING_WORK.md with the three
branch values (file:line per hop) for operator sign-off on the `cTao` definition.
**Do not proceed to step 3's def until that sign-off.**

### 🥈 STEP 2 — the mechanical pattern (sibling + delegate), bottom-up

For each constant-carrying lemma on the `c`-path (scope ≈ Sec5's 37 carriers + the Sec3
glue: `descentProb_ladder` :303 → `descent_whp` :392 → `window_bad_sum` :558 →
`tao_syracuse_quantitative_sum` :669 → `tao_syracuse_quantitative` :978 →
`tao_collatz_quantitative_spine` :1331):

1. Name its `c`-witness as a `noncomputable def` (e.g. `c_valSum : ℝ := ...`), keeping it
   **symbolic** (`Real.log 2` stays `Real.log 2`; the repo precedent is
   `alpha : ℝ := 1.001`, `FirstPassage.lean:116`, ~290 uses).
2. Add a sibling lemma `foo_explicit` stating the SAME content with the def in the `c` slot
   (only the `c` slot — `C` and thresholds stay `∃`).
3. Re-prove the ORIGINAL `∃`-lemma as `⟨c_foo, ...⟩` delegating to the sibling. **The
   original statement stays byte-identical** — the differ will check.

You only ever need **lower** bounds `c₀ ≤ c` (the headline is monotone in `c` for
`Real.log N₀ ≥ 1`, i.e. `N₀ ≥ 3`; the window `2 ≤ N₀ < 3` is absorbed by choosing `C ≥ 1`
so the bound is `≤ 0 ≤ logProb`). So min-trees collapse via `le_min` and you never need
branch-vs-branch comparisons beyond step 1's chosen `c₀`. Comparisons against numerals:
`Real.log_two_gt_d9` / `Real.log_two_lt_d9` (already used ~20× in-repo).

**Cost center warning:** `positivity` currently discharges `0 < c` at ~58 sites from the
`obtain`ed hypothesis. After de-existentialization those become `0 < c_foo` goals on a
`noncomputable def` — prove ONE `c_foo_pos` lemma per def and use it; do not let laps grind
`positivity` failures site by site.

### 🥉 STEP 3 — the headline + `cTao`, appended to `Statement.lean`

Append to `TaoCollatz/Statement.lean`: the `cTao` def (value from step 1's sign-off) + the
`tao_collatz_quantitative_explicit` theorem, proved by delegation to the explicit spine.
**Append-only**: the two existing headline statements stay byte-identical (differ-watched);
update the file's header comment to describe the three-statement surface and which are the
paper's vs ours. The new docstring says plainly: *this statement is our augmentation, beyond
the paper* (the paper gives `∃ c`; Remark 1.4 gives only a shape). `cTao`'s body must be pure
Mathlib vocabulary (it will be re-declared verbatim in `Comparator/TaoCollatz/Challenge.lean`
at step 4), so the file's statement-import surface does not grow.

### 🏁 STEP 4 — OPERATOR-GATED (do not do in a grind lap)

Comparator additions (declare `cTao` + the third theorem in
`Comparator/TaoCollatz/Challenge.lean`, add to `config.json` `theorem_names`) and the PR #6
note update. These change the public trusted surface → Trevor/judge reads first. Flag
readiness in PENDING_WORK.md and stop.

### 🔒 Hard rails

- **Never edit a ratified statement.** The WATCHED set (`tools/tao_stmt_diff.py`) binds:
  both `Statement.lean` headlines, `stabilization`, `fine_scale_mixing`,
  `first_passage_approx`, `first_passage_nonescape`, the §7 set. Sibling + delegate ONLY;
  the original `∃`-forms stay byte-identical. If a delegation seems to force a statement
  change → `JUDGE-FLAG:`, stop that thread.
- **`c` slots only.** `C` and `x₀`/threshold slots stay existential everywhere. (Thresholds
  move `C`, not `c` — and `C` is out of scope.)
- **Lower bounds only; never claim `=`.** `cTao ≤ c_actual` is the theorem; equality across
  the min-tree is neither needed nor established.
- **Keep every def symbolic.** No decimal approximations of `1/ln 2` anywhere in a def or
  statement. `π²/6` stays symbolic if encountered (it lives on the `C` side; you shouldn't
  meet it).
- **Axiom gate**: `#print axioms tao_collatz_quantitative_explicit` must be exactly the
  standard three at campaign end; `lean-axiom-gate` per lap as usual.
- **A failure to prove `c₀ ≤ branch` is INFORMATION** (the branch is smaller than traced) —
  report it, lower `c₀` via JUDGE-FLAG; do not weaken a statement to force it.

### 🚧 Forbidden drift

- Do NOT touch `Sec7/`, `Sec6/`, or anything on the `C`-side subtree (`mainZ_bound`'s `C`,
  `fine_scale_mixing`). The `c`-path is Sec5/Sec3 only.
- Do NOT modify `Comparator/` or `formalization.yaml` in a grind lap (step 4 is gated).
- Do NOT "improve" constants along the way (no tightening `1/400`, no dropping the `/20`).
  This campaign transcribes the proof's constants; optimization is explicitly out of scope.
- Do NOT touch `notes/effective-constants.md` (it lives on the PR #6 branch, not here).

### 📌 Orientation for a fresh box

- The blocker fix (explicit-threshold lemmas in `Sec7/Monotone.lean`) is already on this
  branch — `hold_weight_expect` no longer routes through rate-free limits. That was the
  `C`-side defect; it does not affect the `c`-path, but it's why the D3 amendment reads the
  way it does.
- The hand-traced map of the whole tower (values, file:line, min-trees):
  `notes/effective-constants.md` on branch `effective-constants` (PR #6). Read it with
  `git show effective-constants:notes/effective-constants.md` — bare `git`, which is the
  correct form in the box (the host's git-door wrappers aren't on the box PATH; see
  box-context). Read it once before step 1; trust the Lean source over the note wherever
  they disagree.
- Build: `lake build` (mathlib oleans are shared via lake-base; project modules only).
- Report per lap: "N of ~37 Sec5 carriers explicit; Sec3 glue M of 6; step-1 branch values
  {c7 ✓, c8 ?, cs ?}".
