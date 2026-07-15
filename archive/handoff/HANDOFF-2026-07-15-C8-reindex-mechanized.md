# Handoff: C8 affine reindex — mechanical layer + orbit estimate DONE; 3 analytic holes remain

**Date**: 2026-07-15. **Branch** `main`, **HEAD `c78f29a`**. Build 🟢 green (full `lake build`, 3322
jobs, pre-commit verified each commit). Tree clean.
**Read `DIRECTION.md` first** (CURRENT DIRECTIVE outranks this). Campaign: C10 ✅ → C8 (pin ✅) →
C7 (prove ✅) → **C8 close (IN PROGRESS)** → C9.

## What this session did — drove the route-decisive C8 leg `first_passage_affine_reindex`

The (5.8) affine reindex went from **one bare `sorry`** to a fully-assembled proved triangle whose
ENTIRE mechanical layer + the shared orbit estimate are proved axiom-clean. Commits (all green):
- `92df3b7` — **`passTime_stepback`** (FirstPassage.lean) + **`firstPass_event_stepback_subset`**: the
  EXACT (5.17) step-back event identity. Finding: the `T_x`/`Pass`/oddness half of `Eprime(syr^{n−m₀}N)`
  is EXACT given `T_x N = n` (no-early-passage is automatic). Only the `E'` *size* window is analytic.
- `32f393a` — **decomposed `first_passage_affine_reindex`** via the `steppedMid` diagonal bridge into a
  proved triangle: legs `first_passage_stepback_reduce` + `first_passage_truncation_reindex`.
- `0a9f2db` — reindex ENGINE: **`map_mask_tsum`/`map_mask_tsum_toReal`** (ℝ≥0∞ pushforward reorder) +
  **`approxMainTerm_eq_source`** (EXACT — eliminates the target-`M`/pushforward layer to pure source masses).
- `c5e1ef2` — **`goodTuple_finite`** + **`entry_le_pre`** (good tuples are a finite set; summability).
- `844a157` — **`steppedMid_le_approxMainTerm`** (axiom-clean): the EXACT half of (5.18) — full `ā↔N`
  reorder + diagonal domination. Helper `expect_indicator_toReal`.
- `923bbe1` — wired the domination into `first_passage_truncation_reindex`: the abs collapses to the
  one-sided nonneg `approxMainTerm − steppedMid`, pinned as **`truncation_error_bound`** (the sole hole).
- `459ef67` — **`syr_iterate_good_bracket`** = the (5.13)/(5.14) orbit estimate
  `3^n N/2^{2n+L} ≤ Syr^n N ≤ 3^n N/2^{2n−L}+3^n` (`L=log^{0.6}x`). Chain: `syr_iterate_bracket`,
  `valSum_dev_on_good`, `two_rpow_valSum_bounds`.
- `028817e` — **`syr_iterate_good_bracket'`**: same in clean `(3/4)^n N·2^{∓L}` form. Bridge `two_rpow_two_mul`.
- `c78f29a` — **`two_rpow_slack_le_exp`**: `2^{log^{0.6}x} ≤ exp(log^{0.7}x)` (orbit slack fits E' window).

`first_passage_affine_reindex` + `first_passage_approx` (C8) `#print axioms` = trust base + `sorryAx`
(the isolated holes only). All new lemmas above are `[propext, Classical.choice, Quot.sound]`.

## C8 remaining = 3 named sorries (all analytic; full plans in PENDING_WORK.md top)
1. **`truncation_error_bound`** (`ApproxFormula.lean`, ~:1130) — the (5.19) crux. `approxMainTerm −
   steppedMid ≤ C log^{-c}x` = `∑_n ∑'_N P N·#{truncation ā ≠ valVec : good ā ∧ Aff N (n−m₀)ā ∈ E'}`.
   The mechanical reorder/domination is DONE; this is the genuine COUNTING of rounding coincidences
   landing in `E'`. Needs the `E'` size window (from the orbit estimate below) then a count bound.
2. **`first_passage_stepback_reduce`** (`ApproxFormula.lean`, ~:1020) — the (5.17) event reduction
   `|firstPassMid − steppedMid|`. Forward inclusion EXACT (`firstPass_event_stepback_subset` ✅);
   remaining = reverse inclusion + `E'` size window + nested `𝒜⁽ⁿ⁰⁾⊂𝒜⁽ⁿ⁻ᵐ⁰⁾`.
3. **`passtime_window_inner`** (`ApproxFormula.lean`, :677) — (5.16) window term, `{passes ∧ T_x∉Iy}`,
   integral test reusing C7's `classMass`/`windowMass`/`intTest_*` in `Sec5.FirstPassage`. Most
   self-contained (C7 machinery is proved) — a good pick if the reindex holes stall.

Then C9 = `stabilization` (`FirstPassage.lean:~1399`, consumes C10 ✅ + C8).

## Next move (recommended)
Both reindex holes (1,2) need the **`E'` size window**: `syr^{n−m₀}N ∈ [exp(−log^{0.7}x)(4/3)^{m₀}x,
exp(+…)…]`. The orbit estimate + slack lemma are built; the remaining piece is the **`IyLo/IyHi`
interval algebra** turning `n∈Iy ⟹ (3/4)^n N ≈ x`.
⚠️ **VERIFY against Tao pp.22-24 BEFORE formalizing this interval step.** My scratch derivation hit a
`y^{α−1}` (= x^{~0.001}) spread that naively looks WIDER than `exp(log^{0.7}x)`; the window is tied to
`n∈Iy` AND `N∈[y,y^α]` *jointly* and I don't yet fully trust the exponent bookkeeping. Read the actual
(5.13)–(5.16) argument (or hand the NL to Aristotle for an independent formalization cross-check) rather
than risk a wrong lap. If it stalls, `passtime_window_inner` (hole 3) is the safe parallel thread.

## Rails / notes
- **Do NOT edit ratified pins** (`approxMainTerm`, `Eprime`, `Iy`, `firstPassMid`, the C8 statements),
  or `steppedMid`/the RATIFY-C8 defs. Decompose *below* them only. Never set `\leanok` yourself.
- Watched statements (`fine_scale_mixing`/`stabilization`) + all ratified pins UNTOUCHED.
- Axiom-check recipe: write `TaoCollatz/ZZ_ax.lean` importing the module with `#print axioms <name>`,
  `lake env lean` it, then `rm -f` (don't leave it — breaks the build tree).
- `git-safe` at `/Users/gotrevor/personal/bin/git-safe` (`export PATH="$HOME/personal/bin:$PATH"`).
- Edit gotcha hit twice this session: an `Edit` whose `old_string` includes a `/-- … -/` docstring
  opener will DROP it if the `new_string` omits it → "unexpected token" / "expected 'lemma'". Keep the
  docstring line in `new_string`, or place `open Classical in` BEFORE the `/--`, never between it and
  the theorem.
- Auto-memory `lean-linarith-decimal-rpow-poison` still applies; `zero_le _` fails for ℝ≥0∞ (use `zero_le'`).
- **Work report: 3 sorries + 0 orange nodes** in C8 (`truncation_error_bound`,
  `first_passage_stepback_reduce`, `passtime_window_inner`) + C9 (`stabilization`, 1 sorry).
