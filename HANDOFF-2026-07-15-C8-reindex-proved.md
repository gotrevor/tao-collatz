# Handoff: C8 false summit caught + re-pinned + reindex crux PROVED axiom-clean

**Date**: 2026-07-15. **Branch** `main`, **HEAD `830419a`**. Build 🟢 green (full `lake build`, 3322
jobs; pre-commit verified each commit). Tree clean.
**Read `DIRECTION.md` first** — its CURRENT DIRECTIVE (deep-reflection block 2026-07-15) outranks this.
Campaign: C10 ✅ → C8 (pin ✅) → C7 (prove ✅) → **C8 close (IN PROGRESS)** → C9.

## What this lap did (deep reflection → route correction → crux proved)

This was a deep-reflection lap that found a **route-decisive defect** and drove it to closure.

1. **Caught a C8 false summit.** The ratified `approxMainTerm` (v1) rendered Tao's (5.8) reindex on
   the **ℕ-truncating** `Aff` with **no divisibility guard**. Tao's reindex is EXACT (Lemma 2.1) on
   the (5.18) congruence `M ≡ F_{n−m₀}(ā) mod 3^{n−m₀}`; under the floor, `Aff N k ā` depends on `ā`
   essentially only through `|ā|`, so exponentially-many good tuples collapse into `E'` and the old
   closing hole `truncation_error_bound` was **FALSE**. Evidence: source read pp.22–25
   (`papers/literature-review.md` §5, HOLE #4) + numeric probe `tools/sandbox/tao_c8_truncation_probe.py`
   (truncating count = thousands, e.g. k=8,N=101 → 19135; exact-guard count = 0–3).
2. **Re-pinned `approxMainTerm` (RATIFY-C8-v2, `8dcabb2`)** to the exact affine event
   `{N : 3^{n−m₀}N + Fnat = M·2^{a_{[1,n−m₀]}}}`.
3. **PROVED the reindex crux `approxMainTerm_eq_steppedMid` axiom-clean (`dbdd742`)** —
   `[propext, Classical.choice, Quot.sound]`. With the guard, `valVec_unique` (Lemma 2.1) +
   `Eprime`-oddness + `syr_iterate_key` collapse the `(ā,M)` double sum to `steppedMid`'s diagonal, so
   `approxMainTerm = steppedMid` EXACTLY. Proof shape: `hEq` (fold the outer `if` into the `N`-sum) →
   reorder `∑'_ā∑'_M∑'_N → ∑'_N` (`ENNReal.tsum_comm` ×2) → per-`N` `hforce` (guard+odd ⇒ ā=valVec,
   M=Syr^kN) + `tsum_eq_single` ×2 → `.toReal` pull (`ENNReal.tsum_toReal_eq`, forward).
   `truncation_error_bound` is now ALSO axiom-clean (consumes the proved reindex).
   `steppedMid_le_approxMainTerm` is now `le_of_eq` of the equality.

Also this lap: full reflection synthesis (STATUS/DIRECTION/PENDING/lit-review §5 refreshed; T5
registered). The host ratified the finding into `blueprint_rules.md` (new "numeric trap" rule citing C8).

## State: 5 sorries + 0 orange nodes

- `Statement.lean:24,31` — the two headline stubs (Thm 1.3 / Thm 3.1), frozen; discharge when C8/C9/C6 land.
- `Sec5/FirstPassage.lean:1399` — C9 `stabilization` (Prop 1.11), consumes C10 ✅ + C8.
- `Sec5/ApproxFormula.lean:808` — **`passtime_window_inner`** (5.16) window term.
- `Sec5/ApproxFormula.lean:1258` — **`first_passage_stepback_reduce`** (5.17) event reduction.

`fine_scale_mixing` (C10), `first_passage_nonescape` (C7), `approxMainTerm_eq_steppedMid`,
`truncation_error_bound` all `#print axioms` = trust base only. `first_passage_approx` (C8) =
trust base + `sorryAx` (the 2 sorries above, via the assembly triangle).

## Next steps (in the CURRENT DIRECTIVE's scope — close C8, then C9)

1. **`passtime_window_inner` (`:808`)** — MOST SELF-CONTAINED. The (5.16) window term
   `ℙ(passes ∧ T_x ∉ I_y) ≤ C·log^{-c}x`: the integral test that `N_y` is not within `2log^{0.8}x`
   of a window edge. Reuse C7's proved `classMass`/`windowMass`/`intTest_*` in `Sec5.FirstPassage`.
2. **`first_passage_stepback_reduce` (`:1258`)** — the (5.17) event reduction
   `|firstPassMid − steppedMid| ≤ C·log^{-c}x`. Forward inclusion is EXACT
   (`firstPass_event_stepback_subset` ✅); remaining = reverse inclusion + the `E'` size window
   `exp(±log^{0.7}x)(4/3)^{m₀}x` (orbit estimate `syr_iterate_good_bracket'` + `two_rpow_slack_le_exp`
   are PROVED — the missing piece is the `IyLo/IyHi` interval algebra) + nested `𝒜⁽ⁿ⁰⁾ ⊂ 𝒜⁽ⁿ⁻ᵐ⁰⁾`.
3. Then **C9 `stabilization`** (`FirstPassage.lean:1399`), then C6 → the two `Statement.lean` headlines.
4. **Hygiene (new blueprint rule):** add a `tools/check_blueprint.py` numeric-trap entry for
   RATIFY-C8-v2 (the exact-affine event) — the probe lives at `tools/sandbox/tao_c8_truncation_probe.py`.

## Rails / notes
- **Do NOT edit ratified pins** (`Eprime`, `Iy`, `firstPassMid`, `steppedMid`, the C8 statements). The
  `approxMainTerm` re-pin to RATIFY-C8-v2 is DONE — leave it; a judge should read it against (5.8)+(5.18).
- Watched (do not touch): `fine_scale_mixing`, `first_passage_nonescape`, `stabilization`, all ratified pins.
- Decidability gotcha hit this lap: a global lemma with an opaque `Set` parameter bakes
  `Classical.propDecidable` for `N ∈ S`, but `set S := {N | …}` uses `Set.decidableSetOf` → `rw`
  pattern mismatch. Fix: prove a LOCAL `expect_indicator`-style lemma over the concrete `S`.
- `ENNReal.tsum_toReal_eq` is oriented `(∑ f).toReal = ∑ (f).toReal` → use it FORWARD to pull `.toReal` out.
- Axiom-check recipe: write `TaoCollatz/ZZ_ax.lean` with `#print axioms`, `lake env lean` it, `rm -f`.
- `git-safe` at `/Users/gotrevor/personal/bin/git-safe` (`export PATH="$HOME/personal/bin:$PATH"`).
- **Work report: 5 sorries + 0 orange nodes** (2 headline stubs, C9, `passtime_window_inner`,
  `first_passage_stepback_reduce`). The route-decisive C8 reindex is CLOSED.
