# Handoff: `mainZ_bound` CLOSED (a-posteriori route) + `Iy_card_bracket` banked

**Date**: 2026-07-15.  **Branch** `main`.  Build 🟢 green (full `lake build`, 3324 jobs).
**Read `DIRECTION.md` first** (🪷 operator note binds; **C6 pins owed BEFORE the C9 census hits
zero** — that gate is now IMMEDIATE, see NEXT).

## This lap

- **`mainZ_bound` PROVED** (`Sec5/Stabilization.lean`, relocated below `harmonic_to_Z` — its only
  consumer `approxMainTerm_to_Z` sits later, so the move is safe; statement byte-identical).
  **Route — the non-trivial insight of the lap**: the crude `c_n`-style integral test can only give
  `Z ≪ log^{0.7}x` (Tao's `O(1)` needs Lemma 5.3's delicate `c_{n,a}`/CRT split, deliberately
  avoided in this campaign).  Instead the proof runs **Tao's a-posteriori identity `Z ≍
  (log(4/3)/2)·ℙ(Pass∈E) = O(1)`** (p.26) NON-CIRCULARLY from already-proved pieces: per
  `n ∈ I_y` (at `y = x^α`), `perNTerm ≥ (mainZ − O(1))/norm` by `perNTerm_harmonic_approx` (leaf A,
  closed last lap) + `harmonic_to_Z` (the C10 seam); summing, `#I_y·(mainZ − O(1))/norm ≤
  approxMainTerm ≤ 1 + O(log^{-c})` by **C8 `first_passage_approx`** + `ℙ ≤ 1`; then `#I_y ≥
  0.001·log x ≥ 0.001·norm` collapses it.  ⚠ approxMainTerm_to_Z (its consumer) is NOT circular:
  it consumes mainZ_bound; mainZ_bound consumes only C8 + the two C9 leaves + the lattice count.
- **`Iy_card_bracket` PROVED** — two-sided lattice count `|#I_y − ((α−1)log y/log(4/3) −
  2·log^{0.8}x)| ≤ 1` for `x ≥ exp(2000⁵)`.  The lower half feeds `mainZ_bound`; **both halves are
  the lattice core of `Iy_count_ratio`** (next hole) — the remaining work there is only the
  ratio-vs-`2/log(4/3)` algebra (error `O(log^{-0.2}x)` from `2·log^{0.8}/norm + O(1/norm)`).
- **`PMF.expect_indicator_le_one`** — small reusable helper (indicator expectation ≤ total mass 1).
- All three `#print axioms` = `[propext, Classical.choice, Quot.sound]` — believed clean, judge to
  verify.  HEARTBEAT 800k on both new theorems (justified in-file).

## Census: **3 sorries + 0 orange** (+ C6 un-pinned surface)

`Sec5/Stabilization.lean`: `Iy_count_ratio` (:2546); `Statement.lean:24,31` (frozen headlines, C6).

## Blueprint

`mainZ_bound`/`Iy_card_bracket` are worker-authored internal decompositions below the
`stabilization` pin (judge cross-read pending per directive).  Flips for C9A/C9B1/C9B2 + the leaf-A
close still owed to the judge.

## NEXT — ORDER MATTERS (operator rail)

1. **C6 pins FIRST** — `Iy_count_ratio` is the LAST C9 hole; the operator note requires the C6
   intermediates pinned (statement-only, copy-not-compose vs §3, + numeric traps in
   `tools/check_blueprint.py`) **BEFORE the C9 census hits zero**.  Pin: Thm 1.6 (over
   `AlmostAllOdd`), Thm 3.1-Syracuse form, the (1.2) log-density reduction, and the
   headline-from-intermediates spine.  Do NOT self-`\leanok`; JUDGE-FLAG for ratify-on-pin.
2. **`Iy_count_ratio`** — from `Iy_card_bracket`: ratio = 2/log(4/3) − (2log^{0.8}x ± 1)·(nrm)⁻¹;
   error ≤ C·log^{-0.2}x?  Check: 2·log^{0.8}/((α−1)/2·log y) ≤ (4/(α−1))·log^{-0.2}x ✓ (log y ≥
   log x).  Take c = 0.2.

## Rails
- `git-safe` only (it lives at `~/personal/bin/git-safe` — NOT on default PATH; export
  `PATH="$HOME/personal/bin:$PATH"` first); targeted adds.
- Never edit ratified pins / frozen constants; JUDGE-FLAG if blocked.
