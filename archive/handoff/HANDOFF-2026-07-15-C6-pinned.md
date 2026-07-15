# Handoff: C6 intermediates PINNED (directive step 2 complete)

**Date**: 2026-07-15.  **Branch** `main` @ `3431731` + this doc.  Build 🟢 (pre-commit full
`lake build`, 3325 jobs).  **Read `DIRECTION.md` first.**

## This lap

- **New `TaoCollatz/Sec3/Reduction.lean`** — the §3 reduction chain, 7 sorried pins,
  copy-not-compose vs arXiv:1909.03562v5 §1.2 (pp.4–5) / §3 (pp.16–18):
  - `tao_syracuse_quantitative_sum` / `tao_syracuse_quantitative` — Thm 3.1 Syracuse, the
    paper's two displays (one claim, "or equivalently").
  - `tao_syracuse` — Thm 1.6 over `AlmostAllOdd`.
  - `logSum_oddPart_pullback`, `almostAllPos_oddPart_of_almostAllOdd` — the (1.2) odd-part
    bridges (worker-authored decomposition; rest on PROVED `colMin_eq_syrMin_oddPart`).
  - `tao_collatz_spine`, `tao_collatz_quantitative_spine` — byte-identical to the frozen
    `Statement.lean` headlines; those discharge by `exact` when these close.
- **Traps `check14`/`check15`** in `tools/check_blueprint.py` — ALL PASS (odd-window
  normalizer; display equivalence Fraction-exact; (1.2) constant 2 exact and >1.8-tight).
- **Blueprint nodes `C6a/C6b/C6c/C6s`**, all `\notready` (rule 1 — no self-`\leanok`).
  `blueprint_audit.py`: 0 drift, 0 false-green; audit's MISSED-FLIP list (C8, C9A, C9B1,
  C9B2 proof flips) still owed to the judge.

## JUDGE-FLAG (event-trigger (a): new pins → ratify-on-pin)

Ratify C6a/C6b/C6c/C6s vs §1.2/§3. Flagged renderings: `tao_syracuse`'s `f : ℕ → ℝ`,
`Tendsto atTop atTop` vs the paper's odd-domain f (equivalent by extension; mirrors the
frozen `tao_collatz` style); both Thm 3.1 displays in one node.

## Census: **10 sorries + 0 orange**

`Sec3/Reduction.lean` ×7 (new pins) · `Sec5/Stabilization.lean:` `Iy_count_ratio` ·
`Statement.lean:24,31` (frozen headlines).

## NEXT

1. **`Iy_count_ratio`** (Stabilization.lean ~2546) — LAST C9 hole; C6-pins-first gate now
   satisfied. From `Iy_card_bracket`: error ≤ (4/(α−1))·log^{-0.2}x, c = 0.2.
2. C9 closes → **judge pass** (event-trigger (b)) before C6 assembly consumes C8/C9 theorems.
3. C6 proof order: `logSum_oddPart_pullback` (elementary, geometric series) →
   `tao_syracuse_quantitative_sum` from `stabilization` (the §3 telescoping, the real work)
   → the rest are short derivations.

## Rails
- `git-safe` only (`export PATH="$HOME/personal/bin:$PATH"`); targeted adds.
- Never edit ratified pins / frozen constants; the new C6 pins are FROZEN too (RATIFY tags).
