# Handoff: C9 leaf A (`perNTerm_harmonic_approx`, Tao (5.19)) CLOSED

**Date**: 2026-07-15.  **Branch** `main`.  Build 🟢 green (full `lake build`, 3324 jobs).
**Read `DIRECTION.md` first** (🪷 operator note binds: vocabulary rail; **C6 pins owed BEFORE the
C9 census hits zero** — see NEXT below).

## This lap

- **`perNTerm_harmonic_approx` PROVED** (`Sec5/Stabilization.lean`, ~240 lines) — the (5.19)
  harmonic reduction, C9 leaf A assembly, exactly per the worked plan in the previous handoff
  (`HANDOFF-2026-07-15-C9-leafA-supports-done.md`):
  - termwise band `cL·(3^k·G2) ≤ A1 ≤ cU·(3^k·G2)` with `cU/cL = (L±Cε)/(L·nrm)`,
    `Cε = 2 + 3(Cw/cD) + 2Cw/(α−1)`; point mass via `Nstar_mem_logWindow` + `Nstar_cast` +
    `logUnifOdd_apply_toReal_of_mem`; the two cross-multiplied nlinarith cores are EXACT
    positive combinations of the six/five hint products (verified by hand first — both closed
    first try);
  - summation via `tsum_tsum_le_tsum_tsum`, dominating family
    `[good]·(2^{pre})⁻¹ · ∑'[E']M⁻¹` (`iid_fiber_summable` + `iid_geomHalf_apply_of_pos`);
  - finish via `perNHarmonic_le` (H ≤ CH·L^0.7) and `L^0.7/L = L^{−0.3}`, c = 0.3, C = Cε·CH.
  - `#print axioms`: `[propext, Classical.choice, Quot.sound]` — believed clean, judge to verify.
  - HEARTBEAT 1.6M (justified comment in-file).
- Gotchas hit: `rw [if_pos ⟨…⟩]` unifies against the FIRST `ite` in the goal — order the rw list
  by goal position (LHS mask first), not by logical order.

## Census: **4 sorries + 0 orange** (+ C6 un-pinned surface)

`Sec5/Stabilization.lean`: `mainZ_bound` (:305), `Iy_count_ratio` (:2239);
`Statement.lean:24,31` (frozen headlines, C6).

## Blueprint

C9A (`perNTerm_harmonic_approx`) is registered `\notready`; statement + proof now both
kernel-backed — **flip owed to the judge** (never self-`\leanok`), as are C9B1/C9B2.

## NEXT (directive order)

1. **`mainZ_bound`** (:305) — coarse-scale mirror of `cn_bound`: `mainZ = ∑_X syracZ(m₀)·c_coarse(X)`
   via `mainZ_eq_sum_cn`-style reindex (already exists at ~:800, `harmonic_reindex` with
   `q = 3^{m₀}`), then `sup c_coarse ≤ C·log^{0.7}x` (single integral test, `cn_window_size` at
   `m = m₀`, `k = m₀ ≤ n₀`) × total syracZ mass 1.  Likely short.
2. **`Iy_count_ratio`** (:2239) — pure lattice count `#I_y = IyHi − IyLo + O(1)`, ratio telescopes
   to `2/log(4/3)`.
3. **C6 pins** — MUST be pinned before the last C9 hole closes (operator rail).  Order the C6
   pinning lap BEFORE finishing whichever of the two C9 holes is last.

## Rails
- `git-safe` only; targeted adds.  Axiom recipe: `ZZ_ax.lean` + `lake env lean` + `rm`.
- Never edit ratified pins / frozen constants; JUDGE-FLAG if blocked.
