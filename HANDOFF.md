# HANDOFF — uniform tilted center bound landed 🌀 (grind lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 remains closed, and directive step 3
now has the complete p-uniform finite-circle-method center regime needed by
Tao's Lemma 2.2(i). The sole Sec7P proof debt is still the mandated-LAST
`pascal_damping_decay` pin: **1 sorry + 0 orange nodes**.

## Concrete advance

- Extended `TaoCollatz/Sec7P/Unroll.lean` with the tilted sum and generic
  circle-method entry:
  - `holdSumP` and `holdSumP_eq_iidSum`;
  - mod-`N` mass domination and the Fourier point-mass bound;
  - `holdP_apply_two_toReal`, exposing cancellation of the conditioning
    normalizer at first coordinate two.
- Proved the compact-window nondegeneracy package:
  - the four atoms `(1,3)`, `(2,5)`, `(2,7)`, `(2,8)` all have mass at least
    `1/4000`, uniformly for `p ∈ [1/5,3/5]`;
  - their mod-`N` projections yield characteristic decay with denominator
    `8000000`;
  - `holdSumP_apply_le_center_window` follows from the existing p-free
    `iidSum_apply_le_center_of_decay` engine.
- Added `TaoCollatz/Sec7P/HoldLocal.lean`, beginning plan row 5:
  - `tiltZ_holdP_le_box_window` bounds the partition function by `6` throughout
    `|λᵢ| ≤ 1/1000`, using positivity of both holding coordinates and the fixed
    positive exponential moment from `HoldTail`;
  - every one of the four atoms retains mass at least `1/25000` after tilting;
  - `tiltHoldP_apply_le_center_window` gives the resulting p- and tilt-uniform
    center point-mass bound via the p-free circle method.
- Added the new module import to `TaoCollatz.lean`. No frozen declaration or
  read-only §7 source changed, and no `sorry` was added.

## Exact verification run

```text
~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.Statement \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay
  Build completed successfully (3313 jobs).
  axioms: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

lake build TaoCollatz.Sec7P.Unroll
  Build completed successfully (3299 jobs).

lake build TaoCollatz.Sec7P.HoldLocal
  Build completed successfully (3317 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.HoldLocal \
  --import TaoCollatz.Sec7P.HoldLocal \
  --axioms TaoCollatz.Sec7P.holdP_four_atoms_lower_window \
  --axioms TaoCollatz.Sec7P.holdSumP_apply_le_center_window \
  --axioms TaoCollatz.Sec7P.tiltHoldP_apply_le_center_window
  Build completed successfully (3317 jobs).
  all three axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

git-safe diff --check
  clean

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.holdP_four_atoms_lower_window \
  --axioms TaoCollatz.Sec7P.holdSumP_apply_le_center_window \
  --axioms TaoCollatz.Sec7P.tiltHoldP_apply_le_center_window
  Build completed successfully (8761 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all four axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer
3/3 closed; Prop 7.3@p modules 0/10 complete, with renewal/unrolling, full
Monotone Case 1, and the p-uniform tilted center-regime local bound landed;
Sec7P sorries 1; differ 46/46 yes; blockers none.`

## Current blocker

The center-regime circle method is no longer the blocker. The next load-bearing
gap is the **uniform second-order MGF estimate around the p-dependent mean**
`q(p)⁻¹ · (1, 2/p)`. The existing bound `tiltZ_holdP_le_box_window ≤ 6` is enough
to preserve tilted atom mass, but is too coarse for Chernoff localization because
raising it to the `n`th power loses exponentially. A quadratic expansion with a
constant chosen before `p` is required.

## Next highest-value attack

1. Add `Sec7P/Mgf.lean` (or the corresponding named section of `HoldLocal`) with
   one-dimensional uniform Taylor bounds for the exact closed forms already in
   `HoldTail`: first coordinate mean `q(p)⁻¹`, second coordinate mean
   `2/(p q(p))`, and one fixed quadratic remainder constant on
   `p ∈ [1/5,3/5]`, `|λ| ≤ 1/1000` (shrink the box if the arithmetic demands it).
2. Combine them through `tiltZ_expW2_sq_le` to prove
   `Z_p(λ) ≤ exp(μ_p·λ + K|λ|²)` with `K` independent of `p`.
3. Feed that estimate and `tiltHoldP_apply_le_center_window` through the existing
   tilting identity to obtain the full p-uniform analogue of
   `holdSum_apply_le_chernoff` / `hold_local_bound`.
4. Only then begin `FpLocationP`, centered at the slope `j ≈ s·p/2`; keep
   `pascal_damping_decay` untouched until final assembly.
