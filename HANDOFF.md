# HANDOFF — uniform quadratic MGF and Chernoff bridge landed 🌀 (grind lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 remains closed, and directive step 3
now has a p-uniform quadratic MGF and the resulting off-center Chernoff estimate.
The sole Sec7P proof debt remains the mandated-LAST `pascal_damping_decay` pin:
**1 sorry + 0 orange nodes**.

## Concrete advance

- Extended `TaoCollatz/Sec7P/HoldLocal.lean` with a reusable Taylor/moment
  lemma: an exact nonnegative first moment plus the already-proved fixed
  exponential moment bounds a one-coordinate MGF by
  `1 + mean * μ + 96000000 * μ²` on `|μ| ≤ 1/2000`.
- Applied it to both holding coordinates. The second-coordinate proof includes
  the support bridge from `Int.toNat` back to the integer coordinate.
- Combined the coordinate estimates through the existing ENNReal
  Cauchy--Schwarz lemma. For every `p ∈ [1/5,3/5]` and
  `|λᵢ| ≤ 1/4000`,
  `tiltZ holdP ≤ 1 + μ_p · λ + 10^9 (λ₁² + λ₂²)`, where
  `μ_p = q(p)⁻¹ (1, 2/p)`; the quadratic constant is chosen before `p`.
- Fed that estimate, the exact tilting identity, and the preceding lap's
  uniform tilted center bound into
  `holdSumP_apply_le_chernoff_window`. This supplies a uniform off-center
  exponential point-mass estimate for the parameterized holding walk.
- No frozen declaration or read-only §7 source changed, and no `sorry` was
  added. Commit: `99101b0`.

## Exact verification run

```text
lake build TaoCollatz.Sec7P.HoldLocal
  Build completed successfully (3317 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.HoldLocal \
  --import TaoCollatz.Sec7P.HoldLocal \
  --axioms TaoCollatz.Sec7P.tiltZ_holdP_le_quad_window \
  --axioms TaoCollatz.Sec7P.holdSumP_apply_le_chernoff_window
  Build completed successfully (3317 jobs).
  both axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.tiltZ_holdP_le_quad_window \
  --axioms TaoCollatz.Sec7P.holdSumP_apply_le_chernoff_window
  Build completed successfully (8761 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all three axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

git-safe diff --check
  clean
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer
3/3 closed; Prop 7.3@p modules 0/10 complete, with renewal/unrolling, full
Monotone Case 1, and the p-uniform quadratic-MGF/Chernoff local layer landed;
Sec7P sorries 1; differ 46/46 yes; blockers none.`

## Current blocker

The uniform MGF expansion and Chernoff transfer are no longer blockers. The
next load-bearing gap is the **deterministic choice of the two tilt parameters**
that turns `holdSumP_apply_le_chernoff_window` into the p-uniform
`hold_local_bound` shape used by `FpLocation`. The optimizer must stay inside
`|λᵢ| ≤ 1/4000`, handle the p-dependent center
`n q(p)⁻¹ (1,2/p)`, and leave constants independent of `p`.

## Next highest-value attack

1. Copy-generalize the optimizer in the p-free `hold_local_bound`, using
   `K = 10^9` and clipping the coordinate tilts to `1/4000`.
2. Package the result as a p-uniform local bound centered at
   `n q(p)⁻¹ (1,2/p)`; kernel-check its headline axiom set.
3. Begin `Sec7P/FpLocation.lean`, replacing Tao's slope `1/4` by `p/2`
   and sizing the localization box uniformly over the window.
4. Keep `pascal_damping_decay` untouched until final assembly.
