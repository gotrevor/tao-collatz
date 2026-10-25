# HANDOFF — tilted Lemma 7.7 and column marginal landed 🌀 (grind lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 remains closed, and the p-uniform
first-passage localization is now proved through both Tao's Lemma 7.7 and its
column-marginal corollary. The sole Sec7P proof debt remains the mandated-LAST
`pascal_damping_decay` pin: **1 sorry + 0 orange nodes**.

## Concrete advance

- Proved `fpDistP_location_bound_core`, the last-step renewal convolution for
  a variable transverse slope `r`. The non-integral horizontal holding mean is
  recentered at the integer endpoint at uniform cost `exp (16γ)`; the vertical
  mean costs `exp (200γ)`. The existing p-free `conv_Gweight_exp`,
  `Gweight_shift`, and `sum_sqrt_exp_le_explicitC` engines then apply unchanged.
- Proved the explicit-constant and constants-before-`p` interfaces
  `fpDistP_location_bound_explicitC` and `fpDistP_location_bound`. Their center
  is exactly `j-(p/2)s`, and all constants are independent of
  `p ∈ [1/5,3/5]`.
- Proved `fpDistP_col_le_core`, `fpDistP_col_le_explicitC`, and
  `fpDistP_col_le`, summing the positive height overshoot geometrically to
  obtain the uniform first-passage column Gaussian.
- No frozen declaration, read-only §7 source, or tool changed; no `sorry` was
  added. Proof commits: `10eb14a`, `06c9326`.

## Exact verification run

```text
lake build TaoCollatz.Sec7P.FpLocation
  Build completed successfully (3318 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.FpLocation \
  --import TaoCollatz.Sec7P.FpLocation \
  --axioms TaoCollatz.Sec7P.fpDistP_location_bound_core \
  --axioms TaoCollatz.Sec7P.fpDistP_location_bound_explicitC \
  --axioms TaoCollatz.Sec7P.fpDistP_location_bound
  Build completed successfully (3318 jobs).
  all three axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.FpLocation \
  --import TaoCollatz.Sec7P.FpLocation \
  --axioms TaoCollatz.Sec7P.fpDistP_col_le_core \
  --axioms TaoCollatz.Sec7P.fpDistP_col_le_explicitC \
  --axioms TaoCollatz.Sec7P.fpDistP_col_le
  Build completed successfully (3318 jobs).
  all three axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

pre-commit full lake build (twice, one per proof commit)
  Build completed successfully (8762 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.fpDistP_location_bound \
  --axioms TaoCollatz.Sec7P.fpDistP_col_le
  Build completed successfully (8762 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all three axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

git diff --check
  clean

rg -n "^[[:space:]]*sorry([[:space:]]|$)" TaoCollatz/Sec7P
  TaoCollatz/Sec7P/Statement.lean:142:  sorry
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer
3/3 closed; Prop 7.3@p modules 3/10 complete through the full FpLocation row;
Sec7P sorries 1; differ 46/46 yes; blockers none.`

## Current blocker

There is no route blocker. The next campaign row is the black-edge / many-
triangles cluster. The new `fpDistP_location_bound_explicitC` and
`fpDistP_col_le_explicitC` are the uniform replacements for the two X6 inputs
used throughout `Sec7/BlackEdge.lean` and `Sec7/ManyTriangles.lean`.

The first slope-sensitive audit should happen in the new
`Sec7P/BlackEdge.lean`: every fixed center `s/4` becomes `(p/2)s`. In Case 2,
the paper's `¼ log 9 < log 2` must become
`(p/2) log 9 < log 2`, uniformly at `p ≤ 3/5`. Do not copy the fixed
`fpDist_fst_mgf_numeric` constants blindly; state the window-uniform version
against the new column bound and retain constants before `p`.

## Next highest-value attack

1. Add `Sec7P/BlackEdge.lean`, importing the p-free deterministic triangle and
   setup machinery plus the new `Sec7P/FpLocation` law-specific inputs.
2. Port the bottom-up analytic leaves consuming X6: the first-coordinate MGF,
   `edgeWeight` expectation, and the Case-2 localization/white-exit estimates,
   with center `(p/2)s`.
3. Prove one named uniform slope-margin lemma from `p ≤ 3/5` and
   `(3/5) log₂ 3 < 1`; reuse it at every former `s/4` budget comparison.
4. Keep `pascal_damping_decay` untouched until final assembly.
