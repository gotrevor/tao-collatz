# HANDOFF — finer epsilon reopens the Sec7P localization route 🌀 (grind lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 remains closed, and the sole Sec7P
proof debt remains the mandated-LAST `pascal_damping_decay` pin: **1 sorry + 0
orange nodes**.

## Concrete advance

- Resolved the previous lap's fixed-scale route obstruction using the operator
  ruling already present in `DIRECTION.md`: when the tilted localization box
  outgrows Lemma 7.4 at `epsBW`, choose a smaller epsilon in `Sec7P/` rather
  than edit the p-free library.
- Added `Sec7P/Setup.lean` with
  `epsP = 10^-100000`, `blackP`, and `whiteP`. Proved `blackP_imp_black` and
  the new separation certificate `twenty_thousand_lt_sepP`.
- Proved the exact replacement for the p-free Lemma-7.2 seam:
  `whiteP_cos_bound` and the full product estimate
  `prod_fCond_le_dampingP`. Thus the final frozen `pascalDamping` can use the
  smaller scale without changing any watched definition or theorem statement.
- Proved the numerical localization gate

  ```text
  Y = 12000, B = 300, X = 3769,
  5Y + B ≤ 16X,
  X² + Y² < ((1/10) log(1/epsP))².
  ```

  This is the inequality that is impossible at the old `epsBW` scale.
- Proved `height_radiusP_numeric`: the already-established uniform positive
  moment at tilt `1/1000` gives the renewal-level geometric bound

  ```text
  6 exp(-12000/1000) / (1-exp(-1/1000)) ≤ 1/16.
  ```

  Also proved `holdP_snd_tail`, extracting the required vertical one-step tail
  directly from `holdP_exponential_tail`.
- Added the new module to `TaoCollatz.lean`. No frozen declaration, existing
  p-free §7 source, blueprint, judge file, direction file, status file, or tool
  file changed. No `sorry` was added.

## Exact verification run

```text
~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --import TaoCollatz \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.prod_fCond_le_dampingP \
  --axioms TaoCollatz.Sec7P.holdP_snd_tail \
  --axioms TaoCollatz.Sec7P.localization_boxP_numeric
  Build completed successfully (8764 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all four axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

lake build TaoCollatz.Sec7P.Setup
  Build completed successfully (3315 jobs).

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

git diff --check
  clean
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer
3/3 closed; Prop 7.3@p modules 3/10 complete plus the Case-2 analytic package
and the finer-epsilon damping/localization numeric gate; Sec7P sorries 1;
differ 46/46 yes; blockers: none operator-level — next proof debt is the
finer-scale deterministic triangle port.`

## Current blocker

The previous `JUDGE-FLAG` remains a valid refutation of the **fixed-`epsBW`**
rectangular route, but it is not a blocker to the directive: the directive had
already authorized `blackP`/`whiteP` at a smaller epsilon. The new scale and
all numerical/probabilistic inputs are now kernel-checked.

The live mathematical task is to copy-generalize Lemma 7.4's deterministic
triangle structure from `black`/`white` to `blackP`/`whiteP`. This is a long but
source-grounded port, not an operator decision. Its quantitative Claim (*)
window must scale from the old 300 lattice units to the new separation radius;
do not reuse a fixed `300` bound silently.

## Next highest-value attack

1. Add `Sec7P/Triangles.lean`, parameterizing the deterministic phase arguments
   at `epsP`; prove the `TriangleFamilyP` cover/separation interface needed by
   the white-exit kernel. Recompute every old `300`-step numeric against
   `epsP = 10^-100000`.
2. After that interface is stable, instantiate the p-free
   strictly-increasing-height renewal proof for `holdP`. Combine
   `holdP_snd_tail` with `height_radiusP_numeric` to prove the first-passage
   vertical bad mass at `Y=12000` is `≤1/16`.
3. Combine that tail with the already-proved transverse `B=300` tail and
   `localization_boxP_numeric`, then port the Case-2 white-exit assembly.
