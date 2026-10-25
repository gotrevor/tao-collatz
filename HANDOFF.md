# HANDOFF — tilted first-passage MGF and tail closed 🌀 (review lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 remains closed, and the two
first-passage inputs to the Case-2 edge-weight estimate are now proved
uniformly over the campaign window. The sole Sec7P proof debt remains the
mandated-LAST `pascal_damping_decay` pin: **1 sorry + 0 orange nodes**.

## Concrete advance

- Began with the binding calibration/review gate. The half-Pascal theorem is
  still trust-base-clean, the 46 frozen declarations still match the plant,
  and the blueprint audit reports no drift or false green.
- Reconstructed the final route from source rather than inheriting the prior
  narrative. `pascalWeight_bridge`, the general convention seams in
  `Sec7P/Bridge.lean`, and the p-free `prod_fCond_le_damping` show that a
  p-parametrized Proposition 7.3 feeds the frozen final target directly. No
  raw-valuation pairing detour or statement change is needed.
- Proved `fpDistP_fst_mgf_numeric`. Its threshold is selected before the centre
  slope. Uniformly for `0 ≤ r ≤ 3/10`, the split
  `K = ⌊m log(1+δ/2)/(2A)⌋` satisfies
  `K+1-rs ≥ m log(1+δ/2)/(4A)`; the prefactor is at most `exp A`, and the
  Gaussian tail closes at rate `c²/200`.
- Specialized this as `fpDistP_fst_mgf_le`, with `Cthr` before `p`, obtaining
  the sharp vanishing-tilt bound `≤ 1+δ` under `s ≤ m/log²m`.
- Proved `fpDistP_fst_tail_le` at the fixed tilt
  `min(c,c²/200)/2`. The cutoff `⌊m/log²m⌋+100` absorbs the moving centre
  `(p/2)s`; Chernoff then gives the uniform `δ m^{-A}` tail past `m/4`.
- Reused the already-proved p-free threshold calculus from the fixed §7
  BlackEdge module; no existing §7 source, frozen declaration, blueprint, or
  tool file changed. No `sorry` was added. Proof commit: `f5fed65`.

## Exact verification run

```text
~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.Statement \
  --import TaoCollatz.Sec7P.Statement \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay
  Build completed successfully (3313 jobs).
  axioms: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

lake build TaoCollatz.Sec7P.BlackEdge
  Build completed successfully (3319 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.BlackEdge \
  --import TaoCollatz.Sec7P.BlackEdge \
  --axioms TaoCollatz.Sec7P.fpDistP_fst_mgf_numeric \
  --axioms TaoCollatz.Sec7P.fpDistP_fst_mgf_le \
  --axioms TaoCollatz.Sec7P.fpDistP_fst_tail_le
  Build completed successfully (3319 jobs).
  all three axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --import TaoCollatz \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.fpDistP_fst_mgf_numeric \
  --axioms TaoCollatz.Sec7P.fpDistP_fst_mgf_le \
  --axioms TaoCollatz.Sec7P.fpDistP_fst_tail_le
  Build completed successfully (8763 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all four axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

pre-commit full lake build
  Build completed successfully (8763 jobs).

git diff --check
  clean

rg -n "^[[:space:]]*sorry([[:space:]]|$)" TaoCollatz/Sec7P
  TaoCollatz/Sec7P/Statement.lean:142:  sorry
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer
3/3 closed; Prop 7.3@p modules 3/10 complete plus BlackEdge Case-2 analytic
core in progress; Sec7P sorries 1; differ 46/46 yes; blockers none.`

## Current blocker

There is no route blocker. The first-passage half of the Case-2 edge-weight
estimate is closed, but its holding-law half is not yet exposed in the real
summation form consumed by the Fubini split. The needed estimates are already
nearby: `tiltZ_holdP_fst_le_quad_window` gives the ENNReal MGF with exact linear
coefficient `pairThreeProb p⁻¹`, and `pairThreeProb_mem_window` bounds this by
`125/8`; `holdP_fst_marginal` identifies the first coordinate as geometric,
with failure ratio at most `117/125`.

Do not use only the coarse total-coordinate tail if the exact marginal makes
the proof shorter. In either route, the threshold must be chosen before `p`.
Keep the final pin untouched until the p-renewal Proposition 7.3 assembly is
available.

## Next highest-value attack

1. Prove `holdP_fst_mgf_le_real`, converting
   `tiltZ_holdP_fst_le_quad_window` through `ENNReal.toReal` and replacing
   `pairThreeProb p⁻¹` by a window-uniform coefficient.
2. Prove `holdP_fst_tail_le` with one threshold before `p`, preferably from
   the exact geometric first marginal and `1-q(p) ≤ 117/125`.
3. Define `edgeWeightP`, port the law-parametric Fubini split, and assemble
   `fpDistP_edgeWeight_le` from the two first-passage estimates proved here and
   the two holding-law estimates above.
4. Then port the Case-2 white-exit estimate; do not enter ManyTriangles/Case 3
   until the complete Case-2 package is green.
