# HANDOFF — window-uniform Proposition 7.8 Case 1 landed 🌀 (review lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed clean,
judge to verify), directive step 2 remains closed, and directive step 3 now includes
the complete white-start / Case-1 branch of tilted Proposition 7.8. The sole Sec7P
proof debt is still the mandated-LAST `pascal_damping_decay` pin: **1 sorry + 0 orange
nodes**.

## Fresh-mind review

- Re-ran the calibration gate before downstream work. `pascalDamping_half_decay`
  builds with exactly `[Classical.choice, Quot.sound, propext]`, and all 46 watched
  declarations are character-identical to plant commit `eb40bf3`.
- Read the frozen target, the convention bridge, the tilted renewal source, and the
  proved `p = 1/2` Case-1 source against one another. The route still reaches the
  headline: `holdP` has first marginal `Geom(q(p))`, with
  `q(p) = 2p²(1-p)`, and the window lemma already proves `q(p) ≥ 8/125`.
- The previous handoff's proposed survival factor is therefore correct:
  `1-q(p) ≤ 117/125`. No hidden dependence on `p` remains in the Case-1 cutoff,
  and no route trigger or statement drift was found.

## Concrete advance

- Extended `TaoCollatz/Sec7P/Prob.lean` with the reusable general geometric API:
  - `geomP_tsum_toReal` and `geomP_summable_toReal`;
  - `geomP_tail`, the exact identity
    `∑_{a>t} Geom(p)(a) = (1-p)^t`.
- Extended `TaoCollatz/Sec7P/Monotone.lean` with the first genuinely
  window-uniform part of Proposition 7.8:
  - `holdPSurvivalBound = 117/125` and
    `pairThreeProb_survival_le_window`;
  - explicit uniform cutoffs `K_geomPWindow`, `T_powGeomPWindow`, `K_holdP`,
    `M1_holdP`, `T_holdP`, and `C_holdP`;
  - `holdP_weight_expect_core`, `_explicitC`, and the uniform existential form,
    reproducing Tao's three-region estimate with the tilted first marginal;
  - `QP_white_case1_explicitC` and `QP_white_case1`, closing (7.41)--(7.43) for
    every `p ∈ [1/5,3/5]` with `C_holdP A` chosen before `p`.
- No `sorry` was added, no frozen declaration changed, and no read-only §7 file was
  edited.

## Exact verification run

```text
~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.Statement \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay
  Build completed successfully (3313 jobs).
  axioms: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

lake build TaoCollatz.Sec7P.Prob
  Build completed successfully (2498 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.Monotone \
  --axioms TaoCollatz.Sec7P.geomP_tail \
  --axioms TaoCollatz.Sec7P.holdP_weight_expect \
  --axioms TaoCollatz.Sec7P.QP_white_case1
  Build completed successfully (2614 jobs).
  all three axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.geomP_tail \
  --axioms TaoCollatz.Sec7P.holdP_weight_expect \
  --axioms TaoCollatz.Sec7P.QP_white_case1
  Build completed successfully (8760 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all four axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer 3/3
closed; Prop 7.3@p modules 0/10 complete, with the renewal/unrolling foundation and
the full Monotone Case-1 branch landed; Sec7P sorries 1; differ 46/46 yes; blockers
none.`

## Next highest-value attack

Continue directive step 3 at the local-limit seam:

1. Add `holdSumP p := iidSum (holdP p)`, its `iidSum` identity, and the generic
   projection/circle-method entry lemmas in `Sec7P/Unroll.lean`.
2. Bound the four aperiodicity atoms `(1,3)`, `(2,5)`, `(2,7)`, `(2,8)` below
   uniformly on `[1/5,3/5]`; feed those minima to the existing p-free
   `iidSum_apply_le_center_of_decay` engine.
3. Combine the resulting uniform center bound with `holdP_exponential_tail` to start
   the tilted `HoldLocal` package and then the first-passage localization row.
4. Keep `pascal_damping_decay` untouched until final assembly.
