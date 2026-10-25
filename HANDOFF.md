# HANDOFF — tilted renewal recursion and first-passage unrolling landed 🌀 (grind lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed clean,
judge to verify), directive step 2 remains closed, and directive step 3 now has its
renewal recursion / monotonicity / unrolling foundation. The sole Sec7P proof debt is
still the mandated-LAST `pascal_damping_decay` pin: **1 sorry + 0 orange nodes**.

## Concrete advance

- Extended `TaoCollatz/Sec7P/Holding.lean` with the general-`p` renewal API:
  - `holdP_fst_marginal`, `holdP_tsum_fst`, total real mass and summability;
  - `QP`, the well-founded `holdP` recursion corresponding to (7.34)--(7.35);
  - `QP_boundary`, `QP_rec`, `QP_nonneg`, and `QP_le_one`.
- Added `TaoCollatz/Sec7P/Monotone.lean`:
  - `QPm`, the tilted version of (7.38);
  - the law-independent bounds `QPm_le_rpow`, `le_QPm`, `QP_le_QPm`, and
    `QPm_nonneg`;
  - `QP_white_contract`, the one-step white contraction at arbitrary `p`.
- Added `TaoCollatz/Sec7P/Unroll.lean`:
  - `QPstop` and the exact first-passage identity `QPstop_eq`;
  - the tilted endpoint law `fpDistP` and its positive-coordinate/overshoot support API;
  - `QP_le_fpDistP_expect`, the (7.45) entry inequality for downstream Cases 2 and 3.
- Imported both new modules from `TaoCollatz.lean`. No `sorry` was added, and no frozen
  statement or read-only §7 file was changed.

## Route finding

The entire finite recursion and first-passage layer depends only on the support facts
already proved for `holdP`, not on any `p = 1/2` numeral. Consequently the original D6
well-founded constructions transfer verbatim with explicit parameters
`p`, `hp0 : 0 < p`, and `hp1 : p < 1`.

The next non-formal transfer is the Case-1 weighted expectation. The original
`hold_weight_expect` uses the exact `Geom(1/4)` survival factor `3/4`. Uniformly on the
campaign window, `q(p) = pairThreeProb p ≥ 8/125`, so the tilted survival factor is at
most `117/125`. The next lap should rebuild the explicit cutoffs with `117/125`; this is
the first place in `Monotone` where a genuinely new window-uniform constant is needed.

## Exact verification run

```text
lake build TaoCollatz.Sec7P.Unroll
  Build completed successfully (2615 jobs).

./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.QP_le_one \
  --axioms TaoCollatz.Sec7P.QPm_le_rpow \
  --axioms TaoCollatz.Sec7P.QP_le_fpDistP_expect
  Build completed successfully (8760 jobs)
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all four axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer 3/3
closed; Prop 7.3@p modules 0/10 complete, with row-4 renewal/monotone/unroll foundation
landed; Sec7P sorries 1; differ 46/46 yes; blockers none.`

## Next highest-value attack

Continue directive step 3 in `Sec7P/Monotone.lean`:

1. Prove an exact/useful `geomP` real-mass or tail formula for parameter
   `q = pairThreeProb p` if the current `Prob.lean` API is insufficient.
2. Generalize `K_geom`, `T_powGeom`, and `hold_weight_expect` with the uniform survival
   bound `(117/125)^k`, using `pairThreeProb_mem_window`.
3. Prove the window-uniform tilted `QP_white_case1`; this closes the remaining Case-1
   portion of the Monotone row.
4. Then extend `Unroll.lean` with `holdSumP` and begin the uniform local-limit input.
5. Keep `pascal_damping_decay` untouched until final assembly.
