# HANDOFF — tilted holding tails and edge-weight Fubini split closed 🌀 (grind lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 remains closed, and all four analytic
inputs plus the law-parametric Fubini heart of the Case-2 edge-weight estimate
are now proved uniformly over the campaign window. The sole Sec7P proof debt
remains the mandated-LAST `pascal_damping_decay` pin: **1 sorry + 0 orange
nodes**.

## Concrete advance

- Re-ran the binding calibration gate before downstream work. The half-Pascal
  theorem still has exactly the trusted three axioms, the 46 frozen
  declarations still match the plant, and the blueprint audit reports no drift
  or false green.
- Proved `holdP_fst_mgf_le_real`. The exact quadratic MGF has linear
  coefficient `pairThreeProb p⁻¹`; the window lower bound
  `pairThreeProb p ≥ 8/125` replaces it uniformly by `125/8` before `p` is
  selected.
- Proved `holdP_fst_tail_le`. `holdP_fst_marginal` reduces the tail exactly to
  `Geom(pairThreeProb p)`, and `1-pairThreeProb p ≤ 117/125` gives a fixed
  exponential rate and a threshold chosen before `p`.
- Defined the law-parametric `edgeWeightFor` and the tilted specialization
  `edgeWeightP`. Proved `edgeWeightFor_split`, which performs the full
  summability/Fubini split for arbitrary PMFs and isolates all law dependence
  into two first-coordinate MGFs and two tails. Specialized it as
  `fpDistP_edgeWeight_split`.
- The preceding lap already supplied the other two analytic inputs
  `fpDistP_fst_mgf_le` and `fpDistP_fst_tail_le`; hence every non-algebraic
  ingredient of `fpDistP_edgeWeight_le` is now green. No existing §7 source,
  frozen declaration, blueprint, or tool file changed. No `sorry` was added.
  Proof commits: `01f32e4`, `d4e2da6`.

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
  --axioms TaoCollatz.Sec7P.holdP_fst_mgf_le_real \
  --axioms TaoCollatz.Sec7P.holdP_fst_tail_le
  Build completed successfully (3319 jobs).
  both axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --import TaoCollatz \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.holdP_fst_mgf_le_real \
  --axioms TaoCollatz.Sec7P.holdP_fst_tail_le \
  --axioms TaoCollatz.Sec7P.edgeWeightFor_split \
  --axioms TaoCollatz.Sec7P.fpDistP_edgeWeight_split
  Build completed successfully (8763 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all five axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.BlackEdge \
  --import TaoCollatz.Sec7P.BlackEdge \
  --axioms TaoCollatz.Sec7P.edgeWeightFor_split \
  --axioms TaoCollatz.Sec7P.fpDistP_edgeWeight_split
  Build completed successfully (3319 jobs).
  both axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

pre-commit full lake build (twice)
  Build completed successfully (8763 jobs).

./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

git diff --check
  clean
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer
3/3 closed; Prop 7.3@p modules 3/10 complete plus BlackEdge Case-2 analytic
inputs and Fubini core complete; Sec7P sorries 1; differ 46/46 yes; blockers
none.`

## Current blocker

There is no route blocker. The remaining Case-2 edge-weight step is algebraic
assembly over `fpDistP_edgeWeight_split`. Compared with the fixed-law proof,
the holding MGF is

```text
1 + (125/8)θ + 96000000θ²
```

rather than `1 + 4θ + 32θ²`, so the small-tilt cutoff must additionally
force, for example, `θ ≤ min (ε/32) (1/192000000)` (as well as
`θ ≤ 1/2000`). Then the quadratic term is at most `θ/2` and the whole
excess is at most `(129/8)θ < ε`. All cutoffs are independent of `p`.

## Next highest-value attack

1. Prove `fpDistP_edgeWeight_le` by combining `fpDistP_edgeWeight_split` with
   `fpDistP_fst_mgf_le`, `holdP_fst_mgf_le_real`,
   `fpDistP_fst_tail_le`, and `holdP_fst_tail_le`. Use
   `ε = min (δ/8) 2` and add the explicit small-tilt threshold described
   above before quantifying `p`.
2. Port the Case-2 white-exit estimate and the `QP` endpoint step using
   `edgeWeightP`; this should close `QP_black_edge_case2`.
3. Only then enter `ManyTriangles`/Case 3. Keep the final pin untouched until
   the p-renewal Proposition 7.3 assembly is available.
