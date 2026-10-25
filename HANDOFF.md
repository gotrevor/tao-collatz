# HANDOFF — tilted holding law has exact mean and full support 🌀 (review lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed clean,
judge to verify). This review independently re-ran that gate, validated the frozen route,
then completed the algebraic `Prob` obligations and most of directive step 2. The final
uniform pin remains deliberately untouched. Current Sec7P debt is **1 sorry + 0 orange
nodes**.

## Concrete advance

- `TaoCollatz/Sec7P/Prob.lean`
  - Proved `pascalP_eq_iidSum`: the explicit mass is exactly the law of two iid
    `geomP` draws, not merely a separately normalized formula.
  - Proved `pairThreeProb_basic_bounds`, so `q(p) ≤ 1/2` on the full probability range.
  - Computed the deleted-atom mass exactly:
    `pascalP_ne_three_mass = ofReal (1 - pairThreeProb p)`.
  - Proved the exact conditioned mass `pascalNe3P_toReal` and positive-support lemmas for
    both `geomP` and `pascalNe3P`.
- Added `TaoCollatz/Sec7P/Holding.lean`.
  - Defined `holdP` for `0 < p < 1` with geometric parameter
    `q(p) = 2p²(1-p)` and conditioned `Pascal(p)` increments.
  - Proved positive first coordinate, second coordinate at least `3`, first marginal,
    pinned-coordinate formula, and the `(1,3)` / `(2,3+b)` application formulas.
- Added `TaoCollatz/Sec7P/HoldBasics.lean`.
  - Proved exact means of `geomP`, its shifted form, `pascalP`, and `pascalNe3P`.
  - Proved the tilted holding mean in `ℝ≥0∞` and real forms:
    `E HoldP = q(p)⁻¹ · (1, 2/p)`.
  - Proved Tao's four support atoms persist and transferred the aperiodicity argument as
    `holdP_aperiodic` for every `0 < p < 1`.
- No new `sorry` was introduced. The sole Sec7P `sorry` remains the mandated-LAST
  `pascal_damping_decay` pin.

## Review findings

- The calibration bridge still reaches the proved §7 theorem with no statement drift:
  `tools/tao_stmt_diff.py eb40bf3 HEAD` reported 46/46 before this checkpoint, and
  `pascalDamping_half_decay` had exactly the trusted three axioms.
- The campaign route remains sound. The closed-mass presentation of `pascalP` is now
  formally connected to the iid-sum machinery needed by the later MGF/local-limit layer.
- The next route-decisive uncertainty is not normalization or mean drift anymore; it is
  choosing and proving a single positive exponential tilt for `holdP` uniformly over the
  compact p-window.

## Exact verification run

Narrow checks completed during development:

```text
lake build TaoCollatz.Sec7P.Prob
  Build completed successfully (2498 jobs).

lake build TaoCollatz.Sec7P.Holding
  Build completed successfully (2499 jobs).

lake build TaoCollatz.Sec7P.HoldBasics
  Build completed successfully (3313 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.Statement \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay
  Build completed successfully (3313 jobs)
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  axioms: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN
```

The post-edit full gate and final differ verdict are recorded below.

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer 2/3
modules fully closed (Prob + holding distribution; HoldBasics lacks only the uniform
tail package); Prop 7.3@p modules 0/10; Sec7P sorries 1; blockers none.`

## Next highest-value attack

Finish directive step 2 with a window-uniform exponential moment/tail for `holdP`:

1. Use `pascalP_eq_iidSum` to derive the probability generating function of
   `Pascal(p)`, then use `pascalNe3P_toReal` to delete the `3` atom and divide by the
   explicit normalizer.
2. Choose one fixed positive tilt valid for all `p ∈ [1/5,3/5]`. The available uniform
   margins are `q(p) ≥ 8/125`, `1-p ≤ 4/5`, and `1-q(p) ≥ 89/125` (the coarser
   full-range normalizer bound `≥ 1/2` is already proved).
3. Sum the geometric number of conditioned increments to obtain the `holdP` exponential
   moment and tail with constants chosen before `p`.
4. Only after that gate is green, add the p-parametrized `Q` recursion and begin the
   `Monotone`/`Unroll` copy-generalization. Keep `pascal_damping_decay` LAST.

## Final gate verdict

```text
./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay
  Build completed successfully (8757 jobs)
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  axioms: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN
```
