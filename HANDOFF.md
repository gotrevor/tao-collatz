# HANDOFF — tilted holding law now has a uniform exponential tail 🌀 (grind lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed clean,
judge to verify), and directive step 2 is now closed. The sole Sec7P proof debt remains
the mandated-LAST `pascal_damping_decay` pin: **1 sorry + 0 orange nodes**.

## Concrete advance

- Added `TaoCollatz/Sec7P/HoldTail.lean` and imported it from `TaoCollatz.lean`.
- Proved exact general-`p` MGF identities:
  - `tiltZ_geomP` and its nonzero/finiteness strip;
  - `tiltZ_pascalP` from `pascalP_eq_iidSum`;
  - `tiltZ_pascalNe3P_add`, the exact deleted-atom identity, plus finiteness;
  - `tiltZ_holdP_factor` and the closed geometric-series form `tiltZ_holdP_closed`.
- Chose the fixed positive tilt `1/1000`. On the full campaign window:
  - `tiltZ_geomP ≤ 200/199`;
  - deleting the `3` atom gives the holding-series ratio `≤ 19/20`;
  - hence `tiltZ holdP (expW2 (1/1000) (1/1000)) ≤ 6`.
- Proved `holdP_exponential_tail`: uniformly in `p`, the `holdP` mass with
  `R ≤ d₁ + d₂` is at most `6·exp(-R/1000)`. This is the final clause of directive
  step 2. No `sorry` was added.

## Route finding

The key was not to bound the conditioned Pascal MGF by the reciprocal normalizer alone;
that loses the strict renewal margin. Instead, the exact identity

```text
(1-q) Z_ne3(λ) + q exp(3λ) = Z_pascal(λ)
```

retains the deleted atom. With `q ≥ 8/125` and the small positive tilt, it yields
`exp(λ)(1-q)Z_ne3(λ) ≤ 19/20`. Thus the paper-level transfer's exponential-tail claim
is sound and window-uniform; no `JUDGE-FLAG` was triggered.

## Exact verification run

```text
lake build TaoCollatz.Sec7P.HoldTail
  Build completed successfully (3314 jobs).

#print axioms TaoCollatz.Sec7P.holdP_exponential_tail
  [propext, Classical.choice, Quot.sound]

./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.holdP_exponential_tail
  Build completed successfully (8758 jobs)
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  both axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer 3/3
closed, including window-uniform tail; Prop 7.3@p modules 0/10; Sec7P sorries 1;
differ 46/46 yes; blockers none.`

## Next highest-value attack

Start directive step 3 at plan row 4:

1. Add the p-parametrized renewal recursion `QP` over `holdP`, mirroring `Q` while
   retaining `p`, `hp0`, and `hp1` as parameters.
2. Prove the boundary equation, recursion equation, nonnegativity, and `≤ 1` API.
3. Copy-generalize `Sec7/Monotone.lean` and `Sec7/Unroll.lean` into `Sec7P/`, using
   `holdP_exponential_tail` for the now-closed probability input.
4. Keep `pascal_damping_decay` untouched until the final assembly.
