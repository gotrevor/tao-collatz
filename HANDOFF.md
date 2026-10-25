# HANDOFF — Case-2 endpoint + transverse localization tail landed 🌀 (reflection lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 remains closed, and the Case-2 port
now has both Tao's endpoint inequality and a usable uniform transverse
first-passage tail. The sole Sec7P proof debt remains the mandated-LAST
`pascal_damping_decay` pin: **1 sorry + 0 orange nodes**.

## Concrete advance

- Re-ran the binding calibration gate before downstream work. The half-Pascal
  theorem still has exactly the trusted three axioms; all 46 frozen
  declarations match the plant; the blueprint audit reports no drift or false
  green.
- Proved the law-parametric landing-weight bounds
  `edgeWeightFor_le_one`, `rpow_neg_le_edgeWeightFor`, and
  `edgeWeightFor_of_deep`, their `edgeWeightP` specializations, and
  `one_le_QPm`. Used them to prove `QP_fp_endpoint_le`, the tilted form of
  Tao's (7.46). Proof commit: `1357544`.
- Reflection against the fixed `Sec7/ManyTriangles.lean` route found a genuine
  quantitative trap: expanding `fpDistP` as a renewal series pays a factor
  `(1-M)⁻¹`. Near `p=3/5` the transverse one-step MGF is about `0.986`, so that
  prefactor forces a half-space radius too large for Lemma 7.4's fixed
  separation. This route is now retired.
- Added `fpDistP_tiltZ_le_one`, a generic finitized optional-stopping theorem:
  every multiplicative weight whose `holdP` expectation is at most one has
  first-passage expectation at most one, for every height budget.
- Proved the exact cancellation
  `tiltZ_holdP_le_one_of_pascalP`. The removed `b=3` atom cancels between the
  holding MGF numerator and its geometric ratio, reducing the test to the
  unconditioned `pascalP` MGF with no geometric loss.
- At `θ=1/100`, proved the uniform scalar bound
  `p·exp(3θ)+(1-p)·exp(-5θ)≤1` on `[1/5,3/5]`, then
  `tiltZ_holdP_transverse_le_one` for the weight
  `exp((16j-5l)/100)`.
- Combined exact cancellation and optional stopping in
  `fpDistP_transverse_tiltZ_le_one`, then proved the concrete Chernoff bound
  `fpDistP_transverse_tail_le_eighth`:
  `P(16e₁-5e₂ ≥ 300) ≤ 1/8`, uniformly before `p` and `s`. Proof commit:
  `750c30d`.
- No frozen declaration, existing p-free §7 source, blueprint, or tool file
  changed. No `sorry` was added.

## Exact verification run

```text
~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.Statement \
  --import TaoCollatz.Sec7P.Statement \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay
  Build completed successfully (3313 jobs).
  axioms: [Classical.choice, Quot.sound, propext]
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  FORMALIZE-TIER GREEN

lake build TaoCollatz.Sec7P.Unroll
  Build completed successfully (3300 jobs).

lake build TaoCollatz.Sec7P.HoldTail
  Build completed successfully (3314 jobs).

lake build TaoCollatz.Sec7P.BlackEdge
  Build completed successfully (3319 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.BlackEdge \
  --import TaoCollatz.Sec7P.BlackEdge \
  --axioms TaoCollatz.Sec7P.fpDistP_tiltZ_le_one \
  --axioms TaoCollatz.Sec7P.tiltZ_holdP_transverse_le_one \
  --axioms TaoCollatz.Sec7P.fpDistP_transverse_tail_le_eighth \
  --axioms TaoCollatz.Sec7P.QP_fp_endpoint_le
  Build completed successfully (3319 jobs).
  all four axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --import TaoCollatz \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.QP_fp_endpoint_le \
  --axioms TaoCollatz.Sec7P.fpDistP_tiltZ_le_one \
  --axioms TaoCollatz.Sec7P.tiltZ_holdP_transverse_le_one \
  --axioms TaoCollatz.Sec7P.fpDistP_transverse_tail_le_eighth
  Build completed successfully (8763 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all five axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

pre-commit full lake build
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
3/3 closed; Prop 7.3@p modules 3/10 complete plus the full Case-2 analytic
package through endpoint and transverse localization; Sec7P sorries 1; differ
46/46 yes; blockers none.`

## Current blocker

There is no route blocker. The next load-bearing lemma is the **vertical
first-passage overshoot bound** needed to complement the transverse tail.
The old generic `holdP_exponential_tail` at rate `1/1000` is far too weak at a
box compatible with the fixed separation; do not spend another lap trying to
inflate that estimate.

The reflection found the sharper algebraic route. If `P(z)` is the height PGF
of `pascalP`, `q=2p²(1-p)`, and `H(z)` is the height PGF of `holdP`, then

```text
H(z) = q z³ / (1 - P(z) + q z³),
1 / (1 - H(z)) = 1 + q z³ / (1 - P(z)).
```

Thus the positive-height `holdP` renewal density is exactly `q` times the
`pascalP` renewal density shifted by three. Its coefficients have the closed
form

```text
U_P(u) = (p/2) · (1 - (1 - 2p)^(u-1)),  u ≥ 2.
```

This is uniformly bounded by `p/2` for `p≤1/2` and by `p` for `p≥1/2`, and is
the intended replacement for the lossy exponential-tail argument.

## Next highest-value attack

1. In a new `Sec7P/ManyTriangles.lean`, formalize the two PGF/coefficient
   identities above and port the renewal proof of
   `fpDist_height_tail_le_sixteenth_sharp` to obtain a useful vertical bound at
   a radius near `Y=200` (only a positive final white-exit mass is required).
2. Generalize the deterministic localization lemma's hard-coded `64` to a
   transverse parameter and instantiate `B=300`. Candidate box:
   `Y=200`, `X=82`, since `5Y+B=1300≤1312=16X` and
   `X²+Y²=46724`. Strengthen `sep_const_gt_two_hundred` locally to separation
   `>217` using `2^32 < 10^10` and `Real.log_two_gt_d9`; the actual separation
   is about `230.26`.
3. Combine vertical, transverse, and the already-proved moving-centre
   out-of-strip tail into the tilted white-exit kernel, then assemble
   `QP_black_edge_case2` with `QP_fp_endpoint_le` and
   `fpDistP_edgeWeight_le`.
