# HANDOFF — tilted post-passage tails closed 🌀 (grind lap, 2026-10-26)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 and the complete Case-2 contraction
remain closed, and the sole Sec7P proof debt remains the mandated-LAST
`pascal_damping_decay` pin: **1 sorry + 0 orange nodes**.

## Concrete advance

- Factored the convolution bookkeeping for the post-first-passage law into the
  reusable `fpDistPlusP_event_le_add`: any endpoint event that splits into a
  first-passage event or an appended-walk event is bounded by the two marginal
  masses. This removes duplicate `bind`/`map`/`tsum` rearrangements from the two
  parts of Tao's (7.61).
- Proved `six_pow_le_exp_two_mul`, the coarse absorption
  `6^k ≤ exp(2k)` used with the established uniform tilted holding-walk MGF.
- Proved `fpDistPlusP_height_tail_explicitC` and its existential interface.
  The first-passage overshoot and holding-walk height are split at `H/2`; the
  deliberately coarse uniform margin `10000(1+k) ≤ H` absorbs `6^k`.
- Proved `fpDistPlusP_col_tail_explicitC` and its existential interface. Its
  centre is the required p-dependent value `p s/2`, not the fixed-law `s/4`;
  the same linear margin absorbs the appended first-coordinate walk.
- The new headline interfaces report exactly the trusted three axioms. No
  frozen declaration, p-free source, blueprint, judge file, direction file,
  status file, or tool file changed. Proof commit: `fcbf156`.

## Exact verification run

```text
lake build TaoCollatz.Sec7P.ManyTriangles
  Build completed successfully (3323 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.ManyTriangles \
  --axioms TaoCollatz.Sec7P.fpDistPlusP_event_le_add \
  --axioms TaoCollatz.Sec7P.fpDistPlusP_height_tail \
  --axioms TaoCollatz.Sec7P.fpDistPlusP_col_tail
  Build completed successfully (3323 jobs).
  all three axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.Statement \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay
  Build completed successfully (3313 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  axioms: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --import TaoCollatz \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.fpDistPlusP_event_le_add \
  --axioms TaoCollatz.Sec7P.fpDistPlusP_height_tail \
  --axioms TaoCollatz.Sec7P.fpDistPlusP_col_tail
  Build completed successfully (8768 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all four axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

# Proof commit pre-commit hook
lake build
  Build completed successfully (8768 jobs).

./tools/tao_stmt_diff.py eb40bf3fbd956024e99ce3817f42dc467057c1cf HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

rg -n '\\bsorry\\b' TaoCollatz/Sec7P
  exactly the Statement.lean campaign prose/pin and line 142 proof debt

git diff --check
  clean
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer
3/3 closed; Prop 7.3@p modules 3/10 complete plus the Case-3 endpoint-tail
layer; Sec7P sorries 1; differ 46/46 yes; blockers: none operator-level.`

## Current blocker

The convolution seam is no longer a blocker: both (7.61) endpoint tails now
hold uniformly on the full p-window with constants chosen before `p`.

The remaining load-bearing route is the deterministic/probabilistic Lemma 7.10
stack. The immediate missing theorem is tilted apex proximity: port
`encounter_apex_proximity_rpow_at` to `TriangleFamilyP`, replace every `s/4`
centre by `p s/2`, and replace the fixed numeric slope argument by
`slope_margin hp1`. The proof's (7.64) intersection contradiction is the first
place where the thin `p log₂ 3 < 1` margin must be rechecked end to end.

## Next highest-value attack

1. Port `encounter_apex_proximity_rpow_at` (or first its underlying deterministic
   `encounter_apex_proximity`) to `TriangleFamilyP`. Keep `p` for the tilt and
   rename Tao's appended-step count to `k`; the transverse hypothesis is
   `|e.1 - p s/2| ≤ 2 s^0.6`. Use `Sec7P.slope_margin` for the (7.64) budget.
2. Port the separated-encounter row summation at the same moving centre. The
   p-free integer `Gweight` engines can be reused unchanged, while the endpoint
   distribution input is now `fpDistPlusP_col_tail_explicitC`.
3. Assemble tilted `triangle_encounter_le_rpow`, then port `Sec7P/Case3.lean`
   with `t₁=24/25`, `t₂=49/50`, `(1-t₂)^(A+k)` targets, and exponent scaling
   `c=3`. Only after the p-uniform Proposition 7.3 is assembled should
   `pascal_damping_decay` be discharged LAST.
