# HANDOFF — tilted Lemma 7.10 apex confinement closed 🌀 (grind lap, 2026-10-26)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 and the complete Case-2 contraction
remain closed, and the sole Sec7P proof debt remains the mandated-LAST
`pascal_damping_decay` pin: **1 sorry + 0 orange nodes**.

## Concrete advance

- Proved `tilted_apex_face_budget`, the moving-centre version of Tao's (7.64):
  `(p s/2 + 2s^0.6) log 9 ≤ s log 2` uniformly for `p ≤ 3/5` and
  `s ≥ 10^8`. The `24/25` slope margin leaves exactly the uniform room needed
  for the localization error.
- Proved `apex_size_budget_of_deep`, sharpening the fixed-law proof's coarse
  encounter estimate from `A²(1+k) ≤ 3s/25` to `A²(1+k) ≤ s/100`. This is
  forced by the lower endpoint `p=1/5`, whose moving centre is only `s/10`;
  the stronger estimate follows directly from `m^0.4 ≤ m^0.8 < s`.
- Proved `tilted_apex_horizontal_room`, which absorbs the localization and
  encounter-scale errors beneath `(p/2)s` uniformly for `p ≥ 1/5`.
- Ported the full deterministic (7.63)–(7.65) intersection argument as
  `encounter_apex_proximityP_rpow_at` over `TriangleFamilyP`, and added the
  uniform existential interface `encounter_apex_proximityP_rpow`. The two
  slope-sensitive sites now close across the entire Pascal window.
- All five new declarations report exactly the trusted three axioms. No frozen
  declaration, p-free source, blueprint, judge file, direction file, status
  file, or tool file changed.

## Exact verification run

```text
lake build TaoCollatz.Sec7P.ManyTriangles
  Build completed successfully (3323 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.ManyTriangles \
  --axioms TaoCollatz.Sec7P.tilted_apex_face_budget \
  --axioms TaoCollatz.Sec7P.apex_size_budget_of_deep \
  --axioms TaoCollatz.Sec7P.tilted_apex_horizontal_room \
  --axioms TaoCollatz.Sec7P.encounter_apex_proximityP_rpow_at \
  --axioms TaoCollatz.Sec7P.encounter_apex_proximityP_rpow
  Build completed successfully (3323 jobs).
  all five axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.Statement \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.encounter_apex_proximityP_rpow
  Build completed successfully (3313 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  both axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --import TaoCollatz \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.encounter_apex_proximityP_rpow
  Build completed successfully (8768 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  both axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

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
3/3 closed; Prop 7.3@p modules 3/10 complete plus the Case-3 endpoint-tail and
apex-confinement layers; Sec7P sorries 1; differ 46/46 yes; blockers: none
operator-level.`

## Current blocker

The thin tilted slope margin in apex confinement is no longer a blocker. The
key correction was to use the actual deep-regime estimate
`A²(1+k) ≤ s/100`; carrying the fixed-law proof's coarse `3s/25` estimate
would falsely exhaust the horizontal centre at `p=1/5`.

The immediate missing theorem is the separated-encounter row sum (X10b). Its
geometry is p-free after centring, but its distributional input must be the
new moving-centre tail `fpDistPlusP_col_tail_explicitC`. Once X10b is ported,
the two endpoint tails plus X10a/X10b feed the tilted
`triangle_encounter_le_rpow` assembly.

## Next highest-value attack

1. Port `encounter_separated_sum_core` and its explicit/existential interfaces
   to `TriangleFamilyP`, using the existing p-free `Gweight` integer-row
   engines and `fpDistPlusP_col_tail_explicitC` at centre `p s/2`.
2. Assemble tilted `triangle_encounter_le_rpow`, then the pinned (7.60)-shaped
   `triangle_encounter_le` interface needed by the few-white stack.
3. Build `Sec7P/Case3.lean` with `t₁=24/25`, `t₂=49/50`,
   `(1-t₂)^(A+k)` probability targets, and exponent scaling `c=3`. Assemble
   p-uniform Proposition 7.3, and discharge `pascal_damping_decay` LAST.
