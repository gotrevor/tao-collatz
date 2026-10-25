# HANDOFF — tilted moving-centre MGF engine landed 🌀 (grind lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 remains closed, and the first analytic
engine for the black-edge row is now proved uniformly over the campaign window.
The sole Sec7P proof debt remains the mandated-LAST `pascal_damping_decay` pin:
**1 sorry + 0 orange nodes**.

## Concrete advance

- Added `TaoCollatz/Sec7P/BlackEdge.lean` and its root import.
- Proved `slope_margin`: from `p ≤ 3/5` and the exact rational comparison
  `3^5 ≤ 2^8`, the moving drift obeys
  `(p/2) log 9 ≤ (24/25) log 2 < log 2`. This is the named uniform margin that
  replaces every fixed-law use of `¼ log 9 < log 2`.
- Proved `gaussExpP_col_tail`, the moving-centre version of the Gaussian times
  growing-exponential column tail. It works for every `0 ≤ r ≤ 3/10`, hence for
  `r = p/2`, with uniform cutoff `m ≥ 100` and rate `c²/200`. The decisive
  geometry is
  `m + 1 - r s ≥ (m - 23)/25` under Tao's budget
  `s log 2 ≤ (m+2) log 9`, giving `1+s ≤ 200(m+1-rs)`.
- Proved the law-independent PMF/Fubini envelope
  `fst_mgf_moving_center_general`, and specialized it as
  `fpDistP_fst_mgf_general` using the uniform tilted column marginal. This is
  the common core for the vanishing-tilt MGF and fixed-tilt Chernoff tail in the
  next checkpoint.
- No frozen declaration, read-only §7 source, blueprint/tool file, or existing
  theorem changed; no `sorry` was added. Proof commit: `e4541c8`.

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
  --axioms TaoCollatz.Sec7P.slope_margin \
  --axioms TaoCollatz.Sec7P.gaussExpP_col_tail \
  --axioms TaoCollatz.Sec7P.fst_mgf_moving_center_general \
  --axioms TaoCollatz.Sec7P.fpDistP_fst_mgf_general
  Build completed successfully (3319 jobs).
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
3/3 closed; Prop 7.3@p modules 3/10 complete plus BlackEdge analytic core in
progress; Sec7P sorries 1; differ 46/46 yes; blockers none.`

## Current blocker

There is no route blocker. `fpDistP_fst_mgf_general` is an envelope, not yet the
sharp vanishing-tilt estimate `≤ 1+δ`: the numeric cutoff argument from
`Sec7/BlackEdge.lean` must be ported with centre `r s`, worst slope `r=3/10`,
and Gaussian rate `c²/200`. The old proof's `exp(A/2)` prefactor becomes safely
`exp(A)`, and its separation condition should use
`log² m ≥ 2A/log(1+δ/2)` so that `r s` consumes at most half the split point.

After that, the fixed-tilt first-coordinate tail can reuse the same envelope.
The holding-law MGF and tail must use `holdP p`; do not copy the fixed-law
`geomQuarter` numerals. `pairThreeProb_mem_window` gives the uniform first-
coordinate success range `[8/125, 36/125]`, while `holdP_exponential_tail`
already supplies a coarser law-uniform Chernoff input.

## Next highest-value attack

1. Port `fpDist_fst_mgf_numeric_at` with the worst moving centre `r ≤ 3/10`,
   then prove the constants-before-`p` interface
   `fpDistP_fst_mgf_le : ∃ Cthr, ∀ p ...` from
   `fpDistP_fst_mgf_general`.
2. Port the fixed-tilt Chernoff bound `fpDistP_fst_tail_le`, again using rate
   `min(c, c²/200)/2` and cutoff at least `100`.
3. Prove uniform `holdP_fst_mgf_le_real` and `holdP_fst_tail_le` from the
   geometric first marginal / existing exponential tail.
4. Define `edgeWeightP` and assemble `fpDistP_edgeWeight_le`; only then proceed
   to the Case-2 white-exit estimate. Keep `pascal_damping_decay` untouched
   until final assembly.
