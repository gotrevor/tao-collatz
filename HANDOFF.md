# HANDOFF — tilted Case-2 white exit landed 🌀 (grind lap, 2026-10-26)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 remains closed, and the sole Sec7P
proof debt remains the mandated-LAST `pascal_damping_decay` pin: **1 sorry + 0
orange nodes**.

## Concrete advance

- Ran the binding calibration gate before edits. The half-decay theorem still
  reports exactly `[propext, Classical.choice, Quot.sound]`, the target build
  was green, and the frozen declaration differ reported 46/46 character-identical.
- Added `whiteSetP` and `whiteStripP` to `Sec7P/ManyTriangles.lean`. They use
  the finer `whiteP` predicate and retain Tao's renewal-to-phase column shift.
- Proved `fpDistP_out_of_strip_le`, uniformly for `p ∈ [1/5,3/5]`. The proof
  specializes `fpDistP_fst_tail_le` at `A=1`, `δ=1/8` and compares the actual
  overshoot event `m < e₁` with the stronger fixed-tilt event `m < 4e₁`.
- Proved `fpDistP_white_exit` with uniform mass `p₀=3/4`. The proof ports the
  p-free cover/indicator decomposition: total mass one minus the `≤1/8`
  out-of-strip event minus the `≤1/8` finer-family capture event is supported
  on `whiteStripP`.
- No frozen declaration, existing p-free §7 source, blueprint, judge file,
  direction file, status file, or tool file changed. No `sorry` was added.

## Exact verification run

```text
# Calibration, before edits
~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.Statement \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay
  Build completed successfully (3313 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  axioms: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

./tools/tao_stmt_diff.py eb40bf3fbd956024e99ce3817f42dc467057c1cf HEAD
  character-identical (46/46)

lake build TaoCollatz.Sec7P.ManyTriangles
  Build completed successfully (3323 jobs).

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --target TaoCollatz.Sec7P.ManyTriangles \
  --import TaoCollatz.Sec7P.ManyTriangles \
  --axioms TaoCollatz.Sec7P.fpDistP_out_of_strip_le \
  --axioms TaoCollatz.Sec7P.fpDistP_white_exit
  Build completed successfully (3323 jobs).
  both axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --import TaoCollatz \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.fpDistP_out_of_strip_le \
  --axioms TaoCollatz.Sec7P.fpDistP_white_exit
  Build completed successfully (8767 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all three axiom sets: [Classical.choice, Quot.sound, propext]
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
3/3 closed; Prop 7.3@p modules 3/10 complete, with BlackEdge analytic inputs
and the ManyTriangles Case-2 white-exit path now closed; Sec7P sorries 1;
differ 46/46 yes; blockers: none operator-level.`

## Current blocker

The finer-scale Case-2 geometry is no longer a blocker: localization, foreign
triangle exclusion, out-of-strip control, and positive `whiteP` exit mass are
all kernel-checked uniformly in `p`.

The immediate interface mismatch is downstream. `QP`, `edgeWeightP`, and the
uniform edge-weight estimate are already law-parametric, but `QPm` and
`QP_fp_endpoint_le` in `Sec7P/Monotone.lean` / `Sec7P/BlackEdge.lean` are still
specialized to Tao's old `whiteSet` and `epsBW`. The new white-exit theorem is
about `whiteSetP`/`whiteStripP` and the final finer damping uses `epsP`, so the
supremum/endpoint layer must be parameterized by the white set (or copied into
a clearly named finer-scale sibling) before the Case-2 assembly can consume it.
This is a formal interface port, not an operator decision.

## Next highest-value attack

1. Generalize the `QPm` supremum lemmas (`le_QPm`, `QP_le_QPm`, nonnegativity,
   and the boundary value) over an arbitrary white set while preserving the
   existing wrappers byte-for-byte outside `Sec7P/`.
2. Port `QP_fp_endpoint_le` at `whiteSetP`/`whiteStripP` and `epsP`.
3. Copy the algebraic `Q_black_edge_case2` assembly with
   `fpDistP_white_exit` + `fpDistP_edgeWeight_le`; then continue into the deep
   ManyTriangles/Case-3 route. Do not touch `pascal_damping_decay` until
   Proposition 7.3@p is closed.
