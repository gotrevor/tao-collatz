# HANDOFF — vertical localization route refuted at `p = 1/5` 🌀 (grind lap, 2026-10-25)

Branch `ren/sec7p-pascal`. The calibration gate remains discharged (believed
clean, judge to verify), directive step 2 remains closed, and the sole Sec7P
proof debt remains the mandated-LAST `pascal_damping_decay` pin: **1 sorry + 0
orange nodes**. This lap found a route-level blocker in the proposed Case-2
white-exit localization and records it as a `JUDGE-FLAG` in `PENDING_WORK.md`.

## Concrete advance

- Proved `fpDistP_zero` in `Sec7P/Unroll.lean`: zero-budget first passage is
  exactly one `holdP` step. This makes the worst small-budget overshoot regime
  available without unfolding the recursion pointwise.
- Proved `sep_const_lt_two_hundred_thirty_four` in
  `Sec7P/BlackEdge.lean`: the frozen Lemma-7.4 separation is `< 234`.
- Audited the prior handoff's proposed sharp vertical-renewal route before
  formalizing its long coefficient algebra. At `p=1/5`, exact rational
  coefficient arithmetic for

  ```text
  H(z) = q z³ / (1 - P(z) + q z³),   q = 8/125,
  P_b = (b-1)/25 · (4/5)^(b-2)
  ```

  gives

  ```text
  Σ_{y=234}^{400} P(holdP-height = y)
    = 0.14693447040571847… > 1/8.
  ```

  The calculation used `fractions.Fraction`; `sum - 1/8` has a strictly
  positive exact numerator. This is a finite lower bound, so truncation cannot
  invalidate it.
- Combining the two Lean facts with the exact calculation refutes the route:
  every Euclidean localization box has `Y ≤ 233`, while already at budget
  `s=0` its vertical bad event has mass `>1/8`. The suggested `Y=200, X=82`
  cannot work, nor can any alternative `Y` that fits the frozen separation.
- No frozen declaration, existing p-free §7 source, blueprint, judge file,
  direction file, status file, or tool file changed. No `sorry` was added.

## Exact verification run

```text
lake build TaoCollatz.Sec7P.Unroll
  Build completed successfully (3300 jobs).

lake build TaoCollatz.Sec7P.BlackEdge
  Build completed successfully (3319 jobs).

python3 exact-Fraction recurrence probe (p=1/5, heights through 400)
  sum[234..400] = 0.14693447040571847…
  sum[234..400] > 1/8 = True

~/personal/bin/lean-green ~/src/tao-collatz-sec7p \
  --import TaoCollatz \
  --axioms TaoCollatz.Sec7P.pascalDamping_half_decay \
  --axioms TaoCollatz.Sec7P.fpDistP_zero \
  --axioms TaoCollatz.Sec7P.sep_const_lt_two_hundred_thirty_four
  Build completed successfully (8763 jobs).
  proof debt: exactly TaoCollatz/Sec7P/Statement.lean:139:8
  all three axiom sets: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

./tools/tao_stmt_diff.py eb40bf3 HEAD
  character-identical (46/46)

./tools/blueprint_audit.py
  26 nodes proved + axiom-clean; 0 orange; 0 drift; 0 false-green

git diff --check
  clean
```

## Campaign state

`sec7p: calibration proof landed (believed clean, judge to verify); prob-layer
3/3 closed; Prop 7.3@p modules 3/10 complete plus the Case-2 analytic package
through endpoint and transverse localization; Sec7P sorries 1; differ 46/46
yes; blocker: proposed vertical localization inequality false at p=1/5.`

## Current blocker

**JUDGE-FLAG:** the current Case-2 assembly route

```text
vertical overshoot tail + transverse tail + Euclidean separation
```

cannot prove the required uniform white-exit mass. The obstruction is in the
frozen window, not constant slop: at `p=1/5` the holding law has mean height
`156.25`, and its zero-budget overshoot retains more than `1/8` mass above every
vertical radius compatible with the fixed separation.

This does not refute `pascal_damping_decay`; it refutes the current transfer
step. A new geometric decomposition would have to use the correlation that
tall endpoints near `p=1/5` have strongly negative transverse displacement,
rather than union-bounding their vertical height in isolation. Changing the
window or frozen target is operator-owned.

## Next highest-value attack after an operator ruling

If the frozen target is retained, replace the rectangular/Euclidean
localization kernel with a sloped safe-region lemma that directly combines
height and transverse displacement. Start from the already-proved
`fpDistP_transverse_tiltZ_le_one` and inspect whether the start-triangle
projection can move down a sloping face for tall endpoints. Do **not** spend a
lap formalizing the `Y≈200` vertical renewal bound: the exact endpoint calculation
above proves that bound false.
