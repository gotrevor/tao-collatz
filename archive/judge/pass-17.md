# Judge pass 17 (2026-07-12 ~21:45 EDT, Ren/Fable — lap-56 boundary + lap-57 re-pin, `2d9747c..3c95898`) — MASS DEMAND SATISFIED ✅; KERNEL DERIVED

Scope: lap 56 (kernel decomposition, 3 commits) + lap 57's opening commit (the
demanded re-pin) + handoff `be46176`.

## The steering channel worked

`3c95898` is character-exact to the pass-16 pre-authorization: the deep pin's
binder `1/2 < p₀` → `51/100 ≤ p₀`, docstring updated with the judge reason, one
proof-plumbing adaptation in `many_triangles_white` (`lt_min` now via
`by linarith`). Arithmetic: `ε₀ = min(1/100, (2·(51/100)−1)/2) = 1/100 ≥ 10⁻⁴`.
**Re-ratified on the diff; the ε₀-floor obligation is DISCHARGED at the
statement level.** BLUEPRINT §2 demand item retired.

## Kernel decomposed — (7.50)-geometry route, one tail left

`fpDist_white_exit_deep` now has a real proof body: whiteness = in-strip ∧
outside-every-triangle (cover), so the mass bound splits as
`P(white∩strip) ≥ 1 − P(out of strip) − P(phase point in some family triangle)`.

- **`fpDist_col_le`** (column marginal off X6's location bound) — PROVED,
  judge-run clean.
- **`fpDist_out_of_strip_le`** (Fubini + column marginal + (7.52) budget) —
  PROVED, judge-run clean.
- **`fpDist_any_triangle_le`** (NEW PIN, :1836): the endpoint's phase point
  lies in ANY family triangle with mass ≤ 1/8. **Ratified as a route
  decomposition** (~85% provable): this is the quantitative form of p.48's
  (7.50)/(7.51) step — the endpoint lands at distance O(1) above the triangle
  top, and X3's separation + the (7.11) slope bound exclude the other
  triangles; same X6+S3 machinery as the two proved siblings. The 1/8 is a
  route numeral: `1 − P(out) − 1/8 ≥ 51/100` needs `P(out) ≤ 0.365` — wide
  margins on both sides.

Dated runs: `fpDist_white_exit_deep` sorryAx (via exactly the new tail),
`many_triangles_white` sorryAx (same trail), both sub-lemmas + the re-pin
plumbing clean.

## Hygiene (/lean-review, range `2d9747c..3c95898`)

✅ CLEAN — 335 added lines, zero registry hits: no `maxHeartbeats`, no
`native_decide`, no new `axiom`, no `unsafe`/`partial`/`implemented_by`/
`extern`/`opaque`, no linter silencing, no bare `#print axioms`, no Prop-def
laundering. New sorries: exactly the one named decomposition pin. Build clean
over the recompiled module (only the expected Statement.lean campaign stubs).

## State after this pass

§7 chain to Prop 1.17 now hangs on: `fpDist_any_triangle_le` (X9's last tail),
X10's separated-Σ assembly, X8's two kernels + two case assemblies. When the
tail lands, X9 completes END-TO-END (many_triangles_white axiom-clean) and the
kernel-merge plan derives X8's Case-2 twin from the deep kernel for free.
