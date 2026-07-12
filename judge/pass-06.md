## Judge pass 6 (2026-07-12 ~15:00 EDT, Ren/Fable + PDF pp.46–49 — handoff `897ad3b`) ⚖️

Scope: campaign laps 46–48 (eighth box session). Two fronts: X8/X10 statement design
(`Sec7/BlackEdge.lean`) and the X6 renewal reduction (`Sec7/FpLocation.lean`).

**Paper front OPENED and read: pp.46–49** (Cases 1–3 of Prop 7.8, (7.42)–(7.56)).
Ratifications vs the PDF:
- `Q_black_edge_case2` ((7.44)–(7.51) Case 2, conclusion = the (7.41) shape
  `Q ≤ m^{-A}·Q_{m-1}` under `s ≤ m/log²m`) — RATIFIED. Renewal→phase shift `j↦j-1`
  consistent with the pass-2 Q-cluster ratification.
- `Q_fp_endpoint_le` ((7.46) endpoint step) — RATIFIED + PROVED. Subtraction form
  `1-(1-e^{-ε³})·1_W` ≡ the paper's `exp(-ε³·1_W)` on {0,1}; the extra Hold step
  (edgeWeight) is the paper's own (7.35)+(7.38) mechanism, constants-equivalent to the
  abbreviated display.
- `fpDist_edgeWeight_le` ((7.42)+(7.48)/(7.49) composite, `≤(1+δ)m^{-A}`) — RATIFIED.
- `fpDist_white_exit` ((7.50)/(7.51), absolute `p₀`, uniform) — RATIFIED, with a noted
  STRENGTHENING: Lean requires white AND in-strip (the damping mechanism needs it; the
  paper leaves in-strip implicit). Extra proof burden, not a faithfulness risk.
- `budget_le_of_mem_triangle` ((7.52)) — RATIFIED + PROVED; lattice slack `(m+2)` for the
  paper's `m`, documented; Case 3 hypothesis carries the matching slack.
- `Q_black_edge_case3` ((7.53)–(7.67) interface) — RATIFIED as the Case-3 entry statement
  (X9/X10/X11 subtree discharges it; Lemmas 7.9/7.10 pp.50–54 remain UNREAD/unstated).
- `Q_black_edge` (case split over the family, black starts) — PROVED from the two cases;
  conditional on their sorries by design.

**Moved-statement audit**: `prop_7_8`, `Q_polynomial_decay` (Monotone→BlackEdge) and
`fpDist_location_bound` (Unroll→FpLocation) — all character-for-character IDENTICAL to
the ratified versions. Bindings unaffected (names unchanged).

**Dated judge-run `#print axioms`** (all = [propext, Classical.choice, Quot.sound]):
`exists_triangleFamily`, `Q_fp_endpoint_le`, `budget_le_of_mem_triangle`,
`edgeWeight_of_deep`, `one_le_Qm`, `fpDist_le_renewal_conv`, `sum_range_exp_neg_sq_le`,
`sum_abs_AP_le`, `renewal_weight_sum_le`, `Gweight_factor`. Ten for ten.

**Flips**: X8 `\notready` → statement-`\leanok` + bindings (TriangleFamily,
Q_black_edge_case2, Q_fp_endpoint_le, fpDist_edgeWeight_le, fpDist_white_exit,
budget_le_of_mem_triangle); re-rated 12–25/high/70% → 8–16/medium/75%. X6 re-rated
10–20/high/70% → 4–10/medium/80% (reduction to `renewalMass_bound` + last-step PROVED).
X7 gains the `Q_black_edge` binding; X11 gains `Q_black_edge_case3`. X9/X10 stay
`\notready` (Lemmas 7.9/7.10 not yet stated in Lean). Graph: 20 green borders / 5 orange.

**Sorry census**: BlackEdge 4 kernels (weight degradation, white-exit, case2 assembly,
case3) + FpLocation 2 (renewalMass_bound, fpDist_location_bound) = the entire §7.4
frontier; everything else in Sec7 is sorry-free.

