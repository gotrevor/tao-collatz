# HANDOFF — Sec7P campaign planted 🌀 (operator, 2026-10-25)

**Nothing proved yet; this is the starting baton.**  Branch `ren/sec7p-pascal` (from
`main` @ `95a7172`, the summit + Tier-1 tree).  Build green with exactly two shielded
`sorry`s, both in `TaoCollatz/Sec7P/Statement.lean`.

## Read, in order

1. `DIRECTION.md` — the CURRENT DIRECTIVE (calibration gate first; discharge LAST).
2. `SEC7P-PLAN.md` — the transfer math (§1), window-uniformity discipline (§2), module
   order (§3), node table (§4).
3. Tao's §7 full text: `tmp/ren-tao/tao.txt` (gitignored; never commit it).  §7.1 starts
   line 1736, Prop 7.3 at 1834, §7.3 (holding time) 2092, Lemma 7.7 2178, §7.4 2253.

## Lap-1 plan

- **Calibration gate**: `TaoCollatz/Sec7P/Bridge.lean` + discharge of
  `pascalDamping_half_decay`.  First check whether the target's paired form lets you
  skip the raw-valuation pairing (`cexpect_pairing`) entirely — the bridge may only need
  `pascalWeight (1/2) b = (pascal b).toReal`, `tsum ↔ PMF.iid expect`, and the
  `fPair ↔ fCond` identity, then `prod_fCond_le_damping` + `renewal_white_encounters`.
- Then the p-probability layer (plan §3 rows 1–3).

## Checks every commit

`lake build` · `tools/tao_stmt_diff.py <plant-commit> HEAD` → 46/46 ·
`./tools/blueprint_audit.py` green · sorries only under `TaoCollatz/Sec7P/`.
