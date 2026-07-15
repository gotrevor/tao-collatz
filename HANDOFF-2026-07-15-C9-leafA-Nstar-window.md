# Handoff: C9 leaf A — N* window membership PROVED; operator note landed

**Date**: 2026-07-15. **Branch** `main`, **HEAD `cdd023c`**. Build 🟢 green (full `lake build`).
**Read `DIRECTION.md` first** — note the NEW **operator note (2026-07-15)**: review laps off,
vocabulary rail (register coined sub-lemma names on the blueprint same-pass), and **C6 intermediate
pinning is the outstanding structural item, ordered BEFORE the C9 census hits zero.**

## This lap (3 green commits: `bafc3fb` rib 1 / `0e1486c` decomposition / `cdd023c` N* window)

1. **B1 CLOSED** — rib 1 `perNHarmonic_eq_sum_cn` proved (see HANDOFF-…-C9-B1-CLOSED.md);
   `perNHarmonic_eq_harmZfine_approx` axiom-clean.
2. **Leaf A (`perNTerm_harmonic_approx`, Tao 5.19) decomposed**: `pre_pos`, `fnat_odd`,
   `Nstar_odd`, `perNHarmonic_le` all PROVED; statement relocated below its new prerequisites.
3. **`Nstar_mem_logWindow` PROVED** (the (5.18) crux): N* = (M·2^pre − fnat)/3^k lands in the odd
   window [y, y^α].  Two-sided log(M·2^pre) bounds (E' window ± log^{0.7}; good prefix ± log^{0.6};
   2k·log2 = k·log(4/3)+k·log3; Iy margins ± log^{0.8}); margin inequality needs log x ≥ 2^{30}
   (x₀ = exp 1073741824).  `-- HEARTBEAT: 1.6M` justified in-file.  All believed axiom-clean
   `[propext, Classical.choice, Quot.sound]`, judge to verify.

**NOTE on `cdd023c`:** it also carries two operator-authored hunks that appeared in the working
tree mid-lap (DIRECTION.md 🪷 operator note; content.tex C9B1/C9B2 registration) — swept in by
`git add -A`. Content is the operator's own directive layer; flagged here for transparency.

## State: **5 sorries + 0 orange** (+ C6 un-pinned surface per operator note)

- `perNTerm_harmonic_approx` (leaf A assembly) — ALL ingredients now in hand:
  `perNTerm_pointmass` → `logUnifOdd_apply_toReal_of_mem` (membership via `Nstar_odd` +
  `Nstar_mem_logWindow`) → (N*)⁻¹ = 3^k/(M·2^pre−fnat) with relative error ≤ 2·3^k/M ≤ x^{-c}
  (`fnat_lt_pow_mul`, `2·fnat ≤ M·2^pre`) → 1/D vs 1/norm swap (`windowMass_estimate`,
  `windowMass_ge_clog`) → absolute errors via `perNHarmonic_le`.  Assembly plan: termwise
  (1−ε)·t2 ≤ t1 ≤ (1+ε)·t2 with t2 = 3^k·(2^pre)⁻¹·M⁻¹/norm, ε ≍ log^{-0.3}; two-sided tsum
  monotonicity (avoid tsum_sub), summability via `cn_class_summable`/`iid_fiber_summable` patterns.
- `mainZ_bound` (:302) — mirror `cn_bound`'s integral test at coarse scale m₀ (likely easiest).
- `Iy_count_ratio` — (5.9) window count.
- `Statement.lean:24,31` — frozen headlines (C6).

## Next steps (directive-ordered)

1. **Register leaf-A sub-lemma names on the blueprint** (vocabulary rail, content.tex): a `C9A`
   node for `perNTerm_harmonic_approx` (\notready), prose-citing Nstar_* sub-lemmas — same-pass
   rule already owed from this lap.
2. **Finish leaf A assembly** (plan above), then `mainZ_bound`, `Iy_count_ratio`.
3. **PIN the C6 intermediates** (§3 reduction: Thm 1.3 ⟸ 1.6 ⟸ 3.1 ⟸ Prop 1.11) — statement-only,
   copy-not-compose against the PDF, + numeric traps in `tools/check_blueprint.py`. Operator
   orders this BEFORE C9 census reaches zero — do not close the last C9 leaf before pinning C6.

## Rails
- Operator note binds: no review laps; JUDGE-FLAG via PENDING_WORK.md; never self-`\leanok`.
- Do NOT edit ratified pins or frozen constants. `git-safe` (bare git hook-blocked); prefer
  targeted `git-safe add <files>` over `-A` (operator may write to the tree mid-lap).
