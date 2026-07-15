# Handoff: C9's C10 seam (B2 `harmZfine_to_mainZ`) FULLY PROVED, axiom-clean

**Date**: 2026-07-15. **Branch** `main`, **HEAD `ece1f36`**. Build 🟢 green (full `lake build`, 3324
jobs). Tree clean, nothing uncommitted.
**Read `DIRECTION.md` first** — its CURRENT DIRECTIVE (close C9 = `harmonic_to_Z` = C10 seam → C6 →
headline) is now substantially FULFILLED on the C10 side. Campaign order `C10 ✅ → C8 ✅ → C7 ✅ →
C9 (live) → C6 → headline`.

## This lap: the whole C10 seam closed (5 green commits)

Coming in: 8 sorries, `cn_bound` integral-test core proved but not assembled, B2 (C10 seam) an
un-decomposed `sorry`. This lap drove the directive's stated crux to completion:

1. `30c5f68` — **`cn_bound` PROVED** (crude `c_n ≤ 4·log^{0.7}x`), axiom-clean. New helper
   `cn_window_size` (the (5.10) window arithmetic: `2·3^k+2 ≤ lo`, `2·lo ≤ hi`, `hi = exp(2log^{0.7}x)·lo`,
   from `3^k ≤ x^{1/5}` + sub-linear gain `log^{0.7}x ≤ (1/8)log x`). Assembly: Eprime-mask ≤ window-mask
   → `harmonic_class_window_bound` → ×`3^{n−m₀}` → `≤ log2 + 2log^{0.7}x + 1 ≤ 4log^{0.7}x`.
2. `183a1f3` — **B2 decomposed**: `harmZfine_to_mainZ` proved from ONE sub-`sorry`
   (`harmZfine_sub_mainZ_le_osc`) + `fine_scale_mixing` (C10) + new `mZero_ge_lin`
   (`m₀ ≥ log x/200000`). The osc→log^{−1} log-arithmetic (A=1.7 ⟹ net `log^{−1}`) fully machine-checked.
3. `ece1f36` — **B2 CORE PROVED**: `harmZfine_sub_mainZ_le_osc` discharged, so the WHOLE seam
   `harmZfine_to_mainZ` is axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`,
   NO `sorryAx`). **C10's fine-scale mixing now demonstrably composes with §5's harmonic sum in Lean.**

### The 4 new seam lemmas (all axiom-clean, in `Sec5/Stabilization.lean`)
- **`harmonic_reindex`** (~366) — reusable fiber-partition: `∑'_M [Eprime] W(M mod q)·M⁻¹ =
  ∑_X W(X)·classMass(X)` via `Summable.tsum_mul_left` + `Summable.tsum_finsetSum` + `Finset.sum_ite_eq`.
- **`harmZfine_eq_sum_cn`** (~800) / **`mainZ_eq_sum_fiber_cn`** (~830) — Tao (5.22–5.23) reindex
  identities. mainZ's coarse residue `M mod 3^{m₀} = castHom(M mod 3^{n−m₀})` (`map_natCast`); `3^{m₀}`
  splits as `3^{m₀−(n−m₀)}·3^{n−m₀}` (`zpow_add₀`), latter absorbed into `c_n`.
- **`osc_syracZ_eq_sum_dev`** (~855) — osc's coarse fiber sum IS the `syracZ(m₀)` marginal
  (`syracZ_map_cast` + `PMF.map_apply`), so `osc = ∑_X|syracZ(n−m₀)(X) − fiber_avg(X)|`.
- **`cn_class_summable`** (~750), **`cn_nonneg`** (~880) — support/positivity of the class weight.

## State: 6 sorries + 0 orange (4 in `Sec5/Stabilization.lean` + 2 headlines)

C9 spine — **all remaining holes are NON-C10** (C10 fully discharged from C9):
- **`perNHarmonic_eq_harmZfine_approx` (B1, :~749)** — the geomHalf→`syracZ` reindex. `perNHarmonic ≈
  harmZfine` up to `O(log^{−c})`. Content (see its docstring): `syracZ_eq_rev_fnat` writes `syracZ(n−m₀)`
  as pushforward of iid geomHalf under `ā ↦ fnat·2^{−pre ā} mod 3^{n−m₀}`; the residual over non-good
  tuples is `approx_good_tuple_whp` (PROVED). **Consumes `cn_bound` (`sup c_n ≤ 4log^{0.7}`) × the
  `log^{−1}` whp decay. Does NOT consume C10.** This is now the route-decisive remaining C9 hole.
- **`Iy_count_ratio` (:~1070)** — (5.9) lattice count. Self-contained, cheapest.
- **`mainZ_bound` (:~305)** — `|mainZ| ≤ C`. Small.
- **`perNTerm_harmonic_approx` (:~334)** — pure (5.19) analytic. Self-contained.
- `Statement.lean:24,31` — the two headline stubs, frozen; discharge when C6 lands.

`harmonic_to_Z` PROVED from B1+B2; `perNTerm_eval` PROVED from `perNTerm_harmonic_approx`+`harmonic_to_Z`.
So B1 + the two analytic leaves finish C9's dependency on §5, then `Iy_count_ratio` → C9 axiom-clean.

## Next steps — hardest-first
1. **B1 `perNHarmonic_eq_harmZfine_approx`** — the last genuinely-structural C9 hole. Pattern mirrors B2:
   likely a `harmonic_reindex`-style regroup on the ā-side plus the `approx_good_tuple_whp` good-restriction.
   Check `syracZ_eq_rev_fnat`, `approx_good_tuple_whp`, `fnat_lt_pow_mul`, `syracZ_eq_rev_fnat` for the
   exact map. May decompose into sub-`sorry`s (reindex identity + whp residual) like B2 did.
2. Then `mainZ_bound`, `perNTerm_harmonic_approx`, `Iy_count_ratio` (all self-contained) → C9 axiom-clean.
3. Then C6 (§3 reduction Thm 1.3⟸1.6⟸3.1⟸Prop 1.11) → headline.

## Rails / notes
- **Do NOT edit ratified pins** (C7/C8/C10 statements, `stabilization`, the two headlines) or frozen
  constants. The internal decompositions below `stabilization` (B1/B2/`cn`/`cn_bound`/`harmonic_reindex`/
  the reindex identities/`osc_syracZ_eq_sum_dev`/`mZero_ge_lin`) are NOT blueprint nodes — editing them is fine.
- **mathlib/instance gotchas this lap** (corpus-worthy, in `PENDING_WORK.md`): `set a := e` is NOT
  reliably defeq — keep shared subterms explicit; **dependent-type rewrite** (`rw [← hk]` where the folded
  term is in `ZMod (3^…)`) → "motive not type correct" — don't fold it; multi-line `if…else 0` as a `calc`
  head mis-parses — parenthesize; `if`-instance clash (`ZMod.decidableEq` vs `Classical.propDecidable`,
  e.g. `osc`/`PMF.map_apply` vs `open Classical`) → use `by_cases`+`if_pos`/`if_neg` (instance-agnostic)
  NOT `if_congr`/`simp [sum_filter]`; `Summable.tsum_finsetSum` (not `tsum_sum`) for finite-sum↔tsum swap;
  `Summable.tsum_le_tsum` is dot-form; `1=1^(1/5)` via `rw` rewrites the `1` in `1/5` — use `calc`+`Real.one_rpow`.
- Axiom recipe: `TaoCollatz/ZZ_ax.lean` importing the module + `#print axioms TaoCollatz.<name>`, `lake env
  lean` it, `rm -f`. `git-safe` at `~/personal/bin/git-safe` (export PATH). Bare `git` is hook-blocked.

## Work report
**6 sorries + 0 orange** (was 8). **C10's entire involvement in C9 is now PROVED and axiom-clean** —
`harmZfine_to_mainZ` and all four supporting seam lemmas verify `[propext, Classical.choice, Quot.sound]`.
The directive's crux ("the last genuine unknown-unknown in C9") is settled in the kernel. Remaining C9 work
is B1 (geomHalf→syracZ reindex, no C10) + three self-contained analytic/combinatorial leaves → C9 clean → C6.
