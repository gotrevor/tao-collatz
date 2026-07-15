# Handoff: C9 B1 decomposed — rib 2 FULLY PROVED, rib 1 bridge landed

**Date**: 2026-07-15. **Branch** `main`, **HEAD `295e08a`**. Build 🟢 green (full `lake build`,
3324 jobs). Tree clean, nothing uncommitted.
**Read `DIRECTION.md` first** — CURRENT DIRECTIVE = close C9 (`harmonic_to_Z` = C10 seam DONE) → C6 →
headline. Campaign order `C10 ✅ → C8 ✅ → C7 ✅ → C9 (live) → C6 → headline`.

## This lap: B1 (the route-decisive C9 reindex) decomposed and largely closed (4 green commits)

Coming in: B1 `perNHarmonic_eq_harmZfine_approx` (Tao 5.20, geomHalf→syracZ reindex) was ONE opaque
`sorry` — the directive's flagged "last genuinely-structural C9 hole." This lap drove it from an
opaque sorry to a proved assembly + fully-proved rib 2 + rib 1's Lemma-2.1 bridge.

1. `3da7edc` — **B1 DECOMPOSED + assembly PROVED.** New def `perNGoodMass` (good-restricted syracZ
   pushforward mass). B1 = `perNHarmonic_eq_harmZfine_approx` proved sorry-free via L¹×L∞ Hölder from
   two ribs: `harmZfine`/`perNHarmonic` both reindex to `∑_X (mass)·c_n(X)`; `0 ≤ c_n ≤ Ccn·log^{0.7}`
   (cn_bound/cn_nonneg) × the `log^{-1}` whp residual → net `log^{-0.3}`.
2. `823d0fb` — **rib 2 STRUCTURAL half PROVED.** `perNGoodMass_eq_iid` (good ⟹ 2^{-pre}=iid mass),
   `syracZ_toReal_eq_tsum_fnat` (PMF.map_apply pushforward form), `iid_fiber_summable`. rib 2
   `syracZ_sub_perNGoodMass_bound` reduced to the analytic `good_tuple_whp_iid` via the fiber-count-1
   telescoping `∑_X ([F=X]−[good∧F=X]) = [¬good]`.
3. `7c274c4` — **rib 2 FULLY PROVED + axiom-clean.** `good_tuple_whp_iid` closed: ℙ(¬good) ≪ log^{-1}
   under `geomHalf.iid k`, the iid half of `goodTuple_prefix_dev_sum` with NO dTV transfer (coord-zero
   event has iid mass 0; prefix deviations via `geomHalf_tail_bound`×`iid_prefix_twosided_eq` summed
   over ≤ k+1 ≤ log x prefixes, then the log·exp(−κ log^{0.2}) ≤ log^{-1} shrink). Both `good_tuple_whp_iid`
   and `syracZ_sub_perNGoodMass_bound` verify `[propext, Classical.choice, Quot.sound]`.
4. `295e08a` — **rib 1 bridge landed.** `two_mul_inv_zmod_three_pow` (2 is a unit mod 3^k) +
   `solvable_iff_fmapZ`: given the guard `fnat ≤ M·2^{pre ā}`, the ℕ affine divisibility
   `3^k ∣ (M·2^{pre}−fnat)` ↔ `M mod 3^k = F ā = (fnat)·2^{-pre}`. This is Lemma 2.1 pointwise.

## State: 4 sorries in Stabilization + 2 headlines = 6

- **`perNHarmonic_eq_sum_cn` (B1 rib 1, `Stabilization.lean:993`)** — THE remaining B1 piece. The (5.22)
  fiber identity `perNHarmonic x E n = ∑_X perNGoodMass x n X · c_n(X)`. Pure reindex, NO probability,
  NO C10. **This is the next attack.**
- `mainZ_bound` (:302), `perNTerm_harmonic_approx` (:328), `Iy_count_ratio` (:1434) — self-contained
  analytic/combinatorial leaves.
- `Statement.lean:24,31` — the two headline stubs, frozen; discharge when C6 lands.

## Next steps — hardest-first

1. **Finish rib 1 `perNHarmonic_eq_sum_cn`.** Building blocks all in hand (`solvable_iff_fmapZ`,
   `cn_class_summable`, `iid_fiber_summable`, `perNGoodMass_eq_iid`). **Plan:**
   - ADD hypotheses `(hx : Real.exp 1024 ≤ x) (hkn : n - mZero x ≤ nZero x)` to the statement — needed
     because the solvable↔congruence equivalence requires `3^k ≤ M` for `M ∈ E'`, which only holds for
     large x via the window (`cn_window_size` gives `2·3^k+2 ≤ lo ≤ M`). The ASSEMBLY
     `perNHarmonic_eq_harmZfine_approx` (`:1227`) already has both: its `cn_bound` x₀ = `exp 1024`
     (so `hxcn : exp 1024 ≤ x`), and `n ∈ Iy → n ≤ nZero x` (`mem_Iy_le_nZero`) gives `hkn`. So update
     the assembly's `rw [perNHarmonic_eq_sum_cn]` → `rw [perNHarmonic_eq_sum_cn x E n hxcn hkn']`.
   - Proof route (both sides = `3^k · ∑'_ā if good then (2^{pre})⁻¹·Sm(F ā) else 0`, `Sm X = ∑'_M
     [E'∧M≡X] M⁻¹`, `cn = 3^k·Sm`):
     - LHS: rewrite perNHarmonic's inner mask `good∧E'∧solvable` to `good∧E'∧(M:ZMod)=F ā` via
       `solvable_iff_fmapZ` + the automatic guard (`fnat_lt_pow_mul` + `3^k ≤ M`); then on good ā,
       collapse the M-sum: `∑'_M [E'∧(M:ZMod)=F ā] (2^{pre})⁻¹·M⁻¹ = (2^{pre})⁻¹·Sm(F ā)` (tsum_mul_left).
     - RHS `∑_X perNGoodMass(X)·cn(X) = 3^k·∑_X perNGoodMass(X)·Sm(X)`: pull Sm(X) into the ā-tsum
       (`Summable.tsum_mul_left`), swap `∑_X`↔`∑'_ā` (`Summable.tsum_finsetSum`), collapse `∑_X` (only
       X=F ā survives, `Finset.sum_ite_eq`) → `3^k·∑'_ā if good then Sm(F ā)·(2^{pre})⁻¹ else 0`.
     - Equate LHS/RHS via `mul_comm`. Mirror `harmonic_reindex` (`:367`) for the ā-side fiber partition.
   - Gotchas hit this lap (see below): `set F/Sm` fold-timing (set folds occurrences at set-time only;
     later `rw [perNGoodMass_eq_iid]` produces UNFOLDED expr → use `simp only [← hFv]` to re-fold, or
     don't `set` and write explicit). Consider defining `Sm` inline / via `have hcnSm : cn = 3^k·Sm`.
2. Once rib 1 lands → **B1 fully proved → C9's §5 dependency is B1+B2(done)+leaves.** Then the three
   self-contained leaves (`mainZ_bound`, `perNTerm_harmonic_approx`, `Iy_count_ratio`) → C9 axiom-clean.
3. Then C6 (§3 reduction Thm 1.3⟸1.6⟸3.1⟸Prop 1.11) → headline.

## Rails / notes
- **Do NOT edit ratified pins** (C7/C8/C10 statements, `stabilization`, the two headlines) or frozen
  constants. Everything below `stabilization` (B1/B2/ribs/`perNGoodMass`/`cn`/helpers) is NOT a blueprint
  node — editing/adding is fine. NOTE: adding hypotheses to `perNHarmonic_eq_sum_cn` is fine (internal
  decomposition, judge-cross-read pending), but keep the ASSEMBLY `perNHarmonic_eq_harmZfine_approx`
  statement intact (it's the B1 pin below `stabilization`).
- **mathlib/instance gotchas this lap** (corpus-worthy): `ENNReal.zero_toReal` does NOT exist — use
  `ENNReal.toReal_zero`; `set f := fun a => e with hf` leaves `f a` un-beta after `rw [hf]` →
  `split_ifs`/`if_pos` fail; use `simp only [hf]` (beta-reduces) or `by_cases` instead; `split_ifs` on
  `if ¬P` may flip branch order → prefer explicit `by_cases`; `tsum_add`/`tsum_eq_zero_of_forall_eq_zero`
  are NOT top-level — use `Summable.tsum_add` (dot form) and `(tsum_congr …).trans tsum_zero`;
  `Finset.sum_induction f Summable (fun _ _ => Summable.add) summable_zero (fun i _ => …)` proves
  `Summable (∑ i in s, f i)`, then `.congr (fun a => Finset.sum_apply a s f)` for the pointwise form;
  `Finset.sum_congr rfl (fun X _ => by …)` as a REWRITE fails when the proof drives the RHS (RHS is a
  metavar) → prove the per-element eq as a standalone `have hcongr : ∀ X, lhs = rhs` first.
- Axiom recipe: `TaoCollatz/ZZ_ax.lean` importing the module + `#print axioms TaoCollatz.<name>`, `lake
  env lean` it, `rm -f`. `git-safe` at `~/personal/bin/git-safe` (export PATH). Bare `git` is hook-blocked.

## Work report
**6 sorries + 0 orange** (was 6 at lap start, but B1's opaque crux sorry was replaced by rib 1 + the now-
proved rib 2 + assembly — net the same count, but B1's route-decisive uncertainty is RETIRED). B1's only
remaining piece is rib 1 (pure mechanical reindex, all building blocks in hand). C10's entire involvement
in C9 (B2) remains proved + axiom-clean from prior laps. Remaining C9 work after rib 1: three self-contained
analytic/combinatorial leaves → C9 clean → C6.
