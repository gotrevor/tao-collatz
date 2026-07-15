# Handoff: C9 `perNTerm_eval` DECOMPOSED + PROVED — C10 seam isolated to one hole

**Date**: 2026-07-15. **Branch** `main`, **HEAD `eeb96c6`**. Build 🟢 green (full `lake build`, 3324
jobs). Tree clean, nothing uncommitted.
**Read `DIRECTION.md` first** — CURRENT DIRECTIVE (JUDGE PASS 30 + review refresh) outranks this doc.
Campaign order: C10 ✅ → C8 ✅ → C7 ✅ → **C9 (this session's focus)** → C6 → headline.

## What this session did — drove the C9 crux leaf `perNTerm_eval` (the sole C10 consumer)

Coming in, C9 rested on 3 leaves (`perNTerm_eval`, `Iy_count_ratio`, `mainZ_bound`). `perNTerm_eval`
is the route-decisive one (consumes Lemma 5.3 + `fine_scale_mixing`, C10). Six green commits, all the
new bricks axiom-clean `[propext, Classical.choice, Quot.sound]`:

1. `3247d22` — **`perNTerm_pointmass`** + `tsum_ite_affine_of_sol`/`_of_nosol`. The affine map
   `N ↦ 3^{n−m₀}N + fnat` is injective, so each inner mass `ℙ(Aff_ā(N_y)=M)` collapses to the SINGLE
   point mass `logUnifOdd y (y^α) N*`, `N* = (M·2^{pre ā}−fnat)/3^{n−m₀}`, nonzero exactly under Tao's
   (5.18) guard `3^{n−m₀} ∣ (M·2^{pre ā}−fnat) ∧ fnat ≤ M·2^{pre ā}`. Discharges the (5.19) affine reindex.
2. `84bd4c1` — **`logUnifOdd_apply_toReal`** (+ `_of_mem`). Evaluates the point mass:
   `(logUnifOdd lo hi N).toReal = if N∈window then (N)⁻¹/windowMass lo hi else 0`.
3. `bba4955` — **`windowMass_estimate`** (in `FirstPassage.lean`). The (5.19) denominator:
   `|windowMass y (y^α) − (α−1)/2·log y| ≤ 3`. Reused `intTest_D_lower`'s odd-AP setup +
   `harmonic_ap_integral_bound` (step 2) + `log_le_sub_one_of_pos` endpoints.
4. `0cd5318` — **`fnat_lt_pow_mul`** (`fnat k a < 3^k·2^{pre a k}`) + helper `pre_mono` (in
   `ApproxFormula.lean`). Numerator bound for the (5.19) `(N*)⁻¹` relative error. Also **mapped the
   (5.20) fine_scale_mixing seam** in PENDING_WORK (see below).
5. `eeb96c6` — **`perNTerm_eval` DECOMPOSED + PROVED.** Defined `perNHarmonic x E n` (the window-free
   harmonic content, (5.20) LHS) and split `perNTerm_eval` into two named sub-sorries, proving it from them.

## State: 6 sorries + 0 orange nodes  (`#print axioms perNTerm_eval` = trust base + sorryAx via A,B only)

- `Statement.lean:24,31` — the two headline stubs (Thm 1.3 / Thm 3.1), frozen; discharge when C6 lands.
- **`Sec5/Stabilization.lean` — the C9 holes** (perNTerm_eval is now PROVED; 4 sorries remain):
  - **`harmonic_to_Z` (:348)** — (5.20). `|perNHarmonic x E n − mainZ x E| ≤ C·log^{-c}`. **THE SOLE C10
    CONSUMER — hardest-first, attack this next.** All of C10's involvement in C9 is now in this one hole.
  - **`perNTerm_harmonic_approx` (:334)** — (5.19). `|perNTerm − perNHarmonic/norm| ≤ C·log^{-c}/norm`,
    `norm=(α−1)/2·log y`. Pure (5.19) analytic layer — **does NOT consume C10**. Bricks 1–4 above are its
    ingredients (pointmass + apply_toReal + windowMass_estimate + N*∈window + fnat_lt_pow_mul).
  - **`Iy_count_ratio` (:416)** — (5.9). Self-contained lattice count. Cheapest leaf.
  - **`mainZ_bound` (:305)** — `|mainZ x E| ≤ C`. Small.

C9 spine fully wired: `stabilization ← approxMainTerm_window_stable ← approxMainTerm_to_Z ←
{perNTerm_eval ✅(from A,B), Iy_count_ratio, mainZ_bound}`; and `perNTerm_eval ← {A, B}`.

## Next steps — hardest-first = `harmonic_to_Z` (the C10 seam)

The interface is now precisely mapped (see PENDING_WORK top, "SEAM UNDERSTOOD"):
- `geomHalf a = 2^{-a}` (a≥1) ⟹ `(iid geomHalf k)` mass of ā = `2^{-pre ā k}` = EXACTLY the perNHarmonic
  weight. And `syracZ k = (iid geomHalf k).map (a ↦ fnat k a·2^{-pre a k} mod 3^k)` (`syracZ_eq_rev_fnat`).
- The solvability congruence `3^{n−m₀} ∣ M·2^{pre ā}−fnat` ⟺ `M ≡ fnat·2^{-pre ā} mod 3^{n−m₀}` = the
  syracZ summand value. So `∑_ā[good,congr] 2^{-pre ā} = syracZ(n−m₀)(M mod 3^{n−m₀})` up to the good-tuple
  whp error (reuse `approx_good_tuple_whp`, already proved).
- `mainZ` uses `syracZ(mZero x)` mod 3^{m₀}. Bridge: `syracZ_map_cast` projects, and **`fine_scale_mixing`'s
  `osc` bounds** `3^{n−m₀}·syracZ(n−m₀)(r) ≈ 3^{m₀}·syracZ(m₀)(r mod 3^{m₀})` (Lemma 5.3 `c_n≪1`). C10 enters here.
- ⚠ First sub-step: rewrite perNHarmonic's ā-tsum as `syracZ(n−m₀)` mass — a real reindex of the good-tuple
  restriction against `syracZ_eq_rev_fnat`. Then the osc/projection bridge. Decompose into named sub-sorries.

Then `perNTerm_harmonic_approx` (A — the N*∈window membership via `syr_iterate_good_bracket` is the main
owed piece; the mass algebra is bricks 1–4), then `Iy_count_ratio`, then `mainZ_bound`.

## 🚩 JUDGE-FLAGS (open, carried from prior sessions — grind laps flag & continue)
1. **Ratify `first_passage_approx` (C8) as PROVEN + flip proof `\leanok`** — blueprint_audit MISSED FLIP.
2. **Confirm the `stabilization` RELOCATION** to `Sec5/Stabilization.lean` (byte-identical statement).
3. **New internal decompositions BELOW the ratified `stabilization` pin** (allowed): `perNHarmonic`,
   `perNTerm_harmonic_approx`, `harmonic_to_Z`, `perNTerm_pointmass`, `logUnifOdd_apply_toReal`,
   `windowMass_estimate`, `fnat_lt_pow_mul`, `pre_mono`. Not blueprint nodes; no numeric trap owed.
   Worth a judge cross-read of `harmonic_to_Z`/`perNTerm_harmonic_approx`/`perNHarmonic` vs pp.25–27.

## Rails / notes
- **Do NOT edit ratified pins** (C7/C8/C10 statements, `stabilization`, the two headlines). Constants
  FROZEN: `epsBW=1/10^1000`, `caConst=30`, `alpha=1.001`.
- Axiom recipe: write `TaoCollatz/ZZ_ax.lean` importing the module + `#print axioms <name>`,
  `lake env lean` it, then `rm -f` (don't leave it — breaks the build tree).
- **mathlib name gotchas this session** (corpus-worthy): `div_le_div_iff` is unknown — use
  `div_le_div_of_nonneg_right (hab) (hc.le)` (`a≤b → 0≤c → a/c ≤ b/c`) or the `₀`-suffixed
  `div_le_iff₀`/`le_div_iff₀`; `div_add_div_same` unknown (use `← add_div`); `Nat.mul_lt_mul_right` is
  now an Iff (`.mpr`); `Nat.mul_le_mul_left` arg-form changed (use `Nat.mul_le_mul (le_refl _) h`);
  `Finset.range_subset.mpr` mis-resolves under `sum_le_sum_of_subset_of_nonneg` — prove the ⊆ by hand;
  `ENNReal.zero_toReal` unknown (use `simp`); `Nat.geomSum_eq (by norm_num : 2≤3) k` gives `(3^k−1)/2`.
- **Work report: 6 sorries + 0 orange.** C9's route-decisive leaf `perNTerm_eval` PROVED from a
  faithful decomposition; C10's entire C9 involvement isolated to `harmonic_to_Z`. Next = that seam,
  then A, then the 2 cheap leaves → C9 axiom-clean → C6 (§3 reduction) → headline.
