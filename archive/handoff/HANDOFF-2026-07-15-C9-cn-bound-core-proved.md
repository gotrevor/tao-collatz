# Handoff: C9 `harmonic_to_Z` (C10 seam) DECOMPOSED; crude `cn_bound` integral-test core PROVED

**Date**: 2026-07-15. **Branch** `main`, **HEAD `f0322cf`**. Build 🟢 green (full `lake build`, 3324
jobs). Tree clean, nothing uncommitted.
**Read `DIRECTION.md` first** — its CURRENT DIRECTIVE (review-lap refresh `5514f13`, THIS lap) outranks
this doc. Objective = close C9's `harmonic_to_Z` (the C10 seam); campaign order
`C10 ✅ → C8 ✅ → C7 ✅ → C9 (live) → C6 → headline`.

## This was a REVIEW lap that turned into substantial C10-seam progress (7 green commits)

Coming in: C8 CLOSED (confirmed axiom-clean this lap), C9's `perNTerm_eval` proved from 2 sub-sorries.
The review found DIRECTION/STATUS stale (C8-worded) and retargeted them to **C9 `harmonic_to_Z`** (Tao
(5.20), the sole remaining C10 consumer in C9), then drove that seam:

1. `97d590c` — **`harmonic_to_Z` DECOMPOSED + PROVED** from two named sub-sorries via a new intermediate
   `harmZfine` (the fine-scale `syracZ(n−m₀)` harmonic content): **B1** `perNHarmonic_eq_harmZfine_approx`
   (geomHalf→syracZ reindex; no C10) + **B2** `harmZfine_to_mainZ` (the `fine_scale_mixing` scale bridge;
   THE C10 seam). Clean triangle assembly.
2. `9997c1e` — **`two_mZero_le_of_mem_Iy` PROVED** (`ApproxFormula.lean`, axiom-clean): `n∈Iy ⟹ 2·m₀ ≤ n`,
   so `m₀ ≤ n−m₀` and `fine_scale_mixing` applies at `(n:=n−m₀, m:=m₀)` for every `n∈Iy` — no degenerate
   low-scale sub-case. Settles B2's applicability.
3. `c6d4627` — **Source read Tao pp.25–27 (PDF)**, CORRECTING the B2 route (the earlier "M-equidistribution"
   worry was a misread). Tao routes B2 through a clean **L¹×L∞ Hölder** bound `(sup c_n)·osc`, nothing more.
   Pinned `c_n` (5.23) + `cn_bound` — the shared self-contained prerequisite of BOTH B1 and B2.
4. `0a8af14` — **Strategic fork RESOLVED**: `cn_bound` restated from Tao's hard Lemma 5.3 (`c_n≪1`, needs
   the `c_{n,a}` split) to the CRUDE `c_n ≤ C·log^{0.7}x` — provable by ONE integral test and SUFFICIENT
   downstream (B1 pairs with `approx_good_tuple_whp`'s `log^{−1}` decay; B2 with `fine_scale_mixing`'s
   `osc ≤ C·m₀^{−A}` for adjustable `A>0.7`).
5. `6803ef8` — **`harmonic_class_window_bound` PROVED** (integral-test core): for modulus `q≥1`, window
   `[lo,hi]`, `∑'_{M∈[lo,hi], M≡X mod q} 1/M ≤ q⁻¹·log((hi+q)/lo) + 1/lo`. tsum→Finset→AP→
   `harmonic_ap_integral_bound`.
6. `f0322cf` — **`class_window_ap_form` PROVED** (the residue-class→AP reindex, general-`q` analog of
   `classMass_ap_form`, axiom-clean). Closes the last hole under `harmonic_class_window_bound`.

## State: 8 sorries + 0 orange  (all in `Sec5/Stabilization.lean` + 2 headlines)

C9 spine (all in `Sec5/Stabilization.lean`), route-decisive first:
- **`cn_bound` (:~469)** — crude `c_n ≤ C·log^{0.7}x`. **The full integral-test core is now PROVED**
  (`harmonic_class_window_bound` + `class_window_ap_form`, both axiom-clean). **Only the
  window-arithmetic reduction remains** — see Next steps. This is the shared prerequisite of B1+B2.
- **`harmZfine_to_mainZ` (B2, :~505)** — THE C10 SEAM. osc-Hölder: `|harmZfine − mainZ| ≤ (sup c_n)·osc
  m₀ (n−m₀) ≤ cn_bound × fine_scale_mixing`. Applicability proved (`two_mZero_le_of_mem_Iy`). Route
  faithful (verified vs PDF). Needs: the osc-identity `harmZfine−mainZ = ∑_X g(X)·c_n(X)` (`g = syracZ(n−m₀)
  − fiber_avg`, via `syracZ_map_cast`), the Hölder step, then `fine_scale_mixing`.
- **`perNHarmonic_eq_harmZfine_approx` (B1, :~449)** — geomHalf→syracZ reindex; no C10. `𝔼[1_{¬good}·c_n]
  ≤ (sup c_n)·ℙ(¬good)` via `cn_bound` + `approx_good_tuple_whp`. Needs the `perNHarmonic = 𝔼[1_good·c_n]`
  + `harmZfine = 𝔼[c_n(Syrac)]` rewrites (Tonelli + `syracZ_eq_rev_fnat`).
- **`Iy_count_ratio` (:~568)** — (5.9) lattice count. Self-contained. Cheapest.
- **`mainZ_bound` (:~302)** — `|mainZ| ≤ C`. Small.
- `Statement.lean:22,28` — the two headline stubs, frozen; discharge when C6 lands.

`harmonic_to_Z` PROVED from B1+B2; `perNTerm_eval` PROVED from `perNTerm_harmonic_approx`+`harmonic_to_Z`.

## Next steps — hardest-first, finish `cn_bound` FIRST (unblocks B1+B2)

1. **`cn_bound` window-arithmetic reduction** (the last piece; core is proved). In `Stabilization.lean`:
   - Unfold `cn = 3^{n−m₀}·∑'_M [Eprime ∧ M≡X mod 3^{n−m₀}] 1/M`.
   - **Bound Eprime-sum ≤ window-sum**: `Eprime x E M → (M₀ ≤ (M:ℝ) ≤ M₁)` where `M₀ =
     exp(−log^{0.7}x)(4/3)^{m₀}x`, `M₁ = exp(+log^{0.7}x)(4/3)^{m₀}x` (the (5.10) window). Termwise
     `if Eprime∧res then 1/M else 0 ≤ if window∧res then 1/M else 0` (both nonneg, Eprime⟹window),
     `tsum_le_tsum` (both finitely supported).
   - **Apply `harmonic_class_window_bound`** with `lo=M₀, hi=M₁, q=3^{n−m₀}, X`. Discharge `hwide`
     (`M₀ + 3^{n−m₀} + 1 ≤ M₁`): `M₁ − M₀ = M₀(exp(2log^{0.7}x)−1) ≫ 3^{n−m₀}` — use `3^{n−m₀} ≤ 3^{nZero} ≤
     x^{0.16}` and `M₀ ≥ x^{0.99}` (needs `nZero`/`mZero` unfolds like `two_mZero_le_of_mem_Iy` did).
   - **Multiply by `3^{n−m₀}`**: `cn ≤ log((M₁+q)/M₀) + 3^{n−m₀}/M₀` (since `3^{n−m₀}·q⁻¹ = 1`).
   - **Bound**: `log((M₁+q)/M₀) ≤ log(2M₁/M₀) = log2 + 2log^{0.7}x` (`q ≤ M₁`), `3^{n−m₀}/M₀ ≤ 1`
     ⟹ `cn ≤ 2log^{0.7}x + log2 + 1 ≤ 3·log^{0.7}x` for large x (`C=3`).
   - The `M₀ ≥ x^{0.99}` / `3^{n−m₀} ≤ x^{0.16}` size lemmas may be worth banking as helpers (reusable in
     B1/B2). Reuse `two_mZero_le_of_mem_Iy`'s idiom (frozen-α rationals, `log(4/3)∈(0,1/3]`).
2. **B2** (`harmZfine_to_mainZ`) — the C10 seam. Pin the osc-identity + Hölder as sub-sorries (see B2
   docstring + PENDING top for the exact `∑_X g(X)c_n(X)` structure). Consumes `cn_bound`,
   `fine_scale_mixing`, `syracZ_map_cast`, `two_mZero_le_of_mem_Iy`.
3. **B1** (`perNHarmonic_eq_harmZfine_approx`) — reindex + good-restriction. Consumes `cn_bound`,
   `approx_good_tuple_whp`, `syracZ_eq_rev_fnat`.
4. Then `Iy_count_ratio`, `mainZ_bound` → C9 axiom-clean → C6 → headline.

## Rails / notes
- **Do NOT edit ratified pins** (C7/C8/C10 statements, `stabilization`, the two headlines) or frozen
  constants (`epsBW=1/10^1000`, `caConst=30`, `alpha=1.001`). B1/B2/`cn`/`cn_bound`/`harmZfine`/
  `class_window_ap_form`/`harmonic_class_window_bound` are internal decompositions below the
  `stabilization` pin (not blueprint nodes, no numeric trap owed) — editing THEM is fine.
- **mathlib gotchas this lap** (corpus-worthy): `div_le_div_iff` unknown → **`div_le_div_iff₀ hb hd`**
  (two-sided, `a/b≤c/d ↔ a*d≤c*b`); `Nat.mul_le_mul_left` arg-form changed → `Nat.mul_le_mul (le_refl _)
  h`; `set ylo := ⌈lo⌉₊` auto-folds the goal's `⌈lo⌉₊` so a later `rw [← hylodef]` fails ("pattern not
  found") — just use the folded name; `Nat.le_floor_iff (h:0≤r)`, `Nat.ceil_le`, `Nat.add_mul_mod_self_left`,
  `Nat.div_mul_le_self`, `Nat.find_min'`/`Nat.find_min`/`Nat.find_spec`, `tsum_eq_sum`, `Finset.sum_image`.
- Axiom recipe: write `TaoCollatz/ZZ_ax.lean` importing the module + `#print axioms <name>`, `lake env lean`
  it, `rm -f` (don't leave it — breaks the build tree). `git-safe` lives at `~/personal/bin/git-safe`
  (export PATH). Bare `git` is hook-blocked.

## Work report
**8 sorries + 0 orange.** C10's entire C9-involvement isolated to B2 (`harmZfine_to_mainZ`); its route is
verified-faithful vs Tao pp.25–27 and de-risked (applicability + core both proved). `cn_bound`'s
integral-test core PROVED; only its window-arithmetic reduction remains. Next = finish `cn_bound`, then
B2 (C10 seam), then B1, then the 2 cheap leaves → C9 axiom-clean → C6 → headline.
