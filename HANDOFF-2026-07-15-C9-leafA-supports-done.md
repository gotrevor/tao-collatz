# Handoff: C9 leaf A — all supports proved; NEXT = the assembly itself

**Date**: 2026-07-15. **Branch** `main`, **HEAD `33893db`**. Build 🟢 green (full `lake build`,
3324 jobs). Tree clean, nothing uncommitted.
**Read `DIRECTION.md` first** — incl. the 🪷 operator note (vocabulary rail; **C6 pins owed BEFORE
C9 census hits zero**; no review laps).

## This lap (6 green commits)

- `bafc3fb` **B1 rib 1 proved** → B1 (`perNHarmonic_eq_harmZfine_approx`) fully axiom-clean.
- `0e1486c` **leaf A decomposed**: `pre_pos`/`fnat_odd`/`Nstar_odd`/`perNHarmonic_le` PROVED,
  `Nstar_mem_logWindow` pinned.
- `cdd023c` **`Nstar_mem_logWindow` PROVED** (the (5.18) crux; x₀ = exp 2³⁰; HEARTBEAT 1.6M).
  ⚠ also swept in two operator-authored hunks (DIRECTION.md note, content.tex C9B1/C9B2) — see
  prior handoff; use targeted `git-safe add`, not `-A`.
- `296bfd5` blueprint: **C9A registered** (`\notready`) per vocabulary rail.
- `33893db` **assembly supports proved**: `Nstar_cast` (exact real value of N*),
  `three_pow_log_le_window` (3^k·log x ≤ E'-floor ⇒ uniform 3^k/M ≤ log⁻¹x relative error),
  `tsum_tsum_le_tsum_tsum` (nested-tsum mono, dominating-side summability only).

All new proofs believed axiom-clean `[propext, Classical.choice, Quot.sound]` (spot-checked with
`#print axioms`); judge to verify.

## Census: **5 sorries + 0 orange** (+ C6 un-pinned surface)

`Sec5/Stabilization.lean`: `perNTerm_harmonic_approx` (leaf A assembly — NEXT), `mainZ_bound`,
`Iy_count_ratio`; `Statement.lean:24,31` (frozen headlines, C6).

## NEXT: `perNTerm_harmonic_approx` assembly — worked plan (all ingredients in hand)

Fix x large, y, n ∈ Iy; write L := log x, nrm := (α−1)/2·log y, D := windowMass y (y^α),
k := n−m₀, P := pre ā k, f := fnat k ā, Q := M·2^P, Cε := 2 + 3·(Cw/cD) + 2·Cw/(α−1).
Obtain: Cw (`windowMass_estimate`), cD (`windowMass_ge_clog`), CH (`perNHarmonic_le`),
x₀N (`Nstar_mem_logWindow`).  x₀ := maxes + exp 1024 + exp Cε (need L ≥ Cε).
Witnesses: c := 0.3, C := Cε·CH.

1. **Hoist per-M facts** (∀ M, Eprime →): `2·3^k ≤ M` (from `cn_window_size` (i));
   `(3:ℝ)^k·L ≤ M` (from `three_pow_log_le_window` + Eprime lower bound).  Derive per-(ā,M):
   `2f ≤ Q` and `f·L ≤ Q` (via `fnat_lt_pow_mul`, all cross-multiplied, NO division).
2. **Termwise keys** (A1 := pointmass integrand from `perNTerm_pointmass`; G2 := perNHarmonic
   integrand): in the solvable case rewrite A1 via `logUnifOdd_apply_toReal_of_mem` (window
   nonempty: witness N* itself via `Nstar_mem_logWindow`; value via `Nstar_cast`, `inv_div`,
   `div_div`), then `div_le_div_iff` + nlinarith:
   - UP: `L·nrm·(2^P·M) ≤ (L+Cε)·((Q−f)·D)` — hints: Q·L·(D+Cw−nrm)≥0 [|D−nrm|≤Cw],
     Q·(C1·D−Cw·L)≥0 [Cw·L ≤ C1·D from cD·L ≤ D, C1 := Cw/cD], D·(Q−f·L)≥0, D·(Q−2f)≥0,
     C1·D·(Q−2f)≥0, (C1+C2)·(Q−f)·D≥0 [C2 := 2Cw/(α−1)].
   - DOWN: `(L−Cε)·((Q−f)·D) ≤ L·nrm·(2^P·M)` — hints: (L−Cε)·D·f≥0, (L−Cε)·Q·(nrm+Cw−D)≥0,
     Q·(C2·nrm−Cw·L)≥0 [nrm ≥ (α−1)/2·L], Cε·Q·Cw≥0, (2+3C1)·Q·nrm≥0.
   False-mask branches: both sides collapse via if_neg + simp.
3. **Summation** via `tsum_tsum_le_tsum_tsum` twice (UP: f=A1, g=cU·(3^k·G2), cU := (L+Cε)/(L·nrm);
   DOWN: f=cL·(3^k·G2), g=A1, cL := (L−Cε)/(L·nrm) ≥ 0 by L ≥ Cε).  Summability: per-ā M-sums have
   finite support (Eprime upper bound, mirror `cn_class_summable` range-floor argument); ā-family
   dominated by (if good then (2^P)⁻¹ else 0)·CS, CS := ∑'M [E'] M⁻¹ — `iid_fiber_summable` +
   `iid_geomHalf_apply_of_pos` congr (the `hsummG` pattern at `perNHarmonic_eq_sum_cn`).
   Pull-outs by unconditional `tsum_mul_left` (ℝ).  `perNHarmonic` unfolds definitionally to
   3^k·∑'∑' G2 (`rw [perNHarmonic]`).
4. **Finish**: cU·H − H/nrm = Cε·H/(L·nrm) (field_simp identities), |…| ≤ Cε·H/(L·nrm)
   ≤ Cε·CH·L^{0.7}/(L·nrm) (`perNHarmonic_le`, H ≥ 0 by tsum_nonneg) = C·L^{−0.3}/nrm
   (rpow: 0.7 = −0.3 + 1).  Expect HEARTBEAT bump needed (mirror Nstar_mem_logWindow).

Then: `mainZ_bound` (coarse-scale `cn_bound` mirror — likely short), `Iy_count_ratio` (5.9),
and **C6 pins** (owed before the last C9 leaf closes — order the C6 pinning lap BEFORE finishing
whichever of the three C9 holes is last).

## Rails
- Operator note binds. Never self-`\leanok`; don't edit ratified pins/frozen constants.
- `git-safe` only (bare git hook-blocked); targeted adds.  Axiom recipe: `ZZ_ax.lean` +
  `lake env lean` + `rm`.
- Corpus gotchas this lap: positivity CANNOT prove `y^alpha ≠ 0` (unfolds `alpha`, isDefEq
  timeout) → use `(Real.rpow_pos_of_pos hy0 alpha).ne'`; per-declaration heartbeats are
  CUMULATIVE — big linarith-heavy proofs need `set_option maxHeartbeats` BEFORE the docstring;
  `rw [← tsum_fintype]` gets stuck on PMF coe — use forward `rwa [tsum_fintype] at h` on
  `(pmf).tsum_coe` instead.
