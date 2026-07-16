## Judge pass (2026-07-09 evening, Ren/Fable + PDF) — RATIFY queue verdicts ⚖️

Independent statement ratification against the paper (pp. 8–14, 33–37, 42–46 read this
pass). One statement bug found and fixed; every queue item now ratified, fixed, or spec'd.

1. **RATIFY-2 (`valVec_unique`, Lemma 2.1 p.14) — RATIFIED.** The divisibility-guarded iff
   is exactly "unique tuple in `(ℕ+1)ⁿ` making `Aff_a(N)` an odd natural": the paper's
   `Aff_a(N) ∈ 2ℕ+1` (a `ℤ[1/2]` membership) is precisely
   `2^{a[1,n]} ∣ 3ⁿN + Fnat ∧ quotient odd`. `n = 0` edge agrees (both sides trivially true).
2. **RATIFY-3 (`stabilization`, Prop 1.11 pp.8–9) — RATIFIED.** Windows `[x^α, x^{α²}]` /
   `[x^{α²}, x^{α³}]` are the paper's `[y, y^α]` at `y = x^α, x^{α²}` verbatim; the `⌊x⌋₊`
   threshold is equivalent to the paper's real-`x` threshold (orbit values are naturals);
   (1.19)/(1.20) shapes and the single shared constant `c` match.
3. **RATIFY-4 (`θq`) — RATIFIED**, one doc fix: mathlib `round` puts `sfrac` in
   `[-1/2, 1/2)`, not the paper's `(-1/2, 1/2]`; they differ only at half-integers, which
   phases with odd denominator `3ⁿ` never attain. Docstring corrected, no statement change.
4. **Prop 7.3 count (`renewal_white_encounters`) — RATIFIED independently** (agrees with
   harness check 7): `(j : Fin (n/2), pre b (j+1))` = paper `(j, b_{[1,j]})`; the `b j = 3`
   conjunct per p.35; `pascal` (p.34), `pascalNe3` (7.29), `geomQuarter` (7.30 coefficient
   `(1/4)(3/4)^{j-1}`), and `hold` (p.42 description) all match the paper exactly.
5. **RATIFY-5 (`black_structure` set-separation fix) — CONFIRMED** vs Lemma 7.4 p.36: the
   paper separates triangle POINT SETS in the Euclidean metric; disjointness follows from
   positive separation; `triangle` = (7.11) verbatim; strip (`⌊n/2⌋`) and confinement
   (real `n/2`) conjuncts both as in the paper.
6. **RATIFY-6/7 (Q cluster) — STATEMENT BUG FOUND & FIXED (off-by-one).**
   `Q`/`Qm`/`prop_7_8`/`Q_polynomial_decay` are paper-1-based (boundary `⌊n/2⌋ < j`, weight
   `⌊n/2⌋ − j` — correct vs (7.34)/(7.38)/(7.40)/(7.37)), but `whiteSet` fed the 0-based
   `white` (RATIFY-4) unshifted, so `Q`'s indicator read the phase one column RIGHT of
   (7.34). Fixes (commit this pass): `whiteSet := {p | 1 ≤ p.1 ∧ white n ξ (p.1-1) p.2}`
   (the coordinate adapter); `Q_white_contract` hypothesis is now `whiteSet` membership;
   `Qm`'s sup restricted to `1 ≤ j` (paper `(ℕ+1)×ℤ` — the old sup admitted the
   nonexistent column 0, which could break `prop_7_8` at `m = ⌊n/2⌋`); `Q_polynomial_decay`
   takes `1 ≤ j` ((7.37) is only asserted on `(ℕ+1)×ℤ`). `Q_rec`/`Q_boundary`/`Q_nonneg`/
   `Q_le_one`/`Qm_le_rpow` are generic in `W` — untouched, still proved.
7. **Queue 2 (`unifOddMod` n'=0) — DECIDED: junk-guard.** The def carried a FALSE `sorry`
   (normalization over an empty odd-residue set at `n' = 0`) — a latent campaign-killer.
   Now `PMF.pure 0` at `n' = 0`; the `n' ≥ 1` normalization `sorry` is TRUE and grindable
   (witness `(1 : ZMod (2^n')).val = 1` odd; sum = `card • card⁻¹`). Statements unchanged.
8. **Queue 5 (Case 1 proper) — SPEC for the box.** (7.43), at `j = ⌊n/2⌋ − m` (paper
   coords, p.45 (7.41)):
   `∀ A > 0, ∃ Cthr, ∀ n ξ, ¬3∣ξ → ∀ m, Cthr ≤ m → m ≤ n/2 → ∀ l, ((n/2 - m : ℕ), l) ∈ whiteSet n ξ →`
   `  Q (n/2) (whiteSet n ξ) epsBW (n/2 - m) l ≤ Real.exp (-(epsBW:ℝ)^3/2) * (m:ℝ)^(-A) * Qm (n/2) n ξ epsBW A (m-1)`
   (`Q_white_contract` stays as the warm-up lemma).
9. **Directive to next lap**: extend the harness with a (7.36)-bridge check against the
   FIXED `whiteSet` — small-`n` comparison of `E Q(Hold)` vs
   `E exp(-ε³ #{j : b_j = 3, (j, b_{[1,j]}) ∈ W})` (paper p.44 derivation; exact via
   truncation + tail bound, or high-precision Monte Carlo). This pins the Q ↔ count seam
   end-to-end and would have caught the off-by-one mechanically.

**Series α is judge-cleared.** Preconditions §3 remaining: audit-machinery transplant + CI
gate (item 2) and the PMF lemma bank ordering (item 4).

