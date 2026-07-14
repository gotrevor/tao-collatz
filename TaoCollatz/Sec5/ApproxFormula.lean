import TaoCollatz.Sec5.FirstPassage
import TaoCollatz.Basic.Valuation

/-!
# §5 approximate first-passage formula (node C8 — Proposition 5.2)

Paper anchors: Tao 2019 §5 pp.22–25, Proposition 5.2 (the approximate formula (5.8)), with the
bookkeeping objects `n₀` (5.1), `m₀` (5.2), `𝒜⁽ⁿ'⁾` (5.11), `I_y` (5.9), `E'` (5.10) and the
`B_{n,y}` equivalence chain.

**This is node C8 — the RISK on the board** (diff 4, 15–30 laps, 75%). It is pinned here (statement
written with `sorry` so it compiles); the proof is owed. Per `blueprint_rules.md`, a pin is a
*claim*, not a fact — the judge ratifies and sets `\leanok`. Nothing here sets `\leanok`.

`C8.\uses{C2, C5, C7}` binds its **proof**. Its **statement** is written over the first-passage
definitions (`passes`, `passTime`, `passLoc`, `logUnifOdd`, `alpha`) and the affine map `Aff`
(1.3) / valuation vector `valVec` (1.8), **all of which already exist**, which is exactly why C8
is pinnable now, before a line of C7 is proved.

## What C8's proof needs from C7 (the deliverable of this pinning objective)

Reading Prop 5.2's proof (pp.22–25) against the blueprint edge `C8.\uses{C7}`: C7 is consumed at
**exactly one place — the (5.16) step**, pinned below as `approx_passtime_window`. That step bounds
`ℙ(T_x(N_y) ∉ I_y)`. The event `T_x(N_y) ∉ I_y` splits as
  `{¬ passes}  ∪  {passes ∧ T_x ∈ [m₀,n₀] but outside the interval I_y}`.
The **first** piece — the escape probability `ℙ(T_x(N_y) = ∞) ≪ x^{-c}` — is precisely
`first_passage_nonescape` (paper (1.19) / (5.5), node C7). The second piece is the integral-test
calculation over the log-uniform window plus (5.12). So **C8 consumes C7 as (1.19) essentially as
the blueprint states it**, entering through the `¬ passes` term of (5.16). The remaining machinery
of Prop 5.2 — (5.12) good-tuple union bound, the `B_{n,y}` equivalence, Lemma 2.1 affine bijection
— does **not** touch C7.
-/

open scoped ENNReal

namespace TaoCollatz

-- `nZero` (5.1) and `mZero` (5.2) live in `Sec5.FirstPassage` (shared with node C7).

/-- Paper (5.11): the good-tuple set `𝒜⁽ⁿ'⁾ ⊂ (ℕ+1)ⁿ'` — tuples `(a₁,…,a_{n'})` with every
`aᵢ ≥ 1` whose every prefix sum stays within `log^{0.6} x` of the mean `2n`:
`|a_{[1,n]} − 2n| < log^{0.6} x` for all `0 ≤ n ≤ n'`.  (`a_{[1,n]} = pre a n`.) -/
def goodTuple (x : ℝ) (n' : ℕ) (a : Fin n' → ℕ) : Prop :=
  (∀ i, 1 ≤ a i) ∧ ∀ n, n ≤ n' → |(pre a n : ℝ) - 2 * n| < Real.log x ^ (0.6 : ℝ)

/-- Lower endpoint of the interval `I_y` (5.9): `log(y/x)/log(4/3) + log^{0.8} x`. -/
noncomputable def IyLo (x y : ℝ) : ℝ :=
  Real.log (y / x) / Real.log (4 / 3) + Real.log x ^ (0.8 : ℝ)

/-- Upper endpoint of the interval `I_y` (5.9): `log(y^α/x)/log(4/3) − log^{0.8} x`. -/
noncomputable def IyHi (x y : ℝ) : ℝ :=
  Real.log (y ^ alpha / x) / Real.log (4 / 3) - Real.log x ^ (0.8 : ℝ)

open Classical in
/-- Paper (5.9): the summation range `I_y` as the natural numbers in `[IyLo, IyHi]`.  Bounded by
`range (n₀+1)` since `I_y ⊂ [m₀, n₀]` (the observation after (5.11)). -/
noncomputable def Iy (x y : ℝ) : Finset ℕ :=
  (Finset.range (nZero x + 1)).filter fun n => IyLo x y ≤ (n : ℝ) ∧ (n : ℝ) ≤ IyHi x y

/-- Paper (5.10): the set `E'` of odd naturals `M` with `T_x(M) = m₀`, `Pass_x(M) ∈ E`, and
`exp(−log^{0.7} x)·(4/3)^{m₀}·x ≤ M ≤ exp(log^{0.7} x)·(4/3)^{m₀}·x`. -/
def Eprime (x : ℝ) (E : Set ℕ) (M : ℕ) : Prop :=
  M % 2 = 1 ∧ passTime ⌊x⌋₊ M = mZero x ∧ passLoc ⌊x⌋₊ M ∈ E ∧
    Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x ≤ (M : ℝ) ∧
    (M : ℝ) ≤ Real.exp (Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x

open Classical in
/-- The right-hand main term of the approximate formula (5.8):
`∑_{n∈I_y} ∑_{ā∈𝒜⁽ⁿ⁻ᵐ⁰⁾} ∑_{M∈E'} ℙ(Aff_ā(N_y) = M)`.  The inner `∑_{ā}∑_{M}` are rendered as
`tsum`s masked by the `goodTuple`/`Eprime` membership predicates (the codebase idiom), and
`ℙ(Aff_ā(N_y) = M)` is the pushforward mass of the fixed affine map `Aff · (n−m₀) ā` at `M`. -/
noncomputable def approxMainTerm (x : ℝ) (E : Set ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Iy x y,
    ∑' (ā : Fin (n - mZero x) → ℕ), ∑' (M : ℕ),
      if goodTuple x (n - mZero x) ā ∧ Eprime x E M then
        (((logUnifOdd y (y ^ alpha)).map (fun N => Aff N (n - mZero x) ā)) M).toReal
      else 0

-- RATIFY-C8: paper Proposition 5.2 / (5.8), §5 pp.22–25.  Rendered against the numbered display;
-- the `O(log^{-c} x)` error is spelled as an explicit `∃ c C x₀` bound (design invariant D3).
/-- **Proposition 5.2** (approximate first-passage formula, paper (5.8)).  For every odd
`E ⊂ [1,x]` and `y ∈ {x^α, x^{α²}}`, the passage-location probability `ℙ(Pass_x(N_y) ∈ E)` agrees
with the affine main term `approxMainTerm` up to `O(log^{-c} x)`:
`ℙ(Pass_x(N_y) ∈ E) = ∑_{n∈I_y} ∑_{ā∈𝒜} ∑_{M∈E'} ℙ(Aff_ā(N_y) = M) + O(log^{-c} x)`.

This is node **C8**.  The proof (owed) runs: (5.12) good-tuple union bound
[`approx_good_tuple_whp`] ⟹ (5.16) passage-time-in-window [`approx_passtime_window`, **which
consumes C7** — see the module docstring] ⟹ the `B_{n,y}` equivalence chain (5.17) ⟹ the Lemma 2.1
affine reindexing (5.18) giving (5.8). -/
theorem first_passage_approx :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
              - approxMainTerm x E y|
            ≤ C * (Real.log x) ^ (-c) := by
  sorry

/-! ## Named decomposition of C8 (route + probe)

Two probabilistic sub-lemmas carry the analytic content of Prop 5.2; the rest of the proof is
pointwise event algebra (the `B_{n,y}` chain and the Lemma 2.1 affine bijection). Pinning these as
named `sorry`s converts the orange C8 seam into visible, attackable holes. -/

/-- **Paper (5.12)** — the good-tuple union bound.  Outside an event of probability `≪ log^{-c} x`
(the paper takes `log^{-10} x`), the full length-`n₀` valuation vector of `N_y` lies in the
good-tuple set `𝒜⁽ⁿ⁰⁾`.  Proof (owed): from (5.4) [C5 / Prop 1.9, axiom-clean] and Lemma 2.2
[S3, two-sided, axiom-clean] each prefix deviates by `≥ log^{0.6} x` with probability
`≪ exp(−c log^{0.2} x)`; union over the `n₀ + 1` prefixes. **Does not use C7.** -/
theorem approx_good_tuple_whp :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
          ≤ C * (Real.log x) ^ (-c) := by
  sorry

/-- **Paper (5.16)** — the passage time lands in the window `I_y` with probability `1 − O(log^{-c} x)`.
Equivalently the complement `{N : ¬(passes ∧ T_x ∈ I_y)}` has probability `≪ log^{-c} x`.

⚠️ **THIS is the C7 consumer.**  The complement event splits as `{¬ passes} ∪ {passes ∧ T_x ∉ I_y}`.
The first term `ℙ(T_x(N_y) = ∞) = ℙ(¬ passes)` is bounded `≪ x^{-c} ≪ log^{-c} x` by
`first_passage_nonescape` (C7, paper (1.19)/(5.5)).  The second term is the integral-test
calculation over the log-uniform window using (5.14)/(5.15) and (5.12).  This is the whole of C8's
dependence on C7. -/
theorem approx_passtime_window :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1)
          ≤ C * (Real.log x) ^ (-c) := by
  sorry

end TaoCollatz
