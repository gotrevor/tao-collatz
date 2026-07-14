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

/-! ## Lemma 2.1 kernels for the (5.18) affine reindexing (the route-decisive assembly step)

The proof of (5.8) reindexes `ℙ((Syr^{n-m₀}N_y ∈ E') ∧ good)` into `∑_ā ∑_M ℙ(Aff_ā(N_y)=M)` via
Tao's Lemma 2.1 (`valVec_unique`, `Basic/Valuation.lean`).  Two facts drive the **main** (exact)
contribution `ā = valVec N k`; both are proved axiom-clean below.

⚠️ **The reindex is APPROXIMATE, not exact.**  Our `Aff` uses truncating ℕ-division while Tao's
`Aff_ā` (1.3) uses exact division.  The count `#{ā good : Aff N k ā ∈ E'}` can exceed 1 on the
truncation set (`2^{pre ā k} ∤ 3^k N + fnat k ā`, where `valVec_unique`'s guard fails).  Tao absorbs
this in the `O(log^{-c} x)` / `O(3^{n-m₀})` errors of (5.18)–(5.19); it is consistent with the
`≤ C·(log x)^{-c}` error of `first_passage_approx`.  **Do not attempt an exact `=` reindex.** -/

/-- **Lemma 2.1, generating direction.**  For odd `N`, the affine map at the true valuation vector
recovers the Syracuse iterate: `Aff N k (valVec N k) = syr^[k] N`.  (The guarded ℕ-division is exact
here: `2^{|valVec N k|}·syr^[k] N = 3^k N + fnat k (valVec N k)` — paper (1.7), `syr_iterate_key`.)
This is the exact/main contribution of the (5.18) reindexing; the truncation `ā ≠ valVec N k` terms
are the error absorbed in `O(log^{-c} x)`. -/
theorem aff_valVec_eq_syr (N k : ℕ) (hN : N % 2 = 1) :
    Aff N k (valVec N k) = syr^[k] N := by
  unfold Aff
  rw [← syr_iterate_key N k hN, Nat.mul_comm, Nat.mul_div_left _ (by positivity)]

-- The positivity hypothesis `valVec_unique` / Lemma 2.1 and the good-tuple set `𝒜⁽ⁿ'⁾` (5.11)
-- require on the reindexing vectors is already proved: `valVec_pos` (`Syracuse/ValuationDist.lean`)
-- gives `1 ≤ valVec N k i` for odd `N` (since `3·(odd)+1` is even).

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

/-! ### Glue for the (5.16) split -/

/-- Expectation of an event indicator dominated pointwise by a sum of two indicators is at most the
sum of their expectations (a union/subadditivity bound for `PMF.expect`). -/
theorem expect_le_add_of_indicator_le {α : Type*} (p : PMF α) (U S T : Set α)
    (h : ∀ a, Set.indicator U (1 : α → ℝ) a ≤ Set.indicator S 1 a + Set.indicator T 1 a) :
    p.expect (Set.indicator U 1) ≤
      p.expect (Set.indicator S 1) + p.expect (Set.indicator T 1) := by
  classical
  have hsumP : Summable fun a => (p a).toReal := ENNReal.summable_toReal p.tsum_coe_ne_top
  have ind01 : ∀ (V : Set α) a,
      (0 : ℝ) ≤ Set.indicator V (1 : α → ℝ) a ∧ Set.indicator V (1 : α → ℝ) a ≤ 1 := by
    intro V a
    refine ⟨Set.indicator_nonneg (fun _ _ => zero_le_one) a, ?_⟩
    rw [Set.indicator_apply]; split <;> simp
  have hsum : ∀ (V : Set α), Summable fun a => (p a).toReal * Set.indicator V (1 : α → ℝ) a := by
    intro V
    exact Summable.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (ind01 V a).1)
      (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (ind01 V a).2) hsumP
  show (∑' a, (p a).toReal * Set.indicator U 1 a) ≤
      (∑' a, (p a).toReal * Set.indicator S 1 a) + (∑' a, (p a).toReal * Set.indicator T 1 a)
  rw [← (hsum S).tsum_add (hsum T)]
  refine (hsum U).tsum_le_tsum (fun a => ?_) ((hsum S).add (hsum T))
  calc (p a).toReal * Set.indicator U 1 a
      ≤ (p a).toReal * (Set.indicator S 1 a + Set.indicator T 1 a) :=
        mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg
    _ = (p a).toReal * Set.indicator S 1 a + (p a).toReal * Set.indicator T 1 a := by ring

/-- For `x ≥ e` and `c > 0`, `x^{-c} ≤ (log x)^{-c}` (since `1 ≤ log x ≤ x`).  This is what lets the
escape term's `x^{-c}` bound (`first_passage_nonescape`) fold into the `(log x)^{-c}` target. -/
theorem escape_to_log {x c : ℝ} (hx : Real.exp 1 ≤ x) (hc : 0 < c) :
    x ^ (-c) ≤ (Real.log x) ^ (-c) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le one_pos hlog1
  have hle : Real.log x ≤ x := le_trans (Real.log_le_sub_one_of_pos hxpos) (by linarith)
  rw [Real.rpow_neg hxpos.le, Real.rpow_neg hlogpos.le, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogpos c)
    (Real.rpow_le_rpow hlogpos.le hle hc.le)

/-- **Paper (5.16), window term** (owed — the integral-test piece).  On the event that `N_y` *does*
pass, the passage time nonetheless lands outside `I_y` only with probability `≪ log^{-c} x`.
Proof (owed): this is the integral test that `N_y` is not within `2 log^{0.8} x` of a window edge
`[y + 2log^{0.8}x, y^α − 2log^{0.8}x]` (via (5.14)/(5.15)), plus the good-tuple event (5.12); reuse
C7's `classMass`/`windowMass`/`intTest_*` machinery in `Sec5.FirstPassage`.  **Does not use C7's
escape bound** — that is the *other* term of (5.16), discharged in `approx_passtime_window`. -/
theorem passtime_window_inner :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} 1)
          ≤ C * (Real.log x) ^ (-c) := by
  sorry

/-- **Paper (5.16)** — the passage time lands in the window `I_y` with probability `1 − O(log^{-c} x)`.
Equivalently the complement `{N : ¬(passes ∧ T_x ∈ I_y)}` has probability `≪ log^{-c} x`.

⚠️ **THIS is the C7 consumer.**  The complement event splits as the disjoint union
`{¬ passes} ∪ {passes ∧ T_x ∉ I_y}`.  The first term `ℙ(T_x(N_y) = ∞) = ℙ(¬ passes) ≪ x^{-c}` is
`first_passage_nonescape` (C7, paper (1.19)/(5.5), **proved axiom-clean**), folded into `log^{-c} x`
via `escape_to_log`.  The second term is `passtime_window_inner` (the integral-test window piece).
This lemma **wires C7 into C8** — the whole of C8's dependence on C7 — leaving only the window
integral test open. -/
theorem approx_passtime_window :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1)
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨c₁, C₁, x₁, hc₁, hC₁, hesc⟩ := first_passage_nonescape
  obtain ⟨c₂, C₂, x₂, hc₂, hC₂, hwin⟩ := passtime_window_inner
  refine ⟨min c₁ c₂, C₁ + C₂, max (max x₁ x₂) (Real.exp 1), lt_min hc₁ hc₂, by positivity,
    fun x hx y hy => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hpw : ∀ N, Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} (1 : ℕ → ℝ) N ≤
      Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1 N +
      Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} 1 N := by
    intro N
    have h1 : (0 : ℝ) ≤ Set.indicator {N | ¬ passes ⌊x⌋₊ N} (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    have h2 : (0 : ℝ) ≤ Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    by_cases hN : N ∈ {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)}
    · rw [Set.indicator_of_mem hN, Pi.one_apply]
      rcases Classical.em (passes ⌊x⌋₊ N) with hp | hp
      · have hq : passTime ⌊x⌋₊ N ∉ Iy x y := fun hq => hN ⟨hp, hq⟩
        have hmemT : N ∈ {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} := ⟨hp, hq⟩
        rw [Set.indicator_of_mem hmemT, Pi.one_apply]; linarith
      · have hmemS : N ∈ {N | ¬ passes ⌊x⌋₊ N} := hp
        rw [Set.indicator_of_mem hmemS, Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hN]; linarith
  have hA : x ^ (-c₁) ≤ (Real.log x) ^ (-(min c₁ c₂)) :=
    le_trans (escape_to_log hxe hc₁)
      (Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_left c₁ c₂)))
  have hB : (Real.log x) ^ (-c₂) ≤ (Real.log x) ^ (-(min c₁ c₂)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_right c₁ c₂))
  calc (logUnifOdd y (y ^ alpha)).expect
          (Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1)
      ≤ (logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1)
          + (logUnifOdd y (y ^ alpha)).expect
              (Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} 1) :=
        expect_le_add_of_indicator_le _ _ _ _ hpw
    _ ≤ C₁ * x ^ (-c₁) + C₂ * (Real.log x) ^ (-c₂) :=
        add_le_add (hesc x hx1 y hy) (hwin x hx2 y hy)
    _ ≤ C₁ * (Real.log x) ^ (-(min c₁ c₂)) + C₂ * (Real.log x) ^ (-(min c₁ c₂)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hC₁.le) (mul_le_mul_of_nonneg_left hB hC₂.le)
    _ = (C₁ + C₂) * (Real.log x) ^ (-(min c₁ c₂)) := by ring

end TaoCollatz
