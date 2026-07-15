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

/-! ## Shared `PMF.expect` / event glue for the C8 sub-lemmas -/

/-- Expectation of an event indicator dominated pointwise by a sum of two indicators is at most the
sum of their expectations (a binary union/subadditivity bound for `PMF.expect`). -/
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

/-- Finset version of the union bound: an indicator dominated pointwise by a finite sum of
indicators has expectation at most the sum of the term expectations. -/
theorem expect_le_sum_of_indicator_le {α ι : Type*} (p : PMF α) (U : Set α)
    (s : Finset ι) (T : ι → Set α)
    (h : ∀ a, Set.indicator U (1 : α → ℝ) a ≤ ∑ i ∈ s, Set.indicator (T i) 1 a) :
    p.expect (Set.indicator U 1) ≤ ∑ i ∈ s, p.expect (Set.indicator (T i) 1) := by
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
  have hsumRHS : Summable fun a => (p a).toReal * ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a := by
    refine Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun i _ => (ind01 (T i) a).1))
      (fun a => ?_) (hsumP.mul_right (s.card : ℝ))
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    calc ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a ≤ ∑ _i ∈ s, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (ind01 (T i) a).2
      _ = (s.card : ℝ) := by simp
  have hswap : (∑ i ∈ s, p.expect (Set.indicator (T i) 1))
      = ∑' a, (p a).toReal * ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a := by
    unfold PMF.expect
    rw [← Summable.tsum_finsetSum (fun i _ => hsum (T i))]
    exact tsum_congr fun a => by rw [Finset.mul_sum]
  rw [hswap]
  show (∑' a, (p a).toReal * Set.indicator U 1 a) ≤ _
  refine (hsum U).tsum_le_tsum (fun a => ?_) hsumRHS
  exact mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg

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

/-- On the odd support, `¬ goodTuple` is exactly the existence of a prefix `n ≤ n₀` whose valuation
sum `valSum N n` deviates from the mean `2n` by `≥ log^{0.6} x` (the positivity conjunct of
`goodTuple` is automatic for odd `N` by `valVec_pos`; `pre (valVec N n₀) n = valSum N n`). -/
theorem not_goodTuple_iff_prefix_dev {x : ℝ} {N n₀ : ℕ} (hN : N % 2 = 1) :
    ¬ goodTuple x n₀ (valVec N n₀) ↔
      ∃ n ∈ Finset.range (n₀ + 1), Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n| := by
  have hpos : ∀ i, 1 ≤ valVec N n₀ i := fun i => valVec_pos N n₀ hN i
  unfold goodTuple
  rw [not_and]
  constructor
  · intro h
    have hdev := h hpos
    push_neg at hdev
    obtain ⟨n, hn, hge⟩ := hdev
    exact ⟨n, Finset.mem_range.mpr (by omega), by rwa [pre_valVec (by omega : n ≤ n₀)] at hge⟩
  · rintro ⟨n, hn, hge⟩ _
    rw [Finset.mem_range] at hn
    push_neg
    exact ⟨n, by omega, by rw [pre_valVec (by omega : n ≤ n₀)]; exact hge⟩

/-! ### Analytic + marginal glue for the (5.12) core `goodTuple_prefix_dev_sum` (below)

These are the reusable bricks the good-tuple deviation sum needs: two elementary
`polynomial-in-log ≪ stretched-exponential` decay facts, an inline copy of the Sec6 prefix-block
marginal `iidMap_pre` (Sec6 is not imported here), the Gweight decay for a fixed threshold
`d·log^{0.6}x` over prefixes `n ≤ nZero x`, and the two-sided prefix analogue of
`iid_geomHalf_overflow_eq`. -/

/-- Real-variable version of `log_le_eps_mul_of_large`: `log w ≤ ε w` for `w` large. -/
theorem log_le_eps_mul_real {ε : ℝ} (hε : 0 < ε) :
    ∃ w₀ : ℝ, ∀ w : ℝ, w₀ ≤ w → Real.log w ≤ ε * w := by
  refine ⟨(2 / ε) ^ 2, fun w hw => ?_⟩
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hsqrt_pos : 0 < Real.sqrt w := Real.sqrt_pos.mpr hwpos
  have hsq : Real.sqrt w ^ 2 = w := Real.sq_sqrt hwpos.le
  have hlog_le : Real.log w ≤ 2 * Real.sqrt w := by
    calc Real.log w = Real.log (Real.sqrt w ^ 2) := by rw [hsq]
      _ = 2 * Real.log (Real.sqrt w) := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 2 * (Real.sqrt w - 1) := by
          have := Real.log_le_sub_one_of_pos hsqrt_pos; linarith
      _ ≤ 2 * Real.sqrt w := by linarith [hsqrt_pos.le]
  have hsqrt_lb : 2 / ε ≤ Real.sqrt w := by
    calc 2 / ε = Real.sqrt ((2 / ε) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt w := Real.sqrt_le_sqrt hw
  have hcomb : 2 * Real.sqrt w ≤ ε * w := by
    have h1 : (2 : ℝ) ≤ ε * Real.sqrt w := by
      have := mul_le_mul_of_nonneg_left hsqrt_lb hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    calc 2 * Real.sqrt w ≤ (ε * Real.sqrt w) * Real.sqrt w :=
          mul_le_mul_of_nonneg_right h1 hsqrt_pos.le
      _ = ε * (Real.sqrt w ^ 2) := by ring
      _ = ε * w := by rw [hsq]
  linarith

/-- Superpolynomial-decay core: for `p, κ, θ > 0`, once `x` is large,
`(log x)^p · exp(−κ·(log x)^θ) ≤ 1`.  (Polynomial-in-`log x` beaten by a stretched exponential.) -/
theorem log_rpow_mul_exp_neg_le_one {p κ θ : ℝ} (hp : 0 < p) (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (Real.log x) ^ p * Real.exp (-κ * (Real.log x) ^ θ) ≤ 1 := by
  obtain ⟨s₀, hs₀⟩ := log_le_eps_mul_real (ε := κ * θ / p) (by positivity)
  refine ⟨Real.exp (max ((max s₀ 1) ^ (1/θ)) 1), fun x hx => ?_⟩
  have hlogx : (max ((max s₀ 1) ^ (1/θ)) 1) ≤ Real.log x := by
    rw [← Real.log_exp (max ((max s₀ 1) ^ (1/θ)) 1)]
    exact Real.log_le_log (Real.exp_pos _) hx
  set w : ℝ := Real.log x with hwdef
  have hw1 : (1 : ℝ) ≤ w := le_trans (le_max_right _ _) hlogx
  have hwpos : 0 < w := lt_of_lt_of_le one_pos hw1
  have hwbig : (max s₀ 1) ^ (1/θ) ≤ w := le_trans (le_max_left _ _) hlogx
  set s : ℝ := w ^ θ with hsdef
  have hspos : 0 < s := Real.rpow_pos_of_pos hwpos θ
  have hsbig : max s₀ 1 ≤ s := by
    have hmono : ((max s₀ 1) ^ (1/θ)) ^ θ ≤ w ^ θ :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_max_of_le_right zero_le_one) _) hwbig hθ.le
    rwa [← Real.rpow_mul (le_max_of_le_right zero_le_one), one_div_mul_cancel hθ.ne',
      Real.rpow_one] at hmono
  have hkey : p * Real.log w ≤ κ * s := by
    have hs0 : s₀ ≤ s := le_trans (le_max_left _ _) hsbig
    have hlogs := hs₀ s hs0
    have hws : w = s ^ (1/θ) := by
      rw [hsdef, ← Real.rpow_mul hwpos.le, mul_one_div, div_self hθ.ne', Real.rpow_one]
    have hlogw : Real.log w = (1/θ) * Real.log s := by
      rw [hws, Real.log_rpow hspos]
    rw [hlogw]
    rw [show p * ((1/θ) * Real.log s) = (p/θ) * Real.log s by ring]
    have hpθ : 0 < p / θ := by positivity
    calc (p/θ) * Real.log s ≤ (p/θ) * ((κ * θ / p) * s) :=
          mul_le_mul_of_nonneg_left hlogs hpθ.le
      _ = κ * s := by field_simp [hp.ne', hθ.ne']
  have hexp : w ^ p ≤ Real.exp (κ * s) := by
    rw [Real.rpow_def_of_pos hwpos]
    exact Real.exp_le_exp.mpr (by rw [mul_comm (Real.log w) p]; exact hkey)
  calc w ^ p * Real.exp (-κ * s)
      ≤ Real.exp (κ * s) * Real.exp (-κ * s) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, show κ * s + -κ * s = 0 by ring, Real.exp_zero]

/-- Inline copy of `pre_eq_fin_sum_castLE` (lives in Sec6, not visible here). -/
theorem pre_eq_fin_sum_castLE' {n : ℕ} (a : Fin n → ℕ) {r : ℕ} (h : r ≤ n) :
    pre a r = ∑ i : Fin r, a (Fin.castLE h i) := by
  rw [pre, ← Fin.sum_univ_eq_sum_range (fun i => if hh : i < n then a ⟨i, hh⟩ else 0) r]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dif_pos (lt_of_lt_of_le i.isLt h)]
  rfl

/-- Inline copy of `iidMap_pre` (Sec6): under `geomHalf.iid n`, the prefix sum `pre a r` is
distributed as `iidSum geomHalf r`, for `r ≤ n`. -/
theorem iidMap_pre' (n r : ℕ) (h : r ≤ n) :
    (geomHalf.iid n).map (fun a : Fin n → ℕ => pre a r) = iidSum geomHalf r := by
  have hcomp : (fun a : Fin n → ℕ => pre a r)
      = (fun w : Fin r → ℕ => ∑ i, w i) ∘ (fun a : Fin n → ℕ => a ∘ Fin.castLE h) := by
    funext a; simp only [Function.comp_apply]; rw [pre_eq_fin_sum_castLE' a h]
  rw [hcomp, ← PMF.map_comp, iid_map_castLE geomHalf r n h]
  rfl

/-- The prefix Gweight decay: for `d > 0`, each `Gweight (1+n) (d·log^{0.6} x)` with `n ≤ nZero x`
is bounded by a stretched exponential `2·exp(−κ·log^{0.2} x)`.  (Both the `exp(−·²/(1+n))` term
— using `1+n ≤ log x / 4` — and the `exp(−d·log^{0.6}x)` term dominate `exp(−κ log^{0.2}x)`.) -/
theorem Gweight_prefix_decay {d : ℝ} (hd : 0 < d) :
    ∃ κ x₀ : ℝ, 0 < κ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ n : ℕ, n ≤ nZero x →
      Gweight (1 + n) (d * (Real.log x ^ (0.6:ℝ)))
        ≤ 2 * Real.exp (-κ * (Real.log x ^ (0.2:ℝ))) := by
  refine ⟨min (4 * d ^ 2) d, Real.exp 20, lt_min (by positivity) hd, fun x hx n hn => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set L : ℝ := Real.log x with hLdef
  have hL20 : (20 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 20]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLpos : 0 < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  set P02 : ℝ := L ^ (0.2 : ℝ) with hP02
  set P06 : ℝ := L ^ (0.6 : ℝ) with hP06
  have hP02pos : 0 < P02 := Real.rpow_pos_of_pos hLpos _
  have hP06pos : 0 < P06 := Real.rpow_pos_of_pos hLpos _
  have hP02ge1 : (1 : ℝ) ≤ P02 := Real.one_le_rpow hL1 (by norm_num)
  have hP0602 : P02 ≤ P06 := by
    rw [hP02, hP06]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hP06sq : P06 ^ 2 = L * P02 := by
    rw [hP06, hP02, ← Real.rpow_natCast (L ^ (0.6:ℝ)) 2, ← Real.rpow_mul hLpos.le,
      show (0.6:ℝ) * (2:ℕ) = 1.2 by push_cast; norm_num,
      show (1.2:ℝ) = 1 + 0.2 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := le_of_lt (by have := Real.log_two_gt_d9; linarith)
  have hnZ : (nZero x : ℝ) ≤ L / 5 := by
    have hfloor : (nZero x : ℝ) ≤ L / (10 * Real.log 2) := by
      rw [hLdef]; unfold nZero; exact Nat.floor_le (by positivity)
    refine le_trans hfloor
      ((div_le_div_iff_of_pos_left hLpos (by linarith) (by norm_num)).mpr (by linarith))
  have hnR : (n : ℝ) ≤ L / 5 := le_trans (by exact_mod_cast hn) hnZ
  have h1n4 : (1 : ℝ) + n ≤ L / 4 := by
    have h20 : (1 : ℝ) ≤ L / 20 := by linarith
    have : L / 5 + L / 20 ≤ L / 4 := by linarith
    linarith
  have h1npos : (0 : ℝ) < 1 + n := by positivity
  set κ : ℝ := min (4 * d ^ 2) d with hκdef
  have hκpos : 0 < κ := lt_min (by positivity) hd
  have hexpand : (d * P06) ^ 2 = d ^ 2 * (L * P02) := by rw [mul_pow, hP06sq]
  have hterm1 : Real.exp (-((d * P06) ^ 2) / (1 + n)) ≤ Real.exp (-κ * P02) := by
    apply Real.exp_le_exp.mpr
    have hκle : κ ≤ 4 * d ^ 2 := min_le_left _ _
    have hkey : κ * P02 * (1 + n) ≤ (d * P06) ^ 2 := by
      rw [hexpand]
      calc κ * P02 * (1 + n) ≤ 4 * d ^ 2 * P02 * (L / 4) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hκle hP02pos.le) h1n4 h1npos.le (by positivity)
        _ = d ^ 2 * (L * P02) := by ring
    rw [neg_div, neg_mul, neg_le_neg_iff, le_div_iff₀ h1npos]
    exact hkey
  have hterm2 : Real.exp (-|d * P06|) ≤ Real.exp (-κ * P02) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg (by positivity), neg_mul]
    have hκd : κ ≤ d := min_le_right _ _
    have hkey2 : κ * P02 ≤ d * P06 :=
      le_trans (mul_le_mul_of_nonneg_right hκd hP02pos.le) (mul_le_mul_of_nonneg_left hP0602 hd.le)
    linarith
  calc Gweight (1 + n) (d * P06)
      = Real.exp (-((d * P06) ^ 2) / (1 + n)) + Real.exp (-|d * P06|) := by simp only [Gweight]
    _ ≤ Real.exp (-κ * P02) + Real.exp (-κ * P02) := add_le_add hterm1 hterm2
    _ = 2 * Real.exp (-κ * P02) := by ring

/-- Prefix analogue of `iid_geomHalf_overflow_eq`, two-sided: the prefix deviation mass under
`geomHalf.iid n₀` equals the `iidSum geomHalf n` deviation mass, for `n ≤ n₀`. -/
theorem iid_prefix_twosided_eq (n₀ n : ℕ) (h : n ≤ n₀) (lam : ℝ) :
    (∑' a : Fin n₀ → ℕ, if lam ≤ |(pre a n : ℝ) - 2 * n| then ((geomHalf.iid n₀) a).toReal else 0)
      = (∑' L : ℕ, if lam ≤ |(L : ℝ) - 2 * n| then ((iidSum geomHalf n) L).toReal else 0) := by
  let E : Set ℕ := {L | lam ≤ |(L : ℝ) - 2 * n|}
  have hmap := PMF.expect_map_of_nonneg (geomHalf.iid n₀) (fun a => pre a n)
    (Set.indicator E 1) (fun L => Set.indicator_nonneg (fun _ _ => zero_le_one) L)
  rw [iidMap_pre' n₀ n h] at hmap
  unfold PMF.expect at hmap
  simpa only [Function.comp_apply, E, Set.indicator, Set.mem_setOf_eq, Pi.one_apply,
    mul_ite, mul_one, mul_zero] using hmap.symm

-- `first_passage_approx` (RATIFY-C8, Prop 5.2 / (5.8)) is proved at the END of this file
-- (after its sub-lemmas `first_passage_window_reduce` + `first_passage_affine_reindex`).

/-! ## Named decomposition of C8 (route + probe)

Two probabilistic sub-lemmas carry the analytic content of Prop 5.2; the rest of the proof is
pointwise event algebra (the `B_{n,y}` chain and the Lemma 2.1 affine bijection). Pinning these as
named `sorry`s converts the orange C8 seam into visible, attackable holes. -/

/-! **Paper (5.12)** — the good-tuple union bound.  Outside an event of probability `≪ log^{-c} x`
(the paper takes `log^{-10} x`), the full length-`n₀` valuation vector of `N_y` lies in the
good-tuple set `𝒜⁽ⁿ⁰⁾`.  The union-bound skeleton (`expect_le_add_of_indicator_le` +
`expect_le_sum_of_indicator_le` + `not_goodTuple_iff_prefix_dev`) is proved in
`approx_good_tuple_whp`; the analytic per-prefix bound is `goodTuple_prefix_dev_sum`.
From (5.4) [C5 / Prop 1.9, axiom-clean] and Lemma 2.2 [S3, two-sided, axiom-clean] each prefix
deviates by `≥ log^{0.6} x` w.p. `≪ exp(−c log^{0.2} x)`; sum over the `n₀ + 1` prefixes.
**Does not use C7.** -/

/-- **(5.12) analytic core** (owed) — the summed per-prefix deviation bound.  Each of the `n₀ + 1`
prefixes `valSum N n` deviates from its mean `2n` by `≥ log^{0.6} x` with probability
`≪ exp(−c log^{0.2} x)` (transfer to `geomHalf.iid` via C5 `valuation_dist`, then the two-sided
S3 `geomHalf_tail_bound`); the sum over prefixes is still `≪ log^{-c} x`.  This is the ONLY analytic
hole of `approx_good_tuple_whp` — the union-bound skeleton around it is proved. -/
theorem goodTuple_prefix_dev_sum :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        ∑ n ∈ Finset.range (nZero x + 1),
            (logUnifOdd y (y ^ alpha)).expect
              (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨K, hK, x₀e, herr⟩ := integral_test_logUnif
  obtain ⟨cd, Cd, hcd, hCd, hdist⟩ := valuation_dist 1 K (by norm_num) hK
  obtain ⟨ct, hct, Ct, hCt, htail⟩ := geomHalf_tail_bound
  obtain ⟨κ, x₀g, hκ, hGdecay⟩ := Gweight_prefix_decay (d := ct) hct
  obtain ⟨x₀A, hA⟩ := log_rpow_mul_exp_neg_le_one (p := 2) (κ := κ) (θ := 0.2)
    (by norm_num) hκ (by norm_num)
  obtain ⟨cq, x₀q, hcq, hqle⟩ := two_rpow_neg_nZero_le hcd
  obtain ⟨x₀B, hB⟩ := log_rpow_mul_exp_neg_le_one (p := 2) (κ := cq) (θ := 1)
    (by norm_num) hcq (by norm_num)
  refine ⟨1, 2 * Ct + Cd, max x₀e (max x₀A (max x₀q (max x₀B (max (Real.exp 20) x₀g)))),
    one_pos, by positivity, fun x hx y hy => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hxe, hxA, hxq, hxB, hx20, hxg⟩ := hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 20) hx20
  have hL20 : (20 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 20]; exact Real.log_le_log (Real.exp_pos _) hx20
  have hLpos : 0 < Real.log x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx20
  have hlam : (0 : ℝ) ≤ Real.log x ^ (0.6 : ℝ) := Real.rpow_nonneg hLpos.le _
  -- window preliminaries (mirror valSum_lower_geom)
  have hy1 : (1 : ℝ) ≤ y := by
    rcases hy with h | h <;> rw [h] <;>
      · rw [show (1 : ℝ) = (1 : ℝ) ^ (_ : ℝ) from (Real.one_rpow _).symm]
        exact Real.rpow_le_rpow (by norm_num) hx1 (by unfold alpha <;> positivity)
  have hyα1 : (1 : ℝ) ≤ y ^ alpha := by
    rw [show (1 : ℝ) = (1 : ℝ) ^ alpha from (Real.one_rpow _).symm]
    exact Real.rpow_le_rpow (by norm_num) hy1 (by unfold alpha; positivity)
  have hodd : ∀ N ∈ (logUnifOdd y (y ^ alpha)).support, N % 2 = 1 :=
    fun N hN => (logUnifOdd_support_le hyα1 hN).1
  have hsize : (2 + 1) * (nZero x : ℝ) ≤ ((3 * nZero x : ℕ) : ℝ) := le_of_eq (by push_cast; ring)
  have hmod : PMF.dTV ((logUnifOdd y (y ^ alpha)).map fun N => (N : ZMod (2 ^ (3 * nZero x))))
      (unifOddMod (3 * nZero x)) ≤ K * (2 : ℝ) ^ (-((3 * nZero x : ℕ) : ℝ)) := by
    rw [show ((3 * nZero x : ℕ) : ℝ) = 3 * (nZero x : ℝ) by push_cast; ring]
    exact herr x hxe y hy
  have hdistPQ := hdist (nZero x) (3 * nZero x) (logUnifOdd y (y ^ alpha)) hsize hodd hmod
  set P₀ : PMF (Fin (nZero x) → ℕ) := (logUnifOdd y (y ^ alpha)).map fun N => valVec N (nZero x)
    with hP₀def
  set Q₀ : PMF (Fin (nZero x) → ℕ) := geomHalf.iid (nZero x) with hQ₀def
  -- hdistPQ : P₀.dTV Q₀ ≤ Cd * 2^(-cd * n₀)
  -- STEP: per-prefix bound
  have hStep : ∀ n ∈ Finset.range (nZero x + 1),
      (logUnifOdd y (y ^ alpha)).expect
          (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
        ≤ Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ)) + P₀.dTV Q₀ := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hnle : n ≤ nZero x := by omega
    -- transfer to P₀
    have htarget : (logUnifOdd y (y ^ alpha)).expect
        (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
        = P₀.expect (Set.indicator
            {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1) := by
      rw [hP₀def, PMF.expect_map_of_nonneg (logUnifOdd y (y ^ alpha)) (fun N => valVec N (nZero x))
        (Set.indicator {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
        (fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) a)]
      unfold PMF.expect
      apply tsum_congr; intro N; congr 1
      simp only [Function.comp_apply, Set.indicator_apply, Set.mem_setOf_eq,
        pre_valVec hnle, Pi.one_apply]
    have hev := PMF.abs_expect_indicator_sub_le_dTV P₀ Q₀
      {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|}
    have hXe : P₀.expect (Set.indicator
          {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
        ≤ Q₀.expect (Set.indicator
          {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
          + P₀.dTV Q₀ := by
      have := le_abs_self (P₀.expect (Set.indicator
        {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
        - Q₀.expect (Set.indicator
        {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1))
      linarith [hev, this]
    have hQside : Q₀.expect (Set.indicator
          {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
        ≤ Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ)) := by
      have hexpand : Q₀.expect (Set.indicator
          {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
          = ∑' a : Fin (nZero x) → ℕ,
              if Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|
                then (Q₀ a).toReal else 0 := by
        unfold PMF.expect
        apply tsum_congr; intro a
        simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, mul_ite, mul_one, mul_zero]
      rw [hexpand, hQ₀def, iid_prefix_twosided_eq (nZero x) n hnle (Real.log x ^ (0.6 : ℝ))]
      exact htail n (Real.log x ^ (0.6 : ℝ)) hlam
    rw [htarget]; linarith [hXe, hQside]
  -- sum the steps
  have hsum1 := Finset.sum_le_sum hStep
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum1
  -- bound the Gweight sum by (n₀+1)·(Ct·2·exp(-κ·log^{0.2}x))
  have hGsum : ∑ n ∈ Finset.range (nZero x + 1), Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ))
      ≤ ((nZero x + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ)))) := by
    have hle : ∀ n ∈ Finset.range (nZero x + 1),
        Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ))
          ≤ Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) := fun n hn =>
      mul_le_mul_of_nonneg_left (hGdecay x hxg n (by rw [Finset.mem_range] at hn; omega)) hCt.le
    calc ∑ n ∈ Finset.range (nZero x + 1), Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ))
        ≤ ∑ _n ∈ Finset.range (nZero x + 1), Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) :=
          Finset.sum_le_sum hle
      _ = ((nZero x + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- (n₀+1 : ℝ) ≤ log x
  have hnZ5 : (nZero x : ℝ) ≤ Real.log x / 5 := by
    have hfloor : (nZero x : ℝ) ≤ Real.log x / (10 * Real.log 2) := by
      unfold nZero; exact Nat.floor_le (by positivity)
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := le_of_lt (by have := Real.log_two_gt_d9; linarith)
    exact le_trans hfloor
      ((div_le_div_iff_of_pos_left hLpos (by linarith) (by norm_num)).mpr (by linarith))
  have hn1L : ((nZero x + 1 : ℕ) : ℝ) ≤ Real.log x := by push_cast; linarith [hnZ5]
  -- the "shrink" step: log x · E ≤ (log x)^{-1} when (log x)^2 · E ≤ 1
  have shrink : ∀ E : ℝ, 0 ≤ E → (Real.log x) ^ (2 : ℝ) * E ≤ 1 →
      Real.log x * E ≤ (Real.log x) ^ (-(1 : ℝ)) := by
    intro E hE0 hE
    have h1 : (Real.log x) ^ (-(1 : ℝ)) * (Real.log x) ^ (2 : ℝ) = Real.log x := by
      rw [← Real.rpow_add hLpos]; norm_num
    calc Real.log x * E = ((Real.log x) ^ (-(1 : ℝ)) * (Real.log x) ^ (2 : ℝ)) * E := by rw [h1]
      _ = (Real.log x) ^ (-(1 : ℝ)) * ((Real.log x) ^ (2 : ℝ) * E) := by ring
      _ ≤ (Real.log x) ^ (-(1 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hLpos.le _)
      _ = (Real.log x) ^ (-(1 : ℝ)) := mul_one _
  -- A-term: the Gweight-decay sum contribution
  have hAterm : ((nZero x + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))))
      ≤ 2 * Ct * (Real.log x) ^ (-(1 : ℝ)) := by
    have hE0 : (0 : ℝ) ≤ Real.exp (-κ * Real.log x ^ (0.2 : ℝ)) := (Real.exp_pos _).le
    have hs := shrink _ hE0 (hA x hxA)
    calc ((nZero x + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))))
        = 2 * Ct * (((nZero x + 1 : ℕ) : ℝ) * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) := by ring
      _ ≤ 2 * Ct * (Real.log x * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn1L hE0) (by positivity)
      _ ≤ 2 * Ct * (Real.log x) ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_left hs (by positivity)
  -- B-term: the dTV contribution
  have hBterm : ((nZero x + 1 : ℕ) : ℝ) * (P₀.dTV Q₀) ≤ Cd * (Real.log x) ^ (-(1 : ℝ)) := by
    have hdtv : P₀.dTV Q₀ ≤ Cd * x ^ (-cq) :=
      le_trans hdistPQ (mul_le_mul_of_nonneg_left (hqle x hxq) hCd.le)
    have hxexp : x ^ (-cq) = Real.exp (-cq * (Real.log x) ^ (1 : ℝ)) := by
      rw [Real.rpow_one, Real.rpow_def_of_pos hxpos, mul_comm (Real.log x) (-cq)]
    have hE0 : (0 : ℝ) ≤ Real.exp (-cq * (Real.log x) ^ (1 : ℝ)) := (Real.exp_pos _).le
    have hs := shrink _ hE0 (hB x hxB)
    calc ((nZero x + 1 : ℕ) : ℝ) * (P₀.dTV Q₀)
        ≤ ((nZero x + 1 : ℕ) : ℝ) * (Cd * x ^ (-cq)) :=
          mul_le_mul_of_nonneg_left hdtv (by positivity)
      _ = Cd * (((nZero x + 1 : ℕ) : ℝ) * Real.exp (-cq * (Real.log x) ^ (1 : ℝ))) := by
          rw [hxexp]; ring
      _ ≤ Cd * (Real.log x * Real.exp (-cq * (Real.log x) ^ (1 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn1L hE0) hCd.le
      _ ≤ Cd * (Real.log x) ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_left hs hCd.le
  -- assemble
  calc ∑ n ∈ Finset.range (nZero x + 1),
          (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
      ≤ (∑ n ∈ Finset.range (nZero x + 1), Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ)))
          + ((nZero x + 1 : ℕ) : ℝ) * (P₀.dTV Q₀) := hsum1
    _ ≤ ((nZero x + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))))
          + ((nZero x + 1 : ℕ) : ℝ) * (P₀.dTV Q₀) := by linarith [hGsum]
    _ ≤ 2 * Ct * (Real.log x) ^ (-(1 : ℝ)) + Cd * (Real.log x) ^ (-(1 : ℝ)) := by
        linarith [hAterm, hBterm]
    _ = (2 * Ct + Cd) * (Real.log x) ^ (-(1 : ℝ)) := by ring

theorem approx_good_tuple_whp :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨c, C, x₀, hc, hC, hsum⟩ := goodTuple_prefix_dev_sum
  refine ⟨c, C, max x₀ 1, hc, hC, fun x hx y hy => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hyα1 : (1 : ℝ) ≤ y ^ alpha := by
    have hy1 : (1 : ℝ) ≤ y := by
      rcases hy with h | h <;> rw [h] <;>
        · rw [show (1 : ℝ) = (1 : ℝ) ^ (_ : ℝ) from (Real.one_rpow _).symm]
          exact Real.rpow_le_rpow (by norm_num) hx1 (by unfold alpha <;> positivity)
    rw [show (1 : ℝ) = (1 : ℝ) ^ alpha from (Real.one_rpow _).symm]
    exact Real.rpow_le_rpow (by norm_num) hy1 (by unfold alpha; positivity)
  set P := logUnifOdd y (y ^ alpha) with hPdef
  have heven0 : P.expect (Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1) = 0 := by
    have hzero : ∀ a, (P a).toReal * Set.indicator {N : ℕ | ¬ (N % 2 = 1)} (1 : ℕ → ℝ) a = 0 := by
      intro a
      by_cases ha : P a = 0
      · rw [ha]; simp
      · have hmem : a ∈ P.support := ha
        have hodd : a % 2 = 1 := (logUnifOdd_support_le hyα1 hmem).1
        rw [Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq, not_not]; exact hodd)]; ring
    show ∑' a, (P a).toReal * Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1 a = 0
    simp_rw [hzero]; exact tsum_zero
  have hpw1 : ∀ N, Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} (1 : ℕ → ℝ) N ≤
      Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1 N +
      Set.indicator {N | ∃ n ∈ Finset.range (nZero x + 1),
        Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1 N := by
    intro N
    have h1 : (0 : ℝ) ≤ Set.indicator {N : ℕ | ¬ (N % 2 = 1)} (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    have h2 : (0 : ℝ) ≤ Set.indicator {N | ∃ n ∈ Finset.range (nZero x + 1),
        Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    by_cases hN : N ∈ {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))}
    · rw [Set.indicator_of_mem hN, Pi.one_apply]
      by_cases hodd : N % 2 = 1
      · have hmem : N ∈ {N | ∃ n ∈ Finset.range (nZero x + 1),
            Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} :=
          (not_goodTuple_iff_prefix_dev hodd).mp hN
        rw [Set.indicator_of_mem hmem, Pi.one_apply]; linarith
      · rw [Set.indicator_of_mem (show N ∈ {N : ℕ | ¬ (N % 2 = 1)} from hodd), Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hN]; linarith
  have hpw2 : ∀ N, Set.indicator {N | ∃ n ∈ Finset.range (nZero x + 1),
        Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} (1 : ℕ → ℝ) N ≤
      ∑ n ∈ Finset.range (nZero x + 1),
        Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1 N := by
    intro N
    by_cases hN : N ∈ {N | ∃ n ∈ Finset.range (nZero x + 1),
        Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|}
    · rw [Set.indicator_of_mem hN, Pi.one_apply]
      obtain ⟨n, hn, hdev⟩ := hN
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun k => Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N k : ℝ) - 2 * k|}
          (1 : ℕ → ℝ) N)
        (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) N) hn)
      rw [Set.indicator_of_mem (show N ∈ {M | Real.log x ^ (0.6 : ℝ) ≤ |(valSum M n : ℝ) - 2 * n|}
        from hdev), Pi.one_apply]
    · rw [Set.indicator_of_notMem hN]
      exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) N)
  calc P.expect (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
      ≤ P.expect (Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1)
          + P.expect (Set.indicator {N | ∃ n ∈ Finset.range (nZero x + 1),
              Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1) :=
        expect_le_add_of_indicator_le _ _ _ _ hpw1
    _ = P.expect (Set.indicator {N | ∃ n ∈ Finset.range (nZero x + 1),
              Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1) := by rw [heven0]; ring
    _ ≤ ∑ n ∈ Finset.range (nZero x + 1),
          P.expect (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1) :=
        expect_le_sum_of_indicator_le _ _ _ _ hpw2
    _ ≤ C * (Real.log x) ^ (-c) := hsum x hx0 y hy

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

/-! ## C8 assembly: the `first_passage_approx` (5.8) chain, decomposed

The assembly runs `ℙ(Pass_x(N_y) ∈ E)  →  firstPassMid  →  approxMainTerm`.  `firstPassMid` is the
probability restricted to the good-tuple × window event and partitioned by the passage time
`T_x(N_y) = n` over `n ∈ I_y` (paper (5.9)); it is the natural bridge between the raw passage
probability and the affine main term.  Two owed sub-lemmas carry the two legs:

* `first_passage_window_reduce` — the (5.12)+(5.16) whp reduction: replacing `{Pass ∈ E}` by its
  restriction to `good ∧ (passes ∧ T_x ∈ I_y)` and partitioning by `T_x = n` costs `O(log^{-c}x)`.
  Consumes the two PROVED whp lemmas `approx_good_tuple_whp` and `approx_passtime_window`.
* `first_passage_affine_reindex` — the (5.17) `B_{n,y}` event chain + (5.18) Lemma 2.1 affine
  reindexing (APPROXIMATE — truncation absorbed, see the module docstring).  This is the
  route-decisive leg against the pinned `approxMainTerm`.

`first_passage_approx` itself is then a triangle inequality over these two, mirroring the
`approx_passtime_window` combine. -/

open Classical in
/-- The bridge term for (5.8): the passage-location probability restricted to the good-tuple event
and partitioned by the passage time `T_x(N_y) = n` over the window `I_y` (5.9). -/
noncomputable def firstPassMid (x : ℝ) (E : Set ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Iy x y,
    (logUnifOdd y (y ^ alpha)).expect
      (Set.indicator {N | passTime ⌊x⌋₊ N = n ∧ passLoc ⌊x⌋₊ N ∈ E ∧
        goodTuple x (nZero x) (valVec N (nZero x))} 1)

/-- **(5.12)+(5.16) whp reduction** (owed) — the first leg of (5.8).  Passing from the raw
`ℙ(Pass_x(N_y) ∈ E)` to the restricted, `T_x`-partitioned `firstPassMid` costs `O(log^{-c} x)`:
the discarded mass lies in `{¬ good} ∪ {¬ (passes ∧ T_x ∈ I_y)}`, each `≪ log^{-c} x` by the two
PROVED whp lemmas `approx_good_tuple_whp` (5.12) and `approx_passtime_window` (5.16).  (On the
complementary good∩window event, `{Pass ∈ E}` is the disjoint union over `n ∈ I_y` of
`{T_x = n ∧ Pass ∈ E ∧ good}`, so the partition is exact there.) -/
theorem first_passage_window_reduce :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
              - firstPassMid x E y|
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨cg, Cg, xg, hcg, hCg, hgood⟩ := approx_good_tuple_whp
  obtain ⟨cw, Cw, xw, hcw, hCw, hwin⟩ := approx_passtime_window
  refine ⟨min cg cw, Cg + Cw, max (max xg xw) (Real.exp 1), lt_min hcg hcw, by positivity,
    fun x hx E hE y hy => ?_⟩
  have hxg : xg ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxw : xw ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  classical
  set P := logUnifOdd y (y ^ alpha) with hP
  -- the big restricted event
  set Sbig : Set ℕ := {N | passTime ⌊x⌋₊ N ∈ Iy x y ∧ passLoc ⌊x⌋₊ N ∈ E ∧
    goodTuple x (nZero x) (valVec N (nZero x))} with hSbig
  have hsum : ∀ (V : Set ℕ), Summable fun a => (P a).toReal * Set.indicator V 1 a := by
    intro V
    have hsumP : Summable fun a => (P a).toReal := ENNReal.summable_toReal P.tsum_coe_ne_top
    refine Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) a))
      (fun a => ?_) hsumP
    rw [Set.indicator_apply]; split
    · simp
    · simp
  -- Step 1: firstPassMid = P.expect (ind Sbig)
  have hcollapse : ∀ a, Set.indicator Sbig (1 : ℕ → ℝ) a
      = ∑ n ∈ Iy x y, Set.indicator {N | passTime ⌊x⌋₊ N = n ∧ passLoc ⌊x⌋₊ N ∈ E ∧
          goodTuple x (nZero x) (valVec N (nZero x))} 1 a := by
    intro a
    by_cases hP2 : passLoc ⌊x⌋₊ a ∈ E ∧ goodTuple x (nZero x) (valVec a (nZero x))
    · by_cases hT : passTime ⌊x⌋₊ a ∈ Iy x y
      · rw [Set.indicator_of_mem (show a ∈ Sbig from ⟨hT, hP2.1, hP2.2⟩), Pi.one_apply]
        rw [Finset.sum_eq_single (passTime ⌊x⌋₊ a)]
        · rw [Set.indicator_of_mem (show a ∈ {N | passTime ⌊x⌋₊ N = passTime ⌊x⌋₊ a ∧
            passLoc ⌊x⌋₊ N ∈ E ∧ goodTuple x (nZero x) (valVec N (nZero x))} from
            ⟨rfl, hP2.1, hP2.2⟩), Pi.one_apply]
        · intro n _ hne
          rw [Set.indicator_of_notMem]
          simp only [Set.mem_setOf_eq]; rintro ⟨he, _, _⟩; exact hne he.symm
        · intro hna; exact absurd hT hna
      · rw [Set.indicator_of_notMem (show a ∉ Sbig from fun h => hT h.1)]
        symm
        apply Finset.sum_eq_zero
        intro n hn
        rw [Set.indicator_of_notMem]
        simp only [Set.mem_setOf_eq]; rintro ⟨he, _, _⟩; exact hT (he ▸ hn)
    · rw [Set.indicator_of_notMem (show a ∉ Sbig from fun h => hP2 ⟨h.2.1, h.2.2⟩)]
      symm
      apply Finset.sum_eq_zero
      intro n _
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_setOf_eq]; rintro ⟨_, h2, h3⟩; exact hP2 ⟨h2, h3⟩
  have hmid : firstPassMid x E y = P.expect (Set.indicator Sbig 1) := by
    unfold firstPassMid PMF.expect
    rw [← hP]
    rw [← Summable.tsum_finsetSum (fun n _ => hsum _)]
    apply tsum_congr; intro a
    rw [hcollapse a, Finset.mul_sum]
  -- Step 2: pointwise domination indA ≤ ind Sbig + ind U23, ind U23 ≤ ind¬G + ind¬window
  set U23 : Set ℕ := {N | ¬ goodTuple x (nZero x) (valVec N (nZero x)) ∨
    ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} with hU23
  have hpw1 : ∀ N, Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} (1 : ℕ → ℝ) N ≤
      Set.indicator Sbig 1 N + Set.indicator U23 1 N := by
    intro N
    have h1 : (0 : ℝ) ≤ Set.indicator Sbig (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    have h2 : (0 : ℝ) ≤ Set.indicator U23 (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    by_cases hN : N ∈ {N | passLoc ⌊x⌋₊ N ∈ E}
    · rw [Set.indicator_of_mem hN, Pi.one_apply]
      by_cases hG : goodTuple x (nZero x) (valVec N (nZero x))
      · by_cases hT : passTime ⌊x⌋₊ N ∈ Iy x y
        · rw [Set.indicator_of_mem (show N ∈ Sbig from ⟨hT, hN, hG⟩), Pi.one_apply]; linarith
        · rw [Set.indicator_of_mem (show N ∈ U23 from Or.inr (fun h => hT h.2)), Pi.one_apply]
          linarith
      · rw [Set.indicator_of_mem (show N ∈ U23 from Or.inl hG), Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hN]; linarith
  have hpw2 : ∀ N, Set.indicator U23 (1 : ℕ → ℝ) N ≤
      Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1 N +
      Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1 N := by
    intro N
    have h1 : (0 : ℝ) ≤ Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))}
      (1 : ℕ → ℝ) N := Set.indicator_nonneg (fun _ _ => zero_le_one) N
    have h2 : (0 : ℝ) ≤ Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)}
      (1 : ℕ → ℝ) N := Set.indicator_nonneg (fun _ _ => zero_le_one) N
    by_cases hN : N ∈ U23
    · rw [Set.indicator_of_mem hN, Pi.one_apply]
      rcases hN with hg | hw
      · rw [Set.indicator_of_mem (show N ∈ {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))}
          from hg), Pi.one_apply]; linarith
      · rw [Set.indicator_of_mem (show N ∈ {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)}
          from hw), Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hN]; linarith
  -- combine
  have hAbound : P.expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
      ≤ P.expect (Set.indicator Sbig 1) + (P.expect (Set.indicator
          {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
        + P.expect (Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1)) := by
    refine le_trans (expect_le_add_of_indicator_le P _ Sbig U23 hpw1) ?_
    gcongr
    exact expect_le_add_of_indicator_le P U23 _ _ hpw2
  -- firstPassMid ≤ P.expect (indA)  (ind Sbig ≤ indA pointwise)
  have hsub : Sbig ⊆ {N | passLoc ⌊x⌋₊ N ∈ E} := fun a ha => ha.2.1
  have hmidle : firstPassMid x E y ≤ P.expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1) := by
    rw [hmid]
    unfold PMF.expect
    refine (hsum Sbig).tsum_le_tsum
      (fun a => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg) (hsum _)
    exact Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le_one) a
  have hA : (Real.log x) ^ (-cg) ≤ (Real.log x) ^ (-(min cg cw)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_left cg cw))
  have hB : (Real.log x) ^ (-cw) ≤ (Real.log x) ^ (-(min cg cw)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_right cg cw))
  rw [abs_of_nonneg (by linarith [hmidle])]
  have hthis := hAbound
  rw [← hmid] at hthis
  calc P.expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1) - firstPassMid x E y
      ≤ Cg * (Real.log x) ^ (-cg) + Cw * (Real.log x) ^ (-cw) := by
        linarith [hgood x hxg y hy, hwin x hxw y hy, hthis]
    _ ≤ Cg * (Real.log x) ^ (-(min cg cw)) + Cw * (Real.log x) ^ (-(min cg cw)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hCg.le) (mul_le_mul_of_nonneg_left hB hCw.le)
    _ = (Cg + Cw) * (Real.log x) ^ (-(min cg cw)) := by ring

/-- **(5.17) `B_{n,y}` event chain + (5.18) Lemma 2.1 affine reindexing** (owed) — the second,
route-decisive leg of (5.8).  For each `n ∈ I_y`, the event `{T_x(N_y)=n ∧ Pass∈E ∧ good}` equals
(step back `m₀` steps, (5.17)) `{Syr^{n-m₀}(N_y) ∈ E' ∧ good}`, whose probability the Lemma 2.1
affine bijection reindexes to `∑_{ā∈𝒜⁽ⁿ⁻ᵐ⁰⁾} ∑_{M∈E'} ℙ(Aff_ā(N_y)=M)` — the summand of
`approxMainTerm`.  The reindex is APPROXIMATE (`Aff` uses truncating ℕ-division; the truncation
coincidences are absorbed in `O(log^{-c}x)`, see the module docstring), so this is the `≤`/error
form, NOT an exact identity.  Kernels `aff_valVec_eq_syr` + `valVec_unique` drive the main term. -/
theorem first_passage_affine_reindex :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |firstPassMid x E y - approxMainTerm x E y|
            ≤ C * (Real.log x) ^ (-c) := by
  sorry

-- RATIFY-C8: paper Proposition 5.2 / (5.8), §5 pp.22–25.  Rendered against the numbered display;
-- the `O(log^{-c} x)` error is spelled as an explicit `∃ c C x₀` bound (design invariant D3).
/-- **Proposition 5.2** (approximate first-passage formula, paper (5.8)).  For every odd
`E ⊂ [1,x]` and `y ∈ {x^α, x^{α²}}`, the passage-location probability `ℙ(Pass_x(N_y) ∈ E)` agrees
with the affine main term `approxMainTerm` up to `O(log^{-c} x)`:
`ℙ(Pass_x(N_y) ∈ E) = ∑_{n∈I_y} ∑_{ā∈𝒜} ∑_{M∈E'} ℙ(Aff_ā(N_y) = M) + O(log^{-c} x)`.

This is node **C8**.  Proof: triangle inequality over the two owed legs
`first_passage_window_reduce` [(5.12)+(5.16) whp reduction to `firstPassMid`] and
`first_passage_affine_reindex` [(5.17) `B_{n,y}` chain + (5.18) affine reindexing to
`approxMainTerm`]. -/
theorem first_passage_approx :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
              - approxMainTerm x E y|
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨c₁, C₁, x₁, hc₁, hC₁, hwr⟩ := first_passage_window_reduce
  obtain ⟨c₂, C₂, x₂, hc₂, hC₂, har⟩ := first_passage_affine_reindex
  refine ⟨min c₁ c₂, C₁ + C₂, max (max x₁ x₂) (Real.exp 1), lt_min hc₁ hc₂, by positivity,
    fun x hx E hE y hy => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hA : (Real.log x) ^ (-c₁) ≤ (Real.log x) ^ (-(min c₁ c₂)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_left c₁ c₂))
  have hB : (Real.log x) ^ (-c₂) ≤ (Real.log x) ^ (-(min c₁ c₂)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_right c₁ c₂))
  calc |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
          - approxMainTerm x E y|
      ≤ |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
            - firstPassMid x E y|
          + |firstPassMid x E y - approxMainTerm x E y| := abs_sub_le _ _ _
    _ ≤ C₁ * (Real.log x) ^ (-c₁) + C₂ * (Real.log x) ^ (-c₂) :=
        add_le_add (hwr x hx1 E hE y hy) (har x hx2 E hE y hy)
    _ ≤ C₁ * (Real.log x) ^ (-(min c₁ c₂)) + C₂ * (Real.log x) ^ (-(min c₁ c₂)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hC₁.le) (mul_le_mul_of_nonneg_left hB hC₂.le)
    _ = (C₁ + C₂) * (Real.log x) ^ (-(min c₁ c₂)) := by ring

end TaoCollatz
