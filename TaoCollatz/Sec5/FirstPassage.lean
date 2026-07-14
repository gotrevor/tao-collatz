import TaoCollatz.Syracuse.ValuationDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §5 first-passage machinery (nodes C7/C8 defs)

Paper anchors: Tao 2019 §1.3, §5, (1.18), Proposition 1.11.

Definitions for the first passage of the Syracuse orbit below `x`: `passes`,
`passTime`, `passLoc` (paper `Pass_x`, with the `Syr^∞ := 1` convention), the
log-uniform window `logUnifOdd`, and the constant `alpha` (1.18). The stabilization
proposition (Prop 1.11 — the spine's key input) carries `sorry`.
-/

open scoped ENNReal

namespace TaoCollatz

/-- `T_x(N) < ∞`: the Syracuse orbit of `N` eventually drops to `≤ x`. -/
def passes (x N : ℕ) : Prop := ∃ n, syr^[n] N ≤ x

/-- First passage time `T_x(N)` below `x` (junk `0` if it never passes). -/
noncomputable def passTime (x N : ℕ) : ℕ := sInf {n | syr^[n] N ≤ x}

open Classical in
/-- First passage location `Pass_x(N)`, with the paper's `Syr^∞ := 1` convention. -/
noncomputable def passLoc (x N : ℕ) : ℕ := if passes x N then syr^[passTime x N] N else 1

/-- The odd numbers in `[lo, hi]`, as a `Finset` (window support). -/
noncomputable def logWindow (lo hi : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil hi + 1)).filter fun N => N % 2 = 1 ∧ lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi

/-- Log-uniform distribution on the odd numbers in `[lo, hi]` (mass `∝ 1/N`);
falls back to `pure 1` when the window is empty. -/
noncomputable def logUnifOdd (lo hi : ℝ) : PMF ℕ :=
  if h : (logWindow lo hi).Nonempty then
    PMF.ofFinset
      (fun N => if N ∈ logWindow lo hi then
          (N : ℝ≥0∞)⁻¹ / ∑ M ∈ logWindow lo hi, (M : ℝ≥0∞)⁻¹ else 0)
      (logWindow lo hi)
      (by
        -- denominator `D = ∑_{M∈W} M⁻¹` is positive (nonempty window) and finite (odd ⇒ M≠0),
        -- so `∑_{N∈W} N⁻¹/D = D/D = 1`.
        have hnetop : (∑ M ∈ logWindow lo hi, (M : ℝ≥0∞)⁻¹) ≠ ∞ := by
          rw [ENNReal.sum_ne_top]
          intro M hM
          rw [ENNReal.inv_ne_top]
          simp only [logWindow, Finset.mem_filter] at hM
          have : M % 2 = 1 := hM.2.1
          simp only [ne_eq, Nat.cast_eq_zero]; omega
        have hne0 : (∑ M ∈ logWindow lo hi, (M : ℝ≥0∞)⁻¹) ≠ 0 := by
          obtain ⟨M₀, hM₀⟩ := h
          intro hsum0
          rw [Finset.sum_eq_zero_iff] at hsum0
          have h0 := hsum0 M₀ hM₀
          rw [ENNReal.inv_eq_zero] at h0
          exact ENNReal.natCast_ne_top M₀ h0
        rw [Finset.sum_congr rfl (fun N hN => if_pos hN)]
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, ENNReal.mul_inv_cancel hne0 hnetop])
      (by intro a ha; rw [if_neg ha])
  else PMF.pure 1

/-- Paper (1.18): the scaling exponent `α = 1.001`. -/
def alpha : ℝ := 1.001

/-- Paper (5.1): `n₀ := ⌊log x / (10 log 2)⌋`, so `2^{n₀} ≍ x^{0.1}`. -/
noncomputable def nZero (x : ℝ) : ℕ := ⌊Real.log x / (10 * Real.log 2)⌋₊

/-- Paper (5.2): `m₀ := ⌊(α−1)/100 · log x⌋` — the fixed number of backward steps. -/
noncomputable def mZero (x : ℝ) : ℕ := ⌊(alpha - 1) / 100 * Real.log x⌋₊

/-! ### C7 decomposition (route + probe of paper (1.19), §5 pp.20–21)

`first_passage_nonescape` (below) assembles from three named sub-lemmas. This converts the single
C7 sorry into visible, attackable holes and isolates the ONE new analytic brick (the integral test).

**The route** (Tao pp.20–21):
1. `integral_test_logUnif` — ⚠️ **the crux, the only new brick.** The integral test
   `dTV(N_y mod 2^{n'}, Unif) ≪ 2^{-n'}` at `n' = 3 n₀`. It is exactly the hypothesis that
   `valuation_dist` / `valuation_tail` (Prop 1.9 / Lemma 4.1, node C5) **take** — those lemmas do
   not prove it; C7 must supply it for `X = logUnifOdd`.
2. `valSum_lower_tail` — paper (5.5): `ℙ(|ā^{(n₀)}(N_y)| ≤ 1.9 n₀) ≪ x^{-c}`. This is the LOWER-tail
   analogue of `valuation_tail` (which does the upper tail); both consume the integral test via
   `valuation_dist` (5.4) and then `geomHalf_tail_bound` (S3, two-sided).
3. `descent_passes` — the (1.5)/(1.7) descent: if `|ā^{(n₀)}(N_y)| > 1.9 n₀` then
   `Syr^{n₀}(N_y) = O(x^{0.99}) ≤ x`, hence `passes`. Pointwise, over `syr_iterate_key` (C2). -/

/-- **The integral test** (Tao pp.20, the one new analytic brick of C7).  For the log-uniform window
`N_y` on odds in `[y, y^α]`, its reduction mod `2^{3 n₀}` is within `≪ 2^{-3 n₀}` (total variation)
of the uniform law on odd residues.  This is precisely the hypothesis consumed by `valuation_dist`
(Prop 1.9) and `valuation_tail` (Lemma 4.1); they do NOT prove it.  Owed.

Proof idea (owed): the count of odd `N ∈ [y,y^α]` in a fixed residue class mod `2^{3n₀}` is
`(1 + O(2^{3n₀}/y))` times the average, by comparing `∑_{N ≡ r} 1/N` to `∫ dt/t` over the window
(the "integral test" / summation-by-parts); with `2^{3n₀} ≍ x^{0.3} ≪ y ≍ x`, the error is `≪ 2^{-3n₀}`. -/
theorem integral_test_logUnif :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        PMF.dTV ((logUnifOdd y (y ^ alpha)).map fun N => (N : ZMod (2 ^ (3 * nZero x))))
                (unifOddMod (3 * nZero x))
          ≤ K * (2 : ℝ) ^ (-(3 * (nZero x : ℝ))) := by
  sorry

/-- **Paper (5.5)** — the lower-tail bound: the total valuation `|ā^{(n₀)}(N_y)| = valSum N_y n₀`
falls at or below `1.9 n₀` with probability `≪ x^{-c}`.  This is the LOWER-tail analogue of
`valuation_tail` (Lemma 4.1, which bounds the UPPER tail `≥ n'`).  Proof (owed): feed
`integral_test_logUnif` into `valuation_dist` for (5.4) `dTV(valVec N_y n₀, Geom(2)^{n₀}) ≪ 2^{-c n₀}`,
then `geomHalf_tail_bound` (two-sided) bounds `ℙ(|Geom(2)^{n₀}| ≤ 1.9 n₀) = ℙ(deviation ≥ 0.1 n₀)`;
convert `2^{-c n₀} ≪ x^{-c}` via `n₀ ≍ log x / (10 log 2)` (5.1). -/
theorem valSum_lower_tail :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | (valSum N (nZero x) : ℝ) ≤ 1.9 * (nZero x : ℝ)} 1)
          ≤ C * x ^ (-c) := by
  sorry

/-- **Support extraction for the log-uniform window.**  Any `N` in the support of `logUnifOdd lo hi`
is odd and `≤ hi` (in the nonempty case it lies in `logWindow lo hi`; in the degenerate empty case
the support is the point mass `{1}`, and `1` is odd and `≤ hi` when `hi ≥ 1`). -/
theorem logUnifOdd_support_le {lo hi : ℝ} (hhi : 1 ≤ hi)
    {N : ℕ} (hN : N ∈ (logUnifOdd lo hi).support) : N % 2 = 1 ∧ (N : ℝ) ≤ hi := by
  unfold logUnifOdd at hN
  by_cases h : (logWindow lo hi).Nonempty
  · rw [dif_pos h, PMF.mem_support_ofFinset_iff] at hN
    have hw := hN.1
    simp only [logWindow, Finset.mem_filter, Finset.mem_range] at hw
    exact ⟨hw.2.1, hw.2.2.2⟩
  · rw [dif_neg h, PMF.mem_support_iff, PMF.pure_apply] at hN
    have hN1 : N = 1 := by by_contra hne; simp [hne] at hN
    subst hN1
    exact ⟨by norm_num, by exact_mod_cast hhi⟩

/-- **Sub-linear powers are eventually dominated.**  For `0 ≤ θ < 1` and `ε > 0`, `x^θ ≤ ε·x` for
all large `x`.  (Take `x₀ = max 1 ((1/ε)^{1/(1-θ)}`).)  The workhorse for the `O(x^{0.99}) ≤ x`
closing of the descent. -/
theorem rpow_le_eps_mul_of_lt_one {θ ε : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → x ^ θ ≤ ε * x := by
  refine ⟨max 1 ((1 / ε) ^ (1 / (1 - θ))), le_max_left _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : 0 < x := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hlb : (1 / ε) ^ (1 / (1 - θ)) ≤ x := le_trans (le_max_right _ _) hx
  have hkey : 1 / ε ≤ x ^ (1 - θ) := by
    have hmono := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hlb (le_of_lt h1θ)
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt h1θ), Real.rpow_one] at hmono
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hxpos θ
  have hsplit : x ^ θ * x ^ (1 - θ) = x := by
    rw [← Real.rpow_add hxpos, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  have h1 : 1 ≤ ε * x ^ (1 - θ) := by
    have hmul := mul_le_mul_of_nonneg_left hkey hε.le
    rwa [mul_one_div, div_self (ne_of_gt hε)] at hmul
  calc x ^ θ = x ^ θ * 1 := (mul_one _).symm
    _ ≤ x ^ θ * (ε * x ^ (1 - θ)) := mul_le_mul_of_nonneg_left h1 hxθ.le
    _ = ε * (x ^ θ * x ^ (1 - θ)) := by ring
    _ = ε * x := by rw [hsplit]

/-- **The two power bounds of the descent numeric** (`2^{n₀} ≍ x^{0.1}`, `n₀ = ⌊log x/(10 log 2)⌋`).
For large `x`: `3^{n₀} ≤ x^{0.2}` and `3^{n₀}·x^{α³}/2^{1.9 n₀} ≤ x^{0.99}`.  The only transcendental
input is `log 3 / log 2 ≤ 8/5`, which is the clean rational fact `3^5 = 243 ≤ 256 = 2^8`. -/
theorem descent_pow_bounds :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (3 : ℝ) ^ (nZero x) ≤ x ^ (0.2 : ℝ) ∧
      (3 : ℝ) ^ (nZero x) * x ^ (alpha ^ 3) / (2 : ℝ) ^ (1.9 * (nZero x : ℝ)) ≤ x ^ (0.99 : ℝ) := by
  refine ⟨(2 : ℝ) ^ (30 : ℕ), by norm_num, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hxpos : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3_0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog : 5 * Real.log 3 ≤ 8 * Real.log 2 := by
    have h := Real.log_le_log (show (0 : ℝ) < (3 : ℝ) ^ (5 : ℕ) by positivity)
      (show (3 : ℝ) ^ (5 : ℕ) ≤ (2 : ℝ) ^ (8 : ℕ) by norm_num)
    rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith
  have hlog30 : (30 : ℝ) * Real.log 2 ≤ Real.log x := by
    rw [show (30 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (30 : ℕ)) by rw [Real.log_pow]; push_cast; ring]
    exact Real.log_le_log (by positivity) hx
  have harg : 0 ≤ Real.log x / (10 * Real.log 2) := by positivity
  have hν_le' : (nZero x : ℝ) * (10 * Real.log 2) ≤ Real.log x := by
    have h : (nZero x : ℝ) ≤ Real.log x / (10 * Real.log 2) := by
      unfold nZero; exact Nat.floor_le harg
    exact (le_div_iff₀ (by positivity)).mp h
  have hν_ge' : Real.log x < ((nZero x : ℝ) + 1) * (10 * Real.log 2) := by
    have h : Real.log x / (10 * Real.log 2) < (nZero x : ℝ) + 1 := by
      unfold nZero; exact Nat.lt_floor_add_one _
    exact (div_lt_iff₀ (by positivity)).mp h
  have hν0 : (0 : ℝ) ≤ (nZero x : ℝ) := Nat.cast_nonneg _
  have hprod2 : (0 : ℝ) ≤ (nZero x : ℝ) * (8 * Real.log 2 - 5 * Real.log 3) :=
    mul_nonneg hν0 (by linarith)
  refine ⟨?_, ?_⟩
  · -- 3^{n₀} ≤ x^{0.2}
    rw [← Real.rpow_natCast (3 : ℝ) (nZero x),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
        Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    nlinarith [hν_le', hprod2, hlog2, hL0]
  · -- 3^{n₀}·x^{α³}/2^{1.9 n₀} ≤ x^{0.99}
    have hα3 : alpha ^ 3 ≤ 1.01 := by unfold alpha; norm_num
    rw [← Real.rpow_natCast (3 : ℝ) (nZero x),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
        Real.rpow_def_of_pos hxpos (alpha ^ 3),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        Real.rpow_def_of_pos hxpos (0.99 : ℝ),
        ← Real.exp_add, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    nlinarith [hν_le', hν_ge', hprod2, hlog2, hL0, hlog30, hα3, hν0]

/-- **The descent step** (Tao pp.21, over (1.5)/(1.7)).  For `x` large and `N` in the support of the
log-uniform window (`N` odd, `y ≤ N ≤ y^α ≤ x^{α³}`), if the total valuation `valSum N n₀` exceeds
`1.9 n₀`, then `Syr^{n₀}(N) ≤ 3^{n₀} 2^{-1.9 n₀} x^{α³} + O(3^{n₀}) = O(x^{0.99}) ≤ x`, so `N` passes.
Uses `syr_descent_bound` (C2 core) + `descent_pow_bounds` (numeric) + `rpow_le_eps_mul_of_lt_one`. -/
theorem descent_passes :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
      ∀ N ∈ (logUnifOdd y (y ^ alpha)).support,
        1.9 * (nZero x : ℝ) < (valSum N (nZero x) : ℝ) → passes ⌊x⌋₊ N := by
  obtain ⟨xa, hxa1, hxa⟩ := rpow_le_eps_mul_of_lt_one (θ := (0.99 : ℝ)) (ε := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨xb, hxb1, hxb⟩ := rpow_le_eps_mul_of_lt_one (θ := (0.2 : ℝ)) (ε := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨xc, hxc1, hpow⟩ := descent_pow_bounds
  refine ⟨max (max xa xb) (max xc 2), fun x hx y hy N hNsupp hval => ?_⟩
  have hxa' : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb' : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc' : xc ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hone : ∀ z : ℝ, 0 ≤ z → (1 : ℝ) ≤ x ^ z := fun z hz => by
    calc (1 : ℝ) = 1 ^ z := (Real.one_rpow z).symm
      _ ≤ x ^ z := Real.rpow_le_rpow zero_le_one hx1 hz
  have haα : (0 : ℝ) ≤ alpha := by unfold alpha; norm_num
  have hyge1 : (1 : ℝ) ≤ y := by
    rcases hy with h | h <;> rw [h]
    · exact hone alpha haα
    · exact hone (alpha ^ 2) (by positivity)
  have hyα1 : (1 : ℝ) ≤ y ^ alpha := by
    calc (1 : ℝ) = 1 ^ alpha := (Real.one_rpow alpha).symm
      _ ≤ y ^ alpha := Real.rpow_le_rpow zero_le_one hyge1 haα
  obtain ⟨hodd, hNle⟩ := logUnifOdd_support_le hyα1 hNsupp
  have hNb : (N : ℝ) ≤ x ^ (alpha ^ 3) := by
    refine le_trans hNle ?_
    rcases hy with h | h
    · rw [h, ← Real.rpow_mul hxpos.le]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by unfold alpha; nlinarith)
    · rw [h, ← Real.rpow_mul hxpos.le]
      exact le_of_eq (by rw [show alpha ^ 2 * alpha = alpha ^ 3 by ring])
  -- descent bound cast to ℝ
  have h2v : (0 : ℝ) < 2 ^ (valSum N (nZero x)) := by positivity
  have hsdR : (2 : ℝ) ^ (valSum N (nZero x)) * (syr^[nZero x] N : ℝ)
      ≤ 3 ^ (nZero x) * (N : ℝ) + 2 ^ (valSum N (nZero x)) * 3 ^ (nZero x) := by
    exact_mod_cast syr_descent_bound N (nZero x) hodd
  have hsyr_le : (syr^[nZero x] N : ℝ)
      ≤ 3 ^ (nZero x) * (N : ℝ) / 2 ^ (valSum N (nZero x)) + 3 ^ (nZero x) := by
    have hrhs : (3 ^ (nZero x) * (N : ℝ) / 2 ^ (valSum N (nZero x)) + 3 ^ (nZero x))
          * 2 ^ (valSum N (nZero x))
        = 3 ^ (nZero x) * (N : ℝ) + 3 ^ (nZero x) * 2 ^ (valSum N (nZero x)) := by
      field_simp
    refine le_of_mul_le_mul_right ?_ h2v
    rw [hrhs]; nlinarith [hsdR]
  have h2vge : (2 : ℝ) ^ (1.9 * (nZero x : ℝ)) ≤ 2 ^ (valSum N (nZero x)) := by
    rw [← Real.rpow_natCast (2 : ℝ) (valSum N (nZero x))]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hval)
  have hfrac : 3 ^ (nZero x) * (N : ℝ) / 2 ^ (valSum N (nZero x))
      ≤ 3 ^ (nZero x) * x ^ (alpha ^ 3) / 2 ^ (1.9 * (nZero x : ℝ)) := by
    have hnumpos : (0 : ℝ) ≤ 3 ^ (nZero x) * x ^ (alpha ^ 3) := by positivity
    calc 3 ^ (nZero x) * (N : ℝ) / 2 ^ (valSum N (nZero x))
        ≤ 3 ^ (nZero x) * x ^ (alpha ^ 3) / 2 ^ (valSum N (nZero x)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNb (by positivity)) h2v.le
      _ ≤ 3 ^ (nZero x) * x ^ (alpha ^ 3) / 2 ^ (1.9 * (nZero x : ℝ)) :=
          div_le_div_of_nonneg_left hnumpos (by positivity) h2vge
  obtain ⟨hp1, hp2⟩ := hpow x hxc'
  have hsyr_final : (syr^[nZero x] N : ℝ) ≤ x ^ (0.99 : ℝ) + x ^ (0.2 : ℝ) := by
    calc (syr^[nZero x] N : ℝ)
        ≤ 3 ^ (nZero x) * (N : ℝ) / 2 ^ (valSum N (nZero x)) + 3 ^ (nZero x) := hsyr_le
      _ ≤ 3 ^ (nZero x) * x ^ (alpha ^ 3) / 2 ^ (1.9 * (nZero x : ℝ)) + 3 ^ (nZero x) :=
          add_le_add hfrac (le_refl _)
      _ ≤ x ^ (0.99 : ℝ) + x ^ (0.2 : ℝ) := add_le_add hp2 hp1
  have hxx : x ^ (0.99 : ℝ) + x ^ (0.2 : ℝ) ≤ x - 1 := by
    have ha := hxa x hxa'
    have hb := hxb x hxb'
    nlinarith [ha, hb, hx2]
  refine ⟨nZero x, ?_⟩
  have hsyrR : (syr^[nZero x] N : ℝ) ≤ x - 1 := le_trans hsyr_final hxx
  have hfloor : x - 1 < (⌊x⌋₊ : ℝ) := by have := Nat.lt_floor_add_one x; linarith
  exact_mod_cast (lt_of_le_of_lt hsyrR hfloor).le

-- RATIFY-C7: paper (1.19), §5 pp.20–21. Stated character-identically to the FIRST CONJUNCT of
-- `stabilization` below, which is where this content had been absorbed. Judge against p.20.
/-- **Paper (1.19)** — first-passage non-escape: a log-uniformly chosen odd `N_y` in the window
`[y, y^α]` fails ever to descend to `≤ x` with probability `≪ x^{-c}`.

This is node **C7**. It is stated here as its own theorem because Tao proves it separately
(§5 pp.20–21) and **C8's proof consumes it** — it had previously existed *only* as the first
conjunct of `stabilization`, i.e. absorbed into a downstream node's statement, which is precisely
how a blueprint node ends up owing a proof while naming no theorem of its own.
`stabilization` is WATCHED and is NOT touched; this sits beside it (always allowed).

**Route** (Tao pp.20–21). Every step but the first runs over already-proved machinery:
1. ⚠️ **The integral test** — `dTV(N_y mod 2^{n'}, unifOddMod n') ≪ 2^{-n'}` for the log-uniform
   window. **Not in Lean yet.** It is exactly the hypothesis Prop 1.9 (`valuation_dist`) takes,
   and it is the ONLY new analytic brick in this node. Tao: "a routine application of the
   integral test" (with plenty of room to spare).
2. Prop 1.9 (C5 ✅ axiom-clean) ⟹ `dTV(valVec N n₀, geomHalf.iid n₀) ≪ 2^{-c·n₀}`   — (5.4).
3. Lemma 2.2 (S3 ✅ axiom-clean; `geomHalf_tail_bound` is TWO-SIDED, so it covers this LOWER
   tail) ⟹ `P(|ā^{(n₀)}(N_y)| ≤ 1.9·n₀) ≪ 2^{-c·n₀} ≪ x^{-c}`   — (5.5).
4. Descent arithmetic: if `|ā^{(n₀)}| > 1.9·n₀` then by (1.5)/(1.7)
   `Syr^{n₀}(N_y) ≤ 3^{n₀}·2^{-1.9n₀}·x^{α³} + O(3^{n₀}) = O(x^{0.99}) ≤ x`, hence
   `T_x(N_y) ≤ n₀ < ∞`. Here `n₀ := ⌊log x / (10·log 2)⌋` (5.1), so `2^{n₀} ≍ x^{0.1}`.
-/
theorem first_passage_nonescape :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1)
          ≤ C * x ^ (-c) := by
  -- Assembly of the C7 route: {¬passes} ⊆ {valSum ≤ 1.9 n₀} (descent, contrapositive), and the
  -- latter has mass ≪ x^{-c} (the (5.5) lower tail).  Only the two named sub-lemmas carry content.
  obtain ⟨c, C, x₀t, hc, hC, htail⟩ := valSum_lower_tail
  obtain ⟨x₀d, hdesc⟩ := descent_passes
  refine ⟨c, C, max x₀t x₀d, hc, hC, ?_⟩
  intro x hx y hy
  have hxt : x₀t ≤ x := le_trans (le_max_left _ _) hx
  have hxd : x₀d ≤ x := le_trans (le_max_right _ _) hx
  have htail' := htail x hxt y hy
  have hsummable : ∀ (S : Set ℕ),
      Summable (fun N => ((logUnifOdd y (y ^ alpha)) N).toReal * Set.indicator S 1 N) := by
    intro S
    refine Summable.of_nonneg_of_le
      (fun N => mul_nonneg ENNReal.toReal_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) N))
      (fun N => ?_)
      (ENNReal.summable_toReal (logUnifOdd y (y ^ alpha)).tsum_coe_ne_top)
    have hind : Set.indicator S (1 : ℕ → ℝ) N ≤ 1 := by
      by_cases h : N ∈ S <;> simp [Set.indicator, h]
    calc ((logUnifOdd y (y ^ alpha)) N).toReal * Set.indicator S 1 N
        ≤ ((logUnifOdd y (y ^ alpha)) N).toReal * 1 :=
          mul_le_mul_of_nonneg_left hind ENNReal.toReal_nonneg
      _ = ((logUnifOdd y (y ^ alpha)) N).toReal := mul_one _
  refine le_trans ?_ htail'
  unfold PMF.expect
  refine Summable.tsum_le_tsum (fun N => ?_)
    (hsummable {N | ¬ passes ⌊x⌋₊ N})
    (hsummable {N | (valSum N (nZero x) : ℝ) ≤ 1.9 * (nZero x : ℝ)})
  by_cases hsupp : N ∈ (logUnifOdd y (y ^ alpha)).support
  · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    by_cases hp1 : ¬ passes ⌊x⌋₊ N
    · have hvle : (valSum N (nZero x) : ℝ) ≤ 1.9 * (nZero x : ℝ) := by
        by_contra hgt
        push_neg at hgt
        exact hp1 (hdesc x hxd y hy N hsupp hgt)
      rw [Set.indicator_of_mem (show N ∈ {N | ¬ passes ⌊x⌋₊ N} from hp1),
          Set.indicator_of_mem
            (show N ∈ {N | (valSum N (nZero x) : ℝ) ≤ 1.9 * (nZero x : ℝ)} from hvle)]
    · rw [Set.indicator_of_notMem
            (show N ∉ {N | ¬ passes ⌊x⌋₊ N} from not_not.mpr (not_not.mp hp1))]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) N
  · have h0 : (logUnifOdd y (y ^ alpha)) N = 0 := by
      rw [PMF.mem_support_iff] at hsupp; exact not_not.mp hsupp
    rw [h0]; simp

-- RATIFY-3: window endpoints spelled per the spec's guidance as `[x^α, x^{α²}]` and
-- `[x^{α²}, x^{α³}]` (using `alpha^2`, `alpha^3`), which the SKELETON-SPEC flagged as the
-- intended reading of its nested-pow shorthand. Judge against §5 pp.25–28.
/-- **Proposition 1.11** (stabilization): the passage-location law is stable across the
two nearby log-windows, and non-passage is rare. The spine's key input. -/
theorem stabilization :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      (∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1)
          ≤ C * x ^ (-c)) ∧
      PMF.dTV ((logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).map (passLoc ⌊x⌋₊))
              ((logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).map (passLoc ⌊x⌋₊))
        ≤ C * (Real.log x) ^ (-c) := by
  sorry

end TaoCollatz
