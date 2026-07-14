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

/-- **Odd-support of the reduced window** — a structural brick of the `intTest_error` dTV reduction.
The pushforward of `logUnifOdd lo hi` under reduction mod `2^{n'}` (`n' ≥ 1`) puts mass `0` on every
EVEN residue: all `N` in the window are odd, and `Nat.cast` to `ZMod (2^{n'})` preserves the low bit
(`(↑N).val % 2 = N % 2`). Hence the dTV against `unifOddMod` collapses to a sum over odd residues.

Note the `.map`-of-a-coercion elaborates (via coercion lifting) to a DOUBLE map `id ∘ cast`, so we
first collapse the identity outer map (`PMF.map_id`) and force the `PMF.map` head (`show`) before
`PMF.map_apply` — otherwise the apply lemmas mis-unify with the identity map (index over `ZMod`). -/
theorem logUnifOdd_map_even_zero {lo hi : ℝ} (hhi : 1 ≤ hi) {n' : ℕ} (hn' : 0 < n')
    (r : ZMod (2 ^ n')) (hr : r.val % 2 = 0) :
    ((logUnifOdd lo hi).map fun N => (N : ZMod (2 ^ n'))) r = 0 := by
  rw [show (fun N : ZMod (2 ^ n') => N) = id from rfl, PMF.map_id]
  show (PMF.map (fun N : ℕ => (N : ZMod (2 ^ n'))) (logUnifOdd lo hi)) r = 0
  rw [PMF.map_apply, ENNReal.tsum_eq_zero]
  intro N
  split_ifs with hcond
  · by_contra hne
    have hsupp : N ∈ (logUnifOdd lo hi).support := hne
    have hodd : N % 2 = 1 := (logUnifOdd_support_le hhi hsupp).1
    have hval : ((N : ℕ) : ZMod (2 ^ n')).val % 2 = 1 := by
      rw [ZMod.val_natCast, Nat.mod_mod_of_dvd N (dvd_pow_self 2 hn'.ne')]; exact hodd
    have hr1 : r.val % 2 = 1 := by rw [hcond]; exact hval
    omega
  · rfl

/-- **Numeric closure for the integral test.**  For `x ≥ 1` and `y ∈ {x^α, x^{α²}}`, the modulus
`2^{3n₀}` (`n₀ = ⌊log x / (10 log 2)⌋`, so `2^{n₀} ≍ x^{0.1}`) gives `2^{3n₀} / y ≤ 2^{-3n₀}`, i.e. the
integral-test error `O(2^{n'}/y)` is `≤ 2^{-n'}`, with room to spare (`2^{6n₀} ≤ x^{0.6} ≤ x^{1.001} ≤ y`).
Mirrors `descent_pow_bounds`; the only transcendental input is `6 n₀ log 2 ≤ 0.6 log x` from
`n₀ · 10 log 2 ≤ log x`. -/
theorem intTest_numeric :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
      (2 : ℝ) ^ (3 * (nZero x : ℝ)) / y ≤ (2 : ℝ) ^ (-(3 * (nZero x : ℝ))) := by
  refine ⟨1, le_refl _, fun x hx1 y hy => ?_⟩
  have hxpos : (0 : ℝ) < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : 0 ≤ Real.log x / (10 * Real.log 2) := by positivity
  have hν_le : (nZero x : ℝ) * (10 * Real.log 2) ≤ Real.log x := by
    have h : (nZero x : ℝ) ≤ Real.log x / (10 * Real.log 2) := by
      unfold nZero; exact Nat.floor_le harg
    exact (le_div_iff₀ (by positivity)).mp h
  have h6le : (2 : ℝ) ^ (6 * (nZero x : ℝ)) ≤ x ^ (0.6 : ℝ) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    nlinarith [hν_le, hlog2, hL0]
  have hy6 : x ^ (0.6 : ℝ) ≤ y := by
    rcases hy with h | h <;> rw [h] <;>
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by unfold alpha; norm_num)
  have h6y : (2 : ℝ) ^ (6 * (nZero x : ℝ)) ≤ y := le_trans h6le hy6
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) h6y
  rw [div_le_iff₀ hypos]
  have hsplit : (2 : ℝ) ^ (-(3 * (nZero x : ℝ))) * (2 : ℝ) ^ (6 * (nZero x : ℝ))
      = (2 : ℝ) ^ (3 * (nZero x : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
  calc (2 : ℝ) ^ (3 * (nZero x : ℝ))
      = (2 : ℝ) ^ (-(3 * (nZero x : ℝ))) * (2 : ℝ) ^ (6 * (nZero x : ℝ)) := hsplit.symm
    _ ≤ (2 : ℝ) ^ (-(3 * (nZero x : ℝ))) * y :=
        mul_le_mul_of_nonneg_left h6y (Real.rpow_nonneg (by norm_num) _)

/-- **L¹ normalization / telescope lemma** — the pure real-analysis core of the integral-test dTV
reduction.  Let `O` be a finite index set (the odd residues mod `M`), `s r ≥ 0` the raw class masses
`S_r = ∑_{N≡r} 1/N`, and `D = ∑_{r∈O} s r > 0` their total.  If every class mass is within `ε` of a
COMMON target `t` (this is exactly what the per-class integral test supplies: `|S_r − L/M| ≤ ε`), then
the L¹ distance between the normalized law `s r / D` and the UNIFORM law `1/|O|` on `O` is
`≤ 2 ε |O| / D`.

This is the step that turns per-class deviations into a total-variation bound: the shared target `t`
cancels in the average, so `|s r/D − 1/|O|| = |s r − D/|O||/D` with `|s r − D/|O|| ≤ 2ε` (triangle:
`ε` from `|s r − t|` and `ε` from `|D/|O| − t| = |avg deviation| ≤ ε`).  It needs neither the value of
`t` nor the nonnegativity of `s` — only `D = ∑ s` and `D > 0`. -/
theorem l1_normalize_telescope {ι : Type*} (O : Finset ι) (s : ι → ℝ) (D t ε : ℝ)
    (hDpos : 0 < D) (hD : D = ∑ r ∈ O, s r)
    (hdev : ∀ r ∈ O, |s r - t| ≤ ε) :
    ∑ r ∈ O, |s r / D - ((O.card : ℝ))⁻¹| ≤ 2 * ε * (O.card : ℝ) / D := by
  by_cases hcard : O.card = 0
  · rw [Finset.card_eq_zero] at hcard
    simp [hcard]
  set c : ℝ := (O.card : ℝ) with hc
  have hc0 : 0 < c := by rw [hc]; exact_mod_cast Nat.pos_of_ne_zero hcard
  -- the average `D/c` is within `ε` of the shared target `t`
  have hDavg : |D / c - t| ≤ ε := by
    have heq : D / c - t = (∑ r ∈ O, (s r - t)) / c := by
      rw [hD, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hc]
      field_simp
    rw [heq, abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
    calc |∑ r ∈ O, (s r - t)| ≤ ∑ r ∈ O, |s r - t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ O, ε := Finset.sum_le_sum hdev
      _ = ε * c := by rw [Finset.sum_const, nsmul_eq_mul, ← hc]; ring
  -- each class mass is within `2ε` of the average
  have hterm : ∀ r ∈ O, |s r - D / c| ≤ 2 * ε := by
    intro r hr
    calc |s r - D / c| ≤ |s r - t| + |t - D / c| := _root_.abs_sub_le _ _ _
      _ ≤ ε + ε := add_le_add (hdev r hr) (by rw [abs_sub_comm]; exact hDavg)
      _ = 2 * ε := by ring
  -- rewrite each normalized deviation and sum
  have hrw : ∀ r ∈ O, |s r / D - c⁻¹| = |s r - D / c| / D := by
    intro r _
    rw [show s r / D - c⁻¹ = (s r - D / c) / D by field_simp, abs_div, abs_of_pos hDpos]
  rw [Finset.sum_congr rfl hrw, ← Finset.sum_div, div_le_div_iff_of_pos_right hDpos]
  calc ∑ r ∈ O, |s r - D / c| ≤ ∑ _r ∈ O, 2 * ε := Finset.sum_le_sum hterm
    _ = 2 * ε * c := by rw [Finset.sum_const, nsmul_eq_mul, ← hc]; ring

/-- Raw class mass `S_r := ∑_{N ∈ W, N ≡ r (mod 2^{n'})} 1/N` for the log-uniform window
`W = logWindow lo hi`.  The pushforward of `logUnifOdd` mod `2^{n'}` puts real mass `S_r / D` on
residue `r`, where `D = windowMass`. -/
noncomputable def classMass (lo hi : ℝ) (n' : ℕ) (r : ZMod (2 ^ n')) : ℝ :=
  ∑ N ∈ (logWindow lo hi).filter (fun N : ℕ => (N : ZMod (2 ^ n')) = r), (N : ℝ)⁻¹

/-- Total window mass `D := ∑_{N ∈ W} 1/N` (the log-uniform normalizer, in ℝ). -/
noncomputable def windowMass (lo hi : ℝ) : ℝ := ∑ N ∈ logWindow lo hi, (N : ℝ)⁻¹

/-- Apply lemma for `logUnifOdd` in the nonempty-window case: mass `∝ 1/N` on the window. -/
theorem logUnifOdd_apply_of_nonempty {lo hi : ℝ} (h : (logWindow lo hi).Nonempty) (N : ℕ) :
    logUnifOdd lo hi N
      = if N ∈ logWindow lo hi then
          (N : ℝ≥0∞)⁻¹ / (∑ M ∈ logWindow lo hi, (M : ℝ≥0∞)⁻¹) else 0 := by
  unfold logUnifOdd
  rw [dif_pos h, PMF.ofFinset_apply]

/-- **Pushforward-mass identity** — the class mass glue of the integral-test dTV reduction.  In the
nonempty-window case the reduction `logUnifOdd lo hi` mod `2^{n'}` puts real mass `S_r / D` on residue
`r` (`S_r = classMass`, `D = windowMass`).  This is what lets `l1_normalize_telescope` consume the
per-class masses. -/
theorem map_res_apply_toReal {lo hi : ℝ} (h : (logWindow lo hi).Nonempty) {n' : ℕ}
    (r : ZMod (2 ^ n')) :
    (((logUnifOdd lo hi).map fun N => (N : ZMod (2 ^ n'))) r).toReal
      = classMass lo hi n' r / windowMass lo hi := by
  -- odd ⇒ every window element is nonzero (needed for `toReal` of `(N)⁻¹`)
  have hne : ∀ N ∈ logWindow lo hi, (N : ℝ≥0∞) ≠ 0 := by
    intro N hN
    simp only [logWindow, Finset.mem_filter] at hN
    have : N % 2 = 1 := hN.2.1
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  -- ENNReal pushforward value: `S_r^{en} / D^{en}`
  have hmap : ((logUnifOdd lo hi).map fun N => (N : ZMod (2 ^ n'))) r
      = (∑ N ∈ (logWindow lo hi).filter (fun N : ℕ => (N : ZMod (2 ^ n')) = r), (N : ℝ≥0∞)⁻¹)
          / (∑ M ∈ logWindow lo hi, (M : ℝ≥0∞)⁻¹) := by
    rw [show (fun N : ZMod (2 ^ n') => N) = id from rfl, PMF.map_id]
    show (PMF.map (fun N : ℕ => (N : ZMod (2 ^ n'))) (logUnifOdd lo hi)) r = _
    rw [PMF.map_apply]
    rw [tsum_eq_sum (s := logWindow lo hi) (fun N hN => by
      rw [logUnifOdd_apply_of_nonempty h, if_neg hN]; split_ifs <;> rfl)]
    -- ENNReal has no `sum_div`; push the normalizer as `* D⁻¹` instead.
    rw [Finset.sum_filter, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [logUnifOdd_apply_of_nonempty h, if_pos hN]
    by_cases hc : (N : ZMod (2 ^ n')) = r
    · rw [if_pos hc.symm, if_pos hc, div_eq_mul_inv]
    · rw [if_neg (fun hh => hc hh.symm), if_neg hc, zero_mul]
  rw [hmap, ENNReal.toReal_div]
  congr 1
  · rw [ENNReal.toReal_sum fun N hN => by
      rw [ne_eq, ENNReal.inv_eq_top, Nat.cast_eq_zero]
      exact fun h0 => hne N (Finset.mem_of_mem_filter N hN) (by simp [h0])]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · rw [ENNReal.toReal_sum fun M hM => by
      rw [ne_eq, ENNReal.inv_eq_top, Nat.cast_eq_zero]
      exact fun h0 => hne M hM (by simp [h0])]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- Casting an odd `N` to `ZMod (2^{n'})` (`n' ≥ 1`) preserves the low bit. -/
theorem cast_val_odd {n' : ℕ} (hn' : 0 < n') {N : ℕ} (hN : N % 2 = 1) :
    ((N : ZMod (2 ^ n')).val) % 2 = 1 := by
  rw [ZMod.val_natCast, Nat.mod_mod_of_dvd N (dvd_pow_self 2 hn'.ne')]; exact hN

/-- **Partition identity**: summing the class masses over the odd residues recovers the total window
mass `D`.  Every window element is odd, so its reduction lands in an odd residue class, and the odd
residues partition the window (`Finset.sum_fiberwise_of_maps_to`). -/
theorem windowMass_eq_sum_classMass {lo hi : ℝ} {n' : ℕ} (hn' : 0 < n') :
    windowMass lo hi
      = ∑ r ∈ Finset.univ.filter (fun r : ZMod (2 ^ n') => r.val % 2 = 1),
          classMass lo hi n' r := by
  classical
  haveI : NeZero (2 ^ n') := ⟨by positivity⟩
  unfold windowMass classMass
  refine (Finset.sum_fiberwise_of_maps_to (fun N hN => ?_) _).symm
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, cast_val_odd hn' ?_⟩
  simp only [logWindow, Finset.mem_filter] at hN
  exact hN.2.1

/-- **The dTV even/odd split** — assembles the integral-test reduction.  Given a per-class deviation
bound `|S_r − t| ≤ ε` uniform over the odd residues (this is what `intTest_class_dev` supplies via the
integral test), the total-variation distance of the reduced log-uniform window from `unifOddMod`
telescopes to `2 ε · 2^{n'−1} / D`.  Even residues carry no mass on either side, so the sum collapses
to the odd residues, where `l1_normalize_telescope` finishes. -/
theorem intTest_dTV_le {lo hi : ℝ} (hhi : 1 ≤ hi) (hne : (logWindow lo hi).Nonempty)
    {n' : ℕ} (hn' : 0 < n') {t ε : ℝ} (hDpos : 0 < windowMass lo hi)
    (hdev : ∀ r : ZMod (2 ^ n'), r.val % 2 = 1 → |classMass lo hi n' r - t| ≤ ε) :
    PMF.dTV ((logUnifOdd lo hi).map fun N => (N : ZMod (2 ^ n'))) (unifOddMod n')
      ≤ 2 * ε * ((2 ^ (n' - 1) : ℕ) : ℝ) / windowMass lo hi := by
  classical
  haveI : NeZero (2 ^ n') := ⟨by positivity⟩
  set O : Finset (ZMod (2 ^ n')) := Finset.univ.filter (fun r => r.val % 2 = 1) with hOdef
  have hcard : O.card = 2 ^ (n' - 1) := card_odd_zmod_two_pow n' hn'
  -- the uniform mass on an odd residue in `ℝ`
  have hu : ((2 ^ (n' - 1) : ℝ≥0∞)⁻¹).toReal = (O.card : ℝ)⁻¹ := by
    rw [hcard, ENNReal.toReal_inv, ENNReal.toReal_pow]
    norm_num
  -- Step 1: dTV collapses to the odd residues
  have hdtv : PMF.dTV ((logUnifOdd lo hi).map fun N => (N : ZMod (2 ^ n'))) (unifOddMod n')
      = ∑ r ∈ O, |classMass lo hi n' r / windowMass lo hi - (O.card : ℝ)⁻¹| := by
    unfold PMF.dTV
    rw [tsum_fintype,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : ZMod (2 ^ n') => r.val % 2 = 1),
      ← hOdef]
    have heven : ∑ r ∈ Finset.univ.filter (fun r : ZMod (2 ^ n') => ¬ r.val % 2 = 1),
        |(((logUnifOdd lo hi).map fun N => (N : ZMod (2 ^ n'))) r).toReal
          - (unifOddMod n' r).toReal| = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [Finset.mem_filter] at hr
      have hre : r.val % 2 = 0 := by omega
      rw [logUnifOdd_map_even_zero hhi hn' r hre, unifOddMod_apply_of_pos n' hn' r, if_neg (by omega)]
      simp
    rw [heven, add_zero]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_filter] at hr
    rw [map_res_apply_toReal hne r, unifOddMod_apply_of_pos n' hn' r, if_pos hr.2, hu]
  rw [hdtv]
  calc ∑ r ∈ O, |classMass lo hi n' r / windowMass lo hi - (O.card : ℝ)⁻¹|
      ≤ 2 * ε * (O.card : ℝ) / windowMass lo hi :=
        l1_normalize_telescope O (classMass lo hi n') (windowMass lo hi) t ε hDpos
          (windowMass_eq_sum_classMass hn') (fun r hr => hdev r ((Finset.mem_filter.mp hr).2))
    _ = 2 * ε * ((2 ^ (n' - 1) : ℕ) : ℝ) / windowMass lo hi := by rw [hcard]

/-- **The integral-test error estimate** — the analytic heart of C7, and the ONE remaining new brick.
For the log-uniform odd window `N_y ∈ [y, y^α]`, the total-variation distance of its reduction mod
`2^{3n₀}` from the uniform law on odd residues is `≪ 2^{3n₀}/y` (the raw integral-test error, before the
numeric closure `intTest_numeric` converts `2^{3n₀}/y` to `≤ 2^{-3n₀}`).

**Proof owed** (the elementary integral test — NOT dynamical equidistribution, which mathlib lacks; this
uses machinery mathlib HAS). Route (see `PENDING_WORK` "C7 integral test — attack plan"):
* `PMF.map_apply` ⟹ the pushforward mass on residue `r` is `S_r/D`, `S_r := ∑_{N≡r} 1/N`, `D := ∑_{N∈W} 1/N`;
  all `N∈W` odd ⇒ supported on odd residues, so `dTV = (1/D) ∑_{r odd} |S_r − 2D/M|` (`M := 2^{3n₀}`);
* per odd class, `S_r = (1/M)·log(y^α/y) + O(1/y)` via `AntitoneOn.sum_le_integral` /
  `AntitoneOn.integral_le_sum` on `t ↦ 1/t` over the AP (step `M`) + `integral_inv` (`∫ 1/t = log`), and
  `D = ½·log(y^α/y) + O(1/y)` likewise (odds are half); AP counts via `Nat.Ioc_filter_modEq_card`;
* summing the `M/2` odd classes and dividing by `D ≥ c·log y` gives `dTV ≤ C·M/y = C·2^{3n₀}/y`. -/
theorem intTest_error :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        PMF.dTV ((logUnifOdd y (y ^ alpha)).map fun N => (N : ZMod (2 ^ (3 * nZero x))))
                (unifOddMod (3 * nZero x))
          ≤ K * ((2 : ℝ) ^ (3 * (nZero x : ℝ)) / y) := by
  sorry

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
  -- Assembled from the analytic error estimate `intTest_error` (dTV ≤ K·2^{3n₀}/y) and the numeric
  -- closure `intTest_numeric` (2^{3n₀}/y ≤ 2^{-3n₀}).  Only `intTest_error` carries owed content.
  obtain ⟨K, hK, x₀e, herr⟩ := intTest_error
  obtain ⟨x₀n, _, hnum⟩ := intTest_numeric
  refine ⟨K, hK, max x₀e x₀n, fun x hx y hy => ?_⟩
  have hxe : x₀e ≤ x := le_trans (le_max_left _ _) hx
  have hxn : x₀n ≤ x := le_trans (le_max_right _ _) hx
  exact le_trans (herr x hxe y hy) (mul_le_mul_of_nonneg_left (hnum x hxn y hy) hK.le)

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
