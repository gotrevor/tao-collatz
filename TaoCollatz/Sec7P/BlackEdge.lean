/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.FpLocation

/-!
# Uniform tilted black-edge estimates

This file starts the `Pascal(p)` generalization of the analytic inputs to Tao's
black-edge argument.  The first-passage Gaussian now has horizontal centre
`(p/2)s`, which moves over `[s/10, 3s/10]`.  The main result below is the
Gaussian-times-exponential tail estimate with that variable centre.  It is the
law-independent engine needed by both the vanishing-tilt MGF and the fixed-tilt
Chernoff bound.
-/

open scoped ENNReal

namespace TaoCollatz.Sec7P

/-- The uniform slope margin behind the tilted versions of Tao's Case 2 and
Case 3.  The rational bound `log 3 / log 2 ≤ 8/5` comes from `3^5 ≤ 2^8`;
therefore `p log₂ 3 ≤ 24/25 < 1` throughout the campaign window. -/
theorem slope_margin {p : ℝ} (hp1 : p ≤ 3 / 5) :
    p / 2 * Real.log 9 ≤ 24 / 25 * Real.log 2 ∧
      p / 2 * Real.log 9 < Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog : 5 * Real.log 3 ≤ 8 * Real.log 2 := by
    have h := Real.log_le_log (show (0 : ℝ) < (3 : ℝ) ^ (5 : ℕ) by positivity)
      (show (3 : ℝ) ^ (5 : ℕ) ≤ (2 : ℝ) ^ (8 : ℕ) by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hp3 : p * Real.log 3 ≤ (3 / 5 : ℝ) * Real.log 3 :=
    mul_le_mul_of_nonneg_right hp1 hlog3
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlog9]
  constructor
  · nlinarith
  · have : (24 / 25 : ℝ) * Real.log 2 < Real.log 2 := by nlinarith
    nlinarith

/-- Gaussian times a growing exponential, summed over columns to the right of
`m`, uniformly for every centre slope `0 ≤ r ≤ 3/10`.  This is the moving-centre
version of `TaoCollatz.gaussExp_col_tail`.

The thinner slope margin changes the convenient constants: the elementary
budget gives `1+s ≤ 200 (m+1-rs)` once `m ≥ 100`, so the Gaussian is reduced to
an exponential at rate `c²/200` (rather than the fixed-law `c²/20`). -/
theorem gaussExpP_col_tail {r c C' theta : ℝ}
    (_hr0 : 0 ≤ r) (hr1 : r ≤ 3 / 10) (hc : 0 < c) (hC' : 0 ≤ C')
    (htheta : theta ≤ min c (c ^ 2 / 200) / 2) (s m : ℕ) (hm : 100 ≤ m)
    (hbud : (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9) :
    Summable (fun j : ℕ => if m < j then
        Real.exp (theta * (j : ℝ)) *
          (C' * (TaoCollatz.Gweight (1 + (s : ℝ))
            (c * ((j : ℝ) - r * s)) / Real.sqrt (1 + (s : ℝ)))) else 0) ∧
    (∑' j : ℕ, if m < j then
        Real.exp (theta * (j : ℝ)) *
          (C' * (TaoCollatz.Gweight (1 + (s : ℝ))
            (c * ((j : ℝ) - r * s)) / Real.sqrt (1 + (s : ℝ)))) else 0)
      ≤ C' * Real.exp (theta * (r * s))
          * (Real.exp (-(c ^ 2 / 200 - theta) * (((m : ℝ) + 1) - r * s))
                / (1 - Real.exp (-(c ^ 2 / 200 - theta)))
           + Real.exp (-(c - theta) * (((m : ℝ) + 1) - r * s))
                / (1 - Real.exp (-(c - theta)))) := by
  set gamma2 : ℝ := c ^ 2 / 200 with hgamma2def
  have hgamma2 : (0 : ℝ) < gamma2 := by rw [hgamma2def]; positivity
  have htheta_gamma2 : theta ≤ gamma2 / 2 :=
    le_trans htheta (by
      apply div_le_div_of_nonneg_right (min_le_right _ _)
      norm_num)
  have htheta_c : theta ≤ c / 2 :=
    le_trans htheta (by
      apply div_le_div_of_nonneg_right (min_le_left _ _)
      norm_num)
  set a2 : ℝ := gamma2 - theta with ha2def
  set a1 : ℝ := c - theta with ha1def
  have ha2 : (0 : ℝ) < a2 := by rw [ha2def]; linarith
  have ha1 : (0 : ℝ) < a1 := by rw [ha1def]; linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog9 : Real.log 9 ≤ 16 / 5 * Real.log 2 := by
    have h := Real.log_le_log (show (0 : ℝ) < (9 : ℝ) ^ (5 : ℕ) by positivity)
      (show (9 : ℝ) ^ (5 : ℕ) ≤ (2 : ℝ) ^ (16 : ℕ) by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hsle : (s : ℝ) ≤ 16 / 5 * ((m : ℝ) + 2) := by
    have h1 : (s : ℝ) * Real.log 2 ≤
        (16 / 5 * ((m : ℝ) + 2)) * Real.log 2 := by
      calc
        (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 := hbud
        _ ≤ ((m : ℝ) + 2) * (16 / 5 * Real.log 2) :=
          mul_le_mul_of_nonneg_left hlog9 (by positivity)
        _ = (16 / 5 * ((m : ℝ) + 2)) * Real.log 2 := by ring
    exact le_of_mul_le_mul_right h1 hlog2
  set t : ℝ := 1 + (s : ℝ) with htdef
  have ht1 : (1 : ℝ) ≤ t := by rw [htdef]; linarith [Nat.cast_nonneg (α := ℝ) s]
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hm100 : (100 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set x0 : ℝ := (m : ℝ) + 1 - r * s with hx0def
  have hrs : r * (s : ℝ) ≤ 24 / 25 * ((m : ℝ) + 2) := by
    calc
      r * (s : ℝ) ≤ (3 / 10 : ℝ) * (s : ℝ) :=
        mul_le_mul_of_nonneg_right hr1 (Nat.cast_nonneg s)
      _ ≤ (3 / 10 : ℝ) * (16 / 5 * ((m : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hsle (by norm_num)
      _ = 24 / 25 * ((m : ℝ) + 2) := by ring
  have hx0lb : ((m : ℝ) - 23) / 25 ≤ x0 := by rw [hx0def]; linarith
  have hx0pos : (0 : ℝ) < x0 :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < ((m : ℝ) - 23) / 25) hx0lb
  have h200 : t ≤ 200 * x0 := by
    rw [htdef, hx0def]
    nlinarith
  have hE2 := TaoCollatz.hasSum_nat_tail_exp ha2 m (r * s)
  have hE1 := TaoCollatz.hasSum_nat_tail_exp ha1 m (r * s)
  set kappa : ℝ := C' * Real.exp (theta * (r * s)) with hkappadef
  have hkappa0 : (0 : ℝ) ≤ kappa := mul_nonneg hC' (Real.exp_pos _).le
  have hg : HasSum (fun j : ℕ => if m < j then
      kappa * (Real.exp (-a2 * ((j : ℝ) - r * s))
        + Real.exp (-a1 * ((j : ℝ) - r * s))) else 0)
      (kappa * (Real.exp (-a2 * (((m : ℝ) + 1) - r * s))
          / (1 - Real.exp (-a2))
        + Real.exp (-a1 * (((m : ℝ) + 1) - r * s))
          / (1 - Real.exp (-a1)))) := by
    have h := (hE2.add hE1).mul_left kappa
    have heq : (fun j : ℕ =>
        kappa * ((if m < j then Real.exp (-a2 * ((j : ℝ) - r * s)) else 0)
          + (if m < j then Real.exp (-a1 * ((j : ℝ) - r * s)) else 0))) =
        fun j : ℕ => if m < j then
          kappa * (Real.exp (-a2 * ((j : ℝ) - r * s))
            + Real.exp (-a1 * ((j : ℝ) - r * s))) else 0 := by
      funext j
      by_cases hj : m < j <;> simp [hj]
    exact heq ▸ h
  have hfg : ∀ j : ℕ,
      (if m < j then Real.exp (theta * (j : ℝ)) *
          (C' * (TaoCollatz.Gweight t (c * ((j : ℝ) - r * s)) /
            Real.sqrt t)) else 0) ≤
        (if m < j then kappa *
          (Real.exp (-a2 * ((j : ℝ) - r * s))
            + Real.exp (-a1 * ((j : ℝ) - r * s))) else 0) := by
    intro j
    by_cases hj : m < j
    · rw [if_pos hj, if_pos hj]
      set X : ℝ := (j : ℝ) - r * s with hX
      have hjm : (m : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj
      have hXx0 : x0 ≤ X := by rw [hX, hx0def]; linarith
      have hX0 : (0 : ℝ) < X := lt_of_lt_of_le hx0pos hXx0
      have hsq1 : (1 : ℝ) ≤ Real.sqrt t := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt ht1
      have hdiv : TaoCollatz.Gweight t (c * X) / Real.sqrt t ≤
          TaoCollatz.Gweight t (c * X) :=
        div_le_self (TaoCollatz.Gweight_nonneg _ _) hsq1
      have hGb : TaoCollatz.Gweight t (c * X) / Real.sqrt t ≤
          Real.exp (-gamma2 * X) + Real.exp (-c * X) := by
        refine hdiv.trans ?_
        unfold TaoCollatz.Gweight
        have habs : |c * X| = c * X := abs_of_nonneg (by positivity)
        have hkey : gamma2 * X * t ≤ (c * X) ^ 2 := by
          have h200X : t ≤ 200 * X := h200.trans (by nlinarith)
          have hfac : 0 ≤ c ^ 2 * X * (200 * X - t) :=
            mul_nonneg (mul_nonneg (sq_nonneg c) hX0.le) (by linarith)
          rw [hgamma2def]
          nlinarith [hfac]
        have hgauss : Real.exp (-((c * X) ^ 2) / t) ≤
            Real.exp (-gamma2 * X) := by
          apply Real.exp_le_exp.mpr
          have hge : gamma2 * X ≤ (c * X) ^ 2 / t := (le_div_iff₀ ht0).mpr hkey
          rw [show -((c * X) ^ 2) / t = -((c * X) ^ 2 / t) by ring, neg_mul]
          linarith
        have hexp2 : Real.exp (-|c * X|) ≤ Real.exp (-c * X) :=
          le_of_eq (by rw [habs, neg_mul])
        exact add_le_add hgauss hexp2
      have hfold2 : Real.exp (theta * (j : ℝ)) * Real.exp (-gamma2 * X) =
          Real.exp (theta * (r * s)) * Real.exp (-a2 * X) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        rw [ha2def, hX]
        ring
      have hfold1 : Real.exp (theta * (j : ℝ)) * Real.exp (-c * X) =
          Real.exp (theta * (r * s)) * Real.exp (-a1 * X) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        rw [ha1def, hX]
        ring
      calc
        Real.exp (theta * (j : ℝ)) *
              (C' * (TaoCollatz.Gweight t (c * X) / Real.sqrt t))
            ≤ Real.exp (theta * (j : ℝ)) *
                (C' * (Real.exp (-gamma2 * X) + Real.exp (-c * X))) := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_left hGb hC'
        _ = kappa * (Real.exp (-a2 * X) + Real.exp (-a1 * X)) := by
              rw [hkappadef]
              have hexpand : Real.exp (theta * (j : ℝ)) *
                  (C' * (Real.exp (-gamma2 * X) + Real.exp (-c * X))) =
                  C' * (Real.exp (theta * (j : ℝ)) * Real.exp (-gamma2 * X)
                    + Real.exp (theta * (j : ℝ)) * Real.exp (-c * X)) := by ring
              rw [hexpand, hfold2, hfold1]
              ring
    · rw [if_neg hj, if_neg hj]
  have hfnn : ∀ j : ℕ, 0 ≤ (if m < j then Real.exp (theta * (j : ℝ)) *
      (C' * (TaoCollatz.Gweight t (c * ((j : ℝ) - r * s)) / Real.sqrt t)) else 0) := by
    intro j
    by_cases hj : m < j
    · rw [if_pos hj]
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg hC' (div_nonneg (TaoCollatz.Gweight_nonneg _ _) (Real.sqrt_nonneg _)))
    · rw [if_neg hj]
  have hsummf : Summable (fun j : ℕ => if m < j then
      Real.exp (theta * (j : ℝ)) *
        (C' * (TaoCollatz.Gweight t (c * ((j : ℝ) - r * s)) / Real.sqrt t)) else 0) :=
    Summable.of_nonneg_of_le hfnn hfg hg.summable
  refine ⟨hsummf, ?_⟩
  calc
    (∑' j : ℕ, if m < j then Real.exp (theta * (j : ℝ)) *
        (C' * (TaoCollatz.Gweight t (c * ((j : ℝ) - r * s)) / Real.sqrt t)) else 0)
        ≤ ∑' j : ℕ, if m < j then kappa *
            (Real.exp (-a2 * ((j : ℝ) - r * s))
              + Real.exp (-a1 * ((j : ℝ) - r * s))) else 0 :=
      hsummf.tsum_le_tsum hfg hg.summable
    _ = kappa * (Real.exp (-a2 * (((m : ℝ) + 1) - r * s)) / (1 - Real.exp (-a2))
        + Real.exp (-a1 * (((m : ℝ) + 1) - r * s)) / (1 - Real.exp (-a1))) :=
      hg.tsum_eq

/-- Fubini envelope for the first-coordinate MGF of any probability law with
the moving-centre column bound supplied by tilted Lemma 7.7.  The bulk uses
only total mass one; the tail uses `gaussExpP_col_tail`. -/
theorem fst_mgf_moving_center_general (F : PMF (ℕ × ℤ)) {r c C' : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 3 / 10) (hc : 0 < c) (hC' : 0 < C') (s : ℕ)
    (hcol : ∀ j : ℕ, ∑' l : ℤ, (F (j, l)).toReal ≤
      C' * (TaoCollatz.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - r * s)) /
        Real.sqrt (1 + (s : ℝ))))
    {theta : ℝ} (htheta0 : 0 ≤ theta)
    (hthetale : theta ≤ min c (c ^ 2 / 200) / 2) (K : ℕ) (hK100 : 100 ≤ K)
    (hbud : (s : ℝ) * Real.log 2 ≤ ((K : ℝ) + 2) * Real.log 9) :
    Summable (fun e : ℕ × ℤ => (F e).toReal * Real.exp (theta * (e.1 : ℝ))) ∧
      ∑' e : ℕ × ℤ, (F e).toReal * Real.exp (theta * (e.1 : ℝ)) ≤
        Real.exp (theta * (K : ℝ))
          + C' * Real.exp (theta * (r * s))
            * (Real.exp (-(c ^ 2 / 200 - theta) * (((K : ℝ) + 1) - r * s)) /
                  (1 - Real.exp (-(c ^ 2 / 200 - theta)))
              + Real.exp (-(c - theta) * (((K : ℝ) + 1) - r * s)) /
                  (1 - Real.exp (-(c - theta)))) := by
  set f : ℕ × ℤ → ℝ := fun e => (F e).toReal * Real.exp (theta * (e.1 : ℝ)) with hfdef
  set M : ℕ → ℝ := fun j => ∑' l : ℤ, (F (j, l)).toReal with hMdef
  have hMnn : ∀ j : ℕ, 0 ≤ M j := fun j => tsum_nonneg fun _ => ENNReal.toReal_nonneg
  have hF2d : Summable (fun e : ℕ × ℤ => (F e).toReal) :=
    ENNReal.summable_toReal (by rw [F.tsum_coe]; exact ENNReal.one_ne_top)
  have hFcol : ∀ j : ℕ, Summable (fun l : ℤ => (F (j, l)).toReal) :=
    fun j => hF2d.comp_injective (fun _ _ h => by simpa using h)
  have hfcol : ∀ j : ℕ, Summable (fun l : ℤ => f (j, l)) := by
    intro j
    simp only [hfdef]
    exact (hFcol j).mul_right _
  have hg_eq : ∀ j : ℕ, (∑' l : ℤ, f (j, l)) = M j * Real.exp (theta * (j : ℝ)) := by
    intro j
    have hcongr : ∀ l : ℤ,
        f (j, l) = (F (j, l)).toReal * Real.exp (theta * (j : ℝ)) :=
      fun _ => by simp only [hfdef]
    rw [tsum_congr hcongr, tsum_mul_right, hMdef]
  have hgnn : ∀ j : ℕ, 0 ≤ ∑' l : ℤ, f (j, l) :=
    fun j => tsum_nonneg fun l =>
      mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  set U : ℕ → ℝ := fun j =>
    (if j ≤ K then Real.exp (theta * (K : ℝ)) * M j else 0)
      + (if K < j then Real.exp (theta * (j : ℝ)) *
          (C' * (TaoCollatz.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - r * s)) /
            Real.sqrt (1 + (s : ℝ)))) else 0) with hUdef
  obtain ⟨hsumT, hleT⟩ :=
    gaussExpP_col_tail hr0 hr1 hc hC'.le hthetale s K hK100 hbud
  have hbulksum : Summable
      (fun j : ℕ => if j ≤ K then Real.exp (theta * (K : ℝ)) * M j else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range (K + 1)) (fun j hj => ?_)
    have hnle : ¬ j ≤ K := by simp only [Finset.mem_range, not_lt] at hj; omega
    rw [if_neg hnle]
  have hUsum : Summable U := hbulksum.add hsumT
  have hgU : ∀ j : ℕ, (∑' l : ℤ, f (j, l)) ≤ U j := by
    intro j
    rw [hg_eq j]
    simp only [hUdef]
    by_cases hjK : j ≤ K
    · rw [if_pos hjK, if_neg (by omega : ¬ K < j), add_zero]
      have hle : Real.exp (theta * (j : ℝ)) ≤ Real.exp (theta * (K : ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjK) htheta0
      calc
        M j * Real.exp (theta * (j : ℝ)) ≤ M j * Real.exp (theta * (K : ℝ)) :=
          mul_le_mul_of_nonneg_left hle (hMnn j)
        _ = Real.exp (theta * (K : ℝ)) * M j := mul_comm _ _
    · rw [if_neg hjK, if_pos (by omega : K < j), zero_add]
      have hMenv : M j ≤ C' *
          (TaoCollatz.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - r * s)) /
            Real.sqrt (1 + (s : ℝ))) := by
        rw [hMdef]
        exact hcol j
      calc
        M j * Real.exp (theta * (j : ℝ)) = Real.exp (theta * (j : ℝ)) * M j :=
          mul_comm _ _
        _ ≤ Real.exp (theta * (j : ℝ)) *
            (C' * (TaoCollatz.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - r * s)) /
              Real.sqrt (1 + (s : ℝ)))) :=
          mul_le_mul_of_nonneg_left hMenv (Real.exp_pos _).le
  have hfsum : Summable f :=
    (summable_prod_of_nonneg
      (fun e => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)).mpr
        ⟨hfcol, Summable.of_nonneg_of_le hgnn hgU hUsum⟩
  refine ⟨hfsum, ?_⟩
  rw [Summable.tsum_prod' hfsum hfcol]
  have hMsum : Summable M :=
    ((summable_prod_of_nonneg (fun _ => ENNReal.toReal_nonneg)).mp hF2d).2
  have hmassM : ∑' j : ℕ, M j = 1 := by
    have hFmass : ∑' e : ℕ × ℤ, (F e).toReal = 1 := by
      rw [← ENNReal.tsum_toReal_eq (fun e => F.apply_ne_top e), F.tsum_coe,
        ENNReal.toReal_one]
    simp only [hMdef]
    rw [← Summable.tsum_prod' hF2d hFcol, hFmass]
  have hindsum : Summable (fun j : ℕ => if j ≤ K then M j else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range (K + 1)) (fun j hj => ?_)
    have hnle : ¬ j ≤ K := by simp only [Finset.mem_range, not_lt] at hj; omega
    rw [if_neg hnle]
  have hindptw : ∀ j : ℕ, (if j ≤ K then M j else 0) ≤ M j := by
    intro j
    by_cases h : j ≤ K
    · rw [if_pos h]
    · rw [if_neg h]
      exact hMnn j
  have hindle : (∑' j : ℕ, if j ≤ K then M j else 0) ≤ ∑' j : ℕ, M j :=
    Summable.tsum_le_tsum hindptw hindsum hMsum
  calc
    (∑' j : ℕ, ∑' l : ℤ, f (j, l)) ≤ ∑' j : ℕ, U j :=
      Summable.tsum_le_tsum hgU (Summable.of_nonneg_of_le hgnn hgU hUsum) hUsum
    _ = (∑' j : ℕ, if j ≤ K then Real.exp (theta * (K : ℝ)) * M j else 0)
        + ∑' j : ℕ, if K < j then Real.exp (theta * (j : ℝ)) *
            (C' * (TaoCollatz.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - r * s)) /
              Real.sqrt (1 + (s : ℝ)))) else 0 := by
      simp only [hUdef]
      exact hbulksum.tsum_add hsumT
    _ ≤ Real.exp (theta * (K : ℝ))
        + C' * Real.exp (theta * (r * s))
          * (Real.exp (-(c ^ 2 / 200 - theta) * (((K : ℝ) + 1) - r * s)) /
                (1 - Real.exp (-(c ^ 2 / 200 - theta)))
            + Real.exp (-(c - theta) * (((K : ℝ) + 1) - r * s)) /
                (1 - Real.exp (-(c - theta)))) := by
      refine add_le_add ?_ hleT
      have hb1 : (fun j : ℕ => if j ≤ K then
          Real.exp (theta * (K : ℝ)) * M j else 0) =
          fun j : ℕ => Real.exp (theta * (K : ℝ)) *
            (if j ≤ K then M j else 0) := by
        funext j
        by_cases hjK : j ≤ K <;> simp [hjK]
      rw [hb1, tsum_mul_left]
      have hstep : (∑' j : ℕ, if j ≤ K then M j else 0) ≤ 1 := by
        rw [← hmassM]
        exact hindle
      calc
        Real.exp (theta * (K : ℝ)) * (∑' j : ℕ, if j ≤ K then M j else 0) ≤
            Real.exp (theta * (K : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
        _ = Real.exp (theta * (K : ℝ)) := mul_one _

/-- The MGF envelope specialized to `fpDistP p`, with all constants uniform on
the campaign window and the exact moving centre `(p/2)s`. -/
theorem fpDistP_fst_mgf_general (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    {theta : ℝ} (htheta0 : 0 ≤ theta)
    (hthetale : theta ≤ min c_fpLocationP (c_fpLocationP ^ 2 / 200) / 2)
    (s K : ℕ) (hK100 : 100 ≤ K)
    (hbud : (s : ℝ) * Real.log 2 ≤ ((K : ℝ) + 2) * Real.log 9) :
    Summable (fun e : ℕ × ℤ =>
      (fpDistP p (by linarith) (by linarith) s e).toReal *
        Real.exp (theta * (e.1 : ℝ))) ∧
      ∑' e : ℕ × ℤ, (fpDistP p (by linarith) (by linarith) s e).toReal *
          Real.exp (theta * (e.1 : ℝ)) ≤
        Real.exp (theta * (K : ℝ))
          + C_fpColP * Real.exp (theta * (p / 2 * s))
            * (Real.exp (-(c_fpLocationP ^ 2 / 200 - theta) *
                  (((K : ℝ) + 1) - p / 2 * s)) /
                (1 - Real.exp (-(c_fpLocationP ^ 2 / 200 - theta)))
              + Real.exp (-(c_fpLocationP - theta) *
                  (((K : ℝ) + 1) - p / 2 * s)) /
                (1 - Real.exp (-(c_fpLocationP - theta)))) := by
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  exact fst_mgf_moving_center_general
    (fpDistP p hp0' hp1' s)
    (r := p / 2) (c := c_fpLocationP) (C' := C_fpColP)
    (by linarith) (by linarith) c_fpLocationP_pos C_fpColP_pos s
    (fun j => fpDistP_col_le_explicitC p hp0' hp1' hp0 hp1 s j)
    htheta0 hthetale K hK100 hbud

end TaoCollatz.Sec7P
