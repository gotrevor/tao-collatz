/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.FpLocation
import TaoCollatz.Sec7.BlackEdge

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

-- HEARTBEAT: this is the full real-inequality package for the moving-centre
-- split; nested exponential denominators make normalization expensive.
set_option maxHeartbeats 4000000 in
/-- Uniform numeric core for the vanishing-tilt first-coordinate MGF.  The
threshold is chosen before the centre slope `r`; throughout `0 ≤ r ≤ 3/10`,
the split point `K = ⌊m log(1+δ/2)/(2A)⌋` puts the moving centre `rs` at most
halfway to `K`.  This is the tilted analogue of
`TaoCollatz.fpDist_fst_mgf_numeric`, with Gaussian rate `c²/200`. -/
theorem fpDistP_fst_mgf_numeric {A δ c C' : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (hc : 0 < c) (hC' : 0 < C') :
    ∃ Cthr : ℕ, 100 ≤ Cthr ∧ ∀ m : ℕ, Cthr ≤ m →
      ∀ r : ℝ, 0 ≤ r → r ≤ 3 / 10 → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∃ K : ℕ, 100 ≤ K ∧
        2 * A / (m : ℝ) ≤ min c (c ^ 2 / 200) / 2 ∧
        (s : ℝ) * Real.log 2 ≤ ((K : ℝ) + 2) * Real.log 9 ∧
        Real.exp (2 * A / (m : ℝ) * (K : ℝ)) ≤ 1 + δ / 2 ∧
        C' * Real.exp (2 * A / (m : ℝ) * (r * s))
          * (Real.exp (-(c ^ 2 / 200 - 2 * A / (m : ℝ)) *
                (((K : ℝ) + 1) - r * s)) /
                (1 - Real.exp (-(c ^ 2 / 200 - 2 * A / (m : ℝ))))
             + Real.exp (-(c - 2 * A / (m : ℝ)) *
                (((K : ℝ) + 1) - r * s)) /
                (1 - Real.exp (-(c - 2 * A / (m : ℝ))))) ≤ δ / 2 := by
  set μ : ℝ := min c (c ^ 2 / 200) / 2 with hμdef
  have hμ : 0 < μ := by
    rw [hμdef]
    have : 0 < min c (c ^ 2 / 200) := lt_min hc (by positivity)
    linarith
  have hμc : μ ≤ c / 2 := by
    rw [hμdef]
    gcongr
    exact min_le_left _ _
  have hμc2 : μ ≤ c ^ 2 / 400 := by
    rw [hμdef]
    have : min c (c ^ 2 / 200) ≤ c ^ 2 / 200 := min_le_right _ _
    linarith
  set L : ℝ := Real.log (1 + δ / 2) with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  set d₂ : ℝ := 1 - Real.exp (-(c ^ 2 / 400)) with hd2def
  set d₁ : ℝ := 1 - Real.exp (-(c / 2)) with hd1def
  have hd2 : 0 < d₂ := by
    rw [hd2def]
    have : Real.exp (-(c ^ 2 / 400)) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [sq_pos_of_pos hc]
    linarith
  have hd1 : 0 < d₁ := by
    rw [hd1def]
    have : Real.exp (-(c / 2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  set ρ : ℝ := min (c ^ 2 / 400) (c / 2) * L / (4 * A) with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    have : 0 < min (c ^ 2 / 400) (c / 2) :=
      lt_min (by positivity) (by positivity)
    positivity
  set Q : ℝ := C' * Real.exp A * (1 / d₂ + 1 / d₁) with hQdef
  have hQ : 0 < Q := by rw [hQdef]; positivity
  obtain ⟨N85, hN85⟩ := TaoCollatz.log_sq_ge_of_large
    (max (max (2 * A * Real.log 2 / (L * Real.log 9)) (2 * A / L)) 1)
  obtain ⟨N4, hN4⟩ := TaoCollatz.exp_neg_mul_le_of_large
    ρ hρ (δ / (2 * Q)) (by positivity)
  set N1 : ℕ := ⌈2 * A / μ⌉₊ with hN1def
  set N3 : ℕ := ⌈200 * A / L⌉₊ with hN3def
  refine ⟨100 + N1 + N3 + N85 + N4, by omega, ?_⟩
  intro m hm r hr0 hr1 s hs
  have hm100 : 100 ≤ m := by omega
  have hmN1 : N1 ≤ m := by omega
  have hmN3 : N3 ≤ m := by omega
  have hmN85 : N85 ≤ m := by omega
  have hmN4 : N4 ≤ m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (by omega : 0 < m)
  set θ : ℝ := 2 * A / (m : ℝ) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθnn : 0 ≤ θ := hθpos.le
  have hlogm_pos : 0 < Real.log m :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlogsq_pos : 0 < Real.log m ^ 2 := by positivity
  have hlogsq := hN85 m hmN85
  have hb3 : 2 * A * Real.log 2 / (L * Real.log 9) ≤ Real.log m ^ 2 :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlogsq
  have hb4 : 2 * A / L ≤ Real.log m ^ 2 :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlogsq
  have hb1 : (1 : ℝ) ≤ Real.log m ^ 2 := le_trans (le_max_right _ _) hlogsq
  have hθμ : θ ≤ μ := by
    rw [hθdef, div_le_iff₀ hmpos]
    have hm1 : (2 * A / μ) ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hmN1)
    have : 2 * A = μ * (2 * A / μ) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hm1 hμ.le
  set κ : ℝ := (m : ℝ) * L / (2 * A) with hκdef
  have hκnn : 0 ≤ κ := by rw [hκdef]; positivity
  set K : ℕ := ⌊κ⌋₊ with hKdef
  have hKle : (K : ℝ) ≤ κ := Nat.floor_le hκnn
  have hKlb : κ - 1 ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one κ
    rw [← hKdef] at this
    linarith
  refine ⟨K, ?_, hθμ, ?_, ?_, ?_⟩
  · rw [hKdef]
    apply Nat.le_floor
    have hm200 : (200 * A / L) ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hmN3)
    have hmL : 200 * A ≤ (m : ℝ) * L := by
      have h := mul_le_mul_of_nonneg_right hm200 hL.le
      rwa [div_mul_cancel₀ _ hL.ne'] at h
    rw [hκdef, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * A)]
    push_cast
    linarith
  · have hb3' : 2 * A * Real.log 2 ≤ Real.log m ^ 2 * (L * Real.log 9) := by
      rw [div_le_iff₀ (by positivity)] at hb3
      linarith
    have hstep1 : (s : ℝ) * Real.log 2 ≤
        ((m : ℝ) / Real.log m ^ 2) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hs hlog2.le
    have hstep2 : ((m : ℝ) / Real.log m ^ 2) * Real.log 2 ≤ κ * Real.log 9 := by
      rw [hκdef,
        show ((m : ℝ) / Real.log m ^ 2) * Real.log 2 =
          ((m : ℝ) * Real.log 2) / Real.log m ^ 2 by ring,
        show ((m : ℝ) * L / (2 * A)) * Real.log 9 =
          ((m : ℝ) * L * Real.log 9) / (2 * A) by ring,
        div_le_div_iff₀ hlogsq_pos (by positivity : (0 : ℝ) < 2 * A)]
      nlinarith [mul_le_mul_of_nonneg_left hb3' hmpos.le]
    have hstep3 : κ * Real.log 9 ≤ ((K : ℝ) + 2) * Real.log 9 :=
      mul_le_mul_of_nonneg_right (by linarith) hlog9.le
    linarith
  · have hθK : θ * (K : ℝ) ≤ L := by
      have h1 : θ * (K : ℝ) ≤ θ * κ := mul_le_mul_of_nonneg_left hKle hθnn
      have h2 : θ * κ = L := by rw [hθdef, hκdef]; field_simp
      linarith
    calc
      Real.exp (θ * (K : ℝ)) ≤ Real.exp L := Real.exp_le_exp.mpr hθK
      _ = 1 + δ / 2 := by rw [hLdef]; exact Real.exp_log (by linarith)
  · set x₀ : ℝ := ((K : ℝ) + 1) - r * s with hx0def
    have hrs : r * (s : ℝ) ≤ (3 / 10 : ℝ) * ((m : ℝ) / Real.log m ^ 2) := by
      calc
        r * (s : ℝ) ≤ (3 / 10 : ℝ) * (s : ℝ) :=
          mul_le_mul_of_nonneg_right hr1 (Nat.cast_nonneg s)
        _ ≤ (3 / 10 : ℝ) * ((m : ℝ) / Real.log m ^ 2) :=
          mul_le_mul_of_nonneg_left hs (by norm_num)
    have hAL : 2 * A ≤ L * Real.log m ^ 2 := by
      rw [div_le_iff₀ hL] at hb4
      linarith
    have hsmall : (3 / 10 : ℝ) * ((m : ℝ) / Real.log m ^ 2) ≤
        (m : ℝ) * L / (4 * A) := by
      have hfrac : (3 / 10 : ℝ) / Real.log m ^ 2 ≤ L / (4 * A) := by
        rw [div_le_div_iff₀ hlogsq_pos (by positivity : (0 : ℝ) < 4 * A)]
        nlinarith
      calc
        (3 / 10 : ℝ) * ((m : ℝ) / Real.log m ^ 2) =
            (m : ℝ) * ((3 / 10 : ℝ) / Real.log m ^ 2) := by ring
        _ ≤ (m : ℝ) * (L / (4 * A)) :=
          mul_le_mul_of_nonneg_left hfrac hmpos.le
        _ = (m : ℝ) * L / (4 * A) := by ring
    have hrs' : r * (s : ℝ) ≤ (m : ℝ) * L / (4 * A) := hrs.trans hsmall
    have hx0lb : (m : ℝ) * L / (4 * A) ≤ x₀ := by
      rw [hx0def]
      have hx1 : κ ≤ (K : ℝ) + 1 := by linarith
      have hκval : κ = (m : ℝ) * L / (2 * A) := hκdef
      have hhalf : κ - (m : ℝ) * L / (4 * A) =
          (m : ℝ) * L / (4 * A) := by rw [hκval]; ring
      linarith
    have hx0pos : 0 < x₀ := lt_of_lt_of_le (by positivity) hx0lb
    have ha2 : c ^ 2 / 400 ≤ c ^ 2 / 200 - θ := by
      linarith [hθμ, hμc2]
    have ha1 : c / 2 ≤ c - θ := by linarith [hθμ, hμc]
    have ha2pos : 0 < c ^ 2 / 200 - θ := lt_of_lt_of_le (by positivity) ha2
    have ha1pos : 0 < c - θ := lt_of_lt_of_le (by positivity) ha1
    have hpre : Real.exp (θ * (r * s)) ≤ Real.exp A := by
      apply Real.exp_le_exp.mpr
      have hθrs : θ * (r * s) ≤ θ *
          ((3 / 10 : ℝ) * ((m : ℝ) / Real.log m ^ 2)) :=
        mul_le_mul_of_nonneg_left hrs hθnn
      have heq : θ * ((3 / 10 : ℝ) * ((m : ℝ) / Real.log m ^ 2)) =
          (3 * A) / (5 * Real.log m ^ 2) := by
        rw [hθdef]
        field_simp
        ring
      have hratio : (3 * A) / (5 * Real.log m ^ 2) ≤ A := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 5 * Real.log m ^ 2)]
        nlinarith
      linarith [hθrs, hratio]
    have hden2 : 1 / (1 - Real.exp (-(c ^ 2 / 200 - θ))) ≤ 1 / d₂ := by
      apply one_div_le_one_div_of_le hd2
      rw [hd2def]
      have : Real.exp (-(c ^ 2 / 200 - θ)) ≤ Real.exp (-(c ^ 2 / 400)) :=
        Real.exp_le_exp.mpr (by linarith [ha2])
      linarith
    have hden1 : 1 / (1 - Real.exp (-(c - θ))) ≤ 1 / d₁ := by
      apply one_div_le_one_div_of_le hd1
      rw [hd1def]
      have : Real.exp (-(c - θ)) ≤ Real.exp (-(c / 2)) :=
        Real.exp_le_exp.mpr (by linarith [ha1])
      linarith
    have hden2pos : 0 < 1 - Real.exp (-(c ^ 2 / 200 - θ)) := by
      have : Real.exp (-(c ^ 2 / 200 - θ)) < 1 := by
        rw [Real.exp_lt_one_iff]
        linarith [ha2pos]
      linarith
    have hden1pos : 0 < 1 - Real.exp (-(c - θ)) := by
      have : Real.exp (-(c - θ)) < 1 := by
        rw [Real.exp_lt_one_iff]
        linarith [ha1pos]
      linarith
    have hnum2 : Real.exp (-(c ^ 2 / 200 - θ) * x₀) ≤ Real.exp (-ρ * m) := by
      apply Real.exp_le_exp.mpr
      have hrate : ρ ≤ (c ^ 2 / 400) * L / (4 * A) := by
        rw [hρdef]
        gcongr
        exact min_le_left _ _
      have hprod : ρ * (m : ℝ) ≤ (c ^ 2 / 200 - θ) * x₀ := by
        calc
          ρ * (m : ℝ) ≤ (c ^ 2 / 400) * L / (4 * A) * (m : ℝ) :=
            mul_le_mul_of_nonneg_right hrate hmpos.le
          _ = (c ^ 2 / 400) * ((m : ℝ) * L / (4 * A)) := by ring
          _ ≤ (c ^ 2 / 200 - θ) * x₀ :=
            mul_le_mul ha2 hx0lb (by positivity) ha2pos.le
      nlinarith [hprod]
    have hnum1 : Real.exp (-(c - θ) * x₀) ≤ Real.exp (-ρ * m) := by
      apply Real.exp_le_exp.mpr
      have hrate : ρ ≤ (c / 2) * L / (4 * A) := by
        rw [hρdef]
        gcongr
        exact min_le_right _ _
      have hprod : ρ * (m : ℝ) ≤ (c - θ) * x₀ := by
        calc
          ρ * (m : ℝ) ≤ (c / 2) * L / (4 * A) * (m : ℝ) :=
            mul_le_mul_of_nonneg_right hrate hmpos.le
          _ = (c / 2) * ((m : ℝ) * L / (4 * A)) := by ring
          _ ≤ (c - θ) * x₀ := mul_le_mul ha1 hx0lb (by positivity) ha1pos.le
      nlinarith [hprod]
    have hterm2 : Real.exp (-(c ^ 2 / 200 - θ) * x₀) /
        (1 - Real.exp (-(c ^ 2 / 200 - θ))) ≤ Real.exp (-ρ * m) * (1 / d₂) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hnum2 hden2 (one_div_nonneg.mpr hden2pos.le) (Real.exp_pos _).le
    have hterm1 : Real.exp (-(c - θ) * x₀) / (1 - Real.exp (-(c - θ))) ≤
        Real.exp (-ρ * m) * (1 / d₁) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hnum1 hden1 (one_div_nonneg.mpr hden1pos.le) (Real.exp_pos _).le
    have hsum : Real.exp (-(c ^ 2 / 200 - θ) * x₀) /
          (1 - Real.exp (-(c ^ 2 / 200 - θ)))
        + Real.exp (-(c - θ) * x₀) / (1 - Real.exp (-(c - θ))) ≤
          Real.exp (-ρ * m) * (1 / d₂ + 1 / d₁) := by
      have := add_le_add hterm2 hterm1
      rw [mul_add]
      linarith
    have hsumnn : 0 ≤ Real.exp (-(c ^ 2 / 200 - θ) * x₀) /
          (1 - Real.exp (-(c ^ 2 / 200 - θ)))
        + Real.exp (-(c - θ) * x₀) / (1 - Real.exp (-(c - θ))) :=
      add_nonneg (div_nonneg (Real.exp_pos _).le hden2pos.le)
        (div_nonneg (Real.exp_pos _).le hden1pos.le)
    have hfinal : C' * Real.exp (θ * (r * s))
          * (Real.exp (-(c ^ 2 / 200 - θ) * x₀) /
                (1 - Real.exp (-(c ^ 2 / 200 - θ)))
             + Real.exp (-(c - θ) * x₀) / (1 - Real.exp (-(c - θ)))) ≤
        Q * Real.exp (-ρ * m) := by
      have h1 : C' * Real.exp (θ * (r * s)) ≤ C' * Real.exp A :=
        mul_le_mul_of_nonneg_left hpre hC'.le
      calc
        C' * Real.exp (θ * (r * s))
              * (Real.exp (-(c ^ 2 / 200 - θ) * x₀) /
                    (1 - Real.exp (-(c ^ 2 / 200 - θ)))
                 + Real.exp (-(c - θ) * x₀) / (1 - Real.exp (-(c - θ))))
            ≤ C' * Real.exp A * (Real.exp (-ρ * m) * (1 / d₂ + 1 / d₁)) :=
              mul_le_mul h1 hsum hsumnn (by positivity)
        _ = Q * Real.exp (-ρ * m) := by rw [hQdef]; ring
    have hlast : Q * Real.exp (-ρ * m) ≤ δ / 2 := by
      have h := hN4 m hmN4
      calc
        Q * Real.exp (-ρ * m) ≤ Q * (δ / (2 * Q)) :=
          mul_le_mul_of_nonneg_left h hQ.le
        _ = δ / 2 := by field_simp
    exact le_trans hfinal hlast

/-- The first-coordinate MGF of the tilted first-passage law converges to one
at the vanishing tilt `2A/m`, uniformly in `p ∈ [1/5,3/5]`.  Crucially, the
threshold is selected before `p`. -/
theorem fpDistP_fst_mgf_le (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ p : ℝ, ∀ hp0 : 1 / 5 ≤ p, ∀ hp1 : p ≤ 3 / 5,
      ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e).toReal *
          Real.exp (2 * A * (e.1 : ℝ) / (m : ℝ)) ≤ 1 + δ := by
  obtain ⟨Cthr, hCthr100, hnum⟩ :=
    fpDistP_fst_mgf_numeric hA hδ c_fpLocationP_pos C_fpColP_pos
  refine ⟨Cthr, ?_⟩
  intro p hp0 hp1 m hm s hs
  obtain ⟨K, hK100, hθle, hbud, hbulk, htail⟩ :=
    hnum m hm (p / 2) (by linarith) (by linarith) s hs
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 100) (hCthr100.trans hm)
  have hθ0 : (0 : ℝ) ≤ 2 * A / (m : ℝ) := by positivity
  have hexp : ∀ e : ℕ × ℤ,
      2 * A * (e.1 : ℝ) / (m : ℝ) = 2 * A / (m : ℝ) * (e.1 : ℝ) :=
    fun _ => by ring
  simp_rw [hexp]
  exact le_trans
    (fpDistP_fst_mgf_general p hp0 hp1 hθ0 hθle s K hK100 hbud).2
    (le_trans (add_le_add hbulk htail) (le_of_eq (by ring)))

-- HEARTBEAT: the fixed-tilt Chernoff proof combines the moving-centre MGF
-- envelope, a pointwise tail comparison, and exponential-versus-polynomial
-- closeout; the nested exponentials make normalization expensive.
set_option maxHeartbeats 2000000 in
/-- Uniform fixed-tilt right tail for the first coordinate of `fpDistP`.
Under the Case-2 budget, `P(e₁ > m/4) ≤ δ m⁻ᴬ`, with one threshold chosen
before `p`.  The cutoff `K = ⌊m/log²m⌋ + 100` accommodates the moving centre
`(p/2)s` and the weaker Gaussian rate `c_fpLocationP²/200`. -/
theorem fpDistP_fst_tail_le (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ p : ℝ, ∀ hp0 : 1 / 5 ≤ p, ∀ hp1 : p ≤ 3 / 5,
      ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e).toReal *
          (if m < 4 * e.1 then (1 : ℝ) else 0) ≤ δ * (m : ℝ) ^ (-A) := by
  set c : ℝ := c_fpLocationP with hcdef
  set C' : ℝ := C_fpColP with hC'def
  have hc : 0 < c := by simpa [hcdef] using c_fpLocationP_pos
  have hC'pos : 0 < C' := by simpa [hC'def] using C_fpColP_pos
  set θ₀ : ℝ := min c (c ^ 2 / 200) / 2 with hθ₀def
  have hθ₀pos : 0 < θ₀ := by
    rw [hθ₀def]
    have : 0 < min c (c ^ 2 / 200) := lt_min hc (by positivity)
    linarith
  have hθ₀nn : 0 ≤ θ₀ := hθ₀pos.le
  have hθ₀le : θ₀ ≤ min c (c ^ 2 / 200) / 2 := le_refl _
  have hθ₀c : θ₀ ≤ c / 2 := by
    rw [hθ₀def]
    gcongr
    exact min_le_left _ _
  have hθ₀c2 : θ₀ ≤ c ^ 2 / 400 := by
    rw [hθ₀def]
    have : min c (c ^ 2 / 200) ≤ c ^ 2 / 200 := min_le_right _ _
    linarith
  have hcsq : (0 : ℝ) < c ^ 2 := by positivity
  have ha2pos : 0 < c ^ 2 / 200 - θ₀ := by nlinarith [hθ₀c2, hcsq]
  have ha1pos : 0 < c - θ₀ := by linarith [hθ₀c]
  set d₂ : ℝ := 1 - Real.exp (-(c ^ 2 / 200 - θ₀)) with hd2def
  set d₁ : ℝ := 1 - Real.exp (-(c - θ₀)) with hd1def
  have hd2 : 0 < d₂ := by
    rw [hd2def]
    have : Real.exp (-(c ^ 2 / 200 - θ₀)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hd1 : 0 < d₁ := by
    rw [hd1def]
    have : Real.exp (-(c - θ₀)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  set B : ℝ := 1 + C' * (1 / d₂ + 1 / d₁) with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]
    have : 0 < C' * (1 / d₂ + 1 / d₁) := by positivity
    linarith
  obtain ⟨Nlog, hNlog⟩ := TaoCollatz.log_le_eps_mul_of_large
    (θ₀ / (16 * A)) (by positivity)
  obtain ⟨Nexp, hNexp⟩ := TaoCollatz.exp_neg_mul_le_of_large
    (θ₀ / 16) (by positivity) (δ / B) (by positivity)
  obtain ⟨N16, hN16⟩ := TaoCollatz.log_sq_ge_of_large 16
  refine ⟨1600 + Nlog + Nexp + N16, ?_⟩
  intro p hp0 hp1 m hm s hs
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  have hm1600 : 1600 ≤ m := by omega
  have hmNlog : Nlog ≤ m := by omega
  have hmNexp : Nexp ≤ m := by omega
  have hmN16 : N16 ≤ m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (by omega : 0 < m)
  have hm1 : 1 < m := by omega
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm1)
  have hlogsq_pos : 0 < Real.log m ^ 2 := by positivity
  have hlog16 : (16 : ℝ) ≤ Real.log m ^ 2 := hN16 m hmN16
  set κ : ℝ := (m : ℝ) / Real.log m ^ 2 with hκdef
  have hκnn : 0 ≤ κ := by rw [hκdef]; positivity
  have hsκ : (s : ℝ) ≤ κ := hs
  set K : ℕ := ⌊κ⌋₊ + 100 with hKdef
  have hK100 : 100 ≤ K := by omega
  have hKle : (K : ℝ) ≤ κ + 100 := by
    rw [hKdef]
    push_cast
    linarith [Nat.floor_le hκnn]
  have hKlb : κ + 99 ≤ (K : ℝ) := by
    rw [hKdef]
    push_cast
    linarith [Nat.lt_floor_add_one κ]
  have hr0 : (0 : ℝ) ≤ p / 2 := by linarith
  have hr1 : p / 2 ≤ (3 / 10 : ℝ) := by linarith
  have hrsκ : p / 2 * (s : ℝ) ≤ κ := by
    calc
      p / 2 * (s : ℝ) ≤ (3 / 10 : ℝ) * (s : ℝ) :=
        mul_le_mul_of_nonneg_right hr1 (Nat.cast_nonneg s)
      _ ≤ (3 / 10 : ℝ) * κ := mul_le_mul_of_nonneg_left hsκ (by norm_num)
      _ ≤ κ := by nlinarith
  have hrsK : p / 2 * (s : ℝ) ≤ (K : ℝ) := by linarith [hrsκ, hKlb]
  have hKx0 : 0 ≤ (K : ℝ) + 1 - p / 2 * (s : ℝ) := by linarith
  have hbud : (s : ℝ) * Real.log 2 ≤ ((K : ℝ) + 2) * Real.log 9 := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hlog9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
    have hlog29 : Real.log 2 ≤ Real.log 9 :=
      Real.log_le_log (by norm_num) (by norm_num)
    calc
      (s : ℝ) * Real.log 2 ≤ κ * Real.log 2 :=
        mul_le_mul_of_nonneg_right hsκ hlog2.le
      _ ≤ κ * Real.log 9 := mul_le_mul_of_nonneg_left hlog29 hκnn
      _ ≤ ((K : ℝ) + 2) * Real.log 9 :=
        mul_le_mul_of_nonneg_right (by linarith [hKlb]) hlog9.le
  have hKupper : (K : ℝ) ≤ (m : ℝ) / 8 := by
    have h1 : κ ≤ (m : ℝ) / 16 := by
      rw [hκdef, div_le_div_iff₀ hlogsq_pos (by norm_num)]
      nlinarith [hlog16, hmpos.le]
    have h2 : (100 : ℝ) ≤ (m : ℝ) / 16 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast hm1600
    linarith [hKle, h1, h2]
  have hKm4 : (K : ℝ) - (m : ℝ) / 4 ≤ -((m : ℝ) / 8) := by
    linarith [hKupper]
  obtain ⟨hZsum, hZle⟩ := fpDistP_fst_mgf_general p hp0 hp1 hθ₀nn hθ₀le
    s K hK100 hbud
  have hZB : ∑' e : ℕ × ℤ,
      (fpDistP p hp0' hp1' s e).toReal * Real.exp (θ₀ * (e.1 : ℝ)) ≤
        B * Real.exp (θ₀ * (K : ℝ)) := by
    refine le_trans hZle ?_
    have hE2 : Real.exp (-(c ^ 2 / 200 - θ₀) *
        (((K : ℝ) + 1) - p / 2 * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [ha2pos, hKx0]
    have hE1 : Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - p / 2 * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [ha1pos, hKx0]
    have hpre : Real.exp (θ₀ * (p / 2 * s)) ≤ Real.exp (θ₀ * (K : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrsK hθ₀nn)
    have hterm2 : Real.exp (-(c ^ 2 / 200 - θ₀) *
          (((K : ℝ) + 1) - p / 2 * s)) / d₂ ≤ 1 / d₂ := by
      rw [div_le_div_iff₀ hd2 hd2]
      nlinarith [hE2, hd2.le]
    have hterm1 : Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - p / 2 * s)) / d₁ ≤
        1 / d₁ := by
      rw [div_le_div_iff₀ hd1 hd1]
      nlinarith [hE1, hd1.le]
    have hgaussle : C' * Real.exp (θ₀ * (p / 2 * s))
          * (Real.exp (-(c ^ 2 / 200 - θ₀) *
                (((K : ℝ) + 1) - p / 2 * s)) /
                (1 - Real.exp (-(c ^ 2 / 200 - θ₀)))
             + Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - p / 2 * s)) /
                (1 - Real.exp (-(c - θ₀)))) ≤
        C' * Real.exp (θ₀ * (K : ℝ)) * (1 / d₂ + 1 / d₁) := by
      rw [← hd2def, ← hd1def]
      have hinner : Real.exp (-(c ^ 2 / 200 - θ₀) *
            (((K : ℝ) + 1) - p / 2 * s)) / d₂
          + Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - p / 2 * s)) / d₁ ≤
            1 / d₂ + 1 / d₁ := add_le_add hterm2 hterm1
      have hcoef : 0 ≤ C' * Real.exp (θ₀ * (p / 2 * s)) := by positivity
      calc
        C' * Real.exp (θ₀ * (p / 2 * s))
              * (Real.exp (-(c ^ 2 / 200 - θ₀) *
                    (((K : ℝ) + 1) - p / 2 * s)) / d₂
                 + Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - p / 2 * s)) / d₁)
            ≤ C' * Real.exp (θ₀ * (p / 2 * s)) * (1 / d₂ + 1 / d₁) :=
              mul_le_mul_of_nonneg_left hinner hcoef
        _ ≤ C' * Real.exp (θ₀ * (K : ℝ)) * (1 / d₂ + 1 / d₁) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hpre hC'pos.le
    calc
      Real.exp (θ₀ * (K : ℝ))
            + C' * Real.exp (θ₀ * (p / 2 * s))
              * (Real.exp (-(c ^ 2 / 200 - θ₀) *
                    (((K : ℝ) + 1) - p / 2 * s)) /
                    (1 - Real.exp (-(c ^ 2 / 200 - θ₀)))
                 + Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - p / 2 * s)) /
                    (1 - Real.exp (-(c - θ₀))))
          ≤ Real.exp (θ₀ * (K : ℝ))
              + C' * Real.exp (θ₀ * (K : ℝ)) * (1 / d₂ + 1 / d₁) :=
            add_le_add (le_refl _) hgaussle
      _ = B * Real.exp (θ₀ * (K : ℝ)) := by rw [hBdef]; ring
  have hfp2d : Summable (fun e : ℕ × ℤ => (fpDistP p hp0' hp1' s e).toReal) :=
    ENNReal.summable_toReal (by
      rw [(fpDistP p hp0' hp1' s).tsum_coe]
      exact ENNReal.one_ne_top)
  have hLHSsum : Summable (fun e : ℕ × ℤ =>
      (fpDistP p hp0' hp1' s e).toReal *
        (if m < 4 * e.1 then (1 : ℝ) else 0)) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hfp2d
    · positivity
    · by_cases h : m < 4 * e.1
      · rw [if_pos h, mul_one]
      · rw [if_neg h, mul_zero]
        exact ENNReal.toReal_nonneg
  have hcher : ∑' e : ℕ × ℤ, (fpDistP p hp0' hp1' s e).toReal *
        (if m < 4 * e.1 then (1 : ℝ) else 0) ≤
      Real.exp (-θ₀ * (m : ℝ) / 4) *
        ∑' e : ℕ × ℤ, (fpDistP p hp0' hp1' s e).toReal *
          Real.exp (θ₀ * (e.1 : ℝ)) := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun e => ?_) hLHSsum (hZsum.mul_left _)
    by_cases hcond : m < 4 * e.1
    · rw [if_pos hcond, mul_one]
      have h4 : (m : ℝ) < 4 * (e.1 : ℝ) := by exact_mod_cast hcond
      have hexp1 : (1 : ℝ) ≤
          Real.exp (θ₀ * (e.1 : ℝ) - θ₀ * (m : ℝ) / 4) := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [hθ₀nn, h4]
      calc
        (fpDistP p hp0' hp1' s e).toReal =
            (fpDistP p hp0' hp1' s e).toReal * 1 := (mul_one _).symm
        _ ≤ (fpDistP p hp0' hp1' s e).toReal *
              Real.exp (θ₀ * (e.1 : ℝ) - θ₀ * (m : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left hexp1 ENNReal.toReal_nonneg
        _ = Real.exp (-θ₀ * (m : ℝ) / 4) *
              ((fpDistP p hp0' hp1' s e).toReal * Real.exp (θ₀ * (e.1 : ℝ))) := by
            rw [show θ₀ * (e.1 : ℝ) - θ₀ * (m : ℝ) / 4 =
              θ₀ * (e.1 : ℝ) + (-θ₀ * (m : ℝ) / 4) by ring, Real.exp_add]
            ring
    · rw [if_neg hcond, mul_zero]
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
  have hAlog : A * Real.log m ≤ θ₀ * (m : ℝ) / 16 := by
    have h := hNlog m hmNlog
    have h2 : A * Real.log m ≤ A * (θ₀ / (16 * A) * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left h hA.le
    have h3 : A * (θ₀ / (16 * A) * (m : ℝ)) = θ₀ * (m : ℝ) / 16 := by
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hfin : B * Real.exp (-θ₀ * (m : ℝ) / 8) ≤ δ * (m : ℝ) ^ (-A) := by
    rw [Real.rpow_neg hmpos.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos hmpos A), Real.rpow_def_of_pos hmpos A,
      mul_assoc, ← Real.exp_add]
    have hexparg : -θ₀ * (m : ℝ) / 8 + Real.log m * A ≤
        -(θ₀ / 16) * (m : ℝ) := by
      nlinarith [hAlog]
    calc
      B * Real.exp (-θ₀ * (m : ℝ) / 8 + Real.log m * A) ≤
          B * Real.exp (-(θ₀ / 16) * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexparg) hBpos.le
      _ ≤ B * (δ / B) := mul_le_mul_of_nonneg_left (hNexp m hmNexp) hBpos.le
      _ = δ := by field_simp
  calc
    ∑' e : ℕ × ℤ, (fpDistP p hp0' hp1' s e).toReal *
          (if m < 4 * e.1 then (1 : ℝ) else 0) ≤
        Real.exp (-θ₀ * (m : ℝ) / 4) *
          ∑' e : ℕ × ℤ, (fpDistP p hp0' hp1' s e).toReal *
            Real.exp (θ₀ * (e.1 : ℝ)) := hcher
    _ ≤ Real.exp (-θ₀ * (m : ℝ) / 4) *
          (B * Real.exp (θ₀ * (K : ℝ))) :=
      mul_le_mul_of_nonneg_left hZB (Real.exp_pos _).le
    _ = B * Real.exp (θ₀ * (K : ℝ) - θ₀ * (m : ℝ) / 4) := by
      rw [show θ₀ * (K : ℝ) - θ₀ * (m : ℝ) / 4 =
        (-θ₀ * (m : ℝ) / 4) + θ₀ * (K : ℝ) by ring, Real.exp_add]
      ring
    _ ≤ B * Real.exp (-θ₀ * (m : ℝ) / 8) := by
      apply mul_le_mul_of_nonneg_left _ hBpos.le
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hKm4 hθ₀nn]
    _ ≤ δ * (m : ℝ) ^ (-A) := hfin

/-! ### Holding-law inputs for the Case-2 edge weight -/

/-- Real-valued first-coordinate MGF bound for the tilted holding law, uniform
on the campaign window.  The exact linear coefficient is `q(p)⁻¹`; here it
is replaced by `125/8` using `q(p) ≥ 8/125`, so the bound can be selected
before `p`. -/
theorem holdP_fst_mgf_le_real {p theta : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1 / 2000) :
    ∑' d : ℕ × ℤ,
        (holdP p (by linarith) (by linarith) d).toReal *
          Real.exp (theta * (d.1 : ℝ)) ≤
      1 + (125 / 8 : ℝ) * theta + 96000000 * theta ^ 2 := by
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  have hterm : ∀ d : ℕ × ℤ,
      (holdP p hp0' hp1' d).toReal * Real.exp (theta * (d.1 : ℝ)) =
        (holdP p hp0' hp1' d * TaoCollatz.expW2 theta 0 d).toReal := by
    intro d
    rw [TaoCollatz.expW2, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    congr 2
    ring
  have hquad :
      ∑' d : ℕ × ℤ,
          (holdP p hp0' hp1' d).toReal * Real.exp (theta * (d.1 : ℝ)) ≤
        1 + (pairThreeProb p)⁻¹ * theta + 96000000 * theta ^ 2 := by
    calc
      ∑' d : ℕ × ℤ,
          (holdP p hp0' hp1' d).toReal * Real.exp (theta * (d.1 : ℝ)) =
          ∑' d : ℕ × ℤ,
            (holdP p hp0' hp1' d * TaoCollatz.expW2 theta 0 d).toReal :=
        tsum_congr hterm
      _ = (TaoCollatz.tiltZ (holdP p hp0' hp1')
          (TaoCollatz.expW2 theta 0)).toReal :=
        (ENNReal.tsum_toReal_eq (fun d =>
          ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top)).symm
      _ ≤ (ENNReal.ofReal
          (1 + (pairThreeProb p)⁻¹ * theta + 96000000 * theta ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (tiltZ_holdP_fst_le_quad_window hp0 hp1 (by linarith) htheta1)
      _ = 1 + (pairThreeProb p)⁻¹ * theta + 96000000 * theta ^ 2 := by
        rw [ENNReal.toReal_ofReal]
        have hqpos := pairThreeProb_pos p hp0' hp1'
        positivity
  have hq := (pairThreeProb_mem_window hp0 hp1).1
  have hinv : (pairThreeProb p)⁻¹ ≤ (125 / 8 : ℝ) := by
    have h := inv_anti₀ (show (0 : ℝ) < 8 / 125 by norm_num) hq
    norm_num at h ⊢
    exact h
  nlinarith

/-- Uniform first-coordinate right tail for `holdP`, the holding-law companion
to `fpDistP_fst_tail_le`.  The exact first marginal is geometric with failure
ratio `1-q(p) ≤ 117/125`; this fixed worst-case ratio gives one threshold
chosen before `p`. -/
theorem holdP_fst_tail_le (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ p : ℝ, ∀ hp0 : 1 / 5 ≤ p, ∀ hp1 : p ≤ 3 / 5,
      ∀ m : ℕ, Cthr ≤ m →
      ∑' d : ℕ × ℤ,
          (holdP p (by linarith [hp0]) (by linarith [hp1]) d).toReal *
            (if m < 4 * d.1 then (1 : ℝ) else 0) ≤
        δ * (m : ℝ) ^ (-A) := by
  set rho : ℝ := Real.log (125 / 117) / 8 with hrhodef
  have hlogpos : 0 < Real.log (125 / 117) := Real.log_pos (by norm_num)
  have hrhopos : 0 < rho := by rw [hrhodef]; positivity
  obtain ⟨Nlog, hNlog⟩ :=
    TaoCollatz.log_le_eps_mul_of_large (rho / (2 * A)) (by positivity)
  obtain ⟨Nexp, hNexp⟩ :=
    TaoCollatz.exp_neg_mul_le_of_large (rho / 2) (by positivity) δ hδ
  refine ⟨max 400 (max Nlog Nexp), ?_⟩
  intro p hp0 hp1 m hm
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  have hm400 : 400 ≤ m := le_trans (le_max_left _ _) hm
  have hmNlog : Nlog ≤ m :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hmNexp : Nexp ≤ m :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hf : ∀ k : ℕ, (0 : ℝ) ≤ (if m < 4 * k then (1 : ℝ) else 0) := by
    intro k
    split_ifs <;> norm_num
  have hstep : ∀ k : ℕ,
      (geomP (pairThreeProb p) (pairThreeProb_pos p hp0' hp1')
          (pairThreeProb_le_one p hp0' hp1') k).toReal *
            (if m < 4 * k then (1 : ℝ) else 0) =
        (if m / 4 < k then
          (geomP (pairThreeProb p) (pairThreeProb_pos p hp0' hp1')
            (pairThreeProb_le_one p hp0' hp1') k).toReal else 0) := by
    intro k
    by_cases h : m < 4 * k
    · rw [if_pos h, mul_one, if_pos (by omega)]
    · rw [if_neg h, mul_zero, if_neg (by omega)]
  have hred :
      ∑' d : ℕ × ℤ, (holdP p hp0' hp1' d).toReal *
          (if m < 4 * d.1 then (1 : ℝ) else 0) =
        (1 - pairThreeProb p) ^ (m / 4) := by
    rw [show (∑' d : ℕ × ℤ, (holdP p hp0' hp1' d).toReal *
          (if m < 4 * d.1 then (1 : ℝ) else 0)) =
        ∑' k : ℕ,
          (geomP (pairThreeProb p) (pairThreeProb_pos p hp0' hp1')
            (pairThreeProb_le_one p hp0' hp1') k).toReal *
              (if m < 4 * k then (1 : ℝ) else 0) from
        holdP_tsum_fst p hp0' hp1'
          (fun k => if m < 4 * k then (1 : ℝ) else 0) hf,
      tsum_congr hstep,
      geomP_tail (pairThreeProb p) (pairThreeProb_pos p hp0' hp1')
        (pairThreeProb_le_one p hp0' hp1')]
  rw [hred]
  have hq := pairThreeProb_mem_window hp0 hp1
  have hsurv0 : 0 ≤ 1 - pairThreeProb p := by
    have := pairThreeProb_le_one p hp0' hp1'
    linarith
  have hsurv : 1 - pairThreeProb p ≤ (117 / 125 : ℝ) := by linarith [hq.1]
  have hpow : (1 - pairThreeProb p) ^ (m / 4) ≤
      (117 / 125 : ℝ) ^ (m / 4) :=
    pow_le_pow_left₀ hsurv0 hsurv _
  have hbase : (117 / 125 : ℝ) ^ (m / 4) =
      Real.exp (Real.log (117 / 125) * ((m / 4 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (117 / 125 : ℝ) (m / 4),
      Real.rpow_def_of_pos (by norm_num)]
  have hm4lb : (m : ℝ) / 8 ≤ ((m / 4 : ℕ) : ℝ) := by
    have hnat : m ≤ 4 * (m / 4) + 3 := by omega
    have hh : (m : ℝ) ≤ 4 * ((m / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hnat
    have h400 : (400 : ℝ) ≤ m := by exact_mod_cast hm400
    linarith
  have hexp_le : Real.log (117 / 125) * ((m / 4 : ℕ) : ℝ) ≤
      -rho * m := by
    have hlog : Real.log (117 / 125) = -Real.log (125 / 117) := by
      rw [show (117 / 125 : ℝ) = (125 / 117)⁻¹ by norm_num, Real.log_inv]
    rw [hlog, hrhodef]
    nlinarith [mul_le_mul_of_nonneg_left hm4lb hlogpos.le]
  have hclose : Real.exp (-rho * m) ≤ δ * (m : ℝ) ^ (-A) := by
    rw [Real.rpow_neg hmpos.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos hmpos A), Real.rpow_def_of_pos hmpos A,
      ← Real.exp_add]
    have hAlog : A * Real.log m ≤ rho / 2 * m := by
      have h := hNlog m hmNlog
      have h2 : A * Real.log m ≤ A * (rho / (2 * A) * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left h hA.le
      have h3 : A * (rho / (2 * A) * (m : ℝ)) = rho / 2 * m := by
        field_simp
      linarith [h2, h3.le, h3.ge]
    have hexparg : -rho * (m : ℝ) + Real.log m * A ≤
        -(rho / 2) * m := by nlinarith [hAlog]
    exact le_trans (Real.exp_le_exp.mpr hexparg) (hNexp m hmNexp)
  calc
    (1 - pairThreeProb p) ^ (m / 4) ≤ (117 / 125 : ℝ) ^ (m / 4) := hpow
    _ = Real.exp (Real.log (117 / 125) * ((m / 4 : ℕ) : ℝ)) := hbase
    _ ≤ Real.exp (-rho * m) := Real.exp_le_exp.mpr hexp_le
    _ ≤ δ * (m : ℝ) ^ (-A) := hclose

/-! ### Law-parametric edge-weight split -/

/-- The depth-weight factor for an arbitrary holding law.  Keeping the law as
an argument isolates the Fubini/summability proof from all `Pascal(p)`
specific estimates. -/
noncomputable def edgeWeightFor (P : PMF (ℕ × ℤ))
    (A : ℝ) (m : ℕ) (e : ℕ × ℤ) : ℝ :=
  ∑' d : ℕ × ℤ,
    (P d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)

/-- The edge-weight factor for the tilted holding law. -/
noncomputable def edgeWeightP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (A : ℝ) (m : ℕ) (e : ℕ × ℤ) : ℝ :=
  edgeWeightFor (holdP p hp0 hp1) A m e

theorem edgeWeightFor_nonneg (P : PMF (ℕ × ℤ))
    (A : ℝ) (m : ℕ) (e : ℕ × ℤ) :
    0 ≤ edgeWeightFor P A m e :=
  tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Law-parametric Fubini split behind Tao's (7.48)--(7.49).  The only
probabilistic inputs are that `P` and `E` are PMFs; all law dependence is
confined to the two MGF series and two one-coordinate tails. -/
theorem edgeWeightFor_split {P E : PMF (ℕ × ℤ)} {A : ℝ}
    (hA : 0 ≤ A) {m : ℕ} (hm : 2 ≤ m)
    (hZE : Summable fun e : ℕ × ℤ =>
      (E e).toReal * Real.exp (2 * A / (m : ℝ) * (e.1 : ℝ)))
    (hZP : Summable fun d : ℕ × ℤ =>
      (P d).toReal * Real.exp (2 * A / (m : ℝ) * (d.1 : ℝ))) :
    ∑' e : ℕ × ℤ, (E e).toReal * edgeWeightFor P A m e ≤
      (m : ℝ) ^ (-A)
          * (∑' e : ℕ × ℤ,
              (E e).toReal * Real.exp (2 * A / (m : ℝ) * (e.1 : ℝ)))
          * (∑' d : ℕ × ℤ,
              (P d).toReal * Real.exp (2 * A / (m : ℝ) * (d.1 : ℝ)))
        + (∑' e : ℕ × ℤ,
            (E e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0))
        + (∑' d : ℕ × ℤ,
            (P d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set theta : ℝ := 2 * A / (m : ℝ) with hthetadef
  have hthetann : 0 ≤ theta := by rw [hthetadef]; positivity
  set mA : ℝ := (m : ℝ) ^ (-A) with hmAdef
  have hmA0 : 0 < mA := Real.rpow_pos_of_pos hmpos _
  set ZE : ℝ := ∑' e : ℕ × ℤ,
    (E e).toReal * Real.exp (theta * (e.1 : ℝ)) with hZEdef
  set ZP : ℝ := ∑' d : ℕ × ℤ,
    (P d).toReal * Real.exp (theta * (d.1 : ℝ)) with hZPdef
  set TE : ℝ := ∑' e : ℕ × ℤ,
    (E e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0) with hTEdef
  set TP : ℝ := ∑' d : ℕ × ℤ,
    (P d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0) with hTPdef
  have hPsum : Summable fun d : ℕ × ℤ => (P d).toReal :=
    ENNReal.summable_toReal P.tsum_coe_ne_top
  have hPmass : ∑' d : ℕ × ℤ, (P d).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun d => P.apply_ne_top d), P.tsum_coe,
      ENNReal.toReal_one]
  have hEsum : Summable fun e : ℕ × ℤ => (E e).toReal :=
    ENNReal.summable_toReal E.tsum_coe_ne_top
  have hEmass : ∑' e : ℕ × ℤ, (E e).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun e => E.apply_ne_top e), E.tsum_coe,
      ENNReal.toReal_one]
  have hsumP_le : ∀ f : ℕ × ℤ → ℝ, (∀ d, 0 ≤ f d) → (∀ d, f d ≤ 1) →
      Summable fun d => (P d).toReal * f d := by
    intro f hf0 hf1
    refine Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg (hf0 d)) (fun d => ?_) hPsum
    simpa using mul_le_mul_of_nonneg_left (hf1 d) ENNReal.toReal_nonneg
  have hsumE_le : ∀ f : ℕ × ℤ → ℝ, (∀ e, 0 ≤ f e) → (∀ e, f e ≤ 1) →
      Summable fun e => (E e).toReal * f e := by
    intro f hf0 hf1
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg (hf0 e)) (fun e => ?_) hEsum
    simpa using mul_le_mul_of_nonneg_left (hf1 e) ENNReal.toReal_nonneg
  have hrpow01 : ∀ e d : ℕ × ℤ,
      ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 :=
    fun e d => Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast Nat.le_max_right _ _) (by linarith)
  have hrpow0 : ∀ e d : ℕ × ℤ,
      (0 : ℝ) ≤ ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) :=
    fun _ _ => Real.rpow_nonneg (by positivity) _
  have hind0 : ∀ (Q : Prop) [Decidable Q],
      (0 : ℝ) ≤ (if Q then (1 : ℝ) else 0) := by
    intro Q _
    split_ifs <;> norm_num
  have hind1 : ∀ (Q : Prop) [Decidable Q],
      (if Q then (1 : ℝ) else 0) ≤ 1 := by
    intro Q _
    split_ifs <;> norm_num
  have hpere : ∀ e : ℕ × ℤ, edgeWeightFor P A m e ≤
      mA * Real.exp (theta * (e.1 : ℝ)) * ZP
        + (if m < 4 * e.1 then (1 : ℝ) else 0) + TP := by
    intro e
    have hEWsum : Summable fun d : ℕ × ℤ =>
        (P d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) :=
      hsumP_le _ (hrpow0 e) (hrpow01 e)
    have ht1 : Summable fun d : ℕ × ℤ =>
        mA * Real.exp (theta * (e.1 : ℝ)) *
          ((P d).toReal * Real.exp (theta * (d.1 : ℝ))) := hZP.mul_left _
    have ht2 : Summable fun d : ℕ × ℤ =>
        (P d).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0) :=
      hsumP_le _ (fun _ => hind0 _) (fun _ => hind1 _)
    have ht3 : Summable fun d : ℕ × ℤ =>
        (P d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0) :=
      hsumP_le _ (fun _ => hind0 _) (fun _ => hind1 _)
    have hptw : ∀ d : ℕ × ℤ,
        (P d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤
          mA * Real.exp (theta * (e.1 : ℝ)) *
              ((P d).toReal * Real.exp (theta * (d.1 : ℝ)))
            + (P d).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
            + (P d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0) := by
      intro d
      have hsummand := TaoCollatz.edgeWeight_summand_le hA hm e d
      have hexpsplit : mA *
          Real.exp (2 * A * ((e.1 + d.1 : ℕ) : ℝ) / (m : ℝ)) =
        mA * Real.exp (theta * (e.1 : ℝ)) * Real.exp (theta * (d.1 : ℝ)) := by
        rw [show 2 * A * ((e.1 + d.1 : ℕ) : ℝ) / (m : ℝ) =
          theta * (e.1 : ℝ) + theta * (d.1 : ℝ) by
            rw [hthetadef]
            push_cast
            ring,
          Real.exp_add]
        ring
      have hind : (if m < 2 * (e.1 + d.1) then (1 : ℝ) else 0) ≤
          (if m < 4 * e.1 then (1 : ℝ) else 0) +
            (if m < 4 * d.1 then (1 : ℝ) else 0) := by
        by_cases h2 : m < 2 * (e.1 + d.1)
        · rw [if_pos h2]
          rcases (by omega : m < 4 * e.1 ∨ m < 4 * d.1) with h | h
          · rw [if_pos h]
            linarith [hind0 (m < 4 * d.1)]
          · rw [if_pos h]
            linarith [hind0 (m < 4 * e.1)]
        · rw [if_neg h2]
          linarith [hind0 (m < 4 * e.1), hind0 (m < 4 * d.1)]
      have hPn : (0 : ℝ) ≤ (P d).toReal := ENNReal.toReal_nonneg
      calc
        (P d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤
            (P d).toReal * ((m : ℝ) ^ (-A) *
              Real.exp (2 * A * ((e.1 + d.1 : ℕ) : ℝ) / (m : ℝ)) +
                (if m < 2 * (e.1 + d.1) then (1 : ℝ) else 0)) :=
          mul_le_mul_of_nonneg_left hsummand hPn
        _ = (P d).toReal * (mA * Real.exp (theta * (e.1 : ℝ)) *
              Real.exp (theta * (d.1 : ℝ))) +
            (P d).toReal * (if m < 2 * (e.1 + d.1) then (1 : ℝ) else 0) := by
          rw [← hmAdef, hexpsplit]
          ring
        _ ≤ mA * Real.exp (theta * (e.1 : ℝ)) *
              ((P d).toReal * Real.exp (theta * (d.1 : ℝ)))
            + (P d).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
            + (P d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0) := by
          have := mul_le_mul_of_nonneg_left hind hPn
          nlinarith
    have hsub1 : (∑' d : ℕ × ℤ,
        mA * Real.exp (theta * (e.1 : ℝ)) *
          ((P d).toReal * Real.exp (theta * (d.1 : ℝ)))) =
        mA * Real.exp (theta * (e.1 : ℝ)) * ZP := by
      rw [tsum_mul_left, ← hZPdef]
    have hsub2 : (∑' d : ℕ × ℤ,
        (P d).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)) =
        (if m < 4 * e.1 then (1 : ℝ) else 0) := by
      rw [tsum_mul_right, hPmass, one_mul]
    calc
      edgeWeightFor P A m e ≤ ∑' d : ℕ × ℤ,
          (mA * Real.exp (theta * (e.1 : ℝ)) *
              ((P d).toReal * Real.exp (theta * (d.1 : ℝ))) +
            (P d).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0) +
            (P d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0)) :=
        hEWsum.tsum_le_tsum hptw ((ht1.add ht2).add ht3)
      _ = mA * Real.exp (theta * (e.1 : ℝ)) * ZP +
          (if m < 4 * e.1 then (1 : ℝ) else 0) + TP := by
        rw [(ht1.add ht2).tsum_add ht3, ht1.tsum_add ht2, hsub1, hsub2, ← hTPdef]
  have hEWEsum : Summable fun e : ℕ × ℤ =>
      (E e).toReal * edgeWeightFor P A m e := by
    refine hsumE_le _ (fun e => edgeWeightFor_nonneg P A m e) (fun e => ?_)
    exact (hsumP_le _ (hrpow0 e) (hrpow01 e)).tsum_le_tsum
      (fun d => by simpa using
        mul_le_mul_of_nonneg_left (hrpow01 e d) ENNReal.toReal_nonneg) hPsum |>.trans_eq hPmass
  have hF1 : Summable fun e : ℕ × ℤ =>
      mA * ZP * ((E e).toReal * Real.exp (theta * (e.1 : ℝ))) := hZE.mul_left _
  have hF2 : Summable fun e : ℕ × ℤ =>
      (E e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0) :=
    hsumE_le _ (fun _ => hind0 _) (fun _ => hind1 _)
  have hF3 : Summable fun e : ℕ × ℤ => (E e).toReal * TP := hEsum.mul_right _
  have hFsum : Summable fun e : ℕ × ℤ => (E e).toReal *
      (mA * Real.exp (theta * (e.1 : ℝ)) * ZP +
        (if m < 4 * e.1 then (1 : ℝ) else 0) + TP) := by
    have heq : (fun e : ℕ × ℤ => (E e).toReal *
        (mA * Real.exp (theta * (e.1 : ℝ)) * ZP +
          (if m < 4 * e.1 then (1 : ℝ) else 0) + TP)) =
        fun e => mA * ZP * ((E e).toReal * Real.exp (theta * (e.1 : ℝ))) +
          (E e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0) +
          (E e).toReal * TP := by
      funext e
      ring
    rw [heq]
    exact (hF1.add hF2).add hF3
  have hsub1 : (∑' e : ℕ × ℤ,
      mA * ZP * ((E e).toReal * Real.exp (theta * (e.1 : ℝ)))) =
      mA * ZP * ZE := by rw [tsum_mul_left, ← hZEdef]
  have hsub3 : (∑' e : ℕ × ℤ, (E e).toReal * TP) = TP := by
    rw [tsum_mul_right, hEmass, one_mul]
  calc
    ∑' e : ℕ × ℤ, (E e).toReal * edgeWeightFor P A m e ≤
        ∑' e : ℕ × ℤ, (E e).toReal *
          (mA * Real.exp (theta * (e.1 : ℝ)) * ZP +
            (if m < 4 * e.1 then (1 : ℝ) else 0) + TP) :=
      hEWEsum.tsum_le_tsum
        (fun e => mul_le_mul_of_nonneg_left (hpere e) ENNReal.toReal_nonneg) hFsum
    _ = ∑' e : ℕ × ℤ,
        (mA * ZP * ((E e).toReal * Real.exp (theta * (e.1 : ℝ))) +
          (E e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0) +
          (E e).toReal * TP) := by
      refine tsum_congr fun e => ?_
      ring
    _ = mA * ZP * ZE + TE + TP := by
      rw [(hF1.add hF2).tsum_add hF3, hF1.tsum_add hF2, hsub1, hsub3, ← hTEdef]
    _ = mA * ZE * ZP + TE + TP := by ring

/-- `Pascal(p)` specialization of the law-parametric Fubini split. -/
theorem fpDistP_edgeWeight_split {p A : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) (hA : 0 ≤ A)
    {m : ℕ} (hm : 2 ≤ m) (s : ℕ)
    (hZf : Summable fun e : ℕ × ℤ =>
      (fpDistP p (by linarith) (by linarith) s e).toReal *
        Real.exp (2 * A / (m : ℝ) * (e.1 : ℝ)))
    (hZh : Summable fun d : ℕ × ℤ =>
      (holdP p (by linarith) (by linarith) d).toReal *
        Real.exp (2 * A / (m : ℝ) * (d.1 : ℝ))) :
    ∑' e : ℕ × ℤ,
        (fpDistP p (by linarith) (by linarith) s e).toReal *
          edgeWeightP p (by linarith) (by linarith) A m e ≤
      (m : ℝ) ^ (-A)
          * (∑' e : ℕ × ℤ,
              (fpDistP p (by linarith) (by linarith) s e).toReal *
                Real.exp (2 * A / (m : ℝ) * (e.1 : ℝ)))
          * (∑' d : ℕ × ℤ,
              (holdP p (by linarith) (by linarith) d).toReal *
                Real.exp (2 * A / (m : ℝ) * (d.1 : ℝ)))
        + (∑' e : ℕ × ℤ,
            (fpDistP p (by linarith) (by linarith) s e).toReal *
              (if m < 4 * e.1 then (1 : ℝ) else 0))
        + (∑' d : ℕ × ℤ,
            (holdP p (by linarith) (by linarith) d).toReal *
              (if m < 4 * d.1 then (1 : ℝ) else 0)) := by
  simpa only [edgeWeightP] using
    (edgeWeightFor_split (P := holdP p (by linarith) (by linarith))
      (E := fpDistP p (by linarith) (by linarith) s) hA hm hZf hZh)

end TaoCollatz.Sec7P
