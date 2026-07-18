import TaoCollatz.Sec6.MixingCore
import Mathlib.Analysis.PSeries

/-! The scale-telescope branch of the §6 proof. -/

namespace TaoCollatz

/-- There is no oscillation between a Syracuse law and its projection to the same level. -/
theorem osc_syracZ_self (n : ℕ) :
    osc n n le_rfl (fun Y => ((syracZ n) Y).toReal) = 0 := by
  rw [osc_syracZ_eq_l1_lift]
  simp [syracLift]

/-- The `(1.22)` triangle inequality telescoped along consecutive projection levels. -/
theorem osc_syracZ_le_sum_steps (m n : ℕ) (hmn : m ≤ n) :
    osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤
      ∑ k ∈ Finset.Ico m n,
        osc k (k + 1) (Nat.le_succ k) (fun Y => ((syracZ (k + 1)) Y).toReal) := by
  induction n, hmn using Nat.le_induction with
  | base => simp [osc_syracZ_self]
  | succ n hmn ih =>
      calc
        osc m (n + 1) (hmn.trans (Nat.le_succ n))
            (fun Y => ((syracZ (n + 1)) Y).toReal) ≤
            osc n (n + 1) (Nat.le_succ n) (fun Y => ((syracZ (n + 1)) Y).toReal) +
              osc m n hmn (fun Y => ((syracZ n) Y).toReal) :=
          osc_syracZ_levels_triangle m n (n + 1) hmn (Nat.le_succ n)
        _ ≤ osc n (n + 1) (Nat.le_succ n) (fun Y => ((syracZ (n + 1)) Y).toReal) +
              ∑ k ∈ Finset.Ico m n,
                osc k (k + 1) (Nat.le_succ k) (fun Y => ((syracZ (k + 1)) Y).toReal) := by
          gcongr
        _ = ∑ k ∈ Finset.Ico m (n + 1),
              osc k (k + 1) (Nat.le_succ k) (fun Y => ((syracZ (k + 1)) Y).toReal) := by
          rw [Finset.sum_Ico_succ_top hmn]
          ac_rfl

/-- The `ζ(2)`-mass of the telescope, symbolic (big-C campaign, step 2). -/
noncomputable def S_zeta2 : ℝ := ∑' k : ℕ, (k : ℝ) ^ (-(2 : ℝ))

theorem S_zeta2_nonneg : 0 ≤ S_zeta2 :=
  tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **(6.1) the regime reduction** (C10, obligation 0): the general bound for all `1 ≤ m ≤ n` follows
from the high-regime bound (`0.9n ≤ m ≤ n`, large `n`). Tao p.28: once (1.23) holds in the regime
`0.9n ≤ m ≤ n`, the (1.22)-consistency telescope across scales gives it for general `10 ≤ m ≤ n`, and
`1 ≤ m < 10` follows trivially from the triangle inequality; the finitely many small `n < n₀` are
absorbed by the trivial `osc ≤ 2` bound (a probability density has total mass ≤ 1) into a large constant.

Threshold-explicit form (big-C campaign, step 2): the high-regime bound is supplied at
exponent `A+2` with EXPLICIT constant `C` and cutoff `n₀`; the general-`m` constant is
`2·(max 9 n₀)^A + C·S_zeta2`. -/
theorem osc_syracZ_regime_telescope_at (A : ℝ) (hA : 0 < A) (C : ℝ) (hC : 0 < C) (n₀ : ℕ)
    (hstep : ∀ n m : ℕ, ∀ hmn : m ≤ n, n₀ ≤ n → 9 * n ≤ 10 * m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-(A + 2))) :
    ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal)
        ≤ (2 * ((max 9 n₀ : ℕ) : ℝ) ^ A + C * S_zeta2) * (m : ℝ) ^ (-A) := by
  unfold S_zeta2
  set N : ℕ := max 9 n₀ with hNdef
  set S : ℝ := ∑' k : ℕ, (k : ℝ) ^ (-(2 : ℝ)) with hSdef
  have hsummable : Summable (fun k : ℕ => (k : ℝ) ^ (-(2 : ℝ))) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hS0 : 0 ≤ S := tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  intro n m hmn hm
  by_cases hmN : m < N
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hmN' : (m : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hmN)
    have hpow : (m : ℝ) ^ A ≤ (N : ℝ) ^ A :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hmN' hA.le
    calc
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ 2 := osc_syracZ_le_two m n hmn
      _ = 2 * (m : ℝ) ^ A * (m : ℝ) ^ (-A) := by
        rw [mul_assoc]
        rw [← Real.rpow_add hmpos]
        norm_num
      _ ≤ (2 * (N : ℝ) ^ A + C * S) * (m : ℝ) ^ (-A) := by
        have hmneg : 0 ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hCS : 0 ≤ C * S := mul_nonneg hC.le hS0
        nlinarith
  · have hNm : N ≤ m := by omega
    have hm9 : 9 ≤ m := (le_max_left 9 n₀).trans hNm
    have hmn_step := osc_syracZ_le_sum_steps m n hmn
    calc
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤
          ∑ k ∈ Finset.Ico m n,
            osc k (k + 1) (Nat.le_succ k) (fun Y => ((syracZ (k + 1)) Y).toReal) := hmn_step
      _ ≤ ∑ k ∈ Finset.Ico m n, C * (k : ℝ) ^ (-(A + 2)) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hmk := (Finset.mem_Ico.mp hk).1
        have hk9 : 9 ≤ k := hm9.trans hmk
        apply hstep (k + 1) k (Nat.le_succ k)
        · exact le_trans (le_max_right 9 n₀) (le_trans hNm (hmk.trans (Nat.le_succ k)))
        · omega
      _ ≤ C * (m : ℝ) ^ (-A) * ∑ k ∈ Finset.Ico m n, (k : ℝ) ^ (-(2 : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hmk : m ≤ k := (Finset.mem_Ico.mp hk).1
        have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
        have hkpos : (0 : ℝ) < k := hmpos.trans_le (by exact_mod_cast hmk)
        have hrpow : (k : ℝ) ^ (-A) ≤ (m : ℝ) ^ (-A) :=
          Real.rpow_le_rpow_of_nonpos hmpos (by exact_mod_cast hmk) (neg_nonpos.mpr hA.le)
        rw [show -(A + 2) = -A + -(2 : ℝ) by ring, Real.rpow_add hkpos]
        have hk2 : 0 ≤ (k : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        calc
          C * ((k : ℝ) ^ (-A) * (k : ℝ) ^ (-(2 : ℝ))) =
              C * (k : ℝ) ^ (-A) * (k : ℝ) ^ (-(2 : ℝ)) := by ring
          _ ≤ C * (m : ℝ) ^ (-A) * (k : ℝ) ^ (-(2 : ℝ)) := by gcongr
      _ ≤ C * (m : ℝ) ^ (-A) * S := by
        gcongr
        exact hsummable.sum_le_tsum (Finset.Ico m n)
          (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ (2 * (N : ℝ) ^ A + C * S) * (m : ℝ) ^ (-A) := by
        have hmneg : 0 ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hNA : 0 ≤ (N : ℝ) ^ A := Real.rpow_nonneg (Nat.cast_nonneg _) _
        nlinarith

/-- **(6.1) the regime reduction**, original `∃`-form: delegates to the
threshold-explicit telescope (big-C campaign, step 2). -/
theorem osc_syracZ_regime_telescope (A : ℝ) (hA : 0 < A)
    (hhigh : ∀ B : ℝ, 0 < B →
      ∃ C > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, ∀ hmn : m ≤ n, n₀ ≤ n → 9 * n ≤ 10 * m →
        osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-B)) :
    ∃ C > 0, ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A) := by
  obtain ⟨C, hC, n₀, hstep⟩ := hhigh (A + 2) (by linarith)
  refine ⟨2 * ((max 9 n₀ : ℕ) : ℝ) ^ A + C * S_zeta2, ?_,
    osc_syracZ_regime_telescope_at A hA C hC n₀ hstep⟩
  have h9 : (0 : ℝ) < ((max 9 n₀ : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ max 9 n₀ := le_trans (by norm_num) (le_max_left _ _)
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one this
  have := mul_nonneg hC.le S_zeta2_nonneg
  nlinarith [Real.rpow_pos_of_pos h9 A]

end TaoCollatz
