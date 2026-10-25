/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7.Decay

/-!
# Convention bridge for the tilted Pascal damping campaign

This file identifies the conventions copied from the moonshot `PascalDampingDecay`
node with the proved §7 library.  The character bridge and prefix bridge are independent
of the Pascal parameter.  At `p = 1/2`, `pascalWeight` is the real mass of the existing
`pascal` PMF; this is the calibration seam used by `pascalDamping_half_decay`.
-/

open scoped ENNReal

namespace TaoCollatz.Sec7P

/-- The inclusive `Fin` prefix used by `Sec7P.pascalDamping` is `pre b (j+1)`.
This convention bridge is independent of the Pascal parameter. -/
theorem prefix_filter_eq_pre {m : ℕ} (b : Fin m → ℕ) (j : Fin m) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ≤ j), b i =
      TaoCollatz.pre b ((j : ℕ) + 1) := by
  rw [TaoCollatz.pre]
  refine Finset.sum_bij
    (s := Finset.univ.filter (fun i : Fin m => i ≤ j))
    (t := Finset.range ((j : ℕ) + 1)) (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Finset.mem_range]
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Fin.ext heq
  · intro k hk
    rw [Finset.mem_range] at hk
    refine ⟨⟨k, by omega⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  · intro i hi
    rw [dif_pos i.isLt]

/-- At the calibration parameter `p = 1/2`, the moonshot pair-sum weight is the
real-valued mass of Tao's existing `pascal` PMF. -/
theorem pascalWeight_half_bridge (b : ℕ) :
    (if 2 ≤ b then ((b : ℝ) - 1) * (1 / 2 : ℝ) ^ 2 *
        (1 - (1 / 2 : ℝ)) ^ (b - 2) else 0) =
      (TaoCollatz.pascal b).toReal := by
  rw [TaoCollatz.pascal_toReal]
  by_cases hb : b < 2
  · rw [if_neg (by omega : ¬ 2 ≤ b), if_pos hb]
  · rw [if_pos (by omega : 2 ≤ b), if_neg hb]
    push_cast [Nat.cast_sub (by omega : 1 ≤ b)]
    rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num,
      show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, mul_assoc]
    congr 1
    rw [← pow_add]
    congr 1
    omega

/-- `eC(q / 3^n)` depends only on the numerator modulo `3^n`. -/
theorem eC_div_congr {n : ℕ} (a b : ℤ)
    (h : (a : ZMod (3 ^ n)) = (b : ZMod (3 ^ n))) :
    TaoCollatz.eC ((a : ℚ) / 3 ^ n) = TaoCollatz.eC ((b : ℚ) / 3 ^ n) := by
  have hdvd : ((3 : ℤ) ^ n) ∣ (a - b) := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) (3 ^ n)).mp (by
      push_cast [h]
      ring)
    simpa using hz
  obtain ⟨k, hk⟩ := hdvd
  have hab : (a : ℚ) / (3 : ℚ) ^ n = (b : ℚ) / (3 : ℚ) ^ n + (k : ℚ) := by
    have hq : (a : ℚ) = (b : ℚ) + (3 : ℚ) ^ n * k := by
      exact_mod_cast (by linarith : a = b + 3 ^ n * k)
    rw [hq]
    field_simp
  rw [hab, TaoCollatz.eC_add, TaoCollatz.eC_intCast, mul_one]

/-- Moving `ξ` from the copied character's `ZMod` argument into Tao's rational
`eC` character changes the integer numerator only by a multiple of `3^n`.
This bridge is independent of the Pascal parameter. -/
theorem charZ_argument_bridge (n ξ : ℕ) (y : ZMod (3 ^ n)) :
    Complex.exp (-(2 * Real.pi * Complex.I *
        (((((ξ : ZMod (3 ^ n)) * y).val : ℕ) : ℂ)) / 3 ^ n)) =
      TaoCollatz.eC (-((ξ : ℚ) * (y.val : ℚ)) / 3 ^ n) := by
  have : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  rw [show Complex.exp (-(2 * Real.pi * Complex.I *
        (((((ξ : ZMod (3 ^ n)) * y).val : ℕ) : ℂ)) / 3 ^ n)) =
      TaoCollatz.eC (-((((ξ : ZMod (3 ^ n)) * y).val : ℕ) : ℚ) / 3 ^ n) by
    unfold TaoCollatz.eC
    congr 1
    push_cast
    ring]
  rw [show (-((((ξ : ZMod (3 ^ n)) * y).val : ℕ) : ℚ)) =
      (((-(((ξ : ZMod (3 ^ n)) * y).val : ℤ)) : ℤ) : ℚ) by push_cast; ring,
    show (-((ξ : ℚ) * (y.val : ℚ))) = (((-(ξ * y.val : ℕ) : ℤ)) : ℚ) by
      push_cast
      ring]
  apply eC_div_congr
  push_cast [ZMod.natCast_zmod_val]
  ring

end TaoCollatz.Sec7P
