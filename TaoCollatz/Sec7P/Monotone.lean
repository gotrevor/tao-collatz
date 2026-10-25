/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.Holding
import TaoCollatz.Sec7.Monotone

/-!
# The monotone renewal quantity for `Pascal(p)`

This starts the `p`-parametrized copy of Tao's Proposition 7.8 machinery.  The
deterministic white set is imported unchanged.  The definitions and lemmas here
are the probability-law-independent front of `Sec7/Monotone.lean`, with `Q`
replaced by `QP p`.
-/

namespace TaoCollatz.Sec7P

/-- Paper (7.38) for the tilted renewal value: the weighted worst-case value at
depth `m` from the far edge. -/
noncomputable def QPm (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (n ξ : ℕ) (ε A : ℝ) (m : ℕ) : ℝ :=
  ⨆ z : {z : ℕ × ℤ // 1 ≤ z.1 ∧ half - m ≤ z.1},
    ((max (half - z.1.1) 1 : ℕ) : ℝ) ^ A *
      QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε z.1.1 z.1.2

/-- The elementary induction-base bound (7.39), uniform in the tilted law. -/
theorem QPm_le_rpow (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half n ξ : ℕ) (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (hm : 1 ≤ m) :
    QPm p hp0 hp1 half n ξ (TaoCollatz.epsBW : ℝ) A m ≤ (m : ℝ) ^ A := by
  have hε : (0 : ℝ) ≤ (TaoCollatz.epsBW : ℝ) := by
    unfold TaoCollatz.epsBW
    positivity
  refine Real.iSup_le (fun z => ?_) (Real.rpow_nonneg (Nat.cast_nonneg m) A)
  have hw : ((max (half - z.1.1) 1 : ℕ) : ℝ) ^ A ≤ (m : ℝ) ^ A := by
    apply Real.rpow_le_rpow (by positivity) _ hA
    have hle : half - z.1.1 ≤ m := by
      obtain ⟨-, h2⟩ := z.2
      omega
    exact_mod_cast max_le hle hm
  calc
    ((max (half - z.1.1) 1 : ℕ) : ℝ) ^ A *
          QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ)
            (TaoCollatz.epsBW : ℝ) z.1.1 z.1.2
        ≤ (m : ℝ) ^ A * 1 := by
          apply mul_le_mul hw
            (QP_le_one p hp0 hp1 _ _ _ hε _ _)
            (QP_nonneg p hp0 hp1 _ _ _ _ _)
          exact Real.rpow_nonneg (Nat.cast_nonneg m) A
    _ = (m : ℝ) ^ A := mul_one _

/-- Every admissible weighted value is bounded by the tilted supremum. -/
theorem le_QPm (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half n ξ : ℕ) (ε A : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε) (m : ℕ)
    {p1 : ℕ} {l : ℤ} (h1 : 1 ≤ p1) (h2 : half - m ≤ p1) :
    ((max (half - p1) 1 : ℕ) : ℝ) ^ A *
        QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε p1 l
      ≤ QPm p hp0 hp1 half n ξ ε A m := by
  have hbdd : BddAbove (Set.range fun z :
      {z : ℕ × ℤ // 1 ≤ z.1 ∧ half - m ≤ z.1} =>
      ((max (half - z.1.1) 1 : ℕ) : ℝ) ^ A *
        QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε z.1.1 z.1.2) := by
    refine ⟨((max half 1 : ℕ) : ℝ) ^ A, ?_⟩
    rintro x ⟨z, rfl⟩
    calc
      ((max (half - z.1.1) 1 : ℕ) : ℝ) ^ A *
            QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε z.1.1 z.1.2
          ≤ ((max half 1 : ℕ) : ℝ) ^ A * 1 := by
            apply mul_le_mul _
              (QP_le_one p hp0 hp1 _ _ _ hε _ _)
              (QP_nonneg p hp0 hp1 _ _ _ _ _)
              (Real.rpow_nonneg (by positivity) A)
            apply Real.rpow_le_rpow (by positivity) _ hA
            exact_mod_cast max_le_max (Nat.sub_le _ _) le_rfl
      _ = ((max half 1 : ℕ) : ℝ) ^ A := mul_one _
  exact le_ciSup hbdd ⟨(p1, l), h1, h2⟩

/-- Inverted form of `le_QPm`, used when one renewal step lands in the
`m`-strip. -/
theorem QP_le_QPm (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half n ξ : ℕ) (ε A : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε) (m : ℕ)
    {p1 : ℕ} {l : ℤ} (h1 : 1 ≤ p1) (h2 : half - m ≤ p1) :
    QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε p1 l
      ≤ ((max (half - p1) 1 : ℕ) : ℝ) ^ (-A) *
        QPm p hp0 hp1 half n ξ ε A m := by
  have hwpos : (0 : ℝ) < ((max (half - p1) 1 : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ max (half - p1) 1 := le_max_right _ _
    have h' : (1 : ℝ) ≤ ((max (half - p1) 1 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hApos : (0 : ℝ) < ((max (half - p1) 1 : ℕ) : ℝ) ^ A :=
    Real.rpow_pos_of_pos hwpos A
  have hle := le_QPm p hp0 hp1 half n ξ ε A hA hε m (l := l) h1 h2
  rw [Real.rpow_neg hwpos.le]
  calc
    QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε p1 l
        = (((max (half - p1) 1 : ℕ) : ℝ) ^ A)⁻¹ *
          (((max (half - p1) 1 : ℕ) : ℝ) ^ A *
            QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε p1 l) := by
              field_simp
    _ ≤ (((max (half - p1) 1 : ℕ) : ℝ) ^ A)⁻¹ *
          QPm p hp0 hp1 half n ξ ε A m :=
      mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hApos.le)

/-- `QPm` is nonnegative. -/
theorem QPm_nonneg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half n ξ : ℕ) (ε A : ℝ) (m : ℕ) :
    0 ≤ QPm p hp0 hp1 half n ξ ε A m :=
  Real.iSup_nonneg fun z =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (QP_nonneg p hp0 hp1 _ _ _ _ _)

/-- At a white starting point, one tilted renewal step contracts by the full
factor `exp (-ε³)`.  This is the law-independent core of Tao's Case 1. -/
theorem QP_white_contract (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (n ξ : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) (l : ℤ)
    (hj : j ≤ half) (hw : (j, l) ∈ TaoCollatz.whiteSet n ξ) :
    QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε j l ≤ Real.exp (-(ε ^ 3)) := by
  rw [QP_rec p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε j l hj]
  have hind : Set.indicator (TaoCollatz.whiteSet n ξ)
      (1 : ℕ × ℤ → ℝ) (j, l) = 1 := Set.indicator_of_mem hw 1
  have hterm : ∀ d : ℕ × ℤ,
      (holdP p hp0 hp1 d).toReal *
          QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε (j + d.1) (l + d.2)
        ≤ (holdP p hp0 hp1 d).toReal := fun d => by
    calc
      (holdP p hp0 hp1 d).toReal *
            QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε (j + d.1) (l + d.2)
          ≤ (holdP p hp0 hp1 d).toReal * 1 :=
            mul_le_mul_of_nonneg_left
              (QP_le_one p hp0 hp1 _ _ _ hε _ _) ENNReal.toReal_nonneg
      _ = (holdP p hp0 hp1 d).toReal := mul_one _
  have hnn : ∀ d : ℕ × ℤ,
      0 ≤ (holdP p hp0 hp1 d).toReal *
        QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε (j + d.1) (l + d.2) :=
    fun d => mul_nonneg ENNReal.toReal_nonneg
      (QP_nonneg p hp0 hp1 _ _ _ _ _)
  have hsum : Summable fun d : ℕ × ℤ =>
      (holdP p hp0 hp1 d).toReal *
        QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε (j + d.1) (l + d.2) :=
    Summable.of_nonneg_of_le hnn hterm (holdP_summable_toReal p hp0 hp1)
  have htsum :
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
          QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε (j + d.1) (l + d.2) ≤ 1 :=
    le_trans (hsum.tsum_le_tsum hterm (holdP_summable_toReal p hp0 hp1))
      (holdP_tsum_toReal p hp0 hp1).le
  calc
    Real.exp (-(ε ^ 3) * Set.indicator (TaoCollatz.whiteSet n ξ) 1 (j, l)) *
          ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
            QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε (j + d.1) (l + d.2)
        ≤ Real.exp (-(ε ^ 3) * Set.indicator (TaoCollatz.whiteSet n ξ) 1 (j, l)) * 1 :=
          mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
    _ = Real.exp (-(ε ^ 3)) := by rw [hind, mul_one, mul_one]

end TaoCollatz.Sec7P
