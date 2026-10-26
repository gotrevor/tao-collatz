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

/-- The depth supremum with an arbitrary damping set.  This is the common
law-independent interface used at both Tao's original `epsBW` white set and
the finer `epsP` white set needed uniformly on the Pascal window. -/
noncomputable def QPmFor (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε A : ℝ) (m : ℕ) : ℝ :=
  ⨆ z : {z : ℕ × ℤ // 1 ≤ z.1 ∧ half - m ≤ z.1},
    ((max (half - z.1.1) 1 : ℕ) : ℝ) ^ A *
      QP p hp0 hp1 half W ε z.1.1 z.1.2

/-- Every admissible weighted value is bounded by the arbitrary-set depth
supremum. -/
theorem le_QPmFor (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε A : ℝ)
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (m : ℕ)
    {p1 : ℕ} {l : ℤ} (h1 : 1 ≤ p1) (h2 : half - m ≤ p1) :
    ((max (half - p1) 1 : ℕ) : ℝ) ^ A *
        QP p hp0 hp1 half W ε p1 l
      ≤ QPmFor p hp0 hp1 half W ε A m := by
  have hbdd : BddAbove (Set.range fun z :
      {z : ℕ × ℤ // 1 ≤ z.1 ∧ half - m ≤ z.1} =>
      ((max (half - z.1.1) 1 : ℕ) : ℝ) ^ A *
        QP p hp0 hp1 half W ε z.1.1 z.1.2) := by
    refine ⟨((max half 1 : ℕ) : ℝ) ^ A, ?_⟩
    rintro x ⟨z, rfl⟩
    calc
      ((max (half - z.1.1) 1 : ℕ) : ℝ) ^ A *
            QP p hp0 hp1 half W ε z.1.1 z.1.2
          ≤ ((max half 1 : ℕ) : ℝ) ^ A * 1 := by
            apply mul_le_mul _
              (QP_le_one p hp0 hp1 _ _ _ hε _ _)
              (QP_nonneg p hp0 hp1 _ _ _ _ _)
              (Real.rpow_nonneg (by positivity) A)
            apply Real.rpow_le_rpow (by positivity) _ hA
            exact_mod_cast max_le_max (Nat.sub_le _ _) le_rfl
      _ = ((max half 1 : ℕ) : ℝ) ^ A := mul_one _
  exact le_ciSup hbdd ⟨(p1, l), h1, h2⟩

/-- Inverted arbitrary-set supremum bound, used after one renewal step. -/
theorem QP_le_QPmFor (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε A : ℝ)
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (m : ℕ)
    {p1 : ℕ} {l : ℤ} (h1 : 1 ≤ p1) (h2 : half - m ≤ p1) :
    QP p hp0 hp1 half W ε p1 l
      ≤ ((max (half - p1) 1 : ℕ) : ℝ) ^ (-A) *
        QPmFor p hp0 hp1 half W ε A m := by
  have hwpos : (0 : ℝ) < ((max (half - p1) 1 : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ max (half - p1) 1 := le_max_right _ _
    have h' : (1 : ℝ) ≤ ((max (half - p1) 1 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hApos : (0 : ℝ) < ((max (half - p1) 1 : ℕ) : ℝ) ^ A :=
    Real.rpow_pos_of_pos hwpos A
  have hle := le_QPmFor p hp0 hp1 half W ε A hA hε m (l := l) h1 h2
  rw [Real.rpow_neg hwpos.le]
  calc
    QP p hp0 hp1 half W ε p1 l
        = (((max (half - p1) 1 : ℕ) : ℝ) ^ A)⁻¹ *
          (((max (half - p1) 1 : ℕ) : ℝ) ^ A *
            QP p hp0 hp1 half W ε p1 l) := by
              field_simp
    _ ≤ (((max (half - p1) 1 : ℕ) : ℝ) ^ A)⁻¹ *
          QPmFor p hp0 hp1 half W ε A m :=
      mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hApos.le)

/-- The arbitrary-set depth supremum is nonnegative. -/
theorem QPmFor_nonneg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε A : ℝ) (m : ℕ) :
    0 ≤ QPmFor p hp0 hp1 half W ε A m :=
  Real.iSup_nonneg fun z =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (QP_nonneg p hp0 hp1 _ _ _ _ _)

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

/-! ### A window-uniform geometric expectation

The first coordinate of `holdP p` is `Geom(q(p))`, where
`q(p) = 2p²(1-p)`.  On the campaign window, `q(p) ≥ 8/125`, so its survival
factor is at most `117/125`.  The following explicit cutoffs repeat Tao's
three-region proof of (7.43) with this worst-case base.  In particular, every
threshold is chosen before `p`.
-/

/-- The worst first-coordinate survival factor on `p ∈ [1/5,3/5]`. -/
noncomputable def holdPSurvivalBound : ℝ := 117 / 125

theorem holdPSurvivalBound_pos : 0 < holdPSurvivalBound := by
  norm_num [holdPSurvivalBound]

theorem holdPSurvivalBound_lt_one : holdPSurvivalBound < 1 := by
  norm_num [holdPSurvivalBound]

/-- The first-coordinate survival factor of `holdP p` is uniformly at most
`117/125` on the campaign window. -/
theorem pairThreeProb_survival_le_window {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    1 - pairThreeProb p ≤ holdPSurvivalBound := by
  have hq := (pairThreeProb_mem_window hp0 hp1).1
  norm_num [holdPSurvivalBound] at *
  linarith

/-- Explicit exponential threshold, copied locally because the corresponding
helper in `Sec7/Monotone` is private. -/
private theorem exp_neg_mul_le_atP (ρ : ℝ) (hρ : 0 < ρ) (b : ℝ) (hb : 0 < b) :
    ∀ m : ℕ, ⌈Real.log b⁻¹ / ρ⌉₊ ≤ m → Real.exp (-ρ * m) ≤ b := by
  intro m hm
  have hx : Real.log b⁻¹ / ρ ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
  have hρm : Real.log b⁻¹ ≤ (m : ℝ) * ρ := by
    have h := mul_le_mul_of_nonneg_right hx hρ.le
    rwa [div_mul_cancel₀ _ hρ.ne'] at h
  have hfin : -ρ * (m : ℝ) ≤ Real.log b := by
    rw [Real.log_inv] at hρm
    nlinarith [hρm]
  calc
    Real.exp (-ρ * (m : ℝ)) ≤ Real.exp (Real.log b) := Real.exp_le_exp.mpr hfin
    _ = b := Real.exp_log hb

/-- Explicit logarithmic threshold, copied locally because the corresponding
helper in `Sec7/Monotone` is private. -/
private theorem log_le_eps_mul_atP (ε : ℝ) (hε : 0 < ε) :
    ∀ m : ℕ, ⌈(2 / ε) ^ 2⌉₊ + 1 ≤ m → Real.log m ≤ ε * m := by
  intro m hm
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
  have hlog_le : Real.log m ≤ 2 * Real.sqrt m := by
    calc
      Real.log m = Real.log (Real.sqrt m ^ 2) := by rw [hsq]
      _ = 2 * Real.log (Real.sqrt m) := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 2 * (Real.sqrt m - 1) := by
        have := Real.log_le_sub_one_of_pos hsqrt_pos
        linarith
      _ ≤ 2 * Real.sqrt m := by linarith [hsqrt_pos.le]
  have hsqrt_lb : 2 / ε ≤ Real.sqrt m := by
    have hx : ((2 / ε) ^ 2 : ℝ) ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈(2 / ε) ^ 2⌉₊ ≤ m))
    calc
      2 / ε = Real.sqrt ((2 / ε) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt m := Real.sqrt_le_sqrt hx
  have hcomb : 2 * Real.sqrt m ≤ ε * m := by
    have h1 : (2 : ℝ) ≤ ε * Real.sqrt m := by
      have h := mul_le_mul_of_nonneg_left hsqrt_lb hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at h
    calc
      2 * Real.sqrt m ≤ (ε * Real.sqrt m) * Real.sqrt m :=
        mul_le_mul_of_nonneg_right h1 hsqrt_pos.le
      _ = ε * (Real.sqrt m ^ 2) := by ring
      _ = ε * m := by rw [hsq]
  linarith

/-- Uniform cutoff after which the worst geometric tail is below `b`. -/
noncomputable def K_geomPWindow (b : ℝ) : ℕ :=
  ⌈Real.log (b / 2)⁻¹ / Real.log (125 / 117)⌉₊

private theorem geomPWindow_lt_at (b : ℝ) (hb : 0 < b) :
    holdPSurvivalBound ^ K_geomPWindow b < b := by
  have hK := exp_neg_mul_le_atP (Real.log (125 / 117))
    (Real.log_pos (by norm_num)) (b / 2) (half_pos hb) (K_geomPWindow b)
    (by unfold K_geomPWindow; exact le_rfl)
  have hlog : Real.log holdPSurvivalBound = -Real.log (125 / 117) := by
    rw [show holdPSurvivalBound = (125 / 117 : ℝ)⁻¹ by
      norm_num [holdPSurvivalBound], Real.log_inv]
  calc
    holdPSurvivalBound ^ K_geomPWindow b =
        Real.exp ((K_geomPWindow b : ℝ) * Real.log holdPSurvivalBound) := by
          rw [Real.exp_nat_mul, Real.exp_log holdPSurvivalBound_pos]
    _ = Real.exp (-Real.log (125 / 117) * K_geomPWindow b) := by rw [hlog, mul_comm]
    _ ≤ b / 2 := hK
    _ < b := by linarith

/-- Uniform cutoff after which `t^k (117/125)^t` is below `b`. -/
noncomputable def T_powGeomPWindow (k : ℕ) (b : ℝ) : ℕ :=
  1 + (⌈(2 / (Real.log (125 / 117) / (2 * ((k : ℝ) + 1)))) ^ 2⌉₊ + 1) +
    ⌈Real.log (b / 2)⁻¹ / (Real.log (125 / 117) / 2)⌉₊

private theorem pow_mul_geomPWindow_lt_at (k : ℕ) (b : ℝ) (hb : 0 < b) :
    ∀ t : ℕ, T_powGeomPWindow k b ≤ t →
      (t : ℝ) ^ k * holdPSurvivalBound ^ t < b := by
  have hρ : (0 : ℝ) < Real.log (125 / 117) := Real.log_pos (by norm_num)
  have hNlog := log_le_eps_mul_atP
    (Real.log (125 / 117) / (2 * ((k : ℝ) + 1))) (div_pos hρ (by positivity))
  have hNexp := exp_neg_mul_le_atP
    (Real.log (125 / 117) / 2) (half_pos hρ) (b / 2) (half_pos hb)
  intro t ht
  unfold T_powGeomPWindow at ht
  set Nlog := ⌈(2 / (Real.log (125 / 117) / (2 * ((k : ℝ) + 1)))) ^ 2⌉₊ + 1
  set Nexp := ⌈Real.log (b / 2)⁻¹ / (Real.log (125 / 117) / 2)⌉₊
  have ht1 : 1 ≤ t := by omega
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hklog : (k : ℝ) * Real.log t ≤ Real.log (125 / 117) / 2 * t := by
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hfrac : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hk1]
      linarith
    have hrw : (k : ℝ) * (Real.log (125 / 117) / (2 * ((k : ℝ) + 1)) * t) =
        (k : ℝ) / ((k : ℝ) + 1) * (Real.log (125 / 117) / 2 * t) := by
      field_simp
    calc
      (k : ℝ) * Real.log t ≤
          (k : ℝ) * (Real.log (125 / 117) / (2 * ((k : ℝ) + 1)) * t) :=
        mul_le_mul_of_nonneg_left (hNlog t (by omega)) (Nat.cast_nonneg k)
      _ = (k : ℝ) / ((k : ℝ) + 1) * (Real.log (125 / 117) / 2 * t) := hrw
      _ ≤ Real.log (125 / 117) / 2 * t :=
        mul_le_of_le_one_left (mul_nonneg (by positivity) htpos.le) hfrac
  have hlog : Real.log holdPSurvivalBound = -Real.log (125 / 117) := by
    rw [show holdPSurvivalBound = (125 / 117 : ℝ)⁻¹ by
      norm_num [holdPSurvivalBound], Real.log_inv]
  have hexp_le : (k : ℝ) * Real.log t + (t : ℝ) * Real.log holdPSurvivalBound ≤
      -(Real.log (125 / 117) / 2) * t := by
    rw [hlog]
    linarith [hklog]
  calc
    (t : ℝ) ^ k * holdPSurvivalBound ^ t =
        Real.exp ((k : ℝ) * Real.log t + (t : ℝ) * Real.log holdPSurvivalBound) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log htpos,
        Real.exp_nat_mul, Real.exp_log holdPSurvivalBound_pos]
    _ ≤ Real.exp (-(Real.log (125 / 117) / 2) * t) := Real.exp_le_exp.mpr hexp_le
    _ ≤ b / 2 := hNexp t (by omega)
    _ < b := by linarith

/-- Uniform middle-tail cutoff for the tilted holding expectation. -/
noncomputable def K_holdP (A : ℝ) : ℕ :=
  K_geomPWindow (TaoCollatz.deltaBW / 3 * (2 : ℝ) ^ (-A))

/-- Uniform head-region cutoff for the tilted holding expectation. -/
noncomputable def M1_holdP (A : ℝ) : ℕ :=
  ⌈(K_holdP A : ℝ) * TaoCollatz.cHold A / (TaoCollatz.cHold A - 1)⌉₊

/-- Uniform far-tail cutoff for the tilted holding expectation. -/
noncomputable def T_holdP (A : ℝ) : ℕ :=
  T_powGeomPWindow ⌈A⌉₊ (TaoCollatz.deltaBW / 3 * (3 : ℝ) ^ (-A))

/-- Tao's Case-1 threshold with all choices uniform on the `p` window. -/
noncomputable def C_holdP (A : ℝ) : ℕ :=
  K_holdP A + M1_holdP A + 2 * T_holdP A + 4

theorem one_le_C_holdP (A : ℝ) : 1 ≤ C_holdP A := by
  unfold C_holdP
  omega

/-- Tao's three-region Case-1 expectation estimate with abstract uniform
cutoffs.  The only law-specific input is the exact `Geom(q(p))` first marginal;
its tails are bounded by the fixed base `117/125`. -/
theorem holdP_weight_expect_core (A : ℝ) (hA : 0 < A)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hpL : 1 / 5 ≤ p) (hpU : p ≤ 3 / 5) (K M1 T : ℕ)
    (hK : holdPSurvivalBound ^ K <
      TaoCollatz.deltaBW / 3 * (2 : ℝ) ^ (-A))
    (hM1 : (K : ℝ) * TaoCollatz.cHold A / (TaoCollatz.cHold A - 1) ≤ (M1 : ℝ))
    (hT : ∀ t : ℕ, T ≤ t →
      (t : ℝ) ^ ⌈A⌉₊ * holdPSurvivalBound ^ t <
        TaoCollatz.deltaBW / 3 * (3 : ℝ) ^ (-A)) :
    ∀ m : ℕ, K + M1 + 2 * T + 4 ≤ m →
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
          ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)
        ≤ Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A) := by
  intro m hm
  set E := Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) with hEdef
  have hεpos : (0 : ℝ) < (TaoCollatz.epsBW : ℝ) ^ 3 / 2 := by
    have h0 : (0 : ℚ) < TaoCollatz.epsBW := by
      unfold TaoCollatz.epsBW
      norm_num
    have h1 : (0 : ℝ) < (TaoCollatz.epsBW : ℝ) := by exact_mod_cast h0
    positivity
  have hδ : 0 < E - 1 := by
    have h2 := Real.add_one_le_exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2)
    rw [hEdef]
    linarith
  set δ := E - 1 with hδdef
  have hE1 : E = 1 + δ := by rw [hδdef]; ring
  have hδBW : TaoCollatz.deltaBW = δ := by
    rw [hδdef, hEdef]
    unfold TaoCollatz.deltaBW
    rfl
  rw [hδBW] at hK hT
  set c := TaoCollatz.cHold A with hcdef
  have hc1 : 1 < c := TaoCollatz.one_lt_cHold A hA
  have hcA : c ^ A = 1 + δ / 3 := by
    rw [hcdef, ← hδBW]
    exact TaoCollatz.cHold_rpow A hA
  set kA := ⌈A⌉₊ with hkAdef
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  let q : ℝ := pairThreeProb p
  have hq0 : 0 < q := by
    dsimp [q]
    exact pairThreeProb_pos p hp0 hp1
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact pairThreeProb_le_one p hp0 hp1
  let g := geomP q hq0 hq1
  have hg_sum : ∑' k : ℕ, (g k).toReal = 1 := by
    simpa [g] using geomP_tsum_toReal q hq0 hq1
  have hg_summable : Summable fun k : ℕ => (g k).toReal := by
    simpa [g] using geomP_summable_toReal q hq0 hq1
  have hg_tail (t : ℕ) :
      ∑' k : ℕ, (if t < k then (g k).toReal else 0) = (1 - q) ^ t := by
    simpa [g] using geomP_tail q hq0 hq1 t
  have hsurv0 : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hsurv_le : 1 - q ≤ holdPSurvivalBound := by
    dsimp [q]
    exact pairThreeProb_survival_le_window hpL hpU
  have hpow_le (t : ℕ) : (1 - q) ^ t ≤ holdPSurvivalBound ^ t :=
    pow_le_pow_left₀ hsurv0 hsurv_le t
  have hmarg :
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
          ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) =
        ∑' k : ℕ, (g k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) := by
    simpa [g, q] using holdP_tsum_fst p hp0 hp1
      (fun k => ((max (m - k) 1 : ℕ) : ℝ) ^ (-A))
      (fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [hmarg]
  have hpmass : ∀ k, (0 : ℝ) ≤ (g k).toReal := fun _ => ENNReal.toReal_nonneg
  have hw0 : ∀ k, (0 : ℝ) ≤ ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) :=
    fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hw1 : ∀ k, ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 := fun k =>
    Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast Nat.le_max_right (m - k) 1) (by linarith)
  have hterm_le : ∀ k, (g k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
      ≤ (g k).toReal := fun k => by
    calc
      (g k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
          ≤ (g k).toReal * 1 := mul_le_mul_of_nonneg_left (hw1 k) (hpmass k)
      _ = (g k).toReal := mul_one _
  have hterm0 : ∀ k, (0 : ℝ) ≤
      (g k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) :=
    fun k => mul_nonneg (hpmass k) (hw0 k)
  set g1 : ℕ → ℝ := fun k => if k ≤ K then
    (g k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) else 0
  set g2 : ℕ → ℝ := fun k => if K < k ∧ k ≤ m / 2 then
    (g k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) else 0
  set g3 : ℕ → ℝ := fun k => if K < k ∧ m / 2 < k then
    (g k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) else 0
  have hsplit : ∀ k, (g k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) =
      g1 k + g2 k + g3 k := by
    intro k
    simp only [g1, g2, g3]
    rcases le_or_gt k K with h1 | h1
    · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]
      ring
    · rcases le_or_gt k (m / 2) with h2 | h2
      · rw [if_neg (by omega), if_pos ⟨h1, h2⟩, if_neg (by omega)]
        ring
      · rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2⟩]
        ring
  have hg1sum : Summable g1 := Summable.of_nonneg_of_le
    (fun k => by simp only [g1]; split_ifs; exacts [hterm0 k, le_rfl])
    (fun k => by simp only [g1]; split_ifs; exacts [hterm_le k, hpmass k]) hg_summable
  have hg2sum : Summable g2 := Summable.of_nonneg_of_le
    (fun k => by simp only [g2]; split_ifs; exacts [hterm0 k, le_rfl])
    (fun k => by simp only [g2]; split_ifs; exacts [hterm_le k, hpmass k]) hg_summable
  have hg3sum : Summable g3 := Summable.of_nonneg_of_le
    (fun k => by simp only [g3]; split_ifs; exacts [hterm0 k, le_rfl])
    (fun k => by simp only [g3]; split_ifs; exacts [hterm_le k, hpmass k]) hg_summable
  have hmKpos : (0 : ℝ) < ((m - K : ℕ) : ℝ) := by
    have h : 1 ≤ m - K := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h
  have hW1 : ((m - K : ℕ) : ℝ) ^ (-A) ≤
      (1 + δ / 3) * (m : ℝ) ^ (-A) := by
    have hcast : ((m - K : ℕ) : ℝ) = (m : ℝ) - K := by
      rw [Nat.cast_sub (by omega)]
    have hcpos : (0 : ℝ) < c - 1 := by linarith
    have hmge : (K : ℝ) * c / (c - 1) ≤ (m : ℝ) := by
      calc
        (K : ℝ) * c / (c - 1) ≤ (M1 : ℝ) := hM1
        _ ≤ (m : ℝ) := by exact_mod_cast (by omega : M1 ≤ m)
    have hKc : (K : ℝ) * c ≤ (m : ℝ) * (c - 1) := by
      rw [div_le_iff₀ hcpos] at hmge
      linarith
    have hmc : (m : ℝ) / c ≤ (m : ℝ) - K := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < c)]
      nlinarith
    have hstep : ((m : ℝ) - K) ^ (-A) ≤ ((m : ℝ) / c) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hmc (by linarith)
    have hdiv : ((m : ℝ) / c) ^ (-A) =
        (m : ℝ) ^ (-A) * (1 + δ / 3) := by
      rw [Real.div_rpow hm0.le (by linarith : (0 : ℝ) ≤ c), Real.rpow_neg
        (by linarith : (0 : ℝ) ≤ c), div_inv_eq_mul, hcA]
    rw [hcast]
    calc
      ((m : ℝ) - K) ^ (-A) ≤ ((m : ℝ) / c) ^ (-A) := hstep
      _ = (1 + δ / 3) * (m : ℝ) ^ (-A) := by rw [hdiv]; ring
  have hreg1w : ∀ k, k ≤ K →
      ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ ((m - K : ℕ) : ℝ) ^ (-A) :=
    fun k hk => Real.rpow_le_rpow_of_nonpos hmKpos
      (by exact_mod_cast (by omega : m - K ≤ max (m - k) 1)) (by linarith)
  have hb1 : ∑' k, g1 k ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) := by
    have hle : ∀ k, g1 k ≤ (g k).toReal * ((m - K : ℕ) : ℝ) ^ (-A) := fun k => by
      simp only [g1]
      split_ifs with h
      · exact mul_le_mul_of_nonneg_left (hreg1w k h) (hpmass k)
      · exact mul_nonneg (hpmass k) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc
      ∑' k, g1 k ≤ ∑' k, (g k).toReal * ((m - K : ℕ) : ℝ) ^ (-A) :=
        hg1sum.tsum_le_tsum hle (hg_summable.mul_right _)
      _ = ((m - K : ℕ) : ℝ) ^ (-A) := by rw [tsum_mul_right, hg_sum, one_mul]
      _ ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) := hW1
  have hreg2w : ∀ k, k ≤ m / 2 →
      ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤
        (2 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
    intro k hk
    have hb : (m : ℝ) / 2 ≤ ((max (m - k) 1 : ℕ) : ℝ) := by
      have h2 : m ≤ 2 * max (m - k) 1 := by omega
      have h2' : (m : ℝ) ≤ 2 * ((max (m - k) 1 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hstep : ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ ((m : ℝ) / 2) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)
    have hdiv : ((m : ℝ) / 2) ^ (-A) = (2 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
      rw [Real.div_rpow hm0.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg
        (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      ring
    exact hstep.trans_eq hdiv
  have htailsum : Summable (fun k => if K < k then (g k).toReal else 0) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs; exacts [hpmass k, le_rfl])
      (fun k => by split_ifs; exacts [le_rfl, hpmass k]) hg_summable
  have hb2 : ∑' k, g2 k ≤ δ / 3 * (m : ℝ) ^ (-A) := by
    have hle : ∀ k, g2 k ≤ (if K < k then (g k).toReal else 0) *
        ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) := by
      intro k
      simp only [g2]
      split_ifs with h1 h2
      · exact mul_le_mul_of_nonneg_left (hreg2w k h1.2) (hpmass k)
      · exact absurd h1.1 h2
      · exact mul_nonneg (hpmass k) (by positivity)
      · rw [zero_mul]
    calc
      ∑' k, g2 k ≤ ∑' k, (if K < k then (g k).toReal else 0) *
          ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) :=
        hg2sum.tsum_le_tsum hle (htailsum.mul_right _)
      _ = (1 - q) ^ K * ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) := by
        rw [tsum_mul_right, hg_tail]
      _ ≤ holdPSurvivalBound ^ K * ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) :=
        mul_le_mul_of_nonneg_right (hpow_le K) (by positivity)
      _ ≤ δ / 3 * (2 : ℝ) ^ (-A) *
          ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) :=
        mul_le_mul_of_nonneg_right hK.le (by positivity)
      _ = δ / 3 * ((2 : ℝ) ^ (-A) * (2 : ℝ) ^ A) * (m : ℝ) ^ (-A) := by ring
      _ = δ / 3 * (m : ℝ) ^ (-A) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel,
          Real.rpow_zero, mul_one]
  have htail3 : holdPSurvivalBound ^ (m / 2) ≤ δ / 3 * (m : ℝ) ^ (-A) := by
    have ht1 : 1 ≤ m / 2 := by omega
    have htT : T ≤ m / 2 := by omega
    have htpos : (1 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by exact_mod_cast ht1
    have hhead := (hT (m / 2) htT).le
    have hm3t : (m : ℝ) ≤ 3 * ((m / 2 : ℕ) : ℝ) := by
      have h : m ≤ 3 * (m / 2) := by omega
      exact_mod_cast h
    have hcancel : ((m / 2 : ℕ) : ℝ) ^ (kA : ℝ) *
        ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) = 1 := by
      rw [← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero]
    have h1 : holdPSurvivalBound ^ (m / 2) =
        ((m / 2 : ℕ) : ℝ) ^ kA * holdPSurvivalBound ^ (m / 2) *
          ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) := by
      rw [mul_comm (((m / 2 : ℕ) : ℝ) ^ kA), mul_assoc,
        ← Real.rpow_natCast _ kA, hcancel, mul_one]
    have h2 : holdPSurvivalBound ^ (m / 2) ≤
        δ / 3 * (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) := by
      rw [h1]
      exact mul_le_mul_of_nonneg_right hhead (Real.rpow_nonneg (by linarith) _)
    have h3 : ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) ≤
        ((m / 2 : ℕ) : ℝ) ^ (-A) := by
      apply Real.rpow_le_rpow_of_exponent_le htpos
      have := Nat.le_ceil A
      rw [neg_le_neg_iff]
      exact_mod_cast this
    have h4 : (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-A) ≤
        (m : ℝ) ^ (-A) := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow_of_nonpos hm0 hm3t (by linarith)
    calc
      holdPSurvivalBound ^ (m / 2) ≤
          δ / 3 * (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) := h2
      _ ≤ δ / 3 * (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-A) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = δ / 3 * ((3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-A)) := by ring
      _ ≤ δ / 3 * (m : ℝ) ^ (-A) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have htail2sum : Summable (fun k => if m / 2 < k then (g k).toReal else 0) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs; exacts [hpmass k, le_rfl])
      (fun k => by split_ifs; exacts [le_rfl, hpmass k]) hg_summable
  have hb3 : ∑' k, g3 k ≤ δ / 3 * (m : ℝ) ^ (-A) := by
    have hle : ∀ k, g3 k ≤ (if m / 2 < k then (g k).toReal else 0) := by
      intro k
      simp only [g3]
      split_ifs with h1 h2
      · exact hterm_le k
      · exact absurd h1.2 h2
      · exact hpmass k
      · exact le_rfl
    calc
      ∑' k, g3 k ≤ ∑' k, (if m / 2 < k then (g k).toReal else 0) :=
        hg3sum.tsum_le_tsum hle htail2sum
      _ = (1 - q) ^ (m / 2) := hg_tail (m / 2)
      _ ≤ holdPSurvivalBound ^ (m / 2) := hpow_le (m / 2)
      _ ≤ δ / 3 * (m : ℝ) ^ (-A) := htail3
  calc
    ∑' k : ℕ, (g k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) =
        ∑' k, g1 k + ∑' k, g2 k + ∑' k, g3 k := by
      rw [tsum_congr hsplit, (hg1sum.add hg2sum).tsum_add hg3sum,
        hg1sum.tsum_add hg2sum]
    _ ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) + δ / 3 * (m : ℝ) ^ (-A) +
        δ / 3 * (m : ℝ) ^ (-A) := add_le_add (add_le_add hb1 hb2) hb3
    _ = (1 + δ) * (m : ℝ) ^ (-A) := by ring
    _ = E * (m : ℝ) ^ (-A) := by rw [← hE1]

/-- The tilted Case-1 expectation at an explicit threshold independent of `p`. -/
theorem holdP_weight_expect_explicitC (A : ℝ) (hA : 0 < A) :
    ∀ p : ℝ, ∀ hpL : 1 / 5 ≤ p, ∀ hpU : p ≤ 3 / 5,
      ∀ m : ℕ, C_holdP A ≤ m →
        ∑' d : ℕ × ℤ,
            (holdP p (by linarith [hpL]) (by linarith [hpU]) d).toReal *
              ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)
          ≤ Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A) := by
  have hb2 : (0 : ℝ) < TaoCollatz.deltaBW / 3 * (2 : ℝ) ^ (-A) :=
    mul_pos (by linarith [TaoCollatz.deltaBW_pos])
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hb3 : (0 : ℝ) < TaoCollatz.deltaBW / 3 * (3 : ℝ) ^ (-A) :=
    mul_pos (by linarith [TaoCollatz.deltaBW_pos])
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hK : holdPSurvivalBound ^ K_holdP A <
      TaoCollatz.deltaBW / 3 * (2 : ℝ) ^ (-A) := by
    unfold K_holdP
    exact geomPWindow_lt_at _ hb2
  have hM1 : (K_holdP A : ℝ) * TaoCollatz.cHold A /
      (TaoCollatz.cHold A - 1) ≤ (M1_holdP A : ℝ) := by
    unfold M1_holdP
    exact Nat.le_ceil _
  have hT : ∀ t : ℕ, T_holdP A ≤ t →
      (t : ℝ) ^ ⌈A⌉₊ * holdPSurvivalBound ^ t <
        TaoCollatz.deltaBW / 3 * (3 : ℝ) ^ (-A) := by
    unfold T_holdP
    exact pow_mul_geomPWindow_lt_at _ _ hb3
  intro p hpL hpU m hm
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  exact holdP_weight_expect_core A hA p hp0 hp1 hpL hpU
    (K_holdP A) (M1_holdP A) (T_holdP A) hK hM1 hT m (by
      unfold C_holdP at hm
      exact hm)

/-- Uniform existential form of the tilted Case-1 expectation.  The threshold
is selected before the Pascal parameter. -/
theorem holdP_weight_expect (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, 1 ≤ Cthr ∧
      ∀ p : ℝ, ∀ hpL : 1 / 5 ≤ p, ∀ hpU : p ≤ 3 / 5,
      ∀ m : ℕ, Cthr ≤ m →
        ∑' d : ℕ × ℤ,
            (holdP p (by linarith [hpL]) (by linarith [hpU]) d).toReal *
              ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)
          ≤ Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A) :=
  ⟨C_holdP A, one_le_C_holdP A, holdP_weight_expect_explicitC A hA⟩

/-- **Tilted Case 1 of Proposition 7.8.**  A white start at depth `m`
contracts by `exp(-epsBW³/2) m⁻ᴬ` against `QPm (m-1)`, uniformly for
`p ∈ [1/5,3/5]`.  This is Tao's (7.41)--(7.43), with the fixed-law
`hold_weight_expect` replaced by `holdP_weight_expect_explicitC`. -/
theorem QP_white_case1_explicitC (A : ℝ) (hA : 0 < A) :
    ∀ p : ℝ, ∀ hp0 : 0 < p, ∀ hp1 : p < 1,
      1 / 5 ≤ p → p ≤ 3 / 5 → ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ m : ℕ, C_holdP A ≤ m → m ≤ n / 2 → ∀ l : ℤ,
        (n / 2 - m, l) ∈ TaoCollatz.whiteSet n ξ →
        QP p hp0 hp1 (n / 2) (TaoCollatz.whiteSet n ξ) (TaoCollatz.epsBW : ℝ)
            (n / 2 - m) l
          ≤ Real.exp (-(TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A) *
            QPm p hp0 hp1 (n / 2) n ξ (TaoCollatz.epsBW : ℝ) A (m - 1) := by
  have hC0one := one_le_C_holdP A
  intro p hp0 hp1 hpL hpU
  have hC0 : ∀ m : ℕ, C_holdP A ≤ m →
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
          ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)
        ≤ Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A) := by
    intro m hm
    simpa using holdP_weight_expect_explicitC A hA p hpL hpU m hm
  intro n ξ _ m hm hmn l hw
  set half := n / 2 with hhalf
  set ε : ℝ := (TaoCollatz.epsBW : ℝ) with hεdef
  have hε0 : (0 : ℝ) ≤ ε := by
    rw [hεdef]
    have h0 : (0 : ℚ) ≤ TaoCollatz.epsBW := by
      unfold TaoCollatz.epsBW
      norm_num
    exact_mod_cast h0
  have hm1 : 1 ≤ m := le_trans hC0one hm
  set QM := QPm p hp0 hp1 half n ξ ε A (m - 1) with hQMdef
  have hQM0 : 0 ≤ QM := QPm_nonneg p hp0 hp1 _ _ _ _ _ _
  rw [QP_rec p hp0 hp1 _ _ _ _ _ (Nat.sub_le _ _)]
  have hind : Set.indicator (TaoCollatz.whiteSet n ξ)
      (1 : ℕ × ℤ → ℝ) (half - m, l) = 1 := Set.indicator_of_mem hw 1
  have hatom : ∀ d : ℕ × ℤ,
      (holdP p hp0 hp1 d).toReal *
          QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε
            (half - m + d.1) (l + d.2)
        ≤ (holdP p hp0 hp1 d).toReal *
          (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) := by
    intro d
    rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
    · rw [holdP_zero_of_fst_zero p hp0 hp1 h0, ENNReal.toReal_zero,
        zero_mul, zero_mul]
    · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have h1 : 1 ≤ half - m + d.1 := by omega
      have h2 : half - (m - 1) ≤ half - m + d.1 := by omega
      have hkey := QP_le_QPm p hp0 hp1 half n ξ ε A hA.le hε0 (m - 1)
        (l := l + d.2) h1 h2
      have heq : half - (half - m + d.1) = m - d.1 := by omega
      rwa [heq] at hkey
  have hble : ∀ d : ℕ × ℤ,
      (holdP p hp0 hp1 d).toReal *
          (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM)
        ≤ (holdP p hp0 hp1 d).toReal * QM := by
    intro d
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    calc
      ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM ≤ 1 * QM :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_one_of_one_le_of_nonpos
            (by exact_mod_cast Nat.le_max_right (m - d.1) 1) (by linarith)) hQM0
      _ = QM := one_mul _
  have hsumR : Summable fun d : ℕ × ℤ =>
      (holdP p hp0 hp1 d).toReal *
        (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hQM0))
      hble ((holdP_summable_toReal p hp0 hp1).mul_right QM)
  have hsumL : Summable fun d : ℕ × ℤ =>
      (holdP p hp0 hp1 d).toReal *
        QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε
          (half - m + d.1) (l + d.2) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg
        (QP_nonneg p hp0 hp1 _ _ _ _ _))
      (fun d => (hatom d).trans (hble d))
      ((holdP_summable_toReal p hp0 hp1).mul_right QM)
  have htsum :
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
          QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε
            (half - m + d.1) (l + d.2)
        ≤ Real.exp (ε ^ 3 / 2) * (m : ℝ) ^ (-A) * QM := by
    calc
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
            QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε
              (half - m + d.1) (l + d.2)
          ≤ ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
            (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
        hsumL.tsum_le_tsum hatom hsumR
      _ = ∑' d : ℕ × ℤ,
          ((holdP p hp0 hp1 d).toReal *
            ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)) * QM :=
        tsum_congr fun d => (mul_assoc _ _ _).symm
      _ = (∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
          ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)) * QM := tsum_mul_right
      _ ≤ Real.exp (ε ^ 3 / 2) * (m : ℝ) ^ (-A) * QM :=
        mul_le_mul_of_nonneg_right (hC0 m hm) hQM0
  rw [hind, mul_one]
  calc
    Real.exp (-ε ^ 3) *
          ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
            QP p hp0 hp1 half (TaoCollatz.whiteSet n ξ) ε
              (half - m + d.1) (l + d.2)
        ≤ Real.exp (-ε ^ 3) *
          (Real.exp (ε ^ 3 / 2) * (m : ℝ) ^ (-A) * QM) :=
      mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
    _ = (Real.exp (-ε ^ 3) * Real.exp (ε ^ 3 / 2)) *
        ((m : ℝ) ^ (-A) * QM) := by ring
    _ = Real.exp (-ε ^ 3 / 2) * ((m : ℝ) ^ (-A) * QM) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    _ = Real.exp (-ε ^ 3 / 2) * (m : ℝ) ^ (-A) * QM := by ring

/-- Uniform existential form of tilted Proposition 7.8 Case 1. -/
theorem QP_white_case1 (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∀ p : ℝ, ∀ hp0 : 0 < p, ∀ hp1 : p < 1,
      1 / 5 ≤ p → p ≤ 3 / 5 → ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ,
        (n / 2 - m, l) ∈ TaoCollatz.whiteSet n ξ →
        QP p hp0 hp1 (n / 2) (TaoCollatz.whiteSet n ξ) (TaoCollatz.epsBW : ℝ)
            (n / 2 - m) l
          ≤ Real.exp (-(TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A) *
            QPm p hp0 hp1 (n / 2) n ξ (TaoCollatz.epsBW : ℝ) A (m - 1) :=
  ⟨C_holdP A, QP_white_case1_explicitC A hA⟩

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
