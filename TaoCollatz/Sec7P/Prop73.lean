/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.Case3

/-!
# Proposition 7.3 at `Pascal(p)`, uniformly on `p ∈ [1/5, 3/5]`

This module assembles the tilted Proposition 7.8 (monotonicity of the depth
supremum `QPmFor` at the finer `epsP` scale and white set `whiteSetP`), the
resulting polynomial decay (7.37) of the tilted renewal value `QP`, the two
convention bridges (iid `Pascal(p)` vector ↔ column recursion ↔ `holdP`-average),
and finally the tilted Proposition 7.3 `renewal_white_encountersP`.

## How `p` enters

* Case 1 needs the holding-weight expectation `Σ holdP(d)·max(m−d₁,1)^{−A} ≤
  e^{epsP³/2}·m^{−A}`: the fixed-law core is `δ`-generic
  (`holdP_weight_expect_core_gen`), instantiated here at `δ = e^{epsP³/2} − 1`.
* Cases 2 and 3 are `QP_black_edge_case2` / `QP_black_edge_case3`.
* The renewal bridge uses the one-column self-similarity of `holdP`: the first
  column is a renewal with probability `q(p) = P(b = 3)`, else it contributes a
  `Pascal(p)`-conditioned-`≠ 3` increment and the draw restarts.
-/

namespace TaoCollatz.Sec7P

open scoped ENNReal

/-! ### Case 1 at the finer scale -/

/-- The Case-1 slack at the finer scale: `δ = e^{epsP³/2} − 1`. -/
noncomputable def deltaP : ℝ := Real.exp ((epsP : ℝ) ^ 3 / 2) - 1

theorem deltaP_pos : 0 < deltaP := by
  have hεpos : (0 : ℝ) < (epsP : ℝ) ^ 3 / 2 := by
    have h1 : (0 : ℝ) < (epsP : ℝ) := by exact_mod_cast epsP_pos
    positivity
  have h2 := Real.add_one_le_exp ((epsP : ℝ) ^ 3 / 2)
  unfold deltaP
  linarith

/-- The head-region contraction base at the finer scale. -/
noncomputable def cHoldP (A : ℝ) : ℝ := (1 + deltaP / 3) ^ A⁻¹

theorem one_lt_cHoldP (A : ℝ) (hA : 0 < A) : 1 < cHoldP A := by
  unfold cHoldP
  rw [Real.one_lt_rpow_iff_of_pos (by linarith [deltaP_pos])]
  exact Or.inl ⟨by linarith [deltaP_pos], by positivity⟩

theorem cHoldP_rpow (A : ℝ) (hA : 0 < A) : cHoldP A ^ A = 1 + deltaP / 3 := by
  unfold cHoldP
  rw [← Real.rpow_mul (by linarith [deltaP_pos]), inv_mul_cancel₀ hA.ne', Real.rpow_one]

/-- Uniform middle-tail cutoff for the finer-scale tilted holding expectation. -/
noncomputable def K_holdPfine (A : ℝ) : ℕ :=
  K_geomPWindow (deltaP / 3 * (2 : ℝ) ^ (-A))

/-- Uniform head-region cutoff for the finer-scale tilted holding expectation. -/
noncomputable def M1_holdPfine (A : ℝ) : ℕ :=
  ⌈(K_holdPfine A : ℝ) * cHoldP A / (cHoldP A - 1)⌉₊

/-- Uniform far-tail cutoff for the finer-scale tilted holding expectation. -/
noncomputable def T_holdPfine (A : ℝ) : ℕ :=
  T_powGeomPWindow ⌈A⌉₊ (deltaP / 3 * (3 : ℝ) ^ (-A))

/-- Tao's Case-1 threshold at the finer scale, uniform on the `p` window. -/
noncomputable def C_holdPfine (A : ℝ) : ℕ :=
  K_holdPfine A + M1_holdPfine A + 2 * T_holdPfine A + 4

theorem one_le_C_holdPfine (A : ℝ) : 1 ≤ C_holdPfine A := by
  unfold C_holdPfine
  omega

/-- The tilted Case-1 expectation at the finer slack `e^{epsP³/2}`, with an explicit
threshold independent of `p`. -/
theorem holdP_weight_expect_fine (A : ℝ) (hA : 0 < A) :
    ∀ p : ℝ, ∀ hpL : 1 / 5 ≤ p, ∀ hpU : p ≤ 3 / 5,
      ∀ m : ℕ, C_holdPfine A ≤ m →
        ∑' d : ℕ × ℤ,
            (holdP p (by linarith [hpL]) (by linarith [hpU]) d).toReal *
              ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)
          ≤ Real.exp ((epsP : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A) := by
  have hb2 : (0 : ℝ) < deltaP / 3 * (2 : ℝ) ^ (-A) :=
    mul_pos (by linarith [deltaP_pos]) (Real.rpow_pos_of_pos (by norm_num) _)
  have hb3 : (0 : ℝ) < deltaP / 3 * (3 : ℝ) ^ (-A) :=
    mul_pos (by linarith [deltaP_pos]) (Real.rpow_pos_of_pos (by norm_num) _)
  have hK : holdPSurvivalBound ^ K_holdPfine A < deltaP / 3 * (2 : ℝ) ^ (-A) := by
    unfold K_holdPfine
    exact geomPWindow_lt_at _ hb2
  have hM1 : (K_holdPfine A : ℝ) * cHoldP A / (cHoldP A - 1) ≤ (M1_holdPfine A : ℝ) := by
    unfold M1_holdPfine
    exact Nat.le_ceil _
  have hT : ∀ t : ℕ, T_holdPfine A ≤ t →
      (t : ℝ) ^ ⌈A⌉₊ * holdPSurvivalBound ^ t < deltaP / 3 * (3 : ℝ) ^ (-A) := by
    unfold T_holdPfine
    exact pow_mul_geomPWindow_lt_at _ _ hb3
  intro p hpL hpU m hm
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  exact holdP_weight_expect_core_gen A hA p hp0 hp1 hpL hpU
    (Real.exp ((epsP : ℝ) ^ 3 / 2)) deltaP (cHoldP A) deltaP_pos
    (by unfold deltaP; ring) (one_lt_cHoldP A hA) (cHoldP_rpow A hA)
    (K_holdPfine A) (M1_holdPfine A) (T_holdPfine A) hK hM1 hT m (by
      unfold C_holdPfine at hm
      exact hm)

/-- **Tilted Case 1 of Proposition 7.8 at the finer scale.**  A `whiteSetP` start at
depth `m` contracts by `exp(−epsP³/2)·m^{−A}` against `QPmFor (m−1)`, uniformly for
`p ∈ [1/5, 3/5]`. -/
theorem QP_white_case1P (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ,
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ,
        (n / 2 - m, l) ∈ whiteSetP n ξ →
        QP p (by linarith [hp0]) (by linarith [hp1]) (n / 2) (whiteSetP n ξ) (epsP : ℝ)
            (n / 2 - m) l
          ≤ Real.exp (-(epsP : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A) *
            QPmFor p (by linarith [hp0]) (by linarith [hp1]) (n / 2) (whiteSetP n ξ)
              (epsP : ℝ) A (m - 1) := by
  refine ⟨C_holdPfine A, ?_⟩
  have hC0one := one_le_C_holdPfine A
  intro p hpL hpU
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have hC0 : ∀ m : ℕ, C_holdPfine A ≤ m →
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
          ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)
        ≤ Real.exp ((epsP : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A) := by
    intro m hm
    simpa using holdP_weight_expect_fine A hA p hpL hpU m hm
  intro n ξ _ m hm hmn l hw
  set half := n / 2 with hhalf
  set ε : ℝ := (epsP : ℝ) with hεdef
  have hε0 : (0 : ℝ) ≤ ε := by
    rw [hεdef]
    exact_mod_cast epsP_pos.le
  have hm1 : 1 ≤ m := le_trans hC0one hm
  set QM := QPmFor p hp0 hp1 half (whiteSetP n ξ) ε A (m - 1) with hQMdef
  have hQM0 : 0 ≤ QM := QPmFor_nonneg p hp0 hp1 _ _ _ _ _
  rw [QP_rec p hp0 hp1 _ _ _ _ _ (Nat.sub_le _ _)]
  have hind : Set.indicator (whiteSetP n ξ)
      (1 : ℕ × ℤ → ℝ) (half - m, l) = 1 := Set.indicator_of_mem hw 1
  have hatom : ∀ d : ℕ × ℤ,
      (holdP p hp0 hp1 d).toReal *
          QP p hp0 hp1 half (whiteSetP n ξ) ε
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
      have hkey := QP_le_QPmFor p hp0 hp1 half (whiteSetP n ξ) ε A hA.le hε0 (m - 1)
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
        QP p hp0 hp1 half (whiteSetP n ξ) ε
          (half - m + d.1) (l + d.2) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg
        (QP_nonneg p hp0 hp1 _ _ _ _ _))
      (fun d => (hatom d).trans (hble d))
      ((holdP_summable_toReal p hp0 hp1).mul_right QM)
  have htsum :
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
          QP p hp0 hp1 half (whiteSetP n ξ) ε
            (half - m + d.1) (l + d.2)
        ≤ Real.exp (ε ^ 3 / 2) * (m : ℝ) ^ (-A) * QM := by
    calc
      ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal *
            QP p hp0 hp1 half (whiteSetP n ξ) ε
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
            QP p hp0 hp1 half (whiteSetP n ξ) ε
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

/-! ### The black-edge case split and Proposition 7.8 -/

/-- **The (7.41) edge bound for BLACK starts** at `Pascal(p)` (Cases 2–3): the black
phase point lies in a finer family triangle, its budget is `O(m)` by (7.52), and the
two cases are split at `s = m/log²m`. -/
theorem QP_black_edgeP (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ,
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ,
      1 ≤ n / 2 - m → (n / 2 - m, l) ∉ whiteSetP n ξ →
      QP p (by linarith [hp0]) (by linarith [hp1]) (n / 2) (whiteSetP n ξ) (epsP : ℝ)
          (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) *
          QPmFor p (by linarith [hp0]) (by linarith [hp1]) (n / 2) (whiteSetP n ξ)
            (epsP : ℝ) A (m - 1) := by
  classical
  obtain ⟨C2, hC2⟩ := QP_black_edge_case2 A hA
  obtain ⟨C3, hC3⟩ := QP_black_edge_case3 A hA
  refine ⟨max C2 C3, fun p hp0 hp1 n ξ hξ m hm hmn l h1 hnw => ?_⟩
  obtain ⟨F⟩ := exists_triangleFamilyP n ξ hξ
  have hb : blackP n ξ (n / 2 - m - 1) l := by
    by_contra hw
    exact hnw ⟨h1, hw⟩
  have hmem0 : (n / 2 - m - 1, l) ∈
      {q : ℕ × ℤ | q.1 + 1 ≤ n / 2 ∧ blackP n ξ q.1 q.2} := ⟨by omega, hb⟩
  rw [F.cover] at hmem0
  simp only [Set.mem_iUnion, exists_prop] at hmem0
  obtain ⟨t, ht, hmem⟩ := hmem0
  have hl : l ≤ t.2.1 := hmem.2.1
  set s : ℕ := (t.2.1 - l).toNat with hs
  have hsZ : (s : ℤ) = t.2.1 - l := by omega
  have hbudget : (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 :=
    budgetP_le_of_mem_triangle F ht hmem (by omega)
  rcases le_or_gt (s : ℝ) ((m : ℝ) / Real.log m ^ 2) with hcase | hcase
  · exact hC2 p hp0 hp1 n ξ hξ F m (le_trans (le_max_left _ _) hm) hmn l h1
      t ht hmem s hsZ hcase
  · exact hC3 p hp0 hp1 n ξ hξ F m (le_trans (le_max_right _ _) hm) hmn l h1
      t ht hmem s hsZ hcase hbudget

/-- **Proposition 7.8 (Monotonicity) at `Pascal(p)`**, finer scale: `QPmFor m ≤ QPmFor
(m−1)` for `m` past a threshold chosen before `p`. -/
theorem prop_7_8P (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ,
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      QPmFor p (by linarith [hp0]) (by linarith [hp1]) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A m
        ≤ QPmFor p (by linarith [hp0]) (by linarith [hp1]) (n / 2) (whiteSetP n ξ)
            (epsP : ℝ) A (m - 1) := by
  obtain ⟨C1, hC1⟩ := QP_white_case1P A hA
  obtain ⟨C2, hC2⟩ := QP_black_edgeP A hA
  refine ⟨max (max C1 C2) 1, ?_⟩
  intro p hp0 hp1 n ξ hξ m hm hmn
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  have hmC1 : C1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmC2 : C2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hε0 : (0 : ℝ) ≤ (epsP : ℝ) := by exact_mod_cast epsP_pos.le
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hQM0 : 0 ≤ QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) :=
    QPmFor_nonneg p hp0' hp1' _ _ _ _ _
  have hcancel : (m : ℝ) ^ A * (m : ℝ) ^ (-A) = 1 := by
    rw [← Real.rpow_add hm0, add_neg_cancel, Real.rpow_zero]
  refine Real.iSup_le (fun z => ?_) hQM0
  obtain ⟨⟨p1, l⟩, hp1z, hpm⟩ := z
  have hp1' : 1 ≤ p1 := hp1z
  have hpm' : n / 2 - m ≤ p1 := hpm
  show ((max (n / 2 - p1) 1 : ℕ) : ℝ) ^ A *
      QP p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) p1 l
    ≤ QPmFor p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1)
  rcases eq_or_lt_of_le hpm' with heq | hlt
  · have hp1eq : p1 = n / 2 - m := heq.symm
    have hwt : (max (n / 2 - p1) 1 : ℕ) = m := by omega
    have hedge : QP p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) p1 l
        ≤ (m : ℝ) ^ (-A) * QPmFor p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) := by
      by_cases hw : (p1, l) ∈ whiteSetP n ξ
      · have h := hC1 p hp0 hp1 n ξ hξ m hmC1 hmn l (hp1eq ▸ hw)
        rw [hp1eq]
        calc QP p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) (n / 2 - m) l
            ≤ Real.exp (-(epsP : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A)
              * QPmFor p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) := h
          _ ≤ (m : ℝ) ^ (-A) * QPmFor p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) := by
              apply mul_le_mul_of_nonneg_right _ hQM0
              have hexp : Real.exp (-(epsP : ℝ) ^ 3 / 2) ≤ 1 := by
                rw [Real.exp_le_one_iff]
                have h3 : (0 : ℝ) ≤ (epsP : ℝ) ^ 3 := by positivity
                linarith
              calc Real.exp (-(epsP : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A)
                  ≤ 1 * (m : ℝ) ^ (-A) :=
                    mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hm0.le _)
                _ = (m : ℝ) ^ (-A) := one_mul _
      · exact hp1eq ▸ hC2 p hp0 hp1 n ξ hξ m hmC2 hmn l (by omega) (hp1eq ▸ hw)
    calc ((max (n / 2 - p1) 1 : ℕ) : ℝ) ^ A *
          QP p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) p1 l
        ≤ ((max (n / 2 - p1) 1 : ℕ) : ℝ) ^ A
            * ((m : ℝ) ^ (-A) *
              QPmFor p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1)) :=
          mul_le_mul_of_nonneg_left hedge (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (m : ℝ) ^ A * (m : ℝ) ^ (-A) *
            QPmFor p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) := by
          rw [hwt]; ring
      _ = QPmFor p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (m - 1) := by
          rw [hcancel, one_mul]
  · exact le_QPmFor p hp0' (by linarith) (n / 2) (whiteSetP n ξ) (epsP : ℝ) A hA.le hε0 (m - 1)
      hp1' (by omega)

/-- The elementary induction-base bound (7.39) for the arbitrary-set depth supremum. -/
theorem QPmFor_le_rpow (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) (A : ℝ) (hA : 0 ≤ A)
    (m : ℕ) (hm : 1 ≤ m) :
    QPmFor p hp0 hp1 half W ε A m ≤ (m : ℝ) ^ A := by
  refine Real.iSup_le (fun z => ?_) (Real.rpow_nonneg (Nat.cast_nonneg m) A)
  have hw : ((max (half - z.1.1) 1 : ℕ) : ℝ) ^ A ≤ (m : ℝ) ^ A := by
    apply Real.rpow_le_rpow (by positivity) _ hA
    have hle : half - z.1.1 ≤ m := by
      obtain ⟨-, h2⟩ := z.2
      omega
    exact_mod_cast max_le hle hm
  calc
    ((max (half - z.1.1) 1 : ℕ) : ℝ) ^ A * QP p hp0 hp1 half W ε z.1.1 z.1.2
        ≤ (m : ℝ) ^ A * 1 := by
          apply mul_le_mul hw (QP_le_one p hp0 hp1 _ _ _ hε _ _)
            (QP_nonneg p hp0 hp1 _ _ _ _ _)
          exact Real.rpow_nonneg (Nat.cast_nonneg m) A
    _ = (m : ℝ) ^ A := mul_one _

/-- **Paper (7.37) at `Pascal(p)`**: `QP(j,l) ≤ C·max(⌊n/2⌋ − j, 1)^{−A}`, uniformly in
`n, ξ, j, l` and `p ∈ [1/5, 3/5]`, by forward induction from (7.39) through
Proposition 7.8. -/
theorem QP_polynomial_decayP (A : ℝ) (hA : 0 < A) :
    ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ (j : ℕ) (l : ℤ), 1 ≤ j →
      QP p (by linarith [hp0]) (by linarith [hp1]) (n / 2) (whiteSetP n ξ) (epsP : ℝ) j l
        ≤ C * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
  obtain ⟨C0, hC0⟩ := prop_7_8P A hA
  set Cb := max C0 1 with hCbdef
  have hCb1 : 1 ≤ Cb := le_max_right _ _
  have hCbR : (1 : ℝ) ≤ ((Cb : ℕ) : ℝ) := by exact_mod_cast hCb1
  have hCbA1 : (1 : ℝ) ≤ ((Cb : ℕ) : ℝ) ^ A := by
    calc (1 : ℝ) = (1 : ℝ) ^ A := (Real.one_rpow A).symm
      _ ≤ ((Cb : ℕ) : ℝ) ^ A := Real.rpow_le_rpow zero_le_one hCbR hA.le
  have hCbpos : (0 : ℝ) < ((Cb : ℕ) : ℝ) := by linarith
  refine ⟨((Cb : ℕ) : ℝ) ^ A, Real.rpow_pos_of_pos hCbpos A, ?_⟩
  intro p hp0 hp1 n ξ hξ j l hj
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  have hε0 : (0 : ℝ) ≤ (epsP : ℝ) := by exact_mod_cast epsP_pos.le
  have hQmb : ∀ m : ℕ, 1 ≤ m → m ≤ n / 2 →
      QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) A m ≤ ((Cb : ℕ) : ℝ) ^ A := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro hm1 hmn
      rcases le_or_gt m Cb with hle | hgt
      · calc QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) A m ≤ (m : ℝ) ^ A :=
              QPmFor_le_rpow p hp0' hp1' _ _ _ hε0 A hA.le _ hm1
          _ ≤ ((Cb : ℕ) : ℝ) ^ A :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) hA.le
      · have h78 := hC0 p hp0 hp1 n ξ hξ m (by omega) hmn
        exact le_trans h78 (IH (m - 1) (by omega) (by omega) (by omega))
  rcases Nat.lt_or_ge j (n / 2) with hjlt | hjge
  · have hle := QP_le_QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) A hA.le hε0
      (n / 2 - j) (l := l) hj (by omega)
    calc QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) j l
        ≤ ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A)
            * QPmFor p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) A (n / 2 - j) := hle
      _ ≤ ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) * (((Cb : ℕ) : ℝ) ^ A) :=
          mul_le_mul_of_nonneg_left (hQmb (n / 2 - j) (by omega) (by omega))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = ((Cb : ℕ) : ℝ) ^ A * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := mul_comm _ _
  · have hw : (max (n / 2 - j) 1 : ℕ) = 1 := by omega
    calc QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) j l ≤ 1 :=
          QP_le_one p hp0' hp1' _ _ _ hε0 _ _
      _ ≤ ((Cb : ℕ) : ℝ) ^ A := hCbA1
      _ = ((Cb : ℕ) : ℝ) ^ A * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
          rw [hw, Nat.cast_one, Real.one_rpow, mul_one]

end TaoCollatz.Sec7P
