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

/-! ### Bridge, vector side: the iid `Pascal(p)` expectation is a column recursion -/

open Classical in
/-- **The column recursion** at `Pascal(p)` (D6 form of the paper's (7.28) product,
resolved one Pascal column at a time): from column `j` with prefix sum `l`, draw
`b ~ Pascal(p)` for column `j+1`; a renewal point (`b = 3`) landing in `W` contributes
the `exp(−ε³)` damping.  `1` past the strip. -/
noncomputable def RcolP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) : ℕ → ℤ → ℝ
  | j, l =>
    if half ≤ j then 1
    else ∑' b : ℕ,
      (pascalP p hp0 hp1.le b).toReal
        * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W then Real.exp (-(ε ^ 3)) else 1)
        * RcolP p hp0 hp1 half W ε (j + 1) (l + b)
  termination_by j _ => half - j
  decreasing_by omega

open Classical in
/-- **Bridge, vector side, generalized** for the induction at `Pascal(p)`. -/
theorem bridge_vectorP_gen (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (m half j : ℕ) (l : ℤ), half - j = m →
      (PMF.iid (pascalP p hp0 hp1.le) m).expect (fun v =>
          Real.exp (-(ε ^ 3) *
            ((Finset.univ.filter fun i : Fin m =>
              v i = 3 ∧ ((j + (i : ℕ) + 1 : ℕ), l + (pre v ((i : ℕ) + 1) : ℤ)) ∈ W).card
              : ℝ)))
        = RcolP p hp0 hp1 half W ε j l := by
  set pas := pascalP p hp0 hp1.le with hpasdef
  intro m
  induction m with
  | zero =>
    intro half j l hm
    rw [PMF.expect_iid_zero, RcolP, if_pos (by omega : half ≤ j)]
    simp
  | succ m IH =>
    intro half j l hm
    rw [PMF.expect_iid_succ pas m _ (fun v => (Real.exp_pos _).le)
      (fun v => by
        rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        exact mul_nonneg (pow_nonneg hε 3) (Nat.cast_nonneg _))]
    have hinner : ∀ a : ℕ,
        ((PMF.iid pas m).expect fun w =>
          Real.exp (-(ε ^ 3) *
            ((Finset.univ.filter fun i : Fin (m + 1) =>
              (Fin.cons a w : Fin (m + 1) → ℕ) i = 3
                ∧ ((j + (i : ℕ) + 1 : ℕ),
                    l + (pre (Fin.cons a w) ((i : ℕ) + 1) : ℤ)) ∈ W).card : ℝ)))
        = (if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W
            then Real.exp (-(ε ^ 3)) else 1)
          * RcolP p hp0 hp1 half W ε (j + 1) (l + (a : ℤ)) := by
      intro a
      rw [← IH half (j + 1) (l + (a : ℤ)) (by omega)]
      have hcount : ∀ w : Fin m → ℕ,
          ((Finset.univ.filter fun i : Fin (m + 1) =>
            (Fin.cons a w : Fin (m + 1) → ℕ) i = 3
              ∧ ((j + (i : ℕ) + 1 : ℕ),
                  l + (pre (Fin.cons a w) ((i : ℕ) + 1) : ℤ)) ∈ W).card
          = (if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W then 1 else 0)
            + (Finset.univ.filter fun i : Fin m =>
                w i = 3 ∧ ((j + 1 + (i : ℕ) + 1 : ℕ),
                  (l + (a : ℤ)) + (pre w ((i : ℕ) + 1) : ℤ)) ∈ W).card) := by
        intro w
        rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have h2 : (j + ((i.succ : Fin (m + 1)) : ℕ) + 1 : ℕ)
            = j + 1 + (i : ℕ) + 1 := by
          rw [Fin.val_succ]; omega
        have h3 : l + (pre (Fin.cons a w) (((i.succ : Fin (m + 1)) : ℕ) + 1) : ℤ)
            = (l + (a : ℤ)) + (pre w ((i : ℕ) + 1) : ℤ) := by
          rw [Fin.val_succ, pre_cons]
          push_cast
          ring
        have hiff : ((Fin.cons a w : Fin (m + 1) → ℕ) i.succ = 3
            ∧ ((j + ((i.succ : Fin (m + 1)) : ℕ) + 1 : ℕ),
                l + (pre (Fin.cons a w) (((i.succ : Fin (m + 1)) : ℕ) + 1) : ℤ)) ∈ W)
            ↔ (w i = 3 ∧ ((j + 1 + (i : ℕ) + 1 : ℕ),
                (l + (a : ℤ)) + (pre w ((i : ℕ) + 1) : ℤ)) ∈ W) := by
          rw [show ((Fin.cons a w : Fin (m + 1) → ℕ) i.succ) = w i
            from Fin.cons_succ (α := fun _ => ℕ) a w i, h2, h3]
        exact if_congr hiff rfl rfl
      unfold PMF.expect
      dsimp only
      rw [← tsum_mul_left]
      refine tsum_congr fun w => ?_
      rw [hcount w]
      push_cast
      rw [mul_add, Real.exp_add]
      have hhead : Real.exp (-(ε ^ 3) *
            ((if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W then (1 : ℝ) else 0)))
          = (if a = 3 ∧ ((j + 1 : ℕ), l + (a : ℤ)) ∈ W
              then Real.exp (-(ε ^ 3)) else 1) := by
        split_ifs
        · rw [mul_one]
        · rw [mul_zero, Real.exp_zero]
      rw [hhead]
      ring
    rw [tsum_congr fun a => by rw [hinner a]]
    rw [RcolP, if_neg (by omega : ¬ half ≤ j)]
    exact tsum_congr fun a => (mul_assoc _ _ _).symm

open Classical in
/-- **Bridge, vector side** at `Pascal(p)`: the iid `Pascal(p)` vector expectation of the
damped finer-white-encounter count equals the column recursion at `whiteSetP`/`epsP`. -/
theorem bridge_vectorP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n ξ : ℕ) :
    (PMF.iid (pascalP p hp0 hp1.le) (n / 2)).expect (fun b =>
        Real.exp (-((epsP : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ whiteP n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)))
      = RcolP p hp0 hp1 (n / 2) (whiteSetP n ξ) (epsP : ℝ) 0 0 := by
  classical
  have hε : (0 : ℝ) ≤ (epsP : ℝ) := by exact_mod_cast epsP_pos.le
  rw [← bridge_vectorP_gen p hp0 hp1 (whiteSetP n ξ) (epsP : ℝ) hε (n / 2) (n / 2) 0 0
    (by omega)]
  refine congrArg _ (funext fun v => ?_)
  have hcard : (Finset.univ.filter fun i : Fin (n / 2) =>
        v i = 3 ∧ whiteP n ξ (i : ℕ) ((pre v ((i : ℕ) + 1) : ℤ))).card
      = (Finset.univ.filter fun i : Fin (n / 2) =>
        v i = 3 ∧ ((0 + (i : ℕ) + 1 : ℕ),
          (0 : ℤ) + (pre v ((i : ℕ) + 1) : ℤ)) ∈ whiteSetP n ξ).card := by
    refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
    refine and_congr_right fun _ => ?_
    rw [show (0 : ℤ) + (pre v ((i : ℕ) + 1) : ℤ) = (pre v ((i : ℕ) + 1) : ℤ)
      from zero_add _]
    unfold whiteSetP
    rw [Set.mem_ofPred_eq, show (0 + (i : ℕ) + 1) - 1 = (i : ℕ) from by omega]
    constructor
    · exact fun h => ⟨by omega, h⟩
    · exact fun h => h.2
  rw [hcard]

/-! ### Bridge, renewal side: the column recursion is a `holdP`-average of `QP` -/

/-- Generic expansion of a `holdP`-expectation through the `bind`/`map` structure. -/
theorem holdP_tsum_expand (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (G : ℕ × ℤ → ℝ≥0∞) :
    ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * G d
      = ∑' k : ℕ, geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
          (pairThreeProb_le_one p hp0 hp1) k *
          ∑' v : Fin (k - 1) → ℕ,
            ((pascalNe3P p hp0 hp1.le).iid (k - 1)) v * G (k, (3 : ℤ) + ∑ i, (v i : ℤ)) := by
  rw [holdP, PMF.tsum_bind_mul]
  exact tsum_congr fun k => by rw [PMF.tsum_map_mul]

/-- One-column self-similarity of `holdP` (paper (7.29), tsum form over `ℝ≥0∞`): a
`holdP` draw is `(1,3)` with probability `q(p)`, else the first column contributes
`(1, b)` with `b ~ Pascal(p)` conditioned `≠ 3` and the draw restarts.  The `b ≠ 3`
Pascal mass is `(1 − q(p))·pascalNe3P` exactly. -/
theorem holdP_tsum_step (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (g : ℕ × ℤ → ℝ≥0∞) :
    ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * g d
      = ENNReal.ofReal (pairThreeProb p) * g (1, 3)
        + ∑' b : ℕ, (if b = 3 then 0 else pascalP p hp0 hp1.le b)
            * ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * g (d.1 + 1, d.2 + b) := by
  classical
  set q : ℝ := pairThreeProb p with hqdef
  have hq0 : 0 < q := pairThreeProb_pos p hp0 hp1
  have hq1 : q < 1 := pairThreeProb_lt_one p hp0 hp1
  set geo := geomP (pairThreeProb p) (pairThreeProb_pos p hp0 hp1)
    (pairThreeProb_le_one p hp0 hp1) with hgeodef
  set pne := pascalNe3P p hp0 hp1.le with hpnedef
  have hgq0 : geo 0 = 0 := by
    rw [hgeodef, geomP_apply]; simp
  have hgq1 : geo 1 = ENNReal.ofReal q := by
    rw [hgeodef, geomP_apply, hqdef]; norm_num
  have hgqs : ∀ k : ℕ, geo (k + 2) = ENNReal.ofReal (1 - q) * geo (k + 1) := by
    intro k
    rw [hgeodef, geomP_apply, geomP_apply, if_neg (by omega), if_neg (by omega),
      ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    rw [show k + 2 - 1 = (k + 1 - 1) + 1 by omega, pow_succ]
    ring
  have hpas : ∀ b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pascalP p hp0 hp1.le b)
      = ENNReal.ofReal (1 - q) * pne b := by
    intro b
    have hfilt : pne b = {b | b ≠ 3}.indicator (pascalP p hp0 hp1.le) b *
        (∑' a', {b | b ≠ 3}.indicator (pascalP p hp0 hp1.le) a')⁻¹ :=
      PMF.filter_apply _ b
    rw [hfilt, pascalP_ne_three_mass]
    have hind : {b | b ≠ 3}.indicator (pascalP p hp0 hp1.le) b
        = if b = 3 then 0 else pascalP p hp0 hp1.le b := by
      by_cases hb : b = 3
      · subst hb; simp
      · simp [hb]
    rw [hind]
    have hne0 : ENNReal.ofReal (1 - q) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
    have hnetop : ENNReal.ofReal (1 - q) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [← mul_assoc, mul_right_comm, ENNReal.mul_inv_cancel hne0 hnetop, one_mul]
  -- LHS: expand holdP, peel k = 1 and k ≥ 2
  have hL1 : ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * g d
      = ENNReal.ofReal q * g (1, 3)
        + ∑' k : ℕ, geo (k + 2) * ∑' v : Fin (k + 1) → ℕ,
            (pne.iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, (v i : ℤ)) := by
    rw [holdP_tsum_expand p hp0 hp1 g, tsum_eq_zero_add' ENNReal.summable,
      hgq0, zero_mul, zero_add,
      tsum_eq_zero_add' ENNReal.summable]
    congr 1
    · rw [hgq1]
      congr 1
      exact (PMF.tsum_iid_zero_mul pne
        (fun v => g (1, (3 : ℤ) + ∑ i, (v i : ℤ)))).trans (by simp)
  -- RHS inner sums, in the same normal form
  have hR : ∀ b : ℕ, ∑' d : ℕ × ℤ, holdP p hp0 hp1 d * g (d.1 + 1, d.2 + (b : ℤ))
      = ∑' k : ℕ, geo (k + 1) * ∑' w : Fin k → ℕ,
          (pne.iid k) w * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (b : ℤ)) := by
    intro b
    rw [holdP_tsum_expand p hp0 hp1 fun d => g (d.1 + 1, d.2 + (b : ℤ)),
      tsum_eq_zero_add' ENNReal.summable, hgq0, zero_mul, zero_add]
    rfl
  -- the tail of hL1 equals the b-sum of hR through one iid-peel + Fubini
  have hL2 : ∑' k : ℕ, geo (k + 2) * ∑' v : Fin (k + 1) → ℕ,
        (pne.iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, (v i : ℤ))
      = ∑' b : ℕ, ENNReal.ofReal (1 - q) * pne b
          * ∑' k : ℕ, geo (k + 1) * ∑' w : Fin k → ℕ,
              (pne.iid k) w
                * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (b : ℤ)) := by
    have hpeel : ∀ k : ℕ, ∑' v : Fin (k + 1) → ℕ,
          (pne.iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, (v i : ℤ))
        = ∑' a : ℕ, pne a * ∑' w : Fin k → ℕ,
            (pne.iid k) w
              * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (a : ℤ)) := by
      intro k
      rw [PMF.tsum_iid_succ_mul pne k
        (fun v => g (k + 2, (3 : ℤ) + ∑ i, (v i : ℤ)))]
      refine tsum_congr fun a => ?_
      congr 1
      refine tsum_congr fun w => ?_
      congr 1
      rw [show ((3 : ℤ) + ∑ i : Fin (k + 1), ((Fin.cons a w : Fin (k + 1) → ℕ) i : ℤ))
          = (3 : ℤ) + (∑ i, (w i : ℤ)) + (a : ℤ) from by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        ring]
    calc ∑' k : ℕ, geo (k + 2) * ∑' v : Fin (k + 1) → ℕ,
          (pne.iid (k + 1)) v * g (k + 2, (3 : ℤ) + ∑ i, (v i : ℤ))
        = ∑' k : ℕ, ∑' a : ℕ, ENNReal.ofReal (1 - q) * pne a
            * (geo (k + 1) * ∑' w : Fin k → ℕ,
                (pne.iid k) w
                  * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (a : ℤ))) := by
          refine tsum_congr fun k => ?_
          rw [hpeel k, hgqs k, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun a => by ring
      _ = ∑' a : ℕ, ∑' k : ℕ, ENNReal.ofReal (1 - q) * pne a
            * (geo (k + 1) * ∑' w : Fin k → ℕ,
                (pne.iid k) w
                  * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (a : ℤ))) :=
          ENNReal.tsum_comm
      _ = ∑' a : ℕ, ENNReal.ofReal (1 - q) * pne a
            * ∑' k : ℕ, geo (k + 1) * ∑' w : Fin k → ℕ,
                (pne.iid k) w
                  * g (k + 1 + 1, (3 : ℤ) + (∑ i, (w i : ℤ)) + (a : ℤ)) :=
          tsum_congr fun a => ENNReal.tsum_mul_left
  rw [hL1, hL2]
  congr 1
  exact tsum_congr fun b => by rw [hpas b, hR b]

/-- Real-valued corollary of `holdP_tsum_step` for `[0,1]`-valued observables. -/
theorem holdP_tsum_step_real (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : ℕ × ℤ → ℝ) (hf0 : ∀ d, 0 ≤ f d) (hf1 : ∀ d, f d ≤ 1) :
    ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal * f d
      = pairThreeProb p * f (1, 3)
        + ∑' b : ℕ, (if b = 3 then 0 else (pascalP p hp0 hp1.le b).toReal)
            * ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal * f (d.1 + 1, d.2 + b) := by
  classical
  set hold := holdP p hp0 hp1 with hholddef
  set pas := pascalP p hp0 hp1.le with hpasdef
  have hq0 : 0 ≤ pairThreeProb p := (pairThreeProb_pos p hp0 hp1).le
  have hstep := holdP_tsum_step p hp0 hp1 fun d => ENNReal.ofReal (f d)
  have hcv : ∀ F : ℕ × ℤ → ℕ × ℤ,
      (∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (F d))).toReal
        = ∑' d : ℕ × ℤ, (hold d).toReal * f (F d) := by
    intro F
    rw [ENNReal.tsum_toReal_eq
      (fun d => ENNReal.mul_ne_top (hold.apply_ne_top d) ENNReal.ofReal_ne_top)]
    exact tsum_congr fun d => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf0 _)]
  have hcv0 : (∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f d)).toReal
      = ∑' d : ℕ × ℤ, (hold d).toReal * f d := hcv id
  have hcvb : ∀ b : ℕ,
      (∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))).toReal
        = ∑' d : ℕ × ℤ, (hold d).toReal * f (d.1 + 1, d.2 + (b : ℤ)) :=
    fun b => hcv fun d => (d.1 + 1, d.2 + (b : ℤ))
  have hTle : ∀ b : ℕ,
      ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ))) ≤ 1 := by
    intro b
    calc ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))
        ≤ ∑' d : ℕ × ℤ, hold d * 1 :=
          ENNReal.tsum_le_tsum fun d => mul_le_mul_right
            (ENNReal.ofReal_le_one.mpr (hf1 _)) _
      _ = 1 := by rw [tsum_congr fun d => mul_one (hold d), hold.tsum_coe]
  have hcb : ∀ b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pas b) ≤ pas b := by
    intro b; split_ifs <;> simp
  have htail_ne : (∑' b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pas b)
      * ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))) ≠ ∞ := by
    refine ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) ?_
    calc ∑' b : ℕ, (if b = 3 then (0 : ℝ≥0∞) else pas b)
          * ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f (d.1 + 1, d.2 + (b : ℤ)))
        ≤ ∑' b : ℕ, pas b * 1 :=
          ENNReal.tsum_le_tsum fun b => mul_le_mul' (hcb b) (hTle b)
      _ = 1 := by rw [tsum_congr fun b => mul_one (pas b), pas.tsum_coe]
  have h := congrArg ENNReal.toReal hstep
  rw [hcv0, ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) htail_ne,
    ENNReal.toReal_mul, ENNReal.tsum_toReal_eq (fun b => ENNReal.mul_ne_top
      (ne_top_of_le_ne_top (PMF.apply_ne_top _ _) (hcb b))
      (ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) (hTle b)))] at h
  rw [h, ENNReal.toReal_ofReal (hf0 _), ENNReal.toReal_ofReal hq0]
  congr 1
  refine tsum_congr fun b => ?_
  rw [ENNReal.toReal_mul, hcvb b]
  congr 1
  split_ifs <;> simp

/-- **Bridge, renewal side** at `Pascal(p)` ((7.27) ≡ (7.28), D6 form): the column
recursion equals the `holdP`-jump average of `QP`.  Downward induction on `half − j`;
the inductive step is `holdP_tsum_step_real` matched against `RcolP`'s one-column
unfolding and `QP_rec` at the renewal landing `b = 3`. -/
theorem bridge_renewalP (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) (l : ℤ) :
    RcolP p hp0 hp1 half W ε j l
      = ∑' d : ℕ × ℤ, (holdP p hp0 hp1 d).toReal * QP p hp0 hp1 half W ε (j + d.1) (l + d.2) := by
  classical
  set hold := holdP p hp0 hp1 with hholddef
  set pas := pascalP p hp0 hp1.le with hpasdef
  have hQ0 := QP_nonneg p hp0 hp1 half W ε
  have hQ1 := QP_le_one p hp0 hp1 half W ε hε
  have hSterm : ∀ (j' : ℕ) (l' : ℤ) (d : ℕ × ℤ),
      (hold d).toReal * QP p hp0 hp1 half W ε (j' + d.1) (l' + d.2) ≤ (hold d).toReal := by
    intro j' l' d
    calc (hold d).toReal * QP p hp0 hp1 half W ε (j' + d.1) (l' + d.2)
        ≤ (hold d).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hQ1 _ _) ENNReal.toReal_nonneg
      _ = (hold d).toReal := mul_one _
  have hSnn : ∀ (j' : ℕ) (l' : ℤ) (d : ℕ × ℤ),
      0 ≤ (hold d).toReal * QP p hp0 hp1 half W ε (j' + d.1) (l' + d.2) :=
    fun j' l' d => mul_nonneg ENNReal.toReal_nonneg (hQ0 _ _)
  have hSsum : ∀ (j' : ℕ) (l' : ℤ),
      Summable fun d : ℕ × ℤ => (hold d).toReal * QP p hp0 hp1 half W ε (j' + d.1) (l' + d.2) :=
    fun j' l' => Summable.of_nonneg_of_le (hSnn j' l') (hSterm j' l')
      (holdP_summable_toReal p hp0 hp1)
  have hSle : ∀ (j' : ℕ) (l' : ℤ),
      ∑' d : ℕ × ℤ, (hold d).toReal * QP p hp0 hp1 half W ε (j' + d.1) (l' + d.2) ≤ 1 :=
    fun j' l' => le_trans
      ((hSsum j' l').tsum_le_tsum (hSterm j' l') (holdP_summable_toReal p hp0 hp1))
      (holdP_tsum_toReal p hp0 hp1).le
  have hSnn' : ∀ (j' : ℕ) (l' : ℤ),
      0 ≤ ∑' d : ℕ × ℤ, (hold d).toReal * QP p hp0 hp1 half W ε (j' + d.1) (l' + d.2) :=
    fun j' l' => tsum_nonneg (hSnn j' l')
  have hp3 : (pas 3).toReal = pairThreeProb p := by
    rw [hpasdef, pascalP_apply_three]; rfl
  have hdamp01 : ∀ (P : Prop) [Decidable P],
      0 ≤ (if P then Real.exp (-(ε ^ 3)) else 1)
        ∧ (if P then Real.exp (-(ε ^ 3)) else 1) ≤ 1 := by
    intro P _
    constructor
    · split_ifs <;> [exact (Real.exp_pos _).le; exact zero_le_one]
    · split_ifs
      · rw [Real.exp_le_one_iff, neg_nonpos]; positivity
      · exact le_refl 1
  have key : ∀ n j l, half - j = n → RcolP p hp0 hp1 half W ε j l
      = ∑' d : ℕ × ℤ, (hold d).toReal * QP p hp0 hp1 half W ε (j + d.1) (l + d.2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro j l hn
      rcases Nat.lt_or_ge j half with hj | hj
      · rw [RcolP, if_neg (by omega : ¬ half ≤ j)]
        have hIH : ∀ b : ℕ, RcolP p hp0 hp1 half W ε (j + 1) (l + (b : ℤ))
            = ∑' d : ℕ × ℤ, (hold d).toReal
                * QP p hp0 hp1 half W ε (j + 1 + d.1) (l + (b : ℤ) + d.2) :=
          fun b => IH (half - (j + 1)) (by omega) _ _ rfl
        have hfr := holdP_tsum_step_real p hp0 hp1
          (fun d => QP p hp0 hp1 half W ε (j + d.1) (l + d.2))
          (fun d => hQ0 _ _) (fun d => hQ1 _ _)
        rw [hfr]
        have hterm_eq : ∀ b : ℕ,
            (pas b).toReal
              * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W
                  then Real.exp (-(ε ^ 3)) else 1)
              * RcolP p hp0 hp1 half W ε (j + 1) (l + (b : ℤ))
            = (pas b).toReal
              * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W
                  then Real.exp (-(ε ^ 3)) else 1)
              * ∑' d : ℕ × ℤ, (hold d).toReal
                  * QP p hp0 hp1 half W ε (j + 1 + d.1) (l + (b : ℤ) + d.2) :=
          fun b => by rw [hIH b]
        rw [tsum_congr hterm_eq]
        have hsummable : Summable fun b : ℕ =>
            (pas b).toReal
              * (if b = 3 ∧ ((j + 1 : ℕ), l + (b : ℤ)) ∈ W
                  then Real.exp (-(ε ^ 3)) else 1)
              * ∑' d : ℕ × ℤ, (hold d).toReal
                  * QP p hp0 hp1 half W ε (j + 1 + d.1) (l + (b : ℤ) + d.2) := by
          refine Summable.of_nonneg_of_le
            (fun b => mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (hdamp01 _).1)
              (hSnn' _ _))
            (fun b => ?_)
            (ENNReal.summable_toReal pas.tsum_coe_ne_top)
          calc (pas b).toReal * _ * _
              ≤ (pas b).toReal * 1 * 1 :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hdamp01 _).2
                  ENNReal.toReal_nonneg) (hSle _ _) (hSnn' _ _)
                  (by positivity)
            _ = (pas b).toReal := by ring
        rw [hsummable.tsum_eq_add_tsum_ite 3]
        congr 1
        · simp only [Nat.cast_ofNat]
          have hrec := QP_rec p hp0 hp1 half W ε (j + 1) (l + 3) (by omega)
          by_cases hW : ((j + 1 : ℕ), l + (3 : ℤ)) ∈ W
          · rw [hp3, if_pos ⟨trivial, hW⟩, hrec, Set.indicator_of_mem hW,
              Pi.one_apply, mul_one, mul_assoc]
          · rw [hp3, if_neg (fun h => hW h.2), hrec, Set.indicator_of_notMem hW,
              mul_zero, Real.exp_zero, one_mul, mul_assoc, one_mul]
        · refine tsum_congr fun b => ?_
          by_cases hb3 : b = 3
          · rw [if_pos hb3, if_pos hb3, zero_mul]
          · rw [if_neg hb3, if_neg hb3,
              if_neg (fun h => hb3 h.1), mul_one]
            congr 1
            refine tsum_congr fun d => ?_
            congr 2
            · omega
            · ring
      · rw [RcolP, if_pos hj]
        symm
        calc ∑' d : ℕ × ℤ, (hold d).toReal * QP p hp0 hp1 half W ε (j + d.1) (l + d.2)
            = ∑' d : ℕ × ℤ, (hold d).toReal := by
              refine tsum_congr fun d => ?_
              rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
              · rw [hholddef, holdP_zero_of_fst_zero p hp0 hp1 h0, ENNReal.toReal_zero,
                  zero_mul]
              · rw [QP_boundary p hp0 hp1 _ _ _ _ _ (by omega), mul_one]
          _ = 1 := holdP_tsum_toReal p hp0 hp1
  exact key _ j l rfl

/-! ### Proposition 7.3 at `Pascal(p)` -/

open Classical in
/-- **Proposition 7.3 at `Pascal(p)`** (finitized, D6 form), uniformly on
`p ∈ [1/5, 3/5]`: the expected damping factor `exp(−epsP³ · #finer white encounters)`
over the paired valuation vector `b ~ Pascal(p)^{⌊n/2⌋}` decays super-polynomially.
Composes the two bridges, (7.37) `QP_polynomial_decayP`, and the Case-1 holding-weight
expectation (any slack suffices here).  The constant is chosen before `p`. -/
theorem renewal_white_encountersP (A : ℝ) (hA : 0 < A) :
    ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ → 1 ≤ n →
      (PMF.iid (pascalP p (by linarith) (by linarith)) (n / 2)).expect (fun b =>
        Real.exp (-((epsP : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ whiteP n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)))
        ≤ C * (n : ℝ) ^ (-A) := by
  obtain ⟨C0, hC00, hC0⟩ := QP_polynomial_decayP A hA
  obtain ⟨C1, hC11, hC1⟩ := holdP_weight_expect A hA
  -- constants: below n₀ := 2·C1 + 2 use the trivial bound E ≤ 1 ≤ n₀^A·n^{-A};
  -- above, the chain gives C0·exp(ε³/2)·3^A·n^{-A}.
  obtain ⟨n0, hn0def⟩ : ∃ n0 : ℕ, n0 = 2 * C1 + 2 := ⟨_, rfl⟩
  have hn0pos : (0 : ℝ) < (n0 : ℝ) := by
    rw [hn0def]; exact_mod_cast (by omega : 0 < 2 * C1 + 2)
  refine ⟨max ((n0 : ℝ) ^ A) (C0 * Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A),
    lt_max_iff.mpr (Or.inl (Real.rpow_pos_of_pos hn0pos A)), ?_⟩
  intro p hp0 hp1 n ξ hξ hn
  have hp0' : 0 < p := by linarith
  have hp1' : p < 1 := by linarith
  set pas := pascalP p hp0' hp1'.le with hpasdef
  set hold := holdP p hp0' hp1' with hholddef
  have hε0 : (0 : ℝ) ≤ (epsP : ℝ) := by exact_mod_cast epsP_pos.le
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hE1 : (PMF.iid pas (n / 2)).expect (fun b =>
      Real.exp (-((epsP : ℝ) ^ 3) *
        ((Finset.univ.filter fun j : Fin (n / 2) =>
          b j = 3 ∧ whiteP n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ))) ≤ 1 := by
    unfold PMF.expect
    have hterm : ∀ b : Fin (n / 2) → ℕ,
        ((PMF.iid pas (n / 2)) b).toReal *
          Real.exp (-((epsP : ℝ) ^ 3) *
            ((Finset.univ.filter fun j : Fin (n / 2) =>
              b j = 3 ∧ whiteP n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ))
          ≤ ((PMF.iid pas (n / 2)) b).toReal := by
      intro b
      have hle1 : Real.exp (-((epsP : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ whiteP n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        positivity
      calc ((PMF.iid pas (n / 2)) b).toReal * _ ≤ _ * 1 :=
            mul_le_mul_of_nonneg_left hle1 ENNReal.toReal_nonneg
        _ = ((PMF.iid pas (n / 2)) b).toReal := mul_one _
    have hsum : Summable fun b : Fin (n / 2) → ℕ => ((PMF.iid pas (n / 2)) b).toReal :=
      ENNReal.summable_toReal (PMF.iid pas (n / 2)).tsum_coe_ne_top
    have hsumf : Summable fun b : Fin (n / 2) → ℕ =>
        ((PMF.iid pas (n / 2)) b).toReal *
          Real.exp (-((epsP : ℝ) ^ 3) *
            ((Finset.univ.filter fun j : Fin (n / 2) =>
              b j = 3 ∧ whiteP n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)) :=
      Summable.of_nonneg_of_le
        (fun b => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hterm hsum
    calc ∑' b, ((PMF.iid pas (n / 2)) b).toReal * _
        ≤ ∑' b, ((PMF.iid pas (n / 2)) b).toReal := hsumf.tsum_le_tsum hterm hsum
      _ = 1 := by
          rw [← ENNReal.tsum_toReal_eq (fun b => ((PMF.iid pas (n / 2)).apply_ne_top b)),
            (PMF.iid pas (n / 2)).tsum_coe, ENNReal.toReal_one]
  rcases lt_or_ge n n0 with hsmall | hbig
  · calc (PMF.iid pas (n / 2)).expect _ ≤ 1 := hE1
      _ ≤ (n0 : ℝ) ^ A * (n : ℝ) ^ (-A) := by
          have h1 : (n : ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hsmall.le
          have h2 : (1 : ℝ) = (n : ℝ) ^ A * (n : ℝ) ^ (-A) := by
            rw [← Real.rpow_add hn0R, add_neg_cancel, Real.rpow_zero]
          rw [h2]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hn0R.le h1 hA.le) (Real.rpow_nonneg hn0R.le _)
      _ ≤ max ((n0 : ℝ) ^ A) (C0 * Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A)
            * (n : ℝ) ^ (-A) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hn0R.le _)
  · have hhalf1 : C1 ≤ n / 2 := by omega
    have hhalfpos : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by
      have h : 1 ≤ n / 2 := le_trans hC11 hhalf1
      exact_mod_cast h
    rw [bridge_vectorP p hp0' hp1' n ξ,
      bridge_renewalP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) hε0 0 0]
    have hpt : ∀ d : ℕ × ℤ,
        (hold d).toReal * QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) (0 + d.1) (0 + d.2)
          ≤ (hold d).toReal * (C0 * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)) := by
      intro d
      rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
      · rw [hholddef, holdP_zero_of_fst_zero p hp0' hp1' h0, ENNReal.toReal_zero, zero_mul,
          zero_mul]
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have h := hC0 p hp0 hp1 n ξ hξ (0 + d.1) (0 + d.2) (by omega)
        simpa using h
    have hnn : ∀ d : ℕ × ℤ,
        0 ≤ (hold d).toReal *
          QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) (0 + d.1) (0 + d.2) :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (QP_nonneg p hp0' hp1' _ _ _ _ _)
    have hwle : ∀ d : ℕ × ℤ, ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 := fun d =>
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast Nat.le_max_right (n / 2 - d.1) 1) (by linarith)
    have hsumw : Summable fun d : ℕ × ℤ =>
        (hold d).toReal * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (fun d => by
          calc (hold d).toReal * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)
              ≤ (hold d).toReal * 1 :=
                mul_le_mul_of_nonneg_left (hwle d) ENNReal.toReal_nonneg
            _ = (hold d).toReal := mul_one _)
        (holdP_summable_toReal p hp0' hp1')
    have hsumCw : Summable fun d : ℕ × ℤ =>
        (hold d).toReal * (C0 * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
      (hsumw.mul_left C0).congr fun d => by ring
    have hsumQ : Summable fun d : ℕ × ℤ =>
        (hold d).toReal *
          QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) (0 + d.1) (0 + d.2) :=
      Summable.of_nonneg_of_le hnn
        (fun d => by
          calc (hold d).toReal *
                QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) (0 + d.1) (0 + d.2)
              ≤ (hold d).toReal * 1 :=
                mul_le_mul_of_nonneg_left (QP_le_one p hp0' hp1' _ _ _ hε0 _ _)
                  ENNReal.toReal_nonneg
            _ = (hold d).toReal := mul_one _)
        (holdP_summable_toReal p hp0' hp1')
    have htail := hC1 p hp0 hp1 (n / 2) hhalf1
    calc ∑' d : ℕ × ℤ,
          (hold d).toReal * QP p hp0' hp1' (n / 2) (whiteSetP n ξ) (epsP : ℝ) (0 + d.1) (0 + d.2)
        ≤ ∑' d : ℕ × ℤ,
            (hold d).toReal * (C0 * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
          hsumQ.tsum_le_tsum hpt hsumCw
      _ = C0 * ∑' d : ℕ × ℤ,
            (hold d).toReal * ((max (n / 2 - d.1) 1 : ℕ) : ℝ) ^ (-A) := by
          rw [← tsum_mul_left]
          exact tsum_congr fun d => by ring
      _ ≤ C0 * (Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * ((n / 2 : ℕ) : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_left htail hC00.le
      _ ≤ C0 * Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A * (n : ℝ) ^ (-A) := by
          have h3 : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
            have h : n ≤ 3 * (n / 2) := by omega
            exact_mod_cast h
          have hstep : ((n / 2 : ℕ) : ℝ) ^ (-A) ≤ (3 : ℝ) ^ A * (n : ℝ) ^ (-A) := by
            have h1 : (n : ℝ) ^ (-A) ≥ (3 * ((n / 2 : ℕ) : ℝ)) ^ (-A) :=
              Real.rpow_le_rpow_of_nonpos hn0R h3 (by linarith)
            have h2 : (3 * ((n / 2 : ℕ) : ℝ)) ^ (-A)
                = (3 : ℝ) ^ (-A) * ((n / 2 : ℕ) : ℝ) ^ (-A) :=
              Real.mul_rpow (by norm_num) hhalfpos.le
            have h4 : ((n / 2 : ℕ) : ℝ) ^ (-A)
                = (3 : ℝ) ^ A * ((3 : ℝ) ^ (-A) * ((n / 2 : ℕ) : ℝ) ^ (-A)) := by
              rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 3),
                add_neg_cancel, Real.rpow_zero, one_mul]
            rw [h4]
            calc (3 : ℝ) ^ A * ((3 : ℝ) ^ (-A) * ((n / 2 : ℕ) : ℝ) ^ (-A))
                = (3 : ℝ) ^ A * (3 * ((n / 2 : ℕ) : ℝ)) ^ (-A) := by rw [h2]
              _ ≤ (3 : ℝ) ^ A * (n : ℝ) ^ (-A) :=
                  mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)
          calc C0 * (Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * ((n / 2 : ℕ) : ℝ) ^ (-A))
              = C0 * Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * ((n / 2 : ℕ) : ℝ) ^ (-A) := by
                ring
            _ ≤ C0 * Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * ((3 : ℝ) ^ A * (n : ℝ) ^ (-A)) :=
                mul_le_mul_of_nonneg_left hstep (by positivity)
            _ = C0 * Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A * (n : ℝ) ^ (-A) := by
                ring
      _ ≤ max ((n0 : ℝ) ^ A) (C0 * Real.exp ((TaoCollatz.epsBW : ℝ) ^ 3 / 2) * (3 : ℝ) ^ A)
            * (n : ℝ) ^ (-A) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hn0R.le _)

end TaoCollatz.Sec7P
