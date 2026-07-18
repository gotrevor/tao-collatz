import TaoCollatz.Sec6.MixingMain
import TaoCollatz.Sec6.MixingError
import TaoCollatz.Sec6.MixingRegime

/-! # §6: fine-scale mixing from character decay (node C10) — Proposition 1.14 -/

namespace TaoCollatz

/-- The high-regime constant/cutoff of `osc_syracZ_high_regime`, symbolic (big-C
campaign, step 2): main arm `C_oscMainHigh A`, error arm `6`. -/
noncomputable def C_oscHigh (A : ℝ) : ℝ := 2 * max (C_oscMainHigh A) 6

theorem C_oscHigh_pos (A : ℝ) : 0 < C_oscHigh A := by
  unfold C_oscHigh
  have := C_oscMainHigh_pos A
  positivity

/-- The high-regime cutoff of `osc_syracZ_high_regime`, symbolic (big-C campaign, step 2). -/
noncomputable def N_oscHigh (A : ℝ) : ℕ := max (N_oscMainHigh A) (N_probGlobalGood A)

/-- **(6.2)–(6.10): the §6 conditioning core** (C10, obligations 1+2+3), in the high regime
`0.9n ≤ m ≤ n` (encoded `9n ≤ 10m`) and for `n` sufficiently large.
`_at` sibling at `C_oscHigh A`/`N_oscHigh A` (big-C campaign, step 2). -/
theorem osc_syracZ_high_regime_at (A : ℝ) (hA : 0 < A) :
    ∀ n m : ℕ, ∀ hmn : m ≤ n, N_oscHigh A ≤ n → 9 * n ≤ 10 * m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C_oscHigh A * (m : ℝ) ^ (-A) := by
  have hCm : (0 : ℝ) < C_oscMainHigh A := C_oscMainHigh_pos A
  have hCe : (0 : ℝ) < 6 := by norm_num
  have hmain := osc_mainHigh_bound_at A hA
  have herr := error_l1_high_bound_at A hA
  unfold C_oscHigh N_oscHigh
  set Cm : ℝ := C_oscMainHigh A with hCmdef
  set Ce : ℝ := (6 : ℝ) with hCedef
  set n1 : ℕ := N_oscMainHigh A with hn1def
  set n2 : ℕ := N_probGlobalGood A with hn2def
  intro n m hmn hn0 hreg
  have hn1 : n1 ≤ n := le_trans (le_max_left _ _) hn0
  have hn2 : n2 ≤ n := le_trans (le_max_right _ _) hn0
  have hmpow : (0 : ℝ) ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg (by positivity) _
  have hcomb := osc_syracZ_split_le m n hmn (mainHigh A n) (max Cm Ce * (m : ℝ) ^ (-A))
    (le_trans (hmain n m hmn hn1 hreg) (by gcongr; exact le_max_left _ _))
    (le_trans (herr n m hmn hn2 hreg) (by gcongr; exact le_max_right _ _))
  calc osc m n hmn (fun Y => ((syracZ n) Y).toReal)
      ≤ max Cm Ce * (m : ℝ) ^ (-A) + max Cm Ce * (m : ℝ) ^ (-A) := hcomb
    _ = 2 * max Cm Ce * (m : ℝ) ^ (-A) := by ring

/-- **(6.2)–(6.10): the §6 conditioning core**, original `∃`-form: delegates to the
`_at` sibling at `C_oscHigh A`/`N_oscHigh A` (big-C campaign, step 2). -/
theorem osc_syracZ_high_regime (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, ∀ hmn : m ≤ n, n₀ ≤ n → 9 * n ≤ 10 * m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A) :=
  ⟨C_oscHigh A, C_oscHigh_pos A, N_oscHigh A, osc_syracZ_high_regime_at A hA⟩

/-- **The Proposition 1.14 constant**, symbolic (big-C campaign, step 2): the
telescope constant at the explicit high-regime pair (`C_oscHigh (A+2)`,
`N_oscHigh (A+2)`). -/
noncomputable def C_fineScale (A : ℝ) : ℝ :=
  2 * ((max 9 (N_oscHigh (A + 2)) : ℕ) : ℝ) ^ A + C_oscHigh (A + 2) * S_zeta2

theorem C_fineScale_pos (A : ℝ) : 0 < C_fineScale A := by
  unfold C_fineScale
  have h9 : (0 : ℝ) < ((max 9 (N_oscHigh (A + 2)) : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ max 9 (N_oscHigh (A + 2)) := le_trans (by norm_num) (le_max_left _ _)
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one this
  have h1 := mul_nonneg (C_oscHigh_pos (A + 2)).le S_zeta2_nonneg
  nlinarith [Real.rpow_pos_of_pos h9 A]

/-- **Proposition 1.14** (fine-scale mixing), `_at` sibling (big-C campaign, step 2):
the telescope at the explicit high-regime constants. -/
theorem fine_scale_mixing_at (A : ℝ) (hA : 0 < A) :
    ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C_fineScale A * (m : ℝ) ^ (-A) := by
  have h := osc_syracZ_regime_telescope_at A hA (C_oscHigh (A + 2)) (C_oscHigh_pos (A + 2))
    (N_oscHigh (A + 2)) (osc_syracZ_high_regime_at (A + 2) (by linarith))
  unfold C_fineScale
  exact h

/-- **Proposition 1.14** (fine-scale mixing): the `Syrac(ℤ/3ⁿℤ)` density oscillates
little at scale `3ᵐ`, uniformly with polynomial decay `m^{-A}` for every `A`. -/
theorem fine_scale_mixing (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A) :=
  ⟨C_fineScale A, C_fineScale_pos A, fine_scale_mixing_at A hA⟩

end TaoCollatz
