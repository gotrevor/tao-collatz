import TaoCollatz.Sec6.MixingMain
import TaoCollatz.Sec6.MixingError
import TaoCollatz.Sec6.MixingRegime

/-! # §6: fine-scale mixing from character decay (node C10) — Proposition 1.14 -/

namespace TaoCollatz

/-- **(6.2)–(6.10): the §6 conditioning core** (C10, obligations 1+2+3), in the high regime
`0.9n ≤ m ≤ n` (encoded `9n ≤ 10m`) and for `n` sufficiently large. -/
theorem osc_syracZ_high_regime (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, ∀ hmn : m ≤ n, n₀ ≤ n → 9 * n ≤ 10 * m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A) := by
  obtain ⟨Cm, hCm, n1, hmain⟩ := osc_mainHigh_bound A hA
  obtain ⟨Ce, hCe, n2, herr⟩ := error_l1_high_bound A hA
  refine ⟨2 * max Cm Ce, by positivity, max n1 n2, fun n m hmn hn0 hreg => ?_⟩
  have hn1 : n1 ≤ n := le_trans (le_max_left _ _) hn0
  have hn2 : n2 ≤ n := le_trans (le_max_right _ _) hn0
  have hmpow : (0 : ℝ) ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg (by positivity) _
  have hcomb := osc_syracZ_split_le m n hmn (mainHigh A n) (max Cm Ce * (m : ℝ) ^ (-A))
    (le_trans (hmain n m hmn hn1 hreg) (by gcongr; exact le_max_left _ _))
    (le_trans (herr n m hmn hn2 hreg) (by gcongr; exact le_max_right _ _))
  calc osc m n hmn (fun Y => ((syracZ n) Y).toReal)
      ≤ max Cm Ce * (m : ℝ) ^ (-A) + max Cm Ce * (m : ℝ) ^ (-A) := hcomb
    _ = 2 * max Cm Ce * (m : ℝ) ^ (-A) := by ring

/-- **Proposition 1.14** (fine-scale mixing): the `Syrac(ℤ/3ⁿℤ)` density oscillates
little at scale `3ᵐ`, uniformly with polynomial decay `m^{-A}` for every `A`. -/
theorem fine_scale_mixing (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A) :=
  osc_syracZ_regime_telescope A hA (fun B hB => osc_syracZ_high_regime B hB)

end TaoCollatz
