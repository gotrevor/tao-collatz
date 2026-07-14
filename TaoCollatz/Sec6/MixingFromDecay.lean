import TaoCollatz.Fourier.ZMod3
import TaoCollatz.Fourier.Parseval
import TaoCollatz.Syracuse.SyracRV
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §6: fine-scale mixing from character decay (node C10) — Prop 1.14

Paper anchor: Tao 2019 §6, Proposition 1.14 (deduced from Prop 1.17 via Plancherel).

`fine_scale_mixing` (Prop 1.14) is decomposed along the paper's Plancherel route into two
sub-lemmas (both `sorry`, the genuine §6 analytic content):

* `osc_le_sqrt_highfreq` — **Cauchy–Schwarz + Parseval bridge**: the `3ᵐ`-scale oscillation
  is bounded by the `√` of the high-frequency `L²` Fourier mass. Uses `ZMod.dft_parseval`.
* `highfreq_l2_le` — **decay of the high-frequency mass**: bounded by `C·m^{-A}` for every `A`,
  from Prop 1.17 (`charFn_decay`, PROVED) via the `syracZ_map_cast` projection reduction.

The reduction of `fine_scale_mixing` to these two IS proved here (invoking the second at the
doubled exponent `2A`, so the `√` restores the target `m^{-A}`). Route: `PENDING_WORK` fruit-7.
-/

open scoped BigOperators

namespace TaoCollatz

/-- The `Syrac(ℤ/3ⁿℤ)` density as a `ℂ`-valued function, for the discrete Fourier transform. -/
noncomputable def densC (n : ℕ) : ZMod (3 ^ n) → ℂ := fun Y => ((syracZ n Y).toReal : ℂ)

/-- The high frequencies at scale `(n, m)`: those `ξ` NOT constant on `3ᵐ`-cosets, i.e. whose
`3`-adic valuation is `< n - m` (equivalently `¬ 3^{n-m} ∣ ξ.val`). These are exactly the modes
killed by the `3ᵐ`-scale conditional average in `osc`. -/
noncomputable def highFreq (m n : ℕ) : Finset (ZMod (3 ^ n)) :=
  Finset.univ.filter (fun ξ : ZMod (3 ^ n) => ¬ (3 ^ (n - m) ∣ ξ.val))

/-- **§6 Cauchy–Schwarz + Parseval bridge** (Remark 1.18 route): the `3ᵐ`-scale oscillation of
the Syracuse density is at most the `√` of its high-frequency `L²` Fourier mass. The `3ᵐ`-scale
conditional average is the projection onto the low frequencies `{ξ : 3^{n-m} ∣ ξ.val}`, so the
deviation is the inverse-DFT over `highFreq`; Cauchy–Schwarz + `ZMod.dft_parseval` gives the
bound. (Genuine §6 content; route in `PENDING_WORK` fruit-7.) -/
theorem osc_le_sqrt_highfreq (m n : ℕ) (hmn : m ≤ n) :
    osc m n hmn (fun Y => (syracZ n Y).toReal)
      ≤ Real.sqrt (∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n) ξ‖ ^ 2) := by
  sorry

/-- **§6 high-frequency decay**: the high-frequency `L²` Fourier mass of the Syracuse density
decays faster than any polynomial in `m`. For `ξ = 3ʲ·η` (`η` coprime to 3, `j < n - m`) the
projection compatibility `syracZ_map_cast` reduces `ĉₙ(ξ)` to level `n - j ≥ m + 1`, where
Prop 1.17 (`charFn_decay`) supplies the decay; summing over the `< n - m` scales (Parseval per
level bounding the count) gives the bound. (Genuine §6 content; route in `PENDING_WORK` fruit-7.) -/
theorem highfreq_l2_le (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      (∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n) ξ‖ ^ 2) ≤ C * (m : ℝ) ^ (-A) := by
  sorry

/-- **Proposition 1.14** (fine-scale mixing): the `Syrac(ℤ/3ⁿℤ)` density oscillates
little at scale `3ᵐ`, uniformly with polynomial decay `m^{-A}` for every `A`.
Proved from `osc_le_sqrt_highfreq` + `highfreq_l2_le` (the latter at exponent `2A`). -/
theorem fine_scale_mixing (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A) := by
  obtain ⟨C, hC, hB⟩ := highfreq_l2_le (2 * A) (by positivity)
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun n m hmn hm => ?_⟩
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hsqrt_pow : Real.sqrt ((m : ℝ) ^ (-(2 * A))) = (m : ℝ) ^ (-A) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hm0]
    congr 1
    ring
  calc osc m n hmn (fun Y => ((syracZ n) Y).toReal)
      ≤ Real.sqrt (∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n) ξ‖ ^ 2) :=
        osc_le_sqrt_highfreq m n hmn
    _ ≤ Real.sqrt (C * (m : ℝ) ^ (-(2 * A))) := Real.sqrt_le_sqrt (hB n m hmn hm)
    _ = Real.sqrt C * Real.sqrt ((m : ℝ) ^ (-(2 * A))) := Real.sqrt_mul hC.le _
    _ = Real.sqrt C * (m : ℝ) ^ (-A) := by rw [hsqrt_pow]

end TaoCollatz
