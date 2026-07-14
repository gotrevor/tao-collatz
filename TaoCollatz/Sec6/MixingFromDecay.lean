import TaoCollatz.Fourier.ZMod3
import TaoCollatz.Fourier.Parseval
import TaoCollatz.Syracuse.SyracRV
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev

/-!
# §6: fine-scale mixing from character decay (node C10) — Prop 1.14

Paper anchor: Tao 2019 §6, Proposition 1.14 (deduced from Prop 1.17 via Plancherel).

`fine_scale_mixing` (Prop 1.14) is decomposed along the paper's Plancherel route.

## Cauchy–Schwarz + Parseval bridge (`osc_le_sqrt_highfreq`)

Write `N := 3ⁿ`, `c := densC n` the (real) density as a `ℂ`-valued function, and
`devC Y := c Y − avg(Y)` where `avg(Y)` is the `3ᵐ`-scale conditional average (the mean of `c`
over the `castHom`-fiber of `Y`). The proof splits into four machine-checked steps:

* `osc_eq_sum_norm_devC` — `osc = ∑_Y ‖devC Y‖` (the `L¹` deviation; **proved**, a cast).
* Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq` — `(∑ ‖devC‖)² ≤ N·∑ ‖devC‖²` (**proved inline**).
* `sum_norm_sq_devC_eq` — `∑_Y ‖devC Y‖² = N⁻¹·∑_{highFreq} ‖𝓕c(ξ)‖²` (**Parseval**, from the
  inversion identity below; `sorry`).
* `devC_eq_highfreq_invDFT` — `devC Y = N⁻¹ ∑_{ξ∈highFreq} 𝓕c(ξ)·e(ξ·Y)` (the genuine crux: the
  `3ᵐ`-conditional average is the low-frequency projection, so the deviation is the high-frequency
  inverse DFT; reduces to the coset character sum `coset_char_sum`; `sorry`).

Then `osc = ∑‖devC‖ = √((∑‖devC‖)²) ≤ √(N·∑‖devC‖²) = √(N·N⁻¹·H) = √H`, i.e. `osc_le_sqrt_highfreq`.

## High-frequency decay (`highfreq_l2_le`)

`∑_{highFreq} ‖𝓕c(ξ)‖² ≤ C·m^{-A}` from Prop 1.17 (`charFn_decay`) via `syracZ_map_cast`; `sorry`.

Route: `PENDING_WORK` fruit-8.
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

/-- The low frequencies at scale `(n, m)`: `{ξ : 3^{n-m} ∣ ξ.val}`, complementary to `highFreq`.
These are the modes constant on `3ᵐ`-cosets; the `3ᵐ`-conditional average is the projection here. -/
noncomputable def lowFreq (m n : ℕ) : Finset (ZMod (3 ^ n)) :=
  Finset.univ.filter (fun ξ : ZMod (3 ^ n) => (3 ^ (n - m) ∣ ξ.val))

/-- The `3ᵐ`-scale fiber of `Y`: the `castHom`-preimage class `{Y' : π Y' = π Y}`. -/
noncomputable def fiber (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (3 ^ n)) : Finset (ZMod (3 ^ n)) :=
  Finset.univ.filter (fun Y' : ZMod (3 ^ n) =>
    ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y'
      = ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y)

/-- The complex `3ᵐ`-scale conditional average of the density at `Y`. -/
noncomputable def condAvgC (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (3 ^ n)) : ℂ :=
  (3 : ℂ) ^ ((m : ℤ) - (n : ℤ)) * ∑ Y' ∈ fiber m n hmn Y, densC n Y'

/-- The complex deviation of the density from its `3ᵐ`-scale conditional average. -/
noncomputable def devC (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (3 ^ n)) : ℂ :=
  densC n Y - condAvgC m n hmn Y

/-- The oscillation functional equals the `L¹` norm of the (complex) deviation. A cast:
the density and its average are real, so each summand's `|·|` is the `ℂ`-norm of `devC`. -/
theorem osc_eq_sum_norm_devC (m n : ℕ) (hmn : m ≤ n) :
    osc m n hmn (fun Y => (syracZ n Y).toReal) = ∑ Y, ‖devC m n hmn Y‖ := by
  rw [osc]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  simp only [devC, condAvgC, densC]
  have hcast : ((syracZ n Y).toReal : ℂ)
        - (3 : ℂ) ^ ((m : ℤ) - (n : ℤ))
            * ∑ Y' ∈ fiber m n hmn Y, ((syracZ n Y').toReal : ℂ)
      = (((syracZ n Y).toReal
          - (3 : ℝ) ^ ((m : ℤ) - (n : ℤ))
              * ∑ Y' ∈ fiber m n hmn Y, (syracZ n Y').toReal : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, fiber]

/-- **The Fourier-inversion crux** (Remark 1.18): the `3ᵐ`-scale deviation is the high-frequency
inverse DFT. The conditional average is the projection onto the low frequencies
`{ξ : 3^{n-m} ∣ ξ.val}` (those `ξ` constant on `3ᵐ`-cosets, by the coset character sum
`coset_char_sum`), so `devC Y = c Y − avg(Y) = N⁻¹ ∑_{ξ∈highFreq} 𝓕c(ξ)·e(ξ·Y)`. -/
theorem devC_eq_highfreq_invDFT (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (3 ^ n)) :
    devC m n hmn Y
      = (3 ^ n : ℂ)⁻¹ * ∑ ξ ∈ highFreq m n,
          ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y) := by
  sorry

/-- **Parseval `L²` identity for the deviation**: `∑_Y ‖devC Y‖² = N⁻¹·∑_{highFreq} ‖𝓕c(ξ)‖²`.
From `devC_eq_highfreq_invDFT` (`devC = 𝓕⁻ g`, `g` the high-frequency restriction of `𝓕c`) and
`ZMod.dft_parseval`. -/
theorem sum_norm_sq_devC_eq (m n : ℕ) (hmn : m ≤ n) :
    ∑ Y, ‖devC m n hmn Y‖ ^ 2
      = (3 ^ n : ℝ)⁻¹ * ∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n) ξ‖ ^ 2 := by
  classical
  -- `g` = the high-frequency restriction of the DFT of the density.
  set g : ZMod (3 ^ n) → ℂ :=
    fun ξ => if ξ ∈ highFreq m n then ZMod.dft (densC n) ξ else 0 with hg
  have hNcast : ((3 ^ n : ℕ) : ℂ) = (3 ^ n : ℂ) := by push_cast; ring
  have hRcast : ((3 ^ n : ℕ) : ℝ) = (3 ^ n : ℝ) := by push_cast; ring
  have hN : (3 ^ n : ℝ) ≠ 0 := by positivity
  -- Step A: the deviation is the inverse DFT of `g`.
  have hsum : ∀ Y : ZMod (3 ^ n), (∑ ξ, ZMod.stdAddChar (ξ * Y) • g ξ)
      = ∑ ξ ∈ highFreq m n, ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y) := by
    intro Y
    simp only [hg, smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem_eq]
    exact Finset.sum_congr rfl (fun ξ _ => mul_comm _ _)
  have hdev : ∀ Y : ZMod (3 ^ n), devC m n hmn Y = ZMod.dft.symm g Y := by
    intro Y
    rw [devC_eq_highfreq_invDFT m n hmn Y, ZMod.invDFT_apply, smul_eq_mul, hNcast, hsum Y]
  -- Step B: the `g`-mass equals the high-frequency mass.
  have hgpt : ∀ ξ, ‖g ξ‖ ^ 2
      = if ξ ∈ highFreq m n then ‖ZMod.dft (densC n) ξ‖ ^ 2 else 0 := by
    intro ξ; simp only [hg]; split_ifs <;> simp
  have hgsum : ∑ ξ, ‖g ξ‖ ^ 2 = ∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n) ξ‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun ξ _ => hgpt ξ), Finset.sum_ite_mem_eq]
  -- Step C: Parseval on `𝓕⁻ g`.
  have hpars := ZMod.dft_parseval (ZMod.dft.symm g)
  rw [LinearEquiv.apply_symm_apply, hgsum, hRcast] at hpars
  -- hpars : ∑ξ∈highFreq, ‖𝓕(densC)ξ‖² = (3^n:ℝ) * ∑ j, ‖𝓕⁻ g j‖²
  have hLHS : ∑ Y, ‖devC m n hmn Y‖ ^ 2 = ∑ Y, ‖ZMod.dft.symm g Y‖ ^ 2 :=
    Finset.sum_congr rfl (fun Y _ => by rw [hdev Y])
  rw [hLHS, hpars, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- **§6 Cauchy–Schwarz + Parseval bridge** (Remark 1.18 route): the `3ᵐ`-scale oscillation of
the Syracuse density is at most the `√` of its high-frequency `L²` Fourier mass. Proved from
`osc_eq_sum_norm_devC`, the Cauchy–Schwarz inequality `sq_sum_le_card_mul_sum_sq`, and the
Parseval `L²` identity `sum_norm_sq_devC_eq`. -/
theorem osc_le_sqrt_highfreq (m n : ℕ) (hmn : m ≤ n) :
    osc m n hmn (fun Y => (syracZ n Y).toReal)
      ≤ Real.sqrt (∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n) ξ‖ ^ 2) := by
  rw [osc_eq_sum_norm_devC]
  set D := ∑ Y, ‖devC m n hmn Y‖ with hD
  set H := ∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n) ξ‖ ^ 2 with hH
  have hN : (3 ^ n : ℝ) ≠ 0 := by positivity
  have hcard : ((Finset.univ : Finset (ZMod (3 ^ n))).card : ℝ) = (3 ^ n : ℝ) := by
    rw [Finset.card_univ, ZMod.card]; push_cast; ring
  have hcs : D ^ 2 ≤ (3 ^ n : ℝ) * ∑ Y, ‖devC m n hmn Y‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod (3 ^ n))))
      (f := fun Y => ‖devC m n hmn Y‖)
    rwa [hcard] at this
  have key : D ^ 2 ≤ H := by
    calc D ^ 2 ≤ (3 ^ n : ℝ) * ∑ Y, ‖devC m n hmn Y‖ ^ 2 := hcs
      _ = (3 ^ n : ℝ) * ((3 ^ n : ℝ)⁻¹ * H) := by rw [sum_norm_sq_devC_eq]
      _ = H := by field_simp
  have hnn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc D = Real.sqrt (D ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt H := Real.sqrt_le_sqrt key

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
