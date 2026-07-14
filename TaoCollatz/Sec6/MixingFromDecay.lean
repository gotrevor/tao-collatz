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

/-- **Fourier inversion** for the density: `densC Y = N⁻¹ ∑_ξ 𝓕(densC)(ξ)·e(ξ·Y)`. Immediate
from `densC = 𝓕⁻(𝓕 densC)` (`LinearEquiv.symm_apply_apply`) and `ZMod.invDFT_apply`. -/
theorem densC_inversion (n : ℕ) (Y : ZMod (3 ^ n)) :
    densC n Y = (3 ^ n : ℂ)⁻¹ * ∑ ξ, ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y) := by
  have hNcast : ((3 ^ n : ℕ) : ℂ) = (3 ^ n : ℂ) := by push_cast; ring
  have hself : densC n Y = ZMod.dft.symm (ZMod.dft (densC n)) Y := by
    rw [LinearEquiv.symm_apply_apply]
  rw [hself, ZMod.invDFT_apply, smul_eq_mul, hNcast]
  congr 1
  exact Finset.sum_congr rfl (fun ξ _ => by rw [smul_eq_mul, mul_comm])

/-- **Geometric sum over roots of unity**: if `r^K = 1` then `∑_{j<K} rʲ = K` when `r = 1`,
else `0` (the numerator `r^K − 1` vanishes). -/
theorem geom_sum_root_of_pow_eq_one {K : ℕ} (r : ℂ) (hr : r ^ K = 1) :
    ∑ j ∈ Finset.range K, r ^ j = if r = 1 then (K : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  · rw [geom_sum_eq h, hr, sub_self, zero_div]

/-- **Fiber reindexing** (pure combinatorics, no character theory): the `3ᵐ`-fiber of `Y` is
`{Y + t·3ᵐ : t < 3^{n-m}}`, so any function summed over it reindexes to a sum over
`Finset.range (3^{n-m})`. -/
theorem fiber_char_reindex (m n : ℕ) (hmn : m ≤ n) (ξ Y : ZMod (3 ^ n)) :
    ∑ Y' ∈ fiber m n hmn Y, ZMod.stdAddChar (ξ * Y')
      = ∑ t ∈ Finset.range (3 ^ (n - m)),
          ZMod.stdAddChar (ξ * (Y + (t : ZMod (3 ^ n)) * (3 ^ m : ZMod (3 ^ n)))) := by
  sorry

/-- **Coset character sum** (the number-theoretic heart of C10): the additive character summed
over a `3ᵐ`-fiber vanishes unless `ξ` is a low frequency (`3^{n-m} ∣ ξ.val`), in which case it is
`3^{n-m}` times the character at the base point. Route: reindex the fiber as `{Y + t·3ᵐ}`
(`fiber_char_reindex`), split the character `e(ξ·(Y+t·3ᵐ)) = e(ξ·Y)·e(ξ·3ᵐ)ᵗ`, and evaluate the
geometric sum over the `3^{n-m}`-th roots of unity (`geom_sum_root_of_pow_eq_one`). -/
theorem coset_char_sum (m n : ℕ) (hmn : m ≤ n) (ξ Y : ZMod (3 ^ n)) :
    ∑ Y' ∈ fiber m n hmn Y, ZMod.stdAddChar (ξ * Y')
      = (if ξ ∈ lowFreq m n then (3 ^ (n - m) : ℂ) else 0) * ZMod.stdAddChar (ξ * Y) := by
  classical
  set r : ℂ := ZMod.stdAddChar (ξ * (3 ^ m : ZMod (3 ^ n))) with hr_def
  -- `(3:ZMod 3ⁿ)ⁿ = 0`.
  have hpow_zero : (3 : ZMod (3 ^ n)) ^ n = 0 := by
    rw [show (3 : ZMod (3 ^ n)) ^ n = ((3 ^ n : ℕ) : ZMod (3 ^ n)) from by push_cast; ring,
      ZMod.natCast_self]
  -- `rᴷ = 1` for `K = 3^{n-m}`: the exponent `3^{n-m}·(ξ·3ᵐ)` is `ξ·3ⁿ = 0`.
  have hrK : r ^ (3 ^ (n - m)) = 1 := by
    rw [hr_def, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    rw [show ((3 ^ (n - m) : ℕ) : ZMod (3 ^ n)) * (ξ * (3 ^ m : ZMod (3 ^ n))) = 0 from ?_,
      AddChar.map_zero_eq_one]
    rw [show ((3 ^ (n - m) : ℕ) : ZMod (3 ^ n)) = (3 : ZMod (3 ^ n)) ^ (n - m) from by
        push_cast; ring,
      show (3 : ZMod (3 ^ n)) ^ (n - m) * (ξ * (3 ^ m : ZMod (3 ^ n)))
        = ξ * ((3 : ZMod (3 ^ n)) ^ (n - m) * (3 : ZMod (3 ^ n)) ^ m) from by ring,
      ← pow_add, Nat.sub_add_cancel hmn, hpow_zero, mul_zero]
  -- `r = 1 ⟺ ξ` is a low frequency.
  have hlow_iff : (ξ ∈ lowFreq m n) ↔ r = 1 := by
    have hchar : (r = 1) ↔ (ξ * (3 ^ m : ZMod (3 ^ n)) = 0) := by
      rw [hr_def]
      constructor
      · intro h
        exact ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm)
      · intro h; rw [h, AddChar.map_zero_eq_one]
    have hdvd : ∀ v : ℕ, ((3 : ℕ) ^ n ∣ v * 3 ^ m ↔ 3 ^ (n - m) ∣ v) := by
      intro v
      rw [show (3 : ℕ) ^ n = 3 ^ (n - m) * 3 ^ m from by rw [← pow_add, Nat.sub_add_cancel hmn]]
      exact Nat.mul_dvd_mul_iff_right (by positivity : 0 < 3 ^ m)
    rw [lowFreq, Finset.mem_filter, hchar]
    simp only [Finset.mem_univ, true_and]
    rw [show ξ * (3 ^ m : ZMod (3 ^ n)) = ((ξ.val * 3 ^ m : ℕ) : ZMod (3 ^ n)) from by
        push_cast [ZMod.natCast_zmod_val]; ring,
      ZMod.natCast_eq_zero_iff]
    exact (hdvd ξ.val).symm
  -- Reindex, split the character, and sum the geometric series.
  rw [fiber_char_reindex m n hmn ξ Y]
  have hsplit : ∀ t : ℕ,
      ZMod.stdAddChar (ξ * (Y + (t : ZMod (3 ^ n)) * (3 ^ m : ZMod (3 ^ n))))
        = ZMod.stdAddChar (ξ * Y) * r ^ t := by
    intro t
    rw [hr_def, mul_add, AddChar.map_add_eq_mul, ← AddChar.map_nsmul_eq_pow]
    congr 2
    rw [nsmul_eq_mul]; ring
  rw [Finset.sum_congr rfl (fun t _ => hsplit t), ← Finset.mul_sum,
    geom_sum_root_of_pow_eq_one r hrK]
  by_cases h : ξ ∈ lowFreq m n
  · rw [if_pos h, if_pos (hlow_iff.mp h)]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun hr1 => h (hlow_iff.mpr hr1)), mul_zero, zero_mul]

/-- **The conditional average is the low-frequency projection**: substituting Fourier inversion
into the fiber average and applying `coset_char_sum` collapses it to the low-frequency inverse DFT
(`3^{m-n}·3^{n-m} = 1` cancels). -/
theorem condAvgC_eq_lowSum (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (3 ^ n)) :
    condAvgC m n hmn Y
      = (3 ^ n : ℂ)⁻¹ * ∑ ξ ∈ lowFreq m n,
          ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y) := by
  classical
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  -- `3^{m-n}·3^{n-m} = 1`.
  have hcancel : (3 : ℂ) ^ ((m : ℤ) - (n : ℤ)) * (3 : ℂ) ^ (n - m) = 1 := by
    rw [← zpow_natCast (3 : ℂ) (n - m), ← zpow_add₀ h3, Nat.cast_sub hmn,
      show (m : ℤ) - (n : ℤ) + ((n : ℤ) - (m : ℤ)) = 0 from by ring, zpow_zero]
  -- Substitute Fourier inversion into the fiber average and swap the sums.
  have hfib : ∑ Y' ∈ fiber m n hmn Y, densC n Y'
      = (3 ^ n : ℂ)⁻¹ * ∑ ξ, ZMod.dft (densC n) ξ
          * ∑ Y' ∈ fiber m n hmn Y, ZMod.stdAddChar (ξ * Y') := by
    calc ∑ Y' ∈ fiber m n hmn Y, densC n Y'
        = ∑ Y' ∈ fiber m n hmn Y, (3 ^ n : ℂ)⁻¹
            * ∑ ξ, ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y') :=
          Finset.sum_congr rfl (fun Y' _ => densC_inversion n Y')
      _ = (3 ^ n : ℂ)⁻¹ * ∑ Y' ∈ fiber m n hmn Y,
            ∑ ξ, ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y') := by rw [Finset.mul_sum]
      _ = (3 ^ n : ℂ)⁻¹ * ∑ ξ,
            ∑ Y' ∈ fiber m n hmn Y, ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y') := by
          rw [Finset.sum_comm]
      _ = (3 ^ n : ℂ)⁻¹ * ∑ ξ, ZMod.dft (densC n) ξ
            * ∑ Y' ∈ fiber m n hmn Y, ZMod.stdAddChar (ξ * Y') := by
          refine congrArg _ (Finset.sum_congr rfl (fun ξ _ => ?_))
          rw [Finset.mul_sum]
  -- Collapse the coset character sum: only low frequencies survive.
  have hcoset : ∀ ξ : ZMod (3 ^ n),
      ZMod.dft (densC n) ξ * ∑ Y' ∈ fiber m n hmn Y, ZMod.stdAddChar (ξ * Y')
        = if ξ ∈ lowFreq m n then
            (3 : ℂ) ^ (n - m) * (ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y)) else 0 := by
    intro ξ
    rw [coset_char_sum m n hmn ξ Y]
    split_ifs with h <;> ring
  rw [condAvgC, hfib, Finset.sum_congr rfl (fun ξ (_ : ξ ∈ Finset.univ) => hcoset ξ),
    Finset.sum_ite_mem_eq, ← Finset.mul_sum]
  rw [show (3 : ℂ) ^ ((m : ℤ) - (n : ℤ)) * ((3 ^ n : ℂ)⁻¹
        * ((3 : ℂ) ^ (n - m) * ∑ ξ ∈ lowFreq m n,
            ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y)))
      = ((3 : ℂ) ^ ((m : ℤ) - (n : ℤ)) * (3 : ℂ) ^ (n - m)) * ((3 ^ n : ℂ)⁻¹
        * ∑ ξ ∈ lowFreq m n, ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y)) from by ring,
    hcancel, one_mul]

/-- **The Fourier-inversion crux** (Remark 1.18): the `3ᵐ`-scale deviation is the high-frequency
inverse DFT. The conditional average is the projection onto the low frequencies (`condAvgC_eq_lowSum`),
so `devC Y = c Y − avg(Y) = N⁻¹·(∑_all − ∑_low) = N⁻¹ ∑_{ξ∈highFreq} 𝓕c(ξ)·e(ξ·Y)`. -/
theorem devC_eq_highfreq_invDFT (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (3 ^ n)) :
    devC m n hmn Y
      = (3 ^ n : ℂ)⁻¹ * ∑ ξ ∈ highFreq m n,
          ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y) := by
  have hsplit : ∑ ξ ∈ highFreq m n, ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y)
      = (∑ ξ, ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y))
        - ∑ ξ ∈ lowFreq m n, ZMod.dft (densC n) ξ * ZMod.stdAddChar (ξ * Y) := by
    rw [highFreq, lowFreq, eq_sub_iff_add_eq, add_comm, Finset.sum_filter_add_sum_filter_not]
  rw [devC, densC_inversion n Y, condAvgC_eq_lowSum m n hmn Y, ← mul_sub, ← hsplit]

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
