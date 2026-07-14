import TaoCollatz.Fourier.ZMod3
import TaoCollatz.Fourier.Parseval
import TaoCollatz.Syracuse.SyracRV
import TaoCollatz.Sec7.Decay
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev

/-!
# §6: fine-scale mixing from character decay (node C10) — Prop 1.14

Paper anchor: Tao 2019 §6, Proposition 1.14 (deduced from Prop 1.17 via Plancherel).

`fine_scale_mixing` (Prop 1.14) is decomposed along the paper's Plancherel route.

## Cauchy–Schwarz + Parseval bridge (`osc_le_sqrt_highfreq`) — PROVED, axiom-clean

Write `N := 3ⁿ`, `c := densC n` the (real) density as a `ℂ`-valued function, and
`devC Y := c Y − avg(Y)` where `avg(Y)` is the `3ᵐ`-scale conditional average (the mean of `c`
over the `castHom`-fiber of `Y`). The proof is now fully machine-checked:

* `osc_eq_sum_norm_devC` — `osc = ∑_Y ‖devC Y‖` (the `L¹` deviation; a cast).
* Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq` — `(∑ ‖devC‖)² ≤ N·∑ ‖devC‖²` (inline).
* `sum_norm_sq_devC_eq` — `∑_Y ‖devC Y‖² = N⁻¹·∑_{highFreq} ‖𝓕c(ξ)‖²` (Parseval, `devC = 𝓕⁻ g`).
* `devC_eq_highfreq_invDFT` — `devC Y = N⁻¹ ∑_{ξ∈highFreq} 𝓕c(ξ)·e(ξ·Y)`, from `densC_inversion`
  + `condAvgC_eq_lowSum` (the `3ᵐ`-conditional average is the low-frequency projection).
* `condAvgC_eq_lowSum` ← `coset_char_sum` ← `fiber_char_reindex` + `geom_sum_root_of_pow_eq_one`
  (fiber `= {Y+t·3ᵐ}`, additive character splits, geometric sum over `3^{n-m}`-th roots of unity).

Then `osc = ∑‖devC‖ = √((∑‖devC‖)²) ≤ √(N·∑‖devC‖²) = √(N·N⁻¹·H) = √H`, i.e. `osc_le_sqrt_highfreq`.

## High-frequency decay — REFUTED for raw `syracZ` (see the route-finding block below)

The naive `∑_{highFreq} ‖𝓕c(ξ)‖² ≤ C·m^{-A}` is FALSE for the raw density (it equals
`Q(n)−Q(m)` which grows ≈ `0.46·(n−m)`, verified by exact DP). `fine_scale_mixing` must go
through Tao's §6 conditioning; `sorry` pending that apparatus. Route: `PENDING_WORK` fruit-8.
-/

open scoped BigOperators

namespace TaoCollatz

/-- Complexification of a real density `c : ZMod (3ⁿ) → ℝ`, for the discrete Fourier transform.
Generalized (brick d) from the raw `syracZ` density to an arbitrary real `c`: the whole
Cauchy–Schwarz/Parseval bridge below never uses `syracZ`-ness, only that the density is real. This
lets the bridge apply to Tao's §6 *conditioned* density `g_{n,k,l}`. -/
noncomputable def densC (n : ℕ) (c : ZMod (3 ^ n) → ℝ) : ZMod (3 ^ n) → ℂ := fun Y => ((c Y : ℝ) : ℂ)

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

/-- The complex `3ᵐ`-scale conditional average of the density `c` at `Y`. -/
noncomputable def condAvgC (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) (Y : ZMod (3 ^ n)) : ℂ :=
  (3 : ℂ) ^ ((m : ℤ) - (n : ℤ)) * ∑ Y' ∈ fiber m n hmn Y, densC n c Y'

/-- The complex deviation of the density `c` from its `3ᵐ`-scale conditional average. -/
noncomputable def devC (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) (Y : ZMod (3 ^ n)) : ℂ :=
  densC n c Y - condAvgC m n hmn c Y

/-- The oscillation functional equals the `L¹` norm of the (complex) deviation. A cast:
the density and its average are real, so each summand's `|·|` is the `ℂ`-norm of `devC`. -/
theorem osc_eq_sum_norm_devC (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    osc m n hmn c = ∑ Y, ‖devC m n hmn c Y‖ := by
  rw [osc]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  simp only [devC, condAvgC, densC]
  have hcast : ((c Y : ℝ) : ℂ)
        - (3 : ℂ) ^ ((m : ℤ) - (n : ℤ))
            * ∑ Y' ∈ fiber m n hmn Y, ((c Y' : ℝ) : ℂ)
      = ((c Y
          - (3 : ℝ) ^ ((m : ℤ) - (n : ℤ))
              * ∑ Y' ∈ fiber m n hmn Y, c Y' : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, fiber]

/-- **Fourier inversion** for the density: `densC Y = N⁻¹ ∑_ξ 𝓕(densC)(ξ)·e(ξ·Y)`. Immediate
from `densC = 𝓕⁻(𝓕 densC)` (`LinearEquiv.symm_apply_apply`) and `ZMod.invDFT_apply`. -/
theorem densC_inversion (n : ℕ) (c : ZMod (3 ^ n) → ℝ) (Y : ZMod (3 ^ n)) :
    densC n c Y = (3 ^ n : ℂ)⁻¹ * ∑ ξ, ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y) := by
  have hNcast : ((3 ^ n : ℕ) : ℂ) = (3 ^ n : ℂ) := by push_cast; ring
  have hself : densC n c Y = ZMod.dft.symm (ZMod.dft (densC n c)) Y := by
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
  classical
  have h3m : (3 ^ m : ZMod (3 ^ n)) = ((3 ^ m : ℕ) : ZMod (3 ^ n)) := by push_cast; ring
  -- `castHom (3ᵐ) = 0`.
  have hcast3m : ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) (3 ^ m : ZMod (3 ^ n)) = 0 := by
    rw [h3m, map_natCast]; exact ZMod.natCast_self _
  set g : ℕ → ZMod (3 ^ n) := fun t => Y + (t : ZMod (3 ^ n)) * (3 ^ m : ZMod (3 ^ n)) with hg
  -- `g` is injective on `range (3^{n-m})`.
  have hginj : Set.InjOn g (Finset.range (3 ^ (n - m))) := by
    intro t ht t' ht' heq
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    simp only [hg] at heq
    have h2 : (t : ZMod (3 ^ n)) * (3 ^ m : ZMod (3 ^ n))
        = (t' : ZMod (3 ^ n)) * (3 ^ m : ZMod (3 ^ n)) := add_left_cancel heq
    rw [show (t : ZMod (3 ^ n)) * (3 ^ m : ZMod (3 ^ n)) = ((t * 3 ^ m : ℕ) : ZMod (3 ^ n)) from by
        push_cast; ring,
      show (t' : ZMod (3 ^ n)) * (3 ^ m : ZMod (3 ^ n)) = ((t' * 3 ^ m : ℕ) : ZMod (3 ^ n)) from by
        push_cast; ring,
      ZMod.natCast_eq_natCast_iff,
      show (3 : ℕ) ^ n = 3 ^ (n - m) * 3 ^ m from by rw [← pow_add, Nat.sub_add_cancel hmn]] at h2
    have h3 : t ≡ t' [MOD 3 ^ (n - m)] := Nat.ModEq.mul_right_cancel' (by positivity) h2
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at h3
  -- The fiber is exactly the image of `g`.
  have hfib_eq : fiber m n hmn Y = (Finset.range (3 ^ (n - m))).image g := by
    ext Y'
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · intro hY'
      rw [fiber, Finset.mem_filter] at hY'
      have hz : ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) (Y' - Y) = 0 := by
        rw [map_sub, hY'.2, sub_self]
      have hval0 : (((Y' - Y).val : ℕ) : ZMod (3 ^ m)) = 0 := by
        rw [ZMod.castHom_apply] at hz
        rw [ZMod.natCast_val]
        exact hz
      have hdvd : (3 ^ m : ℕ) ∣ (Y' - Y).val := (ZMod.natCast_eq_zero_iff _ _).mp hval0
      refine ⟨(Y' - Y).val / 3 ^ m, ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 3 ^ m)]
        calc (Y' - Y).val < 3 ^ n := ZMod.val_lt _
          _ = 3 ^ (n - m) * 3 ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
      · simp only [hg]
        have hmul : (((Y' - Y).val / 3 ^ m : ℕ) : ZMod (3 ^ n)) * (3 ^ m : ZMod (3 ^ n))
            = Y' - Y := by
          rw [h3m, ← Nat.cast_mul, Nat.div_mul_cancel hdvd, ZMod.natCast_zmod_val]
        rw [hmul]; abel
    · rintro ⟨t, _, rfl⟩
      rw [fiber, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [hg, map_add, map_mul, hcast3m, mul_zero, add_zero]
  rw [hfib_eq, Finset.sum_image hginj]

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
theorem condAvgC_eq_lowSum (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) (Y : ZMod (3 ^ n)) :
    condAvgC m n hmn c Y
      = (3 ^ n : ℂ)⁻¹ * ∑ ξ ∈ lowFreq m n,
          ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y) := by
  classical
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  -- `3^{m-n}·3^{n-m} = 1`.
  have hcancel : (3 : ℂ) ^ ((m : ℤ) - (n : ℤ)) * (3 : ℂ) ^ (n - m) = 1 := by
    rw [← zpow_natCast (3 : ℂ) (n - m), ← zpow_add₀ h3, Nat.cast_sub hmn,
      show (m : ℤ) - (n : ℤ) + ((n : ℤ) - (m : ℤ)) = 0 from by ring, zpow_zero]
  -- Substitute Fourier inversion into the fiber average and swap the sums.
  have hfib : ∑ Y' ∈ fiber m n hmn Y, densC n c Y'
      = (3 ^ n : ℂ)⁻¹ * ∑ ξ, ZMod.dft (densC n c) ξ
          * ∑ Y' ∈ fiber m n hmn Y, ZMod.stdAddChar (ξ * Y') := by
    calc ∑ Y' ∈ fiber m n hmn Y, densC n c Y'
        = ∑ Y' ∈ fiber m n hmn Y, (3 ^ n : ℂ)⁻¹
            * ∑ ξ, ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y') :=
          Finset.sum_congr rfl (fun Y' _ => densC_inversion n c Y')
      _ = (3 ^ n : ℂ)⁻¹ * ∑ Y' ∈ fiber m n hmn Y,
            ∑ ξ, ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y') := by rw [Finset.mul_sum]
      _ = (3 ^ n : ℂ)⁻¹ * ∑ ξ,
            ∑ Y' ∈ fiber m n hmn Y, ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y') := by
          rw [Finset.sum_comm]
      _ = (3 ^ n : ℂ)⁻¹ * ∑ ξ, ZMod.dft (densC n c) ξ
            * ∑ Y' ∈ fiber m n hmn Y, ZMod.stdAddChar (ξ * Y') := by
          refine congrArg _ (Finset.sum_congr rfl (fun ξ _ => ?_))
          rw [Finset.mul_sum]
  -- Collapse the coset character sum: only low frequencies survive.
  have hcoset : ∀ ξ : ZMod (3 ^ n),
      ZMod.dft (densC n c) ξ * ∑ Y' ∈ fiber m n hmn Y, ZMod.stdAddChar (ξ * Y')
        = if ξ ∈ lowFreq m n then
            (3 : ℂ) ^ (n - m) * (ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y)) else 0 := by
    intro ξ
    rw [coset_char_sum m n hmn ξ Y]
    split_ifs with h <;> ring
  rw [condAvgC, hfib, Finset.sum_congr rfl (fun ξ (_ : ξ ∈ Finset.univ) => hcoset ξ),
    Finset.sum_ite_mem_eq, ← Finset.mul_sum]
  rw [show (3 : ℂ) ^ ((m : ℤ) - (n : ℤ)) * ((3 ^ n : ℂ)⁻¹
        * ((3 : ℂ) ^ (n - m) * ∑ ξ ∈ lowFreq m n,
            ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y)))
      = ((3 : ℂ) ^ ((m : ℤ) - (n : ℤ)) * (3 : ℂ) ^ (n - m)) * ((3 ^ n : ℂ)⁻¹
        * ∑ ξ ∈ lowFreq m n, ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y)) from by ring,
    hcancel, one_mul]

/-- **The Fourier-inversion crux** (Remark 1.18): the `3ᵐ`-scale deviation is the high-frequency
inverse DFT. The conditional average is the projection onto the low frequencies (`condAvgC_eq_lowSum`),
so `devC Y = c Y − avg(Y) = N⁻¹·(∑_all − ∑_low) = N⁻¹ ∑_{ξ∈highFreq} 𝓕c(ξ)·e(ξ·Y)`. -/
theorem devC_eq_highfreq_invDFT (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) (Y : ZMod (3 ^ n)) :
    devC m n hmn c Y
      = (3 ^ n : ℂ)⁻¹ * ∑ ξ ∈ highFreq m n,
          ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y) := by
  have hsplit : ∑ ξ ∈ highFreq m n, ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y)
      = (∑ ξ, ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y))
        - ∑ ξ ∈ lowFreq m n, ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y) := by
    rw [highFreq, lowFreq, eq_sub_iff_add_eq, add_comm, Finset.sum_filter_add_sum_filter_not]
  rw [devC, densC_inversion n c Y, condAvgC_eq_lowSum m n hmn c Y, ← mul_sub, ← hsplit]

/-- **Parseval `L²` identity for the deviation**: `∑_Y ‖devC Y‖² = N⁻¹·∑_{highFreq} ‖𝓕c(ξ)‖²`.
From `devC_eq_highfreq_invDFT` (`devC = 𝓕⁻ g`, `g` the high-frequency restriction of `𝓕c`) and
`ZMod.dft_parseval`. -/
theorem sum_norm_sq_devC_eq (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    ∑ Y, ‖devC m n hmn c Y‖ ^ 2
      = (3 ^ n : ℝ)⁻¹ * ∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n c) ξ‖ ^ 2 := by
  classical
  -- `g` = the high-frequency restriction of the DFT of the density.
  set g : ZMod (3 ^ n) → ℂ :=
    fun ξ => if ξ ∈ highFreq m n then ZMod.dft (densC n c) ξ else 0 with hg
  have hNcast : ((3 ^ n : ℕ) : ℂ) = (3 ^ n : ℂ) := by push_cast; ring
  have hRcast : ((3 ^ n : ℕ) : ℝ) = (3 ^ n : ℝ) := by push_cast; ring
  have hN : (3 ^ n : ℝ) ≠ 0 := by positivity
  -- Step A: the deviation is the inverse DFT of `g`.
  have hsum : ∀ Y : ZMod (3 ^ n), (∑ ξ, ZMod.stdAddChar (ξ * Y) • g ξ)
      = ∑ ξ ∈ highFreq m n, ZMod.dft (densC n c) ξ * ZMod.stdAddChar (ξ * Y) := by
    intro Y
    simp only [hg, smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem_eq]
    exact Finset.sum_congr rfl (fun ξ _ => mul_comm _ _)
  have hdev : ∀ Y : ZMod (3 ^ n), devC m n hmn c Y = ZMod.dft.symm g Y := by
    intro Y
    rw [devC_eq_highfreq_invDFT m n hmn c Y, ZMod.invDFT_apply, smul_eq_mul, hNcast, hsum Y]
  -- Step B: the `g`-mass equals the high-frequency mass.
  have hgpt : ∀ ξ, ‖g ξ‖ ^ 2
      = if ξ ∈ highFreq m n then ‖ZMod.dft (densC n c) ξ‖ ^ 2 else 0 := by
    intro ξ; simp only [hg]; split_ifs <;> simp
  have hgsum : ∑ ξ, ‖g ξ‖ ^ 2 = ∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n c) ξ‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun ξ _ => hgpt ξ), Finset.sum_ite_mem_eq]
  -- Step C: Parseval on `𝓕⁻ g`.
  have hpars := ZMod.dft_parseval (ZMod.dft.symm g)
  rw [LinearEquiv.apply_symm_apply, hgsum, hRcast] at hpars
  -- hpars : ∑ξ∈highFreq, ‖𝓕(densC)ξ‖² = (3^n:ℝ) * ∑ j, ‖𝓕⁻ g j‖²
  have hLHS : ∑ Y, ‖devC m n hmn c Y‖ ^ 2 = ∑ Y, ‖ZMod.dft.symm g Y‖ ^ 2 :=
    Finset.sum_congr rfl (fun Y _ => by rw [hdev Y])
  rw [hLHS, hpars, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- **§6 Cauchy–Schwarz + Parseval bridge** (Remark 1.18 route): the `3ᵐ`-scale oscillation of
the Syracuse density is at most the `√` of its high-frequency `L²` Fourier mass. Proved from
`osc_eq_sum_norm_devC`, the Cauchy–Schwarz inequality `sq_sum_le_card_mul_sum_sq`, and the
Parseval `L²` identity `sum_norm_sq_devC_eq`. -/
theorem osc_le_sqrt_highfreq (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    osc m n hmn c
      ≤ Real.sqrt (∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n c) ξ‖ ^ 2) := by
  rw [osc_eq_sum_norm_devC]
  set D := ∑ Y, ‖devC m n hmn c Y‖ with hD
  set H := ∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n c) ξ‖ ^ 2 with hH
  have hN : (3 ^ n : ℝ) ≠ 0 := by positivity
  have hcard : ((Finset.univ : Finset (ZMod (3 ^ n))).card : ℝ) = (3 ^ n : ℝ) := by
    rw [Finset.card_univ, ZMod.card]; push_cast; ring
  have hcs : D ^ 2 ≤ (3 ^ n : ℝ) * ∑ Y, ‖devC m n hmn c Y‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod (3 ^ n))))
      (f := fun Y => ‖devC m n hmn c Y‖)
    rwa [hcard] at this
  have key : D ^ 2 ≤ H := by
    calc D ^ 2 ≤ (3 ^ n : ℝ) * ∑ Y, ‖devC m n hmn c Y‖ ^ 2 := hcs
      _ = (3 ^ n : ℝ) * ((3 ^ n : ℝ)⁻¹ * H) := by rw [sum_norm_sq_devC_eq]
      _ = H := by field_simp
  have hnn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc D = Real.sqrt (D ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt H := Real.sqrt_le_sqrt key

/-- **(6.11) collision-entropy skeleton** (C10): for any real density `c`, the high-frequency `L²`
mass is bounded by the collision entropy `3ⁿ·∑_Y (c Y)²`. High freq ⊆ all freq (nonneg terms) +
`dft_parseval` (`∑_ξ‖𝓕Φ ξ‖² = N·∑_Y‖Φ Y‖²`) + `‖(c Y : ℂ)‖² = (c Y)²`. This is the Plancherel side
of the C10 bound: combined with the head-factor decay (`dft_condDens_norm_le`), Tao's (6.11) refines
`∑_{high}‖𝓕(densC condDens)‖²` to `decay²·(tail collision entropy)`; this lemma is the raw Plancherel
step underneath, reusable for any conditioned density. -/
theorem highfreq_l2_le_collision (m n : ℕ) (c : ZMod (3 ^ n) → ℝ) :
    ∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n c) ξ‖ ^ 2 ≤ (3 ^ n : ℝ) * ∑ Y, (c Y) ^ 2 := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  calc ∑ ξ ∈ highFreq m n, ‖ZMod.dft (densC n c) ξ‖ ^ 2
      ≤ ∑ ξ, ‖ZMod.dft (densC n c) ξ‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ξ _ _ => by positivity)
    _ = (3 ^ n : ℝ) * ∑ Y, ‖densC n c Y‖ ^ 2 := by
        rw [ZMod.dft_parseval (densC n c)]; push_cast; ring
    _ = (3 ^ n : ℝ) * ∑ Y, (c Y) ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl (fun Y _ => ?_)
        rw [densC, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **`osc` subadditivity** (C10, the (6.1)–(6.5) triangle inequality). The oscillation functional
is subadditive: `osc(c₁ + c₂) ≤ osc(c₁) + osc(c₂)`. The `3ᵐ`-conditional average is linear, so the
per-`Y` deviation splits and `|a + b| ≤ |a| + |b|`. This is what lets the event assembly telescope
`osc(syracZ density) ≤ ∑_{k,l} osc(condDens_{k,l}) + osc(error)` — the density decomposition over the
conditioning partition passes through `osc` by the triangle inequality. -/
theorem osc_add_le (m n : ℕ) (hmn : m ≤ n) (c₁ c₂ : ZMod (3 ^ n) → ℝ) :
    osc m n hmn (fun Y => c₁ Y + c₂ Y) ≤ osc m n hmn c₁ + osc m n hmn c₂ := by
  unfold osc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun Y _ => ?_)
  rw [show (c₁ Y + c₂ Y) - (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
        ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) =>
          ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y'
            = ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y), (c₁ Y' + c₂ Y')
      = (c₁ Y - (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
          ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) =>
            ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y'
              = ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y), c₁ Y')
        + (c₂ Y - (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
          ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) =>
            ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y'
              = ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y), c₂ Y')
      from by rw [Finset.sum_add_distrib]; ring]
  exact abs_add_le _ _

/-- `osc` is nonnegative (a sum of absolute values). -/
theorem osc_nonneg (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) : 0 ≤ osc m n hmn c :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- **`osc` subadditivity over a finite sum** (C10, the event-assembly telescope). For a density
written as a finite sum `∑ᵢ cᵢ` (e.g. the conditioning partition `∑_{k,l} g_{k,l}` + error),
`osc(∑ᵢ cᵢ) ≤ ∑ᵢ osc(cᵢ)`. Finset induction on `osc_add_le`. This is the exact shape Tao's (6.1)–(6.8)
event assembly needs: decompose the syracZ density over the events, bound each piece's oscillation
(`condDens_osc_le` for the conditioned pieces), and sum. -/
theorem osc_sum_le {ι : Type*} (m n : ℕ) (hmn : m ≤ n) (s : Finset ι) (c : ι → ZMod (3 ^ n) → ℝ) :
    osc m n hmn (fun Y => ∑ i ∈ s, c i Y) ≤ ∑ i ∈ s, osc m n hmn (c i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [osc]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc osc m n hmn (fun Y => ∑ i ∈ insert a s, c i Y)
        = osc m n hmn (fun Y => c a Y + ∑ i ∈ s, c i Y) := by
          refine congrArg _ (funext (fun Y => ?_)); rw [Finset.sum_insert ha]
      _ ≤ osc m n hmn (c a) + osc m n hmn (fun Y => ∑ i ∈ s, c i Y) := osc_add_le _ _ _ _ _
      _ ≤ osc m n hmn (c a) + ∑ i ∈ s, osc m n hmn (c i) := by linarith [ih]

/-! ## ⚠️ ROUTE FINDING (2026-07-15): the raw-`syracZ` high-frequency `L²` mass is NOT small

The naive plan — bound `∑_{ξ∈highFreq} ‖𝓕(densC n) ξ‖²` directly from `charFn_decay` — is
**REFUTED**. By Parseval (`sum_norm_sq_devC_eq` / `dft_parseval`),
`∑_{highFreq m n} ‖ĉ_n(ξ)‖² = 3ⁿ‖syracZ(n)‖₂² − 3ᵐ‖syracZ(m)‖₂² =: Q(n) − Q(m)`,
and an exact DP computation of `syracZ` (scratch `syrac2.py`) shows this **GROWS ≈ 0.46·(n−m)**,
so it is emphatically **not** `≤ C·m^{-A}`. Hence `osc_le_sqrt_highfreq` applied to the *raw*
density is a true but hopelessly lossy inequality (`osc ≤ √(0.46·n)`), and the former
`highfreq_l2_le` was a FALSE lemma — now deleted.

**Why**: `osc_le_sqrt_highfreq` is correct and reusable, but Tao's §6 applies Cauchy–Schwarz to a
*conditioned* density `g_{n,k,l}(Y) = P((Xₙ=Y) ∧ Eₖ ∧ Bₖ ∧ Cₖ,ₗ)`, whose small high-frequency `L²`
mass comes from the **independent split** `Xₙ = F_{k+1}(a_{k+1},…,a₁) + 3^{k+1}2^{-l}F_{n-k-1}(aₙ,…,a_{k+2})`
(1.5)/(1.26): the character sum FACTORS, and the second factor is a Syracuse char sum at level
`n−k−1` that `charFn_decay` (Prop 1.17) bounds. `osc(syracZ)` is recovered from `∑_{k,l} osc(g_{n,k,l})`
by the triangle inequality over the conditioning events (paper (6.2)–(6.10)).

**How to apply**: (1) generalize `osc_le_sqrt_highfreq` to an arbitrary real density `c` (the proof
never used `syracZ`-ness); (2) build the §6 conditioning apparatus (stopping time `k`, events
`E,Eₖ,Bₖ,Cₖ,ₗ`, the `F`-splitting independence); (3) bound `∑_{highFreq}‖ĝ_{n,k,l}‖²` via the
factored char sum + `charFn_decay`; (4) reassemble by triangle inequality. See `PENDING_WORK` fruit-8.
-/

/-- **Brick (b), step 1 — the pointwise character factorization** (C10): the additive character
of the split offset factors multiplicatively across the cut, `stdAddChar(-(X·ξ)) =
stdAddChar(-(head·ξ)) · stdAddChar(-(tail·ξ))`, where `head = 3^p·(Fnat_j·2⁻ᵃ⁽¹ʲ⁾)·2⁻ᵗᵃⁱˡᵛᵃˡ` and
`tail = Fnat_p(last p coords)·2⁻ᵗᵃⁱˡᵛᵃˡ` from `syracZ_offset_split`. This is the additive-to-
multiplicative step of the §6 factorization.

⚠️ **KEY ROUTE FACT** (governs the next step): the `head` factor still carries a `2⁻ᵗᵃⁱˡᵛᵃˡ`
(`M := pre (tail) p`) that depends on the TAIL coordinates, so the character does NOT split into a
pure head-function times a pure tail-function. The expectation `E_a[·]` therefore does **not** factor
into head × tail directly — it factors only AFTER conditioning on the cut-valuation `L := pre a j`
(equivalently on `M`), which fixes `2⁻ᵗᵃⁱˡᵛᵃˡ` to a constant. This is exactly why Tao conditions on
the level `l`; it is mandatory, not bookkeeping. -/
theorem char_offset_split {j p : ℕ} (a : Fin (j + p) → ℕ) (ξ : ZMod (3 ^ (j + p))) :
    ZMod.stdAddChar (-(((fnat (j + p) a : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p)) * ξ))
      = ZMod.stdAddChar (-((3 ^ p * ((fnat j (fun i => a (Fin.castAdd p i)) : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a j)
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre (fun i => a (Fin.natAdd j i)) p) * ξ))
          * ZMod.stdAddChar (-(((fnat p (fun i => a (Fin.natAdd j i)) : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre (fun i => a (Fin.natAdd j i)) p) * ξ)) := by
  rw [syracZ_offset_split, add_mul, neg_add, AddChar.map_add_eq_mul]

/-- The standard additive character has unit norm (it lands on the unit circle). -/
theorem norm_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

/-- **`stdAddChar` ↔ `eC` bridge**: the mathlib standard additive character on `ZMod (3ⁿ)` is the
`§7` phase `eC(j.val/3ⁿ)`. This is the seam that lets the `cond_char_factor` factors (written in
`stdAddChar`) be bounded by `charFn_decay` (Prop 1.17, written in `eC`). -/
theorem stdAddChar_eq_eC {n : ℕ} (j : ZMod (3 ^ n)) :
    ZMod.stdAddChar j = eC ((j.val : ℚ) / 3 ^ n) := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, eC]
  push_cast
  ring_nf

/-- **Character level-descent** (C10 brick b, the tail-reindex crux): multiplying the argument of
the standard additive character by `3ʲ` drops the modulus from `3^(j+p)` down to `3^p`:
`stdAddChar_{3^(j+p)}(3ʲ·w) = stdAddChar_{3^p}(w mod 3^p)`. This is the arithmetic that turns the
tail character factor — after pulling the `3ʲ` out of a high frequency `ξ = 3ʲ·2ˡ·ξ'` — into a
genuine level-`p` Syracuse character sum, on which `charFn_decay` (Prop 1.17) delivers the decay.
Proof: lift `w` to its `ℕ` value `m`, fold the LHS argument into a single `natCast (3ʲ·m)`, push
both characters through `stdAddChar_coe` to `exp(2πi·(·)/·)`, and cancel `3ʲ/3^(j+p) = 1/3^p`. -/
theorem stdAddChar_pow3_descent {j p : ℕ} (w : ZMod (3 ^ (j + p))) :
    ZMod.stdAddChar ((3 : ZMod (3 ^ (j + p))) ^ j * w)
      = ZMod.stdAddChar (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p)) w) := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ p) := ⟨pow_ne_zero _ (by norm_num)⟩
  set m : ℕ := w.val with hmdef
  have hw : w = ((m : ℕ) : ZMod (3 ^ (j + p))) := (ZMod.natCast_zmod_val w).symm
  rw [hw]
  have hL : (3 : ZMod (3 ^ (j + p))) ^ j * ((m : ℕ) : ZMod (3 ^ (j + p)))
      = (((3 ^ j * m : ℕ)) : ZMod (3 ^ (j + p))) := by push_cast; ring
  have hR : ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p))
        ((m : ℕ) : ZMod (3 ^ (j + p))) = ((m : ℕ) : ZMod (3 ^ p)) := by rw [map_natCast]
  rw [hL, hR,
     show (((3 ^ j * m : ℕ)) : ZMod (3 ^ (j + p)))
         = (((3 ^ j * m : ℕ) : ℤ) : ZMod (3 ^ (j + p))) by push_cast; ring,
     show ((m : ℕ) : ZMod (3 ^ p)) = (((m : ℕ) : ℤ) : ZMod (3 ^ p)) by push_cast; ring,
     ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_add]
  field_simp

/-- **Character level-descent, right-summand variant** (C10 head-block): multiplying the argument
by `3ᵖ` (the *second* exponent summand) drops the modulus `3^(j+p) → 3^j`:
`stdAddChar_{3^(j+p)}(3ᵖ·w) = stdAddChar_{3^j}(w mod 3^j)`. This is the mirror of
`stdAddChar_pow3_descent`, needed for the head factor whose `3ᵖ` block-scaling prefactor sits at the
*low* end of the modulus `3^(j+p)`. Same proof: lift `w` to `ℕ`, fold into `natCast (3ᵖ·m)`, push
through `stdAddChar_coe`, cancel `3ᵖ / 3^(j+p) = 1/3ʲ`. -/
theorem stdAddChar_pow3_descent_right {j p : ℕ} (w : ZMod (3 ^ (j + p))) :
    ZMod.stdAddChar ((3 : ZMod (3 ^ (j + p))) ^ p * w)
      = ZMod.stdAddChar (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right j p)) (ZMod (3 ^ j)) w) := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ j) := ⟨pow_ne_zero _ (by norm_num)⟩
  set m : ℕ := w.val with hmdef
  have hw : w = ((m : ℕ) : ZMod (3 ^ (j + p))) := (ZMod.natCast_zmod_val w).symm
  rw [hw]
  have hL : (3 : ZMod (3 ^ (j + p))) ^ p * ((m : ℕ) : ZMod (3 ^ (j + p)))
      = (((3 ^ p * m : ℕ)) : ZMod (3 ^ (j + p))) := by push_cast; ring
  have hR : ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right j p)) (ZMod (3 ^ j))
        ((m : ℕ) : ZMod (3 ^ (j + p))) = ((m : ℕ) : ZMod (3 ^ j)) := by rw [map_natCast]
  rw [hL, hR,
     show (((3 ^ p * m : ℕ)) : ZMod (3 ^ (j + p)))
         = (((3 ^ p * m : ℕ) : ℤ) : ZMod (3 ^ (j + p))) by push_cast; ring,
     show ((m : ℕ) : ZMod (3 ^ j)) = (((m : ℕ) : ℤ) : ZMod (3 ^ j)) by push_cast; ring,
     ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_add]
  field_simp

/-- `castHom` sends the level-`(j+p)` inverse of `2` to the level-`p` inverse of `2` (both are the
unique inverse of the unit `2` under the ring hom). Used to reduce the Syracuse offset mod `3^p`. -/
theorem castHom_two_inv {j p : ℕ} :
    ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p)) (2 : ZMod (3 ^ (j + p)))⁻¹
      = (2 : ZMod (3 ^ p))⁻¹ := by
  set F := ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p)) with hF
  have h2 : (2 : ZMod (3 ^ p)) * (2 : ZMod (3 ^ p))⁻¹ = 1 := by
    apply ZMod.mul_inv_of_unit
    rw [show (2 : ZMod (3 ^ p)) = ((2 : ℕ) : ZMod (3 ^ p)) by norm_cast, ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (by decide)
  have h1 : (2 : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ = 1 := by
    apply ZMod.mul_inv_of_unit
    rw [show (2 : ZMod (3 ^ (j + p))) = ((2 : ℕ) : ZMod (3 ^ (j + p))) by norm_cast,
      ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (by decide)
  have hF2 : F (2 : ZMod (3 ^ (j + p))) = (2 : ZMod (3 ^ p)) := by
    rw [hF, show (2 : ZMod (3 ^ (j + p))) = ((2 : ℕ) : ZMod (3 ^ (j + p))) by norm_cast,
      map_natCast]; norm_cast
  have hc : (2 : ZMod (3 ^ p)) * F (2 : ZMod (3 ^ (j + p)))⁻¹ = 1 := by
    have := congrArg F h1; rwa [map_mul, map_one, hF2] at this
  calc F (2 : ZMod (3 ^ (j + p)))⁻¹
      = (2 : ZMod (3 ^ p))⁻¹ * ((2 : ZMod (3 ^ p)) * F (2 : ZMod (3 ^ (j + p)))⁻¹) := by
        rw [← mul_assoc, mul_comm ((2 : ZMod (3 ^ p))⁻¹) 2, h2, one_mul]
    _ = (2 : ZMod (3 ^ p))⁻¹ := by rw [hc, mul_one]

/-- `castHom` sends the level-`(j+p)` inverse of `2` to the level-`j` inverse of `2` (right-summand
descent, `3^(j+p) → 3^j`). Mirror of `castHom_two_inv`, used to reduce the head Syracuse offset. -/
theorem castHom_two_inv_right {j p : ℕ} :
    ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right j p)) (ZMod (3 ^ j)) (2 : ZMod (3 ^ (j + p)))⁻¹
      = (2 : ZMod (3 ^ j))⁻¹ := by
  set F := ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right j p)) (ZMod (3 ^ j)) with hF
  have h2 : (2 : ZMod (3 ^ j)) * (2 : ZMod (3 ^ j))⁻¹ = 1 := by
    apply ZMod.mul_inv_of_unit
    rw [show (2 : ZMod (3 ^ j)) = ((2 : ℕ) : ZMod (3 ^ j)) by norm_cast, ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (by decide)
  have h1 : (2 : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ = 1 := by
    apply ZMod.mul_inv_of_unit
    rw [show (2 : ZMod (3 ^ (j + p))) = ((2 : ℕ) : ZMod (3 ^ (j + p))) by norm_cast,
      ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (by decide)
  have hF2 : F (2 : ZMod (3 ^ (j + p))) = (2 : ZMod (3 ^ j)) := by
    rw [hF, show (2 : ZMod (3 ^ (j + p))) = ((2 : ℕ) : ZMod (3 ^ (j + p))) by norm_cast,
      map_natCast]; norm_cast
  have hc : (2 : ZMod (3 ^ j)) * F (2 : ZMod (3 ^ (j + p)))⁻¹ = 1 := by
    have := congrArg F h1; rwa [map_mul, map_one, hF2] at this
  calc F (2 : ZMod (3 ^ (j + p)))⁻¹
      = (2 : ZMod (3 ^ j))⁻¹ * ((2 : ZMod (3 ^ j)) * F (2 : ZMod (3 ^ (j + p)))⁻¹) := by
        rw [← mul_assoc, mul_comm ((2 : ZMod (3 ^ j))⁻¹) 2, h2, one_mul]
    _ = (2 : ZMod (3 ^ j))⁻¹ := by rw [hc, mul_one]

/-- **Brick (b), the tail-factor reindex** (C10): for a frequency of the form `ξ = 3ʲ·ζ`, the tail
character factor `stdAddChar_{3^(j+p)}(-(offset(vt)·ξ))` — with `offset(vt) = Fnat_p(vt)·2⁻ᵖʳᵉ⁽ᵛᵗ,ᵖ⁾`
the reduced Syracuse offset — descends to the **level-`p` Syracuse character** at `castHom ζ`. Proof:
factor `3ʲ` out of the argument (`ring`), apply `stdAddChar_pow3_descent`, then push `castHom`
through the offset (`map_mul`/`map_pow`/`map_natCast` + `castHom_two_inv`). Combined with
`syracZ_eq_rev_fnat` + `cexpect_map`, this turns the tail expectation into a `syracZ p`-cexpect that
`stdAddChar_eq_eC` matches to `charFn_decay`'s `eC` form. -/
theorem tail_char_descent {j p : ℕ} (ζ : ZMod (3 ^ (j + p))) (vt : Fin p → ℕ) :
    ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ((3 : ZMod (3 ^ (j + p))) ^ j * ζ)))
      = ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ p))
        * (2 : ZMod (3 ^ p))⁻¹ ^ pre vt p)
        * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p)) ζ)) := by
  have harg : -(((fnat p vt : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ((3 : ZMod (3 ^ (j + p))) ^ j * ζ))
      = (3 : ZMod (3 ^ (j + p))) ^ j * (-(((fnat p vt : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ζ)) := by ring
  rw [harg, stdAddChar_pow3_descent]
  congr 1
  rw [map_neg, map_mul, map_mul, map_pow, map_natCast, castHom_two_inv]

/-- `eC` only depends on its numerator mod `3ⁿ`: congruent integers give equal phases (periodicity
via `eC_add` + `eC_intCast`). -/
theorem eC_val_congr {n : ℕ} (a b : ℤ) (h : (a : ZMod (3 ^ n)) = (b : ZMod (3 ^ n))) :
    eC ((a : ℚ) / 3 ^ n) = eC ((b : ℚ) / 3 ^ n) := by
  have hdvd : ((3 : ℤ) ^ n) ∣ (a - b) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) (3 ^ n)).mp (by push_cast [h]; ring)
    simpa using this
  obtain ⟨k, hk⟩ := hdvd
  have hab : (a : ℚ) / (3 : ℚ) ^ n = (b : ℚ) / (3 : ℚ) ^ n + (k : ℚ) := by
    have h3 : ((3 : ℚ) ^ n) ≠ 0 := by positivity
    have hq : (a : ℚ) = (b : ℚ) + (3 : ℚ) ^ n * k := by
      exact_mod_cast (by linarith : a = b + 3 ^ n * k)
    rw [hq]; field_simp
  rw [hab, eC_add, eC_intCast, mul_one]

/-- `stdAddChar` of a product equals the exact `eC` phase used by `charFn_decay` (Prop 1.17):
`stdAddChar(-(Y·ξ)) = eC(-(ξ.val·Y.val)/3ⁿ)`. The `.val`-product congruence is handled by
`eC_val_congr` (both sides reduce to `-(ξ·Y)` in `ZMod (3ⁿ)`). -/
theorem stdAddChar_mul_eq_eC {n : ℕ} (ξ Y : ZMod (3 ^ n)) :
    ZMod.stdAddChar (-(Y * ξ)) = eC (-(ξ.val * Y.val : ℚ) / 3 ^ n) := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [stdAddChar_eq_eC,
    show ((-(Y * ξ)).val : ℚ) = (((-(Y * ξ)).val : ℤ) : ℚ) by push_cast; ring,
    show (-(ξ.val * Y.val : ℚ)) = (((-(↑ξ.val * ↑Y.val) : ℤ)) : ℚ) by push_cast; ring]
  apply eC_val_congr; push_cast [ZMod.natCast_zmod_val]; ring

/-- The tail block expectation over `iid geomHalf p` of the level-`p` Syracuse character is a
`syracZ p`-expectation, via `syracZ_eq_rev_fnat` (the pushforward form) and `cexpect_map`. -/
theorem tail_cexpect_eq_syracZ {j p : ℕ} (ζ : ZMod (3 ^ (j + p))) :
    (geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ p))
        * (2 : ZMod (3 ^ p))⁻¹ ^ pre vt p)
        * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p)) ζ)))
      = (syracZ p).cexpect (fun Y => ZMod.stdAddChar (-(Y
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p)) ζ))) := by
  haveI : NeZero (3 ^ p) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [syracZ_eq_rev_fnat p, cexpect_map _ _ _ (fun Y => le_of_eq (norm_stdAddChar _))]

/-- **Brick (b), the tail-factor ⟹ `charFn_decay` capstone** (C10): for a frequency `ξ = 3ʲ·ζ`, the
tail character factor over the `p`-coordinate block equals **exactly** the level-`p` Syracuse
character sum in `charFn_decay`'s form, at frequency `ξ' = ζ mod 3^p`:
`E_vt[stdAddChar_{3^(j+p)}(-(offset(vt)·3ʲζ))] = (syracZ p).cexpect (Y ↦ eC(-(ξ'.val·Y.val)/3^p))`.
Chains `tail_char_descent` (pointwise level-descent) → `tail_cexpect_eq_syracZ` (pushforward) →
`stdAddChar_mul_eq_eC` (`stdAddChar`→`eC`). So `charFn_decay` bounds the tail factor by `Cₐ·p⁻ᴬ`
whenever `3 ∤ ξ'.val`. -/
theorem tail_factor_eq_charFn {j p : ℕ} (ζ : ZMod (3 ^ (j + p))) :
    (geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ((3 : ZMod (3 ^ (j + p))) ^ j * ζ))))
      = (syracZ p).cexpect (fun Y => eC (-(((ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j))
          (ZMod (3 ^ p)) ζ).val) * Y.val : ℚ) / 3 ^ p)) := by
  rw [show (geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ((3 : ZMod (3 ^ (j + p))) ^ j * ζ))))
        = (geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ p))
          * (2 : ZMod (3 ^ p))⁻¹ ^ pre vt p)
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p)) ζ)))
        from congrArg (PMF.cexpect (geomHalf.iid p)) (funext (fun vt => tail_char_descent ζ vt)),
      tail_cexpect_eq_syracZ]
  exact congrArg (PMF.cexpect (syracZ p)) (funext (fun Y => stdAddChar_mul_eq_eC _ Y))

/-- **Brick (b), the tail-factor decay bound** (C10): the tail character factor over the
`p`-coordinate block decays polynomially, `≤ Cₐ·p⁻ᴬ`, for every high frequency `ξ = 3ʲ·ζ` with
`3∤(ζ mod 3^p).val`. Immediate from `tail_factor_eq_charFn` + `charFn_decay` (Prop 1.17). This is
the high-entropy factor whose decay drives Prop 1.14. -/
theorem tail_factor_norm_le (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ (j p : ℕ), 1 ≤ p → ∀ (ζ : ZMod (3 ^ (j + p))),
      ¬ (3 ∣ (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p)) ζ).val) →
      ‖(geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ((3 : ZMod (3 ^ (j + p))) ^ j * ζ))))‖
        ≤ C * (p : ℝ) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := charFn_decay A hA
  refine ⟨C, hC0, fun j p hp ζ hζ => ?_⟩
  rw [tail_factor_eq_charFn]
  exact hC p hp _ hζ

/-- **The Syracuse consistency descent** (C10 head-block novelty, Tao's (1.22) applied to a
character sum at a `3`-divisible frequency). For a level-`(j'+q)` Syracuse character sum at the
frequency `3^{j'}·η`, the `3^{j'}` factor descends the whole expectation to the **level-`q`**
Syracuse character sum at the reduced frequency `castHom η`. This is the exact step Tao performs
when the decay block `Fₙ₋ₖ₋₁ mod 3^{n-k-j-1}` collapses to a lower-level Syracuse random variable:
extract `3ʲ'` from the high frequency `ξ = 3ʲ'·2ˡ·ξ'`, and the level drops by the valuation `j'`.
Proof: pointwise `stdAddChar_pow3_descent` drops the modulus `3^{j'+q}→3^q` (turning `Y` into
`castHom Y`); then `cexpect_map` + `syracZ_map_cast` (the (1.22) projection compatibility) rewrites
the pushforward `(syracZ (j'+q)).map castHom` as `syracZ q`. This is why `charFn_decay` (which needs
a `3`-coprime frequency) applies at level `q` even though the raw frequency `3^{j'}·η` is divisible
by `3`. -/
theorem syracZ_char_descent {j' q : ℕ} (η : ZMod (3 ^ (j' + q))) :
    (syracZ (j' + q)).cexpect (fun Y => ZMod.stdAddChar (-(Y *
        ((3 : ZMod (3 ^ (j' + q))) ^ j' * η))))
      = (syracZ q).cexpect (fun Y' => ZMod.stdAddChar (-(Y' *
          ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j')) (ZMod (3 ^ q)) η))) := by
  haveI : NeZero (3 ^ q) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hpt : ∀ Y : ZMod (3 ^ (j' + q)),
      ZMod.stdAddChar (-(Y * ((3 : ZMod (3 ^ (j' + q))) ^ j' * η)))
        = ZMod.stdAddChar (-(ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j')) (ZMod (3 ^ q)) Y
            * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j')) (ZMod (3 ^ q)) η)) := by
    intro Y
    rw [show -(Y * ((3 : ZMod (3 ^ (j' + q))) ^ j' * η))
        = (3 : ZMod (3 ^ (j' + q))) ^ j' * (-(Y * η)) by ring,
      stdAddChar_pow3_descent, map_neg, map_mul]
  rw [show (fun Y : ZMod (3 ^ (j' + q)) => ZMod.stdAddChar (-(Y *
        ((3 : ZMod (3 ^ (j' + q))) ^ j' * η))))
      = (fun Y : ZMod (3 ^ (j' + q)) => ZMod.stdAddChar
          (-(ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j')) (ZMod (3 ^ q)) Y
            * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j')) (ZMod (3 ^ q)) η)))
      from funext hpt,
    ← syracZ_map_cast (Nat.le_add_left q j'),
    cexpect_map _ _ _ (fun Y => le_of_eq (norm_stdAddChar _))]

/-- **Brick (b), the head-factor Stage-A descent** (C10, pointwise). The head character factor from
`cond_char_factor` carries a `3^p` block-scaling prefactor (at the *low* end of the modulus
`3^(j+p)`) and the frozen tail-valuation phase `2⁻ˡ`. The `3^p` prefactor descends the character
from level `j+p` down to level `j`, landing the head offset `Fnat_j(vh)·2⁻ᵖʳᵉ` at level `j` as a
genuine level-`j` Syracuse character at the **reduced frequency** `2⁻ˡ·(ξ mod 3ʲ)` — the frozen
phase `2⁻ˡ` is a unit coprime to `3`, so it is absorbed into the frequency (it need not cancel; it
preserves the `3`-adic valuation). Proof: `ring`-refactor to pull `3^p` leftmost,
`stdAddChar_pow3_descent_right` (right-summand descent `3^(j+p)→3ʲ`), then push `castHom` through the
offset and phase (`castHom_two_inv_right`). Stage B is `syracZ_char_descent`, which peels the `3ʲ'`
valuation of the reduced frequency off to `charFn_decay`'s level. -/
theorem head_char_descent {j p : ℕ} (l : ℕ) (ξ : ZMod (3 ^ (j + p))) (vh : Fin j → ℕ) :
    ZMod.stdAddChar (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ))
      = ZMod.stdAddChar (-(((fnat j vh : ZMod (3 ^ j))
        * (2 : ZMod (3 ^ j))⁻¹ ^ pre vh j)
        * ((2 : ZMod (3 ^ j))⁻¹ ^ l
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right j p)) (ZMod (3 ^ j)) ξ))) := by
  have harg : -((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)
      = (3 : ZMod (3 ^ (j + p))) ^ p * (-(((fnat j vh : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
        * ((2 : ZMod (3 ^ (j + p)))⁻¹ ^ l * ξ))) := by ring
  rw [harg, stdAddChar_pow3_descent_right]
  congr 1
  simp only [map_neg, map_mul, map_pow, map_natCast, castHom_two_inv_right]

/-- The block expectation over `iid geomHalf n` of a level-`n` Syracuse character (offset
`Fnat_n·2⁻ᵖʳᵉ`) at any frequency `freq` is a `syracZ n`-expectation. General form of
`tail_cexpect_eq_syracZ`, used for the head block via `head_char_descent`. `syracZ_eq_rev_fnat`
(pushforward) + `cexpect_map`. -/
theorem offset_cexpect_eq_syracZ {n : ℕ} (freq : ZMod (3 ^ n)) :
    (geomHalf.iid n).cexpect (fun v => ZMod.stdAddChar (-(((fnat n v : ZMod (3 ^ n))
        * (2 : ZMod (3 ^ n))⁻¹ ^ pre v n) * freq)))
      = (syracZ n).cexpect (fun Y => ZMod.stdAddChar (-(Y * freq))) := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [syracZ_eq_rev_fnat n, cexpect_map _ _ _ (fun Y => le_of_eq (norm_stdAddChar _))]

/-- **Brick (b), the head factor as a level-`j` Syracuse character sum** (C10, Stage A wrapped). The
head character factor from `cond_char_factor` equals the level-`j` `syracZ` character sum at the
reduced frequency `2⁻ˡ·(ξ mod 3ʲ)`. Chains `head_char_descent` (pointwise Stage-A descent) through
`offset_cexpect_eq_syracZ` (the `iid j → syracZ j` pushforward). Stage B (`syracZ_char_eq_charFn`)
then peels the `3`-valuation of the reduced frequency off to `charFn_decay`. -/
theorem head_factor_eq_syracZ {j p : ℕ} (l : ℕ) (ξ : ZMod (3 ^ (j + p))) :
    (geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))
      = (syracZ j).cexpect (fun Y => ZMod.stdAddChar (-(Y
          * ((2 : ZMod (3 ^ j))⁻¹ ^ l
            * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right j p)) (ZMod (3 ^ j)) ξ)))) := by
  rw [congrArg (PMF.cexpect (geomHalf.iid j))
      (funext (fun vh : Fin j → ℕ => head_char_descent l ξ vh))]
  exact offset_cexpect_eq_syracZ _

/-- **Brick (b), the Syracuse character descent to `charFn_decay` form** (C10, Stage B + `eC`). For a
level-`(j'+q)` `syracZ` character sum at a frequency `3ʲ'·η` (valuation `j'`), the sum equals the
level-`q` Syracuse character sum in `charFn_decay`'s exact `eC` form at the reduced frequency
`castHom η`. Chains `syracZ_char_descent` (the consistency descent, level `j'+q → q`) with
`stdAddChar_mul_eq_eC`. So `charFn_decay` (Prop 1.17) bounds it `≤ Cₐ·q⁻ᴬ` when `3 ∤ (castHom η).val`. -/
theorem syracZ_char_eq_charFn {j' q : ℕ} (η : ZMod (3 ^ (j' + q))) :
    (syracZ (j' + q)).cexpect (fun Y => ZMod.stdAddChar (-(Y
        * ((3 : ZMod (3 ^ (j' + q))) ^ j' * η))))
      = (syracZ q).cexpect (fun Y' => eC (-(((ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j'))
          (ZMod (3 ^ q)) η).val) * Y'.val : ℚ) / 3 ^ q)) := by
  rw [syracZ_char_descent]
  exact congrArg (PMF.cexpect (syracZ q)) (funext (fun Y' => stdAddChar_mul_eq_eC _ Y'))

/-- **Brick (b), the head-factor ⟹ `charFn_decay` capstone** (C10). For a high frequency `ξ` at
level `(j'+q)+p` whose reduced frequency `2⁻ˡ·(ξ mod 3^(j'+q))` factors as `3ʲ'·η` (valuation `j'`,
cofactor `η`, encoded by `hfreq`), the head character factor from `cond_char_factor` equals **exactly**
a level-`q` Syracuse character sum in `charFn_decay`'s `eC` form at `castHom η`. Chains
`head_factor_eq_syracZ` (Stage A → `syracZ (j'+q)`), the `hfreq` frequency decomposition, and
`syracZ_char_eq_charFn` (Stage B: the consistency descent `j'+q → q` + `eC`). This is the head-block
analog of `tail_factor_eq_charFn`, and — via the `syracZ_char_descent` novelty — the object on which
`charFn_decay` (Prop 1.17) delivers the `q⁻ᴬ` decay of the C10 high-entropy factor. -/
theorem head_factor_eq_charFn {j' q p : ℕ} (l : ℕ) (ξ : ZMod (3 ^ ((j' + q) + p)))
    (η : ZMod (3 ^ (j' + q)))
    (hfreq : (2 : ZMod (3 ^ (j' + q)))⁻¹ ^ l
        * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right (j' + q) p)) (ZMod (3 ^ (j' + q))) ξ
      = (3 : ZMod (3 ^ (j' + q))) ^ j' * η) :
    (geomHalf.iid (j' + q)).cexpect (fun vh => ZMod.stdAddChar
        (-((3 ^ p * ((fnat (j' + q) vh : ZMod (3 ^ ((j' + q) + p)))
          * (2 : ZMod (3 ^ ((j' + q) + p)))⁻¹ ^ pre vh (j' + q))
          * (2 : ZMod (3 ^ ((j' + q) + p)))⁻¹ ^ l) * ξ)))
      = (syracZ q).cexpect (fun Y' => eC (-(((ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j'))
          (ZMod (3 ^ q)) η).val) * Y'.val : ℚ) / 3 ^ q)) := by
  rw [head_factor_eq_syracZ, hfreq, syracZ_char_eq_charFn]

/-- **Brick (b), the head-factor decay bound** (C10): the head character factor decays polynomially
`≤ Cₐ·q⁻ᴬ` whenever the reduced-frequency cofactor `η` (valuation `j'`) is `3`-coprime after the
final descent. Immediate from `head_factor_eq_charFn` + `charFn_decay` (Prop 1.17). Together with the
tail factor's `≤ 1` bound, this is the per-frequency decay of `‖𝓕(densC condDens) ξ‖`. -/
theorem head_factor_norm_le_charFn (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ (j' q p l : ℕ), 1 ≤ q → ∀ (ξ : ZMod (3 ^ ((j' + q) + p)))
      (η : ZMod (3 ^ (j' + q))),
      (2 : ZMod (3 ^ (j' + q)))⁻¹ ^ l
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right (j' + q) p)) (ZMod (3 ^ (j' + q))) ξ
        = (3 : ZMod (3 ^ (j' + q))) ^ j' * η →
      ¬ (3 ∣ (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j')) (ZMod (3 ^ q)) η).val) →
      ‖(geomHalf.iid (j' + q)).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat (j' + q) vh : ZMod (3 ^ ((j' + q) + p)))
            * (2 : ZMod (3 ^ ((j' + q) + p)))⁻¹ ^ pre vh (j' + q))
            * (2 : ZMod (3 ^ ((j' + q) + p)))⁻¹ ^ l) * ξ)))‖
        ≤ C * (q : ℝ) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := charFn_decay A hA
  refine ⟨C, hC0, fun j' q p l hq ξ η hfreq hη => ?_⟩
  rw [head_factor_eq_charFn l ξ η hfreq]
  exact hC q hq _ hη



/-- **Brick (b), the head-factor `≤ 1` bound** (C10): the head character factor is a character
expectation, hence has norm `≤ 1` (`cexpect_norm_le` + `norm_stdAddChar`). The low-entropy factor. -/
theorem head_factor_norm_le {j p : ℕ} (ξ : ZMod (3 ^ (j + p))) (l : ℕ) :
    ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))‖ ≤ 1 := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact cexpect_norm_le _ _ (fun vh => le_of_eq (norm_stdAddChar _))

/-- **Brick (b), step 3 — the conditional character factorization** (C10). Fix the cut
`n = j + p` and the level `l`. Conditioning the character sum on the tail-valuation event
`{pre(tail) = l}` makes the split character factor into a **pure head expectation** times a
**pure tail expectation** (the tail carrying the indicator). This is `char_offset_split`
(pointwise additive→multiplicative split) fed through `cexpect_iid_append` (iid block
independence): on `{pre(tail) = l}` the residual coupling `2⁻ᵖʳᵉ⁽ᵗᵃⁱˡ⁾` in the head factor is
frozen to the constant `2⁻ˡ`, so the head factor becomes head-coordinate-only and the two blocks
separate. The tail expectation is a level-`p` Syracuse character sum (ready for `charFn_decay`);
the head expectation has norm `≤ 1`. -/
theorem cond_char_factor {j p : ℕ} (ξ : ZMod (3 ^ (j + p))) (l : ℕ) :
    (geomHalf.iid (j + p)).cexpect
        (fun a => ZMod.stdAddChar (-(((fnat (j + p) a : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p)) * ξ))
          * (if pre (fun i => a (Fin.natAdd j i)) p = l then 1 else 0))
      = (geomHalf.iid j).cexpect
            (fun vh => ZMod.stdAddChar (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
                  * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
                  * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))
        * (geomHalf.iid p).cexpect
            (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
                  * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
              * (if pre vt p = l then 1 else 0)) := by
  -- head-block observable (pure function of the first `j` coordinates)
  set f : (Fin j → ℕ) → ℂ := fun vh => ZMod.stdAddChar (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
      * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)) with hf
  -- tail-block observable (pure function of the last `p` coordinates), carrying the indicator
  set g : (Fin p → ℕ) → ℂ := fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
      * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ)) * (if pre vt p = l then 1 else 0) with hg
  have hfb : ∀ vh, ‖f vh‖ ≤ 1 := fun vh => le_of_eq (norm_stdAddChar _)
  have hgb : ∀ vt, ‖g vt‖ ≤ 1 := fun vt => by
    simp only [hg]
    by_cases h : pre vt p = l
    · rw [if_pos h, mul_one]; exact le_of_eq (norm_stdAddChar _)
    · rw [if_neg h, mul_zero, norm_zero]; exact zero_le_one
  rw [← PMF.cexpect_iid_append geomHalf j p f g hfb hgb]
  refine congrArg (PMF.cexpect (geomHalf.iid (j + p))) ?_
  funext a
  simp only [hf, hg]
  by_cases h : pre (fun i => a (Fin.natAdd j i)) p = l
  · -- on the event: the split character factors and the frozen tail-valuation `l` matches
    rw [char_offset_split a ξ, pre_castAdd a (le_refl j), h, if_pos rfl]
    ring
  · -- off the event: both sides vanish through the indicator
    simp only [if_neg h, mul_zero]

/-- **DFT of a conditioned pushforward density** (general engine, C10 brick b). For any PMF `P`
on `Fin n → ℕ`, any random variable `X` into `ZMod (3ⁿ)`, and any event `w`, the DFT of the density
`Y ↦ P(X = Y ∧ w)` equals the conditioned character sum `E[stdAddChar(-(X·ξ))·1_w]`. This is the
`𝓕(densC g) ↔ cexpect` bridge that connects the proved Cauchy–Schwarz bridge `osc_le_sqrt_highfreq`
(applied to the conditioned density) with the factorization `cond_char_factor`. Proof: `dft_apply`
unfolds `𝓕` to `∑_Y stdAddChar(-(Y·ξ))·g(Y)`; push `Complex.ofReal_tsum` through `g(Y)=∑'_a …`;
swap the finite `∑_Y` with `∑'_a` (`Summable.tsum_finsetSum`, summability from the iid mass
dominating the bounded observable); collapse `∑_Y stdAddChar(-(Y·ξ))·1_{X=Y}=stdAddChar(-(X·ξ))`
(`Finset.sum_ite_eq`). -/
theorem dft_cond_density {ι : Type*} {n : ℕ} (P : PMF ι) (X : ι → ZMod (3 ^ n))
    (w : ι → Prop) [DecidablePred w] (ξ : ZMod (3 ^ n)) :
    ZMod.dft (densC n (fun Y =>
        ∑' a, (P a).toReal * (if X a = Y ∧ w a then (1 : ℝ) else 0))) ξ
      = P.cexpect (fun a => ZMod.stdAddChar (-(X a * ξ)) * (if w a then (1 : ℂ) else 0)) := by
  classical
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  have hbase : Summable (fun a => (P a).toReal) :=
    ENNReal.summable_toReal (by rw [P.tsum_coe]; exact ENNReal.one_ne_top)
  have hsum : ∀ Y : ZMod (3 ^ n), Summable (fun a => ZMod.stdAddChar (-(Y * ξ))
      * (((P a).toReal : ℂ) * ((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ))) := by
    intro Y
    refine Summable.of_norm_bounded hbase (fun a => ?_)
    rw [norm_mul, norm_mul, norm_stdAddChar, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    have hle : ‖((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; by_cases h : X a = Y ∧ w a
      · rw [if_pos h]; simp
      · rw [if_neg h]; simp
    calc (P a).toReal * ‖((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ)‖
        ≤ (P a).toReal * 1 := mul_le_mul_of_nonneg_left hle ENNReal.toReal_nonneg
      _ = (P a).toReal := mul_one _
  -- the inner finite sum over `Y` collapses onto `Y = X a`
  have hcore : ∀ a : ι, (∑ Y, ZMod.stdAddChar (-(Y * ξ))
        * ((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ))
      = ZMod.stdAddChar (-(X a * ξ)) * (if w a then (1 : ℂ) else 0) := by
    intro a
    by_cases h : w a
    · simp only [h, and_true, if_pos h, mul_one, apply_ite (Complex.ofReal), Complex.ofReal_one,
        Complex.ofReal_zero, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ (X a) (fun Y => ZMod.stdAddChar (-(Y * ξ)))]
      simp
    · simp only [h, and_false, if_false, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]
  -- push the ofReal through the inner tsum, pull the (Y-constant) character into it
  have hterm : ∀ Y : ZMod (3 ^ n),
      ZMod.stdAddChar (-(Y * ξ)) * ((∑' a, (P a).toReal
          * (if X a = Y ∧ w a then (1 : ℝ) else 0) : ℝ) : ℂ)
        = ∑' a, ZMod.stdAddChar (-(Y * ξ)) * (((P a).toReal : ℂ)
          * ((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ)) := by
    intro Y
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr (fun a => ?_); push_cast; ring
  rw [ZMod.dft_apply, PMF.cexpect]
  simp only [smul_eq_mul, densC]
  -- swap ∑_Y with ∑'_a, then collapse and refactor
  rw [Finset.sum_congr rfl (fun Y _ => hterm Y), ← Summable.tsum_finsetSum (fun Y _ => hsum Y)]
  refine tsum_congr (fun a => ?_)
  rw [show (fun Y => ZMod.stdAddChar (-(Y * ξ)) * (((P a).toReal : ℂ)
        * ((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ)))
      = (fun Y => ((P a).toReal : ℂ) * (ZMod.stdAddChar (-(Y * ξ))
        * ((if X a = Y ∧ w a then (1 : ℝ) else 0 : ℝ) : ℂ))) from by funext Y; ring,
    ← Finset.mul_sum, hcore a]

/-- The **conditioned density** `g_{j,p,l}` (Tao's `g_{n,k,l}` with cut `n = j + p`): the sub-PMF
of `Xₙ = Fnat(a)·2⁻ᵖʳᵉ` restricted to the tail-valuation event `{pre(tail) = l}`, as a real density. -/
noncomputable def condDens (j p l : ℕ) : ZMod (3 ^ (j + p)) → ℝ := fun Y =>
  ∑' a : Fin (j + p) → ℕ, ((geomHalf.iid (j + p)) a).toReal
    * (if (fnat (j + p) a : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p) = Y
          ∧ pre (fun i => a (Fin.natAdd j i)) p = l then (1 : ℝ) else 0)

/-- **Brick (b), the DFT↔cexpect bridge specialized to `condDens`** (C10): the DFT of the
conditioned Syracuse density is exactly the character sum `cond_char_factor` factors into head ×
tail. Immediate from the general `dft_cond_density` at `P = iid geomHalf`, `X = syracOffset`,
`w = {pre(tail)=l}`. -/
theorem dft_condDens_eq_cond_char (j p l : ℕ) (ξ : ZMod (3 ^ (j + p))) :
    ZMod.dft (densC (j + p) (condDens j p l)) ξ
      = (geomHalf.iid (j + p)).cexpect (fun a =>
          ZMod.stdAddChar (-(((fnat (j + p) a : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p)) * ξ))
            * (if pre (fun i => a (Fin.natAdd j i)) p = l then 1 else 0)) :=
  dft_cond_density (geomHalf.iid (j + p))
    (fun a => (fnat (j + p) a : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p))
    (fun a => pre (fun i => a (Fin.natAdd j i)) p = l) ξ

/-- **The `l`-marginalization of the conditioned density** (C10, the (6.9) innermost identity):
summing `condDens j p l` over all tail-valuations `l ∈ ℕ` recovers the real Syracuse density at
level `j + p`. This is `∑_l g_{n,k,l} = (marginal density)` — the identity on which the event
telescope of `fine_scale_mixing` will rest (the partition `⨆_l {pre(tail) = l}` of the sample
space is exhaustive, so conditioning on it loses no mass). Proof: `syracZ = (iid).map offset`
(`syracZ_eq_rev_fnat`), lift both sides to `ENNReal`, Tonelli-swap `∑_l` inside the `iid`-tsum
(`ENNReal.tsum_comm`), and collapse `∑_l 1_{pre(tail)=l} = 1` (single point). -/
theorem syracZ_eq_tsum_condDens (j p : ℕ) (Y : ZMod (3 ^ (j + p))) :
    ((syracZ (j + p)) Y).toReal = ∑' l : ℕ, condDens j p l Y := by
  classical
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  -- each per-`l` indicator term of `condDens` is finite in `ENNReal`
  have hGne : ∀ (a : Fin (j + p) → ℕ) (l : ℕ),
      (geomHalf.iid (j + p)) a
        * (if (fnat (j + p) a : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p) = Y
              ∧ pre (fun i => a (Fin.natAdd j i)) p = l then (1 : ENNReal) else 0) ≠ ⊤ :=
    fun a l => ENNReal.mul_ne_top ((geomHalf.iid (j + p)).apply_ne_top a) (by split <;> simp)
  -- `condDens j p l Y` is the `toReal` of the ENNReal `a`-sum of that family
  have hcond : ∀ l : ℕ, condDens j p l Y
      = (∑' a, (geomHalf.iid (j + p)) a
          * (if (fnat (j + p) a : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p) = Y
                ∧ pre (fun i => a (Fin.natAdd j i)) p = l then (1 : ENNReal) else 0)).toReal := by
    intro l
    simp only [condDens]
    rw [ENNReal.tsum_toReal_eq (fun a => hGne a l)]
    refine tsum_congr (fun a => ?_)
    rw [ENNReal.toReal_mul]
    congr 1
    split <;> simp
  -- the `a`-sums are finite (bounded by `∑'_a iid a = 1`)
  have hFne : ∀ l : ℕ, (∑' a, (geomHalf.iid (j + p)) a
        * (if (fnat (j + p) a : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p) = Y
              ∧ pre (fun i => a (Fin.natAdd j i)) p = l then (1 : ENNReal) else 0)) ≠ ⊤ := by
    intro l
    refine ne_top_of_le_ne_top (b := ∑' a, (geomHalf.iid (j + p)) a)
      (by rw [(geomHalf.iid (j + p)).tsum_coe]; exact ENNReal.one_ne_top) ?_
    refine ENNReal.tsum_le_tsum (fun a => ?_)
    exact le_trans (mul_le_mul_left' (by split <;> simp) _) (le_of_eq (mul_one _))
  -- collapse the `l`-sum of the tail-valuation indicator to the pure offset indicator
  have hcollapse : ∀ a : Fin (j + p) → ℕ,
      (∑' l : ℕ, (if (fnat (j + p) a : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p) = Y
              ∧ pre (fun i => a (Fin.natAdd j i)) p = l then (1 : ENNReal) else 0))
        = (if (fnat (j + p) a : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p) = Y
            then (1 : ENNReal) else 0) := by
    intro a
    by_cases h : (fnat (j + p) a : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p) = Y
    · simp only [h, true_and, if_true]
      rw [tsum_eq_single (pre (fun i => a (Fin.natAdd j i)) p) (fun l' hl' => by
        rw [if_neg]; exact fun hc => hl' hc.symm)]
      simp
    · simp only [h, false_and, if_false, tsum_zero]
  -- assemble: rewrite RHS via `hcond`, pull `toReal` outside, swap sums, collapse, match syracZ
  rw [tsum_congr hcond, ← ENNReal.tsum_toReal_eq hFne]
  congr 1
  rw [syracZ_eq_rev_fnat, PMF.map_apply, ENNReal.tsum_comm]
  refine tsum_congr (fun a => ?_)
  rw [ENNReal.tsum_mul_left, hcollapse a]
  split_ifs with h1 h2 h2
  · rw [mul_one]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rw [mul_zero]

/-- The **tail sub-density** `Y ↦ P(offset_p = Y ∧ pre = l)` at level `j+p`: the pushforward of the
level-`p` Syracuse offset (embedded in `ZMod (3^(j+p))`) restricted to the tail-valuation event. Its
DFT is the tail factor of `cond_char_factor` (`tail_factor_dft_eq`), so its collision entropy
`∑_Y (tailDens)²` controls the tail `ℓ²`-mass via Parseval (`tail_factor_l2_eq`). -/
noncomputable def tailDens (j p l : ℕ) : ZMod (3 ^ (j + p)) → ℝ := fun Y =>
  ∑' vt : Fin p → ℕ, ((geomHalf.iid p) vt).toReal
    * (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
          ∧ pre vt p = l then (1 : ℝ) else 0)

/-- The tail factor of `cond_char_factor` is the DFT of the tail sub-density `tailDens` (general
`dft_cond_density` at `P = iid geomHalf p`, `X = level-p offset`, `w = {pre = l}`; note the index `p`
differs from the modulus level `j+p`, which is why `dft_cond_density` is stated for a general index). -/
theorem tail_factor_dft_eq (j p l : ℕ) (ξ : ZMod (3 ^ (j + p))) :
    ZMod.dft (densC (j + p) (tailDens j p l)) ξ
      = (geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
          * (if pre vt p = l then 1 else 0)) :=
  dft_cond_density (geomHalf.iid p)
    (fun vt => (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p)
    (fun vt => pre vt p = l) ξ

/-- **(6.11) tail collision entropy** (C10): the total `ℓ²`-mass of the tail factor over all
frequencies equals the tail collision entropy `3^(j+p)·∑_Y (tailDens)²`, by Parseval
(`dft_parseval`) applied through `tail_factor_dft_eq`. This is the Rényi-2-entropy side of the C10
bound; combined with the head-factor decay it drives `∑_{high ξ}‖𝓕(densC condDens)‖²` small. -/
theorem tail_factor_l2_eq (j p l : ℕ) :
    ∑ ξ, ‖(geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ)) * (if pre vt p = l then 1 else 0))‖ ^ 2
      = (3 ^ (j + p) : ℝ) * ∑ Y, (tailDens j p l Y) ^ 2 := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h1 : ∀ ξ : ZMod (3 ^ (j + p)),
      (geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ)) * (if pre vt p = l then 1 else 0))
        = ZMod.dft (densC (j + p) (tailDens j p l)) ξ := fun ξ => (tail_factor_dft_eq j p l ξ).symm
  have hnorm : ∀ Y : ZMod (3 ^ (j + p)),
      ‖densC (j + p) (tailDens j p l) Y‖ ^ 2 = (tailDens j p l Y) ^ 2 := by
    intro Y; rw [densC, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [h1]
  rw [ZMod.dft_parseval (densC (j + p) (tailDens j p l))]
  simp_rw [hnorm]
  push_cast; ring

/-- **General collision-entropy reduction** (C10, the Rényi-2 skeleton): for a sub-density
`0 ≤ d Y ≤ M`, the collision entropy is `∑_Y (d Y)² ≤ M·∑_Y d Y`. Pointwise `(d Y)² = d Y·d Y ≤
M·d Y`. This reduces the tail Rényi count `∑(tailDens)²` to the single-point mass bound
`sup_Y tailDens Y ≤ M` (the genuine Syracuse near-uniformity / offset-injectivity content of Lemma
6.2), since `∑ tailDens ≤ 1` (`tailDens_sum_le_one`). -/
theorem sum_sq_le_max_mul_sum {N : ℕ} [NeZero N] (d : ZMod N → ℝ) (M : ℝ)
    (h0 : ∀ Y, 0 ≤ d Y) (hM : ∀ Y, d Y ≤ M) :
    ∑ Y, (d Y) ^ 2 ≤ M * ∑ Y, d Y := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun Y _ => ?_)
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hM Y) (h0 Y)

/-- The tail sub-density is nonnegative (a `tsum` of nonneg terms). -/
theorem tailDens_nonneg (j p l : ℕ) (Y : ZMod (3 ^ (j + p))) : 0 ≤ tailDens j p l Y := by
  refine tsum_nonneg (fun vt => ?_)
  exact mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num)

/-- The tail sub-density total mass is `≤ 1` (it is `P(pre = l) ≤ 1`): swap the finite `∑_Y` into the
`tsum`, collapse `∑_Y 1_{offset = Y ∧ pre = l} = 1_{pre = l} ≤ 1`, and use `∑' (iid) = 1`. -/
theorem tailDens_sum_le_one (j p l : ℕ) : ∑ Y, tailDens j p l Y ≤ 1 := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hbase : Summable (fun vt : Fin p → ℕ => ((geomHalf.iid p) vt).toReal) :=
    ENNReal.summable_toReal (by rw [(geomHalf.iid p).tsum_coe]; exact ENNReal.one_ne_top)
  have hone : ∑' vt : Fin p → ℕ, ((geomHalf.iid p) vt).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun vt => (geomHalf.iid p).apply_ne_top vt),
      (geomHalf.iid p).tsum_coe]; rfl
  have hsum : ∀ Y : ZMod (3 ^ (j + p)), Summable (fun vt : Fin p → ℕ =>
      ((geomHalf.iid p) vt).toReal
        * (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
              ∧ pre vt p = l then (1 : ℝ) else 0)) := by
    intro Y
    refine Summable.of_nonneg_of_le (fun vt => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun vt => ?_) hbase
    calc ((geomHalf.iid p) vt).toReal
          * (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
                ∧ pre vt p = l then (1 : ℝ) else 0)
        ≤ ((geomHalf.iid p) vt).toReal * 1 :=
          mul_le_mul_of_nonneg_left (by split <;> norm_num) ENNReal.toReal_nonneg
      _ = ((geomHalf.iid p) vt).toReal := mul_one _
  have hcollapse : ∀ vt : Fin p → ℕ,
      ∑ Y : ZMod (3 ^ (j + p)),
        (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
            ∧ pre vt p = l then (1 : ℝ) else 0)
        = (if pre vt p = l then (1 : ℝ) else 0) := by
    intro vt
    by_cases h : pre vt p = l
    · simp only [h, and_true, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp [h]
  calc ∑ Y, tailDens j p l Y
      = ∑' vt : Fin p → ℕ, ((geomHalf.iid p) vt).toReal
          * ∑ Y : ZMod (3 ^ (j + p)),
            (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
                ∧ pre vt p = l then (1 : ℝ) else 0) := by
        simp only [tailDens]
        rw [← Summable.tsum_finsetSum (fun Y _ => hsum Y)]
        refine tsum_congr (fun vt => ?_)
        rw [Finset.mul_sum]
    _ = ∑' vt : Fin p → ℕ, ((geomHalf.iid p) vt).toReal * (if pre vt p = l then (1 : ℝ) else 0) := by
        refine tsum_congr (fun vt => ?_); rw [hcollapse vt]
    _ ≤ ∑' vt : Fin p → ℕ, ((geomHalf.iid p) vt).toReal := by
        have hle : ∀ vt : Fin p → ℕ,
            ((geomHalf.iid p) vt).toReal * (if pre vt p = l then (1 : ℝ) else 0)
              ≤ ((geomHalf.iid p) vt).toReal := by
          intro vt
          calc ((geomHalf.iid p) vt).toReal * (if pre vt p = l then (1 : ℝ) else 0)
              ≤ ((geomHalf.iid p) vt).toReal * 1 :=
                mul_le_mul_of_nonneg_left (by split <;> norm_num) ENNReal.toReal_nonneg
            _ = ((geomHalf.iid p) vt).toReal := mul_one _
        refine Summable.tsum_le_tsum hle ?_ hbase
        exact Summable.of_nonneg_of_le
          (fun vt => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num)) hle hbase
    _ = 1 := hone

/-- **The tail Rényi count reduces to the single-point mass bound** (C10, obligation 3 skeleton).
Given a uniform bound `tailDens Y ≤ M` (the Syracuse near-uniformity / offset-injectivity of Lemma
6.2, the one genuinely-remaining input), the tail collision entropy is `∑_Y (tailDens)² ≤ M`. Immediate
from `sum_sq_le_max_mul_sum` + `tailDens_sum_le_one` (`∑ tailDens ≤ 1`) + `M ≥ 0`. So the whole tail
`ℓ²`-mass in `condDens_osc_le`'s `√` collapses to `M`, and the remaining analytic content of the
Rényi block is exactly `sup_Y tailDens Y ≤ M ≈ 3⁻ᵖ`. -/
theorem tailDens_renyi_le (j p l : ℕ) (M : ℝ) (hM : ∀ Y, tailDens j p l Y ≤ M) :
    ∑ Y, (tailDens j p l Y) ^ 2 ≤ M := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hM0 : 0 ≤ M := le_trans (tailDens_nonneg j p l 0) (hM 0)
  calc ∑ Y, (tailDens j p l Y) ^ 2
      ≤ M * ∑ Y, tailDens j p l Y :=
        sum_sq_le_max_mul_sum _ M (tailDens_nonneg j p l) hM
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (tailDens_sum_le_one j p l) hM0
    _ = M := mul_one M

/-- **Corollary 6.3 wrapper** (C10, obligation 3): the mod-`3^{j+p}` injectivity of the Syracuse
offset that `tailDens`'s single-point mass rests on, reduced to the **window bound** `fnat < 3^{j+p}`.
Given two positive-coordinate tuples of equal total valuation `l` whose offsets agree in
`ZMod (3^{j+p})`, and whose `fnat` values are both `< 3^{j+p}` (Tao's (6.14)→(6.15): the sub-Gaussian
window (6.12) forces the offset naturals below the modulus), the tuples are equal. Proof: cancel the
unit `(2⁻¹)^l` to get `fnat vt ≡ fnat vt' mod 3^{j+p}`; the two bounds upgrade the congruence to
natural equality (`Nat.mod_eq_of_lt`); then `fnat_inj_fixed_val` (Lemma 6.2) at valuation `l` closes.
The `< 3^{j+p}` bound is the sole remaining analytic content of the tail collision count — everything
else is now machine-checked. -/
theorem fnat_offset_zmod_inj {j p l : ℕ} (vt vt' : Fin p → ℕ)
    (hpos : ∀ i, 1 ≤ vt i) (hpos' : ∀ i, 1 ≤ vt' i)
    (hl : pre vt p = l) (hl' : pre vt' p = l)
    (hb : fnat p vt < 3 ^ (j + p)) (hb' : fnat p vt' < 3 ^ (j + p))
    (hoff : (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p
          = (fnat p vt' : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt' p) :
    vt = vt' := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [hl, hl'] at hoff
  have hunit : (2 : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ = 1 := by
    apply ZMod.mul_inv_of_unit
    rw [show (2 : ZMod (3 ^ (j + p))) = ((2 : ℕ) : ZMod (3 ^ (j + p))) from by norm_cast,
      ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (by decide)
  have hinv2 : (2 : ZMod (3 ^ (j + p)))⁻¹ * 2 = 1 := by rw [mul_comm]; exact hunit
  have hcast : (fnat p vt : ZMod (3 ^ (j + p))) = (fnat p vt' : ZMod (3 ^ (j + p))) := by
    have h := congrArg (· * (2 : ZMod (3 ^ (j + p))) ^ l) hoff
    simp only [mul_assoc, ← mul_pow, hinv2, one_pow, mul_one] at h
    exact h
  have hnat : fnat p vt = fnat p vt' := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
    rwa [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at this
  exact fnat_inj_fixed_val p vt vt' hpos hpos' (by rw [hl, hl']) hnat

/-- **Brick (b), the tail/indicator-factor `≤ 1` bound** (C10): the tail character factor from
`cond_char_factor` — which carries the conditioning indicator `1_{pre vt = l}` — is a character
expectation of a norm-`≤1` observable, so `‖tail factor‖ ≤ 1` (`cexpect_norm_le`). This is the
low-entropy (Rényi) block; its `ℓ²`-mass is controlled separately by the collision-entropy count. -/
theorem tail_indicator_factor_norm_le {j p : ℕ} (ξ : ZMod (3 ^ (j + p))) (l : ℕ) :
    ‖(geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
        * (if pre vt p = l then 1 else 0))‖ ≤ 1 := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  refine cexpect_norm_le _ _ (fun vt => ?_)
  by_cases h : pre vt p = l
  · rw [if_pos h, mul_one]; exact le_of_eq (norm_stdAddChar _)
  · rw [if_neg h, mul_zero, norm_zero]; exact zero_le_one

/-- **Brick (b), the per-frequency DFT decay of the conditioned density** (C10). For a high
frequency `ξ` (level `(j'+q)+p`) whose reduced frequency factors as `3ʲ'·η` (encoded by `hfreq`) with
`3`-coprime cofactor after the descent (`hη`), the DFT of the conditioned density decays
`≤ Cₐ·q⁻ᴬ`. This is the product bound `‖𝓕(densC condDens) ξ‖ = ‖head · tail‖ ≤ (Cₐ·q⁻ᴬ)·1`:
`dft_condDens_eq_cond_char` + `cond_char_factor` split it into the decaying head factor
(`head_factor_norm_le_charFn`, the DECAY block) and the `≤1` tail/indicator factor
(`tail_indicator_factor_norm_le`, the Rényi block). It is the per-`ξ` input to the `ℓ²`-mass count. -/
theorem dft_condDens_norm_le (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ (j' q p l : ℕ), 1 ≤ q → ∀ (ξ : ZMod (3 ^ ((j' + q) + p)))
      (η : ZMod (3 ^ (j' + q))),
      (2 : ZMod (3 ^ (j' + q)))⁻¹ ^ l
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right (j' + q) p)) (ZMod (3 ^ (j' + q))) ξ
        = (3 : ZMod (3 ^ (j' + q))) ^ j' * η →
      ¬ (3 ∣ (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j')) (ZMod (3 ^ q)) η).val) →
      ‖ZMod.dft (densC ((j' + q) + p) (condDens (j' + q) p l)) ξ‖ ≤ C * (q : ℝ) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := head_factor_norm_le_charFn A hA
  refine ⟨C, hC0, fun j' q p l hq ξ η hfreq hη => ?_⟩
  rw [dft_condDens_eq_cond_char, cond_char_factor, norm_mul]
  have hCq : (0 : ℝ) ≤ C * (q : ℝ) ^ (-A) :=
    mul_nonneg hC0.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc ‖(geomHalf.iid (j' + q)).cexpect (fun vh => ZMod.stdAddChar
            (-((3 ^ p * ((fnat (j' + q) vh : ZMod (3 ^ ((j' + q) + p)))
              * (2 : ZMod (3 ^ ((j' + q) + p)))⁻¹ ^ pre vh (j' + q))
              * (2 : ZMod (3 ^ ((j' + q) + p)))⁻¹ ^ l) * ξ)))‖
        * ‖(geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar
            (-(((fnat p vt : ZMod (3 ^ ((j' + q) + p)))
              * (2 : ZMod (3 ^ ((j' + q) + p)))⁻¹ ^ pre vt p) * ξ))
            * (if pre vt p = l then 1 else 0))‖
      ≤ (C * (q : ℝ) ^ (-A)) * 1 :=
        mul_le_mul (hC j' q p l hq ξ η hfreq hη) (tail_indicator_factor_norm_le ξ l)
          (norm_nonneg _) hCq
    _ = C * (q : ℝ) ^ (-A) := mul_one _

/-- **Brick (b), the sharp `ℓ²`-mass refinement** (C10, (6.10)–(6.11)). Given a **uniform** head-factor
decay bound `D` over all high frequencies (`hunif` — the valuation bookkeeping: each high `ξ` has
residual descent level `q ≥ q_min`, so `‖head(ξ)‖ ≤ Cₐ·q_min⁻ᴬ =: D`), the high-frequency `ℓ²`-mass
of the conditioned density is `≤ D²·(tail collision entropy)`. Proof: per high `ξ`,
`𝓕(densC condDens)ξ = head·tail` (`dft_condDens_eq_cond_char` + `cond_char_factor`) so
`‖𝓕‖² = ‖head‖²‖tail‖² ≤ D²‖tail‖²`; sum, drop to all frequencies (nonneg), and apply the tail
Parseval `tail_factor_l2_eq`. This isolates the two genuinely-remaining obligations — establishing
`hunif` (uniform head decay) and bounding `∑(tailDens)²` (the Rényi/offset-injectivity count, Lemma
6.2) — behind a machine-checked reduction. -/
theorem condDens_highfreq_l2_le (j p l m : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hunif : ∀ ξ ∈ highFreq m (j + p),
      ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))‖ ≤ D) :
    ∑ ξ ∈ highFreq m (j + p), ‖ZMod.dft (densC (j + p) (condDens j p l)) ξ‖ ^ 2
      ≤ D ^ 2 * (3 ^ (j + p) : ℝ) * ∑ Y, (tailDens j p l Y) ^ 2 := by
  have hpt : ∀ ξ ∈ highFreq m (j + p),
      ‖ZMod.dft (densC (j + p) (condDens j p l)) ξ‖ ^ 2
        ≤ D ^ 2 * ‖(geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar
            (-(((fnat p vt : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
            * (if pre vt p = l then 1 else 0))‖ ^ 2 := by
    intro ξ hξ
    rw [dft_condDens_eq_cond_char, cond_char_factor, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hunif ξ hξ) 2)
      (sq_nonneg _)
  calc ∑ ξ ∈ highFreq m (j + p), ‖ZMod.dft (densC (j + p) (condDens j p l)) ξ‖ ^ 2
      ≤ ∑ ξ ∈ highFreq m (j + p), D ^ 2 * ‖(geomHalf.iid p).cexpect (fun vt =>
            ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
            * (if pre vt p = l then 1 else 0))‖ ^ 2 := Finset.sum_le_sum hpt
    _ = D ^ 2 * ∑ ξ ∈ highFreq m (j + p), ‖(geomHalf.iid p).cexpect (fun vt =>
            ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
            * (if pre vt p = l then 1 else 0))‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ D ^ 2 * ∑ ξ, ‖(geomHalf.iid p).cexpect (fun vt =>
            ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
            * (if pre vt p = l then 1 else 0))‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => sq_nonneg _)) (sq_nonneg _)
    _ = D ^ 2 * ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDens j p l Y) ^ 2) := by rw [tail_factor_l2_eq]
    _ = D ^ 2 * (3 ^ (j + p) : ℝ) * ∑ Y, (tailDens j p l Y) ^ 2 := by ring

/-- **Brick (b), the per-conditioning osc bound** (C10, (6.10)). Assembling the full Plancherel
chain: for a conditioned density `condDens j p l`, given the uniform head decay `D` (`hunif`), the
`3ᵐ`-scale oscillation is `≤ D·√(3^(j+p)·∑(tailDens)²)` — the Cauchy–Schwarz/Parseval bridge
`osc_le_sqrt_highfreq` on the sharp `ℓ²`-refinement `condDens_highfreq_l2_le`. This is Tao's (6.10)
for a single conditioning `(k,l)`, machine-checked modulo the two remaining obligations (`hunif`
uniform head decay + the tail collision-entropy count inside the `√`). The event assembly (6.1)–(6.8)
then telescopes these single-conditioning bounds into `fine_scale_mixing`. -/
theorem condDens_osc_le (j p l m : ℕ) (hmn : m ≤ j + p) (D : ℝ) (hD : 0 ≤ D)
    (hunif : ∀ ξ ∈ highFreq m (j + p),
      ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))‖ ≤ D) :
    osc m (j + p) hmn (condDens j p l)
      ≤ D * Real.sqrt ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDens j p l Y) ^ 2) := by
  calc osc m (j + p) hmn (condDens j p l)
      ≤ Real.sqrt (∑ ξ ∈ highFreq m (j + p),
          ‖ZMod.dft (densC (j + p) (condDens j p l)) ξ‖ ^ 2) :=
        osc_le_sqrt_highfreq _ _ _ _
    _ ≤ Real.sqrt (D ^ 2 * ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDens j p l Y) ^ 2)) := by
        apply Real.sqrt_le_sqrt
        rw [← mul_assoc]
        exact condDens_highfreq_l2_le j p l m D hD hunif
    _ = D * Real.sqrt ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDens j p l Y) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD]


/-- **Proposition 1.14** (fine-scale mixing): the `Syrac(ℤ/3ⁿℤ)` density oscillates
little at scale `3ᵐ`, uniformly with polynomial decay `m^{-A}` for every `A`.

The Cauchy–Schwarz/Parseval bridge `osc_le_sqrt_highfreq` is proved (axiom-clean), but the naive
`highfreq_l2_le` route is REFUTED (see the route finding above): the raw high-frequency `L²` mass
grows, so the bound must go through Tao's §6 **conditioning** of the density (independent `F`-split
+ `charFn_decay` on the high-entropy factor + triangle inequality over the events). This is the
genuine heroic §6 core; `sorry` pending that apparatus. -/
theorem fine_scale_mixing (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n m : ℕ, ∀ hmn : m ≤ n, 1 ≤ m →
      osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ C * (m : ℝ) ^ (-A) := by
  sorry

end TaoCollatz
