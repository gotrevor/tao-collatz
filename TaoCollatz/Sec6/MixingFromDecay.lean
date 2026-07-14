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
`cond_char_factor` carries a `3ᵖ` block-scaling prefactor (at the *low* end of the modulus) and the
frozen tail-valuation phase `2⁻ˡ`. For a high frequency `ξ = 3ʲ'·2ˡ·ξ'`, the `2⁻ˡ·2ˡ = 1`
cancellation removes the frozen phase, and the `3ᵖ` prefactor descends the character from level
`j+p` down to level `j`, landing the head offset `Fnat_j(vh)·2⁻ᵖʳᵉ` at level `j` as a genuine
level-`j` Syracuse character at the frequency `3ʲ'·(ξ' mod 3ʲ)`. Proof: `ring`-fold the `2⁻ˡ·2ˡ`
into a single factor and cancel it, then `stdAddChar_pow3_descent_right` (right-summand descent) +
push `castHom` through the offset (`castHom_two_inv_right`, `map_ofNat`). This is Stage A; Stage B is
`syracZ_char_descent`, which then descends the `3ʲ'` valuation to `charFn_decay`'s level `j - j'`. -/
theorem head_char_descent {j p : ℕ} (j' l : ℕ) (ξ' : ZMod (3 ^ (j + p))) (vh : Fin j → ℕ) :
    ZMod.stdAddChar (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l)
        * ((3 : ZMod (3 ^ (j + p))) ^ j' * (2 : ZMod (3 ^ (j + p))) ^ l * ξ')))
      = ZMod.stdAddChar (-(((fnat j vh : ZMod (3 ^ j))
        * (2 : ZMod (3 ^ j))⁻¹ ^ pre vh j)
        * ((3 : ZMod (3 ^ j)) ^ j'
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right j p)) (ZMod (3 ^ j)) ξ'))) := by
  have hunit : (2 : ZMod (3 ^ (j + p)))⁻¹ * (2 : ZMod (3 ^ (j + p))) = 1 := by
    rw [mul_comm]; apply ZMod.mul_inv_of_unit
    rw [show (2 : ZMod (3 ^ (j + p))) = ((2 : ℕ) : ZMod (3 ^ (j + p))) by norm_cast,
      ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (by decide)
  have hcancel : (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l * (2 : ZMod (3 ^ (j + p))) ^ l = 1 := by
    rw [← mul_pow, hunit, one_pow]
  have harg : -((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l)
        * ((3 : ZMod (3 ^ (j + p))) ^ j' * (2 : ZMod (3 ^ (j + p))) ^ l * ξ'))
      = (3 : ZMod (3 ^ (j + p))) ^ p * (-(((fnat j vh : ZMod (3 ^ (j + p)))
        * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
        * ((3 : ZMod (3 ^ (j + p))) ^ j' * ξ'))) := by
    have hfold : (3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l)
          * ((3 : ZMod (3 ^ (j + p))) ^ j' * (2 : ZMod (3 ^ (j + p))) ^ l * ξ')
        = ((3 : ZMod (3 ^ (j + p))) ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
          * ((3 : ZMod (3 ^ (j + p))) ^ j' * ξ'))
          * ((2 : ZMod (3 ^ (j + p)))⁻¹ ^ l * (2 : ZMod (3 ^ (j + p))) ^ l) := by ring
    rw [hfold, hcancel, mul_one]; ring
  rw [harg, stdAddChar_pow3_descent_right]
  congr 1
  simp only [map_neg, map_mul, map_pow, map_natCast, castHom_two_inv_right, map_ofNat]

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
theorem dft_cond_density {n : ℕ} (P : PMF (Fin n → ℕ)) (X : (Fin n → ℕ) → ZMod (3 ^ n))
    (w : (Fin n → ℕ) → Prop) [DecidablePred w] (ξ : ZMod (3 ^ n)) :
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
  have hcore : ∀ a : Fin n → ℕ, (∑ Y, ZMod.stdAddChar (-(Y * ξ))
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
