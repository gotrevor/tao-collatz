import TaoCollatz.Fourier.ZMod3
import TaoCollatz.Fourier.Parseval
import TaoCollatz.Syracuse.SyracRV
import TaoCollatz.Sec7.Decay
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Chebyshev

/-!
# §6 core: fine-scale mixing from character decay (node C10) — Prop 1.14

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

/-- The `3ᵐ`-scale fiber has exactly `3^{n-m}` points (the `castHom` kernel size): it is the image
of `t ↦ Y + t·3ᵐ` over `range (3^{n-m})` (`fiber_char_reindex`'s injective reindexing), so
`card = 3^{n-m}`. Used for the `L¹`-contraction of the conditional-average (`osc_le_two_mul_l1`). -/
theorem fiber_card (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (3 ^ n)) :
    (fiber m n hmn Y).card = 3 ^ (n - m) := by
  classical
  have h3m : (3 ^ m : ZMod (3 ^ n)) = ((3 ^ m : ℕ) : ZMod (3 ^ n)) := by push_cast; ring
  have hcast3m : ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) (3 ^ m : ZMod (3 ^ n)) = 0 := by
    rw [h3m, map_natCast]; exact ZMod.natCast_self _
  set g : ℕ → ZMod (3 ^ n) := fun t => Y + (t : ZMod (3 ^ n)) * (3 ^ m : ZMod (3 ^ n)) with hg
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
  rw [hfib_eq, Finset.card_image_of_injOn hginj, Finset.card_range]

/-- Equation (1.22), in pointwise fiber form: summing the level-`n` Syracuse law over
the `castHom`-fiber above `Y` gives the level-`m` law at the projection of `Y`.

This is the exact consistency identity needed by Tao's final scale telescope in §6. -/
theorem fiber_syracZ_sum (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (3 ^ n)) :
    ∑ Y' ∈ fiber m n hmn Y, ((syracZ n) Y').toReal =
      ((syracZ m) (ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y)).toReal := by
  classical
  let π : ZMod (3 ^ n) → ZMod (3 ^ m) :=
    ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m))
  have hmap := congrArg
    (fun p : PMF (ZMod (3 ^ m)) => (p (π Y)).toReal)
    (syracZ_map_cast hmn)
  rw [PMF.map_apply,
    tsum_eq_sum (s := Finset.univ) (fun a ha => absurd (Finset.mem_univ a) ha),
    ENNReal.toReal_sum (fun a _ => by
      split
      · exact (syracZ n).apply_ne_top a
      · exact ENNReal.zero_ne_top)] at hmap
  simpa only [fiber, Finset.sum_filter, apply_ite ENNReal.toReal,
    ENNReal.toReal_zero, eq_comm, π] using hmap

/-- The level-`m` Syracuse density, lifted uniformly to level `n`. -/
noncomputable def syracLift (m n : ℕ) (hmn : m ≤ n) (Y : ZMod (3 ^ n)) : ℝ :=
  (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
    ((syracZ m) (ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y)).toReal

/-- The oscillation of `syracZ n` is exactly its `L¹` distance from the uniform lift of
the projected law `syracZ m`. This exposes the metric form used in the scale telescope. -/
theorem osc_syracZ_eq_l1_lift (m n : ℕ) (hmn : m ≤ n) :
    osc m n hmn (fun Y => ((syracZ n) Y).toReal) =
      ∑ Y, |((syracZ n) Y).toReal - syracLift m n hmn Y| := by
  classical
  rw [osc]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  change |((syracZ n) Y).toReal - (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
      ∑ Y' ∈ fiber m n hmn Y, ((syracZ n) Y').toReal| = _
  rw [fiber_syracZ_sum]
  rfl

/-- Every fiber of the level projection has the expected cardinality. -/
theorem castFiber_card (m n : ℕ) (hmn : m ≤ n) (Z : ZMod (3 ^ m)) :
    (Finset.univ.filter (fun Y : ZMod (3 ^ n) =>
      ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y = Z)).card = 3 ^ (n - m) := by
  classical
  obtain ⟨Y, rfl⟩ := ZMod.castHom_surjective (pow_dvd_pow 3 hmn) Z
  simpa only [fiber] using fiber_card m n hmn Y

/-- Summing a function pulled back along `ZMod (3ⁿ) → ZMod (3ᵐ)` repeats every value
exactly `3^{n-m}` times. -/
theorem sum_comp_castHom (m n : ℕ) (hmn : m ≤ n) (f : ZMod (3 ^ m) → ℝ) :
    ∑ Y : ZMod (3 ^ n),
        f (ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y) =
      ((3 ^ (n - m) : ℕ) : ℝ) * ∑ Z, f Z := by
  classical
  let π : ZMod (3 ^ n) → ZMod (3 ^ m) :=
    ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m))
  calc
    ∑ Y, f (π Y) = ∑ Z, ∑ Y ∈ Finset.univ with π Y = Z, f (π Y) := by
      simpa using
        (Finset.sum_fiberwise (Finset.univ : Finset (ZMod (3 ^ n))) π (fun Y => f (π Y))).symm
    _ = ∑ Z, ((3 ^ (n - m) : ℕ) : ℝ) * f Z := by
      refine Finset.sum_congr rfl (fun Z _ => ?_)
      simp only [Finset.sum_filter]
      calc
        ∑ Y, (if π Y = Z then f (π Y) else 0) =
            ∑ Y, (if π Y = Z then f Z else 0) := by
          refine Finset.sum_congr rfl (fun Y _ => ?_)
          split_ifs with h
          · rw [h]
          · rfl
        _ = ((3 ^ (n - m) : ℕ) : ℝ) * f Z := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          congr 1
          norm_cast
          simpa only [π] using castFiber_card m n hmn Z
    _ = ((3 ^ (n - m) : ℕ) : ℝ) * ∑ Z, f Z := by
      rw [Finset.mul_sum]

/-- Uniform lifts compose across an intermediate scale. -/
theorem syracLift_tower (m k n : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) (Y : ZMod (3 ^ n)) :
    syracLift m n (hmk.trans hkn) Y =
      (3 : ℝ) ^ ((k : ℤ) - (n : ℤ)) *
        syracLift m k hmk
          (ZMod.castHom (pow_dvd_pow 3 hkn) (ZMod (3 ^ k)) Y) := by
  have hcast :
      ZMod.castHom (pow_dvd_pow 3 hmk) (ZMod (3 ^ m))
          (ZMod.castHom (pow_dvd_pow 3 hkn) (ZMod (3 ^ k)) Y) =
        ZMod.castHom (pow_dvd_pow 3 (hmk.trans hkn)) (ZMod (3 ^ m)) Y := by
    exact congrArg (fun f : ZMod (3 ^ n) →+* ZMod (3 ^ m) => f Y)
      (ZMod.castHom_comp (pow_dvd_pow 3 hmk) (pow_dvd_pow 3 hkn))
  rw [syracLift, syracLift, hcast]
  rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 2
  ring

/-- The `L¹` distance between two lifted laws is unchanged by lifting both to a finer level. -/
theorem sum_abs_syracLift_sub_lift (m k n : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) :
    ∑ Y : ZMod (3 ^ n),
        |syracLift k n hkn Y - syracLift m n (hmk.trans hkn) Y| =
      osc m k hmk (fun Z => ((syracZ k) Z).toReal) := by
  classical
  rw [osc_syracZ_eq_l1_lift]
  let π : ZMod (3 ^ n) → ZMod (3 ^ k) :=
    ZMod.castHom (pow_dvd_pow 3 hkn) (ZMod (3 ^ k))
  have hlift (Y : ZMod (3 ^ n)) :
      |syracLift k n hkn Y - syracLift m n (hmk.trans hkn) Y| =
        (3 : ℝ) ^ ((k : ℤ) - (n : ℤ)) *
          |((syracZ k) (π Y)).toReal - syracLift m k hmk (π Y)| := by
    rw [syracLift_tower m k n hmk hkn]
    change |(3 : ℝ) ^ ((k : ℤ) - (n : ℤ)) * ((syracZ k) (π Y)).toReal -
      (3 : ℝ) ^ ((k : ℤ) - (n : ℤ)) * syracLift m k hmk (π Y)| = _
    rw [← mul_sub, abs_mul, abs_of_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)]
  simp_rw [hlift]
  rw [← Finset.mul_sum]
  have hsum :
      ∑ i : ZMod (3 ^ n), |((syracZ k) (π i)).toReal - syracLift m k hmk (π i)| =
        ((3 ^ (n - k) : ℕ) : ℝ) *
          ∑ Z, |((syracZ k) Z).toReal - syracLift m k hmk Z| := by
    simpa only [π] using sum_comp_castHom k n hkn
      (fun Z => |((syracZ k) Z).toReal - syracLift m k hmk Z|)
  rw [hsum]
  rw [← mul_assoc]
  have hpow : ((3 ^ (n - k) : ℕ) : ℝ) = (3 : ℝ) ^ ((n : ℤ) - (k : ℤ)) := by
    rw [← Nat.cast_sub hkn, zpow_natCast]
    norm_cast
  rw [hpow, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  norm_num

/-- Triangle inequality across Syracuse projection scales. This is the exact metric consequence
of (1.22) used by the regime telescope on Tao p.28. -/
theorem osc_syracZ_levels_triangle (m k n : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) :
    osc m n (hmk.trans hkn) (fun Y => ((syracZ n) Y).toReal) ≤
      osc k n hkn (fun Y => ((syracZ n) Y).toReal) +
        osc m k hmk (fun Z => ((syracZ k) Z).toReal) := by
  rw [osc_syracZ_eq_l1_lift, osc_syracZ_eq_l1_lift]
  calc
    ∑ Y, |((syracZ n) Y).toReal - syracLift m n (hmk.trans hkn) Y| ≤
        ∑ Y, (|((syracZ n) Y).toReal - syracLift k n hkn Y| +
          |syracLift k n hkn Y - syracLift m n (hmk.trans hkn) Y|) := by
      exact Finset.sum_le_sum (fun Y _ => abs_sub_le _ _ _)
    _ = (∑ Y, |((syracZ n) Y).toReal - syracLift k n hkn Y|) +
        ∑ Y, |syracLift k n hkn Y - syracLift m n (hmk.trans hkn) Y| :=
      Finset.sum_add_distrib
    _ = (∑ Y, |((syracZ n) Y).toReal - syracLift k n hkn Y|) +
        osc m k hmk (fun Z => ((syracZ k) Z).toReal) := by
      rw [sum_abs_syracLift_sub_lift]

/-- **`L¹`-contraction of the oscillation** (C10, the error-term tool): the `3ᵐ`-scale oscillation
of a density `c` is at most twice its `L¹` mass, `osc(c) ≤ 2·∑_Y |c Y|`. The conditional average is
an `L¹`-contraction (`∑_Y ‖condAvgC Y‖ ≤ ∑_Y |c Y|`, via the `fiber_card` double-count), and
`devC = densC − condAvgC` gives the triangle bound. This is the lemma that turns "small total mass"
into "small oscillation" — the mechanism bounding the bad-event error `osc(syracZ − ∑ condDens) ≤
2·P(Ē)` in the §6 event telescope, and the finite-`l`-window truncation tail. -/
theorem osc_le_two_mul_l1 (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    osc m n hmn c ≤ 2 * ∑ Y, |c Y| := by
  classical
  rw [osc_eq_sum_norm_devC]
  have hnorm3 : ‖(3 : ℂ) ^ ((m : ℤ) - (n : ℤ))‖ = (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) := by
    rw [norm_zpow, Complex.norm_ofNat]
  have hdens : ∀ Y, ‖densC n c Y‖ = |c Y| := fun Y => by
    rw [densC, Complex.norm_real, Real.norm_eq_abs]
  have hcount : ∑ Y, ∑ Y' ∈ fiber m n hmn Y, |c Y'|
      = ((3 ^ (n - m) : ℕ) : ℝ) * ∑ Y', |c Y'| := by
    have h1 : ∀ Y, ∑ Y' ∈ fiber m n hmn Y, |c Y'|
        = ∑ Y', (if ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y'
              = ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y then |c Y'| else 0) := by
      intro Y; rw [fiber, Finset.sum_filter]
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Y' _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const]
    have hfeq : (Finset.univ.filter (fun Y => ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y'
          = ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y)) = fiber m n hmn Y' := by
      rw [fiber]; ext Y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
    rw [hfeq, fiber_card, nsmul_eq_mul]
  have hpow : ((3 ^ (n - m) : ℕ) : ℝ) = (3 : ℝ) ^ ((n : ℤ) - (m : ℤ)) := by
    rw [← Nat.cast_sub hmn, zpow_natCast]; push_cast; ring
  have hcond : ∑ Y, ‖condAvgC m n hmn c Y‖ ≤ ∑ Y, |c Y| := by
    have hpt : ∀ Y, ‖condAvgC m n hmn c Y‖
        ≤ (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ∑ Y' ∈ fiber m n hmn Y, |c Y'| := by
      intro Y
      rw [condAvgC, norm_mul, hnorm3]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖∑ Y' ∈ fiber m n hmn Y, densC n c Y'‖
          ≤ ∑ Y' ∈ fiber m n hmn Y, ‖densC n c Y'‖ := norm_sum_le _ _
        _ = ∑ Y' ∈ fiber m n hmn Y, |c Y'| := Finset.sum_congr rfl (fun Y' _ => hdens Y')
    calc ∑ Y, ‖condAvgC m n hmn c Y‖
        ≤ ∑ Y, (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ∑ Y' ∈ fiber m n hmn Y, |c Y'| :=
          Finset.sum_le_sum (fun Y _ => hpt Y)
      _ = (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) * ∑ Y, ∑ Y' ∈ fiber m n hmn Y, |c Y'| := by
          rw [Finset.mul_sum]
      _ = (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) * (((3 ^ (n - m) : ℕ) : ℝ) * ∑ Y', |c Y'|) := by rw [hcount]
      _ = ∑ Y', |c Y'| := by
          rw [hpow, ← mul_assoc, ← zpow_add₀ (by norm_num : (3:ℝ) ≠ 0)]
          norm_num
  calc ∑ Y, ‖devC m n hmn c Y‖
      ≤ ∑ Y, (‖densC n c Y‖ + ‖condAvgC m n hmn c Y‖) := by
        refine Finset.sum_le_sum (fun Y _ => ?_); rw [devC]; exact norm_sub_le _ _
    _ = (∑ Y, ‖densC n c Y‖) + ∑ Y, ‖condAvgC m n hmn c Y‖ := Finset.sum_add_distrib
    _ ≤ (∑ Y, |c Y|) + ∑ Y, |c Y| :=
        add_le_add (le_of_eq (Finset.sum_congr rfl (fun Y _ => hdens Y))) hcond
    _ = 2 * ∑ Y, |c Y| := by ring

/-- The real density of the finite Syracuse law has total mass one. -/
theorem sum_syracZ_toReal_eq_one (n : ℕ) :
    ∑ Y : ZMod (3 ^ n), ((syracZ n) Y).toReal = 1 := by
  have h : ∑' Y : ZMod (3 ^ n), ((syracZ n) Y).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun Y => (syracZ n).apply_ne_top Y),
      (syracZ n).tsum_coe, ENNReal.toReal_one]
  rw [tsum_eq_sum (s := (Finset.univ : Finset (ZMod (3 ^ n))))
    (fun Y hY => absurd (Finset.mem_univ Y) hY)] at h
  exact h

/-- The probability-density oscillation is uniformly at most two. -/
theorem osc_syracZ_le_two (m n : ℕ) (hmn : m ≤ n) :
    osc m n hmn (fun Y => ((syracZ n) Y).toReal) ≤ 2 := by
  calc
    osc m n hmn (fun Y => ((syracZ n) Y).toReal)
        ≤ 2 * ∑ Y, |((syracZ n) Y).toReal| := osc_le_two_mul_l1 m n hmn _
    _ = 2 * ∑ Y, ((syracZ n) Y).toReal := by
      congr 1
      exact Finset.sum_congr rfl (fun Y _ => abs_of_nonneg ENNReal.toReal_nonneg)
    _ = 2 := by rw [sum_syracZ_toReal_eq_one, mul_one]

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
theorem tail_factor_norm_le_at (A : ℝ) (hA : 0 < A) :
    ∀ (j p : ℕ), 1 ≤ p → ∀ (ζ : ZMod (3 ^ (j + p))),
      ¬ (3 ∣ (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p)) ζ).val) →
      ‖(geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ((3 : ZMod (3 ^ (j + p))) ^ j * ζ))))‖
        ≤ C_renewalWhite A * (p : ℝ) ^ (-A) := by
  have hC := charFn_decay_at A hA
  intro j p hp ζ hζ
  rw [tail_factor_eq_charFn]
  exact hC p hp _ hζ

/-- `tail_factor_norm_le`, original `∃`-form: delegates to the `_at` sibling at
`C_renewalWhite A` (big-C campaign, step 2). -/
theorem tail_factor_norm_le (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ (j p : ℕ), 1 ≤ p → ∀ (ζ : ZMod (3 ^ (j + p))),
      ¬ (3 ∣ (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left p j)) (ZMod (3 ^ p)) ζ).val) →
      ‖(geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ((3 : ZMod (3 ^ (j + p))) ^ j * ζ))))‖
        ≤ C * (p : ℝ) ^ (-A) :=
  ⟨C_renewalWhite A, C_renewalWhite_pos A, tail_factor_norm_le_at A hA⟩

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
theorem head_factor_norm_le_charFn_at (A : ℝ) (hA : 0 < A) :
    ∀ (j' q p l : ℕ), 1 ≤ q → ∀ (ξ : ZMod (3 ^ ((j' + q) + p)))
      (η : ZMod (3 ^ (j' + q))),
      (2 : ZMod (3 ^ (j' + q)))⁻¹ ^ l
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right (j' + q) p)) (ZMod (3 ^ (j' + q))) ξ
        = (3 : ZMod (3 ^ (j' + q))) ^ j' * η →
      ¬ (3 ∣ (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j')) (ZMod (3 ^ q)) η).val) →
      ‖(geomHalf.iid (j' + q)).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat (j' + q) vh : ZMod (3 ^ ((j' + q) + p)))
            * (2 : ZMod (3 ^ ((j' + q) + p)))⁻¹ ^ pre vh (j' + q))
            * (2 : ZMod (3 ^ ((j' + q) + p)))⁻¹ ^ l) * ξ)))‖
        ≤ C_renewalWhite A * (q : ℝ) ^ (-A) := by
  have hC := charFn_decay_at A hA
  intro j' q p l hq ξ η hfreq hη
  rw [head_factor_eq_charFn l ξ η hfreq]
  exact hC q hq _ hη

/-- `head_factor_norm_le_charFn`, original `∃`-form: delegates to the `_at` sibling at
`C_renewalWhite A` (big-C campaign, step 2). -/
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
        ≤ C * (q : ℝ) ^ (-A) :=
  ⟨C_renewalWhite A, C_renewalWhite_pos A, head_factor_norm_le_charFn_at A hA⟩



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
    · simp only [h, and_true, mul_one, apply_ite (Complex.ofReal), Complex.ofReal_one,
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
    exact le_trans (mul_le_mul_right (by split <;> simp) _) (le_of_eq (mul_one _))
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

/-- `pre vt p` over the full index range is the plain coordinate sum `∑ i, vt i`. -/
theorem pre_self_eq_sum_univ {p : ℕ} (vt : Fin p → ℕ) : pre vt p = ∑ i, vt i := by
  rw [pre, ← Fin.sum_univ_eq_sum_range (fun i => if h : i < p then vt ⟨i, h⟩ else 0) p]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt]

/-- **The windowed tail sub-density** (C10, obligation 3): `tailDens` carrying an additional
tail-measurable conditioning event `W` — the sub-Gaussian window (6.12) + the tight `Bₖ` budget,
per the 2026-07-14 reflection. The full §6 conditioning event `Eₖ ∧ Bₖ ∧ Cₖ,ₗ` depends only on
the tail block, so it is a predicate of exactly this shape; `W := fun _ => True` recovers
`tailDens`. -/
noncomputable def tailDensW (j p l : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W] :
    ZMod (3 ^ (j + p)) → ℝ := fun Y =>
  ∑' vt : Fin p → ℕ, ((geomHalf.iid p) vt).toReal
    * (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
          ∧ pre vt p = l ∧ W vt then (1 : ℝ) else 0)

/-- The windowed tail sub-density is nonnegative. -/
theorem tailDensW_nonneg (j p l : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W]
    (Y : ZMod (3 ^ (j + p))) : 0 ≤ tailDensW j p l W Y := by
  refine tsum_nonneg (fun vt => ?_)
  exact mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num)

/-- A tuple carrying nonzero `iid geomHalf` mass has all coordinates positive. -/
theorem geomHalf_iid_pos_coords {p : ℕ} {vt : Fin p → ℕ}
    (h : (geomHalf.iid p) vt ≠ 0) : ∀ i, 1 ≤ vt i := by
  intro i
  have hi := PMF.iid_support_coord geomHalf p vt (((geomHalf.iid p).mem_support_iff vt).mpr h) i
  rw [geomHalf.mem_support_iff, geomHalf_apply] at hi
  by_contra hcon
  have h0 : vt i = 0 := by omega
  rw [if_pos h0] at hi
  exact hi rfl

/-- The `iid geomHalf` mass of a positive tuple is exactly `2^{-(total valuation)}`. -/
theorem geomHalf_iid_apply_pos {p : ℕ} (vt : Fin p → ℕ) (hpos : ∀ i, 1 ≤ vt i) :
    (geomHalf.iid p) vt = (2 : ENNReal)⁻¹ ^ pre vt p := by
  rw [PMF.iid_apply_eq_prod,
    Finset.prod_congr rfl (fun i _ => by
      rw [geomHalf_apply, if_neg (by have := hpos i; omega)]),
    Finset.prod_pow_eq_pow_sum, pre_self_eq_sum_univ]

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

/-- The **windowed** tail sub-density total mass is `≤ 1` (it is `P(pre = l ∧ W) ≤ 1`): the exact
mirror of `tailDens_sum_le_one` carrying the extra conditioning conjunct `W vt`. Swap the finite `∑_Y`
into the `tsum`, collapse `∑_Y 1_{offset = Y ∧ pre = l ∧ W} = 1_{pre = l ∧ W} ≤ 1`, and use
`∑' (iid) = 1`. -/
theorem tailDensW_sum_le_one (j p l : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W] :
    ∑ Y, tailDensW j p l W Y ≤ 1 := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hbase : Summable (fun vt : Fin p → ℕ => ((geomHalf.iid p) vt).toReal) :=
    ENNReal.summable_toReal (by rw [(geomHalf.iid p).tsum_coe]; exact ENNReal.one_ne_top)
  have hone : ∑' vt : Fin p → ℕ, ((geomHalf.iid p) vt).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun vt => (geomHalf.iid p).apply_ne_top vt),
      (geomHalf.iid p).tsum_coe]; rfl
  have hsum : ∀ Y : ZMod (3 ^ (j + p)), Summable (fun vt : Fin p → ℕ =>
      ((geomHalf.iid p) vt).toReal
        * (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
              ∧ pre vt p = l ∧ W vt then (1 : ℝ) else 0)) := by
    intro Y
    refine Summable.of_nonneg_of_le (fun vt => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun vt => ?_) hbase
    calc ((geomHalf.iid p) vt).toReal
          * (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
                ∧ pre vt p = l ∧ W vt then (1 : ℝ) else 0)
        ≤ ((geomHalf.iid p) vt).toReal * 1 :=
          mul_le_mul_of_nonneg_left (by split <;> norm_num) ENNReal.toReal_nonneg
      _ = ((geomHalf.iid p) vt).toReal := mul_one _
  have hcollapse : ∀ vt : Fin p → ℕ,
      ∑ Y : ZMod (3 ^ (j + p)),
        (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
            ∧ pre vt p = l ∧ W vt then (1 : ℝ) else 0)
        = (if pre vt p = l ∧ W vt then (1 : ℝ) else 0) := by
    intro vt
    by_cases h : pre vt p = l ∧ W vt
    · simp only [h, and_true, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp only [h, and_false, if_false, Finset.sum_const_zero]
  calc ∑ Y, tailDensW j p l W Y
      = ∑' vt : Fin p → ℕ, ((geomHalf.iid p) vt).toReal
          * ∑ Y : ZMod (3 ^ (j + p)),
            (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
                ∧ pre vt p = l ∧ W vt then (1 : ℝ) else 0) := by
        simp only [tailDensW]
        rw [← Summable.tsum_finsetSum (fun Y _ => hsum Y)]
        refine tsum_congr (fun vt => ?_)
        rw [Finset.mul_sum]
    _ = ∑' vt : Fin p → ℕ, ((geomHalf.iid p) vt).toReal
          * (if pre vt p = l ∧ W vt then (1 : ℝ) else 0) := by
        refine tsum_congr (fun vt => ?_); rw [hcollapse vt]
    _ ≤ ∑' vt : Fin p → ℕ, ((geomHalf.iid p) vt).toReal := by
        have hle : ∀ vt : Fin p → ℕ,
            ((geomHalf.iid p) vt).toReal * (if pre vt p = l ∧ W vt then (1 : ℝ) else 0)
              ≤ ((geomHalf.iid p) vt).toReal := by
          intro vt
          calc ((geomHalf.iid p) vt).toReal * (if pre vt p = l ∧ W vt then (1 : ℝ) else 0)
              ≤ ((geomHalf.iid p) vt).toReal * 1 :=
                mul_le_mul_of_nonneg_left (by split <;> norm_num) ENNReal.toReal_nonneg
            _ = ((geomHalf.iid p) vt).toReal := mul_one _
        refine Summable.tsum_le_tsum hle ?_ hbase
        exact Summable.of_nonneg_of_le
          (fun vt => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num)) hle hbase
    _ = 1 := hone

/-- **The windowed tail Rényi count reduces to the single-point mass bound** (C10, obligation 3):
given `tailDensW Y ≤ M` (from `tailDensW_le_single_mass`, `M = 2⁻ˡ`), the windowed tail collision
entropy is `∑_Y (tailDensW)² ≤ M`. Mirror of `tailDens_renyi_le`; `sum_sq_le_max_mul_sum` +
`tailDensW_sum_le_one`. This is the exact quantity the windowed osc `√` consumes. -/
theorem tailDensW_renyi_le (j p l : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W] (M : ℝ)
    (hM : ∀ Y, tailDensW j p l W Y ≤ M) :
    ∑ Y, (tailDensW j p l W Y) ^ 2 ≤ M := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hM0 : 0 ≤ M := le_trans (tailDensW_nonneg j p l W 0) (hM 0)
  calc ∑ Y, (tailDensW j p l W Y) ^ 2
      ≤ M * ∑ Y, tailDensW j p l W Y :=
        sum_sq_le_max_mul_sum _ M (tailDensW_nonneg j p l W) hM
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left (tailDensW_sum_le_one j p l W) hM0
    _ = M := mul_one M

/-- `∑_{m<p} 2ᵐ < 2ᵖ` (the geometric partial sum `= 2ᵖ−1`). -/
theorem sum_two_pow_lt (p : ℕ) : ∑ m ∈ Finset.range p, 2 ^ m < 2 ^ p := by
  induction p with
  | zero => simp
  | succ p ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- **The window bound `fnat p vt < 3^{j+p}` from a per-prefix ℕ hypothesis** (C10, obligation 3;
Tao (6.14)→(6.15), the pure-algebra half). This ISOLATES the geometric-sum content of Corollary 6.3
from its analytic input: given, for each prefix `m`, `3^{p-1-m}·2^{a_{[1,m]}+(p-m)} < 3^{j+p}` — the
statement that the prefix valuation `a_{[1,m]}` is not too large, which the **sub-Gaussian window
(6.12)** delivers (via `a_{[1,m]} ≥ 2m − Cₐ√(m log n) − log n` and Young's inequality) — the offset
`fnat p vt` stays below the modulus `3^{j+p}`. Proof: multiply by `2ᵖ`, split `2ᵖ = 2ᵐ·2^{p-m}` per
term, apply the hypothesis, and sum the geometric `∑2ᵐ < 2ᵖ`.

⚠️ **NOTE (deep reflection 2026-07-14): the per-prefix hypothesis here is UNSATISFIABLE in the §6
operating regime** (`p = k+1 ≈ 0.79·(j+p)`): its `m = 0` instance reads `3^(p-1)·2^p < 3^(j+p)`,
which fails (per-`n` coefficient `0.79·(ln3+ln2) ≈ 1.42 > ln3 ≈ 1.10`). The lemma is kept as a
true conditional statement, but the consumable supplier of `fnat < 3^(j+p)` is
`fnat_lt_of_suffix_window` below (suffix form + tight `l`-window). Do not route through this. -/
theorem fnat_lt_of_prefix_bound {j p : ℕ} (vt : Fin p → ℕ)
    (H : ∀ m, m < p → 3 ^ (p - 1 - m) * 2 ^ (pre vt m + (p - m)) < 3 ^ (j + p)) :
    fnat p vt < 3 ^ (j + p) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp only [fnat, Finset.range_zero, Finset.sum_empty]; positivity
  have hmul : 2 ^ p * fnat p vt < 2 ^ p * 3 ^ (j + p) := by
    calc 2 ^ p * fnat p vt
        = ∑ m ∈ Finset.range p, 2 ^ m * (3 ^ (p - 1 - m) * 2 ^ (pre vt m + (p - m))) := by
          rw [fnat, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m hm => ?_)
          rw [Finset.mem_range] at hm
          have h2p : 2 ^ p = 2 ^ m * 2 ^ (p - m) := by
            rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hm)]
          rw [pow_add, h2p]; ring
      _ < ∑ m ∈ Finset.range p, 2 ^ m * 3 ^ (j + p) := by
          refine Finset.sum_lt_sum_of_nonempty ?_ (fun m hm => ?_)
          · exact Finset.nonempty_range_iff.mpr hp.ne'
          · rw [Finset.mem_range] at hm
            exact mul_lt_mul_of_pos_left (H m hm) (by positivity)
      _ = (∑ m ∈ Finset.range p, 2 ^ m) * 3 ^ (j + p) := by rw [Finset.sum_mul]
      _ < 2 ^ p * 3 ^ (j + p) := mul_lt_mul_of_pos_right (sum_two_pow_lt p) (by positivity)
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- `exp(1/5) < 16/13` — the numeric seed for the corrected §6 window ratio `q = (3/4)·e^{1/5}`:
fifth powers reduce it to `e < (16/13)⁵ = 1048576/371293 ≈ 2.824`, within `exp_one_lt_d9`. -/
theorem exp_fifth_lt : Real.exp (1 / 5) < 16 / 13 := by
  have h5 : Real.exp (1 / 5) ^ (5 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  refine lt_of_pow_lt_pow_left₀ 5 (by norm_num) ?_
  rw [h5]
  calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    _ < (16 / 13 : ℝ) ^ (5 : ℕ) := by norm_num

/-- **The corrected window bound (C10, obligation 3; deep reflection 2026-07-14)** — the
SUFFIX-form geometric estimate for Tao (6.14)→(6.15). Hypotheses:

* `hsuf` — the sub-Gaussian window (6.12) applied to **suffix** intervals of the tail block:
  `l − a_{[1,p−r]} = a_{[p−r+1,p]} ≥ 2r − C(√(r·log n) + log n)` for `1 ≤ r ≤ p`;
* `hbudget` — the **tight** `l`-budget `l·ln2 + (C·ln2 + (5/4)(C·ln2)²)·log n + ln4 < n·ln3`,
  which the stopping rule `Bₖ` + the one-step `Eₖ` bound deliver (`l ≤ n·log₂3 − (C²−2C)·log n
  − O(1)`, coefficient `ln2·(C²−2C) ≈ 0.693C²` vs cost `≈ 0.601C²` — closes for `C ≳ 23`).
  ⚠️ The paper's own window (6.8) (upper end `n·log₂3 − ½C²·log n`) is provably TOO LOSSY here
  (budget `0.347C²` < the minimal Young cost `0.418C²`); see `papers/literature-review.md`,
  source hole #3. Do NOT weaken this hypothesis toward (6.8).

Conclusion: the Syracuse offset stays below the modulus, `fnat p vt < 3^(j+p)` — exactly what
`fnat_offset_zmod_inj` consumes. Proof: reflect the sum (`r := p−m`), bound each term
`3^(r−1)·2^(l−suffix_r) ≤ B·q^r` with `q = (3/4)·e^{1/5} ≤ 12/13` via AM-GM at `ε = 1/5`
(`(C·ln2)·√(rL) ≤ r/5 + (5/4)(C·ln2)²·L`), sum the geometric series (`≤ 12·B`), and close the
exponent comparison with `hbudget` (`ln12 = ln4 + ln3`). Replaces the in-regime-unusable
`fnat_lt_of_prefix_bound` route. -/
theorem fnat_lt_of_suffix_window {j p : ℕ} (vt : Fin p → ℕ) (l : ℕ) (C : ℝ)
    (hl : pre vt p = l)
    (hsuf : ∀ r : ℕ, 1 ≤ r → r ≤ p →
      2 * (r : ℝ) - C * (Real.sqrt (r * Real.log ((j + p : ℕ) : ℝ))
          + Real.log ((j + p : ℕ) : ℝ))
        ≤ (l : ℝ) - (pre vt (p - r) : ℝ))
    (hbudget : (l : ℝ) * Real.log 2
        + (C * Real.log 2 + 5 / 4 * (C * Real.log 2) ^ 2) * Real.log ((j + p : ℕ) : ℝ)
        + Real.log 4 < ((j + p : ℕ) : ℝ) * Real.log 3) :
    fnat p vt < 3 ^ (j + p) := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst hp0
    simp only [fnat, Finset.range_zero, Finset.sum_empty]
    positivity
  set L : ℝ := Real.log ((j + p : ℕ) : ℝ) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
  have hln2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hln3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set δ : ℝ := 2 * Real.log 2 - Real.log 3 - 1 / 5 with hδdef
  set q : ℝ := Real.exp (-δ) with hqdef
  have hq0 : (0 : ℝ) < q := Real.exp_pos _
  have hq_eq : q = 3 / 4 * Real.exp (1 / 5) := by
    rw [hqdef, hδdef, show -(2 * Real.log 2 - Real.log 3 - 1 / 5)
        = Real.log 3 - (Real.log 2 + Real.log 2) + 1 / 5 by ring,
      Real.exp_add, Real.exp_sub, Real.exp_add,
      Real.exp_log (by norm_num : (0:ℝ) < 3), Real.exp_log (by norm_num : (0:ℝ) < 2)]
    ring
  have hq1 : q ≤ 12 / 13 := by
    rw [hq_eq]
    have h := exp_fifth_lt
    nlinarith [Real.exp_pos (1 / 5 : ℝ)]
  have hq_lt_one : q < 1 := lt_of_le_of_lt hq1 (by norm_num)
  set E : ℝ := (l : ℝ) * Real.log 2
      + (C * Real.log 2 + 5 / 4 * (C * Real.log 2) ^ 2) * L - Real.log 3 with hEdef
  set B : ℝ := Real.exp E with hBdef
  have hB0 : (0 : ℝ) < B := Real.exp_pos _
  -- per-term bound: `3^i · 2^(pre vt (p−1−i)) ≤ B·q^(i+1)`
  have hterm : ∀ i ∈ Finset.range p,
      (3 : ℝ) ^ i * 2 ^ pre vt (p - 1 - i) ≤ B * q ^ (i + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hs := hsuf (i + 1) (by omega) (by omega)
    rw [show p - (i + 1) = p - 1 - i by omega] at hs
    have hi1 : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
    have hsplit : Real.sqrt (((i + 1 : ℕ) : ℝ) * L)
        = Real.sqrt ((i + 1 : ℕ) : ℝ) * Real.sqrt L := Real.sqrt_mul hi1 L
    have hamgm : (C * Real.log 2) * (Real.sqrt ((i + 1 : ℕ) : ℝ) * Real.sqrt L)
        ≤ ((i + 1 : ℕ) : ℝ) / 5 + 5 / 4 * (C * Real.log 2) ^ 2 * L := by
      nlinarith [sq_nonneg (2 * Real.sqrt ((i + 1 : ℕ) : ℝ)
          - 5 * (C * Real.log 2) * Real.sqrt L),
        Real.sq_sqrt hi1, Real.sq_sqrt hL0]
    have hpre : (pre vt (p - 1 - i) : ℝ)
        ≤ (l : ℝ) - 2 * ((i + 1 : ℕ) : ℝ)
          + C * (Real.sqrt (((i + 1 : ℕ) : ℝ) * L) + L) := by linarith
    have h1 : (pre vt (p - 1 - i) : ℝ) * Real.log 2
        ≤ ((l : ℝ) - 2 * ((i + 1 : ℕ) : ℝ)
          + C * (Real.sqrt (((i + 1 : ℕ) : ℝ) * L) + L)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hpre hln2.le
    have hexp : (i : ℝ) * Real.log 3 + (pre vt (p - 1 - i) : ℝ) * Real.log 2
        ≤ E + ((i : ℝ) + 1) * (-δ) := by
      rw [hEdef, hδdef]
      rw [hsplit] at h1
      push_cast at h1 hamgm ⊢
      nlinarith [h1, hamgm]
    calc (3 : ℝ) ^ i * 2 ^ pre vt (p - 1 - i)
        = Real.exp ((i : ℝ) * Real.log 3 + (pre vt (p - 1 - i) : ℝ) * Real.log 2) := by
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
            Real.exp_log (by norm_num : (0:ℝ) < 3), Real.exp_log (by norm_num : (0:ℝ) < 2)]
      _ ≤ Real.exp (E + ((i : ℝ) + 1) * (-δ)) := Real.exp_le_exp.mpr hexp
      _ = B * q ^ (i + 1) := by
          rw [Real.exp_add, ← hBdef, show ((i : ℝ) + 1) * (-δ) = ((i + 1 : ℕ) : ℝ) * (-δ) by
            push_cast; ring, Real.exp_nat_mul, ← hqdef]
  -- cast + reflect the sum
  have hcast : ((fnat p vt : ℕ) : ℝ)
      = ∑ m ∈ Finset.range p, (3 : ℝ) ^ (p - 1 - m) * 2 ^ pre vt m := by
    simp only [fnat]
    push_cast
    rfl
  have hrefl : ∑ m ∈ Finset.range p, (3 : ℝ) ^ (p - 1 - m) * 2 ^ pre vt m
      = ∑ i ∈ Finset.range p, (3 : ℝ) ^ i * 2 ^ pre vt (p - 1 - i) := by
    rw [← Finset.sum_range_reflect (fun i => (3 : ℝ) ^ i * 2 ^ pre vt (p - 1 - i)) p]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [show p - 1 - (p - 1 - m) = m by omega]
  have hsum : ((fnat p vt : ℕ) : ℝ) ≤ B * ∑ i ∈ Finset.range p, q ^ (i + 1) := by
    rw [hcast, hrefl, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  -- geometric series: `∑_{i<p} q^(i+1) ≤ 12`
  have hgeo : ∑ i ∈ Finset.range p, q ^ (i + 1) ≤ 12 := by
    have hqp : (0 : ℝ) ≤ q ^ p := (pow_pos hq0 p).le
    have hgs : ∑ i ∈ Finset.range p, q ^ i ≤ 13 := by
      rw [geom_sum_eq (ne_of_lt hq_lt_one)]
      rw [div_le_iff_of_neg (by linarith : q - 1 < 0)]
      nlinarith
    have hsum_nonneg : (0 : ℝ) ≤ ∑ i ∈ Finset.range p, q ^ i :=
      Finset.sum_nonneg fun i _ => (pow_pos hq0 i).le
    calc ∑ i ∈ Finset.range p, q ^ (i + 1)
        = q * ∑ i ∈ Finset.range p, q ^ i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => pow_succ' q i
      _ ≤ (12 / 13) * 13 := mul_le_mul hq1 hgs hsum_nonneg (by norm_num)
      _ = 12 := by norm_num
  -- close: `12·B < 3^n` from the budget
  have h3n : ((3 ^ (j + p) : ℕ) : ℝ) = Real.exp (((j + p : ℕ) : ℝ) * Real.log 3) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 3)]
    push_cast
    ring
  have hlt : ((fnat p vt : ℕ) : ℝ) < ((3 ^ (j + p) : ℕ) : ℝ) := by
    have hb12 : B * 12 < ((3 ^ (j + p) : ℕ) : ℝ) := by
      rw [h3n, hBdef, show (12 : ℝ) = Real.exp (Real.log 12) from
        (Real.exp_log (by norm_num)).symm, ← Real.exp_add]
      apply Real.exp_lt_exp.mpr
      have hlog12 : Real.log 12 = Real.log 4 + Real.log 3 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      rw [hEdef]
      linarith
    calc ((fnat p vt : ℕ) : ℝ)
        ≤ B * ∑ i ∈ Finset.range p, q ^ (i + 1) := hsum
      _ ≤ B * 12 := mul_le_mul_of_nonneg_left hgeo hB0.le
      _ < _ := hb12
  exact_mod_cast hlt

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

/-- **The windowed single-point mass** (C10, obligation 3 — the Rényi numerator): if the window
forces the offset below the modulus (`hwin`, supplied by `fnat_lt_of_suffix_window` from (6.12) +
the tight budget), then each residue class `Y` carries at most ONE positive tuple of valuation
`l` in the window (`fnat_offset_zmod_inj`), each of mass exactly `2⁻ˡ` — so `tailDensW Y ≤ 2⁻ˡ`.
This is the single-point bound `M = 2⁻ˡ` that the collision-entropy count
(`sum_sq_le_max_mul_sum`) feeds into `condDens_osc_le`'s `√`. -/
theorem tailDensW_le_single_mass (j p l : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W]
    (hwin : ∀ vt : Fin p → ℕ, (∀ i, 1 ≤ vt i) → pre vt p = l → W vt →
      fnat p vt < 3 ^ (j + p))
    (Y : ZMod (3 ^ (j + p))) :
    tailDensW j p l W Y ≤ (2 : ℝ)⁻¹ ^ l := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  by_cases hex : ∃ vt₀ : Fin p → ℕ, (∀ i, 1 ≤ vt₀ i)
      ∧ (fnat p vt₀ : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt₀ p = Y
      ∧ pre vt₀ p = l ∧ W vt₀
  · obtain ⟨vt₀, hpos₀, hoff₀, hl₀, hW₀⟩ := hex
    have hsingle : ∀ vt : Fin p → ℕ, vt ≠ vt₀ →
        ((geomHalf.iid p) vt).toReal
          * (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
                ∧ pre vt p = l ∧ W vt then (1 : ℝ) else 0) = 0 := by
      intro vt hne
      by_cases hind : (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
          ∧ pre vt p = l ∧ W vt
      · by_cases hz : (geomHalf.iid p) vt = 0
        · rw [hz]; simp
        · exact absurd
            (fnat_offset_zmod_inj vt vt₀ (geomHalf_iid_pos_coords hz) hpos₀ hind.2.1 hl₀
              (hwin vt (geomHalf_iid_pos_coords hz) hind.2.1 hind.2.2)
              (hwin vt₀ hpos₀ hl₀ hW₀)
              (by rw [hind.1, hoff₀])) hne
      · rw [if_neg hind, mul_zero]
    calc tailDensW j p l W Y
        = ((geomHalf.iid p) vt₀).toReal
          * (if (fnat p vt₀ : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt₀ p = Y
                ∧ pre vt₀ p = l ∧ W vt₀ then (1 : ℝ) else 0) := by
          simp only [tailDensW]
          exact tsum_eq_single vt₀ hsingle
      _ = ((2 : ENNReal)⁻¹ ^ l).toReal := by
          rw [if_pos ⟨hoff₀, hl₀, hW₀⟩, mul_one, geomHalf_iid_apply_pos vt₀ hpos₀, hl₀]
      _ ≤ (2 : ℝ)⁻¹ ^ l := by
          rw [ENNReal.toReal_pow, ENNReal.toReal_inv]
          norm_num
  · have hall : ∀ vt : Fin p → ℕ,
        ((geomHalf.iid p) vt).toReal
          * (if (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
                ∧ pre vt p = l ∧ W vt then (1 : ℝ) else 0) = 0 := by
      intro vt
      by_cases hind : (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p = Y
          ∧ pre vt p = l ∧ W vt
      · by_cases hz : (geomHalf.iid p) vt = 0
        · rw [hz]; simp
        · exact absurd ⟨vt, geomHalf_iid_pos_coords hz, hind.1, hind.2.1, hind.2.2⟩ hex
      · rw [if_neg hind, mul_zero]
    have hzero : tailDensW j p l W Y = 0 := by
      simp only [tailDensW]
      exact (tsum_congr hall).trans tsum_zero
    rw [hzero]
    positivity

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
theorem dft_condDens_norm_le_at (A : ℝ) (hA : 0 < A) :
    ∀ (j' q p l : ℕ), 1 ≤ q → ∀ (ξ : ZMod (3 ^ ((j' + q) + p)))
      (η : ZMod (3 ^ (j' + q))),
      (2 : ZMod (3 ^ (j' + q)))⁻¹ ^ l
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right (j' + q) p)) (ZMod (3 ^ (j' + q))) ξ
        = (3 : ZMod (3 ^ (j' + q))) ^ j' * η →
      ¬ (3 ∣ (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j')) (ZMod (3 ^ q)) η).val) →
      ‖ZMod.dft (densC ((j' + q) + p) (condDens (j' + q) p l)) ξ‖ ≤ C_renewalWhite A * (q : ℝ) ^ (-A) := by
  have hC := head_factor_norm_le_charFn_at A hA
  have hC0 : (0 : ℝ) < C_renewalWhite A := C_renewalWhite_pos A
  set C : ℝ := C_renewalWhite A with hCdef
  intro j' q p l hq ξ η hfreq hη
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

/-- `dft_condDens_norm_le`, original `∃`-form: delegates to the `_at` sibling at
`C_renewalWhite A` (big-C campaign, step 2). -/
theorem dft_condDens_norm_le (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ (j' q p l : ℕ), 1 ≤ q → ∀ (ξ : ZMod (3 ^ ((j' + q) + p)))
      (η : ZMod (3 ^ (j' + q))),
      (2 : ZMod (3 ^ (j' + q)))⁻¹ ^ l
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right (j' + q) p)) (ZMod (3 ^ (j' + q))) ξ
        = (3 : ZMod (3 ^ (j' + q))) ^ j' * η →
      ¬ (3 ∣ (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_left q j')) (ZMod (3 ^ q)) η).val) →
      ‖ZMod.dft (densC ((j' + q) + p) (condDens (j' + q) p l)) ξ‖ ≤ C * (q : ℝ) ^ (-A) :=
  ⟨C_renewalWhite A, C_renewalWhite_pos A, dft_condDens_norm_le_at A hA⟩

/-- **Brick (b), the sharp `ℓ²`-mass refinement** (C10, (6.10)–(6.11)). Given a **uniform** head-factor
decay bound `D` over all high frequencies (`hunif` — the valuation bookkeeping: each high `ξ` has
residual descent level `q ≥ q_min`, so `‖head(ξ)‖ ≤ Cₐ·q_min⁻ᴬ =: D`), the high-frequency `ℓ²`-mass
of the conditioned density is `≤ D²·(tail collision entropy)`. Proof: per high `ξ`,
`𝓕(densC condDens)ξ = head·tail` (`dft_condDens_eq_cond_char` + `cond_char_factor`) so
`‖𝓕‖² = ‖head‖²‖tail‖² ≤ D²‖tail‖²`; sum, drop to all frequencies (nonneg), and apply the tail
Parseval `tail_factor_l2_eq`. This isolates the two genuinely-remaining obligations — establishing
`hunif` (uniform head decay) and bounding `∑(tailDens)²` (the Rényi/offset-injectivity count, Lemma
6.2) — behind a machine-checked reduction. -/
theorem condDens_highfreq_l2_le (j p l m : ℕ) (D : ℝ)
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
        exact condDens_highfreq_l2_le j p l m D hunif
    _ = D * Real.sqrt ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDens j p l Y) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD]


/-! ### Windowed conditioned density — the osc bound carrying the (6.12) window `W`

The §6 assembly conditions on the full event `Eₖ ∧ Bₖ ∧ Cₖ,ₗ`, which is tail-measurable, i.e. a
predicate `W` of the tail block `Fin p → ℕ`. The following mirror `condDens`/`tailDens` and their
osc chain with the extra conjunct `W vt`, so the windowed single-point mass
`tailDensW_le_single_mass` (`tailDensW Y ≤ 2⁻ˡ`, only valid on the window) actually feeds the osc `√`.
Everything is the exact non-windowed proof with `pre vt p = l` replaced by `pre vt p = l ∧ W vt`; the
head factor is unchanged (the `2⁻ˡ` freeze uses only `pre(tail) = l`). -/

/-- The **windowed conditioned density** `g_{j,p,l,W}` (Tao's `g_{n,k,l}` with the tail-measurable
event `W`): `condDens` restricted to `{pre(tail) = l ∧ W(tail)}`. -/
noncomputable def condDensW (j p l : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W] :
    ZMod (3 ^ (j + p)) → ℝ := fun Y =>
  ∑' a : Fin (j + p) → ℕ, ((geomHalf.iid (j + p)) a).toReal
    * (if (fnat (j + p) a : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p) = Y
          ∧ pre (fun i => a (Fin.natAdd j i)) p = l ∧ W (fun i => a (Fin.natAdd j i))
        then (1 : ℝ) else 0)

/-- The DFT of the windowed conditioned density is the windowed conditional character sum
(general `dft_cond_density` at `w = {pre(tail) = l ∧ W(tail)}`). -/
theorem dft_condDensW_eq_cond_char (j p l : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W]
    (ξ : ZMod (3 ^ (j + p))) :
    ZMod.dft (densC (j + p) (condDensW j p l W)) ξ
      = (geomHalf.iid (j + p)).cexpect (fun a =>
          ZMod.stdAddChar (-(((fnat (j + p) a : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p)) * ξ))
            * (if pre (fun i => a (Fin.natAdd j i)) p = l ∧ W (fun i => a (Fin.natAdd j i))
                then 1 else 0)) :=
  dft_cond_density (geomHalf.iid (j + p))
    (fun a => (fnat (j + p) a : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p))
    (fun a => pre (fun i => a (Fin.natAdd j i)) p = l ∧ W (fun i => a (Fin.natAdd j i))) ξ

/-- **The windowed conditional character factorization** — mirror of `cond_char_factor` carrying the
extra tail conjunct `W(tail)`. The head factor is identical; only the tail expectation's indicator
gains `∧ W`. -/
theorem cond_char_factorW {j p : ℕ} (ξ : ZMod (3 ^ (j + p))) (l : ℕ)
    (W : (Fin p → ℕ) → Prop) [DecidablePred W] :
    (geomHalf.iid (j + p)).cexpect
        (fun a => ZMod.stdAddChar (-(((fnat (j + p) a : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre a (j + p)) * ξ))
          * (if pre (fun i => a (Fin.natAdd j i)) p = l ∧ W (fun i => a (Fin.natAdd j i))
              then 1 else 0))
      = (geomHalf.iid j).cexpect
            (fun vh => ZMod.stdAddChar (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
                  * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
                  * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))
        * (geomHalf.iid p).cexpect
            (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
                  * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
              * (if pre vt p = l ∧ W vt then 1 else 0)) := by
  set f : (Fin j → ℕ) → ℂ := fun vh => ZMod.stdAddChar (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
      * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)) with hf
  set g : (Fin p → ℕ) → ℂ := fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
      * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ)) * (if pre vt p = l ∧ W vt then 1 else 0) with hg
  have hfb : ∀ vh, ‖f vh‖ ≤ 1 := fun vh => le_of_eq (norm_stdAddChar _)
  have hgb : ∀ vt, ‖g vt‖ ≤ 1 := fun vt => by
    simp only [hg]
    by_cases h : pre vt p = l ∧ W vt
    · rw [if_pos h, mul_one]; exact le_of_eq (norm_stdAddChar _)
    · rw [if_neg h, mul_zero, norm_zero]; exact zero_le_one
  rw [← PMF.cexpect_iid_append geomHalf j p f g hfb hgb]
  refine congrArg (PMF.cexpect (geomHalf.iid (j + p))) ?_
  funext a
  simp only [hf, hg]
  by_cases h : pre (fun i => a (Fin.natAdd j i)) p = l ∧ W (fun i => a (Fin.natAdd j i))
  · simp only [if_pos h, mul_one]
    rw [char_offset_split a ξ, pre_castAdd a (le_refl j), h.1]
  · simp only [if_neg h, mul_zero]

/-- The windowed tail factor is the DFT of the windowed tail sub-density `tailDensW`
(general `dft_cond_density` at `w = {pre = l ∧ W}`). -/
theorem tail_factor_dft_eqW (j p l : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W]
    (ξ : ZMod (3 ^ (j + p))) :
    ZMod.dft (densC (j + p) (tailDensW j p l W)) ξ
      = (geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
          * (if pre vt p = l ∧ W vt then 1 else 0)) :=
  dft_cond_density (geomHalf.iid p)
    (fun vt => (fnat p vt : ZMod (3 ^ (j + p))) * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p)
    (fun vt => pre vt p = l ∧ W vt) ξ

/-- **(6.11) windowed tail collision entropy**: `∑_ξ ‖windowed tail factor‖² = 3^(j+p)·∑ (tailDensW)²`,
by Parseval through `tail_factor_dft_eqW`. Mirror of `tail_factor_l2_eq`. -/
theorem tail_factor_l2_eqW (j p l : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W] :
    ∑ ξ, ‖(geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ)) * (if pre vt p = l ∧ W vt then 1 else 0))‖ ^ 2
      = (3 ^ (j + p) : ℝ) * ∑ Y, (tailDensW j p l W Y) ^ 2 := by
  haveI : NeZero (3 ^ (j + p)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have h1 : ∀ ξ : ZMod (3 ^ (j + p)),
      (geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
          * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ)) * (if pre vt p = l ∧ W vt then 1 else 0))
        = ZMod.dft (densC (j + p) (tailDensW j p l W)) ξ := fun ξ => (tail_factor_dft_eqW j p l W ξ).symm
  have hnorm : ∀ Y : ZMod (3 ^ (j + p)),
      ‖densC (j + p) (tailDensW j p l W) Y‖ ^ 2 = (tailDensW j p l W Y) ^ 2 := by
    intro Y; rw [densC, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [h1]
  rw [ZMod.dft_parseval (densC (j + p) (tailDensW j p l W))]
  simp_rw [hnorm]
  push_cast; ring

/-- **Windowed sharp `ℓ²`-mass refinement** — mirror of `condDens_highfreq_l2_le` for `condDensW`. -/
theorem condDensW_highfreq_l2_le (j p l m : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W]
    (D : ℝ)
    (hunif : ∀ ξ ∈ highFreq m (j + p),
      ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))‖ ≤ D) :
    ∑ ξ ∈ highFreq m (j + p), ‖ZMod.dft (densC (j + p) (condDensW j p l W)) ξ‖ ^ 2
      ≤ D ^ 2 * (3 ^ (j + p) : ℝ) * ∑ Y, (tailDensW j p l W Y) ^ 2 := by
  have hpt : ∀ ξ ∈ highFreq m (j + p),
      ‖ZMod.dft (densC (j + p) (condDensW j p l W)) ξ‖ ^ 2
        ≤ D ^ 2 * ‖(geomHalf.iid p).cexpect (fun vt => ZMod.stdAddChar
            (-(((fnat p vt : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
            * (if pre vt p = l ∧ W vt then 1 else 0))‖ ^ 2 := by
    intro ξ hξ
    rw [dft_condDensW_eq_cond_char, cond_char_factorW, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hunif ξ hξ) 2)
      (sq_nonneg _)
  calc ∑ ξ ∈ highFreq m (j + p), ‖ZMod.dft (densC (j + p) (condDensW j p l W)) ξ‖ ^ 2
      ≤ ∑ ξ ∈ highFreq m (j + p), D ^ 2 * ‖(geomHalf.iid p).cexpect (fun vt =>
            ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
            * (if pre vt p = l ∧ W vt then 1 else 0))‖ ^ 2 := Finset.sum_le_sum hpt
    _ = D ^ 2 * ∑ ξ ∈ highFreq m (j + p), ‖(geomHalf.iid p).cexpect (fun vt =>
            ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
            * (if pre vt p = l ∧ W vt then 1 else 0))‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ D ^ 2 * ∑ ξ, ‖(geomHalf.iid p).cexpect (fun vt =>
            ZMod.stdAddChar (-(((fnat p vt : ZMod (3 ^ (j + p)))
              * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vt p) * ξ))
            * (if pre vt p = l ∧ W vt then 1 else 0))‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => sq_nonneg _)) (sq_nonneg _)
    _ = D ^ 2 * ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDensW j p l W Y) ^ 2) := by rw [tail_factor_l2_eqW]
    _ = D ^ 2 * (3 ^ (j + p) : ℝ) * ∑ Y, (tailDensW j p l W Y) ^ 2 := by ring

/-- **The windowed per-conditioning osc bound** (C10, (6.10) with the window `W`): mirror of
`condDens_osc_le`. `osc(condDensW) ≤ D·√(3^(j+p)·∑ (tailDensW)²)`. With `∑ (tailDensW)² ≤ 2⁻ˡ`
(`tailDensW_renyi_le` ∘ `tailDensW_le_single_mass`) and the head decay `D`, the `√` collapses. -/
theorem condDensW_osc_le (j p l m : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W]
    (hmn : m ≤ j + p) (D : ℝ) (hD : 0 ≤ D)
    (hunif : ∀ ξ ∈ highFreq m (j + p),
      ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))‖ ≤ D) :
    osc m (j + p) hmn (condDensW j p l W)
      ≤ D * Real.sqrt ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDensW j p l W Y) ^ 2) := by
  calc osc m (j + p) hmn (condDensW j p l W)
      ≤ Real.sqrt (∑ ξ ∈ highFreq m (j + p),
          ‖ZMod.dft (densC (j + p) (condDensW j p l W)) ξ‖ ^ 2) :=
        osc_le_sqrt_highfreq _ _ _ _
    _ ≤ Real.sqrt (D ^ 2 * ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDensW j p l W Y) ^ 2)) := by
        apply Real.sqrt_le_sqrt
        rw [← mul_assoc]
        exact condDensW_highfreq_l2_le j p l m W D hunif
    _ = D * Real.sqrt ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDensW j p l W Y) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD]

/-- **The §6 event-assembly inner loop** (C10, (6.10) telescoped over the conditioning partition).
For a FINITE family of windowed conditionings `(l i, W i)` (Tao's `(k, l)` index set), the oscillation
of the summed conditioned density is controlled by the per-conditioning osc bounds:
`osc(∑ᵢ condDensW) ≤ ∑ᵢ Dᵢ·√(3^(j+p)·∑ (tailDensW)²)`. Pure composition of the proved
`osc_sum_le` (subadditivity) with `condDensW_osc_le` (the per-conditioning Cauchy–Schwarz/Parseval
bound). This is the reusable core of the `fine_scale_mixing` assembly: the remaining obligations are
(i) exhibiting the decomposition `syracZ = ∑ condDensW + error` with tail-measurable events (obl 1),
(ii) the head uniform-decay `hunif` giving `Dᵢ = Cₐ·q⁻ᴬ` (obl 2), and (iii) the geometric `l`-sum of
`√(2⁻ˡ)` + the error `L¹` bound (obl 1 tail); the collision entropy inside the `√` is already
`≤ 2⁻ˡ` (`tailDensW_renyi_le`, obl 3 DONE). -/
theorem osc_windowed_conditioning_le {ι : Type*} (m j p : ℕ) (hmn : m ≤ j + p)
    (s : Finset ι) (l : ι → ℕ) (W : ι → (Fin p → ℕ) → Prop) [∀ i, DecidablePred (W i)]
    (D : ι → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hunif : ∀ i ∈ s, ∀ ξ ∈ highFreq m (j + p),
      ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ (l i)) * ξ)))‖ ≤ D i) :
    osc m (j + p) hmn (fun Y => ∑ i ∈ s, condDensW j p (l i) (W i) Y)
      ≤ ∑ i ∈ s, D i * Real.sqrt ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDensW j p (l i) (W i) Y) ^ 2) := by
  calc osc m (j + p) hmn (fun Y => ∑ i ∈ s, condDensW j p (l i) (W i) Y)
      ≤ ∑ i ∈ s, osc m (j + p) hmn (condDensW j p (l i) (W i)) :=
        osc_sum_le m (j + p) hmn s (fun i => condDensW j p (l i) (W i))
    _ ≤ ∑ i ∈ s, D i * Real.sqrt ((3 ^ (j + p) : ℝ) * ∑ Y, (tailDensW j p (l i) (W i) Y) ^ 2) :=
        Finset.sum_le_sum (fun i hi =>
          condDensW_osc_le j p (l i) m (W i) hmn (D i) (hD i) (hunif i hi))

/-- **The (6.2)/(6.12) window event `Eₖ`** on the tail block (`p = k+1` coords), in the SUFFIX form
the kernel `fnat_lt_of_suffix_window` consumes: `2r − Cₐ(√(r·log n)+log n) ≤ l − pre vt (p−r)` for all
`1 ≤ r ≤ p`. This is Tao (6.2) restricted to `1 ≤ i < j ≤ k+1` (so it depends only on `a₁,…,a_{k+1}`,
i.e. the tail block), reindexed to suffix intervals `[p−r+1, p]`. Real-inequality predicate; decidable
only classically. -/
def condWindow (j p : ℕ) (C : ℝ) (l : ℕ) : (Fin p → ℕ) → Prop := fun vt =>
  ∀ r : ℕ, 1 ≤ r → r ≤ p →
    2 * (r : ℝ) - C * (Real.sqrt (r * Real.log ((j + p : ℕ) : ℝ)) + Real.log ((j + p : ℕ) : ℝ))
      ≤ (l : ℝ) - (pre vt (p - r) : ℝ)

noncomputable instance condWindow_decidablePred (j p : ℕ) (C : ℝ) (l : ℕ) :
    DecidablePred (condWindow j p C l) := Classical.decPred _

/-- **Obligation 3, packaged for the §6 assembly**: on the suffix window `condWindow` with the
tight-window budget `hbudget` (discharged from the (6.8) `l`-range + `Cₐ ≥ 10`, `n ≥ n₀` — a
`vt`-independent numeric fact), the windowed tail single-point mass is `≤ 2⁻ˡ`. This composes the
proved collision bound `tailDensW_le_single_mass` with the kernel `fnat_lt_of_suffix_window`, so the
whole obligation-3 pipeline (kernel → injectivity → single-point mass) is now available at the concrete
window event `Eₖ`. It feeds `tailDensW_renyi_le` (`∑ (tailDensW)² ≤ 2⁻ˡ`) → `condDensW_osc_le`. -/
theorem tailDensW_condWindow_le (j p l : ℕ) (C : ℝ)
    (hbudget : (l : ℝ) * Real.log 2
        + (C * Real.log 2 + 5 / 4 * (C * Real.log 2) ^ 2) * Real.log ((j + p : ℕ) : ℝ)
        + Real.log 4 < ((j + p : ℕ) : ℝ) * Real.log 3)
    (Y : ZMod (3 ^ (j + p))) :
    tailDensW j p l (condWindow j p C l) Y ≤ (2 : ℝ)⁻¹ ^ l :=
  tailDensW_le_single_mass j p l (condWindow j p C l)
    (fun vt _ hl hW => fnat_lt_of_suffix_window vt l C hl hW hbudget) Y

/-- **The stopping event `Bₖ`** (Tao (6.6)) on the reversed tail block.  With `p = k+1`, the tail is
stored as `(a_{k+1}, …, a₁)`, so Tao's `a[1,k]` is its total sum with the *first* reversed coordinate
removed: `pre vt p - pre vt 1`.  Thus this is exactly
`a[1,k] ≤ T < a[1,k+1]`, for `T = n·log3/log2 − Cₐ²·log n`.  Dropping `pre vt (p−1)` instead would
remove `a₁`, not `a_{k+1}`, and the resulting events would not form a stopping-time partition. -/
def stopEvent (p : ℕ) (T : ℝ) : (Fin p → ℕ) → Prop := fun vt =>
  (pre vt p : ℝ) - (pre vt 1 : ℝ) ≤ T ∧ T < (pre vt p : ℝ)

/-- **The full §6 conditioning window `Eₖ ∧ Bₖ`** on the tail block (Tao (6.9), minus `Cₖ,ₗ = {pre = l}`
which `tailDensW`/`condDensW` bake in): the (6.2) window `condWindow` together with the stopping event
`stopEvent`. This is the tail-measurable `W` that the (6.9) density `g_{n,k,l} = condDensW … W` carries,
and the exact event over which the decomposition identity `syracZ = ∑_{k,l} g_{k,l} + error` sums. -/
def condWindowB (j p : ℕ) (C : ℝ) (l : ℕ) (T : ℝ) : (Fin p → ℕ) → Prop := fun vt =>
  condWindow j p C l vt ∧ stopEvent p T vt

noncomputable instance condWindowB_decidablePred (j p : ℕ) (C : ℝ) (l : ℕ) (T : ℝ) :
    DecidablePred (condWindowB j p C l T) := Classical.decPred _

/-- **Obligation 3 at the full window `Eₖ ∧ Bₖ`**: `tailDensW … (condWindowB) Y ≤ 2⁻ˡ`, given the same
numeric `hbudget`. The extra stopping conjunct `Bₖ` only shrinks the event, so the suffix-window
hypothesis of `fnat_lt_of_suffix_window` is still supplied by the `condWindow` component. This is the
obligation-3 output at the exact `W` the decomposition consumes. -/
theorem tailDensW_condWindowB_le (j p l : ℕ) (C T : ℝ)
    (hbudget : (l : ℝ) * Real.log 2
        + (C * Real.log 2 + 5 / 4 * (C * Real.log 2) ^ 2) * Real.log ((j + p : ℕ) : ℝ)
        + Real.log 4 < ((j + p : ℕ) : ℝ) * Real.log 3)
    (Y : ZMod (3 ^ (j + p))) :
    tailDensW j p l (condWindowB j p C l T) Y ≤ (2 : ℝ)⁻¹ ^ l :=
  tailDensW_le_single_mass j p l (condWindowB j p C l T)
    (fun vt _ hl hW => fnat_lt_of_suffix_window vt l C hl hW.1 hbudget) Y

/-- **The fully-assembled single-conditioning osc bound** (C10, Tao (6.10)+(6.11) with obligation 3
discharged): for one conditioning `(k, l)` — cut `(j, p) = (n−k−1, k+1)`, window `Eₖ ∧ Bₖ` — the
oscillation of the conditioned density is `≤ D·√(3^(j+p)·2⁻ˡ)`, where `D` is the head uniform-decay
bound (`hunif`, obligation 2) and the `2⁻ˡ` is the discharged tail collision entropy. This composes
`condDensW_osc_le` (the Cauchy–Schwarz/Parseval bridge) with `tailDensW_renyi_le ∘ tailDensW_condWindowB_le`
(the Rényi count `∑ (tailDensW)² ≤ 2⁻ˡ`). It is the exact per-term bound the (6.4)/(6.8) union sum over
`(k, l)` adds up (via `osc_windowed_conditioning_le`); the only remaining inputs are `hunif` (obligation
2) and `hbudget` (the (6.8) `l`-range numeric, obligation 1). -/
theorem condDensWB_osc_le (j p l m : ℕ) (C T : ℝ) (hmn : m ≤ j + p) (D : ℝ) (hD : 0 ≤ D)
    (hunif : ∀ ξ ∈ highFreq m (j + p),
      ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))‖ ≤ D)
    (hbudget : (l : ℝ) * Real.log 2
        + (C * Real.log 2 + 5 / 4 * (C * Real.log 2) ^ 2) * Real.log ((j + p : ℕ) : ℝ)
        + Real.log 4 < ((j + p : ℕ) : ℝ) * Real.log 3) :
    osc m (j + p) hmn (condDensW j p l (condWindowB j p C l T))
      ≤ D * Real.sqrt ((3 ^ (j + p) : ℝ) * (2 : ℝ)⁻¹ ^ l) := by
  refine le_trans (condDensW_osc_le j p l m (condWindowB j p C l T) hmn D hD hunif) ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hD
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact tailDensW_renyi_le j p l (condWindowB j p C l T) ((2 : ℝ)⁻¹ ^ l)
    (tailDensW_condWindowB_le j p l C T hbudget)

/-- **The (6.8) `l`-union sum at a fixed cut** (C10 assembly, obligation-3 discharged): summing the
single-conditioning bound `condDensWB_osc_le` over a finite family of valuations `l i` (Tao's union over
`l` in the (6.8) range, at a fixed stopping time `k` ⇒ fixed cut `(j, p)`), the oscillation of the summed
conditioned density is `≤ ∑ᵢ Dᵢ·√(3^(j+p)·2⁻ˡⁱ)`. Composes `osc_sum_le` (subadditivity) with the
fully-assembled `condDensWB_osc_le`. Only `hunif` (obligation 2) and `hbudget` (the (6.8) numeric,
obligation 1) remain per term; the tail collision entropy is already the explicit `2⁻ˡⁱ`. -/
theorem osc_windowedB_conditioning_le {ι : Type*} (m j p : ℕ) (hmn : m ≤ j + p) (C T : ℝ)
    (s : Finset ι) (l : ι → ℕ) (D : ι → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hunif : ∀ i ∈ s, ∀ ξ ∈ highFreq m (j + p),
      ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ (l i)) * ξ)))‖ ≤ D i)
    (hbudget : ∀ i ∈ s, (l i : ℝ) * Real.log 2
        + (C * Real.log 2 + 5 / 4 * (C * Real.log 2) ^ 2) * Real.log ((j + p : ℕ) : ℝ)
        + Real.log 4 < ((j + p : ℕ) : ℝ) * Real.log 3) :
    osc m (j + p) hmn (fun Y => ∑ i ∈ s, condDensW j p (l i) (condWindowB j p C (l i) T) Y)
      ≤ ∑ i ∈ s, D i * Real.sqrt ((3 ^ (j + p) : ℝ) * (2 : ℝ)⁻¹ ^ (l i)) := by
  calc osc m (j + p) hmn (fun Y => ∑ i ∈ s, condDensW j p (l i) (condWindowB j p C (l i) T) Y)
      ≤ ∑ i ∈ s, osc m (j + p) hmn (condDensW j p (l i) (condWindowB j p C (l i) T)) :=
        osc_sum_le m (j + p) hmn s (fun i => condDensW j p (l i) (condWindowB j p C (l i) T))
    _ ≤ ∑ i ∈ s, D i * Real.sqrt ((3 ^ (j + p) : ℝ) * (2 : ℝ)⁻¹ ^ (l i)) :=
        Finset.sum_le_sum (fun i hi =>
          condDensWB_osc_le j p (l i) m C T hmn (D i) (hD i) (hunif i hi) (hbudget i hi))


/-- The stopping-cut exponent identity: for `k < n`, `(n−1−k) + (k+1) = n`. A *named* lemma so the
`Eq.rec` proof term is syntactically stable. -/
theorem cutEq {n k : ℕ} (h : k < n) : n - 1 - k + (k + 1) = n := by omega

/-- The k-sum cast helper: transport osc across an exponent equality (free vars ⇒ `subst`). -/
theorem osc_cast {a b m : ℕ} (h : a = b) (hma : m ≤ a) (f : ZMod (3^a) → ℝ) :
    osc m b (h ▸ hma) (h ▸ f) = osc m a hma f := by
  subst h; rfl

/-- Proof-irrelevant variant of `osc_cast`: takes both `m ≤ a` and `m ≤ b` explicitly. -/
theorem osc_cast' {a b m : ℕ} (h : a = b) (hma : m ≤ a) (hmb : m ≤ b) (f : ZMod (3^a) → ℝ) :
    osc m b hmb (h ▸ f) = osc m a hma f := by
  subst h; rfl

/-- **A single stopping-cut term** cast to level `n`: the windowed conditioned density at cut
`(n−1−k, k+1)` (native level `(n−1−k)+(k+1)`), transported to `ZMod (3^n)` when `k < n` (else `0`).
Wrapping the `Eq.rec` transport in its own `def` keeps it opaque to the `osc_sum_le` unifier — a raw
`▸` under the sum forces `whnf` into `condDensW`'s `tsum` on every defeq check. -/
noncomputable def castedTerm (n k l : ℕ) (C T : ℝ) : ZMod (3 ^ n) → ℝ :=
  if h : k < n then
    cutEq h ▸ condDensW (n - 1 - k) (k + 1) l (condWindowB (n - 1 - k) (k + 1) C l T)
  else 0

/-- Uniform level bound: `(n−1−k)+(k+1) ≥ n` for every `k`, so `m ≤ (n−1−k)+(k+1)` whenever `m ≤ n`. -/
theorem m_le_cut (n m : ℕ) (hmn : m ≤ n) (k : ℕ) : m ≤ n - 1 - k + (k + 1) :=
  le_trans hmn (by omega)

/-- The per-cut osc of `castedTerm` equals the native-level osc of `condDensW` (via the cast helper). -/
theorem osc_castedTerm (n m k l : ℕ) (hmn : m ≤ n) (hkn : k < n) (C T : ℝ) :
    osc m n hmn (castedTerm n k l C T)
      = osc m (n - 1 - k + (k + 1)) (m_le_cut n m hmn k)
          (condDensW (n - 1 - k) (k + 1) l (condWindowB (n - 1 - k) (k + 1) C l T)) := by
  unfold castedTerm
  rw [dif_pos hkn]
  exact osc_cast' (cutEq hkn) (m_le_cut n m hmn k) hmn _

/-- **The §6 main conditioned density at level `n`** (Tao (6.9), summed over the stopping
time `k` and the valuation `l`): the `(k,l)`-sum of the cast conditioned densities `castedTerm`. -/
noncomputable def mainDensity (n : ℕ) (C T : ℝ) (Lset : ℕ → Finset ℕ) :
    ZMod (3 ^ n) → ℝ := fun Y =>
  ∑ k ∈ Finset.range n, ∑ l ∈ Lset k, castedTerm n k l C T Y

/-- **The main-density osc bound = the k-sum cast glue** (C10 assembly): the oscillation of the
`(k,l)`-summed main density is bounded by the sum of the per-cut oscillations of the native-level
`condDensW`, via `osc_sum_le` (twice) composed with the cast helper. This discharges the k-sum
dependent-index cast `(n−1−k)+(k+1)=n` flagged as the main new friction: each summand lives on a
different `ZMod (3^…)`, but its *oscillation* is a real number transported losslessly to level `n`.
The per-cut bound `B k l` is supplied by the caller (`condDensWB_osc_le`). -/
theorem osc_mainDensity_le (n m : ℕ) (hmn : m ≤ n) (C T : ℝ)
    (Lset : ℕ → Finset ℕ) (B : ℕ → ℕ → ℝ)
    (hterm : ∀ k ∈ Finset.range n, ∀ l ∈ Lset k,
      osc m (n - 1 - k + (k + 1)) (m_le_cut n m hmn k)
        (condDensW (n - 1 - k) (k + 1) l (condWindowB (n - 1 - k) (k + 1) C l T)) ≤ B k l) :
    osc m n hmn (mainDensity n C T Lset)
      ≤ ∑ k ∈ Finset.range n, ∑ l ∈ Lset k, B k l := by
  unfold mainDensity
  refine le_trans (osc_sum_le m n hmn (Finset.range n)
    (fun k Y => ∑ l ∈ Lset k, castedTerm n k l C T Y)) ?_
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hkn : k < n := Finset.mem_range.mp hk
  refine le_trans (osc_sum_le m n hmn (Lset k)
    (fun l Y => castedTerm n k l C T Y)) ?_
  refine Finset.sum_le_sum (fun l hl => ?_)
  rw [show (fun Y => castedTerm n k l C T Y) = castedTerm n k l C T from rfl,
    osc_castedTerm n m k l hmn hkn C T]
  exact hterm k hk l hl

open Real in
/-- The (6.6) stopping threshold `T = n·log₂3 − C_A²·log n`. -/
noncomputable def caThr (C : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log 3 / Real.log 2 - C ^ 2 * Real.log n

/-- The (6.8)/tight-window valuation range for `l = a[1,k+1]` (judge pass 28: the **tight** upper
end `n·log₂3 − (C_A²−2C_A)·log n`, NOT the paper's lossy `−½C_A²`). Lower end from `Bₖ` (6.7). -/
noncomputable def lRange (C : ℝ) (n : ℕ) : Finset ℕ :=
  Finset.Icc ⌈(n : ℝ) * Real.log 3 / Real.log 2 - C ^ 2 * Real.log n⌉₊
             ⌊(n : ℝ) * Real.log 3 / Real.log 2 - (C ^ 2 - 2 * C) * Real.log n⌋₊

/-- `C_A`, the §6 conditioning constant. Tao chooses this after fixing the target exponent `A`;
that dependence is essential for the exceptional-event estimate (6.3). The explicit choice is
deliberately generous and always exceeds the tight-window budget threshold `30`. -/
noncomputable def caConst (A : ℝ) : ℝ := 1000 * (max A 0 + 3)

theorem caConst_ge_thirty (A : ℝ) : 30 ≤ caConst A := by
  unfold caConst
  have : 0 ≤ max A 0 := le_max_right _ _
  nlinarith

/-- The explicit conditioning constant has enough linear-in-`A` room for the `c = 1/400`
exponential tail supplied by `geomHalf_tail_bound`, including the quadratic union bound in (6.3). -/
theorem caConst_tail_exponent (A : ℝ) : A + 3 ≤ caConst A / 400 := by
  unfold caConst
  have hAmax : A ≤ max A 0 := le_max_left _ _
  have hmax0 : 0 ≤ max A 0 := le_max_right _ _
  nlinarith

/-- **The high-regime main density** (Tao (6.9)): the `(k,l)`-sum of the cast conditioned densities
at the `A`-dependent constant `C_A`, threshold `caThr`, and tight valuation range `lRange`. -/
noncomputable def mainHigh (A : ℝ) (n : ℕ) : ZMod (3 ^ n) → ℝ :=
  mainDensity n (caConst A) (caThr (caConst A) n) (fun _ => lRange (caConst A) n)

/-- **Discharge of `hbudget` from the tight valuation window**, uniformly for `C ≥ 30`.
The remaining logarithmic coefficient is
`C log 2 * (3 + C * (5/4 * log 2 - 1))`, uniformly negative in this range. -/
theorem lRange_hbudget_of_ge_thirty (C : ℝ) (hC : 30 ≤ C)
    (n : ℕ) (hn : 2 ≤ n) (l : ℕ) (hl : l ∈ lRange C n)
    (hwin : (C ^ 2 - 2 * C) * Real.log (n:ℝ) ≤ (n:ℝ) * Real.log 3 / Real.log 2) :
    (l : ℝ) * Real.log 2
      + (C * Real.log 2 + 5 / 4 * (C * Real.log 2) ^ 2) * Real.log (n : ℝ)
      + Real.log 4 < (n : ℝ) * Real.log 3 := by
  set L := Real.log 2 with hL
  have hLlo : (0.6931471803 : ℝ) < L := Real.log_two_gt_d9
  have hLhi : L < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hLpos : 0 < L := by linarith
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hlog4 : Real.log 4 = 2 * L := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hlogn_pos : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hlogn_ge : L ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hn2
  set coeff := C * L + 5 / 4 * (C * L) ^ 2 - (C ^ 2 - 2 * C) * L with hcoeff
  have hcoeff_val : coeff = C * L * (3 + C * (5 / 4 * L - 1)) := by rw [hcoeff]; ring
  have hslope : 5 / 4 * L - 1 < -(13 / 100 : ℝ) := by nlinarith [hLhi]
  have hfactor : 3 + C * (5 / 4 * L - 1) < -(9 / 10 : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hslope hCpos
    have hneg : C * (-(13 / 100 : ℝ)) ≤ 30 * (-(13 / 100 : ℝ)) := by nlinarith
    nlinarith
  have hCL : 0 < C * L := mul_pos hCpos hLpos
  have hCL20 : 20 < C * L := by
    have hbase : 20 < 30 * L := by nlinarith [hLlo]
    exact lt_of_lt_of_le hbase (mul_le_mul_of_nonneg_right hC hLpos.le)
  have hcoeff_lt : coeff < -2 := by
    rw [hcoeff_val]
    have hmul := mul_lt_mul_of_pos_left hfactor hCL
    nlinarith [mul_pos (sub_pos.mpr hCL20) (by norm_num : (0 : ℝ) < 9 / 10)]
  have hcoeff_neg : coeff < 0 := lt_trans hcoeff_lt (by norm_num)
  -- the window upper bound
  have hupper : (l : ℝ) * L
      ≤ (n:ℝ) * Real.log 3 - (C ^ 2 - 2 * C) * L * Real.log (n:ℝ) := by
    rw [lRange, Finset.mem_Icc] at hl
    have hlb : l ≤ ⌊(n : ℝ) * Real.log 3 / Real.log 2
        - (C ^ 2 - 2 * C) * Real.log (n:ℝ)⌋₊ := hl.2
    set hival := (n : ℝ) * Real.log 3 / Real.log 2
        - (C ^ 2 - 2 * C) * Real.log (n:ℝ) with hhi
    have hival_nonneg : 0 ≤ hival := by rw [hhi, ← hL]; linarith [hwin]
    have hlle : (l : ℝ) ≤ hival := le_trans (Nat.cast_le.mpr hlb) (Nat.floor_le hival_nonneg)
    have hmul : (l:ℝ) * L ≤ hival * L := mul_le_mul_of_nonneg_right hlle (le_of_lt hLpos)
    rw [hhi, ← hL] at hmul
    calc (l:ℝ) * L
        ≤ ((n : ℝ) * Real.log 3 / L - (C ^ 2 - 2 * C) * Real.log (n:ℝ)) * L := hmul
      _ = (n:ℝ) * Real.log 3 - (C ^ 2 - 2 * C) * L * Real.log (n:ℝ) := by field_simp
  have key : coeff * Real.log (n:ℝ) + Real.log 4 < 0 := by
    rw [hlog4]
    have h1 : coeff * Real.log (n:ℝ) ≤ coeff * L :=
      mul_le_mul_of_nonpos_left hlogn_ge (le_of_lt hcoeff_neg)
    rw [hcoeff_val] at h1
    nlinarith [h1, hLlo, hLhi, hLpos]
  have hexpand : (l : ℝ) * L
      + (C * L + 5 / 4 * (C * L) ^ 2) * Real.log (n:ℝ) + Real.log 4
      ≤ (n:ℝ) * Real.log 3 + (coeff * Real.log (n:ℝ) + Real.log 4) := by
    rw [hcoeff]; nlinarith [hupper]
  linarith [hexpand, key]

/-- The tight-window budget at the paper's `A`-dependent conditioning constant. -/
theorem lRange_hbudget (A : ℝ) (n : ℕ) (hn : 2 ≤ n) (l : ℕ)
    (hl : l ∈ lRange (caConst A) n)
    (hwin : ((caConst A) ^ 2 - 2 * caConst A) * Real.log (n:ℝ)
      ≤ (n:ℝ) * Real.log 3 / Real.log 2) :
    (l : ℝ) * Real.log 2
      + (caConst A * Real.log 2 + 5 / 4 * (caConst A * Real.log 2) ^ 2) * Real.log (n : ℝ)
      + Real.log 4 < (n : ℝ) * Real.log 3 := by
  apply lRange_hbudget_of_ge_thirty (caConst A) _ n hn l hl hwin
  exact caConst_ge_thirty A

/-- **The pointwise main/error split combiner** (C10 obl-1 skeleton, fully proved): splitting the
syracZ density as `main + (syracZ − main)`, its oscillation is bounded by `osc(main)` plus twice the
error `L¹` mass (`osc_add_le` + `osc_le_two_mul_l1`). The content is entirely in the two inputs. -/
theorem osc_syracZ_split_le (m n : ℕ) (hmn : m ≤ n) (main : ZMod (3 ^ n) → ℝ) (b : ℝ)
    (hmain : osc m n hmn main ≤ b)
    (herr : 2 * ∑ Y, |(syracZ n Y).toReal - main Y| ≤ b) :
    osc m n hmn (fun Y => (syracZ n Y).toReal) ≤ b + b := by
  have hsplit : (fun Y => (syracZ n Y).toReal)
      = (fun Y => main Y + ((syracZ n Y).toReal - main Y)) := by funext Y; ring
  rw [hsplit]
  refine le_trans (osc_add_le m n hmn main (fun Y => (syracZ n Y).toReal - main Y)) ?_
  exact add_le_add hmain (le_trans (osc_le_two_mul_l1 m n hmn _) herr)

end TaoCollatz
