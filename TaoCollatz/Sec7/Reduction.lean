import TaoCollatz.Sec7.Bridge
import TaoCollatz.Sec7.White

/-!
# §7.1: reduction of Proposition 7.1 to Proposition 7.3 (node X1)

Paper anchors: Tao 2019 pp.33–35, (7.1)–(7.6), Lemma 7.2. The character sum
`S_χ(n)` over `a ~ Geom(2)ⁿ` (Prop 7.1 = `key_fourier_decay`) is reduced to the
white-encounter damping expectation (Prop 7.3 = `renewal_white_encounters`,
PROVED in `Bridge.lean`) in three steps:

1. **Pairing/conditioning (7.4)–(7.5)** (`cexpect_pairing`, the X1 crux `sorry`):
   group the `n` geometric variables into pairs `b_j = a_{2j-1} + a_{2j}`
   (`b ~ Pascal^{⌊n/2⌋}`, `pascal_eq_map_iid`); conditionally on all `b_j` the
   factors `χ(x_j(2^{a_{2j}}+3))` are independent, giving
   `|S_χ(n)| ≤ E_b ∏_j |f(x_j, b_j)|` where `f` is the conditional character
   average (7.4) and `x_j = 3^{2j-2}·2^{-b_{[1,j]}}`; the odd-`n` leftover factor
   `g` has `|g| ≤ 1` and is dropped (7.6).
2. **Lemma 7.2** (`fCond_three_norm`): at `b = 3` the conditional pair is uniform
   on `{(1,2),(2,1)}`, so `|f(x,3)| = |1 + χ(2x)|/2 = |cos(π θ(j,l))|`.
3. **Damping** (`prod_fCond_le_damping`): `|f| ≤ 1` always (7.6), and
   `≤ exp(-ε³)` at white renewal points (`white_cos_bound`, node X2); hence the
   product is dominated by `exp(-ε³ · #white encounters)` — Prop 7.3's integrand.

`key_fourier_decay` (Prop 7.1; statement moved verbatim from `Holding.lean`,
2026-07-12) is then PROVED from these pieces.
-/

open scoped Real ENNReal

namespace TaoCollatz

/-! ### Additive-character helpers for `eC` -/

/-- `eC` has unit norm. -/
theorem eC_norm (q : ℚ) : ‖eC q‖ = 1 := by
  unfold eC
  have harg : 2 * Real.pi * Complex.I * (q : ℂ) = ((2 * Real.pi * q : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

/-- `eC` is additive: `e(q + r) = e(q)·e(r)`. -/
theorem eC_add (q r : ℚ) : eC (q + r) = eC q * eC r := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

/-- `eC` is trivial on integers. -/
theorem eC_intCast (k : ℤ) : eC (k : ℚ) = 1 := by
  unfold eC
  have harg : 2 * Real.pi * Complex.I * ((k : ℚ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]

/-- The character `y ↦ e(-ξ·y.val/3ⁿ)` (paper (7.1)) is additive on `ZMod (3ⁿ)`:
the `val` of a sum differs from the sum of `val`s by a multiple of `3ⁿ`, which
`eC` kills. -/
theorem eC_char_add (n ξ : ℕ) (y z : ZMod (3 ^ n)) :
    eC (-(ξ * (((y + z).val : ℕ) : ℚ)) / 3 ^ n)
      = eC (-(ξ * ((y.val : ℕ) : ℚ)) / 3 ^ n) * eC (-(ξ * ((z.val : ℕ) : ℚ)) / 3 ^ n) := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  set t : ℕ := (y.val + z.val) / 3 ^ n with ht
  have hval : y.val + z.val = 3 ^ n * t + (y + z).val := by
    rw [ZMod.val_add, ht]
    exact (Nat.div_add_mod _ _).symm
  have hq : ((y.val : ℚ)) + ((z.val : ℚ)) = 3 ^ n * (t : ℚ) + (((y + z).val : ℕ) : ℚ) := by
    exact_mod_cast hval
  have h3 : (3 : ℚ) ^ n ≠ 0 := by positivity
  have hv : (((y + z).val : ℕ) : ℚ) = (y.val : ℚ) + (z.val : ℚ) - 3 ^ n * (t : ℚ) := by
    linarith
  have hnat : eC (((ξ * t : ℕ) : ℚ)) = 1 := by
    have := eC_intCast ((ξ * t : ℕ) : ℤ)
    simpa using this
  have hsplit : -(ξ * (((y + z).val : ℕ) : ℚ)) / 3 ^ n
      = (-(ξ * ((y.val : ℕ) : ℚ)) / 3 ^ n + -(ξ * ((z.val : ℕ) : ℚ)) / 3 ^ n)
        + ((ξ * t : ℕ) : ℚ) := by
    rw [hv]
    field_simp
    push_cast
    ring
  rw [hsplit, eC_add, eC_add, hnat, mul_one]

/-! ### The conditional character factor `f(x,b)` (paper (7.4)) -/

/-- **The pair-conditioned character factor** `f(x,b)` (paper (7.4)), concretely:
conditioned on `a₁ + a₂ = b` for `(a₁,a₂)` iid `Geom(2)`, the pair is uniform over
the `b-1` values `a₂ ∈ [1, b-1]`, so
`f(x,b) = (b-1)⁻¹ · ∑_{a=1}^{b-1} χ(x·(2^a+3))` with `χ(y) := e(-ξ·y.val/3ⁿ)`.
For `b ≤ 1` (off `Pascal`'s support) the empty sum makes `f = 0`. -/
noncomputable def fCond (n ξ : ℕ) (x : ZMod (3 ^ n)) (b : ℕ) : ℂ :=
  ((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1),
    eC (-(ξ * (((x * (2 ^ a + 3)).val : ℕ) : ℚ)) / 3 ^ n)

/-- The renewal-coordinate argument `x_j = 3^{2j-2}·2^{-b_{[1,j]}}` of (7.5), in
Lean coordinates (RATIFY-4: paper `j = j_lean + 1`, so the exponent is `2j`). -/
noncomputable def xArg (n j l : ℕ) : ZMod (3 ^ n) :=
  3 ^ (2 * j) * (2 : ZMod (3 ^ n))⁻¹ ^ l

/-- Paper (7.6): `|f(x,b)| ≤ 1` — `f` is an average of unit vectors (and `0` for
`b ≤ 1`). -/
theorem fCond_norm_le_one (n ξ : ℕ) (x : ZMod (3 ^ n)) (b : ℕ) :
    ‖fCond n ξ x b‖ ≤ 1 := by
  unfold fCond
  rcases Nat.lt_or_ge b 2 with hb | hb
  · have h0 : b - 1 = 0 := by omega
    simp [h0]
  · rw [norm_mul]
    have hcast : ((b : ℂ) - 1) = (((b - 1 : ℕ) : ℕ) : ℂ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ b)]; ring
    have hinv : ‖((b : ℂ) - 1)⁻¹‖ = (((b - 1 : ℕ) : ℝ))⁻¹ := by
      rw [norm_inv, hcast, Complex.norm_natCast]
    have hsum : ‖∑ a ∈ Finset.Icc 1 (b - 1),
        eC (-(ξ * (((x * (2 ^ a + 3)).val : ℕ) : ℚ)) / 3 ^ n)‖ ≤ ((b - 1 : ℕ) : ℝ) := by
      calc ‖∑ a ∈ Finset.Icc 1 (b - 1),
            eC (-(ξ * (((x * (2 ^ a + 3)).val : ℕ) : ℚ)) / 3 ^ n)‖
          ≤ ∑ a ∈ Finset.Icc 1 (b - 1),
            ‖eC (-(ξ * (((x * (2 ^ a + 3)).val : ℕ) : ℚ)) / 3 ^ n)‖ :=
            norm_sum_le _ _
        _ = ((b - 1 : ℕ) : ℝ) := by
            rw [Finset.sum_congr rfl fun a _ => eC_norm _, Finset.sum_const,
              Nat.card_Icc, nsmul_eq_mul, mul_one]
            congr 1
    have hpos : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by
      have : 1 ≤ b - 1 := by omega
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    rw [hinv]
    calc (((b - 1 : ℕ) : ℝ))⁻¹ * ‖∑ a ∈ Finset.Icc 1 (b - 1),
          eC (-(ξ * (((x * (2 ^ a + 3)).val : ℕ) : ℚ)) / 3 ^ n)‖
        ≤ (((b - 1 : ℕ) : ℝ))⁻¹ * ((b - 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- `‖1 + e(-q)‖ = 2·|cos(πq)|`: factor out the half-angle phase,
`1 + e^{iφ} = e^{iφ/2}·2cos(φ/2)`. -/
theorem norm_one_add_eC_neg (q : ℚ) : ‖1 + eC (-q)‖ = 2 * |Real.cos (Real.pi * q)| := by
  have hfact : (1 : ℂ) + eC (-q)
      = Complex.exp (-(Real.pi * q) * Complex.I)
        * (2 * Complex.cos (((Real.pi * (q : ℝ) : ℝ) : ℂ))) := by
    rw [Complex.cos, mul_comm (2 : ℂ)]
    rw [div_mul_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
    unfold eC
    congr 1
    · rw [← Complex.exp_zero]
      congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  rw [hfact, norm_mul]
  have h1 : ‖Complex.exp (-(Real.pi * q) * Complex.I)‖ = 1 := by
    have harg : -(Real.pi * (q : ℂ)) * Complex.I = ((-(Real.pi * q) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  rw [h1, one_mul, ← Complex.ofReal_cos, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num

/-- **Lemma 7.2, concrete form**: at `b = 3` the conditional factor has magnitude
exactly `|cos(π θ(j,l))|` — the pair `(a₁,a₂)` is uniform on `{(1,2),(2,1)}`, so
`f(x,3) = (χ(5x) + χ(7x))/2 = χ(5x)(1 + χ(2x))/2` and `2x = 3^{2j}·2^{1-l}` is the
(7.7) phase point. -/
theorem fCond_three_norm (n ξ j l : ℕ) :
    ‖fCond n ξ (xArg n j l) 3‖ = |cosπθ n ξ j (l : ℤ)| := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  set x := xArg n j l with hx
  -- the two-term sum: a ∈ {1, 2}
  have hIcc : Finset.Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) := by decide
  have hsum : fCond n ξ x 3
      = ((3 : ℂ) - 1)⁻¹ *
        (eC (-(ξ * (((x * 5).val : ℕ) : ℚ)) / 3 ^ n)
          + eC (-(ξ * (((x * 7).val : ℕ) : ℚ)) / 3 ^ n)) := by
    unfold fCond
    rw [hIcc, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
  -- χ(7x) = χ(5x)·χ(2x)
  have hsplit : eC (-(ξ * (((x * 7).val : ℕ) : ℚ)) / 3 ^ n)
      = eC (-(ξ * (((x * 5).val : ℕ) : ℚ)) / 3 ^ n)
        * eC (-(ξ * (((x * 2).val : ℕ) : ℚ)) / 3 ^ n) := by
    have h7 : x * 7 = x * 5 + x * 2 := by ring
    rw [h7]
    exact eC_char_add n ξ (x * 5) (x * 2)
  -- 2x is the θ phase point: x·2 = 3^{2j}·u2^{1-l}
  have hphase : x * 2 = 3 ^ (2 * j) * (((u2 n) ^ ((1 : ℤ) - (l : ℤ)) : (ZMod (3 ^ n))ˣ)
      : ZMod (3 ^ n)) := by
    have hu2 : ((u2 n : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) = 2 := by
      rw [u2, ZMod.coe_unitOfCoprime]; norm_num
    have hinv2 : (2 : ZMod (3 ^ n))⁻¹ = ((u2 n)⁻¹ : (ZMod (3 ^ n))ˣ) := by
      rw [← hu2, ZMod.inv_coe_unit]
    have hzpow : (((u2 n) ^ ((1 : ℤ) - (l : ℤ)) : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n))
        = 2 * (2 : ZMod (3 ^ n))⁻¹ ^ l := by
      rw [hinv2, ← Units.val_pow_eq_pow_val, inv_pow, sub_eq_add_neg, zpow_add (u2 n),
        zpow_one, zpow_neg, zpow_natCast, Units.val_mul, hu2]
    rw [hzpow, hx]
    unfold xArg
    ring
  -- χ at the phase point is e(-θ)
  have hchi : eC (-(ξ * (((x * 2).val : ℕ) : ℚ)) / 3 ^ n) = eC (-(θq n ξ j (l : ℤ))) := by
    set W : ZMod (3 ^ n) := 3 ^ (2 * j) * (((u2 n) ^ ((1 : ℤ) - (l : ℤ)) : (ZMod (3 ^ n))ˣ)
      : ZMod (3 ^ n)) with hW
    rw [hphase]
    have hθ : θq n ξ j (l : ℤ) = sfrac ((ξ * (W.val : ℚ)) / 3 ^ n) := by
      rw [θq, hW]
    have hround : -(ξ * ((W.val : ℕ) : ℚ)) / 3 ^ n
        = -(θq n ξ j (l : ℤ)) + (-(round ((ξ * (W.val : ℚ)) / 3 ^ n)) : ℤ) := by
      rw [hθ]
      unfold sfrac
      push_cast
      ring
    rw [hround, eC_add, eC_intCast, mul_one]
  rw [hsum, hsplit, hchi, ← mul_one_add, norm_mul, norm_mul]
  have h3inv : ‖((3 : ℂ) - 1)⁻¹‖ = 2⁻¹ := by
    norm_num
  rw [h3inv, eC_norm, one_mul, norm_one_add_eC_neg, cosπθ]
  ring

/-! ### The (7.5) pairing bound — the X1 crux -/

open Classical in
/-- `cexpect` of a pushforward is `cexpect` of the composition (for bounded
observables): the (1.26) seam between `syracZ` and the raw geometric vector. -/
theorem cexpect_map {α β : Type*} (p : PMF α) (f : α → β) (g : β → ℂ)
    (hg : ∀ b, ‖g b‖ ≤ 1) :
    (p.map f).cexpect g = p.cexpect fun a => g (f a) := by
  have hsumP : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hite0 : ∀ (b : β) (a : α), (0 : ℝ) ≤ (if b = f a then (p a).toReal else 0) := by
    intro b a; split <;> simp [ENNReal.toReal_nonneg]
  have hiteP : ∀ (b : β) (a : α), (if b = f a then (p a).toReal else 0) ≤ (p a).toReal := by
    intro b a; split <;> simp [ENNReal.toReal_nonneg]
  have hsIte : ∀ b : β, Summable fun a => (if b = f a then (p a).toReal else 0 : ℝ) :=
    fun b => Summable.of_nonneg_of_le (hite0 b) (hiteP b) hsumP
  -- the pushforward mass at b, in ℝ
  have hreal : ∀ b, ((p.map f) b).toReal
      = ∑' a, (if b = f a then (p a).toReal else 0 : ℝ) := by
    intro b
    rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
    · exact tsum_congr fun a => by rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    · intro a
      split
      · exact p.apply_ne_top a
      · exact ENNReal.zero_ne_top
  have hmap : ∀ b, (((p.map f) b).toReal : ℂ)
      = ∑' a, ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ) := by
    intro b
    rw [hreal b]
    exact (Complex.ofRealCLM.hasSum (hsIte b).hasSum).tsum_eq.symm
  -- summability on the product
  have hG : Summable fun ab : β × α => (if ab.1 = f ab.2 then (p ab.2).toReal else 0 : ℝ) := by
    rw [summable_prod_of_nonneg (fun ab => hite0 ab.1 ab.2)]
    exact ⟨fun b => hsIte b,
      Summable.of_nonneg_of_le (fun b => tsum_nonneg (hite0 b))
        (fun b => (hreal b).ge)
        (ENNReal.summable_toReal (p.map f).tsum_coe_ne_top)⟩
  have hF : Summable fun ab : β × α =>
      ((if ab.1 = f ab.2 then (p ab.2).toReal else 0 : ℝ) : ℂ) * g ab.1 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun ab => norm_nonneg _)
      (fun ab => ?_) hG)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hite0 ab.1 ab.2)]
    calc (if ab.1 = f ab.2 then (p ab.2).toReal else 0 : ℝ) * ‖g ab.1‖
        ≤ (if ab.1 = f ab.2 then (p ab.2).toReal else 0 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (hg ab.1) (hite0 ab.1 ab.2)
      _ = _ := mul_one _
  -- assemble
  show ∑' b, (((p.map f) b).toReal : ℂ) * g b = ∑' a, ((p a).toReal : ℂ) * g (f a)
  calc ∑' b, (((p.map f) b).toReal : ℂ) * g b
      = ∑' b, ∑' a, ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ) * g b := by
        refine tsum_congr fun b => ?_
        rw [hmap b, tsum_mul_right]
    _ = ∑' a, ∑' b, ((if b = f a then (p a).toReal else 0 : ℝ) : ℂ) * g b := by
        refine (Summable.tsum_comm' hF (fun b => ?_) (fun a => ?_)).symm
        · exact (Complex.ofRealCLM.summable (hsIte b)).mul_right (g b)
        · refine summable_of_ne_finset_zero (s := {f a}) (fun b hb => ?_)
          rw [if_neg (by simpa using hb), Complex.ofReal_zero, zero_mul]
    _ = ∑' a, ((p a).toReal : ℂ) * g (f a) := by
        refine tsum_congr fun a => ?_
        rw [tsum_eq_single (f a) (fun b hb => ?_)]
        · rw [if_pos rfl]
        · rw [if_neg hb, Complex.ofReal_zero, zero_mul]

/-! #### `cexpect` calculus for the pair-peeling induction -/

/-- Triangle bound: a `cexpect` of unit-bounded observables has norm `≤ 1`. -/
theorem cexpect_norm_le {α : Type*} (p : PMF α) (f : α → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1) :
    ‖p.cexpect f‖ ≤ 1 := by
  have hsumP : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hb : ∀ a, ‖((p a).toReal : ℂ) * f a‖ ≤ (p a).toReal := fun a => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    calc (p a).toReal * ‖f a‖ ≤ (p a).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hf a) ENNReal.toReal_nonneg
      _ = _ := mul_one _
  have hsn : Summable fun a => ‖((p a).toReal : ℂ) * f a‖ :=
    Summable.of_nonneg_of_le (fun a => norm_nonneg _) hb hsumP
  calc ‖p.cexpect f‖ ≤ ∑' a, ‖((p a).toReal : ℂ) * f a‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' a, (p a).toReal := hsn.tsum_le_tsum hb hsumP
    _ = 1 := by
        rw [← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe,
          ENNReal.toReal_one]

/-- `cexpect` pulls out a constant factor. -/
theorem cexpect_const_mul {α : Type*} (p : PMF α) (c : ℂ) (f : α → ℂ) :
    (p.cexpect fun a => c * f a) = c * p.cexpect f := by
  show ∑' a, ((p a).toReal : ℂ) * (c * f a) = c * ∑' a, ((p a).toReal : ℂ) * f a
  rw [← tsum_mul_left]
  exact tsum_congr fun a => by ring

open Classical in
/-- `cexpect` of a bind averages the fiber `cexpect`s (bounded observables). -/
theorem cexpect_bind {α β : Type*} (p : PMF α) (q : α → PMF β) (g : β → ℂ)
    (hg : ∀ b, ‖g b‖ ≤ 1) :
    (p.bind q).cexpect g = ∑' a, ((p a).toReal : ℂ) * (q a).cexpect g := by
  have hsumP : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hq1 : ∀ (a : α) (b : β), (q a b).toReal ≤ 1 := fun a b => by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top ((q a).coe_le_one b)
  have hw0 : ∀ (b : β) (a : α), (0 : ℝ) ≤ (p a).toReal * (q a b).toReal := fun b a =>
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hwle : ∀ (b : β) (a : α), (p a).toReal * (q a b).toReal ≤ (p a).toReal := fun b a =>
    (mul_le_mul_of_nonneg_left (hq1 a b) ENNReal.toReal_nonneg).trans (mul_one _).le
  have hsFib : ∀ b : β, Summable fun a => (p a).toReal * (q a b).toReal := fun b =>
    Summable.of_nonneg_of_le (hw0 b) (hwle b) hsumP
  have hreal : ∀ b, ((p.bind q) b).toReal = ∑' a, (p a).toReal * (q a b).toReal := by
    intro b
    rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
      (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b))]
    exact tsum_congr fun a => ENNReal.toReal_mul
  have hmap : ∀ b, (((p.bind q) b).toReal : ℂ)
      = ∑' a, (((p a).toReal * (q a b).toReal : ℝ) : ℂ) := by
    intro b
    rw [hreal b]
    exact (Complex.ofRealCLM.hasSum (hsFib b).hasSum).tsum_eq.symm
  have hG : Summable fun ba : β × α => (p ba.2).toReal * (q ba.2 ba.1).toReal := by
    rw [summable_prod_of_nonneg (fun ba => hw0 ba.1 ba.2)]
    exact ⟨fun b => hsFib b,
      Summable.of_nonneg_of_le (fun b => tsum_nonneg (hw0 b)) (fun b => (hreal b).ge)
        (ENNReal.summable_toReal (p.bind q).tsum_coe_ne_top)⟩
  have hF : Summable fun ba : β × α =>
      (((p ba.2).toReal * (q ba.2 ba.1).toReal : ℝ) : ℂ) * g ba.1 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun ba => norm_nonneg _)
      (fun ba => ?_) hG)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 ba.1 ba.2)]
    calc ((p ba.2).toReal * (q ba.2 ba.1).toReal) * ‖g ba.1‖
        ≤ ((p ba.2).toReal * (q ba.2 ba.1).toReal) * 1 :=
          mul_le_mul_of_nonneg_left (hg ba.1) (hw0 ba.1 ba.2)
      _ = _ := mul_one _
  show ∑' b, (((p.bind q) b).toReal : ℂ) * g b = _
  calc ∑' b, (((p.bind q) b).toReal : ℂ) * g b
      = ∑' b, ∑' a, (((p a).toReal * (q a b).toReal : ℝ) : ℂ) * g b := by
        refine tsum_congr fun b => ?_
        rw [hmap b, tsum_mul_right]
    _ = ∑' a, ∑' b, (((p a).toReal * (q a b).toReal : ℝ) : ℂ) * g b := by
        refine (Summable.tsum_comm' hF (fun b => ?_) (fun a => ?_)).symm
        · refine Summable.of_norm (Summable.of_nonneg_of_le (fun a => norm_nonneg _)
            (fun a => ?_) hsumP)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw0 b a)]
          calc ((p a).toReal * (q a b).toReal) * ‖g b‖
              ≤ ((p a).toReal * (q a b).toReal) * 1 :=
                mul_le_mul_of_nonneg_left (hg b) (hw0 b a)
            _ ≤ (p a).toReal := (mul_one _).le.trans (hwle b a)
        · refine Summable.of_norm (Summable.of_nonneg_of_le (fun b => norm_nonneg _)
            (fun b => ?_) ((ENNReal.summable_toReal (q a).tsum_coe_ne_top).mul_left
              ((p a).toReal)))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw0 b a)]
          calc ((p a).toReal * (q a b).toReal) * ‖g b‖
              ≤ ((p a).toReal * (q a b).toReal) * 1 :=
                mul_le_mul_of_nonneg_left (hg b) (hw0 b a)
            _ = (p a).toReal * (q a b).toReal := mul_one _
    _ = ∑' a, ((p a).toReal : ℂ) * (q a).cexpect g := by
        refine tsum_congr fun a => ?_
        show ∑' b, (((p a).toReal * (q a b).toReal : ℝ) : ℂ) * g b
          = ((p a).toReal : ℂ) * ∑' b, ((q a b).toReal : ℂ) * g b
        rw [← tsum_mul_left]
        exact tsum_congr fun b => by push_cast; ring

/-- Peel one coordinate off a `cexpect` over an iid vector. -/
theorem cexpect_iid_succ {α : Type*} (p : PMF α) (m : ℕ) (h : (Fin (m + 1) → α) → ℂ)
    (hh : ∀ v, ‖h v‖ ≤ 1) :
    (p.iid (m + 1)).cexpect h
      = ∑' a, ((p a).toReal : ℂ) * (p.iid m).cexpect fun w => h (Fin.cons a w) := by
  rw [show p.iid (m + 1) = p.bind fun a => (p.iid m).map (Fin.cons a) from rfl,
    cexpect_bind _ _ _ hh]
  exact tsum_congr fun a => by rw [cexpect_map _ _ _ hh]

/-! #### Mass functions in ℝ, and the head-pair reindex -/

/-- `geomHalf` mass in ℝ. -/
theorem geomHalf_toReal (a : ℕ) :
    (geomHalf a).toReal = if a = 0 then 0 else (2⁻¹ : ℝ) ^ a := by
  rw [geomHalf_apply]
  split
  · exact ENNReal.toReal_zero
  · rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]

/-- `pascal` mass in ℝ. -/
theorem pascal_toReal (b : ℕ) :
    (pascal b).toReal = if b < 2 then 0 else ((b - 1 : ℕ) : ℝ) * 2⁻¹ ^ b := by
  have happ : pascal b
      = if b < 2 then (0 : ℝ≥0∞) else ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b := rfl
  rw [happ]
  split
  · exact ENNReal.toReal_zero
  · rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat]

/-- Prefix sums start at zero. -/
theorem pre_zero {ℓ : ℕ} (u : Fin ℓ → ℕ) : pre u 0 = 0 := by
  unfold pre
  exact Finset.sum_range_zero _

/-- `2⁻¹`-power cancellation in `ZMod (3ⁿ)` (2 is a unit). -/
theorem inv2_cancel (n i j : ℕ) :
    (2 : ZMod (3 ^ n))⁻¹ ^ (i + j) * 2 ^ j = (2 : ZMod (3 ^ n))⁻¹ ^ i := by
  have hu2 : ((u2 n : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) = 2 := by
    rw [u2, ZMod.coe_unitOfCoprime]; norm_num
  have hu : IsUnit (2 : ZMod (3 ^ n)) := hu2 ▸ (u2 n).isUnit
  have h1 : (2 : ZMod (3 ^ n))⁻¹ * 2 = 1 := ZMod.inv_mul_of_unit 2 hu
  rw [pow_add, mul_assoc, ← mul_pow, h1, one_pow, mul_one]

set_option maxHeartbeats 1000000 in
/-- **Head-pair reindex**: a double `Geom(2)` expectation, grouped by `b = a₀+a₁`,
is a `pascal` expectation of the uniform pair average — the (7.4) conditioning
made exact. The map `(a₀,a₁) ↦ (a₀+a₁,a₁)` is injective with range
`{(b,a) : a ≤ b}`; endpoints `a ∈ {0,b}` carry zero `geomHalf` mass, leaving the
uniform average over `a ∈ [1,b-1]` with weight `2⁻ᵇ = pascal(b)/(b-1)`. -/
theorem tsum_geom_pair (G : ℕ → ℕ → ℂ) (hG : ∀ b a, ‖G b a‖ ≤ 1) :
    ∑' a₀ : ℕ, ((geomHalf a₀).toReal : ℂ)
        * ∑' a₁ : ℕ, ((geomHalf a₁).toReal : ℂ) * G (a₀ + a₁) a₁
      = ∑' b : ℕ, ((pascal b).toReal : ℂ)
          * (((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), G b a) := by
  have hgr0 : ∀ a, (0 : ℝ) ≤ (geomHalf a).toReal := fun a => ENNReal.toReal_nonneg
  have hgrS : Summable fun a => (geomHalf a).toReal :=
    ENNReal.summable_toReal geomHalf.tsum_coe_ne_top
  -- the paired summand and its zero-extension
  set f₁ : ℕ × ℕ → ℂ := fun q =>
    (((geomHalf q.1).toReal : ℂ) * ((geomHalf q.2).toReal : ℂ)) * G (q.1 + q.2) q.2
    with hf₁
  set F : ℕ × ℕ → ℂ := fun q =>
    if q.2 ≤ q.1 then
      (((geomHalf (q.1 - q.2)).toReal : ℂ) * ((geomHalf q.2).toReal : ℂ)) * G q.1 q.2
    else 0 with hF
  have hprod : Summable fun q : ℕ × ℕ => (geomHalf q.1).toReal * (geomHalf q.2).toReal :=
    hgrS.mul_of_nonneg hgrS hgr0 hgr0
  have hf₁norm : ∀ q : ℕ × ℕ, ‖f₁ q‖ ≤ (geomHalf q.1).toReal * (geomHalf q.2).toReal := by
    intro q
    rw [hf₁]
    dsimp only
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (hgr0 _), abs_of_nonneg (hgr0 _)]
    calc (geomHalf q.1).toReal * (geomHalf q.2).toReal * ‖G (q.1 + q.2) q.2‖
        ≤ (geomHalf q.1).toReal * (geomHalf q.2).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hG _ _) (mul_nonneg (hgr0 _) (hgr0 _))
      _ = _ := mul_one _
  have hf₁S : Summable f₁ :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun q => norm_nonneg _) hf₁norm hprod)
  -- the reindexing injection
  have hi : Function.Injective (fun q : ℕ × ℕ => (q.1 + q.2, q.2)) := by
    intro q q' h
    rw [Prod.ext_iff] at h ⊢
    obtain ⟨h1, h2⟩ := h
    dsimp only at h1 h2
    omega
  have hcomp : ∀ q : ℕ × ℕ, F (q.1 + q.2, q.2) = f₁ q := by
    intro q
    rw [hF, hf₁]
    dsimp only
    rw [if_pos (Nat.le_add_left _ _), Nat.add_sub_cancel]
  have hsupp : ∀ x : ℕ × ℕ, x ∉ Set.range (fun q : ℕ × ℕ => (q.1 + q.2, q.2)) → F x = 0 := by
    intro x hx
    rw [hF]
    dsimp only
    rw [if_neg]
    intro hle
    exact hx ⟨(x.1 - x.2, x.2), by
      rw [Prod.ext_iff]
      exact ⟨by dsimp only; omega, rfl⟩⟩
  have hFS : Summable F := by
    rw [← Function.Injective.summable_iff hi hsupp]
    exact hf₁S.congr fun q => (hcomp q).symm
  -- fibers of f₁ and F
  have hf₁fib : ∀ a₀, Summable fun a₁ => f₁ (a₀, a₁) := by
    intro a₀
    have hb : Summable fun a₁ : ℕ =>
        (geomHalf (a₀, a₁).1).toReal * (geomHalf (a₀, a₁).2).toReal := by
      simpa using hgrS.mul_left ((geomHalf a₀).toReal)
    exact Summable.of_norm (Summable.of_nonneg_of_le (fun a₁ => norm_nonneg _)
      (fun a₁ => hf₁norm (a₀, a₁)) hb)
  have hFfib : ∀ b, Summable fun a => F (b, a) := by
    intro b
    refine summable_of_ne_finset_zero (s := Finset.range (b + 1)) (fun a ha => ?_)
    rw [hF]
    dsimp only
    rw [if_neg (by simp at ha; omega)]
  -- assemble
  calc ∑' a₀ : ℕ, ((geomHalf a₀).toReal : ℂ)
        * ∑' a₁ : ℕ, ((geomHalf a₁).toReal : ℂ) * G (a₀ + a₁) a₁
      = ∑' a₀, ∑' a₁, f₁ (a₀, a₁) := by
        refine tsum_congr fun a₀ => ?_
        rw [← tsum_mul_left]
        exact tsum_congr fun a₁ => by rw [hf₁]; dsimp only; ring
    _ = ∑' q : ℕ × ℕ, f₁ q := (hf₁S.tsum_prod' hf₁fib).symm
    _ = ∑' q : ℕ × ℕ, F (q.1 + q.2, q.2) := (tsum_congr fun q => (hcomp q).symm)
    _ = ∑' x : ℕ × ℕ, F x := Function.Injective.tsum_eq hi (Function.support_subset_iff'.2 hsupp)
    _ = ∑' b, ∑' a, F (b, a) := hFS.tsum_prod' hFfib
    _ = ∑' b : ℕ, ((pascal b).toReal : ℂ)
          * (((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), G b a) := by
        refine tsum_congr fun b => ?_
        -- the fiber is a finite sum over [1, b-1]
        have hfin : ∑' a, F (b, a) = ∑ a ∈ Finset.Icc 1 (b - 1), F (b, a) := by
          refine tsum_eq_sum (fun a ha => ?_)
          rw [hF]
          dsimp only
          rcases Nat.lt_or_ge b a with hab | hab
          · rw [if_neg (by omega)]
          · rw [if_pos hab]
            simp only [Finset.mem_Icc, not_and_or, not_le] at ha
            rcases ha with h1 | h2
            · have ha0 : a = 0 := by omega
              rw [ha0]
              simp [geomHalf_toReal]
            · have hab' : a = b := by omega
              rw [hab', Nat.sub_self]
              simp [geomHalf_toReal]
        rw [hfin]
        rcases Nat.lt_or_ge b 2 with hb | hb
        · -- b < 2: both sides vanish
          have hIcc : Finset.Icc 1 (b - 1) = (∅ : Finset ℕ) := by
            rw [Finset.Icc_eq_empty_iff]
            omega
          rw [hIcc, Finset.sum_empty, Finset.sum_empty, pascal_toReal, if_pos hb]
          norm_num
        · -- b ≥ 2: uniform weight 2⁻ᵇ per pair
          have hterm : ∀ a ∈ Finset.Icc 1 (b - 1),
              F (b, a) = (((2⁻¹ : ℝ) ^ b : ℝ) : ℂ) * G b a := by
            intro a ha
            simp only [Finset.mem_Icc] at ha
            rw [hF]
            dsimp only
            rw [if_pos (by omega), geomHalf_toReal, geomHalf_toReal,
              if_neg (by omega), if_neg (by omega)]
            push_cast
            have hpow : (2⁻¹ : ℂ) ^ (b - a) * (2⁻¹ : ℂ) ^ a = (2⁻¹ : ℂ) ^ b := by
              rw [← pow_add]
              congr 1
              omega
            rw [← hpow]
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, pascal_toReal, if_neg (by omega)]
          have hne : ((b - 1 : ℕ) : ℂ) ≠ 0 := by
            rw [Nat.cast_ne_zero]
            omega
          have hcast : ((b : ℂ) - 1) = ((b - 1 : ℕ) : ℂ) := by
            push_cast [Nat.cast_sub (by omega : 1 ≤ b)]
            ring
          rw [hcast]
          push_cast
          field_simp

/-- Real-expectation constant pull-out. -/
theorem expect_const_mul {α : Type*} (p : PMF α) (c : ℝ) (f : α → ℝ) :
    (p.expect fun a => c * f a) = c * p.expect f := by
  show ∑' a, (p a).toReal * (c * f a) = c * ∑' a, (p a).toReal * f a
  rw [← tsum_mul_left]
  exact tsum_congr fun a => by ring

/-- Real-expectation monotonicity for `[0,1]`-dominated observables. -/
theorem expect_mono_le {α : Type*} (p : PMF α) (f g : α → ℝ) (hf0 : ∀ a, 0 ≤ f a)
    (hfg : ∀ a, f a ≤ g a) (hg1 : ∀ a, g a ≤ 1) : p.expect f ≤ p.expect g := by
  have hsumP : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hgle : ∀ a, (p a).toReal * g a ≤ (p a).toReal := fun a =>
    (mul_le_mul_of_nonneg_left (hg1 a) ENNReal.toReal_nonneg).trans (mul_one _).le
  have hfle : ∀ a, (p a).toReal * f a ≤ (p a).toReal := fun a =>
    (mul_le_mul_of_nonneg_left ((hfg a).trans (hg1 a)) ENNReal.toReal_nonneg).trans
      (mul_one _).le
  have hsumg : Summable fun a => (p a).toReal * g a :=
    Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg ((hf0 a).trans (hfg a))) hgle hsumP
  have hsumf : Summable fun a => (p a).toReal * f a :=
    Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (hf0 a)) hfle hsumP
  exact hsumf.tsum_le_tsum
    (fun a => mul_le_mul_of_nonneg_left (hfg a) ENNReal.toReal_nonneg) hsumg

/-- Expectations of `[0,1]` observables are at most one. -/
theorem expect_le_one {α : Type*} (p : PMF α) (f : α → ℝ) (h0 : ∀ a, 0 ≤ f a)
    (h1 : ∀ a, f a ≤ 1) : p.expect f ≤ 1 := by
  calc p.expect f ≤ p.expect fun _ => 1 :=
        expect_mono_le p f (fun _ => 1) h0 h1 (fun _ => le_refl 1)
    _ = 1 := by
        show ∑' a, (p a).toReal * 1 = 1
        simp only [mul_one]
        rw [← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe,
          ENNReal.toReal_one]

/-- Expectations of nonneg observables are nonneg. -/
theorem expect_nonneg {α : Type*} (p : PMF α) (f : α → ℝ) (h0 : ∀ a, 0 ≤ f a) :
    0 ≤ p.expect f :=
  tsum_nonneg fun a => mul_nonneg ENNReal.toReal_nonneg (h0 a)

open Classical in
/-- **The generalized (7.5) pairing bound**, strong induction form: from pair-index
offset `k` and accumulated prefix `L` (phase multiplier `xArg n k L`), the character
expectation over `m` remaining `Geom(2)` coordinates is dominated by the `pascal`
expectation of the `fCond` product over `⌊m/2⌋` pairs. Two-coordinate peel +
`tsum_geom_pair`; odd leftover coordinate absorbed by `cexpect_norm_le`. -/
theorem cexpect_pairing_gen (n ξ : ℕ) :
    ∀ m k L : ℕ,
      ‖(PMF.iid geomHalf m).cexpect fun a =>
          eC (-(ξ * ((xArg n k L * ∑ j ∈ Finset.range m,
            (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre a (j + 1)).val) : ℚ)
            / 3 ^ n)‖
        ≤ (PMF.iid pascal (m / 2)).expect fun b =>
            ∏ j : Fin (m / 2),
              ‖fCond n ξ (xArg n (k + (j : ℕ)) (L + pre b ((j : ℕ) + 1))) (b j)‖ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro k L
    rcases Nat.lt_or_ge m 2 with hm | hm
    · -- m ∈ {0,1}: the RHS is the empty product 1; triangle inequality on the LHS
      have hdiv : m / 2 = 0 := by omega
      refine le_trans (cexpect_norm_le _ _ (fun a => (eC_norm _).le)) (le_of_eq ?_)
      rw [hdiv, PMF.expect_iid_zero]
      exact (Finset.prod_of_isEmpty _).symm
    · -- m = m' + 2: peel one pair
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      rw [show (m + 2) / 2 = m / 2 + 1 from Nat.add_div_right m (by norm_num)]
      -- ZMod identity: the (1.26) sum splits off the head pair
      have hzmod : ∀ (a₀ a₁ : ℕ) (w : Fin m → ℕ),
          xArg n k L * ∑ j ∈ Finset.range (m + 2), (3 : ZMod (3 ^ n)) ^ j
              * (2 : ZMod (3 ^ n))⁻¹ ^ pre (Fin.cons a₀ (Fin.cons a₁ w)) (j + 1)
            = xArg n k (L + (a₀ + a₁)) * (2 ^ a₁ + 3)
              + xArg n (k + 1) (L + (a₀ + a₁)) * ∑ j ∈ Finset.range m,
                  (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre w (j + 1) := by
        intro a₀ a₁ w
        have hp1 : pre (Fin.cons a₀ (Fin.cons a₁ w) : Fin (m + 2) → ℕ) (0 + 1) = a₀ := by
          rw [pre_cons, pre_zero]
          omega
        have hp2 : pre (Fin.cons a₀ (Fin.cons a₁ w) : Fin (m + 2) → ℕ) (0 + 1 + 1)
            = a₀ + a₁ := by
          rw [pre_cons, pre_cons, pre_zero]
          omega
        have hterm : ∀ j, (3 : ZMod (3 ^ n)) ^ (j + 1 + 1)
              * (2 : ZMod (3 ^ n))⁻¹
                ^ pre (Fin.cons a₀ (Fin.cons a₁ w) : Fin (m + 2) → ℕ) (j + 1 + 1 + 1)
            = (3 ^ 2 * (2 : ZMod (3 ^ n))⁻¹ ^ (a₀ + a₁))
              * ((3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre w (j + 1)) := by
          intro j
          have hp : pre (Fin.cons a₀ (Fin.cons a₁ w) : Fin (m + 2) → ℕ) (j + 1 + 1 + 1)
              = (a₀ + a₁) + pre w (j + 1) := by
            rw [pre_cons, pre_cons]
            ring
          rw [hp, pow_add, pow_add]
          ring
        rw [Finset.sum_range_succ' _ (m + 1), Finset.sum_range_succ' _ m,
          Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, hp1, hp2]
        have hcanc : (2 : ZMod (3 ^ n))⁻¹ ^ (L + (a₀ + a₁)) * 2 ^ a₁
            = (2 : ZMod (3 ^ n))⁻¹ ^ (L + a₀) := by
          rw [show L + (a₀ + a₁) = (L + a₀) + a₁ from by ring]
          exact inv2_cancel n (L + a₀) a₁
        unfold xArg
        linear_combination (-(3 : ZMod (3 ^ n)) ^ (2 * k)) * hcanc
      -- the split at the eC level
      have hsplit : ∀ (a₀ a₁ : ℕ) (w : Fin m → ℕ),
          eC (-(ξ * ((xArg n k L * ∑ j ∈ Finset.range (m + 2), (3 : ZMod (3 ^ n)) ^ j
              * (2 : ZMod (3 ^ n))⁻¹ ^ pre (Fin.cons a₀ (Fin.cons a₁ w)) (j + 1)).val) : ℚ)
              / 3 ^ n)
            = eC (-(ξ * (((xArg n k (L + (a₀ + a₁)) * (2 ^ a₁ + 3)).val : ℕ) : ℚ)) / 3 ^ n)
              * eC (-(ξ * ((xArg n (k + 1) (L + (a₀ + a₁)) * ∑ j ∈ Finset.range m,
                  (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre w (j + 1)).val) : ℚ)
                  / 3 ^ n) := by
        intro a₀ a₁ w
        rw [hzmod a₀ a₁ w]
        exact eC_char_add n ξ _ _
      -- the tail expectation and head factor
      set T : ℕ → ℂ := fun b => (PMF.iid geomHalf m).cexpect fun w =>
        eC (-(ξ * ((xArg n (k + 1) (L + b) * ∑ j ∈ Finset.range m,
          (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre w (j + 1)).val) : ℚ)
          / 3 ^ n) with hT
      have hTle : ∀ b, ‖T b‖ ≤ 1 := fun b =>
        cexpect_norm_le _ _ (fun w => (eC_norm _).le)
      set H : ℕ → ℕ → ℂ := fun b a =>
        eC (-(ξ * (((xArg n k (L + b) * (2 ^ a + 3)).val : ℕ) : ℚ)) / 3 ^ n) with hH
      have hHG : ∀ b a, ‖H b a * T b‖ ≤ 1 := by
        intro b a
        rw [norm_mul, hH]
        calc ‖eC _‖ * ‖T b‖ ≤ 1 * 1 :=
              mul_le_mul (eC_norm _).le (hTle b) (norm_nonneg _) zero_le_one
          _ = 1 := mul_one 1
      -- peel two coordinates and regroup by b
      have hpeel : ((PMF.iid geomHalf (m + 2)).cexpect fun a =>
          eC (-(ξ * ((xArg n k L * ∑ j ∈ Finset.range (m + 2),
            (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre a (j + 1)).val) : ℚ)
            / 3 ^ n))
          = ∑' b : ℕ, ((pascal b).toReal : ℂ)
              * (((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), H b a * T b) := by
        rw [cexpect_iid_succ _ _ _ (fun v => (eC_norm _).le)]
        have hinner : ∀ a₀ : ℕ, ((PMF.iid geomHalf (m + 1)).cexpect fun w =>
            eC (-(ξ * ((xArg n k L * ∑ j ∈ Finset.range (m + 2),
              (3 : ZMod (3 ^ n)) ^ j
                * (2 : ZMod (3 ^ n))⁻¹ ^ pre (Fin.cons a₀ w) (j + 1)).val) : ℚ)
              / 3 ^ n))
            = ∑' a₁ : ℕ, ((geomHalf a₁).toReal : ℂ)
                * (H (a₀ + a₁) a₁ * T (a₀ + a₁)) := by
          intro a₀
          rw [cexpect_iid_succ _ _ _ (fun v => (eC_norm _).le)]
          refine tsum_congr fun a₁ => ?_
          congr 1
          calc ((PMF.iid geomHalf m).cexpect fun w =>
                eC (-(ξ * ((xArg n k L * ∑ j ∈ Finset.range (m + 2),
                  (3 : ZMod (3 ^ n)) ^ j
                    * (2 : ZMod (3 ^ n))⁻¹
                      ^ pre (Fin.cons a₀ (Fin.cons a₁ w)) (j + 1)).val) : ℚ)
                  / 3 ^ n))
              = (PMF.iid geomHalf m).cexpect fun w => H (a₀ + a₁) a₁
                  * eC (-(ξ * ((xArg n (k + 1) (L + (a₀ + a₁)) * ∑ j ∈ Finset.range m,
                      (3 : ZMod (3 ^ n)) ^ j
                        * (2 : ZMod (3 ^ n))⁻¹ ^ pre w (j + 1)).val) : ℚ)
                      / 3 ^ n) := by
                congr 1
                funext w
                rw [hsplit a₀ a₁ w]
            _ = H (a₀ + a₁) a₁ * T (a₀ + a₁) := by
                rw [cexpect_const_mul, hT]
        calc ∑' a₀ : ℕ, ((geomHalf a₀).toReal : ℂ)
              * ((PMF.iid geomHalf (m + 1)).cexpect fun w =>
                eC (-(ξ * ((xArg n k L * ∑ j ∈ Finset.range (m + 2),
                  (3 : ZMod (3 ^ n)) ^ j
                    * (2 : ZMod (3 ^ n))⁻¹ ^ pre (Fin.cons a₀ w) (j + 1)).val) : ℚ)
                  / 3 ^ n))
            = ∑' a₀ : ℕ, ((geomHalf a₀).toReal : ℂ)
                * ∑' a₁ : ℕ, ((geomHalf a₁).toReal : ℂ)
                  * (H (a₀ + a₁) a₁ * T (a₀ + a₁)) := by
              exact tsum_congr fun a₀ => by rw [hinner a₀]
          _ = ∑' b : ℕ, ((pascal b).toReal : ℂ)
                * (((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), H b a * T b) :=
              tsum_geom_pair _ hHG
      rw [hpeel]
      -- the finite sum is fCond times the tail
      have hsum_fCond : ∀ b : ℕ,
          ((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), H b a * T b
            = fCond n ξ (xArg n k (L + b)) b * T b := by
        intro b
        rw [← Finset.sum_mul, fCond, hH]
        ring
      -- the induction hypothesis for the tail
      have hIH : ∀ b, ‖T b‖ ≤ (PMF.iid pascal (m / 2)).expect fun c =>
          ∏ j : Fin (m / 2),
            ‖fCond n ξ (xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1))) (c j)‖ :=
        fun b => IH m (by omega) (k + 1) (L + b)
      have hE0 : ∀ b, (0:ℝ) ≤ (PMF.iid pascal (m / 2)).expect fun c =>
          ∏ j : Fin (m / 2),
            ‖fCond n ξ (xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1))) (c j)‖ :=
        fun b => expect_nonneg _ _ fun c => Finset.prod_nonneg fun j _ => norm_nonneg _
      have hE1 : ∀ b, ((PMF.iid pascal (m / 2)).expect fun c =>
          ∏ j : Fin (m / 2),
            ‖fCond n ξ (xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1))) (c j)‖)
          ≤ 1 :=
        fun b => expect_le_one _ _
          (fun c => Finset.prod_nonneg fun j _ => norm_nonneg _)
          (fun c => Finset.prod_le_one (fun j _ => norm_nonneg _)
            (fun j _ => fCond_norm_le_one _ _ _ _))
      -- summability bookkeeping
      have hΦnorm : ∀ b : ℕ, ‖((pascal b).toReal : ℂ)
            * (((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), H b a * T b)‖
          = (pascal b).toReal * (‖fCond n ξ (xArg n k (L + b)) b‖ * ‖T b‖) := by
        intro b
        rw [hsum_fCond b, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg]
      have hmass : Summable fun b => (pascal b).toReal :=
        ENNReal.summable_toReal pascal.tsum_coe_ne_top
      have hΦbound : ∀ b : ℕ,
          (pascal b).toReal * (‖fCond n ξ (xArg n k (L + b)) b‖ * ‖T b‖)
            ≤ (pascal b).toReal := fun b => by
        calc (pascal b).toReal * (‖fCond n ξ (xArg n k (L + b)) b‖ * ‖T b‖)
            ≤ (pascal b).toReal * (1 * 1) := by
              refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              exact mul_le_mul (fCond_norm_le_one _ _ _ _) (hTle b) (norm_nonneg _)
                zero_le_one
          _ = (pascal b).toReal := by ring
      have hΦS : Summable fun b : ℕ => ‖((pascal b).toReal : ℂ)
          * (((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), H b a * T b)‖ :=
        Summable.of_nonneg_of_le (fun b => norm_nonneg _)
          (fun b => (hΦnorm b).le.trans (hΦbound b)) hmass
      have hRHSb : ∀ b : ℕ, (0:ℝ) ≤ (pascal b).toReal
          * (‖fCond n ξ (xArg n k (L + b)) b‖
            * (PMF.iid pascal (m / 2)).expect fun c =>
              ∏ j : Fin (m / 2),
                ‖fCond n ξ (xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖) :=
        fun b => mul_nonneg ENNReal.toReal_nonneg
          (mul_nonneg (norm_nonneg _) (hE0 b))
      have hRHSS : Summable fun b : ℕ => (pascal b).toReal
          * (‖fCond n ξ (xArg n k (L + b)) b‖
            * (PMF.iid pascal (m / 2)).expect fun c =>
              ∏ j : Fin (m / 2),
                ‖fCond n ξ (xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖) := by
        refine Summable.of_nonneg_of_le hRHSb (fun b => ?_) hmass
        calc (pascal b).toReal * (‖fCond n ξ (xArg n k (L + b)) b‖ * _)
            ≤ (pascal b).toReal * (1 * 1) := by
              refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
              exact mul_le_mul (fCond_norm_le_one _ _ _ _) (hE1 b) (hE0 b) zero_le_one
          _ = (pascal b).toReal := by ring
      -- unfold the target expectation one pascal draw
      have hprodcons : ∀ (b : ℕ) (c : Fin (m / 2) → ℕ),
          (∏ j : Fin (m / 2 + 1),
            ‖fCond n ξ (xArg n (k + (j : ℕ))
                (L + pre (Fin.cons b c : Fin (m / 2 + 1) → ℕ) ((j : ℕ) + 1)))
              ((Fin.cons b c : Fin (m / 2 + 1) → ℕ) j)‖)
            = ‖fCond n ξ (xArg n k (L + b)) b‖
              * ∏ j : Fin (m / 2),
                ‖fCond n ξ (xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖ := by
        intro b c
        rw [Fin.prod_univ_succ]
        simp only [Fin.val_zero, Fin.cons_zero, Fin.val_succ, Fin.cons_succ, pre_cons,
          pre_zero, add_zero]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [show k + ((j : ℕ) + 1) = (k + 1) + (j : ℕ) from by ring,
          show L + (b + pre c ((j : ℕ) + 1)) = (L + b) + pre c ((j : ℕ) + 1) from by ring]
      have htarget : ((PMF.iid pascal (m / 2 + 1)).expect fun b =>
            ∏ j : Fin (m / 2 + 1),
              ‖fCond n ξ (xArg n (k + (j : ℕ)) (L + pre b ((j : ℕ) + 1))) (b j)‖)
          = ∑' b : ℕ, (pascal b).toReal
              * (‖fCond n ξ (xArg n k (L + b)) b‖
                * (PMF.iid pascal (m / 2)).expect fun c =>
                  ∏ j : Fin (m / 2),
                    ‖fCond n ξ (xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                      (c j)‖) := by
        rw [PMF.expect_iid_succ _ _ _
          (fun v => Finset.prod_nonneg fun j _ => norm_nonneg _)
          (fun v => Finset.prod_le_one (fun j _ => norm_nonneg _)
            (fun j _ => fCond_norm_le_one _ _ _ _))]
        refine tsum_congr fun b => ?_
        congr 1
        rw [show (fun c : Fin (m / 2) → ℕ =>
            ∏ j : Fin (m / 2 + 1),
              ‖fCond n ξ (xArg n (k + (j : ℕ))
                  (L + pre (Fin.cons b c : Fin (m / 2 + 1) → ℕ) ((j : ℕ) + 1)))
                ((Fin.cons b c : Fin (m / 2 + 1) → ℕ) j)‖)
          = fun c : Fin (m / 2) → ℕ => ‖fCond n ξ (xArg n k (L + b)) b‖
              * ∏ j : Fin (m / 2),
                ‖fCond n ξ (xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                  (c j)‖ from funext fun c => hprodcons b c, expect_const_mul]
      -- close
      calc ‖∑' b : ℕ, ((pascal b).toReal : ℂ)
            * (((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), H b a * T b)‖
          ≤ ∑' b : ℕ, ‖((pascal b).toReal : ℂ)
              * (((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), H b a * T b)‖ :=
            norm_tsum_le_tsum_norm hΦS
        _ ≤ ∑' b : ℕ, (pascal b).toReal
              * (‖fCond n ξ (xArg n k (L + b)) b‖
                * (PMF.iid pascal (m / 2)).expect fun c =>
                  ∏ j : Fin (m / 2),
                    ‖fCond n ξ (xArg n ((k + 1) + (j : ℕ)) ((L + b) + pre c ((j : ℕ) + 1)))
                      (c j)‖) := by
            refine hΦS.tsum_le_tsum (fun b => ?_) hRHSS
            rw [hΦnorm b]
            refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            exact mul_le_mul_of_nonneg_left (hIH b) (norm_nonneg _)
        _ = _ := htarget.symm

open Classical in
/-- **The (7.4)/(7.5) pairing bound** (paper pp.33–34) — THE X1 crux. Route:
induction on the number of pairs, peeling two `geomHalf` coordinates per step
through `PMF.iid`. The (1.26) sum splits as
`Σ = Σ_{j∈[n/2]} 3^{2j-2}·2^{-b_{[1,j]}}·(2^{a_{2j}}+3) + (odd leftover)`, so `eC`'s
additivity (`eC_char_add`) factors the integrand; the double geometric sum over the
head pair `(a₁,a₂)` reindexes by `b := a₁+a₂` (`geomHalf a₁ · geomHalf a₂ = 2^{-b}`,
`#{pairs} = b-1`, i.e. `pascal b = (b-1)·2^{-b}`, cf. `pascal_eq_map_iid`),
producing one `pascal` draw and the factor `fCond(x_j, b)`; the tail's dependence
on the head is through `b` alone. The odd-`n` leftover factor `g` has `‖g‖ ≤ 1`
(7.6) and is dropped after the triangle inequality. -/
theorem cexpect_pairing (n ξ : ℕ) :
    ‖(PMF.iid geomHalf n).cexpect fun a =>
        eC (-(ξ * ((∑ j ∈ Finset.range n,
          (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre a (j + 1)).val) : ℚ)
          / 3 ^ n)‖
      ≤ (PMF.iid pascal (n / 2)).expect fun b =>
          ∏ j : Fin (n / 2), ‖fCond n ξ (xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖ := by
  have h := cexpect_pairing_gen n ξ n 0 0
  have hx : xArg n 0 0 = 1 := by
    unfold xArg
    norm_num
  simp only [hx, one_mul, zero_add] at h
  exact h

/-! ### Damping: the product is dominated by the white-encounter count -/

open Classical in
/-- The (7.5) product is dominated by Prop 7.3's damping integrand: each factor is
`≤ 1` (7.6), and at a white renewal point (`b_j = 3`, `(j, b_{[1,j]})` white) it is
`≤ exp(-ε³)` by Lemma 7.2 + `white_cos_bound`. -/
theorem prod_fCond_le_damping (n ξ : ℕ) (b : Fin (n / 2) → ℕ) :
    ∏ j : Fin (n / 2), ‖fCond n ξ (xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖
      ≤ Real.exp (-((epsBW : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)) := by
  have hstep : ∏ j : Fin (n / 2), ‖fCond n ξ (xArg n (j : ℕ) (pre b ((j : ℕ) + 1))) (b j)‖
      ≤ ∏ j : Fin (n / 2),
        (if b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))
          then Real.exp (-((epsBW : ℝ) ^ 3)) else 1) := by
    refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
    by_cases h : b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))
    · rw [if_pos h, h.1, fCond_three_norm]
      exact white_cos_bound n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ)) h.2
    · rw [if_neg h]
      exact fCond_norm_le_one n ξ _ _
  refine le_trans hstep (le_of_eq ?_)
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one,
    ← Real.exp_nat_mul]
  congr 1
  ring

/-! ### Assembly: Proposition 7.1 -/

open Classical in
/-- **Proposition 7.1** (= Prop 1.17 restated through the (1.26) reversed form): the
character sum over the raw valuation vector `a ~ Geom(2)ⁿ` decays polynomially,
uniformly in `ξ` coprime to 3. PROVED (moved from `Holding.lean`, 2026-07-12) from
the pairing bound (7.5) + Lemma 7.2 damping + Proposition 7.3
(`renewal_white_encounters`). -/
theorem key_fourier_decay (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ∀ ξ : ZMod (3 ^ n), ¬ (3 ∣ ξ.val) →
      ‖(PMF.iid geomHalf n).cexpect fun a =>
          eC (-(ξ.val * ((∑ j ∈ Finset.range n,
            (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre a (j + 1)).val) : ℚ)
            / 3 ^ n)‖
        ≤ C * (n : ℝ) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := renewal_white_encounters A hA
  refine ⟨C, hC0, fun n hn ξ hξ => ?_⟩
  refine le_trans (cexpect_pairing n ξ.val) (le_trans ?_ (hC n ξ.val hξ hn))
  refine expect_mono_le _ _ _
    (fun b => Finset.prod_nonneg fun j _ => norm_nonneg _)
    (fun b => prod_fCond_le_damping n ξ.val b)
    (fun b => ?_)
  rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
  have hε0 : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  exact mul_nonneg (pow_nonneg hε0 3) (Nat.cast_nonneg _)

end TaoCollatz
