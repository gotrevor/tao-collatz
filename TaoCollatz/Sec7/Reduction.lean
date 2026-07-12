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

open scoped Real

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
  sorry

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
