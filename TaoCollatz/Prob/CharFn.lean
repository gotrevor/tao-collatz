import TaoCollatz.Prob.LocalBound
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Finite circle method: characteristic functions on `ZMod N × ZMod N` (node S3)

Paper anchor: Tao 2019 Lemma 2.2 proof pp.15–16. Per design decision D5 the paper's
`[-π,π]²` Fourier-inversion integral is replaced by finite Fourier inversion on the
group `ZMod N × ZMod N` (all sums finite, no measure theory): for any PMF `r` on the
pair group and any `x`,
```
r x = N⁻² ∑_ξ  r̂(ξ) e(-ξ·x),      r̂(ξ) = ∑_y r y · e(ξ·y),
```
and iid sums raise `r̂` to powers, so
```
P(S_n = x) ≤ N⁻² ∑_ξ ‖r̂(ξ)‖ⁿ.
```
Combined with `holdSum_le_modPair` (mod-`N` reduction only merges mass) this bounds
the lattice-local mass of the `Hold` walk for EVERY modulus `N`; the remaining
analytic inputs for `hold_local_bound` are the character decay of `hold` and the
Gaussian summation over `ξ` at `N ≈ √n`.

* `pairChar ξ y = e((ξ₁y₁ + ξ₂y₂)/N)` — the product standard character.
* `sum_pairChar` — 2-D orthogonality (`N²` at `0`, else `0`).
* `charFn r ξ` — the characteristic function `r̂(ξ)`.
* `charFn_inversion`, `apply_toReal_le_sum_norm_charFn` — inversion + triangle bound.
* `charFn_iidSum` — `charFn (iidSum r n) = charFn r ^ n`.
* `iidSum_apply_toReal_le` — the composite circle-method bound.
-/

open scoped ENNReal

namespace TaoCollatz

variable {N : ℕ} [NeZero N]

/-- 1-D orthogonality: the geometric sum of the standard character `e(t·/N)`. -/
theorem sum_stdAddChar_mul (t : ZMod N) :
    ∑ i : ZMod N, ZMod.stdAddChar (t * i) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp only [h, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · simp only [← AddChar.mulShift_apply (ψ := ZMod.stdAddChar) (r := t)]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

/-- The product standard character on `ZMod N × ZMod N`: `e((ξ₁y₁ + ξ₂y₂)/N)`. -/
noncomputable def pairChar (ξ y : ZMod N × ZMod N) : ℂ :=
  ZMod.stdAddChar (ξ.1 * y.1 + ξ.2 * y.2)

theorem pairChar_norm (ξ y : ZMod N × ZMod N) : ‖pairChar ξ y‖ = 1 := by
  rw [pairChar, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem pairChar_zero_right (ξ : ZMod N × ZMod N) : pairChar ξ 0 = 1 := by
  rw [pairChar]
  simp

theorem pairChar_add_right (ξ y z : ZMod N × ZMod N) :
    pairChar ξ (y + z) = pairChar ξ y * pairChar ξ z := by
  rw [pairChar, pairChar, pairChar, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- 2-D orthogonality: `∑_ξ e(ξ·z/N) = N²` at `z = 0` and `0` elsewhere. -/
theorem sum_pairChar (z : ZMod N × ZMod N) :
    ∑ ξ : ZMod N × ZMod N, pairChar ξ z = if z = 0 then ((N : ℂ) ^ 2) else 0 := by
  have hsplit : ∑ ξ : ZMod N × ZMod N, pairChar ξ z
      = (∑ t : ZMod N, ZMod.stdAddChar (z.1 * t))
        * (∑ t : ZMod N, ZMod.stdAddChar (z.2 * t)) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ξ₁ _ => Finset.sum_congr rfl fun ξ₂ _ => ?_
    rw [pairChar, AddChar.map_add_eq_mul, mul_comm ξ₁ z.1, mul_comm ξ₂ z.2]
  rw [hsplit, sum_stdAddChar_mul, sum_stdAddChar_mul]
  rcases eq_or_ne z 0 with rfl | hz
  · simp [sq]
  · rw [if_neg hz]
    have : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (Prod.ext h.1 h.2)
    rcases this with h1 | h2
    · rw [if_neg h1, zero_mul]
    · rw [if_neg h2, mul_zero]

/-- The characteristic function `r̂(ξ)` of a PMF on the pair group (finite sum). -/
noncomputable def charFn (r : PMF (ZMod N × ZMod N)) (ξ : ZMod N × ZMod N) : ℂ :=
  ∑ y, ((r y).toReal : ℂ) * pairChar ξ y

/-- Bind mass on a finite type, in real form. -/
theorem toReal_bind_apply {α β : Type*} [Fintype α] (p : PMF α) (f : α → PMF β)
    (y : β) : ((p.bind f) y).toReal = ∑ a, (p a).toReal * ((f a) y).toReal := by
  rw [PMF.bind_apply, tsum_eq_sum (s := Finset.univ) (fun a ha => absurd (Finset.mem_univ a) ha),
    ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (p.apply_ne_top a) ((f a).apply_ne_top y))]
  exact Finset.sum_congr rfl fun a _ => ENNReal.toReal_mul

/-- Pushforward change of variables for finite complex-weighted sums. -/
theorem sum_map_mul_complex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (q : PMF α) (φ : α → β) (g : β → ℂ) :
    ∑ y, (((q.map φ) y).toReal : ℂ) * g y = ∑ z, ((q z).toReal : ℂ) * g (φ z) := by
  classical
  have h1 : ∀ y, (((q.map φ) y).toReal : ℂ)
      = ∑ z, if y = φ z then ((q z).toReal : ℂ) else 0 := by
    intro y
    rw [PMF.map_apply, tsum_eq_sum (s := Finset.univ) (fun a ha => absurd (Finset.mem_univ a) ha),
      ENNReal.toReal_sum (fun a _ => by
        split_ifs with h
        · exact q.apply_ne_top a
        · exact ENNReal.zero_ne_top)]
    push_cast
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> simp
  calc ∑ y, (((q.map φ) y).toReal : ℂ) * g y
      = ∑ y, ∑ z, (if y = φ z then ((q z).toReal : ℂ) else 0) * g y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [h1, Finset.sum_mul]
    _ = ∑ z, ∑ y, (if y = φ z then ((q z).toReal : ℂ) else 0) * g y :=
        Finset.sum_comm
    _ = ∑ z, ((q z).toReal : ℂ) * g (φ z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_eq_single (φ z)
          (fun y _ hy => by rw [if_neg hy, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h)]
        rw [if_pos rfl]

/-- Fourier inversion for PMFs on the pair group (paper pp.15–16, finite form). -/
theorem charFn_inversion (r : PMF (ZMod N × ZMod N)) (x : ZMod N × ZMod N) :
    ((r x).toReal : ℂ)
      = ((N : ℂ) ^ 2)⁻¹ * ∑ ξ, charFn r ξ * pairChar ξ (-x) := by
  have hkey : ∑ ξ, charFn r ξ * pairChar ξ (-x)
      = ((r x).toReal : ℂ) * (N : ℂ) ^ 2 := by
    calc ∑ ξ, charFn r ξ * pairChar ξ (-x)
        = ∑ ξ, ∑ y, ((r y).toReal : ℂ) * pairChar ξ (y + -x) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [charFn, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [pairChar_add_right, mul_assoc]
      _ = ∑ y, ((r y).toReal : ℂ) * ∑ ξ, pairChar ξ (y + -x) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ y, ((r y).toReal : ℂ) * (if y + -x = 0 then ((N : ℂ) ^ 2) else 0) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [sum_pairChar]
      _ = ((r x).toReal : ℂ) * (N : ℂ) ^ 2 := by
          rw [Finset.sum_eq_single x
            (fun y _ hy => by
              rw [if_neg (fun h => hy (by rwa [add_neg_eq_zero] at h)), mul_zero])
            (fun h => absurd (Finset.mem_univ _) h)]
          rw [if_pos (by rw [add_neg_cancel])]
  have hN : ((N : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne N))
  rw [hkey, mul_comm (((N : ℂ) ^ 2)⁻¹), mul_assoc, mul_inv_cancel₀ hN, mul_one]

/-- Triangle-inequality form of the inversion: the point mass is at most the
normalized `ℓ¹` mass of the characteristic function. -/
theorem apply_toReal_le_sum_norm_charFn (r : PMF (ZMod N × ZMod N))
    (x : ZMod N × ZMod N) :
    (r x).toReal ≤ ((N : ℝ) ^ 2)⁻¹ * ∑ ξ, ‖charFn r ξ‖ := by
  have h0 : (r x).toReal = ‖((r x).toReal : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [h0, charFn_inversion r x]
  calc ‖((N : ℂ) ^ 2)⁻¹ * ∑ ξ, charFn r ξ * pairChar ξ (-x)‖
      = ((N : ℝ) ^ 2)⁻¹ * ‖∑ ξ, charFn r ξ * pairChar ξ (-x)‖ := by
        rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    _ ≤ ((N : ℝ) ^ 2)⁻¹ * ∑ ξ, ‖charFn r ξ‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ξ _ => ?_)
        rw [norm_mul, pairChar_norm, mul_one]

theorem charFn_pure_zero (ξ : ZMod N × ZMod N) :
    charFn (PMF.pure 0) ξ = 1 := by
  rw [charFn, Finset.sum_eq_single (0 : ZMod N × ZMod N)
    (fun y _ hy => by
      rw [show ((PMF.pure (0 : ZMod N × ZMod N)) y) = 0 from by
        rw [PMF.pure_apply, if_neg hy], ENNReal.toReal_zero, Complex.ofReal_zero,
        zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [PMF.pure_apply, if_pos rfl, ENNReal.toReal_one, Complex.ofReal_one, one_mul,
    pairChar_zero_right]

/-- `charFn` of a translated PMF picks up the character of the shift. -/
theorem charFn_map_add (q : PMF (ZMod N × ZMod N)) (a ξ : ZMod N × ZMod N) :
    charFn (q.map (a + ·)) ξ = pairChar ξ a * charFn q ξ := by
  rw [charFn, sum_map_mul_complex q (a + ·) (pairChar ξ), charFn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [pairChar_add_right]
  ring

/-- `charFn` of a bind averages the component characteristic functions. -/
theorem charFn_bind (p : PMF (ZMod N × ZMod N)) (f : ZMod N × ZMod N → PMF (ZMod N × ZMod N))
    (ξ : ZMod N × ZMod N) :
    charFn (p.bind f) ξ = ∑ a, ((p a).toReal : ℂ) * charFn (f a) ξ := by
  rw [charFn]
  calc ∑ y, (((p.bind f) y).toReal : ℂ) * pairChar ξ y
      = ∑ y, ∑ a, ((p a).toReal : ℂ) * (((f a) y).toReal : ℂ) * pairChar ξ y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [toReal_bind_apply]
        push_cast
        rw [Finset.sum_mul]
    _ = ∑ a, ∑ y, ((p a).toReal : ℂ) * (((f a) y).toReal : ℂ) * pairChar ξ y :=
        Finset.sum_comm
    _ = ∑ a, ((p a).toReal : ℂ) * charFn (f a) ξ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [charFn, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring

/-- **Characteristic functions of iid sums are powers** (the circle-method engine). -/
theorem charFn_iidSum (r : PMF (ZMod N × ZMod N)) (n : ℕ) (ξ : ZMod N × ZMod N) :
    charFn (iidSum r n) ξ = (charFn r ξ) ^ n := by
  induction n with
  | zero => rw [iidSum_zero, pow_zero, charFn_pure_zero]
  | succ n IH =>
    rw [iidSum_succ, charFn_bind, pow_succ]
    calc ∑ a, ((r a).toReal : ℂ) * charFn ((iidSum r n).map (a + ·)) ξ
        = ∑ a, ((r a).toReal : ℂ) * pairChar ξ a * (charFn r ξ) ^ n := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [charFn_map_add, IH]
          ring
      _ = (∑ a, ((r a).toReal : ℂ) * pairChar ξ a) * (charFn r ξ) ^ n := by
          rw [Finset.sum_mul]
      _ = (charFn r ξ) ^ n * charFn r ξ := by
          rw [← charFn]
          ring

/-- **The composite circle-method bound**: for any PMF on `ZMod N × ZMod N`, the
`n`-fold iid sum has point masses `≤ N⁻² ∑_ξ ‖r̂(ξ)‖ⁿ`. -/
theorem iidSum_apply_toReal_le (r : PMF (ZMod N × ZMod N)) (n : ℕ)
    (x : ZMod N × ZMod N) :
    ((iidSum r n) x).toReal ≤ ((N : ℝ) ^ 2)⁻¹ * ∑ ξ, ‖charFn r ξ‖ ^ n := by
  refine le_trans (apply_toReal_le_sum_norm_charFn (iidSum r n) x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_of_eq (Finset.sum_congr rfl fun ξ _ => ?_)
  rw [charFn_iidSum, norm_pow]

/-- Conjugating the product character negates its argument. -/
theorem pairChar_conj (ξ y : ZMod N × ZMod N) :
    (starRingEnd ℂ) (pairChar ξ y) = pairChar ξ (-y) := by
  have hneg : pairChar ξ (-y) = (pairChar ξ y)⁻¹ := by
    rw [pairChar, pairChar, show ξ.1 * (-y).1 + ξ.2 * (-y).2
        = -(ξ.1 * y.1 + ξ.2 * y.2) from by
      simp only [Prod.fst_neg, Prod.snd_neg]
      ring, AddChar.map_neg_eq_inv]
  rw [hneg, Complex.inv_eq_conj (pairChar_norm ξ y)]

/-- Character product with a conjugate is the character of the difference. -/
theorem pairChar_mul_conj (ξ y y' : ZMod N × ZMod N) :
    pairChar ξ y * (starRingEnd ℂ) (pairChar ξ y') = pairChar ξ (y - y') := by
  rw [pairChar_conj, ← pairChar_add_right, sub_eq_add_neg]

/-- PMF masses on a finite type sum to one (real form). -/
theorem sum_toReal_eq_one {α : Type*} [Fintype α] (r : PMF α) :
    ∑ y, (r y).toReal = 1 := by
  have h := r.tsum_coe
  rw [tsum_eq_sum (s := Finset.univ) (fun a ha => absurd (Finset.mem_univ a) ha)] at h
  rw [← ENNReal.toReal_sum (fun a _ => r.apply_ne_top a), h, ENNReal.toReal_one]

/-- **The two-atom anti-concentration bound** (heart of the paper's `|M(it)| < 1`
nondegeneracy step, p.16): any two distinct atoms of `r` whose relative character is
bounded away from `1` pull `‖r̂(ξ)‖` off the unit circle, quantitatively. -/
theorem charFn_normSq_pair_bound (r : PMF (ZMod N × ZMod N))
    (ξ y₀ y₁ : ZMod N × ZMod N) (h01 : y₀ ≠ y₁) :
    2 * (r y₀).toReal * (r y₁).toReal * (1 - (pairChar ξ (y₀ - y₁)).re)
      ≤ 1 - ‖charFn r ξ‖ ^ 2 := by
  classical
  set m : ZMod N × ZMod N → ℝ := fun y => (r y).toReal with hm
  set F : ZMod N × ZMod N → ZMod N × ZMod N → ℝ :=
    fun y y' => m y * m y' * (1 - (pairChar ξ (y - y')).re) with hF
  -- expansion of the squared norm as a double character sum
  have hexp : ‖charFn r ξ‖ ^ 2
      = ∑ y, ∑ y', m y * m y' * (pairChar ξ (y - y')).re := by
    have h0 : ‖charFn r ξ‖ ^ 2 = (charFn r ξ * (starRingEnd ℂ) (charFn r ξ)).re := by
      rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [h0, charFn, map_sum, Finset.sum_mul_sum]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    have hterm : ((m y : ℂ) * pairChar ξ y) * ((m y' : ℂ) * (starRingEnd ℂ) (pairChar ξ y'))
        = ((m y * m y' : ℝ) : ℂ) * pairChar ξ (y - y') := by
      rw [← pairChar_mul_conj]
      push_cast
      ring
    rw [hterm, Complex.re_ofReal_mul, mul_assoc]
  -- the double sum of the complementary weights
  have hone : (1 : ℝ) = ∑ y, ∑ y', m y * m y' := by
    calc (1 : ℝ) = (∑ y, m y) * (∑ y', m y') := by
          rw [sum_toReal_eq_one, one_mul]
      _ = ∑ y, ∑ y', m y * m y' := Finset.sum_mul_sum _ _ _ _
  have hsub : 1 - ‖charFn r ξ‖ ^ 2 = ∑ y, ∑ y', F y y' := by
    rw [hexp]
    calc (1 : ℝ) - ∑ y, ∑ y', m y * m y' * (pairChar ξ (y - y')).re
        = (∑ y, ∑ y', m y * m y') - ∑ y, ∑ y', m y * m y' * (pairChar ξ (y - y')).re := by
          rw [← hone]
      _ = ∑ y, ((∑ y', m y * m y') - ∑ y', m y * m y' * (pairChar ξ (y - y')).re) := by
          rw [Finset.sum_sub_distrib]
      _ = ∑ y, ∑ y', F y y' := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [hF]
          ring
  -- every term of the double sum is nonnegative
  have hterm_nonneg : ∀ y y', 0 ≤ F y y' := by
    intro y y'
    refine mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ?_
    rw [sub_nonneg]
    calc (pairChar ξ (y - y')).re ≤ |(pairChar ξ (y - y')).re| := le_abs_self _
      _ ≤ ‖pairChar ξ (y - y')‖ := Complex.abs_re_le_norm _
      _ = 1 := pairChar_norm _ _
  -- single out the (y₀,y₁) and (y₁,y₀) terms
  have hsym : F y₁ y₀ = F y₀ y₁ := by
    simp only [hF]
    have hre : (pairChar ξ (y₁ - y₀)).re = (pairChar ξ (y₀ - y₁)).re := by
      rw [show y₁ - y₀ = -(y₀ - y₁) from by ring, ← pairChar_conj, Complex.conj_re]
    rw [hre]
    ring
  have hrow : ∀ y, 0 ≤ ∑ y', F y y' :=
    fun y => Finset.sum_nonneg fun y' _ => hterm_nonneg y y'
  have h1 : F y₀ y₁ ≤ ∑ y', F y₀ y' :=
    Finset.single_le_sum (fun y' _ => hterm_nonneg y₀ y') (Finset.mem_univ y₁)
  have h2 : F y₁ y₀ ≤ ∑ y', F y₁ y' :=
    Finset.single_le_sum (fun y' _ => hterm_nonneg y₁ y') (Finset.mem_univ y₀)
  have h3 : (∑ y', F y₀ y') + (∑ y', F y₁ y') ≤ ∑ y, ∑ y', F y y' := by
    have hp := Finset.sum_pair (f := fun y => ∑ y', F y y') h01
    rw [← hp]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => hrow y)
  have hfinal : F y₀ y₁ + F y₁ y₀ ≤ ∑ y, ∑ y', F y y' := by
    calc F y₀ y₁ + F y₁ y₀ ≤ (∑ y', F y₀ y') + (∑ y', F y₁ y') := add_le_add h1 h2
      _ ≤ _ := h3
  rw [hsub]
  calc 2 * m y₀ * m y₁ * (1 - (pairChar ξ (y₀ - y₁)).re)
      = F y₀ y₁ + F y₁ y₀ := by rw [hsym, hF]; ring
    _ ≤ ∑ y, ∑ y', F y y' := hfinal

/-- **Jordan-type lower bound for the character defect**: `1 - Re e(j/N)` is at
least `8·dist(j/N, ℤ)²` (where `dist(j/N, ℤ) = min(val, N - val)/N`). -/
theorem one_sub_re_stdAddChar_ge (j : ZMod N) :
    8 * ((min (j.val : ℝ) ((N : ℝ) - j.val)) / N) ^ 2
      ≤ 1 - (ZMod.stdAddChar j).re := by
  have hN : (0 : ℝ) < N := by
    have := NeZero.ne N
    positivity
  set v : ℝ := (j.val : ℝ) with hv
  have hv0 : 0 ≤ v := Nat.cast_nonneg _
  have hvN : v < N := by
    rw [hv]
    have := ZMod.val_lt j
    exact_mod_cast this
  -- the real part is a cosine
  have hre : (ZMod.stdAddChar j).re = Real.cos (2 * Real.pi * v / N) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    have harg : 2 * Real.pi * Complex.I * (j.val : ℂ) / N
        = ((2 * Real.pi * v / N : ℝ) : ℂ) * Complex.I := by
      rw [hv]
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I_re]
  rw [hre]
  set t : ℝ := v / N with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hN]
    exact hvN
  have hmin : min v (N - v) / N = min t (1 - t) := by
    rw [ht, ← min_div_div_right hN.le, sub_div, div_self hN.ne']
  rw [hmin]
  -- 1 - cos(2πt) = 2 sin²(πt)
  have hangle : 2 * Real.pi * v / N = 2 * (Real.pi * t) := by
    rw [ht]
    ring
  rw [hangle]
  have hcos : Real.cos (2 * (Real.pi * t)) = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
    have h1 := Real.cos_two_mul (Real.pi * t)
    have h2 := Real.sin_sq_add_cos_sq (Real.pi * t)
    nlinarith
  rw [hcos]
  -- Jordan: sin(πt) ≥ 2·min(t, 1-t) on [0,1]
  have hsin : 2 * min t (1 - t) ≤ Real.sin (Real.pi * t) := by
    rcases le_or_gt t 2⁻¹ with hhalf | hhalf
    · rw [min_eq_left (by linarith)]
      have h := Real.mul_le_sin (x := Real.pi * t)
        (by positivity) (by nlinarith [Real.pi_pos])
      calc 2 * t = 2 / Real.pi * (Real.pi * t) := by
            field_simp
        _ ≤ Real.sin (Real.pi * t) := h
    · rw [min_eq_right (by linarith)]
      have hs : Real.sin (Real.pi * t) = Real.sin (Real.pi * (1 - t)) := by
        rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t from by ring,
          Real.sin_pi_sub]
      rw [hs]
      have h := Real.mul_le_sin (x := Real.pi * (1 - t))
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      calc 2 * (1 - t) = 2 / Real.pi * (Real.pi * (1 - t)) := by
            field_simp
        _ ≤ Real.sin (Real.pi * (1 - t)) := h
  have hmin0 : 0 ≤ min t (1 - t) := le_min ht0 (by linarith)
  nlinarith [hsin, hmin0, sq_nonneg (Real.sin (Real.pi * t) - 2 * min t (1 - t))]

end TaoCollatz
