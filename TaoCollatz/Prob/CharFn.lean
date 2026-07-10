import TaoCollatz.Prob.LocalBound
import Mathlib.Analysis.Fourier.ZMod

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

end TaoCollatz
