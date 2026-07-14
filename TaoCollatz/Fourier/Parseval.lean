import Mathlib.Analysis.Fourier.ZMod

/-!
# Parseval / Plancherel for the discrete Fourier transform on `ZMod N` (node S4)

Paper anchor: Tao 2019 §6, the Plancherel step feeding Prop 1.14 (fine-scale mixing).

Mathlib provides `ZMod.dft` (the DFT, `𝓕`) with inversion `ZMod.dft_dft`, but not the
`L²` Parseval identity. We derive it from additive-character orthogonality
(`∑ₖ stdAddChar (t·k) = if t = 0 then N else 0`):

* `ZMod.dft_parseval_complex` — `∑ₖ 𝓕Φ(k)·conj(𝓕Φ(k)) = N · ∑ⱼ Φ(j)·conj(Φ(j))`.
* `ZMod.dft_parseval` — the real form `∑ₖ ‖𝓕Φ(k)‖² = N · ∑ⱼ ‖Φ(j)‖²`.

Both are the exact shape §6's Cauchy–Schwarz + Plancherel bridge (C10) consumes.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace ZMod
variable {N : ℕ} [NeZero N]

/-- **Plancherel (complex form)** for `ZMod.dft`: the Hermitian pairing is preserved up
to the factor `N`. -/
theorem dft_parseval_complex (Φ : ZMod N → ℂ) :
    ∑ k, dft Φ k * conj (dft Φ k) = (N : ℂ) * ∑ j, Φ j * conj (Φ j) := by
  have hortho : ∀ t : ZMod N, ∑ k : ZMod N, stdAddChar (t * k) = if t = 0 then (N : ℂ) else 0 := by
    intro t
    split_ifs with h
    · simp [h]
    · exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)
  simp only [dft_apply, smul_eq_mul]
  have hconj : ∀ k : ZMod N, conj (∑ l, stdAddChar (-(l * k)) * Φ l)
      = ∑ l, stdAddChar (l * k) * conj (Φ l) := by
    intro k
    rw [map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_mul, ← AddChar.map_neg_eq_conj, neg_neg]
  simp_rw [hconj]
  have step : ∀ k : ZMod N,
      (∑ j, stdAddChar (-(j * k)) * Φ j) * (∑ l, stdAddChar (l * k) * conj (Φ l))
        = ∑ j, ∑ l, (Φ j * conj (Φ l)) * stdAddChar ((l - j) * k) := by
    intro k
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show stdAddChar (-(j * k)) * Φ j * (stdAddChar (l * k) * conj (Φ l))
        = (Φ j * conj (Φ l)) * (stdAddChar (-(j * k)) * stdAddChar (l * k)) from by ring,
      ← AddChar.map_add_eq_mul, show -(j * k) + l * k = (l - j) * k from by ring]
  simp_rw [step]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single j]
  · simp_rw [sub_self, zero_mul, AddChar.map_zero_eq_one, mul_one]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_comm]
  · intro l _ hl
    rw [← Finset.mul_sum, hortho (l - j), if_neg (fun h => hl (sub_eq_zero.mp h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Parseval (real / `L²` form)** for `ZMod.dft`: `∑ₖ ‖𝓕Φ(k)‖² = N · ∑ⱼ ‖Φ(j)‖²`. -/
theorem dft_parseval (Φ : ZMod N → ℂ) :
    ∑ k, ‖dft Φ k‖ ^ 2 = (N : ℝ) * ∑ j, ‖Φ j‖ ^ 2 := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj]; norm_cast; exact Complex.sq_norm z
  have hcast : ((∑ k, ‖dft Φ k‖ ^ 2 : ℝ) : ℂ) = ((N : ℝ) * ∑ j, ‖Φ j‖ ^ 2 : ℝ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast,
      Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hz (dft Φ k)),
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hz (Φ j))]
    exact dft_parseval_complex Φ
  exact_mod_cast hcast

end ZMod
