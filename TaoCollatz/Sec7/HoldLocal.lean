import TaoCollatz.Sec7.Unroll
import TaoCollatz.Prob.Mgf

/-!
# Lemma 2.2(i) for `Hold`: assembly of the tilted circle method (node S3, steps F4–F5)

Paper anchors: Tao 2019 Lemma 2.2 pp.14–16 instantiated at the 2-D `Hold` walk
(p.42, mean `(4,16)`); the tilting identity is the Chernoff step of the Lemma 2.2
proof (p.15), the center bound is the finite circle method (D5, no contour
integration).

This module composes the proved engine:
* `tilt_hold_map_mass` — the four nondegeneracy atoms `(1,3), (2,5), (2,7), (2,8)`
  of the TILTED hold walk keep mass `≥ 1/400` after projection mod `N`
  (`tilt_hold_apply_ge` + `PMF.apply_le_map_apply`).
* `tiltHold_apply_le_center` — **(F4b)**: the center-regime local bound for the
  tilted walk, `P_λ(S̃_n = v) ≤ (32·80000)²/(1+n)` uniformly on the tilt box
  `|λᵢ| ≤ 1/50` (`charFn_decay_of_atoms` at `μ = 1/400`, so decay constant
  `c = (2μ²)⁻¹ = 80000`, fed to `iidSum_apply_le_center_of_decay`).

Next (F5): the tilting identity `iidSum_apply_eq_tilt` converts this into
`P(S_n = v) ≤ C/(1+n) · Z(λ)ⁿ e^{-λ·v}`, and the λ-optimization over the box
(second-order bound `Z(λ) ≤ 1 + 4λ₁ + 16λ₂ + K|λ|²`) yields `hold_local_bound`.
-/

open scoped ENNReal

namespace TaoCollatz

/-- The four `hold` nondegeneracy atoms keep mass `≥ 1/400` in the tilted walk
after projection mod `N`: transfer `tilt_hold_apply_ge` through
`PMF.apply_le_map_apply`. -/
theorem tilt_hold_map_mass {l1 l2 : ℝ} (h1lo : -(1 / 50) ≤ l1) (h1hi : l1 ≤ 1 / 50)
    (h2lo : -(1 / 50) ≤ l2) (h2hi : l2 ≤ 1 / 50) {N : ℕ} [NeZero N] (y : ℕ × ℤ)
    (hy1 : (y.1 : ℝ) ≤ 2) (hy2 : (0 : ℝ) ≤ (y.2 : ℝ)) (hy2' : (y.2 : ℝ) ≤ 8)
    (hm : (1 / 32 : ℝ) ≤ (hold y).toReal) :
    (1 / 400 : ℝ)
      ≤ (((tilt hold (expW2 l1 l2) (tiltZ_hold_ne_zero l1 l2)
            (tiltZ_hold_ne_top h1lo h1hi h2lo h2hi)).map (modPair N))
          (modPair N y)).toReal :=
  le_trans (tilt_hold_apply_ge h1lo h1hi h2lo h2hi y hy1 hy2 hy2' hm)
    (ENNReal.toReal_mono (PMF.apply_ne_top _ _) (PMF.apply_le_map_apply _ _ _))

/-- **Center-regime local bound for the TILTED `Hold` walk** ((F4b) of node S3):
uniformly on the tilt box `|λᵢ| ≤ 1/50` and in the target `v`, the `n`-fold tilted
walk has point masses `≤ (32·80000)²/(1+n)`. The decay constant `80000 = (2μ²)⁻¹`
comes from the tilted atom masses `μ = 1/400`. -/
theorem tiltHold_apply_le_center {l1 l2 : ℝ} (h1lo : -(1 / 50) ≤ l1)
    (h1hi : l1 ≤ 1 / 50) (h2lo : -(1 / 50) ≤ l2) (h2hi : l2 ≤ 1 / 50)
    (n : ℕ) (v : ℕ × ℤ) :
    ((iidSum (tilt hold (expW2 l1 l2) (tiltZ_hold_ne_zero l1 l2)
        (tiltZ_hold_ne_top h1lo h1hi h2lo h2hi)) n) v).toReal
      ≤ 6553600000000 / (1 + (n : ℝ)) := by
  set p := tilt hold (expW2 l1 l2) (tiltZ_hold_ne_zero l1 l2)
    (tiltZ_hold_ne_top h1lo h1hi h2lo h2hi) with hp
  have hdec : ∀ (N : ℕ) [NeZero N], 4 ≤ N → ∀ ξ : ZMod N × ZMod N,
      ‖charFn (p.map (modPair N)) ξ‖ ^ 2
        ≤ 1 - (((nd ξ.1 : ℝ) / N) ^ 2 + ((nd ξ.2 : ℝ) / N) ^ 2) / 80000 := by
    intro N _ hN ξ
    have h13 := tilt_hold_map_mass h1lo h1hi h2lo h2hi (N := N) (1, 3)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [hold_apply_one_three]; norm_num)
    have h25 := tilt_hold_map_mass h1lo h1hi h2lo h2hi (N := N) (2, 5)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [hold_apply_two_five]; norm_num)
    have h27 := tilt_hold_map_mass h1lo h1hi h2lo h2hi (N := N) (2, 7)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [hold_apply_two_seven]; norm_num)
    have h28 := tilt_hold_map_mass h1lo h1hi h2lo h2hi (N := N) (2, 8)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [hold_apply_two_eight]; norm_num)
    have h := charFn_decay_of_atoms hN (p.map (modPair N)) (μ := (1 / 400 : ℝ))
      (by norm_num) h13 h25 h27 h28 ξ
    refine le_trans h (le_of_eq ?_)
    ring
  have h := iidSum_apply_le_center_of_decay p (c := 80000) (by norm_num) hdec n v
  refine le_trans h (le_of_eq ?_)
  norm_num

end TaoCollatz
