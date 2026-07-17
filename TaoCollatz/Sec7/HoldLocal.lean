import TaoCollatz.Sec7.Unroll
import TaoCollatz.Prob.Mgf
import TaoCollatz.Prob.LocalInstances

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
            (tiltZ_hold_ne_top h1hi h2lo h2hi)).map (modPair N))
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
        (tiltZ_hold_ne_top h1hi h2lo h2hi)) n) v).toReal
      ≤ 6553600000000 / (1 + (n : ℝ)) := by
  set p := tilt hold (expW2 l1 l2) (tiltZ_hold_ne_zero l1 l2)
    (tiltZ_hold_ne_top h1hi h2lo h2hi) with hp
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

/-! ### (F5): assembly of Lemma 2.2(i) for `Hold` -/

/-- **The Chernoff bridge** ((F5) step 1 of node S3): for any tilt `λ` in the
`1/200`-box, `P(Hold_{[1,n]} = (j,l)) ≤ C₀/(1+n) · e^{n(4λ₁+16λ₂+1000|λ|²) − λ·(j,l)}`.
Composition of the tilting identity `iidSum_apply_eq_tilt` (paper p.15 Chernoff
step), the tilted center bound `tiltHold_apply_le_center`, the quadratic MGF
bound `tiltZ_hold_le_quad`, and `1 + u ≤ e^u`. -/
theorem holdSum_apply_le_chernoff {l1 l2 : ℝ}
    (h1lo : -(1 / 200) ≤ l1) (h1hi : l1 ≤ 1 / 200)
    (h2lo : -(1 / 200) ≤ l2) (h2hi : l2 ≤ 1 / 200) (n : ℕ) (j : ℕ) (l : ℤ) :
    ((holdSum n) (j, l)).toReal
      ≤ 6553600000000 / (1 + (n : ℝ))
        * Real.exp ((n : ℝ) * (4 * l1 + 16 * l2 + 1000 * (l1 ^ 2 + l2 ^ 2))
            - (l1 * j + l2 * l)) := by
  have h1lo' : -(1 / 50) ≤ l1 := by linarith
  have h1hi' : l1 ≤ 1 / 50 := by linarith
  have h2lo' : -(1 / 50) ≤ l2 := by linarith
  have h2hi' : l2 ≤ 1 / 50 := by linarith
  have hZ0 := tiltZ_hold_ne_zero l1 l2
  have hZt := tiltZ_hold_ne_top h1hi' h2lo' h2hi'
  set u : ℝ := 4 * l1 + 16 * l2 + 1000 * (l1 ^ 2 + l2 ^ 2) with hu
  set θ : ℝ := l1 * j + l2 * l with hθ
  have hwv0 : expW2 l1 l2 (j, l) ≠ 0 := by
    simp only [expW2]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hwvt : expW2 l1 l2 (j, l) ≠ ∞ := by
    simp only [expW2]
    exact ENNReal.ofReal_ne_top
  have key := iidSum_apply_eq_tilt hold (expW2_zero l1 l2) (expW2_add l1 l2)
    hZ0 hZt n (j, l) hwv0 hwvt
  -- the Z-power bound: `Zⁿ ≤ e^{nu}`
  have hZle : tiltZ hold (expW2 l1 l2) ≤ ENNReal.ofReal (Real.exp u) :=
    le_trans (tiltZ_hold_le_quad h1lo h1hi h2lo h2hi)
      (ENNReal.ofReal_le_ofReal (by
        have h := Real.add_one_le_exp u
        rw [hu] at h ⊢
        linarith))
  have hBpow : tiltZ hold (expW2 l1 l2) ^ n
      ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by
    calc tiltZ hold (expW2 l1 l2) ^ n
        ≤ ENNReal.ofReal (Real.exp u) ^ n := by gcongr
      _ = ENNReal.ofReal (Real.exp u ^ n) :=
          (ENNReal.ofReal_pow (Real.exp_pos _).le n).symm
      _ = ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by rw [← Real.exp_nat_mul]
  have hB : ((tiltZ hold (expW2 l1 l2)) ^ n).toReal ≤ Real.exp ((n : ℝ) * u) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBpow
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
  -- the weight-inverse factor is exactly `e^{-θ}`
  have hCeq : ((expW2 l1 l2 (j, l))⁻¹).toReal = Real.exp (-θ) := by
    simp only [expW2]
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, hθ]
  have hA := tiltHold_apply_le_center h1lo' h1hi' h2lo' h2hi' n (j, l)
  rw [holdSum_eq_iidSum, key, ENNReal.toReal_mul, ENNReal.toReal_mul, hCeq]
  calc ((iidSum (tilt hold (expW2 l1 l2) hZ0 hZt) n) (j, l)).toReal
        * ((tiltZ hold (expW2 l1 l2)) ^ n).toReal * Real.exp (-θ)
      ≤ (6553600000000 / (1 + (n : ℝ)) * Real.exp ((n : ℝ) * u)) * Real.exp (-θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact mul_le_mul hA hB ENNReal.toReal_nonneg (by positivity)
    _ = 6553600000000 / (1 + (n : ℝ)) * Real.exp ((n : ℝ) * u - θ) := by
        rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]

noncomputable def c_holdLocal : ℝ := 1 / 400

noncomputable def C_holdLocal : ℝ := 6553600000000

theorem c_holdLocal_pos : 0 < c_holdLocal := by unfold c_holdLocal; norm_num

theorem C_holdLocal_pos : 0 < C_holdLocal := by unfold C_holdLocal; norm_num

/-- Sibling of `hold_local_bound` with the witnesses pinned to the symbolic
`c_holdLocal = 1/400`, `C_holdLocal = (32·80000)²` (big-C campaign, step 2);
the original `∃`-form delegates. -/
theorem hold_local_bound_explicitC :
    ∀ (n : ℕ) (j : ℕ) (l : ℤ),
      ((holdSum n) (j, l)).toReal
        ≤ C_holdLocal / (1 + n)
          * Gweight (1 + n)
              (c_holdLocal * ‖(((j : ℝ) - 4 * n, (l : ℝ) - 16 * n) : ℝ × ℝ)‖) := by
  unfold c_holdLocal C_holdLocal
  intro n j l
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: `holdSum 0` is the point mass at the origin
    rw [holdSum_eq_iidSum, iidSum_zero, PMF.pure_apply]
    split_ifs with h
    · have hj : j = 0 := congrArg Prod.fst h
      have hl : l = 0 := congrArg Prod.snd h
      subst hj
      subst hl
      rw [ENNReal.toReal_one]
      norm_num [Gweight, Prod.norm_def, Real.norm_eq_abs, Real.exp_zero]
    · rw [ENNReal.toReal_zero]
      exact mul_nonneg (by positivity) (Gweight_nonneg _ _)
  · -- n ≥ 1: Chernoff with the clipped tilt in each coordinate
    have hn1 : 1 ≤ n := hn
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := by linarith
    set d1 : ℝ := (j : ℝ) - 4 * n with hd1
    set d2 : ℝ := (l : ℝ) - 16 * n with hd2
    obtain ⟨l1, h1lo, h1hi, hE1⟩ := chernoff_clip_le hn1 d1
    obtain ⟨l2, h2lo, h2hi, hE2⟩ := chernoff_clip_le hn1 d2
    have hch := holdSum_apply_le_chernoff h1lo h1hi h2lo h2hi n j l
    -- exponent identity: recentre around the mean `(4n, 16n)`
    have hEeq : (n : ℝ) * (4 * l1 + 16 * l2 + 1000 * (l1 ^ 2 + l2 ^ 2))
          - (l1 * j + l2 * l)
        = (1000 * n * l1 ^ 2 - l1 * d1) + (1000 * n * l2 ^ 2 - l2 * d2) := by
      rw [hd1, hd2]
      ring
    rw [hEeq] at hch
    -- the sup norm is the max coordinate deviation
    set M : ℝ := max |d1| |d2| with hM
    have hnorm : ‖((d1, d2) : ℝ × ℝ)‖ = M := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have hM0 : 0 ≤ M := le_trans (abs_nonneg d1) (le_max_left _ _)
    have hmin_nonneg : ∀ x : ℝ, 0 ≤ min (x ^ 2 / (4000 * n)) (|x| / 400) := fun x =>
      le_min (by positivity) (by positivity)
    -- both per-coordinate exponents are ≤ 0; the max coordinate dominates
    have hEle : (1000 * n * l1 ^ 2 - l1 * d1) + (1000 * n * l2 ^ 2 - l2 * d2)
        ≤ -min (M ^ 2 / (4000 * n)) (M / 400) := by
      rcases max_cases |d1| |d2| with ⟨hMe, _⟩ | ⟨hMe, _⟩
      · have h2np : 1000 * n * l2 ^ 2 - l2 * d2 ≤ 0 :=
          le_trans hE2 (neg_nonpos.mpr (hmin_nonneg d2))
        have hsq : M ^ 2 = d1 ^ 2 := by rw [hM, hMe, sq_abs]
        have habs : M = |d1| := by rw [hM, hMe]
        calc (1000 * n * l1 ^ 2 - l1 * d1) + (1000 * n * l2 ^ 2 - l2 * d2)
            ≤ -min (d1 ^ 2 / (4000 * n)) (|d1| / 400) + 0 := add_le_add hE1 h2np
          _ = -min (M ^ 2 / (4000 * n)) (M / 400) := by
              rw [add_zero, hsq, habs]
      · have h1np : 1000 * n * l1 ^ 2 - l1 * d1 ≤ 0 :=
          le_trans hE1 (neg_nonpos.mpr (hmin_nonneg d1))
        have hsq : M ^ 2 = d2 ^ 2 := by rw [hM, hMe, sq_abs]
        have habs : M = |d2| := by rw [hM, hMe]
        calc (1000 * n * l1 ^ 2 - l1 * d1) + (1000 * n * l2 ^ 2 - l2 * d2)
            ≤ 0 + -min (d2 ^ 2 / (4000 * n)) (|d2| / 400) := add_le_add h1np hE2
          _ = -min (M ^ 2 / (4000 * n)) (M / 400) := by
              rw [zero_add, hsq, habs]
    -- match the optimized exponent to the two `Gweight` branches
    have hGw : Real.exp ((1000 * n * l1 ^ 2 - l1 * d1) + (1000 * n * l2 ^ 2 - l2 * d2))
        ≤ Gweight (1 + n) (1 / 400 * M) := by
      refine le_trans (Real.exp_le_exp.mpr hEle) ?_
      rcases min_cases (M ^ 2 / (4000 * (n : ℝ))) (M / 400) with ⟨hm, _⟩ | ⟨hm, _⟩
      · -- Gaussian branch: M²/(4000n) ≥ (M/400)²/(1+n)
        rw [hm]
        have hbr : Real.exp (-(M ^ 2 / (4000 * n)))
            ≤ Real.exp (-((1 / 400 * M) ^ 2) / (1 + (n : ℝ))) := by
          apply Real.exp_le_exp.mpr
          rw [neg_div, neg_le_neg_iff,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg M, mul_nonneg (sq_nonneg M) hnpos.le]
        exact le_trans hbr (le_add_of_nonneg_right (Real.exp_pos _).le)
      · -- exponential branch: exactly the second `Gweight` term
        rw [hm]
        have hbr : -(M / 400) = -|1 / 400 * M| := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 400 * M)]
          ring
        rw [hbr]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    -- assemble
    calc ((holdSum n) (j, l)).toReal
        ≤ 6553600000000 / (1 + (n : ℝ))
          * Real.exp ((1000 * n * l1 ^ 2 - l1 * d1)
              + (1000 * n * l2 ^ 2 - l2 * d2)) := hch
      _ ≤ 6553600000000 / (1 + (n : ℝ)) * Gweight (1 + n) (1 / 400 * M) :=
          mul_le_mul_of_nonneg_left hGw (by positivity)
      _ = 6553600000000 / (1 + (n : ℝ))
          * Gweight (1 + n) (1 / 400 * ‖((d1, d2) : ℝ × ℝ)‖) := by rw [hnorm]

/-- **Lemma 2.2(i) for `Hold`** (paper p.42: "the conclusion of Lemma 2.2 holds for
`Hold`", mean `(4, 16)`, `d = 2`): the 2-D local Gaussian-type bound
`P(Hold_{[1,n]} = (j,l)) ≪ (n+1)^{-1} · G_n(c((j,l) − n(4,16)))`. Node S3, the hard
kernel behind Lemma 7.7 (X6). D5 route: exponential tilting + `ZMod` circle method;
witnesses `c = 1/400`, `C = (32·80000)² = 6553600000000` — now the symbolic
`c_holdLocal`/`C_holdLocal`, via the `_explicitC` sibling (big-C campaign, step 2).
-- RATIFY-DRIFT (norm): `‖·‖` on `ℝ × ℝ` is the sup norm; the paper's Euclidean
-- `|x|` satisfies `|x|/√2 ≤ ‖x‖_∞ ≤ |x|`, so the two forms of the statement are
-- interchangeable after adjusting the constants `c, C`, which are existential. -/
theorem hold_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (j : ℕ) (l : ℤ),
      ((holdSum n) (j, l)).toReal
        ≤ C / (1 + n) * Gweight (1 + n) (c * ‖(((j : ℝ) - 4 * n, (l : ℝ) - 16 * n) : ℝ × ℝ)‖) :=
  ⟨c_holdLocal, c_holdLocal_pos, C_holdLocal, C_holdLocal_pos, hold_local_bound_explicitC⟩

/-- **One-sided Chernoff/Markov bound for a `Hold` tail half-space**: if the tilt
weight is at least `e^a` everywhere on the region `cond`, then the region's
`iidSum` mass is at most `e^{n·quad(λ) − a}` — Markov's inequality under the tilt,
`tiltZ_iidSum` multiplicativity, and the quadratic MGF bound `tiltZ_hold_le_quad`.
No center bound needed (this is Lemma 2.2(ii)'s engine, paper p.15). -/
theorem holdSum_halfspace_le {l1 l2 : ℝ}
    (h1lo : -(1 / 200) ≤ l1) (h1hi : l1 ≤ 1 / 200)
    (h2lo : -(1 / 200) ≤ l2) (h2hi : l2 ≤ 1 / 200)
    (n : ℕ) (cond : ℕ × ℤ → Prop) [DecidablePred cond] (a : ℝ)
    (hcond : ∀ d : ℕ × ℤ, cond d → a ≤ l1 * d.1 + l2 * d.2) :
    (∑' d : ℕ × ℤ, if cond d then (iidSum hold n) d else 0)
      ≤ ENNReal.ofReal
          (Real.exp ((n : ℝ) * (4 * l1 + 16 * l2 + 1000 * (l1 ^ 2 + l2 ^ 2)) - a)) := by
  have h1lo' : -(1 / 50) ≤ l1 := by linarith
  have h1hi' : l1 ≤ 1 / 50 := by linarith
  have h2lo' : -(1 / 50) ≤ l2 := by linarith
  have h2hi' : l2 ≤ 1 / 50 := by linarith
  have hZ0 := tiltZ_hold_ne_zero l1 l2
  have hZt := tiltZ_hold_ne_top h1hi' h2lo' h2hi'
  set u : ℝ := 4 * l1 + 16 * l2 + 1000 * (l1 ^ 2 + l2 ^ 2) with hu
  -- Markov under the tilt
  have hM : (∑' d : ℕ × ℤ, if cond d then (iidSum hold n) d else 0)
      ≤ ENNReal.ofReal (Real.exp (-a)) * tiltZ hold (expW2 l1 l2) ^ n := by
    rw [← tiltZ_iidSum hold (expW2_zero l1 l2) (expW2_add l1 l2) hZ0 hZt n, tiltZ,
      ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun d => ?_
    split_ifs with h
    · have hw : ENNReal.ofReal (Real.exp a) ≤ expW2 l1 l2 d := by
        simp only [expW2]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hcond d h))
      calc (iidSum hold n) d
          = ENNReal.ofReal (Real.exp (-a))
              * (ENNReal.ofReal (Real.exp a) * (iidSum hold n) d) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
              neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (Real.exp (-a))
              * ((iidSum hold n) d * expW2 l1 l2 d) := by
            rw [mul_comm (ENNReal.ofReal (Real.exp a))]
            gcongr
    · exact bot_le
  refine le_trans hM ?_
  -- the Z-power bound
  have hZle : tiltZ hold (expW2 l1 l2) ≤ ENNReal.ofReal (Real.exp u) :=
    le_trans (tiltZ_hold_le_quad h1lo h1hi h2lo h2hi)
      (ENNReal.ofReal_le_ofReal (by
        have h := Real.add_one_le_exp u
        rw [hu] at h ⊢
        linarith))
  have hBpow : tiltZ hold (expW2 l1 l2) ^ n
      ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by
    calc tiltZ hold (expW2 l1 l2) ^ n
        ≤ ENNReal.ofReal (Real.exp u) ^ n := by gcongr
      _ = ENNReal.ofReal (Real.exp u ^ n) :=
          (ENNReal.ofReal_pow (Real.exp_pos _).le n).symm
      _ = ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by rw [← Real.exp_nat_mul]
  calc ENNReal.ofReal (Real.exp (-a)) * tiltZ hold (expW2 l1 l2) ^ n
      ≤ ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal (Real.exp ((n : ℝ) * u)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp ((n : ℝ) * u - a)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, sub_eq_add_neg,
          add_comm (-a)]

/-- **Large-tilt half-space Chernoff bound.**  Same Markov-under-tilt argument as
`holdSum_halfspace_le`, but taking the `Hold` MGF bound `Z ≤ e^M` (here a NUMERIC
`ofReal M`) as a hypothesis instead of the quadratic box `tiltZ_hold_le_quad` —
this lets the tilt live *outside* the `|λ| ≤ 1/200` box (the exact closed-form MGF
`tiltZ_hold_le_num` is finite up to `θ ≈ 0.213`).  Finiteness of the partition
function comes from the bound itself.  The `4·10⁷ → 64` sharpening of the (7.50)
localization runs through this lemma. -/
theorem holdSum_halfspace_le_of_mgf {l1 l2 M : ℝ}
    (hZle : tiltZ hold (expW2 l1 l2) ≤ ENNReal.ofReal M)
    (n : ℕ) (cond : ℕ × ℤ → Prop) [DecidablePred cond] (a : ℝ)
    (hcond : ∀ d : ℕ × ℤ, cond d → a ≤ l1 * d.1 + l2 * d.2) :
    (∑' d : ℕ × ℤ, if cond d then (iidSum hold n) d else 0)
      ≤ ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal M ^ n := by
  have hZ0 := tiltZ_hold_ne_zero l1 l2
  have hZt : tiltZ hold (expW2 l1 l2) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hZle
  have hM : (∑' d : ℕ × ℤ, if cond d then (iidSum hold n) d else 0)
      ≤ ENNReal.ofReal (Real.exp (-a)) * tiltZ hold (expW2 l1 l2) ^ n := by
    rw [← tiltZ_iidSum hold (expW2_zero l1 l2) (expW2_add l1 l2) hZ0 hZt n, tiltZ,
      ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun d => ?_
    split_ifs with h
    · have hw : ENNReal.ofReal (Real.exp a) ≤ expW2 l1 l2 d := by
        simp only [expW2]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hcond d h))
      calc (iidSum hold n) d
          = ENNReal.ofReal (Real.exp (-a))
              * (ENNReal.ofReal (Real.exp a) * (iidSum hold n) d) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
              neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (Real.exp (-a))
              * ((iidSum hold n) d * expW2 l1 l2 d) := by
            rw [mul_comm (ENNReal.ofReal (Real.exp a))]
            gcongr
    · exact bot_le
  refine le_trans hM ?_
  gcongr

/-- **Lemma 2.2(ii) for `Hold`** (paper p.42 / p.15): the 2-D tail bound
`P(|Hold_{[1,n]} − n(4,16)| ≥ λ) ≪ G_n(cλ)`; witnesses `c = 1/400`, `C = 4`.
Direct Chernoff: the sup-norm tail is covered by four sign-pattern half-spaces,
each bounded by `holdSum_halfspace_le` with the clipped tilt of
`chernoff_clip_le_nonneg` in the matching coordinate/direction (same norm drift
note as `hold_local_bound`). -/
theorem hold_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' d : ℕ × ℤ, if lam ≤ ‖(((d.1 : ℝ) - 4 * n, (d.2 : ℝ) - 16 * n) : ℝ × ℝ)‖
          then ((holdSum n) d).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  refine ⟨1 / 400, by norm_num, 4, by norm_num, fun n lam hlam => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: point mass at the origin
    simp only [holdSum_eq_iidSum, iidSum_zero]
    rw [tsum_eq_single (0 : ℕ × ℤ) (fun d hd => by
      rw [PMF.pure_apply, if_neg hd, ENNReal.toReal_zero, ite_self])]
    rw [PMF.pure_apply, if_pos rfl, ENNReal.toReal_one]
    split_ifs with h0
    · have hlam0 : lam = 0 := by
        simp only [Prod.fst_zero, Prod.snd_zero] at h0
        norm_num [Prod.norm_def] at h0
        linarith
      rw [hlam0]
      rw [Gweight]
      norm_num [Real.exp_zero]
    · exact mul_nonneg (by norm_num) (Gweight_nonneg _ _)
  · -- n ≥ 1: four half-space Chernoff bounds
    have hn1 : 1 ≤ n := hn
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    obtain ⟨mu, hmu0, hmuhi, hexp⟩ := chernoff_clip_le_nonneg hn1 hlam
    set B : ℝ := Real.exp (1000 * n * mu ^ 2 - mu * lam) with hB
    have hmulo : -(1 / 200) ≤ mu := by linarith
    have hmulo' : -(1 / 200) ≤ -mu := by linarith
    have hmuhi' : -mu ≤ 1 / 200 := by linarith
    have hz1 : -(1 / 200 : ℝ) ≤ 0 := by norm_num
    have hz2 : (0 : ℝ) ≤ 1 / 200 := by norm_num
    -- the four half-space ENNReal bounds
    have hT1 := holdSum_halfspace_le hmulo hmuhi hz1 hz2 n
      (fun d : ℕ × ℤ => lam ≤ (d.1 : ℝ) - 4 * n) (mu * (4 * n + lam))
      (fun d hd => by
        have h := mul_le_mul_of_nonneg_left
          (show (4 * (n : ℝ) + lam) ≤ (d.1 : ℝ) by linarith) hmu0
        simp only [zero_mul, add_zero]
        linarith)
    have hT2 := holdSum_halfspace_le hmulo' hmuhi' hz1 hz2 n
      (fun d : ℕ × ℤ => (d.1 : ℝ) - 4 * n ≤ -lam) (-mu * (4 * n - lam))
      (fun d hd => by
        have h := mul_le_mul_of_nonneg_left
          (show (d.1 : ℝ) ≤ 4 * (n : ℝ) - lam by linarith) hmu0
        simp only [zero_mul, add_zero]
        nlinarith)
    have hT3 := holdSum_halfspace_le hz1 hz2 hmulo hmuhi n
      (fun d : ℕ × ℤ => lam ≤ (d.2 : ℝ) - 16 * n) (mu * (16 * n + lam))
      (fun d hd => by
        have h := mul_le_mul_of_nonneg_left
          (show (16 * (n : ℝ) + lam) ≤ (d.2 : ℝ) by linarith) hmu0
        simp only [zero_mul, zero_add]
        linarith)
    have hT4 := holdSum_halfspace_le hz1 hz2 hmulo' hmuhi' n
      (fun d : ℕ × ℤ => (d.2 : ℝ) - 16 * n ≤ -lam) (-mu * (16 * n - lam))
      (fun d hd => by
        have h := mul_le_mul_of_nonneg_left
          (show (d.2 : ℝ) ≤ 16 * (n : ℝ) - lam by linarith) hmu0
        simp only [zero_mul, zero_add]
        nlinarith)
    -- each exponent collapses to `1000nμ² − μ·lam`
    have he1 : (n : ℝ) * (4 * mu + 16 * 0 + 1000 * (mu ^ 2 + 0 ^ 2))
        - mu * (4 * n + lam) = 1000 * n * mu ^ 2 - mu * lam := by ring
    have he2 : (n : ℝ) * (4 * -mu + 16 * 0 + 1000 * ((-mu) ^ 2 + 0 ^ 2))
        - -mu * (4 * n - lam) = 1000 * n * mu ^ 2 - mu * lam := by ring
    have he3 : (n : ℝ) * (4 * 0 + 16 * mu + 1000 * (0 ^ 2 + mu ^ 2))
        - mu * (16 * n + lam) = 1000 * n * mu ^ 2 - mu * lam := by ring
    have he4 : (n : ℝ) * (4 * 0 + 16 * -mu + 1000 * (0 ^ 2 + (-mu) ^ 2))
        - -mu * (16 * n - lam) = 1000 * n * mu ^ 2 - mu * lam := by ring
    rw [he1] at hT1
    rw [he2] at hT2
    rw [he3] at hT3
    rw [he4] at hT4
    -- pointwise 4-way split of the sup-norm tail indicator
    have hsplit : ∀ d : ℕ × ℤ,
        (if lam ≤ ‖(((d.1 : ℝ) - 4 * n, (d.2 : ℝ) - 16 * n) : ℝ × ℝ)‖
            then (iidSum hold n) d else 0)
          ≤ (if lam ≤ (d.1 : ℝ) - 4 * n then (iidSum hold n) d else 0)
            + (if (d.1 : ℝ) - 4 * n ≤ -lam then (iidSum hold n) d else 0)
            + (if lam ≤ (d.2 : ℝ) - 16 * n then (iidSum hold n) d else 0)
            + (if (d.2 : ℝ) - 16 * n ≤ -lam then (iidSum hold n) d else 0) := by
      intro d
      by_cases h0 : lam ≤ ‖(((d.1 : ℝ) - 4 * n, (d.2 : ℝ) - 16 * n) : ℝ × ℝ)‖
      · rw [if_pos h0]
        rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at h0
        rcases le_max_iff.mp h0 with h | h
        · rcases le_abs.mp h with h' | h'
          · exact le_of_eq (if_pos h').symm |>.trans
              (((self_le_add_right _ _).trans (self_le_add_right _ _)).trans
                (self_le_add_right _ _))
          · have hc : (d.1 : ℝ) - 4 * n ≤ -lam := by linarith
            exact le_of_eq (if_pos hc).symm |>.trans
              (((self_le_add_left _ _).trans (self_le_add_right _ _)).trans
                (self_le_add_right _ _))
        · rcases le_abs.mp h with h' | h'
          · exact le_of_eq (if_pos h').symm |>.trans
              ((self_le_add_left _ _).trans (self_le_add_right _ _))
          · have hc : (d.2 : ℝ) - 16 * n ≤ -lam := by linarith
            exact le_of_eq (if_pos hc).symm |>.trans (self_le_add_left _ _)
      · rw [if_neg h0]
        exact bot_le
    -- the ENNReal tail mass bound
    have hchain : (∑' d : ℕ × ℤ,
        if lam ≤ ‖(((d.1 : ℝ) - 4 * n, (d.2 : ℝ) - 16 * n) : ℝ × ℝ)‖
          then (iidSum hold n) d else 0)
        ≤ 4 * ENNReal.ofReal B := by
      refine le_trans (ENNReal.tsum_le_tsum hsplit) ?_
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
      calc _ ≤ ENNReal.ofReal B + ENNReal.ofReal B + ENNReal.ofReal B
            + ENNReal.ofReal B :=
            add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4
        _ = 4 * ENNReal.ofReal B := by ring
    -- pass to `toReal`
    have hTop : ∀ d : ℕ × ℤ,
        (if lam ≤ ‖(((d.1 : ℝ) - 4 * n, (d.2 : ℝ) - 16 * n) : ℝ × ℝ)‖
          then (iidSum hold n) d else 0) ≠ ∞ := fun d => by
      split_ifs
      · exact PMF.apply_ne_top _ _
      · exact ENNReal.zero_ne_top
    have hlhs : (∑' d : ℕ × ℤ,
        if lam ≤ ‖(((d.1 : ℝ) - 4 * n, (d.2 : ℝ) - 16 * n) : ℝ × ℝ)‖
          then ((holdSum n) d).toReal else 0)
        = (∑' d : ℕ × ℤ,
            if lam ≤ ‖(((d.1 : ℝ) - 4 * n, (d.2 : ℝ) - 16 * n) : ℝ × ℝ)‖
              then (iidSum hold n) d else 0).toReal := by
      rw [ENNReal.tsum_toReal_eq hTop]
      refine tsum_congr fun d => ?_
      rw [holdSum_eq_iidSum, apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    rw [hlhs]
    have hfin : (4 : ℝ≥0∞) * ENNReal.ofReal B ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    calc (∑' d : ℕ × ℤ,
        if lam ≤ ‖(((d.1 : ℝ) - 4 * n, (d.2 : ℝ) - 16 * n) : ℝ × ℝ)‖
          then (iidSum hold n) d else 0).toReal
        ≤ ((4 : ℝ≥0∞) * ENNReal.ofReal B).toReal := ENNReal.toReal_mono hfin hchain
      _ = 4 * B := by
          rw [hB, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
          norm_num
      _ ≤ 4 * Gweight (1 + n) (1 / 400 * lam) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact le_trans (Real.exp_le_exp.mpr hexp) (exp_neg_min_le_Gweight hn1 hlam)

end TaoCollatz
