import TaoCollatz.Prob.LocalBound

/-!
# Exponential tilting of PMFs (node S3, step (F))

Paper anchor: Tao 2019 Lemma 2.2 proof pp.15–16 — the Chernoff/tilting step: for a
tilt parameter `λ` with finite MGF, `P(S_n = v) = M(λ)ⁿ e^{-λ·v} P_λ(S̃_n = v)`,
where `P_λ` is the exponentially tilted walk. Per design decision D5 everything is
finite/discrete: the tilt weight is an abstract multiplicative weight
`w : M → ℝ≥0∞` (`w 0 = 1`, `w(a+b) = w a · w b`; instantiated at
`w d = exp(λ·d)`), the partition function `tiltZ p w = Σ_d p d · w d` is the MGF,
and the identity is proved for point masses of `iidSum` by induction — entirely in
`ℝ≥0∞`, so no convergence side conditions beyond `0 < Z < ∞`.

* `tiltZ p w` — the partition function (MGF at the tilt).
* `tilt p w` — the tilted PMF `p·w/Z`.
* `iidSum_tilt_apply` — the tilting identity in product form:
  `P_λ(S̃_n = v) · Zⁿ = P(S_n = v) · w v`.
* `iidSum_apply_eq_tilt` — the consumption form
  `P(S_n = v) = P_λ(S̃_n = v) · Zⁿ · (w v)⁻¹`.
-/

open scoped ENNReal

namespace TaoCollatz

variable {M : Type*}

/-- The partition function (moment generating function at the tilt weight `w`). -/
noncomputable def tiltZ (p : PMF M) (w : M → ℝ≥0∞) : ℝ≥0∞ := ∑' d, p d * w d

/-- **The exponentially tilted PMF** `tilt p w = p · w / Z` (paper p.15, the measure
`P_λ`), for any weight with finite nonzero partition function. -/
noncomputable def tilt (p : PMF M) (w : M → ℝ≥0∞) (hZ0 : tiltZ p w ≠ 0)
    (hZt : tiltZ p w ≠ ∞) : PMF M :=
  ⟨fun d => p d * w d * (tiltZ p w)⁻¹, by
    have h : ∑' d, p d * w d * (tiltZ p w)⁻¹ = 1 := by
      rw [ENNReal.tsum_mul_right, ← tiltZ, ENNReal.mul_inv_cancel hZ0 hZt]
    rw [← h]
    exact ENNReal.summable.hasSum⟩

theorem tilt_apply (p : PMF M) (w : M → ℝ≥0∞) (hZ0 : tiltZ p w ≠ 0)
    (hZt : tiltZ p w ≠ ∞) (d : M) :
    tilt p w hZ0 hZt d = p d * w d * (tiltZ p w)⁻¹ := rfl

/-- **The tilting identity for iid sums** (paper p.15, product form — total, no
division): the tilted walk's point mass times `Zⁿ` is the original walk's point mass
times the weight. Induction on `n`; the multiplicativity of `w` recombines the head
draw's weight with the tail sum's weight on the diagonal `v = a + e`. -/
theorem iidSum_tilt_apply [AddCommMonoid M] (p : PMF M) {w : M → ℝ≥0∞} (hw0 : w 0 = 1)
    (hwadd : ∀ a b, w (a + b) = w a * w b)
    (hZ0 : tiltZ p w ≠ 0) (hZt : tiltZ p w ≠ ∞) (n : ℕ) (v : M) :
    (iidSum (tilt p w hZ0 hZt) n) v * (tiltZ p w) ^ n = (iidSum p n) v * w v := by
  classical
  induction n generalizing v with
  | zero =>
    rw [iidSum_zero, iidSum_zero, pow_zero, mul_one, PMF.pure_apply]
    split_ifs with h
    · rw [h, hw0, mul_one]
    · rw [zero_mul]
  | succ n IH =>
    rw [iidSum_succ, iidSum_succ, pow_succ]
    simp only [PMF.bind_apply, PMF.map_apply]
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [tilt_apply]
    -- the tail sum, tilted back through the induction hypothesis
    have hA : (∑' e, if v = a + e then (iidSum (tilt p w hZ0 hZt) n) e else 0)
          * tiltZ p w ^ n
        = ∑' e, if v = a + e then (iidSum p n) e * w e else 0 := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun e => ?_
      split_ifs with h
      · exact IH e
      · rw [zero_mul]
    -- weights recombine on the diagonal `v = a + e`
    have hB : w a * ((∑' e, if v = a + e then (iidSum (tilt p w hZ0 hZt) n) e else 0)
          * tiltZ p w ^ n)
        = (∑' e, if v = a + e then (iidSum p n) e else 0) * w v := by
      rw [hA, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun e => ?_
      split_ifs with h
      · rw [h, hwadd a e]
        ring
      · rw [mul_zero, zero_mul]
    calc p a * w a * (tiltZ p w)⁻¹
          * (∑' e, if v = a + e then (iidSum (tilt p w hZ0 hZt) n) e else 0)
          * (tiltZ p w ^ n * tiltZ p w)
        = ((tiltZ p w)⁻¹ * tiltZ p w) * (p a
            * (w a * ((∑' e, if v = a + e then (iidSum (tilt p w hZ0 hZt) n) e else 0)
              * tiltZ p w ^ n))) := by ring
      _ = p a * ((∑' e, if v = a + e then (iidSum p n) e else 0) * w v) := by
          rw [ENNReal.inv_mul_cancel hZ0 hZt, one_mul, hB]
      _ = p a * (∑' e, if v = a + e then (iidSum p n) e else 0) * w v := by ring

/-- Partition functions push forward: `tiltZ (p.map φ) w = tiltZ p (w ∘ φ)`. -/
theorem tiltZ_map {M' : Type*} (p : PMF M) (φ : M → M') (w : M' → ℝ≥0∞) :
    tiltZ (p.map φ) w = tiltZ p (w ∘ φ) :=
  PMF.tsum_map_mul p φ w

/-- **Partition functions of iid sums are powers** (MGF multiplicativity, the
Chernoff engine): `Z_{S_n}(λ) = Z(λ)ⁿ`. -/
theorem tiltZ_iidSum [AddCommMonoid M] (p : PMF M) {w : M → ℝ≥0∞} (hw0 : w 0 = 1)
    (hwadd : ∀ a b, w (a + b) = w a * w b)
    (hZ0 : tiltZ p w ≠ 0) (hZt : tiltZ p w ≠ ∞) (n : ℕ) :
    tiltZ (iidSum p n) w = (tiltZ p w) ^ n := by
  rw [tiltZ,
    tsum_congr fun v => (iidSum_tilt_apply p hw0 hwadd hZ0 hZt n v).symm,
    ENNReal.tsum_mul_right, (iidSum (tilt p w hZ0 hZt) n).tsum_coe, one_mul]

/-- **The tilting identity, consumption form** (paper p.15):
`P(S_n = v) = P_λ(S̃_n = v) · M(λ)ⁿ · w(v)⁻¹` whenever the weight at `v` is finite
and nonzero — the change of measure that converts the tilted walk's center-regime
local bound into the original walk's off-center Gaussian bound. -/
theorem iidSum_apply_eq_tilt [AddCommMonoid M] (p : PMF M) {w : M → ℝ≥0∞} (hw0 : w 0 = 1)
    (hwadd : ∀ a b, w (a + b) = w a * w b)
    (hZ0 : tiltZ p w ≠ 0) (hZt : tiltZ p w ≠ ∞) (n : ℕ) (v : M)
    (hwv0 : w v ≠ 0) (hwvt : w v ≠ ∞) :
    (iidSum p n) v
      = (iidSum (tilt p w hZ0 hZt) n) v * (tiltZ p w) ^ n * (w v)⁻¹ := by
  rw [iidSum_tilt_apply p hw0 hwadd hZ0 hZt n v, mul_assoc,
    ENNReal.mul_inv_cancel hwv0 hwvt, mul_one]

/-! ### Weighted Cauchy–Schwarz for partition functions

The 2-D `Hold` MGF second-order bound splits into two 1-D bounds via
`Z(λ₁,λ₂)² ≤ Z(2λ₁,0)·Z(0,2λ₂)` — Cauchy–Schwarz preserves the first-order
(mean) term exactly, which AM–GM would not. Proved from scratch in `ℝ≥0∞`
(mathlib's Hölder is stated for `ℝ≥0` with summability side conditions). -/

/-- Pointwise AM–GM in `ℝ≥0∞`: `x·y ≤ (x² + y²)/2` (top cases by hand, finite case
lifted to `ℝ` through `NNReal`). -/
theorem ennreal_mul_le_sq_add_sq_div_two (x y : ℝ≥0∞) :
    x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
  rcases eq_or_ne x 0 with hx0 | hx0
  · rw [hx0, zero_mul]
    exact bot_le
  rcases eq_or_ne y 0 with hy0 | hy0
  · rw [hy0, mul_zero]
    exact bot_le
  rcases eq_or_ne x ⊤ with hx | hx
  · refine le_trans le_top (le_of_eq ?_)
    rw [eq_comm, ENNReal.div_eq_top]
    exact Or.inr ⟨ENNReal.add_eq_top.mpr (Or.inl (by rw [hx, ENNReal.top_pow two_ne_zero])),
      by finiteness⟩
  rcases eq_or_ne y ⊤ with hy | hy
  · refine le_trans le_top (le_of_eq ?_)
    rw [eq_comm, ENNReal.div_eq_top]
    exact Or.inr ⟨ENNReal.add_eq_top.mpr (Or.inr (by rw [hy, ENNReal.top_pow two_ne_zero])),
      by finiteness⟩
  -- both finite: lift to ℝ
  lift x to NNReal using hx
  lift y to NNReal using hy
  rw [← ENNReal.coe_mul, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_add,
    show ((2 : ℝ≥0∞)) = ((2 : NNReal) : ℝ≥0∞) from rfl,
    ← ENNReal.coe_div (by norm_num), ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast
  rw [le_div_iff₀ (by norm_num)]
  nlinarith [two_mul_le_add_sq (x : ℝ) (y : ℝ)]

/-- **Weighted Cauchy–Schwarz for `ℝ≥0∞` sums**:
`(Σ p·u·v)² ≤ (Σ p·u²)·(Σ p·v²)` — no summability side conditions.
Double-sum expansion; each cross term `p_d p_e (u_d v_d)(u_e v_e)` is at most
`p_d p_e ((u_d v_e)² + (u_e v_d)²)/2`, and the two halves each sum to the
right-hand product (one after swapping the summation order). -/
theorem tsum_mul_mul_sq_le {ι : Type*} (p u v : ι → ℝ≥0∞) :
    (∑' d, p d * (u d * v d)) ^ 2
      ≤ (∑' d, p d * (u d) ^ 2) * (∑' d, p d * (v d) ^ 2) := by
  have hexpand : (∑' d, p d * (u d * v d)) ^ 2
      = ∑' d, ∑' e, (p d * (u d * v d)) * (p e * (u e * v e)) := by
    rw [sq, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun d => ENNReal.tsum_mul_left.symm
  have hpoint : ∀ d e, (p d * (u d * v d)) * (p e * (u e * v e))
      ≤ (p d * p e) * (((u d * v e) ^ 2 + (u e * v d) ^ 2) / 2) := by
    intro d e
    calc (p d * (u d * v d)) * (p e * (u e * v e))
        = (p d * p e) * ((u d * v e) * (u e * v d)) := by ring
      _ ≤ (p d * p e) * (((u d * v e) ^ 2 + (u e * v d) ^ 2) / 2) := by
          gcongr
          exact ennreal_mul_le_sq_add_sq_div_two _ _
  have hhalf : ∀ d e, (p d * p e) * (((u d * v e) ^ 2 + (u e * v d) ^ 2) / 2)
      = ((p d * (u d) ^ 2) * (p e * (v e) ^ 2)
          + (p d * (v d) ^ 2) * (p e * (u e) ^ 2)) / 2 := by
    intro d e
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  calc (∑' d, p d * (u d * v d)) ^ 2
      = ∑' d, ∑' e, (p d * (u d * v d)) * (p e * (u e * v e)) := hexpand
    _ ≤ ∑' d, ∑' e, ((p d * (u d) ^ 2) * (p e * (v e) ^ 2)
          + (p d * (v d) ^ 2) * (p e * (u e) ^ 2)) / 2 := by
        refine ENNReal.tsum_le_tsum fun d => ENNReal.tsum_le_tsum fun e => ?_
        exact le_trans (hpoint d e) (le_of_eq (hhalf d e))
    _ = (∑' d, ∑' e, ((p d * (u d) ^ 2) * (p e * (v e) ^ 2)
          + (p d * (v d) ^ 2) * (p e * (u e) ^ 2))) / 2 := by
        rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun d => ?_
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun e => div_eq_mul_inv _ _
    _ = ((∑' d, p d * (u d) ^ 2) * (∑' d, p d * (v d) ^ 2)
          + (∑' d, p d * (v d) ^ 2) * (∑' d, p d * (u d) ^ 2)) / 2 := by
        congr 1
        calc ∑' d, ∑' e, ((p d * (u d) ^ 2) * (p e * (v e) ^ 2)
              + (p d * (v d) ^ 2) * (p e * (u e) ^ 2))
            = ∑' d, ((p d * (u d) ^ 2) * ∑' e, p e * (v e) ^ 2
                + (p d * (v d) ^ 2) * ∑' e, p e * (u e) ^ 2) :=
              tsum_congr fun d => by
                rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
          _ = (∑' d, p d * (u d) ^ 2) * (∑' d, p d * (v d) ^ 2)
                + (∑' d, p d * (v d) ^ 2) * (∑' d, p d * (u d) ^ 2) := by
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    _ = (∑' d, p d * (u d) ^ 2) * (∑' d, p d * (v d) ^ 2) := by
        rw [mul_comm (∑' d, p d * (v d) ^ 2) (∑' d, p d * (u d) ^ 2),
          ← ENNReal.div_add_div_same, ENNReal.add_halves]

end TaoCollatz
