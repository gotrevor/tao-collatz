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

variable {M : Type*} [AddCommMonoid M]

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
theorem iidSum_tilt_apply (p : PMF M) {w : M → ℝ≥0∞} (hw0 : w 0 = 1)
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
theorem tiltZ_iidSum (p : PMF M) {w : M → ℝ≥0∞} (hw0 : w 0 = 1)
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
theorem iidSum_apply_eq_tilt (p : PMF M) {w : M → ℝ≥0∞} (hw0 : w 0 = 1)
    (hwadd : ∀ a b, w (a + b) = w a * w b)
    (hZ0 : tiltZ p w ≠ 0) (hZt : tiltZ p w ≠ ∞) (n : ℕ) (v : M)
    (hwv0 : w v ≠ 0) (hwvt : w v ≠ ∞) :
    (iidSum p n) v
      = (iidSum (tilt p w hZ0 hZt) n) v * (tiltZ p w) ^ n * (w v)⁻¹ := by
  rw [iidSum_tilt_apply p hw0 hwadd hZ0 hZt n v, mul_assoc,
    ENNReal.mul_inv_cancel hwv0 hwvt, mul_one]

end TaoCollatz
