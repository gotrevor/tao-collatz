import TaoCollatz.Prob.Mgf

/-!
# The d=1 instances of Lemma 2.2 (node S3 leaves)

Paper anchors: Tao 2019 Lemma 2.2 pp.14–16, displayed instances for
`|Geom(2)|` (mean 2, p.15) and the mean-4 walks `geomQuarter`, `Pascal` (§7.3).
The statements were RATIFIED in `Prob/LocalBound.lean` and are proved here (this
module sits above `Prob/Mgf.lean`, whose tilting/MGF engine the proofs consume;
a NOTE at the old site points across).

* Tail bounds (2.2(ii)) — PROVED by the same direct Chernoff as
  `hold_tail_bound`: one-sided Markov under the exponential tilt
  (`iidSum_nat_halfspace_le`), two half-lines, clipped tilt
  (`chernoff_clip_le_nonneg`), `Gweight` branch matching
  (`exp_neg_min_le_Gweight`). The 1-D quadratic MGF bounds come from the closed
  forms: `tiltZ_geomHalf` (geometric series), `tiltZ_hold_fst_le` via
  `hold_map_fst` (for `geomQuarter`), `tiltZ_pascal = tiltZ_geomHalf ^ 2`.
  All envelopes numerically validated (K = 8 for `Geom(2)` at box `1/200`,
  squared `≤ 1 + 4λ + 24λ²` for `Pascal`; both weakened to the uniform
  `K = 1000` that `chernoff_clip_le_nonneg` is tuned to).
* Local bounds (2.2(i)) — still open: they need the d=1 center bound
  `C/√(1+n)`, i.e. a single-`ZMod` circle-method analogue of
  `iidSum_apply_le_center_of_decay` (same proof shape, one factor of
  `charFn` decay, `N = ⌊√n⌋ + 1`), which is the next prerequisite.
-/

open scoped ENNReal

namespace TaoCollatz

/-- Positive tilt weights never kill the partition function: `Z(λ) ≠ 0` for any
PMF on `ℕ` (some atom has positive mass, and `e^{λa} > 0`). -/
theorem tiltZ_expW_ne_zero (p : PMF ℕ) (lam : ℝ) : tiltZ p (expW lam) ≠ 0 := by
  intro h
  rw [tiltZ, ENNReal.tsum_eq_zero] at h
  have hp : ∀ a : ℕ, p a = 0 := fun a => by
    have ha := h a
    rcases mul_eq_zero.mp ha with h0 | h0
    · exact h0
    · exact absurd h0 (by
        rw [expW]
        exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
  have := p.tsum_coe
  rw [tsum_congr hp, tsum_zero] at this
  exact zero_ne_one this

/-- **The λ-clip optimization, nonneg-deviation form** ((F5) step 2, shared by all
Lemma 2.2 tail assemblies): for `n ≥ 1` and `dev ≥ 0`, the clipped tilt
`μ = clip(dev/(2000n), 1/200) ≥ 0` makes the Chernoff exponent `1000nμ² − μ·dev`
at most `−min(dev²/(4000n), dev/400)` (central regime `dev ≤ 10n` exact Gaussian;
tail regime exponential). -/
theorem chernoff_clip_le_nonneg {n : ℕ} (hn : 1 ≤ n) {dev : ℝ} (hdev : 0 ≤ dev) :
    ∃ mu : ℝ, 0 ≤ mu ∧ mu ≤ 1 / 200 ∧
      1000 * (n : ℝ) * mu ^ 2 - mu * dev
        ≤ -min (dev ^ 2 / (4000 * n)) (dev / 400) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hne : (n : ℝ) ≠ 0 := hnpos.ne'
  by_cases hc : dev ≤ 10 * n
  · refine ⟨dev / (2000 * n), by positivity, ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      linarith
    · have heq : 1000 * (n : ℝ) * (dev / (2000 * n)) ^ 2 - dev / (2000 * n) * dev
          = -(dev ^ 2 / (4000 * n)) := by
        field_simp
        ring
      rw [heq, neg_le_neg_iff]
      exact min_le_left _ _
  · push_neg at hc
    refine ⟨1 / 200, by norm_num, le_refl _, ?_⟩
    refine le_trans ?_ (neg_le_neg (min_le_right (dev ^ 2 / (4000 * n)) (dev / 400)))
    nlinarith

/-- Matching the optimized Chernoff exponent to the two `Gweight` branches
(shared by all Lemma 2.2 assemblies): for `n ≥ 1`, `x ≥ 0`,
`e^{−min(x²/4000n, x/400)} ≤ G_{1+n}(x/400)`. -/
theorem exp_neg_min_le_Gweight {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-min (x ^ 2 / (4000 * n)) (x / 400)) ≤ Gweight (1 + n) (1 / 400 * x) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  rcases min_cases (x ^ 2 / (4000 * (n : ℝ))) (x / 400) with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm]
    have hbr : Real.exp (-(x ^ 2 / (4000 * n)))
        ≤ Real.exp (-((1 / 400 * x) ^ 2) / (1 + (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_le_neg_iff,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) hnpos.le]
    exact le_trans hbr (le_add_of_nonneg_right (Real.exp_pos _).le)
  · rw [hm]
    have hbr : -(x / 400) = -|1 / 400 * x| := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 400 * x)]
      ring
    rw [hbr]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-! ### 1-D quadratic MGF bounds (mean exact to first order, uniform `K = 1000`) -/

/-- **Second-order MGF bound for `Geom(2)`** (mean 2 exact): on `|λ| ≤ 1/200`,
`Z(λ) ≤ 1 + 2λ + 1000λ²` (the tight constant is `K = 8`; numerically validated).
From the geometric closed form `tiltZ_geomHalf` with envelope `e^λ ≤ 1+λ+2λ²`. -/
theorem tiltZ_geomHalf_le_quad {lam : ℝ} (hlo : -(1 / 200) ≤ lam)
    (hhi : lam ≤ 1 / 200) :
    tiltZ geomHalf (expW lam) ≤ ENNReal.ofReal (1 + 2 * lam + 8 * lam ^ 2) := by
  set E : ℝ := 1 + lam + 2 * lam ^ 2 with hE
  have hexpE : Real.exp lam ≤ E := exp_le_one_add_add_two_sq (by linarith)
  have hE1 : E / 2 < 1 := by
    rw [hE]
    nlinarith
  have hEpos : (0 : ℝ) < E := by
    rw [hE]
    nlinarith
  rw [tiltZ_geomHalf]
  refine le_trans (frac_closed_le (by positivity) (by linarith : Real.exp lam / 2 ≤ E / 2)
    (by positivity) (by linarith : Real.exp lam / 2 ≤ E / 2) hE1) ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - E / 2)]
  rw [hE]
  have hb1 : (0 : ℝ) ≤ 1 / 200 - lam := by linarith
  have hb2 : (0 : ℝ) ≤ 1 / 200 + lam := by linarith
  nlinarith [sq_nonneg lam, mul_nonneg hb1 (sq_nonneg lam),
    mul_nonneg hb2 (sq_nonneg lam),
    mul_nonneg (mul_nonneg hb1 hb2) (sq_nonneg lam)]

/-- **Second-order MGF bound for `Pascal`** (mean 4 exact): on `|λ| ≤ 1/200`,
`Z(λ) ≤ 1 + 4λ + 1000λ²` — the square of the `Geom(2)` bound
(`(1+2λ+8λ²)² ≤ 1+4λ+24λ²` on the box, numerically validated). -/
theorem tiltZ_pascal_le_quad {lam : ℝ} (hlo : -(1 / 200) ≤ lam)
    (hhi : lam ≤ 1 / 200) :
    tiltZ pascal (expW lam) ≤ ENNReal.ofReal (1 + 4 * lam + 1000 * lam ^ 2) := by
  have hstrip : Real.exp lam < 2 :=
    lt_of_le_of_lt (exp_le_one_add_add_two_sq (by linarith)) (by nlinarith)
  have hgh := tiltZ_geomHalf_le_quad hlo hhi
  have hP : (0 : ℝ) ≤ 1 + 2 * lam + 8 * lam ^ 2 := by nlinarith
  calc tiltZ pascal (expW lam)
      = tiltZ geomHalf (expW lam) ^ 2 := tiltZ_pascal hstrip
    _ ≤ ENNReal.ofReal (1 + 2 * lam + 8 * lam ^ 2) ^ 2 := by gcongr
    _ = ENNReal.ofReal ((1 + 2 * lam + 8 * lam ^ 2) ^ 2) :=
        (ENNReal.ofReal_pow hP 2).symm
    _ ≤ ENNReal.ofReal (1 + 4 * lam + 1000 * lam ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hb1 : (0 : ℝ) ≤ 1 / 200 - lam := by linarith
        have hb2 : (0 : ℝ) ≤ 1 / 200 + lam := by linarith
        nlinarith [sq_nonneg lam, mul_nonneg hb1 (sq_nonneg lam),
          mul_nonneg hb2 (sq_nonneg lam),
          mul_nonneg (mul_nonneg hb1 hb2) (sq_nonneg lam)]

/-- The `geomQuarter` partition function is the first-coordinate `Hold` partition
function (`hold_map_fst` + `tiltZ_map`). -/
theorem tiltZ_geomQuarter_eq (lam : ℝ) :
    tiltZ geomQuarter (expW lam) = tiltZ hold (expW2 lam 0) := by
  rw [← hold_map_fst, tiltZ_map]
  refine tsum_congr fun d => ?_
  congr 1
  simp only [Function.comp_apply, expW, expW2]
  norm_num

/-- **Second-order MGF bound for `geomQuarter`** (mean 4 exact): on `|λ| ≤ 1/200`,
`Z(λ) ≤ 1 + 4λ + 1000λ²` — transfer of `tiltZ_hold_fst_le` (`K = 32`). -/
theorem tiltZ_geomQuarter_le_quad {lam : ℝ} (hlo : -(1 / 200) ≤ lam)
    (hhi : lam ≤ 1 / 200) :
    tiltZ geomQuarter (expW lam) ≤ ENNReal.ofReal (1 + 4 * lam + 1000 * lam ^ 2) := by
  rw [tiltZ_geomQuarter_eq]
  refine le_trans (tiltZ_hold_fst_le (by linarith) (by linarith)) ?_
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg lam]

/-! ### The generic 1-D Chernoff tail machine -/

/-- **One-sided Markov bound for a 1-D tail half-line** (mirror of
`holdSum_halfspace_le`, generic in the walk): if the tilt weight is `≥ e^a` on
the region `cond`, the region's `iidSum` mass is `≤ e^{-a}·Z(λ)ⁿ`. -/
theorem iidSum_nat_halfspace_le (p : PMF ℕ) {t : ℝ}
    (hZt : tiltZ p (expW t) ≠ ∞) (n : ℕ)
    (cond : ℕ → Prop) [DecidablePred cond] (a : ℝ)
    (hcond : ∀ L : ℕ, cond L → a ≤ t * L) :
    (∑' L : ℕ, if cond L then (iidSum p n) L else 0)
      ≤ ENNReal.ofReal (Real.exp (-a)) * tiltZ p (expW t) ^ n := by
  have hZ0 := tiltZ_expW_ne_zero p t
  rw [← tiltZ_iidSum p (expW_zero t) (expW_add t) hZ0 hZt n, tiltZ,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun L => ?_
  split_ifs with h
  · have hw : ENNReal.ofReal (Real.exp a) ≤ expW t L := by
      rw [expW]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hcond L h))
    calc (iidSum p n) L
        = ENNReal.ofReal (Real.exp (-a))
            * (ENNReal.ofReal (Real.exp a) * (iidSum p n) L) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (-a))
            * ((iidSum p n) L * expW t L) := by
          rw [mul_comm (ENNReal.ofReal (Real.exp a))]
          gcongr
  · exact bot_le

/-- **The generic d=1 Lemma 2.2(ii)** (direct Chernoff): any walk on `ℕ` with a
second-order MGF bound `Z(λ) ≤ 1 + mλ + 1000λ²` on `|λ| ≤ 1/200` satisfies the
tail bound with `c = 1/400`, `C = 2` — two half-lines, clipped tilt, `Gweight`
branch matching. -/
theorem iidSum_nat_tail_of_quad (p : PMF ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hquad : ∀ lam : ℝ, -(1 / 200) ≤ lam → lam ≤ 1 / 200 →
      tiltZ p (expW lam) ≤ ENNReal.ofReal (1 + m * lam + 1000 * lam ^ 2))
    (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∑' L : ℕ, if lam ≤ |(L : ℝ) - m * n| then ((iidSum p n) L).toReal else 0)
      ≤ 2 * Gweight (1 + n) (1 / 400 * lam) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: point mass at the origin
    simp only [iidSum_zero]
    rw [tsum_eq_single (0 : ℕ) (fun L hL => by
      rw [PMF.pure_apply, if_neg hL, ENNReal.toReal_zero, ite_self])]
    rw [PMF.pure_apply, if_pos rfl, ENNReal.toReal_one]
    split_ifs with h0
    · have hlam0 : lam = 0 := by
        simp only [Nat.cast_zero, mul_zero, zero_sub, abs_neg, abs_zero] at h0
        linarith
      rw [hlam0]
      rw [Gweight]
      norm_num [Real.exp_zero]
    · exact mul_nonneg (by norm_num) (Gweight_nonneg _ _)
  · -- n ≥ 1: two half-line Chernoff bounds
    have hn1 : 1 ≤ n := hn
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    obtain ⟨mu, hmu0, hmuhi, hexp⟩ := chernoff_clip_le_nonneg hn1 hlam
    set B : ℝ := Real.exp (1000 * n * mu ^ 2 - mu * lam) with hB
    have hmulo : -(1 / 200) ≤ mu := by linarith
    have hmulo' : -(1 / 200) ≤ -mu := by linarith
    have hmuhi' : -mu ≤ 1 / 200 := by linarith
    -- exp-form MGF bounds at ±μ
    have hq1 : tiltZ p (expW mu) ≤ ENNReal.ofReal (Real.exp (m * mu + 1000 * mu ^ 2)) :=
      le_trans (hquad mu hmulo hmuhi) (ENNReal.ofReal_le_ofReal (by
        have h := Real.add_one_le_exp (m * mu + 1000 * mu ^ 2)
        linarith))
    have hq2 : tiltZ p (expW (-mu))
        ≤ ENNReal.ofReal (Real.exp (m * -mu + 1000 * mu ^ 2)) :=
      le_trans (hquad (-mu) hmulo' hmuhi') (ENNReal.ofReal_le_ofReal (by
        have h := Real.add_one_le_exp (m * -mu + 1000 * mu ^ 2)
        nlinarith [sq_nonneg mu]))
    have hZt1 : tiltZ p (expW mu) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hq1
    have hZt2 : tiltZ p (expW (-mu)) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hq2
    -- powers
    have hpow : ∀ {t q : ℝ}, tiltZ p (expW t) ≤ ENNReal.ofReal (Real.exp q) →
        tiltZ p (expW t) ^ n ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * q)) := by
      intro t q hZq
      calc tiltZ p (expW t) ^ n
          ≤ ENNReal.ofReal (Real.exp q) ^ n := by gcongr
        _ = ENNReal.ofReal (Real.exp q ^ n) :=
            (ENNReal.ofReal_pow (Real.exp_pos _).le n).symm
        _ = ENNReal.ofReal (Real.exp ((n : ℝ) * q)) := by rw [← Real.exp_nat_mul]
    -- the two half-line bounds
    have hT1 : (∑' L : ℕ, if lam ≤ (L : ℝ) - m * n then (iidSum p n) L else 0)
        ≤ ENNReal.ofReal B := by
      refine le_trans (le_trans (le_of_eq rfl)
        (iidSum_nat_halfspace_le p hZt1 n _ (mu * (m * n + lam))
          (fun L hL => by nlinarith))) ?_
      calc ENNReal.ofReal (Real.exp (-(mu * (m * n + lam)))) * tiltZ p (expW mu) ^ n
          ≤ ENNReal.ofReal (Real.exp (-(mu * (m * n + lam))))
            * ENNReal.ofReal (Real.exp ((n : ℝ) * (m * mu + 1000 * mu ^ 2))) := by
            gcongr
            exact hpow hq1
        _ = ENNReal.ofReal B := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hB]
            congr 1
            ring
    have hT2 : (∑' L : ℕ, if (L : ℝ) - m * n ≤ -lam then (iidSum p n) L else 0)
        ≤ ENNReal.ofReal B := by
      refine le_trans (le_trans (le_of_eq rfl)
        (iidSum_nat_halfspace_le p hZt2 n _ (-mu * (m * n - lam))
          (fun L hL => by nlinarith))) ?_
      calc ENNReal.ofReal (Real.exp (-(-mu * (m * n - lam)))) * tiltZ p (expW (-mu)) ^ n
          ≤ ENNReal.ofReal (Real.exp (-(-mu * (m * n - lam))))
            * ENNReal.ofReal (Real.exp ((n : ℝ) * (m * -mu + 1000 * mu ^ 2))) := by
            gcongr
            exact hpow hq2
        _ = ENNReal.ofReal B := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hB]
            congr 1
            ring
    -- pointwise 2-way split of the tail indicator
    have hsplit : ∀ L : ℕ,
        (if lam ≤ |(L : ℝ) - m * n| then (iidSum p n) L else 0)
          ≤ (if lam ≤ (L : ℝ) - m * n then (iidSum p n) L else 0)
            + (if (L : ℝ) - m * n ≤ -lam then (iidSum p n) L else 0) := by
      intro L
      by_cases h0 : lam ≤ |(L : ℝ) - m * n|
      · rw [if_pos h0]
        rcases le_abs.mp h0 with h' | h'
        · exact le_of_eq (if_pos h').symm |>.trans (self_le_add_right _ _)
        · have hc : (L : ℝ) - m * n ≤ -lam := by linarith
          exact le_of_eq (if_pos hc).symm |>.trans (self_le_add_left _ _)
      · rw [if_neg h0]
        exact bot_le
    have hchain : (∑' L : ℕ, if lam ≤ |(L : ℝ) - m * n| then (iidSum p n) L else 0)
        ≤ 2 * ENNReal.ofReal B := by
      refine le_trans (ENNReal.tsum_le_tsum hsplit) ?_
      rw [ENNReal.tsum_add]
      calc _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hT1 hT2
        _ = 2 * ENNReal.ofReal B := (two_mul _).symm
    -- pass to `toReal`
    have hTop : ∀ L : ℕ,
        (if lam ≤ |(L : ℝ) - m * n| then (iidSum p n) L else 0) ≠ ∞ := fun L => by
      split_ifs
      · exact PMF.apply_ne_top _ _
      · exact ENNReal.zero_ne_top
    have hlhs : (∑' L : ℕ, if lam ≤ |(L : ℝ) - m * n| then ((iidSum p n) L).toReal else 0)
        = (∑' L : ℕ, if lam ≤ |(L : ℝ) - m * n| then (iidSum p n) L else 0).toReal := by
      rw [ENNReal.tsum_toReal_eq hTop]
      refine tsum_congr fun L => ?_
      rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    rw [hlhs]
    have hfin : (2 : ℝ≥0∞) * ENNReal.ofReal B ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    calc (∑' L : ℕ, if lam ≤ |(L : ℝ) - m * n| then (iidSum p n) L else 0).toReal
        ≤ ((2 : ℝ≥0∞) * ENNReal.ofReal B).toReal := ENNReal.toReal_mono hfin hchain
      _ = 2 * B := by
          rw [hB, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
          norm_num
      _ ≤ 2 * Gweight (1 + n) (1 / 400 * lam) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact le_trans (Real.exp_le_exp.mpr hexp) (exp_neg_min_le_Gweight hn1 hlam)

/-! ### The six ratified d=1 Lemma 2.2 statements (moved from `Prob/LocalBound.lean`) -/

/-- **Lemma 2.2(ii) for `Geom(2)`** (paper p.15, displayed instance):
`P(||Geom(2)_n| − 2n| ≥ λ) ≪ G_n(cλ)`. -/
theorem geomHalf_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 2 * n| then ((iidSum geomHalf n) L).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  refine ⟨1 / 400, by norm_num, 2, by norm_num, fun n lam hlam => ?_⟩
  exact iidSum_nat_tail_of_quad geomHalf 2 (by norm_num)
    (fun t hlo hhi => le_trans (tiltZ_geomHalf_le_quad hlo hhi)
      (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg t]))) n lam hlam

/-- **Lemma 2.2(ii) for `geomQuarter`** (mean 4; §7.3 consumes this through
`Hold`'s first coordinate). -/
theorem geomQuarter_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 4 * n| then ((iidSum geomQuarter n) L).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  refine ⟨1 / 400, by norm_num, 2, by norm_num, fun n lam hlam => ?_⟩
  exact iidSum_nat_tail_of_quad geomQuarter 4 (by norm_num)
    (fun t hlo hhi => tiltZ_geomQuarter_le_quad hlo hhi) n lam hlam

/-- **Lemma 2.2(ii) for `Pascal`** (mean 4). -/
theorem pascal_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 4 * n| then ((iidSum pascal n) L).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  refine ⟨1 / 400, by norm_num, 2, by norm_num, fun n lam hlam => ?_⟩
  exact iidSum_nat_tail_of_quad pascal 4 (by norm_num)
    (fun t hlo hhi => tiltZ_pascal_le_quad hlo hhi) n lam hlam

/-- **Lemma 2.2(i) for `Geom(2)`** (paper p.15, displayed instance):
`P(|Geom(2)_n| = L) ≪ (n+1)^{-1/2} · G_n(c(L − 2n))`.
OPEN: needs the d=1 center bound `C/√(1+n)` — a single-`ZMod` circle-method
analogue of `iidSum_apply_le_center_of_decay` (one `charFn` decay factor,
`N = ⌊√n⌋ + 1`); the Chernoff/tilting assembly is then identical to
`hold_local_bound`. -/
theorem geomHalf_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum geomHalf n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - 2 * n)) := by
  sorry

/-- **Lemma 2.2(i) for `Geom(4)`-shaped `geomQuarter`** (mean 4).
OPEN: same d=1 center-bound prerequisite as `geomHalf_local_bound`. -/
theorem geomQuarter_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum geomQuarter n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - 4 * n)) := by
  sorry

/-- **Lemma 2.2(i) for `Pascal`** (mean 4). Via `pascal_eq_map_iid`, `iidSum pascal n`
is the law of `|Geom(2)_{2n}|`, so this also reduces to the exact negative-binomial
point mass `C(L-1, 2n-1)·2^{-L}` (`negBinomial_apply`) plus Stirling-type estimates.
OPEN: same d=1 center-bound prerequisite as `geomHalf_local_bound` (the circle
method route avoids Stirling). -/
theorem pascal_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum pascal n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - 4 * n)) := by
  sorry

end TaoCollatz
