import TaoCollatz.Sec7.Monotone
import TaoCollatz.Sec7.Unroll
import TaoCollatz.Sec7.FpLocation

/-!
# §7.4 Cases 2–3 of Proposition 7.8: the black-edge bound (nodes X8/X10/X11)

Decomposition of `Q_black_edge` — the (7.41) edge bound for BLACK starts —
per paper pp.46–49, eqs (7.44)–(7.67). A black edge point `(⌊n/2⌋-m, l)` lies
(after the renewal→phase index shift `j ↦ j-1`) in a Lemma 7.4 triangle `Δ`;
with height budget `s := l_Δ - l` the first-passage decomposition
`Q_le_fpDist_expect` ((7.45), `Unroll.lean`) reduces (7.41) to control of the
first-passage endpoint `(j,l) + v_{[1,k]}`:

* `TriangleFamily` — bundled Lemma 7.4 data (`black_structure`).
* `edgeWeight` ((7.46) weight factor) + `Q_fp_endpoint_le` — one more (7.35)
  step at the endpoint exposes the white damping `exp(-ε³·1_W)` and the depth
  weight `max(m - j_{[1,k]} - Geom(4), 1)^{-A}`; PROVED.
* `fpDist_edgeWeight_le` ((7.42)+(7.48)/(7.49)) — the weight degradation is
  `≤ (1+δ)·m^{-A}` for `m ≥ C_{A,δ}` in Case 2; OPEN (consumes Lemma 7.7 = X6).
* `fpDist_white_exit` ((7.50)/(7.51)) — the endpoint is white (and in-strip)
  with probability `≥ p₀ > 0` absolute; OPEN (consumes X6 + separation).
* `budget_le_of_mem_triangle` ((7.52)) — `s·log 2 ≤ (m+2)·log 9`; PROVED.
* `Q_black_edge_case2` ((7.46)–(7.51) assembly, `s ≤ m/log²m`); OPEN.
* `Q_black_edge_of_case3` — the case split, parameterized by the downstream
  Case 3 bound so the X11 proof can consume Lemmas 7.9/7.10 without an import
  cycle; its local body is checked (the separate X8 inputs remain open).

The corresponding Proposition 7.8 and polynomial-decay assemblies are also
parameterized here. `Case3.lean` owns the final theorem names after supplying
the sole X11 gate.
-/

namespace TaoCollatz

open scoped ENNReal

-- `epsBW = 10⁻¹⁰⁰⁰` ⟹ `1/ε = 10^1000` past the default `norm_num`
-- exponentiation cap (256); raise it so `1 ≤ 10^1000` etc. evaluate.
set_option exponentiation.threshold 3000

/-- **Lemma 7.4 data, bundled** (paper pp.38–41): the family of corner triangles
covering the black strip, with pairwise set-separation and strip confinement.
Produced by `black_structure` (`Triangles.lean`); consumed by Cases 2–3 of
Proposition 7.8, whose sub-lemmas need the WHOLE family (whiteness of an exit
point requires separation from every OTHER triangle). -/
structure TriangleFamily (n ξ : ℕ) : Type where
  /-- the triangle parameters (apex `(j₀, l₀)`, size `s_Δ`) -/
  T : Set (ℕ × ℤ × ℝ)
  size_nonneg : ∀ t ∈ T, 0 ≤ t.2.2
  /-- every member is one of the canonical corner triangles from Lemma 7.4 -/
  canonical : ∀ t ∈ T, ∃ p : ℕ × ℤ, p.1 + 1 ≤ n / 2 ∧ black n ξ p.1 p.2 ∧
    t = cornerTriple n ξ p
  /-- the black strip is exactly the union of the triangles -/
  cover : {p : ℕ × ℤ | p.1 + 1 ≤ n / 2 ∧ black n ξ p.1 p.2}
    = ⋃ t ∈ T, triangle t.1 t.2.1 t.2.2
  /-- pairwise Euclidean set-separation by `(1/10)·log(1/ε)` (squared form) -/
  separated : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
    ∀ p ∈ triangle t.1 t.2.1 t.2.2, ∀ p' ∈ triangle t'.1 t'.2.1 t'.2.2,
    ((1 / 10 : ℝ) * Real.log (1 / (epsBW : ℝ))) ^ 2
      ≤ ((p.1 : ℝ) - p'.1) ^ 2 + ((p.2 : ℝ) - p'.2) ^ 2
  /-- confinement `j + 1 ≤ n/2 - (1/10)·log(1/ε)` for every triangle point -/
  confined : ∀ t ∈ T, ∀ p ∈ triangle t.1 t.2.1 t.2.2,
    (p.1 : ℝ) + 1 ≤ (n : ℝ) / 2 - (1 / 10 : ℝ) * Real.log (1 / (epsBW : ℝ))

/-- `black_structure` repackaged: a `TriangleFamily` exists. -/
theorem exists_triangleFamily (n ξ : ℕ) (hξ : ¬ 3 ∣ ξ) :
    Nonempty (TriangleFamily n ξ) := by
  obtain ⟨T, h0, hcanonical, h1, h2, h3⟩ := black_structure n ξ hξ
  exact ⟨⟨T, h0, hcanonical, h1, h2, h3⟩⟩

/-- **Big triangles have exponentially deep apexes** (lap 16, Option B probe;
true for ANY route): a family triangle of size `≥ S` has apex phase
`|θq(apex)| ≤ ε·e^{−S}`. Near-definitional: by `canonical` every member is a
`cornerTriple`, whose size is `log(ε/|θ*|)` by construction, so size `≥ S`
inverts to exactly this depth bound. -/
theorem bigTriangle_apex_deep {n ξ : ℕ} (hξ : ¬ 3 ∣ ξ) (F : TriangleFamily n ξ)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ F.T) {S : ℝ} (hS : S ≤ t.2.2) :
    |(θq n ξ t.1 t.2.1 : ℝ)| ≤ (epsBW : ℝ) * Real.exp (-S) := by
  obtain ⟨p, hps, hpb, rfl⟩ := F.canonical t ht
  have h2j : 2 * p.1 + 1 ≤ n := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hps
    omega
  have hθpos : (0:ℝ) < |(θq n ξ (jstar n ξ p.1 p.2) (lstar n ξ p.1 p.2) : ℝ)| := by
    exact_mod_cast corner_phase_pos hξ h2j
  have hε : (0:ℝ) < (epsBW : ℝ) := by
    have h : (0:ℚ) < epsBW := by unfold epsBW; norm_num
    exact_mod_cast h
  simp only [cornerTriple] at hS ⊢
  have hexp : Real.exp S ≤ (epsBW : ℝ)
      / |(θq n ξ (jstar n ξ p.1 p.2) (lstar n ξ p.1 p.2) : ℝ)| := by
    have h := Real.exp_le_exp.mpr hS
    rwa [Real.exp_log (by positivity)] at h
  have h1 : |(θq n ξ (jstar n ξ p.1 p.2) (lstar n ξ p.1 p.2) : ℝ)| * Real.exp S
      ≤ (epsBW : ℝ) := by
    calc |(θq n ξ (jstar n ξ p.1 p.2) (lstar n ξ p.1 p.2) : ℝ)| * Real.exp S
        ≤ |(θq n ξ (jstar n ξ p.1 p.2) (lstar n ξ p.1 p.2) : ℝ)|
            * ((epsBW : ℝ)
              / |(θq n ξ (jstar n ξ p.1 p.2) (lstar n ξ p.1 p.2) : ℝ)|) :=
          mul_le_mul_of_nonneg_left hexp hθpos.le
      _ = (epsBW : ℝ) := mul_div_cancel₀ _ (ne_of_gt hθpos)
  calc |(θq n ξ (jstar n ξ p.1 p.2) (lstar n ξ p.1 p.2) : ℝ)|
      = |(θq n ξ (jstar n ξ p.1 p.2) (lstar n ξ p.1 p.2) : ℝ)|
        * Real.exp S * Real.exp (-S) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ (epsBW : ℝ) * Real.exp (-S) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-- The white points of the strip `j ≤ ⌊n/2⌋` (renewal coordinates). Case 2's
white-exit gain ((7.47)) only counts endpoints that are white AND still inside
the strip: beyond the strip edge `Q ≡ 1` and no damping is available. -/
def whiteStrip (n ξ : ℕ) : Set (ℕ × ℤ) := {p | p.1 ≤ n / 2 ∧ p ∈ whiteSet n ξ}

/-- The (7.46) depth-weight factor at a first-passage endpoint `e` (renewal
start `(⌊n/2⌋-m, l)`): one further `Hold` step lands at depth `m - e₁ - d₁`
from the far edge, contributing `max(m - e₁ - d₁, 1)^{-A}` against `Q_{m-1}`. -/
noncomputable def edgeWeight (A : ℝ) (m : ℕ) (e : ℕ × ℤ) : ℝ :=
  ∑' d : ℕ × ℤ, (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)

theorem edgeWeight_nonneg (A : ℝ) (m : ℕ) (e : ℕ × ℤ) : 0 ≤ edgeWeight A m e :=
  tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Past the far edge (`e₁ > m`) every landing weight is `1`, so
`edgeWeight = 1`. -/
theorem edgeWeight_of_deep (A : ℝ) {m : ℕ} {e : ℕ × ℤ} (he : m < e.1) :
    edgeWeight A m e = 1 := by
  unfold edgeWeight
  have h1 : ∀ d : ℕ × ℤ,
      (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)
        = (hold d).toReal := by
    intro d
    have h0 : m - e.1 - d.1 = 0 := by omega
    rw [h0]
    simp [Real.one_rpow]
  rw [tsum_congr h1, hold_tsum_toReal]

/-- `Qm ≥ 1`: the sup ranges over points past the strip edge, where the weight
is `1` and `Q = 1` (boundary). Needed to absorb out-of-strip endpoints. -/
theorem one_le_Qm (half n ξ : ℕ) (ε A : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε) (m : ℕ) :
    1 ≤ Qm half n ξ ε A m := by
  have h := le_Qm half n ξ ε A hA hε m (p1 := half + 1) (l := 0)
    (by omega) (by omega)
  have hw : (max (half - (half + 1)) 1 : ℕ) = 1 := by omega
  rw [hw, Q_boundary _ _ _ _ _ (by omega)] at h
  simpa using h

/-- **The (7.46) endpoint step** (one application of (7.35)+(7.38) at the
first-passage endpoint, paper p.47): the renewal value at endpoint
`(⌊n/2⌋-m+e₁, l+e₂)` is bounded by `edgeWeight · Q_{m-1}`, GAINING the factor
`exp(-ε³)` when the endpoint is white-in-strip. Stated in the subtraction-free
form `1 - (1 - e^{-ε³})·1_{whiteStrip}` consumed by the (7.47) split. -/
theorem Q_fp_endpoint_le (n ξ : ℕ) (ε A : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n / 2) (l : ℤ) (e : ℕ × ℤ) :
    Q (n / 2) (whiteSet n ξ) ε (n / 2 - m + e.1) (l + e.2)
      ≤ (1 - (1 - Real.exp (-ε ^ 3))
            * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2))
        * (edgeWeight A m e * Qm (n / 2) n ξ ε A (m - 1)) := by
  set half := n / 2 with hhalf
  set j' := half - m + e.1 with hj'
  set QM := Qm half n ξ ε A (m - 1) with hQM
  have hQM0 : 0 ≤ QM := Qm_nonneg _ _ _ _ _ _
  have hQM1 : 1 ≤ QM := one_le_Qm _ _ _ _ _ hA hε _
  rcases Nat.lt_or_ge half j' with hout | hin
  · -- past the strip edge: LHS = 1, indicator = 0, edgeWeight = 1, QM ≥ 1
    rw [Q_boundary _ _ _ _ _ hout,
      Set.indicator_of_notMem (fun hmem => absurd hmem.1 (by omega)) 1,
      mul_zero, sub_zero, one_mul, edgeWeight_of_deep A (by omega), one_mul]
    exact hQM1
  · -- in strip: one Q_rec step, per-atom Q_le_Qm at depth m-1
    rw [Q_rec _ _ _ _ _ hin]
    have hatom : ∀ d : ℕ × ℤ,
        (hold d).toReal * Q half (whiteSet n ξ) ε (j' + d.1) (l + e.2 + d.2)
          ≤ (hold d).toReal * (((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) := by
      intro d
      rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
      · rw [hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul, zero_mul]
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have h1 : 1 ≤ j' + d.1 := by omega
        have h2 : half - (m - 1) ≤ j' + d.1 := by omega
        have hkey := Q_le_Qm half n ξ ε A hA hε (m - 1)
          (l := l + e.2 + d.2) h1 h2
        have heq : half - (j' + d.1) = m - e.1 - d.1 := by omega
        rwa [heq] at hkey
    have hwle : ∀ d : ℕ × ℤ,
        (hold d).toReal * (((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM)
          ≤ (hold d).toReal * QM := by
      intro d
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      calc ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM
          ≤ 1 * QM := mul_le_mul_of_nonneg_right
            (Real.rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast Nat.le_max_right (m - e.1 - d.1) 1)
              (by linarith)) hQM0
        _ = QM := one_mul _
    have hsumR : Summable fun d : ℕ × ℤ =>
        (hold d).toReal * (((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg
          (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hQM0))
        hwle (hold_summable_toReal.mul_right QM)
    have hsumL : Summable fun d : ℕ × ℤ =>
        (hold d).toReal * Q half (whiteSet n ξ) ε (j' + d.1) (l + e.2 + d.2) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (Q_nonneg _ _ _ _ _))
        (fun d => (hatom d).trans (hwle d)) (hold_summable_toReal.mul_right QM)
    have htsum : ∑' d : ℕ × ℤ,
        (hold d).toReal * Q half (whiteSet n ξ) ε (j' + d.1) (l + e.2 + d.2)
          ≤ edgeWeight A m e * QM := by
      calc ∑' d : ℕ × ℤ,
          (hold d).toReal * Q half (whiteSet n ξ) ε (j' + d.1) (l + e.2 + d.2)
          ≤ ∑' d : ℕ × ℤ,
            (hold d).toReal * (((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
            hsumL.tsum_le_tsum hatom hsumR
        _ = ∑' d : ℕ × ℤ,
            ((hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)) * QM :=
            tsum_congr fun d => (mul_assoc _ _ _).symm
        _ = edgeWeight A m e * QM := tsum_mul_right
    have hS0 : 0 ≤ ∑' d : ℕ × ℤ,
        (hold d).toReal * Q half (whiteSet n ξ) ε (j' + d.1) (l + e.2 + d.2) :=
      tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Q_nonneg _ _ _ _ _)
    -- the damping factor matches the subtraction form exactly (in-strip)
    have hdamp : Real.exp (-ε ^ 3 * Set.indicator (whiteSet n ξ) 1 (j', l + e.2))
        = 1 - (1 - Real.exp (-ε ^ 3))
            * Set.indicator (whiteStrip n ξ) 1 (j', l + e.2) := by
      by_cases hw : (j', l + e.2) ∈ whiteSet n ξ
      · have e1 : Set.indicator (whiteSet n ξ) (1 : ℕ × ℤ → ℝ) (j', l + e.2) = 1 :=
          Set.indicator_of_mem hw 1
        have hmem : (j', l + e.2) ∈ whiteStrip n ξ := ⟨hin, hw⟩
        have e2 : Set.indicator (whiteStrip n ξ) (1 : ℕ × ℤ → ℝ) (j', l + e.2) = 1 :=
          Set.indicator_of_mem hmem 1
        rw [e1, e2, mul_one, mul_one]
        ring
      · have e1 : Set.indicator (whiteSet n ξ) (1 : ℕ × ℤ → ℝ) (j', l + e.2) = 0 :=
          Set.indicator_of_notMem hw 1
        have e2 : Set.indicator (whiteStrip n ξ) (1 : ℕ × ℤ → ℝ) (j', l + e.2) = 0 :=
          Set.indicator_of_notMem (fun hmem => hw hmem.2) 1
        rw [e1, e2, mul_zero, mul_zero, sub_zero, Real.exp_zero]
    calc Real.exp (-ε ^ 3 * Set.indicator (whiteSet n ξ) 1 (j', l + e.2)) *
          ∑' d : ℕ × ℤ,
            (hold d).toReal * Q half (whiteSet n ξ) ε (j' + d.1) (l + e.2 + d.2)
        ≤ Real.exp (-ε ^ 3 * Set.indicator (whiteSet n ξ) 1 (j', l + e.2))
            * (edgeWeight A m e * QM) :=
          mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
      _ = (1 - (1 - Real.exp (-ε ^ 3))
            * Set.indicator (whiteStrip n ξ) 1 (j', l + e.2))
            * (edgeWeight A m e * QM) := by rw [hdamp]

/-- **(7.42) concavity core**: for `A ≥ 0` and `0 ≤ x ≤ 1/2`,
`(1-x)^{-A} ≤ exp(2Ax)`.  This is the pointwise weight-degradation bound behind
`fpDist_edgeWeight_le`: with `x = J/m` the total `j`-advance fraction, the depth
weight `(m-J)^{-A} = m^{-A}(1-x)^{-A} ≤ m^{-A}·exp(2A·J/m)`, turning the average
depth weight into an MGF of `J` at tilt `2A/m`.  Route: `log(1-x) ≥ 1 - 1/(1-x)`
(`log_le_sub_one_of_pos` at `1/(1-x)`) gives `-log(1-x) ≤ x/(1-x) ≤ 2x`. -/
theorem one_sub_rpow_neg_le_exp {A x : ℝ} (hA : 0 ≤ A) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x) ^ (-A) ≤ Real.exp (2 * A * x) := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  rw [Real.rpow_def_of_pos h1x]
  apply Real.exp_le_exp.mpr
  have hlog : -Real.log (1 - x) ≤ 2 * x := by
    have hy : Real.log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero (by linarith), Real.log_one, zero_sub] at hy
    have hle : 1 / (1 - x) - 1 ≤ 2 * x := by
      rw [div_sub_one (by linarith)]
      rw [div_le_iff₀ h1x]; nlinarith
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog hA]

/-- **The (7.48) pointwise weight bound** (uniform, no region split).  For every
first-passage step `e` and hold step `d`, writing `J = e₁ + d₁` for the total
`j`-advance, the depth weight is dominated by an MGF term plus a hard tail:
`max(m − J, 1)^{−A} ≤ m^{−A}·exp(2A·J/m) + 1_{m < 2J}`.

This is the key that lets the double sum `∑ fpDist·edgeWeight` factor into an MGF
`m^{−A}·Z_{fp,fst}(2A/m)·Z_{hold,fst}(2A/m)` plus a large-deviation tail
`P(J > m/2)`, WITHOUT an inner `[J ≤ m/2]` region split (which would need a
Fubini/summability barrier).  In the main region `J ≤ m/2` (so `x = J/m ≤ 1/2`),
the concavity core `one_sub_rpow_neg_le_exp` gives the MGF term; in the tail the
weight is `≤ 1 ≤` the indicator.  Requires `m ≥ 2`. -/
theorem edgeWeight_summand_le {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 2 ≤ m)
    (e d : ℕ × ℤ) :
    ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)
      ≤ (m : ℝ) ^ (-A) * Real.exp (2 * A * ((e.1 + d.1 : ℕ) : ℝ) / (m : ℝ))
        + (if m < 2 * (e.1 + d.1) then (1 : ℝ) else 0) := by
  set J : ℕ := e.1 + d.1 with hJ
  have hmm : m - e.1 - d.1 = m - J := by rw [hJ, Nat.sub_sub]
  rw [hmm]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hexp_nonneg : (0 : ℝ) ≤ (m : ℝ) ^ (-A) * Real.exp (2 * A * (J : ℝ) / (m : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hmpos.le _) (Real.exp_pos _).le
  by_cases hbig : m < 2 * J
  · rw [if_pos hbig]
    have hle1 : ((max (m - J) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast Nat.le_max_right (m - J) 1) (by linarith)
    linarith
  · rw [if_neg hbig]
    push Not at hbig  -- `2 * J ≤ m`
    have hJm : J ≤ m := by omega
    have hmax : max (m - J) 1 = m - J := max_eq_left (by omega : (1 : ℕ) ≤ m - J)
    rw [hmax]
    have hcast : ((m - J : ℕ) : ℝ) = (m : ℝ) - (J : ℝ) := by
      rw [Nat.cast_sub hJm]
    have hx0 : (0 : ℝ) ≤ (J : ℝ) / m := by positivity
    have hx : (J : ℝ) / m ≤ 1 / 2 := by
      rw [div_le_iff₀ hmpos]
      have : (2 : ℝ) * J ≤ m := by exact_mod_cast hbig
      linarith
    have h1x : (0 : ℝ) ≤ 1 - (J : ℝ) / m := by linarith
    have hfactor : ((m : ℝ) - J) = (m : ℝ) * (1 - (J : ℝ) / m) := by
      field_simp
    have hsplit : ((m - J : ℕ) : ℝ) ^ (-A)
        = (m : ℝ) ^ (-A) * (1 - (J : ℝ) / m) ^ (-A) := by
      rw [hcast, hfactor, Real.mul_rpow hmpos.le h1x]
    rw [hsplit]
    have hconc := one_sub_rpow_neg_le_exp hA hx0 hx
    have hearg : 2 * A * ((J : ℝ) / m) = 2 * A * (J : ℝ) / m := by ring
    rw [hearg] at hconc
    have := mul_le_mul_of_nonneg_left hconc (Real.rpow_nonneg hmpos.le (-A))
    linarith

/-- Explicit threshold past which `log² m ≥ b` (witness of `log_sq_ge_of_large`,
reified — big-C campaign step 2). -/
noncomputable def T_logSq (b : ℝ) : ℕ := ⌈Real.exp (Real.sqrt (max b 0))⌉₊

/-- `log² m` exceeds `b` for all `m ≥ T_logSq b`, threshold-explicit form. -/
theorem log_sq_ge_at (b : ℝ) : ∀ m : ℕ, T_logSq b ≤ m → b ≤ Real.log m ^ 2 := by
  intro m hm
  unfold T_logSq at hm
  set r : ℝ := Real.sqrt (max b 0) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hexp_pos : 0 < Real.exp r := Real.exp_pos _
  have hmN : Real.exp r ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
  have hlogm : r ≤ Real.log m := by
    rw [← Real.log_exp r]; exact Real.log_le_log hexp_pos hmN
  calc b ≤ max b 0 := le_max_left _ _
    _ = r ^ 2 := (Real.sq_sqrt (le_max_right _ _)).symm
    _ ≤ Real.log m ^ 2 := pow_le_pow_left₀ hr0 hlogm 2

/-- `log_sq_ge_of_large`, original `∃`-form: delegates to `log_sq_ge_at` at `T_logSq b`. -/
theorem log_sq_ge_of_large (b : ℝ) : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → b ≤ Real.log m ^ 2 :=
  ⟨T_logSq b, log_sq_ge_at b⟩

/-- Explicit threshold past which `exp(−ρm) ≤ b` (witness of `exp_neg_mul_le_of_large`,
reified — big-C campaign step 2). -/
noncomputable def T_expNeg (ρ b : ℝ) : ℕ := ⌈Real.log b⁻¹ / ρ⌉₊

/-- `exp (-ρ m)` drops below `b` for all `m ≥ T_expNeg ρ b`, threshold-explicit form. -/
theorem exp_neg_mul_le_at (ρ : ℝ) (hρ : 0 < ρ) (b : ℝ) (hb : 0 < b) :
    ∀ m : ℕ, T_expNeg ρ b ≤ m → Real.exp (-ρ * m) ≤ b := by
  intro m hm
  unfold T_expNeg at hm
  have hx : Real.log b⁻¹ / ρ ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
  have hρm : Real.log b⁻¹ ≤ (m : ℝ) * ρ := by
    have h := mul_le_mul_of_nonneg_right hx hρ.le
    rwa [div_mul_cancel₀ _ hρ.ne'] at h
  have hfin : -ρ * (m : ℝ) ≤ Real.log b := by rw [Real.log_inv] at hρm; nlinarith [hρm]
  calc Real.exp (-ρ * (m : ℝ)) ≤ Real.exp (Real.log b) := Real.exp_le_exp.mpr hfin
    _ = b := Real.exp_log hb

/-- `exp_neg_mul_le_of_large`, original `∃`-form: delegates to `exp_neg_mul_le_at`. -/
theorem exp_neg_mul_le_of_large (ρ : ℝ) (hρ : 0 < ρ) (b : ℝ) (hb : 0 < b) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → Real.exp (-ρ * m) ≤ b :=
  ⟨T_expNeg ρ b, exp_neg_mul_le_at ρ hρ b hb⟩

/-- Explicit threshold past which `log m ≤ ε·m` (witness of `log_le_eps_mul_of_large`,
reified — big-C campaign step 2). -/
noncomputable def T_logLin (ε : ℝ) : ℕ := ⌈(2 / ε) ^ 2⌉₊ + 1

/-- `log m ≤ ε·m` for all `m ≥ T_logLin ε`, threshold-explicit form (`log` is sublinear;
proof via `log m ≤ 2√m` and `√m ≥ 2/ε`). -/
theorem log_le_eps_mul_at (ε : ℝ) (hε : 0 < ε) :
    ∀ m : ℕ, T_logLin ε ≤ m → Real.log m ≤ ε * m := by
  intro m hm
  unfold T_logLin at hm
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
  -- log m ≤ 2√m
  have hlog_le : Real.log m ≤ 2 * Real.sqrt m := by
    calc Real.log m = Real.log (Real.sqrt m ^ 2) := by rw [hsq]
      _ = 2 * Real.log (Real.sqrt m) := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 2 * (Real.sqrt m - 1) := by
          have := Real.log_le_sub_one_of_pos hsqrt_pos; linarith
      _ ≤ 2 * Real.sqrt m := by linarith [hsqrt_pos.le]
  -- √m ≥ 2/ε
  have hsqrt_lb : 2 / ε ≤ Real.sqrt m := by
    have hx : ((2 / ε) ^ 2 : ℝ) ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈(2 / ε) ^ 2⌉₊ ≤ m))
    calc 2 / ε = Real.sqrt ((2 / ε) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt m := Real.sqrt_le_sqrt hx
  -- combine: 2√m ≤ ε·m
  have hcomb : 2 * Real.sqrt m ≤ ε * m := by
    have h1 : (2 : ℝ) ≤ ε * Real.sqrt m := by
      have := mul_le_mul_of_nonneg_left hsqrt_lb hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    calc 2 * Real.sqrt m ≤ (ε * Real.sqrt m) * Real.sqrt m :=
          mul_le_mul_of_nonneg_right h1 hsqrt_pos.le
      _ = ε * (Real.sqrt m ^ 2) := by ring
      _ = ε * m := by rw [hsq]
  linarith

/-- `log_le_eps_mul_of_large`, original `∃`-form: delegates to `log_le_eps_mul_at`. -/
theorem log_le_eps_mul_of_large (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → Real.log m ≤ ε * m :=
  ⟨T_logLin ε, log_le_eps_mul_at ε hε⟩

/-- **`fpDist_fst_mgf_le` threshold**, symbolic (big-C campaign, step 2):
`25 + N₁ + N₃ + N₈₅ + N₄` of `fpDist_fst_mgf_numeric` at (`A, δ, c, C'`). -/
noncomputable def T_mgfNumeric (A δ c C' : ℝ) : ℕ :=
  25 + ⌈2 * A / (min c (c ^ 2 / 20) / 2)⌉₊ + ⌈50 * A / Real.log (1 + δ / 2)⌉₊
    + T_logSq (max (max (2 * A * Real.log 2 / (Real.log (1 + δ / 2) * Real.log 9))
        (A / Real.log (1 + δ / 2))) 1)
    + T_expNeg (min (c ^ 2 / 40) (c / 2) * Real.log (1 + δ / 2) / (4 * A))
        (δ / (2 * (C' * Real.exp (A / 2)
          * (1 / (1 - Real.exp (-(c ^ 2 / 40))) + 1 / (1 - Real.exp (-(c / 2)))))))

set_option maxHeartbeats 4000000 in
/-- Numeric core of `fpDist_fst_mgf_le`, `_at` sibling at the explicit threshold `T_mgfNumeric` (big-C campaign, step 2) — the explicit threshold `Cthr` and the
per-`(m,s)` split point `K` bundling all the constant-juggling estimates that the
mechanical Fubini/split assembly consumes.  With `θ = 2A/m` and
`K = ⌊m·log(1+δ/2)/(2A)⌋` this asserts: (a) the tilt lands in `gaussExp_col_tail`'s
range `θ ≤ ½·min(c, c²/20)`; (b) the `gaussExp` cutoff budget `s·log2 ≤ (K+2)·log9`
(from `s ≤ m/log²m`, `K = Θ(m)`); (c) the bulk factor `exp(θK) ≤ 1+δ/2` (floor of
`K`); (d) the `gaussExp` tail RHS at cutoff `K` is `≤ δ/2` (super-exponential decay
`x₀ = K+1-s/4 = Θ(m)` beats the bounded prefactor `exp(θs/4) ≤ exp(A/2)`).

PROVED (axiom-clean) via `log_sq_ge_of_large` (budget + `x₀` bound) and
`exp_neg_mul_le_of_large` (the final tail decay); rates `a₂ = c²/20-θ ≥ c²/40`,
`a₁ = c-θ ≥ c/2` bound the geometric denominators; `Cthr = 25+N₁+N₃+N₈₅+N₄`. -/
theorem fpDist_fst_mgf_numeric_at {A δ c C' : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (hc : 0 < c) (hC' : 0 < C') :
    25 ≤ T_mgfNumeric A δ c C' ∧ ∀ m : ℕ, T_mgfNumeric A δ c C' ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∃ K : ℕ, 25 ≤ K ∧
        2 * A / (m : ℝ) ≤ min c (c ^ 2 / 20) / 2 ∧
        (s : ℝ) * Real.log 2 ≤ ((K : ℝ) + 2) * Real.log 9 ∧
        Real.exp (2 * A / (m : ℝ) * (K : ℝ)) ≤ 1 + δ / 2 ∧
        C' * Real.exp (2 * A / (m : ℝ) * ((s : ℝ) / 4))
          * (Real.exp (-(c ^ 2 / 20 - 2 * A / (m : ℝ)) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                / (1 - Real.exp (-(c ^ 2 / 20 - 2 * A / (m : ℝ))))
             + Real.exp (-(c - 2 * A / (m : ℝ)) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                / (1 - Real.exp (-(c - 2 * A / (m : ℝ))))) ≤ δ / 2 := by
  unfold T_mgfNumeric
  -- absolute constants
  set μ : ℝ := min c (c ^ 2 / 20) / 2 with hμdef
  have hμ : 0 < μ := by rw [hμdef]; have : 0 < min c (c ^ 2 / 20) := lt_min hc (by positivity); linarith
  have hμc : μ ≤ c / 2 := by rw [hμdef]; gcongr; exact min_le_left _ _
  have hμc2 : μ ≤ c ^ 2 / 40 := by
    rw [hμdef]; have : min c (c ^ 2 / 20) ≤ c ^ 2 / 20 := min_le_right _ _; linarith
  set L : ℝ := Real.log (1 + δ / 2) with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  -- decay rate and denominators
  set d₂ : ℝ := 1 - Real.exp (-(c ^ 2 / 40)) with hd2def
  set d₁ : ℝ := 1 - Real.exp (-(c / 2)) with hd1def
  have hd2 : 0 < d₂ := by
    rw [hd2def]; have : Real.exp (-(c ^ 2 / 40)) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
    linarith
  have hd1 : 0 < d₁ := by
    rw [hd1def]; have : Real.exp (-(c / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  set ρ : ℝ := min (c ^ 2 / 40) (c / 2) * L / (4 * A) with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]; have : 0 < min (c ^ 2 / 40) (c / 2) := lt_min (by positivity) (by positivity)
    positivity
  set Q : ℝ := C' * Real.exp (A / 2) * (1 / d₂ + 1 / d₁) with hQdef
  have hQ : 0 < Q := by rw [hQdef]; positivity
  -- thresholds
  set N85 : ℕ := T_logSq (max (max (2 * A * Real.log 2 / (L * Real.log 9)) (A / L)) 1)
    with hN85def
  have hN85 := log_sq_ge_at (max (max (2 * A * Real.log 2 / (L * Real.log 9)) (A / L)) 1)
  set N4 : ℕ := T_expNeg ρ (δ / (2 * Q)) with hN4def
  have hN4 := exp_neg_mul_le_at ρ hρ (δ / (2 * Q)) (by positivity)
  set N1 : ℕ := ⌈2 * A / μ⌉₊ with hN1def
  set N3 : ℕ := ⌈50 * A / L⌉₊ with hN3def
  refine ⟨by omega, fun m hm s hs => ?_⟩
  -- unpack the threshold
  have hm25 : 25 ≤ m := by omega
  have hmN1 : N1 ≤ m := by omega
  have hmN3 : N3 ≤ m := by omega
  have hmN85 : N85 ≤ m := by omega
  have hmN4 : N4 ≤ m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  set θ : ℝ := 2 * A / (m : ℝ) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθnn : 0 ≤ θ := hθpos.le
  -- log m facts
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlogsq_pos : 0 < Real.log m ^ 2 := by positivity
  have hlogsq := hN85 m hmN85
  have hb3 : 2 * A * Real.log 2 / (L * Real.log 9) ≤ Real.log m ^ 2 :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlogsq
  have hb4 : A / L ≤ Real.log m ^ 2 :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlogsq
  have hb1 : (1 : ℝ) ≤ Real.log m ^ 2 := le_trans (le_max_right _ _) hlogsq
  -- (E1) θ ≤ μ
  have hθμ : θ ≤ μ := by
    rw [hθdef, div_le_iff₀ hmpos]
    have hm1 : (2 * A / μ) ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hmN1)
    have : 2 * A = μ * (2 * A / μ) := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left hm1 hμ.le
  -- the split point K
  set κ : ℝ := (m : ℝ) * L / (2 * A) with hκdef
  have hκnn : 0 ≤ κ := by rw [hκdef]; positivity
  set K : ℕ := ⌊κ⌋₊ with hKdef
  have hKle : (K : ℝ) ≤ κ := Nat.floor_le hκnn
  have hKlb : κ - 1 ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one κ; rw [← hKdef] at this; linarith
  refine ⟨K, ?_, hθμ, ?_, ?_, ?_⟩
  · -- 25 ≤ K
    rw [hKdef]; apply Nat.le_floor
    have hm50 : (50 * A / L) ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hmN3)
    have hmL : 50 * A ≤ (m : ℝ) * L := by
      have h := mul_le_mul_of_nonneg_right hm50 hL.le
      rwa [div_mul_cancel₀ _ hL.ne'] at h
    rw [hκdef, le_div_iff₀ (by positivity : (0:ℝ) < 2 * A)]
    push_cast; linarith
  · -- (E3) budget: s·log2 ≤ (K+2)·log9
    have hb3' : 2 * A * Real.log 2 ≤ Real.log m ^ 2 * (L * Real.log 9) := by
      rw [div_le_iff₀ (by positivity)] at hb3; linarith
    have hstep1 : (s : ℝ) * Real.log 2 ≤ ((m : ℝ) / Real.log m ^ 2) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hs hlog2.le
    have hstep2 : ((m : ℝ) / Real.log m ^ 2) * Real.log 2 ≤ κ * Real.log 9 := by
      rw [hκdef,
        show ((m:ℝ)/Real.log m^2)*Real.log 2 = ((m:ℝ)*Real.log 2)/Real.log m^2 by ring,
        show ((m:ℝ)*L/(2*A))*Real.log 9 = ((m:ℝ)*L*Real.log 9)/(2*A) by ring,
        div_le_div_iff₀ hlogsq_pos (by positivity : (0:ℝ) < 2*A)]
      nlinarith [mul_le_mul_of_nonneg_left hb3' hmpos.le]
    have hstep3 : κ * Real.log 9 ≤ ((K : ℝ) + 2) * Real.log 9 :=
      mul_le_mul_of_nonneg_right (by linarith) hlog9.le
    linarith
  · -- (E2) bulk: exp(θK) ≤ 1+δ/2
    have hθK : θ * (K : ℝ) ≤ L := by
      have h1 : θ * (K : ℝ) ≤ θ * κ := mul_le_mul_of_nonneg_left hKle hθnn
      have h2 : θ * κ = L := by rw [hθdef, hκdef]; field_simp
      linarith
    calc Real.exp (θ * (K : ℝ)) ≤ Real.exp L := Real.exp_le_exp.mpr hθK
      _ = 1 + δ / 2 := by rw [hLdef]; exact Real.exp_log (by linarith)
  · -- (E4) tail ≤ δ/2
    set x₀ : ℝ := ((K : ℝ) + 1) - (s : ℝ) / 4 with hx0def
    have hs4 : (s : ℝ) / 4 ≤ (m : ℝ) / (4 * Real.log m ^ 2) := by
      rw [show (m:ℝ)/(4*Real.log m^2) = ((m:ℝ)/Real.log m^2)/4 by ring]
      linarith [hs]
    -- x₀ ≥ κ - s/4 ≥ m L/(4A) (uses log²m ≥ A/L)
    have hx0lb : (m : ℝ) * L / (4 * A) ≤ x₀ := by
      rw [hx0def]
      have hx1 : κ ≤ (K : ℝ) + 1 := by linarith
      have hsmall : (m : ℝ) / (4 * Real.log m ^ 2) ≤ (m : ℝ) * L / (4 * A) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : A ≤ L * Real.log m ^ 2 := by
          rw [div_le_iff₀ hL] at hb4; linarith
        nlinarith [this, hmpos.le]
      have hκval : κ = (m : ℝ) * L / (2 * A) := hκdef
      have : (m : ℝ) * L / (4 * A) ≤ κ - (s : ℝ) / 4 := by
        have hh : (s : ℝ) / 4 ≤ (m : ℝ) * L / (4 * A) := le_trans hs4 hsmall
        have h2 : κ - (m:ℝ)*L/(4*A) = (m:ℝ)*L/(4*A) := by rw [hκval]; ring
        linarith
      linarith
    have hx0pos : 0 < x₀ := lt_of_lt_of_le (by positivity) hx0lb
    -- rates
    have ha2 : c ^ 2 / 40 ≤ c ^ 2 / 20 - θ := by linarith [hθμ, hμc2]
    have ha1 : c / 2 ≤ c - θ := by linarith [hθμ, hμc]
    have ha2pos : 0 < c ^ 2 / 20 - θ := lt_of_lt_of_le (by positivity) ha2
    have ha1pos : 0 < c - θ := lt_of_lt_of_le (by positivity) ha1
    -- prefactor: exp(θ s/4) ≤ exp(A/2)
    have hpre : Real.exp (θ * ((s : ℝ) / 4)) ≤ Real.exp (A / 2) := by
      apply Real.exp_le_exp.mpr
      have hθs : θ * ((s : ℝ) / 4) ≤ A / (2 * Real.log m ^ 2) := by
        have hsm : (s : ℝ) * Real.log m ^ 2 ≤ (m : ℝ) := by
          have h := mul_le_mul_of_nonneg_right hs hlogsq_pos.le
          rwa [div_mul_cancel₀ _ hlogsq_pos.ne'] at h
        have hkey : (s : ℝ) / (m : ℝ) ≤ 1 / Real.log m ^ 2 := by
          rw [div_le_div_iff₀ hmpos hlogsq_pos]; nlinarith [hsm]
        have e1 : θ * ((s : ℝ) / 4) = (A / 2) * ((s : ℝ) / (m : ℝ)) := by rw [hθdef]; ring
        have e2 : A / (2 * Real.log m ^ 2) = (A / 2) * (1 / Real.log m ^ 2) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left hkey (by positivity)
      have hle2 : A / (2 * Real.log m ^ 2) ≤ A / 2 :=
        div_le_div_of_nonneg_left hA.le (by norm_num) (by nlinarith [hb1])
      linarith
    -- denominators: 1/(1-exp(-a)) ≤ 1/d
    have hden2 : 1 / (1 - Real.exp (-(c ^ 2 / 20 - θ))) ≤ 1 / d₂ := by
      apply one_div_le_one_div_of_le hd2
      rw [hd2def]
      have : Real.exp (-(c ^ 2 / 20 - θ)) ≤ Real.exp (-(c ^ 2 / 40)) :=
        Real.exp_le_exp.mpr (by linarith [ha2])
      linarith
    have hden1 : 1 / (1 - Real.exp (-(c - θ))) ≤ 1 / d₁ := by
      apply one_div_le_one_div_of_le hd1
      rw [hd1def]
      have : Real.exp (-(c - θ)) ≤ Real.exp (-(c / 2)) := Real.exp_le_exp.mpr (by linarith [ha1])
      linarith
    have hden2pos : 0 < 1 - Real.exp (-(c ^ 2 / 20 - θ)) := by
      have : Real.exp (-(c ^ 2 / 20 - θ)) < 1 := by rw [Real.exp_lt_one_iff]; linarith [ha2pos]
      linarith
    have hden1pos : 0 < 1 - Real.exp (-(c - θ)) := by
      have : Real.exp (-(c - θ)) < 1 := by rw [Real.exp_lt_one_iff]; linarith [ha1pos]
      linarith
    -- numerators: exp(-a x₀) ≤ exp(-ρ m)
    have hnum2 : Real.exp (-(c ^ 2 / 20 - θ) * x₀) ≤ Real.exp (-ρ * m) := by
      apply Real.exp_le_exp.mpr
      have hrate : ρ ≤ (c ^ 2 / 40) * L / (4 * A) := by
        rw [hρdef]; gcongr; exact min_le_left _ _
      have hprod : ρ * (m : ℝ) ≤ (c ^ 2 / 20 - θ) * x₀ := by
        calc ρ * (m : ℝ) ≤ (c ^ 2 / 40) * L / (4 * A) * (m : ℝ) :=
              mul_le_mul_of_nonneg_right hrate hmpos.le
          _ = (c ^ 2 / 40) * ((m : ℝ) * L / (4 * A)) := by ring
          _ ≤ (c ^ 2 / 20 - θ) * x₀ :=
              mul_le_mul ha2 hx0lb (by positivity) ha2pos.le
      nlinarith [hprod]
    have hnum1 : Real.exp (-(c - θ) * x₀) ≤ Real.exp (-ρ * m) := by
      apply Real.exp_le_exp.mpr
      have hrate : ρ ≤ (c / 2) * L / (4 * A) := by
        rw [hρdef]; gcongr; exact min_le_right _ _
      have hprod : ρ * (m : ℝ) ≤ (c - θ) * x₀ := by
        calc ρ * (m : ℝ) ≤ (c / 2) * L / (4 * A) * (m : ℝ) :=
              mul_le_mul_of_nonneg_right hrate hmpos.le
          _ = (c / 2) * ((m : ℝ) * L / (4 * A)) := by ring
          _ ≤ (c - θ) * x₀ := mul_le_mul ha1 hx0lb (by positivity) ha1pos.le
      nlinarith [hprod]
    -- assemble each term ≤ exp(-ρm)/d, sum, then prefactor
    have hterm2 : Real.exp (-(c ^ 2 / 20 - θ) * x₀) / (1 - Real.exp (-(c ^ 2 / 20 - θ)))
        ≤ Real.exp (-ρ * m) * (1 / d₂) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hnum2 hden2 (one_div_nonneg.mpr hden2pos.le) (Real.exp_pos _).le
    have hterm1 : Real.exp (-(c - θ) * x₀) / (1 - Real.exp (-(c - θ)))
        ≤ Real.exp (-ρ * m) * (1 / d₁) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hnum1 hden1 (one_div_nonneg.mpr hden1pos.le) (Real.exp_pos _).le
    have hsum : Real.exp (-(c ^ 2 / 20 - θ) * x₀) / (1 - Real.exp (-(c ^ 2 / 20 - θ)))
        + Real.exp (-(c - θ) * x₀) / (1 - Real.exp (-(c - θ)))
        ≤ Real.exp (-ρ * m) * (1 / d₂ + 1 / d₁) := by
      have := add_le_add hterm2 hterm1; rw [mul_add]; linarith [this]
    have hsumnn : 0 ≤ Real.exp (-(c ^ 2 / 20 - θ) * x₀) / (1 - Real.exp (-(c ^ 2 / 20 - θ)))
        + Real.exp (-(c - θ) * x₀) / (1 - Real.exp (-(c - θ))) :=
      add_nonneg (div_nonneg (Real.exp_pos _).le hden2pos.le)
        (div_nonneg (Real.exp_pos _).le hden1pos.le)
    have hfinal : C' * Real.exp (θ * ((s : ℝ) / 4))
        * (Real.exp (-(c ^ 2 / 20 - θ) * x₀) / (1 - Real.exp (-(c ^ 2 / 20 - θ)))
           + Real.exp (-(c - θ) * x₀) / (1 - Real.exp (-(c - θ))))
        ≤ Q * Real.exp (-ρ * m) := by
      have h1 : C' * Real.exp (θ * ((s : ℝ) / 4)) ≤ C' * Real.exp (A / 2) :=
        mul_le_mul_of_nonneg_left hpre hC'.le
      calc C' * Real.exp (θ * ((s : ℝ) / 4))
            * (Real.exp (-(c ^ 2 / 20 - θ) * x₀) / (1 - Real.exp (-(c ^ 2 / 20 - θ)))
               + Real.exp (-(c - θ) * x₀) / (1 - Real.exp (-(c - θ))))
          ≤ C' * Real.exp (A / 2) * (Real.exp (-ρ * m) * (1 / d₂ + 1 / d₁)) :=
            mul_le_mul h1 hsum hsumnn (by positivity)
        _ = Q * Real.exp (-ρ * m) := by rw [hQdef]; ring
    have hlast : Q * Real.exp (-ρ * m) ≤ δ / 2 := by
      have h := hN4 m hmN4
      calc Q * Real.exp (-ρ * m) ≤ Q * (δ / (2 * Q)) :=
            mul_le_mul_of_nonneg_left h hQ.le
        _ = δ / 2 := by field_simp
    exact le_trans hfinal hlast

/-- **Numeric core of `fpDist_fst_mgf_le`** — the explicit threshold `Cthr` and the
per-`(m,s)` split point `K` bundling all the constant-juggling estimates that the
mechanical Fubini/split assembly consumes.  With `θ = 2A/m` and
`K = ⌊m·log(1+δ/2)/(2A)⌋` this asserts: (a) the tilt lands in `gaussExp_col_tail`'s
range `θ ≤ ½·min(c, c²/20)`; (b) the `gaussExp` cutoff budget `s·log2 ≤ (K+2)·log9`
(from `s ≤ m/log²m`, `K = Θ(m)`); (c) the bulk factor `exp(θK) ≤ 1+δ/2` (floor of
`K`); (d) the `gaussExp` tail RHS at cutoff `K` is `≤ δ/2` (super-exponential decay
`x₀ = K+1-s/4 = Θ(m)` beats the bounded prefactor `exp(θs/4) ≤ exp(A/2)`).

PROVED (axiom-clean) via `log_sq_ge_of_large` (budget + `x₀` bound) and
`exp_neg_mul_le_of_large` (the final tail decay); rates `a₂ = c²/20-θ ≥ c²/40`,
`a₁ = c-θ ≥ c/2` bound the geometric denominators; `Cthr = 25+N₁+N₃+N₈₅+N₄`. -/
theorem fpDist_fst_mgf_numeric {A δ c C' : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (hc : 0 < c) (hC' : 0 < C') :
    ∃ Cthr : ℕ, 25 ≤ Cthr ∧ ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∃ K : ℕ, 25 ≤ K ∧
        2 * A / (m : ℝ) ≤ min c (c ^ 2 / 20) / 2 ∧
        (s : ℝ) * Real.log 2 ≤ ((K : ℝ) + 2) * Real.log 9 ∧
        Real.exp (2 * A / (m : ℝ) * (K : ℝ)) ≤ 1 + δ / 2 ∧
        C' * Real.exp (2 * A / (m : ℝ) * ((s : ℝ) / 4))
          * (Real.exp (-(c ^ 2 / 20 - 2 * A / (m : ℝ)) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                / (1 - Real.exp (-(c ^ 2 / 20 - 2 * A / (m : ℝ))))
             + Real.exp (-(c - 2 * A / (m : ℝ)) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                / (1 - Real.exp (-(c - 2 * A / (m : ℝ))))) ≤ δ / 2 :=
  ⟨T_mgfNumeric A δ c C', fpDist_fst_mgf_numeric_at hA hδ hc hC'⟩

/-- **Reusable first-coordinate `fpDist` MGF envelope** — the Fubini + `gaussExp`
envelope core shared by `fpDist_fst_mgf_le` (vanishing tilt `θ = 2A/m`) and
`fpDist_fst_tail_le` (fixed tilt `θ₀ = Θ(1)`).  For ANY admissible tilt
`0 ≤ θ ≤ ½·min(c, c²/20)`, cutoff `K ≥ 25`, and budget `s·log2 ≤ (K+2)·log9`, the
first-coordinate MGF is summable and splits as `bulk ≤ exp(θK)` (probability mass 1
on `e.1 ≤ K`) plus the `gaussExp_col_tail` envelope on `e.1 > K`.  Both callers then
pin the two pieces numerically. -/
theorem fpDist_fst_mgf_general {c C' : ℝ} (hc : 0 < c) (hC' : 0 < C')
    (hcol : ∀ s j : ℕ, ∑' l : ℤ, (fpDist s (j, l)).toReal
        ≤ C' * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4))
                  / Real.sqrt (1 + (s : ℝ))))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθle : θ ≤ min c (c ^ 2 / 20) / 2) (s K : ℕ)
    (hK25 : 25 ≤ K) (hbud : (s : ℝ) * Real.log 2 ≤ ((K : ℝ) + 2) * Real.log 9) :
    Summable (fun e : ℕ × ℤ => (fpDist s e).toReal * Real.exp (θ * (e.1 : ℝ)))
    ∧ ∑' e : ℕ × ℤ, (fpDist s e).toReal * Real.exp (θ * (e.1 : ℝ))
      ≤ Real.exp (θ * (K : ℝ))
        + C' * Real.exp (θ * ((s : ℝ) / 4))
          * (Real.exp (-(c ^ 2 / 20 - θ) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                / (1 - Real.exp (-(c ^ 2 / 20 - θ)))
             + Real.exp (-(c - θ) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                / (1 - Real.exp (-(c - θ)))) := by
  set f : ℕ × ℤ → ℝ := fun e => (fpDist s e).toReal * Real.exp (θ * (e.1 : ℝ)) with hfdef
  set M : ℕ → ℝ := fun j => ∑' l : ℤ, (fpDist s (j, l)).toReal with hMdef
  have hMnn : ∀ j : ℕ, 0 ≤ M j := fun j => tsum_nonneg (fun _ => ENNReal.toReal_nonneg)
  have hfp2d : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal) :=
    ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
  have hfpcol : ∀ j : ℕ, Summable (fun l : ℤ => (fpDist s (j, l)).toReal) :=
    fun j => hfp2d.comp_injective (fun _ _ h => by simpa using h)
  have hfcol : ∀ j : ℕ, Summable (fun l : ℤ => f (j, l)) := by
    intro j; simp only [hfdef]; exact (hfpcol j).mul_right _
  have hg_eq : ∀ j : ℕ, (∑' l : ℤ, f (j, l)) = M j * Real.exp (θ * (j : ℝ)) := by
    intro j
    have hcongr : ∀ l : ℤ, f (j, l) = (fpDist s (j, l)).toReal * Real.exp (θ * (j : ℝ)) :=
      fun l => by simp only [hfdef]
    rw [tsum_congr hcongr, tsum_mul_right, hMdef]
  have hgnn : ∀ j : ℕ, 0 ≤ ∑' l : ℤ, f (j, l) :=
    fun j => tsum_nonneg (fun l => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
  set U : ℕ → ℝ := fun j =>
    (if j ≤ K then Real.exp (θ * (K : ℝ)) * M j else 0)
      + (if K < j then Real.exp (θ * (j : ℝ)) *
          (C' * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4))
                  / Real.sqrt (1 + (s : ℝ)))) else 0) with hUdef
  obtain ⟨hsumT, hleT⟩ := gaussExp_col_tail hc hC'.le hθle s K hK25 hbud
  have hbulksum : Summable
      (fun j : ℕ => if j ≤ K then Real.exp (θ * (K : ℝ)) * M j else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range (K + 1)) (fun j hj => ?_)
    have hnle : ¬ j ≤ K := by simp only [Finset.mem_range, not_lt] at hj; omega
    rw [if_neg hnle]
  have hUsum : Summable U := hbulksum.add hsumT
  have hgU : ∀ j : ℕ, (∑' l : ℤ, f (j, l)) ≤ U j := by
    intro j
    rw [hg_eq j]
    simp only [hUdef]
    by_cases hjK : j ≤ K
    · rw [if_pos hjK, if_neg (by omega : ¬ K < j), add_zero]
      have hle : Real.exp (θ * (j : ℝ)) ≤ Real.exp (θ * (K : ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjK) hθ0
      calc M j * Real.exp (θ * (j : ℝ)) ≤ M j * Real.exp (θ * (K : ℝ)) :=
            mul_le_mul_of_nonneg_left hle (hMnn j)
        _ = Real.exp (θ * (K : ℝ)) * M j := mul_comm _ _
    · rw [if_neg hjK, if_pos (by omega : K < j), zero_add]
      have hMenv : M j ≤ C' * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4))
          / Real.sqrt (1 + (s : ℝ))) := by rw [hMdef]; exact hcol s j
      calc M j * Real.exp (θ * (j : ℝ)) = Real.exp (θ * (j : ℝ)) * M j := mul_comm _ _
        _ ≤ Real.exp (θ * (j : ℝ)) * (C' * (Gweight (1 + (s : ℝ))
              (c * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt (1 + (s : ℝ)))) :=
            mul_le_mul_of_nonneg_left hMenv (Real.exp_pos _).le
  have hfsum : Summable f :=
    (summable_prod_of_nonneg
        (fun e => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)).mpr
      ⟨hfcol, Summable.of_nonneg_of_le hgnn hgU hUsum⟩
  refine ⟨hfsum, ?_⟩
  rw [Summable.tsum_prod' hfsum hfcol]
  have hMsum : Summable M :=
    ((summable_prod_of_nonneg (fun _ => ENNReal.toReal_nonneg)).mp hfp2d).2
  have hmassM : ∑' j : ℕ, M j = 1 := by
    have hfpmass : ∑' e : ℕ × ℤ, (fpDist s e).toReal = 1 := by
      rw [← ENNReal.tsum_toReal_eq (fun e => PMF.apply_ne_top _ _), (fpDist s).tsum_coe,
        ENNReal.toReal_one]
    simp only [hMdef]
    rw [← Summable.tsum_prod' hfp2d hfpcol, hfpmass]
  have hindsum : Summable (fun j : ℕ => if j ≤ K then M j else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range (K + 1)) (fun j hj => ?_)
    have hnle : ¬ j ≤ K := by simp only [Finset.mem_range, not_lt] at hj; omega
    rw [if_neg hnle]
  have hindptw : ∀ j : ℕ, (if j ≤ K then M j else 0) ≤ M j := by
    intro j; by_cases h : j ≤ K
    · rw [if_pos h]
    · rw [if_neg h]; exact hMnn j
  have hindle : (∑' j : ℕ, if j ≤ K then M j else 0) ≤ ∑' j : ℕ, M j :=
    Summable.tsum_le_tsum hindptw hindsum hMsum
  calc ∑' (j : ℕ), ∑' (l : ℤ), f (j, l)
      ≤ ∑' (j : ℕ), U j :=
        Summable.tsum_le_tsum hgU (Summable.of_nonneg_of_le hgnn hgU hUsum) hUsum
    _ = (∑' j : ℕ, if j ≤ K then Real.exp (θ * (K : ℝ)) * M j else 0)
          + ∑' j : ℕ, if K < j then Real.exp (θ * (j : ℝ)) *
              (C' * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4))
                      / Real.sqrt (1 + (s : ℝ)))) else 0 := by
        simp only [hUdef]; exact hbulksum.tsum_add hsumT
    _ ≤ Real.exp (θ * (K : ℝ))
          + C' * Real.exp (θ * ((s : ℝ) / 4))
            * (Real.exp (-(c ^ 2 / 20 - θ) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                  / (1 - Real.exp (-(c ^ 2 / 20 - θ)))
               + Real.exp (-(c - θ) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                  / (1 - Real.exp (-(c - θ)))) := by
        refine add_le_add ?_ hleT
        have hb1 : (fun j : ℕ => if j ≤ K then Real.exp (θ * (K : ℝ)) * M j else 0)
            = fun j => Real.exp (θ * (K : ℝ)) * (if j ≤ K then M j else 0) := by
          funext j; by_cases hjK : j ≤ K <;> simp [hjK]
        rw [hb1, tsum_mul_left]
        have hstep : (∑' j : ℕ, if j ≤ K then M j else 0) ≤ 1 := by rw [← hmassM]; exact hindle
        calc Real.exp (θ * (K : ℝ)) * (∑' j : ℕ, if j ≤ K then M j else 0)
            ≤ Real.exp (θ * (K : ℝ)) * 1 :=
              mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
          _ = Real.exp (θ * (K : ℝ)) := mul_one _

/-- **`fpDist` first-coordinate MGF threshold**, symbolic (big-C campaign, step 2):
`T_mgfNumeric` at the column-marginal constants (`c_fpLocation`, `C_fpCol`). -/
noncomputable def T_fstMgf (A δ : ℝ) : ℕ := T_mgfNumeric A δ c_fpLocation C_fpCol

/-- `fpDist_fst_mgf_le`, `_at` sibling at `T_fstMgf A δ` (big-C campaign, step 2);
original body verbatim over `fpDist_col_le_explicitC` + `fpDist_fst_mgf_numeric_at`. -/
theorem fpDist_fst_mgf_le_at (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∀ m : ℕ, T_fstMgf A δ ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal * Real.exp (2 * A * (e.1 : ℝ) / (m : ℝ))
        ≤ 1 + δ := by
  have hc := c_fpLocation_pos
  have hC'pos := C_fpCol_pos
  have hcol := fpDist_col_le_explicitC
  have hCthr25 := (fpDist_fst_mgf_numeric_at hA hδ hc hC'pos).1
  have hnum := (fpDist_fst_mgf_numeric_at hA hδ hc hC'pos).2
  unfold T_fstMgf
  intro m hm s hs
  obtain ⟨K, hK25, hθle, hbud, hbulk, htail⟩ := hnum m hm s hs
  have hmpos : (0 : ℝ) < m := by
    have h25 : (25 : ℕ) ≤ m := le_trans hCthr25 hm
    exact_mod_cast lt_of_lt_of_le (by norm_num) h25
  have hθ0 : (0 : ℝ) ≤ 2 * A / (m : ℝ) := by positivity
  -- rewrite the exponent `2A·e.1/m` as `θ·e.1`, then invoke the reusable envelope
  have hexp : ∀ e : ℕ × ℤ,
      2 * A * (e.1 : ℝ) / (m : ℝ) = 2 * A / (m : ℝ) * (e.1 : ℝ) := fun e => by ring
  simp_rw [hexp]
  -- bulk `exp(θK) ≤ 1+δ/2` and gaussExp tail `≤ δ/2` are exactly `hbulk`, `htail`
  exact le_trans (fpDist_fst_mgf_general hc hC'pos hcol hθ0 hθle s K hK25 hbud).2
    (le_trans (add_le_add hbulk htail) (le_of_eq (by ring)))

/-- **First-coordinate `fpDist` MGF bound** (node X8 sub-goal — the genuinely-new
analytic input on which both the main term and the tail of `fpDist_edgeWeight_le`
depend).  At the vanishing tilt `θ = 2A/m`, under the (7.52) budget
`s ≤ m/log²m`, the first-passage column advance `e.1` (mean `≈ s/4`) has MGF
converging to `1`:
`∑_e fpDist(s,e)·exp(2A·e.1/m) ≤ 1 + δ` for `m ≥ C_{A,δ}`.

Rationale: `E[exp(θ·e.1)] ≈ 1 + θ·E[e.1] + … ≤ 1 + (2A/m)·(s/4)+O = 1 + A·s/(2m)
+ … ≤ 1 + A/(2log²m) → 1` as `m → ∞`.

ROUTE (mass-1 bulk + X6-lossy tail — NO renewal MGF needed; this is the simpler
route that supersedes the earlier renewal plan).  Write
`∑_e fpDist·exp(θ e.1) = 1 + ∑_e fpDist·(exp(θ e.1) − 1)` (`fpDist` mass 1,
`θ = 2A/m`; the `−1` term is `≥ 0`).  Split the excess at a threshold
`K = Θ(m/log)` (concretely `K = ⌊m·log(1+δ/2)/(2A)⌋`, so `θK ≤ log(1+δ/2)`):
• **Bulk** `e.1 ≤ K`: `exp(θ e.1) − 1 ≤ exp(θK) − 1 ≤ δ/2`, and `∑ fpDist ≤ 1`,
  so this part `≤ δ/2`.  Uses ONLY the probability normalisation — no envelope.
• **Tail** `e.1 > K`: bound `fpDist` by X6 `fpDist_location_bound`
  (`≤ C·e^{−c(l−s)}/√(1+s)·Gweight(1+s, c(j−s/4))`, available upstream in
  `FpLocation`).  With `j = e.1 > K = Θ(m)` far in the Gaussian tail
  (centre `s/4 ≤ m/(4log²m) ≪ K`), the super-exponential decay beats the linear
  `exp(θ j)` weight (`θ j − c²j²/(1+s) → −∞` since `1+s ≤ m`), so even the lossy
  `C` is harmless: the tail `≤ δ/2` for `m ≥ Cthr`.  Reuses the `Gweight`/geometric
  summation toolbox (`sum_sqrt_exp_le`, `sum_range_exp_neg_sq_le`, `conv_Gweight_exp`)
  plus the `l`-geometric `∑_{l>s} e^{−c(l−s)}`.
The whole point: the SHARP `≤ 1+δ` comes from `fpDist` being a probability measure
on the bulk; the envelope is used only where it is exponentially slack.
Original `∃`-form: delegates to the `_at` sibling at `T_fstMgf`. -/
theorem fpDist_fst_mgf_le (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal * Real.exp (2 * A * (e.1 : ℝ) / (m : ℝ))
        ≤ 1 + δ :=
  ⟨T_fstMgf A δ, fpDist_fst_mgf_le_at A hA δ hδ⟩

/-- ℝ-valued first-coordinate `Hold` MGF bound (bridge from the `ℝ≥0∞` `tiltZ`):
`∑_d hold(d)·exp(θ·d₁) ≤ 1 + 4θ + 32θ²` for `|θ| ≤ 1/100`.  This is the `Z_hold`
factor of `fpDist_edgeWeight_le`'s MGF term, in ℝ (via `tiltZ_hold_fst_le` +
`ENNReal.toReal`). -/
theorem hold_fst_mgf_le_real {θ : ℝ} (hlo : -(1 / 100) ≤ θ) (hhi : θ ≤ 1 / 100) :
    ∑' d : ℕ × ℤ, (hold d).toReal * Real.exp (θ * (d.1 : ℝ)) ≤ 1 + 4 * θ + 32 * θ ^ 2 := by
  have hterm : ∀ d : ℕ × ℤ,
      (hold d).toReal * Real.exp (θ * (d.1 : ℝ)) = (hold d * expW2 θ 0 d).toReal := by
    intro d
    rw [expW2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    congr 2; ring
  calc ∑' d : ℕ × ℤ, (hold d).toReal * Real.exp (θ * (d.1 : ℝ))
      = ∑' d : ℕ × ℤ, (hold d * expW2 θ 0 d).toReal := tsum_congr hterm
    _ = (∑' d : ℕ × ℤ, hold d * expW2 θ 0 d).toReal :=
        (ENNReal.tsum_toReal_eq
          (fun d => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top)).symm
    _ = (tiltZ hold (expW2 θ 0)).toReal := rfl
    _ ≤ (ENNReal.ofReal (1 + 4 * θ + 32 * θ ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (tiltZ_hold_fst_le hlo hhi)
    _ = 1 + 4 * θ + 32 * θ ^ 2 := ENNReal.toReal_ofReal (by nlinarith [sq_nonneg θ])

/-- **`fpDist` fixed-tilt tail threshold**, symbolic (big-C campaign, step 2):
`400 + Nlog + Nexp + N16` of `fpDist_fst_tail_le` at (`c_fpLocation`, `C_fpCol`). -/
noncomputable def T_fstTail (A δ : ℝ) : ℕ :=
  400 + T_logLin (min c_fpLocation (c_fpLocation ^ 2 / 20) / 2 / (16 * A))
    + T_expNeg (min c_fpLocation (c_fpLocation ^ 2 / 20) / 2 / 16)
        (δ / (1 + C_fpCol * (1 / (1 - Real.exp (-(c_fpLocation ^ 2 / 20
              - min c_fpLocation (c_fpLocation ^ 2 / 20) / 2)))
           + 1 / (1 - Real.exp (-(c_fpLocation
              - min c_fpLocation (c_fpLocation ^ 2 / 20) / 2))))))
    + T_logSq 16

-- HEARTBEAT: the fixed-tilt Chernoff assembles the reusable MGF envelope, a
-- pointwise Chernoff, and a polynomial-vs-exponential closeout in one declaration;
-- the nested `Real.exp` atoms make `isDefEq`/`nlinarith` costly. 2M covers it.
set_option maxHeartbeats 2000000 in
/-- **Fixed-tilt `fpDist` first-coordinate right tail** (the large-deviation input to
`fpDist_edgeWeight_le`'s tail).  `P(e₁ > m/4) ≤ δ·m^{−A}`.  ⚠️ The tilt MUST be a
FIXED constant (`θ₀ = ½·min(c, c²/20)` from `fpDist_col_le`), NOT `2A/m`: the Chernoff
`P(e₁>m/4) ≤ e^{−θ·m/4}·Z_fp(θ)` only decays like `m^{−A}` when `θ` is `Θ(1)` (at
`θ = 2A/m` the factor is the non-decaying `e^{−A/2}`).  Route: Fubini + `fpDist_col_le`
+ `gaussExp_col_tail` at cutoff `K' = Θ(s)` (budget `s·log2 ≤ (K'+2)log9`), giving
`Z_fp(θ₀) ≤ exp(O(m/log²m))`, so `e^{−θ₀m/4}·Z_fp(θ₀) = exp(−θ₀m/4 + o(m)) ≪ m^{−A}`.
`_at` sibling at `T_fstTail A δ` (big-C campaign, step 2); original body verbatim over
`fpDist_col_le_explicitC` and the explicit thresholds. -/
theorem fpDist_fst_tail_le_at (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∀ m : ℕ, T_fstTail A δ ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
        ≤ δ * (m : ℝ) ^ (-A) := by
  have hcol := fpDist_col_le_explicitC
  unfold T_fstTail
  set c : ℝ := c_fpLocation with hcdef
  set C' : ℝ := C_fpCol with hC'def
  have hc : 0 < c := c_fpLocation_pos
  have hC'pos : 0 < C' := C_fpCol_pos
  -- FIXED tilt `θ₀ = ½·min(c, c²/20)` (Θ(1); NOT `2A/m`)
  set θ₀ : ℝ := min c (c ^ 2 / 20) / 2 with hθ₀def
  have hθ₀pos : 0 < θ₀ := by
    rw [hθ₀def]; have : 0 < min c (c ^ 2 / 20) := lt_min hc (by positivity); linarith
  have hθ₀nn : 0 ≤ θ₀ := hθ₀pos.le
  have hθ₀le : θ₀ ≤ min c (c ^ 2 / 20) / 2 := le_refl _
  have hθ₀c : θ₀ ≤ c / 2 := by rw [hθ₀def]; gcongr; exact min_le_left _ _
  have hθ₀c2 : θ₀ ≤ c ^ 2 / 40 := by
    rw [hθ₀def]; have : min c (c ^ 2 / 20) ≤ c ^ 2 / 20 := min_le_right _ _; linarith
  have hcsq : (0 : ℝ) < c ^ 2 := by positivity
  have ha2pos : 0 < c ^ 2 / 20 - θ₀ := by nlinarith [hθ₀c2, hcsq]
  have ha1pos : 0 < c - θ₀ := by linarith [hθ₀c]
  -- geometric denominators and the envelope constant `B`
  set d₂ : ℝ := 1 - Real.exp (-(c ^ 2 / 20 - θ₀)) with hd2def
  set d₁ : ℝ := 1 - Real.exp (-(c - θ₀)) with hd1def
  have hd2 : 0 < d₂ := by
    rw [hd2def]; have : Real.exp (-(c ^ 2 / 20 - θ₀)) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith [ha2pos]
    linarith
  have hd1 : 0 < d₁ := by
    rw [hd1def]; have : Real.exp (-(c - θ₀)) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith [ha1pos]
    linarith
  set B : ℝ := 1 + C' * (1 / d₂ + 1 / d₁) with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]; have : 0 < C' * (1 / d₂ + 1 / d₁) := by positivity
    linarith
  -- thresholds
  set Nlog : ℕ := T_logLin (θ₀ / (16 * A)) with hNlogdef
  have hNlog := log_le_eps_mul_at (θ₀ / (16 * A)) (by positivity)
  set Nexp : ℕ := T_expNeg (θ₀ / 16) (δ / B) with hNexpdef
  have hNexp := exp_neg_mul_le_at (θ₀ / 16) (by positivity) (δ / B) (by positivity)
  set N16 : ℕ := T_logSq 16 with hN16def
  have hN16 := log_sq_ge_at 16
  intro m hm s hs
  have hm400 : 400 ≤ m := by omega
  have hmNlog : Nlog ≤ m := by omega
  have hmNexp : Nexp ≤ m := by omega
  have hmN16 : N16 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : 1 < m := by omega
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm1)
  have hlogsq_pos : 0 < Real.log m ^ 2 := by positivity
  have hlog16 : (16 : ℝ) ≤ Real.log m ^ 2 := hN16 m hmN16
  -- cutoff `K = ⌊m/log²m⌋ + 25`
  set κ : ℝ := (m : ℝ) / Real.log m ^ 2 with hκdef
  have hκnn : 0 ≤ κ := by rw [hκdef]; positivity
  have hsκ : (s : ℝ) ≤ κ := hs
  set K : ℕ := ⌊κ⌋₊ + 25 with hKdef
  have hK25 : 25 ≤ K := by omega
  have hKle : (K : ℝ) ≤ κ + 25 := by rw [hKdef]; push_cast; linarith [Nat.floor_le hκnn]
  have hKlb : κ + 24 ≤ (K : ℝ) := by
    rw [hKdef]; push_cast; linarith [Nat.lt_floor_add_one κ]
  have hsK : (s : ℝ) / 4 ≤ (K : ℝ) := by
    have hsleK : (s : ℝ) ≤ (K : ℝ) := le_trans hsκ (by linarith [hKlb])
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hKx0 : 0 ≤ (K : ℝ) + 1 - (s : ℝ) / 4 := by linarith [hsK]
  -- budget `s·log2 ≤ (K+2)·log9`
  have hbud : (s : ℝ) * Real.log 2 ≤ ((K : ℝ) + 2) * Real.log 9 := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hlog9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
    have hlog29 : Real.log 2 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
    calc (s : ℝ) * Real.log 2 ≤ κ * Real.log 2 := mul_le_mul_of_nonneg_right hsκ hlog2.le
      _ ≤ κ * Real.log 9 := mul_le_mul_of_nonneg_left hlog29 hκnn
      _ ≤ ((K : ℝ) + 2) * Real.log 9 :=
          mul_le_mul_of_nonneg_right (by linarith [hKlb]) hlog9.le
  -- `K ≤ m/8`, so `K - m/4 ≤ -m/8`
  have hKupper : (K : ℝ) ≤ (m : ℝ) / 8 := by
    have h1 : κ ≤ (m : ℝ) / 16 := by
      rw [hκdef, div_le_div_iff₀ hlogsq_pos (by norm_num)]
      nlinarith [hlog16, hmpos.le]
    have h2 : (25 : ℝ) ≤ (m : ℝ) / 16 := by
      rw [le_div_iff₀ (by norm_num)]; have : (400 : ℝ) ≤ m := by exact_mod_cast hm400
      linarith
    linarith [hKle, h1, h2]
  have hKm4 : (K : ℝ) - (m : ℝ) / 4 ≤ -((m : ℝ) / 8) := by linarith [hKupper]
  -- the MGF envelope at the fixed tilt: `Z ≤ exp(θ₀K) + gaussExp_RHS`
  obtain ⟨hZsum, hZle⟩ := fpDist_fst_mgf_general hc hC'pos hcol hθ₀nn hθ₀le s K hK25 hbud
  -- collapse the envelope to `Z ≤ B·exp(θ₀K)`
  have hZB : ∑' e : ℕ × ℤ, (fpDist s e).toReal * Real.exp (θ₀ * (e.1 : ℝ))
      ≤ B * Real.exp (θ₀ * (K : ℝ)) := by
    refine le_trans hZle ?_
    have hE2 : Real.exp (-(c ^ 2 / 20 - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [ha2pos, hKx0]
    have hE1 : Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [ha1pos, hKx0]
    have hpre : Real.exp (θ₀ * ((s : ℝ) / 4)) ≤ Real.exp (θ₀ * (K : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsK hθ₀nn)
    have hterm2 :
        Real.exp (-(c ^ 2 / 20 - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4)) / d₂ ≤ 1 / d₂ := by
      rw [div_le_div_iff₀ hd2 hd2]; nlinarith [hE2, hd2.le]
    have hterm1 :
        Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4)) / d₁ ≤ 1 / d₁ := by
      rw [div_le_div_iff₀ hd1 hd1]; nlinarith [hE1, hd1.le]
    have hgaussle : C' * Real.exp (θ₀ * ((s : ℝ) / 4))
          * (Real.exp (-(c ^ 2 / 20 - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                / (1 - Real.exp (-(c ^ 2 / 20 - θ₀)))
             + Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                / (1 - Real.exp (-(c - θ₀))))
        ≤ C' * Real.exp (θ₀ * (K : ℝ)) * (1 / d₂ + 1 / d₁) := by
      rw [← hd2def, ← hd1def]
      have hinner : Real.exp (-(c ^ 2 / 20 - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4)) / d₂
            + Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4)) / d₁
          ≤ 1 / d₂ + 1 / d₁ := add_le_add hterm2 hterm1
      have hcoef : 0 ≤ C' * Real.exp (θ₀ * ((s : ℝ) / 4)) := by positivity
      calc C' * Real.exp (θ₀ * ((s : ℝ) / 4))
              * (Real.exp (-(c ^ 2 / 20 - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4)) / d₂
                 + Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4)) / d₁)
            ≤ C' * Real.exp (θ₀ * ((s : ℝ) / 4)) * (1 / d₂ + 1 / d₁) :=
              mul_le_mul_of_nonneg_left hinner hcoef
        _ ≤ C' * Real.exp (θ₀ * (K : ℝ)) * (1 / d₂ + 1 / d₁) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hpre hC'pos.le
    calc Real.exp (θ₀ * (K : ℝ))
          + C' * Real.exp (θ₀ * ((s : ℝ) / 4))
            * (Real.exp (-(c ^ 2 / 20 - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                  / (1 - Real.exp (-(c ^ 2 / 20 - θ₀)))
               + Real.exp (-(c - θ₀) * (((K : ℝ) + 1) - (s : ℝ) / 4))
                  / (1 - Real.exp (-(c - θ₀))))
        ≤ Real.exp (θ₀ * (K : ℝ)) + C' * Real.exp (θ₀ * (K : ℝ)) * (1 / d₂ + 1 / d₁) :=
          add_le_add (le_refl _) hgaussle
      _ = B * Real.exp (θ₀ * (K : ℝ)) := by rw [hBdef]; ring
  -- Chernoff at the fixed tilt: `T ≤ exp(-θ₀m/4)·Z`
  have hfp2d : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal) :=
    ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
  have hLHSsum : Summable
      (fun e : ℕ × ℤ => (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hfp2d
    · positivity
    · by_cases h : m < 4 * e.1
      · rw [if_pos h, mul_one]
      · rw [if_neg h, mul_zero]; exact ENNReal.toReal_nonneg
  have hcher : ∑' e : ℕ × ℤ, (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
      ≤ Real.exp (-θ₀ * (m : ℝ) / 4)
        * ∑' e : ℕ × ℤ, (fpDist s e).toReal * Real.exp (θ₀ * (e.1 : ℝ)) := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun e => ?_) hLHSsum (hZsum.mul_left _)
    by_cases hcond : m < 4 * e.1
    · rw [if_pos hcond, mul_one]
      have h4 : (m : ℝ) < 4 * (e.1 : ℝ) := by exact_mod_cast hcond
      have hexp1 : (1 : ℝ) ≤ Real.exp (θ₀ * (e.1 : ℝ) - θ₀ * (m : ℝ) / 4) := by
        rw [← Real.exp_zero]; apply Real.exp_le_exp.mpr; nlinarith [hθ₀nn, h4]
      calc (fpDist s e).toReal = (fpDist s e).toReal * 1 := (mul_one _).symm
        _ ≤ (fpDist s e).toReal * Real.exp (θ₀ * (e.1 : ℝ) - θ₀ * (m : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left hexp1 ENNReal.toReal_nonneg
        _ = Real.exp (-θ₀ * (m : ℝ) / 4) * ((fpDist s e).toReal * Real.exp (θ₀ * (e.1 : ℝ))) := by
            rw [show θ₀ * (e.1 : ℝ) - θ₀ * (m : ℝ) / 4
                  = θ₀ * (e.1 : ℝ) + (-θ₀ * (m : ℝ) / 4) by ring, Real.exp_add]; ring
    · rw [if_neg hcond, mul_zero]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
  -- final numeric: `B·exp(-θ₀m/8) ≤ δ·m^{-A}`
  have hAlog : A * Real.log m ≤ θ₀ * (m : ℝ) / 16 := by
    have h := hNlog m hmNlog
    have h2 : A * Real.log m ≤ A * (θ₀ / (16 * A) * (m : ℝ)) := mul_le_mul_of_nonneg_left h hA.le
    have h3 : A * (θ₀ / (16 * A) * (m : ℝ)) = θ₀ * (m : ℝ) / 16 := by
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hfin : B * Real.exp (-θ₀ * (m : ℝ) / 8) ≤ δ * (m : ℝ) ^ (-A) := by
    rw [Real.rpow_neg hmpos.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos hmpos A), Real.rpow_def_of_pos hmpos A,
      mul_assoc, ← Real.exp_add]
    have hexparg : -θ₀ * (m : ℝ) / 8 + Real.log m * A ≤ -(θ₀ / 16) * (m : ℝ) := by
      nlinarith [hAlog]
    calc B * Real.exp (-θ₀ * (m : ℝ) / 8 + Real.log m * A)
        ≤ B * Real.exp (-(θ₀ / 16) * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexparg) hBpos.le
      _ ≤ B * (δ / B) := mul_le_mul_of_nonneg_left (hNexp m hmNexp) hBpos.le
      _ = δ := by field_simp
  -- chain: `T ≤ exp(-θ₀m/4)·Z ≤ B·exp(θ₀K - θ₀m/4) ≤ B·exp(-θ₀m/8) ≤ δ·m^{-A}`
  calc ∑' e : ℕ × ℤ, (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
      ≤ Real.exp (-θ₀ * (m : ℝ) / 4)
          * ∑' e : ℕ × ℤ, (fpDist s e).toReal * Real.exp (θ₀ * (e.1 : ℝ)) := hcher
    _ ≤ Real.exp (-θ₀ * (m : ℝ) / 4) * (B * Real.exp (θ₀ * (K : ℝ))) :=
        mul_le_mul_of_nonneg_left hZB (Real.exp_pos _).le
    _ = B * Real.exp (θ₀ * (K : ℝ) - θ₀ * (m : ℝ) / 4) := by
        rw [show θ₀ * (K : ℝ) - θ₀ * (m : ℝ) / 4
              = (-θ₀ * (m : ℝ) / 4) + θ₀ * (K : ℝ) by ring, Real.exp_add]; ring
    _ ≤ B * Real.exp (-θ₀ * (m : ℝ) / 8) := by
        apply mul_le_mul_of_nonneg_left _ hBpos.le
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hKm4 hθ₀nn]
    _ ≤ δ * (m : ℝ) ^ (-A) := hfin


/-- `fpDist_fst_tail_le`, original `∃`-form: delegates to the `_at` sibling at `T_fstTail`. -/
theorem fpDist_fst_tail_le (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
        ≤ δ * (m : ℝ) ^ (-A) :=
  ⟨T_fstTail A δ, fpDist_fst_tail_le_at A hA δ hδ⟩

/-- **`Hold` first-coordinate tail threshold**, symbolic (big-C campaign, step 2):
`400 + Nlog + Nexp` of `hold_fst_tail_le` at `ρ = log(4/3)/8`. -/
noncomputable def T_holdTail (A δ : ℝ) : ℕ :=
  400 + T_logLin (Real.log (4 / 3) / 8 / (2 * A)) + T_expNeg (Real.log (4 / 3) / 8 / 2) δ

/-- **`Hold` first-coordinate right tail** (the hold half of `fpDist_edgeWeight_le`'s
tail): `P_hold(d₁ > m/4) ≤ δ·m^{−A}`.  `hold`'s first marginal is EXACTLY the geometric
`geomQuarter` (`hold_map_fst`), so this reduces via `hold_tsum_fst` to the closed-form
geometric tail `geomQuarter_tail`: `∑_{k>m/4} geomQuarter(k) = (3/4)^{⌊m/4⌋}`.  Then
`(3/4)^{⌊m/4⌋} = exp(−log(4/3)·⌊m/4⌋) ≤ exp(−(log(4/3)/8)·m) ≤ δ·m^{−A}` for `m` large
(`⌊m/4⌋ ≥ m/8`; polynomial `m^A` beaten by `exp(−ρm)`).  `_at` sibling at
`T_holdTail A δ` (big-C campaign, step 2); original body verbatim. -/
theorem hold_fst_tail_le_at (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∀ m : ℕ, T_holdTail A δ ≤ m →
      ∑' d : ℕ × ℤ, (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0)
        ≤ δ * (m : ℝ) ^ (-A) := by
  unfold T_holdTail
  set ρ : ℝ := Real.log (4 / 3) / 8 with hρdef
  have hlog43pos : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  set Nlog : ℕ := T_logLin (ρ / (2 * A)) with hNlogdef
  have hNlog := log_le_eps_mul_at (ρ / (2 * A)) (by positivity)
  set Nexp : ℕ := T_expNeg (ρ / 2) δ with hNexpdef
  have hNexp := exp_neg_mul_le_at (ρ / 2) (by positivity) δ hδ
  intro m hm
  have hm400 : 400 ≤ m := by omega
  have hmNlog : Nlog ≤ m := by omega
  have hmNexp : Nexp ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  -- reduce the hold tail to the closed-form geometric tail
  have hf : ∀ k : ℕ, (0 : ℝ) ≤ (if m < 4 * k then (1 : ℝ) else 0) := by
    intro k; split_ifs <;> norm_num
  have hstep : ∀ k : ℕ, (geomQuarter k).toReal * (if m < 4 * k then (1 : ℝ) else 0)
      = (if m / 4 < k then (geomQuarter k).toReal else 0) := by
    intro k
    by_cases h : m < 4 * k
    · rw [if_pos h, mul_one, if_pos (by omega)]
    · rw [if_neg h, mul_zero, if_neg (by omega)]
  have hred : ∑' d : ℕ × ℤ, (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0)
      = (3 / 4 : ℝ) ^ (m / 4) := by
    rw [show (∑' d : ℕ × ℤ, (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0))
          = ∑' k : ℕ, (geomQuarter k).toReal * (if m < 4 * k then (1 : ℝ) else 0)
        from hold_tsum_fst (fun k => if m < 4 * k then (1 : ℝ) else 0) hf,
      tsum_congr hstep, geomQuarter_tail]
  rw [hred]
  -- `(3/4)^{⌊m/4⌋} = exp(log(3/4)·⌊m/4⌋)`
  have h34 : (3 / 4 : ℝ) ^ (m / 4) = Real.exp (Real.log (3 / 4) * ((m / 4 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (3 / 4 : ℝ) (m / 4), Real.rpow_def_of_pos (by norm_num)]
  have hm4lb : (m : ℝ) / 8 ≤ ((m / 4 : ℕ) : ℝ) := by
    have hnat : m ≤ 4 * (m / 4) + 3 := by omega
    have hh : (m : ℝ) ≤ 4 * ((m / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hnat
    have h400 : (400 : ℝ) ≤ m := by exact_mod_cast hm400
    linarith
  have hexp_le : Real.log (3 / 4) * ((m / 4 : ℕ) : ℝ) ≤ -ρ * m := by
    have hlog34 : Real.log (3 / 4) = -Real.log (4 / 3) := by
      rw [show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
    rw [hlog34, hρdef]
    nlinarith [mul_le_mul_of_nonneg_left hm4lb hlog43pos.le]
  -- `exp(-ρm) ≤ δ·m^{-A}` (polynomial beaten by super-exponential decay)
  have hclose : Real.exp (-ρ * m) ≤ δ * (m : ℝ) ^ (-A) := by
    rw [Real.rpow_neg hmpos.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos hmpos A), Real.rpow_def_of_pos hmpos A, ← Real.exp_add]
    have hAlog : A * Real.log m ≤ ρ / 2 * m := by
      have h := hNlog m hmNlog
      have h2 : A * Real.log m ≤ A * (ρ / (2 * A) * (m : ℝ)) := mul_le_mul_of_nonneg_left h hA.le
      have h3 : A * (ρ / (2 * A) * (m : ℝ)) = ρ / 2 * m := by field_simp
      linarith [h2, h3.le, h3.ge]
    have hexparg : -ρ * (m : ℝ) + Real.log m * A ≤ -(ρ / 2) * m := by nlinarith [hAlog]
    exact le_trans (Real.exp_le_exp.mpr hexparg) (hNexp m hmNexp)
  calc (3 / 4 : ℝ) ^ (m / 4) = Real.exp (Real.log (3 / 4) * ((m / 4 : ℕ) : ℝ)) := h34
    _ ≤ Real.exp (-ρ * m) := Real.exp_le_exp.mpr hexp_le
    _ ≤ δ * (m : ℝ) ^ (-A) := hclose


/-- `hold_fst_tail_le`, original `∃`-form: delegates to the `_at` sibling at `T_holdTail`. -/
theorem hold_fst_tail_le (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ m : ℕ, Cthr ≤ m →
      ∑' d : ℕ × ℤ, (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0)
        ≤ δ * (m : ℝ) ^ (-A) :=
  ⟨T_holdTail A δ, hold_fst_tail_le_at A hA δ hδ⟩

/-- **Fubini split of the (7.48) double sum** — the mechanical heart of
`fpDist_edgeWeight_le`.  Summing the pointwise `edgeWeight_summand_le` over the hold
step `d` (with `hold`) and the first-passage step `e` (with `fpDist`), and splitting
the joint tail via `1_{m<2(e₁+d₁)} ≤ 1_{m<4e₁} + 1_{m<4d₁}`, the average depth weight
factors into `m^{−A}·Z_fp(θ)·Z_hold(θ)` (θ = 2A/m) plus the two one-sided first-coord
tails.  Takes the two MGF summabilities as hypotheses (the callers supply them). -/
theorem fpDist_edgeWeight_split {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 2 ≤ m) (s : ℕ)
    (hZf : Summable (fun e : ℕ × ℤ =>
      (fpDist s e).toReal * Real.exp (2 * A / (m : ℝ) * (e.1 : ℝ))))
    (hZh : Summable (fun d : ℕ × ℤ =>
      (hold d).toReal * Real.exp (2 * A / (m : ℝ) * (d.1 : ℝ)))) :
    ∑' e : ℕ × ℤ, (fpDist s e).toReal * edgeWeight A m e
      ≤ (m : ℝ) ^ (-A)
          * (∑' e : ℕ × ℤ, (fpDist s e).toReal * Real.exp (2 * A / (m : ℝ) * (e.1 : ℝ)))
          * (∑' d : ℕ × ℤ, (hold d).toReal * Real.exp (2 * A / (m : ℝ) * (d.1 : ℝ)))
        + (∑' e : ℕ × ℤ, (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0))
        + (∑' d : ℕ × ℤ, (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set θ : ℝ := 2 * A / (m : ℝ) with hθdef
  have hθnn : 0 ≤ θ := by rw [hθdef]; positivity
  set mA : ℝ := (m : ℝ) ^ (-A) with hmAdef
  have hmA0 : 0 < mA := Real.rpow_pos_of_pos hmpos _
  set Zf : ℝ := ∑' e : ℕ × ℤ, (fpDist s e).toReal * Real.exp (θ * (e.1 : ℝ)) with hZfdef
  set Zh : ℝ := ∑' d : ℕ × ℤ, (hold d).toReal * Real.exp (θ * (d.1 : ℝ)) with hZhdef
  set Tf : ℝ := ∑' e : ℕ × ℤ, (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
    with hTfdef
  set Th : ℝ := ∑' d : ℕ × ℤ, (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0)
    with hThdef
  -- PMF facts
  have hholdsum : Summable (fun d : ℕ × ℤ => (hold d).toReal) := hold_summable_toReal
  have hholdmass : ∑' d : ℕ × ℤ, (hold d).toReal = 1 := hold_tsum_toReal
  have hfpsum : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal) :=
    ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
  have hfpmass : ∑' e : ℕ × ℤ, (fpDist s e).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun e => PMF.apply_ne_top _ _), (fpDist s).tsum_coe,
      ENNReal.toReal_one]
  -- "(sub-)probability × [0,1] weight is summable" helpers
  have hsum_hold_le : ∀ f : ℕ × ℤ → ℝ, (∀ d, 0 ≤ f d) → (∀ d, f d ≤ 1) →
      Summable (fun d => (hold d).toReal * f d) := by
    intro f hf0 hf1
    refine Summable.of_nonneg_of_le (fun d => mul_nonneg ENNReal.toReal_nonneg (hf0 d))
      (fun d => ?_) hholdsum
    calc (hold d).toReal * f d ≤ (hold d).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hf1 d) ENNReal.toReal_nonneg
      _ = (hold d).toReal := mul_one _
  have hsum_fp_le : ∀ f : ℕ × ℤ → ℝ, (∀ e, 0 ≤ f e) → (∀ e, f e ≤ 1) →
      Summable (fun e => (fpDist s e).toReal * f e) := by
    intro f hf0 hf1
    refine Summable.of_nonneg_of_le (fun e => mul_nonneg ENNReal.toReal_nonneg (hf0 e))
      (fun e => ?_) hfpsum
    calc (fpDist s e).toReal * f e ≤ (fpDist s e).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hf1 e) ENNReal.toReal_nonneg
      _ = (fpDist s e).toReal := mul_one _
  have hrpow01 : ∀ e d : ℕ × ℤ, ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 :=
    fun e d => Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast Nat.le_max_right _ _) (by linarith)
  have hrpow0 : ∀ e d : ℕ × ℤ, (0 : ℝ) ≤ ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) :=
    fun e d => Real.rpow_nonneg (by positivity) _
  have hind0 : ∀ (P : Prop) [Decidable P], (0 : ℝ) ≤ (if P then (1 : ℝ) else 0) := by
    intro P _; split_ifs <;> norm_num
  have hind1 : ∀ (P : Prop) [Decidable P], (if P then (1 : ℝ) else 0) ≤ 1 := by
    intro P _; split_ifs <;> norm_num
  -- per-`e` bound: `edgeWeight A m e ≤ mA·exp(θe₁)·Zh + 1_{m<4e₁} + Th`
  have hpere : ∀ e : ℕ × ℤ, edgeWeight A m e
      ≤ mA * Real.exp (θ * (e.1 : ℝ)) * Zh + (if m < 4 * e.1 then (1 : ℝ) else 0) + Th := by
    intro e
    have hEWsum : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
      hsum_hold_le _ (hrpow0 e) (hrpow01 e)
    have ht1 : Summable (fun d : ℕ × ℤ =>
        mA * Real.exp (θ * (e.1 : ℝ)) * ((hold d).toReal * Real.exp (θ * (d.1 : ℝ)))) :=
      hZh.mul_left _
    have ht2 : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)) :=
      hsum_hold_le _ (fun _ => hind0 _) (fun _ => hind1 _)
    have ht3 : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0)) :=
      hsum_hold_le _ (fun _ => hind0 _) (fun _ => hind1 _)
    have hptw : ∀ d : ℕ × ℤ,
        (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)
        ≤ mA * Real.exp (θ * (e.1 : ℝ)) * ((hold d).toReal * Real.exp (θ * (d.1 : ℝ)))
          + (hold d).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
          + (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0) := by
      intro d
      have hsummand := edgeWeight_summand_le hA hm e d
      have hexpsplit : mA * Real.exp (2 * A * ((e.1 + d.1 : ℕ) : ℝ) / (m : ℝ))
          = mA * Real.exp (θ * (e.1 : ℝ)) * Real.exp (θ * (d.1 : ℝ)) := by
        rw [show 2 * A * ((e.1 + d.1 : ℕ) : ℝ) / (m : ℝ) = θ * (e.1 : ℝ) + θ * (d.1 : ℝ) by
              rw [hθdef]; push_cast; ring, Real.exp_add]; ring
      have hind : (if m < 2 * (e.1 + d.1) then (1 : ℝ) else 0)
          ≤ (if m < 4 * e.1 then (1 : ℝ) else 0) + (if m < 4 * d.1 then (1 : ℝ) else 0) := by
        by_cases h2 : m < 2 * (e.1 + d.1)
        · rw [if_pos h2]
          rcases (by omega : m < 4 * e.1 ∨ m < 4 * d.1) with h | h
          · rw [if_pos h]; linarith [hind0 (m < 4 * d.1)]
          · rw [if_pos h]; linarith [hind0 (m < 4 * e.1)]
        · rw [if_neg h2]; linarith [hind0 (m < 4 * e.1), hind0 (m < 4 * d.1)]
      have hhn : (0 : ℝ) ≤ (hold d).toReal := ENNReal.toReal_nonneg
      calc (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)
          ≤ (hold d).toReal * ((m : ℝ) ^ (-A)
              * Real.exp (2 * A * ((e.1 + d.1 : ℕ) : ℝ) / (m : ℝ))
              + (if m < 2 * (e.1 + d.1) then (1 : ℝ) else 0)) :=
            mul_le_mul_of_nonneg_left hsummand hhn
        _ = (hold d).toReal * (mA * Real.exp (θ * (e.1 : ℝ)) * Real.exp (θ * (d.1 : ℝ)))
              + (hold d).toReal * (if m < 2 * (e.1 + d.1) then (1 : ℝ) else 0) := by
            rw [← hmAdef, hexpsplit]; ring
        _ ≤ mA * Real.exp (θ * (e.1 : ℝ)) * ((hold d).toReal * Real.exp (θ * (d.1 : ℝ)))
            + (hold d).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
            + (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0) := by
              have := mul_le_mul_of_nonneg_left hind hhn
              nlinarith [this]
    have hsub1 : ∑' d : ℕ × ℤ,
        mA * Real.exp (θ * (e.1 : ℝ)) * ((hold d).toReal * Real.exp (θ * (d.1 : ℝ)))
        = mA * Real.exp (θ * (e.1 : ℝ)) * Zh := by rw [tsum_mul_left, ← hZhdef]
    have hsub2 : ∑' d : ℕ × ℤ, (hold d).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
        = (if m < 4 * e.1 then (1 : ℝ) else 0) := by
      rw [tsum_mul_right, hholdmass, one_mul]
    calc edgeWeight A m e
        = ∑' d : ℕ × ℤ, (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) := rfl
      _ ≤ ∑' d : ℕ × ℤ, (mA * Real.exp (θ * (e.1 : ℝ))
              * ((hold d).toReal * Real.exp (θ * (d.1 : ℝ)))
            + (hold d).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
            + (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0)) :=
          hEWsum.tsum_le_tsum hptw ((ht1.add ht2).add ht3)
      _ = mA * Real.exp (θ * (e.1 : ℝ)) * Zh
            + (if m < 4 * e.1 then (1 : ℝ) else 0) + Th := by
          rw [(ht1.add ht2).tsum_add ht3, ht1.tsum_add ht2, hsub1, hsub2, ← hThdef]
  -- sum the per-`e` bound over `e` with `fpDist`
  have hEWfpsum : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal * edgeWeight A m e) := by
    refine hsum_fp_le _ (fun e => edgeWeight_nonneg A m e) (fun e => ?_)
    calc edgeWeight A m e
        = ∑' d : ℕ × ℤ, (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) := rfl
      _ ≤ ∑' d : ℕ × ℤ, (hold d).toReal := by
          refine (hsum_hold_le _ (hrpow0 e) (hrpow01 e)).tsum_le_tsum (fun d => ?_) hholdsum
          calc (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)
              ≤ (hold d).toReal * 1 := mul_le_mul_of_nonneg_left (hrpow01 e d) ENNReal.toReal_nonneg
            _ = (hold d).toReal := mul_one _
      _ = 1 := hholdmass
  have hFF1 : Summable (fun e : ℕ × ℤ =>
      mA * Zh * ((fpDist s e).toReal * Real.exp (θ * (e.1 : ℝ)))) := hZf.mul_left _
  have hFF2 : Summable (fun e : ℕ × ℤ =>
      (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)) :=
    hsum_fp_le _ (fun _ => hind0 _) (fun _ => hind1 _)
  have hFF3 : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal * Th) := hfpsum.mul_right _
  have hFsum : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal
      * (mA * Real.exp (θ * (e.1 : ℝ)) * Zh + (if m < 4 * e.1 then (1 : ℝ) else 0) + Th)) := by
    have heq : (fun e : ℕ × ℤ => (fpDist s e).toReal
        * (mA * Real.exp (θ * (e.1 : ℝ)) * Zh + (if m < 4 * e.1 then (1 : ℝ) else 0) + Th))
        = fun e => mA * Zh * ((fpDist s e).toReal * Real.exp (θ * (e.1 : ℝ)))
            + (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
            + (fpDist s e).toReal * Th := by
      funext e; ring
    rw [heq]; exact (hFF1.add hFF2).add hFF3
  have hgsub1 : ∑' e : ℕ × ℤ, mA * Zh * ((fpDist s e).toReal * Real.exp (θ * (e.1 : ℝ)))
      = mA * Zh * Zf := by rw [tsum_mul_left, ← hZfdef]
  have hgsub3 : ∑' e : ℕ × ℤ, (fpDist s e).toReal * Th = Th := by
    rw [tsum_mul_right, hfpmass, one_mul]
  calc ∑' e : ℕ × ℤ, (fpDist s e).toReal * edgeWeight A m e
      ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
          * (mA * Real.exp (θ * (e.1 : ℝ)) * Zh
             + (if m < 4 * e.1 then (1 : ℝ) else 0) + Th) :=
        hEWfpsum.tsum_le_tsum
          (fun e => mul_le_mul_of_nonneg_left (hpere e) ENNReal.toReal_nonneg) hFsum
    _ = ∑' e : ℕ × ℤ, (mA * Zh * ((fpDist s e).toReal * Real.exp (θ * (e.1 : ℝ)))
            + (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
            + (fpDist s e).toReal * Th) := by
        refine tsum_congr (fun e => ?_); ring
    _ = mA * Zh * Zf + Tf + Th := by
        rw [(hFF1.add hFF2).tsum_add hFF3, hFF1.tsum_add hFF2, hgsub1, hgsub3, ← hTfdef]
    _ = mA * Zf * Zh + Tf + Th := by ring

/-- **`fpDist_edgeWeight_le` threshold**, symbolic (big-C campaign, step 2):
the (7.48)/(7.49) Case-2 weight-degradation threshold at `ε = min(δ/8, 2)` and the
column-marginal constants. -/
noncomputable def T_edgeWeight (A δ : ℝ) : ℕ :=
  T_fstMgf A (min (δ / 8) 2) + T_fstTail A (δ / 4) + T_holdTail A (δ / 4)
    + ⌈200 * A⌉₊ + ⌈10 * A / min (δ / 8) 2⌉₊
    + ⌈4 * A / min c_fpLocation (c_fpLocation ^ 2 / 20)⌉₊ + 2

set_option maxHeartbeats 1000000 in
/-- **The (7.48)/(7.49) weight degradation, Case 2** (paper p.47). With budget
`s ≤ m/log²m`, the first-passage endpoint's `j`-coordinate concentrates near
`s/4 ≪ m/log²m` (Lemma 7.7 = `fpDist_location_bound`, node X6), so the average
depth weight `E[edgeWeight]` exceeds `m^{-A}` only by `exp(O(A·log m/m ·
m/log²m)) = 1 + O(A/log m) ≤ 1 + δ` once `m ≥ C_{A,δ}` ((7.42) concavity bound
+ Chernoff truncation of `j_{[1,k]} > m/log²m`).

DECOMPOSITION (2026-07-14, corrected): `edgeWeight_summand_le` reduces this to
(i) the MGF factor `m^{−A}·Z_fp(2A/m)·Z_hold(2A/m) ≤ (1+δ/2)m^{−A}`
(`fpDist_fst_mgf_le` × `hold_fst_mgf_le_real`, both PROVED) plus (ii) the tail
`P(e₁+d₁ > m/2) ≤ (δ/2)m^{−A}`, split as `P_fp(e₁>m/4) + P_hold(d₁>m/4)` via
`fpDist_fst_tail_le` + `hold_fst_tail_le`.  ⚠️ CORRECTION: (ii) is NOT a Chernoff of
`fpDist_fst_mgf_le` — the `2A/m` tilt gives only `e^{−A/2}` (non-decaying).  It needs
FIXED-tilt tails (see `fpDist_fst_tail_le`); this is genuine new analytic input, not
pure glue as the earlier note claimed.

PROVED (node X8): glue over `fpDist_edgeWeight_split` (Fubini heart) + the four
inputs `fpDist_fst_mgf_le` (Z_fp ≤ 1+ε), `hold_fst_mgf_le_real` (Z_hold ≤ 1+4θ+32θ²
≤ 1+ε), `fpDist_fst_tail_le` (T_fp ≤ (δ/4)m^{−A}), `hold_fst_tail_le` (T_hold ≤
(δ/4)m^{−A}), all axiom-clean.  With `ε = min(δ/8, 2)`: MGF term `≤ m^{−A}(1+ε)² ≤
(1+δ/2)m^{−A}`, tail `≤ (δ/2)m^{−A}`, sum `= (1+δ)m^{−A}`. -/
theorem fpDist_edgeWeight_le_at (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∀ m : ℕ, T_edgeWeight A δ ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal * edgeWeight A m e
        ≤ (1 + δ) * (m : ℝ) ^ (-A) := by
  have hcol := fpDist_col_le_explicitC
  unfold T_edgeWeight
  set c : ℝ := c_fpLocation with hcdef
  set C' : ℝ := C_fpCol with hC'def2
  have hc : 0 < c := c_fpLocation_pos
  have hC'pos : 0 < C' := C_fpCol_pos
  set ε : ℝ := min (δ / 8) 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min (by positivity) (by norm_num)
  have hεle2 : ε ≤ 2 := min_le_right _ _
  have hε8 : ε ≤ δ / 8 := min_le_left _ _
  have hminpos : 0 < min c (c ^ 2 / 20) := lt_min hc (by positivity)
  set Cf : ℕ := T_fstMgf A ε with hCfdef
  have hCf := fpDist_fst_mgf_le_at A hA ε hεpos
  set Ctf : ℕ := T_fstTail A (δ / 4) with hCtfdef
  have hCtf := fpDist_fst_tail_le_at A hA (δ / 4) (by positivity)
  set Cth : ℕ := T_holdTail A (δ / 4) with hCthdef
  have hCth := hold_fst_tail_le_at A hA (δ / 4) (by positivity)
  intro m hm s hs
  have hmCf : Cf ≤ m := by omega
  have hmCtf : Ctf ≤ m := by omega
  have hmCth : Cth ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hθnn : (0 : ℝ) ≤ 2 * A / (m : ℝ) := by positivity
  -- tilt smallness
  have h200 : (200 : ℝ) * A ≤ m :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast (show ⌈200 * A⌉₊ ≤ m by omega))
  have h10 : (10 : ℝ) * A / ε ≤ m :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast (show ⌈10 * A / ε⌉₊ ≤ m by omega))
  have hNc : (4 : ℝ) * A / min c (c ^ 2 / 20) ≤ m :=
    le_trans (Nat.le_ceil _)
      (by exact_mod_cast (show ⌈4 * A / min c (c ^ 2 / 20)⌉₊ ≤ m by omega))
  have hθ100 : 2 * A / (m : ℝ) ≤ 1 / 100 := by rw [div_le_iff₀ hmpos]; nlinarith [h200]
  have hθε : 2 * A / (m : ℝ) ≤ ε / 5 := by
    rw [div_le_iff₀ hmpos]
    have h' : 10 * A ≤ ε * m := by rw [div_le_iff₀ hεpos] at h10; linarith
    nlinarith [h']
  have hθmin : 2 * A / (m : ℝ) ≤ min c (c ^ 2 / 20) / 2 := by
    rw [div_le_iff₀ hmpos]
    have h' : 4 * A ≤ min c (c ^ 2 / 20) * m := by rw [div_le_iff₀ hminpos] at hNc; linarith
    nlinarith [h']
  -- cutoff `K` and budget for the fp-MGF summability
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlogsq_pos : 0 < Real.log m ^ 2 := by positivity
  set κ : ℝ := (m : ℝ) / Real.log m ^ 2 with hκdef
  have hκnn : 0 ≤ κ := by rw [hκdef]; positivity
  have hsκ : (s : ℝ) ≤ κ := hs
  set K : ℕ := ⌊κ⌋₊ + 25 with hKdef
  have hK25 : 25 ≤ K := by omega
  have hKlb : κ + 24 ≤ (K : ℝ) := by
    rw [hKdef]; push_cast; linarith [Nat.lt_floor_add_one κ]
  have hbud : (s : ℝ) * Real.log 2 ≤ ((K : ℝ) + 2) * Real.log 9 := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hlog9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
    have hlog29 : Real.log 2 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
    calc (s : ℝ) * Real.log 2 ≤ κ * Real.log 2 := mul_le_mul_of_nonneg_right hsκ hlog2.le
      _ ≤ κ * Real.log 9 := mul_le_mul_of_nonneg_left hlog29 hκnn
      _ ≤ ((K : ℝ) + 2) * Real.log 9 :=
          mul_le_mul_of_nonneg_right (by linarith [hKlb]) hlog9.le
  -- the two MGF summabilities that `fpDist_edgeWeight_split` needs
  have hZf_sum : Summable (fun e : ℕ × ℤ =>
      (fpDist s e).toReal * Real.exp (2 * A / (m : ℝ) * (e.1 : ℝ))) :=
    (fpDist_fst_mgf_general hc hC'pos hcol hθnn hθmin s K hK25 hbud).1
  have hZh_sum : Summable (fun d : ℕ × ℤ =>
      (hold d).toReal * Real.exp (2 * A / (m : ℝ) * (d.1 : ℝ))) := by
    have hne : ∑' d : ℕ × ℤ, hold d * expW2 (2 * A / (m : ℝ)) 0 d ≠ ∞ := by
      rw [← tiltZ]
      exact tiltZ_hold_ne_top (by linarith [hθ100]) (by norm_num) (by norm_num)
    refine (ENNReal.summable_toReal hne).congr (fun d => ?_)
    rw [expW2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    congr 2; ring
  -- apply the Fubini split, then bound each piece
  refine le_trans (fpDist_edgeWeight_split hA.le hm2 s hZf_sum hZh_sum) ?_
  set mA : ℝ := (m : ℝ) ^ (-A) with hmAdef
  have hmA0 : 0 < mA := by rw [hmAdef]; exact Real.rpow_pos_of_pos hmpos _
  set Zf : ℝ := ∑' e : ℕ × ℤ, (fpDist s e).toReal * Real.exp (2 * A / (m : ℝ) * (e.1 : ℝ))
    with hZfdef
  set Zh : ℝ := ∑' d : ℕ × ℤ, (hold d).toReal * Real.exp (2 * A / (m : ℝ) * (d.1 : ℝ))
    with hZhdef
  set Tf : ℝ := ∑' e : ℕ × ℤ, (fpDist s e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)
    with hTfdef
  set Th : ℝ := ∑' d : ℕ × ℤ, (hold d).toReal * (if m < 4 * d.1 then (1 : ℝ) else 0)
    with hThdef
  have hZh0 : 0 ≤ Zh := by
    rw [hZhdef]; exact tsum_nonneg fun d => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  -- `Z_fp ≤ 1+ε`
  have hZfb : Zf ≤ 1 + ε := by
    rw [hZfdef]
    refine le_trans (le_of_eq (tsum_congr (fun e => ?_))) (hCf m hmCf s hs)
    rw [show 2 * A / (m : ℝ) * (e.1 : ℝ) = 2 * A * (e.1 : ℝ) / (m : ℝ) by ring]
  -- `Z_hold ≤ 1+4θ+32θ² ≤ 1+ε`
  have hZhb : Zh ≤ 1 + ε := by
    rw [hZhdef]
    refine le_trans (hold_fst_mgf_le_real (by linarith [hθnn]) hθ100) ?_
    nlinarith [hθε, hθ100, hθnn, mul_le_mul_of_nonneg_left hθ100 hθnn]
  -- the two tails
  have hTfb : Tf ≤ δ / 4 * mA := by rw [hTfdef, hmAdef]; exact hCtf m hmCtf s hs
  have hThb : Th ≤ δ / 4 * mA := by rw [hThdef, hmAdef]; exact hCth m hmCth
  -- MGF term `≤ (1+δ/2)m^{−A}`
  have hquad : 2 * ε + ε ^ 2 ≤ δ / 2 := by nlinarith [hεle2, hε8, hεpos]
  have hMGF : mA * Zf * Zh ≤ (1 + δ / 2) * mA := by
    have h1 : mA * Zf * Zh ≤ mA * (1 + ε) * (1 + ε) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hZfb hmA0.le) hZhb hZh0 (by positivity)
    have h2 : mA * (1 + ε) * (1 + ε) ≤ (1 + δ / 2) * mA := by
      have hh := mul_le_mul_of_nonneg_left hquad hmA0.le
      calc mA * (1 + ε) * (1 + ε) = mA + mA * (2 * ε + ε ^ 2) := by ring
        _ ≤ mA + mA * (δ / 2) := by linarith [hh]
        _ = (1 + δ / 2) * mA := by ring
    linarith [h1, h2]
  calc mA * Zf * Zh + Tf + Th
      ≤ (1 + δ / 2) * mA + δ / 4 * mA + δ / 4 * mA :=
        add_le_add (add_le_add hMGF hTfb) hThb
    _ = (1 + δ) * mA := by ring



/-- `fpDist_edgeWeight_le`, original `∃`-form: delegates to the `_at` sibling at
`T_edgeWeight A δ`. -/
theorem fpDist_edgeWeight_le (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal * edgeWeight A m e
        ≤ (1 + δ) * (m : ℝ) ^ (-A) :=
  ⟨T_edgeWeight A δ, fpDist_edgeWeight_le_at A hA δ hδ⟩

/-- **The (7.52) budget bound** (paper p.48): a triangle point at depth `≤ m+1`
from the far edge has height budget `s = l_Δ - l ≤ (log 9/log 2)·(m+2)` (the
paper's `s ≤ (log 9/log 2)·m`, with lattice-floor slack — Case 3 only consumes
`s = O(m)`). From membership `(j - j_Δ)·log 9 + s·log 2 ≤ s_Δ` and confinement
of the lattice extent point `(j_Δ + ⌊s_Δ/log 9⌋, l_Δ)`, which forces
`s_Δ < (n/2 - j_Δ)·log 9`. -/
theorem budget_le_of_mem_triangle {n ξ : ℕ} (F : TriangleFamily n ξ)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ F.T) {j : ℕ} {l : ℤ}
    (hmem : (j, l) ∈ triangle t.1 t.2.1 t.2.2) {m : ℕ} (hjm : n / 2 ≤ j + 1 + m) :
    ((t.2.1 - l).toNat : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 := by
  obtain ⟨hj0, hl0, hlin⟩ := hmem
  have hsz0 : 0 ≤ t.2.2 := F.size_nonneg t ht
  have hlog9 : (0 : ℝ) < Real.log 9 := Real.log_pos (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the lattice extent point (j_Δ + ⌊s_Δ/log 9⌋, l_Δ) is in the triangle
  set K : ℕ := ⌊t.2.2 / Real.log 9⌋₊ with hK
  have hKle : (K : ℝ) * Real.log 9 ≤ t.2.2 := by
    have hfl : (K : ℝ) ≤ t.2.2 / Real.log 9 := Nat.floor_le (by positivity)
    calc (K : ℝ) * Real.log 9 ≤ t.2.2 / Real.log 9 * Real.log 9 :=
          mul_le_mul_of_nonneg_right hfl hlog9.le
      _ = t.2.2 := div_mul_cancel₀ _ hlog9.ne'
  have hqmem : ((t.1 + K, t.2.1) : ℕ × ℤ) ∈ triangle t.1 t.2.1 t.2.2 := by
    refine ⟨Nat.le_add_right _ _, le_refl _, ?_⟩
    push_cast
    have h : ((t.1 : ℝ) + K - t.1) * Real.log 9 = (K : ℝ) * Real.log 9 := by ring
    rw [h]
    simpa using hKle
  have hconf := F.confined t ht _ hqmem
  -- separation constant is nonnegative
  have hsep : (0 : ℝ) ≤ (1 / 10 : ℝ) * Real.log (1 / (epsBW : ℝ)) := by
    have heps : (1 : ℝ) / (epsBW : ℝ) = 10 ^ 1000 := by
      rw [show epsBW = 1 / 10 ^ 1000 from rfl]
      push_cast
      norm_num
    rw [heps]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  -- confinement in real form: t.1 + K + 1 ≤ n/2
  have h3 : (t.1 : ℝ) + K + 1 ≤ (n : ℝ) / 2 := by
    push_cast at hconf
    linarith
  -- real half vs floor half
  have h4 : (n : ℝ) / 2 ≤ ((n / 2 : ℕ) : ℝ) + 1 / 2 := by
    have hn : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hn
    linarith
  have h5 : ((n / 2 : ℕ) : ℝ) ≤ (j : ℝ) + 1 + m := by exact_mod_cast hjm
  -- the extent bound: s_Δ < (K+1)·log 9
  have hK1 : t.2.2 < ((K : ℝ) + 1) * Real.log 9 := by
    have hlt : t.2.2 / Real.log 9 < (K : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (t.2.2 / Real.log 9)
      exact_mod_cast this
    calc t.2.2 = t.2.2 / Real.log 9 * Real.log 9 := (div_mul_cancel₀ _ hlog9.ne').symm
      _ < ((K : ℝ) + 1) * Real.log 9 := mul_lt_mul_of_pos_right hlt hlog9
  -- cast the budget and the apex-left inequality
  have htn : (((t.2.1 - l).toNat : ℕ) : ℝ) = (t.2.1 : ℝ) - l := by
    have h := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ t.2.1 - l)
    have : (((t.2.1 - l).toNat : ℕ) : ℤ) = t.2.1 - l := h
    exact_mod_cast this
  have hj0R : (t.1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
  -- assemble
  have h6 : (K : ℝ) + 1 - j + t.1 ≤ (m : ℝ) + 2 := by linarith
  calc ((t.2.1 - l).toNat : ℝ) * Real.log 2
      = ((t.2.1 : ℝ) - l) * Real.log 2 := by rw [htn]
    _ ≤ t.2.2 - ((j : ℝ) - t.1) * Real.log 9 := by linarith [hlin]
    _ ≤ ((K : ℝ) + 1) * Real.log 9 - ((j : ℝ) - t.1) * Real.log 9 := by linarith
    _ = ((K : ℝ) + 1 - j + t.1) * Real.log 9 := by ring
    _ ≤ ((m : ℝ) + 2) * Real.log 9 := mul_le_mul_of_nonneg_right h6 hlog9.le

end TaoCollatz
