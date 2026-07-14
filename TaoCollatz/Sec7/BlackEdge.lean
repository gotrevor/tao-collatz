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
theorem exists_triangleFamily (n ξ : ℕ) (hξ : ¬ 3 ∣ ξ) (hn : 1 ≤ n) :
    Nonempty (TriangleFamily n ξ) := by
  obtain ⟨T, h0, hcanonical, h1, h2, h3⟩ := black_structure n ξ hξ hn
  exact ⟨⟨T, h0, hcanonical, h1, h2, h3⟩⟩

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
    push_neg at hbig  -- `2 * J ≤ m`
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

/-- **Numeric core of `fpDist_fst_mgf_le`** — the explicit threshold `Cthr` and the
per-`(m,s)` split point `K` bundling all the constant-juggling estimates that the
mechanical Fubini/split assembly consumes.  With `θ = 2A/m` and
`K = ⌊m·log(1+δ/2)/(2A)⌋` this asserts: (a) the tilt lands in `gaussExp_col_tail`'s
range `θ ≤ ½·min(c, c²/20)`; (b) the `gaussExp` cutoff budget `s·log2 ≤ (K+2)·log9`
(from `s ≤ m/log²m`, `K = Θ(m)`); (c) the bulk factor `exp(θK) ≤ 1+δ/2` (floor of
`K`); (d) the `gaussExp` tail RHS at cutoff `K` is `≤ δ/2` (super-exponential decay
`x₀ = K+1-s/4 = Θ(m)` beats the bounded prefactor `exp(θs/4) ≤ exp(A/2)`).

OPEN (the analytic tail-threshold; route sound via `gaussExp_col_tail`).  The
mechanical assembly `fpDist_fst_mgf_le` below is PROVED off this interface. -/
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
                / (1 - Real.exp (-(c - 2 * A / (m : ℝ))))) ≤ δ / 2 := by
  sorry

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
on the bulk; the envelope is used only where it is exponentially slack. -/
theorem fpDist_fst_mgf_le (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal * Real.exp (2 * A * (e.1 : ℝ) / (m : ℝ))
        ≤ 1 + δ := by
  obtain ⟨c, hc, C', hC'pos, hcol⟩ := fpDist_col_le
  obtain ⟨Cthr, hCthr25, hnum⟩ := fpDist_fst_mgf_numeric hA hδ hc hC'pos
  refine ⟨Cthr, fun m hm s hs => ?_⟩
  obtain ⟨K, hK25, hθle, hbud, hbulk, htail⟩ := hnum m hm s hs
  have hmpos : (0 : ℝ) < m := by
    have h25 : (25 : ℕ) ≤ m := le_trans hCthr25 hm
    exact_mod_cast lt_of_lt_of_le (by norm_num) h25
  set θ : ℝ := 2 * A / (m : ℝ) with hθdef
  have hθ0 : (0 : ℝ) ≤ θ := by rw [hθdef]; positivity
  -- rewrite the exponent `2A·e.1/m` as `θ·e.1`
  have hexp : ∀ e : ℕ × ℤ, 2 * A * (e.1 : ℝ) / (m : ℝ) = θ * (e.1 : ℝ) := by
    intro e; rw [hθdef]; ring
  simp_rw [hexp]
  -- abbreviations
  set f : ℕ × ℤ → ℝ := fun e => (fpDist s e).toReal * Real.exp (θ * (e.1 : ℝ)) with hfdef
  set M : ℕ → ℝ := fun j => ∑' l : ℤ, (fpDist s (j, l)).toReal with hMdef
  have hMnn : ∀ j : ℕ, 0 ≤ M j := fun j => tsum_nonneg (fun _ => ENNReal.toReal_nonneg)
  -- summability of the raw `fpDist` mass (2-D) and its column slices
  have hfp2d : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal) :=
    ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
  have hfpcol : ∀ j : ℕ, Summable (fun l : ℤ => (fpDist s (j, l)).toReal) :=
    fun j => hfp2d.comp_injective (fun _ _ h => by simpa using h)
  have hfcol : ∀ j : ℕ, Summable (fun l : ℤ => f (j, l)) := by
    intro j; simp only [hfdef]; exact (hfpcol j).mul_right _
  -- the column marginal of `f`
  have hg_eq : ∀ j : ℕ, (∑' l : ℤ, f (j, l)) = M j * Real.exp (θ * (j : ℝ)) := by
    intro j
    have hcongr : ∀ l : ℤ, f (j, l) = (fpDist s (j, l)).toReal * Real.exp (θ * (j : ℝ)) :=
      fun l => by simp only [hfdef]
    rw [tsum_congr hcongr, tsum_mul_right, hMdef]
  have hgnn : ∀ j : ℕ, 0 ≤ ∑' l : ℤ, f (j, l) :=
    fun j => tsum_nonneg (fun l => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
  -- the dominating envelope `U = (bulk, capped at exp θK) + (gaussExp tail column)`
  set U : ℕ → ℝ := fun j =>
    (if j ≤ K then Real.exp (θ * (K : ℝ)) * M j else 0)
      + (if K < j then Real.exp (θ * (j : ℝ)) *
          (C' * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4))
                  / Real.sqrt (1 + (s : ℝ)))) else 0) with hUdef
  obtain ⟨hsumT, hleT⟩ := gaussExp_col_tail hc hC'pos.le hθ0 hθle s K hK25 hbud
  have hbulksum : Summable
      (fun j : ℕ => if j ≤ K then Real.exp (θ * (K : ℝ)) * M j else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range (K + 1)) (fun j hj => ?_)
    have hnle : ¬ j ≤ K := by simp only [Finset.mem_range, not_lt] at hj; omega
    rw [if_neg hnle]
  have hUsum : Summable U := hbulksum.add hsumT
  -- `g ≤ U` pointwise
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
  -- 2-D summability of `f` via Tonelli, then Fubini to the column marginals
  have hfsum : Summable f :=
    (summable_prod_of_nonneg
        (fun e => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)).mpr
      ⟨hfcol, Summable.of_nonneg_of_le hgnn hgU hUsum⟩
  rw [Summable.tsum_prod' hfsum hfcol]
  -- total `fpDist` mass and the marginal-mass facts for the bulk
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
  -- assemble: `∑ g ≤ ∑ U = bulk + tail ≤ (1+δ/2) + δ/2 = 1+δ`
  calc ∑' (j : ℕ), ∑' (l : ℤ), f (j, l)
      ≤ ∑' (j : ℕ), U j :=
        Summable.tsum_le_tsum hgU (Summable.of_nonneg_of_le hgnn hgU hUsum) hUsum
    _ = (∑' j : ℕ, if j ≤ K then Real.exp (θ * (K : ℝ)) * M j else 0)
          + ∑' j : ℕ, if K < j then Real.exp (θ * (j : ℝ)) *
              (C' * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4))
                      / Real.sqrt (1 + (s : ℝ)))) else 0 := by
        simp only [hUdef]; exact hbulksum.tsum_add hsumT
    _ ≤ (1 + δ / 2) + δ / 2 := by
        refine add_le_add ?_ (hleT.trans htail)
        have hb1 : (fun j : ℕ => if j ≤ K then Real.exp (θ * (K : ℝ)) * M j else 0)
            = fun j => Real.exp (θ * (K : ℝ)) * (if j ≤ K then M j else 0) := by
          funext j; by_cases hjK : j ≤ K <;> simp [hjK]
        rw [hb1, tsum_mul_left]
        have hstep : (∑' j : ℕ, if j ≤ K then M j else 0) ≤ 1 := by rw [← hmassM]; exact hindle
        calc Real.exp (θ * (K : ℝ)) * (∑' j : ℕ, if j ≤ K then M j else 0)
            ≤ Real.exp (θ * (K : ℝ)) * 1 :=
              mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
          _ = Real.exp (θ * (K : ℝ)) := mul_one _
          _ ≤ 1 + δ / 2 := hbulk
    _ = 1 + δ := by ring

/-- **The (7.48)/(7.49) weight degradation, Case 2** (paper p.47). With budget
`s ≤ m/log²m`, the first-passage endpoint's `j`-coordinate concentrates near
`s/4 ≪ m/log²m` (Lemma 7.7 = `fpDist_location_bound`, node X6), so the average
depth weight `E[edgeWeight]` exceeds `m^{-A}` only by `exp(O(A·log m/m ·
m/log²m)) = 1 + O(A/log m) ≤ 1 + δ` once `m ≥ C_{A,δ}` ((7.42) concavity bound
+ Chernoff truncation of `j_{[1,k]} > m/log²m`).

DECOMPOSITION (2026-07-14): the pointwise bound `edgeWeight_summand_le` reduces
this to (i) the MGF factor `Z_{fp,fst}(2A/m)·Z_{hold,fst}(2A/m) ≤ 1 + δ/2` and
(ii) the tail `P(e.1+d.1 > m/2) ≤ (δ/2)·m^{-A}`.  Both depend on the first-coord
`fpDist` MGF `fpDist_fst_mgf_le` (the hold factors are `tiltZ_hold_fst_le`);
`Z_{hold,fst}(2A/m) → 1` and the tail is a Chernoff of `fpDist_fst_mgf_le`
(`e.1 > m/4`) + a `hold` Chernoff (`d.1 > m/4`, `holdSum_halfspace_le`).

OPEN (node X8): reduces to `fpDist_fst_mgf_le` + `edgeWeight_summand_le` (proved)
+ glue (double-`tsum` algebra, no new analytic content). -/
theorem fpDist_edgeWeight_le (A : ℝ) (hA : 0 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cthr : ℕ, ∀ m : ℕ, Cthr ≤ m → ∀ s : ℕ,
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal * edgeWeight A m e
        ≤ (1 + δ) * (m : ℝ) ^ (-A) := by
  sorry

/-- **The (7.50)/(7.51) white-exit bound** (paper p.48): starting the renewal
walk at a black edge point `(⌊n/2⌋-m, l)` whose phase point `(⌊n/2⌋-m-1, l)`
lies in triangle `t` of the family, with budget `s = l_Δ - l ≤ m/log²m`, the
first-passage endpoint is WHITE and IN-STRIP with probability `≥ p₀` for an
absolute `p₀ > 0` (uniform in `n, ξ, m, l, t`).

Route ((7.50): Lemma 7.7 puts the endpoint at `(j + s/4 + O((1+s)^{1/2}),
l_Δ + O(1))` with probability `≫ 1`; every endpoint exceeds height `l_Δ`
(`fpDist_support_snd_gt`), i.e. lies strictly above the triangle top; the
(7.11) slope bound `-O(1) ≤ (j'-j_Δ)log 9 ≤ s_Δ + O(1)` plus the family
separation put it outside every OTHER triangle, hence white by `cover`;
in-strip follows from `s/4 + O(√(1+s)) ≪ m`.

OPEN (node X8, the hardest Case-2 kernel): consumes `fpDist_location_bound`
(X6) and the geometric fight between the paper's `O(1)` exit-ring constants
and the fixed `ε = 10⁻⁴` separation `(1/10)·log(1/ε) ≈ 0.92` — numerically
validated ≈ 0.99 white-exit mass (harness check 9, 2026-07-10). -/
theorem fpDist_white_exit :
    ∃ p₀ > (0 : ℝ), ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamily n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      p₀ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) := by
  sorry

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

/-- **Case 2 of Proposition 7.8** ((7.46)–(7.51) assembly, paper pp.46–48):
black edge start whose triangle-top budget satisfies `s ≤ m/log²m`. Route:
`Q_le_fpDist_expect` ((7.45) entry) + `Q_fp_endpoint_le` per endpoint, then
the (7.47) split `E[(1-(1-e^{-ε³})·1_W)·w] ≤ E[w] - (1-e^{-ε³})·m^{-A}·P(W)`
(using `w ≥ m^{-A}` pointwise), bounded via `fpDist_edgeWeight_le` (δ :=
`(1-e^{-ε³})·p₀/2`) and `fpDist_white_exit`:
`Q ≤ ((1+δ) - (1-e^{-ε³})·p₀)·m^{-A}·Q_{m-1} ≤ m^{-A}·Q_{m-1}`.

OPEN (node X8 assembly): mechanical once the two kernels above land; the
remaining work is `ℝ≥0∞`→`ℝ` bookkeeping across the fpDist tsum. -/
theorem Q_black_edge_case2 (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  sorry

/-- **The (7.41) edge bound for BLACK starts** (Cases 2–3 of Proposition 7.8,
paper (7.44)–(7.67), pp.46–49): the case split. The black phase point
`(⌊n/2⌋-m-1, l)` lies in a triangle of the family (`cover`); its budget
`s := l_Δ - l` is `≤ (log 9/log 2)·(m+1)` by (7.52); Case 2 handles
`s ≤ m/log²m`, Case 3 the rest. The Case 3 bound is an explicit argument so
the downstream X11 module can close the assembly without a cycle. -/
theorem Q_black_edge_of_case3 (A : ℝ) (hA : 0 < A)
    (hcase3 :
      ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
        ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
        ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
        ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
        (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
        (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
        Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
          ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ,
      1 ≤ n / 2 - m → (n / 2 - m, l) ∉ whiteSet n ξ →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  classical
  obtain ⟨C2, hC2⟩ := Q_black_edge_case2 A hA
  obtain ⟨C3, hC3⟩ := hcase3
  refine ⟨max C2 C3, fun n ξ hξ m hm hmn l h1 hnw => ?_⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨F⟩ := exists_triangleFamily n ξ hξ hn1
  -- the phase point is black
  have hb : black n ξ (n / 2 - m - 1) l := by
    by_contra hw
    exact hnw ⟨h1, hw⟩
  -- hence lies in some triangle of the family
  have hmem0 : (n / 2 - m - 1, l) ∈
      {p : ℕ × ℤ | p.1 + 1 ≤ n / 2 ∧ black n ξ p.1 p.2} := ⟨by omega, hb⟩
  rw [F.cover] at hmem0
  simp only [Set.mem_iUnion, exists_prop] at hmem0
  obtain ⟨t, ht, hmem⟩ := hmem0
  -- the height budget
  have hl : l ≤ t.2.1 := hmem.2.1
  set s : ℕ := (t.2.1 - l).toNat with hs
  have hsZ : (s : ℤ) = t.2.1 - l := by omega
  -- (7.52): s·log 2 ≤ (m+1)·log 9
  have hbudget : (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 :=
    budget_le_of_mem_triangle F ht hmem (by omega)
  rcases le_or_gt (s : ℝ) ((m : ℝ) / Real.log m ^ 2) with hcase | hcase
  · exact hC2 n ξ hξ F m (le_trans (le_max_left _ _) hm) hmn l h1
      t ht hmem s hsZ hcase
  · exact hC3 n ξ hξ F m (le_trans (le_max_right _ _) hm) hmn l h1
      t ht hmem s hsZ hcase hbudget

/-- **Proposition 7.8 (Monotonicity)**, paper p.45: `Q_m ≤ Q_{m-1}` whenever
`C_{A,ε} ≤ m ≤ ⌊n/2⌋`, for a sufficiently large threshold `C_{A,ε}` depending only on
`A` (our `ε = epsBW` is a fixed numeral, D4). Uniform in `n, ξ`.

Proof: the `Qm m` sup splits. Interior points (`p₁ > ⌊n/2⌋ - m`) are admissible at
depth `m-1` with the same weight, so `le_Qm` bounds them by `Q_{m-1}` directly. Edge
points (`p₁ = ⌊n/2⌋ - m`, weight `m^A`) satisfy (7.41) `Q ≤ m^{-A}·Q_{m-1}`: white
starts by `Q_white_case1` (Case 1, proved), black starts by the supplied
`Q_black_edge` bound. -/
theorem prop_7_8_of_black_edge (A : ℝ) (hA : 0 < A)
    (hblack :
      ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
        ∀ l : ℤ, 1 ≤ n / 2 - m → (n / 2 - m, l) ∉ whiteSet n ξ →
        Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
          ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      Qm (n / 2) n ξ (epsBW : ℝ) A m ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  obtain ⟨C1, hC1⟩ := Q_white_case1 A hA
  obtain ⟨C2, hC2⟩ := hblack
  refine ⟨max (max C1 C2) 1, fun n ξ hξ m hm hmn => ?_⟩
  have hmC1 : C1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmC2 : C2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hε0 : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hQM0 : 0 ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := Qm_nonneg _ _ _ _ _ _
  have hcancel : (m : ℝ) ^ A * (m : ℝ) ^ (-A) = 1 := by
    rw [← Real.rpow_add hm0, add_neg_cancel, Real.rpow_zero]
  refine Real.iSup_le (fun p => ?_) hQM0
  obtain ⟨⟨p1, l⟩, hp1, hpm⟩ := p
  have hp1' : 1 ≤ p1 := hp1
  have hpm' : n / 2 - m ≤ p1 := hpm
  show ((max (n / 2 - p1) 1 : ℕ) : ℝ) ^ A * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) p1 l
    ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)
  rcases eq_or_lt_of_le hpm' with heq | hlt
  · -- edge point: p1 = n/2 - m, weight = m^A
    have hp1eq : p1 = n / 2 - m := heq.symm
    have hwt : (max (n / 2 - p1) 1 : ℕ) = m := by omega
    have hedge : Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) p1 l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
      by_cases hw : (p1, l) ∈ whiteSet n ξ
      · have h := hC1 n ξ hξ m hmC1 hmn l (hp1eq ▸ hw)
        rw [hp1eq]
        calc Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
            ≤ Real.exp (-(epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A)
              * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := h
          _ ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
              apply mul_le_mul_of_nonneg_right _ hQM0
              have hexp : Real.exp (-(epsBW : ℝ) ^ 3 / 2) ≤ 1 := by
                rw [Real.exp_le_one_iff]
                have h3 : (0 : ℝ) ≤ (epsBW : ℝ) ^ 3 := by positivity
                linarith
              calc Real.exp (-(epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A)
                  ≤ 1 * (m : ℝ) ^ (-A) :=
                    mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hm0.le _)
                _ = (m : ℝ) ^ (-A) := one_mul _
      · exact hp1eq ▸ hC2 n ξ hξ m hmC2 hmn l (by omega) (hp1eq ▸ hw)
    calc ((max (n / 2 - p1) 1 : ℕ) : ℝ) ^ A * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) p1 l
        ≤ ((max (n / 2 - p1) 1 : ℕ) : ℝ) ^ A
            * ((m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :=
          mul_le_mul_of_nonneg_left hedge (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (m : ℝ) ^ A * (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
          rw [hwt]; ring
      _ = Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by rw [hcancel, one_mul]
  · -- interior point: admissible at depth m-1 with the same weight
    exact le_Qm (n / 2) n ξ (epsBW : ℝ) A hA.le hε0 (m - 1) hp1 (by omega)

/-- Paper (7.37), the consequence of (7.39) + Proposition 7.8 by forward induction on `m`:
`Q(j,l) ≪_A max(⌊n/2⌋ - j, 1)^{-A}`, uniformly in `n, ξ, j, l`. This is what feeds
(7.36) `E Q(Hold) ≪_A n^{-A}` and hence Proposition 7.3 in `Decay.lean`. -/
theorem Q_polynomial_decay_of_prop_7_8 (A : ℝ) (hA : 0 < A)
    (hmono :
      ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
        Qm (n / 2) n ξ (epsBW : ℝ) A m
          ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :
    ∃ C > 0, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ (j : ℕ) (l : ℤ), 1 ≤ j →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l ≤ C * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
  obtain ⟨C0, hC0⟩ := hmono
  set Cb := max C0 1 with hCbdef
  have hCb1 : 1 ≤ Cb := le_max_right _ _
  have hCbR : (1 : ℝ) ≤ ((Cb : ℕ) : ℝ) := by exact_mod_cast hCb1
  have hCbA1 : (1 : ℝ) ≤ ((Cb : ℕ) : ℝ) ^ A := by
    calc (1 : ℝ) = (1 : ℝ) ^ A := (Real.one_rpow A).symm
      _ ≤ ((Cb : ℕ) : ℝ) ^ A := Real.rpow_le_rpow zero_le_one hCbR hA.le
  refine ⟨((Cb : ℕ) : ℝ) ^ A, Real.rpow_pos_of_pos (by linarith) A, ?_⟩
  intro n ξ hξ j l hj
  have hε0 : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  -- the uniform bound Q_m ≤ Cb^A for 1 ≤ m ≤ n/2, by forward induction from (7.39)
  have hQmb : ∀ m : ℕ, 1 ≤ m → m ≤ n / 2 →
      Qm (n / 2) n ξ (epsBW : ℝ) A m ≤ ((Cb : ℕ) : ℝ) ^ A := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro hm1 hmn
      rcases le_or_gt m Cb with hle | hgt
      · calc Qm (n / 2) n ξ (epsBW : ℝ) A m ≤ (m : ℝ) ^ A := Qm_le_rpow _ _ _ _ hA.le _ hm1
          _ ≤ ((Cb : ℕ) : ℝ) ^ A :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) hA.le
      · have h78 := hC0 n ξ hξ m (by omega) hmn
        exact le_trans h78 (IH (m - 1) (by omega) (by omega) (by omega))
  rcases Nat.lt_or_ge j (n / 2) with hjlt | hjge
  · -- inside the strip: use le_Qm at depth m = n/2 - j, then the uniform bound
    have hle := Q_le_Qm (n / 2) n ξ (epsBW : ℝ) A hA.le hε0 (n / 2 - j) (l := l) hj
      (by omega)
    calc Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l
        ≤ ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A)
            * Qm (n / 2) n ξ (epsBW : ℝ) A (n / 2 - j) := hle
      _ ≤ ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) * (((Cb : ℕ) : ℝ) ^ A) :=
          mul_le_mul_of_nonneg_left (hQmb (n / 2 - j) (by omega) (by omega))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = ((Cb : ℕ) : ℝ) ^ A * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := mul_comm _ _
  · -- past the strip edge: Q ≤ 1 and the weight is 1
    have hw : (max (n / 2 - j) 1 : ℕ) = 1 := by omega
    calc Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l ≤ 1 := Q_le_one _ _ _ hε0 _ _
      _ ≤ ((Cb : ℕ) : ℝ) ^ A := hCbA1
      _ = ((Cb : ℕ) : ℝ) ^ A * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
          rw [hw, Nat.cast_one, Real.one_rpow, mul_one]

end TaoCollatz
