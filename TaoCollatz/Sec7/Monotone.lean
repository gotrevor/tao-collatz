import TaoCollatz.Sec7.Holding
import TaoCollatz.Sec7.Triangles
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §7.4: the monotone quantity `Q_m` and Proposition 7.8 (node X7)

Paper anchors: Tao 2019 §7.4, (7.38), Proposition 7.8, Case 1 (7.42)–(7.43).

* `Qm` — paper (7.38): the weighted sup of `Q` over starting points within `m`
  columns of the strip's far edge, `Q_m := ⨆_{j ≥ ⌊n/2⌋-m, l} max(⌊n/2⌋-j, 1)^A · Q(j,l)`.
  The polynomial weight is INSIDE the sup and `m` measures depth from the FAR edge
  (ratified against the paper 2026-07-09, replacing an earlier inverted guess).
* `Qm_le_rpow` — the trivial base bound (7.39): `Q_m ≤ m^A`.
* `prop_7_8` — **Proposition 7.8 (Monotonicity)**: `Q_m ≤ Q_{m-1}` for
  `C_{A,ε} ≤ m ≤ ⌊n/2⌋`. Statement only (`sorry`).
* `Q_polynomial_decay` — the consequence (7.37) of (7.39) + Prop 7.8 by induction on `m`:
  `Q(j,l) ≪_A max(⌊n/2⌋-j, 1)^{-A}`, which feeds (7.36) `E Q(Hold) ≪_A n^{-A}` in Decay.lean.

The white set fed to `Q` is the §7.1 white set of `(n, ξ)` (paper (7.9)); `Q`'s `W`
parameter is the set where the `exp(-ε³)` damping applies — i.e. the WHITE points.
-/

open scoped ENNReal

namespace TaoCollatz

/-- The white set of `(n, ξ)` as a subset of the `(j,l)` lattice (the damping set for
the renewal value `Q`), in PAPER coordinates: membership of `(j, l)` reads the phase of
paper column `j`, i.e. `white n ξ (j - 1) l` — because `θq`/`black`/`white` are 0-based
(RATIFY-4) while `Q`/`Qm`/`prop_7_8` follow the paper's 1-based `j` (boundary
`⌊n/2⌋ < j`, weight `⌊n/2⌋ - j`, per RATIFY-6/7). The `1 ≤ p.1` guard keeps the
nonexistent paper column 0 out.

JUDGE FIX (2026-07-09 pass, vs paper (7.34) p.44): the earlier unshifted
`{p | white n ξ p.1 p.2}` made `Q`'s indicator consult the phase one column to the
RIGHT of the paper's. With this adapter, a paper walk point `(j, b_{[1,j]})` lands in
`whiteSet` iff `white n ξ (j-1) (b_{[1,j]})` — exactly the (0-based) test
`renewal_white_encounters` performs, so the future (7.36) bridge is coordinate-consistent. -/
def whiteSet (n ξ : ℕ) : Set (ℕ × ℤ) := {p | 1 ≤ p.1 ∧ white n ξ (p.1 - 1) p.2}

-- RATIFY-7 (resolved 2026-07-09 against paper p.45): (7.38) is
-- `Q_m := sup_{(j,l) : j ≥ ⌊n/2⌋ - m} max(⌊n/2⌋ - j, 1)^A · Q(j,l)` — the sup runs over
-- points within `m` columns of the FAR edge and carries the polynomial weight inside.
-- `half - p.1.1` is ℕ-truncated subtraction, which matches `max(⌊n/2⌋ - j, 1)` for `j > half`
-- via the `max · 1`. `⨆` is `Real.iSup` (set is nonempty; bounded via `Q_le_one` + weight ≤ m^A).
/-- Paper (7.38): the weighted worst-case renewal value at depth `m` from the far edge.
The `1 ≤ p.1` conjunct is the paper's `(j,l) ∈ (ℕ+1) × ℤ` (judge pass 2026-07-09:
without it the sup ranged over the nonexistent column `j = 0` too — an unfaithful
strengthening that could break `prop_7_8` at `m = ⌊n/2⌋`). -/
noncomputable def Qm (half : ℕ) (n ξ : ℕ) (ε A : ℝ) (m : ℕ) : ℝ :=
  ⨆ p : {p : ℕ × ℤ // 1 ≤ p.1 ∧ half - m ≤ p.1},
    ((max (half - p.1.1) 1 : ℕ) : ℝ) ^ A * Q half (whiteSet n ξ) ε p.1.1 p.1.2

/-- Paper (7.39), the induction base: `Q_m ≤ m^A` (from `Q ≤ 1` and the weight bound). -/
theorem Qm_le_rpow (half n ξ : ℕ) (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (hm : 1 ≤ m) :
    Qm half n ξ (epsBW : ℝ) A m ≤ (m : ℝ) ^ A := by
  have hε : (0 : ℝ) ≤ (epsBW : ℝ) := by unfold epsBW; positivity
  refine Real.iSup_le (fun p => ?_) (Real.rpow_nonneg (Nat.cast_nonneg m) A)
  have hw : ((max (half - p.1.1) 1 : ℕ) : ℝ) ^ A ≤ (m : ℝ) ^ A := by
    apply Real.rpow_le_rpow (by positivity) _ hA
    have hle : half - p.1.1 ≤ m := by obtain ⟨-, h2⟩ := p.2; omega
    exact_mod_cast max_le hle hm
  calc ((max (half - p.1.1) 1 : ℕ) : ℝ) ^ A * Q half (whiteSet n ξ) (epsBW : ℝ) p.1.1 p.1.2
      ≤ (m : ℝ) ^ A * 1 := by
        apply mul_le_mul hw (Q_le_one _ _ _ hε _ _) (Q_nonneg _ _ _ _ _)
        exact Real.rpow_nonneg (Nat.cast_nonneg m) A
    _ = (m : ℝ) ^ A := mul_one _

/-- **Proposition 7.8 (Monotonicity)**, paper p.45: `Q_m ≤ Q_{m-1}` whenever
`C_{A,ε} ≤ m ≤ ⌊n/2⌋`, for a sufficiently large threshold `C_{A,ε}` depending only on
`A` (our `ε = epsBW` is a fixed numeral, D4). Uniform in `n, ξ`. -/
theorem prop_7_8 (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      Qm (n / 2) n ξ (epsBW : ℝ) A m ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  sorry

/-- Paper (7.37), the consequence of (7.39) + Proposition 7.8 by forward induction on `m`:
`Q(j,l) ≪_A max(⌊n/2⌋ - j, 1)^{-A}`, uniformly in `n, ξ, j, l`. This is what feeds
(7.36) `E Q(Hold) ≪_A n^{-A}` and hence Proposition 7.3 in `Decay.lean`. -/
theorem Q_polynomial_decay (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ (j : ℕ) (l : ℤ), 1 ≤ j →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l ≤ C * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
  sorry

/-- Each admissible point's weighted value is below the `Qm` sup (the `le_ciSup`
direction; the range is bounded via `Q ≤ 1` and the weight cap `max(half,1)^A`). -/
theorem le_Qm (half n ξ : ℕ) (ε A : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε) (m : ℕ)
    {p1 : ℕ} {l : ℤ} (h1 : 1 ≤ p1) (h2 : half - m ≤ p1) :
    ((max (half - p1) 1 : ℕ) : ℝ) ^ A * Q half (whiteSet n ξ) ε p1 l
      ≤ Qm half n ξ ε A m := by
  have hbdd : BddAbove (Set.range fun p : {p : ℕ × ℤ // 1 ≤ p.1 ∧ half - m ≤ p.1} =>
      ((max (half - p.1.1) 1 : ℕ) : ℝ) ^ A * Q half (whiteSet n ξ) ε p.1.1 p.1.2) := by
    refine ⟨((max half 1 : ℕ) : ℝ) ^ A, ?_⟩
    rintro x ⟨p, rfl⟩
    calc ((max (half - p.1.1) 1 : ℕ) : ℝ) ^ A * Q half (whiteSet n ξ) ε p.1.1 p.1.2
        ≤ ((max half 1 : ℕ) : ℝ) ^ A * 1 := by
          apply mul_le_mul _ (Q_le_one _ _ _ hε _ _) (Q_nonneg _ _ _ _ _)
            (Real.rpow_nonneg (by positivity) A)
          apply Real.rpow_le_rpow (by positivity) _ hA
          exact_mod_cast max_le_max (Nat.sub_le _ _) le_rfl
      _ = ((max half 1 : ℕ) : ℝ) ^ A := mul_one _
  exact le_ciSup hbdd ⟨(p1, l), h1, h2⟩

/-- Inverted form: `Q(p) ≤ max(half - p₁, 1)^{-A} · Q_m` for admissible `p` — the
step that converts each hold-atom's landing value into a `Q_{m-1}` contribution in
Case 1/Case 2 of Prop 7.8. -/
theorem Q_le_Qm (half n ξ : ℕ) (ε A : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε) (m : ℕ)
    {p1 : ℕ} {l : ℤ} (h1 : 1 ≤ p1) (h2 : half - m ≤ p1) :
    Q half (whiteSet n ξ) ε p1 l
      ≤ ((max (half - p1) 1 : ℕ) : ℝ) ^ (-A) * Qm half n ξ ε A m := by
  have hwpos : (0:ℝ) < ((max (half - p1) 1 : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ max (half - p1) 1 := le_max_right _ _
    have : (1:ℝ) ≤ ((max (half - p1) 1 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hApos : (0:ℝ) < ((max (half - p1) 1 : ℕ) : ℝ) ^ A :=
    Real.rpow_pos_of_pos hwpos A
  have hle := le_Qm half n ξ ε A hA hε m (l := l) h1 h2
  rw [Real.rpow_neg hwpos.le]
  calc Q half (whiteSet n ξ) ε p1 l
      = (((max (half - p1) 1 : ℕ) : ℝ) ^ A)⁻¹
        * (((max (half - p1) 1 : ℕ) : ℝ) ^ A * Q half (whiteSet n ξ) ε p1 l) := by
        field_simp
    _ ≤ (((max (half - p1) 1 : ℕ) : ℝ) ^ A)⁻¹ * Qm half n ξ ε A m :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hApos.le)

/-- `Qm ≥ 0` (sup of nonnegative terms over a nonempty index). -/
theorem Qm_nonneg (half n ξ : ℕ) (ε A : ℝ) (m : ℕ) : 0 ≤ Qm half n ξ ε A m :=
  Real.iSup_nonneg fun p =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Q_nonneg _ _ _ _ _)

/-- **The Case 1 geometric-expectation leaf** ((7.43) numerics): the holding step's
first coordinate is `Geom(4)`-distributed, so the expected depth-weight ratio is
`1 + o(1)`; quantitatively `E[max(m - d₁, 1)^{-A}] ≤ exp(ε³/2)·m^{-A}` once
`m ≥ C_A`. Proof (2026-07-10): marginalize to `geomQuarter` via `hold_tsum_fst`, then a
three-region split with `δ := exp(ε³/2) - 1 > 0`: head `k ≤ K` (full mass, weight
`≤ (m-K)^{-A} ≤ (1+δ/3)m^{-A}` once `m ≥ ⌈Kc/(c-1)⌉` with `c := (1+δ/3)^{1/A}`),
middle `K < k ≤ m/2` (tail mass `(3/4)^K ≤ (δ/3)2^{-A}` by choice of `K`, weight
`≤ 2^A m^{-A}`), tail `k > m/2` (weight `≤ 1`, mass `(3/4)^{m/2} ≤ (δ/3)m^{-A}` for
large `m` since geometric beats polynomial). -/
theorem hold_weight_expect (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, 1 ≤ Cthr ∧ ∀ m : ℕ, Cthr ≤ m →
      ∑' d : ℕ × ℤ, (hold d).toReal * ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)
        ≤ Real.exp ((epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A) := by
  set E := Real.exp ((epsBW : ℝ) ^ 3 / 2) with hEdef
  have hεpos : (0 : ℝ) < (epsBW : ℝ) ^ 3 / 2 := by
    have h0 : (0 : ℚ) < epsBW := by unfold epsBW; norm_num
    have h1 : (0 : ℝ) < (epsBW : ℝ) := by exact_mod_cast h0
    positivity
  have hδ : 0 < E - 1 := by
    have h2 := Real.add_one_le_exp ((epsBW : ℝ) ^ 3 / 2)
    rw [hEdef]; linarith
  set δ := E - 1 with hδdef
  have hE1 : E = 1 + δ := by rw [hδdef]; ring
  -- middle-region cutoff K: geometric tail beats the δ/3-budget over the 2^A weight
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < δ / 3 * (2 : ℝ) ^ (-A) by positivity)
    (show (3 / 4 : ℝ) < 1 by norm_num)
  -- head-region constant c > 1 with c^A = 1 + δ/3
  set c := (1 + δ / 3) ^ A⁻¹ with hcdef
  have hc1 : 1 < c := by
    rw [hcdef, Real.one_lt_rpow_iff_of_pos (by linarith)]
    exact Or.inl ⟨by linarith, by positivity⟩
  have hcA : c ^ A = 1 + δ / 3 := by
    rw [hcdef, ← Real.rpow_mul (by linarith), inv_mul_cancel₀ hA.ne', Real.rpow_one]
  set M1 := ⌈(K : ℝ) * c / (c - 1)⌉₊ with hM1def
  -- tail-region threshold T from geometric × polynomial → 0
  set kA := ⌈A⌉₊ with hkAdef
  have htend : Filter.Tendsto (fun t : ℕ => (t : ℝ) ^ kA * (3 / 4 : ℝ) ^ t)
      Filter.atTop (nhds 0) := by
    have hs : Summable fun t : ℕ => (t : ℝ) ^ kA * (3 / 4 : ℝ) ^ t := by
      apply Summable.of_norm
      have h := summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) kA
        (r := (3 / 4 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)
      simpa using h
    exact hs.tendsto_atTop_zero
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (htend.eventually_lt_const (show (0 : ℝ) < δ / 3 * (3 : ℝ) ^ (-A) by positivity))
  refine ⟨K + M1 + 2 * T + 4, by omega, fun m hm => ?_⟩
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  -- marginalize the ℕ×ℤ sum onto the first coordinate
  refine le_trans (le_of_eq (hold_tsum_fst (fun k => ((max (m - k) 1 : ℕ) : ℝ) ^ (-A))
    (fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _))) ?_
  show ∑' k : ℕ, (geomQuarter k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
    ≤ E * (m : ℝ) ^ (-A)
  -- notation
  have hp0 : ∀ k, (0 : ℝ) ≤ (geomQuarter k).toReal := fun _ => ENNReal.toReal_nonneg
  have hw0 : ∀ k, (0 : ℝ) ≤ ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) :=
    fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hw1 : ∀ k, ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 := fun k =>
    Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast Nat.le_max_right (m - k) 1) (by linarith)
  have hterm_le : ∀ k, (geomQuarter k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
      ≤ (geomQuarter k).toReal := fun k => by
    calc (geomQuarter k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
        ≤ (geomQuarter k).toReal * 1 := mul_le_mul_of_nonneg_left (hw1 k) (hp0 k)
      _ = (geomQuarter k).toReal := mul_one _
  have hterm0 : ∀ k, (0 : ℝ) ≤ (geomQuarter k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) :=
    fun k => mul_nonneg (hp0 k) (hw0 k)
  have hpsum := geomQuarter_summable_toReal
  -- the three regions
  set g1 : ℕ → ℝ := fun k => if k ≤ K then
    (geomQuarter k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) else 0 with hg1def
  set g2 : ℕ → ℝ := fun k => if K < k ∧ k ≤ m / 2 then
    (geomQuarter k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) else 0 with hg2def
  set g3 : ℕ → ℝ := fun k => if K < k ∧ m / 2 < k then
    (geomQuarter k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) else 0 with hg3def
  have hsplit : ∀ k, (geomQuarter k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
      = g1 k + g2 k + g3 k := by
    intro k
    simp only [hg1def, hg2def, hg3def]
    rcases le_or_gt k K with h1 | h1
    · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]; ring
    · rcases le_or_gt k (m / 2) with h2 | h2
      · rw [if_neg (by omega), if_pos ⟨h1, h2⟩, if_neg (by omega)]; ring
      · rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2⟩]; ring
  have hg1sum : Summable g1 := Summable.of_nonneg_of_le
    (fun k => by simp only [hg1def]; split_ifs; exacts [hterm0 k, le_rfl])
    (fun k => by simp only [hg1def]; split_ifs; exacts [hterm_le k, hp0 k]) hpsum
  have hg2sum : Summable g2 := Summable.of_nonneg_of_le
    (fun k => by simp only [hg2def]; split_ifs; exacts [hterm0 k, le_rfl])
    (fun k => by simp only [hg2def]; split_ifs; exacts [hterm_le k, hp0 k]) hpsum
  have hg3sum : Summable g3 := Summable.of_nonneg_of_le
    (fun k => by simp only [hg3def]; split_ifs; exacts [hterm0 k, le_rfl])
    (fun k => by simp only [hg3def]; split_ifs; exacts [hterm_le k, hp0 k]) hpsum
  -- region 1 bound: full mass, weight ≤ (m-K)^{-A} ≤ (1+δ/3) m^{-A}
  have hmKpos : (0 : ℝ) < ((m - K : ℕ) : ℝ) := by
    have h : 1 ≤ m - K := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h
  have hW1 : ((m - K : ℕ) : ℝ) ^ (-A) ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) := by
    have hcast : ((m - K : ℕ) : ℝ) = (m : ℝ) - K := by
      rw [Nat.cast_sub (by omega)]
    have hcpos : (0 : ℝ) < c - 1 := by linarith
    have hmge : (K : ℝ) * c / (c - 1) ≤ (m : ℝ) := by
      calc (K : ℝ) * c / (c - 1) ≤ (M1 : ℝ) := Nat.le_ceil _
        _ ≤ (m : ℝ) := by exact_mod_cast (by omega : M1 ≤ m)
    have hKc : (K : ℝ) * c ≤ (m : ℝ) * (c - 1) := by
      rw [div_le_iff₀ hcpos] at hmge; linarith
    have hmc : (m : ℝ) / c ≤ (m : ℝ) - K := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < c)]
      nlinarith
    have hstep : ((m : ℝ) - K) ^ (-A) ≤ ((m : ℝ) / c) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hmc (by linarith)
    have hdiv : ((m : ℝ) / c) ^ (-A) = (m : ℝ) ^ (-A) * (1 + δ / 3) := by
      rw [Real.div_rpow hm0.le (by linarith : (0 : ℝ) ≤ c), Real.rpow_neg
        (by linarith : (0 : ℝ) ≤ c), div_inv_eq_mul, hcA]
    rw [hcast]
    calc ((m : ℝ) - K) ^ (-A) ≤ ((m : ℝ) / c) ^ (-A) := hstep
      _ = (1 + δ / 3) * (m : ℝ) ^ (-A) := by rw [hdiv]; ring
  have hreg1w : ∀ k, k ≤ K → ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ ((m - K : ℕ) : ℝ) ^ (-A) :=
    fun k hk => Real.rpow_le_rpow_of_nonpos hmKpos
      (by exact_mod_cast (by omega : m - K ≤ max (m - k) 1)) (by linarith)
  have hb1 : ∑' k, g1 k ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) := by
    have hle : ∀ k, g1 k ≤ (geomQuarter k).toReal * ((m - K : ℕ) : ℝ) ^ (-A) := fun k => by
      simp only [hg1def]; split_ifs with h
      · exact mul_le_mul_of_nonneg_left (hreg1w k h) (hp0 k)
      · exact mul_nonneg (hp0 k) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc ∑' k, g1 k
        ≤ ∑' k, (geomQuarter k).toReal * ((m - K : ℕ) : ℝ) ^ (-A) :=
          hg1sum.tsum_le_tsum hle (hpsum.mul_right _)
      _ = ((m - K : ℕ) : ℝ) ^ (-A) := by
          rw [tsum_mul_right, geomQuarter_tsum_toReal, one_mul]
      _ ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) := hW1
  -- region 2 bound: tail mass (3/4)^K, weight ≤ 2^A m^{-A}
  have hreg2w : ∀ k, k ≤ m / 2 →
      ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ (2 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
    intro k hk
    have hb : (m : ℝ) / 2 ≤ ((max (m - k) 1 : ℕ) : ℝ) := by
      have h2 : m ≤ 2 * max (m - k) 1 := by omega
      have h2' : (m : ℝ) ≤ 2 * ((max (m - k) 1 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hstep : ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ ((m : ℝ) / 2) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)
    have hdiv : ((m : ℝ) / 2) ^ (-A) = (2 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
      rw [Real.div_rpow hm0.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg
        (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      ring
    calc ((max (m - k) 1 : ℕ) : ℝ) ^ (-A) ≤ ((m : ℝ) / 2) ^ (-A) := hstep
      _ = (2 : ℝ) ^ A * (m : ℝ) ^ (-A) := hdiv
  have htailsum : Summable (fun k => if K < k then (geomQuarter k).toReal else 0) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs; exacts [hp0 k, le_rfl])
      (fun k => by split_ifs; exacts [le_rfl, hp0 k]) hpsum
  have hb2 : ∑' k, g2 k ≤ δ / 3 * (m : ℝ) ^ (-A) := by
    have hle : ∀ k, g2 k
        ≤ (if K < k then (geomQuarter k).toReal else 0)
          * ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) := by
      intro k
      simp only [hg2def]
      split_ifs with h1 h2
      · exact mul_le_mul_of_nonneg_left (hreg2w k h1.2) (hp0 k)
      · exact absurd h1.1 h2
      · exact mul_nonneg (hp0 k) (by positivity)
      · rw [zero_mul]
    calc ∑' k, g2 k
        ≤ ∑' k, (if K < k then (geomQuarter k).toReal else 0)
            * ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) :=
          hg2sum.tsum_le_tsum hle (htailsum.mul_right _)
      _ = (3 / 4 : ℝ) ^ K * ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) := by
          rw [tsum_mul_right, geomQuarter_tail]
      _ ≤ δ / 3 * (2 : ℝ) ^ (-A) * ((2 : ℝ) ^ A * (m : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_right hK.le (by positivity)
      _ = δ / 3 * ((2 : ℝ) ^ (-A) * (2 : ℝ) ^ A) * (m : ℝ) ^ (-A) := by ring
      _ = δ / 3 * (m : ℝ) ^ (-A) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel,
            Real.rpow_zero, mul_one]
  -- region 3 bound: weight ≤ 1, geometric tail mass beats the polynomial
  have htail3 : (3 / 4 : ℝ) ^ (m / 2) ≤ δ / 3 * (m : ℝ) ^ (-A) := by
    have ht1 : 1 ≤ m / 2 := by omega
    have htT : T ≤ m / 2 := by omega
    have htpos : (1 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by exact_mod_cast ht1
    have hhead := (hT (m / 2) htT).le
    have hm3t : (m : ℝ) ≤ 3 * ((m / 2 : ℕ) : ℝ) := by
      have h : m ≤ 3 * (m / 2) := by omega
      exact_mod_cast h
    -- (3/4)^t ≤ (δ/3 · 3^{-A}) · t^{-kA}
    have hcancel : ((m / 2 : ℕ) : ℝ) ^ (kA : ℝ) * ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) = 1 := by
      rw [← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero]
    have h1 : (3 / 4 : ℝ) ^ (m / 2)
        = ((m / 2 : ℕ) : ℝ) ^ kA * (3 / 4 : ℝ) ^ (m / 2) * ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) := by
      rw [mul_comm (((m / 2 : ℕ) : ℝ) ^ kA), mul_assoc, ← Real.rpow_natCast _ kA, hcancel,
        mul_one]
    have h2 : (3 / 4 : ℝ) ^ (m / 2)
        ≤ δ / 3 * (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) := by
      rw [h1]
      exact mul_le_mul_of_nonneg_right hhead (Real.rpow_nonneg (by linarith) _)
    have h3 : ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) ≤ ((m / 2 : ℕ) : ℝ) ^ (-A) := by
      apply Real.rpow_le_rpow_of_exponent_le htpos
      have := Nat.le_ceil A
      rw [neg_le_neg_iff]
      exact_mod_cast this
    have h4 : (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-A) ≤ (m : ℝ) ^ (-A) := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow_of_nonpos hm0 hm3t (by linarith)
    calc (3 / 4 : ℝ) ^ (m / 2)
        ≤ δ / 3 * (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-(kA : ℝ)) := h2
      _ ≤ δ / 3 * (3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-A) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = δ / 3 * ((3 : ℝ) ^ (-A) * ((m / 2 : ℕ) : ℝ) ^ (-A)) := by ring
      _ ≤ δ / 3 * (m : ℝ) ^ (-A) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have htail2sum : Summable (fun k => if m / 2 < k then (geomQuarter k).toReal else 0) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs; exacts [hp0 k, le_rfl])
      (fun k => by split_ifs; exacts [le_rfl, hp0 k]) hpsum
  have hb3 : ∑' k, g3 k ≤ δ / 3 * (m : ℝ) ^ (-A) := by
    have hle : ∀ k, g3 k ≤ (if m / 2 < k then (geomQuarter k).toReal else 0) := by
      intro k
      simp only [hg3def]
      split_ifs with h1 h2
      · exact hterm_le k
      · exact absurd h1.2 h2
      · exact hp0 k
      · exact le_rfl
    calc ∑' k, g3 k
        ≤ ∑' k, (if m / 2 < k then (geomQuarter k).toReal else 0) :=
          hg3sum.tsum_le_tsum hle htail2sum
      _ = (3 / 4 : ℝ) ^ (m / 2) := geomQuarter_tail (m / 2)
      _ ≤ δ / 3 * (m : ℝ) ^ (-A) := htail3
  -- assemble
  calc ∑' k : ℕ, (geomQuarter k).toReal * ((max (m - k) 1 : ℕ) : ℝ) ^ (-A)
      = ∑' k, g1 k + ∑' k, g2 k + ∑' k, g3 k := by
        rw [tsum_congr hsplit, (hg1sum.add hg2sum).tsum_add hg3sum, hg1sum.tsum_add hg2sum]
    _ ≤ (1 + δ / 3) * (m : ℝ) ^ (-A) + δ / 3 * (m : ℝ) ^ (-A) + δ / 3 * (m : ℝ) ^ (-A) :=
        add_le_add (add_le_add hb1 hb2) hb3
    _ = (1 + δ) * (m : ℝ) ^ (-A) := by ring
    _ = E * (m : ℝ) ^ (-A) := by rw [← hE1]

/-- **Case 1 proper** of Proposition 7.8 (paper (7.41)–(7.43), stated per the judge
item 8 spec, 2026-07-09): a white start at depth `m` from the far edge contracts by
`exp(-ε³/2)·m^{-A}` against `Q_{m-1}`.

Proof route (paper p.45): `Q_rec` pulls out the `exp(-ε³)` white factor
(`Q_white_contract` is the warm-up that stops there); each hold-atom `d` lands at
depth `≤ m - d₁ ≤ m - 1`, so `Q_le_Qm` bounds its value by
`max(m - d₁, 1)^{-A}·Q_{m-1}`; the remaining hold-expectation
`E[max(m - d₁, 1)^{-A}] ≤ exp(ε³/2)·m^{-A}` for `m ≥ C_A` is the geometric-tail
estimate (first marginal of `hold` is `Geom(4)`): split at `d₁ ≤ m/2`, where the
weight ratio `(m - d₁)^{-A}/m^{-A} ≤ 2^A` needs only `exp(ε³/2)`-room from the
sub-1 mass at `d₁ ≥ 1`, and the tail `P(d₁ > m/2) ≤ (3/4)^{m/2}` is
super-polynomial (that leaf is `hold_weight_expect`, proved). -/
theorem Q_white_case1 (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ,
      (n / 2 - m, l) ∈ whiteSet n ξ →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ Real.exp (-(epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A)
          * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  obtain ⟨C0, hC0one, hC0⟩ := hold_weight_expect A hA
  refine ⟨C0, fun n ξ _ m hm hmn l hw => ?_⟩
  set half := n / 2 with hhalf
  set ε : ℝ := (epsBW : ℝ) with hεdef
  have hε0 : (0 : ℝ) ≤ ε := by
    rw [hεdef]
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  have hm1 : 1 ≤ m := le_trans hC0one hm
  set QM := Qm half n ξ ε A (m - 1) with hQMdef
  have hQM0 : 0 ≤ QM := Qm_nonneg _ _ _ _ _ _
  rw [Q_rec _ _ _ _ _ (Nat.sub_le _ _)]
  have hind : Set.indicator (whiteSet n ξ) (1 : ℕ × ℤ → ℝ) (half - m, l) = 1 :=
    Set.indicator_of_mem hw 1
  -- per-atom: each hold-atom lands at depth ≤ m-1 with weight max(m-d₁,1)^{-A}
  have hatom : ∀ d : ℕ × ℤ,
      (hold d).toReal * Q half (whiteSet n ξ) ε (half - m + d.1) (l + d.2)
        ≤ (hold d).toReal * (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) := by
    intro d
    rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
    · rw [hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul, zero_mul]
    · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have h1 : 1 ≤ half - m + d.1 := by omega
      have h2 : half - (m - 1) ≤ half - m + d.1 := by omega
      have hkey := Q_le_Qm half n ξ ε A hA.le hε0 (m - 1) (l := l + d.2) h1 h2
      have heq : half - (half - m + d.1) = m - d.1 := by omega
      rwa [heq] at hkey
  have hble : ∀ d : ℕ × ℤ,
      (hold d).toReal * (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM)
        ≤ (hold d).toReal * QM := by
    intro d
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    calc ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM
        ≤ 1 * QM := mul_le_mul_of_nonneg_right
          (Real.rpow_le_one_of_one_le_of_nonpos
            (by exact_mod_cast Nat.le_max_right (m - d.1) 1) (by linarith)) hQM0
      _ = QM := one_mul _
  have hsumR : Summable fun d : ℕ × ℤ =>
      (hold d).toReal * (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hQM0))
      hble (hold_summable_toReal.mul_right QM)
  have hsumL : Summable fun d : ℕ × ℤ =>
      (hold d).toReal * Q half (whiteSet n ξ) ε (half - m + d.1) (l + d.2) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg (Q_nonneg _ _ _ _ _))
      (fun d => (hatom d).trans (hble d)) (hold_summable_toReal.mul_right QM)
  have htsum : ∑' d : ℕ × ℤ,
      (hold d).toReal * Q half (whiteSet n ξ) ε (half - m + d.1) (l + d.2)
        ≤ Real.exp (ε ^ 3 / 2) * (m : ℝ) ^ (-A) * QM := by
    calc ∑' d : ℕ × ℤ, (hold d).toReal * Q half (whiteSet n ξ) ε (half - m + d.1) (l + d.2)
        ≤ ∑' d : ℕ × ℤ, (hold d).toReal * (((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A) * QM) :=
          hsumL.tsum_le_tsum hatom hsumR
      _ = ∑' d : ℕ × ℤ, ((hold d).toReal * ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)) * QM :=
          tsum_congr fun d => (mul_assoc _ _ _).symm
      _ = (∑' d : ℕ × ℤ, (hold d).toReal * ((max (m - d.1) 1 : ℕ) : ℝ) ^ (-A)) * QM :=
          tsum_mul_right
      _ ≤ Real.exp (ε ^ 3 / 2) * (m : ℝ) ^ (-A) * QM :=
          mul_le_mul_of_nonneg_right (hC0 m hm) hQM0
  rw [hind, mul_one]
  calc Real.exp (-ε ^ 3) *
        ∑' d : ℕ × ℤ, (hold d).toReal * Q half (whiteSet n ξ) ε (half - m + d.1) (l + d.2)
      ≤ Real.exp (-ε ^ 3) * (Real.exp (ε ^ 3 / 2) * (m : ℝ) ^ (-A) * QM) :=
        mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
    _ = (Real.exp (-ε ^ 3) * Real.exp (ε ^ 3 / 2)) * ((m : ℝ) ^ (-A) * QM) := by ring
    _ = Real.exp (-ε ^ 3 / 2) * ((m : ℝ) ^ (-A) * QM) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ = Real.exp (-ε ^ 3 / 2) * (m : ℝ) ^ (-A) * QM := by ring

/-- **Case 1, warm-up form** ((7.42)–(7.43)): if the starting point is white, one step of
the recursion (7.35) already contracts by `exp(-ε³)`:
`Q (j,l) ≤ exp(-ε³) · sup_{d ∈ supp Hold} Q ((j,l)+d)`-shaped bound via the tsum. -/
theorem Q_white_contract (half : ℕ) (n ξ : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) (l : ℤ)
    (hj : j ≤ half) (hw : (j, l) ∈ whiteSet n ξ) :
    Q half (whiteSet n ξ) ε j l ≤ Real.exp (-(ε ^ 3)) := by
  rw [Q_rec _ _ _ _ _ hj]
  have hind : Set.indicator (whiteSet n ξ) (1 : ℕ × ℤ → ℝ) (j, l) = 1 :=
    Set.indicator_of_mem hw 1
  have hterm : ∀ d : ℕ × ℤ,
      (hold d).toReal * Q half (whiteSet n ξ) ε (j + d.1) (l + d.2) ≤ (hold d).toReal :=
    fun d => by
      calc (hold d).toReal * Q half (whiteSet n ξ) ε (j + d.1) (l + d.2)
          ≤ (hold d).toReal * 1 :=
            mul_le_mul_of_nonneg_left (Q_le_one _ _ _ hε _ _) ENNReal.toReal_nonneg
        _ = (hold d).toReal := mul_one _
  have hnn : ∀ d : ℕ × ℤ,
      0 ≤ (hold d).toReal * Q half (whiteSet n ξ) ε (j + d.1) (l + d.2) :=
    fun d => mul_nonneg ENNReal.toReal_nonneg (Q_nonneg _ _ _ _ _)
  have hsum : Summable fun d : ℕ × ℤ =>
      (hold d).toReal * Q half (whiteSet n ξ) ε (j + d.1) (l + d.2) :=
    Summable.of_nonneg_of_le hnn hterm hold_summable_toReal
  have htsum : ∑' d : ℕ × ℤ, (hold d).toReal * Q half (whiteSet n ξ) ε (j + d.1) (l + d.2)
      ≤ 1 :=
    le_trans (hsum.tsum_le_tsum hterm hold_summable_toReal) hold_tsum_toReal.le
  calc Real.exp (-(ε ^ 3) * Set.indicator (whiteSet n ξ) 1 (j, l)) *
        ∑' d : ℕ × ℤ, (hold d).toReal * Q half (whiteSet n ξ) ε (j + d.1) (l + d.2)
      ≤ Real.exp (-(ε ^ 3) * Set.indicator (whiteSet n ξ) 1 (j, l)) * 1 :=
        mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
    _ = Real.exp (-(ε ^ 3)) := by rw [hind, mul_one, mul_one]

end TaoCollatz
