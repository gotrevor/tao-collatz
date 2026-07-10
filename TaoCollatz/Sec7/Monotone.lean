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
the renewal value `Q`). -/
def whiteSet (n ξ : ℕ) : Set (ℕ × ℤ) := {p | white n ξ p.1 p.2}

-- RATIFY-7 (resolved 2026-07-09 against paper p.45): (7.38) is
-- `Q_m := sup_{(j,l) : j ≥ ⌊n/2⌋ - m} max(⌊n/2⌋ - j, 1)^A · Q(j,l)` — the sup runs over
-- points within `m` columns of the FAR edge and carries the polynomial weight inside.
-- `half - p.1.1` is ℕ-truncated subtraction, which matches `max(⌊n/2⌋ - j, 1)` for `j > half`
-- via the `max · 1`. `⨆` is `Real.iSup` (set is nonempty; bounded via `Q_le_one` + weight ≤ m^A).
/-- Paper (7.38): the weighted worst-case renewal value at depth `m` from the far edge. -/
noncomputable def Qm (half : ℕ) (n ξ : ℕ) (ε A : ℝ) (m : ℕ) : ℝ :=
  ⨆ p : {p : ℕ × ℤ // half - m ≤ p.1},
    ((max (half - p.1.1) 1 : ℕ) : ℝ) ^ A * Q half (whiteSet n ξ) ε p.1.1 p.1.2

/-- Paper (7.39), the induction base: `Q_m ≤ m^A` (from `Q ≤ 1` and the weight bound). -/
theorem Qm_le_rpow (half n ξ : ℕ) (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (hm : 1 ≤ m) :
    Qm half n ξ (epsBW : ℝ) A m ≤ (m : ℝ) ^ A := by
  have hε : (0 : ℝ) ≤ (epsBW : ℝ) := by unfold epsBW; positivity
  refine Real.iSup_le (fun p => ?_) (Real.rpow_nonneg (Nat.cast_nonneg m) A)
  have hw : ((max (half - p.1.1) 1 : ℕ) : ℝ) ^ A ≤ (m : ℝ) ^ A := by
    apply Real.rpow_le_rpow (by positivity) _ hA
    have hle : half - p.1.1 ≤ m := by have := p.2; omega
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
    ∃ C > 0, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ (j : ℕ) (l : ℤ),
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l ≤ C * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
  sorry

/-- **Case 1** of Prop 7.8 ((7.42)–(7.43)): if the starting point is white, one step of
the recursion (7.35) already contracts by `exp(-ε³)`:
`Q (j,l) ≤ exp(-ε³) · sup_{d ∈ supp Hold} Q ((j,l)+d)`-shaped bound via the tsum. -/
theorem Q_white_contract (half : ℕ) (n ξ : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) (l : ℤ)
    (hj : j ≤ half) (hw : white n ξ j l) :
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
