import TaoCollatz.Prob.Geometric
import TaoCollatz.Sec7.Setup
import TaoCollatz.Fourier.ZMod3
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §7.3–7.4: the holding distribution and the `Q` recursion (node X4)

Paper anchors: Tao 2019 §7.3, §7.4, (7.34)–(7.36). **Design decision D6**: the paper's
infinite renewal process is finitized by *defining* `Q` via the recursion (7.35) rather
than as an infinite product over an infinite iid sequence. This file validates D6.

* `hold` — the holding distribution `Hold` (§7.3); first coordinate always `≥ 1`.
* `Q` — the renewal value, well-founded on `half + 1 - j` (the walk only moves right).
* `Q_boundary`, `Q_rec` (7.35), `Q_nonneg`, `Q_le_one` — **proved**.

-- RATIFY-6: `Q` uses `j : ℕ` (paper coordinate; the renewal walk only increases `j`),
-- `l : ℤ`. Well-founded on `half + 1 - j`. `Q_le_one` takes `0 ≤ ε` (the paper's ε is a
-- fixed positive numeral, so this is free at every use site).
-/

open scoped ENNReal

namespace TaoCollatz

/-- The holding distribution `Hold` (§7.3): draw `k ~ Geom(4)`, then `k-1` iid
`pascalNe3` increments; output `(k, 3 + Σ increments)`. First coordinate is always `≥ 1`. -/
noncomputable def hold : PMF (ℕ × ℤ) :=
  geomQuarter.bind fun k => (pascalNe3.iid (k - 1)).map fun v => (k, (3 + ∑ i, v i : ℤ))

/-- The first coordinate of any `hold`-atom is positive (drives D6's termination). -/
theorem hold_support_fst_pos (d : ℕ × ℤ) (hd : d ∈ hold.support) : 1 ≤ d.1 := by
  rw [hold, PMF.mem_support_bind_iff] at hd
  obtain ⟨k, hk, hkd⟩ := hd
  rw [PMF.mem_support_map_iff] at hkd
  obtain ⟨v, _, hv⟩ := hkd
  have hk0 : k ≠ 0 := by
    intro h
    rw [PMF.mem_support_iff] at hk
    apply hk
    rw [h]
    rfl
  rw [← hv]
  exact Nat.one_le_iff_ne_zero.mpr hk0

/-- `hold` puts zero mass wherever the first coordinate is `0`. -/
theorem hold_zero_of_fst_zero {d : ℕ × ℤ} (h0 : d.1 = 0) : hold d = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro hd
  exact absurd (hold_support_fst_pos d hd) (by omega)

/-- `∑' d, (hold d).toReal = 1` (holding is a genuine probability distribution). -/
theorem hold_tsum_toReal : ∑' d : ℕ × ℤ, (hold d).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun d => hold.apply_ne_top d), hold.tsum_coe,
    ENNReal.toReal_one]

/-- `fun d => (hold d).toReal` is summable (mass is finite). -/
theorem hold_summable_toReal : Summable fun d : ℕ × ℤ => (hold d).toReal :=
  ENNReal.summable_toReal hold.tsum_coe_ne_top

/-- **D6 finitization.** The renewal value `Q` (paper (7.34)/(7.35)): `1` past the strip,
and a holding-averaged self-recursion inside it. Well-founded on `half + 1 - j` because
`hold`'s first coordinate is `≥ 1`, so each recursive call strictly increases `j`. -/
noncomputable def Q (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) : ℕ → ℤ → ℝ
  | j, l =>
    if half < j then 1
    else Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) *
      ∑' d : ℕ × ℤ,
        if hd : d.1 = 0 then 0
        else (hold d).toReal * Q half W ε (j + d.1) (l + d.2)
  termination_by j _ => half + 1 - j
  decreasing_by omega

/-- Boundary case (7.34): past the strip, `Q = 1`. -/
theorem Q_boundary (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (j : ℕ) (l : ℤ) (hj : half < j) :
    Q half W ε j l = 1 := by
  rw [Q]; simp [hj]

/-- The recursion (7.35): inside the strip, `Q` is a holding-averaged self-recursion. -/
theorem Q_rec (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (j : ℕ) (l : ℤ) (hj : j ≤ half) :
    Q half W ε j l = Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) *
      ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2) := by
  rw [Q]
  rw [if_neg (by omega : ¬ half < j)]
  congr 1
  apply tsum_congr
  intro d
  by_cases h0 : d.1 = 0
  · rw [dif_pos h0, hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul]
  · rw [dif_neg h0]

/-- `Q` is nonnegative. -/
theorem Q_nonneg (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) : ∀ j l, 0 ≤ Q half W ε j l := by
  have key : ∀ n j l, half + 1 - j = n → 0 ≤ Q half W ε j l := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro j l hn
      rcases Nat.lt_or_ge half j with hj | hj
      · rw [Q_boundary _ _ _ _ _ hj]; exact zero_le_one
      · rw [Q_rec _ _ _ _ _ hj]
        refine mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun d => ?_)
        rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
        · rw [hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul]
        · exact mul_nonneg ENNReal.toReal_nonneg
            (IH (half + 1 - (j + d.1)) (by omega) _ _ rfl)
  exact fun j l => key _ j l rfl

/-- `Q ≤ 1` (for the paper's nonnegative `ε`). -/
theorem Q_le_one (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ j l, Q half W ε j l ≤ 1 := by
  have key : ∀ n j l, half + 1 - j = n → Q half W ε j l ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro j l hn
      rcases Nat.lt_or_ge half j with hj | hj
      · rw [Q_boundary _ _ _ _ _ hj]
      · rw [Q_rec _ _ _ _ _ hj]
        have hexp : Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) ≤ 1 := by
          rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
          exact mul_nonneg (pow_nonneg hε 3)
            (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        have hterm : ∀ d : ℕ × ℤ,
            (hold d).toReal * Q half W ε (j + d.1) (l + d.2) ≤ (hold d).toReal := by
          intro d
          rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
          · rw [hold_zero_of_fst_zero h0, ENNReal.toReal_zero, zero_mul]
          · calc (hold d).toReal * Q half W ε (j + d.1) (l + d.2)
                ≤ (hold d).toReal * 1 :=
                  mul_le_mul_of_nonneg_left
                    (IH (half + 1 - (j + d.1)) (by omega) _ _ rfl) ENNReal.toReal_nonneg
              _ = (hold d).toReal := mul_one _
        have hterm_nonneg : ∀ d : ℕ × ℤ,
            0 ≤ (hold d).toReal * Q half W ε (j + d.1) (l + d.2) :=
          fun d => mul_nonneg ENNReal.toReal_nonneg (Q_nonneg _ _ _ _ _)
        have hsum_f : Summable fun d : ℕ × ℤ =>
            (hold d).toReal * Q half W ε (j + d.1) (l + d.2) :=
          Summable.of_nonneg_of_le hterm_nonneg hterm hold_summable_toReal
        have htsum : ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2) ≤ 1 :=
          le_trans (Summable.tsum_le_tsum hterm hsum_f hold_summable_toReal)
            hold_tsum_toReal.le
        calc Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) *
              ∑' d, (hold d).toReal * Q half W ε (j + d.1) (l + d.2)
            ≤ 1 * 1 := mul_le_mul hexp htsum (tsum_nonneg hterm_nonneg) zero_le_one
          _ = 1 := mul_one 1
  exact fun j l => key _ j l rfl

open Classical in
/-- **Proposition 7.3** (finitized, D6 form): the expected damping factor
`exp(-ε³ · #white encounters)` over the paired valuation vector `b ~ Pascal^{⌊n/2⌋}`
decays super-polynomially: `≤ C·n^{-A}` for every `A`. The count is over indices `j`
with `b_j = 3` landing at a white point `(j, b_{[1,j+1]})`. -/
theorem renewal_white_encounters (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → 1 ≤ n →
      (PMF.iid pascal (n / 2)).expect (fun b =>
        Real.exp (-((epsBW : ℝ) ^ 3) *
          ((Finset.univ.filter fun j : Fin (n / 2) =>
            b j = 3 ∧ white n ξ (j : ℕ) ((pre b ((j : ℕ) + 1) : ℤ))).card : ℝ)))
        ≤ C * (n : ℝ) ^ (-A) := by
  sorry

/-- **Proposition 7.1** (= Prop 1.17 restated through the (1.26) reversed form): the
character sum over the raw valuation vector `a ~ Geom(2)ⁿ` decays polynomially,
uniformly in `ξ` coprime to 3. Reduction chain (7.4)/(7.5) lives in grind laps. -/
theorem key_fourier_decay (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ∀ ξ : ZMod (3 ^ n), ¬ (3 ∣ ξ.val) →
      ‖(PMF.iid geomHalf n).cexpect fun a =>
          eC (-(ξ.val * ((∑ j ∈ Finset.range n,
            (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre a (j + 1)).val) : ℚ)
            / 3 ^ n)‖
        ≤ C * (n : ℝ) ^ (-A) := by
  sorry

end TaoCollatz
