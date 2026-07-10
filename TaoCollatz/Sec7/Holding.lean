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
-- JUDGE ADDENDUM (2026-07-09, ratified vs (7.34)/(7.35) p.44): because `Q`'s `j` is the
-- paper's 1-based coordinate, any `W` fed to `Q` must be a PAPER-coordinate set —
-- `whiteSet` in `Monotone.lean` is the shift adapter onto the 0-based `white` (RATIFY-4).
-- `Q`/`Q_rec`/`Q_boundary` themselves are generic in `W` and verbatim (7.34)/(7.35).
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

/-- The first marginal of `hold` is `Geom(4)` (the `k`-draw is passed through). -/
theorem hold_map_fst : hold.map Prod.fst = geomQuarter := by
  rw [hold, PMF.map_bind]
  have h : ∀ k : ℕ,
      (((pascalNe3.iid (k - 1)).map fun v => (k, (3 + ∑ i, v i : ℤ))).map Prod.fst)
        = PMF.pure k := by
    intro k
    rw [PMF.map_comp]
    exact PMF.map_const _ _
  simp only [h]
  exact PMF.bind_pure _

/-- Slicing `hold` at a fixed first coordinate recovers the `geomQuarter` mass. -/
theorem hold_fst_marginal (k : ℕ) : ∑' l : ℤ, hold (k, l) = geomQuarter k := by
  have h1 : hold.map Prod.fst k = ∑' l : ℤ, hold (k, l) := by
    rw [PMF.map_apply, ENNReal.tsum_prod']
    rw [tsum_eq_single k (fun k' hk' => by simp [Ne.symm hk'])]
    exact tsum_congr fun l => by simp
  rw [← h1, hold_map_fst]

/-- Expectations of first-coordinate functions under `hold` reduce to `geomQuarter`. -/
theorem hold_tsum_fst (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑' d : ℕ × ℤ, (hold d).toReal * f d.1 = ∑' k : ℕ, (geomQuarter k).toReal * f k := by
  have hEN : ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f d.1)
      = ∑' k : ℕ, geomQuarter k * ENNReal.ofReal (f k) := by
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun k => ?_
    have : ∀ l : ℤ, hold (k, l) * ENNReal.ofReal (f (k, l).1)
        = hold (k, l) * ENNReal.ofReal (f k) := fun l => rfl
    rw [tsum_congr this, ENNReal.tsum_mul_right, hold_fst_marginal]
  calc ∑' d : ℕ × ℤ, (hold d).toReal * f d.1
      = ∑' d : ℕ × ℤ, (hold d * ENNReal.ofReal (f d.1)).toReal :=
        tsum_congr fun d => by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _)]
    _ = (∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (f d.1)).toReal :=
        (ENNReal.tsum_toReal_eq fun d =>
          ENNReal.mul_ne_top (hold.apply_ne_top d) ENNReal.ofReal_ne_top).symm
    _ = (∑' k : ℕ, geomQuarter k * ENNReal.ofReal (f k)).toReal := by rw [hEN]
    _ = ∑' k : ℕ, (geomQuarter k * ENNReal.ofReal (f k)).toReal :=
        ENNReal.tsum_toReal_eq fun k =>
          ENNReal.mul_ne_top (geomQuarter.apply_ne_top k) ENNReal.ofReal_ne_top
    _ = ∑' k : ℕ, (geomQuarter k).toReal * f k :=
        tsum_congr fun k => by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _)]

/-- Pin the first coordinate of a `hold` atom: only the matching `Geom(4)` draw
contributes, leaving the pushed-forward increment law. -/
theorem hold_apply_pin (k₀ : ℕ) (y : ℤ) :
    hold (k₀, y) = geomQuarter k₀ *
      ((pascalNe3.iid (k₀ - 1)).map fun v => ((3 : ℤ) + ∑ i, (v i : ℤ))) y := by
  classical
  rw [hold, PMF.bind_apply]
  rw [tsum_eq_single k₀ (fun k hk => by
    have hz : ((pascalNe3.iid (k - 1)).map fun v => ((k : ℕ), ((3 : ℤ) + ∑ i, (v i : ℤ)))) (k₀, y)
        = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.mpr fun v => ?_
      rw [if_neg (fun h => hk ((congrArg Prod.fst h).symm : k = k₀))]
    rw [hz, mul_zero])]
  congr 1
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun v => ?_
  congr 1
  rw [Prod.ext_iff]
  simp

/-- `hold` at `(1, 3)`: the single-step atom (real mass `1/4`). -/
theorem hold_apply_one_three : (hold (1, 3)).toReal = 4⁻¹ := by
  rw [hold_apply_pin]
  have h0 : pascalNe3.iid (1 - 1) = PMF.pure (fun i : Fin 0 => i.elim0) := rfl
  rw [h0, PMF.pure_map]
  have hval : ((3 : ℤ) + ∑ i : Fin 0, (((fun i : Fin 0 => i.elim0) i : ℕ) : ℤ)) = 3 := by
    simp
  rw [hval, PMF.pure_apply, if_pos rfl, mul_one, geomQuarter_toReal]
  norm_num

/-- `hold` at `(2, 3 + b)`: one `pascalNe3` increment on top of the base offset `3`. -/
theorem hold_apply_two (b : ℕ) : hold (2, 3 + (b : ℤ)) = geomQuarter 2 * pascalNe3 b := by
  classical
  rw [hold_apply_pin]
  congr 1
  have hiid1 : pascalNe3.iid (2 - 1)
      = pascalNe3.map fun a => Fin.cons (α := fun _ => ℕ) a (fun i : Fin 0 => i.elim0) := by
    show pascalNe3.bind
        (fun a => (PMF.pure (fun i : Fin 0 => i.elim0)).map (Fin.cons (α := fun _ => ℕ) a)) = _
    rw [PMF.map]
    refine congrArg _ (funext fun a => ?_)
    rw [PMF.pure_map]
    rfl
  rw [hiid1, PMF.map_comp, PMF.map_apply]
  rw [tsum_eq_single b (fun a ha => by
    rw [if_neg (fun h => ha (by
      simp only [Function.comp_apply, Fin.sum_cons] at h
      have h' : (3 : ℤ) + b = 3 + a := by simpa using h
      omega))]),
    if_pos (by
      simp only [Function.comp_apply, Fin.sum_cons]
      simp)]

/-- Real mass of `pascalNe3`. -/
theorem pascalNe3_toReal (b : ℕ) :
    (pascalNe3 b).toReal = if b < 2 ∨ b = 3 then 0
      else (4 / 3) * (((b - 1 : ℕ) : ℝ) * 2⁻¹ ^ b) := by
  rw [show pascalNe3 b = if b < 2 ∨ b = 3 then 0
      else (4 / 3) * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b) from rfl]
  split_ifs with h
  · simp
  · rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_div]
    norm_num

/-- Numeric `hold` atoms for the character-decay nondegeneracy ((D) of node S3):
`(1,3), (2,5), (2,7), (2,8)` carry masses `1/4, 1/16, 3/64, 1/32`, and the
difference set `{(1,2), (0,2), (0,3)}` affinely generates `ℤ²`. -/
theorem hold_apply_two_five : (hold (2, 5)).toReal = 16⁻¹ := by
  have h := hold_apply_two 2
  rw [show ((3 : ℤ) + ((2 : ℕ) : ℤ)) = 5 from by norm_num] at h
  rw [h, ENNReal.toReal_mul, geomQuarter_toReal, pascalNe3_toReal]
  norm_num

theorem hold_apply_two_seven : (hold (2, 7)).toReal = 3 / 64 := by
  have h := hold_apply_two 4
  rw [show ((3 : ℤ) + ((4 : ℕ) : ℤ)) = 7 from by norm_num] at h
  rw [h, ENNReal.toReal_mul, geomQuarter_toReal, pascalNe3_toReal]
  norm_num

theorem hold_apply_two_eight : (hold (2, 8)).toReal = 32⁻¹ := by
  have h := hold_apply_two 5
  rw [show ((3 : ℤ) + ((5 : ℕ) : ℤ)) = 8 from by norm_num] at h
  rw [h, ENNReal.toReal_mul, geomQuarter_toReal, pascalNe3_toReal]
  norm_num

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
