import TaoCollatz.Sec7.Holding

/-!
# §7.4: the first-passage unrolling of the `Q` recursion (paper (7.45), node X8/X9 entry)

Paper anchor: Tao 2019 (7.44)–(7.45), p.47. The paper iterates (7.35) up to the
stopping time `k` = first time the cumulative `l`-increment exceeds `s`, obtaining
```
Q(j,l) = E [ exp(-ε³ Σ_{i<k} 1_W((j,l)+v_{[1,i]})) · Q((j,l)+v_{[1,k]}) ].     (7.45)
```
**D6 finitization**: no infinite iid sequence / stopping-time measure theory. Instead
we define the *stopped value* `Qstop s j l` by well-founded recursion on the remaining
height budget `s : ℕ` — each `hold` step spends its (positive) second coordinate from
`s`, and a step that overshoots (`d₂ > s`, the paper's first passage `l_{[1,k]} > s`)
lands on the un-stopped `Q`. The identity `Qstop_eq : Qstop s j l = Q j l` (any `s`)
is then (7.45) verbatim, proved by strong induction on `s` over `Q_rec`.

Case 2 (X8, (7.46)–(7.51)) and Lemma 7.9 (X9) both consume this operator: the
overshoot branch is exactly "the walk exits the triangle through the top edge",
and its endpoint value is what `Q_le_Qm` / the white-exit bound (7.51) control.

* `hold_support_snd_ge` / `hold_zero_of_snd_lt` — `hold`'s second coordinate is `≥ 3`
  (`(k, 3 + Σ pascalNe3 increments)`), so every step spends height and the budget
  recursion terminates.
* `Qstop` — the stopped value.
* `Qstop_eq` — the (7.45) identity.
-/

open scoped ENNReal

namespace TaoCollatz

/-- The second coordinate of any `hold`-atom is at least `3` (it is
`3 + a sum of ℕ-casts`). Drives the `Qstop` height-budget termination and the
paper's "the `l_k` are all positive integers" (first passage well-defined). -/
theorem hold_support_snd_ge (d : ℕ × ℤ) (hd : d ∈ hold.support) : 3 ≤ d.2 := by
  rw [hold, PMF.mem_support_bind_iff] at hd
  obtain ⟨k, hk, hkd⟩ := hd
  rw [PMF.mem_support_map_iff] at hkd
  obtain ⟨v, _, hv⟩ := hkd
  rw [← hv]
  have h0 : (0 : ℤ) ≤ ∑ i, (v i : ℤ) := Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
  show (3 : ℤ) ≤ 3 + ∑ i, (v i : ℤ)
  linarith

/-- `hold` puts zero mass wherever the second coordinate is `< 3`. -/
theorem hold_zero_of_snd_lt {d : ℕ × ℤ} (h2 : d.2 < 3) : hold d = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro hd
  exact absurd (hold_support_snd_ge d hd) (by omega)

/-- **The stopped value** (D6 form of the paper's (7.45) right-hand side): run the
`Q` recursion while the height budget `s` lasts; a step overshooting the budget
(the paper's first passage `l_{[1,k]} > s`) lands on the plain `Q`. -/
noncomputable def Qstop (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) : ℕ → ℕ → ℤ → ℝ
  | s, j, l =>
    if half < j then Q half W ε j l
    else Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) *
      ∑' d : ℕ × ℤ,
        if _hd : 1 ≤ d.2 ∧ d.2 ≤ (s : ℤ) then
          (hold d).toReal * Qstop half W ε (s - d.2.toNat) (j + d.1) (l + d.2)
        else (hold d).toReal * Q half W ε (j + d.1) (l + d.2)
  termination_by s _ _ => s
  decreasing_by omega

/-- **The (7.45) identity, D6 form**: the stopped value agrees with `Q` for every
height budget `s`. Strong induction on `s` over `Q_rec`; each `hold` step spends
`d₂ ≥ 1` from the budget. This is the entry point for Case 2 ((7.46)–(7.51)) and
Lemma 7.9: analyses may pick `s` per triangle and reason about the overshoot
(first-passage) branch separately. -/
theorem Qstop_eq (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) :
    ∀ s (j : ℕ) (l : ℤ), Qstop half W ε s j l = Q half W ε j l := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro j l
    rw [Qstop]
    rcases Nat.lt_or_ge half j with hj | hj
    · rw [if_pos hj]
    · rw [if_neg (by omega), Q_rec _ _ _ _ _ hj]
      congr 1
      apply tsum_congr
      intro d
      split_ifs with hd
      · rw [IH (s - d.2.toNat) (by omega) (j + d.1) (l + d.2)]
      · rfl

/-- **The first-passage endpoint distribution** (D6 form of the paper's `v_{[1,k]}`,
(7.44)): the displacement accumulated by the renewal walk from its start until the
cumulative second coordinate first exceeds the height budget `s`. Defined by budget
recursion mirroring `Qstop`: draw `d ~ Hold`; an overshooting step (`d₂ > s`) IS the
first passage (endpoint `d`); otherwise recurse with budget `s - d₂` and translate.
The `d₂ ≤ 0` guard only fires on `hold`-null atoms (`hold_zero_of_snd_lt`) and keeps
the recursion well-founded; normalization is free from the `PMF` combinators. -/
noncomputable def fpDist : ℕ → PMF (ℕ × ℤ)
  | s =>
    hold.bind fun d =>
      if _h : d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
      else (fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)
  termination_by s => s
  decreasing_by
    push_neg at _h
    omega

/-- Every `fpDist`-endpoint has positive first coordinate (the walk takes ≥ 1 step). -/
theorem fpDist_support_fst_pos :
    ∀ s, ∀ e ∈ (fpDist s).support, 1 ≤ e.1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro e he
    rw [fpDist, PMF.mem_support_bind_iff] at he
    obtain ⟨d, hd, hde⟩ := he
    have hd1 := hold_support_fst_pos d hd
    split_ifs at hde with hcond
    · rw [PMF.support_pure, Set.mem_singleton_iff] at hde
      subst hde
      exact hd1
    · rw [PMF.mem_support_map_iff] at hde
      obtain ⟨e', _, he'⟩ := hde
      rw [← he']
      show 1 ≤ d.1 + e'.1
      omega

/-- Every `fpDist`-endpoint overshoots the budget: `s < e₂` (the paper's
`l_{[1,k]} > s`, the defining property of the first passage). -/
theorem fpDist_support_snd_gt :
    ∀ s, ∀ e ∈ (fpDist s).support, (s : ℤ) < e.2 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro e he
    rw [fpDist, PMF.mem_support_bind_iff] at he
    obtain ⟨d, hd, hde⟩ := he
    have hd2 := hold_support_snd_ge d hd
    split_ifs at hde with hcond
    · rw [PMF.support_pure, Set.mem_singleton_iff] at hde
      subst hde
      rcases hcond with h | h
      · omega
      · exact h
    · push_neg at hcond
      rw [PMF.mem_support_map_iff] at hde
      obtain ⟨e', he's, he'⟩ := hde
      have hrec := IH (s - d.2.toNat) (by omega) e' he's
      rw [← he']
      show (s : ℤ) < d.2 + e'.2
      have : ((s - d.2.toNat : ℕ) : ℤ) = (s : ℤ) - d.2 := by omega
      omega

/-- **The (7.45) first-passage inequality, D6 form** (`ℝ≥0∞`-valued to keep the
change-of-variables unconditional): dropping the accumulated damping (each factor
`≤ 1`), the renewal value at `(j,l)` is bounded by the average of `Q` over the
first-passage endpoint for ANY height budget `s`. This is the entry inequality for
Case 2 ((7.46)) and Case 3 ((7.53) at `P = 0`): pick `s := l_Δ - l` per triangle
and the endpoint is where Lemma 7.7 + the white-exit bound (7.50)/(7.51) take over. -/
theorem Q_le_fpDist_expect (half : ℕ) (W : Set (ℕ × ℤ)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      ENNReal.ofReal (Q half W ε j l)
        ≤ ∑' e : ℕ × ℤ, fpDist s e * ENNReal.ofReal (Q half W ε (j + e.1) (l + e.2)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro j l
    rcases Nat.lt_or_ge half j with hj | hj
    · -- boundary: every endpoint moves right, so both sides are 1
      rw [Q_boundary _ _ _ _ _ hj]
      have hRHS : ∑' e : ℕ × ℤ,
          fpDist s e * ENNReal.ofReal (Q half W ε (j + e.1) (l + e.2)) = 1 := by
        rw [← (fpDist s).tsum_coe]
        refine tsum_congr fun e => ?_
        by_cases h0 : fpDist s e = 0
        · rw [h0, zero_mul]
        · have h1 := fpDist_support_fst_pos s e (by rwa [PMF.mem_support_iff])
          rw [Q_boundary _ _ _ _ _ (by omega), ENNReal.ofReal_one, mul_one]
      rw [hRHS, ENNReal.ofReal_one]
    · -- interior: one Q_rec step against one fpDist layer
      rw [Q_rec _ _ _ _ _ hj]
      -- drop the damping factor at (j,l)
      have hexp1 : Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        exact mul_nonneg (pow_nonneg hε 3)
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      have hS0 : 0 ≤ ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2) :=
        tsum_nonneg fun d => mul_nonneg ENNReal.toReal_nonneg (Q_nonneg _ _ _ _ _)
      have hdrop : ENNReal.ofReal (Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) *
            ∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2))
          ≤ ENNReal.ofReal
            (∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2)) :=
        ENNReal.ofReal_le_ofReal (by
          calc Real.exp (-(ε ^ 3) * Set.indicator W 1 (j, l)) * _
              ≤ 1 * (∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2)) :=
                mul_le_mul_of_nonneg_right hexp1 hS0
            _ = _ := one_mul _)
      refine le_trans hdrop ?_
      -- lift the real hold-average to ℝ≥0∞
      have hlift : ENNReal.ofReal
            (∑' d : ℕ × ℤ, (hold d).toReal * Q half W ε (j + d.1) (l + d.2))
          = ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal (Q half W ε (j + d.1) (l + d.2)) := by
        rw [← PMF.toReal_tsum_mul_ofReal hold _ (fun d => Q_nonneg _ _ _ _ _),
          ENNReal.ofReal_toReal]
        exact ne_top_of_le_ne_top (by simp)
          (PMF.tsum_mul_ofReal_le_one hold _ (fun d => Q_le_one _ _ _ hε _ _))
      rw [hlift, fpDist, PMF.tsum_bind_mul]
      -- termwise comparison under the hold average
      refine ENNReal.tsum_le_tsum fun d => ?_
      by_cases h0 : hold d = 0
      · rw [h0, zero_mul, zero_mul]
      · have hd2 := hold_support_snd_ge d (by rwa [PMF.mem_support_iff])
        refine mul_le_mul_left' ?_ _
        split_ifs with hcond
        · -- overshoot: the endpoint is d itself
          refine le_of_eq ?_
          rw [tsum_eq_single d (fun e he => by
            rw [PMF.pure_apply, if_neg he, zero_mul])]
          rw [PMF.pure_apply, if_pos rfl, one_mul]
        · -- within budget: recurse with s - d₂ from (j+d₁, l+d₂)
          push_neg at hcond
          rw [PMF.tsum_map_mul]
          have hIH := IH (s - d.2.toNat) (by omega) (j + d.1) (l + d.2)
          refine le_trans hIH (le_of_eq (tsum_congr fun e => ?_))
          rw [show (j + d.1) + e.1 = j + (d.1 + e.1) from by omega,
            show (l + d.2) + e.2 = l + (d.2 + e.2) from by ring]


/-- The Gaussian-type weight `G_t(x) = exp(-x²/t) + exp(-|x|)` (paper (2.2)). -/
noncomputable def Gweight (t x : ℝ) : ℝ := Real.exp (-(x ^ 2) / t) + Real.exp (-|x|)

/-- **Lemma 7.7 (Distribution of first passage location), D6 statement** (paper p.43,
(7.30)–(7.33)): the first-passage endpoint mass at `(j, l)` is Gaussian-concentrated —
`j` near `s/4` at scale `(1+s)^{1/2}`, `l` within `O(1)` of `s`. For `l ≤ s` the left
side vanishes (`fpDist_support_snd_gt`), so the statement is unconditional.
OPEN (X6, the hard probabilistic kernel): the paper route is the union bound over the
last step + Lemma 7.6 (exponential tail of `Hold`) + Lemma 2.2 (2-D local Gaussian
bound for iid `Hold` sums — node S3, D5: exponential tilting + circle method, no
contour integration). -/
theorem fpDist_location_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (fpDist s (j, l)).toReal
        ≤ C * (Real.exp (-c * ((l : ℝ) - s)) / Real.sqrt (1 + s))
            * Gweight (1 + s) (c * ((j : ℝ) - s / 4)) := by
  sorry

end TaoCollatz
