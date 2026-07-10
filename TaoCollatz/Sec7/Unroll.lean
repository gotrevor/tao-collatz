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

end TaoCollatz
