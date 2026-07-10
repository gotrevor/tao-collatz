import TaoCollatz.Sec7.Holding
import TaoCollatz.Prob.LocalBound
import TaoCollatz.Prob.CharFn

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


/-- The law of the 2-D sum `d₁ + ⋯ + dₙ` of `n` iid copies of `hold` (paper `v_{[1,n]}`
for the §7.3 renewal walk; mean `(4, 16)` per p.42). -/
noncomputable def holdSum (n : ℕ) : PMF (ℕ × ℤ) :=
  (hold.iid n).map fun v => (∑ i, (v i).1, ∑ i, (v i).2)

/-- **Lemma 2.2(i) for `Hold`** (paper p.42: "the conclusion of Lemma 2.2 holds for
`Hold`", mean `(4, 16)`, `d = 2`): the 2-D local Gaussian-type bound
`P(Hold_{[1,n]} = (j,l)) ≪ (n+1)^{-1} · G_n(c((j,l) − n(4,16)))`. Node S3, the hard
kernel behind Lemma 7.7 (X6). D5 route: exponential tilting + `ZMod` circle method.
-- RATIFY-DRIFT (norm): `‖·‖` on `ℝ × ℝ` is the sup norm; the paper's Euclidean
-- `|x|` satisfies `|x|/√2 ≤ ‖x‖_∞ ≤ |x|`, so the two forms of the statement are
-- interchangeable after adjusting the constants `c, C`, which are existential. -/
theorem hold_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (j : ℕ) (l : ℤ),
      ((holdSum n) (j, l)).toReal
        ≤ C / (1 + n) * Gweight (1 + n) (c * ‖(((j : ℝ) - 4 * n, (l : ℝ) - 16 * n) : ℝ × ℝ)‖) := by
  sorry

/-- **Lemma 2.2(ii) for `Hold`**: the 2-D tail bound
`P(|Hold_{[1,n]} − n(4,16)| ≥ λ) ≪ G_n(cλ)` (same norm drift note as
`hold_local_bound`). -/
theorem hold_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' d : ℕ × ℤ, if lam ≤ ‖(((d.1 : ℝ) - 4 * n, (d.2 : ℝ) - 16 * n) : ℝ × ℝ)‖
          then ((holdSum n) d).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  sorry

/-- `holdSum` is the generic iid sum of `hold` in the product monoid `ℕ × ℤ`. -/
theorem holdSum_eq_iidSum (n : ℕ) : holdSum n = iidSum hold n := by
  rw [holdSum, iidSum]
  have hf : (fun v : Fin n → ℕ × ℤ => ((∑ i, (v i).1, ∑ i, (v i).2) : ℕ × ℤ))
      = fun v : Fin n → ℕ × ℤ => ∑ i, v i := by
    funext v
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
    · rw [Prod.snd_sum]
  rw [hf]

/-- The mod-`N` reduction of the renewal lattice `ℕ × ℤ`. -/
def modPair (N : ℕ) (d : ℕ × ℤ) : ZMod N × ZMod N := ((d.1 : ZMod N), (d.2 : ZMod N))

/-- **Circle-method entry for `hold_local_bound`** (D5, step 1 of the finite circle
method): the lattice point mass of the `n`-fold `Hold` walk is dominated — for EVERY
modulus `N` — by the corresponding point mass of the iid walk on the finite group
`ZMod N × ZMod N`. Upper bounds need no tail truncation: reduction only merges mass.
What remains for `hold_local_bound`'s Gaussian regime (next steps, node S3):
finite Fourier inversion `(r x).toReal ≤ N⁻² ∑_ξ ‖r̂ ξ‖^…` with `r̂` multiplicative
in iid sums, character decay for (tilted) `hold`, and the exponential tilting wrapper
for the off-center regime. -/
theorem holdSum_le_modPair (n N : ℕ) (v : ℕ × ℤ) :
    (holdSum n) v ≤ (iidSum (hold.map (modPair N)) n) (modPair N v) := by
  rw [holdSum_eq_iidSum]
  calc (iidSum hold n) v ≤ ((iidSum hold n).map (modPair N)) (modPair N v) :=
        PMF.apply_le_map_apply _ _ _
    _ = (iidSum (hold.map (modPair N)) n) (modPair N v) := by
        rw [iidSum_map hold (modPair N) (by simp [modPair])
          (fun a b => by simp [modPair, Prod.ext_iff])]

/-- **The circle-method bound for the `Hold` walk**, all algebraic steps composed:
for every modulus `N`, the lattice point mass of `Hold_{[1,n]}` is at most
`N⁻² ∑_ξ ‖r̂(ξ)‖ⁿ` where `r̂` is the characteristic function of `hold mod N`.
What remains for `hold_local_bound` is analysis only: character decay of `hold`
(nondegeneracy) and Gaussian summation over `ξ` at `N ≈ √n`, plus the tilting
wrapper for the off-center regime. -/
theorem holdSum_toReal_le_charFn (n N : ℕ) [NeZero N] (v : ℕ × ℤ) :
    ((holdSum n) v).toReal
      ≤ ((N : ℝ) ^ 2)⁻¹ * ∑ ξ : ZMod N × ZMod N, ‖charFn (hold.map (modPair N)) ξ‖ ^ n := by
  refine le_trans (ENNReal.toReal_mono
    ((iidSum (hold.map (modPair N)) n).apply_ne_top _)
    (holdSum_le_modPair n N v)) ?_
  exact iidSum_apply_toReal_le (hold.map (modPair N)) n (modPair N v)

/-- Transfer a two-atom anti-concentration bound through mass lower bounds and a
Jordan bound (helper for `charFn_hold_decay`). -/
theorem pair_transfer {X m0 m1 c0 c1 R u : ℝ} (hm0 : c0 ≤ m0) (hm1 : c1 ≤ m1)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hJ : 8 * u ^ 2 ≤ 1 - R)
    (hb : 2 * m0 * m1 * (1 - R) ≤ X) : 2 * c0 * c1 * (8 * u ^ 2) ≤ X := by
  have h1R : 0 ≤ 1 - R := le_trans (by positivity) hJ
  have hm0' : 0 ≤ m0 := le_trans hc0 hm0
  have hm1' : 0 ≤ m1 := le_trans hc1 hm1
  calc 2 * c0 * c1 * (8 * u ^ 2) ≤ 2 * c0 * c1 * (1 - R) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ ≤ 2 * m0 * m1 * (1 - R) := by
        have hcm : c0 * c1 ≤ m0 * m1 := mul_le_mul hm0 hm1 hc1 hm0'
        nlinarith
    _ ≤ X := hb

/-! ### Character decay for `hold mod N` -/

/-- **Character decay for the projected holding distribution** ((D) of node S3):
uniformly in the modulus `N ≥ 4`, the characteristic function of `hold mod N` decays
quadratically in the cyclic distance of the frequency. Nondegeneracy comes from the
four explicit atoms `(1,3), (2,5), (2,7), (2,8)` whose differences `(1,2), (0,2),
(0,3)` affinely generate `ℤ²`. -/
theorem charFn_hold_decay {N : ℕ} [NeZero N] (hN : 4 ≤ N) (ξ : ZMod N × ZMod N) :
    ‖charFn (hold.map (modPair N)) ξ‖ ^ 2
      ≤ 1 - (((nd ξ.1 : ℝ) / N) ^ 2 + ((nd ξ.2 : ℝ) / N) ^ 2) / 768 := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  set r := hold.map (modPair N) with hr
  -- transferred atom masses
  have hmass : ∀ (d : ℕ × ℤ), (hold d).toReal ≤ (r (modPair N d)).toReal := fun d =>
    ENNReal.toReal_mono (r.apply_ne_top _) (PMF.apply_le_map_apply hold (modPair N) d)
  have hm13 : (4⁻¹ : ℝ) ≤ (r (modPair N (1, 3))).toReal := by
    have h := hmass (1, 3)
    rwa [hold_apply_one_three] at h
  have hm25 : (16⁻¹ : ℝ) ≤ (r (modPair N (2, 5))).toReal := by
    have h := hmass (2, 5)
    rwa [hold_apply_two_five] at h
  have hm27 : (3 / 64 : ℝ) ≤ (r (modPair N (2, 7))).toReal := by
    have h := hmass (2, 7)
    rwa [hold_apply_two_seven] at h
  have hm28 : (32⁻¹ : ℝ) ≤ (r (modPair N (2, 8))).toReal := by
    have h := hmass (2, 8)
    rwa [hold_apply_two_eight] at h
  -- distinctness of the projected atoms (any collision forces N ∣ 1, 2 or 3)
  have hdvd : ∀ k : ℕ, 0 < k → k < 4 → ¬ ((k : ZMod N) = 0) := by
    intro k hk0 hk4 h
    have := (ZMod.natCast_eq_zero_iff k N).mp h
    have := Nat.le_of_dvd hk0 this
    omega
  have hd1 : modPair N (2, 5) ≠ modPair N (1, 3) := by
    intro h
    have h1 : ((2 : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
      have := congrArg Prod.fst h
      simpa [modPair] using this
    exact hdvd 1 (by omega) (by omega) (by
      have : ((2 : ℕ) : ZMod N) - ((1 : ℕ) : ZMod N) = 0 := by rw [h1, sub_self]
      calc ((1 : ℕ) : ZMod N) = ((2 : ℕ) : ZMod N) - ((1 : ℕ) : ZMod N) := by
            push_cast
            ring
        _ = 0 := this)
  have hd2 : modPair N (2, 7) ≠ modPair N (2, 5) := by
    intro h
    have h1 : ((7 : ℤ) : ZMod N) = ((5 : ℤ) : ZMod N) := by
      have := congrArg Prod.snd h
      simpa [modPair] using this
    exact hdvd 2 (by omega) (by omega) (by
      have : ((7 : ℤ) : ZMod N) - ((5 : ℤ) : ZMod N) = 0 := by rw [h1, sub_self]
      calc ((2 : ℕ) : ZMod N) = ((7 : ℤ) : ZMod N) - ((5 : ℤ) : ZMod N) := by
            push_cast
            ring
        _ = 0 := this)
  have hd3 : modPair N (2, 8) ≠ modPair N (2, 5) := by
    intro h
    have h1 : ((8 : ℤ) : ZMod N) = ((5 : ℤ) : ZMod N) := by
      have := congrArg Prod.snd h
      simpa [modPair] using this
    exact hdvd 3 (by omega) (by omega) (by
      have : ((8 : ℤ) : ZMod N) - ((5 : ℤ) : ZMod N) = 0 := by rw [h1, sub_self]
      calc ((3 : ℕ) : ZMod N) = ((8 : ℤ) : ZMod N) - ((5 : ℤ) : ZMod N) := by
            push_cast
            ring
        _ = 0 := this)
  -- the three atom differences
  have hw1 : modPair N (2, 5) - modPair N (1, 3) = (((1 : ℕ) : ZMod N), ((2 : ℕ) : ZMod N)) := by
    rw [modPair, modPair, Prod.ext_iff]
    constructor <;> (show _ - _ = _) <;> push_cast <;> ring
  have hw2 : modPair N (2, 7) - modPair N (2, 5) = (((0 : ℕ) : ZMod N), ((2 : ℕ) : ZMod N)) := by
    rw [modPair, modPair, Prod.ext_iff]
    constructor <;> (show _ - _ = _) <;> push_cast <;> ring
  have hw3 : modPair N (2, 8) - modPair N (2, 5) = (((0 : ℕ) : ZMod N), ((3 : ℕ) : ZMod N)) := by
    rw [modPair, modPair, Prod.ext_iff]
    constructor <;> (show _ - _ = _) <;> push_cast <;> ring
  -- pinned frequencies
  set j1 : ZMod N := ξ.1 * ((1 : ℕ) : ZMod N) + ξ.2 * ((2 : ℕ) : ZMod N) with hj1
  set j2 : ZMod N := ξ.1 * ((0 : ℕ) : ZMod N) + ξ.2 * ((2 : ℕ) : ZMod N) with hj2
  set j3 : ZMod N := ξ.1 * ((0 : ℕ) : ZMod N) + ξ.2 * ((3 : ℕ) : ZMod N) with hj3
  set u1 : ℝ := (nd j1 : ℝ) / N with hu1
  set u2 : ℝ := (nd j2 : ℝ) / N with hu2
  set u3 : ℝ := (nd j3 : ℝ) / N with hu3
  -- Jordan bounds
  have hJ1 : 8 * u1 ^ 2 ≤ 1 - (pairChar ξ (((1 : ℕ) : ZMod N), ((2 : ℕ) : ZMod N))).re :=
    one_sub_re_stdAddChar_ge' j1
  have hJ2 : 8 * u2 ^ 2 ≤ 1 - (pairChar ξ (((0 : ℕ) : ZMod N), ((2 : ℕ) : ZMod N))).re :=
    one_sub_re_stdAddChar_ge' j2
  have hJ3 : 8 * u3 ^ 2 ≤ 1 - (pairChar ξ (((0 : ℕ) : ZMod N), ((3 : ℕ) : ZMod N))).re :=
    one_sub_re_stdAddChar_ge' j3
  -- pair anti-concentration bounds
  have hb1 := charFn_normSq_pair_bound r ξ _ _ hd1
  have hb2 := charFn_normSq_pair_bound r ξ _ _ hd2
  have hb3 := charFn_normSq_pair_bound r ξ _ _ hd3
  rw [hw1] at hb1
  rw [hw2] at hb2
  rw [hw3] at hb3
  -- combined per-pair lower bounds on 1 - ‖φ‖²
  set X : ℝ := 1 - ‖charFn r ξ‖ ^ 2 with hX
  have hA1 : 2 * 16⁻¹ * 4⁻¹ * (8 * u1 ^ 2) ≤ X :=
    pair_transfer hm25 hm13 (by norm_num) (by norm_num) hJ1 hb1
  have hA2 : 2 * (3 / 64) * 16⁻¹ * (8 * u2 ^ 2) ≤ X :=
    pair_transfer hm27 hm25 (by norm_num) (by norm_num) hJ2 hb2
  have hA3 : 2 * 32⁻¹ * 16⁻¹ * (8 * u3 ^ 2) ≤ X :=
    pair_transfer hm28 hm25 (by norm_num) (by norm_num) hJ3 hb3
  have hu1X : u1 ^ 2 ≤ 4 * X := by linarith
  have hu2X : u2 ^ 2 ≤ (64 / 3) * X := by linarith
  have hu3X : u3 ^ 2 ≤ 32 * X := by linarith
  -- triangle: recover ξ from the pinned frequencies
  have ht1 : nd ξ.1 ≤ nd j1 + nd j2 := by
    have h := nd_sub_le j1 j2
    have hsub : j1 - j2 = ξ.1 := by
      rw [hj1, hj2]
      push_cast
      ring
    rwa [hsub] at h
  have ht2 : nd ξ.2 ≤ nd j3 + nd j2 := by
    have h := nd_sub_le j3 j2
    have hsub : j3 - j2 = ξ.2 := by
      rw [hj3, hj2]
      push_cast
      ring
    rwa [hsub] at h
  have ht1R : (nd ξ.1 : ℝ) / N ≤ u1 + u2 := by
    rw [hu1, hu2, ← add_div]
    gcongr
    exact_mod_cast ht1
  have ht2R : (nd ξ.2 : ℝ) / N ≤ u3 + u2 := by
    rw [hu3, hu2, ← add_div]
    gcongr
    exact_mod_cast ht2
  have hnd1nn : (0 : ℝ) ≤ (nd ξ.1 : ℝ) / N := by positivity
  have hnd2nn : (0 : ℝ) ≤ (nd ξ.2 : ℝ) / N := by positivity
  have ha2 : ((nd ξ.1 : ℝ) / N) ^ 2 ≤ 2 * u1 ^ 2 + 2 * u2 ^ 2 := by
    nlinarith [ht1R, hnd1nn, sq_nonneg (u1 - u2)]
  have hb2' : ((nd ξ.2 : ℝ) / N) ^ 2 ≤ 2 * u3 ^ 2 + 2 * u2 ^ 2 := by
    nlinarith [ht2R, hnd2nn, sq_nonneg (u3 - u2)]
  linarith [ha2, hb2', hu1X, hu2X, hu3X, sq_nonneg u1, sq_nonneg u2, sq_nonneg u3]

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
