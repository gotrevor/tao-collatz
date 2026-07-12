import TaoCollatz.Sec7.HoldLocal

/-!
# Lemma 7.7: distribution of the first passage location (node X6)

Paper p.43–44, (7.30)–(7.33). Route (D6): because every `hold` step strictly
increases the height coordinate (`hold_support_snd_ge`), a path reaching `p`
with `p₂ ≤ s` has ALL its partial sums at height `≤ p₂ ≤ s` — no barrier
condition. Hence the first-passage endpoint mass factors through the plain
renewal measure:

* `renewalMass p := ∑' k, iidSum hold k p` — the expected number of visits to
  `p` (paper `∑_k P(v_{[1,k]} = p)`; the events are disjoint in `k` since the
  height strictly increases, so this is also a probability).
* `fpDist_le_renewal_conv` — the first-passage decomposition
  `fpDist s e ≤ ∑_{p₂ ≤ s} renewalMass p · hold(e - p)` (PROVED, budget
  induction; stated with delta-convolutions to avoid truncated subtraction).
* `renewalMass_bound` — the renewal Gaussian bound (paper p.44 first display):
  `renewalMass (j,l) ≪ (1+l)^{-1/2}·G_{1+l}(c(j - l/4))`; OPEN — sums
  `hold_local_bound` (Lemma 2.2(i), node S3, PROVED) over `k` in the three
  regions `16(k-1) ∈ [l/2, 2l]`, `< l/2`, `> 2l`.
* `fpDist_location_bound` — **Lemma 7.7** (moved here from `Unroll.lean`):
  OPEN — convolve `renewalMass_bound` with the single-step bounds
  (`hold_local_bound`/`hold_tail_bound` at `n = 1`) over the last-step split
  `l' ≤ s/2` vs `l' > s/2` (paper p.44 last paragraph).
-/

namespace TaoCollatz

open scoped ENNReal

/-- The renewal measure of the `Hold` walk: expected visits to `p` (equally,
the probability of ever visiting `p`, the events being `k`-disjoint since the
height strictly increases). Paper `∑_k P(v_{[1,k]} = p)`, p.44. -/
noncomputable def renewalMass (p : ℕ × ℤ) : ℝ≥0∞ :=
  ∑' k : ℕ, iidSum hold k p

/-- The `≥ 1`-step part of the renewal measure. -/
noncomputable def stepMass (p : ℕ × ℤ) : ℝ≥0∞ :=
  ∑' k : ℕ, iidSum hold (k + 1) p

/-- Peel the `k = 0` layer: `renewalMass = δ₀ + stepMass`. -/
theorem renewalMass_eq (p : ℕ × ℤ) :
    renewalMass p = PMF.pure (0 : ℕ × ℤ) p + stepMass p := by
  rw [renewalMass, tsum_eq_zero_add' ENNReal.summable, iidSum_zero, stepMass]

/-- The origin carries full renewal mass at `k = 0`. -/
theorem one_le_renewalMass_zero : 1 ≤ renewalMass (0 : ℕ × ℤ) := by
  rw [renewalMass_eq, PMF.pure_apply, if_pos rfl]
  exact le_add_right le_rfl

/-- `PMF.map_apply` for a translation, with the canonical `DecidableEq`
instance (the raw lemma produces `Classical.propDecidable` ites, which do not
match hand-written ites; `congr` bridges via `Subsingleton`). -/
theorem map_apply_ite {α : Type*} [DecidableEq α] (μ : PMF α) (f : α → α)
    (b : α) : (μ.map f) b = ∑' a : α, (if b = f a then μ a else 0) := by
  rw [PMF.map_apply]
  exact tsum_congr fun a => by congr

/-- Pointwise form of `iidSum_succ`: peel the first draw off an iid sum, with
the landing point exposed through a delta-convolution. -/
theorem iidSum_succ_apply (k : ℕ) (p : ℕ × ℤ) :
    iidSum hold (k + 1) p
      = ∑' d : ℕ × ℤ, hold d * ∑' q : ℕ × ℤ,
          (if p = d + q then iidSum hold k q else 0) := by
  rw [iidSum_succ, PMF.bind_apply]
  exact tsum_congr fun d => by rw [map_apply_ite]

/-- The first-step decomposition of the renewal measure:
`stepMass = hold ⋆ renewalMass`. -/
theorem stepMass_eq_conv (p : ℕ × ℤ) :
    stepMass p
      = ∑' d : ℕ × ℤ, hold d * ∑' q : ℕ × ℤ,
          (if p = d + q then renewalMass q else 0) := by
  rw [stepMass]
  calc ∑' k : ℕ, iidSum hold (k + 1) p
      = ∑' k : ℕ, ∑' d : ℕ × ℤ, hold d * ∑' q : ℕ × ℤ,
          (if p = d + q then iidSum hold k q else 0) :=
        tsum_congr fun k => iidSum_succ_apply k p
    _ = ∑' d : ℕ × ℤ, ∑' k : ℕ, hold d * ∑' q : ℕ × ℤ,
          (if p = d + q then iidSum hold k q else 0) := ENNReal.tsum_comm
    _ = ∑' d : ℕ × ℤ, hold d * ∑' k : ℕ, ∑' q : ℕ × ℤ,
          (if p = d + q then iidSum hold k q else 0) :=
        tsum_congr fun _ => ENNReal.tsum_mul_left
    _ = ∑' d : ℕ × ℤ, hold d * ∑' q : ℕ × ℤ, ∑' k : ℕ,
          (if p = d + q then iidSum hold k q else 0) :=
        tsum_congr fun _ => congrArg _ ENNReal.tsum_comm
    _ = ∑' d : ℕ × ℤ, hold d * ∑' q : ℕ × ℤ,
          (if p = d + q then renewalMass q else 0) := by
        refine tsum_congr fun d => congrArg _ (tsum_congr fun q => ?_)
        by_cases h : p = d + q
        · simp only [if_pos h, renewalMass]
        · simp only [if_neg h, tsum_zero]

/-- Collapse an intermediate landing point: summing a delta-chain
`e = d' + e'`, `e' = q + d` over `e'` leaves the single constraint
`e = d' + q + d`. -/
theorem tsum_delta_chain (e d' q : ℕ × ℤ) (g : ℕ × ℤ → ℝ≥0∞) :
    ∑' e' : ℕ × ℤ, ∑' d : ℕ × ℤ, (if e = d' + e' then
        (if e' = q + d then g d else 0) else 0)
      = ∑' d : ℕ × ℤ, (if e = d' + q + d then g d else 0) := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun d => ?_
  rw [tsum_eq_single (q + d) (fun e' he' => by rw [if_neg he', ite_self])]
  rw [if_pos rfl, add_assoc]

/-- Reindex a double sum against the landing point `p = d + q`
(delta-convolution form of Fubini for `ℝ≥0∞`). -/
theorem tsum_conv_reindex (G : ℕ × ℤ → ℕ × ℤ → ℝ≥0∞) (F : ℕ × ℤ → ℝ≥0∞) :
    ∑' d : ℕ × ℤ, ∑' q : ℕ × ℤ, G d q * F (d + q)
      = ∑' p : ℕ × ℤ, (∑' d : ℕ × ℤ, ∑' q : ℕ × ℤ,
          (if p = d + q then G d q else 0)) * F p := by
  have h1 : ∀ d q : ℕ × ℤ, G d q * F (d + q)
      = ∑' p : ℕ × ℤ, (if p = d + q then G d q * F p else 0) := by
    intro d q
    rw [tsum_eq_single (d + q) (fun p hp => if_neg hp), if_pos rfl]
  calc ∑' d : ℕ × ℤ, ∑' q : ℕ × ℤ, G d q * F (d + q)
      = ∑' d : ℕ × ℤ, ∑' q : ℕ × ℤ, ∑' p : ℕ × ℤ,
          (if p = d + q then G d q * F p else 0) :=
        tsum_congr fun d => tsum_congr fun q => h1 d q
    _ = ∑' d : ℕ × ℤ, ∑' p : ℕ × ℤ, ∑' q : ℕ × ℤ,
          (if p = d + q then G d q * F p else 0) :=
        tsum_congr fun _ => ENNReal.tsum_comm
    _ = ∑' p : ℕ × ℤ, ∑' d : ℕ × ℤ, ∑' q : ℕ × ℤ,
          (if p = d + q then G d q * F p else 0) := ENNReal.tsum_comm
    _ = ∑' p : ℕ × ℤ, (∑' d : ℕ × ℤ, ∑' q : ℕ × ℤ,
          (if p = d + q then G d q else 0)) * F p := by
        refine tsum_congr fun p => ?_
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun d => by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun q => by rw [ite_mul, zero_mul]

/-- **The first-passage decomposition** (D6 form of the paper's
`P(v_{[1,k]} = ·)` splitting, p.43–44): the endpoint mass is dominated by the
renewal measure at the pre-passage point convolved with one `hold` step over
the budget line. Upper bound only (all downstream uses are upper bounds; the
(7.50) lower bound comes from the complement, `fpDist` being a `PMF`). -/
theorem fpDist_le_renewal_conv : ∀ (s : ℕ) (e : ℕ × ℤ),
    fpDist s e ≤ ∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
      * ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro e
    -- split the RHS as the δ₀ layer (= hold e) plus the ≥1-step layer
    have hRHS : ∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
          * ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0)
        = hold e + ∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then stepMass p else 0)
          * ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0) := by
      have hsplit : ∀ p : ℕ × ℤ,
          (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
              * ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0)
            = (if p.2 ≤ (s : ℤ) then PMF.pure (0 : ℕ × ℤ) p else 0)
                * ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0)
              + (if p.2 ≤ (s : ℤ) then stepMass p else 0)
                * ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0) := by
        intro p
        by_cases hp : p.2 ≤ (s : ℤ)
        · rw [if_pos hp, if_pos hp, if_pos hp, renewalMass_eq, add_mul]
        · rw [if_neg hp, if_neg hp, if_neg hp, zero_mul, add_zero]
      rw [tsum_congr hsplit, ENNReal.tsum_add]
      congr 1
      -- the δ₀ layer collapses to `hold e`
      rw [tsum_eq_single (0 : ℕ × ℤ) (fun p hp => by
        rw [PMF.pure_apply, if_neg hp, ite_self, zero_mul])]
      have h00 : ((0 : ℕ × ℤ).2 : ℤ) ≤ (s : ℤ) := by simp
      rw [if_pos h00, PMF.pure_apply, if_pos rfl, one_mul,
        tsum_eq_single e (fun d hd => by
          rw [if_neg (by simpa [eq_comm] using hd)]), if_pos (by simp)]
    rw [hRHS, fpDist, PMF.bind_apply]
    -- split each hold-atom's dite into the overshoot and in-budget parts
    have hterm : ∀ d' : ℕ × ℤ,
        hold d' * (if _h : d'.2 ≤ 0 ∨ (s : ℤ) < d'.2 then PMF.pure d'
            else (fpDist (s - d'.2.toNat)).map
              fun e' => (d'.1 + e'.1, d'.2 + e'.2)) e
          = (if d'.2 ≤ 0 ∨ (s : ℤ) < d'.2 then hold d' * PMF.pure d' e else 0)
            + (if d'.2 ≤ 0 ∨ (s : ℤ) < d'.2 then 0
              else hold d' * ((fpDist (s - d'.2.toNat)).map
                fun e' => (d'.1 + e'.1, d'.2 + e'.2)) e) := by
      intro d'
      by_cases hc : d'.2 ≤ 0 ∨ (s : ℤ) < d'.2
      · rw [dif_pos hc, if_pos hc, if_pos hc, add_zero]
      · rw [dif_neg hc, if_neg hc, if_neg hc, zero_add]
    rw [tsum_congr hterm, ENNReal.tsum_add]
    refine add_le_add ?_ ?_
    · -- overshoot layer ≤ hold e
      calc ∑' d' : ℕ × ℤ,
          (if d'.2 ≤ 0 ∨ (s : ℤ) < d'.2 then hold d' * PMF.pure d' e else 0)
          ≤ ∑' d' : ℕ × ℤ, (if e = d' then hold d' else 0) := by
            refine ENNReal.tsum_le_tsum fun d' => ?_
            rw [PMF.pure_apply]
            by_cases hc : d'.2 ≤ 0 ∨ (s : ℤ) < d'.2
            · rw [if_pos hc]
              by_cases he : e = d'
              · rw [if_pos he, if_pos he, mul_one]
              · rw [if_neg he, if_neg he, mul_zero]
            · rw [if_neg hc]
              exact zero_le
        _ = hold e := by
            rw [tsum_eq_single e (fun d' hd' => by
              rw [if_neg (by simpa [eq_comm] using hd')]), if_pos rfl]
    · -- in-budget layer: IH per atom, drop the guard, reindex p = d' + q
      have hIH : ∀ d' : ℕ × ℤ,
          (if d'.2 ≤ 0 ∨ (s : ℤ) < d'.2 then 0
            else hold d' * ((fpDist (s - d'.2.toNat)).map
              fun e' => (d'.1 + e'.1, d'.2 + e'.2)) e)
          ≤ ∑' q : ℕ × ℤ, (hold d'
              * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMass q else 0))
              * ∑' d : ℕ × ℤ, (if e = d' + q + d then hold d else 0) := by
        intro d'
        by_cases hc : d'.2 ≤ 0 ∨ (s : ℤ) < d'.2
        · rw [if_pos hc]
          exact zero_le
        · rw [if_neg hc]
          push_neg at hc
          obtain ⟨hd2pos, hd2le⟩ := hc
          set s' : ℕ := s - d'.2.toNat with hs'
          have hs'lt : s' < s := by omega
          have hcond : ∀ q : ℕ × ℤ,
              (d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2) ↔ q.2 ≤ (s' : ℤ) := by
            intro q
            constructor
            · rintro ⟨h, -⟩; omega
            · intro h; exact ⟨by omega, hd2pos⟩
          calc hold d' * ((fpDist s').map
                fun e' => (d'.1 + e'.1, d'.2 + e'.2)) e
              ≤ hold d' * ∑' q : ℕ × ℤ,
                  (if q.2 ≤ (s' : ℤ) then renewalMass q else 0)
                  * ∑' d : ℕ × ℤ, (if e = d' + q + d then hold d else 0) := by
                refine mul_le_mul_left' ?_ _
                rw [map_apply_ite]
                refine le_trans (le_of_eq (tsum_congr fun e' =>
                  if_congr Iff.rfl rfl rfl)) ?_
                calc ∑' e' : ℕ × ℤ, (if e = d' + e' then fpDist s' e' else 0)
                    ≤ ∑' e' : ℕ × ℤ, (if e = d' + e' then
                        ∑' q : ℕ × ℤ, (if q.2 ≤ (s' : ℤ) then renewalMass q else 0)
                          * ∑' d : ℕ × ℤ, (if e' = q + d then hold d else 0)
                        else 0) := by
                      refine ENNReal.tsum_le_tsum fun e' => ?_
                      by_cases he' : e = d' + e'
                      · rw [if_pos he', if_pos he']
                        exact IH s' hs'lt e'
                      · rw [if_neg he', if_neg he']
                  _ = ∑' q : ℕ × ℤ, (if q.2 ≤ (s' : ℤ) then renewalMass q else 0)
                        * ∑' d : ℕ × ℤ, (if e = d' + q + d then hold d else 0) := by
                      have hpush : ∀ e' : ℕ × ℤ, (if e = d' + e' then
                            ∑' q : ℕ × ℤ, (if q.2 ≤ (s' : ℤ) then renewalMass q else 0)
                              * ∑' d : ℕ × ℤ, (if e' = q + d then hold d else 0)
                            else 0)
                          = ∑' q : ℕ × ℤ, (if q.2 ≤ (s' : ℤ) then renewalMass q else 0)
                              * ∑' d : ℕ × ℤ, (if e = d' + e' then
                                  (if e' = q + d then hold d else 0) else 0) := by
                        intro e'
                        by_cases hce : e = d' + e'
                        · simp only [if_pos hce]
                        · simp only [if_neg hce, tsum_zero, mul_zero]
                      rw [tsum_congr hpush, ENNReal.tsum_comm]
                      refine tsum_congr fun q => ?_
                      rw [ENNReal.tsum_mul_left, tsum_delta_chain e d' q hold]
            _ = ∑' q : ℕ × ℤ, (hold d'
                  * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMass q else 0))
                  * ∑' d : ℕ × ℤ, (if e = d' + q + d then hold d else 0) := by
                rw [← ENNReal.tsum_mul_left]
                refine tsum_congr fun q => ?_
                rw [if_congr (hcond q) rfl rfl, ← mul_assoc]
      refine le_trans (ENNReal.tsum_le_tsum hIH) (le_of_eq ?_)
      -- reindex against the landing point p = d' + q
      have hre := tsum_conv_reindex
        (fun d' q => hold d'
          * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMass q else 0))
        (fun p => ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0))
      have hshape : ∀ d' : ℕ × ℤ, ∑' q : ℕ × ℤ, (hold d'
            * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMass q else 0))
            * ∑' d : ℕ × ℤ, (if e = d' + q + d then hold d else 0)
          = ∑' q : ℕ × ℤ, (hold d'
            * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMass q else 0))
            * ∑' d : ℕ × ℤ, (if e = (d' + q) + d then hold d else 0) :=
        fun d' => rfl
      rw [tsum_congr hshape, hre]
      -- identify the inner double sum with the budget-restricted stepMass
      refine tsum_congr fun p => ?_
      congr 1
      -- the `0 < d'.2` guard is absorbed: `hold` vanishes at heights < 3
      have hinner : ∀ (d' q : ℕ × ℤ), (if p = d' + q then hold d'
            * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMass q else 0) else 0)
          = (if p.2 ≤ (s : ℤ) then
              (if p = d' + q then hold d' * renewalMass q else 0) else 0) := by
        intro d' q
        by_cases hpq : p = d' + q
        · have hp2 : p.2 = d'.2 + q.2 := by rw [hpq]; rfl
          rcases lt_or_ge (0 : ℤ) d'.2 with hd2 | hd2
          · -- positive step: the two conditions coincide
            by_cases hps : p.2 ≤ (s : ℤ)
            · rw [if_pos hpq, if_pos hps, if_pos hpq, if_pos ⟨by omega, hd2⟩]
            · rw [if_pos hpq, if_neg hps,
                if_neg (show ¬(d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2) from
                  fun h => hps (by omega)), mul_zero]
          · -- null step: `hold d' = 0` kills both sides
            have h0 : hold d' = 0 := hold_zero_of_snd_lt (by omega)
            rw [if_pos hpq, h0, zero_mul]
            by_cases hps : p.2 ≤ (s : ℤ)
            · rw [if_pos hps, if_pos hpq, zero_mul]
            · rw [if_neg hps]
        · rw [if_neg hpq]
          by_cases hps : p.2 ≤ (s : ℤ)
          · rw [if_pos hps, if_neg hpq]
          · rw [if_neg hps]
      rw [tsum_congr fun d' => tsum_congr fun q => hinner d' q]
      -- pull the budget condition out of the double sum
      by_cases hps : p.2 ≤ (s : ℤ)
      · simp only [if_pos hps]
        rw [stepMass_eq_conv]
        refine tsum_congr fun d' => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun q => by rw [mul_ite, mul_zero]
      · simp only [if_neg hps, tsum_zero]

/-! ### Elementary summation toolkit for the renewal bound

Everything below is finite and integral-free: the Gaussian arithmetic-
progression sums are handled by an `M`-split (bulk of `≍ 1/√β` unit terms +
geometric tail), and super-polynomial decay by `e^u ≥ (1 + u/2)² ≥ u²/4`. -/

/-- `Gweight t` is antitone in the (nonnegative) argument. -/
theorem Gweight_anti {t x y : ℝ} (ht : 0 < t) (hx : 0 ≤ x) (hxy : x ≤ y) :
    Gweight t y ≤ Gweight t x := by
  unfold Gweight
  have hy : 0 ≤ y := hx.trans hxy
  have h1 : Real.exp (-(y ^ 2) / t) ≤ Real.exp (-(x ^ 2) / t) := by
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hinv : 0 < t⁻¹ := inv_pos.mpr ht
    nlinarith [mul_self_le_mul_self hx hxy, hinv]
  have h2 : Real.exp (-|y|) ≤ Real.exp (-|x|) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    linarith
  exact add_le_add h1 h2

/-- Crude super-polynomial decay: `e^{-u} ≤ 4/u²` (from `e^{u/2} ≥ 1 + u/2`). -/
theorem exp_neg_le_four_div_sq {u : ℝ} (hu : 0 < u) :
    Real.exp (-u) ≤ 4 / u ^ 2 := by
  have h2 : u ^ 2 / 4 ≤ Real.exp u := by
    have h1 : 1 + u / 2 ≤ Real.exp (u / 2) := by
      linarith [Real.add_one_le_exp (u / 2)]
    calc u ^ 2 / 4 = (u / 2) ^ 2 := by ring
      _ ≤ (1 + u / 2) ^ 2 := by nlinarith
      _ ≤ Real.exp (u / 2) ^ 2 := by nlinarith [Real.exp_pos (u / 2)]
      _ = Real.exp (u / 2) * Real.exp (u / 2) := sq _
      _ = Real.exp u := by rw [← Real.exp_add]; ring_nf
  rw [Real.exp_neg, le_div_iff₀ (by positivity : (0 : ℝ) < u ^ 2)]
  calc (Real.exp u)⁻¹ * u ^ 2 ≤ (Real.exp u)⁻¹ * (4 * Real.exp u) := by
        have hnn := inv_nonneg.mpr (Real.exp_pos u).le
        nlinarith
    _ = 4 := by field_simp

/-- Tail of the geometric-comparison bound: `(1 - e^{-u})⁻¹ ≤ 1 + 1/u`. -/
theorem one_sub_exp_neg_inv_le_one_add {u : ℝ} (hu : 0 < u) :
    (1 - Real.exp (-u))⁻¹ ≤ 1 + 1 / u := by
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hkey : u / (u + 1) ≤ 1 - Real.exp (-u) := by
    have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
    have h2 : Real.exp (-u) ≤ (u + 1)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ (by linarith) h1
    have h3 : u / (u + 1) = 1 - (u + 1)⁻¹ := by
      field_simp
      ring
    linarith
  rw [inv_le_comm₀ (by linarith) (by positivity)]
  calc (1 + 1 / u)⁻¹ = u / (u + 1) := by
        rw [one_add_div hu.ne', inv_div]
    _ ≤ 1 - Real.exp (-u) := hkey

/-- Partial geometric sums are bounded by `(1-r)⁻¹`. -/
theorem sum_range_geom_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ m ∈ Finset.range N, r ^ m ≤ (1 - r)⁻¹ := by
  have hsum : Summable fun m : ℕ => r ^ m := summable_geometric_of_lt_one h0 h1
  calc ∑ m ∈ Finset.range N, r ^ m
      ≤ ∑' m : ℕ, r ^ m :=
        hsum.sum_le_tsum _ (fun m _ => pow_nonneg h0 m)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one h0 h1

/-- **Gaussian AP sum, elementary form**: `∑_{m<N} e^{-βm²} ≤ 3 + 2/√β`.
`M`-split: `≍ 1/√β` unit terms, then `m² ≥ Mm` turns the tail geometric. -/
theorem sum_range_exp_neg_sq_le {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    ∑ m ∈ Finset.range N, Real.exp (-β * (m : ℝ) ^ 2) ≤ 3 + 2 / Real.sqrt β := by
  set M : ℕ := ⌊1 / Real.sqrt β⌋₊ + 1 with hM
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hMge : 1 / Real.sqrt β ≤ (M : ℝ) := by
    rw [hM]
    push_cast
    exact (Nat.lt_floor_add_one _).le
  have hMle : (M : ℝ) ≤ 1 / Real.sqrt β + 1 := by
    rw [hM]
    push_cast
    have := Nat.floor_le (by positivity : (0:ℝ) ≤ 1 / Real.sqrt β)
    linarith
  have hM0 : (0:ℝ) < (M : ℝ) := by
    rw [hM]
    push_cast
    positivity
  set r : ℝ := Real.exp (-(β * M)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    nlinarith [mul_pos hβ hM0]
  have hterm : ∀ m : ℕ, Real.exp (-β * (m : ℝ) ^ 2)
      ≤ (if m ≤ M then 1 else 0) + r ^ m := by
    intro m
    by_cases hm : m ≤ M
    · rw [if_pos hm]
      have hle1 : Real.exp (-β * (m : ℝ) ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (m : ℝ)])
      have hrm : (0:ℝ) ≤ r ^ m := pow_nonneg hr0 m
      linarith
    · rw [if_neg hm]
      have hMm : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.le_of_not_lt (by omega)
      have hexp : Real.exp (-β * (m : ℝ) ^ 2) ≤ r ^ m := by
        rw [hr, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith [mul_le_mul_of_nonneg_left hMm
          (mul_nonneg hβ.le hm0)]
      linarith
  calc ∑ m ∈ Finset.range N, Real.exp (-β * (m : ℝ) ^ 2)
      ≤ ∑ m ∈ Finset.range N, ((if m ≤ M then 1 else 0) + r ^ m) :=
        Finset.sum_le_sum fun m _ => hterm m
    _ = (∑ m ∈ Finset.range N, if m ≤ M then (1:ℝ) else 0)
        + ∑ m ∈ Finset.range N, r ^ m := Finset.sum_add_distrib
    _ ≤ ((M : ℝ) + 1) + (1 - r)⁻¹ := by
        gcongr
        · calc (∑ m ∈ Finset.range N, if m ≤ M then (1:ℝ) else 0)
              = (((Finset.range N).filter fun m => m ≤ M).card : ℝ) := by
                rw [Finset.sum_boole]
            _ ≤ ((Finset.range (M + 1)).card : ℝ) := by
                have hsub : (Finset.range N).filter (fun m => m ≤ M)
                    ⊆ Finset.range (M + 1) := by
                  intro m hm
                  have := (Finset.mem_filter.mp hm).2
                  exact Finset.mem_range.mpr (by omega)
                exact_mod_cast Finset.card_le_card hsub
            _ = (M : ℝ) + 1 := by
                rw [Finset.card_range]
                push_cast
                ring
        · exact sum_range_geom_le hr0 hr1 N
    _ ≤ (1 / Real.sqrt β + 1 + 1) + (1 + 1 / (β * M)) := by
        have hβM : (0:ℝ) < β * M := mul_pos hβ hM0
        have hinv := one_sub_exp_neg_inv_le_one_add hβM
        rw [hr]
        linarith
    _ ≤ 3 + 2 / Real.sqrt β := by
        have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ.le
        have hβM : Real.sqrt β ≤ β * M := by
          have hmul := mul_le_mul_of_nonneg_left hMge hβ.le
          calc Real.sqrt β = β * (1 / Real.sqrt β) := by
                rw [mul_one_div, eq_div_iff hsβ.ne']
                exact hsq
            _ ≤ β * M := hmul
        have h1 : 1 / (β * M) ≤ 1 / Real.sqrt β :=
          one_div_le_one_div_of_le hsβ hβM
        calc 1 / Real.sqrt β + 1 + 1 + (1 + 1 / (β * M))
            = 3 + (1 / Real.sqrt β + 1 / (β * M)) := by ring
          _ ≤ 3 + (1 / Real.sqrt β + 1 / Real.sqrt β) := by linarith
          _ = 3 + 2 / Real.sqrt β := by ring

/-- **Arithmetic-progression sum against an antitone envelope**: the offsets
`|w - 16k|`, `k < N`, cover each value `16m` at most twice (once on each side
of `w/16`), so the sum is at most twice the on-progression sum. -/
theorem sum_abs_AP_le {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u)
    (hanti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v → f v ≤ f u)
    (w N : ℕ) (hw : w < 16 * N) :
    ∑ k ∈ Finset.range N, f |(w : ℝ) - 16 * k|
      ≤ 2 * ∑ m ∈ Finset.range N, f (16 * m) := by
  set q : ℕ := w / 16 with hq
  have h16q : 16 * q ≤ w := by omega
  have hwq : w < 16 * (q + 1) := by omega
  have hqN : q < N := by omega
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun k => k ≤ q)]
  have hA : ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q), f |(w : ℝ) - 16 * k|
      ≤ ∑ m ∈ Finset.range N, f (16 * m) := by
    have hstep : ∀ k ∈ (Finset.range N).filter (fun k => k ≤ q),
        f |(w : ℝ) - 16 * k| ≤ f (16 * ((q - k : ℕ) : ℝ)) := by
      intro k hk
      have hkq : k ≤ q := (Finset.mem_filter.mp hk).2
      have hkw : 16 * k ≤ w := le_trans (by omega) h16q
      refine hanti (by positivity) ?_
      have h0 : (0 : ℝ) ≤ (w : ℝ) - 16 * k := by
        have : ((16 * k : ℕ) : ℝ) ≤ (w : ℕ) := Nat.cast_le.mpr hkw
        push_cast at this
        linarith
      rw [abs_of_nonneg h0, Nat.cast_sub hkq]
      have : ((16 * q : ℕ) : ℝ) ≤ (w : ℕ) := Nat.cast_le.mpr h16q
      push_cast at this
      linarith
    have hinj : ∀ x ∈ (Finset.range N).filter (fun k => k ≤ q),
        ∀ y ∈ (Finset.range N).filter (fun k => k ≤ q),
          q - x = q - y → x = y := by
      intro x hx y hy hxy
      have hxq := (Finset.mem_filter.mp hx).2
      have hyq := (Finset.mem_filter.mp hy).2
      omega
    have key : ∑ m ∈ ((Finset.range N).filter (fun k => k ≤ q)).image (fun k => q - k),
        f (16 * (m : ℝ))
        = ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q), f (16 * ((q - k : ℕ) : ℝ)) :=
      Finset.sum_image hinj
    calc ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q), f |(w : ℝ) - 16 * k|
        ≤ ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q), f (16 * ((q - k : ℕ) : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = ∑ m ∈ ((Finset.range N).filter (fun k => k ≤ q)).image (fun k => q - k),
            f (16 * (m : ℝ)) := key.symm
      _ ≤ ∑ m ∈ Finset.range N, f (16 * m) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn _
          intro m hm
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
          exact Finset.mem_range.mpr (by omega)
  have hB : ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q), f |(w : ℝ) - 16 * k|
      ≤ ∑ m ∈ Finset.range N, f (16 * m) := by
    have hstep : ∀ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
        f |(w : ℝ) - 16 * k| ≤ f (16 * ((k - (q + 1) : ℕ) : ℝ)) := by
      intro k hk
      have hkq : q < k := Nat.lt_of_not_le (Finset.mem_filter.mp hk).2
      refine hanti (by positivity) ?_
      have hwk : w ≤ 16 * k := by omega
      have h0 : (w : ℝ) - 16 * k ≤ 0 := by
        have : ((w : ℕ) : ℝ) ≤ ((16 * k : ℕ) : ℝ) := Nat.cast_le.mpr hwk
        push_cast at this
        linarith
      rw [abs_of_nonpos h0, Nat.cast_sub (by omega : q + 1 ≤ k)]
      have h1 : ((16 * (q + 1) : ℕ) : ℝ) ≥ ((w : ℕ) : ℝ) := Nat.cast_le.mpr hwq.le
      push_cast at h1 ⊢
      linarith
    have hinj : ∀ x ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
        ∀ y ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
          x - (q + 1) = y - (q + 1) → x = y := by
      intro x hx y hy hxy
      have hxq := Nat.lt_of_not_le (Finset.mem_filter.mp hx).2
      have hyq := Nat.lt_of_not_le (Finset.mem_filter.mp hy).2
      omega
    have key : ∑ m ∈ ((Finset.range N).filter (fun k => ¬ k ≤ q)).image
          (fun k => k - (q + 1)), f (16 * (m : ℝ))
        = ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
            f (16 * ((k - (q + 1) : ℕ) : ℝ)) :=
      Finset.sum_image hinj
    calc ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q), f |(w : ℝ) - 16 * k|
        ≤ ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
            f (16 * ((k - (q + 1) : ℕ) : ℝ)) := Finset.sum_le_sum hstep
      _ = ∑ m ∈ ((Finset.range N).filter (fun k => ¬ k ≤ q)).image
            (fun k => k - (q + 1)), f (16 * (m : ℝ)) := key.symm
      _ ≤ ∑ m ∈ Finset.range N, f (16 * m) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn _
          intro m hm
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
          have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
          exact Finset.mem_range.mpr (by omega)
  linarith

/-- Every `hold` step raises the height by at least `3`, so `k` steps cannot
land at height `< 3k`. This truncates the renewal `k`-sum at `⌊l/3⌋`. -/
theorem iidSum_hold_snd_zero : ∀ (k : ℕ) (q : ℕ × ℤ), q.2 < 3 * (k : ℤ) →
    iidSum hold k q = 0 := by
  intro k
  induction k with
  | zero =>
    intro q hq
    rw [iidSum_zero, PMF.pure_apply, if_neg]
    intro h
    subst h
    simp at hq
  | succ k ih =>
    intro q hq
    rw [iidSum_succ_apply]
    refine ENNReal.tsum_eq_zero.mpr fun d => ?_
    by_cases hd : hold d = 0
    · rw [hd, zero_mul]
    · have hd2 : 3 ≤ d.2 := hold_support_snd_ge d (by rwa [PMF.mem_support_iff])
      have hz : (∑' q' : ℕ × ℤ, if q = d + q' then iidSum hold k q' else 0) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun q' => ?_
        by_cases he : q = d + q'
        · rw [if_pos he]
          refine ih q' ?_
          have hsnd : q.2 = d.2 + q'.2 := by rw [he]; rfl
          push_cast at hq ⊢
          omega
        · rw [if_neg he]
      rw [hz, mul_zero]

/-- The renewal mass at height `l ≥ 0` is a FINITE sum over `k ≤ ⌊l/3⌋`
(later layers cannot reach down to height `l`). -/
theorem renewalMass_toReal_eq (j : ℕ) (l : ℤ) :
    (renewalMass (j, l)).toReal
      = ∑ k ∈ Finset.range (l.toNat / 3 + 1), (iidSum hold k (j, l)).toReal := by
  have htr : renewalMass (j, l)
      = ∑ k ∈ Finset.range (l.toNat / 3 + 1), iidSum hold k (j, l) := by
    rw [renewalMass]
    refine tsum_eq_sum fun k hk => iidSum_hold_snd_zero k (j, l) ?_
    have hk' : l.toNat / 3 + 1 ≤ k := Nat.le_of_not_lt fun h => hk (Finset.mem_range.mpr h)
    show l < 3 * (k : ℤ)
    omega
  rw [htr, ENNReal.toReal_sum fun k _ => PMF.apply_ne_top _ _]

/-- **Gweight factorization** for the renewal `k`-sum: peel a Gaussian ×
exponential weight in the height offset `z` off the target weight in `x`, at
half the decay constant (`AB + CD ≤ (A+C)(B+D)`). The hypothesis
`|x| + (3/4)z ≤ y` is the triangle inequality for the drift-recentred offsets
(`x = u - v/4`, `y = |u| + |v|`, `z = |v|`), and `t1 ≤ t2` widens the Gaussian
to the target time scale. -/
theorem Gweight_factor {c1 t1 t2 x z y : ℝ} (hc1 : 0 < c1) (ht1 : 0 < t1)
    (ht : t1 ≤ t2) (hz : 0 ≤ z) (hy : |x| + 3 / 4 * z ≤ y) :
    Gweight t1 (c1 * y)
      ≤ Gweight t2 (c1 / 2 * x)
        * (Real.exp (-(c1 ^ 2 / 2) * z ^ 2 / t1) + Real.exp (-(c1 / 2) * z)) := by
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hy0 : 0 ≤ y := by linarith
  have ht2 : 0 < t2 := lt_of_lt_of_le ht1 ht
  set A := Real.exp (-(c1 / 2 * x) ^ 2 / t2) with hA
  set B := Real.exp (-(c1 ^ 2 / 2) * z ^ 2 / t1) with hB
  set C := Real.exp (-|c1 / 2 * x|) with hC
  set D := Real.exp (-(c1 / 2) * z) with hD
  have hquad : Real.exp (-(c1 * y) ^ 2 / t1) ≤ A * B := by
    rw [hA, hB, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [div_add_div _ _ ht2.ne' ht1.ne', div_le_div_iff₀ ht1 (by positivity)]
    -- reduces to: t2·((c1/2·x)²·t1/t2-ish) — do it as one nlinarith with the
    -- two structural products supplied
    have hy2 : x ^ 2 + z ^ 2 / 2 ≤ y ^ 2 := by
      have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      nlinarith [mul_nonneg hx0 hz, sq_nonneg z]
    nlinarith [mul_le_mul_of_nonneg_left hy2 (sq_nonneg c1),
      mul_le_mul_of_nonneg_left ht (mul_nonneg (sq_nonneg (c1 * x)) ht1.le),
      sq_nonneg (c1 * x), sq_nonneg (c1 * z), mul_pos ht1 ht2,
      mul_nonneg (mul_nonneg (sq_nonneg (c1 * z)) ht1.le) (sub_nonneg.mpr ht)]
  have hlin : Real.exp (-|c1 * y|) ≤ C * D := by
    rw [hC, hD, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg (mul_nonneg hc1.le hy0), abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < c1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hy hc1.le, mul_nonneg hc1.le hx0,
      mul_nonneg hc1.le hz]
  have hABCD : A * B + C * D ≤ (A + C) * (B + D) := by
    nlinarith [mul_nonneg (Real.exp_pos (-(c1 / 2 * x) ^ 2 / t2)).le
        (Real.exp_pos (-(c1 / 2) * z)).le,
      mul_nonneg (Real.exp_pos (-|c1 / 2 * x|)).le
        (Real.exp_pos (-(c1 ^ 2 / 2) * z ^ 2 / t1)).le]
  calc Gweight t1 (c1 * y) = Real.exp (-(c1 * y) ^ 2 / t1) + Real.exp (-|c1 * y|) := rfl
    _ ≤ A * B + C * D := add_le_add hquad hlin
    _ ≤ (A + C) * (B + D) := hABCD
    _ = Gweight t2 (c1 / 2 * x) * (B + D) := rfl

/-- **The renewal `k`-sum envelope**: summing the per-`k` prefactor
`(1+k)⁻¹ · W_k` (as produced by `Gweight_factor` applied to
`hold_local_bound`) over the truncated range `k ≤ ⌊l/3⌋` costs only
`C₅/√(1+l)`. Two regions (paper p.44 "routine calculation"): `k < ⌊l/32⌋` has
height offset `z ≥ l/2`, so `W_k` is exponentially small in `l` and even
`(1+l)` terms of it vanish against `√(1+l)`; `k ≥ ⌊l/32⌋` has
`(1+k)⁻¹ ≤ 32/(1+l)` and the `z`-sums are arithmetic-progression sums handled
by `sum_abs_AP_le` + `sum_range_exp_neg_sq_le` / `sum_range_geom_le`. -/
theorem renewal_weight_sum_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C5 > (0 : ℝ), ∀ (l : ℤ), 0 ≤ l →
      ∑ k ∈ Finset.range (l.toNat / 3 + 1),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - 16 * k|))
        ≤ C5 / Real.sqrt (1 + (l : ℝ)) := by
  set ε : ℝ := min (a / 8) (b / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  refine ⟨32 / ε ^ 2 + (256 + 4 / b + 8 / Real.sqrt a), by positivity, fun l hl => ?_⟩
  set t : ℕ := l.toNat with hts
  have hcast : ((t : ℕ) : ℝ) = (l : ℝ) := by
    have := Int.toNat_of_nonneg hl
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) this
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have h1l : (0 : ℝ) < 1 + (l : ℝ) := by linarith
  set s : ℝ := Real.sqrt (1 + (l : ℝ)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr h1l
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by linarith)
  have hss : s * s = 1 + (l : ℝ) := Real.mul_self_sqrt h1l.le
  set N : ℕ := t / 3 + 1 with hN
  set T : ℕ := t / 32 with hT
  -- every k in range is ≤ l (as a real), so 1 + k ≤ 1 + l
  have hkl : ∀ k ∈ Finset.range N, (k : ℝ) ≤ (l : ℝ) := by
    intro k hk
    have hk' : k ≤ t := by
      have := Finset.mem_range.mp hk
      omega
    rw [← hcast]
    exact_mod_cast hk'
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun k => k < T)]
  have hterm_nonneg : ∀ k : ℕ, 0 ≤ 1 / (1 + (k : ℝ))
      * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
        + Real.exp (-b * |(l : ℝ) - 16 * k|)) := fun k => by positivity
  -- ── Edge region: k < ⌊l/32⌋, so z ≥ l/2 and W_k is exponentially small ──
  have hedge : ∑ k ∈ (Finset.range N).filter (fun k => k < T),
      1 / (1 + (k : ℝ))
        * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
          + Real.exp (-b * |(l : ℝ) - 16 * k|))
      ≤ (32 / ε ^ 2) / s := by
    by_cases hT0 : T = 0
    · rw [Finset.filter_false_of_mem (fun k _ => by omega), Finset.sum_empty]
      positivity
    · have ht32 : 32 ≤ t := by omega
      have hl1 : (1 : ℝ) ≤ (l : ℝ) := by
        rw [← hcast]; exact_mod_cast le_trans (by norm_num) ht32
      have hbound : ∀ k ∈ (Finset.range N).filter (fun k => k < T),
          1 / (1 + (k : ℝ))
            * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-b * |(l : ℝ) - 16 * k|))
          ≤ 2 * Real.exp (-(ε * (l : ℝ))) := by
        intro k hk
        have hkT : k < T := (Finset.mem_filter.mp hk).2
        have hkN := (Finset.mem_filter.mp hk).1
        have h32k : 32 * k + 32 ≤ t := by
          have := Nat.div_mul_le_self t 32
          omega
        have h16k : 16 * (k : ℝ) ≤ (l : ℝ) / 2 := by
          have : ((32 * k + 32 : ℕ) : ℝ) ≤ ((t : ℕ) : ℝ) := Nat.cast_le.mpr h32k
          rw [hcast] at this
          push_cast at this
          linarith
        have hzl : (l : ℝ) / 2 ≤ |(l : ℝ) - 16 * k| := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        have hz0 : (0 : ℝ) ≤ (l : ℝ) / 2 := by linarith
        have h1k : (0 : ℝ) < 1 + (k : ℝ) := by positivity
        have h1kl : 1 + (k : ℝ) ≤ 1 + (l : ℝ) := by
          linarith [hkl k hkN]
        -- quadratic exponent dominates ε·l
        have hq : ε * (l : ℝ) ≤ a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)) := by
          have h1 : a * ((l : ℝ) / 2) ^ 2 / (1 + (l : ℝ))
              ≤ a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)) := by
            calc a * ((l : ℝ) / 2) ^ 2 / (1 + (l : ℝ))
                ≤ a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (l : ℝ)) := by
                  gcongr
              _ ≤ a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)) :=
                  div_le_div_of_nonneg_left (by positivity) h1k h1kl
          have h2 : ε * (l : ℝ) ≤ a * ((l : ℝ) / 2) ^ 2 / (1 + (l : ℝ)) := by
            rw [le_div_iff₀ h1l]
            have hεa : ε ≤ a / 8 := min_le_left _ _
            nlinarith [mul_nonneg ha.le (mul_nonneg hl0 (sub_nonneg.mpr hl1)),
              mul_le_mul_of_nonneg_right hεa (mul_nonneg hl0 h1l.le)]
          linarith
        -- linear exponent dominates ε·l
        have hlin : ε * (l : ℝ) ≤ b * |(l : ℝ) - 16 * k| := by
          have hεb : ε ≤ b / 2 := min_le_right _ _
          nlinarith [mul_le_mul_of_nonneg_left hzl hb.le,
            mul_le_mul_of_nonneg_right hεb hl0]
        have hE1 : Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
            ≤ Real.exp (-(ε * (l : ℝ))) := by
          apply Real.exp_le_exp.mpr
          rw [neg_mul, neg_div]
          linarith
        have hE2 : Real.exp (-b * |(l : ℝ) - 16 * k|)
            ≤ Real.exp (-(ε * (l : ℝ))) := by
          apply Real.exp_le_exp.mpr
          rw [neg_mul]
          linarith
        have hfr : 1 / (1 + (k : ℝ)) ≤ 1 := by
          rw [div_le_one h1k]
          linarith
        calc 1 / (1 + (k : ℝ))
            * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-b * |(l : ℝ) - 16 * k|))
            ≤ 1 * (Real.exp (-(ε * (l : ℝ))) + Real.exp (-(ε * (l : ℝ)))) := by
              apply mul_le_mul hfr (add_le_add hE1 hE2) (by positivity) one_pos.le
          _ = 2 * Real.exp (-(ε * (l : ℝ))) := by ring
      -- card ≤ N ≤ 1 + l, then super-polynomial decay kills √(1+l)·(1+l)
      have hcard : ∑ k ∈ (Finset.range N).filter (fun k => k < T),
          1 / (1 + (k : ℝ))
            * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-b * |(l : ℝ) - 16 * k|))
          ≤ (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ)))) := by
        calc ∑ k ∈ (Finset.range N).filter (fun k => k < T),
            1 / (1 + (k : ℝ))
              * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
                + Real.exp (-b * |(l : ℝ) - 16 * k|))
            ≤ ∑ _k ∈ (Finset.range N).filter (fun k => k < T),
              2 * Real.exp (-(ε * (l : ℝ))) := Finset.sum_le_sum hbound
          _ = (((Finset.range N).filter (fun k => k < T)).card : ℝ)
              * (2 * Real.exp (-(ε * (l : ℝ)))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ)))) := by
              apply mul_le_mul_of_nonneg_right ?_ (by positivity)
              have hc1 : ((Finset.range N).filter (fun k => k < T)).card ≤ N :=
                le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])
              have hc2 : ((N : ℕ) : ℝ) ≤ 1 + (l : ℝ) := by
                have hN3 : ((t / 3 : ℕ) : ℝ) ≤ (t : ℝ) / 3 := Nat.cast_div_le
                have : (N : ℝ) = ((t / 3 : ℕ) : ℝ) + 1 := by
                  rw [hN]; push_cast; ring
                rw [this, ← hcast] at *
                nlinarith [Nat.cast_nonneg (α := ℝ) t]
              exact le_trans (Nat.cast_le.mpr hc1) hc2
      refine hcard.trans ?_
      rw [le_div_iff₀ hs0]
      have hsle : s ≤ 1 + (l : ℝ) := by
        calc s ≤ s * s := le_mul_of_one_le_left hs0.le hs1
          _ = 1 + (l : ℝ) := hss
      have hεl : 0 < ε * (l : ℝ) := mul_pos hε0 (by linarith)
      have hexp : Real.exp (-(ε * (l : ℝ))) ≤ 4 / (ε * (l : ℝ)) ^ 2 :=
        exp_neg_le_four_div_sq hεl
      have h2l : 1 + (l : ℝ) ≤ 2 * (l : ℝ) := by linarith
      calc (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ)))) * s
          ≤ (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ)))) * (1 + (l : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hsle (by positivity)
        _ = 2 * ((1 + (l : ℝ)) ^ 2 * Real.exp (-(ε * (l : ℝ)))) := by ring
        _ ≤ 2 * ((2 * (l : ℝ)) ^ 2 * (4 / (ε * (l : ℝ)) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
            apply mul_le_mul (by nlinarith) hexp (Real.exp_pos _).le (by positivity)
        _ = 32 / ε ^ 2 := by
            field_simp
            ring
  -- ── Central region: k ≥ ⌊l/32⌋, prefactor ≤ 32/(1+l), AP sums in z ──
  have hcen : ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
      1 / (1 + (k : ℝ))
        * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
          + Real.exp (-b * |(l : ℝ) - 16 * k|))
      ≤ (256 + 4 / b + 8 / Real.sqrt a) / s := by
    have hper : ∀ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - 16 * k|))
        ≤ 32 / (1 + (l : ℝ))
          * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (l : ℝ)))
            + Real.exp (-b * |(l : ℝ) - 16 * k|)) := by
      intro k hk
      have hkT : T ≤ k := Nat.le_of_not_lt (Finset.mem_filter.mp hk).2
      have hkN := (Finset.mem_filter.mp hk).1
      have h1k : (0 : ℝ) < 1 + (k : ℝ) := by positivity
      have h1kl : 1 + (k : ℝ) ≤ 1 + (l : ℝ) := by linarith [hkl k hkN]
      have h32 : 1 + (l : ℝ) ≤ 32 * (1 + (k : ℝ)) := by
        have h1 : t ≤ 32 * k + 31 := by omega
        have h2 : ((t : ℕ) : ℝ) ≤ ((32 * k + 31 : ℕ) : ℝ) := Nat.cast_le.mpr h1
        rw [hcast] at h2
        push_cast at h2
        linarith
      have hfrac : 1 / (1 + (k : ℝ)) ≤ 32 / (1 + (l : ℝ)) := by
        rw [div_le_div_iff₀ h1k h1l]
        linarith
      have hquad : Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
          ≤ Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (l : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [neg_mul, neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (by positivity) h1k h1kl
      apply mul_le_mul hfrac (add_le_add hquad le_rfl) (by positivity) (by positivity)
    have hwN : t < 16 * N := by omega
    -- Gaussian AP sum
    have hf1nn : ∀ u : ℝ, 0 ≤ Real.exp (-a * u ^ 2 / (1 + (l : ℝ))) :=
      fun u => (Real.exp_pos _).le
    have hf1anti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v →
        Real.exp (-a * v ^ 2 / (1 + (l : ℝ))) ≤ Real.exp (-a * u ^ 2 / (1 + (l : ℝ))) := by
      intro u v hu huv
      apply Real.exp_le_exp.mpr
      rw [neg_mul, neg_div, neg_mul, neg_div, neg_le_neg_iff]
      apply div_le_div_of_nonneg_right ?_ h1l.le
      nlinarith [mul_self_le_mul_self hu huv, ha.le]
    have hAP1 := sum_abs_AP_le hf1nn hf1anti t N hwN
    rw [hcast] at hAP1
    have hf2nn : ∀ u : ℝ, 0 ≤ Real.exp (-b * u) := fun u => (Real.exp_pos _).le
    have hf2anti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v →
        Real.exp (-b * v) ≤ Real.exp (-b * u) := by
      intro u v hu huv
      apply Real.exp_le_exp.mpr
      nlinarith
    have hAP2 := sum_abs_AP_le hf2nn hf2anti t N hwN
    rw [hcast] at hAP2
    -- on-progression Gaussian sum
    set β : ℝ := 256 * a / (1 + (l : ℝ)) with hβdef
    have hβ : 0 < β := by positivity
    have hgauss : ∑ m ∈ Finset.range N, Real.exp (-a * (16 * (m : ℝ)) ^ 2 / (1 + (l : ℝ)))
        ≤ 3 + 2 / Real.sqrt β := by
      calc ∑ m ∈ Finset.range N, Real.exp (-a * (16 * (m : ℝ)) ^ 2 / (1 + (l : ℝ)))
          = ∑ m ∈ Finset.range N, Real.exp (-β * (m : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl fun m _ => congrArg Real.exp ?_
            rw [hβdef]
            field_simp
            ring
        _ ≤ 3 + 2 / Real.sqrt β := sum_range_exp_neg_sq_le hβ N
    -- √β against √(1+l)
    have hβs : Real.sqrt β * s = 16 * Real.sqrt a := by
      rw [hs, ← Real.sqrt_mul hβ.le]
      rw [show β * (1 + (l : ℝ)) = 256 * a by rw [hβdef]; field_simp]
      rw [show (256 : ℝ) * a = 16 ^ 2 * a by norm_num,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16 ^ 2), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 16)]
    have hβpos : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
    have h2β : 2 / Real.sqrt β ≤ s / (8 * Real.sqrt a) := by
      rw [div_le_div_iff₀ hβpos (by positivity)]
      nlinarith [hβs]
    -- on-progression geometric sum
    have hgeom : ∑ m ∈ Finset.range N, Real.exp (-b * (16 * (m : ℝ)))
        ≤ 1 + 1 / (16 * b) := by
      have hterm : ∀ m : ℕ, Real.exp (-b * (16 * (m : ℝ))) = Real.exp (-(16 * b)) ^ m := by
        intro m
        rw [← Real.exp_nat_mul]
        exact congrArg Real.exp (by ring)
      rw [Finset.sum_congr rfl fun m _ => hterm m]
      have hr1 : Real.exp (-(16 * b)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      calc ∑ m ∈ Finset.range N, Real.exp (-(16 * b)) ^ m
          ≤ (1 - Real.exp (-(16 * b)))⁻¹ := sum_range_geom_le (Real.exp_pos _).le hr1 N
        _ ≤ 1 + 1 / (16 * b) := one_sub_exp_neg_inv_le_one_add (by positivity)
    -- assemble the central sum
    calc ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - 16 * k|))
        ≤ ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
          32 / (1 + (l : ℝ))
            * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (l : ℝ)))
              + Real.exp (-b * |(l : ℝ) - 16 * k|)) := Finset.sum_le_sum hper
      _ ≤ ∑ k ∈ Finset.range N,
          32 / (1 + (l : ℝ))
            * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (l : ℝ)))
              + Real.exp (-b * |(l : ℝ) - 16 * k|)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun k _ _ => by positivity
      _ = 32 / (1 + (l : ℝ))
          * (∑ k ∈ Finset.range N, Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (l : ℝ)))
            + ∑ k ∈ Finset.range N, Real.exp (-b * |(l : ℝ) - 16 * k|)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 32 / (1 + (l : ℝ))
          * (2 * (3 + 2 / Real.sqrt β) + 2 * (1 + 1 / (16 * b))) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          have g1 : ∑ k ∈ Finset.range N, Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (l : ℝ)))
              ≤ 2 * (3 + 2 / Real.sqrt β) :=
            hAP1.trans (by linarith [hgauss])
          have g2 : ∑ k ∈ Finset.range N, Real.exp (-b * |(l : ℝ) - 16 * k|)
              ≤ 2 * (1 + 1 / (16 * b)) :=
            hAP2.trans (by linarith [hgeom])
          linarith
      _ ≤ 32 / (1 + (l : ℝ)) * (8 + 1 / (8 * b) + s / (4 * Real.sqrt a)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h4β : 4 / Real.sqrt β ≤ s / (4 * Real.sqrt a) := by
            have e1 : (4 : ℝ) / Real.sqrt β = 2 * (2 / Real.sqrt β) := by ring
            have e2 : s / (4 * Real.sqrt a) = 2 * (s / (8 * Real.sqrt a)) := by ring
            rw [e1, e2]
            linarith [h2β]
          have e3 : 2 * (2 / Real.sqrt β) = 4 / Real.sqrt β := by ring
          have e4 : 2 * (1 / (16 * b)) = 1 / (8 * b) := by ring
          linarith [h4β, e3, e4]
      _ ≤ (256 + 4 / b + 8 / Real.sqrt a) / s := by
          rw [← hss, le_div_iff₀ hs0]
          have hinvb : (0 : ℝ) ≤ 1 / b := by positivity
          have hinva : (0 : ℝ) ≤ 1 / Real.sqrt a := by positivity
          have hkey : 0 ≤ s * (s - 1) := mul_nonneg hs0.le (by linarith)
          field_simp
          nlinarith [mul_nonneg (mul_nonneg hinvb hs0.le) (sub_nonneg.mpr hs1),
            mul_nonneg (mul_nonneg hinva hs0.le) (sub_nonneg.mpr hs1),
            mul_nonneg hkey hb.le, mul_nonneg hkey hsa.le,
            mul_pos hb hsa, mul_pos hs0 hs0]
  calc ∑ k ∈ (Finset.range N).filter (fun k => k < T),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - 16 * k|))
      + ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - 16 * k|))
      ≤ (32 / ε ^ 2) / s + (256 + 4 / b + 8 / Real.sqrt a) / s := add_le_add hedge hcen
    _ = (32 / ε ^ 2 + (256 + 4 / b + 8 / Real.sqrt a)) / s := (add_div _ _ _).symm

/-- **The renewal Gaussian bound** (paper p.44, first display of the Lemma 7.7
proof): `∑_k P(v_{[1,k-1]} = (j', s')) ≪ (1+s')^{-1/2}·G_{1+s'}(c(j'-s'/4))`.

OPEN (X6, step 2): insert `hold_local_bound` (Lemma 2.2(i), PROVED) per `k` and
sum, splitting into the regions `16(k-1) ∈ [s'/2, 2s']` (≍ √s' terms, each
`≪ 1/s'` with the Gaussian in `j' - s'/4` surviving), `16(k-1) < s'/2` and
`> 2s'` (the height offset `|s' - 16(k-1)| ≳ s'` makes `G_k` exponentially
small). PROVED: truncate at `k ≤ ⌊l/3⌋` (`iidSum_hold_snd_zero`), insert
`hold_local_bound` per `k`, peel the height weight with `Gweight_factor`
(constants `c₁ = c₀/2`, target decay `c = c₀/4`), and close the `k`-sum with
`renewal_weight_sum_le`. -/
theorem renewalMass_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (j : ℕ) (l : ℤ), 0 ≤ l →
      (renewalMass (j, l)).toReal
        ≤ C / Real.sqrt (1 + (l : ℝ))
            * Gweight (1 + (l : ℝ)) (c * ((j : ℝ) - (l : ℝ) / 4)) := by
  obtain ⟨c0, hc0, C0, hC0, hloc⟩ := hold_local_bound
  set c1 : ℝ := c0 / 2 with hc1def
  have hc1 : 0 < c1 := by rw [hc1def]; positivity
  obtain ⟨C5, hC5, hsum⟩ := renewal_weight_sum_le
    (a := c1 ^ 2 / 2) (b := c1 / 2) (by positivity) (by positivity)
  refine ⟨c1 / 2, by positivity, C0 * C5, by positivity, fun j l hl => ?_⟩
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have h1l : (0 : ℝ) < 1 + (l : ℝ) := by linarith
  set G : ℝ := Gweight (1 + (l : ℝ)) (c1 / 2 * ((j : ℝ) - (l : ℝ) / 4)) with hGdef
  have hG : 0 ≤ G := Gweight_nonneg _ _
  set N : ℕ := l.toNat / 3 + 1 with hN
  have hkl : ∀ k ∈ Finset.range N, (k : ℝ) ≤ (l : ℝ) := by
    intro k hk
    have hk3 : k ≤ l.toNat := by
      have := Finset.mem_range.mp hk
      omega
    have h : ((k : ℕ) : ℝ) ≤ ((l.toNat : ℕ) : ℝ) := Nat.cast_le.mpr hk3
    rwa [show ((l.toNat : ℕ) : ℝ) = (l : ℝ) by
      exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hl)] at h
  have hterm : ∀ k ∈ Finset.range N,
      (iidSum hold k (j, l)).toReal
        ≤ C0 * G * (1 / (1 + (k : ℝ))
            * (Real.exp (-(c1 ^ 2 / 2) * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-(c1 / 2) * |(l : ℝ) - 16 * k|))) := by
    intro k hk
    have h1 := hloc k j l
    rw [holdSum_eq_iidSum] at h1
    refine h1.trans ?_
    set u : ℝ := (j : ℝ) - 4 * k with hu
    set v : ℝ := (l : ℝ) - 16 * k with hv
    have h1k : (0 : ℝ) < 1 + (k : ℝ) := by positivity
    have h1kl : 1 + (k : ℝ) ≤ 1 + (l : ℝ) := by linarith [hkl k hk]
    -- sup norm dominates half the ℓ¹ norm
    have hnorm : ‖((u, v) : ℝ × ℝ)‖ = max |u| |v| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have hstep1 : Gweight (1 + (k : ℝ)) (c0 * ‖((u, v) : ℝ × ℝ)‖)
        ≤ Gweight (1 + (k : ℝ)) (c1 * (|u| + |v|)) := by
      apply Gweight_anti h1k (by positivity)
      rw [hnorm, hc1def]
      rcases max_cases |u| |v| with ⟨hm, hle⟩ | ⟨hm, hle⟩ <;> rw [hm] <;>
        nlinarith [abs_nonneg u, abs_nonneg v, hc0.le]
    -- drift-recentred triangle inequality: j - l/4 = u - v/4
    have hxe : (j : ℝ) - (l : ℝ) / 4 = u - v / 4 := by rw [hu, hv]; ring
    have hxabs : |(j : ℝ) - (l : ℝ) / 4| ≤ |u| + |v| / 4 := by
      rw [hxe, abs_le]
      constructor <;>
        · have h1 := le_abs_self u
          have h2 := neg_abs_le u
          have h3 := le_abs_self v
          have h4 := neg_abs_le v
          linarith
    have hy : |(j : ℝ) - (l : ℝ) / 4| + 3 / 4 * |v| ≤ |u| + |v| := by linarith
    have hstep2 := Gweight_factor (x := (j : ℝ) - (l : ℝ) / 4) (z := |v|)
      (y := |u| + |v|) hc1 h1k h1kl (abs_nonneg v) hy
    calc C0 / (1 + (k : ℝ)) * Gweight (1 + (k : ℝ)) (c0 * ‖((u, v) : ℝ × ℝ)‖)
        ≤ C0 / (1 + (k : ℝ)) * (G
            * (Real.exp (-(c1 ^ 2 / 2) * |v| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-(c1 / 2) * |v|))) := by
          apply mul_le_mul_of_nonneg_left (hstep1.trans hstep2) (by positivity)
      _ = C0 * G * (1 / (1 + (k : ℝ))
            * (Real.exp (-(c1 ^ 2 / 2) * |v| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-(c1 / 2) * |v|))) := by ring
  calc (renewalMass (j, l)).toReal
      = ∑ k ∈ Finset.range N, (iidSum hold k (j, l)).toReal := renewalMass_toReal_eq j l
    _ ≤ ∑ k ∈ Finset.range N, C0 * G * (1 / (1 + (k : ℝ))
          * (Real.exp (-(c1 ^ 2 / 2) * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-(c1 / 2) * |(l : ℝ) - 16 * k|))) := Finset.sum_le_sum hterm
    _ = C0 * G * ∑ k ∈ Finset.range N, 1 / (1 + (k : ℝ))
          * (Real.exp (-(c1 ^ 2 / 2) * |(l : ℝ) - 16 * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-(c1 / 2) * |(l : ℝ) - 16 * k|)) := by
        rw [Finset.mul_sum]
    _ ≤ C0 * G * (C5 / Real.sqrt (1 + (l : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (hsum l hl) (by positivity)
    _ = C0 * C5 / Real.sqrt (1 + (l : ℝ)) * G := by ring

/-- **Lemma 7.7 (Distribution of first passage location), D6 statement** (paper
p.43, (7.30)–(7.33)): the first-passage endpoint mass at `(j, l)` is
Gaussian-concentrated — `j` near `s/4` at scale `(1+s)^{1/2}`, `l` within
`O(1)` of `s`. For `l ≤ s` the left side vanishes (`fpDist_support_snd_gt`),
so the statement is unconditional.

OPEN (X6, step 3 — assembly): `fpDist_le_renewal_conv` + `renewalMass_bound`
at the pre-passage point `(j₁, l₁)`, `l₁ ≤ s`, + the single-step bounds
(`hold_local_bound`/`hold_tail_bound` at `n = 1`) for the overshoot step
`(j - j₁, l - l₁)`, `l - l₁ > s - l₁`; sum over the split `l₁ ≤ s/2` vs
`l₁ > s/2` (paper p.44 closing paragraph). -/
theorem fpDist_location_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (fpDist s (j, l)).toReal
        ≤ C * (Real.exp (-c * ((l : ℝ) - s)) / Real.sqrt (1 + s))
            * Gweight (1 + s) (c * ((j : ℝ) - s / 4)) := by
  sorry

end TaoCollatz
