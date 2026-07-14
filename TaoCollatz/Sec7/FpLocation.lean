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

/-- Convolving the unrestricted renewal measure with one final `hold` step is
exactly the positive-time renewal measure.  This is the commuted form of
`stepMass_eq_conv`; it is the convenient orientation for first passage, where
the pre-passage point is chosen before the final step. -/
theorem renewalMass_conv_hold_eq_stepMass (e : ℕ × ℤ) :
    (∑' p : ℕ × ℤ, renewalMass p *
      ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0)) = stepMass e := by
  rw [stepMass_eq_conv]
  calc
    (∑' p : ℕ × ℤ, renewalMass p *
        ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0))
        = ∑' p : ℕ × ℤ, ∑' d : ℕ × ℤ,
            renewalMass p * (if e = p + d then hold d else 0) := by
              refine tsum_congr fun p => ?_
              rw [ENNReal.tsum_mul_left]
    _ = ∑' d : ℕ × ℤ, ∑' p : ℕ × ℤ,
          renewalMass p * (if e = p + d then hold d else 0) := ENNReal.tsum_comm
    _ = ∑' d : ℕ × ℤ, hold d * ∑' p : ℕ × ℤ,
          (if e = d + p then renewalMass p else 0) := by
            refine tsum_congr fun d => ?_
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun p => ?_
            by_cases h : e = p + d
            · rw [if_pos h, if_pos (by simpa [add_comm] using h), mul_comm]
            · simp only [if_neg h, if_neg (by simpa [add_comm] using h), mul_zero]

/-- A first-passage endpoint is in particular a positive-time renewal endpoint.
Dropping the restriction that the pre-passage point lies below the budget line
turns `fpDist_le_renewal_conv` into `stepMass`. -/
theorem fpDist_le_stepMass (s : ℕ) (e : ℕ × ℤ) : fpDist s e ≤ stepMass e := by
  refine (fpDist_le_renewal_conv s e).trans ?_
  rw [← renewalMass_conv_hold_eq_stepMass e]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases hp : p.2 ≤ (s : ℤ)
  · rw [if_pos hp]
  · rw [if_neg hp, zero_mul]
    exact bot_le

/-- **Explicit transverse tail for first passage.**  The linear form
`16*j - 5*l` has negative drift under `Hold`.  At the tilt
`(1/1250, -1/4000)` the quadratic MGF exponent is exactly
`-39/400000` per step.  Since a first-passage endpoint is dominated by the
positive-time renewal measure, summing the iid Chernoff bound over every
possible passage time gives this fully explicit geometric tail.

This is the quantitative substitute for the paper's hidden-constant `O(1)`
localization in (7.50). -/
theorem fpDist_linear_tail (s : ℕ) (B : ℝ) :
    (∑' e : ℕ × ℤ,
      if B ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ) then fpDist s e else 0)
      ≤ ENNReal.ofReal (Real.exp (-B / 20000))
          * ENNReal.ofReal (Real.exp (-39 / 400000 : ℝ))
          * (1 - ENNReal.ofReal (Real.exp (-39 / 400000 : ℝ)))⁻¹ := by
  let cond : ℕ × ℤ → Prop := fun e =>
    B ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
  have hquad :
      4 * (1 / 1250 : ℝ) + 16 * (-(1 / 4000 : ℝ))
          + 1000 * ((1 / 1250 : ℝ) ^ 2 + (-(1 / 4000 : ℝ)) ^ 2)
        = -39 / 400000 := by norm_num
  have hchern : ∀ k : ℕ,
      (∑' e : ℕ × ℤ, if cond e then iidSum hold (k + 1) e else 0)
        ≤ ENNReal.ofReal
            (Real.exp (((k + 1 : ℕ) : ℝ) * (-39 / 400000) - B / 20000)) := by
    intro k
    have h := holdSum_halfspace_le
      (l1 := (1 / 1250 : ℝ)) (l2 := -(1 / 4000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (k + 1) cond (B / 20000) (fun e he => by
        dsimp only [cond] at he
        have hscale := div_le_div_of_nonneg_right he (by norm_num : (0 : ℝ) ≤ 20000)
        norm_num at hscale ⊢
        linarith)
    rw [hquad] at h
    exact h
  have hgeom :
      (∑' k : ℕ, ENNReal.ofReal
          (Real.exp (((k + 1 : ℕ) : ℝ) * (-39 / 400000) - B / 20000)))
        = ENNReal.ofReal (Real.exp (-B / 20000))
            * ENNReal.ofReal (Real.exp (-39 / 400000 : ℝ))
            * (1 - ENNReal.ofReal (Real.exp (-39 / 400000 : ℝ)))⁻¹ := by
    have hterm : ∀ k : ℕ,
        ENNReal.ofReal
            (Real.exp (((k + 1 : ℕ) : ℝ) * (-39 / 400000) - B / 20000))
          = ENNReal.ofReal (Real.exp (-B / 20000))
              * ENNReal.ofReal (Real.exp (-39 / 400000 : ℝ)) ^ (k + 1) := by
      intro k
      rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      ring_nf
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
    ac_rfl
  calc
    (∑' e : ℕ × ℤ, if B ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
        then fpDist s e else 0)
        ≤ ∑' e : ℕ × ℤ, if cond e then stepMass e else 0 := by
          refine ENNReal.tsum_le_tsum fun e => ?_
          by_cases he : cond e
          · rw [if_pos he, if_pos he]
            exact fpDist_le_stepMass s e
          · rw [if_neg he, if_neg he]
    _ = ∑' k : ℕ, ∑' e : ℕ × ℤ,
          if cond e then iidSum hold (k + 1) e else 0 := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun e => ?_
          by_cases he : cond e
          · rw [if_pos he]
            simp_rw [if_pos he]
            exact rfl
          · rw [if_neg he]
            simp_rw [if_neg he]
            exact (tsum_zero : (∑' _ : ℕ, (0 : ℝ≥0∞)) = 0).symm
    _ ≤ ∑' k : ℕ, ENNReal.ofReal
          (Real.exp (((k + 1 : ℕ) : ℝ) * (-39 / 400000) - B / 20000)) :=
        ENNReal.tsum_le_tsum hchern
    _ = _ := hgeom

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

/-- A deliberately conservative numerical instance of
`fpDist_linear_tail`.  Its large threshold is useful: it is certified solely
from the explicit quadratic MGF box, with no dependence on the existential
constants in `fpDist_location_bound`. -/
theorem fpDist_linear_tail_le_sixteenth (s : ℕ) :
    (∑' e : ℕ × ℤ,
      if (40000000 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
        then fpDist s e else 0) ≤ (1 : ℝ≥0∞) / 16 := by
  have h := fpDist_linear_tail s 40000000
  refine h.trans ?_
  have hx : (0 : ℝ) < 39 / 400000 := by norm_num
  have hexplt : Real.exp (-(39 / 400000 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hden : (0 : ℝ) < 1 - Real.exp (-(39 / 400000 : ℝ)) := by linarith
  have hinv := one_sub_exp_neg_inv_le_one_add hx
  have hfac : Real.exp (-(39 / 400000 : ℝ))
      * (1 - Real.exp (-(39 / 400000 : ℝ)))⁻¹ ≤ 20000 := by
    have he0 := (Real.exp_pos (-(39 / 400000 : ℝ))).le
    have he1 : Real.exp (-(39 / 400000 : ℝ)) ≤ 1 := hexplt.le
    calc Real.exp (-(39 / 400000 : ℝ))
          * (1 - Real.exp (-(39 / 400000 : ℝ)))⁻¹
        ≤ 1 * (1 + 1 / (39 / 400000 : ℝ)) :=
          mul_le_mul he1 hinv (by positivity) (by positivity)
      _ ≤ 20000 := by norm_num
  have hdecay : Real.exp (-(2000 : ℝ)) ≤ 1 / 1000000 := by
    calc Real.exp (-(2000 : ℝ)) ≤ 4 / (2000 : ℝ) ^ 2 :=
          exp_neg_le_four_div_sq (by norm_num)
      _ = 1 / 1000000 := by norm_num
  have hreal : Real.exp (-(2000 : ℝ))
      * (Real.exp (-(39 / 400000 : ℝ))
        * (1 - Real.exp (-(39 / 400000 : ℝ)))⁻¹) ≤ 1 / 16 := by
    calc Real.exp (-(2000 : ℝ))
          * (Real.exp (-(39 / 400000 : ℝ))
            * (1 - Real.exp (-(39 / 400000 : ℝ)))⁻¹)
        ≤ (1 / 1000000 : ℝ) * 20000 :=
          mul_le_mul hdecay hfac (by positivity) (by positivity)
      _ ≤ 1 / 16 := by norm_num
  have hrewrite :
      ENNReal.ofReal (Real.exp (-(40000000 : ℝ) / 20000))
          * ENNReal.ofReal (Real.exp (-39 / 400000 : ℝ))
          * (1 - ENNReal.ofReal (Real.exp (-39 / 400000 : ℝ)))⁻¹
        = ENNReal.ofReal
            (Real.exp (-(2000 : ℝ))
              * (Real.exp (-(39 / 400000 : ℝ))
                * (1 - Real.exp (-(39 / 400000 : ℝ)))⁻¹)) := by
    have hneg : (-39 / 400000 : ℝ) = -(39 / 400000 : ℝ) := by ring
    have hden' : (0 : ℝ) < 1 - Real.exp (-39 / 400000 : ℝ) := by
      rw [hneg]
      exact hden
    have hsub :
        (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-39 / 400000 : ℝ))
          = ENNReal.ofReal (1 - Real.exp (-39 / 400000 : ℝ)) := by
      rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
    rw [show (-(40000000 : ℝ) / 20000) = -2000 by norm_num, hsub,
      ← ENNReal.ofReal_inv_of_pos hden']
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [← ENNReal.ofReal_mul
      (by positivity : (0 : ℝ) ≤ Real.exp (-2000) * Real.exp (-39 / 400000))]
    congr 1
    rw [hneg]
    ring
  rw [hrewrite]
  have hout := ENNReal.ofReal_le_ofReal hreal
  have h16 : ENNReal.ofReal (1 / 16 : ℝ) = (1 : ℝ≥0∞) / 16 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16)]
    norm_num
  rwa [h16] at hout

/-- **Sharpened transverse tail for first passage** (the `B ≈ 64` version).  Same
Chernoff-over-renewal-times argument as `fpDist_linear_tail`, but tilted at the
*exact*-MGF-admissible `θ = 1/16` (tilt `(1,-5/16)` on `Z = 16j - 5l`) rather than
the quadratic box's `θ = 1/20000`.  The per-step MGF is bounded by the closed form
`tiltZ_hold_le_num` (`≤ 76/100 < 1`), so the geometric renewal sum converges and the
threshold that gives a `≤ 1/16` tail collapses from `4·10⁷` to `64`.  This removes the
`~10⁶` slack in the (7.50) localization box (node X11, constant `B`). -/
theorem fpDist_linear_tail_sharp (s : ℕ) (B : ℝ) :
    (∑' e : ℕ × ℤ,
      if B ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ) then fpDist s e else 0)
      ≤ ENNReal.ofReal (Real.exp (-(B / 16)))
          * ENNReal.ofReal (76 / 100)
          * (1 - ENNReal.ofReal (76 / 100))⁻¹ := by
  let cond : ℕ × ℤ → Prop := fun e => B ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
  have hchern : ∀ k : ℕ,
      (∑' e : ℕ × ℤ, if cond e then iidSum hold (k + 1) e else 0)
        ≤ ENNReal.ofReal (Real.exp (-(B / 16)))
            * ENNReal.ofReal (76 / 100) ^ (k + 1) := by
    intro k
    exact holdSum_halfspace_le_of_mgf (l1 := 1) (l2 := -5 / 16) (M := 76 / 100)
      tiltZ_hold_le_num (k + 1) cond (B / 16)
      (fun e he => by
        dsimp only [cond] at he
        push_cast
        linarith)
  have hgeom :
      (∑' k : ℕ, ENNReal.ofReal (Real.exp (-(B / 16)))
          * ENNReal.ofReal (76 / 100) ^ (k + 1))
        = ENNReal.ofReal (Real.exp (-(B / 16)))
            * ENNReal.ofReal (76 / 100)
            * (1 - ENNReal.ofReal (76 / 100))⁻¹ := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
    ac_rfl
  calc
    (∑' e : ℕ × ℤ, if B ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
        then fpDist s e else 0)
        ≤ ∑' e : ℕ × ℤ, if cond e then stepMass e else 0 := by
          refine ENNReal.tsum_le_tsum fun e => ?_
          by_cases he : cond e
          · rw [if_pos he, if_pos he]
            exact fpDist_le_stepMass s e
          · rw [if_neg he, if_neg he]
    _ = ∑' k : ℕ, ∑' e : ℕ × ℤ,
          if cond e then iidSum hold (k + 1) e else 0 := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun e => ?_
          by_cases he : cond e
          · rw [if_pos he]
            simp_rw [if_pos he]
            exact rfl
          · rw [if_neg he]
            simp_rw [if_neg he]
            exact (tsum_zero : (∑' _ : ℕ, (0 : ℝ≥0∞)) = 0).symm
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(B / 16)))
          * ENNReal.ofReal (76 / 100) ^ (k + 1) :=
        ENNReal.tsum_le_tsum hchern
    _ = _ := hgeom

/-- A sharp numerical instance of `fpDist_linear_tail_sharp` at `B = 64`: the
first-passage transverse tail past `16j - 5l = 64` has mass `≤ 1/16`.  This is the
`4·10⁷ → 64` replacement for `fpDist_linear_tail_le_sixteenth`; it is certified from
the exact closed-form `Hold` MGF (`tiltZ_hold_le_num`), still with no dependence on
the existential constants of `fpDist_location_bound`. -/
theorem fpDist_linear_tail_le_sixteenth_sharp (s : ℕ) :
    (∑' e : ℕ × ℤ,
      if (64 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
        then fpDist s e else 0) ≤ (1 : ℝ≥0∞) / 16 := by
  refine (fpDist_linear_tail_sharp s 64).trans ?_
  have h4 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 4 := by
    have he : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    exact pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 4
  have h5 : (1000 / 19 : ℝ) ≤ Real.exp 4 := le_trans (by norm_num) h4
  have he4 : Real.exp (-(64 / 16 : ℝ)) ≤ 19 / 1000 := by
    rw [show (-(64 / 16 : ℝ)) = -(4 : ℝ) from by norm_num, Real.exp_neg]
    calc (Real.exp 4)⁻¹ ≤ ((1000 / 19 : ℝ))⁻¹ := inv_anti₀ (by norm_num) h5
      _ = 19 / 1000 := by norm_num
  have hreal : Real.exp (-(64 / 16 : ℝ)) * (76 / 100) * (1 - 76 / 100)⁻¹ ≤ 1 / 16 := by
    rw [show ((1 : ℝ) - 76 / 100)⁻¹ = 100 / 24 from by norm_num]
    nlinarith [he4, (Real.exp_pos (-(64 / 16 : ℝ))).le]
  have hrewrite :
      ENNReal.ofReal (Real.exp (-(64 / 16 : ℝ))) * ENNReal.ofReal (76 / 100)
          * (1 - ENNReal.ofReal (76 / 100))⁻¹
        = ENNReal.ofReal
            (Real.exp (-(64 / 16 : ℝ)) * (76 / 100) * (1 - 76 / 100)⁻¹) := by
    have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (76 / 100)
        = ENNReal.ofReal (1 - 76 / 100) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
        ← ENNReal.ofReal_sub 1 (by norm_num)]
    rw [hsub, ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (by positivity)]
  rw [hrewrite]
  have hout := ENNReal.ofReal_le_ofReal hreal
  have h16 : ENNReal.ofReal (1 / 16 : ℝ) = (1 : ℝ≥0∞) / 16 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16)]
    norm_num
  rwa [h16] at hout

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
theorem renewalMass_eq_sum (j : ℕ) (l : ℤ) :
    renewalMass (j, l) = ∑ k ∈ Finset.range (l.toNat / 3 + 1), iidSum hold k (j, l) := by
  rw [renewalMass]
  refine tsum_eq_sum fun k hk => iidSum_hold_snd_zero k (j, l) ?_
  have hk' : l.toNat / 3 + 1 ≤ k := Nat.le_of_not_lt fun h => hk (Finset.mem_range.mpr h)
  show l < 3 * (k : ℤ)
  omega

theorem renewalMass_toReal_eq (j : ℕ) (l : ℤ) :
    (renewalMass (j, l)).toReal
      = ∑ k ∈ Finset.range (l.toNat / 3 + 1), (iidSum hold k (j, l)).toReal := by
  rw [renewalMass_eq_sum, ENNReal.toReal_sum fun k _ => PMF.apply_ne_top _ _]

/-- The renewal mass is finite (it is a finite sum of PMF values). -/
theorem renewalMass_ne_top (p : ℕ × ℤ) : renewalMass p ≠ ⊤ := by
  obtain ⟨j, l⟩ := p
  rw [renewalMass_eq_sum]
  exact (ENNReal.sum_lt_top.mpr fun k _ =>
    lt_of_le_of_lt (PMF.coe_le_one _ _) ENNReal.one_lt_top).ne

/-- Negative heights carry no renewal mass. -/
theorem renewalMass_zero_of_snd_neg {p : ℕ × ℤ} (hp : p.2 < 0) : renewalMass p = 0 := by
  rw [renewalMass]
  refine ENNReal.tsum_eq_zero.mpr fun k => iidSum_hold_snd_zero k p ?_
  have : (0 : ℤ) ≤ 3 * (k : ℤ) := by positivity
  omega

/-! ### Renewal mass per height level is `≤ 1` (strictly-increasing heights)

The height coordinate of the `Hold` renewal walk strictly increases (`+≥3` per
step, `hold_support_snd_ge`), so along any single trajectory each height level is
visited **at most once**.  Hence the expected number of renewal epochs at a fixed
height level `u` — `∑_j renewalMass (j,u)` — is `≤ 1`.  This is the "trick" that
lets the (7.50) vertical-overshoot radius `Y` be an explicit numeral instead of an
existential (judge pass 24).  The proof reduces to the 1-D height marginal
`hold.map Prod.snd` (a renewal process on `ℤ` with increments `≥ 3`) and the
renewal equation `U = δ₀ + F ⋆ U`, closed by strong induction on the level. -/

/-- The single-step height marginal `F = hold.map snd` is supported on `≥ 3`. -/
theorem holdSnd_support_ge {a : ℤ} (ha : (hold.map Prod.snd) a ≠ 0) : 3 ≤ a := by
  rw [← PMF.mem_support_iff, PMF.mem_support_map_iff] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  exact hold_support_snd_ge p hp

/-- A translation `map (a + ·)` on `ℤ` just shifts the argument. -/
theorem pmf_map_add_apply (μ : PMF ℤ) (a u : ℤ) :
    (μ.map (a + ·)) u = μ (u - a) := by
  rw [PMF.map_apply]
  refine (tsum_eq_single (u - a) (fun q hq => if_neg (fun h => ?_))).trans ?_
  · exact hq (by have : u = a + q := h; omega)
  · rw [if_pos (show u = a + (u - a) by ring)]

/-- The height renewal density `U(u) = ∑_k F^{*k}(u)`, where `F = hold.map snd`. -/
noncomputable def renewalHeight (u : ℤ) : ℝ≥0∞ :=
  ∑' k : ℕ, (iidSum (hold.map Prod.snd) k) u

/-- The height marginal after `k` steps equals the fiber sum of `iidSum hold k`. -/
theorem iidSum_holdSnd_apply (k : ℕ) (u : ℤ) :
    (iidSum (hold.map Prod.snd) k) u = ∑' j : ℕ, iidSum hold k (j, u) := by
  rw [← iidSum_map hold Prod.snd rfl (fun _ _ => rfl) k, PMF.map_apply, ENNReal.tsum_prod']
  refine tsum_congr fun j => ?_
  refine (tsum_eq_single u (fun l hl => if_neg (fun h => ?_))).trans ?_
  · exact hl h.symm
  · rw [if_pos rfl]

/-- Negative height levels carry no renewal mass. -/
theorem renewalHeight_zero_of_neg {u : ℤ} (hu : u < 0) : renewalHeight u = 0 := by
  show (∑' k : ℕ, (iidSum (hold.map Prod.snd) k) u) = 0
  refine ENNReal.tsum_eq_zero.mpr fun k => ?_
  rw [iidSum_holdSnd_apply]
  refine ENNReal.tsum_eq_zero.mpr fun j => ?_
  refine iidSum_hold_snd_zero k (j, u) ?_
  have : (0 : ℤ) ≤ 3 * (k : ℤ) := by positivity
  omega

/-- **Renewal equation** for the height density: `U(u) = δ₀(u) + ∑_a F(a)·U(u-a)`. -/
theorem renewalHeight_eq (u : ℤ) :
    renewalHeight u
      = (if u = 0 then 1 else 0)
        + ∑' a : ℤ, (hold.map Prod.snd) a * renewalHeight (u - a) := by
  have hstep : ∀ k : ℕ, (iidSum (hold.map Prod.snd) (k + 1)) u
      = ∑' a : ℤ, (hold.map Prod.snd) a * (iidSum (hold.map Prod.snd) k) (u - a) := by
    intro k
    rw [iidSum_succ, PMF.bind_apply]
    exact tsum_congr fun a => by rw [pmf_map_add_apply]
  have htail : (∑' k : ℕ, (iidSum (hold.map Prod.snd) (k + 1)) u)
      = ∑' a : ℤ, (hold.map Prod.snd) a * renewalHeight (u - a) := by
    calc (∑' k : ℕ, (iidSum (hold.map Prod.snd) (k + 1)) u)
        = ∑' k : ℕ, ∑' a : ℤ,
            (hold.map Prod.snd) a * (iidSum (hold.map Prod.snd) k) (u - a) :=
          tsum_congr hstep
      _ = ∑' a : ℤ, ∑' k : ℕ,
            (hold.map Prod.snd) a * (iidSum (hold.map Prod.snd) k) (u - a) :=
          ENNReal.tsum_comm
      _ = ∑' a : ℤ, (hold.map Prod.snd) a * renewalHeight (u - a) := by
          refine tsum_congr fun a => ?_
          rw [show renewalHeight (u - a)
              = ∑' k : ℕ, (iidSum (hold.map Prod.snd) k) (u - a) from rfl]
          exact ENNReal.tsum_mul_left
  rw [show renewalHeight u = ∑' k : ℕ, (iidSum (hold.map Prod.snd) k) u from rfl,
    tsum_eq_zero_add' ENNReal.summable, iidSum_zero, PMF.pure_apply]
  exact congr_arg₂ (· + ·) (by congr) htail

/-- **Renewal density per level is `≤ 1`.**  Strong induction on the (nonnegative)
level: at `u=0` only the `k=0` epoch contributes; at `u≥1` the renewal equation
folds each mass back to a strictly smaller level, and the increment law has total
mass `1`. -/
theorem renewalHeight_le_one (u : ℤ) : renewalHeight u ≤ 1 := by
  rcases lt_or_ge u 0 with hu | hu
  · rw [renewalHeight_zero_of_neg hu]; exact zero_le_one
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, u = (n : ℤ) := ⟨u.toNat, (Int.toNat_of_nonneg hu).symm⟩
  clear hu
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rw [renewalHeight_eq]
    have hbody : ∀ a : ℤ, (hold.map Prod.snd) a * renewalHeight ((n : ℤ) - a)
        ≤ (hold.map Prod.snd) a := by
      intro a
      by_cases hFa : (hold.map Prod.snd) a = 0
      · simp [hFa]
      · have ha3 : 3 ≤ a := holdSnd_support_ge hFa
        have hrec : renewalHeight ((n : ℤ) - a) ≤ 1 := by
          rcases lt_or_ge ((n : ℤ) - a) 0 with hneg | hpos
          · rw [renewalHeight_zero_of_neg hneg]; exact zero_le_one
          · obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℤ) - a = (m : ℤ) :=
              ⟨((n : ℤ) - a).toNat, (Int.toNat_of_nonneg hpos).symm⟩
            have hmn : m < n := by omega
            rw [hm]; exact IH m hmn
        calc (hold.map Prod.snd) a * renewalHeight ((n : ℤ) - a)
            ≤ (hold.map Prod.snd) a * 1 := by gcongr
          _ = (hold.map Prod.snd) a := mul_one _
    have hsum : (∑' a : ℤ, (hold.map Prod.snd) a * renewalHeight ((n : ℤ) - a)) ≤ 1 := by
      calc (∑' a : ℤ, (hold.map Prod.snd) a * renewalHeight ((n : ℤ) - a))
          ≤ ∑' a : ℤ, (hold.map Prod.snd) a := ENNReal.tsum_le_tsum hbody
        _ = 1 := (hold.map Prod.snd).tsum_coe
    by_cases hn0 : (n : ℤ) = 0
    · rw [if_pos hn0]
      have hz : (∑' a : ℤ, (hold.map Prod.snd) a * renewalHeight ((n : ℤ) - a)) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun a => ?_
        by_cases hFa : (hold.map Prod.snd) a = 0
        · rw [hFa, zero_mul]
        · have ha3 : 3 ≤ a := holdSnd_support_ge hFa
          rw [renewalHeight_zero_of_neg (by omega), mul_zero]
      rw [hz, add_zero]
    · rw [if_neg hn0, zero_add]
      exact hsum

/-- **Renewal mass per height level is `≤ 1`** (the strictly-increasing-heights
trick).  `∑_j renewalMass (j,u) ≤ 1`, uniformly in the level `u`. -/
theorem renewal_level_le_one (u : ℤ) :
    (∑' j : ℕ, renewalMass (j, u)) ≤ 1 := by
  have hrw : (∑' j : ℕ, renewalMass (j, u)) = renewalHeight u := by
    show (∑' j : ℕ, renewalMass (j, u)) = ∑' k : ℕ, (iidSum (hold.map Prod.snd) k) u
    calc (∑' j : ℕ, renewalMass (j, u))
        = ∑' j : ℕ, ∑' k : ℕ, iidSum hold k (j, u) := by
          refine tsum_congr fun j => ?_; rw [renewalMass]
      _ = ∑' k : ℕ, ∑' j : ℕ, iidSum hold k (j, u) := ENNReal.tsum_comm
      _ = ∑' k : ℕ, (iidSum (hold.map Prod.snd) k) u :=
          tsum_congr fun k => (iidSum_holdSnd_apply k u).symm
  rw [hrw]; exact renewalHeight_le_one u

/-- One draw: `iidSum hold 1 = hold` pointwise. -/
theorem iidSum_one_apply (p : ℕ × ℤ) : iidSum hold 1 p = hold p := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, iidSum_succ_apply]
  simp only [iidSum_zero]
  have hinner : ∀ d : ℕ × ℤ,
      (∑' q : ℕ × ℤ, if p = d + q then (PMF.pure (0 : ℕ × ℤ)) q else 0)
        = if p = d then 1 else 0 := by
    intro d
    rw [tsum_eq_single (0 : ℕ × ℤ)
      (fun q hq => by rw [PMF.pure_apply, if_neg hq, ite_self]), add_zero,
      PMF.pure_apply, if_pos rfl]
  rw [tsum_congr fun d => by rw [hinner d]]
  rw [tsum_eq_single p (fun d hd => by rw [if_neg (fun h => hd h.symm), mul_zero]),
    if_pos rfl, mul_one]

/-! ### Single-step height Chernoff and the explicit overshoot radius `Y` (node X11)

The (7.61)-type height tail `P(endpoint height ≥ s + Y) ≤ 1/16` is made EXPLICIT
(`Y = 150`) via the renewal decomposition instead of X6's existential envelope.
Ingredients: (i) `renewal_level_le_one` — heights strictly increase, so each level
carries renewal mass `≤ 1`; (ii) a single-step positive-tilt Chernoff bound on the
`hold` height increment, using the exact `Hold` MGF closed form at tilt `μ = 1/20`
(outside the `|μ| ≤ 1/50` polynomial box, so a fresh large-tilt numeric bound
`tiltZ_hold_snd_num` is proved, mirroring `tiltZ_hold_le_num` for `B`); (iii) a
geometric sum over the levels below the budget line. -/

/-- **Large-tilt numeric bound on the `pascalNe3` MGF** at the positive tilt
`λ = 1/20`: `Z_{ne3}(1/20) ≤ 1252/1000`.  Same atom-split as
`tiltZ_pascalNe3_le_num` (the `B` analogue at `-5/16`), here at the height-tail
tilt `μ = 1/20 ≈ 0.05`; the `Geom(2)` factor is bounded through
`e^{1/20} ≤ 1.05128` and the removed `b=3` atom below through `e^{3/20} ≥ 1.1618`
(both `Real.exp_bound`). -/
theorem tiltZ_pascalNe3_le_num_snd :
    tiltZ pascalNe3 (expW (1 / 20)) ≤ ENNReal.ofReal (1252 / 1000) := by
  have hlam_up : Real.exp (1 / 20) ≤ 105128 / 100000 := by
    have h := Real.exp_bound (x := 1 / 20)
      (by rw [abs_le]; constructor <;> norm_num) (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [Nat.factorial] at h
    rw [abs_le] at h; nlinarith [h.1, h.2]
  have h3lam_lo : (11618 / 10000 : ℝ) ≤ Real.exp (3 / 20) := by
    have h := Real.exp_bound (x := 3 / 20)
      (by rw [abs_le]; constructor <;> norm_num) (n := 7) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [Nat.factorial] at h
    rw [abs_le] at h; nlinarith [h.1, h.2]
  have hexp2 : Real.exp (1 / 20) < 2 := lt_of_le_of_lt hlam_up (by norm_num)
  -- `Geom(2)` factor: closed form ≤ ofReal((52564/100000)/(1-52564/100000))
  have hgh : tiltZ geomHalf (expW (1 / 20))
      ≤ ENNReal.ofReal ((52564 / 100000) / (1 - 52564 / 100000)) := by
    rw [tiltZ_geomHalf]
    exact geom_closed_le (by positivity) (by linarith) (by norm_num)
  have hZp : tiltZ pascal (expW (1 / 20))
      ≤ ENNReal.ofReal (((52564 / 100000) / (1 - 52564 / 100000)) ^ 2) := by
    rw [tiltZ_pascal hexp2, ENNReal.ofReal_pow (by norm_num)]
    exact pow_le_pow_left' hgh 2
  -- removed `b=3` atom, bounded below
  have he3 : ENNReal.ofReal ((1 / 3) * (11618 / 10000)) ≤ 3⁻¹ * expW (1 / 20) 3 := by
    rw [expW, show ((3 : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / 3) from by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
          ENNReal.ofReal_ofNat, one_div],
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have harg : (1 / 20 : ℝ) * (3 : ℕ) = 3 / 20 := by push_cast; ring
    rw [harg]
    nlinarith [h3lam_lo]
  have hfin : (3 : ℝ≥0∞)⁻¹ * expW (1 / 20) 3 ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top
  have hmain : tiltZ pascalNe3 (expW (1 / 20)) + 3⁻¹ * expW (1 / 20) 3
      ≤ ENNReal.ofReal (1252 / 1000) + 3⁻¹ * expW (1 / 20) 3 := by
    rw [tiltZ_pascalNe3_add (1 / 20)]
    calc (4 / 3 : ℝ≥0∞) * tiltZ pascal (expW (1 / 20))
        ≤ (4 / 3 : ℝ≥0∞) * ENNReal.ofReal (((52564 / 100000) / (1 - 52564 / 100000)) ^ 2) := by
          gcongr
      _ = ENNReal.ofReal ((4 / 3) * (((52564 / 100000) / (1 - 52564 / 100000)) ^ 2)) := by
          rw [show (4 / 3 : ℝ≥0∞) = ENNReal.ofReal (4 / 3) from by
              rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat,
                ENNReal.ofReal_ofNat],
            ← ENNReal.ofReal_mul (by norm_num)]
      _ ≤ ENNReal.ofReal (1252 / 1000) + ENNReal.ofReal ((1 / 3) * (11618 / 10000)) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (by norm_num)
      _ ≤ ENNReal.ofReal (1252 / 1000) + 3⁻¹ * expW (1 / 20) 3 := by gcongr
  exact (ENNReal.add_le_add_iff_right hfin).mp hmain

/-- **Large-tilt numeric bound on the second-coordinate `Hold` MGF** at
`μ = 1/20`: `Z(0, 1/20) ≤ 48/10`.  Via the exact closed form `tiltZ_hold_closed`
(so the tilt lives outside the `|μ| ≤ 1/50` box of `tiltZ_hold_snd`), with
`e^{3/20} ≤ 1.1619` (`Real.exp_bound`) and `tiltZ_pascalNe3_le_num_snd`; the
geometric ratio `(3/4)·1.252 = 0.939 < 1`.  Feeds the single-step height
Chernoff. -/
theorem tiltZ_hold_snd_num :
    tiltZ hold (expW2 0 (1 / 20)) ≤ ENNReal.ofReal (48 / 10) := by
  have hZt : tiltZ pascalNe3 (expW (1 / 20)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top tiltZ_pascalNe3_le_num_snd
  rw [tiltZ_hold_closed hZt]
  have hnum_up : Real.exp (0 + 3 * (1 / 20)) ≤ 11619 / 10000 := by
    have harg : (0 + 3 * (1 / 20) : ℝ) = 3 / 20 := by norm_num
    rw [harg]
    have h := Real.exp_bound (x := 3 / 20)
      (by rw [abs_le]; constructor <;> norm_num) (n := 7) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [Nat.factorial] at h
    rw [abs_le] at h; nlinarith [h.1, h.2]
  have he0 : (3 * Real.exp (0 : ℝ) / 4 : ℝ) = 3 / 4 := by rw [Real.exp_zero]; norm_num
  set rval : ℝ := (3 / 4) * (1252 / 1000) with hrval
  have hrval1 : rval < 1 := by rw [hrval]; norm_num
  have hS : ENNReal.ofReal (3 * Real.exp 0 / 4) * tiltZ pascalNe3 (expW (1 / 20))
      ≤ ENNReal.ofReal rval := by
    rw [he0]
    calc ENNReal.ofReal (3 / 4) * tiltZ pascalNe3 (expW (1 / 20))
        ≤ ENNReal.ofReal (3 / 4) * ENNReal.ofReal (1252 / 1000) :=
          mul_le_mul' le_rfl tiltZ_pascalNe3_le_num_snd
      _ = ENNReal.ofReal rval := by
          rw [← ENNReal.ofReal_mul (by norm_num), hrval]
  calc ENNReal.ofReal (Real.exp (0 + 3 * (1 / 20)) / 4)
        * (1 - ENNReal.ofReal (3 * Real.exp 0 / 4)
            * tiltZ pascalNe3 (expW (1 / 20)))⁻¹
      ≤ ENNReal.ofReal (Real.exp (0 + 3 * (1 / 20)) / 4)
          * (1 - ENNReal.ofReal rval)⁻¹ := by
        gcongr
    _ ≤ ENNReal.ofReal ((11619 / 10000 / 4) / (1 - rval)) := by
        exact frac_closed_le (a := Real.exp (0 + 3 * (1 / 20)) / 4)
          (a' := 11619 / 10000 / 4) (r := rval) (r' := rval)
          (by positivity) (by linarith) (le_of_lt (by rw [hrval]; positivity))
          le_rfl hrval1
    _ ≤ ENNReal.ofReal (48 / 10) := ENNReal.ofReal_le_ofReal (by rw [hrval]; norm_num)

/-- **Single-step height Chernoff.**  For an integer threshold `T`, the `hold`
step's height mass above `T` decays as `e^{-μT}` at tilt `μ = 1/20`:
`∑_{d : d.2 ≥ T} hold d ≤ e^{-T/20}·(48/10)`.  Markov-under-tilt in the second
coordinate (`holdSum_halfspace_le_of_mgf` at `n = 1`, `iidSum hold 1 = hold`), with
the MGF supplied by `tiltZ_hold_snd_num`. -/
theorem holdStep_height_tail (T : ℤ) :
    (∑' d : ℕ × ℤ, if T ≤ d.2 then hold d else 0)
      ≤ ENNReal.ofReal (Real.exp (-(1 / 20) * (T : ℝ))) * ENNReal.ofReal (48 / 10) := by
  have h := holdSum_halfspace_le_of_mgf (l1 := 0) (l2 := 1 / 20) (M := 48 / 10)
    tiltZ_hold_snd_num 1 (fun d => T ≤ d.2) ((1 / 20 : ℝ) * (T : ℝ))
    (fun d hd => by
      have hTd : ((T : ℝ)) ≤ (d.2 : ℝ) := by exact_mod_cast hd
      simp only [zero_mul, zero_add]
      nlinarith [hTd])
  simp only [pow_one] at h
  rw [show -(1 / 20) * (T : ℝ) = -((1 / 20 : ℝ) * (T : ℝ)) by ring]
  refine le_trans (le_of_eq ?_) h
  exact tsum_congr fun d => by rw [iidSum_one_apply]

/-- **Geometric sum over the levels below the budget line** (ℝ form).  Summing the
single-step tail prefactor `e^{-(1/20)(s+150-u)}` over all integer levels `u ≤ s`
gives the geometric total `e^{-(1/20)·150}/(1-e^{-1/20})`.  Reflection `u ↦ s-u`
turns the `u ≤ s` tail into the `k ≥ 0` half-line, then `of_nat_of_neg_add_one`
sums the resulting `ℕ`-geometric. -/
theorem hasSum_int_level_geom (s : ℕ) :
    HasSum (fun u : ℤ =>
        if u ≤ (s : ℤ) then Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (u : ℝ))) else 0)
      (Real.exp (-(1 / 20) * 150) / (1 - Real.exp (-(1 / 20)))) := by
  have he0 : (0 : ℝ) < Real.exp (-(1 / 20)) := Real.exp_pos _
  have he1 : Real.exp (-(1 / 20)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  rw [← (Equiv.subLeft (s : ℤ)).hasSum_iff]
  have hfun : ((fun u : ℤ =>
        if u ≤ (s : ℤ) then Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (u : ℝ))) else 0)
        ∘ (Equiv.subLeft (s : ℤ)))
      = fun k : ℤ => if 0 ≤ k then Real.exp (-(1 / 20) * (150 + (k : ℝ))) else 0 := by
    funext k
    simp only [Function.comp_apply, Equiv.subLeft_apply]
    by_cases hk : 0 ≤ k
    · rw [if_pos (by omega), if_pos hk]; congr 1; push_cast; ring
    · rw [if_neg (by omega), if_neg hk]
  rw [hfun]
  have hnat : HasSum (fun n : ℕ =>
        if 0 ≤ ((n : ℤ)) then Real.exp (-(1 / 20) * (150 + (((n : ℤ)) : ℝ))) else 0)
      (Real.exp (-(1 / 20) * 150) / (1 - Real.exp (-(1 / 20)))) := by
    have hgeo := (hasSum_geometric_of_lt_one he0.le he1).mul_left (Real.exp (-(1 / 20) * 150))
    rw [← div_eq_mul_inv] at hgeo
    have hrw : (fun n : ℕ =>
          if 0 ≤ ((n : ℤ)) then Real.exp (-(1 / 20) * (150 + (((n : ℤ)) : ℝ))) else 0)
        = fun n : ℕ => Real.exp (-(1 / 20) * 150) * Real.exp (-(1 / 20)) ^ n := by
      funext n
      rw [if_pos (by positivity), ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; push_cast; ring
    rw [hrw]; exact hgeo
  have hneg : HasSum (fun n : ℕ =>
        if 0 ≤ (-((n : ℤ) + 1)) then Real.exp (-(1 / 20) * (150 + ((-((n : ℤ) + 1)) : ℝ))) else 0)
      0 := by
    have hz : (fun n : ℕ =>
          if 0 ≤ (-((n : ℤ) + 1)) then Real.exp (-(1 / 20) * (150 + ((-((n : ℤ) + 1)) : ℝ))) else 0)
        = fun _ : ℕ => (0 : ℝ) := by
      funext n; rw [if_neg (by omega)]
    rw [hz]; exact hasSum_zero
  have hcombine := HasSum.of_nat_of_neg_add_one
    (f := fun k : ℤ => if 0 ≤ k then Real.exp (-(1 / 20) * (150 + (k : ℝ))) else 0)
    hnat hneg
  rwa [add_zero] at hcombine

/-- The `ℝ≥0∞` form of `hasSum_int_level_geom`, ready to feed the level-grouped
renewal sum. -/
theorem geom_level_sum_le (s : ℕ) :
    (∑' u : ℤ, if u ≤ (s : ℤ)
        then ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (u : ℝ)))) else 0)
      ≤ ENNReal.ofReal (Real.exp (-(1 / 20) * 150) / (1 - Real.exp (-(1 / 20)))) := by
  have hsum := hasSum_int_level_geom s
  have hnn : ∀ u : ℤ,
      0 ≤ (if u ≤ (s : ℤ) then Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (u : ℝ))) else 0) := by
    intro u; split <;> [positivity; rfl]
  refine le_of_eq ?_
  rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable]
  refine tsum_congr fun u => ?_
  split_ifs with h
  · rfl
  · exact (ENNReal.ofReal_zero).symm

/-- **Explicit (7.61) height tail** (node X11, `Y = 150`).  Apart from mass `1/16`,
a first-passage endpoint overshoots the start height `s` by at most `150`.  Unlike
`fpDist_height_tail_le_sixteenth` (whose radius is X6-existential), the radius here
is a numeral, so it feeds the localization-box inequality directly.  Route:
`fpDist_le_renewal_conv` (endpoint = a pre-passage point below the budget line plus
one `hold` step) + `renewal_level_le_one` (heights strictly increase ⟹ ≤ 1 renewal
mass per level) + `holdStep_height_tail` (single-step Chernoff at tilt `1/20`) +
`geom_level_sum_le` (geometric sum over the levels `u ≤ s`). -/
theorem fpDist_height_tail_le_sixteenth_sharp (s : ℕ) :
    (∑' e : ℕ × ℤ, if (s : ℝ) + 150 ≤ (e.2 : ℝ) then fpDist s e else 0)
      ≤ (1 : ℝ≥0∞) / 16 := by
  classical
  -- switch the real threshold for the integer one
  have hpred : ∀ e : ℕ × ℤ, ((s : ℝ) + 150 ≤ (e.2 : ℝ)) ↔ ((s : ℤ) + 150 ≤ e.2) := by
    intro e; constructor <;> intro h <;> exact_mod_cast h
  simp only [hpred]
  -- notation
  set C : ℝ≥0∞ := ENNReal.ofReal (48 / 10) with hC
  -- Step 1: renewal-convolution upper bound
  have hstep1 : (∑' e : ℕ × ℤ, if (s : ℤ) + 150 ≤ e.2 then fpDist s e else 0)
      ≤ ∑' e : ℕ × ℤ, if (s : ℤ) + 150 ≤ e.2
          then (∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
            * ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0)) else 0 := by
    refine ENNReal.tsum_le_tsum fun e => ?_
    by_cases he : (s : ℤ) + 150 ≤ e.2
    · rw [if_pos he, if_pos he]; exact fpDist_le_renewal_conv s e
    · rw [if_neg he, if_neg he]
  -- Step 2: swap the endpoint sum inward
  have hswap : (∑' e : ℕ × ℤ, if (s : ℤ) + 150 ≤ e.2
        then (∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
          * ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0)) else 0)
      = ∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
          * ∑' d : ℕ × ℤ, (if (s : ℤ) + 150 ≤ (p + d).2 then hold d else 0) := by
    have e1 : (∑' e : ℕ × ℤ, if (s : ℤ) + 150 ≤ e.2
          then (∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
            * ∑' d : ℕ × ℤ, (if e = p + d then hold d else 0)) else 0)
        = ∑' e : ℕ × ℤ, ∑' p : ℕ × ℤ, ∑' d : ℕ × ℤ,
            (if (s : ℤ) + 150 ≤ e.2
              then (if p.2 ≤ (s : ℤ) then renewalMass p else 0) * (if e = p + d then hold d else 0)
              else 0) := by
      refine tsum_congr fun e => ?_
      by_cases he : (s : ℤ) + 150 ≤ e.2
      · rw [if_pos he]
        refine tsum_congr fun p => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun d => (if_pos he).symm
      · simp only [if_neg he, tsum_zero]
    have e2 : (∑' e : ℕ × ℤ, ∑' p : ℕ × ℤ, ∑' d : ℕ × ℤ,
            (if (s : ℤ) + 150 ≤ e.2
              then (if p.2 ≤ (s : ℤ) then renewalMass p else 0) * (if e = p + d then hold d else 0)
              else 0))
        = ∑' p : ℕ × ℤ, ∑' d : ℕ × ℤ, ∑' e : ℕ × ℤ,
            (if (s : ℤ) + 150 ≤ e.2
              then (if p.2 ≤ (s : ℤ) then renewalMass p else 0) * (if e = p + d then hold d else 0)
              else 0) := by
      rw [ENNReal.tsum_comm]
      exact tsum_congr fun p => ENNReal.tsum_comm
    have e3 : (∑' p : ℕ × ℤ, ∑' d : ℕ × ℤ, ∑' e : ℕ × ℤ,
            (if (s : ℤ) + 150 ≤ e.2
              then (if p.2 ≤ (s : ℤ) then renewalMass p else 0) * (if e = p + d then hold d else 0)
              else 0))
        = ∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
            * ∑' d : ℕ × ℤ, (if (s : ℤ) + 150 ≤ (p + d).2 then hold d else 0) := by
      refine tsum_congr fun p => ?_
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun d => ?_
      rw [tsum_eq_single (p + d) (fun e' he' => by rw [if_neg he', mul_zero, ite_self]),
        if_pos rfl, mul_ite, mul_zero]
    rw [e1, e2, e3]
  -- now bound the swapped sum
  refine le_trans (hstep1.trans_eq hswap) ?_
  -- Step 3: single-step Chernoff on the inner hold tail
  have hstep3 : (∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
        * ∑' d : ℕ × ℤ, (if (s : ℤ) + 150 ≤ (p + d).2 then hold d else 0))
      ≤ ∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
          * (ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (p.2 : ℝ)))) * C) := by
    refine ENNReal.tsum_le_tsum fun p => ?_
    gcongr
    have hcond : (∑' d : ℕ × ℤ, (if (s : ℤ) + 150 ≤ (p + d).2 then hold d else 0))
        = ∑' d : ℕ × ℤ, (if (s : ℤ) + 150 - p.2 ≤ d.2 then hold d else 0) := by
      refine tsum_congr fun d => ?_
      by_cases hc : (s : ℤ) + 150 ≤ (p + d).2
      · rw [if_pos hc, if_pos (by simp only [Prod.snd_add] at hc ⊢; omega)]
      · rw [if_neg hc, if_neg (by simp only [Prod.snd_add] at hc ⊢; omega)]
    rw [hcond, hC]
    refine (holdStep_height_tail ((s : ℤ) + 150 - p.2)).trans_eq ?_
    congr 2
    push_cast; ring
  refine le_trans hstep3 ?_
  -- Step 4: pull out the constant `C`
  have hstep4 : (∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
        * (ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (p.2 : ℝ)))) * C))
      = C * ∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
          * ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (p.2 : ℝ)))) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun p => by ring
  rw [hstep4]
  -- Step 5: group by height level and apply `renewal_level_le_one`
  have hstep5 : (∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
        * ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (p.2 : ℝ)))))
      ≤ ∑' u : ℤ, if u ≤ (s : ℤ)
          then ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (u : ℝ)))) else 0 := by
    have hgroup : (∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
          * ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (p.2 : ℝ)))))
        = ∑' u : ℤ, ∑' j : ℕ, (if ((j, u) : ℕ × ℤ).2 ≤ (s : ℤ) then renewalMass (j, u) else 0)
            * ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - ((u : ℝ))))) := by
      rw [ENNReal.tsum_prod']; exact ENNReal.tsum_comm
    rw [hgroup]
    refine ENNReal.tsum_le_tsum fun u => ?_
    rw [ENNReal.tsum_mul_right]
    by_cases hu : u ≤ (s : ℤ)
    · have hle : (∑' j : ℕ, (if ((j, u) : ℕ × ℤ).2 ≤ (s : ℤ) then renewalMass (j, u) else 0))
          ≤ 1 := by
        simp only [if_pos hu]; exact renewal_level_le_one u
      calc (∑' j : ℕ, (if ((j, u) : ℕ × ℤ).2 ≤ (s : ℤ) then renewalMass (j, u) else 0))
            * ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (u : ℝ))))
          ≤ 1 * ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (u : ℝ)))) := by gcongr
        _ = ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (u : ℝ)))) := one_mul _
        _ = if u ≤ (s : ℤ)
              then ENNReal.ofReal (Real.exp (-(1 / 20) * ((s : ℝ) + 150 - (u : ℝ)))) else 0 :=
            (if_pos hu).symm
    · simp only [if_neg hu, tsum_zero, zero_mul, le_refl]
  refine le_trans (mul_le_mul_left' hstep5 C) ?_
  -- Step 6: geometric sum
  refine le_trans (mul_le_mul_left' (geom_level_sum_le s) C) ?_
  -- Step 7: the numeric bound
  rw [hC, ← ENNReal.ofReal_mul (by norm_num),
    show (1 : ℝ≥0∞) / 16 = ENNReal.ofReal (1 / 16) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num]
  refine ENNReal.ofReal_le_ofReal ?_
  have he1lo : Real.exp (-(1 / 20)) ≤ 9513 / 10000 := by
    have h := Real.exp_bound (x := -(1 / 20))
      (by rw [abs_le]; constructor <;> norm_num) (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [Nat.factorial] at h
    rw [abs_le] at h; nlinarith [h.1, h.2]
  have he0 : (0 : ℝ) < Real.exp (-(1 / 20)) := Real.exp_pos _
  have hden : (0 : ℝ) < 1 - Real.exp (-(1 / 20)) := by
    have : Real.exp (-(1 / 20)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    linarith
  -- upper bound on `exp(-7.5)` via `exp(7.5) = exp(3/4)^10 ≥ (211/100)^10 ≥ 1667`
  have h075 : (211 / 100 : ℝ) ≤ Real.exp (3 / 4) := by
    have h := Real.exp_bound (x := 3 / 4)
      (by rw [abs_le]; constructor <;> norm_num) (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num [Nat.factorial] at h
    rw [abs_le] at h; nlinarith [h.1, h.2]
  have h75 : (1667 : ℝ) ≤ Real.exp (15 / 2) := by
    rw [show (15 / 2 : ℝ) = (3 / 4) * 10 from by norm_num, Real.exp_mul,
      show ((10 : ℝ)) = ((10 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    calc (1667 : ℝ) ≤ (211 / 100) ^ 10 := by norm_num
      _ ≤ Real.exp (3 / 4) ^ 10 := by gcongr
  have he75 : Real.exp (-(1 / 20) * 150) ≤ 1 / 1667 := by
    rw [show (-(1 / 20) * 150 : ℝ) = -(15 / 2) from by norm_num, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h75
  -- combine
  rw [← mul_div_assoc, div_le_iff₀ hden]
  have hA : 48 / 10 * Real.exp (-(1 / 20) * 150) ≤ 48 / 10 * (1 / 1667) :=
    mul_le_mul_of_nonneg_left he75 (by norm_num)
  have hB : 1 / 16 * (1 - 9513 / 10000) ≤ 1 / 16 * (1 - Real.exp (-(1 / 20))) :=
    mul_le_mul_of_nonneg_left (by linarith [he1lo]) (by norm_num)
  linarith [hA, hB]

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

/-! ### Gweight algebra for the last-step convolution (Lemma 7.7 assembly)

The overshoot step contributes an exponential factor in both coordinates
(`Gweight_two_le` on `hold_local_bound` at `n = 1`); convolving it against the
renewal Gaussian needs: a step-1 arithmetic-progression sum, a pointwise
Gaussian×exponential convolution bound, a shift-absorption lemma (recentring
`j - l₁/4` to `j - s/4` at cost `e^{c|δ|}`), and the `l₁`-sum envelope. -/

/-- The exponential part alone lower-bounds `Gweight`. -/
theorem exp_neg_abs_le_Gweight (t x : ℝ) : Real.exp (-|x|) ≤ Gweight t x := by
  unfold Gweight
  linarith [(Real.exp_pos (-x ^ 2 / t)).le]

/-- `Gweight` is monotone in the time scale. -/
theorem Gweight_mono_t {t1 t2 : ℝ} (ht1 : 0 < t1) (ht : t1 ≤ t2) (x : ℝ) :
    Gweight t1 x ≤ Gweight t2 x := by
  unfold Gweight
  have ht2 : 0 < t2 := lt_of_lt_of_le ht1 ht
  have h1 : Real.exp (-x ^ 2 / t1) ≤ Real.exp (-x ^ 2 / t2) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg x) ht1 ht
  linarith

/-- At time scale `2` the Gaussian part is dominated by the exponential:
`Gweight 2 x ≤ 4·e^{-x/2}` for `x ≥ 0`. -/
theorem Gweight_two_le {x : ℝ} (hx : 0 ≤ x) : Gweight 2 x ≤ 4 * Real.exp (-x / 2) := by
  unfold Gweight
  have hg : Real.exp (-x ^ 2 / 2) ≤ 3 * Real.exp (-x / 2) := by
    rcases le_total x 1 with h1 | h1
    · have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-x / 2) := by
        have := Real.add_one_le_exp (-x / 2)
        linarith
      have h1 : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      linarith
    · calc Real.exp (-x ^ 2 / 2) ≤ Real.exp (-x / 2) :=
            Real.exp_le_exp.mpr (by nlinarith)
        _ ≤ 3 * Real.exp (-x / 2) := by linarith [(Real.exp_pos (-x / 2)).le]
  have he : Real.exp (-|x|) ≤ Real.exp (-x / 2) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hx]
    linarith
  linarith

/-- Step-1 analogue of `sum_abs_AP_le`, with an integer (possibly negative)
centre: the offsets `|w - k|`, `k < J`, cover each value `m` at most twice. -/
theorem sum_abs_int_le {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u)
    (hanti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v → f v ≤ f u)
    (w : ℤ) (J : ℕ) (hw : w.toNat < J) :
    ∑ k ∈ Finset.range J, f |(w : ℝ) - k| ≤ 2 * ∑ m ∈ Finset.range J, f m := by
  set q : ℕ := w.toNat with hq
  have hcast : ∀ k : ℕ, ∀ n : ℕ, ((n : ℤ) ≤ |w - (k : ℤ)|) →
      ((n : ℝ) ≤ |(w : ℝ) - (k : ℝ)|) := by
    intro k n h
    have h2 : ((n : ℤ) : ℝ) ≤ ((|w - (k : ℤ)| : ℤ) : ℝ) := Int.cast_le.mpr h
    push_cast at h2
    exact h2
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range J) (fun k => k ≤ q)]
  have hA : ∑ k ∈ (Finset.range J).filter (fun k => k ≤ q), f |(w : ℝ) - k|
      ≤ ∑ m ∈ Finset.range J, f m := by
    have hstep : ∀ k ∈ (Finset.range J).filter (fun k => k ≤ q),
        f |(w : ℝ) - k| ≤ f ((q - k : ℕ) : ℝ) := by
      intro k hk
      have hkq : k ≤ q := (Finset.mem_filter.mp hk).2
      refine hanti (by positivity) (hcast k _ ?_)
      rcases abs_cases (w - (k : ℤ)) with ⟨he, h0⟩ | ⟨he, h0⟩ <;> omega
    have hinj : ∀ x ∈ (Finset.range J).filter (fun k => k ≤ q),
        ∀ y ∈ (Finset.range J).filter (fun k => k ≤ q), q - x = q - y → x = y := by
      intro x hx y hy hxy
      have := (Finset.mem_filter.mp hx).2
      have := (Finset.mem_filter.mp hy).2
      omega
    have key : ∑ m ∈ ((Finset.range J).filter (fun k => k ≤ q)).image (fun k => q - k),
        f (m : ℝ)
        = ∑ k ∈ (Finset.range J).filter (fun k => k ≤ q), f ((q - k : ℕ) : ℝ) :=
      Finset.sum_image hinj
    calc ∑ k ∈ (Finset.range J).filter (fun k => k ≤ q), f |(w : ℝ) - k|
        ≤ ∑ k ∈ (Finset.range J).filter (fun k => k ≤ q), f ((q - k : ℕ) : ℝ) :=
          Finset.sum_le_sum hstep
      _ = ∑ m ∈ ((Finset.range J).filter (fun k => k ≤ q)).image (fun k => q - k),
            f (m : ℝ) := key.symm
      _ ≤ ∑ m ∈ Finset.range J, f m := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn _
          intro m hm
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
          exact Finset.mem_range.mpr (by omega)
  have hB : ∑ k ∈ (Finset.range J).filter (fun k => ¬ k ≤ q), f |(w : ℝ) - k|
      ≤ ∑ m ∈ Finset.range J, f m := by
    have hstep : ∀ k ∈ (Finset.range J).filter (fun k => ¬ k ≤ q),
        f |(w : ℝ) - k| ≤ f ((k - (q + 1) : ℕ) : ℝ) := by
      intro k hk
      have hkq : q < k := Nat.lt_of_not_le (Finset.mem_filter.mp hk).2
      refine hanti (by positivity) (hcast k _ ?_)
      rcases abs_cases (w - (k : ℤ)) with ⟨he, h0⟩ | ⟨he, h0⟩ <;> omega
    have hinj : ∀ x ∈ (Finset.range J).filter (fun k => ¬ k ≤ q),
        ∀ y ∈ (Finset.range J).filter (fun k => ¬ k ≤ q),
          x - (q + 1) = y - (q + 1) → x = y := by
      intro x hx y hy hxy
      have := Nat.lt_of_not_le (Finset.mem_filter.mp hx).2
      have := Nat.lt_of_not_le (Finset.mem_filter.mp hy).2
      omega
    have key : ∑ m ∈ ((Finset.range J).filter (fun k => ¬ k ≤ q)).image
          (fun k => k - (q + 1)), f (m : ℝ)
        = ∑ k ∈ (Finset.range J).filter (fun k => ¬ k ≤ q), f ((k - (q + 1) : ℕ) : ℝ) :=
      Finset.sum_image hinj
    calc ∑ k ∈ (Finset.range J).filter (fun k => ¬ k ≤ q), f |(w : ℝ) - k|
        ≤ ∑ k ∈ (Finset.range J).filter (fun k => ¬ k ≤ q), f ((k - (q + 1) : ℕ) : ℝ) :=
          Finset.sum_le_sum hstep
      _ = ∑ m ∈ ((Finset.range J).filter (fun k => ¬ k ≤ q)).image
            (fun k => k - (q + 1)), f (m : ℝ) := key.symm
      _ ≤ ∑ m ∈ Finset.range J, f m := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn _
          intro m hm
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
          have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
          exact Finset.mem_range.mpr (by omega)
  linarith

/-- Geometric comparison: `∑_{m<J} e^{-γm} ≤ 1 + 1/γ`. -/
theorem sum_exp_geom_le {γ : ℝ} (hγ : 0 < γ) (J : ℕ) :
    ∑ m ∈ Finset.range J, Real.exp (-γ * m) ≤ 1 + 1 / γ := by
  have hterm : ∀ m : ℕ, Real.exp (-γ * m) = Real.exp (-γ) ^ m := by
    intro m
    rw [← Real.exp_nat_mul]
    exact congrArg Real.exp (by ring)
  rw [Finset.sum_congr rfl fun m _ => hterm m]
  have hr1 : Real.exp (-γ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  calc ∑ m ∈ Finset.range J, Real.exp (-γ) ^ m
      ≤ (1 - Real.exp (-γ))⁻¹ := sum_range_geom_le (Real.exp_pos _).le hr1 J
    _ ≤ 1 + 1 / γ := one_sub_exp_neg_inv_le_one_add hγ

/-- **Shift absorption**: recentring the `Gweight` argument by `δ` (and
widening the time scale) costs a factor `2·e^{c|δ|}` and half the decay
constant. -/
theorem Gweight_shift {t1 t2 c : ℝ} (ht1 : 0 < t1) (ht : t1 ≤ t2) (hc : 0 < c)
    (X δ : ℝ) :
    Gweight t1 (c * (X + δ)) ≤ 2 * Real.exp (c * |δ|) * Gweight t2 (c / 2 * X) := by
  have hE1 : (1 : ℝ) ≤ Real.exp (c * |δ|) :=
    Real.one_le_exp (by positivity)
  rcases le_total |X| (2 * |δ|) with hcase | hcase
  · -- near: crude bound 2, matched by the shift factor
    calc Gweight t1 (c * (X + δ)) ≤ 2 := Gweight_le_two _ _ ht1.le
      _ ≤ 2 * Real.exp (c * |δ|) * Real.exp (-|c / 2 * X|) := by
          rw [mul_assoc, ← Real.exp_add]
          have hle : 0 ≤ c * |δ| - |c / 2 * X| := by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < c / 2)]
            nlinarith [abs_nonneg X, abs_nonneg δ]
          have := Real.one_le_exp (by linarith : (0:ℝ) ≤ c * |δ| + -|c / 2 * X|)
          linarith
      _ ≤ 2 * Real.exp (c * |δ|) * Gweight t2 (c / 2 * X) := by
          apply mul_le_mul_of_nonneg_left (exp_neg_abs_le_Gweight _ _) (by positivity)
  · -- far: |X + δ| ≥ |X|/2, use antitonicity and time-scale monotonicity
    have habs : |X| / 2 ≤ |X + δ| := by
      have := abs_add_le (X + δ) (-δ)
      simp only [add_neg_cancel_right, abs_neg] at this
      linarith
    calc Gweight t1 (c * (X + δ))
        = Gweight t1 (c * |X + δ|) := by rw [← Gweight_abs, abs_mul, abs_of_pos hc]
      _ ≤ Gweight t1 (c / 2 * |X|) := by
          apply Gweight_anti ht1 (by positivity)
          nlinarith [abs_nonneg (X + δ)]
      _ ≤ Gweight t2 (c / 2 * |X|) := Gweight_mono_t ht1 ht _
      _ = Gweight t2 (c / 2 * X) := by
          rw [show c / 2 * |X| = |c / 2 * X| by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < c / 2)], Gweight_abs]
      _ ≤ 2 * Real.exp (c * |δ|) * Gweight t2 (c / 2 * X) := by
          nlinarith [Gweight_nonneg t2 (c / 2 * X)]

/-- **Discrete Gaussian × exponential convolution** (the `j₁`-sum of the
Lemma 7.7 assembly): summing the renewal Gaussian at centre `μ` against an
exponential window at centre `w` reproduces a Gaussian at centre `w`, with
decay constant `min(c/2, γ/4)`. -/
theorem conv_Gweight_exp {t c γ : ℝ} (ht : 0 < t) (hc : 0 < c) (hγ : 0 < γ)
    (μ : ℝ) (w : ℤ) (J : ℕ) (hw : w.toNat < J) :
    ∑ k ∈ Finset.range J, Gweight t (c * (k - μ)) * Real.exp (-γ * |(w : ℝ) - k|)
      ≤ (4 + 8 / γ) * Gweight t (min (c / 2) (γ / 4) * ((w : ℝ) - μ)) := by
  set c9 : ℝ := min (c / 2) (γ / 4) with hc9def
  have hc9 : 0 < c9 := lt_min (by positivity) (by positivity)
  set G : ℝ := Gweight t (c9 * ((w : ℝ) - μ)) with hGdef
  have hG : 0 ≤ G := Gweight_nonneg _ _
  -- pointwise: each term ≤ 2·G·e^{-(γ/2)|w-k|}
  have hpt : ∀ k : ℕ, Gweight t (c * (k - μ)) * Real.exp (-γ * |(w : ℝ) - k|)
      ≤ 2 * G * Real.exp (-(γ / 2) * |(w : ℝ) - k|) := by
    intro k
    rcases le_total (|(w : ℝ) - μ| / 2) |(k : ℝ) - μ| with hfar | hnear
    · -- far from the Gaussian centre: the Gaussian factor is already small
      have h1 : Gweight t (c * (k - μ)) ≤ G := by
        rw [hGdef, ← Gweight_abs t (c9 * _), ← Gweight_abs t (c * _)]
        rw [abs_mul, abs_mul, abs_of_pos hc, abs_of_pos hc9]
        apply Gweight_anti ht (by positivity)
        have hc92 : c9 ≤ c / 2 := min_le_left _ _
        nlinarith [abs_nonneg ((w : ℝ) - μ), abs_nonneg ((k : ℝ) - μ)]
      have h2 : Real.exp (-γ * |(w : ℝ) - k|) ≤ Real.exp (-(γ / 2) * |(w : ℝ) - k|) := by
        apply Real.exp_le_exp.mpr
        nlinarith [abs_nonneg ((w : ℝ) - k)]
      calc Gweight t (c * (k - μ)) * Real.exp (-γ * |(w : ℝ) - k|)
          ≤ G * Real.exp (-(γ / 2) * |(w : ℝ) - k|) :=
            mul_le_mul h1 h2 (Real.exp_pos _).le hG
        _ ≤ 2 * G * Real.exp (-(γ / 2) * |(w : ℝ) - k|) := by
            nlinarith [(Real.exp_pos (-(γ / 2) * |(w : ℝ) - k|)).le, hG]
    · -- near the Gaussian centre: the exponential window is small there
      have hwk : |(w : ℝ) - μ| / 2 ≤ |(w : ℝ) - k| := by
        have := abs_add_le ((w : ℝ) - k) ((k : ℝ) - μ)
        have heq : (w : ℝ) - k + ((k : ℝ) - μ) = (w : ℝ) - μ := by ring
        rw [heq] at this
        linarith
      have h1 : Gweight t (c * (k - μ)) ≤ 2 := Gweight_le_two _ _ ht.le
      have h2 : Real.exp (-γ * |(w : ℝ) - k|)
          ≤ Real.exp (-(γ / 2) * |(w : ℝ) - k|) * Real.exp (-(γ / 4) * |(w : ℝ) - μ|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [abs_nonneg ((w : ℝ) - k), abs_nonneg ((w : ℝ) - μ)]
      have h3 : Real.exp (-(γ / 4) * |(w : ℝ) - μ|) ≤ G := by
        rw [hGdef]
        calc Real.exp (-(γ / 4) * |(w : ℝ) - μ|)
            ≤ Real.exp (-|c9 * ((w : ℝ) - μ)|) := by
              apply Real.exp_le_exp.mpr
              rw [abs_mul, abs_of_pos hc9]
              have hc94 : c9 ≤ γ / 4 := min_le_right _ _
              nlinarith [abs_nonneg ((w : ℝ) - μ)]
          _ ≤ Gweight t (c9 * ((w : ℝ) - μ)) := exp_neg_abs_le_Gweight _ _
      calc Gweight t (c * (k - μ)) * Real.exp (-γ * |(w : ℝ) - k|)
          ≤ 2 * (Real.exp (-(γ / 2) * |(w : ℝ) - k|)
              * Real.exp (-(γ / 4) * |(w : ℝ) - μ|)) := by
            apply mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
        _ ≤ 2 * G * Real.exp (-(γ / 2) * |(w : ℝ) - k|) := by
            have := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-(γ / 2) * |(w : ℝ) - k|)).le
            nlinarith
  calc ∑ k ∈ Finset.range J, Gweight t (c * (k - μ)) * Real.exp (-γ * |(w : ℝ) - k|)
      ≤ ∑ k ∈ Finset.range J, 2 * G * Real.exp (-(γ / 2) * |(w : ℝ) - k|) :=
        Finset.sum_le_sum fun k _ => hpt k
    _ = 2 * G * ∑ k ∈ Finset.range J, Real.exp (-(γ / 2) * |(w : ℝ) - k|) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * G * (2 * (1 + 1 / (γ / 2))) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ k ∈ Finset.range J, Real.exp (-(γ / 2) * |(w : ℝ) - k|)
            ≤ 2 * ∑ m ∈ Finset.range J, Real.exp (-(γ / 2) * m) :=
              sum_abs_int_le (fun u => (Real.exp_pos _).le)
                (fun u v hu huv => Real.exp_le_exp.mpr (by nlinarith)) w J hw
          _ ≤ 2 * (1 + 1 / (γ / 2)) := by
              have := sum_exp_geom_le (by positivity : (0:ℝ) < γ / 2) J
              linarith
    _ = (4 + 8 / γ) * G := by
        field_simp
        ring

/-- **The single-overshoot-step bound**: one `hold` step has exponential decay
in both drift-recentred coordinates (from `hold_local_bound` at `n = 1` via
`Gweight_two_le`). -/
theorem hold_step_bound :
    ∃ γ > (0 : ℝ), ∃ C7 > (0 : ℝ), ∀ d : ℕ × ℤ,
      (hold d).toReal
        ≤ C7 * Real.exp (-γ * |(d.1 : ℝ) - 4|) * Real.exp (-γ * |(d.2 : ℝ) - 16|) := by
  obtain ⟨c0, hc0, C0, hC0, hloc⟩ := hold_local_bound
  refine ⟨c0 / 4, by positivity, 2 * C0, by positivity, fun d => ?_⟩
  have h1 := hloc 1 d.1 d.2
  rw [holdSum_eq_iidSum] at h1
  have hd : ((d.1, d.2) : ℕ × ℤ) = d := rfl
  rw [hd, iidSum_one_apply] at h1
  refine h1.trans ?_
  set A : ℝ := (d.1 : ℝ) - 4 * (1 : ℕ) with hA
  set B : ℝ := (d.2 : ℝ) - 16 * (1 : ℕ) with hB
  have hnorm : ‖((A, B) : ℝ × ℝ)‖ = max |A| |B| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : (0 : ℝ) < 1 + (1 : ℕ) := by norm_num
  have hstep1 : Gweight (1 + ((1 : ℕ) : ℝ)) (c0 * ‖((A, B) : ℝ × ℝ)‖)
      ≤ Gweight (1 + ((1 : ℕ) : ℝ)) (c0 / 2 * (|A| + |B|)) := by
    apply Gweight_anti (by push_cast; norm_num) (by positivity)
    rw [hnorm]
    rcases max_cases |A| |B| with ⟨hm, hle⟩ | ⟨hm, hle⟩ <;> rw [hm] <;>
      nlinarith [abs_nonneg A, abs_nonneg B, hc0.le]
  have hstep2 : Gweight (1 + ((1 : ℕ) : ℝ)) (c0 / 2 * (|A| + |B|))
      ≤ 4 * Real.exp (-(c0 / 4) * |A|) * Real.exp (-(c0 / 4) * |B|) := by
    have h12 : (1 : ℝ) + ((1 : ℕ) : ℝ) = 2 := by push_cast; norm_num
    rw [h12]
    calc Gweight 2 (c0 / 2 * (|A| + |B|))
        ≤ 4 * Real.exp (-(c0 / 2 * (|A| + |B|)) / 2) :=
          Gweight_two_le (by positivity)
      _ = 4 * Real.exp (-(c0 / 4) * |A|) * Real.exp (-(c0 / 4) * |B|) := by
          rw [mul_assoc, ← Real.exp_add]
          exact congrArg (4 * ·) (congrArg Real.exp (by ring))
  have hAe : |A| = |(d.1 : ℝ) - 4| := by rw [hA]; push_cast; norm_num
  have hBe : |B| = |(d.2 : ℝ) - 16| := by rw [hB]; push_cast; norm_num
  calc C0 / (1 + ((1 : ℕ) : ℝ))
      * Gweight (1 + ((1 : ℕ) : ℝ)) (c0 * ‖((A, B) : ℝ × ℝ)‖)
      ≤ C0 / (1 + ((1 : ℕ) : ℝ))
        * (4 * Real.exp (-(c0 / 4) * |A|) * Real.exp (-(c0 / 4) * |B|)) := by
        apply mul_le_mul_of_nonneg_left (hstep1.trans hstep2) (by positivity)
    _ = 2 * C0 * Real.exp (-(c0 / 4) * |A|) * Real.exp (-(c0 / 4) * |B|) := by
        push_cast
        ring
    _ = 2 * C0 * Real.exp (-(c0 / 4) * |(d.1 : ℝ) - 4|)
        * Real.exp (-(c0 / 4) * |(d.2 : ℝ) - 16|) := by
        rw [hAe, hBe]

/-- The `l₁`-sum envelope for the Lemma 7.7 assembly: the exponential window
at the budget line beats the `1/√(1+l₁)` renewal prefactor, at cost
`1/√(1+s)`. -/
theorem sum_sqrt_exp_le {γ : ℝ} (hγ : 0 < γ) :
    ∃ K > (0 : ℝ), ∀ s : ℕ,
      ∑ m ∈ Finset.range (s + 1), Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
        ≤ K / Real.sqrt (1 + s) := by
  refine ⟨2 * (1 + 1 / γ) + 64 / γ ^ 2, by positivity, fun s => ?_⟩
  have h1s : (0 : ℝ) < 1 + (s : ℝ) := by positivity
  have hs0 : 0 < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr h1s
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (s + 1)) (fun m => s ≤ 2 * m)]
  have hhigh : ∑ m ∈ (Finset.range (s + 1)).filter (fun m => s ≤ 2 * m),
      Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
      ≤ (2 * (1 + 1 / γ)) / Real.sqrt (1 + s) := by
    have hpt : ∀ m ∈ (Finset.range (s + 1)).filter (fun m => s ≤ 2 * m),
        Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
          ≤ Real.exp (-γ * ((s : ℝ) - m)) * (2 / Real.sqrt (1 + s)) := by
      intro m hm
      have hm2 : s ≤ 2 * m := (Finset.mem_filter.mp hm).2
      have h1m : (0 : ℝ) < 1 + (m : ℝ) := by positivity
      have hsm : Real.sqrt (1 + (s : ℝ)) ≤ 2 * Real.sqrt (1 + (m : ℝ)) := by
        calc Real.sqrt (1 + (s : ℝ)) ≤ Real.sqrt (4 * (1 + (m : ℝ))) := by
              apply Real.sqrt_le_sqrt
              have : (s : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hm2
              linarith
          _ = 2 * Real.sqrt (1 + (m : ℝ)) := by
              rw [show (4 : ℝ) * (1 + (m : ℝ)) = 2 ^ 2 * (1 + (m : ℝ)) by ring,
                Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2 ^ 2),
                Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      have hfrac : 1 / Real.sqrt (1 + (m : ℝ)) ≤ 2 / Real.sqrt (1 + (s : ℝ)) := by
        rw [div_le_div_iff₀ (Real.sqrt_pos.mpr h1m) hs0]
        linarith
      calc Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
          = Real.exp (-γ * ((s : ℝ) - m)) * (1 / Real.sqrt (1 + (m : ℝ))) := by ring
        _ ≤ Real.exp (-γ * ((s : ℝ) - m)) * (2 / Real.sqrt (1 + (s : ℝ))) :=
            mul_le_mul_of_nonneg_left hfrac (Real.exp_pos _).le
    calc ∑ m ∈ (Finset.range (s + 1)).filter (fun m => s ≤ 2 * m),
        Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
        ≤ ∑ m ∈ (Finset.range (s + 1)).filter (fun m => s ≤ 2 * m),
          Real.exp (-γ * ((s : ℝ) - m)) * (2 / Real.sqrt (1 + s)) :=
          Finset.sum_le_sum hpt
      _ ≤ ∑ m ∈ Finset.range (s + 1),
          Real.exp (-γ * ((s : ℝ) - m)) * (2 / Real.sqrt (1 + s)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => by positivity
      _ = (∑ m ∈ Finset.range (s + 1), Real.exp (-γ * ((s : ℝ) - m)))
          * (2 / Real.sqrt (1 + s)) := by rw [← Finset.sum_mul]
      _ ≤ (1 + 1 / γ) * (2 / Real.sqrt (1 + s)) := by
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hre : ∑ m ∈ Finset.range (s + 1), Real.exp (-γ * ((s : ℝ) - m))
              = ∑ m ∈ Finset.range (s + 1), Real.exp (-γ * (m : ℝ)) := by
            rw [← Finset.sum_range_reflect (fun m => Real.exp (-γ * (m : ℝ))) (s + 1)]
            refine Finset.sum_congr rfl fun m hm => ?_
            have hm' : m ≤ s := by
              have := Finset.mem_range.mp hm
              omega
            congr 1
            rw [show s + 1 - 1 - m = s - m by omega, Nat.cast_sub hm']
          rw [hre]
          exact sum_exp_geom_le hγ (s + 1)
      _ = (2 * (1 + 1 / γ)) / Real.sqrt (1 + s) := by ring
  have hlow : ∑ m ∈ (Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m),
      Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
      ≤ (64 / γ ^ 2) / Real.sqrt (1 + s) := by
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · rw [Finset.filter_false_of_mem (fun m hm => by
        have := Finset.mem_range.mp hm
        omega), Finset.sum_empty]
      positivity
    · have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
      have hpt : ∀ m ∈ (Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m),
          Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
            ≤ Real.exp (-(γ * s / 2)) := by
        intro m hm
        have hm2 : 2 * m < s := Nat.lt_of_not_le (Finset.mem_filter.mp hm).2
        have hm2R : 2 * (m : ℝ) < (s : ℝ) := by exact_mod_cast hm2
        have hsq1 : (1 : ℝ) ≤ Real.sqrt (1 + (m : ℝ)) :=
          Real.one_le_sqrt.mpr (le_add_of_nonneg_right (Nat.cast_nonneg m))
        calc Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
            ≤ Real.exp (-γ * ((s : ℝ) - m)) / 1 := by
              exact div_le_div_of_nonneg_left (Real.exp_pos _).le one_pos hsq1
          _ = Real.exp (-γ * ((s : ℝ) - m)) := by rw [div_one]
          _ ≤ Real.exp (-(γ * s / 2)) := by
              apply Real.exp_le_exp.mpr
              nlinarith
      calc ∑ m ∈ (Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m),
          Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
          ≤ ∑ _m ∈ (Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m),
            Real.exp (-(γ * s / 2)) := Finset.sum_le_sum hpt
        _ = (((Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m)).card : ℝ)
            * Real.exp (-(γ * s / 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (1 + (s : ℝ)) * Real.exp (-(γ * s / 2)) := by
            apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            have hc : ((Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m)).card ≤ s + 1 :=
              le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])
            calc (((Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m)).card : ℝ)
                ≤ ((s + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hc
              _ = 1 + (s : ℝ) := by push_cast; ring
        _ ≤ (64 / γ ^ 2) / Real.sqrt (1 + s) := by
            rw [le_div_iff₀ hs0]
            have hsle : Real.sqrt (1 + (s : ℝ)) ≤ 1 + (s : ℝ) := by
              have h := Real.sqrt_le_sqrt (show (1:ℝ) + s ≤ (1 + s) ^ 2 by nlinarith)
              rwa [Real.sqrt_sq h1s.le] at h
            have hexp : Real.exp (-(γ * s / 2)) ≤ 4 / (γ * s / 2) ^ 2 :=
              exp_neg_le_four_div_sq (by positivity)
            calc (1 + (s : ℝ)) * Real.exp (-(γ * s / 2)) * Real.sqrt (1 + s)
                ≤ (1 + (s : ℝ)) * Real.exp (-(γ * s / 2)) * (1 + (s : ℝ)) := by
                  apply mul_le_mul_of_nonneg_left hsle (by positivity)
              _ = (1 + (s : ℝ)) ^ 2 * Real.exp (-(γ * s / 2)) := by ring
              _ ≤ (2 * (s : ℝ)) ^ 2 * (4 / (γ * s / 2) ^ 2) := by
                  apply mul_le_mul (by nlinarith) hexp (Real.exp_pos _).le (by positivity)
              _ = 64 / γ ^ 2 := by
                  field_simp
                  ring
  calc ∑ m ∈ (Finset.range (s + 1)).filter (fun m => s ≤ 2 * m),
        Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
      + ∑ m ∈ (Finset.range (s + 1)).filter (fun m => ¬ s ≤ 2 * m),
        Real.exp (-γ * ((s : ℝ) - m)) / Real.sqrt (1 + m)
      ≤ (2 * (1 + 1 / γ)) / Real.sqrt (1 + s) + (64 / γ ^ 2) / Real.sqrt (1 + s) :=
        add_le_add hhigh hlow
    _ = (2 * (1 + 1 / γ) + 64 / γ ^ 2) / Real.sqrt (1 + s) := (add_div _ _ _).symm

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
  obtain ⟨c6, hc6, C6, hC6, hU⟩ := renewalMass_bound
  obtain ⟨γ, hγ, C7, hC7, hstep⟩ := hold_step_bound
  set c9 : ℝ := min (c6 / 2) (γ / 4) with hc9def
  have hc9 : 0 < c9 := lt_min (by positivity) (by positivity)
  have hc9γ : c9 ≤ γ / 4 := min_le_right _ _
  obtain ⟨K, hK, hKs⟩ := sum_sqrt_exp_le (γ := γ / 2) (by positivity)
  set cF : ℝ := min (c9 / 2) γ with hcFdef
  have hcF : 0 < cF := lt_min (by positivity) hγ
  set D : ℝ := C6 * C7 * Real.exp (16 * γ) * (4 + 8 / γ) * (2 * Real.exp (4 * c9))
    with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  refine ⟨cF, hcF, D * K, by positivity, fun s j l => ?_⟩
  have h1s : (0 : ℝ) < 1 + (s : ℝ) := by positivity
  have hsq : 0 < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr h1s
  set X : ℝ := (j : ℝ) - s / 4 with hXdef
  have hGF : 0 ≤ Gweight (1 + (s : ℝ)) (cF * X) := Gweight_nonneg _ _
  by_cases hls : l ≤ (s : ℤ)
  · -- below the budget line the first passage carries no mass
    have h0 : fpDist s (j, l) = 0 := by
      by_contra h
      exact absurd (fpDist_support_snd_gt s (j, l) (by rwa [PMF.mem_support_iff]))
        (not_lt.mpr hls)
    rw [h0, ENNReal.toReal_zero]
    positivity
  push_neg at hls
  have hlsR : (s : ℝ) ≤ (l : ℝ) := by exact_mod_cast hls.le
  -- ── Step 1: finite-sum reduction of the renewal convolution (in ℝ≥0∞) ──
  set F : Finset (ℕ × ℤ) := (Finset.range (j + 1)) ×ˢ (Finset.Icc (0 : ℤ) (s : ℤ))
    with hF
  have hinner : ∀ p : ℕ × ℤ,
      (∑' d : ℕ × ℤ, if (j, l) = p + d then hold d else 0)
        = if p.1 ≤ j then hold (j - p.1, l - p.2) else 0 := by
    intro p
    by_cases hp : p.1 ≤ j
    · rw [if_pos hp, tsum_eq_single ((j - p.1, l - p.2) : ℕ × ℤ) ?_, if_pos ?_]
      · apply Prod.ext
        · show j = p.1 + (j - p.1)
          omega
        · show l = p.2 + (l - p.2)
          ring
      · intro d hd
        rw [if_neg]
        intro he
        apply hd
        have h1 : j = p.1 + d.1 := congrArg Prod.fst he
        have h2 : l = p.2 + d.2 := congrArg Prod.snd he
        obtain ⟨d1, d2⟩ := d
        apply Prod.ext
        · show d1 = j - p.1
          simp only at h1
          omega
        · show d2 = l - p.2
          simp only at h2
          omega
    · rw [if_neg hp]
      refine ENNReal.tsum_eq_zero.mpr fun d => ?_
      rw [if_neg]
      intro he
      apply hp
      have h1 : j = p.1 + d.1 := congrArg Prod.fst he
      omega
  have hred : (∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMass p else 0)
        * ∑' d : ℕ × ℤ, (if (j, l) = p + d then hold d else 0))
      = ∑ p ∈ F, renewalMass p * hold (j - p.1, l - p.2) := by
    rw [tsum_congr fun p => by rw [hinner p]]
    rw [tsum_eq_sum (s := F) ?_]
    · refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have h1 : p.1 ≤ j := by
        have := Finset.mem_range.mp hp1
        omega
      have h2 := (Finset.mem_Icc.mp hp2).2
      rw [if_pos h2, if_pos h1]
    · intro p hp
      by_cases h1 : p.1 ≤ j
      · by_cases h2 : p.2 ≤ (s : ℤ)
        · have h3 : p.2 < 0 := by
            by_contra h3
            push_neg at h3
            exact hp (Finset.mem_product.mpr
              ⟨Finset.mem_range.mpr (by omega), Finset.mem_Icc.mpr ⟨h3, h2⟩⟩)
          rw [renewalMass_zero_of_snd_neg h3, ite_self, zero_mul]
        · rw [if_neg h2, zero_mul]
      · rw [if_neg h1, mul_zero]
  have hfp : fpDist s (j, l) ≤ ∑ p ∈ F, renewalMass p * hold (j - p.1, l - p.2) :=
    hred ▸ fpDist_le_renewal_conv s (j, l)
  -- ── Step 2: pass to real numbers ──
  have hterm_ne : ∀ p ∈ F, renewalMass p * hold (j - p.1, l - p.2) ≠ ⊤ := fun p _ =>
    ENNReal.mul_ne_top (renewalMass_ne_top p) (PMF.apply_ne_top _ _)
  have hsum_ne : (∑ p ∈ F, renewalMass p * hold (j - p.1, l - p.2)) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun p hp => (hterm_ne p hp).lt_top).ne
  have hreal : (fpDist s (j, l)).toReal
      ≤ ∑ p ∈ F, (renewalMass p).toReal * (hold (j - p.1, l - p.2)).toReal := by
    calc (fpDist s (j, l)).toReal
        ≤ (∑ p ∈ F, renewalMass p * hold (j - p.1, l - p.2)).toReal :=
          ENNReal.toReal_mono hsum_ne hfp
      _ = ∑ p ∈ F, (renewalMass p).toReal * (hold (j - p.1, l - p.2)).toReal := by
          rw [ENNReal.toReal_sum hterm_ne]
          exact Finset.sum_congr rfl fun p _ => ENNReal.toReal_mul
  refine hreal.trans ?_
  -- ── Step 3: ℕ-indexed double sum ──
  have hIcc : Finset.Icc (0 : ℤ) (s : ℤ) = (Finset.range (s + 1)).image
      (fun m : ℕ => (m : ℤ)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, hs'⟩
      exact ⟨x.toNat, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩
      omega
  have hsplit : ∑ p ∈ F, (renewalMass p).toReal * (hold (j - p.1, l - p.2)).toReal
      = ∑ j₁ ∈ Finset.range (j + 1), ∑ m ∈ Finset.range (s + 1),
          (renewalMass (j₁, (m : ℤ))).toReal * (hold (j - j₁, l - m)).toReal := by
    rw [hF, Finset.sum_product]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [hIcc, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]
  rw [hsplit]
  -- ── Step 4: per-(j₁, m) envelope, then j₁-convolution, shift, m-sum ──
  set G2 : ℝ := Gweight (1 + (s : ℝ)) (c9 / 2 * X) with hG2def
  have hG2 : 0 ≤ G2 := Gweight_nonneg _ _
  have hmsum : ∀ m ∈ Finset.range (s + 1),
      ∑ j₁ ∈ Finset.range (j + 1),
        (renewalMass (j₁, (m : ℤ))).toReal * (hold (j - j₁, l - m)).toReal
      ≤ D * Real.exp (-γ * ((l : ℝ) - s)) * G2
          * (Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m)) := by
    intro m hm
    have hms : m ≤ s := by
      have := Finset.mem_range.mp hm
      omega
    have hmsR : (m : ℝ) ≤ (s : ℝ) := by exact_mod_cast hms
    have h1m : (0 : ℝ) < 1 + (m : ℝ) := by positivity
    have h1ms : 1 + (m : ℝ) ≤ 1 + (s : ℝ) := by linarith
    -- per-term envelope
    have hterm : ∀ j₁ ∈ Finset.range (j + 1),
        (renewalMass (j₁, (m : ℤ))).toReal * (hold (j - j₁, l - m)).toReal
        ≤ (C7 * Real.exp (16 * γ) * Real.exp (-γ * ((l : ℝ) - m)))
            * (C6 / Real.sqrt (1 + m))
            * (Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - (m : ℝ) / 4))
              * Real.exp (-γ * |((((j : ℤ) - 4) : ℤ) : ℝ) - (j₁ : ℝ)|)) := by
      intro j₁ hj₁
      have hj₁j : j₁ ≤ j := by
        have := Finset.mem_range.mp hj₁
        omega
      have hUb := hU j₁ (m : ℤ) (Int.natCast_nonneg m)
      simp only [Int.cast_natCast] at hUb
      have hsb := hstep (j - j₁, l - m)
      have hc1 : (((j - j₁ : ℕ) : ℝ)) = (j : ℝ) - j₁ := by
        rw [Nat.cast_sub hj₁j]
      have hc2 : (((l - m : ℤ) : ℝ)) = (l : ℝ) - m := by push_cast; ring
      dsimp only at hsb
      rw [hc1, hc2] at hsb
      have habs1 : |(j : ℝ) - j₁ - 4| = |((((j : ℤ) - 4) : ℤ) : ℝ) - (j₁ : ℝ)| := by
        congr 1
        push_cast
        ring
      have hexp2 : Real.exp (-γ * |(l : ℝ) - m - 16|)
          ≤ Real.exp (16 * γ) * Real.exp (-γ * ((l : ℝ) - m)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have := le_abs_self ((l : ℝ) - m - 16)
        nlinarith
      have hhold : (hold (j - j₁, l - m)).toReal
          ≤ C7 * Real.exp (-γ * |((((j : ℤ) - 4) : ℤ) : ℝ) - (j₁ : ℝ)|)
            * (Real.exp (16 * γ) * Real.exp (-γ * ((l : ℝ) - m))) := by
        rw [← habs1]
        calc (hold (j - j₁, l - m)).toReal
            ≤ C7 * Real.exp (-γ * |(j : ℝ) - j₁ - 4|)
              * Real.exp (-γ * |(l : ℝ) - m - 16|) := hsb
          _ ≤ C7 * Real.exp (-γ * |(j : ℝ) - j₁ - 4|)
              * (Real.exp (16 * γ) * Real.exp (-γ * ((l : ℝ) - m))) := by
              apply mul_le_mul_of_nonneg_left hexp2 (by positivity)
      calc (renewalMass (j₁, (m : ℤ))).toReal * (hold (j - j₁, l - m)).toReal
          ≤ (C6 / Real.sqrt (1 + (m : ℝ))
              * Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - (m : ℝ) / 4)))
            * (C7 * Real.exp (-γ * |((((j : ℤ) - 4) : ℤ) : ℝ) - (j₁ : ℝ)|)
              * (Real.exp (16 * γ) * Real.exp (-γ * ((l : ℝ) - m)))) := by
            apply mul_le_mul hUb hhold ENNReal.toReal_nonneg
              (mul_nonneg (by positivity) (Gweight_nonneg _ _))
        _ = (C7 * Real.exp (16 * γ) * Real.exp (-γ * ((l : ℝ) - m)))
            * (C6 / Real.sqrt (1 + m))
            * (Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - (m : ℝ) / 4))
              * Real.exp (-γ * |((((j : ℤ) - 4) : ℤ) : ℝ) - (j₁ : ℝ)|)) := by
            ring
    -- j₁-convolution
    have hconv := conv_Gweight_exp (t := 1 + (m : ℝ)) (c := c6) (γ := γ)
      h1m hc6 hγ ((m : ℝ) / 4) ((j : ℤ) - 4) (j + 1) (by omega)
    -- shift to the (j - s/4) centre at time scale 1+s
    have hshift : Gweight (1 + (m : ℝ)) (c9 * ((((j : ℤ) - 4 : ℤ) : ℝ) - (m : ℝ) / 4))
        ≤ 2 * Real.exp (4 * c9) * Real.exp ((c9 / 4) * ((s : ℝ) - m)) * G2 := by
      have harg : (((j : ℤ) - 4 : ℤ) : ℝ) - (m : ℝ) / 4
          = X + (((s : ℝ) - m) / 4 - 4) := by
        rw [hXdef]
        push_cast
        ring
      rw [harg, hG2def]
      refine (Gweight_shift h1m h1ms hc9 X (((s : ℝ) - m) / 4 - 4)).trans ?_
      have hδ : |((s : ℝ) - m) / 4 - 4| ≤ ((s : ℝ) - m) / 4 + 4 := by
        rw [abs_le]
        constructor <;> nlinarith
      have hE : Real.exp (c9 * |((s : ℝ) - m) / 4 - 4|)
          ≤ Real.exp (4 * c9) * Real.exp ((c9 / 4) * ((s : ℝ) - m)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [hc9.le]
      calc 2 * Real.exp (c9 * |((s : ℝ) - m) / 4 - 4|)
            * Gweight (1 + (s : ℝ)) (c9 / 2 * X)
          ≤ 2 * (Real.exp (4 * c9) * Real.exp ((c9 / 4) * ((s : ℝ) - m)))
            * Gweight (1 + (s : ℝ)) (c9 / 2 * X) := by
            apply mul_le_mul_of_nonneg_right ?_ (Gweight_nonneg _ _)
            apply mul_le_mul_of_nonneg_left hE (by norm_num)
        _ = 2 * Real.exp (4 * c9) * Real.exp ((c9 / 4) * ((s : ℝ) - m))
            * Gweight (1 + (s : ℝ)) (c9 / 2 * X) := by ring
    -- exponent bookkeeping: e^{-γ(l-m)}·e^{(c9/4)(s-m)} ≤ e^{-γ(l-s)}·e^{-(γ/2)(s-m)}
    have hexps : Real.exp (-γ * ((l : ℝ) - m)) * Real.exp ((c9 / 4) * ((s : ℝ) - m))
        ≤ Real.exp (-γ * ((l : ℝ) - s)) * Real.exp (-(γ / 2) * ((s : ℝ) - m)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hc9γ (by linarith : (0:ℝ) ≤ (s : ℝ) - m)]
    calc ∑ j₁ ∈ Finset.range (j + 1),
        (renewalMass (j₁, (m : ℤ))).toReal * (hold (j - j₁, l - m)).toReal
        ≤ ∑ j₁ ∈ Finset.range (j + 1),
          (C7 * Real.exp (16 * γ) * Real.exp (-γ * ((l : ℝ) - m)))
            * (C6 / Real.sqrt (1 + m))
            * (Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - (m : ℝ) / 4))
              * Real.exp (-γ * |((((j : ℤ) - 4) : ℤ) : ℝ) - (j₁ : ℝ)|)) :=
          Finset.sum_le_sum hterm
      _ = (C7 * Real.exp (16 * γ) * Real.exp (-γ * ((l : ℝ) - m)))
          * (C6 / Real.sqrt (1 + m))
          * ∑ j₁ ∈ Finset.range (j + 1),
            Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - (m : ℝ) / 4))
              * Real.exp (-γ * |((((j : ℤ) - 4) : ℤ) : ℝ) - (j₁ : ℝ)|) := by
          rw [Finset.mul_sum]
      _ ≤ (C7 * Real.exp (16 * γ) * Real.exp (-γ * ((l : ℝ) - m)))
          * (C6 / Real.sqrt (1 + m))
          * ((4 + 8 / γ)
            * (2 * Real.exp (4 * c9) * Real.exp ((c9 / 4) * ((s : ℝ) - m)) * G2)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine hconv.trans ?_
          exact mul_le_mul_of_nonneg_left hshift (by positivity)
      _ = (D * G2) * (Real.exp (-γ * ((l : ℝ) - m))
            * Real.exp ((c9 / 4) * ((s : ℝ) - m)))
          * (1 / Real.sqrt (1 + m)) := by
          rw [hDdef]
          ring
      _ ≤ (D * G2) * (Real.exp (-γ * ((l : ℝ) - s))
            * Real.exp (-(γ / 2) * ((s : ℝ) - m)))
          * (1 / Real.sqrt (1 + m)) := by
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          apply mul_le_mul_of_nonneg_left hexps (by positivity)
      _ = D * Real.exp (-γ * ((l : ℝ) - s)) * G2
          * (Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m)) := by
          ring
  -- ── Step 5: the m-sum and the final constant/decay relaxations ──
  calc ∑ j₁ ∈ Finset.range (j + 1), ∑ m ∈ Finset.range (s + 1),
        (renewalMass (j₁, (m : ℤ))).toReal * (hold (j - j₁, l - m)).toReal
      = ∑ m ∈ Finset.range (s + 1), ∑ j₁ ∈ Finset.range (j + 1),
        (renewalMass (j₁, (m : ℤ))).toReal * (hold (j - j₁, l - m)).toReal :=
        Finset.sum_comm
    _ ≤ ∑ m ∈ Finset.range (s + 1),
        D * Real.exp (-γ * ((l : ℝ) - s)) * G2
          * (Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m)) :=
        Finset.sum_le_sum hmsum
    _ = D * Real.exp (-γ * ((l : ℝ) - s)) * G2
        * ∑ m ∈ Finset.range (s + 1),
          Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m) := by
        rw [Finset.mul_sum]
    _ ≤ D * Real.exp (-γ * ((l : ℝ) - s)) * G2 * (K / Real.sqrt (1 + s)) := by
        apply mul_le_mul_of_nonneg_left (hKs s) (by positivity)
    _ ≤ D * K * (Real.exp (-cF * ((l : ℝ) - s)) / Real.sqrt (1 + s))
        * Gweight (1 + (s : ℝ)) (cF * X) := by
        have hexpF : Real.exp (-γ * ((l : ℝ) - s)) ≤ Real.exp (-cF * ((l : ℝ) - s)) := by
          apply Real.exp_le_exp.mpr
          have hcFγ : cF ≤ γ := min_le_right _ _
          have h := mul_le_mul_of_nonneg_right hcFγ (sub_nonneg.mpr hlsR)
          linarith only [h]
        have hGrel : G2 ≤ Gweight (1 + (s : ℝ)) (cF * X) := by
          rw [hG2def, ← Gweight_abs _ (c9 / 2 * X), ← Gweight_abs _ (cF * X),
            abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < c9 / 2),
            abs_of_pos hcF]
          apply Gweight_anti h1s (by positivity)
          have hcF9 : cF ≤ c9 / 2 := min_le_left _ _
          linarith only [mul_le_mul_of_nonneg_right hcF9 (abs_nonneg X)]
        calc D * Real.exp (-γ * ((l : ℝ) - s)) * G2 * (K / Real.sqrt (1 + s))
            ≤ D * Real.exp (-cF * ((l : ℝ) - s))
              * Gweight (1 + (s : ℝ)) (cF * X) * (K / Real.sqrt (1 + s)) := by
              apply mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc D * Real.exp (-γ * ((l : ℝ) - s)) * G2
                  ≤ D * Real.exp (-cF * ((l : ℝ) - s)) * G2 := by
                    apply mul_le_mul_of_nonneg_right ?_ hG2
                    exact mul_le_mul_of_nonneg_left hexpF hD.le
                _ ≤ D * Real.exp (-cF * ((l : ℝ) - s))
                    * Gweight (1 + (s : ℝ)) (cF * X) := by
                    apply mul_le_mul_of_nonneg_left hGrel (by positivity)
            _ = D * K * (Real.exp (-cF * ((l : ℝ) - s)) / Real.sqrt (1 + s))
                * Gweight (1 + (s : ℝ)) (cF * X) := by ring

/-- A support-shifted exponential over `ℤ` sums geometrically: the mass at or
below `s` vanishes and the positive tail is `∑_{k≥1} e^{-ck} = e^{-c}/(1-e^{-c})`.
Reusable building block for the white-exit Gaussian tails (`fpDist_col_le`). -/
theorem hasSum_int_shift_exp {c : ℝ} (hc : 0 < c) (s : ℕ) :
    HasSum (fun l : ℤ => if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0)
      (Real.exp (-c) / (1 - Real.exp (-c))) := by
  have he1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have he0 : (0 : ℝ) < Real.exp (-c) := Real.exp_pos _
  set f : ℤ → ℝ :=
    fun l => if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0 with hf
  have hgeom : HasSum (fun n : ℕ => Real.exp (-c) * Real.exp (-c) ^ n)
      (Real.exp (-c) / (1 - Real.exp (-c))) := by
    have h := (hasSum_geometric_of_lt_one he0.le he1).mul_left (Real.exp (-c))
    rwa [← div_eq_mul_inv] at h
  have hneg : HasSum (fun n : ℕ => f (-(↑n + 1))) 0 := by
    have h0 : (fun n : ℕ => f (-(↑n + 1))) = fun _ => (0 : ℝ) := by
      funext n; rw [hf]; dsimp only; rw [if_neg (by push_cast; omega)]
    rw [h0]; exact hasSum_zero
  have hnat : HasSum (fun n : ℕ => f (n : ℤ)) (Real.exp (-c) / (1 - Real.exp (-c))) := by
    have h2 : HasSum (fun n : ℕ => f (((n + (s + 1) : ℕ)) : ℤ))
        (Real.exp (-c) / (1 - Real.exp (-c))) := by
      have he : (fun n : ℕ => f (((n + (s + 1) : ℕ)) : ℤ))
          = fun n : ℕ => Real.exp (-c) * Real.exp (-c) ^ n := by
        funext n; rw [hf]; dsimp only
        rw [if_pos (by push_cast; omega), ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1; push_cast; ring
      rw [he]; exact hgeom
    have hfront : ∑ i ∈ Finset.range (s + 1), f (i : ℤ) = 0 := by
      apply Finset.sum_eq_zero; intro i hi; rw [hf]; dsimp only
      rw [if_neg (by have := Finset.mem_range.mp hi; push_cast; omega)]
    rw [← hasSum_nat_add_iff' (s + 1)]
    simpa [hfront] using h2
  simpa using hnat.of_nat_of_neg_add_one hneg

/-- **First-passage column marginal** (the `l`-collapse of Lemma 7.7): summing the
`fpDist_location_bound` (X6) Gaussian envelope over the height coordinate `l`
(mass lives only on `l > s`, so the `e^{-c(l-s)}` factor collapses geometrically)
gives a per-column bound `≤ C'·Gweight(1+s, c(j-s/4))/√(1+s)`. This is the shared
prerequisite of both white-exit tails: `fpDist_out_of_strip_le` sums it over the
columns `j > m`, and the separation argument reads column-wise Gaussian decay. -/
theorem fpDist_col_le :
    ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ (s j : ℕ),
      ∑' l : ℤ, (fpDist s (j, l)).toReal
        ≤ C' * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4))
                  / Real.sqrt (1 + (s : ℝ))) := by
  obtain ⟨c, hc, C, hC, hbound⟩ := fpDist_location_bound
  have he1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have he0 : (0 : ℝ) < Real.exp (-c) := Real.exp_pos _
  have hpos : (0 : ℝ) < 1 - Real.exp (-c) := by linarith
  refine ⟨c, hc, C * (Real.exp (-c) / (1 - Real.exp (-c))),
    mul_pos hC (div_pos he0 hpos), ?_⟩
  intro s j
  set G : ℝ := Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4)) with hG
  have hGnn : 0 ≤ G := Gweight_nonneg _ _
  have hsq : (0 : ℝ) < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  set A : ℝ := C * G / Real.sqrt (1 + (s : ℝ)) with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hdom : HasSum
      (fun l : ℤ => A * (if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0))
      (A * (Real.exp (-c) / (1 - Real.exp (-c)))) := (hasSum_int_shift_exp hc s).mul_left A
  have hptw : ∀ l : ℤ, (fpDist s (j, l)).toReal
      ≤ A * (if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0) := by
    intro l
    by_cases hl : (s : ℤ) < l
    · rw [if_pos hl, hA, hG]
      calc (fpDist s (j, l)).toReal
          ≤ C * (Real.exp (-c * ((l : ℝ) - (s : ℝ))) / Real.sqrt (1 + (s : ℝ)))
              * Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4)) := hbound s j l
        _ = C * Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt (1 + (s : ℝ))
              * Real.exp (-c * ((l : ℝ) - (s : ℝ))) := by ring
    · rw [if_neg hl, mul_zero]
      have h0 : fpDist s (j, l) = 0 := by
        by_contra h
        exact hl (fpDist_support_snd_gt s (j, l) (by rwa [PMF.mem_support_iff]))
      rw [h0, ENNReal.toReal_zero]
  have hslice : Summable (fun l : ℤ => (fpDist s (j, l)).toReal) := by
    have h2d : Summable (fun p : ℕ × ℤ => (fpDist s p).toReal) :=
      ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
    exact h2d.comp_injective (fun a b h => by simpa using h)
  calc ∑' l : ℤ, (fpDist s (j, l)).toReal
      ≤ ∑' l : ℤ, A * (if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0) :=
        hslice.tsum_le_tsum hptw hdom.summable
    _ = A * (Real.exp (-c) / (1 - Real.exp (-c))) := hdom.tsum_eq
    _ = C * (Real.exp (-c) / (1 - Real.exp (-c))) * (G / Real.sqrt (1 + (s : ℝ))) := by
        rw [hA]; ring

end TaoCollatz
