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

/-- **The renewal Gaussian bound** (paper p.44, first display of the Lemma 7.7
proof): `∑_k P(v_{[1,k-1]} = (j', s')) ≪ (1+s')^{-1/2}·G_{1+s'}(c(j'-s'/4))`.

OPEN (X6, step 2): insert `hold_local_bound` (Lemma 2.2(i), PROVED) per `k` and
sum, splitting into the regions `16(k-1) ∈ [s'/2, 2s']` (≍ √s' terms, each
`≪ 1/s'` with the Gaussian in `j' - s'/4` surviving), `16(k-1) < s'/2` and
`> 2s'` (the height offset `|s' - 16(k-1)| ≳ s'` makes `G_k` exponentially
small). Numeric envelope to be validated in python before formalizing. -/
theorem renewalMass_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (j : ℕ) (l : ℤ), 0 ≤ l →
      (renewalMass (j, l)).toReal
        ≤ C / Real.sqrt (1 + (l : ℝ))
            * Gweight (1 + (l : ℝ)) (c * ((j : ℝ) - (l : ℝ) / 4)) := by
  sorry

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
