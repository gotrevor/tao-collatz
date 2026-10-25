/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.HoldLocal

/-!
# Renewal algebra for the `Pascal(p)` first-passage walk

This is the probability-law-dependent front of Tao's Lemma 7.7.  It lifts the
renewal measure and the first-passage convolution from the fixed `hold` law to
`holdP p`.  The algebra is otherwise unchanged; the sole law-specific input is
that every supported holding increment has positive height.
-/

open scoped ENNReal

namespace TaoCollatz.Sec7P

section

variable (tilt : ℝ) (htilt0 : 0 < tilt) (htilt1 : tilt < 1)

local notation "holdLaw" => holdP tilt htilt0 htilt1
local notation "fpLaw" => fpDistP tilt htilt0 htilt1
/-- The renewal measure of the `Hold` walk: expected visits to `p` (equally,
the probability of ever visiting `p`, the events being `k`-disjoint since the
height strictly increases). Paper `∑_k P(v_{[1,k]} = p)`, p.44. -/
noncomputable def renewalMassP (p : ℕ × ℤ) : ℝ≥0∞ :=
  ∑' k : ℕ, iidSum holdLaw k p

/-- The `≥ 1`-step part of the renewal measure. -/
noncomputable def stepMassP (p : ℕ × ℤ) : ℝ≥0∞ :=
  ∑' k : ℕ, iidSum holdLaw (k + 1) p

local notation "renewalMassLaw" => renewalMassP tilt htilt0 htilt1
local notation "stepMassLaw" => stepMassP tilt htilt0 htilt1

/-- Peel the `k = 0` layer: `renewalMassLaw = δ₀ + stepMassLaw`. -/
theorem renewalMassP_eq (p : ℕ × ℤ) :
    renewalMassLaw p = PMF.pure (0 : ℕ × ℤ) p + stepMassLaw p := by
  rw [renewalMassP, tsum_eq_zero_add' ENNReal.summable, iidSum_zero, stepMassP]

/-- The origin carries full renewal mass at `k = 0`. -/
theorem one_le_renewalMassP_zero : 1 ≤ renewalMassLaw (0 : ℕ × ℤ) := by
  rw [renewalMassP_eq, PMF.pure_apply, if_pos rfl]
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
    iidSum holdLaw (k + 1) p
      = ∑' d : ℕ × ℤ, holdLaw d * ∑' q : ℕ × ℤ,
          (if p = d + q then iidSum holdLaw k q else 0) := by
  rw [iidSum_succ, PMF.bind_apply]
  exact tsum_congr fun d => by rw [map_apply_ite]

/-- The first-step decomposition of the renewal measure:
`stepMassLaw = holdLaw ⋆ renewalMassLaw`. -/
theorem stepMassP_eq_conv (p : ℕ × ℤ) :
    stepMassLaw p
      = ∑' d : ℕ × ℤ, holdLaw d * ∑' q : ℕ × ℤ,
          (if p = d + q then renewalMassLaw q else 0) := by
  rw [stepMassP]
  calc ∑' k : ℕ, iidSum holdLaw (k + 1) p
      = ∑' k : ℕ, ∑' d : ℕ × ℤ, holdLaw d * ∑' q : ℕ × ℤ,
          (if p = d + q then iidSum holdLaw k q else 0) :=
        tsum_congr fun k => iidSum_succ_apply tilt htilt0 htilt1 k p
    _ = ∑' d : ℕ × ℤ, ∑' k : ℕ, holdLaw d * ∑' q : ℕ × ℤ,
          (if p = d + q then iidSum holdLaw k q else 0) := ENNReal.tsum_comm
    _ = ∑' d : ℕ × ℤ, holdLaw d * ∑' k : ℕ, ∑' q : ℕ × ℤ,
          (if p = d + q then iidSum holdLaw k q else 0) :=
        tsum_congr fun _ => ENNReal.tsum_mul_left
    _ = ∑' d : ℕ × ℤ, holdLaw d * ∑' q : ℕ × ℤ, ∑' k : ℕ,
          (if p = d + q then iidSum holdLaw k q else 0) :=
        tsum_congr fun _ => congrArg _ ENNReal.tsum_comm
    _ = ∑' d : ℕ × ℤ, holdLaw d * ∑' q : ℕ × ℤ,
          (if p = d + q then renewalMassLaw q else 0) := by
        refine tsum_congr fun d => congrArg _ (tsum_congr fun q => ?_)
        by_cases h : p = d + q
        · simp only [if_pos h, renewalMassP]
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
renewal measure at the pre-passage point convolved with one `holdLaw` step over
the budget line. Upper bound only (all downstream uses are upper bounds; the
(7.50) lower bound comes from the complement, `fpLaw` being a `PMF`). -/
theorem fpDistP_le_renewal_conv : ∀ (s : ℕ) (e : ℕ × ℤ),
    fpLaw s e ≤ ∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMassLaw p else 0)
      * ∑' d : ℕ × ℤ, (if e = p + d then holdLaw d else 0) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro e
    -- split the RHS as the δ₀ layer (= holdLaw e) plus the ≥1-step layer
    have hRHS : ∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMassLaw p else 0)
          * ∑' d : ℕ × ℤ, (if e = p + d then holdLaw d else 0)
        = holdLaw e + ∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then stepMassLaw p else 0)
          * ∑' d : ℕ × ℤ, (if e = p + d then holdLaw d else 0) := by
      have hsplit : ∀ p : ℕ × ℤ,
          (if p.2 ≤ (s : ℤ) then renewalMassLaw p else 0)
              * ∑' d : ℕ × ℤ, (if e = p + d then holdLaw d else 0)
            = (if p.2 ≤ (s : ℤ) then PMF.pure (0 : ℕ × ℤ) p else 0)
                * ∑' d : ℕ × ℤ, (if e = p + d then holdLaw d else 0)
              + (if p.2 ≤ (s : ℤ) then stepMassLaw p else 0)
                * ∑' d : ℕ × ℤ, (if e = p + d then holdLaw d else 0) := by
        intro p
        by_cases hp : p.2 ≤ (s : ℤ)
        · rw [if_pos hp, if_pos hp, if_pos hp, renewalMassP_eq, add_mul]
        · rw [if_neg hp, if_neg hp, if_neg hp, zero_mul, add_zero]
      rw [tsum_congr hsplit, ENNReal.tsum_add]
      congr 1
      -- the δ₀ layer collapses to `holdLaw e`
      rw [tsum_eq_single (0 : ℕ × ℤ) (fun p hp => by
        rw [PMF.pure_apply, if_neg hp, ite_self, zero_mul])]
      have h00 : ((0 : ℕ × ℤ).2 : ℤ) ≤ (s : ℤ) := by simp
      rw [if_pos h00, PMF.pure_apply, if_pos rfl, one_mul,
        tsum_eq_single e (fun d hd => by
          rw [if_neg (by simpa [eq_comm] using hd)]), if_pos (by simp)]
    rw [hRHS, fpDistP, PMF.bind_apply]
    -- split each holdLaw-atom's dite into the overshoot and in-budget parts
    have hterm : ∀ d' : ℕ × ℤ,
        holdLaw d' * (if _h : d'.2 ≤ 0 ∨ (s : ℤ) < d'.2 then PMF.pure d'
            else (fpLaw (s - d'.2.toNat)).map
              fun e' => (d'.1 + e'.1, d'.2 + e'.2)) e
          = (if d'.2 ≤ 0 ∨ (s : ℤ) < d'.2 then holdLaw d' * PMF.pure d' e else 0)
            + (if d'.2 ≤ 0 ∨ (s : ℤ) < d'.2 then 0
              else holdLaw d' * ((fpLaw (s - d'.2.toNat)).map
                fun e' => (d'.1 + e'.1, d'.2 + e'.2)) e) := by
      intro d'
      by_cases hc : d'.2 ≤ 0 ∨ (s : ℤ) < d'.2
      · rw [dif_pos hc, if_pos hc, if_pos hc, add_zero]
      · rw [dif_neg hc, if_neg hc, if_neg hc, zero_add]
    rw [tsum_congr hterm, ENNReal.tsum_add]
    refine add_le_add ?_ ?_
    · -- overshoot layer ≤ holdLaw e
      calc ∑' d' : ℕ × ℤ,
          (if d'.2 ≤ 0 ∨ (s : ℤ) < d'.2 then holdLaw d' * PMF.pure d' e else 0)
          ≤ ∑' d' : ℕ × ℤ, (if e = d' then holdLaw d' else 0) := by
            refine ENNReal.tsum_le_tsum fun d' => ?_
            rw [PMF.pure_apply]
            by_cases hc : d'.2 ≤ 0 ∨ (s : ℤ) < d'.2
            · rw [if_pos hc]
              by_cases he : e = d'
              · rw [if_pos he, if_pos he, mul_one]
              · rw [if_neg he, if_neg he, mul_zero]
            · rw [if_neg hc]
              exact zero_le
        _ = holdLaw e := by
            rw [tsum_eq_single e (fun d' hd' => by
              rw [if_neg (by simpa [eq_comm] using hd')]), if_pos rfl]
    · -- in-budget layer: IH per atom, drop the guard, reindex p = d' + q
      have hIH : ∀ d' : ℕ × ℤ,
          (if d'.2 ≤ 0 ∨ (s : ℤ) < d'.2 then 0
            else holdLaw d' * ((fpLaw (s - d'.2.toNat)).map
              fun e' => (d'.1 + e'.1, d'.2 + e'.2)) e)
          ≤ ∑' q : ℕ × ℤ, (holdLaw d'
              * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMassLaw q else 0))
              * ∑' d : ℕ × ℤ, (if e = d' + q + d then holdLaw d else 0) := by
        intro d'
        by_cases hc : d'.2 ≤ 0 ∨ (s : ℤ) < d'.2
        · rw [if_pos hc]
          exact zero_le
        · rw [if_neg hc]
          push Not at hc
          obtain ⟨hd2pos, hd2le⟩ := hc
          set s' : ℕ := s - d'.2.toNat with hs'
          have hs'lt : s' < s := by omega
          have hcond : ∀ q : ℕ × ℤ,
              (d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2) ↔ q.2 ≤ (s' : ℤ) := by
            intro q
            constructor
            · rintro ⟨h, -⟩; omega
            · intro h; exact ⟨by omega, hd2pos⟩
          calc holdLaw d' * ((fpLaw s').map
                fun e' => (d'.1 + e'.1, d'.2 + e'.2)) e
              ≤ holdLaw d' * ∑' q : ℕ × ℤ,
                  (if q.2 ≤ (s' : ℤ) then renewalMassLaw q else 0)
                  * ∑' d : ℕ × ℤ, (if e = d' + q + d then holdLaw d else 0) := by
                refine mul_le_mul_right ?_ _
                rw [map_apply_ite]
                refine le_trans (le_of_eq (tsum_congr fun e' =>
                  if_congr Iff.rfl rfl rfl)) ?_
                calc ∑' e' : ℕ × ℤ, (if e = d' + e' then fpLaw s' e' else 0)
                    ≤ ∑' e' : ℕ × ℤ, (if e = d' + e' then
                        ∑' q : ℕ × ℤ, (if q.2 ≤ (s' : ℤ) then renewalMassLaw q else 0)
                          * ∑' d : ℕ × ℤ, (if e' = q + d then holdLaw d else 0)
                        else 0) := by
                      refine ENNReal.tsum_le_tsum fun e' => ?_
                      by_cases he' : e = d' + e'
                      · rw [if_pos he', if_pos he']
                        exact IH s' hs'lt e'
                      · rw [if_neg he', if_neg he']
                  _ = ∑' q : ℕ × ℤ, (if q.2 ≤ (s' : ℤ) then renewalMassLaw q else 0)
                        * ∑' d : ℕ × ℤ, (if e = d' + q + d then holdLaw d else 0) := by
                      have hpush : ∀ e' : ℕ × ℤ, (if e = d' + e' then
                            ∑' q : ℕ × ℤ, (if q.2 ≤ (s' : ℤ) then renewalMassLaw q else 0)
                              * ∑' d : ℕ × ℤ, (if e' = q + d then holdLaw d else 0)
                            else 0)
                          = ∑' q : ℕ × ℤ, (if q.2 ≤ (s' : ℤ) then renewalMassLaw q else 0)
                              * ∑' d : ℕ × ℤ, (if e = d' + e' then
                                  (if e' = q + d then holdLaw d else 0) else 0) := by
                        intro e'
                        by_cases hce : e = d' + e'
                        · simp only [if_pos hce]
                        · simp only [if_neg hce, tsum_zero, mul_zero]
                      rw [tsum_congr hpush, ENNReal.tsum_comm]
                      refine tsum_congr fun q => ?_
                      rw [ENNReal.tsum_mul_left, tsum_delta_chain e d' q holdLaw]
            _ = ∑' q : ℕ × ℤ, (holdLaw d'
                  * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMassLaw q else 0))
                  * ∑' d : ℕ × ℤ, (if e = d' + q + d then holdLaw d else 0) := by
                rw [← ENNReal.tsum_mul_left]
                refine tsum_congr fun q => ?_
                rw [if_congr (hcond q) rfl rfl, ← mul_assoc]
      refine le_trans (ENNReal.tsum_le_tsum hIH) (le_of_eq ?_)
      -- reindex against the landing point p = d' + q
      have hre := tsum_conv_reindex
        (fun d' q => holdLaw d'
          * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMassLaw q else 0))
        (fun p => ∑' d : ℕ × ℤ, (if e = p + d then holdLaw d else 0))
      have hshape : ∀ d' : ℕ × ℤ, ∑' q : ℕ × ℤ, (holdLaw d'
            * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMassLaw q else 0))
            * ∑' d : ℕ × ℤ, (if e = d' + q + d then holdLaw d else 0)
          = ∑' q : ℕ × ℤ, (holdLaw d'
            * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMassLaw q else 0))
            * ∑' d : ℕ × ℤ, (if e = (d' + q) + d then holdLaw d else 0) :=
        fun d' => rfl
      rw [tsum_congr hshape, hre]
      -- identify the inner double sum with the budget-restricted stepMassLaw
      refine tsum_congr fun p => ?_
      congr 1
      -- the `0 < d'.2` guard is absorbed: `holdLaw` vanishes at heights < 3
      have hinner : ∀ (d' q : ℕ × ℤ), (if p = d' + q then holdLaw d'
            * (if d'.2 + q.2 ≤ (s : ℤ) ∧ 0 < d'.2 then renewalMassLaw q else 0) else 0)
          = (if p.2 ≤ (s : ℤ) then
              (if p = d' + q then holdLaw d' * renewalMassLaw q else 0) else 0) := by
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
          · -- null step: `holdLaw d' = 0` kills both sides
            have h0 : holdLaw d' = 0 := holdP_zero_of_snd_lt tilt htilt0 htilt1 (by omega)
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
        rw [stepMassP_eq_conv]
        refine tsum_congr fun d' => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun q => by rw [mul_ite, mul_zero]
      · simp only [if_neg hps, tsum_zero]

/-- Convolving the unrestricted renewal measure with one final `holdLaw` step is
exactly the positive-time renewal measure.  This is the commuted form of
`stepMassP_eq_conv`; it is the convenient orientation for first passage, where
the pre-passage point is chosen before the final step. -/
theorem renewalMassP_conv_holdP_eq_stepMassP (e : ℕ × ℤ) :
    (∑' p : ℕ × ℤ, renewalMassLaw p *
      ∑' d : ℕ × ℤ, (if e = p + d then holdLaw d else 0)) = stepMassLaw e := by
  rw [stepMassP_eq_conv]
  calc
    (∑' p : ℕ × ℤ, renewalMassLaw p *
        ∑' d : ℕ × ℤ, (if e = p + d then holdLaw d else 0))
        = ∑' p : ℕ × ℤ, ∑' d : ℕ × ℤ,
            renewalMassLaw p * (if e = p + d then holdLaw d else 0) := by
              refine tsum_congr fun p => ?_
              rw [ENNReal.tsum_mul_left]
    _ = ∑' d : ℕ × ℤ, ∑' p : ℕ × ℤ,
          renewalMassLaw p * (if e = p + d then holdLaw d else 0) := ENNReal.tsum_comm
    _ = ∑' d : ℕ × ℤ, holdLaw d * ∑' p : ℕ × ℤ,
          (if e = d + p then renewalMassLaw p else 0) := by
            refine tsum_congr fun d => ?_
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun p => ?_
            by_cases h : e = p + d
            · rw [if_pos h, if_pos (by simpa [add_comm] using h), mul_comm]
            · simp only [if_neg h, if_neg (by simpa [add_comm] using h), mul_zero]

/-- A first-passage endpoint is in particular a positive-time renewal endpoint.
Dropping the restriction that the pre-passage point lies below the budget line
turns `fpDistP_le_renewal_conv` into `stepMassLaw`. -/
theorem fpDistP_le_stepMassP (s : ℕ) (e : ℕ × ℤ) : fpLaw s e ≤ stepMassLaw e := by
  refine (fpDistP_le_renewal_conv tilt htilt0 htilt1 s e).trans ?_
  rw [← renewalMassP_conv_holdP_eq_stepMassP tilt htilt0 htilt1 e]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases hp : p.2 ≤ (s : ℤ)
  · rw [if_pos hp]
  · rw [if_neg hp, zero_mul]
    exact bot_le

/-! ### Finite renewal sums and a variable-spacing summation tool

The fixed-law proof of Lemma 7.7 sums its local bound along the lattice
`16 * k`.  For `holdP`, the corresponding height drift is
`k / (p³(1-p))`, which is generally not integral.  The following results
separate the two issues needed by the tilted proof: the renewal sum still
truncates at `k ≤ l / 3`, and an antitone envelope can be summed along any
positive real arithmetic progression with the same factor-two loss as in the
integer-spacing argument.
-/

/-- Every tilted holding step raises the height by at least `3`, so `k` steps
cannot land at height below `3k`. -/
theorem iidSum_holdP_snd_zero : ∀ (k : ℕ) (q : ℕ × ℤ),
    q.2 < 3 * (k : ℤ) → TaoCollatz.iidSum holdLaw k q = 0 := by
  intro k
  induction k with
  | zero =>
    intro q hq
    rw [TaoCollatz.iidSum_zero, PMF.pure_apply, if_neg]
    intro h
    subst h
    simp at hq
  | succ k ih =>
    intro q hq
    rw [iidSum_succ_apply]
    refine ENNReal.tsum_eq_zero.mpr fun d => ?_
    by_cases hd : holdLaw d = 0
    · rw [hd, zero_mul]
    · have hd2 : 3 ≤ d.2 :=
        holdP_support_snd_ge tilt htilt0 htilt1 d (by rwa [PMF.mem_support_iff])
      have hz : (∑' q' : ℕ × ℤ,
          if q = d + q' then TaoCollatz.iidSum holdLaw k q' else 0) = 0 := by
        refine ENNReal.tsum_eq_zero.mpr fun q' => ?_
        by_cases he : q = d + q'
        · rw [if_pos he]
          refine ih q' ?_
          have hsnd : q.2 = d.2 + q'.2 := by rw [he]; rfl
          push_cast at hq ⊢
          omega
        · rw [if_neg he]
      rw [hz, mul_zero]

/-- The tilted renewal mass at nonnegative height `l` is a finite sum. -/
theorem renewalMassP_eq_sum (j : ℕ) (l : ℤ) :
    renewalMassLaw (j, l) =
      ∑ k ∈ Finset.range (l.toNat / 3 + 1), TaoCollatz.iidSum holdLaw k (j, l) := by
  rw [renewalMassP]
  refine tsum_eq_sum fun k hk => iidSum_holdP_snd_zero tilt htilt0 htilt1 k (j, l) ?_
  have hk' : l.toNat / 3 + 1 ≤ k :=
    Nat.le_of_not_lt fun h => hk (Finset.mem_range.mpr h)
  show l < 3 * (k : ℤ)
  omega

/-- Real-valued form of `renewalMassP_eq_sum`. -/
theorem renewalMassP_toReal_eq (j : ℕ) (l : ℤ) :
    (renewalMassLaw (j, l)).toReal =
      ∑ k ∈ Finset.range (l.toNat / 3 + 1),
        (TaoCollatz.iidSum holdLaw k (j, l)).toReal := by
  rw [renewalMassP_eq_sum, ENNReal.toReal_sum fun k _ => PMF.apply_ne_top _ _]

/-- The tilted renewal mass is finite. -/
theorem renewalMassP_ne_top (p : ℕ × ℤ) : renewalMassLaw p ≠ ⊤ := by
  obtain ⟨j, l⟩ := p
  rw [renewalMassP_eq_sum]
  exact (ENNReal.sum_lt_top.mpr fun k _ =>
    lt_of_le_of_lt (PMF.coe_le_one _ _) ENNReal.one_lt_top).ne

/-- Negative heights carry no tilted renewal mass. -/
theorem renewalMassP_zero_of_snd_neg {p : ℕ × ℤ} (hp : p.2 < 0) :
    renewalMassLaw p = 0 := by
  rw [renewalMassP]
  refine ENNReal.tsum_eq_zero.mpr fun k =>
    iidSum_holdP_snd_zero tilt htilt0 htilt1 k p ?_
  have : (0 : ℤ) ≤ 3 * (k : ℤ) := by positivity
  omega

/-- The height drift of one tilted holding increment stays in a fixed compact
interval on the campaign window.  The generous endpoints `10` and `200` are
chosen to make the subsequent renewal summation uniform and transparent. -/
theorem holdP_height_drift_mem_window {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    10 ≤ (pairThreeProb p)⁻¹ * (2 / p) ∧
      (pairThreeProb p)⁻¹ * (2 / p) ≤ 200 := by
  have hp : 0 < p := by linarith
  have hq := pairThreeProb_mem_window hp0 hp1
  have hqpos : 0 < pairThreeProb p := by linarith
  have hprodpos : 0 < pairThreeProb p * p := mul_pos hqpos hp
  have hform : (pairThreeProb p)⁻¹ * (2 / p) =
      2 / (pairThreeProb p * p) := by
    field_simp
  rw [hform]
  constructor
  · rw [le_div_iff₀ hprodpos]
    have hprod : pairThreeProb p * p ≤ (36 / 125 : ℝ) * (3 / 5) :=
      mul_le_mul hq.2 hp1 (by linarith) (by linarith)
    nlinarith
  · rw [div_le_iff₀ hprodpos]
    have hprod : (8 / 125 : ℝ) * (1 / 5) ≤ pairThreeProb p * p :=
      mul_le_mul hq.1 hp0 (by norm_num) (by linarith)
    nlinarith

/-- The exact p-dependent drift cancels in the transverse coordinate
`j - (p/2)l`.  This is the tilted replacement for the fixed-law identity
`(j-4k) - (l-16k)/4 = j-l/4`. -/
theorem holdP_transverse_drift_cancel {p : ℝ} (hp : p ≠ 0)
    (j l k : ℝ) :
    (j - (pairThreeProb p)⁻¹ * k) - p / 2 *
        (l - ((pairThreeProb p)⁻¹ * (2 / p)) * k) =
      j - p / 2 * l := by
  field_simp
  ring

/-- Uniform triangle inequality behind the tilted `Gweight` factorization.
The coefficient `7/10` is exactly the worst-case remainder `1-p/2` on the
campaign window. -/
theorem transverse_triangle_window {p u v : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) :
    |u - p / 2 * v| + 7 / 10 * |v| ≤ |u| + |v| := by
  have hpnonneg : 0 ≤ p := by linarith
  have htri : |u - p / 2 * v| ≤ |u| + |p / 2 * v| := abs_sub _ _
  have habs : |p / 2 * v| = p / 2 * |v| := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hpnonneg (by norm_num))]
  have hpv : p / 2 * |v| ≤ 3 / 10 * |v| := by
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg v)
  rw [habs] at htri
  linarith

/-- Uniform `Gweight` factorization for the tilted transverse slope.  On the
window, `p/2 ≤ 3/10`, so the height error retains at least `7/10` of its
coefficient after recentering.  The Gaussian height factor is weakened from
the fixed-law `c²/2` to `2c²/5`; this is the small but essential adjustment
at the top endpoint `p = 3/5`. -/
theorem Gweight_factorP {c1 t1 t2 x z y : ℝ} (hc1 : 0 < c1)
    (ht1 : 0 < t1) (ht : t1 ≤ t2) (hz : 0 ≤ z)
    (hy : |x| + 7 / 10 * z ≤ y) :
    TaoCollatz.Gweight t1 (c1 * y) ≤
      TaoCollatz.Gweight t2 (c1 / 2 * x) *
        (Real.exp (-(2 * c1 ^ 2 / 5) * z ^ 2 / t1) +
          Real.exp (-(c1 / 2) * z)) := by
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hy0 : 0 ≤ y := by linarith
  have ht2 : 0 < t2 := lt_of_lt_of_le ht1 ht
  set A := Real.exp (-(c1 / 2 * x) ^ 2 / t2) with hA
  set B := Real.exp (-(2 * c1 ^ 2 / 5) * z ^ 2 / t1) with hB
  set C := Real.exp (-|c1 / 2 * x|) with hC
  set D := Real.exp (-(c1 / 2) * z) with hD
  have hquad : Real.exp (-(c1 * y) ^ 2 / t1) ≤ A * B := by
    rw [hA, hB, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [div_add_div _ _ ht2.ne' ht1.ne', div_le_div_iff₀ ht1 (by positivity)]
    have hy2 : x ^ 2 + 2 / 5 * z ^ 2 ≤ y ^ 2 := by
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
      abs_of_pos (by positivity : (0 : ℝ) < c1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hy hc1.le,
      mul_nonneg hc1.le hx0, mul_nonneg hc1.le hz]
  have hABCD : A * B + C * D ≤ (A + C) * (B + D) := by
    nlinarith [mul_nonneg (Real.exp_pos (-(c1 / 2 * x) ^ 2 / t2)).le
        (Real.exp_pos (-(c1 / 2) * z)).le,
      mul_nonneg (Real.exp_pos (-|c1 / 2 * x|)).le
        (Real.exp_pos (-(2 * c1 ^ 2 / 5) * z ^ 2 / t1)).le]
  calc
    TaoCollatz.Gweight t1 (c1 * y) =
        Real.exp (-(c1 * y) ^ 2 / t1) + Real.exp (-|c1 * y|) := rfl
    _ ≤ A * B + C * D := add_le_add hquad hlin
    _ ≤ (A + C) * (B + D) := hABCD
    _ = TaoCollatz.Gweight t2 (c1 / 2 * x) * (B + D) := rfl

/-- **Real arithmetic-progression sum against an antitone envelope.**
The offsets `|w - d*k|`, for positive real spacing `d`, lie on two monotone
rays about `⌊w/d⌋`.  Each ray is bounded by the progression `d*m`, so the
whole sum costs at most twice the on-progression sum.  This is the
variable-drift replacement for `TaoCollatz.sum_abs_AP_le`. -/
theorem sum_abs_real_AP_le {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u)
    (hanti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v → f v ≤ f u)
    {d : ℝ} (hd : 0 < d) (w N : ℕ) (hw : (w : ℝ) < d * N) :
    ∑ k ∈ Finset.range N, f |(w : ℝ) - d * k|
      ≤ 2 * ∑ m ∈ Finset.range N, f (d * m) := by
  set q : ℕ := ⌊(w : ℝ) / d⌋₊ with hq
  have hdiv0 : 0 ≤ (w : ℝ) / d := by positivity
  have hqle : (q : ℝ) ≤ (w : ℝ) / d := by
    rw [hq]
    exact Nat.floor_le hdiv0
  have hqlt : (w : ℝ) / d < q + 1 := by
    rw [hq]
    exact Nat.lt_floor_add_one _
  have hdq : d * q ≤ (w : ℝ) := by
    have := (le_div_iff₀ hd).mp hqle
    simpa [mul_comm] using this
  have hwdq : (w : ℝ) < d * (q + 1) := by
    have := (div_lt_iff₀ hd).mp hqlt
    simpa [mul_comm] using this
  have hqN : q < N := by
    have hwdiv : (w : ℝ) / d < N := by
      rw [div_lt_iff₀ hd]
      simpa [mul_comm] using hw
    exact_mod_cast lt_of_le_of_lt hqle hwdiv
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun k => k ≤ q)]
  have hA : ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q),
      f |(w : ℝ) - d * k| ≤ ∑ m ∈ Finset.range N, f (d * m) := by
    have hstep : ∀ k ∈ (Finset.range N).filter (fun k => k ≤ q),
        f |(w : ℝ) - d * k| ≤ f (d * (q - k : ℕ)) := by
      intro k hk
      have hkq : k ≤ q := (Finset.mem_filter.mp hk).2
      refine hanti (by positivity) ?_
      have hdk : d * k ≤ (w : ℝ) := by
        calc d * k ≤ d * q := by gcongr
          _ ≤ (w : ℝ) := hdq
      rw [abs_of_nonneg (sub_nonneg.mpr hdk), Nat.cast_sub hkq]
      calc
        d * ((q : ℝ) - k) = d * q - d * k := by ring
        _ ≤ (w : ℝ) - d * k := sub_le_sub_right hdq _
    have hinj : ∀ x ∈ (Finset.range N).filter (fun k => k ≤ q),
        ∀ y ∈ (Finset.range N).filter (fun k => k ≤ q),
          q - x = q - y → x = y := by
      intro x hx y hy hxy
      have hxq := (Finset.mem_filter.mp hx).2
      have hyq := (Finset.mem_filter.mp hy).2
      omega
    have key : ∑ m ∈ ((Finset.range N).filter (fun k => k ≤ q)).image
          (fun k => q - k), f (d * m)
        = ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q),
            f (d * (q - k : ℕ)) := Finset.sum_image hinj
    calc
      ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q), f |(w : ℝ) - d * k|
          ≤ ∑ k ∈ (Finset.range N).filter (fun k => k ≤ q),
              f (d * (q - k : ℕ)) := Finset.sum_le_sum hstep
      _ = ∑ m ∈ ((Finset.range N).filter (fun k => k ≤ q)).image
            (fun k => q - k), f (d * m) := key.symm
      _ ≤ ∑ m ∈ Finset.range N, f (d * m) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn _
        intro m hm
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
        exact Finset.mem_range.mpr (by omega)
  have hB : ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
      f |(w : ℝ) - d * k| ≤ ∑ m ∈ Finset.range N, f (d * m) := by
    have hstep : ∀ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
        f |(w : ℝ) - d * k| ≤ f (d * (k - (q + 1) : ℕ)) := by
      intro k hk
      have hkq : q < k := Nat.lt_of_not_le (Finset.mem_filter.mp hk).2
      refine hanti (by positivity) ?_
      have hwk : (w : ℝ) ≤ d * k := by
        calc (w : ℝ) ≤ d * (q + 1) := hwdq.le
          _ ≤ d * k := by gcongr; exact_mod_cast Nat.succ_le_iff.mpr hkq
      rw [abs_of_nonpos (sub_nonpos.mpr hwk), Nat.cast_sub (by omega : q + 1 ≤ k)]
      have hwdq' : (w : ℝ) ≤ d * ((q + 1 : ℕ) : ℝ) := by
        simpa using hwdq.le
      calc
        d * ((k : ℝ) - ((q + 1 : ℕ) : ℝ)) =
            d * k - d * (q + 1 : ℕ) := by ring
        _ ≤ d * k - (w : ℝ) := sub_le_sub_left hwdq' _
        _ = -((w : ℝ) - d * k) := by ring
    have hinj : ∀ x ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
        ∀ y ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
          x - (q + 1) = y - (q + 1) → x = y := by
      intro x hx y hy hxy
      have hxq := Nat.lt_of_not_le (Finset.mem_filter.mp hx).2
      have hyq := Nat.lt_of_not_le (Finset.mem_filter.mp hy).2
      omega
    have key : ∑ m ∈ ((Finset.range N).filter (fun k => ¬ k ≤ q)).image
          (fun k => k - (q + 1)), f (d * m)
        = ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
            f (d * (k - (q + 1) : ℕ)) := Finset.sum_image hinj
    calc
      ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q), f |(w : ℝ) - d * k|
          ≤ ∑ k ∈ (Finset.range N).filter (fun k => ¬ k ≤ q),
              f (d * (k - (q + 1) : ℕ)) := Finset.sum_le_sum hstep
      _ = ∑ m ∈ ((Finset.range N).filter (fun k => ¬ k ≤ q)).image
            (fun k => k - (q + 1)), f (d * m) := key.symm
      _ ≤ ∑ m ∈ Finset.range N, f (d * m) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn _
        intro m hm
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
        have hkN := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
        exact Finset.mem_range.mpr (by omega)
  linarith

end

end TaoCollatz.Sec7P
