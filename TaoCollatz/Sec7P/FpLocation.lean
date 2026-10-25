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

/-! ### Uniform renewal summation along the tilted drift

The height drift of `holdP p` is not integral, but on the campaign window it
lies in `[10, 200]`.  The next estimate is the variable-spacing analogue of
`TaoCollatz.renewal_weight_sum_le_explicitC`.  The edge/central split is made
at `k = ⌊l/400⌋`: the upper drift bound then leaves a height discrepancy at
least `l/2` in the edge range, while the lower drift bound controls both
arithmetic-progression sums in the central range.
-/

/-- A uniform constant for `renewal_weight_sumP_le_explicitC`. -/
noncomputable def C_renewalWeightP (a b : ℝ) : ℝ :=
  32 / min (a / 8) (b / 2) ^ 2 + (3200 + 80 / b + 160 / Real.sqrt a)

theorem C_renewalWeightP_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < C_renewalWeightP a b := by
  unfold C_renewalWeightP
  have hε0 : 0 < min (a / 8) (b / 2) := lt_min (by positivity) (by positivity)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  positivity

/-- **Uniform tilted renewal `k`-sum envelope.**  For every real drift spacing
`d ∈ [10,200]`, the local-limit weights summed over the possible renewal
lengths cost only a constant (independent of `d`) times `(1+l)⁻¹ᐟ²`. -/
theorem renewal_weight_sumP_le_explicitC {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd0 : 10 ≤ d) (hd1 : d ≤ 200) :
    ∀ (l : ℤ), 0 ≤ l →
      ∑ k ∈ Finset.range (l.toNat / 3 + 1),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - d * k|))
        ≤ C_renewalWeightP a b / Real.sqrt (1 + (l : ℝ)) := by
  unfold C_renewalWeightP
  set ε : ℝ := min (a / 8) (b / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hd0
  intro l hl
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
  set T : ℕ := t / 400 with hT
  have hkl : ∀ k ∈ Finset.range N, (k : ℝ) ≤ (l : ℝ) := by
    intro k hk
    have hk' : k ≤ t := by
      have := Finset.mem_range.mp hk
      omega
    rw [← hcast]
    exact_mod_cast hk'
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun k => k < T)]
  have hterm_nonneg : ∀ k : ℕ, 0 ≤ 1 / (1 + (k : ℝ))
      * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
        + Real.exp (-b * |(l : ℝ) - d * k|)) := fun k => by positivity
  -- Edge range: `k < l/400`, so the worst drift `d = 200` still leaves `z ≥ l/2`.
  have hedge : ∑ k ∈ (Finset.range N).filter (fun k => k < T),
      1 / (1 + (k : ℝ))
        * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
          + Real.exp (-b * |(l : ℝ) - d * k|))
      ≤ (32 / ε ^ 2) / s := by
    by_cases hT0 : T = 0
    · rw [Finset.filter_false_of_mem (fun k _ => by omega), Finset.sum_empty]
      positivity
    · have ht400 : 400 ≤ t := by omega
      have hl1 : (1 : ℝ) ≤ (l : ℝ) := by
        rw [← hcast]
        exact_mod_cast le_trans (by norm_num) ht400
      have hbound : ∀ k ∈ (Finset.range N).filter (fun k => k < T),
          1 / (1 + (k : ℝ))
            * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-b * |(l : ℝ) - d * k|))
          ≤ 2 * Real.exp (-(ε * (l : ℝ))) := by
        intro k hk
        have hkT : k < T := (Finset.mem_filter.mp hk).2
        have hkN := (Finset.mem_filter.mp hk).1
        have h400k : 400 * k + 400 ≤ t := by
          have := Nat.div_mul_le_self t 400
          omega
        have h200k : 200 * (k : ℝ) ≤ (l : ℝ) / 2 := by
          have h : ((400 * k + 400 : ℕ) : ℝ) ≤ ((t : ℕ) : ℝ) :=
            Nat.cast_le.mpr h400k
          rw [hcast] at h
          push_cast at h
          nlinarith
        have hdk : d * (k : ℝ) ≤ (l : ℝ) / 2 := by
          calc
            d * (k : ℝ) ≤ 200 * (k : ℝ) :=
              mul_le_mul_of_nonneg_right hd1 (Nat.cast_nonneg k)
            _ ≤ (l : ℝ) / 2 := h200k
        have hzl : (l : ℝ) / 2 ≤ |(l : ℝ) - d * k| := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        have hz0 : (0 : ℝ) ≤ (l : ℝ) / 2 := by linarith
        have h1k : (0 : ℝ) < 1 + (k : ℝ) := by positivity
        have h1kl : 1 + (k : ℝ) ≤ 1 + (l : ℝ) := by
          linarith [hkl k hkN]
        have hq : ε * (l : ℝ) ≤
            a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)) := by
          have h1 : a * ((l : ℝ) / 2) ^ 2 / (1 + (l : ℝ))
              ≤ a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)) := by
            calc
              a * ((l : ℝ) / 2) ^ 2 / (1 + (l : ℝ))
                  ≤ a * |(l : ℝ) - d * k| ^ 2 / (1 + (l : ℝ)) := by
                    gcongr
              _ ≤ a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)) :=
                    div_le_div_of_nonneg_left (by positivity) h1k h1kl
          have h2 : ε * (l : ℝ) ≤
              a * ((l : ℝ) / 2) ^ 2 / (1 + (l : ℝ)) := by
            rw [le_div_iff₀ h1l]
            have hεa : ε ≤ a / 8 := min_le_left _ _
            nlinarith [mul_nonneg ha.le (mul_nonneg hl0 (sub_nonneg.mpr hl1)),
              mul_le_mul_of_nonneg_right hεa (mul_nonneg hl0 h1l.le)]
          linarith
        have hlin : ε * (l : ℝ) ≤ b * |(l : ℝ) - d * k| := by
          have hεb : ε ≤ b / 2 := min_le_right _ _
          nlinarith [mul_le_mul_of_nonneg_left hzl hb.le,
            mul_le_mul_of_nonneg_right hεb hl0]
        have hE1 : Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
            ≤ Real.exp (-(ε * (l : ℝ))) := by
          apply Real.exp_le_exp.mpr
          rw [neg_mul, neg_div]
          linarith
        have hE2 : Real.exp (-b * |(l : ℝ) - d * k|)
            ≤ Real.exp (-(ε * (l : ℝ))) := by
          apply Real.exp_le_exp.mpr
          rw [neg_mul]
          linarith
        have hfr : 1 / (1 + (k : ℝ)) ≤ 1 := by
          rw [div_le_one h1k]
          linarith
        calc
          1 / (1 + (k : ℝ))
              * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
                + Real.exp (-b * |(l : ℝ) - d * k|))
              ≤ 1 * (Real.exp (-(ε * (l : ℝ))) +
                  Real.exp (-(ε * (l : ℝ)))) := by
                apply mul_le_mul hfr (add_le_add hE1 hE2) (by positivity) one_pos.le
          _ = 2 * Real.exp (-(ε * (l : ℝ))) := by ring
      have hcard : ∑ k ∈ (Finset.range N).filter (fun k => k < T),
          1 / (1 + (k : ℝ))
            * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-b * |(l : ℝ) - d * k|))
          ≤ (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ)))) := by
        calc
          ∑ k ∈ (Finset.range N).filter (fun k => k < T),
              1 / (1 + (k : ℝ))
                * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
                  + Real.exp (-b * |(l : ℝ) - d * k|))
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
                    rw [hN]
                    push_cast
                    ring
                  rw [this, ← hcast] at *
                  nlinarith [Nat.cast_nonneg (α := ℝ) t]
                exact le_trans (Nat.cast_le.mpr hc1) hc2
      refine hcard.trans ?_
      rw [le_div_iff₀ hs0]
      have hsle : s ≤ 1 + (l : ℝ) := by
        calc
          s ≤ s * s := le_mul_of_one_le_left hs0.le hs1
          _ = 1 + (l : ℝ) := hss
      have hεl : 0 < ε * (l : ℝ) := mul_pos hε0 (by linarith)
      have hexp : Real.exp (-(ε * (l : ℝ))) ≤ 4 / (ε * (l : ℝ)) ^ 2 :=
        TaoCollatz.exp_neg_le_four_div_sq hεl
      have h2l : 1 + (l : ℝ) ≤ 2 * (l : ℝ) := by linarith
      calc
        (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ)))) * s
            ≤ (1 + (l : ℝ)) * (2 * Real.exp (-(ε * (l : ℝ))))
                * (1 + (l : ℝ)) := by
              apply mul_le_mul_of_nonneg_left hsle (by positivity)
        _ = 2 * ((1 + (l : ℝ)) ^ 2 * Real.exp (-(ε * (l : ℝ)))) := by ring
        _ ≤ 2 * ((2 * (l : ℝ)) ^ 2 * (4 / (ε * (l : ℝ)) ^ 2)) := by
              apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
              apply mul_le_mul (by nlinarith) hexp (Real.exp_pos _).le (by positivity)
        _ = 32 / ε ^ 2 := by
              field_simp
              ring
  -- Central range: the reciprocal prefactor costs at most `400/(1+l)`.
  have hcen : ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
      1 / (1 + (k : ℝ))
        * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
          + Real.exp (-b * |(l : ℝ) - d * k|))
      ≤ (3200 + 80 / b + 160 / Real.sqrt a) / s := by
    have hper : ∀ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - d * k|))
        ≤ 400 / (1 + (l : ℝ))
          * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (l : ℝ)))
            + Real.exp (-b * |(l : ℝ) - d * k|)) := by
      intro k hk
      have hkT : T ≤ k := Nat.le_of_not_lt (Finset.mem_filter.mp hk).2
      have hkN := (Finset.mem_filter.mp hk).1
      have h1k : (0 : ℝ) < 1 + (k : ℝ) := by positivity
      have h1kl : 1 + (k : ℝ) ≤ 1 + (l : ℝ) := by
        linarith [hkl k hkN]
      have h400 : 1 + (l : ℝ) ≤ 400 * (1 + (k : ℝ)) := by
        have h1 : t ≤ 400 * k + 399 := by omega
        have h2 : ((t : ℕ) : ℝ) ≤ ((400 * k + 399 : ℕ) : ℝ) := Nat.cast_le.mpr h1
        rw [hcast] at h2
        push_cast at h2
        linarith
      have hfrac : 1 / (1 + (k : ℝ)) ≤ 400 / (1 + (l : ℝ)) := by
        rw [div_le_div_iff₀ h1k h1l]
        linarith
      have hquad :
          Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
            ≤ Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (l : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [neg_mul, neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (by positivity) h1k h1kl
      apply mul_le_mul hfrac (add_le_add hquad le_rfl) (by positivity) (by positivity)
    have hwNnat : t < 10 * N := by omega
    have hwN10 : (t : ℝ) < 10 * (N : ℝ) := by exact_mod_cast hwNnat
    have hwN : (t : ℝ) < d * (N : ℝ) :=
      hwN10.trans_le (mul_le_mul_of_nonneg_right hd0 (Nat.cast_nonneg N))
    have hf1nn : ∀ u : ℝ, 0 ≤ Real.exp (-a * u ^ 2 / (1 + (l : ℝ))) :=
      fun u => (Real.exp_pos _).le
    have hf1anti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v →
        Real.exp (-a * v ^ 2 / (1 + (l : ℝ)))
          ≤ Real.exp (-a * u ^ 2 / (1 + (l : ℝ))) := by
      intro u v hu huv
      apply Real.exp_le_exp.mpr
      rw [neg_mul, neg_div, neg_mul, neg_div, neg_le_neg_iff]
      apply div_le_div_of_nonneg_right ?_ h1l.le
      nlinarith [mul_self_le_mul_self hu huv, ha.le]
    have hAP1 := sum_abs_real_AP_le hf1nn hf1anti hd t N hwN
    rw [hcast] at hAP1
    have hf2nn : ∀ u : ℝ, 0 ≤ Real.exp (-b * u) :=
      fun u => (Real.exp_pos _).le
    have hf2anti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v →
        Real.exp (-b * v) ≤ Real.exp (-b * u) := by
      intro u v hu huv
      apply Real.exp_le_exp.mpr
      nlinarith
    have hAP2 := sum_abs_real_AP_le hf2nn hf2anti hd t N hwN
    rw [hcast] at hAP2
    set β : ℝ := d ^ 2 * a / (1 + (l : ℝ)) with hβdef
    have hβ : 0 < β := by positivity
    have hgauss : ∑ m ∈ Finset.range N,
        Real.exp (-a * (d * (m : ℝ)) ^ 2 / (1 + (l : ℝ)))
          ≤ 3 + 2 / Real.sqrt β := by
      calc
        ∑ m ∈ Finset.range N,
            Real.exp (-a * (d * (m : ℝ)) ^ 2 / (1 + (l : ℝ)))
            = ∑ m ∈ Finset.range N, Real.exp (-β * (m : ℝ) ^ 2) := by
                refine Finset.sum_congr rfl fun m _ => congrArg Real.exp ?_
                rw [hβdef]
                field_simp
        _ ≤ 3 + 2 / Real.sqrt β := TaoCollatz.sum_range_exp_neg_sq_le hβ N
    have hβs : Real.sqrt β * s = d * Real.sqrt a := by
      rw [hs, ← Real.sqrt_mul hβ.le]
      rw [show β * (1 + (l : ℝ)) = d ^ 2 * a by rw [hβdef]; field_simp]
      rw [Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd.le]
    have hβpos : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
    have h2β : 2 / Real.sqrt β ≤ s / (5 * Real.sqrt a) := by
      rw [div_le_div_iff₀ hβpos (by positivity)]
      nlinarith [hβs, mul_le_mul_of_nonneg_right hd0 hsa.le]
    have hgeom : ∑ m ∈ Finset.range N, Real.exp (-b * (d * (m : ℝ)))
        ≤ 1 + 1 / (10 * b) := by
      have hterm : ∀ m : ℕ,
          Real.exp (-b * (d * (m : ℝ))) = Real.exp (-(d * b)) ^ m := by
        intro m
        rw [← Real.exp_nat_mul]
        exact congrArg Real.exp (by ring)
      rw [Finset.sum_congr rfl fun m _ => hterm m]
      have hr1 : Real.exp (-(d * b)) < 1 :=
        Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hd hb))
      calc
        ∑ m ∈ Finset.range N, Real.exp (-(d * b)) ^ m
            ≤ (1 - Real.exp (-(d * b)))⁻¹ :=
              TaoCollatz.sum_range_geom_le (Real.exp_pos _).le hr1 N
        _ ≤ 1 + 1 / (d * b) := TaoCollatz.one_sub_exp_neg_inv_le_one_add (by positivity)
        _ ≤ 1 + 1 / (10 * b) := by
              gcongr
    calc
      ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
          1 / (1 + (k : ℝ))
            * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-b * |(l : ℝ) - d * k|))
          ≤ ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
              400 / (1 + (l : ℝ))
                * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (l : ℝ)))
                  + Real.exp (-b * |(l : ℝ) - d * k|)) := Finset.sum_le_sum hper
      _ ≤ ∑ k ∈ Finset.range N,
            400 / (1 + (l : ℝ))
              * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (l : ℝ)))
                + Real.exp (-b * |(l : ℝ) - d * k|)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun k _ _ => by positivity
      _ = 400 / (1 + (l : ℝ))
            * (∑ k ∈ Finset.range N,
                Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (l : ℝ)))
              + ∑ k ∈ Finset.range N, Real.exp (-b * |(l : ℝ) - d * k|)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 400 / (1 + (l : ℝ))
            * (2 * (3 + 2 / Real.sqrt β) + 2 * (1 + 1 / (10 * b))) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          have g1 : ∑ k ∈ Finset.range N,
              Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (l : ℝ)))
                ≤ 2 * (3 + 2 / Real.sqrt β) :=
            hAP1.trans (by linarith [hgauss])
          have g2 : ∑ k ∈ Finset.range N, Real.exp (-b * |(l : ℝ) - d * k|)
                ≤ 2 * (1 + 1 / (10 * b)) :=
            hAP2.trans (by linarith [hgeom])
          linarith
      _ ≤ 400 / (1 + (l : ℝ))
            * (8 + 1 / (5 * b) + 2 * s / (5 * Real.sqrt a)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h4β : 4 / Real.sqrt β ≤ 2 * s / (5 * Real.sqrt a) := by
            calc
              4 / Real.sqrt β = 2 * (2 / Real.sqrt β) := by ring
              _ ≤ 2 * (s / (5 * Real.sqrt a)) :=
                mul_le_mul_of_nonneg_left h2β (by norm_num)
              _ = 2 * s / (5 * Real.sqrt a) := by ring
          have e3 : 2 * (2 / Real.sqrt β) = 4 / Real.sqrt β := by ring
          have e4 : 2 * (1 / (10 * b)) = 1 / (5 * b) := by ring
          linarith [h4β, e3, e4]
      _ ≤ (3200 + 80 / b + 160 / Real.sqrt a) / s := by
          rw [← hss, le_div_iff₀ hs0]
          have heq : 400 / (s * s)
                * (8 + 1 / (5 * b) + 2 * s / (5 * Real.sqrt a)) * s
              = 3200 / s + 80 / (b * s) + 160 / Real.sqrt a := by
            field_simp [hs0.ne', hb.ne', hsa.ne']
            ring
          rw [heq]
          have hA : 3200 / s ≤ (3200 : ℝ) := by
            rw [div_le_iff₀ hs0]
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hs1 (show (0 : ℝ) ≤ 3200 by norm_num))
          have hB : 80 / (b * s) ≤ 80 / b := by
            rw [div_le_div_iff₀ (mul_pos hb hs0) hb]
            exact mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_right hb.le hs1) (by norm_num)
          exact add_le_add (add_le_add hA hB) le_rfl
  calc
    ∑ k ∈ (Finset.range N).filter (fun k => k < T),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - d * k|))
      + ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < T),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - d * k|))
        ≤ (32 / ε ^ 2) / s + (3200 + 80 / b + 160 / Real.sqrt a) / s :=
          add_le_add hedge hcen
    _ = (32 / ε ^ 2 + (3200 + 80 / b + 160 / Real.sqrt a)) / s :=
      (add_div _ _ _).symm

/-- Existential-constant form of the uniform tilted renewal sum. -/
theorem renewal_weight_sumP_le {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd0 : 10 ≤ d) (hd1 : d ≤ 200) :
    ∃ C > (0 : ℝ), ∀ (l : ℤ), 0 ≤ l →
      ∑ k ∈ Finset.range (l.toNat / 3 + 1),
        1 / (1 + (k : ℝ))
          * (Real.exp (-a * |(l : ℝ) - d * k| ^ 2 / (1 + (k : ℝ)))
            + Real.exp (-b * |(l : ℝ) - d * k|))
        ≤ C / Real.sqrt (1 + (l : ℝ)) :=
  ⟨C_renewalWeightP a b, C_renewalWeightP_pos ha hb,
    renewal_weight_sumP_le_explicitC ha hb hd0 hd1⟩

/-! ### Uniform renewal Gaussian bound -/

/-- The transverse decay rate in the tilted renewal-mass bound. -/
noncomputable def c_renewalMassP : ℝ := c_holdLocalP / 2 / 2

/-- A constant for the tilted renewal-mass bound, uniform over the campaign
window. -/
noncomputable def C_renewalMassP : ℝ :=
  C_holdLocalP *
    C_renewalWeightP (2 * (c_holdLocalP / 2) ^ 2 / 5) (c_holdLocalP / 2 / 2)

theorem c_renewalMassP_pos : 0 < c_renewalMassP := by
  unfold c_renewalMassP
  linarith [c_holdLocalP_pos]

theorem C_renewalMassP_pos : 0 < C_renewalMassP := by
  have h5 := C_renewalWeightP_pos
    (a := 2 * (c_holdLocalP / 2) ^ 2 / 5) (b := c_holdLocalP / 2 / 2)
    (by positivity [c_holdLocalP_pos]) (by positivity [c_holdLocalP_pos])
  unfold C_renewalMassP
  exact mul_pos C_holdLocalP_pos h5

/-- **Uniform tilted renewal Gaussian bound** (the first display in Tao's
Lemma 7.7 proof).  The exact drift is removed from the transverse coordinate,
leaving the center `j - (p/2)l`; all constants are independent of `p` on
`[1/5,3/5]`. -/
theorem renewalMassP_bound_explicitC
    (hp0 : 1 / 5 ≤ tilt) (hp1 : tilt ≤ 3 / 5) :
    ∀ (j : ℕ) (l : ℤ), 0 ≤ l →
      (renewalMassLaw (j, l)).toReal
        ≤ C_renewalMassP / Real.sqrt (1 + (l : ℝ))
            * TaoCollatz.Gweight (1 + (l : ℝ))
              (c_renewalMassP * ((j : ℝ) - tilt / 2 * (l : ℝ))) := by
  have hc0 := c_holdLocalP_pos
  have hC0 := C_holdLocalP_pos
  have hloc := holdP_local_bound_explicitC tilt hp0 hp1
  unfold C_renewalMassP c_renewalMassP
  set c0 := c_holdLocalP with hc0def
  set C0 := C_holdLocalP with hC0def
  set c1 : ℝ := c0 / 2 with hc1def
  have hc1 : 0 < c1 := by rw [hc1def]; positivity
  have hC5 := C_renewalWeightP_pos (a := 2 * c1 ^ 2 / 5) (b := c1 / 2)
    (by positivity) (by positivity)
  set C5 := C_renewalWeightP (2 * c1 ^ 2 / 5) (c1 / 2) with hC5def
  set d : ℝ := (pairThreeProb tilt)⁻¹ * (2 / tilt) with hddef
  have hdmem : 10 ≤ d ∧ d ≤ 200 := by
    rw [hddef]
    exact holdP_height_drift_mem_window hp0 hp1
  have hsum := renewal_weight_sumP_le_explicitC
    (a := 2 * c1 ^ 2 / 5) (b := c1 / 2) (d := d)
    (by positivity) (by positivity) hdmem.1 hdmem.2
  intro j l hl
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have h1l : (0 : ℝ) < 1 + (l : ℝ) := by linarith
  set G : ℝ := TaoCollatz.Gweight (1 + (l : ℝ))
    (c1 / 2 * ((j : ℝ) - tilt / 2 * (l : ℝ))) with hGdef
  have hG : 0 ≤ G := TaoCollatz.Gweight_nonneg _ _
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
      (TaoCollatz.iidSum holdLaw k (j, l)).toReal
        ≤ C0 * G * (1 / (1 + (k : ℝ))
            * (Real.exp (-(2 * c1 ^ 2 / 5) * |(l : ℝ) - d * k| ^ 2 /
                (1 + (k : ℝ)))
              + Real.exp (-(c1 / 2) * |(l : ℝ) - d * k|))) := by
    intro k hk
    have h1 := hloc k j l
    rw [holdSumP_eq_iidSum] at h1
    refine h1.trans ?_
    set u : ℝ := (j : ℝ) - (pairThreeProb tilt)⁻¹ * k with hu
    set v : ℝ := (l : ℝ) - d * k with hv
    have h1k : (0 : ℝ) < 1 + (k : ℝ) := by positivity
    have h1kl : 1 + (k : ℝ) ≤ 1 + (l : ℝ) := by linarith [hkl k hk]
    have hnorm : ‖((u, v) : ℝ × ℝ)‖ = max |u| |v| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have hstep1 : TaoCollatz.Gweight (1 + (k : ℝ))
          (c0 * ‖((u, v) : ℝ × ℝ)‖)
        ≤ TaoCollatz.Gweight (1 + (k : ℝ)) (c1 * (|u| + |v|)) := by
      apply TaoCollatz.Gweight_anti h1k (by positivity)
      rw [hnorm, hc1def]
      rcases max_cases |u| |v| with ⟨hm, hle⟩ | ⟨hm, hle⟩ <;> rw [hm] <;>
        nlinarith [abs_nonneg u, abs_nonneg v, hc0.le]
    have hxe : (j : ℝ) - tilt / 2 * (l : ℝ) = u - tilt / 2 * v := by
      rw [hu, hv, hddef]
      exact (holdP_transverse_drift_cancel htilt0.ne' (j : ℝ) (l : ℝ) (k : ℝ)).symm
    have hy : |(j : ℝ) - tilt / 2 * (l : ℝ)| + 7 / 10 * |v| ≤ |u| + |v| := by
      have h := transverse_triangle_window (p := tilt) (u := u) (v := v) hp0 hp1
      rwa [← hxe] at h
    have hstep2 := Gweight_factorP
      (x := (j : ℝ) - tilt / 2 * (l : ℝ)) (z := |v|) (y := |u| + |v|)
      hc1 h1k h1kl (abs_nonneg v) hy
    calc
      C0 / (1 + (k : ℝ)) * TaoCollatz.Gweight (1 + (k : ℝ))
          (c0 * ‖((u, v) : ℝ × ℝ)‖)
          ≤ C0 / (1 + (k : ℝ)) * (G
              * (Real.exp (-(2 * c1 ^ 2 / 5) * |v| ^ 2 / (1 + (k : ℝ)))
                + Real.exp (-(c1 / 2) * |v|))) := by
            apply mul_le_mul_of_nonneg_left (hstep1.trans hstep2) (by positivity)
      _ = C0 * G * (1 / (1 + (k : ℝ))
            * (Real.exp (-(2 * c1 ^ 2 / 5) * |v| ^ 2 / (1 + (k : ℝ)))
              + Real.exp (-(c1 / 2) * |v|))) := by ring
  calc
    (renewalMassLaw (j, l)).toReal
        = ∑ k ∈ Finset.range N,
            (TaoCollatz.iidSum holdLaw k (j, l)).toReal :=
          renewalMassP_toReal_eq tilt htilt0 htilt1 j l
    _ ≤ ∑ k ∈ Finset.range N, C0 * G * (1 / (1 + (k : ℝ))
          * (Real.exp (-(2 * c1 ^ 2 / 5) * |(l : ℝ) - d * k| ^ 2 /
              (1 + (k : ℝ)))
            + Real.exp (-(c1 / 2) * |(l : ℝ) - d * k|))) :=
        Finset.sum_le_sum hterm
    _ = C0 * G * ∑ k ∈ Finset.range N, 1 / (1 + (k : ℝ))
          * (Real.exp (-(2 * c1 ^ 2 / 5) * |(l : ℝ) - d * k| ^ 2 /
              (1 + (k : ℝ)))
            + Real.exp (-(c1 / 2) * |(l : ℝ) - d * k|)) := by
        rw [Finset.mul_sum]
    _ ≤ C0 * G * (C5 / Real.sqrt (1 + (l : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (hsum l hl) (by positivity)
    _ = C0 * C5 / Real.sqrt (1 + (l : ℝ)) * G := by ring

/-- Existential interface: both renewal constants are chosen before `p`. -/
theorem renewalMassP_bound_window :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ (j : ℕ) (l : ℤ), 0 ≤ l →
        (renewalMassP p (by linarith) (by linarith) (j, l)).toReal
          ≤ C / Real.sqrt (1 + (l : ℝ))
              * TaoCollatz.Gweight (1 + (l : ℝ))
                (c * ((j : ℝ) - p / 2 * (l : ℝ))) :=
  ⟨c_renewalMassP, c_renewalMassP_pos,
    C_renewalMassP, C_renewalMassP_pos,
    fun p hp0 hp1 => renewalMassP_bound_explicitC p (by linarith) (by linarith) hp0 hp1⟩

/-! ### Uniform one-step overshoot bound -/

/-- Uniform exponential rate for one tilted holding increment. -/
noncomputable def gamma_holdStepP : ℝ := c_holdLocalP / 4

/-- Uniform constant for one tilted holding increment. -/
noncomputable def C_holdStepP : ℝ := 2 * C_holdLocalP

theorem gamma_holdStepP_pos : 0 < gamma_holdStepP := by
  unfold gamma_holdStepP
  linarith [c_holdLocalP_pos]

theorem C_holdStepP_pos : 0 < C_holdStepP := by
  unfold C_holdStepP
  linarith [C_holdLocalP_pos]

/-- The single-overshoot-step estimate for `holdP`, centered at its exact
p-dependent mean and with constants uniform on `[1/5,3/5]`. -/
theorem holdP_step_bound_explicitC
    (hp0 : 1 / 5 ≤ tilt) (hp1 : tilt ≤ 3 / 5) :
    ∀ d : ℕ × ℤ,
      (holdLaw d).toReal
        ≤ C_holdStepP *
            Real.exp (-gamma_holdStepP *
              |(d.1 : ℝ) - (pairThreeProb tilt)⁻¹|) *
            Real.exp (-gamma_holdStepP *
              |(d.2 : ℝ) - (pairThreeProb tilt)⁻¹ * (2 / tilt)|) := by
  have hc0 := c_holdLocalP_pos
  have hC0 := C_holdLocalP_pos
  have hloc := holdP_local_bound_explicitC tilt hp0 hp1
  unfold C_holdStepP gamma_holdStepP
  set c0 := c_holdLocalP with hc0def
  set C0 := C_holdLocalP with hC0def
  intro e
  have h1 := hloc 1 e.1 e.2
  rw [holdSumP_eq_iidSum] at h1
  have hone : TaoCollatz.iidSum holdLaw 1 = holdLaw := by
    rw [TaoCollatz.iidSum_succ, TaoCollatz.iidSum_zero]
    simp only [PMF.pure_map, add_zero, PMF.bind_pure]
  rw [hone] at h1
  refine h1.trans ?_
  set A : ℝ := (e.1 : ℝ) - (pairThreeProb tilt)⁻¹ * (1 : ℕ) with hA
  set B : ℝ := (e.2 : ℝ) -
    ((pairThreeProb tilt)⁻¹ * (2 / tilt)) * (1 : ℕ) with hB
  have hnorm : ‖((A, B) : ℝ × ℝ)‖ = max |A| |B| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hstep1 : TaoCollatz.Gweight (1 + ((1 : ℕ) : ℝ))
        (c0 * ‖((A, B) : ℝ × ℝ)‖)
      ≤ TaoCollatz.Gweight (1 + ((1 : ℕ) : ℝ))
          (c0 / 2 * (|A| + |B|)) := by
    apply TaoCollatz.Gweight_anti (by push_cast; norm_num) (by positivity)
    rw [hnorm]
    rcases max_cases |A| |B| with ⟨hm, hle⟩ | ⟨hm, hle⟩ <;> rw [hm] <;>
      nlinarith [abs_nonneg A, abs_nonneg B, hc0.le]
  have hstep2 : TaoCollatz.Gweight (1 + ((1 : ℕ) : ℝ))
        (c0 / 2 * (|A| + |B|))
      ≤ 4 * Real.exp (-(c0 / 4) * |A|) * Real.exp (-(c0 / 4) * |B|) := by
    have h12 : (1 : ℝ) + ((1 : ℕ) : ℝ) = 2 := by push_cast; norm_num
    rw [h12]
    calc
      TaoCollatz.Gweight 2 (c0 / 2 * (|A| + |B|))
          ≤ 4 * Real.exp (-(c0 / 2 * (|A| + |B|)) / 2) :=
            TaoCollatz.Gweight_two_le (by positivity)
      _ = 4 * Real.exp (-(c0 / 4) * |A|) *
            Real.exp (-(c0 / 4) * |B|) := by
          rw [mul_assoc, ← Real.exp_add]
          exact congrArg (4 * ·) (congrArg Real.exp (by ring))
  have hAe : |A| = |(e.1 : ℝ) - (pairThreeProb tilt)⁻¹| := by
    rw [hA]
    push_cast
    ring
  have hBe : |B| =
      |(e.2 : ℝ) - (pairThreeProb tilt)⁻¹ * (2 / tilt)| := by
    rw [hB]
    push_cast
    ring
  calc
    C0 / (1 + ((1 : ℕ) : ℝ)) * TaoCollatz.Gweight (1 + ((1 : ℕ) : ℝ))
        (c0 * ‖((A, B) : ℝ × ℝ)‖)
        ≤ C0 / (1 + ((1 : ℕ) : ℝ))
            * (4 * Real.exp (-(c0 / 4) * |A|) *
              Real.exp (-(c0 / 4) * |B|)) := by
          apply mul_le_mul_of_nonneg_left (hstep1.trans hstep2) (by positivity)
    _ = 2 * C0 * Real.exp (-(c0 / 4) * |A|) *
          Real.exp (-(c0 / 4) * |B|) := by
        push_cast
        ring
    _ = 2 * C0 *
          Real.exp (-(c0 / 4) * |(e.1 : ℝ) - (pairThreeProb tilt)⁻¹|) *
          Real.exp (-(c0 / 4) *
            |(e.2 : ℝ) - (pairThreeProb tilt)⁻¹ * (2 / tilt)|) := by
        rw [hAe, hBe]

/-- Existential interface for the uniform one-step estimate. -/
theorem holdP_step_bound_window :
    ∃ γ > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5), ∀ d : ℕ × ℤ,
        (holdP p (by linarith) (by linarith) d).toReal
          ≤ C * Real.exp (-γ * |(d.1 : ℝ) - (pairThreeProb p)⁻¹|) *
              Real.exp (-γ *
                |(d.2 : ℝ) - (pairThreeProb p)⁻¹ * (2 / p)|) :=
  ⟨gamma_holdStepP, gamma_holdStepP_pos, C_holdStepP, C_holdStepP_pos,
    fun p hp0 hp1 => holdP_step_bound_explicitC p (by linarith) (by linarith) hp0 hp1⟩

/-! ### Uniform first-passage localization -/

/-- The last-step convolution assembly for a holding law whose transverse
renewal slope is `r`.  Unlike the fixed-law proof, the horizontal step mean
need not be an integer: on the campaign window it is at most `16`, so moving
the exponential window to the integer endpoint costs `exp (16 * γ)`.  The
vertical mean is at most `200`, and its analogous cost is `exp (200 * γ)`.
All remaining analytic inputs are the p-free lemmas used in Tao's Lemma 7.7. -/
theorem fpDistP_location_bound_core (r m1 m2 c6 C6 γ C7 K : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hm1 : |m1| ≤ 16) (hm2 : |m2| ≤ 200)
    (hc6 : 0 < c6) (hC6 : 0 < C6) (hγ : 0 < γ) (hC7 : 0 < C7) (hK : 0 < K)
    (hU : ∀ (j : ℕ) (l : ℤ), 0 ≤ l →
      (renewalMassLaw (j, l)).toReal
        ≤ C6 / Real.sqrt (1 + (l : ℝ))
            * TaoCollatz.Gweight (1 + (l : ℝ)) (c6 * ((j : ℝ) - r * (l : ℝ))))
    (hstep : ∀ d : ℕ × ℤ,
      (holdLaw d).toReal
        ≤ C7 * Real.exp (-γ * |(d.1 : ℝ) - m1|)
            * Real.exp (-γ * |(d.2 : ℝ) - m2|))
    (hKs : ∀ s : ℕ,
      ∑ m ∈ Finset.range (s + 1),
          Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m)
        ≤ K / Real.sqrt (1 + s)) :
    ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (fpLaw s (j, l)).toReal
        ≤ C6 * C7 * Real.exp (16 * γ) * Real.exp (200 * γ) * (4 + 8 / γ)
              * 2 * K
            * (Real.exp (-(min (min (c6 / 2) (γ / 4) / 2) γ) * ((l : ℝ) - s))
                / Real.sqrt (1 + s))
            * TaoCollatz.Gweight (1 + s)
                (min (min (c6 / 2) (γ / 4) / 2) γ * ((j : ℝ) - r * s)) := by
  set c9 : ℝ := min (c6 / 2) (γ / 4) with hc9def
  have hc9 : 0 < c9 := lt_min (by positivity) (by positivity)
  have hc9γ : c9 ≤ γ / 4 := min_le_right _ _
  set cF : ℝ := min (c9 / 2) γ with hcFdef
  have hcF : 0 < cF := lt_min (by positivity) hγ
  set D : ℝ :=
    C6 * C7 * Real.exp (16 * γ) * Real.exp (200 * γ) * (4 + 8 / γ) * 2 with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  intro s j l
  have h1s : (0 : ℝ) < 1 + (s : ℝ) := by positivity
  set X : ℝ := (j : ℝ) - r * s with hXdef
  by_cases hls : l ≤ (s : ℤ)
  · have h0 : fpLaw s (j, l) = 0 := by
      by_contra h
      exact absurd
        (fpDistP_support_snd_gt tilt htilt0 htilt1 s (j, l)
          (by rwa [PMF.mem_support_iff]))
        (not_lt.mpr hls)
    rw [h0, ENNReal.toReal_zero]
    apply mul_nonneg
    · positivity
    · exact TaoCollatz.Gweight_nonneg _ _
  push Not at hls
  have hlsR : (s : ℝ) ≤ (l : ℝ) := by exact_mod_cast hls.le
  set F : Finset (ℕ × ℤ) := (Finset.range (j + 1)) ×ˢ (Finset.Icc (0 : ℤ) (s : ℤ))
    with hF
  have hinner : ∀ p : ℕ × ℤ,
      (∑' d : ℕ × ℤ, if (j, l) = p + d then holdLaw d else 0)
        = if p.1 ≤ j then holdLaw (j - p.1, l - p.2) else 0 := by
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
  have hred : (∑' p : ℕ × ℤ, (if p.2 ≤ (s : ℤ) then renewalMassLaw p else 0)
        * ∑' d : ℕ × ℤ, (if (j, l) = p + d then holdLaw d else 0))
      = ∑ p ∈ F, renewalMassLaw p * holdLaw (j - p.1, l - p.2) := by
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
            push Not at h3
            exact hp (Finset.mem_product.mpr
              ⟨Finset.mem_range.mpr (by omega), Finset.mem_Icc.mpr ⟨h3, h2⟩⟩)
          rw [renewalMassP_zero_of_snd_neg tilt htilt0 htilt1 h3, ite_self, zero_mul]
        · rw [if_neg h2, zero_mul]
      · rw [if_neg h1, mul_zero]
  have hfp : fpLaw s (j, l) ≤
      ∑ p ∈ F, renewalMassLaw p * holdLaw (j - p.1, l - p.2) :=
    hred ▸ fpDistP_le_renewal_conv tilt htilt0 htilt1 s (j, l)
  have hterm_ne : ∀ p ∈ F,
      renewalMassLaw p * holdLaw (j - p.1, l - p.2) ≠ ⊤ := fun p _ =>
    ENNReal.mul_ne_top (renewalMassP_ne_top tilt htilt0 htilt1 p) (PMF.apply_ne_top _ _)
  have hsum_ne : (∑ p ∈ F,
      renewalMassLaw p * holdLaw (j - p.1, l - p.2)) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun p hp => (hterm_ne p hp).lt_top).ne
  have hreal : (fpLaw s (j, l)).toReal
      ≤ ∑ p ∈ F, (renewalMassLaw p).toReal
          * (holdLaw (j - p.1, l - p.2)).toReal := by
    calc
      (fpLaw s (j, l)).toReal
          ≤ (∑ p ∈ F, renewalMassLaw p * holdLaw (j - p.1, l - p.2)).toReal :=
            ENNReal.toReal_mono hsum_ne hfp
      _ = ∑ p ∈ F, (renewalMassLaw p).toReal
            * (holdLaw (j - p.1, l - p.2)).toReal := by
          rw [ENNReal.toReal_sum hterm_ne]
          exact Finset.sum_congr rfl fun p _ => ENNReal.toReal_mul
  refine hreal.trans ?_
  have hIcc : Finset.Icc (0 : ℤ) (s : ℤ) = (Finset.range (s + 1)).image
      (fun m : ℕ => (m : ℤ)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, hs'⟩
      exact ⟨x.toNat, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩
      omega
  have hsplit : ∑ p ∈ F, (renewalMassLaw p).toReal
        * (holdLaw (j - p.1, l - p.2)).toReal
      = ∑ j₁ ∈ Finset.range (j + 1), ∑ m ∈ Finset.range (s + 1),
          (renewalMassLaw (j₁, (m : ℤ))).toReal
            * (holdLaw (j - j₁, l - m)).toReal := by
    rw [hF, Finset.sum_product]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [hIcc, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]
  rw [hsplit]
  set G2 : ℝ := TaoCollatz.Gweight (1 + (s : ℝ)) (c9 / 2 * X) with hG2def
  have hG2 : 0 ≤ G2 := TaoCollatz.Gweight_nonneg _ _
  have hmsum : ∀ m ∈ Finset.range (s + 1),
      ∑ j₁ ∈ Finset.range (j + 1),
        (renewalMassLaw (j₁, (m : ℤ))).toReal
          * (holdLaw (j - j₁, l - m)).toReal
      ≤ D * Real.exp (-γ * ((l : ℝ) - s)) * G2
          * (Real.exp (-(γ / 2) * ((s : ℝ) - m)) / Real.sqrt (1 + m)) := by
    intro m hm
    have hms : m ≤ s := by
      have := Finset.mem_range.mp hm
      omega
    have hmsR : (m : ℝ) ≤ (s : ℝ) := by exact_mod_cast hms
    have h1m : (0 : ℝ) < 1 + (m : ℝ) := by positivity
    have h1ms : 1 + (m : ℝ) ≤ 1 + (s : ℝ) := by linarith
    have hterm : ∀ j₁ ∈ Finset.range (j + 1),
        (renewalMassLaw (j₁, (m : ℤ))).toReal
            * (holdLaw (j - j₁, l - m)).toReal
        ≤ (C7 * Real.exp (16 * γ) * Real.exp (200 * γ)
              * Real.exp (-γ * ((l : ℝ) - m)))
            * (C6 / Real.sqrt (1 + m))
            * (TaoCollatz.Gweight (1 + (m : ℝ))
                  (c6 * ((j₁ : ℝ) - r * m))
              * Real.exp (-γ * |(j : ℝ) - j₁|)) := by
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
      have htri1 : |(j : ℝ) - j₁| ≤ |(j : ℝ) - j₁ - m1| + 16 := by
        have h := abs_add_le ((j : ℝ) - j₁ - m1) m1
        rw [show (j : ℝ) - j₁ - m1 + m1 = (j : ℝ) - j₁ by ring] at h
        linarith
      have hexp1 : Real.exp (-γ * |(j : ℝ) - j₁ - m1|)
          ≤ Real.exp (16 * γ) * Real.exp (-γ * |(j : ℝ) - j₁|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      have htri2 : (l : ℝ) - m ≤ |(l : ℝ) - m - m2| + 200 := by
        have h := abs_add_le ((l : ℝ) - m - m2) m2
        rw [show (l : ℝ) - m - m2 + m2 = (l : ℝ) - m by ring] at h
        linarith [le_abs_self ((l : ℝ) - m)]
      have hexp2 : Real.exp (-γ * |(l : ℝ) - m - m2|)
          ≤ Real.exp (200 * γ) * Real.exp (-γ * ((l : ℝ) - m)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hhold : (holdLaw (j - j₁, l - m)).toReal
          ≤ C7 * (Real.exp (16 * γ) * Real.exp (-γ * |(j : ℝ) - j₁|))
              * (Real.exp (200 * γ) * Real.exp (-γ * ((l : ℝ) - m))) := by
        calc
          (holdLaw (j - j₁, l - m)).toReal
              ≤ C7 * Real.exp (-γ * |(j : ℝ) - j₁ - m1|)
                  * Real.exp (-γ * |(l : ℝ) - m - m2|) := hsb
          _ ≤ C7 * (Real.exp (16 * γ) * Real.exp (-γ * |(j : ℝ) - j₁|))
                  * (Real.exp (200 * γ) * Real.exp (-γ * ((l : ℝ) - m))) := by
              calc
                C7 * Real.exp (-γ * |(j : ℝ) - j₁ - m1|)
                      * Real.exp (-γ * |(l : ℝ) - m - m2|)
                    ≤ C7 * (Real.exp (16 * γ) * Real.exp (-γ * |(j : ℝ) - j₁|))
                        * Real.exp (-γ * |(l : ℝ) - m - m2|) :=
                      mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left hexp1 hC7.le) (Real.exp_pos _).le
                _ ≤ C7 * (Real.exp (16 * γ) * Real.exp (-γ * |(j : ℝ) - j₁|))
                        * (Real.exp (200 * γ) * Real.exp (-γ * ((l : ℝ) - m))) :=
                      mul_le_mul_of_nonneg_left hexp2 (by positivity)
      calc
        (renewalMassLaw (j₁, (m : ℤ))).toReal
              * (holdLaw (j - j₁, l - m)).toReal
            ≤ (C6 / Real.sqrt (1 + (m : ℝ))
                * TaoCollatz.Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - r * m)))
              * (C7 * (Real.exp (16 * γ) * Real.exp (-γ * |(j : ℝ) - j₁|))
                * (Real.exp (200 * γ) * Real.exp (-γ * ((l : ℝ) - m)))) := by
              apply mul_le_mul hUb hhold ENNReal.toReal_nonneg
                (mul_nonneg (by positivity) (TaoCollatz.Gweight_nonneg _ _))
        _ = (C7 * Real.exp (16 * γ) * Real.exp (200 * γ)
                * Real.exp (-γ * ((l : ℝ) - m)))
              * (C6 / Real.sqrt (1 + m))
              * (TaoCollatz.Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - r * m))
                * Real.exp (-γ * |(j : ℝ) - j₁|)) := by ring
    have hconv := TaoCollatz.conv_Gweight_exp (t := 1 + (m : ℝ)) (c := c6) (γ := γ)
      h1m hc6 hγ (r * m) (j : ℤ) (j + 1) (by simp)
    have hshift : TaoCollatz.Gweight (1 + (m : ℝ)) (c9 * ((j : ℝ) - r * m))
        ≤ 2 * Real.exp (c9 * r * ((s : ℝ) - m)) * G2 := by
      have harg : (j : ℝ) - r * m = X + r * ((s : ℝ) - m) := by
        rw [hXdef]
        ring
      rw [harg, hG2def]
      refine (TaoCollatz.Gweight_shift h1m h1ms hc9 X (r * ((s : ℝ) - m))).trans ?_
      have habs : |r * ((s : ℝ) - m)| = r * ((s : ℝ) - m) := by
        rw [abs_of_nonneg (mul_nonneg hr0 (by linarith))]
      rw [habs]
      exact le_of_eq (by ring)
    have hexps : Real.exp (-γ * ((l : ℝ) - m))
          * Real.exp (c9 * r * ((s : ℝ) - m))
        ≤ Real.exp (-γ * ((l : ℝ) - s))
            * Real.exp (-(γ / 2) * ((s : ℝ) - m)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcr : c9 * r ≤ γ / 4 := by
        exact (mul_le_mul hc9γ hr1 hr0 (by positivity)).trans_eq (by ring)
      nlinarith [mul_le_mul_of_nonneg_right hcr (by linarith : (0 : ℝ) ≤ (s : ℝ) - m)]
    calc
      ∑ j₁ ∈ Finset.range (j + 1),
          (renewalMassLaw (j₁, (m : ℤ))).toReal
            * (holdLaw (j - j₁, l - m)).toReal
          ≤ ∑ j₁ ∈ Finset.range (j + 1),
            (C7 * Real.exp (16 * γ) * Real.exp (200 * γ)
                * Real.exp (-γ * ((l : ℝ) - m)))
              * (C6 / Real.sqrt (1 + m))
              * (TaoCollatz.Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - r * m))
                * Real.exp (-γ * |(j : ℝ) - j₁|)) :=
            Finset.sum_le_sum hterm
      _ = (C7 * Real.exp (16 * γ) * Real.exp (200 * γ)
              * Real.exp (-γ * ((l : ℝ) - m)))
            * (C6 / Real.sqrt (1 + m))
            * ∑ j₁ ∈ Finset.range (j + 1),
              TaoCollatz.Gweight (1 + (m : ℝ)) (c6 * ((j₁ : ℝ) - r * m))
                * Real.exp (-γ * |(j : ℝ) - j₁|) := by
          rw [Finset.mul_sum]
      _ ≤ (C7 * Real.exp (16 * γ) * Real.exp (200 * γ)
              * Real.exp (-γ * ((l : ℝ) - m)))
            * (C6 / Real.sqrt (1 + m))
            * ((4 + 8 / γ) * (2 * Real.exp (c9 * r * ((s : ℝ) - m)) * G2)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine hconv.trans ?_
          exact mul_le_mul_of_nonneg_left hshift (by positivity)
      _ = (D * G2) * (Real.exp (-γ * ((l : ℝ) - m))
            * Real.exp (c9 * r * ((s : ℝ) - m)))
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
  calc
    ∑ j₁ ∈ Finset.range (j + 1), ∑ m ∈ Finset.range (s + 1),
        (renewalMassLaw (j₁, (m : ℤ))).toReal
          * (holdLaw (j - j₁, l - m)).toReal
        = ∑ m ∈ Finset.range (s + 1), ∑ j₁ ∈ Finset.range (j + 1),
          (renewalMassLaw (j₁, (m : ℤ))).toReal
            * (holdLaw (j - j₁, l - m)).toReal := Finset.sum_comm
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
        * TaoCollatz.Gweight (1 + (s : ℝ)) (cF * X) := by
      have hexpF : Real.exp (-γ * ((l : ℝ) - s))
          ≤ Real.exp (-cF * ((l : ℝ) - s)) := by
        apply Real.exp_le_exp.mpr
        have hcFγ : cF ≤ γ := min_le_right _ _
        have h := mul_le_mul_of_nonneg_right hcFγ (sub_nonneg.mpr hlsR)
        linarith only [h]
      have hGrel : G2 ≤ TaoCollatz.Gweight (1 + (s : ℝ)) (cF * X) := by
        rw [hG2def, ← TaoCollatz.Gweight_abs _ (c9 / 2 * X),
          ← TaoCollatz.Gweight_abs _ (cF * X), abs_mul, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < c9 / 2), abs_of_pos hcF]
        apply TaoCollatz.Gweight_anti h1s (by positivity)
        have hcF9 : cF ≤ c9 / 2 := min_le_left _ _
        linarith only [mul_le_mul_of_nonneg_right hcF9 (abs_nonneg X)]
      calc
        D * Real.exp (-γ * ((l : ℝ) - s)) * G2 * (K / Real.sqrt (1 + s))
            ≤ D * Real.exp (-cF * ((l : ℝ) - s))
                * TaoCollatz.Gweight (1 + (s : ℝ)) (cF * X)
                * (K / Real.sqrt (1 + s)) := by
              apply mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc
                D * Real.exp (-γ * ((l : ℝ) - s)) * G2
                    ≤ D * Real.exp (-cF * ((l : ℝ) - s)) * G2 := by
                      apply mul_le_mul_of_nonneg_right ?_ hG2
                      exact mul_le_mul_of_nonneg_left hexpF hD.le
                _ ≤ D * Real.exp (-cF * ((l : ℝ) - s))
                    * TaoCollatz.Gweight (1 + (s : ℝ)) (cF * X) := by
                      apply mul_le_mul_of_nonneg_left hGrel (by positivity)
        _ = D * K * (Real.exp (-cF * ((l : ℝ) - s)) / Real.sqrt (1 + s))
            * TaoCollatz.Gweight (1 + (s : ℝ)) (cF * X) := by ring

/-- Uniform decay rate in Lemma 7.7 for the tilted holding laws. -/
noncomputable def c_fpLocationP : ℝ :=
  min (min (c_renewalMassP / 2) (gamma_holdStepP / 4) / 2) gamma_holdStepP

/-- Uniform multiplicative constant in Lemma 7.7 for the tilted holding laws. -/
noncomputable def C_fpLocationP : ℝ :=
  C_renewalMassP * C_holdStepP
    * Real.exp (16 * gamma_holdStepP) * Real.exp (200 * gamma_holdStepP)
    * (4 + 8 / gamma_holdStepP) * 2
    * TaoCollatz.K_sqrtExp (gamma_holdStepP / 2)

theorem c_fpLocationP_pos : 0 < c_fpLocationP := by
  have hc := c_renewalMassP_pos
  have hγ := gamma_holdStepP_pos
  unfold c_fpLocationP
  exact lt_min (by positivity) hγ

theorem C_fpLocationP_pos : 0 < C_fpLocationP := by
  have hγ := gamma_holdStepP_pos
  have hγ2 : 0 < gamma_holdStepP / 2 := by linarith
  have hK := TaoCollatz.K_sqrtExp_pos hγ2
  unfold C_fpLocationP
  exact mul_pos
    (mul_pos
      (mul_pos
        (mul_pos
          (mul_pos
            (mul_pos C_renewalMassP_pos C_holdStepP_pos)
              (Real.exp_pos _))
            (Real.exp_pos _))
          (by positivity))
        (by norm_num))
    hK

/-- Lemma 7.7 for `holdP p`, with one rate and one constant valid on the
whole campaign window.  This is the `_explicitC` interface consumed by the
tilted many-triangles argument. -/
theorem fpDistP_location_bound_explicitC
    (hp0 : 1 / 5 ≤ tilt) (hp1 : tilt ≤ 3 / 5) :
    ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (fpLaw s (j, l)).toReal
        ≤ C_fpLocationP
            * (Real.exp (-c_fpLocationP * ((l : ℝ) - s)) / Real.sqrt (1 + s))
            * TaoCollatz.Gweight (1 + s)
                (c_fpLocationP * ((j : ℝ) - tilt / 2 * s)) := by
  have hp : 0 < tilt := by linarith
  have hq := pairThreeProb_mem_window hp0 hp1
  have hqpos : 0 < pairThreeProb tilt := by linarith
  have hm10 : 0 ≤ (pairThreeProb tilt)⁻¹ := inv_nonneg.mpr hqpos.le
  have hm1hi : (pairThreeProb tilt)⁻¹ ≤ 16 := by
    rw [inv_le_comm₀ hqpos (by norm_num : (0 : ℝ) < 16)]
    norm_num
    linarith [hq.1]
  have hm1 : |(pairThreeProb tilt)⁻¹| ≤ 16 := by
    rw [abs_of_nonneg hm10]
    exact hm1hi
  have hm20 : 0 ≤ (pairThreeProb tilt)⁻¹ * (2 / tilt) :=
    mul_nonneg hm10 (div_nonneg (by norm_num) hp.le)
  have hm2 : |(pairThreeProb tilt)⁻¹ * (2 / tilt)| ≤ 200 := by
    rw [abs_of_nonneg hm20]
    exact (holdP_height_drift_mem_window hp0 hp1).2
  have hγ := gamma_holdStepP_pos
  have h := fpDistP_location_bound_core tilt htilt0 htilt1
    (tilt / 2) (pairThreeProb tilt)⁻¹
    ((pairThreeProb tilt)⁻¹ * (2 / tilt))
    c_renewalMassP C_renewalMassP gamma_holdStepP C_holdStepP
    (TaoCollatz.K_sqrtExp (gamma_holdStepP / 2))
    (by positivity) (by linarith) hm1 hm2
    c_renewalMassP_pos C_renewalMassP_pos gamma_holdStepP_pos C_holdStepP_pos
    (TaoCollatz.K_sqrtExp_pos (by linarith))
    (renewalMassP_bound_explicitC tilt htilt0 htilt1 hp0 hp1)
    (holdP_step_bound_explicitC tilt htilt0 htilt1 hp0 hp1)
    (TaoCollatz.sum_sqrt_exp_le_explicitC (by linarith : 0 < gamma_holdStepP / 2))
  intro s j l
  have hs := h s j l
  unfold C_fpLocationP c_fpLocationP
  exact hs

/-- Existential interface for the window-uniform tilted Lemma 7.7.  Both
constants are chosen before `p`. -/
theorem fpDistP_location_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ (s : ℕ) (j : ℕ) (l : ℤ),
        (fpDistP p (by linarith) (by linarith) s (j, l)).toReal
          ≤ C * (Real.exp (-c * ((l : ℝ) - s)) / Real.sqrt (1 + s))
              * TaoCollatz.Gweight (1 + s) (c * ((j : ℝ) - p / 2 * s)) :=
  ⟨c_fpLocationP, c_fpLocationP_pos, C_fpLocationP, C_fpLocationP_pos,
    fun p hp0 hp1 => fpDistP_location_bound_explicitC p (by linarith) (by linarith) hp0 hp1⟩

/-- Collapse the height coordinate in the tilted Lemma 7.7 bound.  The proof
is law-independent after the support statement; `r` only records the moving
horizontal centre. -/
theorem fpDistP_col_le_core (r c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hbound : ∀ (s : ℕ) (j : ℕ) (l : ℤ),
      (fpLaw s (j, l)).toReal
        ≤ C * (Real.exp (-c * ((l : ℝ) - s)) / Real.sqrt (1 + s))
            * TaoCollatz.Gweight (1 + s) (c * ((j : ℝ) - r * s))) :
    ∀ (s j : ℕ),
      ∑' l : ℤ, (fpLaw s (j, l)).toReal
        ≤ C * (Real.exp (-c) / (1 - Real.exp (-c)))
            * (TaoCollatz.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - r * s))
                  / Real.sqrt (1 + (s : ℝ))) := by
  have he1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hpos : (0 : ℝ) < 1 - Real.exp (-c) := by linarith
  intro s j
  set G : ℝ := TaoCollatz.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - r * s)) with hG
  have hGnn : 0 ≤ G := TaoCollatz.Gweight_nonneg _ _
  have hsq : (0 : ℝ) < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  set A : ℝ := C * G / Real.sqrt (1 + (s : ℝ)) with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hdom : HasSum
      (fun l : ℤ => A * (if (s : ℤ) < l then
        Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0))
      (A * (Real.exp (-c) / (1 - Real.exp (-c)))) :=
    (TaoCollatz.hasSum_int_shift_exp hc s).mul_left A
  have hptw : ∀ l : ℤ, (fpLaw s (j, l)).toReal
      ≤ A * (if (s : ℤ) < l then
          Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0) := by
    intro l
    by_cases hl : (s : ℤ) < l
    · rw [if_pos hl, hA, hG]
      calc
        (fpLaw s (j, l)).toReal
            ≤ C * (Real.exp (-c * ((l : ℝ) - (s : ℝ)))
                / Real.sqrt (1 + (s : ℝ)))
              * TaoCollatz.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - r * s)) :=
              hbound s j l
        _ = C * TaoCollatz.Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - r * s))
              / Real.sqrt (1 + (s : ℝ))
              * Real.exp (-c * ((l : ℝ) - (s : ℝ))) := by ring
    · rw [if_neg hl, mul_zero]
      have h0 : fpLaw s (j, l) = 0 := by
        by_contra h
        exact hl (fpDistP_support_snd_gt tilt htilt0 htilt1 s (j, l)
          (by rwa [PMF.mem_support_iff]))
      rw [h0, ENNReal.toReal_zero]
  have hslice : Summable (fun l : ℤ => (fpLaw s (j, l)).toReal) := by
    have h2d : Summable (fun p : ℕ × ℤ => (fpLaw s p).toReal) :=
      ENNReal.summable_toReal (by rw [(fpLaw s).tsum_coe]; exact ENNReal.one_ne_top)
    exact h2d.comp_injective (fun a b h => by simpa using h)
  calc
    ∑' l : ℤ, (fpLaw s (j, l)).toReal
        ≤ ∑' l : ℤ, A * (if (s : ℤ) < l then
            Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0) :=
          hslice.tsum_le_tsum hptw hdom.summable
    _ = A * (Real.exp (-c) / (1 - Real.exp (-c))) := hdom.tsum_eq
    _ = C * (Real.exp (-c) / (1 - Real.exp (-c)))
          * (G / Real.sqrt (1 + (s : ℝ))) := by rw [hA]; ring

/-- Uniform constant for the tilted first-passage column marginal. -/
noncomputable def C_fpColP : ℝ :=
  C_fpLocationP * (Real.exp (-c_fpLocationP) / (1 - Real.exp (-c_fpLocationP)))

theorem C_fpColP_pos : 0 < C_fpColP := by
  have hc := c_fpLocationP_pos
  have he1 : Real.exp (-c_fpLocationP) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  unfold C_fpColP
  exact mul_pos C_fpLocationP_pos (div_pos (Real.exp_pos _) (by linarith))

/-- Uniform tilted first-passage column marginal, with explicit constants. -/
theorem fpDistP_col_le_explicitC
    (hp0 : 1 / 5 ≤ tilt) (hp1 : tilt ≤ 3 / 5) :
    ∀ (s j : ℕ),
      ∑' l : ℤ, (fpLaw s (j, l)).toReal
        ≤ C_fpColP
            * (TaoCollatz.Gweight (1 + (s : ℝ))
                (c_fpLocationP * ((j : ℝ) - tilt / 2 * s))
              / Real.sqrt (1 + (s : ℝ))) := by
  have h := fpDistP_col_le_core tilt htilt0 htilt1 (tilt / 2)
    c_fpLocationP C_fpLocationP c_fpLocationP_pos C_fpLocationP_pos
    (fpDistP_location_bound_explicitC tilt htilt0 htilt1 hp0 hp1)
  intro s j
  have hs := h s j
  unfold C_fpColP
  exact hs

/-- Existential interface for the tilted first-passage column marginal. -/
theorem fpDistP_col_le :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5), ∀ (s j : ℕ),
        ∑' l : ℤ, (fpDistP p (by linarith) (by linarith) s (j, l)).toReal
          ≤ C * (TaoCollatz.Gweight (1 + (s : ℝ))
              (c * ((j : ℝ) - p / 2 * s)) / Real.sqrt (1 + (s : ℝ))) :=
  ⟨c_fpLocationP, c_fpLocationP_pos, C_fpColP, C_fpColP_pos,
    fun p hp0 hp1 => fpDistP_col_le_explicitC p (by linarith) (by linarith) hp0 hp1⟩

end

end TaoCollatz.Sec7P
