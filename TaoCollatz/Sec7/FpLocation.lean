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
