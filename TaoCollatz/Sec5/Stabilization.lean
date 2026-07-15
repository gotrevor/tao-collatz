import TaoCollatz.Sec5.ApproxFormula
import TaoCollatz.Sec6.MixingFromDecay

/-!
# §5 — Proposition 1.11 (stabilization), the C9 assembly

`stabilization` (Prop 1.11) is the spine's key input.  Its proof composes the two upstream cruxes:

* **C8** `first_passage_approx` (Prop 5.2 / (5.8)) — the approximate first-passage formula
  `ℙ(Pass_x(N_y) ∈ E) = approxMainTerm x E y + O(log^{-c} x)`, uniformly over odd `E ⊆ [1,x]`;
* **C10** `fine_scale_mixing` (Prop 1.14) — fine-scale mixing of the Syracuse density.

Because `first_passage_approx` lives in `Sec5.ApproxFormula` (which imports `Sec5.FirstPassage`) and
`fine_scale_mixing` lives in `Sec6.MixingFromDecay`, the assembly cannot sit in `FirstPassage.lean`
(that would be an import cycle).  The `stabilization` pin therefore RELOCATES here — **the statement is
byte-identical** to the former `FirstPassage.lean` pin (RATIFY-3); only its file moves, which the
statement differ explicitly anticipates ("pins get relocated").  `Sec5/Stabilization.lean` is added to
the differ's `SEARCH_FILES` so the WATCH follows the pin.

## The assembly (SEAM TEST — directive step 1)

The two windows in the dTV are exactly C8's two `y`-values: `y = x^α` gives `logUnifOdd (x^α) (x^{α²})`
and `y = x^{α²}` gives `logUnifOdd (x^{α²}) (x^{α³})`.  So:

1. **Conjunct 1** (non-passage rarity) is *character-identical* to `first_passage_nonescape` (C7,
   PROVED) — discharged directly.
2. **Conjunct 2** (passage-location stability) reduces, via the signed/Hahn decomposition of the two
   pushforwards (`dTV_passLoc_event_witness`, a structural on-path rib), to a single odd event
   `E ⊆ [1,x]`; C8 controls `ℙ(Pass ∈ E)` by `approxMainTerm x E y` in each window, and the
   window-stability of the main term (`approxMainTerm_window_stable`, the rib where C10 enters) closes
   the gap.

The two ribs are named `sorry`s: they turn the C9 seam into visible, attackable holes.  This lap is the
seam probe — it verifies the C8 interface (odd `E ⊆ [1,x]`, the two `y`-windows, the `log^{-c}`
normaliser) actually composes with the dTV structure.  **It does.**
-/

open scoped ENNReal

namespace TaoCollatz

/-- Pushforward–expectation identity for indicators: the `μ.map φ`-probability of an event `E`
equals the `μ`-probability of its `φ`-preimage.  `(μ.map φ).expect 𝟙_E = μ.expect 𝟙_{φ ∈ E}`. -/
theorem expect_map_indicator {α β : Type*} (μ : PMF α) (φ : α → β) (E : Set β) :
    (μ.map φ).expect (Set.indicator E 1)
      = μ.expect (Set.indicator {a | φ a ∈ E} 1) := by
  classical
  unfold PMF.expect
  rw [← PMF.toReal_tsum_mul_ofReal (μ.map φ) (Set.indicator E 1)
        (fun b => Set.indicator_nonneg (fun _ _ => zero_le_one) b),
      PMF.tsum_map_mul μ φ (fun b => ENNReal.ofReal (Set.indicator E 1 b)),
      PMF.toReal_tsum_mul_ofReal μ (fun a => Set.indicator E 1 (φ a))
        (fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) (φ a))]
  rfl

/-- Every passage location of an odd start is odd (Syracuse iterate of an odd, or the default `1`). -/
theorem passLoc_odd (xn N : ℕ) (hN : N % 2 = 1) : passLoc xn N % 2 = 1 := by
  unfold passLoc
  split
  · exact syr_iterate_odd N _ hN
  · rfl

/-- The passage location is `≤ xn` (when it passes) or the default `1`. -/
theorem passLoc_le (xn N : ℕ) : passLoc xn N ≤ xn ∨ passLoc xn N = 1 := by
  unfold passLoc
  split
  · exact Or.inl (Nat.sInf_mem ‹passes xn N›)
  · exact Or.inr rfl

/-- The real bound `(passLoc ⌊x⌋₊ N : ℝ) ≤ x` for `x ≥ 1`. -/
theorem passLoc_le_cast (N : ℕ) (x : ℝ) (hx : 1 ≤ x) : (passLoc ⌊x⌋₊ N : ℝ) ≤ x := by
  rcases passLoc_le ⌊x⌋₊ N with h | h
  · calc (passLoc ⌊x⌋₊ N : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h
      _ ≤ x := Nat.floor_le (by linarith)
  · rw [h]; simpa using hx

/-- **dTV → single-event reduction** for the two passage-location pushforwards (structural, on-path).
Both `P₁ = (logUnifOdd (x^α) (x^{α²})).map (passLoc ⌊x⌋₊)` and
`P₂ = (logUnifOdd (x^{α²}) (x^{α³})).map (passLoc ⌊x⌋₊)` are supported on odd naturals `≤ x`
(`passLoc` returns an odd Syracuse iterate `≤ x`, or the default `1`).  Hence the Hahn set
`{a | P₁ a ≥ P₂ a}`, intersected with the support, is an odd event `E ⊆ [1,x]` witnessing
`dTV(P₁,P₂) = 2·|P₁(E) − P₂(E)|`; we only need `≤`.  The event probabilities are written in base-measure
`expect` form (`P_i(E) = μ_i.expect 𝟙_{passLoc ∈ E}`) so they plug straight into C8.

**[C9 SEAM PROBE — sorried rib.]** Content: the tsum sign-split `∑|P₁−P₂| = (P₁−P₂)(E⁺)+(P₂−P₁)(E⁻)`
plus the `passLoc` support fact (odd `≤ x`).  No paper input; pure measure theory. -/
theorem dTV_passLoc_event_witness (x : ℝ) (hx : 1 ≤ x) :
    ∃ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) ∧
      PMF.dTV ((logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).map (passLoc ⌊x⌋₊))
              ((logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).map (passLoc ⌊x⌋₊))
        ≤ 2 * |(logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).expect
                    (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
                - (logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).expect
                    (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)| := by
  classical
  set P₁ := (logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).map (passLoc ⌊x⌋₊) with hP1
  set P₂ := (logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).map (passLoc ⌊x⌋₊) with hP2
  -- The two windows are `≥ 1`, so their base measures are supported on odds (`logUnifOdd_support_le`).
  have hone : ∀ z : ℝ, 0 ≤ z → (1 : ℝ) ≤ x ^ z := fun z hz => by
    calc (1 : ℝ) = x ^ (0 : ℝ) := (Real.rpow_zero x).symm
      _ ≤ x ^ z := Real.rpow_le_rpow_of_exponent_le hx hz
  have hhi1 : (1 : ℝ) ≤ x ^ alpha ^ 2 := hone _ (by positivity)
  -- Pushforward support: a positive-mass value is odd and `≤ x`.
  have hsupp1 : ∀ M : ℕ, P₁ M ≠ 0 → M % 2 = 1 ∧ (M : ℝ) ≤ x := by
    intro M hM
    have hmem : M ∈ P₁.support := hM
    rw [hP1, PMF.mem_support_map_iff] at hmem
    obtain ⟨N, hNsupp, hNM⟩ := hmem
    have hNodd : N % 2 = 1 := (logUnifOdd_support_le hhi1 hNsupp).1
    subst hNM
    exact ⟨passLoc_odd _ _ hNodd, passLoc_le_cast _ _ hx⟩
  -- Summability + total mass of the two real densities.
  have hg : Summable (fun v => (P₁ v).toReal) :=
    ENNReal.summable_toReal (by rw [P₁.tsum_coe]; exact ENNReal.one_ne_top)
  have hh : Summable (fun v => (P₂ v).toReal) :=
    ENNReal.summable_toReal (by rw [P₂.tsum_coe]; exact ENNReal.one_ne_top)
  have hsg : ∑' v, (P₁ v).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun v => P₁.apply_ne_top v), P₁.tsum_coe]; simp
  have hsh : ∑' v, (P₂ v).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun v => P₂.apply_ne_top v), P₂.tsum_coe]; simp
  have hf : Summable (fun v => (P₁ v).toReal - (P₂ v).toReal) := hg.sub hh
  have hsf : ∑' v, ((P₁ v).toReal - (P₂ v).toReal) = 0 := by
    rw [hg.tsum_sub hh, hsg, hsh]; ring
  refine ⟨{M : ℕ | M % 2 = 1 ∧ (M : ℝ) ≤ x ∧ (P₂ M).toReal ≤ (P₁ M).toReal}, ?_, ?_⟩
  · intro M hM
    exact ⟨hM.1, by have := hM.1; omega, hM.2.1⟩
  · set E := {M : ℕ | M % 2 = 1 ∧ (M : ℝ) ≤ x ∧ (P₂ M).toReal ≤ (P₁ M).toReal} with hEdef
    -- event masses ↔ base-measure expectations
    have hEexp : ∀ μ : PMF ℕ,
        ∑' v, Set.indicator E (fun w => (μ w).toReal) v = μ.expect (Set.indicator E 1) := by
      intro μ
      unfold PMF.expect
      refine tsum_congr fun v => ?_
      by_cases hv : v ∈ E
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]; simp
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]; simp
    have hD1 : ∑' v, Set.indicator E (fun w => (P₁ w).toReal) v
        = (logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).expect
            (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1) := by
      rw [hEexp P₁, hP1, expect_map_indicator]
    have hD2 : ∑' v, Set.indicator E (fun w => (P₂ w).toReal) v
        = (logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).expect
            (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1) := by
      rw [hEexp P₂, hP2, expect_map_indicator]
    -- pointwise Hahn identity: `|g − h| = 2·(𝟙_E g − 𝟙_E h) − (g − h)`
    have key : ∀ v, |(P₁ v).toReal - (P₂ v).toReal|
        = 2 * (Set.indicator E (fun w => (P₁ w).toReal) v
               - Set.indicator E (fun w => (P₂ w).toReal) v)
          - ((P₁ v).toReal - (P₂ v).toReal) := by
      intro v
      by_cases hv : v ∈ E
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv,
            abs_of_nonneg (by have := hv.2.2; linarith)]; ring
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
        have hle : (P₁ v).toReal ≤ (P₂ v).toReal := by
          by_cases hox : v % 2 = 1 ∧ (v : ℝ) ≤ x
          · have hc : ¬ ((P₂ v).toReal ≤ (P₁ v).toReal) := fun hc => hv ⟨hox.1, hox.2, hc⟩
            linarith [not_le.mp hc]
          · have h0 : P₁ v = 0 := by
              by_contra hne; exact hox (hsupp1 v hne)
            rw [h0]; simp
        rw [abs_of_nonpos (by linarith)]; ring
    have hIndG : Summable (Set.indicator E (fun w => (P₁ w).toReal)) := hg.indicator E
    have hIndH : Summable (Set.indicator E (fun w => (P₂ w).toReal)) := hh.indicator E
    have hFsum : Summable (fun v => 2 * (Set.indicator E (fun w => (P₁ w).toReal) v
                    - Set.indicator E (fun w => (P₂ w).toReal) v)) :=
      Summable.mul_left 2 (hIndG.sub hIndH)
    calc PMF.dTV P₁ P₂
        = ∑' v, |(P₁ v).toReal - (P₂ v).toReal| := rfl
      _ = ∑' v, (2 * (Set.indicator E (fun w => (P₁ w).toReal) v
                      - Set.indicator E (fun w => (P₂ w).toReal) v)
                 - ((P₁ v).toReal - (P₂ v).toReal)) := tsum_congr key
      _ = (∑' v, 2 * (Set.indicator E (fun w => (P₁ w).toReal) v
                      - Set.indicator E (fun w => (P₂ w).toReal) v))
          - ∑' v, ((P₁ v).toReal - (P₂ v).toReal) := hFsum.tsum_sub hf
      _ = 2 * (∑' v, Set.indicator E (fun w => (P₁ w).toReal) v)
          - 2 * (∑' v, Set.indicator E (fun w => (P₂ w).toReal) v) := by
            rw [tsum_mul_left, hIndG.tsum_sub hIndH, hsf]; ring
      _ = 2 * ((logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).expect
                  (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
               - (logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).expect
                  (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)) := by
            rw [hD1, hD2]; ring
      _ ≤ 2 * |(logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).expect
                  (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
               - (logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).expect
                  (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)| := by
            gcongr; exact le_abs_self _

open Classical in
/-- Tao's window-independent quantity **`Z` (5.21)**:
`∑_{M∈E'} 3^{m₀}·ℙ(M = Syrac(ℤ/3^{m₀}ℤ) mod 3^{m₀}) / M`, where `E' = Eprime x E` and the Syracuse
law mod `3^{m₀}` is `syracZ (mZero x)`.  Crucially this depends only on `x` and `E` — **NOT on the
window `y`** (the paper, p.26: "`Z` does not depend on whether `y` equals `x^α` or `x^{α²}`").  That
`y`-independence is the entire content of the stabilization (Prop 1.11). -/
noncomputable def mainZ (x : ℝ) (E : Set ℕ) : ℝ :=
  ∑' M : ℕ, if Eprime x E M then
      (3 : ℝ) ^ mZero x * ((syracZ (mZero x)) (M : ZMod (3 ^ mZero x))).toReal / (M : ℝ)
    else 0

open Classical in
/-- The per-`n` summand of `approxMainTerm` (5.8): `∑_{ā∈𝒜⁽ⁿ⁻ᵐ⁰⁾} ∑_{M∈E'} ℙ(Aff_ā(N_y)=M)`, i.e. the
contribution of a single first-passage time `n ∈ I_y`. -/
noncomputable def perNTerm (x : ℝ) (E : Set ℕ) (y : ℝ) (n : ℕ) : ℝ :=
  ∑' (ā : Fin (n - mZero x) → ℕ), ∑' (M : ℕ),
    if goodTuple x (n - mZero x) ā ∧ Eprime x E M then
      (∑' N, if 3 ^ (n - mZero x) * N + fnat (n - mZero x) ā = M * 2 ^ pre ā (n - mZero x)
             then (logUnifOdd y (y ^ alpha)) N else 0).toReal
    else 0

/-- `approxMainTerm` is the sum of its per-`n` terms over `I_y` (definitional unfolding of (5.8)). -/
theorem approxMainTerm_eq_sum_perNTerm (x : ℝ) (E : Set ℕ) (y : ℝ) :
    approxMainTerm x E y = ∑ n ∈ Iy x y, perNTerm x E y n := rfl

/-- **Affine single-point selection** — the ENNReal core of Tao's (5.19).  The affine equation
`a·N + b = c` in `N` has at most one solution when `a > 0` (the map `N ↦ a·N + b` is injective), so if
`N₀` solves it the masked tsum collapses to the single mass `g N₀`. -/
theorem tsum_ite_affine_of_sol (a b c N₀ : ℕ) (ha : 0 < a) (hsol : a * N₀ + b = c)
    (g : ℕ → ℝ≥0∞) :
    (∑' N, if a * N + b = c then g N else 0) = g N₀ := by
  rw [tsum_eq_single N₀, if_pos hsol]
  intro N hN
  rw [if_neg]
  intro h
  exact hN (Nat.eq_of_mul_eq_mul_left ha (by omega))

/-- **Affine no-solution collapse** — if the affine equation `a·N + b = c` has no solution in `N`, the
masked tsum vanishes.  (Companion of `tsum_ite_affine_of_sol`.) -/
theorem tsum_ite_affine_of_nosol (a b c : ℕ) (g : ℕ → ℝ≥0∞)
    (hns : ∀ N, ¬ (a * N + b = c)) :
    (∑' N, if a * N + b = c then g N else 0) = 0 := by
  rw [tsum_congr (fun N => if_neg (hns N)), tsum_zero]

/-- **Point-mass value of `logUnifOdd`** (real form).  On the window, `logUnifOdd lo hi` puts real
mass `(N)⁻¹ / windowMass lo hi` at `N` (`windowMass = ∑_{M∈W} 1/M`, the harmonic normaliser `D`); off
the window the mass is `0`.  This is the (5.19) evaluation of the single point mass produced by
`perNTerm_pointmass`. -/
theorem logUnifOdd_apply_toReal {lo hi : ℝ} (h : (logWindow lo hi).Nonempty) (N : ℕ) :
    (logUnifOdd lo hi N).toReal
      = if N ∈ logWindow lo hi then (N : ℝ)⁻¹ / windowMass lo hi else 0 := by
  rw [logUnifOdd_apply_of_nonempty h]
  by_cases hN : N ∈ logWindow lo hi
  · rw [if_pos hN, if_pos hN, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        windowMass]
    have hne : ∀ M ∈ logWindow lo hi, (M : ℝ≥0∞) ≠ 0 := by
      intro M hM
      simp only [logWindow, Finset.mem_filter] at hM
      have : M % 2 = 1 := hM.2.1
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    congr 1
    rw [ENNReal.toReal_sum fun M hM => by
      rw [ne_eq, ENNReal.inv_eq_top, Nat.cast_eq_zero]; exact fun h0 => hne M hM (by simp [h0])]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · rw [if_neg hN, if_neg hN]; simp

/-- Point-mass value on the window (the `if_pos` case of `logUnifOdd_apply_toReal`). -/
theorem logUnifOdd_apply_toReal_of_mem {lo hi : ℝ} (h : (logWindow lo hi).Nonempty)
    {N : ℕ} (hN : N ∈ logWindow lo hi) :
    (logUnifOdd lo hi N).toReal = (N : ℝ)⁻¹ / windowMass lo hi := by
  rw [logUnifOdd_apply_toReal h, if_pos hN]

open Classical in
/-- **(5.19) single-value reduction of `perNTerm`.**  The inner affine mass
`ℙ(Aff_ā(N_y)=M) = ∑' N, if 3^{n−m₀}·N + fnat = M·2^{pre ā} then logUnifOdd N else 0` collapses to the
mass at the unique solving `N` — which exists exactly when `3^{n−m₀} ∣ (M·2^{pre ā} − fnat)` with
`fnat ≤ M·2^{pre ā}`, and then equals `N* = (M·2^{pre ā} − fnat)/3^{n−m₀}`.  So `perNTerm` is a double
sum of point masses.  This is the first step of `perNTerm_eval`: it discharges the affine reindex,
leaving the harmonic-mass evaluation of `logUnifOdd(N*)` (5.19 tail) and the `Z`-reduction (5.20). -/
theorem perNTerm_pointmass (x : ℝ) (E : Set ℕ) (y : ℝ) (n : ℕ) :
    perNTerm x E y n
      = ∑' (ā : Fin (n - mZero x) → ℕ), ∑' (M : ℕ),
          if goodTuple x (n - mZero x) ā ∧ Eprime x E M then
            (if 3 ^ (n - mZero x) ∣ (M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā)
                ∧ fnat (n - mZero x) ā ≤ M * 2 ^ pre ā (n - mZero x) then
              (logUnifOdd y (y ^ alpha)
                ((M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā) / 3 ^ (n - mZero x))).toReal
            else 0)
          else 0 := by
  unfold perNTerm
  set k := n - mZero x with hk
  refine tsum_congr fun ā => tsum_congr fun M => ?_
  by_cases hcond : goodTuple x k ā ∧ Eprime x E M
  · rw [if_pos hcond, if_pos hcond]
    set b := fnat k ā with hb
    set c := M * 2 ^ pre ā k with hc
    by_cases hsolv : 3 ^ k ∣ (c - b) ∧ b ≤ c
    · rw [if_pos hsolv]
      obtain ⟨hdvd, hle⟩ := hsolv
      congr 1
      refine tsum_ite_affine_of_sol (3 ^ k) b c ((c - b) / 3 ^ k) (by positivity) ?_ _
      rw [Nat.mul_div_cancel' hdvd]; omega
    · rw [if_neg hsolv,
          tsum_ite_affine_of_nosol (3 ^ k) b c _ (fun N hN => hsolv ⟨⟨N, by omega⟩, by omega⟩)]
      simp
  · rw [if_neg hcond, if_neg hcond]

/-- **`mainZ` is `O(1)`** — the y-free quantity `Z` (5.21) is bounded uniformly (it is a probability-
weighted harmonic average over `E'`, and `#E'·(mass/M)` telescopes to `O(1)`; equivalently `Z ≍
(log(4/3)/2)·ℙ(Pass∈E) = O(1)`).  Needed so the multiplicative `(5.19)`/`(5.9)` errors on `mainZ` stay
`O(log^{-c})`. -/
theorem mainZ_bound :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) → |mainZ x E| ≤ C := by
  sorry

open Classical in
/-- **The window-free harmonic content of the per-`n` term (5.20 LHS).**
`perNHarmonic x E n = 3^{n−m₀}·∑_ā∑_{M} [good ∧ E' ∧ affine-solvable] 2^{−a_{[1,n−m₀]}}/M`.  This is the
`perNTerm` numerator after the (5.19) single-value + harmonic-mass reduction, stripped of the
`1/windowMass = 1/D_y` normaliser.  By the (5.20) reduction it is `≈ mainZ` (window-independent): the
`2^{−pre ā}` weight IS the `iid geomHalf` mass, so `∑_ā[good, F(ā)≡M] 2^{−pre ā} = syracZ(n−m₀)(M) + whp`,
and `fine_scale_mixing` bridges `3^{n−m₀}·syracZ(n−m₀) ≈ 3^{m₀}·syracZ(m₀)` (Lemma 5.3, C10). -/
noncomputable def perNHarmonic (x : ℝ) (E : Set ℕ) (n : ℕ) : ℝ :=
  (3 : ℝ) ^ (n - mZero x) * ∑' (ā : Fin (n - mZero x) → ℕ), ∑' (M : ℕ),
    if goodTuple x (n - mZero x) ā ∧ Eprime x E M
        ∧ 3 ^ (n - mZero x) ∣ (M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā)
        ∧ fnat (n - mZero x) ā ≤ M * 2 ^ pre ā (n - mZero x)
    then ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹ / (M : ℝ) else 0

/-- **(5.19) harmonic reduction of `perNTerm`** — sub-lemma A of `perNTerm_eval`.  Each per-`n` term
equals its harmonic content divided by the harmonic normaliser `norm = ((α−1)/2)·log y`, up to a
*relative* `O(log^{-c}x)/norm` error.  Combines `perNTerm_pointmass` (affine → single point),
`logUnifOdd_apply_toReal` (point mass `= (N*)⁻¹/D_y`), `windowMass_estimate` (`D_y = norm + O(1)`, the
`1/D_y → 1/norm` swap), the `N* ∈ window` membership, and the `(N*)⁻¹ = 3^{n−m₀}/(M·2^{pre ā}−fnat) ≈
3^{n−m₀}/(M·2^{pre ā})` relative error (`fnat_lt_pow_mul`).
**[C9 leaf A — pure (5.19) analytic layer; does NOT consume C10.]** -/
theorem perNTerm_harmonic_approx :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNTerm x E y n - perNHarmonic x E n / ((alpha - 1) / 2 * Real.log y)|
            ≤ C * (Real.log x) ^ (-c) / ((alpha - 1) / 2 * Real.log y) := by
  sorry

open Classical in
/-- **Fine-scale harmonic content** — the intermediate between `perNHarmonic` and `mainZ` in the
(5.20) reduction.  It replaces `perNHarmonic`'s inner `2^{−pre ā}` good-tuple sum by the exact
`Syrac(ℤ/3^{n−m₀}ℤ)` mass at residue `M`:
`harmZfine x E n = ∑_{M∈E'} 3^{n−m₀}·ℙ(Syrac(ℤ/3^{n−m₀}ℤ) = M mod 3^{n−m₀}) / M`.
This is `perNHarmonic` *after* the geomHalf→`syracZ` reindex (sub-lemma B1) and *before* the
`fine_scale_mixing` scale-collapse to `mainZ` (sub-lemma B2).  Note it has the same shape as `mainZ`
but at the finer scale `n−m₀` in place of `m₀`. -/
noncomputable def harmZfine (x : ℝ) (E : Set ℕ) (n : ℕ) : ℝ :=
  ∑' M : ℕ, if Eprime x E M then
      (3 : ℝ) ^ (n - mZero x)
        * ((syracZ (n - mZero x)) (M : ZMod (3 ^ (n - mZero x)))).toReal / (M : ℝ)
    else 0

open Classical in
/-- **Tao's harmonic weight `c_n` (5.23)** — the `E'`-harmonic mass of a residue class mod `3^{n−m₀}`:
`c_n(X) = 3^{n−m₀}·∑_{M∈E', M ≡ X mod 3^{n−m₀}} 1/M`.  With it, the (5.20) LHS `perNHarmonic` is the
`Geom(2)^{n−m₀}`-expectation `𝔼[1_good · c_n(F_{n−m₀}(ā) mod 3^{n−m₀})]` (5.22), and the intermediate
`harmZfine = 𝔼[c_n(Syrac(ℤ/3^{n−m₀}ℤ))] = ∑_X syracZ(n−m₀)(X)·c_n(X)` (drop the `1_good` restriction). -/
noncomputable def cn (x : ℝ) (E : Set ℕ) (n : ℕ) (X : ZMod (3 ^ (n - mZero x))) : ℝ :=
  (3 : ℝ) ^ (n - mZero x)
    * ∑' M : ℕ, if Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X then (M : ℝ)⁻¹ else 0

/-- **Crude harmonic-weight bound** (`c_n(X) ≪ log^{0.7}x`) — the shared self-contained prerequisite of
B1 and B2.  This is a *weakening* of Tao's Lemma 5.3 (`c_n ≪ 1`, which needs the delicate `c_{n,a}`
split over `ℕ^{m₀}` with the extra CRT modulus `2^{a_{[1,m₀]}+1}`).  We only need the crude bound: the
`E'` window (5.10) is `exp(±log^{0.7}x)·(4/3)^{m₀}·x`, so a SINGLE integral test (5.25,
`harmonic_ap_integral_bound`) on the residue class mod `3^{n−m₀}` gives
`c_n(X) = 3^{n−m₀}·∑_{M∈E', M≡X} 1/M ≤ log(M₁/M₀) + 3^{n−m₀}/M₀ ≤ 2·log^{0.7}x + o(1) ≤ C·log^{0.7}x`.
This SUFFICES downstream because both consumers have adjustable/faster-decaying partners:
**B1** pairs it with `approx_good_tuple_whp` (decay `log^{−1}x`, so `log^{0.7}·log^{−1} = log^{−0.3}`),
**B2** pairs it with `fine_scale_mixing`'s `osc ≤ C·m₀^{−A}` for EVERY `A>0` (take `A>0.7`).
**[Self-contained integral-test estimate; does NOT consume C10.  NOT Lemma 5.3 — a sufficient crude
weakening.  Used as `sup_X c_n ≤ C·log^{0.7}x` by both B1 and B2.]** -/
theorem cn_bound :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          ∀ X : ZMod (3 ^ (n - mZero x)), cn x E n X ≤ C * (Real.log x) ^ (0.7 : ℝ) := by
  sorry

/-- **(5.20) sub-lemma B1 — geomHalf → `syracZ` reindex.**  `perNHarmonic` (whose inner weight is the
`2^{−pre ā}` iid-geomHalf mass over *good, affine-solvable* tuples) agrees with `harmZfine` (the exact
`Syrac(ℤ/3^{n−m₀}ℤ)` mass) up to `O(log^{-c}x)`.  Content: `syracZ_eq_rev_fnat` writes `syracZ(n−m₀)`
as the pushforward of `iid geomHalf` under `ā ↦ fnat·2^{−pre ā} mod 3^{n−m₀}`, so the affine congruence
`3^{n−m₀} ∣ M·2^{pre ā}−fnat` is exactly `(map value of ā) = (M : ZMod 3^{n−m₀})`; and for good `ā`,
`M ∈ E'` the `ℕ`-subtraction guard `fnat ≤ M·2^{pre ā}` is automatic
(`fnat < 3^{n−m₀}·2^{pre ā} ≤ M·2^{pre ā}` via `fnat_lt_pow_mul` and `3^{n−m₀} ≤ M`).  The residual over
*non-good* tuples is the good-tuple whp error `approx_good_tuple_whp`.
**[C9 leaf B1 — pure reindex + whp; does NOT consume C10.]** -/
theorem perNHarmonic_eq_harmZfine_approx :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNHarmonic x E n - harmZfine x E n| ≤ C * (Real.log x) ^ (-c) := by
  sorry

/-- **(5.20) sub-lemma B2 — the `fine_scale_mixing` scale bridge (THE C10 SEAM).**  The fine-scale
harmonic content `harmZfine = ∑_X syracZ(n−m₀)(X)·c_n(X)` agrees with `mainZ = ∑_{X'} syracZ(m₀)(X')·
c_n^{coarse}(X')` up to `O(log^{-c}x)`.  Route (Tao p.26, verified against PDF 2026-07-15): the coarse
weight is the `3^{m₀}`-fiber **average** of `c_n` (`d_n(X') = 3^{m₀−(n−m₀)}·∑_{X≡X'} c_n(X)`), and
`syracZ(m₀)` is the marginal of `syracZ(n−m₀)` (`syracZ_map_cast`), so
`harmZfine − mainZ = ∑_X [syracZ(n−m₀)(X) − fiber_avg(X)]·c_n(X)` with `fiber_avg(X) =
3^{m₀−(n−m₀)}·syracZ(m₀)(X mod 3^{m₀})`.  Bound by **L¹×L∞ Hölder**:
`|harmZfine − mainZ| ≤ (sup_X c_n(X))·∑_X|syracZ(n−m₀)(X) − fiber_avg(X)| = (sup c_n)·osc m₀ (n−m₀)`,
then `sup c_n ≤ C·log^{0.7}x` by the crude `cn_bound` and `osc ≤ C'·m₀^{−A}` by **Prop 1.14
(`fine_scale_mixing`, C10)** for EVERY `A>0` — applicable since `m₀ ≤ n−m₀` (`two_mZero_le_of_mem_Iy`).
Taking `A > 0.7 + c`: `≤ C''·log^{0.7}x·(10⁻⁵ log x)^{−A} ≤ C‴·log^{−c}x`.  **NO M-equidistribution
needed** — Tao routes the whole thing through the sup/osc pair, not through equidistributing `M`.
**[C9 leaf B2 — the C10 seam; the sole isolated C10 hole in C9.]** -/
theorem harmZfine_to_mainZ :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |harmZfine x E n - mainZ x E| ≤ C * (Real.log x) ^ (-c) := by
  sorry

/-- **(5.20) harmonic → `Z` reduction** — sub-lemma B of `perNTerm_eval`, **the sole C10 consumer**.
The window-free harmonic content agrees with Tao's `Z` (5.21) up to `O(log^{-c}x)`.  **PROVED** from the
geomHalf→`syracZ` reindex `perNHarmonic_eq_harmZfine_approx` (B1) and the `fine_scale_mixing` scale
bridge `harmZfine_to_mainZ` (B2, the C10 seam) via the triangle through the shared `harmZfine`:
`perNHarmonic ≈ harmZfine ≈ mainZ`.  All of C10's involvement in C9 is now isolated to B2. -/
theorem harmonic_to_Z :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNHarmonic x E n - mainZ x E| ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨c1, C1, x1, hc1, hC1, h1⟩ := perNHarmonic_eq_harmZfine_approx
  obtain ⟨c2, C2, x2, hc2, hC2, h2⟩ := harmZfine_to_mainZ
  refine ⟨min c1 c2, C1 + C2, max (max x1 x2) (Real.exp 1),
    lt_min hc1 hc2, by positivity, fun x hx E hE y hy n hn => ?_⟩
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  set L := Real.log x with hLdef
  have hLc1 : L ^ (-c1) ≤ L ^ (-(min c1 c2)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (min_le_left _ _))
  have hLc2 : L ^ (-c2) ≤ L ^ (-(min c1 c2)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (min_le_right _ _))
  have hp1 := h1 x hx1 E hE y hy n hn
  have hp2 := h2 x hx2 E hE y hy n hn
  calc |perNHarmonic x E n - mainZ x E|
      ≤ |perNHarmonic x E n - harmZfine x E n| + |harmZfine x E n - mainZ x E| :=
        abs_sub_le _ _ _
    _ ≤ C1 * L ^ (-c1) + C2 * L ^ (-c2) := add_le_add hp1 hp2
    _ ≤ C1 * L ^ (-(min c1 c2)) + C2 * L ^ (-(min c1 c2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hLc1 hC1.le)
          (mul_le_mul_of_nonneg_left hLc2 hC2.le)
    _ = (C1 + C2) * L ^ (-(min c1 c2)) := by ring

/-- **Per-`n` evaluation (5.19)+(5.20).**  For each `n ∈ I_y`, the per-`n` term equals the
window-independent `mainZ x E` divided by the harmonic normaliser `((α−1)/2)·log y`, up to a *relative*
`O(log^{-c} x)` error.  **PROVED** from the (5.19) harmonic reduction `perNTerm_harmonic_approx` (leaf A),
the (5.20) `Z`-reduction `harmonic_to_Z` (leaf B, the C10 seam), and `windowMass_estimate`
(`D_y = (α−1)/2·log y + O(1)`): the harmonic content `perNHarmonic ≈ mainZ` and dividing by
`windowMass ≈ norm` gives `perNTerm ≈ mainZ/norm` (the `windowMass`↔`norm` swap costs only
`O(1/norm²) = O(L^{-2}) ≤ L^{-1-c}`). -/
theorem perNTerm_eval :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNTerm x E y n - mainZ x E / ((alpha - 1) / 2 * Real.log y)|
            ≤ C * (Real.log x) ^ (-c) / ((alpha - 1) / 2 * Real.log y) := by
  obtain ⟨cA, CA, xA, hcA, hCA, hA⟩ := perNTerm_harmonic_approx
  obtain ⟨cB, CB, xB, hcB, hCB, hB⟩ := harmonic_to_Z
  refine ⟨min cA cB, CA + CB, max (max xA xB) (Real.exp 1),
    lt_min hcA hcB, by positivity, fun x hx E hE y hy n hn => ?_⟩
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxA : xA ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxB : xB ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hL0 : 0 < Real.log x := by linarith
  set L := Real.log x with hLdef
  have halpha0 : (0 : ℝ) < alpha := by norm_num [alpha]
  have hLy : 0 < Real.log y := by
    rcases hy with rfl | rfl
    · rw [Real.log_rpow hxpos]; exact mul_pos halpha0 hL0
    · rw [Real.log_rpow hxpos]; exact mul_pos (pow_pos halpha0 2) hL0
  have hnormpos : 0 < (alpha - 1) / 2 * Real.log y := mul_pos (by norm_num [alpha]) hLy
  set c := min cA cB with hcdef
  have hccA : c ≤ cA := min_le_left _ _
  have hccB : c ≤ cB := min_le_right _ _
  have hLcA : L ^ (-cA) ≤ L ^ (-c) := Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg hccA)
  have hLcB : L ^ (-cB) ≤ L ^ (-c) := Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg hccB)
  have hApiece := hA x hxA E hE y hy n hn
  have hBpiece := hB x hxB E hE y hy n hn
  set norm := (alpha - 1) / 2 * Real.log y with hnormdef
  -- clean two-term split through the shared harmonic content
  have hsplit : perNTerm x E y n - mainZ x E / norm
      = (perNTerm x E y n - perNHarmonic x E n / norm)
        + (perNHarmonic x E n - mainZ x E) / norm := by
    field_simp; ring
  calc |perNTerm x E y n - mainZ x E / norm|
      ≤ |perNTerm x E y n - perNHarmonic x E n / norm|
        + |(perNHarmonic x E n - mainZ x E) / norm| := by rw [hsplit]; exact abs_add_le _ _
    _ ≤ CA * L ^ (-cA) / norm + CB * L ^ (-cB) / norm := by
        refine add_le_add hApiece ?_
        rw [abs_div, abs_of_pos hnormpos]
        exact div_le_div_of_nonneg_right hBpiece hnormpos.le
    _ ≤ CA * L ^ (-c) / norm + CB * L ^ (-c) / norm := by
        refine add_le_add ?_ ?_
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLcA hCA.le) hnormpos.le
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLcB hCB.le) hnormpos.le
    _ = (CA + CB) * L ^ (-c) / norm := by ring

/-- **Interval count (5.9).**  `#I_y = (1+O(log^{-c}x))·(α−1)/log(4/3)·log y`, rendered as the ratio to
the harmonic normaliser: `#I_y / (((α−1)/2)·log y) = 2/log(4/3) + O(log^{-c}x)`.  This is the pure
lattice-point count `#{n∈[IyLo,IyHi]}` = interval length `+ O(1)` (via `IyHi−IyLo = (α−1)log y/log(4/3)
− 2log^{0.8}x`), whose ratio telescopes the window into the **y-free** `2/log(4/3)`. -/
theorem Iy_count_ratio :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        |((Iy x y).card : ℝ) / ((alpha - 1) / 2 * Real.log y) - 2 / Real.log (4 / 3)|
          ≤ C * (Real.log x) ^ (-c) := by
  sorry

/-- **(5.18)–(5.21) + (5.9) evaluation of the affine main term.**  For `y ∈ {x^α, x^{α²}}`,
`approxMainTerm x E y = (2 / log(4/3))·mainZ x E + O(log^{-c} x)`.  This subsumes Tao's pp.25–27
chain: the single-value mass formula (5.19)
`ℙ(Aff_ā(N_y)=M) = (1+O(x^{-c}))·2^{-|ā|}·3^{n−m₀} / (((α−1)/2)·log y · M)`; the harmonic-sum reduction
(5.20)→`Z` — **where Lemma 5.3 (`c_n(X)≪1`) and Prop 1.14 (`fine_scale_mixing`, C10) are consumed**;
and the interval count `#I_y` (5.9) `= (1+O(log^{-c}x))·(α−1)/log(4/3)·log y`, whose ratio to the
`((α−1)/2)·log y` normaliser telescopes to the **window-free** `2/log(4/3)`.

**[C9 CRUX — the sole remaining C9 hole; this is where C10 enters.]**  Target is `y`-independent (`Z`),
which is the faithful rendering of the paper's cancellation; `approxMainTerm_window_stable` below is a
one-line triangle over this. -/
theorem approxMainTerm_to_Z :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |approxMainTerm x E y - 2 / Real.log (4 / 3) * mainZ x E|
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨c1, C1, x1, hc1, hC1, h9⟩ := Iy_count_ratio
  obtain ⟨Cz, xz, hCz, hZb⟩ := mainZ_bound
  obtain ⟨c2, C2, x2, hc2, hC2, hp⟩ := perNTerm_eval
  have hlog43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have halpha0 : 0 < alpha := by norm_num [alpha]
  have halpha1 : 0 < alpha - 1 := by norm_num [alpha]
  have hb2 : (0 : ℝ) < 2 / Real.log (4 / 3) := by positivity
  refine ⟨min c1 c2, (2 / Real.log (4 / 3) + C1) * C2 + Cz * C1,
    max (max (max x1 xz) x2) (Real.exp 1), lt_min hc1 hc2, by nlinarith [hC1, hC2, hCz, hb2],
    fun x hx E hE y hy => ?_⟩
  -- thresholds
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : x1 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxz : xz ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hL0 : 0 < Real.log x := by linarith
  have hLy : 0 < Real.log y := by
    rcases hy with rfl | rfl
    · rw [Real.log_rpow hxpos]; exact mul_pos halpha0 hL0
    · rw [Real.log_rpow hxpos]; exact mul_pos (pow_pos halpha0 2) hL0
  set c := min c1 c2 with hc
  have hcc1 : c ≤ c1 := min_le_left _ _
  have hcc2 : c ≤ c2 := min_le_right _ _
  set L := Real.log x with hLdef
  have hLc1 : L ^ (-c1) ≤ L ^ (-c) := Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg hcc1)
  have hLc2 : L ^ (-c2) ≤ L ^ (-c) := Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg hcc2)
  have hLc1le1 : L ^ (-c1) ≤ 1 := by
    rw [show (1 : ℝ) = L ^ (0 : ℝ) from (Real.rpow_zero L).symm]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hc1.le])
  have hLcpos : 0 < L ^ (-c) := Real.rpow_pos_of_pos hL0 _
  set norm := (alpha - 1) / 2 * Real.log y with hnorm
  have hnormpos : 0 < norm := mul_pos (by linarith) hLy
  -- (5.9) ratio bound, and nonnegativity of the ratio
  have h9' := h9 x hx1 y hy
  set ratio := ((Iy x y).card : ℝ) / norm with hratio
  have hratio_nn : 0 ≤ ratio := by rw [hratio]; positivity
  have hratio_le : ratio ≤ 2 / Real.log (4 / 3) + C1 * L ^ (-c1) := by
    have := (abs_le.mp h9').2; linarith
  -- Structural split of the target through the shared `mainZ`.
  rw [approxMainTerm_eq_sum_perNTerm]
  have hsplit : (∑ n ∈ Iy x y, perNTerm x E y n) - 2 / Real.log (4 / 3) * mainZ x E
      = (∑ n ∈ Iy x y, (perNTerm x E y n - mainZ x E / norm))
        + mainZ x E * (ratio - 2 / Real.log (4 / 3)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hratio]; ring
  rw [hsplit]
  -- Part A: ∑|δ_n| ≤ ratio · C2 L^{-c2}
  have hPartA : (∑ n ∈ Iy x y, |perNTerm x E y n - mainZ x E / norm|)
      ≤ ratio * (C2 * L ^ (-c2)) := by
    calc (∑ n ∈ Iy x y, |perNTerm x E y n - mainZ x E / norm|)
        ≤ ∑ _n ∈ Iy x y, C2 * L ^ (-c2) / norm := by
          refine Finset.sum_le_sum fun n hn => ?_
          have := hp x hx2 E hE y hy n hn
          rw [hnorm, hLdef]; exact this
      _ = ((Iy x y).card : ℝ) * (C2 * L ^ (-c2) / norm) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ratio * (C2 * L ^ (-c2)) := by rw [hratio]; ring
  -- Two component bounds, then a numeric collapse.
  have ha1nn : 0 ≤ L ^ (-c1) := (Real.rpow_pos_of_pos hL0 _).le
  have ha2nn : 0 ≤ L ^ (-c2) := (Real.rpow_pos_of_pos hL0 _).le
  have hAbs : |∑ n ∈ Iy x y, (perNTerm x E y n - mainZ x E / norm)| ≤ ratio * (C2 * L ^ (-c2)) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) hPartA
  have hMZ : |mainZ x E * (ratio - 2 / Real.log (4 / 3))| ≤ Cz * (C1 * L ^ (-c1)) := by
    rw [abs_mul]
    exact mul_le_mul (hZb x hxz E hE) h9' (abs_nonneg _) hCz.le
  -- ratio·(C2 a2) ≤ (2/log43 + C1)·C2·a  and  Cz·(C1 a1) ≤ Cz·C1·a
  have hStepA : ratio * (C2 * L ^ (-c2)) ≤ (2 / Real.log (4 / 3) + C1) * C2 * L ^ (-c) := by
    have h1 : ratio * (C2 * L ^ (-c2))
        ≤ (2 / Real.log (4 / 3) + C1 * L ^ (-c1)) * (C2 * L ^ (-c2)) :=
      mul_le_mul_of_nonneg_right hratio_le (mul_nonneg hC2.le ha2nn)
    have h2 : (2 / Real.log (4 / 3) + C1 * L ^ (-c1)) * (C2 * L ^ (-c2))
        ≤ (2 / Real.log (4 / 3) + C1) * (C2 * L ^ (-c)) := by
      apply mul_le_mul _ (mul_le_mul_of_nonneg_left hLc2 hC2.le) (mul_nonneg hC2.le ha2nn)
        (by positivity)
      nlinarith [hLc1le1, hC1.le]
    calc ratio * (C2 * L ^ (-c2)) ≤ (2 / Real.log (4 / 3) + C1) * (C2 * L ^ (-c)) := le_trans h1 h2
      _ = (2 / Real.log (4 / 3) + C1) * C2 * L ^ (-c) := by ring
  have hStepB : Cz * (C1 * L ^ (-c1)) ≤ Cz * C1 * L ^ (-c) := by
    have : C1 * L ^ (-c1) ≤ C1 * L ^ (-c) := mul_le_mul_of_nonneg_left hLc1 hC1.le
    calc Cz * (C1 * L ^ (-c1)) ≤ Cz * (C1 * L ^ (-c)) := mul_le_mul_of_nonneg_left this hCz.le
      _ = Cz * C1 * L ^ (-c) := by ring
  calc |(∑ n ∈ Iy x y, (perNTerm x E y n - mainZ x E / norm))
          + mainZ x E * (ratio - 2 / Real.log (4 / 3))|
      ≤ |∑ n ∈ Iy x y, (perNTerm x E y n - mainZ x E / norm)|
        + |mainZ x E * (ratio - 2 / Real.log (4 / 3))| := abs_add_le _ _
    _ ≤ ratio * (C2 * L ^ (-c2)) + Cz * (C1 * L ^ (-c1)) := add_le_add hAbs hMZ
    _ ≤ (2 / Real.log (4 / 3) + C1) * C2 * L ^ (-c) + Cz * C1 * L ^ (-c) :=
        add_le_add hStepA hStepB
    _ = ((2 / Real.log (4 / 3) + C1) * C2 + Cz * C1) * L ^ (-c) := by ring

/-- **Lemma 5.3 + (5.18)–(5.21)** — window-stability of the affine main term.  `approxMainTerm x E y`
agrees across the two nested windows `y = x^α` and `y = x^{α²}` up to `O(log^{-c} x)`.  PROVED from
`approxMainTerm_to_Z` by the triangle inequality through the window-independent `mainZ x E`: both
windows evaluate to `(2/log(4/3))·mainZ x E + O(log^{-c} x)` with the **same** `mainZ`, so their
difference is `O(log^{-c} x)`. -/
theorem approxMainTerm_window_stable :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        |approxMainTerm x E (x ^ alpha) - approxMainTerm x E (x ^ alpha ^ 2)|
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨c, C, x₀, hc, hC, hZ⟩ := approxMainTerm_to_Z
  refine ⟨c, 2 * C, x₀, hc, by positivity, fun x hx E hE => ?_⟩
  have hmem1 : (x ^ alpha) ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ) := Set.mem_insert _ _
  have hmem2 : (x ^ alpha ^ 2) ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ) :=
    Set.mem_insert_of_mem _ rfl
  have h1 := hZ x hx E hE (x ^ alpha) hmem1
  have h2 := hZ x hx E hE (x ^ alpha ^ 2) hmem2
  calc |approxMainTerm x E (x ^ alpha) - approxMainTerm x E (x ^ alpha ^ 2)|
      ≤ |approxMainTerm x E (x ^ alpha) - 2 / Real.log (4 / 3) * mainZ x E|
        + |2 / Real.log (4 / 3) * mainZ x E - approxMainTerm x E (x ^ alpha ^ 2)| :=
        abs_sub_le _ _ _
    _ ≤ C * (Real.log x) ^ (-c) + C * (Real.log x) ^ (-c) := by
        rw [abs_sub_comm (2 / Real.log (4 / 3) * mainZ x E)]; exact add_le_add h1 h2
    _ = 2 * C * (Real.log x) ^ (-c) := by ring

-- RATIFY-3: window endpoints spelled per the spec's guidance as `[x^α, x^{α²}]` and
-- `[x^{α²}, x^{α³}]` (using `alpha^2`, `alpha^3`), which the SKELETON-SPEC flagged as the
-- intended reading of its nested-pow shorthand. Judge against §5 pp.25–28.
-- RELOCATED (2026-07-15) from `Sec5/FirstPassage.lean` VERBATIM (byte-identical statement) so the
-- assembly can consume C8 (`first_passage_approx`) + C10 (`fine_scale_mixing`) without an import cycle.
/-- **Proposition 1.11** (stabilization): the passage-location law is stable across the
two nearby log-windows, and non-passage is rare. The spine's key input. -/
theorem stabilization :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      (∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1)
          ≤ C * x ^ (-c)) ∧
      PMF.dTV ((logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).map (passLoc ⌊x⌋₊))
              ((logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).map (passLoc ⌊x⌋₊))
        ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨c7, C7, x7, hc7, hC7, h7⟩ := first_passage_nonescape
  obtain ⟨c8, C8, x8, hc8, hC8, h8⟩ := first_passage_approx
  obtain ⟨cs, Cs, xs, hcs, hCs, hstab⟩ := approxMainTerm_window_stable
  refine ⟨min (min c7 c8) cs, C7 + 4 * C8 + 2 * Cs,
    max (max (max x7 x8) xs) (Real.exp 1),
    lt_min (lt_min hc7 hc8) hcs, by positivity, ?_⟩
  intro x hx
  -- thresholds
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx7 : x7 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hx
  have hx8 : x8 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hx
  have hxs : xs ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by
    calc (1 : ℝ) ≤ Real.exp 1 := by
          rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
      _ ≤ x := hxe) le_rfl
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx1
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  set c := min (min c7 c8) cs with hc
  have hcc7 : c ≤ c7 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcc8 : c ≤ c8 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hccs : c ≤ cs := min_le_right _ _
  -- rpow window bridges: `(x^α)^α = x^{α²}` and `(x^{α²})^α = x^{α³}`
  have hpow2 : (x ^ alpha) ^ alpha = x ^ alpha ^ 2 := by
    rw [← Real.rpow_mul hx0, pow_two]
  have hpow3 : (x ^ alpha ^ 2) ^ alpha = x ^ alpha ^ 3 := by
    have he : alpha ^ 2 * alpha = alpha ^ 3 := by ring
    rw [← Real.rpow_mul hx0, he]
  have hμ1 : logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)
      = logUnifOdd (x ^ alpha) ((x ^ alpha) ^ alpha) := by rw [hpow2]
  have hμ2 : logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)
      = logUnifOdd (x ^ alpha ^ 2) ((x ^ alpha ^ 2) ^ alpha) := by rw [hpow3]
  refine ⟨?_, ?_⟩
  · -- Conjunct 1 = first_passage_nonescape (C7)
    intro y hy
    refine le_trans (h7 x hx7 y hy) ?_
    have hmono : x ^ (-c7) ≤ x ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg hcc7)
    calc C7 * x ^ (-c7) ≤ C7 * x ^ (-c) := mul_le_mul_of_nonneg_left hmono hC7.le
      _ ≤ (C7 + 4 * C8 + 2 * Cs) * x ^ (-c) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0 _); nlinarith [hC8, hCs]
  · -- Conjunct 2 = dTV stability, via C8 + the two ribs
    obtain ⟨E, hEodd, hwit⟩ := dTV_passLoc_event_witness x hx1
    -- abbreviations
    set D₁ := (logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).expect
                (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1) with hD1
    set D₂ := (logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).expect
                (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1) with hD2
    set m₁ := approxMainTerm x E (x ^ alpha) with hm1
    set m₂ := approxMainTerm x E (x ^ alpha ^ 2) with hm2
    -- C8 at y = x^α : |D₁ − m₁| ≤ C8 log^{-c8}
    have hmem1 : (x ^ alpha) ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ) := Set.mem_insert _ _
    have hmem2 : (x ^ alpha ^ 2) ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ) :=
      Set.mem_insert_of_mem _ rfl
    have h8a := h8 x hx8 E hEodd (x ^ alpha) hmem1
    have h8b := h8 x hx8 E hEodd (x ^ alpha ^ 2) hmem2
    rw [← hμ1] at h8a
    rw [← hμ2] at h8b
    -- now h8a : |D₁ − m₁| ≤ C8 log^{-c8}, h8b : |D₂ − m₂| ≤ C8 log^{-c8}
    have hD1m : |D₁ - m₁| ≤ C8 * (Real.log x) ^ (-c8) := h8a
    have hD2m : |D₂ - m₂| ≤ C8 * (Real.log x) ^ (-c8) := h8b
    -- rib B : |m₁ − m₂| ≤ Cs log^{-cs}
    have hmm : |m₁ - m₂| ≤ Cs * (Real.log x) ^ (-cs) := hstab x hxs E hEodd
    -- triangle : |D₁ − D₂| ≤ 2 C8 log^{-c8} + Cs log^{-cs}
    have htri : |D₁ - D₂| ≤ 2 * C8 * (Real.log x) ^ (-c8) + Cs * (Real.log x) ^ (-cs) := by
      calc |D₁ - D₂| ≤ |D₁ - m₁| + |m₁ - m₂| + |m₂ - D₂| := by
            calc |D₁ - D₂| ≤ |D₁ - m₁| + |m₁ - D₂| := abs_sub_le _ _ _
              _ ≤ |D₁ - m₁| + (|m₁ - m₂| + |m₂ - D₂|) := by gcongr; exact abs_sub_le _ _ _
              _ = |D₁ - m₁| + |m₁ - m₂| + |m₂ - D₂| := by ring
        _ ≤ C8 * (Real.log x) ^ (-c8) + Cs * (Real.log x) ^ (-cs)
              + C8 * (Real.log x) ^ (-c8) := by
            gcongr
            rw [abs_sub_comm]; exact hD2m
        _ = 2 * C8 * (Real.log x) ^ (-c8) + Cs * (Real.log x) ^ (-cs) := by ring
    -- log-exponent monotonicity to the shared exponent −c
    have hmono8 : (Real.log x) ^ (-c8) ≤ (Real.log x) ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg hcc8)
    have hmonos : (Real.log x) ^ (-cs) ≤ (Real.log x) ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg hccs)
    have hLnn : (0 : ℝ) ≤ (Real.log x) ^ (-c) := Real.rpow_nonneg (by linarith) _
    calc PMF.dTV _ _ ≤ 2 * |D₁ - D₂| := hwit
      _ ≤ 2 * (2 * C8 * (Real.log x) ^ (-c8) + Cs * (Real.log x) ^ (-cs)) := by
          gcongr
      _ ≤ 2 * (2 * C8 * (Real.log x) ^ (-c) + Cs * (Real.log x) ^ (-c)) := by
          have e1 : (2 : ℝ) * C8 * (Real.log x) ^ (-c8) ≤ 2 * C8 * (Real.log x) ^ (-c) :=
            mul_le_mul_of_nonneg_left hmono8 (by linarith)
          have e2 : Cs * (Real.log x) ^ (-cs) ≤ Cs * (Real.log x) ^ (-c) :=
            mul_le_mul_of_nonneg_left hmonos hCs.le
          linarith [e1, e2]
      _ = (4 * C8 + 2 * Cs) * (Real.log x) ^ (-c) := by ring
      _ ≤ (C7 + 4 * C8 + 2 * Cs) * (Real.log x) ^ (-c) := by
          apply mul_le_mul_of_nonneg_right _ hLnn; linarith

end TaoCollatz
