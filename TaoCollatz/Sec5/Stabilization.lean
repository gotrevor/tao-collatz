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

open Classical in
/-- **Fiber-partition reindex** — the reusable core of both `harmZfine`/`mainZ` → `∑_X (weight)·c_n(X)`
identities.  For any residue-weight `W : ZMod q → ℝ`, the `E'`-harmonic sum with weight
`W(M mod q)` regroups by residue class as `∑_X W(X)·classMass(X)`, where `classMass(X) =
∑_{M∈E', M≡X} 1/M`.  Proof: pull `W X` into each class `tsum` (`Summable.tsum_mul_left`), swap the
finite `∑_X` past the `tsum` (`tsum_sum`), then collapse the finite sum pointwise (`Finset.sum_ite_eq`:
only `X = M mod q` survives).  Requires each class sum summable (`hsum`; holds since `E'` is a bounded
window). -/
theorem harmonic_reindex (x : ℝ) (E : Set ℕ) (q : ℕ) [NeZero q] (W : ZMod q → ℝ)
    (hsum : ∀ X : ZMod q,
      Summable (fun M : ℕ => if Eprime x E M ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0)) :
    (∑' M : ℕ, if Eprime x E M then W (M : ZMod q) * (M : ℝ)⁻¹ else 0)
      = ∑ X : ZMod q, W X
          * ∑' M : ℕ, if Eprime x E M ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0 := by
  -- pull `W X` inside each class tsum, then swap `∑_X` past the tsum
  have hstep1 : (∑ X : ZMod q, W X
        * ∑' M : ℕ, if Eprime x E M ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0)
      = ∑' M : ℕ, ∑ X : ZMod q,
          W X * (if Eprime x E M ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0) :=
    calc (∑ X : ZMod q, W X
          * ∑' M : ℕ, if Eprime x E M ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0)
        = ∑ X : ZMod q, ∑' M : ℕ,
            W X * (if Eprime x E M ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0) :=
          Finset.sum_congr rfl (fun X _ => (Summable.tsum_mul_left (W X) (hsum X)).symm)
      _ = ∑' M : ℕ, ∑ X : ZMod q,
            W X * (if Eprime x E M ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0) :=
          (Summable.tsum_finsetSum (fun X _ => (hsum X).mul_left (W X))).symm
  rw [hstep1]
  refine tsum_congr (fun M => ?_)
  -- collapse the finite `∑_X`: only `X = (M : ZMod q)` contributes
  by_cases hEp : Eprime x E M
  · have : ∀ X : ZMod q,
        W X * (if Eprime x E M ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0)
          = if (M : ZMod q) = X then W X * (M : ℝ)⁻¹ else 0 := by
      intro X; by_cases hX : (M : ZMod q) = X
      · rw [if_pos (And.intro hEp hX), if_pos hX]
      · rw [if_neg (fun h => hX h.2), if_neg hX, mul_zero]
    rw [Finset.sum_congr rfl (fun X _ => this X),
      Finset.sum_ite_eq Finset.univ (M : ZMod q) (fun X => W X * (M : ℝ)⁻¹),
      if_pos (Finset.mem_univ _), if_pos hEp]
  · rw [if_neg hEp]
    refine (Finset.sum_eq_zero (fun X _ => ?_)).symm
    rw [if_neg (fun h => hEp h.1), mul_zero]

/-- **Residue-class window as an arithmetic progression** (general AP reindex).  For modulus `q ≥ 1`, a
real window `[lo, hi]` at least one period wide (`lo + q + 1 ≤ hi`, so the class is nonempty), and any
residue `X : ZMod q`, the naturals in `[⌈lo⌉, ⌊hi⌋]` congruent to `X mod q` form an AP
`{a, a+q, …, a+q(count−1)}` with first term `a ≥ lo` and one-past-end `a + q·count ≤ hi + q`.  (The
`3^{n−m₀}`/general-`q` analog of `classMass_ap_form`, without the oddness filter; same
`Nat.find`-least-element + `range.image` bijection argument.) -/
theorem class_window_ap_form {lo hi : ℝ} (hlo : 1 ≤ lo) {q : ℕ} (hq : 1 ≤ q)
    (hwide : (lo : ℝ) + (q : ℝ) + 1 ≤ hi) (X : ZMod q) :
    ∃ a count : ℕ,
      ((Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun M : ℕ => (M : ZMod q) = X)
        = (Finset.range count).image (fun i => a + q * i))
      ∧ lo ≤ (a : ℝ)
      ∧ (a : ℝ) + (q : ℝ) * (count : ℝ) ≤ hi + (q : ℝ) := by
  have hqpos : 0 < q := hq
  haveI : NeZero q := ⟨by omega⟩
  have hlopos : (0 : ℝ) < lo := by linarith
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hhi : (0 : ℝ) ≤ hi := by linarith
  set ylo : ℕ := ⌈lo⌉₊ with hylodef
  set yhi : ℕ := ⌊hi⌋₊ with hyhidef
  have hylo_ge : lo ≤ (ylo : ℝ) := Nat.le_ceil lo
  have hylo_lt : (ylo : ℝ) < lo + 1 := Nat.ceil_lt_add_one hlopos.le
  have hyhi_le : (yhi : ℝ) ≤ hi := Nat.floor_le hhi
  have hyhi_gt : hi - 1 < (yhi : ℝ) := by
    have := Nat.lt_floor_add_one hi; rw [← hyhidef] at this; push_cast at this ⊢; linarith
  -- residue
  set ρ : ℕ := X.val with hρdef
  have hρlt : ρ < q := ZMod.val_lt X
  have hZbridge : ∀ N : ℕ, ((N : ZMod q) = X) ↔ N % q = ρ := by
    intro N
    rw [show X = ((ρ : ℕ) : ZMod q) from (ZMod.natCast_zmod_val X).symm,
      ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hρlt]
  -- least class element ≥ ylo (the AP start `a`)
  have hex : ∃ N, ylo ≤ N ∧ N % q = ρ := by
    refine ⟨ρ + q * ylo, ?_, ?_⟩
    · exact le_trans (Nat.le_mul_of_pos_left ylo hqpos) (Nat.le_add_left _ _)
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρlt]
  set a : ℕ := Nat.find hex with hadef
  obtain ⟨haylo, hamod⟩ : ylo ≤ a ∧ a % q = ρ := Nat.find_spec hex
  have ha_lt : a < ylo + q := by
    by_contra hcon
    push_neg at hcon
    have hle : q ≤ a := by omega
    have hre : a - q + q = a := Nat.sub_add_cancel hle
    have h2 : (a - q) % q = ρ := by rw [← Nat.add_mod_right (a - q) q, hre]; exact hamod
    exact Nat.find_min hex (show a - q < a by omega) ⟨by omega, h2⟩
  have haR_ge : lo ≤ (a : ℝ) := le_trans hylo_ge (by exact_mod_cast haylo)
  -- `a ≤ yhi` from the width hypothesis (guarantees the class is nonempty)
  have ha_le_yhi : a ≤ yhi := by
    have haRlt : (a : ℝ) < lo + q := by
      have h1 : (a : ℝ) + 1 ≤ (ylo : ℝ) + q := by exact_mod_cast ha_lt
      linarith [hylo_lt]
    have : (a : ℝ) < (yhi : ℝ) := by linarith [hyhi_gt, hwide]
    exact_mod_cast Nat.le_of_lt (by exact_mod_cast this)
  set count : ℕ := (yhi - a) / q + 1 with hcountdef
  -- the class finset IS the AP `{a + q·i : i < count}`
  have hFeq : (Finset.Icc ylo yhi).filter (fun N : ℕ => (N : ZMod q) = X)
      = (Finset.range count).image (fun i => a + q * i) := by
    ext N
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, Finset.mem_Icc, hZbridge]
    constructor
    · rintro ⟨⟨hNylo, hNyhi⟩, hNmod⟩
      have haN : a ≤ N := Nat.find_min' hex ⟨hNylo, hNmod⟩
      have hdvd : q ∣ N - a := (Nat.modEq_iff_dvd' haN).mp (by
        show a % q = N % q; rw [hamod, hNmod])
      refine ⟨(N - a) / q, ?_, ?_⟩
      · have : (N - a) / q ≤ (yhi - a) / q := Nat.div_le_div_right (Nat.sub_le_sub_right hNyhi a)
        omega
      · rw [Nat.mul_div_cancel' hdvd]; omega
    · rintro ⟨i, hi, rfl⟩
      have hmod : (a + q * i) % q = ρ := by rw [Nat.add_mul_mod_self_left]; exact hamod
      have hile : i ≤ (yhi - a) / q := by omega
      have hmul : q * i ≤ yhi - a := by
        calc q * i ≤ q * ((yhi - a) / q) := Nat.mul_le_mul (le_refl q) hile
          _ = (yhi - a) / q * q := by ring
          _ ≤ yhi - a := Nat.div_mul_le_self _ _
      exact ⟨⟨by omega, by omega⟩, hmod⟩
  have hcount_lower : a + q * count ≤ yhi + q := by
    have hmul : q * ((yhi - a) / q) ≤ yhi - a := by
      calc q * ((yhi - a) / q) = (yhi - a) / q * q := by ring
        _ ≤ yhi - a := Nat.div_mul_le_self _ _
    have hexp : q * count = q * ((yhi - a) / q) + q := by rw [hcountdef]; ring
    omega
  refine ⟨a, count, hFeq, haR_ge, ?_⟩
  · have hcast : ((a + q * count : ℕ) : ℝ) = (a : ℝ) + (q : ℝ) * (count : ℝ) := by push_cast; ring
    have hle : ((a + q * count : ℕ) : ℝ) ≤ ((yhi + q : ℕ) : ℝ) := by exact_mod_cast hcount_lower
    rw [hcast] at hle
    push_cast at hle
    linarith [hyhi_le]

/-- **Residue-class harmonic window bound** (general AP integral test).  The harmonic mass of the
residue class `X mod q` in the window `[lo, hi]` is bounded by the integral term plus the `O(1/lo)`
discretization error: a single application of `harmonic_ap_integral_bound` on the AP `{a + q·i}` from
`class_window_ap_form`.  This is the reusable analytic core of the crude `cn_bound`. -/
theorem harmonic_class_window_bound {lo hi : ℝ} (hlo : 1 ≤ lo) {q : ℕ} (hq : 1 ≤ q)
    (hwide : (lo : ℝ) + (q : ℝ) + 1 ≤ hi) (X : ZMod q) :
    (∑' M : ℕ, if lo ≤ (M : ℝ) ∧ (M : ℝ) ≤ hi ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0)
      ≤ (q : ℝ)⁻¹ * Real.log ((hi + q) / lo) + 1 / lo := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlopos : (0 : ℝ) < lo := by linarith
  have hhipos : (0 : ℝ) < hi := by linarith
  obtain ⟨a, count, hAP, ha_ge, hend⟩ := class_window_ap_form hlo hq hwide X
  have haposR : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le hlopos ha_ge
  have hcond : ∀ M : ℕ, (lo ≤ (M : ℝ) ∧ (M : ℝ) ≤ hi ∧ (M : ZMod q) = X)
      ↔ M ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun M : ℕ => (M : ZMod q) = X) := by
    intro M
    rw [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hhipos.le]
    tauto
  have htsum : (∑' M : ℕ, if lo ≤ (M : ℝ) ∧ (M : ℝ) ≤ hi ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0)
      = ∑ M ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun M : ℕ => (M : ZMod q) = X), (M : ℝ)⁻¹ := by
    rw [tsum_eq_sum (s := (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun M : ℕ => (M : ZMod q) = X))
      (fun M hM => if_neg (fun h => hM ((hcond M).mp h)))]
    exact Finset.sum_congr rfl (fun M hM => if_pos ((hcond M).mpr hM))
  rw [htsum, hAP]
  have hinj : ∀ i ∈ Finset.range count, ∀ j ∈ Finset.range count,
      a + q * i = a + q * j → i = j := fun i _ j _ h =>
    Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel h)
  rw [Finset.sum_image hinj]
  have hcast : ∀ i : ℕ, ((a + q * i : ℕ) : ℝ)⁻¹ = ((a : ℝ) + (q : ℝ) * (i : ℝ))⁻¹ := by
    intro i; push_cast; ring_nf
  rw [Finset.sum_congr rfl (fun i _ => hcast i)]
  have hharm := harmonic_ap_integral_bound haposR hqR count
  have hsum_le : (∑ i ∈ Finset.range count, ((a : ℝ) + (q : ℝ) * (i : ℝ))⁻¹)
      ≤ (q : ℝ)⁻¹ * Real.log (((a : ℝ) + (q : ℝ) * (count : ℝ)) / (a : ℝ)) + (a : ℝ)⁻¹ := by
    have h := (abs_le.mp hharm).2; linarith
  refine le_trans hsum_le ?_
  have hlog_le : Real.log (((a : ℝ) + (q : ℝ) * (count : ℝ)) / (a : ℝ))
      ≤ Real.log ((hi + q) / lo) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ haposR hlopos]
    nlinarith [mul_le_mul_of_nonneg_right hend hlopos.le,
      mul_le_mul_of_nonneg_left ha_ge (by positivity : (0 : ℝ) ≤ hi + (q : ℝ))]
  have hainv : (a : ℝ)⁻¹ ≤ 1 / lo := by rw [one_div]; exact inv_anti₀ hlopos ha_ge
  exact add_le_add (mul_le_mul_of_nonneg_left hlog_le (by positivity)) hainv

/-- **Window size facts** for the crude `cn_bound` integral test.  For `x ≥ exp(1024)` and a fine
scale `k ≤ n₀`, the (5.10) window `[lo, hi] = [exp(−log^{0.7}x)·(4/3)^m·x, exp(log^{0.7}x)·(4/3)^m·x]`
satisfies: (i) `2·3^k + 2 ≤ lo` (so `q = 3^k ≤ lo`, `lo ≥ 1`, and the residue class is nonempty),
(ii) `2·lo ≤ hi` (so `lo + q + 1 ≤ hi`), and (iii) `hi = exp(2 log^{0.7}x)·lo` (so `log(hi/lo)`
is exactly `2 log^{0.7}x`).  Core estimates: `3^k ≤ 3^{n₀} ≤ x^{1/5}` (`three_pow_nZero_le`), and the
sub-linear gain `log^{0.7}x ≤ (1/8) log x` (from `log^{0.3}x ≥ 1024^{0.3} = 8`), giving
`log^{0.7}x + log 4 ≤ (4/5) log x`, i.e. `4·x^{1/5} ≤ exp(−log^{0.7}x)·x ≤ lo`. -/
theorem cn_window_size {x : ℝ} (hx : Real.exp 1024 ≤ x) {k m : ℕ} (hk : k ≤ nZero x) :
    2 * (3 : ℝ) ^ k + 2 ≤ Real.exp (-(Real.log x ^ (0.7 : ℝ))) * (4 / 3) ^ m * x ∧
    2 * (Real.exp (-(Real.log x ^ (0.7 : ℝ))) * (4 / 3) ^ m * x)
      ≤ Real.exp (Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ m * x ∧
    Real.exp (Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ m * x
      = Real.exp (2 * Real.log x ^ (0.7 : ℝ))
          * (Real.exp (-(Real.log x ^ (0.7 : ℝ))) * (4 / 3) ^ m * x) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1024 : ℝ)]) hx
  have hL1024 : (1024 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1024]; exact Real.log_le_log (Real.exp_pos _) hx
  set L := Real.log x with hLdef
  have hLpos : (0 : ℝ) < L := by linarith
  set t := L ^ (0.7 : ℝ) with htdef
  have ht1 : (1 : ℝ) ≤ t := by
    rw [htdef]
    calc (1 : ℝ) = (1 : ℝ) ^ (0.7 : ℝ) := (Real.one_rpow _).symm
      _ ≤ L ^ (0.7 : ℝ) := Real.rpow_le_rpow (by norm_num) (by linarith : (1 : ℝ) ≤ L) (by norm_num)
  have htnn : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
  have hxe : Real.exp L = x := Real.exp_log hxpos
  have hm1 : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  -- `hi = exp(2t)·lo`
  have hhieq : Real.exp t * (4 / 3) ^ m * x
      = Real.exp (2 * t) * (Real.exp (-t) * (4 / 3) ^ m * x) := by
    rw [show Real.exp (2 * t) * (Real.exp (-t) * (4 / 3 : ℝ) ^ m * x)
        = (Real.exp (2 * t) * Real.exp (-t)) * ((4 / 3 : ℝ) ^ m * x) by ring,
      ← Real.exp_add, show 2 * t + -t = t by ring]
    ring
  refine ⟨?_, ?_, hhieq⟩
  · -- (i) `2·3^k + 2 ≤ lo`
    have h3k : (3 : ℝ) ^ k ≤ x ^ ((1 : ℝ) / 5) :=
      le_trans (pow_le_pow_right₀ (by norm_num) hk) (three_pow_nZero_le hx1.le)
    have hx15_1 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 5) :=
      calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 5) := (Real.one_rpow _).symm
        _ ≤ x ^ ((1 : ℝ) / 5) := Real.rpow_le_rpow (by norm_num) hx1.le (by norm_num)
    have hLsplit : L = t * L ^ (0.3 : ℝ) := by rw [htdef, ← Real.rpow_add hLpos]; norm_num
    have he1024 : (1024 : ℝ) ^ (0.3 : ℝ) = 8 := by
      rw [show (0.3 : ℝ) = (3 : ℝ) / 10 by norm_num,
        show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num,
        ← Real.rpow_natCast (2 : ℝ) 10, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show ((10 : ℕ) : ℝ) * ((3 : ℝ) / 10) = ((3 : ℕ) : ℝ) by push_cast; norm_num,
        Real.rpow_natCast]
      norm_num
    have hL03 : (8 : ℝ) ≤ L ^ (0.3 : ℝ) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1024) hL1024
        (by norm_num : (0 : ℝ) ≤ (0.3 : ℝ))
      rwa [he1024] at h
    have hkey1 : 8 * t ≤ L := by
      have hml := mul_le_mul_of_nonneg_left hL03 htnn
      nlinarith [hLsplit, hml]
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
    have hkey : t + Real.log 4 ≤ 4 * L / 5 := by nlinarith [hkey1, hlog4, hL1024]
    have hx15e : x ^ ((1 : ℝ) / 5) = Real.exp (L * (1 / 5)) := by
      rw [Real.rpow_def_of_pos hxpos]
    have hstep : 4 * x ^ ((1 : ℝ) / 5) ≤ Real.exp (-t) * x := by
      have hlhs : 4 * x ^ ((1 : ℝ) / 5) = Real.exp (Real.log 4 + L * (1 / 5)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), ← hx15e]
      have hrhs : Real.exp (-t) * x = Real.exp (-t + L) := by rw [Real.exp_add, hxe]
      rw [hlhs, hrhs]; exact Real.exp_le_exp.mpr (by linarith [hkey])
    have hlo_ge : Real.exp (-t) * x ≤ Real.exp (-t) * (4 / 3) ^ m * x := by
      rw [mul_right_comm]
      exact le_mul_of_one_le_right (mul_pos (Real.exp_pos _) hxpos).le hm1
    have hcombine : 2 * (3 : ℝ) ^ k + 2 ≤ 4 * x ^ ((1 : ℝ) / 5) := by nlinarith [h3k, hx15_1]
    calc 2 * (3 : ℝ) ^ k + 2 ≤ 4 * x ^ ((1 : ℝ) / 5) := hcombine
      _ ≤ Real.exp (-t) * x := hstep
      _ ≤ Real.exp (-t) * (4 / 3) ^ m * x := hlo_ge
  · -- (ii) `2·lo ≤ hi`
    have hlopos : (0 : ℝ) < Real.exp (-t) * (4 / 3) ^ m * x :=
      mul_pos (mul_pos (Real.exp_pos _) (by positivity)) hxpos
    have hexp2 : (2 : ℝ) ≤ Real.exp (2 * t) := by
      have hlog2 : Real.log 2 ≤ 2 * t := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); nlinarith [ht1]
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp (2 * t) := Real.exp_le_exp.mpr hlog2
    rw [hhieq]; nlinarith [hlopos, hexp2]

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
  refine ⟨4, Real.exp 1024, by norm_num, fun x hx E hE y hy n hn X => ?_⟩
  classical
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1024 : ℝ)]) hx
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _)
      (le_trans (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 1024)) hx)
  have ht1 : (1 : ℝ) ≤ Real.log x ^ (0.7 : ℝ) :=
    calc (1 : ℝ) = (1 : ℝ) ^ (0.7 : ℝ) := (Real.one_rpow _).symm
      _ ≤ Real.log x ^ (0.7 : ℝ) := Real.rpow_le_rpow (by norm_num) hL1 (by norm_num)
  -- fine scale `n − m₀`, modulus `q = 3^{n−m₀}` (kept explicit to match `cn` after unfolding)
  have hkn0 : n - mZero x ≤ nZero x := le_trans (Nat.sub_le _ _) (mem_Iy_le_nZero hn)
  have hq1 : 1 ≤ 3 ^ (n - mZero x) := Nat.one_le_pow _ _ (by norm_num)
  have hqcast : ((3 ^ (n - mZero x) : ℕ) : ℝ) = (3 : ℝ) ^ (n - mZero x) := by push_cast; ring
  have h3kpos : (1 : ℝ) ≤ (3 : ℝ) ^ (n - mZero x) := one_le_pow₀ (by norm_num)
  -- window endpoints (byte-identical to `Eprime`'s (5.10) bounds)
  obtain ⟨hS1, hS2, hhieq⟩ := cn_window_size hx hkn0 (m := mZero x)
  set lo := Real.exp (-(Real.log x ^ (0.7 : ℝ))) * (4 / 3) ^ mZero x * x with hlodef
  set hi := Real.exp (Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x with hidef
  have hlopos : (0 : ℝ) < lo := by nlinarith [hS1, h3kpos]
  have hhipos : (0 : ℝ) < hi := by nlinarith [hS1, hS2, h3kpos]
  have hlo1 : (1 : ℝ) ≤ lo := by nlinarith [hS1, h3kpos]
  have hQle_lo : (3 : ℝ) ^ (n - mZero x) ≤ lo := by nlinarith [hS1, h3kpos]
  have hwide : lo + ((3 ^ (n - mZero x) : ℕ) : ℝ) + 1 ≤ hi := by
    rw [hqcast]; nlinarith [hS1, hS2, h3kpos]
  -- the residue-class harmonic window bound (integral test)
  have hwin := harmonic_class_window_bound hlo1 hq1 hwide X
  -- termwise domination: `Eprime`-mask ≤ window-mask (explicit lambdas; `le_trans` bridges by defeq)
  have hf_nonneg : ∀ M : ℕ,
      0 ≤ (if Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X then (M : ℝ)⁻¹ else 0) := by
    intro M; split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg M)
    · exact le_rfl
  have hdom : ∀ M : ℕ,
      (if Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X then (M : ℝ)⁻¹ else 0)
        ≤ (if lo ≤ (M : ℝ) ∧ (M : ℝ) ≤ hi ∧ (M : ZMod (3 ^ (n - mZero x))) = X
            then (M : ℝ)⁻¹ else 0) := by
    intro M
    by_cases hA : Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X
    · have hwc : lo ≤ (M : ℝ) ∧ (M : ℝ) ≤ hi ∧ (M : ZMod (3 ^ (n - mZero x))) = X := by
        refine ⟨?_, ?_, hA.2⟩
        · rw [hlodef]; exact hA.1.2.2.2.1
        · rw [hidef]; exact hA.1.2.2.2.2
      rw [if_pos hA, if_pos hwc]
    · rw [if_neg hA]; split_ifs
      · exact inv_nonneg.mpr (Nat.cast_nonneg M)
      · exact le_rfl
  have hg_summ : Summable (fun M : ℕ =>
      if lo ≤ (M : ℝ) ∧ (M : ℝ) ≤ hi ∧ (M : ZMod (3 ^ (n - mZero x))) = X
        then (M : ℝ)⁻¹ else 0) := by
    refine summable_of_ne_finset_zero
      (s := (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun M : ℕ => (M : ZMod (3 ^ (n - mZero x))) = X))
      (fun b hb => ?_)
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact hb (by
      rw [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hhipos.le]
      exact ⟨⟨h1, h2⟩, h3⟩)
  have hf_summ : Summable (fun M : ℕ =>
      if Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X then (M : ℝ)⁻¹ else 0) :=
    Summable.of_nonneg_of_le hf_nonneg hdom hg_summ
  have hcore := le_trans (hf_summ.tsum_le_tsum hdom hg_summ) hwin
  -- assemble: `cn = q·∑ ≤ q·(window bound) ≤ 4 log^{0.7}x`
  have hQne : (3 : ℝ) ^ (n - mZero x) ≠ 0 := by positivity
  have hQdivlo : (3 : ℝ) ^ (n - mZero x) / lo ≤ 1 := (div_le_one hlopos).mpr hQle_lo
  have hlo_le_hi : lo ≤ hi := by nlinarith [hS2, hlopos]
  have hnum : hi + (3 : ℝ) ^ (n - mZero x) ≤ 2 * hi := by nlinarith [le_trans hQle_lo hlo_le_hi]
  have hfrac : (hi + (3 : ℝ) ^ (n - mZero x)) / lo ≤ 2 * Real.exp (2 * Real.log x ^ (0.7 : ℝ)) := by
    rw [div_le_iff₀ hlopos]
    calc hi + (3 : ℝ) ^ (n - mZero x) ≤ 2 * hi := hnum
      _ = 2 * (Real.exp (2 * Real.log x ^ (0.7 : ℝ)) * lo) := by rw [hhieq]
      _ = 2 * Real.exp (2 * Real.log x ^ (0.7 : ℝ)) * lo := by ring
  have hlogbound : Real.log ((hi + (3 : ℝ) ^ (n - mZero x)) / lo)
      ≤ Real.log 2 + 2 * Real.log x ^ (0.7 : ℝ) := by
    have hpos : (0 : ℝ) < (hi + (3 : ℝ) ^ (n - mZero x)) / lo := by positivity
    calc Real.log ((hi + (3 : ℝ) ^ (n - mZero x)) / lo)
        ≤ Real.log (2 * Real.exp (2 * Real.log x ^ (0.7 : ℝ))) := Real.log_le_log hpos hfrac
      _ = Real.log 2 + 2 * Real.log x ^ (0.7 : ℝ) := by
          rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have harith : (3 : ℝ) ^ (n - mZero x)
        * (((3 ^ (n - mZero x) : ℕ) : ℝ)⁻¹
            * Real.log ((hi + ((3 ^ (n - mZero x) : ℕ) : ℝ)) / lo) + 1 / lo)
      = Real.log ((hi + (3 : ℝ) ^ (n - mZero x)) / lo) + (3 : ℝ) ^ (n - mZero x) / lo := by
    rw [hqcast, mul_add, ← mul_assoc, mul_inv_cancel₀ hQne, one_mul, mul_one_div]
  rw [cn]
  calc (3 : ℝ) ^ (n - mZero x)
        * (∑' M, (if Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X then (M : ℝ)⁻¹ else 0))
      ≤ (3 : ℝ) ^ (n - mZero x)
          * (((3 ^ (n - mZero x) : ℕ) : ℝ)⁻¹
              * Real.log ((hi + ((3 ^ (n - mZero x) : ℕ) : ℝ)) / lo) + 1 / lo) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = Real.log ((hi + (3 : ℝ) ^ (n - mZero x)) / lo) + (3 : ℝ) ^ (n - mZero x) / lo := harith
    _ ≤ 4 * Real.log x ^ (0.7 : ℝ) := by nlinarith [hlogbound, hQdivlo, hlog2, ht1]

-- **(5.20) sub-lemma B1 (`perNHarmonic_eq_harmZfine_approx`)** is decomposed and proved *below*, after
-- the `c_n` machinery (`cn_bound`, `cn_nonneg`, `harmZfine_eq_sum_cn`) it consumes.  See the
-- `perNGoodMass` def + the two ribs `perNHarmonic_eq_sum_cn` / `syracZ_sub_perNGoodMass_bound`.

/-- **Linear lower bound on `m₀`** — `m₀ = ⌊(α−1)/100·log x⌋ ≥ (1/200000)·log x` for `x ≥ exp(200000)`.
Since `(α−1)/100 = 1/100000`, `m₀ > log x/100000 − 1 ≥ log x/200000` once `log x ≥ 200000`.  Used to
turn `fine_scale_mixing`'s `m₀^{−A}` decay into `(log x)^{−A}` decay (B2's final log-arithmetic). -/
theorem mZero_ge_lin :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → (1 / 200000 : ℝ) * Real.log x ≤ (mZero x : ℝ) := by
  refine ⟨Real.exp 200000, Real.one_le_exp (by norm_num), fun x hx => ?_⟩
  have hL : (200000 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 200000]; exact Real.log_le_log (Real.exp_pos _) hx
  have ha1 : (alpha - 1) / 100 = (1 : ℝ) / 100000 := by unfold alpha; norm_num
  have hlt : (alpha - 1) / 100 * Real.log x < (mZero x : ℝ) + 1 := by
    unfold mZero; exact Nat.lt_floor_add_one _
  rw [ha1] at hlt
  linarith

open Classical in
/-- Each residue-class harmonic sum `∑_{M∈E', M≡X} 1/M` is summable: `E'` bounds `M` to the finite
window `[·, ⌊exp(log^{0.7}x)(4/3)^{m₀}x⌋]` (`Eprime`'s upper bound), so the support is finite. -/
theorem cn_class_summable (x : ℝ) (E : Set ℕ) (q : ℕ) (X : ZMod q) :
    Summable (fun M : ℕ => if Eprime x E M ∧ (M : ZMod q) = X then (M : ℝ)⁻¹ else 0) := by
  classical
  refine summable_of_ne_finset_zero
    (s := Finset.range
      (⌊Real.exp (Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x⌋₊ + 1)) (fun b hb => ?_)
  rw [if_neg]
  rintro ⟨hEp, _⟩
  refine hb (Finset.mem_range.mpr ?_)
  have hble : (b : ℝ) ≤ Real.exp (Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x := hEp.2.2.2.2
  have := Nat.le_floor hble
  omega

open Classical in
/-- **B1/B2 reindex identity (harm side)** — `harmZfine = ∑_X syracZ(n−m₀)(X)·c_n(X)` (Tao 5.22–5.23):
regroup the `E'`-harmonic sum by residue class `X = M mod 3^{n−m₀}` via `harmonic_reindex` with weight
`W(X) = 3^{n−m₀}·syracZ(n−m₀)(X)`, then absorb the `3^{n−m₀}` into `c_n(X)`. -/
theorem harmZfine_eq_sum_cn (x : ℝ) (E : Set ℕ) (n : ℕ) :
    harmZfine x E n
      = ∑ X : ZMod (3 ^ (n - mZero x)), ((syracZ (n - mZero x)) X).toReal * cn x E n X := by
  haveI : NeZero (3 ^ (n - mZero x)) := ⟨by positivity⟩
  have hreindex := harmonic_reindex x E (3 ^ (n - mZero x))
    (fun X => (3 : ℝ) ^ (n - mZero x) * ((syracZ (n - mZero x)) X).toReal)
    (fun X => cn_class_summable x E _ X)
  rw [harmZfine]
  have hconv : (∑' M : ℕ, if Eprime x E M then
        (3 : ℝ) ^ (n - mZero x)
          * ((syracZ (n - mZero x)) (M : ZMod (3 ^ (n - mZero x)))).toReal / (M : ℝ) else 0)
      = ∑' M : ℕ, if Eprime x E M then
        ((3 : ℝ) ^ (n - mZero x)
          * ((syracZ (n - mZero x)) (M : ZMod (3 ^ (n - mZero x)))).toReal) * (M : ℝ)⁻¹ else 0 := by
    refine tsum_congr (fun M => ?_)
    by_cases h : Eprime x E M
    · rw [if_pos h, if_pos h, div_eq_mul_inv]
    · rw [if_neg h, if_neg h]
  rw [hconv, hreindex]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  rw [cn]; ring

open Classical in
/-- **B2 reindex identity (main side)** — `mainZ = ∑_X fiber_avg(X)·c_n(X)`, `fiber_avg(X) =
3^{m₀−(n−m₀)}·syracZ(m₀)(castHom X)`.  The coarse residue `M mod 3^{m₀}` is `castHom (M mod 3^{n−m₀})`
(`map_natCast`), so `mainZ`'s weight `3^{m₀}·syracZ(m₀)(M mod 3^{m₀})` regroups by the FINE class via
`harmonic_reindex`; the `3^{m₀}` splits as `3^{m₀−(n−m₀)}·3^{n−m₀}`, the latter absorbed into `c_n`. -/
theorem mainZ_eq_sum_fiber_cn (x : ℝ) (E : Set ℕ) (n : ℕ) (hmn : mZero x ≤ n - mZero x) :
    mainZ x E
      = ∑ X : ZMod (3 ^ (n - mZero x)),
          ((3 : ℝ) ^ ((mZero x : ℤ) - ((n - mZero x : ℕ) : ℤ))
              * ((syracZ (mZero x))
                  (ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ mZero x)) X)).toReal)
            * cn x E n X := by
  haveI : NeZero (3 ^ (n - mZero x)) := ⟨by positivity⟩
  have hreindex := harmonic_reindex x E (3 ^ (n - mZero x))
    (fun X => (3 : ℝ) ^ mZero x
      * ((syracZ (mZero x)) (ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ mZero x)) X)).toReal)
    (fun X => cn_class_summable x E _ X)
  rw [mainZ]
  have hconv : (∑' M : ℕ, if Eprime x E M then
        (3 : ℝ) ^ mZero x * ((syracZ (mZero x)) (M : ZMod (3 ^ mZero x))).toReal / (M : ℝ) else 0)
      = ∑' M : ℕ, if Eprime x E M then
        ((3 : ℝ) ^ mZero x * ((syracZ (mZero x))
          (ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ mZero x))
            (M : ZMod (3 ^ (n - mZero x))))).toReal) * (M : ℝ)⁻¹ else 0 := by
    refine tsum_congr (fun M => ?_)
    by_cases h : Eprime x E M
    · rw [if_pos h, if_pos h, div_eq_mul_inv,
        map_natCast (ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ mZero x))) M]
    · rw [if_neg h, if_neg h]
  rw [hconv, hreindex]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  rw [cn]
  have h3 : (3 : ℝ) ^ mZero x
      = (3 : ℝ) ^ ((mZero x : ℤ) - ((n - mZero x : ℕ) : ℤ)) * (3 : ℝ) ^ (n - mZero x) := by
    rw [← zpow_natCast (3 : ℝ) (n - mZero x), ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      ← zpow_natCast (3 : ℝ) (mZero x)]
    congr 1; ring
  rw [h3]; ring

/-- **osc as an `L¹` deviation against `fiber_avg`** — the coarse fiber sum in `osc`'s definition is the
`syracZ(m)` marginal (`syracZ_map_cast`): `∑_{Y'≡Y} syracZ(fine)(Y') = syracZ(m)(castHom Y)`.  So
`osc m fine (syracZ(fine)) = ∑_X |syracZ(fine)(X) − 3^{m−fine}·syracZ(m)(castHom X)|`, matching the
`harmZfine − mainZ` deviation term. -/
theorem osc_syracZ_eq_sum_dev {m fine : ℕ} (hmn : m ≤ fine) :
    osc m fine hmn (fun Y => ((syracZ fine) Y).toReal)
      = ∑ X : ZMod (3 ^ fine),
          |((syracZ fine) X).toReal
            - (3 : ℝ) ^ ((m : ℤ) - (fine : ℤ))
                * ((syracZ m)
                    (ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) X)).toReal| := by
  have hfib : ∀ Y : ZMod (3 ^ fine),
      (∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ fine) =>
          ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y'
            = ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y), ((syracZ fine) Y').toReal)
        = ((syracZ m) (ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y)).toReal := by
    intro Y
    rw [← ENNReal.toReal_sum (fun Y' _ => PMF.apply_ne_top _ _)]
    congr 1
    rw [← syracZ_map_cast hmn, PMF.map_apply, tsum_fintype, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hc : ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) a
        = ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y
    · rw [if_pos hc, if_pos hc.symm]
    · rw [if_neg hc, if_neg (fun h => hc h.symm)]
  rw [osc]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  rw [hfib Y]

/-- `c_n(X) ≥ 0` — it is `3^{n−m₀}` times a `tsum` of nonnegative masked reciprocals. -/
theorem cn_nonneg (x : ℝ) (E : Set ℕ) (n : ℕ) (X : ZMod (3 ^ (n - mZero x))) :
    0 ≤ cn x E n X := by
  classical
  rw [cn]
  refine mul_nonneg (by positivity) (tsum_nonneg (fun M => ?_))
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg M)
  · exact le_rfl

/-- **B2 Hölder core** — `|harmZfine − mainZ| ≤ (sup c_n)·osc m₀ (n−m₀)`.  Reindex both sides
(`harmZfine_eq_sum_cn`, `mainZ_eq_sum_fiber_cn`): `harmZfine − mainZ = ∑_X (syracZ(n−m₀)(X) −
fiber_avg(X))·c_n(X)`.  Then **L¹×L∞ Hölder** with `0 ≤ c_n(X) ≤ Ccn·log^{0.7}x` (`hcn`, from
`cn_bound`) and `∑_X|syracZ(n−m₀)(X) − fiber_avg(X)| = osc m₀ (n−m₀)` (`osc_syracZ_eq_sum_dev`, via
`syracZ_map_cast`).  Parameterized by the `c_n` bound `(Ccn, hcn)` so the caller supplies `cn_bound`. -/
theorem harmZfine_sub_mainZ_le_osc {x : ℝ} {E : Set ℕ} {n : ℕ} (hmn : mZero x ≤ n - mZero x)
    {Ccn : ℝ} (hCcn : 0 ≤ Ccn)
    (hcn : ∀ X : ZMod (3 ^ (n - mZero x)), cn x E n X ≤ Ccn * Real.log x ^ (0.7 : ℝ)) :
    |harmZfine x E n - mainZ x E|
      ≤ (Ccn * Real.log x ^ (0.7 : ℝ))
          * osc (mZero x) (n - mZero x) hmn (fun Y => ((syracZ (n - mZero x)) Y).toReal) := by
  rw [harmZfine_eq_sum_cn, mainZ_eq_sum_fiber_cn x E n hmn, osc_syracZ_eq_sum_dev hmn,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun X _ => ?_))
  rw [← sub_mul, abs_mul, mul_comm (Ccn * Real.log x ^ (0.7 : ℝ))]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_of_nonneg (cn_nonneg x E n X)]
  exact hcn X

open Classical in
/-- **Good-restricted `syracZ` pushforward mass at residue `X`** (scale `k = n − m₀`).  `perNHarmonic`'s
inner weight `1_good · 2^{−pre ā}` is exactly `1_good · (geomHalf.iid k)(ā).toReal` (a good tuple has
every coordinate `≥ 1`), pushed forward under the reversed-`fnat` map
`ā ↦ (fnat ā)·2^{−pre ā} mod 3^k`.  Dropping the `1_good` restriction recovers `syracZ k`
(`syracZ_eq_rev_fnat`); the dropped mass is `ℙ(¬good)`, controlled whp. -/
noncomputable def perNGoodMass (x : ℝ) (n : ℕ) (X : ZMod (3 ^ (n - mZero x))) : ℝ :=
  ∑' ā : Fin (n - mZero x) → ℕ,
    if goodTuple x (n - mZero x) ā
        ∧ (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
            * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
      then ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹ else 0

open Classical in
/-- **`perNGoodMass` in iid-mass form.**  On a good tuple every coordinate is `≥ 1`, so the literal
`2^{−pre ā}` weight is exactly the iid `geomHalf` mass `(geomHalf.iid k)(ā).toReal`.  Rewriting to this
form lines `perNGoodMass` up termwise with the `syracZ`-pushforward. -/
theorem perNGoodMass_eq_iid (x : ℝ) (n : ℕ) (X : ZMod (3 ^ (n - mZero x))) :
    perNGoodMass x n X
      = ∑' ā : Fin (n - mZero x) → ℕ,
          if goodTuple x (n - mZero x) ā
              ∧ (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
                  * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
            then ((geomHalf.iid (n - mZero x)) ā).toReal else 0 := by
  rw [perNGoodMass]
  refine tsum_congr fun ā => ?_
  by_cases h : goodTuple x (n - mZero x) ā
      ∧ (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
          * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
  · rw [if_pos h, if_pos h, iid_geomHalf_apply_of_pos _ _ h.1.1,
      ENNReal.toReal_pow, ENNReal.toReal_inv, inv_pow]
    norm_num
  · rw [if_neg h, if_neg h]

open Classical in
/-- **`syracZ` marginal in `fnat`-pushforward form.**  `syracZ k = (geomHalf.iid k).map (ā ↦
(fnat ā)·2^{−pre ā})` (`syracZ_eq_rev_fnat`), so its real mass at `X` is the iid mass summed over the
fiber `{ā | (fnat ā)·2^{−pre ā} = X}`. -/
theorem syracZ_toReal_eq_tsum_fnat (x : ℝ) (n : ℕ) (X : ZMod (3 ^ (n - mZero x))) :
    ((syracZ (n - mZero x)) X).toReal
      = ∑' ā : Fin (n - mZero x) → ℕ,
          if (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
                  * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
            then ((geomHalf.iid (n - mZero x)) ā).toReal else 0 := by
  rw [syracZ_eq_rev_fnat, PMF.map_apply,
    ENNReal.tsum_toReal_eq (fun ā => by split_ifs; exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top])]
  refine tsum_congr fun ā => ?_
  by_cases h : (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
      * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun he => h he.symm), if_neg h, ENNReal.toReal_zero]

/-- Summability of the `syracZ`-fiber iid mass (bounded above by the full iid mass, which sums to 1). -/
theorem iid_fiber_summable (k : ℕ) (P : (Fin k → ℕ) → Prop) [DecidablePred P] :
    Summable (fun ā : Fin k → ℕ => if P ā then ((geomHalf.iid k) ā).toReal else 0) := by
  refine Summable.of_nonneg_of_le (fun ā => by positivity) (fun ā => ?_)
    (ENNReal.summable_toReal (by rw [(geomHalf.iid k).tsum_coe]; exact ENNReal.one_ne_top))
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

/-- `2` is a unit mod `3^k` (coprime), so `2·2⁻¹ = 1` there. -/
theorem two_mul_inv_zmod_three_pow (k : ℕ) :
    (2 : ZMod (3 ^ k)) * (2 : ZMod (3 ^ k))⁻¹ = 1 := by
  apply ZMod.mul_inv_of_unit
  rw [show (2 : ZMod (3 ^ k)) = ((2 : ℕ) : ZMod (3 ^ k)) from by norm_cast,
    ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right k (by decide)

/-- **The `ℕ`-affine guard is exactly the `ZMod` fiber condition** (Lemma 2.1 reindex, pointwise).
Given the size guard `fnat ≤ M·2^{pre ā}` (automatic for good `ā`, `M ∈ E'`), the exact affine
divisibility `3^k ∣ (M·2^{pre ā} − fnat ā)` holds iff `M mod 3^k` equals the reversed-`fnat` map value
`F ā = (fnat ā)·2^{−pre ā}`.  This is the bridge that turns `perNHarmonic`'s inner solvability mask into
`perNGoodMass`'s residue-class fiber. -/
theorem solvable_iff_fmapZ (k : ℕ) [NeZero (3 ^ k)] (ā : Fin k → ℕ) (M : ℕ)
    (hguard : fnat k ā ≤ M * 2 ^ pre ā k) :
    (3 ^ k ∣ (M * 2 ^ pre ā k - fnat k ā))
      ↔ (M : ZMod (3 ^ k))
          = (fnat k ā : ZMod (3 ^ k)) * (2 : ZMod (3 ^ k))⁻¹ ^ pre ā k := by
  have hunit := two_mul_inv_zmod_three_pow k
  -- divisibility ↔ ZMod equality of the naturals
  have hdvd_iff : (3 ^ k ∣ (M * 2 ^ pre ā k - fnat k ā))
      ↔ (fnat k ā : ZMod (3 ^ k)) = ((M * 2 ^ pre ā k : ℕ) : ZMod (3 ^ k)) := by
    rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd' hguard]
  rw [hdvd_iff, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  -- `(fnat) = (M)·2^pre  ↔  (M) = (fnat)·(2⁻¹)^pre`
  constructor
  · intro h
    rw [h, mul_assoc, ← mul_pow, hunit, one_pow, mul_one]
  · intro h
    rw [h, mul_assoc, ← mul_pow, mul_comm (2 : ZMod (3 ^ k))⁻¹ 2, hunit, one_pow, mul_one]

/-- **B1 rib 1 — the `(5.22)` fiber identity (harm side, good-restricted).**  `perNHarmonic` regroups by
residue class `X = M mod 3^{n−m₀}` exactly as `harmZfine` does, but with the good-restricted pushforward
mass `perNGoodMass` in place of the full `syracZ(n−m₀)` mass:
`perNHarmonic x E n = ∑_X perNGoodMass x n X · c_n(X)`.  Proof route (mirrors `harmZfine_eq_sum_cn`): on a
good tuple `ā` and `M ∈ E'` the ℕ-affine guard `3^{n−m₀} ∣ M·2^{pre ā}−fnat ∧ fnat ≤ M·2^{pre ā}` is
equivalent to the `ZMod` congruence `(M : ZMod 3^{n−m₀}) = (fnat ā)·2^{−pre ā}` (the guard `fnat ≤ M·2^{pre
ā}` is automatic via `fnat_lt_pow_mul` + `3^{n−m₀} ≤ M`), so the inner `M`-sum is `c_n(F ā)/3^{n−m₀}·3^{n−m₀}`;
then a fiber partition of the `ā`-tsum over the finite `ZMod (3^{n−m₀})` groups by `X = F ā`.
**[C9 leaf B1 rib — pure reindex; does NOT consume C10.]** -/
theorem perNHarmonic_eq_sum_cn (x : ℝ) (E : Set ℕ) (n : ℕ) :
    perNHarmonic x E n
      = ∑ X : ZMod (3 ^ (n - mZero x)), perNGoodMass x n X * cn x E n X := by
  sorry

open Classical in
/-- **iid good-tuple whp bound (Tao (5.11)/(5.12), iid form).**  Under the `geomHalf.iid k` law, a length-`k`
tuple fails to be good with probability `≪ log^{-1}x` (for `k ≤ n₀`).  This is the iid half of
`goodTuple_prefix_dev_sum` — `¬good` means a coord is `0` (mass `0`, since `geomHalf` has no atom at `0`)
or some prefix `pre a m` deviates from `2m` by `≥ log^{0.6}x` (each `≪ exp(−c·log^{0.2}x)` via
`geomHalf_tail_bound`; sum over the `≤ k+1 ≤ log x` prefixes, then the `log x·exp(−c log^{0.2}) ≤ log^{-1}`
shrink).  No dTV transfer is needed because the base law is already `geomHalf.iid`. -/
theorem good_tuple_whp_iid :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ k : ℕ, k ≤ nZero x →
      (∑' ā : Fin k → ℕ,
          if ¬ goodTuple x k ā then ((geomHalf.iid k) ā).toReal else 0)
        ≤ C * (Real.log x) ^ (-(1 : ℝ)) := by
  classical
  obtain ⟨ct, hct, Ct, hCt, htail⟩ := geomHalf_tail_bound
  obtain ⟨κ, x₀g, hκ, hGdecay⟩ := Gweight_prefix_decay (d := ct) hct
  obtain ⟨x₀A, hA⟩ := log_rpow_mul_exp_neg_le_one (p := 2) (κ := κ) (θ := 0.2)
    (by norm_num) hκ (by norm_num)
  refine ⟨2 * Ct, max x₀A (max (Real.exp 20) x₀g), by positivity, fun x hx k hk => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hxA, hx20, hxg⟩ := hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 20) hx20
  have hL20 : (20 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 20]; exact Real.log_le_log (Real.exp_pos _) hx20
  have hLpos : 0 < Real.log x := by linarith
  have hlam : (0 : ℝ) ≤ Real.log x ^ (0.6 : ℝ) := Real.rpow_nonneg hLpos.le _
  -- masked fiber families: `Z` = coord-zero event, `D n` = prefix-`n` deviation event
  set m : (Fin k → ℕ) → ℝ := fun ā => ((geomHalf.iid k) ā).toReal with hm
  set Z : (Fin k → ℕ) → ℝ := fun ā => if ¬ (∀ i, 1 ≤ ā i) then m ā else 0 with hZ
  set D : ℕ → (Fin k → ℕ) → ℝ := fun n ā =>
    if Real.log x ^ (0.6 : ℝ) ≤ |(pre ā n : ℝ) - 2 * n| then m ā else 0 with hD
  have hmnn : ∀ ā, 0 ≤ m ā := fun ā => ENNReal.toReal_nonneg
  have hDnn : ∀ n ā, 0 ≤ D n ā := fun n ā => by
    simp only [hD]; split_ifs <;> first | exact hmnn ā | exact le_rfl
  have hZnn : ∀ ā, 0 ≤ Z ā := fun ā => by
    simp only [hZ]; split_ifs <;> first | exact hmnn ā | exact le_rfl
  have hsummZ : Summable Z := iid_fiber_summable k (fun ā => ¬ (∀ i, 1 ≤ ā i))
  have hsummD : ∀ n, Summable (D n) := fun n =>
    iid_fiber_summable k (fun ā => Real.log x ^ (0.6 : ℝ) ≤ |(pre ā n : ℝ) - 2 * n|)
  have hsummLHS : Summable (fun ā : Fin k → ℕ => if ¬ goodTuple x k ā then m ā else 0) :=
    iid_fiber_summable k (fun ā => ¬ goodTuple x k ā)
  have hsummDsum : Summable (fun ā : Fin k → ℕ => ∑ n ∈ Finset.range (k + 1), D n ā) := by
    have h : Summable (∑ n ∈ Finset.range (k + 1), D n) :=
      Finset.sum_induction D Summable (fun _ _ ha hb => ha.add hb) summable_zero
        (fun n _ => hsummD n)
    exact h.congr (fun ā => Finset.sum_apply ā (Finset.range (k + 1)) D)
  -- termwise: `[¬good] m ≤ Z + ∑_{n≤k} D n`
  have hterm : ∀ ā, (if ¬ goodTuple x k ā then m ā else 0)
      ≤ Z ā + ∑ n ∈ Finset.range (k + 1), D n ā := by
    intro ā
    have hsumnn : 0 ≤ ∑ n ∈ Finset.range (k + 1), D n ā :=
      Finset.sum_nonneg (fun n _ => hDnn n ā)
    by_cases hg : goodTuple x k ā
    · rw [if_neg (not_not.mpr hg)]; linarith [hZnn ā]
    · rw [if_pos hg]
      -- unfold `¬good`
      rw [goodTuple, not_and_or] at hg
      rcases hg with hpos | hdev
      · -- coord zero ⟹ `Z ā = m ā`, and it dominates
        have hZm : Z ā = m ā := by simp only [hZ]; rw [if_pos hpos]
        linarith
      · -- prefix deviation at some `n* ≤ k`
        push_neg at hdev
        obtain ⟨n, hnk, hn⟩ := hdev
        have hnmem : n ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
        have hDn : D n ā = m ā := by simp only [hD]; rw [if_pos hn]
        have hsingle : D n ā ≤ ∑ n' ∈ Finset.range (k + 1), D n' ā :=
          Finset.single_le_sum (fun n' _ => hDnn n' ā) hnmem
        rw [hDn] at hsingle; linarith [hZnn ā]
  -- `∑' Z = 0` (coord-zero has iid mass `0`)
  have hZzero : ∑' ā : Fin k → ℕ, Z ā = 0 := by
    refine (tsum_congr (fun ā => ?_)).trans tsum_zero
    simp only [hZ]
    by_cases hp : (∀ i, 1 ≤ ā i)
    · rw [if_neg (not_not.mpr hp)]
    · rw [if_pos hp]; simp only [hm]
      rw [iid_geomHalf_apply_eq_zero_of_not_pos k ā hp, ENNReal.toReal_zero]
  -- per-prefix deviation mass `≤ Ct·Gweight`
  have hDbound : ∀ n ∈ Finset.range (k + 1),
      ∑' ā : Fin k → ℕ, D n ā ≤ Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ)) := by
    intro n hn
    have hnk : n ≤ k := by rw [Finset.mem_range] at hn; omega
    simp only [hD, hm]
    rw [iid_prefix_twosided_eq k n hnk (Real.log x ^ (0.6 : ℝ))]
    exact htail n (Real.log x ^ (0.6 : ℝ)) hlam
  -- assemble the tsum bound
  have hmain : ∑' ā : Fin k → ℕ, (if ¬ goodTuple x k ā then m ā else 0)
      ≤ ∑ n ∈ Finset.range (k + 1), Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ)) := by
    calc ∑' ā : Fin k → ℕ, (if ¬ goodTuple x k ā then m ā else 0)
        ≤ ∑' ā : Fin k → ℕ, (Z ā + ∑ n ∈ Finset.range (k + 1), D n ā) :=
          hsummLHS.tsum_le_tsum hterm (hsummZ.add hsummDsum)
      _ = (∑' ā, Z ā) + ∑' ā, ∑ n ∈ Finset.range (k + 1), D n ā :=
          hsummZ.tsum_add hsummDsum
      _ = ∑ n ∈ Finset.range (k + 1), ∑' ā, D n ā := by
          rw [hZzero, zero_add, ← Summable.tsum_finsetSum (fun n _ => hsummD n)]
      _ ≤ ∑ n ∈ Finset.range (k + 1), Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ)) :=
          Finset.sum_le_sum hDbound
  -- Gweight decay + (k+1 ≤ log x) + the `log·exp ≤ log^{-1}` shrink
  have hnZ5 : (nZero x : ℝ) ≤ Real.log x / 5 := by
    have hfloor : (nZero x : ℝ) ≤ Real.log x / (10 * Real.log 2) := by
      unfold nZero; exact Nat.floor_le (by positivity)
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := le_of_lt (by have := Real.log_two_gt_d9; linarith)
    exact le_trans hfloor
      ((div_le_div_iff_of_pos_left hLpos (by linarith) (by norm_num)).mpr (by linarith))
  have hn1L : ((k + 1 : ℕ) : ℝ) ≤ Real.log x := by
    have hkR : (k : ℝ) ≤ Real.log x / 5 := le_trans (by exact_mod_cast hk) hnZ5
    push_cast; linarith
  have hGsum : ∑ n ∈ Finset.range (k + 1), Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ))
      ≤ ((k + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ)))) := by
    calc ∑ n ∈ Finset.range (k + 1), Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ))
        ≤ ∑ _n ∈ Finset.range (k + 1), Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) :=
          Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left
            (hGdecay x hxg n (by rw [Finset.mem_range] at hn; omega)) hCt.le)
      _ = ((k + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have shrink : Real.log x * Real.exp (-κ * Real.log x ^ (0.2 : ℝ)) ≤ Real.log x ^ (-(1 : ℝ)) := by
    have h1 : (Real.log x) ^ (-(1 : ℝ)) * (Real.log x) ^ (2 : ℝ) = Real.log x := by
      rw [← Real.rpow_add hLpos]; norm_num
    calc Real.log x * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))
        = ((Real.log x) ^ (-(1 : ℝ)) * (Real.log x) ^ (2 : ℝ))
            * Real.exp (-κ * Real.log x ^ (0.2 : ℝ)) := by rw [h1]
      _ = (Real.log x) ^ (-(1 : ℝ))
            * ((Real.log x) ^ (2 : ℝ) * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) := by ring
      _ ≤ (Real.log x) ^ (-(1 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left (hA x hxA) (Real.rpow_nonneg hLpos.le _)
      _ = (Real.log x) ^ (-(1 : ℝ)) := mul_one _
  calc ∑' ā : Fin k → ℕ, (if ¬ goodTuple x k ā then ((geomHalf.iid k) ā).toReal else 0)
      = ∑' ā : Fin k → ℕ, (if ¬ goodTuple x k ā then m ā else 0) := by rw [hm]
    _ ≤ ((k + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ)))) :=
        le_trans hmain hGsum
    _ = 2 * Ct * (((k + 1 : ℕ) : ℝ) * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) := by ring
    _ ≤ 2 * Ct * (Real.log x * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hn1L (Real.exp_pos _).le) (by positivity)
    _ ≤ 2 * Ct * (Real.log x) ^ (-(1 : ℝ)) :=
        mul_le_mul_of_nonneg_left shrink (by positivity)

/-- **B1 rib 2 — the good-tuple whp residual.**  Dropping the `1_good` restriction from `perNGoodMass`
only *adds* nonnegative mass, and the total added mass over all residues is exactly `ℙ(¬good)` under the
`geomHalf.iid (n−m₀)` law, which is `≪ log^{-1} x` (mirror of `goodTuple_prefix_dev_sum`'s iid half — the
per-prefix `geomHalf_tail_bound` summed over the `≤ n₀` prefixes, no dTV transfer needed since the base
law is already `geomHalf.iid`).  So `perNGoodMass x n X ≤ syracZ(n−m₀)(X).toReal` pointwise and
`∑_X (syracZ(n−m₀)(X).toReal − perNGoodMass x n X) ≤ C·log^{-1}x`.
**[C9 leaf B1 rib — pushforward decomposition + analytic whp; does NOT consume C10.]** -/
theorem syracZ_sub_perNGoodMass_bound :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          (∀ X : ZMod (3 ^ (n - mZero x)),
              perNGoodMass x n X ≤ ((syracZ (n - mZero x)) X).toReal) ∧
            ∑ X : ZMod (3 ^ (n - mZero x)),
                (((syracZ (n - mZero x)) X).toReal - perNGoodMass x n X)
              ≤ C * (Real.log x) ^ (-(1 : ℝ)) := by
  classical
  obtain ⟨C, x₀, hC, hwhp⟩ := good_tuple_whp_iid
  refine ⟨C, x₀, hC, fun x hx E hE y hy n hn => ?_⟩
  set k := n - mZero x with hk
  have hkn : k ≤ nZero x := le_trans (Nat.sub_le _ _) (mem_Iy_le_nZero hn)
  -- abbreviations for the two masked fiber families
  set F : (Fin k → ℕ) → ZMod (3 ^ k) := fun ā =>
    (fnat k ā : ZMod (3 ^ k)) * (2 : ZMod (3 ^ k))⁻¹ ^ pre ā k with hF
  -- summability of the full and good-restricted fibers
  have hFsumm : ∀ X : ZMod (3 ^ k),
      Summable (fun ā : Fin k → ℕ => if F ā = X then ((geomHalf.iid k) ā).toReal else 0) :=
    fun X => iid_fiber_summable k (fun ā => F ā = X)
  have hGsumm : ∀ X : ZMod (3 ^ k),
      Summable (fun ā : Fin k → ℕ =>
        if goodTuple x k ā ∧ F ā = X then ((geomHalf.iid k) ā).toReal else 0) :=
    fun X => iid_fiber_summable k (fun ā => goodTuple x k ā ∧ F ā = X)
  -- pointwise `perNGoodMass ≤ syracZ.toReal`
  have hpoint : ∀ X : ZMod (3 ^ k),
      perNGoodMass x n X ≤ ((syracZ k) X).toReal := by
    intro X
    rw [perNGoodMass_eq_iid, syracZ_toReal_eq_tsum_fnat]
    refine (hGsumm X).tsum_le_tsum (fun ā => ?_) (hFsumm X)
    by_cases hgx : goodTuple x k ā ∧ F ā = X
    · rw [if_pos hgx, if_pos hgx.2]
    · rw [if_neg hgx]; split_ifs
      · exact ENNReal.toReal_nonneg
      · exact le_rfl
  refine ⟨hpoint, ?_⟩
  -- the residue sum collapses to `ℙ(¬good)` under the iid law
  have hcollapse :
      ∑ X : ZMod (3 ^ k), (((syracZ k) X).toReal - perNGoodMass x n X)
        = ∑' ā : Fin k → ℕ, if ¬ goodTuple x k ā then ((geomHalf.iid k) ā).toReal else 0 := by
    have hterm : ∀ X : ZMod (3 ^ k),
        ((syracZ k) X).toReal - perNGoodMass x n X
          = ∑' ā : Fin k → ℕ,
              ((if F ā = X then ((geomHalf.iid k) ā).toReal else 0)
                - if goodTuple x k ā ∧ F ā = X then ((geomHalf.iid k) ā).toReal else 0) := by
      intro X
      rw [syracZ_toReal_eq_tsum_fnat, perNGoodMass_eq_iid,
        (hFsumm X).tsum_sub (hGsumm X)]
    rw [Finset.sum_congr rfl (fun X _ => hterm X),
      (Summable.tsum_finsetSum (fun X _ => (hFsumm X).sub (hGsumm X))).symm]
    refine tsum_congr fun ā => ?_
    -- fiber count = 1: `∑_X ([F ā=X] − [good ∧ F ā=X]) = [¬good]`
    rw [Finset.sum_sub_distrib]
    have hfull : ∑ X : ZMod (3 ^ k), (if F ā = X then ((geomHalf.iid k) ā).toReal else 0)
        = ((geomHalf.iid k) ā).toReal := by
      rw [Finset.sum_ite_eq Finset.univ (F ā) (fun _ => ((geomHalf.iid k) ā).toReal),
        if_pos (Finset.mem_univ _)]
    by_cases hg : goodTuple x k ā
    · have hgood : ∑ X : ZMod (3 ^ k),
          (if goodTuple x k ā ∧ F ā = X then ((geomHalf.iid k) ā).toReal else 0)
          = ((geomHalf.iid k) ā).toReal := by
        have hcongr : ∀ X : ZMod (3 ^ k),
            (if goodTuple x k ā ∧ F ā = X then ((geomHalf.iid k) ā).toReal else 0)
              = (if F ā = X then ((geomHalf.iid k) ā).toReal else 0) := by
          intro X
          by_cases hX : F ā = X
          · rw [if_pos ⟨hg, hX⟩, if_pos hX]
          · rw [if_neg (fun h => hX h.2), if_neg hX]
        rw [Finset.sum_congr rfl (fun X _ => hcongr X), hfull]
      rw [hfull, hgood, if_neg (not_not.mpr hg), sub_self]
    · have hgood : ∑ X : ZMod (3 ^ k),
          (if goodTuple x k ā ∧ F ā = X then ((geomHalf.iid k) ā).toReal else 0) = 0 :=
        Finset.sum_eq_zero (fun X _ => if_neg (fun h => hg h.1))
      rw [hfull, hgood, if_pos hg, sub_zero]
  rw [hcollapse]
  exact hwhp x hx k hkn

/-- **(5.20) sub-lemma B1 — geomHalf → `syracZ` reindex** (assembled from the two ribs above).
`perNHarmonic` (inner weight the `2^{−pre ā}` iid-geomHalf mass over *good, affine-solvable* tuples)
agrees with `harmZfine` (the exact `Syrac(ℤ/3^{n−m₀}ℤ)` mass) up to `O(log^{-c}x)`.  Both reindex to
`∑_X (mass)·c_n(X)` — `harmZfine` with the full `syracZ` mass (`harmZfine_eq_sum_cn`), `perNHarmonic`
with the good-restricted `perNGoodMass` (`perNHarmonic_eq_sum_cn`).  L¹×L∞ Hölder with `0 ≤ c_n ≤
Ccn·log^{0.7}x` (`cn_bound`/`cn_nonneg`) against the `log^{-1}x` whp residual
(`syracZ_sub_perNGoodMass_bound`) gives net `log^{0.7−1} = log^{-0.3}`.
**[C9 leaf B1 — pure reindex + whp; does NOT consume C10.]** -/
theorem perNHarmonic_eq_harmZfine_approx :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNHarmonic x E n - harmZfine x E n| ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨Ccn, x₀cn, hCcn, hcn⟩ := cn_bound
  obtain ⟨Cw, x₀w, hCw, hwhp⟩ := syracZ_sub_perNGoodMass_bound
  refine ⟨0.3, Ccn * Cw, max (max x₀cn x₀w) (Real.exp 1), by norm_num, by positivity,
    fun x hx E hE y hy n hn => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxcn, hxw⟩, hxe1⟩ := hx
  have hLpos : (0 : ℝ) < Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe1
    rw [Real.log_exp] at h; linarith
  have hL07 : (0 : ℝ) ≤ Real.log x ^ (0.7 : ℝ) := Real.rpow_nonneg hLpos.le _
  obtain ⟨hle, hsum⟩ := hwhp x hxw E hE y hy n hn
  -- termwise: `|perNGoodMass·cn − syracZ·cn| ≤ (syracZ − perNGoodMass)·(Ccn·log^{0.7})`
  have key : ∀ X : ZMod (3 ^ (n - mZero x)),
      |perNGoodMass x n X * cn x E n X - ((syracZ (n - mZero x)) X).toReal * cn x E n X|
        ≤ (((syracZ (n - mZero x)) X).toReal - perNGoodMass x n X)
            * (Ccn * Real.log x ^ (0.7 : ℝ)) := by
    intro X
    rw [← sub_mul, abs_mul,
      abs_of_nonpos (by linarith [hle X] : perNGoodMass x n X - ((syracZ (n - mZero x)) X).toReal ≤ 0),
      abs_of_nonneg (cn_nonneg x E n X), neg_sub]
    exact mul_le_mul_of_nonneg_left (hcn x hxcn E hE y hy n hn X)
      (by linarith [hle X])
  -- `log^{0.7}·log^{-1} = log^{-0.3}`
  have hmul : Real.log x ^ (0.7 : ℝ) * Real.log x ^ (-(1 : ℝ)) = Real.log x ^ (-(0.3 : ℝ)) := by
    rw [← Real.rpow_add hLpos]; norm_num
  rw [perNHarmonic_eq_sum_cn, harmZfine_eq_sum_cn, ← Finset.sum_sub_distrib]
  calc |∑ X : ZMod (3 ^ (n - mZero x)),
          (perNGoodMass x n X * cn x E n X - ((syracZ (n - mZero x)) X).toReal * cn x E n X)|
      ≤ ∑ X : ZMod (3 ^ (n - mZero x)),
          |perNGoodMass x n X * cn x E n X - ((syracZ (n - mZero x)) X).toReal * cn x E n X| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ X : ZMod (3 ^ (n - mZero x)),
          (((syracZ (n - mZero x)) X).toReal - perNGoodMass x n X)
            * (Ccn * Real.log x ^ (0.7 : ℝ)) := Finset.sum_le_sum (fun X _ => key X)
    _ = (∑ X : ZMod (3 ^ (n - mZero x)),
          (((syracZ (n - mZero x)) X).toReal - perNGoodMass x n X))
            * (Ccn * Real.log x ^ (0.7 : ℝ)) := by rw [← Finset.sum_mul]
    _ ≤ (Cw * Real.log x ^ (-(1 : ℝ))) * (Ccn * Real.log x ^ (0.7 : ℝ)) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = Ccn * Cw * Real.log x ^ (-(0.3 : ℝ)) := by rw [← hmul]; ring

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
  obtain ⟨x1, _, htwo⟩ := two_mZero_le_of_mem_Iy
  obtain ⟨x2, _, hmzlin⟩ := mZero_ge_lin
  obtain ⟨Cfsm, hCfsm, hfsm⟩ := fine_scale_mixing 1.7 (by norm_num)
  obtain ⟨Ccn, xcn, hCcnpos, hcnb⟩ := cn_bound
  refine ⟨1, Ccn * Cfsm * (1 / 200000 : ℝ) ^ (-(1.7 : ℝ)),
    max (Real.exp 200000) (max x1 (max x2 xcn)), by norm_num,
    mul_pos (mul_pos hCcnpos hCfsm) (Real.rpow_pos_of_pos (by norm_num) _),
    fun x hx E hE y hy n hn => ?_⟩
  have h200 : Real.exp 200000 ≤ x := le_trans (le_max_left _ _) hx
  have hrest : max x1 (max x2 xcn) ≤ x := le_trans (le_max_right _ _) hx
  have hxx1 : x1 ≤ x := le_trans (le_max_left _ _) hrest
  have hx2xcn : max x2 xcn ≤ x := le_trans (le_max_right _ _) hrest
  have hxx2 : x2 ≤ x := le_trans (le_max_left _ _) hx2xcn
  have hxxcn : xcn ≤ x := le_trans (le_max_right _ _) hx2xcn
  have hL200 : (200000 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 200000]; exact Real.log_le_log (Real.exp_pos _) h200
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hmn : mZero x ≤ n - mZero x := by have := htwo x hxx1 y hy n hn; omega
  have hmzR : (1 / 200000 : ℝ) * Real.log x ≤ (mZero x : ℝ) := hmzlin x hxx2
  have hm1R : (1 : ℝ) ≤ (mZero x : ℝ) := by nlinarith [hmzR, hL200]
  have hm1 : 1 ≤ mZero x := by exact_mod_cast hm1R
  have hcn : ∀ X : ZMod (3 ^ (n - mZero x)), cn x E n X ≤ Ccn * Real.log x ^ (0.7 : ℝ) :=
    fun X => hcnb x hxxcn E hE y hy n hn X
  have hkey := harmZfine_sub_mainZ_le_osc hmn hCcnpos.le hcn
  have hosc := hfsm (n - mZero x) (mZero x) hmn hm1
  have hCnn : (0 : ℝ) ≤ Ccn * Real.log x ^ (0.7 : ℝ) := by positivity
  have hc0pos : (0 : ℝ) < (1 / 200000 : ℝ) * Real.log x := by positivity
  have hmono : (mZero x : ℝ) ^ (-(1.7 : ℝ))
      ≤ ((1 / 200000 : ℝ) * Real.log x) ^ (-(1.7 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hc0pos hmzR (by norm_num)
  have hsplit : ((1 / 200000 : ℝ) * Real.log x) ^ (-(1.7 : ℝ))
      = (1 / 200000 : ℝ) ^ (-(1.7 : ℝ)) * Real.log x ^ (-(1.7 : ℝ)) :=
    Real.mul_rpow (by norm_num) hLpos.le
  have hcomb : Real.log x ^ (0.7 : ℝ) * Real.log x ^ (-(1.7 : ℝ)) = Real.log x ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hLpos]; norm_num
  calc |harmZfine x E n - mainZ x E|
      ≤ (Ccn * Real.log x ^ (0.7 : ℝ))
          * osc (mZero x) (n - mZero x) hmn (fun Y => ((syracZ (n - mZero x)) Y).toReal) := hkey
    _ ≤ (Ccn * Real.log x ^ (0.7 : ℝ)) * (Cfsm * (mZero x : ℝ) ^ (-(1.7 : ℝ))) :=
        mul_le_mul_of_nonneg_left hosc hCnn
    _ ≤ (Ccn * Real.log x ^ (0.7 : ℝ)) * (Cfsm * ((1 / 200000 : ℝ) * Real.log x) ^ (-(1.7 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hCnn
        exact mul_le_mul_of_nonneg_left hmono hCfsm.le
    _ = (Ccn * Cfsm * (1 / 200000 : ℝ) ^ (-(1.7 : ℝ)))
          * (Real.log x ^ (0.7 : ℝ) * Real.log x ^ (-(1.7 : ℝ))) := by rw [hsplit]; ring
    _ = (Ccn * Cfsm * (1 / 200000 : ℝ) ^ (-(1.7 : ℝ))) * Real.log x ^ (-(1 : ℝ)) := by rw [hcomb]

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
