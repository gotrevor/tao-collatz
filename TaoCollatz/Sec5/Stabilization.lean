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

-- **`mainZ` is `O(1)`** (`mainZ_bound`): stated and PROVED *below*, after `harmonic_to_Z` —
-- its proof runs Tao's a-posteriori route `Z ≍ (log(4/3)/2)·ℙ(Pass∈E) = O(1)` (p.26) through the
-- (5.19)/(5.20) reductions and Prop 5.2, all of which live later in this file.

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

-- **(5.19) harmonic reduction `perNTerm_harmonic_approx`** (C9 leaf A) is decomposed and stated
-- *below*, after the rib-1 fiber machinery it consumes (`perNHarmonic_eq_sum_cn` → `perNHarmonic_le`)
-- and the `N*` sub-lemmas (`Nstar_odd`, `Nstar_mem_logWindow`).

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
    have := Nat.lt_floor_add_one hi; rw [← hyhidef] at this; linarith
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
    push Not at hcon
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

/-- The `cn_bound` cutoff, symbolic (big-C campaign, step 2); constant = numeral 4. -/
noncomputable def X_cnBound : ℝ := Real.exp 1024

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
weakening.  Used as `sup_X c_n ≤ C·log^{0.7}x` by both B1 and B2.]**

`_at` sibling at (`4`, `X_cnBound := exp 1024`) (big-C campaign, step 2). -/
theorem cn_bound_at :
    ∀ x : ℝ, X_cnBound ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          ∀ X : ZMod (3 ^ (n - mZero x)), cn x E n X ≤ 4 * (Real.log x) ^ (0.7 : ℝ) := by
  unfold X_cnBound
  intro x hx E hE y hy n hn X
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

/-- `cn_bound`, original `∃`-form: delegates to the `_at` sibling at
(`4`, `X_cnBound`) (big-C campaign, step 2). -/
theorem cn_bound :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          ∀ X : ZMod (3 ^ (n - mZero x)), cn x E n X ≤ C * (Real.log x) ^ (0.7 : ℝ) :=
  ⟨4, X_cnBound, by norm_num, cn_bound_at⟩

/-- The `mZero_ge_lin` cutoff, symbolic (big-C campaign, step 2). -/
noncomputable def X_mZeroLin : ℝ := Real.exp 200000

/-- **Linear lower bound on `m₀`** — `m₀ = ⌊(α−1)/100·log x⌋ ≥ (1/200000)·log x` for `x ≥ exp(200000)`.
Since `(α−1)/100 = 1/100000`, `m₀ > log x/100000 − 1 ≥ log x/200000` once `log x ≥ 200000`.  Used to
turn `fine_scale_mixing`'s `m₀^{−A}` decay into `(log x)^{−A}` decay (B2's final log-arithmetic).

`_at` sibling at `X_mZeroLin := exp 200000` (big-C campaign, step 2). -/
theorem mZero_ge_lin_at :
    ∀ x : ℝ, X_mZeroLin ≤ x → (1 / 200000 : ℝ) * Real.log x ≤ (mZero x : ℝ) := by
  unfold X_mZeroLin
  intro x hx
  have hL : (200000 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 200000]; exact Real.log_le_log (Real.exp_pos _) hx
  have ha1 : (alpha - 1) / 100 = (1 : ℝ) / 100000 := by unfold alpha; norm_num
  have hlt : (alpha - 1) / 100 * Real.log x < (mZero x : ℝ) + 1 := by
    unfold mZero; exact Nat.lt_floor_add_one _
  rw [ha1] at hlt
  linarith

/-- `mZero_ge_lin`, original `∃`-form: delegates to the `_at` sibling at
`X_mZeroLin` (big-C campaign, step 2). -/
theorem mZero_ge_lin :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → (1 / 200000 : ℝ) * Real.log x ≤ (mZero x : ℝ) :=
  ⟨X_mZeroLin, Real.one_le_exp (by norm_num), mZero_ge_lin_at⟩

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
    {Ccn : ℝ}
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
theorem perNHarmonic_eq_sum_cn (x : ℝ) (E : Set ℕ) (n : ℕ)
    (hx : Real.exp 1024 ≤ x) (hkn : n - mZero x ≤ nZero x) :
    perNHarmonic x E n
      = ∑ X : ZMod (3 ^ (n - mZero x)), perNGoodMass x n X * cn x E n X := by
  classical
  haveI : NeZero (3 ^ (n - mZero x)) := ⟨by positivity⟩
  -- every `M ∈ E'` dominates the modulus: `3^{n−m₀} ≤ M` (window floor, `cn_window_size` (i))
  have h3kM : ∀ M : ℕ, Eprime x E M → 3 ^ (n - mZero x) ≤ M := by
    intro M hEp
    have hlo := (cn_window_size hx hkn (m := mZero x)).1
    have hMlo := hEp.2.2.2.1
    have h3R : ((3 ^ (n - mZero x) : ℕ) : ℝ) ≤ (M : ℝ) := by
      push_cast
      linarith [pow_pos (show (0 : ℝ) < 3 by norm_num) (n - mZero x)]
    exact_mod_cast h3R
  -- so the ℕ-affine size guard is automatic on `E'`
  have hguard : ∀ (ā : Fin (n - mZero x) → ℕ) (M : ℕ), Eprime x E M →
      fnat (n - mZero x) ā ≤ M * 2 ^ pre ā (n - mZero x) := fun ā M hEp =>
    le_trans (fnat_lt_pow_mul (n - mZero x) ā).le
      (Nat.mul_le_mul (h3kM M hEp) le_rfl)
  -- LHS: solvability mask → residue fiber (`solvable_iff_fmapZ`), inner `M`-sum factors
  have hLHS : perNHarmonic x E n
      = (3 : ℝ) ^ (n - mZero x) * ∑' ā : Fin (n - mZero x) → ℕ,
          (if goodTuple x (n - mZero x) ā then
              ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹
                * ∑' M : ℕ, (if Eprime x E M
                    ∧ (M : ZMod (3 ^ (n - mZero x)))
                        = (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
                            * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x)
                  then (M : ℝ)⁻¹ else 0)
            else 0) := by
    rw [perNHarmonic]
    congr 1
    refine tsum_congr fun ā => ?_
    by_cases hg : goodTuple x (n - mZero x) ā
    · rw [if_pos hg, ← tsum_mul_left]
      refine tsum_congr fun M => ?_
      by_cases hEp : Eprime x E M
      · by_cases hc : (M : ZMod (3 ^ (n - mZero x)))
            = (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
                * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x)
        · rw [if_pos ⟨hg, hEp,
              (solvable_iff_fmapZ (n - mZero x) ā M (hguard ā M hEp)).mpr hc,
              hguard ā M hEp⟩, if_pos ⟨hEp, hc⟩, div_eq_mul_inv]
        · rw [if_neg (fun h =>
              hc ((solvable_iff_fmapZ (n - mZero x) ā M (hguard ā M hEp)).mp h.2.2.1)),
            if_neg (fun h => hc h.2), mul_zero]
      · rw [if_neg (fun h => hEp h.2.1), if_neg (fun h => hEp h.1), mul_zero]
    · rw [if_neg hg]
      exact (tsum_congr fun M => if_neg (fun h => hg h.1)).trans tsum_zero
  -- summability of the good-restricted fiber (via the iid form, `iid_fiber_summable`)
  have hsummG : ∀ X : ZMod (3 ^ (n - mZero x)),
      Summable (fun ā : Fin (n - mZero x) → ℕ =>
        if goodTuple x (n - mZero x) ā
            ∧ (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
                * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
          then ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹ else 0) := by
    intro X
    refine (iid_fiber_summable (n - mZero x)
      (fun ā => goodTuple x (n - mZero x) ā
        ∧ (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
            * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X)).congr fun ā => ?_
    by_cases h : goodTuple x (n - mZero x) ā
        ∧ (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
            * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
    · rw [if_pos h, if_pos h, iid_geomHalf_apply_of_pos _ _ h.1.1,
        ENNReal.toReal_pow, ENNReal.toReal_inv, inv_pow]
      norm_num
    · rw [if_neg h, if_neg h]
  -- RHS termwise: push `cn X` into the `ā`-tsum of `perNGoodMass X`
  have hRHS : ∀ X : ZMod (3 ^ (n - mZero x)),
      perNGoodMass x n X * cn x E n X
        = ∑' ā : Fin (n - mZero x) → ℕ,
            (if goodTuple x (n - mZero x) ā
                ∧ (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
                    * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
              then ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹ else 0)
            * ((3 : ℝ) ^ (n - mZero x)
                * ∑' M : ℕ, (if Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X
                    then (M : ℝ)⁻¹ else 0)) := by
    intro X
    rw [perNGoodMass, cn, ← tsum_mul_right]
  rw [hLHS, Finset.sum_congr rfl (fun X _ => hRHS X),
    (Summable.tsum_finsetSum (fun (X : ZMod (3 ^ (n - mZero x))) _ =>
      (hsummG X).mul_right ((3 : ℝ) ^ (n - mZero x)
        * ∑' M : ℕ, (if Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X
            then (M : ℝ)⁻¹ else 0)))).symm, ← tsum_mul_left]
  refine tsum_congr fun ā => ?_
  by_cases hg : goodTuple x (n - mZero x) ā
  · -- collapse the finite `∑_X`: only `X = F ā` survives
    have hterm : ∀ X : ZMod (3 ^ (n - mZero x)),
        (if goodTuple x (n - mZero x) ā
            ∧ (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
                * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
          then ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹ else 0)
          * ((3 : ℝ) ^ (n - mZero x)
              * ∑' M : ℕ, (if Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X
                  then (M : ℝ)⁻¹ else 0))
        = if (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
              * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
          then ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹
              * ((3 : ℝ) ^ (n - mZero x)
                  * ∑' M : ℕ, (if Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X
                      then (M : ℝ)⁻¹ else 0))
          else 0 := by
      intro X
      by_cases hX : (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
          * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
      · rw [if_pos ⟨hg, hX⟩, if_pos hX]
      · rw [if_neg (fun h => hX h.2), if_neg hX, zero_mul]
    rw [if_pos hg, Finset.sum_congr rfl (fun X _ => hterm X),
      Finset.sum_ite_eq Finset.univ
        ((fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
          * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x))
        (fun X => ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹
          * ((3 : ℝ) ^ (n - mZero x)
              * ∑' M : ℕ, (if Eprime x E M ∧ (M : ZMod (3 ^ (n - mZero x))) = X
                  then (M : ℝ)⁻¹ else 0))),
      if_pos (Finset.mem_univ _)]
    ring
  · rw [if_neg hg, mul_zero]
    exact (Finset.sum_eq_zero fun X _ => by
      rw [if_neg (fun h => hg h.1), zero_mul]).symm

/-- On a positive tuple every nonempty prefix sum is `≥ 1` (the `i = 0` summand already is). -/
theorem pre_pos {k : ℕ} (hk : 0 < k) (ā : Fin k → ℕ) (hpos : ∀ i, 1 ≤ ā i) {m : ℕ}
    (hm : 1 ≤ m) : 1 ≤ pre ā m := by
  have hs := Finset.single_le_sum (f := fun i => if h : i < k then ā ⟨i, h⟩ else 0)
    (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (show 0 < m by omega))
  rw [pre]
  refine le_trans ?_ hs
  rw [dif_pos hk]
  exact hpos _

/-- **`fnat` is odd** for `k ≥ 1` on positive tuples: the `m = 0` summand is `3^{k−1}·2^{pre ā 0} =
3^{k−1}` (odd), and every `m ≥ 1` summand carries `2^{pre ā m}` with `pre ā m ≥ ā₀ ≥ 1` (even). -/
theorem fnat_odd {k : ℕ} (hk : 1 ≤ k) (ā : Fin k → ℕ) (hpos : ∀ i, 1 ≤ ā i) :
    fnat k ā % 2 = 1 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [fnat, Finset.sum_range_succ']
  have h0 : pre ā 0 = 0 := by simp [pre]
  have htail : 2 ∣ ∑ m ∈ Finset.range k', 3 ^ (k' + 1 - 1 - (m + 1)) * 2 ^ pre ā (m + 1) := by
    refine Finset.dvd_sum fun m _ => Dvd.dvd.mul_left ?_ _
    exact dvd_pow_self 2 (by have := pre_pos (Nat.succ_pos k') ā hpos (m := m + 1) (by omega); omega)
  have hodd : (3 ^ (k' + 1 - 1 - 0) * 2 ^ pre ā 0) % 2 = 1 := by
    rw [h0, pow_zero, mul_one, Nat.pow_mod]; norm_num
  obtain ⟨t, ht⟩ := htail
  omega

/-- **`N*` is odd** — the affine solution `N* = (M·2^{pre ā} − fnat)/3^{n−m₀}` inherits `M`'s oddness:
for `k = 0` it *is* `M`; for `k ≥ 1`, `M·2^{pre ā k}` is even (`pre ā k ≥ 1`) while `fnat` is odd
(`fnat_odd`), so `3^k·N* = M·2^{pre} − fnat` is odd, hence so is `N*`.  This is what routes the
solution into the ODD log-window that `logUnifOdd` is supported on. -/
theorem Nstar_odd {k : ℕ} (ā : Fin k → ℕ) (hpos : ∀ i, 1 ≤ ā i) {M : ℕ} (hM : M % 2 = 1)
    (hdvd : 3 ^ k ∣ (M * 2 ^ pre ā k - fnat k ā)) (hle : fnat k ā ≤ M * 2 ^ pre ā k) :
    ((M * 2 ^ pre ā k - fnat k ā) / 3 ^ k) % 2 = 1 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    have h0 : pre ā 0 = 0 := by simp [pre]
    have hf0 : fnat 0 ā = 0 := by simp [fnat]
    simpa [h0, hf0] using hM
  · obtain ⟨N, hN⟩ := hdvd
    rw [hN, Nat.mul_div_cancel_left N (by positivity)]
    have heq : 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k := by omega
    have hf := fnat_odd hk1 ā hpos
    have h3 : 3 ^ k % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    have hNprod : (3 ^ k * N) % 2 = N % 2 := by
      rw [Nat.mul_mod, h3, one_mul]; omega
    obtain ⟨c, hc⟩ := (dvd_pow_self 2
      (by have := pre_pos hk1 ā hpos (m := k) hk1; omega : pre ā k ≠ 0)).mul_left M
    omega

-- HEARTBEAT: one large log-arithmetic assembly (window bounds × margin rpow algebra × casts); the
-- many linarith/nlinarith/positivity calls exhaust the default per-declaration budget cumulatively.
set_option maxHeartbeats 1600000 in
open Classical in
/-- **(5.18) `N*` window membership** — for `n ∈ I_y`, good `ā`, `M` in the `E'` window (5.10), and
the affine equation solvable, the solution `N* = (M·2^{pre ā} − fnat)/3^{n−m₀}` lands in the odd
log-window `[y, y^α]` (oddness by `Nstar_odd`), so `logUnifOdd y (y^α)` puts mass `(N*)⁻¹/D` on it.
Log-arithmetic: `3^{n−m₀}·N* = M·2^{pre ā}·(1 − fnat/(M·2^{pre}))` with `fnat/(M·2^{pre}) < 3^{n−m₀}/M
= O(x^{-2/5})`, so `log N* = log M + pre·log 2 − (n−m₀)·log 3 + O(x^{-c}) = log x + n·log(4/3) ±
(log^{0.7} + log 2·log^{0.6} + o(1))·x`, and the `±log^{0.8}x` margins built into `IyLo`/`IyHi` (5.9)
dominate the slack.  **[C9 leaf A sub-lemma — pure log-arithmetic; does NOT consume C10.]** -/
theorem Nstar_mem_logWindow :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
        ∀ ā : Fin (n - mZero x) → ℕ, goodTuple x (n - mZero x) ā →
          ∀ M : ℕ, M % 2 = 1 →
            Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x ≤ (M : ℝ) →
            (M : ℝ) ≤ Real.exp (Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x →
            3 ^ (n - mZero x) ∣ (M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā) →
            fnat (n - mZero x) ā ≤ M * 2 ^ pre ā (n - mZero x) →
            ((M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā) / 3 ^ (n - mZero x))
              ∈ logWindow y (y ^ alpha) := by
  classical
  obtain ⟨x₁, _, htwo⟩ := two_mZero_le_of_mem_Iy
  refine ⟨max (Real.exp 1073741824) x₁, fun x hx y hy n hn ā hg M hModd hMlo hMhi hdvd hle => ?_⟩
  have hxbig : Real.exp 1073741824 ≤ x := le_trans (le_max_left _ _) hx
  have hxx1 : x₁ ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxbig
  have hL : (1073741824 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1073741824]; exact Real.log_le_log (Real.exp_pos _) hxbig
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hy0 : (0 : ℝ) < y := by
    rcases (by simpa [Set.mem_insert_iff] using hy : y = x ^ alpha ∨ y = x ^ alpha ^ 2) with h | h <;>
      rw [h] <;> exact Real.rpow_pos_of_pos hxpos _
  have hkn : n - mZero x ≤ nZero x := le_trans (Nat.sub_le _ _) (mem_Iy_le_nZero hn)
  have hx1024 : Real.exp 1024 ≤ x :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hxbig
  -- `E'` dominates the modulus (window floor), so the guard is comfortable: `2·fnat ≤ M·2^{pre}`
  obtain ⟨hS1, -, -⟩ := cn_window_size hx1024 hkn (m := mZero x)
  have hMposR : (0 : ℝ) < (M : ℝ) := by
    have h32 : (0 : ℝ) < 2 * (3 : ℝ) ^ (n - mZero x) + 2 := by positivity
    linarith [hS1, hMlo]
  have hM3nat : 2 * 3 ^ (n - mZero x) ≤ M := by
    have hR : ((2 * 3 ^ (n - mZero x) : ℕ) : ℝ) ≤ (M : ℝ) := by push_cast; linarith [hS1, hMlo]
    exact_mod_cast hR
  have hf2 : 2 * fnat (n - mZero x) ā ≤ M * 2 ^ pre ā (n - mZero x) :=
    calc 2 * fnat (n - mZero x) ā
        ≤ (2 * 3 ^ (n - mZero x)) * 2 ^ pre ā (n - mZero x) := by
          rw [mul_assoc]
          exact Nat.mul_le_mul le_rfl (fnat_lt_pow_mul _ ā).le
      _ ≤ M * 2 ^ pre ā (n - mZero x) := Nat.mul_le_mul hM3nat le_rfl
  have hf2R : 2 * (fnat (n - mZero x) ā : ℝ) ≤ (M : ℝ) * 2 ^ pre ā (n - mZero x) := by
    exact_mod_cast hf2
  -- rpow margin arithmetic: `log^{0.8}·log(4/3) ≥ log^{0.7} + log^{0.6}·log 2 + log 2`
  have ht6nn : (0 : ℝ) ≤ Real.log x ^ (0.6 : ℝ) := Real.rpow_nonneg hLpos.le _
  have ht7nn : (0 : ℝ) ≤ Real.log x ^ (0.7 : ℝ) := Real.rpow_nonneg hLpos.le _
  have ht8nn : (0 : ℝ) ≤ Real.log x ^ (0.8 : ℝ) := Real.rpow_nonneg hLpos.le _
  have ht61 : (1 : ℝ) ≤ Real.log x ^ (0.6 : ℝ) :=
    calc (1 : ℝ) = (1 : ℝ) ^ (0.6 : ℝ) := (Real.one_rpow _).symm
      _ ≤ Real.log x ^ (0.6 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have hL01 : (8 : ℝ) ≤ Real.log x ^ (0.1 : ℝ) := by
    have h8 : ((1073741824 : ℝ)) ^ ((0.1 : ℝ)) = 8 := by
      rw [show (1073741824 : ℝ) = (8 : ℝ) ^ (10 : ℕ) by norm_num,
        ← Real.rpow_natCast (8 : ℝ) 10, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8),
        show ((10 : ℕ) : ℝ) * (0.1 : ℝ) = 1 by push_cast; norm_num, Real.rpow_one]
    have h := Real.rpow_le_rpow (by norm_num) hL (by norm_num : (0 : ℝ) ≤ (0.1 : ℝ))
    rwa [h8] at h
  have hsplit87 : Real.log x ^ (0.1 : ℝ) * Real.log x ^ (0.7 : ℝ) = Real.log x ^ (0.8 : ℝ) := by
    rw [← Real.rpow_add hLpos]; norm_num
  have hsplit76 : Real.log x ^ (0.1 : ℝ) * Real.log x ^ (0.6 : ℝ) = Real.log x ^ (0.7 : ℝ) := by
    rw [← Real.rpow_add hLpos]; norm_num
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hl43pos : (0 : ℝ) < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hl43_lb : (1 / 4 : ℝ) ≤ Real.log (4 / 3) := by
    have h34 : Real.log (3 / 4 : ℝ) ≤ 3 / 4 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have hinv : Real.log ((3 / 4 : ℝ)⁻¹) = -Real.log (3 / 4 : ℝ) := Real.log_inv _
    rw [show ((3 / 4 : ℝ)⁻¹) = (4 / 3 : ℝ) by norm_num] at hinv
    linarith
  have hA : 8 * Real.log x ^ (0.7 : ℝ) ≤ Real.log x ^ (0.8 : ℝ) := by
    rw [← hsplit87]; exact mul_le_mul_of_nonneg_right hL01 ht7nn
  have hB : 8 * Real.log x ^ (0.6 : ℝ) ≤ Real.log x ^ (0.7 : ℝ) := by
    rw [← hsplit76]; exact mul_le_mul_of_nonneg_right hL01 ht6nn
  have hD : Real.log x ^ (0.6 : ℝ) * Real.log 2 ≤ Real.log x ^ (0.6 : ℝ) :=
    mul_le_of_le_one_right ht6nn hlog2le1
  have hE : Real.log x ^ (0.8 : ℝ) * (1 / 4) ≤ Real.log x ^ (0.8 : ℝ) * Real.log (4 / 3) :=
    mul_le_mul_of_nonneg_left hl43_lb ht8nn
  have hmargin : Real.log x ^ (0.7 : ℝ) + Real.log x ^ (0.6 : ℝ) * Real.log 2 + Real.log 2
      ≤ Real.log x ^ (0.8 : ℝ) * Real.log (4 / 3) := by linarith
  -- `log M` window bounds
  have hlml : -Real.log x ^ (0.7 : ℝ) + (mZero x : ℝ) * Real.log (4 / 3) + Real.log x
      ≤ Real.log (M : ℝ) := by
    have hlopos : (0 : ℝ) < Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x := by
      positivity
    have h := Real.log_le_log hlopos hMlo
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_pow] at h
  have hlmh : Real.log (M : ℝ)
      ≤ Real.log x ^ (0.7 : ℝ) + (mZero x : ℝ) * Real.log (4 / 3) + Real.log x := by
    have h := Real.log_le_log hMposR hMhi
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_pow] at h
  -- good-tuple prefix bound at full length: `|pre − 2k| < log^{0.6}`
  have habs := hg.2 (n - mZero x) le_rfl
  rw [abs_lt] at habs
  have hPlo : 2 * ((n - mZero x : ℕ) : ℝ) - Real.log x ^ (0.6 : ℝ)
      ≤ (pre ā (n - mZero x) : ℝ) := by linarith [habs.1]
  have hPhi : (pre ā (n - mZero x) : ℝ)
      ≤ 2 * ((n - mZero x : ℕ) : ℝ) + Real.log x ^ (0.6 : ℝ) := by linarith [habs.2]
  have hPlo2 : 2 * ((n - mZero x : ℕ) : ℝ) * Real.log 2
        - Real.log x ^ (0.6 : ℝ) * Real.log 2
      ≤ (pre ā (n - mZero x) : ℝ) * Real.log 2 := by nlinarith [hPlo, hlog2pos.le]
  have hPhi2 : (pre ā (n - mZero x) : ℝ) * Real.log 2
      ≤ 2 * ((n - mZero x : ℕ) : ℝ) * Real.log 2
        + Real.log x ^ (0.6 : ℝ) * Real.log 2 := by nlinarith [hPhi, hlog2pos.le]
  -- `2·log 2 = log(4/3) + log 3`, and `m₀ + (n − m₀) = n`
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hl43eq : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), h4]
  have e2l : ((n - mZero x : ℕ) : ℝ) * Real.log (4 / 3)
      = 2 * ((n - mZero x : ℕ) : ℝ) * Real.log 2 - ((n - mZero x : ℕ) : ℝ) * Real.log 3 := by
    rw [hl43eq]; ring
  have hm0n : mZero x ≤ n := by have := htwo x hxx1 y hy n hn; omega
  have e3 : (mZero x : ℝ) + ((n - mZero x : ℕ) : ℝ) = (n : ℝ) := by
    push_cast [Nat.cast_sub hm0n]; ring
  have e3l : (mZero x : ℝ) * Real.log (4 / 3) + ((n - mZero x : ℕ) : ℝ) * Real.log (4 / 3)
      = (n : ℝ) * Real.log (4 / 3) := by rw [← add_mul, e3]
  -- `I_y` endpoint bounds, multiplied through by `log(4/3)`
  have hIy1 : Real.log y - Real.log x + Real.log x ^ (0.8 : ℝ) * Real.log (4 / 3)
      ≤ (n : ℝ) * Real.log (4 / 3) := by
    have h := (mem_Iy_bounds hn).1
    rw [IyLo] at h
    have h' := mul_le_mul_of_nonneg_right h hl43pos.le
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hl43pos),
      Real.log_div (ne_of_gt hy0) (ne_of_gt hxpos)] at h'
    linarith
  have hIy2 : (n : ℝ) * Real.log (4 / 3)
      ≤ alpha * Real.log y - Real.log x - Real.log x ^ (0.8 : ℝ) * Real.log (4 / 3) := by
    have h := (mem_Iy_bounds hn).2
    rw [IyHi] at h
    have h' := mul_le_mul_of_nonneg_right h hl43pos.le
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hl43pos),
      Real.log_div (Real.rpow_pos_of_pos hy0 alpha).ne' (ne_of_gt hxpos),
      Real.log_rpow hy0] at h'
    linarith
  -- the two multiplicative bounds on `Q = M·2^{pre}`
  have hQpos : (0 : ℝ) < (M : ℝ) * 2 ^ pre ā (n - mZero x) :=
    mul_pos hMposR (by positivity)
  have e1 : Real.log ((M : ℝ) * 2 ^ pre ā (n - mZero x))
      = Real.log (M : ℝ) + (pre ā (n - mZero x) : ℝ) * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hQlo : 2 * y * (3 : ℝ) ^ (n - mZero x) ≤ (M : ℝ) * 2 ^ pre ā (n - mZero x) := by
    have h2y3pos : (0 : ℝ) < 2 * y * (3 : ℝ) ^ (n - mZero x) :=
      mul_pos (mul_pos two_pos hy0) (by positivity)
    have tlo : Real.log (2 * y * (3 : ℝ) ^ (n - mZero x))
        = Real.log 2 + Real.log y + ((n - mZero x : ℕ) : ℝ) * Real.log 3 := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (ne_of_gt hy0), Real.log_pow]
    have hlog : Real.log (2 * y * (3 : ℝ) ^ (n - mZero x))
        ≤ Real.log ((M : ℝ) * 2 ^ pre ā (n - mZero x)) := by
      rw [tlo, e1]
      linarith [hlml, hPlo2, e2l, e3l, hIy1, hmargin]
    have h := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log h2y3pos, Real.exp_log hQpos] at h
  have hQhi : (M : ℝ) * 2 ^ pre ā (n - mZero x) ≤ y ^ alpha * (3 : ℝ) ^ (n - mZero x) := by
    have hyapos : (0 : ℝ) < y ^ alpha * (3 : ℝ) ^ (n - mZero x) :=
      mul_pos (Real.rpow_pos_of_pos hy0 _) (by positivity)
    have thi : Real.log (y ^ alpha * (3 : ℝ) ^ (n - mZero x))
        = alpha * Real.log y + ((n - mZero x : ℕ) : ℝ) * Real.log 3 := by
      rw [Real.log_mul (Real.rpow_pos_of_pos hy0 alpha).ne' (by positivity),
        Real.log_rpow hy0, Real.log_pow]
    have hlog : Real.log ((M : ℝ) * 2 ^ pre ā (n - mZero x))
        ≤ Real.log (y ^ alpha * (3 : ℝ) ^ (n - mZero x)) := by
      rw [thi, e1]
      linarith [hlmh, hPhi2, e2l, e3l, hIy2, hmargin, hlog2pos]
    have h := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log hQpos, Real.exp_log hyapos] at h
  -- exact real value of `N*`, then the window bounds
  obtain ⟨N, hN⟩ := hdvd
  have hcastN : (((M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā)
        / 3 ^ (n - mZero x) : ℕ) : ℝ)
      = ((M : ℝ) * 2 ^ pre ā (n - mZero x) - (fnat (n - mZero x) ā : ℝ))
          / 3 ^ (n - mZero x) := by
    rw [hN, Nat.mul_div_cancel_left N (by positivity)]
    have hNR : (M : ℝ) * 2 ^ pre ā (n - mZero x) - (fnat (n - mZero x) ā : ℝ)
        = 3 ^ (n - mZero x) * (N : ℝ) := by
      have h := congrArg (fun t : ℕ => (t : ℝ)) hN
      push_cast [Nat.cast_sub hle] at h
      exact h
    rw [hNR, mul_div_cancel_left₀ _ (by positivity : ((3 : ℝ) ^ (n - mZero x)) ≠ 0)]
  rw [mem_logWindow_iff]
  refine ⟨Nstar_odd ā hg.1 hModd ⟨N, hN⟩ hle, ?_, ?_⟩
  · rw [hcastN, le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ (n - mZero x))]
    linarith [hQlo, hf2R]
  · rw [hcastN, div_le_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ (n - mZero x))]
    have hfnn : (0 : ℝ) ≤ (fnat (n - mZero x) ā : ℝ) := Nat.cast_nonneg _
    linarith [hQhi, hfnn]

/-- **`N*` cast to ℝ** — the exact-division value `(M·2^{pre ā} − fnat)/3^k` as a real quotient
(the division is exact by the affine divisibility). -/
theorem Nstar_cast {k : ℕ} (ā : Fin k → ℕ) {M : ℕ}
    (hdvd : 3 ^ k ∣ (M * 2 ^ pre ā k - fnat k ā)) (hle : fnat k ā ≤ M * 2 ^ pre ā k) :
    (((M * 2 ^ pre ā k - fnat k ā) / 3 ^ k : ℕ) : ℝ)
      = ((M : ℝ) * 2 ^ pre ā k - (fnat k ā : ℝ)) / 3 ^ k := by
  obtain ⟨N, hN⟩ := hdvd
  rw [hN, Nat.mul_div_cancel_left N (by positivity)]
  have hNR : (M : ℝ) * 2 ^ pre ā k - (fnat k ā : ℝ) = 3 ^ k * (N : ℝ) := by
    have h := congrArg (fun t : ℕ => (t : ℝ)) hN
    push_cast [Nat.cast_sub hle] at h
    exact h
  rw [hNR, mul_div_cancel_left₀ _ (by positivity : ((3 : ℝ) ^ k) ≠ 0)]

/-- **Modulus × log clears the `E'` window floor** — `3^k·log x ≤ exp(−log^{0.7}x)·(4/3)^{m₀}·x` for
`k ≤ n₀`.  Sharpening of `cn_window_size` (i): gives `3^{n−m₀}/M ≤ log^{-1}x` uniformly on `E'`, the
relative error of the `(N*)⁻¹ ≈ 3^{n−m₀}/(M·2^{pre})` swap in (5.19).  Proof: `3^k ≤ x^{1/5}`
(`three_pow_nZero_le`) and `log L + L^{0.7} ≤ (4/5)·L` (via `log L ≤ 2L^{1/2} − 2 ≤ 2L^{0.7}` and
`L ≥ 8·L^{0.7}` from `L^{0.3} ≥ 1024^{0.3} = 8`). -/
theorem three_pow_log_le_window {x : ℝ} (hx : Real.exp 1024 ≤ x) {k : ℕ} (hk : k ≤ nZero x) :
    (3 : ℝ) ^ k * Real.log x
      ≤ Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x := by
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (1024 : ℝ)]) hx
  have hL1024 : (1024 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1024]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have h3k : (3 : ℝ) ^ k ≤ x ^ ((1 : ℝ) / 5) :=
    le_trans (pow_le_pow_right₀ (by norm_num) hk) (three_pow_nZero_le hx1.le)
  have h12 : Real.log (Real.log x ^ ((1 : ℝ) / 2)) ≤ Real.log x ^ ((1 : ℝ) / 2) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hLpos _)
  have hlogrw : Real.log (Real.log x ^ ((1 : ℝ) / 2)) = (1 / 2) * Real.log (Real.log x) :=
    Real.log_rpow hLpos _
  have h1207 : Real.log x ^ ((1 : ℝ) / 2) ≤ Real.log x ^ (0.7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hsplit : Real.log x ^ (0.3 : ℝ) * Real.log x ^ (0.7 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hLpos, show (0.3 : ℝ) + 0.7 = 1 by norm_num, Real.rpow_one]
  have h03 : (8 : ℝ) ≤ Real.log x ^ (0.3 : ℝ) := by
    have he : ((1024 : ℝ)) ^ ((0.3 : ℝ)) = 8 := by
      rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 10,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show ((10 : ℕ) : ℝ) * (0.3 : ℝ) = ((3 : ℕ) : ℝ) by push_cast; norm_num,
        Real.rpow_natCast]
      norm_num
    have h := Real.rpow_le_rpow (by norm_num) hL1024 (by norm_num : (0 : ℝ) ≤ (0.3 : ℝ))
    rwa [he] at h
  have ht7nn : (0 : ℝ) ≤ Real.log x ^ (0.7 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hexp : Real.log x * (1 / 5) + Real.log (Real.log x)
      ≤ -Real.log x ^ (0.7 : ℝ) + Real.log x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h03) ht7nn, hsplit, h12, hlogrw, h1207]
  calc (3 : ℝ) ^ k * Real.log x
      ≤ x ^ ((1 : ℝ) / 5) * Real.log x := mul_le_mul_of_nonneg_right h3k hLpos.le
    _ = Real.exp (Real.log x * (1 / 5)) * Real.exp (Real.log (Real.log x)) := by
        rw [Real.rpow_def_of_pos hxpos, Real.exp_log hLpos]
    _ = Real.exp (Real.log x * (1 / 5) + Real.log (Real.log x)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-Real.log x ^ (0.7 : ℝ) + Real.log x) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (-Real.log x ^ (0.7 : ℝ)) * x := by rw [Real.exp_add, Real.exp_log hxpos]
    _ ≤ Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x := by
        rw [mul_right_comm]
        exact le_mul_of_one_le_right (mul_pos (Real.exp_pos _) hxpos).le
          (one_le_pow₀ (by norm_num))

/-- **Nested-tsum monotonicity** — `∑'∑' f ≤ ∑'∑' g` from termwise `0 ≤ f ≤ g`, needing only the
DOMINATING family's summability (inner per-`a`, and of the inner sums). -/
theorem tsum_tsum_le_tsum_tsum {α β : Type*} {f g : α → β → ℝ}
    (hf0 : ∀ a b, 0 ≤ f a b) (hfg : ∀ a b, f a b ≤ g a b)
    (hgM : ∀ a, Summable (g a)) (hgS : Summable fun a => ∑' b, g a b) :
    (∑' a, ∑' b, f a b) ≤ ∑' a, ∑' b, g a b := by
  have hfM : ∀ a, Summable (f a) := fun a =>
    Summable.of_nonneg_of_le (hf0 a) (hfg a) (hgM a)
  have hinner : ∀ a, (∑' b, f a b) ≤ ∑' b, g a b := fun a =>
    (hfM a).tsum_le_tsum (hfg a) (hgM a)
  exact (Summable.of_nonneg_of_le (fun a => tsum_nonneg (hf0 a)) hinner hgS).tsum_le_tsum
    hinner hgS

/-- **Crude size bound on `perNHarmonic`** — `perNHarmonic ≤ C·log^{0.7}x`.  Via the (5.22) fiber
identity (rib 1, `perNHarmonic_eq_sum_cn`): `perNHarmonic = ∑_X perNGoodMass·c_n ≤ (sup c_n)·∑_X
syracZ = sup c_n ≤ C·log^{0.7}x` (`cn_bound`; `perNGoodMass ≤ syracZ` pointwise, total `syracZ` mass
`1`).  Turns the relative errors of the (5.19) reduction into absolute `O(log^{-c})` errors. -/
theorem perNHarmonic_le_at :
    ∀ x : ℝ, max X_cnBound (Real.exp 1024) ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          perNHarmonic x E n ≤ 4 * (Real.log x) ^ (0.7 : ℝ) := by
  classical
  have hcn := cn_bound_at
  set Ccn : ℝ := (4 : ℝ) with hCcndef
  set xcn : ℝ := X_cnBound with hxcndef
  have hCcn : (0 : ℝ) < Ccn := by norm_num
  intro x hx E hE y hy n hn
  have hxcn : xcn ≤ x := le_trans (le_max_left _ _) hx
  have hx1024 : Real.exp 1024 ≤ x := le_trans (le_max_right _ _) hx
  have hkn : n - mZero x ≤ nZero x := le_trans (Nat.sub_le _ _) (mem_Iy_le_nZero hn)
  haveI : NeZero (3 ^ (n - mZero x)) := ⟨by positivity⟩
  rw [perNHarmonic_eq_sum_cn x E n hx1024 hkn]
  -- pointwise `perNGoodMass ≤ syracZ` (drop the good-restriction)
  have hpoint : ∀ X : ZMod (3 ^ (n - mZero x)),
      perNGoodMass x n X ≤ ((syracZ (n - mZero x)) X).toReal := by
    intro X
    rw [perNGoodMass_eq_iid, syracZ_toReal_eq_tsum_fnat]
    refine (iid_fiber_summable _ _).tsum_le_tsum (fun ā => ?_) (iid_fiber_summable _ _)
    by_cases hgx : goodTuple x (n - mZero x) ā
        ∧ (fnat (n - mZero x) ā : ZMod (3 ^ (n - mZero x)))
            * (2 : ZMod (3 ^ (n - mZero x)))⁻¹ ^ pre ā (n - mZero x) = X
    · rw [if_pos hgx, if_pos hgx.2]
    · rw [if_neg hgx]; split_ifs
      · exact ENNReal.toReal_nonneg
      · exact le_rfl
  -- total `syracZ` mass is `1`
  have hmass1 : ∑ X : ZMod (3 ^ (n - mZero x)), ((syracZ (n - mZero x)) X).toReal = 1 := by
    have h1 : ∑ X : ZMod (3 ^ (n - mZero x)), (syracZ (n - mZero x)) X = 1 := by
      have h := (syracZ (n - mZero x)).tsum_coe
      rwa [tsum_fintype] at h
    rw [← ENNReal.toReal_sum (fun X _ => PMF.apply_ne_top _ _), h1, ENNReal.toReal_one]
  calc ∑ X : ZMod (3 ^ (n - mZero x)), perNGoodMass x n X * cn x E n X
      ≤ ∑ X : ZMod (3 ^ (n - mZero x)),
          ((syracZ (n - mZero x)) X).toReal * (Ccn * Real.log x ^ (0.7 : ℝ)) :=
        Finset.sum_le_sum fun X _ => mul_le_mul (hpoint X) (hcn x hxcn E hE y hy n hn X)
          (cn_nonneg x E n X) ENNReal.toReal_nonneg
    _ = Ccn * Real.log x ^ (0.7 : ℝ) := by rw [← Finset.sum_mul, hmass1, one_mul]

/-- Original ∃-form of the crude `perNHarmonic` size bound: delegates to
`perNHarmonic_le_at` (big-C campaign, step 2: `C := 4`, cutoff `max X_cnBound (exp 1024)`). -/
theorem perNHarmonic_le :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          perNHarmonic x E n ≤ C * (Real.log x) ^ (0.7 : ℝ) :=
  ⟨4, max X_cnBound (Real.exp 1024), by norm_num, perNHarmonic_le_at⟩

/-- **(5.19) harmonic reduction of `perNTerm`** — sub-lemma A of `perNTerm_eval`.  Each per-`n` term
equals its harmonic content divided by the harmonic normaliser `norm = ((α−1)/2)·log y`, up to a
*relative* `O(log^{-c}x)/norm` error.  Combines `perNTerm_pointmass` (affine → single point),
`logUnifOdd_apply_toReal` (point mass `= (N*)⁻¹/D_y`), `Nstar_odd`/`Nstar_mem_logWindow` (the point
is on the window), `windowMass_estimate` + `windowMass_ge_clog` (`D_y = norm + O(1)`, the
`1/D_y → 1/norm` swap), the `(N*)⁻¹ = 3^{n−m₀}/(M·2^{pre ā}−fnat) ≈ 3^{n−m₀}/(M·2^{pre ā})` relative
error (`fnat_lt_pow_mul`), and `perNHarmonic_le` to convert relative into absolute errors.
**[C9 leaf A — pure (5.19) analytic layer; does NOT consume C10.]** -/
noncomputable def c_perNHarm : ℝ := 0.3

theorem c_perNHarm_pos : 0 < c_perNHarm := by norm_num [c_perNHarm]

/-- The relative-error constant `Cε` of the (5.19) reduction, at the pinned leaf constants
`Cw = 3` (`windowMass_estimate_atC`), `cD = 1/10000` (`windowMass_ge_clog_at`)
— big-C campaign, step 2. -/
noncomputable def C_epsPerNHarm : ℝ := 2 + 3 * ((3 : ℝ) / (1 / 10000)) + 2 * 3 / (alpha - 1)

theorem C_epsPerNHarm_pos : 0 < C_epsPerNHarm := by
  unfold C_epsPerNHarm alpha; norm_num

/-- The (5.19) leaf-A constant: `Cε · CH` with `CH = 4` (`perNHarmonic_le_at`) —
big-C campaign, step 2. -/
noncomputable def C_perNHarm : ℝ := C_epsPerNHarm * 4

theorem C_perNHarm_pos : 0 < C_perNHarm :=
  mul_pos C_epsPerNHarm_pos (by norm_num)

-- HEARTBEAT: one large analytic assembly (per-(ā,M) window/harmonic algebra with two nlinarith
-- cores, plus nested-tsum summability plumbing); the many nlinarith/positivity calls exhaust the
-- default per-declaration budget cumulatively (mirrors `Nstar_mem_logWindow`).
set_option maxHeartbeats 1600000 in
open Classical in
/-- Sibling of `perNTerm_harmonic_approx` with the `c`/`C` slots pinned at
(`c_perNHarm`, `C_perNHarm`) — the `_atC` form (big-C campaign, step 2), cutoff existential
(`windowMass_estimate_atC` / `Nstar_mem_logWindow` cutoffs are existential). -/
theorem perNTerm_harmonic_approx_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNTerm x E y n - perNHarmonic x E n / ((alpha - 1) / 2 * Real.log y)|
            ≤ C_perNHarm * (Real.log x) ^ (-c_perNHarm) / ((alpha - 1) / 2 * Real.log y) := by
  rw [show c_perNHarm = 0.3 from rfl]
  classical
  obtain ⟨xw, hw⟩ := windowMass_estimate_atC
  have hDlbAll := windowMass_ge_clog_at
  have hHAll := perNHarmonic_le_at
  -- (`set` the pinned constants FIRST, then obtain `Nstar_mem_logWindow` — its statement
  -- carries `4/3` literals that `set Cw := 3`/`set CH := 4` must not abstract)
  set Cw : ℝ := (3 : ℝ) with hCwdef
  set cD : ℝ := (1 / 10000 : ℝ) with hcDdef
  set CH : ℝ := (4 : ℝ) with hCHdef
  set xD : ℝ := (2 : ℝ) ^ (2000 : ℝ) with hxDdef
  set xH : ℝ := max X_cnBound (Real.exp 1024) with hxHdef
  have hCwpos : (0 : ℝ) < Cw := by rw [hCwdef]; norm_num
  have hcDpos : (0 : ℝ) < cD := by rw [hcDdef]; norm_num
  have hCHpos : (0 : ℝ) < CH := by rw [hCHdef]; norm_num
  obtain ⟨xN, hNwin⟩ := Nstar_mem_logWindow
  have halpha1 : (0 : ℝ) < alpha - 1 := by norm_num [alpha]
  have hC1nn : (0 : ℝ) ≤ Cw / cD := (div_pos hCwpos hcDpos).le
  have hC2nn : (0 : ℝ) ≤ 2 * Cw / (alpha - 1) :=
    div_nonneg (by linarith [hCwpos]) halpha1.le
  set Cε : ℝ := 2 + 3 * (Cw / cD) + 2 * Cw / (alpha - 1) with hCεdef
  have hCεpos : 0 < Cε := by rw [hCεdef]; linarith
  have hCeq : C_perNHarm = Cε * CH := by
    rw [hCεdef, hCwdef, hcDdef, hCHdef]; unfold C_perNHarm C_epsPerNHarm; norm_num
  rw [hCeq]
  refine ⟨max (max xw xD) (max (max xH xN) (max (Real.exp 1024) (Real.exp Cε))),
    fun x hx E hE y hy n hn => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxw, hxD⟩, ⟨hxH, hxN⟩, hx1024, hxCε⟩ := hx
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx1024
  have hL1024 : (1024 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1024]; exact Real.log_le_log (Real.exp_pos _) hx1024
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hLCε : Cε ≤ Real.log x := by
    rw [← Real.log_exp Cε]; exact Real.log_le_log (Real.exp_pos _) hxCε
  have ha1 : (1 : ℝ) ≤ alpha := by norm_num [alpha]
  have ha2 : (1 : ℝ) ≤ alpha ^ 2 := by norm_num [alpha]
  have hlogy : Real.log x ≤ Real.log y := by
    rcases (by simpa [Set.mem_insert_iff] using hy :
        y = x ^ alpha ∨ y = x ^ alpha ^ 2) with h | h <;> rw [h, Real.log_rpow hxpos]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ alpha - 1) hLpos.le]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ alpha ^ 2 - 1) hLpos.le]
  set nrm := (alpha - 1) / 2 * Real.log y with hnrmdef
  have hnrmlb : (alpha - 1) / 2 * Real.log x ≤ nrm := by
    rw [hnrmdef]; exact mul_le_mul_of_nonneg_left hlogy (by linarith)
  have hnrmpos : (0 : ℝ) < nrm :=
    lt_of_lt_of_le (mul_pos (by linarith) hLpos) hnrmlb
  set D := windowMass y (y ^ alpha) with hDdef
  have hDest : |D - nrm| ≤ Cw := hw x hxw y hy
  have hDub : D ≤ nrm + Cw := by have := (abs_le.mp hDest).2; linarith
  have hDlb2 : nrm - Cw ≤ D := by have := (abs_le.mp hDest).1; linarith
  have hDlbL : cD * Real.log x ≤ D := hDlbAll x hxD y hy
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (mul_pos hcDpos hLpos) hDlbL
  have hC1L : Cw * Real.log x ≤ Cw / cD * D := by
    have h := mul_le_mul_of_nonneg_left hDlbL hC1nn
    calc Cw * Real.log x = Cw / cD * (cD * Real.log x) := by
          field_simp
      _ ≤ Cw / cD * D := h
  have hC2L : Cw * Real.log x ≤ 2 * Cw / (alpha - 1) * nrm := by
    have h := mul_le_mul_of_nonneg_left hnrmlb hC2nn
    calc Cw * Real.log x = 2 * Cw / (alpha - 1) * ((alpha - 1) / 2 * Real.log x) := by
          field_simp
      _ ≤ 2 * Cw / (alpha - 1) * nrm := h
  have hkn : n - mZero x ≤ nZero x := le_trans (Nat.sub_le _ _) (mem_Iy_le_nZero hn)
  have h3M : ∀ M : ℕ, Eprime x E M → 2 * (3 : ℝ) ^ (n - mZero x) + 2 ≤ (M : ℝ) := fun M hEp =>
    le_trans (cn_window_size hx1024 hkn (m := mZero x)).1 hEp.2.2.2.1
  have h3LM : ∀ M : ℕ, Eprime x E M →
      (3 : ℝ) ^ (n - mZero x) * Real.log x ≤ (M : ℝ) := fun M hEp =>
    le_trans (three_pow_log_le_window hx1024 hkn) hEp.2.2.2.1
  -- the two masked integrand families: `A1` = (5.19) point masses, `G2` = harmonic terms
  set A1 : (Fin (n - mZero x) → ℕ) → ℕ → ℝ := fun ā M =>
    if goodTuple x (n - mZero x) ā ∧ Eprime x E M then
      (if 3 ^ (n - mZero x) ∣ (M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā)
          ∧ fnat (n - mZero x) ā ≤ M * 2 ^ pre ā (n - mZero x) then
        (logUnifOdd y (y ^ alpha)
          ((M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā) / 3 ^ (n - mZero x))).toReal
      else 0)
    else 0 with hA1def
  set G2 : (Fin (n - mZero x) → ℕ) → ℕ → ℝ := fun ā M =>
    if goodTuple x (n - mZero x) ā ∧ Eprime x E M
        ∧ 3 ^ (n - mZero x) ∣ (M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā)
        ∧ fnat (n - mZero x) ā ≤ M * 2 ^ pre ā (n - mZero x)
    then ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹ / (M : ℝ) else 0 with hG2def
  have hA1nn : ∀ ā M, 0 ≤ A1 ā M := by
    intro ā M; rw [hA1def]; dsimp only
    split_ifs <;> first | exact ENNReal.toReal_nonneg | exact le_rfl
  have hG2nn : ∀ ā M, 0 ≤ G2 ā M := by
    intro ā M; rw [hG2def]; dsimp only
    split_ifs
    · positivity
    · exact le_rfl
  -- the (5.19) termwise band: `cL·(3^k·G2) ≤ A1 ≤ cU·(3^k·G2)`
  have hband : ∀ ā M,
      (Real.log x - Cε) / (Real.log x * nrm) * ((3 : ℝ) ^ (n - mZero x) * G2 ā M) ≤ A1 ā M
      ∧ A1 ā M ≤ (Real.log x + Cε) / (Real.log x * nrm) * ((3 : ℝ) ^ (n - mZero x) * G2 ā M) := by
    intro ā M
    rw [hA1def, hG2def]; dsimp only
    by_cases hcond : goodTuple x (n - mZero x) ā ∧ Eprime x E M
    · obtain ⟨hg, hEp⟩ := hcond
      by_cases hs : 3 ^ (n - mZero x) ∣ (M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā)
          ∧ fnat (n - mZero x) ā ≤ M * 2 ^ pre ā (n - mZero x)
      · obtain ⟨hdvd, hle⟩ := hs
        rw [if_pos ⟨hg, hEp, hdvd, hle⟩, if_pos ⟨hg, hEp⟩, if_pos ⟨hdvd, hle⟩]
        -- window/size facts for this (ā, M)
        have h3pos : (0 : ℝ) < (3 : ℝ) ^ (n - mZero x) := by positivity
        have h2Ppos : (0 : ℝ) < (2 : ℝ) ^ pre ā (n - mZero x) := by positivity
        have hM2 : 2 * (3 : ℝ) ^ (n - mZero x) + 2 ≤ (M : ℝ) := h3M M hEp
        have hML : (3 : ℝ) ^ (n - mZero x) * Real.log x ≤ (M : ℝ) := h3LM M hEp
        have hMpos : (0 : ℝ) < (M : ℝ) := by linarith [h3pos]
        have hfQR : (fnat (n - mZero x) ā : ℝ)
            < (3 : ℝ) ^ (n - mZero x) * (2 : ℝ) ^ pre ā (n - mZero x) := by
          exact_mod_cast fnat_lt_pow_mul (n - mZero x) ā
        have hfnn : (0 : ℝ) ≤ (fnat (n - mZero x) ā : ℝ) := Nat.cast_nonneg _
        have hQpos : (0 : ℝ) < (M : ℝ) * (2 : ℝ) ^ pre ā (n - mZero x) :=
          mul_pos hMpos h2Ppos
        have h2f : 2 * (fnat (n - mZero x) ā : ℝ)
            ≤ (M : ℝ) * (2 : ℝ) ^ pre ā (n - mZero x) := by
          nlinarith [hfQR, h2Ppos,
            mul_nonneg (by linarith : (0 : ℝ) ≤ (M : ℝ) - 2 * (3 : ℝ) ^ (n - mZero x))
              h2Ppos.le]
        have hfL : (fnat (n - mZero x) ā : ℝ) * Real.log x
            ≤ (M : ℝ) * (2 : ℝ) ^ pre ā (n - mZero x) := by
          nlinarith [mul_le_mul_of_nonneg_right hfQR.le hLpos.le,
            mul_nonneg
              (by linarith : (0 : ℝ) ≤ (M : ℝ) - (3 : ℝ) ^ (n - mZero x) * Real.log x)
              h2Ppos.le]
        have hQfpos : (0 : ℝ)
            < (M : ℝ) * (2 : ℝ) ^ pre ā (n - mZero x) - (fnat (n - mZero x) ā : ℝ) := by
          linarith [h2f, hQpos, hfnn]
        -- evaluate the point mass at `N*`
        have hNmem := hNwin x hxN y hy n hn ā hg M hEp.1 hEp.2.2.2.1 hEp.2.2.2.2 hdvd hle
        have hval : (logUnifOdd y (y ^ alpha)
              ((M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā)
                / 3 ^ (n - mZero x))).toReal
            = (3 : ℝ) ^ (n - mZero x)
              / (((M : ℝ) * (2 : ℝ) ^ pre ā (n - mZero x) - (fnat (n - mZero x) ā : ℝ)) * D) := by
          rw [logUnifOdd_apply_toReal_of_mem ⟨_, hNmem⟩ hNmem, Nstar_cast ā hdvd hle,
            inv_div, div_div, ← hDdef]
        have hharm : ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹ / (M : ℝ)
            = ((M : ℝ) * (2 : ℝ) ^ pre ā (n - mZero x))⁻¹ := by
          rw [mul_inv, div_eq_mul_inv]; exact mul_comm _ _
        rw [hval, hharm]
        set QR := (M : ℝ) * (2 : ℝ) ^ pre ā (n - mZero x) with hQRdef
        set fR := (fnat (n - mZero x) ā : ℝ) with hfRdef
        -- the two cross-multiplied cores (exact positive combinations; see handoff plan)
        have hcoreUP : Real.log x * nrm * QR ≤ (Real.log x + Cε) * ((QR - fR) * D) := by
          nlinarith [mul_nonneg (mul_nonneg hQpos.le hLpos.le)
              (by linarith [hDlb2] : (0 : ℝ) ≤ D + Cw - nrm),
            mul_nonneg hQpos.le (by linarith [hC1L] : (0 : ℝ) ≤ Cw / cD * D - Cw * Real.log x),
            mul_nonneg hDpos.le (by linarith [hfL] : (0 : ℝ) ≤ QR - fR * Real.log x),
            mul_nonneg hDpos.le (by linarith [h2f] : (0 : ℝ) ≤ QR - 2 * fR),
            mul_nonneg (mul_nonneg hC1nn hDpos.le) (by linarith [h2f] : (0 : ℝ) ≤ QR - 2 * fR),
            mul_nonneg (mul_nonneg (by linarith [hC1nn, hC2nn] :
                (0 : ℝ) ≤ Cw / cD + 2 * Cw / (alpha - 1)) hQfpos.le) hDpos.le,
            hCεdef]
        have hcoreDOWN : (Real.log x - Cε) * ((QR - fR) * D) ≤ Real.log x * nrm * QR := by
          nlinarith [mul_nonneg (mul_nonneg (by linarith [hLCε] :
                (0 : ℝ) ≤ Real.log x - Cε) hDpos.le) hfnn,
            mul_nonneg (mul_nonneg (by linarith [hLCε] :
                (0 : ℝ) ≤ Real.log x - Cε) hQpos.le)
              (by linarith [hDub] : (0 : ℝ) ≤ nrm + Cw - D),
            mul_nonneg hQpos.le
              (by linarith [hC2L] : (0 : ℝ) ≤ 2 * Cw / (alpha - 1) * nrm - Cw * Real.log x),
            mul_nonneg (mul_nonneg hCεpos.le hQpos.le) hCwpos.le,
            mul_nonneg (mul_nonneg (by linarith [hC1nn] : (0 : ℝ) ≤ 2 + 3 * (Cw / cD))
              hQpos.le) hnrmpos.le,
            hCεdef]
        constructor
        · -- DOWN: `cL·3^k/QR ≤ 3^k/((QR−fR)·D)`
          rw [show (Real.log x - Cε) / (Real.log x * nrm)
                * ((3 : ℝ) ^ (n - mZero x) * QR⁻¹)
              = (Real.log x - Cε) * (3 : ℝ) ^ (n - mZero x) / (Real.log x * nrm * QR) by
            rw [← div_eq_mul_inv, div_mul_div_comm, mul_assoc]]
          rw [div_le_div_iff₀ (mul_pos (mul_pos hLpos hnrmpos) hQpos)
            (mul_pos hQfpos hDpos)]
          nlinarith [mul_le_mul_of_nonneg_left hcoreDOWN h3pos.le]
        · -- UP: `3^k/((QR−fR)·D) ≤ cU·3^k/QR`
          rw [show (Real.log x + Cε) / (Real.log x * nrm)
                * ((3 : ℝ) ^ (n - mZero x) * QR⁻¹)
              = (Real.log x + Cε) * (3 : ℝ) ^ (n - mZero x) / (Real.log x * nrm * QR) by
            rw [← div_eq_mul_inv, div_mul_div_comm, mul_assoc]]
          rw [div_le_div_iff₀ (mul_pos hQfpos hDpos)
            (mul_pos (mul_pos hLpos hnrmpos) hQpos)]
          nlinarith [mul_le_mul_of_nonneg_left hcoreUP h3pos.le]
      · rw [if_neg (fun h => hs ⟨h.2.2.1, h.2.2.2⟩), if_pos ⟨hg, hEp⟩, if_neg hs]
        constructor <;> simp
    · rw [if_neg (fun h => hcond ⟨h.1, h.2.1⟩), if_neg hcond]
      constructor <;> simp
  -- summability plumbing (dominating sides)
  have hCSsumm : Summable (fun M : ℕ => if Eprime x E M then (M : ℝ)⁻¹ else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range
      (⌊Real.exp (Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x⌋₊ + 1)) (fun b hb => ?_)
    rw [if_neg]
    intro hEp
    exact hb (Finset.mem_range.mpr (by have := Nat.le_floor hEp.2.2.2.2; omega))
  have hdomG2 : ∀ ā M, G2 ā M
      ≤ ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹ * (if Eprime x E M then (M : ℝ)⁻¹ else 0) := by
    intro ā M
    rw [hG2def]; dsimp only
    by_cases h : goodTuple x (n - mZero x) ā ∧ Eprime x E M
        ∧ 3 ^ (n - mZero x) ∣ (M * 2 ^ pre ā (n - mZero x) - fnat (n - mZero x) ā)
        ∧ fnat (n - mZero x) ā ≤ M * 2 ^ pre ā (n - mZero x)
    · rw [if_pos h, if_pos h.2.1, div_eq_mul_inv]
    · rw [if_neg h]
      split_ifs
      · positivity
      · simp
  have hG2M : ∀ ā, Summable (fun M => G2 ā M) := fun ā =>
    Summable.of_nonneg_of_le (hG2nn ā) (hdomG2 ā)
      (hCSsumm.mul_left ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹)
  have hgoodsumm : Summable (fun ā : Fin (n - mZero x) → ℕ =>
      if goodTuple x (n - mZero x) ā then ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹ else 0) := by
    refine (iid_fiber_summable (n - mZero x)
      (fun ā => goodTuple x (n - mZero x) ā)).congr fun ā => ?_
    by_cases h : goodTuple x (n - mZero x) ā
    · rw [if_pos h, if_pos h, iid_geomHalf_apply_of_pos _ _ h.1,
        ENNReal.toReal_pow, ENNReal.toReal_inv, inv_pow]
      norm_num
    · rw [if_neg h, if_neg h]
  have hG2inner_le : ∀ ā, (∑' M, G2 ā M)
      ≤ (if goodTuple x (n - mZero x) ā then ((2 : ℝ) ^ pre ā (n - mZero x))⁻¹ else 0)
        * (∑' M : ℕ, if Eprime x E M then (M : ℝ)⁻¹ else 0) := by
    intro ā
    by_cases hgd : goodTuple x (n - mZero x) ā
    · rw [if_pos hgd, ← tsum_mul_left]
      exact (hG2M ā).tsum_le_tsum (hdomG2 ā) (hCSsumm.mul_left _)
    · rw [if_neg hgd, zero_mul]
      have hz : ∀ M, G2 ā M = 0 := by
        intro M; rw [hG2def]; dsimp only
        exact if_neg (fun h => hgd h.1)
      rw [tsum_congr hz, tsum_zero]
  have hG2outer : Summable (fun ā => ∑' M, G2 ā M) :=
    Summable.of_nonneg_of_le (fun ā => tsum_nonneg (hG2nn ā)) hG2inner_le
      (hgoodsumm.mul_right _)
  -- the two tsum-level bounds
  have hPT : perNTerm x E y n = ∑' ā, ∑' M, A1 ā M := by
    rw [hA1def]; exact perNTerm_pointmass x E y n
  have hHeq : perNHarmonic x E n = (3 : ℝ) ^ (n - mZero x) * ∑' ā, ∑' M, G2 ā M := by
    rw [hG2def]; rfl
  have hgMU : ∀ ā, Summable (fun M =>
      (Real.log x + Cε) / (Real.log x * nrm) * ((3 : ℝ) ^ (n - mZero x) * G2 ā M)) := fun ā =>
    ((hG2M ā).mul_left ((3 : ℝ) ^ (n - mZero x))).mul_left _
  have hpullU : ∀ ā, (∑' M, (Real.log x + Cε) / (Real.log x * nrm)
        * ((3 : ℝ) ^ (n - mZero x) * G2 ā M))
      = (Real.log x + Cε) / (Real.log x * nrm)
        * ((3 : ℝ) ^ (n - mZero x) * ∑' M, G2 ā M) := fun ā => by
    rw [tsum_mul_left, tsum_mul_left]
  have hgSU : Summable (fun ā => ∑' M, (Real.log x + Cε) / (Real.log x * nrm)
      * ((3 : ℝ) ^ (n - mZero x) * G2 ā M)) :=
    (((hG2outer.mul_left ((3 : ℝ) ^ (n - mZero x))).mul_left _).congr
      (fun ā => (hpullU ā).symm))
  have hUP : perNTerm x E y n
      ≤ (Real.log x + Cε) / (Real.log x * nrm) * perNHarmonic x E n := by
    rw [hPT, hHeq]
    calc (∑' ā, ∑' M, A1 ā M)
        ≤ ∑' ā, ∑' M, (Real.log x + Cε) / (Real.log x * nrm)
            * ((3 : ℝ) ^ (n - mZero x) * G2 ā M) :=
          tsum_tsum_le_tsum_tsum hA1nn (fun ā M => (hband ā M).2) hgMU hgSU
      _ = (Real.log x + Cε) / (Real.log x * nrm)
            * ((3 : ℝ) ^ (n - mZero x) * ∑' ā, ∑' M, G2 ā M) := by
          rw [tsum_congr hpullU, tsum_mul_left, tsum_mul_left]
  have hA1M : ∀ ā, Summable (fun M => A1 ā M) := fun ā =>
    Summable.of_nonneg_of_le (hA1nn ā) (fun M => (hband ā M).2) (hgMU ā)
  have hA1S : Summable (fun ā => ∑' M, A1 ā M) := by
    refine Summable.of_nonneg_of_le (fun ā => tsum_nonneg (hA1nn ā)) (fun ā => ?_) hgSU
    exact (hA1M ā).tsum_le_tsum (fun M => (hband ā M).2) (hgMU ā)
  have hcLnn : (0 : ℝ) ≤ (Real.log x - Cε) / (Real.log x * nrm) :=
    div_nonneg (by linarith [hLCε]) (mul_pos hLpos hnrmpos).le
  have hpullD : ∀ ā, (∑' M, (Real.log x - Cε) / (Real.log x * nrm)
        * ((3 : ℝ) ^ (n - mZero x) * G2 ā M))
      = (Real.log x - Cε) / (Real.log x * nrm)
        * ((3 : ℝ) ^ (n - mZero x) * ∑' M, G2 ā M) := fun ā => by
    rw [tsum_mul_left, tsum_mul_left]
  have hDOWN : (Real.log x - Cε) / (Real.log x * nrm) * perNHarmonic x E n
      ≤ perNTerm x E y n := by
    rw [hPT, hHeq]
    calc (Real.log x - Cε) / (Real.log x * nrm)
          * ((3 : ℝ) ^ (n - mZero x) * ∑' ā, ∑' M, G2 ā M)
        = ∑' ā, ∑' M, (Real.log x - Cε) / (Real.log x * nrm)
            * ((3 : ℝ) ^ (n - mZero x) * G2 ā M) := by
          rw [tsum_congr hpullD, tsum_mul_left, tsum_mul_left]
      _ ≤ ∑' ā, ∑' M, A1 ā M :=
          tsum_tsum_le_tsum_tsum
            (fun ā M => mul_nonneg hcLnn (mul_nonneg (by positivity) (hG2nn ā M)))
            (fun ā M => (hband ā M).1) hA1M hA1S
  -- assemble: relative → absolute error via `perNHarmonic_le`
  have hH : perNHarmonic x E n ≤ CH * Real.log x ^ (0.7 : ℝ) :=
    hHAll x hxH E hE y hy n hn
  have hHnn : 0 ≤ perNHarmonic x E n := by
    rw [hHeq]
    exact mul_nonneg (by positivity)
      (tsum_nonneg fun ā => tsum_nonneg fun M => hG2nn ā M)
  obtain ⟨t3, ht3⟩ : ∃ t, t = Real.log x ^ (-(0.3 : ℝ)) := ⟨_, rfl⟩
  have ht3nn : 0 ≤ t3 := by rw [ht3]; positivity
  have ht7eq : Real.log x ^ (0.7 : ℝ) = t3 * Real.log x := by
    rw [ht3, show Real.log x ^ (0.7 : ℝ) = Real.log x ^ (-(0.3 : ℝ) + 1) by norm_num,
      Real.rpow_add hLpos, Real.rpow_one]
  rw [ht7eq] at hH
  set H := perNHarmonic x E n with hHdef
  have hkey : Cε * H / (Real.log x * nrm) ≤ Cε * CH * t3 / nrm := by
    rw [div_le_div_iff₀ (mul_pos hLpos hnrmpos) hnrmpos]
    nlinarith [mul_le_mul_of_nonneg_left hH (mul_nonneg hCεpos.le hnrmpos.le)]
  rw [← ht3, abs_le]
  constructor
  · have hid : (Real.log x - Cε) / (Real.log x * nrm) * H - H / nrm
        = -(Cε * H / (Real.log x * nrm)) := by
      field_simp
      ring
    linarith [hDOWN, hid, hkey]
  · have hid : (Real.log x + Cε) / (Real.log x * nrm) * H - H / nrm
        = Cε * H / (Real.log x * nrm) := by
      field_simp
      ring
    linarith [hUP, hid, hkey]

/-- Sibling of `perNTerm_harmonic_approx` with the `c`-slot pinned to `c_perNHarm`; the
original delegates here.  Now delegates to `perNTerm_harmonic_approx_atC` (big-C campaign,
step 2: `C := C_perNHarm`). -/
theorem perNTerm_harmonic_approx_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNTerm x E y n - perNHarmonic x E n / ((alpha - 1) / 2 * Real.log y)|
            ≤ C * (Real.log x) ^ (-c_perNHarm) / ((alpha - 1) / 2 * Real.log y) := by
  obtain ⟨x₀, h⟩ := perNTerm_harmonic_approx_atC
  exact ⟨C_perNHarm, x₀, C_perNHarm_pos, h⟩

theorem perNTerm_harmonic_approx :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNTerm x E y n - perNHarmonic x E n / ((alpha - 1) / 2 * Real.log y)|
            ≤ C * (Real.log x) ^ (-c) / ((alpha - 1) / 2 * Real.log y) := by
  obtain ⟨C, x₀, hC, h⟩ := perNTerm_harmonic_approx_explicit
  exact ⟨c_perNHarm, C, x₀, c_perNHarm_pos, hC, h⟩

/-- The `C`-witness of `good_tuple_whp_iid` (big-C campaign, step 2): `2·C_geomTail = 4`
(the `Z` + prefix-deviation union bound doubles the `geomHalf` tail constant).  The cutoff is
kept existential — it feeds the `x₀`-threshold (via `log_rpow_mul_exp_neg_le_one` /
`Gweight_prefix_decay`), NOT `CTao`. -/
noncomputable def C_goodWhp : ℝ := 2 * C_geomTail

theorem C_goodWhp_pos : 0 < C_goodWhp := by
  unfold C_goodWhp; exact mul_pos (by norm_num) C_geomTail_pos

open Classical in
/-- `good_tuple_whp_iid` with the `C`-slot pinned to `C_goodWhp` (big-C campaign, step 2);
the cutoff stays existential.  The ratified-shape `good_tuple_whp_iid` delegates here.  Body
verbatim from the ∃-form: `set ct/Ct` re-bind the constant NAMES to `c_geomTail`/`C_geomTail`
(via `geomHalf_tail_bound_atC`) so the union-bound body ports with zero edits. -/
theorem good_tuple_whp_iid_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ k : ℕ, k ≤ nZero x →
      (∑' ā : Fin k → ℕ,
          if ¬ goodTuple x k ā then ((geomHalf.iid k) ā).toReal else 0)
        ≤ C_goodWhp * (Real.log x) ^ (-(1 : ℝ)) := by
  classical
  set ct : ℝ := c_geomTail
  set Ct : ℝ := C_geomTail
  have hct : (0 : ℝ) < ct := c_geomTail_pos
  have hCt : (0 : ℝ) < Ct := C_geomTail_pos
  have htail : ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 2 * n| then ((iidSum geomHalf n) L).toReal else 0)
        ≤ Ct * Gweight (1 + n) (ct * lam) := geomHalf_tail_bound_atC
  obtain ⟨κ, x₀g, hκ, hGdecay⟩ := Gweight_prefix_decay (d := ct) hct
  obtain ⟨x₀A, hA⟩ := log_rpow_mul_exp_neg_le_one (p := 2) (κ := κ) (θ := 0.2)
    (by norm_num) hκ (by norm_num)
  refine ⟨max x₀A (max (Real.exp 20) x₀g), fun x hx k hk => ?_⟩
  show (∑' ā : Fin k → ℕ,
      if ¬ goodTuple x k ā then ((geomHalf.iid k) ā).toReal else 0)
        ≤ 2 * Ct * (Real.log x) ^ (-(1 : ℝ))
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
        push Not at hdev
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

open Classical in
/-- **iid good-tuple whp bound (Tao (5.11)/(5.12), iid form).**  Under the `geomHalf.iid k` law, a length-`k`
tuple fails to be good with probability `≪ log^{-1}x` (for `k ≤ n₀`).  This is the iid half of
`goodTuple_prefix_dev_sum` — `¬good` means a coord is `0` (mass `0`, since `geomHalf` has no atom at `0`)
or some prefix `pre a m` deviates from `2m` by `≥ log^{0.6}x` (each `≪ exp(−c·log^{0.2}x)` via
`geomHalf_tail_bound`; sum over the `≤ k+1 ≤ log x` prefixes, then the `log x·exp(−c log^{0.2}) ≤ log^{-1}`
shrink).  No dTV transfer is needed because the base law is already `geomHalf.iid`.
Delegates to `good_tuple_whp_iid_atC` (big-C campaign, step 2: `C := C_goodWhp`). -/
theorem good_tuple_whp_iid :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ k : ℕ, k ≤ nZero x →
      (∑' ā : Fin k → ℕ,
          if ¬ goodTuple x k ā then ((geomHalf.iid k) ā).toReal else 0)
        ≤ C * (Real.log x) ^ (-(1 : ℝ)) := by
  obtain ⟨x₀, h⟩ := good_tuple_whp_iid_atC
  exact ⟨C_goodWhp, x₀, C_goodWhp_pos, h⟩

/-- The `C`-witness of `syracZ_sub_perNGoodMass_bound` (big-C campaign, step 2): a pure
passthrough of `good_tuple_whp_iid`'s constant, `C_syracZsub := C_goodWhp` (=4). -/
noncomputable def C_syracZsub : ℝ := C_goodWhp

theorem C_syracZsub_pos : 0 < C_syracZsub := C_goodWhp_pos

/-- **B1 rib 2 — the good-tuple whp residual.**  Dropping the `1_good` restriction from `perNGoodMass`
only *adds* nonnegative mass, and the total added mass over all residues is exactly `ℙ(¬good)` under the
`geomHalf.iid (n−m₀)` law, which is `≪ log^{-1} x` (mirror of `goodTuple_prefix_dev_sum`'s iid half — the
per-prefix `geomHalf_tail_bound` summed over the `≤ n₀` prefixes, no dTV transfer needed since the base
law is already `geomHalf.iid`).  So `perNGoodMass x n X ≤ syracZ(n−m₀)(X).toReal` pointwise and
`∑_X (syracZ(n−m₀)(X).toReal − perNGoodMass x n X) ≤ C·log^{-1}x`.
**[C9 leaf B1 rib — pushforward decomposition + analytic whp; does NOT consume C10.]**
`_atC` sibling (big-C campaign, step 2): `C := C_syracZsub`, cutoff existential; the ratified
∃-form delegates. -/
theorem syracZ_sub_perNGoodMass_bound_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          (∀ X : ZMod (3 ^ (n - mZero x)),
              perNGoodMass x n X ≤ ((syracZ (n - mZero x)) X).toReal) ∧
            ∑ X : ZMod (3 ^ (n - mZero x)),
                (((syracZ (n - mZero x)) X).toReal - perNGoodMass x n X)
              ≤ C_syracZsub * (Real.log x) ^ (-(1 : ℝ)) := by
  classical
  obtain ⟨x₀, hwhp⟩ := good_tuple_whp_iid_atC
  refine ⟨x₀, fun x hx E hE y hy n hn => ?_⟩
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

/-- **B1 rib 2**, ratified ∃-form: delegates to `syracZ_sub_perNGoodMass_bound_atC`
(big-C campaign, step 2: `C := C_syracZsub`). -/
theorem syracZ_sub_perNGoodMass_bound :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          (∀ X : ZMod (3 ^ (n - mZero x)),
              perNGoodMass x n X ≤ ((syracZ (n - mZero x)) X).toReal) ∧
            ∑ X : ZMod (3 ^ (n - mZero x)),
                (((syracZ (n - mZero x)) X).toReal - perNGoodMass x n X)
              ≤ C * (Real.log x) ^ (-(1 : ℝ)) := by
  obtain ⟨x₀, h⟩ := syracZ_sub_perNGoodMass_bound_atC
  exact ⟨C_syracZsub, x₀, C_syracZsub_pos, h⟩

/-- **(5.20) sub-lemma B1 — geomHalf → `syracZ` reindex** (assembled from the two ribs above).
`perNHarmonic` (inner weight the `2^{−pre ā}` iid-geomHalf mass over *good, affine-solvable* tuples)
agrees with `harmZfine` (the exact `Syrac(ℤ/3^{n−m₀}ℤ)` mass) up to `O(log^{-c}x)`.  Both reindex to
`∑_X (mass)·c_n(X)` — `harmZfine` with the full `syracZ` mass (`harmZfine_eq_sum_cn`), `perNHarmonic`
with the good-restricted `perNGoodMass` (`perNHarmonic_eq_sum_cn`).  L¹×L∞ Hölder with `0 ≤ c_n ≤
Ccn·log^{0.7}x` (`cn_bound`/`cn_nonneg`) against the `log^{-1}x` whp residual
(`syracZ_sub_perNGoodMass_bound`) gives net `log^{0.7−1} = log^{-0.3}`.
**[C9 leaf B1 — pure reindex + whp; does NOT consume C10.]** -/
noncomputable def c_harmZfine : ℝ := 0.3

theorem c_harmZfine_pos : 0 < c_harmZfine := by norm_num [c_harmZfine]

/-- The `C`-witness of `perNHarmonic_eq_harmZfine_approx` (big-C campaign, step 2):
`C_harmZfine := 4·C_syracZsub` (=16) — the `cn` sup constant `Ccn = 4` (`cn_bound_at`) times
the whp-residual constant `C_syracZsub`, from the L¹×L∞ Hölder step. -/
noncomputable def C_harmZfine : ℝ := 4 * C_syracZsub

theorem C_harmZfine_pos : 0 < C_harmZfine := by
  unfold C_harmZfine; exact mul_pos (by norm_num) C_syracZsub_pos

/-- Sibling of `perNHarmonic_eq_harmZfine_approx` with BOTH slots pinned (`c := c_harmZfine`,
`C := C_harmZfine`); the `_at` form (big-C campaign, step 2), cutoff existential.  Uses
`cn_bound_at` (Ccn=4) + `syracZ_sub_perNGoodMass_bound_atC` (Cw=C_syracZsub); `set Ccn/Cw`
re-bind the constant names so the Hölder body ports verbatim. -/
theorem perNHarmonic_eq_harmZfine_approx_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNHarmonic x E n - harmZfine x E n| ≤ C_harmZfine * (Real.log x) ^ (-c_harmZfine) := by
  obtain ⟨x₀w, hwhp⟩ := syracZ_sub_perNGoodMass_bound_atC
  have hcn := cn_bound_at
  rw [show c_harmZfine = 0.3 from rfl]
  refine ⟨max (max X_cnBound x₀w) (Real.exp 1024), fun x hx E hE y hy n hn => ?_⟩
  show |perNHarmonic x E n - harmZfine x E n| ≤ 4 * C_syracZsub * Real.log x ^ (-(0.3 : ℝ))
  set Ccn : ℝ := (4 : ℝ) with hCcndef
  set Cw : ℝ := C_syracZsub with hCwdef
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxcn, hxw⟩, hxe1024⟩ := hx
  have hLpos : (0 : ℝ) < Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1024) hxe1024
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
  rw [perNHarmonic_eq_sum_cn x E n hxe1024
      (le_trans (Nat.sub_le _ _) (mem_Iy_le_nZero hn)),
    harmZfine_eq_sum_cn, ← Finset.sum_sub_distrib]
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

/-- Sibling of `perNHarmonic_eq_harmZfine_approx` with the `c`-slot pinned to `c_harmZfine`;
the original delegates here.  Now delegates to `perNHarmonic_eq_harmZfine_approx_atC`
(big-C campaign, step 2: `C := C_harmZfine`). -/
theorem perNHarmonic_eq_harmZfine_approx_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNHarmonic x E n - harmZfine x E n| ≤ C * (Real.log x) ^ (-c_harmZfine) := by
  obtain ⟨x₀, h⟩ := perNHarmonic_eq_harmZfine_approx_atC
  exact ⟨C_harmZfine, x₀, C_harmZfine_pos, h⟩

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
noncomputable def c_mainZbridge : ℝ := 1

theorem c_mainZbridge_pos : 0 < c_mainZbridge := by norm_num [c_mainZbridge]

/-- The B2 bridge constant, symbolic (big-C campaign, step 2): `4·C_fineScale 1.7·
(1/200000)^{-1.7}` (the `cn` arm, the C10 mixing constant at `A = 1.7`, and the
`m₀ ≥ log x/200000` conversion). -/
noncomputable def C_mainZbridge : ℝ :=
  4 * C_fineScale 1.7 * (1 / 200000 : ℝ) ^ (-(1.7 : ℝ))

theorem C_mainZbridge_pos : 0 < C_mainZbridge := by
  unfold C_mainZbridge
  exact mul_pos (mul_pos (by norm_num) (C_fineScale_pos 1.7))
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- The B2 bridge cutoff, symbolic (big-C campaign, step 2). -/
noncomputable def X_mainZbridge : ℝ :=
  max (Real.exp 200000) (max X_twoMZero (max X_mZeroLin X_cnBound))

/-- Sibling of `harmZfine_to_mainZ` with the `c`-slot pinned to `c_mainZbridge` and the
`C`/`x₀` slots at (`C_mainZbridge`, `X_mainZbridge`) — the `_at` form (big-C campaign, step 2). -/
theorem harmZfine_to_mainZ_at :
    ∀ x : ℝ, X_mainZbridge ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |harmZfine x E n - mainZ x E| ≤ C_mainZbridge * (Real.log x) ^ (-c_mainZbridge) := by
  have htwo := two_mZero_le_of_mem_Iy_at
  have hmzlin := mZero_ge_lin_at
  have hCfsm : (0 : ℝ) < C_fineScale 1.7 := C_fineScale_pos 1.7
  have hfsm := fine_scale_mixing_at 1.7 (by norm_num)
  have hCcnpos : (0 : ℝ) < (4 : ℝ) := by norm_num
  have hcnb := cn_bound_at
  unfold C_mainZbridge X_mainZbridge
  rw [show c_mainZbridge = 1 from rfl]
  set Cfsm : ℝ := C_fineScale 1.7 with hCfsmdef
  set Ccn : ℝ := (4 : ℝ) with hCcndef
  set x1 : ℝ := X_twoMZero with hx1def
  set x2 : ℝ := X_mZeroLin with hx2def
  set xcn : ℝ := X_cnBound with hxcndef
  intro x hx E hE y hy n hn
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
  have hkey := harmZfine_sub_mainZ_le_osc hmn hcn
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

/-- Sibling of `harmZfine_to_mainZ` with the `c`-slot pinned to `c_mainZbridge`,
original `∃`-form: delegates to the `_at` sibling (big-C campaign, step 2). -/
theorem harmZfine_to_mainZ_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |harmZfine x E n - mainZ x E| ≤ C * (Real.log x) ^ (-c_mainZbridge) :=
  ⟨C_mainZbridge, X_mainZbridge, C_mainZbridge_pos, harmZfine_to_mainZ_at⟩

/-- **(5.20) harmonic → `Z` reduction** — sub-lemma B of `perNTerm_eval`, **the sole C10 consumer**.
The window-free harmonic content agrees with Tao's `Z` (5.21) up to `O(log^{-c}x)`.  **PROVED** from the
geomHalf→`syracZ` reindex `perNHarmonic_eq_harmZfine_approx` (B1) and the `fine_scale_mixing` scale
bridge `harmZfine_to_mainZ` (B2, the C10 seam) via the triangle through the shared `harmZfine`:
`perNHarmonic ≈ harmZfine ≈ mainZ`.  All of C10's involvement in C9 is now isolated to B2. -/
theorem perNHarmonic_eq_harmZfine_approx :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNHarmonic x E n - harmZfine x E n| ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := perNHarmonic_eq_harmZfine_approx_explicit
  exact ⟨c_harmZfine, C, x₀, c_harmZfine_pos, hC, h⟩

theorem harmZfine_to_mainZ :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |harmZfine x E n - mainZ x E| ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := harmZfine_to_mainZ_explicit
  exact ⟨c_mainZbridge, C, x₀, c_mainZbridge_pos, hC, h⟩

noncomputable def c_harmonicZ : ℝ := min c_harmZfine c_mainZbridge

theorem c_harmonicZ_pos : 0 < c_harmonicZ :=
  lt_min c_harmZfine_pos c_mainZbridge_pos

/-- The explicit (5.20) `harmonic_to_Z` constant: triangle through `harmZfine` combining
B1 (`C_harmZfine`) and B2 (`C_mainZbridge`) — big-C campaign, step 2. -/
noncomputable def C_harmonicZ : ℝ := C_harmZfine + C_mainZbridge

theorem C_harmonicZ_pos : 0 < C_harmonicZ :=
  add_pos C_harmZfine_pos C_mainZbridge_pos

/-- Sibling of `harmonic_to_Z` with the `c`/`C` slots pinned at
(`c_harmonicZ`, `C_harmonicZ`) — the `_atC` form (big-C campaign, step 2), cutoff
existential (B1's cutoff is existential). -/
theorem harmonic_to_Z_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNHarmonic x E n - mainZ x E| ≤ C_harmonicZ * (Real.log x) ^ (-c_harmonicZ) := by
  obtain ⟨x1, h1⟩ := perNHarmonic_eq_harmZfine_approx_atC
  have h2 := harmZfine_to_mainZ_at
  set C1 : ℝ := C_harmZfine with hC1def
  set C2 : ℝ := C_mainZbridge with hC2def
  set x2 : ℝ := X_mainZbridge with hx2def
  have hC1 : 0 < C1 := C_harmZfine_pos
  have hC2 : 0 < C2 := C_mainZbridge_pos
  set c1 : ℝ := c_harmZfine with hc1def
  set c2 : ℝ := c_mainZbridge with hc2def
  have hc1 : 0 < c1 := c_harmZfine_pos
  have hc2 : 0 < c2 := c_mainZbridge_pos
  rw [show C_harmonicZ = C1 + C2 from rfl, show c_harmonicZ = min c1 c2 from rfl]
  refine ⟨max (max x1 x2) (Real.exp 1), fun x hx E hE y hy n hn => ?_⟩
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

/-- Sibling of `harmonic_to_Z` with the `c`-slot pinned to `c_harmonicZ`; the original
delegates here.  Now delegates to `harmonic_to_Z_atC` (big-C campaign, step 2:
`C := C_harmonicZ`). -/
theorem harmonic_to_Z_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNHarmonic x E n - mainZ x E| ≤ C * (Real.log x) ^ (-c_harmonicZ) := by
  obtain ⟨x₀, h⟩ := harmonic_to_Z_atC
  exact ⟨C_harmonicZ, x₀, C_harmonicZ_pos, h⟩

theorem harmonic_to_Z :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNHarmonic x E n - mainZ x E| ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := harmonic_to_Z_explicit
  exact ⟨c_harmonicZ, C, x₀, c_harmonicZ_pos, hC, h⟩

/-- An indicator expectation is at most the total mass `1`. -/
theorem PMF.expect_indicator_le_one {α : Type*} (p : PMF α) (S : Set α) :
    p.expect (Set.indicator S 1) ≤ 1 := by
  have hsum1 : Summable (fun a => (p a).toReal) :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)
  have htot : ∑' a, (p a).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe]; simp
  have hterm : ∀ a, (p a).toReal * Set.indicator S 1 a ≤ (p a).toReal := by
    intro a
    by_cases h : a ∈ S
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  have htermnn : ∀ a, 0 ≤ (p a).toReal * Set.indicator S 1 a := fun a =>
    mul_nonneg ENNReal.toReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) a)
  have hfs : Summable (fun a => (p a).toReal * Set.indicator S 1 a) :=
    Summable.of_nonneg_of_le htermnn hterm hsum1
  calc p.expect (Set.indicator S 1) = ∑' a, (p a).toReal * Set.indicator S 1 a := rfl
    _ ≤ ∑' a, (p a).toReal := hfs.tsum_le_tsum hterm hsum1
    _ = 1 := htot

-- HEARTBEAT: floor/ceiling lattice count over rpow window endpoints; many small linarith calls
-- over rpow atoms exhaust the default per-declaration budget cumulatively.
set_option maxHeartbeats 800000 in
/-- **`#I_y` lattice bracket** — the integer count of the (5.9) interval is its real length
`(α−1)·log y/log(4/3) − 2·log^{0.8}x` up to `±1`.  Elementary floor/ceiling count once the window
is wide (`≥ 0.002·log x`) and sits inside `[0, n₀]`.  Lower half feeds `mainZ_bound` (via the
a-posteriori `Z ≪ 1`); both halves are the lattice core of `Iy_count_ratio` (5.9). -/
theorem Iy_card_bracket :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
      (alpha - 1) * Real.log y / Real.log (4 / 3) - 2 * Real.log x ^ (0.8 : ℝ) - 1
          ≤ ((Iy x y).card : ℝ)
        ∧ ((Iy x y).card : ℝ)
          ≤ (alpha - 1) * Real.log y / Real.log (4 / 3) - 2 * Real.log x ^ (0.8 : ℝ) + 1 := by
  refine ⟨Real.exp ((2000 : ℝ) ^ (5 : ℕ)), fun x hx y hy => ?_⟩
  have hyval : y = x ^ alpha ∨ y = x ^ alpha ^ 2 := by simpa [Set.mem_insert_iff] using hy
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hLT5 : (2000 : ℝ) ^ (5 : ℕ) ≤ Real.log x := by
    rw [← Real.log_exp ((2000 : ℝ) ^ (5 : ℕ))]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hLbig : (3.2e16 : ℝ) ≤ Real.log x := by
    rw [show (3.2e16 : ℝ) = (2000 : ℝ) ^ (5 : ℕ) by norm_num]; exact hLT5
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hy0 : (0 : ℝ) < y := by
    rcases hyval with h | h <;> rw [h] <;> exact Real.rpow_pos_of_pos hxpos _
  have halpha1 : (0 : ℝ) < alpha - 1 := by norm_num [alpha]
  have hly_ge : Real.log x ≤ Real.log y := by
    rcases hyval with h | h
    · rw [h, Real.log_rpow hxpos]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ alpha - 1 by norm_num [alpha]) hLpos.le]
    · rw [h, Real.log_rpow hxpos]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ alpha ^ 2 - 1 by norm_num [alpha]) hLpos.le]
  have hlynn : (0 : ℝ) ≤ Real.log y := le_trans hLpos.le hly_ge
  have hly_le : Real.log y ≤ alpha ^ 2 * Real.log x := by
    rcases hyval with h | h
    · rw [h, Real.log_rpow hxpos]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ alpha ^ 2 - alpha by norm_num [alpha]) hLpos.le]
    · rw [h, Real.log_rpow hxpos]
  have hlog43pos : (0 : ℝ) < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hlog43_ub : Real.log (4 / 3) ≤ 1 / 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num); linarith
  have hlog43_lb : (1 / 4 : ℝ) ≤ Real.log (4 / 3) := by
    have h34 : Real.log (3 / 4) ≤ 3 / 4 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have hinv : Real.log (4 / 3) = -Real.log (3 / 4) := by
      rw [show (3 : ℝ) / 4 = (4 / 3)⁻¹ by norm_num, Real.log_inv, neg_neg]
    linarith [hinv]
  -- `log^{0.8}x ≤ log x/2000`
  have h02 : (2000 : ℝ) ≤ Real.log x ^ (0.2 : ℝ) := by
    have hcomp : ((2000 : ℝ) ^ (5 : ℕ)) ^ (0.2 : ℝ) = 2000 := by
      rw [← Real.rpow_natCast (2000 : ℝ) 5, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2000),
        show ((5 : ℕ) : ℝ) * (0.2 : ℝ) = 1 by norm_num, Real.rpow_one]
    calc (2000 : ℝ) = ((2000 : ℝ) ^ (5 : ℕ)) ^ (0.2 : ℝ) := hcomp.symm
      _ ≤ Real.log x ^ (0.2 : ℝ) := Real.rpow_le_rpow (by positivity) hLT5 (by norm_num)
  have hsplit : Real.log x ^ (0.2 : ℝ) * Real.log x ^ (0.8 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hLpos, show (0.2 : ℝ) + 0.8 = 1 by norm_num, Real.rpow_one]
  have h08nn : (0 : ℝ) ≤ Real.log x ^ (0.8 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hL08 : Real.log x ^ (0.8 : ℝ) ≤ Real.log x / 2000 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2000)]
    nlinarith [mul_le_mul_of_nonneg_right h02 h08nn, hsplit]
  -- endpoint values and the width
  have hIyHi_eq : IyHi x y
      = (alpha * Real.log y - Real.log x) / Real.log (4 / 3) - Real.log x ^ (0.8 : ℝ) := by
    rw [IyHi, Real.log_div (Real.rpow_pos_of_pos hy0 alpha).ne' hxpos.ne', Real.log_rpow hy0]
  have hIyLo_eq : IyLo x y
      = (Real.log y - Real.log x) / Real.log (4 / 3) + Real.log x ^ (0.8 : ℝ) := by
    rw [IyLo, Real.log_div hy0.ne' hxpos.ne']
  have hW : IyHi x y - IyLo x y
      = (alpha - 1) * Real.log y / Real.log (4 / 3) - 2 * Real.log x ^ (0.8 : ℝ) := by
    rw [hIyHi_eq, hIyLo_eq]; ring
  -- width lower bound `≥ 0.002·log x`
  have hwidth_term : 3 * ((alpha - 1) * Real.log y)
      ≤ (alpha - 1) * Real.log y / Real.log (4 / 3) := by
    rw [le_div_iff₀ hlog43pos]
    have h3nn : (0 : ℝ) ≤ 3 * ((alpha - 1) * Real.log y) :=
      mul_nonneg (by norm_num) (mul_nonneg halpha1.le hlynn)
    nlinarith [mul_le_mul_of_nonneg_left hlog43_ub h3nn]
  have hkey1 : 0.003 * Real.log x ≤ 3 * ((alpha - 1) * Real.log y) := by
    nlinarith [mul_le_mul_of_nonneg_left hly_ge
        (show (0 : ℝ) ≤ 3 * (alpha - 1) by norm_num [alpha]),
      mul_le_mul_of_nonneg_right (show (0.003 : ℝ) ≤ 3 * (alpha - 1) by norm_num [alpha])
        hLpos.le]
  have hwidth : 0.002 * Real.log x ≤ IyHi x y - IyLo x y := by
    rw [hW]; linarith [hwidth_term, hL08, hkey1]
  -- endpoints sit in `[0, n₀]`
  have hIyLo_nn : (0 : ℝ) ≤ IyLo x y := by
    rw [hIyLo_eq]
    have : (0 : ℝ) ≤ (Real.log y - Real.log x) / Real.log (4 / 3) :=
      div_nonneg (by linarith [hly_ge]) hlog43pos.le
    linarith [h08nn]
  have hIyHi_nn : (0 : ℝ) ≤ IyHi x y := by linarith [hwidth, hIyLo_nn, hLpos]
  have hIyHi_le_nZ : IyHi x y ≤ (nZero x : ℝ) := by
    have hann : (0 : ℝ) ≤ alpha * Real.log y - Real.log x := by
      have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ alpha by norm_num [alpha]) hlynn
      rw [one_mul] at h
      linarith [hly_ge]
    have hup : alpha * Real.log y - Real.log x ≤ 0.0031 * Real.log x := by
      have h1 := mul_le_mul_of_nonneg_left hly_le (show (0 : ℝ) ≤ alpha by norm_num [alpha])
      have h2 := mul_le_mul_of_nonneg_right
        (show alpha * alpha ^ 2 ≤ 1.0031 by norm_num [alpha]) hLpos.le
      nlinarith [h1, h2]
    have hdiv4 : (alpha * Real.log y - Real.log x) / Real.log (4 / 3)
        ≤ 4 * (alpha * Real.log y - Real.log x) := by
      rw [div_le_iff₀ hlog43pos]
      nlinarith [mul_le_mul_of_nonneg_left hlog43_lb hann]
    have hlog2ub : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hnZ : Real.log x / 7 - 1 ≤ (nZero x : ℝ) := by
      have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hfl := Nat.lt_floor_add_one (Real.log x / (10 * Real.log 2))
      have h7 : Real.log x / 7 ≤ Real.log x / (10 * Real.log 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [hLpos.le, hlog2ub]
      rw [nZero]
      linarith [hfl, h7]
    rw [hIyHi_eq]
    linarith [hdiv4, hup, hnZ, hLbig, h08nn]
  -- the integer interval
  have haR_lt : ((⌈IyLo x y⌉₊ : ℝ)) < IyLo x y + 1 := Nat.ceil_lt_add_one hIyLo_nn
  have haR_ge : IyLo x y ≤ ((⌈IyLo x y⌉₊ : ℝ)) := Nat.le_ceil _
  have hbR_gt : IyHi x y - 1 < ((⌊IyHi x y⌋₊ : ℝ)) := by
    have := Nat.lt_floor_add_one (IyHi x y); linarith
  have hbR_le : ((⌊IyHi x y⌋₊ : ℝ)) ≤ IyHi x y := Nat.floor_le hIyHi_nn
  have hab : ⌈IyLo x y⌉₊ ≤ ⌊IyHi x y⌋₊ := by
    have : ((⌈IyLo x y⌉₊ : ℝ)) < ((⌊IyHi x y⌋₊ : ℝ)) := by linarith [hwidth, hLbig]
    exact_mod_cast this.le
  have hsub1 : Finset.Icc ⌈IyLo x y⌉₊ ⌊IyHi x y⌋₊ ⊆ Iy x y := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Iy, Finset.mem_filter, Finset.mem_range]
    have h1 : IyLo x y ≤ (n : ℝ) := le_trans haR_ge (by exact_mod_cast hn.1)
    have h2 : (n : ℝ) ≤ IyHi x y := le_trans (by exact_mod_cast hn.2) hbR_le
    have h4 : n ≤ nZero x := by exact_mod_cast le_trans h2 hIyHi_le_nZ
    exact ⟨by omega, h1, h2⟩
  have hsub2 : Iy x y ⊆ Finset.Icc ⌈IyLo x y⌉₊ ⌊IyHi x y⌋₊ := by
    intro n hn
    rw [Iy, Finset.mem_filter] at hn
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr hn.2.1, Nat.le_floor hn.2.2⟩
  have hcardR : ((Finset.Icc ⌈IyLo x y⌉₊ ⌊IyHi x y⌋₊).card : ℝ)
      = ((⌊IyHi x y⌋₊ : ℝ)) + 1 - ((⌈IyLo x y⌉₊ : ℝ)) := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega : ⌈IyLo x y⌉₊ ≤ ⌊IyHi x y⌋₊ + 1)]
    push_cast; ring
  have hle1 : ((Finset.Icc ⌈IyLo x y⌉₊ ⌊IyHi x y⌋₊).card : ℝ) ≤ ((Iy x y).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub1
  have hle2 : ((Iy x y).card : ℝ) ≤ ((Finset.Icc ⌈IyLo x y⌉₊ ⌊IyHi x y⌋₊).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub2
  constructor
  · rw [← hW]; linarith [hle1, hcardR, haR_lt, hbR_gt]
  · rw [← hW]; linarith [hle2, hcardR, haR_ge, hbR_le]

/-- **The `mainZ = O(1)` constant** (big-C campaign, step 2): (5.19) leaf + (5.20) leaf +
the `0.001`-count inversion of `1 + C8`. -/
noncomputable def C_mainZ : ℝ := C_perNHarm + C_harmonicZ + 1000 * (1 + C_fpApprox)

theorem C_mainZ_pos : 0 < C_mainZ :=
  add_pos (add_pos C_perNHarm_pos C_harmonicZ_pos)
    (by nlinarith [C_fpApprox_pos])

-- HEARTBEAT: assembles four ∃-lemmas and a lattice count; the cumulative linarith/nlinarith
-- budget exceeds the default.
set_option maxHeartbeats 800000 in
/-- Sibling of `mainZ_bound` with the `C`-slot pinned at `C_mainZ` — the `_atC` form
(big-C campaign, step 2), cutoff existential.  **`mainZ` is `O(1)`** — via Tao's
a-posteriori route (p.26): `Z ≍ (log(4/3)/2)·ℙ(Pass∈E) = O(1)`.
Non-circular assembly from PROVED pieces: for every `n ∈ I_y` (at `y = x^α`),
`perNTerm ≥ (mainZ − O(1))/norm` by the (5.19) reduction (`perNTerm_harmonic_approx`) and the
(5.20) `Z`-reduction (`harmonic_to_Z`); summing over the `≥ 0.001·log x` values of `n`
(`Iy_card_bracket`) gives `#I_y·(mainZ − O(1))/norm ≤ approxMainTerm ≤ 1 + O(log^{-c}x)` by
Prop 5.2 (`first_passage_approx`, C8) and `ℙ ≤ 1`; since `#I_y/norm ≫ 1`, `mainZ ≪ 1`. -/
theorem mainZ_bound_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) → |mainZ x E| ≤ C_mainZ := by
  classical
  obtain ⟨xA, hA⟩ := perNTerm_harmonic_approx_atC
  obtain ⟨xB, hB⟩ := harmonic_to_Z_atC
  obtain ⟨x8, h8⟩ := first_passage_approx_atC
  obtain ⟨xI, hIcard⟩ := Iy_card_bracket
  set cA : ℝ := c_perNHarm with hcAdef
  set CA : ℝ := C_perNHarm with hCAdef
  set cB : ℝ := c_harmonicZ with hcBdef
  set CB : ℝ := C_harmonicZ with hCBdef
  set c8 : ℝ := c_fpApprox with hc8def
  set C8 : ℝ := C_fpApprox with hC8def
  have hcA : 0 < cA := c_perNHarm_pos
  have hCA : 0 < CA := C_perNHarm_pos
  have hcB : 0 < cB := c_harmonicZ_pos
  have hCB : 0 < CB := C_harmonicZ_pos
  have hc8 : 0 < c8 := c_fpApprox_pos
  have hC8 : 0 < C8 := C_fpApprox_pos
  rw [show C_mainZ = CA + CB + 1000 * (1 + C8) from rfl]
  refine ⟨max (max xA xB)
      (max x8 (max xI (Real.exp ((2000 : ℝ) ^ (5 : ℕ))))),
    fun x hx E hE => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxA, hxB⟩, hx8, hxI, hxT⟩ := hx
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxT
  have hLT5 : (2000 : ℝ) ^ (5 : ℕ) ≤ Real.log x := by
    rw [← Real.log_exp ((2000 : ℝ) ^ (5 : ℕ))]
    exact Real.log_le_log (Real.exp_pos _) hxT
  have hLbig : (3.2e16 : ℝ) ≤ Real.log x := by
    rw [show (3.2e16 : ℝ) = (2000 : ℝ) ^ (5 : ℕ) by norm_num]; exact hLT5
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  -- work in the window `y = x^α`
  have hy : (x ^ alpha) ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ) := Set.mem_insert _ _
  have hlogy : Real.log (x ^ alpha) = alpha * Real.log x := Real.log_rpow hxpos alpha
  have hnrmpos : (0 : ℝ) < (alpha - 1) / 2 * Real.log (x ^ alpha) := by
    rw [hlogy]
    exact mul_pos (by norm_num [alpha]) (mul_pos (by norm_num [alpha]) hLpos)
  have hnrm_le_L : (alpha - 1) / 2 * Real.log (x ^ alpha) ≤ Real.log x := by
    rw [hlogy]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - (alpha - 1) / 2 * alpha by norm_num [alpha])
      hLpos.le]
  -- `mainZ ≥ 0`
  have hZnn : 0 ≤ mainZ x E := by
    rw [mainZ]
    refine tsum_nonneg fun M => ?_
    split_ifs
    · exact div_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg) (Nat.cast_nonneg M)
    · exact le_rfl
  -- per-`n` lower bound: `mainZ − (CA + CB) ≤ perNTerm·norm`
  have hLcA : Real.log x ^ (-cA) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hLcB : Real.log x ^ (-cB) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hLc8 : Real.log x ^ (-c8) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hlow : ∀ n ∈ Iy x (x ^ alpha),
      mainZ x E - (CA + CB)
        ≤ perNTerm x E (x ^ alpha) n * ((alpha - 1) / 2 * Real.log (x ^ alpha)) := by
    intro n hn
    have h1 := (abs_le.mp (hA x hxA E hE _ hy n hn)).1
    have h2 := (abs_le.mp (hB x hxB E hE _ hy n hn)).1
    -- clear the divisions in `h1` by multiplying through `norm > 0`
    have h1' : perNHarmonic x E n - CA * Real.log x ^ (-cA)
        ≤ perNTerm x E (x ^ alpha) n * ((alpha - 1) / 2 * Real.log (x ^ alpha)) := by
      have hmul := mul_le_mul_of_nonneg_right h1 hnrmpos.le
      rw [sub_mul, div_mul_cancel₀ _ hnrmpos.ne', neg_mul,
        div_mul_cancel₀ _ hnrmpos.ne'] at hmul
      linarith
    have hCAle : CA * Real.log x ^ (-cA) ≤ CA :=
      mul_le_of_le_one_right hCA.le hLcA
    have hCBle : CB * Real.log x ^ (-cB) ≤ CB :=
      mul_le_of_le_one_right hCB.le hLcB
    linarith
  -- sum over `I_y`, compare with the (5.8) formula and `ℙ ≤ 1`
  have hsum : ((Iy x (x ^ alpha)).card : ℝ) * (mainZ x E - (CA + CB))
      ≤ approxMainTerm x E (x ^ alpha) * ((alpha - 1) / 2 * Real.log (x ^ alpha)) := by
    have h := Finset.card_nsmul_le_sum (Iy x (x ^ alpha))
      (fun n => perNTerm x E (x ^ alpha) n * ((alpha - 1) / 2 * Real.log (x ^ alpha)))
      (mainZ x E - (CA + CB)) hlow
    rw [nsmul_eq_mul] at h
    rw [approxMainTerm_eq_sum_perNTerm, Finset.sum_mul]
    exact h
  have h8x := (abs_le.mp (h8 x hx8 E hE _ hy)).1
  have hexp1 : (logUnifOdd (x ^ alpha) ((x ^ alpha) ^ alpha)).expect
      (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1) ≤ 1 :=
    PMF.expect_indicator_le_one _ _
  have hAMT : approxMainTerm x E (x ^ alpha) ≤ 1 + C8 := by
    have hC8le : C8 * Real.log x ^ (-c8) ≤ C8 := mul_le_of_le_one_right hC8.le hLc8
    linarith
  -- the count lower bound `0.001·log x ≤ #I_y`
  have hcard : 0.001 * Real.log x ≤ ((Iy x (x ^ alpha)).card : ℝ) := by
    have hbr := (hIcard x hxI _ hy).1
    have hlog43pos : (0 : ℝ) < Real.log (4 / 3) := Real.log_pos (by norm_num)
    have hlog43_ub : Real.log (4 / 3) ≤ 1 / 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num); linarith
    have hlynn : (0 : ℝ) ≤ Real.log (x ^ alpha) := by
      rw [hlogy]; exact mul_nonneg (by norm_num [alpha]) hLpos.le
    have hwt : 3 * ((alpha - 1) * Real.log (x ^ alpha))
        ≤ (alpha - 1) * Real.log (x ^ alpha) / Real.log (4 / 3) := by
      rw [le_div_iff₀ hlog43pos]
      have h3nn : (0 : ℝ) ≤ 3 * ((alpha - 1) * Real.log (x ^ alpha)) :=
        mul_nonneg (by norm_num)
          (mul_nonneg (show (0 : ℝ) ≤ alpha - 1 by norm_num [alpha]) hlynn)
      nlinarith [mul_le_mul_of_nonneg_left hlog43_ub h3nn]
    have h02 : (2000 : ℝ) ≤ Real.log x ^ (0.2 : ℝ) := by
      have hcomp : ((2000 : ℝ) ^ (5 : ℕ)) ^ (0.2 : ℝ) = 2000 := by
        rw [← Real.rpow_natCast (2000 : ℝ) 5, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2000),
          show ((5 : ℕ) : ℝ) * (0.2 : ℝ) = 1 by norm_num, Real.rpow_one]
      calc (2000 : ℝ) = ((2000 : ℝ) ^ (5 : ℕ)) ^ (0.2 : ℝ) := hcomp.symm
        _ ≤ Real.log x ^ (0.2 : ℝ) := Real.rpow_le_rpow (by positivity) hLT5 (by norm_num)
    have hsplit : Real.log x ^ (0.2 : ℝ) * Real.log x ^ (0.8 : ℝ) = Real.log x := by
      rw [← Real.rpow_add hLpos, show (0.2 : ℝ) + 0.8 = 1 by norm_num, Real.rpow_one]
    have h08nn : (0 : ℝ) ≤ Real.log x ^ (0.8 : ℝ) := Real.rpow_nonneg hLpos.le _
    have hL08 : Real.log x ^ (0.8 : ℝ) ≤ Real.log x / 2000 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2000)]
      nlinarith [mul_le_mul_of_nonneg_right h02 h08nn, hsplit]
    have hgrow : 0.003 * Real.log x ≤ 3 * ((alpha - 1) * Real.log (x ^ alpha)) := by
      rw [hlogy]
      nlinarith [mul_le_mul_of_nonneg_right
        (show (0.003 : ℝ) ≤ 3 * ((alpha - 1) * alpha) by norm_num [alpha]) hLpos.le]
    linarith [hbr, hwt, hL08, hgrow, hLbig]
  -- collapse
  rw [abs_of_nonneg hZnn]
  by_cases hZsmall : mainZ x E ≤ CA + CB
  · nlinarith [hC8.le]
  · push Not at hZsmall
    have hpos : (0 : ℝ) < mainZ x E - (CA + CB) := by linarith
    have hA1 : (0.001 * Real.log x) * (mainZ x E - (CA + CB))
        ≤ ((Iy x (x ^ alpha)).card : ℝ) * (mainZ x E - (CA + CB)) :=
      mul_le_mul_of_nonneg_right hcard hpos.le
    have hA2 : approxMainTerm x E (x ^ alpha) * ((alpha - 1) / 2 * Real.log (x ^ alpha))
        ≤ (1 + C8) * Real.log x := by
      have h1 : approxMainTerm x E (x ^ alpha) * ((alpha - 1) / 2 * Real.log (x ^ alpha))
          ≤ (1 + C8) * ((alpha - 1) / 2 * Real.log (x ^ alpha)) :=
        mul_le_mul_of_nonneg_right hAMT hnrmpos.le
      have h2 : (1 + C8) * ((alpha - 1) / 2 * Real.log (x ^ alpha)) ≤ (1 + C8) * Real.log x :=
        mul_le_mul_of_nonneg_left hnrm_le_L (by linarith)
      linarith
    have hfin : 0.001 * (mainZ x E - (CA + CB)) ≤ 1 + C8 := by
      have hchain : (0.001 * Real.log x) * (mainZ x E - (CA + CB)) ≤ (1 + C8) * Real.log x := by
        linarith [hA1, hsum, hA2]
      nlinarith [hchain, hLpos, hpos]
    linarith

/-- **`mainZ` is `O(1)`** — the ∃-form.  Now delegates to `mainZ_bound_atC`
(big-C campaign, step 2: `C := C_mainZ`). -/
theorem mainZ_bound :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) → |mainZ x E| ≤ C := by
  obtain ⟨x₀, h⟩ := mainZ_bound_atC
  exact ⟨C_mainZ, x₀, C_mainZ_pos, h⟩

/-- **Per-`n` evaluation (5.19)+(5.20).**  For each `n ∈ I_y`, the per-`n` term equals the
window-independent `mainZ x E` divided by the harmonic normaliser `((α−1)/2)·log y`, up to a *relative*
`O(log^{-c} x)` error.  **PROVED** from the (5.19) harmonic reduction `perNTerm_harmonic_approx` (leaf A),
the (5.20) `Z`-reduction `harmonic_to_Z` (leaf B, the C10 seam), and `windowMass_estimate`
(`D_y = (α−1)/2·log y + O(1)`): the harmonic content `perNHarmonic ≈ mainZ` and dividing by
`windowMass ≈ norm` gives `perNTerm ≈ mainZ/norm` (the `windowMass`↔`norm` swap costs only
`O(1/norm²) = O(L^{-2}) ≤ L^{-1-c}`). -/
noncomputable def c_perNTermEval : ℝ := min c_perNHarm c_harmonicZ

theorem c_perNTermEval_pos : 0 < c_perNTermEval :=
  lt_min c_perNHarm_pos c_harmonicZ_pos

/-- The per-`n` evaluation constant: leaf A + leaf B, triangle through `perNHarmonic`
(big-C campaign, step 2). -/
noncomputable def C_perNTermEval : ℝ := C_perNHarm + C_harmonicZ

theorem C_perNTermEval_pos : 0 < C_perNTermEval :=
  add_pos C_perNHarm_pos C_harmonicZ_pos

/-- Sibling of `perNTerm_eval` with the `c`/`C` slots pinned at
(`c_perNTermEval`, `C_perNTermEval`) — the `_atC` form (big-C campaign, step 2), cutoff
existential (both legs' cutoffs are existential). -/
theorem perNTerm_eval_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNTerm x E y n - mainZ x E / ((alpha - 1) / 2 * Real.log y)|
            ≤ C_perNTermEval * (Real.log x) ^ (-c_perNTermEval)
              / ((alpha - 1) / 2 * Real.log y) := by
  obtain ⟨xA, hA⟩ := perNTerm_harmonic_approx_atC
  obtain ⟨xB, hB⟩ := harmonic_to_Z_atC
  set CA : ℝ := C_perNHarm with hCAdef
  set CB : ℝ := C_harmonicZ with hCBdef
  have hCA : 0 < CA := C_perNHarm_pos
  have hCB : 0 < CB := C_harmonicZ_pos
  set cA : ℝ := c_perNHarm with hcAdef
  set cB : ℝ := c_harmonicZ with hcBdef
  have hcA : 0 < cA := c_perNHarm_pos
  have hcB : 0 < cB := c_harmonicZ_pos
  rw [show C_perNTermEval = CA + CB from rfl, show c_perNTermEval = min cA cB from rfl]
  refine ⟨max (max xA xB) (Real.exp 1), fun x hx E hE y hy n hn => ?_⟩
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

/-- Sibling of `perNTerm_eval` with the `c`-slot pinned to `c_perNTermEval`; the original
delegates here.  Now delegates to `perNTerm_eval_atC` (big-C campaign, step 2:
`C := C_perNTermEval`). -/
theorem perNTerm_eval_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNTerm x E y n - mainZ x E / ((alpha - 1) / 2 * Real.log y)|
            ≤ C * (Real.log x) ^ (-c_perNTermEval) / ((alpha - 1) / 2 * Real.log y) := by
  obtain ⟨x₀, h⟩ := perNTerm_eval_atC
  exact ⟨C_perNTermEval, x₀, C_perNTermEval_pos, h⟩

theorem perNTerm_eval :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
          |perNTerm x E y n - mainZ x E / ((alpha - 1) / 2 * Real.log y)|
            ≤ C * (Real.log x) ^ (-c) / ((alpha - 1) / 2 * Real.log y) := by
  obtain ⟨C, x₀, hC, h⟩ := perNTerm_eval_explicit
  exact ⟨c_perNTermEval, C, x₀, c_perNTermEval_pos, hC, h⟩

noncomputable def c_IyRatio : ℝ := 0.2

theorem c_IyRatio_pos : 0 < c_IyRatio := by norm_num [c_IyRatio]

/-- **Interval count (5.9).**  `#I_y = (1+O(log^{-c}x))·(α−1)/log(4/3)·log y`, rendered as the ratio to
the harmonic normaliser: `#I_y / (((α−1)/2)·log y) = 2/log(4/3) + O(log^{-c}x)`.  This is the pure
lattice-point count `#{n∈[IyLo,IyHi]}` = interval length `+ O(1)` (via `IyHi−IyLo = (α−1)log y/log(4/3)
− 2log^{0.8}x`), whose ratio telescopes the window into the **y-free** `2/log(4/3)`. -/
theorem Iy_count_ratio_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        |((Iy x y).card : ℝ) / ((alpha - 1) / 2 * Real.log y) - 2 / Real.log (4 / 3)|
          ≤ 6000 * (Real.log x) ^ (-c_IyRatio) := by
  obtain ⟨xB, hB⟩ := Iy_card_bracket
  rw [show c_IyRatio = 0.2 from rfl]
  refine ⟨max xB (Real.exp ((2000 : ℝ) ^ (5 : ℕ))),
    fun x hx y hy => ?_⟩
  have hxB : xB ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp ((2000 : ℝ) ^ (5 : ℕ)) ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hLT5 : (2000 : ℝ) ^ (5 : ℕ) ≤ Real.log x := by
    rw [← Real.log_exp ((2000 : ℝ) ^ (5 : ℕ))]
    exact Real.log_le_log (Real.exp_pos _) hxe
  have hLpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le (by positivity) hLT5
  have hL1 : (1 : ℝ) ≤ Real.log x := le_trans (by norm_num) hLT5
  have hyval : y = x ^ alpha ∨ y = x ^ alpha ^ 2 := by simpa [Set.mem_insert_iff] using hy
  have hy0 : (0 : ℝ) < y := by
    rcases hyval with h | h <;> rw [h] <;> exact Real.rpow_pos_of_pos hxpos _
  have halpha1 : (0 : ℝ) < alpha - 1 := by norm_num [alpha]
  have hly_ge : Real.log x ≤ Real.log y := by
    rcases hyval with h | h
    · rw [h, Real.log_rpow hxpos]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ alpha - 1 by norm_num [alpha]) hLpos.le]
    · rw [h, Real.log_rpow hxpos]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ alpha ^ 2 - 1 by norm_num [alpha]) hLpos.le]
  have hlog43pos : (0 : ℝ) < Real.log (4 / 3) := Real.log_pos (by norm_num)
  obtain ⟨hlo, hhi⟩ := hB x hxB y hy
  -- opaque rpow atoms: `u = log^{0.8}x`, `v = log^{-0.2}x`, glued by `v·log x = u`
  set L := Real.log x with hLdef
  set u := L ^ (0.8 : ℝ) with hudef
  set v := L ^ (-(0.2 : ℝ)) with hvdef
  have hvL : v * L = u := by
    rw [hudef, hvdef, ← Real.rpow_add_one hLpos.ne']; norm_num
  have hu1 : (1 : ℝ) ≤ u := by
    calc (1 : ℝ) = (1 : ℝ) ^ (0.8 : ℝ) := (Real.one_rpow _).symm
      _ ≤ u := Real.rpow_le_rpow (by norm_num) hL1 (by norm_num)
  have hvpos : (0 : ℝ) < v := Real.rpow_pos_of_pos hLpos _
  -- the normaliser: `nrm = 0.0005·log y ≥ 0.0005·L > 0`
  set nrm := (alpha - 1) / 2 * Real.log y with hnrmdef
  have hnrmpos : (0 : ℝ) < nrm :=
    mul_pos (by norm_num [alpha]) (lt_of_lt_of_le hLpos hly_ge)
  have hnrm_lb : (alpha - 1) / 2 * L ≤ nrm :=
    mul_le_mul_of_nonneg_left hly_ge (by norm_num [alpha])
  -- exact ratio identity: the window midpoint `W = (α−1)·log y/log(4/3)` has `W/nrm = 2/log(4/3)`
  have key : ((Iy x y).card : ℝ) / nrm - 2 / Real.log (4 / 3)
      = (((Iy x y).card : ℝ) - (alpha - 1) * Real.log y / Real.log (4 / 3)) / nrm := by
    have hlogy_ne : Real.log y ≠ 0 := (lt_of_lt_of_le hLpos hly_ge).ne'
    rw [hnrmdef]
    field_simp
  rw [key, abs_div, abs_of_pos hnrmpos]
  -- numerator bracket: `|card − W| ≤ 2u + 1` from `Iy_card_bracket`
  have hnum : |((Iy x y).card : ℝ) - (alpha - 1) * Real.log y / Real.log (4 / 3)|
      ≤ 2 * u + 1 := by
    rw [abs_le]
    constructor <;> nlinarith [hu1]
  calc |((Iy x y).card : ℝ) - (alpha - 1) * Real.log y / Real.log (4 / 3)| / nrm
      ≤ (2 * u + 1) / nrm := div_le_div_of_nonneg_right hnum hnrmpos.le
    _ ≤ (2 * u + 1) / ((alpha - 1) / 2 * L) :=
        div_le_div_of_nonneg_left (by nlinarith [hu1])
          (mul_pos (by norm_num [alpha]) hLpos) hnrm_lb
    _ ≤ 6000 * L ^ (-(0.2 : ℝ)) := by
        rw [← hvdef, div_le_iff₀ (mul_pos (by norm_num [alpha] : (0:ℝ) < (alpha - 1)/2) hLpos)]
        -- `6000·v·0.0005·L = 3·v·L = 3u ≥ 2u + 1` since `u ≥ 1`
        have halpha : alpha - 1 = 0.001 := by norm_num [alpha]
        rw [halpha]
        nlinarith [hvL, hu1, hvpos.le, hLpos.le]

/-- Original explicit-`c` form of the (5.9) count ratio: delegates to `Iy_count_ratio_atC`
(big-C campaign, step 2: `C := 6000`, cutoff existential via `Iy_card_bracket`). -/
theorem Iy_count_ratio_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        |((Iy x y).card : ℝ) / ((alpha - 1) / 2 * Real.log y) - 2 / Real.log (4 / 3)|
          ≤ C * (Real.log x) ^ (-c_IyRatio) := by
  obtain ⟨x₀, h⟩ := Iy_count_ratio_atC
  exact ⟨6000, x₀, by norm_num, h⟩

theorem Iy_count_ratio :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        |((Iy x y).card : ℝ) / ((alpha - 1) / 2 * Real.log y) - 2 / Real.log (4 / 3)|
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := Iy_count_ratio_explicit
  exact ⟨c_IyRatio, C, x₀, c_IyRatio_pos, hC, h⟩

/-- Effective-constants campaign: the `c`-witness of the cs branch (`approxMainTerm_to_Z` /
`approxMainTerm_window_stable`). By the step-1 trace this equals `1/5`. -/
noncomputable def c_approxToZ : ℝ := min c_IyRatio c_perNTermEval

theorem c_approxToZ_pos : 0 < c_approxToZ :=
  lt_min c_IyRatio_pos c_perNTermEval_pos

/-- The (5.21) main-term evaluation constant (big-C campaign, step 2): count-ratio
(`6000`) × per-`n` evaluation, plus `mainZ`-bound × count-ratio. -/
noncomputable def C_approxToZ : ℝ :=
  (2 / Real.log (4 / 3) + 6000) * C_perNTermEval + C_mainZ * 6000

theorem C_approxToZ_pos : 0 < C_approxToZ :=
  add_pos
    (mul_pos (add_pos (by positivity : (0 : ℝ) < 2 / Real.log (4 / 3)) (by norm_num))
      C_perNTermEval_pos)
    (mul_pos C_mainZ_pos (by norm_num))

/-- Sibling of `approxMainTerm_to_Z` with the `c`/`C` slots pinned at
(`c_approxToZ`, `C_approxToZ`) — the `_atC` form (big-C campaign, step 2), cutoff
existential.  (5.21) main-term evaluation:
`approxMainTerm x E y = (2 / log(4/3))·mainZ x E + O(log^{-c} x)`.  This subsumes Tao's pp.25–27
chain: the single-value mass formula (5.19)
`ℙ(Aff_ā(N_y)=M) = (1+O(x^{-c}))·2^{-|ā|}·3^{n−m₀} / (((α−1)/2)·log y · M)`; the harmonic-sum reduction
(5.20)→`Z` — **where Lemma 5.3 (`c_n(X)≪1`) and Prop 1.14 (`fine_scale_mixing`, C10) are consumed**;
and the interval count `#I_y` (5.9) `= (1+O(log^{-c}x))·(α−1)/log(4/3)·log y`, whose ratio to the
`((α−1)/2)·log y` normaliser telescopes to the **window-free** `2/log(4/3)`.

**[C9 CRUX — the sole remaining C9 hole; this is where C10 enters.]**  Target is `y`-independent (`Z`),
which is the faithful rendering of the paper's cancellation; `approxMainTerm_window_stable` below is a
one-line triangle over this. -/
theorem approxMainTerm_to_Z_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |approxMainTerm x E y - 2 / Real.log (4 / 3) * mainZ x E|
            ≤ C_approxToZ * (Real.log x) ^ (-c_approxToZ) := by
  obtain ⟨x1, h9⟩ := Iy_count_ratio_atC
  obtain ⟨xz, hZb⟩ := mainZ_bound_atC
  obtain ⟨x2, hp⟩ := perNTerm_eval_atC
  set C1 : ℝ := (6000 : ℝ) with hC1def
  set Cz : ℝ := C_mainZ with hCzdef
  set C2 : ℝ := C_perNTermEval with hC2def
  have hC1 : (0 : ℝ) < C1 := by rw [hC1def]; norm_num
  have hCz : 0 < Cz := C_mainZ_pos
  have hC2 : 0 < C2 := C_perNTermEval_pos
  set c1 : ℝ := c_IyRatio with hc1def
  set c2 : ℝ := c_perNTermEval with hc2def
  have hc1 : 0 < c1 := c_IyRatio_pos
  have hc2 : 0 < c2 := c_perNTermEval_pos
  have hlog43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have halpha0 : 0 < alpha := by norm_num [alpha]
  have halpha1 : 0 < alpha - 1 := by norm_num [alpha]
  have hb2 : (0 : ℝ) < 2 / Real.log (4 / 3) := by positivity
  rw [show c_approxToZ = min c1 c2 from rfl,
    show C_approxToZ = (2 / Real.log (4 / 3) + C1) * C2 + Cz * C1 from rfl]
  refine ⟨max (max (max x1 xz) x2) (Real.exp 1), fun x hx E hE y hy => ?_⟩
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

/-- Original explicit-`c` form of the (5.21) evaluation: delegates to
`approxMainTerm_to_Z_atC` (big-C campaign, step 2: `C := C_approxToZ`). -/
theorem approxMainTerm_to_Z_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |approxMainTerm x E y - 2 / Real.log (4 / 3) * mainZ x E|
            ≤ C * (Real.log x) ^ (-c_approxToZ) := by
  obtain ⟨x₀, h⟩ := approxMainTerm_to_Z_atC
  exact ⟨C_approxToZ, x₀, C_approxToZ_pos, h⟩

theorem approxMainTerm_to_Z :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |approxMainTerm x E y - 2 / Real.log (4 / 3) * mainZ x E|
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := approxMainTerm_to_Z_explicit
  exact ⟨c_approxToZ, C, x₀, c_approxToZ_pos, hC, h⟩

/-- The window-stability constant: two triangle legs through `mainZ`
(big-C campaign, step 2). -/
noncomputable def C_windowStable : ℝ := 2 * C_approxToZ

theorem C_windowStable_pos : 0 < C_windowStable :=
  mul_pos (by norm_num) C_approxToZ_pos

/-- Sibling of `approxMainTerm_window_stable` with the `c`/`C` slots pinned at
(`c_approxToZ`, `C_windowStable`) — the `_atC` form (big-C campaign, step 2), cutoff
existential.  **Lemma 5.3 + (5.18)–(5.21)** — window-stability of the affine main term.
`approxMainTerm x E y` agrees across the two nested windows `y = x^α` and `y = x^{α²}` up to
`O(log^{-c} x)`.  PROVED from `approxMainTerm_to_Z` by the triangle inequality through the
window-independent `mainZ x E`: both windows evaluate to `(2/log(4/3))·mainZ x E + O(log^{-c} x)`
with the **same** `mainZ`, so their difference is `O(log^{-c} x)`. -/
theorem approxMainTerm_window_stable_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        |approxMainTerm x E (x ^ alpha) - approxMainTerm x E (x ^ alpha ^ 2)|
          ≤ C_windowStable * (Real.log x) ^ (-c_approxToZ) := by
  obtain ⟨x₀, hZ⟩ := approxMainTerm_to_Z_atC
  set C : ℝ := C_approxToZ with hCdef
  have hC : 0 < C := C_approxToZ_pos
  set c : ℝ := c_approxToZ with hcdef
  have hc : 0 < c := c_approxToZ_pos
  rw [show C_windowStable = 2 * C from rfl]
  refine ⟨x₀, fun x hx E hE => ?_⟩
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

/-- Original explicit-`c` form of the window stability: delegates to
`approxMainTerm_window_stable_atC` (big-C campaign, step 2: `C := C_windowStable`). -/
theorem approxMainTerm_window_stable_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        |approxMainTerm x E (x ^ alpha) - approxMainTerm x E (x ^ alpha ^ 2)|
          ≤ C * (Real.log x) ^ (-c_approxToZ) := by
  obtain ⟨x₀, h⟩ := approxMainTerm_window_stable_atC
  exact ⟨C_windowStable, x₀, C_windowStable_pos, h⟩

theorem approxMainTerm_window_stable :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        |approxMainTerm x E (x ^ alpha) - approxMainTerm x E (x ^ alpha ^ 2)|
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := approxMainTerm_window_stable_explicit
  exact ⟨c_approxToZ, C, x₀, c_approxToZ_pos, hC, h⟩

/-- Effective-constants campaign: the `c`-witness of the WATCHED `stabilization` (Prop 1.11) —
the three-way min over the c7 / c8 / cs branches. By the step-1 trace it equals the c7 value
`c_valSumTail = 1/(640000000·log 2)`. -/
noncomputable def c_stab : ℝ := min (min c_valSumTail c_fpApprox) c_approxToZ

theorem c_stab_pos : 0 < c_stab :=
  lt_min (lt_min c_valSumTail_pos c_fpApprox_pos) c_approxToZ_pos

-- RATIFY-3: window endpoints spelled per the spec's guidance as `[x^α, x^{α²}]` and
-- `[x^{α²}, x^{α³}]` (using `alpha^2`, `alpha^3`), which the SKELETON-SPEC flagged as the
-- intended reading of its nested-pow shorthand. Judge against §5 pp.25–28.
-- RELOCATED (2026-07-15) from `Sec5/FirstPassage.lean` VERBATIM (byte-identical statement) so the
-- assembly can consume C8 (`first_passage_approx`) + C10 (`fine_scale_mixing`) without an import cycle.
/-- **Proposition 1.11** (stabilization): the passage-location law is stable across the
two nearby log-windows, and non-passage is rare. The spine's key input. -/
theorem stabilization_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      (∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1)
          ≤ C * x ^ (-c_stab)) ∧
      PMF.dTV ((logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)).map (passLoc ⌊x⌋₊))
              ((logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3)).map (passLoc ⌊x⌋₊))
        ≤ C * (Real.log x) ^ (-c_stab) := by
  obtain ⟨C7, x7, hC7, h7⟩ := first_passage_nonescape_explicit
  obtain ⟨C8, x8, hC8, h8⟩ := first_passage_approx_explicit
  obtain ⟨Cs, xs, hCs, hstab⟩ := approxMainTerm_window_stable_explicit
  set c7 : ℝ := c_valSumTail with hc7def
  set c8 : ℝ := c_fpApprox with hc8def
  set cs : ℝ := c_approxToZ with hcsdef
  have hc7 : 0 < c7 := c_valSumTail_pos
  have hc8 : 0 < c8 := c_fpApprox_pos
  have hcs : 0 < cs := c_approxToZ_pos
  rw [show c_stab = min (min c7 c8) cs from rfl]
  refine ⟨C7 + 4 * C8 + 2 * Cs,
    max (max (max x7 x8) xs) (Real.exp 1),
    by positivity, ?_⟩
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

-- RATIFY-3 (see above): statement byte-identical to the ratified pin; the proof body lives in
-- `stabilization_explicit` (effective-constants campaign, sibling + delegate).
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
  obtain ⟨C, x₀, hC, h⟩ := stabilization_explicit
  exact ⟨c_stab, C, x₀, c_stab_pos, hC, h⟩

end TaoCollatz
