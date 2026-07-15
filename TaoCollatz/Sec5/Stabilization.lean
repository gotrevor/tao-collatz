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
  sorry

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
