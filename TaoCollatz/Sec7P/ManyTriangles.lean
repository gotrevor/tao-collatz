/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.Localization

/-!
# Finer-scale many-triangle geometry for the tilted holding law

This module starts the `Pascal(p)` port of Tao's Case-2 white-exit argument.  It
connects the explicit first-passage localization box to the `epsP` triangle
family: a supported endpoint captured by the family cannot remain inside both
the height and transverse radii, because the start triangle contributes no
endpoint and every other triangle is farther away than the box diagonal.
-/

namespace TaoCollatz.Sec7P

open scoped ENNReal

/-- Phase points beyond the right edge of the half strip. -/
def outStripSetP (n : ℕ) : Set (ℕ × ℤ) := {q : ℕ × ℤ | n / 2 < q.1}

/-- Finer-scale white points in renewal coordinates.  The phase coordinate is
one column behind the renewal coordinate, exactly as in Tao's `whiteSet`. -/
def whiteSetP (n ξ : ℕ) : Set (ℕ × ℤ) :=
  {q : ℕ × ℤ | 1 ≤ q.1 ∧ whiteP n ξ (q.1 - 1) q.2}

/-- Finer-scale white renewal points which have not crossed the right edge of
the half strip. -/
def whiteStripP (n ξ : ℕ) : Set (ℕ × ℤ) :=
  {q : ℕ × ℤ | q.1 ≤ n / 2 ∧ q ∈ whiteSetP n ξ}

/-- Phase points whose predecessor column lies in a finer-scale family triangle. -/
def phaseInFamilyP {n ξ : ℕ} (F : TriangleFamilyP n ξ) : Set (ℕ × ℤ) :=
  {q : ℕ × ℤ | ∃ t ∈ F.T,
    ((q.1 - 1, q.2) : ℕ × ℤ) ∈ triangle t.1 t.2.1 t.2.2}

/-- A first-passage endpoint clears the apex of its starting triangle. -/
theorem endpoint_notMem_start_triangleP {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {s : ℕ} {l lΔ : ℤ} (hs : (s : ℤ) = lΔ - l)
    {e : ℕ × ℤ} (he : e ∈ (fpDistP p hp0 hp1 s).support)
    {j₀ a : ℕ} {sΔ : ℝ} :
    ((a, l + e.2) : ℕ × ℤ) ∉ triangle j₀ lΔ sΔ := by
  intro hmem
  have hgt := fpDistP_support_snd_gt p hp0 hp1 s e he
  have h2 : l + e.2 ≤ lΔ := hmem.2.1
  omega

/-- Deterministic half of the tilted white-exit localization.  If a supported
endpoint is captured by some finer-scale family triangle, it must violate the
height radius `Y` or the fixed transverse radius `300`, provided the resulting
`X × Y` box fits inside the `epsP` separation scale. -/
theorem phaseInFamilyP_support_imp_localization_bad {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) {n ξ X Y : ℕ}
    (F : TriangleFamilyP n ξ) {m : ℕ} (hmn : m ≤ n / 2)
    {l : ℤ} (hl : 1 ≤ n / 2 - m)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ F.T)
    (hmem : (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2)
    {s : ℕ} (hs : (s : ℤ) = t.2.1 - l)
    (hXY : (5 : ℝ) * Y + 300 ≤ 16 * X)
    (hsepXY : (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 <
      ((1 / 10 : ℝ) * Real.log (1 / (epsP : ℝ))) ^ 2)
    {e : ℕ × ℤ}
    (he : e ∈ (fpDistP p (by linarith) (by linarith) s).support)
    (hphase : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ phaseInFamilyP F) :
    (s : ℝ) + Y ≤ (e.2 : ℝ) ∨
      (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ) := by
  by_contra hgood
  push Not at hgood
  obtain ⟨t', ht', hmem'⟩ := hphase
  have hcolEq : n / 2 - m + e.1 - 1 = n / 2 - m - 1 + e.1 := by omega
  have hmemPhase : ((n / 2 - m - 1 + e.1, l + e.2) : ℕ × ℤ) ∈
      triangle t'.1 t'.2.1 t'.2.2 := by
    simpa only [hcolEq] using hmem'
  have hne : t ≠ t' := by
    intro heq
    subst t'
    exact endpoint_notMem_start_triangleP (p := p) (by linarith) (by linarith)
      hs he hmemPhase
  set a : ℕ := e.1 - X with ha
  have ha_le : a ≤ e.1 := by omega
  have he_le : e.1 ≤ a + X := by omega
  have hsR : (s : ℝ) = (t.2.1 : ℝ) - (l : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hs
    push_cast at h
    exact h
  have he2R : (e.2 : ℝ) < (s : ℝ) + Y := hgood.1
  have hfaceRat : (16 : ℝ) * a ≤ 5 * s := by
    by_cases heX : e.1 ≤ X
    · have ha0 : a = 0 := by omega
      rw [ha0]
      norm_num
    · have hacast : (a : ℝ) = (e.1 : ℝ) - X := by
        rw [ha, Nat.cast_sub (by omega : X ≤ e.1)]
      rw [hacast]
      have hXY' : (5 : ℝ) * Y + 300 ≤ 16 * X := hXY
      nlinarith [hgood.2]
  have hlogSlope : 5 * Real.log 9 < 16 * Real.log 2 := by
    have hp : (9 : ℝ) ^ 5 < (2 : ℝ) ^ 16 := by norm_num
    have hl' := Real.log_lt_log (by positivity : (0 : ℝ) < (9 : ℝ) ^ 5) hp
    rw [Real.log_pow, Real.log_pow] at hl'
    norm_num at hl' ⊢
    exact hl'
  have hface : (a : ℝ) * Real.log 9 ≤ (s : ℝ) * Real.log 2 := by
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hlog9 : (0 : ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
    have hslack : (0 : ℝ) ≤ (s : ℝ) * (16 * Real.log 2 - 5 * Real.log 9) :=
      mul_nonneg hs0 (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hfaceRat hlog9
    nlinarith
  have hproj := triangle_top_mem_add hmem hs hface
  have hsep := F.separated t ht t' ht' hne
    ((n / 2 - m - 1 + a, t.2.1) : ℕ × ℤ) hproj
    ((n / 2 - m - 1 + e.1, l + e.2) : ℕ × ℤ) hmemPhase
  have hjlo : -(X : ℝ) ≤
      ((n / 2 - m - 1 + a : ℕ) : ℝ) - (n / 2 - m - 1 + e.1 : ℕ) := by
    have heR : (e.1 : ℝ) ≤ (a : ℝ) + X := by exact_mod_cast he_le
    push_cast
    linarith
  have hjhi :
      ((n / 2 - m - 1 + a : ℕ) : ℝ) - (n / 2 - m - 1 + e.1 : ℕ)
        ≤ X := by
    have haR : (a : ℝ) ≤ (e.1 : ℝ) := by exact_mod_cast ha_le
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) X]
  have hjsq :
      (((n / 2 - m - 1 + a : ℕ) : ℝ) - (n / 2 - m - 1 + e.1 : ℕ)) ^ 2
        ≤ (X : ℝ) ^ 2 := by nlinarith
  have hegt : (s : ℤ) < e.2 :=
    fpDistP_support_snd_gt p (by linarith) (by linarith) s e he
  have hvlo : -(Y : ℝ) ≤ (t.2.1 : ℝ) - ((l + e.2 : ℤ) : ℝ) := by
    push_cast
    linarith
  have hvhi : (t.2.1 : ℝ) - ((l + e.2 : ℤ) : ℝ) ≤ Y := by
    have hlo : (s : ℝ) < (e.2 : ℝ) := by exact_mod_cast hegt
    push_cast
    linarith
  have hvsq : ((t.2.1 : ℝ) - ((l + e.2 : ℤ) : ℝ)) ^ 2 ≤ (Y : ℝ) ^ 2 := by
    nlinarith
  linarith

/-- The deterministic capture implication at the explicit campaign box. -/
theorem phaseInFamilyP_support_imp_localization_bad_explicit {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5) {n ξ : ℕ}
    (F : TriangleFamilyP n ξ) {m : ℕ} (hmn : m ≤ n / 2)
    {l : ℤ} (hl : 1 ≤ n / 2 - m)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ F.T)
    (hmem : (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2)
    {s : ℕ} (hs : (s : ℤ) = t.2.1 - l)
    {e : ℕ × ℤ}
    (he : e ∈ (fpDistP p (by linarith) (by linarith) s).support)
    (hphase : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ phaseInFamilyP F) :
    (s : ℝ) + 12000 ≤ (e.2 : ℝ) ∨
      (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ) := by
  exact phaseInFamilyP_support_imp_localization_bad hp0 hp1 F hmn hl ht hmem hs
    localization_boxP_numeric.1 localization_boxP_numeric.2 he hphase

/-- The first-passage mass captured by the finer-scale triangle family is at
most `1/8`, uniformly over the Pascal window.  The start triangle has zero
mass, while capture by a foreign triangle implies the explicit localization
bad event. -/
theorem fpDistP_any_triangle_le :
    ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ∀ F : TriangleFamilyP n ξ, ∀ m : ℕ, m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      ∑' e : ℕ × ℤ,
        (fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e).toReal *
          Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2) ≤ 1 / 8 := by
  classical
  intro p hp0 hp1 n ξ F m hmn l hl t ht hmem s hs
  let hp0' : 0 < p := by linarith
  let hp1' : p < 1 := by linarith
  let fpLaw := fpDistP p hp0' hp1' s
  let bad : ℕ × ℤ → Prop := fun e =>
    (s : ℝ) + 12000 ≤ (e.2 : ℝ) ∨
      (300 : ℝ) ≤ 16 * (e.1 : ℝ) - 5 * (e.2 : ℝ)
  let captured : ℕ × ℤ → Prop := fun e =>
    ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ phaseInFamilyP F
  set P : ℝ≥0∞ := ∑' e : ℕ × ℤ, if captured e then fpLaw e else 0 with hP
  set B : ℝ≥0∞ := ∑' e : ℕ × ℤ, if bad e then fpLaw e else 0 with hB
  have hPB : P ≤ B := by
    rw [hP, hB]
    refine ENNReal.tsum_le_tsum fun e => ?_
    by_cases hc : captured e
    · rw [if_pos hc]
      by_cases hz : fpLaw e = 0
      · rw [hz]
        exact bot_le
      · have he : e ∈ fpLaw.support := by rwa [PMF.mem_support_iff]
        have hb := phaseInFamilyP_support_imp_localization_bad_explicit hp0 hp1 F
          hmn hl ht hmem hs he hc
        rw [if_pos hb]
    · rw [if_neg hc]
      exact bot_le
  have hBle : B ≤ (1 : ℝ≥0∞) / 8 := by
    rw [hB]
    exact fpDistP_localization_le_eighth hp0 hp1 s
  have hPtop : P ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) (hPB.trans hBle)
  have hLHS :
      (∑' e : ℕ × ℤ, (fpLaw e).toReal *
        Set.indicator (phaseInFamilyP F) 1
          (n / 2 - m + e.1, l + e.2)) = P.toReal := by
    rw [hP, ENNReal.tsum_toReal_eq (fun e => by
      split_ifs
      exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top])]
    refine tsum_congr fun e => ?_
    by_cases hc : captured e
    · rw [if_pos hc, Set.indicator_of_mem hc, Pi.one_apply, mul_one]
    · rw [if_neg hc, Set.indicator_of_notMem hc, mul_zero, ENNReal.toReal_zero]
  change (∑' e : ℕ × ℤ, (fpLaw e).toReal *
    Set.indicator (phaseInFamilyP F) 1
      (n / 2 - m + e.1, l + e.2)) ≤ 1 / 8
  rw [hLHS]
  have hto : P.toReal ≤ ((1 : ℝ≥0∞) / 8).toReal :=
    ENNReal.toReal_mono (by finiteness) (hPB.trans hBle)
  norm_num at hto ⊢
  exact hto

/-- The Case-2 first-passage endpoint crosses the right edge with mass at most
`1/8`, uniformly in the Pascal parameter.  This is an immediate consequence of
the stronger fixed-tilt tail `fpDistP_fst_tail_le`, whose event `m < 4e₁`
contains the actual overshoot event `m < e₁`. -/
theorem fpDistP_out_of_strip_le :
    ∃ Cthr : ℕ, ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, ∀ s : ℕ, (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      ∑' e : ℕ × ℤ,
        (fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e).toReal *
          Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2) ≤ 1 / 8 := by
  obtain ⟨C, hC⟩ := fpDistP_fst_tail_le (1 : ℝ) (by norm_num)
    (1 / 8 : ℝ) (by norm_num)
  refine ⟨max C 1, ?_⟩
  intro p hp0 hp1 n m hm hmn l s hs
  let fpLaw := fpDistP p (by linarith [hp0]) (by linarith [hp1]) s
  have htail := hC p hp0 hp1 m (le_trans (le_max_left C 1) hm) s hs
  have hm1 : 1 ≤ m := le_trans (le_max_right C 1) hm
  have hind : ∀ e : ℕ × ℤ,
      Set.indicator (outStripSetP n) 1
          (n / 2 - m + e.1, l + e.2) =
        (if m < e.1 then (1 : ℝ) else 0) := by
    intro e
    have hiff : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ outStripSetP n ↔
        m < e.1 := by
      simp only [outStripSetP, Set.mem_ofPred_eq]
      omega
    by_cases h : m < e.1
    · rw [Set.indicator_of_mem (hiff.mpr h), Pi.one_apply, if_pos h]
    · rw [Set.indicator_of_notMem (fun he => h (hiff.mp he)), if_neg h]
  simp_rw [hind]
  have hmass : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal) :=
    ENNReal.summable_toReal (by rw [fpLaw.tsum_coe]; exact ENNReal.one_ne_top)
  have hsmall : Summable (fun e : ℕ × ℤ =>
      (fpLaw e).toReal * (if m < e.1 then (1 : ℝ) else 0)) := by
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num))
      (fun e => ?_) hmass
    by_cases he : m < e.1 <;> simp [he, ENNReal.toReal_nonneg]
  have hlarge : Summable (fun e : ℕ × ℤ =>
      (fpLaw e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0)) := by
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num))
      (fun e => ?_) hmass
    by_cases he : m < 4 * e.1 <;> simp [he, ENNReal.toReal_nonneg]
  have hsub : (∑' e : ℕ × ℤ,
      (fpLaw e).toReal * (if m < e.1 then (1 : ℝ) else 0)) ≤
      ∑' e : ℕ × ℤ,
        (fpLaw e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0) := by
    refine hsmall.tsum_le_tsum (fun e => ?_) hlarge
    by_cases he : m < e.1
    · rw [if_pos he, if_pos (by omega : m < 4 * e.1)]
    · rw [if_neg he]
      by_cases he4 : m < 4 * e.1 <;> simp [he4, ENNReal.toReal_nonneg]
  have hrpow : (m : ℝ) ^ (-(1 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1) (by norm_num)
  change (∑' e : ℕ × ℤ,
      (fpLaw e).toReal * (if m < e.1 then (1 : ℝ) else 0)) ≤ 1 / 8
  calc
    _ ≤ ∑' e : ℕ × ℤ,
        (fpLaw e).toReal * (if m < 4 * e.1 then (1 : ℝ) else 0) := hsub
    _ ≤ (1 / 8 : ℝ) * (m : ℝ) ^ (-(1 : ℝ)) := htail
    _ ≤ 1 / 8 := by nlinarith

/-- Tao's Case-2 white-exit estimate at the finer Sec7P scale.  Outside an
exceptional mass `1/8 + 1/8`, an endpoint is in the strip and outside every
finer family triangle; the exact cover then makes its predecessor phase point
`whiteP`.  All constants are chosen before `p`. -/
theorem fpDistP_white_exit :
    ∃ p₀ > (0 : ℝ), ∃ Cthr : ℕ,
      ∀ (p : ℝ) (hp0 : 1 / 5 ≤ p) (hp1 : p ≤ 3 / 5),
      ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamilyP n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      p₀ ≤ ∑' e : ℕ × ℤ,
        (fpDistP p (by linarith [hp0]) (by linarith [hp1]) s e).toReal *
          Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2) := by
  obtain ⟨Cthr, hOut⟩ := fpDistP_out_of_strip_le
  refine ⟨3 / 4, by norm_num, Cthr, ?_⟩
  intro p hp0 hp1 n ξ hξ F m hm hmn l hl t ht htmem s hs hbudget
  let fpLaw := fpDistP p (by linarith [hp0]) (by linarith [hp1]) s
  have hout := hOut p hp0 hp1 n m hm hmn l s hbudget
  have htri := fpDistP_any_triangle_le p hp0 hp1 n ξ F m hmn l hl t ht htmem s hs
  have hmass : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal) :=
    ENNReal.summable_toReal (by rw [fpLaw.tsum_coe]; exact ENNReal.one_ne_top)
  have hsummand : ∀ (S : Set (ℕ × ℤ)),
      Summable (fun e : ℕ × ℤ => (fpLaw e).toReal *
        Set.indicator S 1 (n / 2 - m + e.1, l + e.2)) := by
    intro S
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (fun e => ?_) hmass
    refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
    by_cases he : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ S
    · simp [Set.indicator_of_mem he]
    · simp [Set.indicator_of_notMem he]
  have hptw : ∀ e : ℕ × ℤ,
      (1 : ℝ) - Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2)
          - Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2)
        ≤ Set.indicator (whiteStripP n ξ) 1
            (n / 2 - m + e.1, l + e.2) := by
    intro e
    have hWnn : (0 : ℝ) ≤ Set.indicator (whiteStripP n ξ) 1
        (n / 2 - m + e.1, l + e.2) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hOnn : (0 : ℝ) ≤ Set.indicator (outStripSetP n) 1
        (n / 2 - m + e.1, l + e.2) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hPnn : (0 : ℝ) ≤ Set.indicator (phaseInFamilyP F) 1
        (n / 2 - m + e.1, l + e.2) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hq1 : 1 ≤ n / 2 - m + e.1 := by omega
    by_cases hO : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ outStripSetP n
    · rw [Set.indicator_of_mem hO]
      simp only [Pi.one_apply]
      linarith
    · by_cases hP : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ phaseInFamilyP F
      · rw [Set.indicator_of_mem hP]
        simp only [Pi.one_apply]
        linarith
      · have hle : n / 2 - m + e.1 ≤ n / 2 := by
          simp only [outStripSetP, Set.mem_ofPred_eq, not_lt] at hO
          exact hO
        have hWmem : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈
            whiteStripP n ξ := by
          refine ⟨hle, hq1, ?_⟩
          intro hblack
          apply hP
          have hcov : ((n / 2 - m + e.1 - 1, l + e.2) : ℕ × ℤ) ∈
              {q : ℕ × ℤ | q.1 + 1 ≤ n / 2 ∧ blackP n ξ q.1 q.2} :=
            ⟨by omega, hblack⟩
          rw [F.cover] at hcov
          simp only [Set.mem_iUnion, exists_prop] at hcov
          obtain ⟨t', ht', hmem'⟩ := hcov
          exact ⟨t', ht', hmem'⟩
        rw [Set.indicator_of_mem hWmem, Set.indicator_of_notMem hO,
          Set.indicator_of_notMem hP]
        simp
  have hsumLHS : Summable (fun e : ℕ × ℤ => (fpLaw e).toReal *
      ((1 : ℝ) - Set.indicator (outStripSetP n) 1
          (n / 2 - m + e.1, l + e.2)
        - Set.indicator (phaseInFamilyP F) 1
          (n / 2 - m + e.1, l + e.2))) :=
    ((hmass.sub (hsummand (outStripSetP n))).sub (hsummand (phaseInFamilyP F))).congr
      (fun e => by ring)
  have hexpand : (∑' e : ℕ × ℤ, (fpLaw e).toReal *
      ((1 : ℝ) - Set.indicator (outStripSetP n) 1
          (n / 2 - m + e.1, l + e.2)
        - Set.indicator (phaseInFamilyP F) 1
          (n / 2 - m + e.1, l + e.2))) =
      1 - (∑' e : ℕ × ℤ, (fpLaw e).toReal *
        Set.indicator (outStripSetP n) 1
          (n / 2 - m + e.1, l + e.2))
        - (∑' e : ℕ × ℤ, (fpLaw e).toReal *
          Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2)) := by
    have h1 : ∀ e : ℕ × ℤ, (fpLaw e).toReal *
        ((1 : ℝ) - Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2)
          - Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2)) =
        (fpLaw e).toReal
          - (fpLaw e).toReal * Set.indicator (outStripSetP n) 1
              (n / 2 - m + e.1, l + e.2)
          - (fpLaw e).toReal * Set.indicator (phaseInFamilyP F) 1
              (n / 2 - m + e.1, l + e.2) := by
      intro e
      ring
    simp_rw [h1]
    rw [Summable.tsum_sub (hmass.sub (hsummand (outStripSetP n)))
        (hsummand (phaseInFamilyP F)),
      Summable.tsum_sub hmass (hsummand (outStripSetP n)),
      ← ENNReal.tsum_toReal_eq (fun e => PMF.apply_ne_top fpLaw e),
      fpLaw.tsum_coe, ENNReal.toReal_one]
  change (3 : ℝ) / 4 ≤ ∑' e : ℕ × ℤ, (fpLaw e).toReal *
    Set.indicator (whiteStripP n ξ) 1
      (n / 2 - m + e.1, l + e.2)
  calc
    (3 : ℝ) / 4 = 1 - 1 / 8 - 1 / 8 := by norm_num
    _ ≤ 1 - (∑' e : ℕ × ℤ, (fpLaw e).toReal *
          Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2))
        - (∑' e : ℕ × ℤ, (fpLaw e).toReal *
          Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2)) := by linarith
    _ = ∑' e : ℕ × ℤ, (fpLaw e).toReal *
        ((1 : ℝ) - Set.indicator (outStripSetP n) 1
            (n / 2 - m + e.1, l + e.2)
          - Set.indicator (phaseInFamilyP F) 1
            (n / 2 - m + e.1, l + e.2)) := hexpand.symm
    _ ≤ ∑' e : ℕ × ℤ, (fpLaw e).toReal *
        Set.indicator (whiteStripP n ξ) 1
          (n / 2 - m + e.1, l + e.2) :=
      Summable.tsum_le_tsum
        (fun e => mul_le_mul_of_nonneg_left (hptw e) ENNReal.toReal_nonneg)
        hsumLHS (hsummand (whiteStripP n ξ))

end TaoCollatz.Sec7P
