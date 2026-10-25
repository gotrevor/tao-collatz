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

end TaoCollatz.Sec7P
