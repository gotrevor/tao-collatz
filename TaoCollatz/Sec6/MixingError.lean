import TaoCollatz.Sec6.MixingCore

/-! The bad-event/error branch of the §6 conditioning proof. -/

open scoped BigOperators

namespace TaoCollatz

/-- The real sub-density obtained by pushing a PMF through `X` while retaining only `E`.
This is the measure-theoretic skeleton underlying every `condDensW` term. -/
noncomputable def restrictedDensity {α β : Type*} [Fintype β] [DecidableEq β]
    (P : PMF α) (X : α → β)
    (E : α → Prop) [DecidablePred E] : β → ℝ := fun Y =>
  ∑' a, (P a).toReal * (if X a = Y ∧ E a then 1 else 0)

theorem restrictedDensity_nonneg {α β : Type*} [Fintype β] [DecidableEq β]
    (P : PMF α) (X : α → β)
    (E : α → Prop) [DecidablePred E] (Y : β) :
    0 ≤ restrictedDensity P X E Y := by
  exact tsum_nonneg fun a => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num)

/-- A restricted pushforward loses precisely the mass of the complementary event, in `L¹`.
The statement is deliberately over an arbitrary finite target; §6 later specializes it to
`ZMod (3^n)`. -/
theorem sum_abs_map_sub_restrictedDensity {α β : Type*} [Fintype β] [DecidableEq β]
    (P : PMF α) (X : α → β) (E : α → Prop) [DecidablePred E] :
    ∑ Y, |((P.map X) Y).toReal - restrictedDensity P X E Y|
      = ∑' a, if E a then 0 else (P a).toReal := by
  classical
  have hPsum : Summable fun a => (P a).toReal :=
    ENNReal.summable_toReal P.tsum_coe_ne_top
  have hPmass : ∑' a, (P a).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a => P.apply_ne_top a), P.tsum_coe,
      ENNReal.toReal_one]
  have hmap (Y : β) : ((P.map X) Y).toReal =
      ∑' a, (P a).toReal * (if X a = Y then 1 else 0) := by
    rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
    · refine tsum_congr fun a => ?_
      by_cases h : X a = Y
      · simp [h]
      · simp [h, Ne.symm h]
    · intro a
      by_cases h : Y = X a <;> simp [h, P.apply_ne_top a]
  have hrestSummable (Y : β) : Summable fun a =>
      (P a).toReal * (if X a = Y ∧ E a then 1 else 0) := by
    exact Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun a => by by_cases h : X a = Y ∧ E a <;> simp [h, ENNReal.toReal_nonneg]) hPsum
  have hfullSummable (Y : β) : Summable fun a =>
      (P a).toReal * (if X a = Y then 1 else 0) := by
    exact Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun a => by by_cases h : X a = Y <;> simp [h, ENNReal.toReal_nonneg]) hPsum
  have hrestricted_le (Y : β) :
      restrictedDensity P X E Y ≤ ((P.map X) Y).toReal := by
    rw [restrictedDensity, hmap]
    exact (hrestSummable Y).tsum_le_tsum
      (fun a => by
        gcongr
        by_cases hX : X a = Y <;> by_cases hE : E a <;> simp [hX, hE])
      (hfullSummable Y)
  have hcompSummable : Summable fun a => if E a then 0 else (P a).toReal := by
    exact Summable.of_nonneg_of_le
      (fun a => by by_cases h : E a <;> simp [h, ENNReal.toReal_nonneg])
      (fun a => by by_cases h : E a <;> simp [h, ENNReal.toReal_nonneg]) hPsum
  have heventSummable : Summable fun a => if E a then (P a).toReal else 0 := by
    exact Summable.of_nonneg_of_le
      (fun a => by by_cases h : E a <;> simp [h, ENNReal.toReal_nonneg])
      (fun a => by by_cases h : E a <;> simp [h, ENNReal.toReal_nonneg]) hPsum
  have hsumRestricted :
      ∑ Y, restrictedDensity P X E Y = ∑' a, if E a then (P a).toReal else 0 := by
    simp only [restrictedDensity]
    rw [← Summable.tsum_finsetSum (fun Y _ => hrestSummable Y)]
    apply tsum_congr
    intro a
    by_cases hE : E a <;> simp [hE]
  have hsplit :
      (∑' a, if E a then (P a).toReal else 0) +
          (∑' a, if E a then 0 else (P a).toReal) = 1 := by
    rw [← heventSummable.tsum_add hcompSummable]
    calc
      (∑' a, ((if E a then (P a).toReal else 0) +
          (if E a then 0 else (P a).toReal))) = ∑' a, (P a).toReal := by
            apply tsum_congr
            intro a
            by_cases h : E a <;> simp [h]
      _ = 1 := hPmass
  calc
    ∑ Y, |((P.map X) Y).toReal - restrictedDensity P X E Y|
        = ∑ Y, (((P.map X) Y).toReal - restrictedDensity P X E Y) := by
            apply Finset.sum_congr rfl
            intro Y _
            rw [abs_of_nonneg (sub_nonneg.mpr (hrestricted_le Y))]
    _ = (∑ Y, ((P.map X) Y).toReal) - ∑ Y, restrictedDensity P X E Y := by
          rw [Finset.sum_sub_distrib]
    _ = 1 - ∑' a, if E a then (P a).toReal else 0 := by
          rw [hsumRestricted]
          congr 1
          have hmass : ∑' Y, ((P.map X) Y).toReal = 1 := by
            rw [← ENNReal.tsum_toReal_eq (fun Y => (P.map X).apply_ne_top Y),
              (P.map X).tsum_coe, ENNReal.toReal_one]
          simpa only [tsum_fintype] using hmass
    _ = ∑' a, if E a then 0 else (P a).toReal := by linarith

/-- The suffix block at cut `k`, transported along the arithmetic identity `cutEq`. -/
def cutTail (n k : ℕ) (h : k < n) (a : Fin n → ℕ) : Fin (k + 1) → ℕ := fun i =>
  a (Fin.cast (cutEq h) (Fin.natAdd (n - 1 - k) i))

/-- Transporting a windowed conditioned density to an equal level is the same as transporting
its suffix coordinates inside the defining restricted pushforward. -/
theorem cast_condDensW_apply_eq_restricted (j p n l : ℕ) (e : j + p = n)
    (W : (Fin p → ℕ) → Prop) [DecidablePred W] (Y : ZMod (3 ^ n)) :
    (e ▸ condDensW j p l W) Y =
      restrictedDensity (geomHalf.iid n)
        (fun a => (fnat n a : ZMod (3 ^ n)) *
          (2 : ZMod (3 ^ n))⁻¹ ^ pre a n)
        (fun a =>
          let vt : Fin p → ℕ := fun i => a (Fin.cast e (Fin.natAdd j i))
          pre vt p = l ∧ W vt) Y := by
  subst n
  rfl

/-- Pointwise form of a casted conditioning term, now expressed directly on level-`n`
valuation vectors.  This removes the dependent `Eq.rec` before the event partition is assembled. -/
theorem castedTerm_apply_eq_restricted (n k l : ℕ) (C T : ℝ) (h : k < n)
    (Y : ZMod (3 ^ n)) :
    castedTerm n k l C T Y =
      restrictedDensity (geomHalf.iid n)
        (fun a => (fnat n a : ZMod (3 ^ n)) *
          (2 : ZMod (3 ^ n))⁻¹ ^ pre a n)
        (fun a =>
          let vt : Fin (k + 1) → ℕ := fun i =>
            a (Fin.cast (cutEq h) (Fin.natAdd (n - 1 - k) i))
          pre vt (k + 1) = l ∧ condWindowB (n - 1 - k) (k + 1) C l T vt) Y := by
  unfold castedTerm
  rw [dif_pos h]
  exact cast_condDensW_apply_eq_restricted (n - 1 - k) (k + 1) n l (cutEq h)
    (condWindowB (n - 1 - k) (k + 1) C l T) Y

/-- Prefix sums are monotone in their length argument. -/
theorem pre_mono_length {n r s : ℕ} (a : Fin n → ℕ) (hrs : r ≤ s) :
    pre a r ≤ pre a s := by
  unfold pre
  rw [show s = r + (s - r) by omega, Finset.sum_range_add]
  omega

/-- The full sum of a transported tail is the full sum minus the preceding head. -/
theorem pre_cast_tail_eq_sub (j p n : ℕ) (e : j + p = n) (a : Fin n → ℕ) :
    pre (fun i : Fin p => a (Fin.cast e (Fin.natAdd j i))) p = pre a n - pre a j := by
  subst n
  simp only [Fin.cast_eq_self]
  have hsplit := pre_natAdd_split a (m := p) le_rfl
  omega

/-- Removing the first reversed-tail coordinate leaves the suffix after the enlarged head. -/
theorem pre_cast_tail_sub_first_eq_sub (j p n : ℕ) (hp : 1 ≤ p) (e : j + p = n)
    (a : Fin n → ℕ) :
    pre (fun i : Fin p => a (Fin.cast e (Fin.natAdd j i))) p -
        pre (fun i : Fin p => a (Fin.cast e (Fin.natAdd j i))) 1 =
      pre a n - pre a (j + 1) := by
  subst n
  simp only [Fin.cast_eq_self]
  have hfull := pre_natAdd_split a (m := p) le_rfl
  have hone := pre_natAdd_split a (m := 1) hp
  omega

/-- The event carried by one `(k,l)` summand of `mainDensity`, written on the common
level-`n` valuation space. -/
def mainPieceEvent (n k l : ℕ) (C T : ℝ) (a : Fin n → ℕ) : Prop :=
  if h : k < n then
    let vt : Fin (k + 1) → ℕ := fun i =>
      a (Fin.cast (cutEq h) (Fin.natAdd (n - 1 - k) i))
    pre vt (k + 1) = l ∧ condWindowB (n - 1 - k) (k + 1) C l T vt
  else False

noncomputable instance mainPieceEvent_decidablePred (n k l : ℕ) (C T : ℝ) :
    DecidablePred (mainPieceEvent n k l C T) := Classical.decPred _

theorem castedTerm_apply_eq_pieceDensity (n k l : ℕ) (C T : ℝ) (Y : ZMod (3 ^ n)) :
    castedTerm n k l C T Y =
      restrictedDensity (geomHalf.iid n)
        (fun a => (fnat n a : ZMod (3 ^ n)) *
          (2 : ZMod (3 ^ n))⁻¹ ^ pre a n)
        (mainPieceEvent n k l C T) Y := by
  by_cases h : k < n
  · rw [castedTerm_apply_eq_restricted n k l C T h Y]
    congr 1
    funext a
    simp only [mainPieceEvent, dif_pos h]
  · unfold castedTerm
    rw [dif_neg h]
    simp [restrictedDensity, mainPieceEvent, h]

/-- Corrected `Bₖ` events are disjoint: two distinct cuts cannot both straddle the same
threshold in the nested suffix sums. -/
theorem mainPieceEvent_cut_unique (n k k' l l' : ℕ) (C T : ℝ) (a : Fin n → ℕ)
    (hk : mainPieceEvent n k l C T a) (hk' : mainPieceEvent n k' l' C T a) :
    k = k' := by
  simp only [mainPieceEvent] at hk hk'
  split at hk <;> rename_i hkn
  · split at hk' <;> rename_i hk'n
    · rcases hk with ⟨_, _, hstop⟩
      rcases hk' with ⟨_, _, hstop'⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · let vt : Fin (k + 1) → ℕ := fun i =>
          a (Fin.cast (cutEq hkn) (Fin.natAdd (n - 1 - k) i))
        let vt' : Fin (k' + 1) → ℕ := fun i =>
          a (Fin.cast (cutEq hk'n) (Fin.natAdd (n - 1 - k') i))
        have hsum := pre_cast_tail_eq_sub (n - 1 - k) (k + 1) n (cutEq hkn) a
        have hpred := pre_cast_tail_sub_first_eq_sub (n - 1 - k') (k' + 1) n
          (by omega) (cutEq hk'n) a
        have hpref : pre a ((n - 1 - k') + 1) ≤ pre a (n - 1 - k) :=
          pre_mono_length a (by omega)
        have hnat : pre vt (k + 1) ≤ pre vt' (k' + 1) - pre vt' 1 := by
          dsimp only [vt, vt']
          rw [hsum, hpred]
          exact Nat.sub_le_sub_left hpref (pre a n)
        have hreal : (pre vt (k + 1) : ℝ) ≤
            (pre vt' (k' + 1) : ℝ) - (pre vt' 1 : ℝ) := by
          have hone : pre vt' 1 ≤ pre vt' (k' + 1) := pre_mono_length vt' (by omega)
          rw [← Nat.cast_sub hone]
          exact_mod_cast hnat
        exact (not_lt_of_ge (hreal.trans hstop'.1)) hstop.2
      · let vt : Fin (k + 1) → ℕ := fun i =>
          a (Fin.cast (cutEq hkn) (Fin.natAdd (n - 1 - k) i))
        let vt' : Fin (k' + 1) → ℕ := fun i =>
          a (Fin.cast (cutEq hk'n) (Fin.natAdd (n - 1 - k') i))
        have hsum := pre_cast_tail_eq_sub (n - 1 - k') (k' + 1) n (cutEq hk'n) a
        have hpred := pre_cast_tail_sub_first_eq_sub (n - 1 - k) (k + 1) n
          (by omega) (cutEq hkn) a
        have hpref : pre a ((n - 1 - k) + 1) ≤ pre a (n - 1 - k') :=
          pre_mono_length a (by omega)
        have hnat : pre vt' (k' + 1) ≤ pre vt (k + 1) - pre vt 1 := by
          dsimp only [vt, vt']
          rw [hsum, hpred]
          exact Nat.sub_le_sub_left hpref (pre a n)
        have hreal : (pre vt' (k' + 1) : ℝ) ≤
            (pre vt (k + 1) : ℝ) - (pre vt 1 : ℝ) := by
          have hone : pre vt 1 ≤ pre vt (k + 1) := pre_mono_length vt (by omega)
          rw [← Nat.cast_sub hone]
          exact_mod_cast hnat
        exact (not_lt_of_ge (hreal.trans hstop.1)) hstop'.2
    · contradiction
  · contradiction

theorem mainPieceEvent_index_unique (n k k' l l' : ℕ) (C T : ℝ) (a : Fin n → ℕ)
    (hk : mainPieceEvent n k l C T a) (hk' : mainPieceEvent n k' l' C T a) :
    (k, l) = (k', l') := by
  have hkk := mainPieceEvent_cut_unique n k k' l l' C T a hk hk'
  subst k'
  have hll : l = l' := by
    simp only [mainPieceEvent] at hk hk'
    split at hk <;> rename_i hkn
    · split at hk' <;> rename_i hkn'
      · exact hk.1.symm.trans hk'.1
      · contradiction
    · contradiction
  subst l'
  rfl

/-- A finite disjoint sum of restricted pushforwards is the restricted pushforward of the union. -/
theorem sum_restrictedDensity_eq_union {α β ι : Type*} [Fintype β] [DecidableEq β]
    [DecidableEq ι] (P : PMF α) (X : α → β) (s : Finset ι)
    (E : ι → α → Prop) [∀ i, DecidablePred (E i)]
    [DecidablePred (fun a => ∃ i ∈ s, E i a)]
    (hdisj : ∀ a i, i ∈ s → ∀ i', i' ∈ s → E i a → E i' a → i = i') (Y : β) :
    ∑ i ∈ s, restrictedDensity P X (E i) Y =
      restrictedDensity P X (fun a => ∃ i ∈ s, E i a) Y := by
  classical
  have hPsum : Summable fun a => (P a).toReal :=
    ENNReal.summable_toReal P.tsum_coe_ne_top
  have hsummable (i : ι) : Summable fun a =>
      (P a).toReal * (if X a = Y ∧ E i a then 1 else 0) := by
    exact Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun a => by by_cases h : X a = Y ∧ E i a <;> simp [h, ENNReal.toReal_nonneg]) hPsum
  simp only [restrictedDensity]
  rw [← Summable.tsum_finsetSum (fun i _ => hsummable i)]
  apply tsum_congr
  intro a
  rw [← Finset.mul_sum]
  congr 1
  by_cases hX : X a = Y
  · simp only [hX, true_and]
    by_cases hex : ∃ i ∈ s, E i a
    · obtain ⟨i, hi, hEi⟩ := hex
      rw [if_pos ⟨i, hi, hEi⟩, Finset.sum_eq_single i]
      · simp [hEi]
      · intro i' hi' hne
        rw [if_neg]
        exact fun hEi' => hne (hdisj a i hi i' hi' hEi hEi').symm
      · exact fun hnot => (hnot hi).elim
    · rw [if_neg hex]
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg]
      exact fun hEi => hex ⟨i, hi, hEi⟩
  · simp [hX]

/-- The union event represented by `mainHigh`. -/
def mainEvent (A : ℝ) (n : ℕ) (a : Fin n → ℕ) : Prop :=
  ∃ kl ∈ Finset.range n ×ˢ lRange (caConst A) n,
    mainPieceEvent n kl.1 kl.2 (caConst A) (caThr (caConst A) n) a

noncomputable instance mainEvent_decidablePred (A : ℝ) (n : ℕ) :
    DecidablePred (mainEvent A n) := Classical.decPred _

/-- `mainHigh` is exactly the Syracuse pushforward restricted to its stopping/window event. -/
theorem mainHigh_eq_restrictedDensity (A : ℝ) (n : ℕ) (Y : ZMod (3 ^ n)) :
    mainHigh A n Y =
      restrictedDensity (geomHalf.iid n)
        (fun a => (fnat n a : ZMod (3 ^ n)) *
          (2 : ZMod (3 ^ n))⁻¹ ^ pre a n)
        (mainEvent A n) Y := by
  classical
  unfold mainHigh mainDensity
  simp only [castedTerm_apply_eq_pieceDensity]
  rw [← Finset.sum_product']
  unfold mainEvent
  let E : ℕ × ℕ → (Fin n → ℕ) → Prop := fun kl =>
    mainPieceEvent n kl.1 kl.2 (caConst A) (caThr (caConst A) n)
  letI : ∀ kl, DecidablePred (E kl) := fun _ => Classical.decPred _
  letI : DecidablePred (fun a =>
      ∃ kl ∈ Finset.range n ×ˢ lRange (caConst A) n, E kl a) := Classical.decPred _
  have hdisj : ∀ a kl, kl ∈ Finset.range n ×ˢ lRange (caConst A) n →
      ∀ kl', kl' ∈ Finset.range n ×ˢ lRange (caConst A) n →
        E kl a → E kl' a → kl = kl' := by
    intro a kl _ kl' _ hE hE'
    exact mainPieceEvent_index_unique n kl.1 kl'.1 kl.2 kl'.2
      (caConst A) (caThr (caConst A) n) a hE hE'
  convert sum_restrictedDensity_eq_union (geomHalf.iid n)
      (fun a => (fnat n a : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ pre a n)
      (Finset.range n ×ˢ lRange (caConst A) n) E hdisj Y using 1
  unfold restrictedDensity
  apply tsum_congr
  intro a
  by_cases h : ∃ kl ∈ Finset.range n ×ˢ lRange (caConst A) n,
      mainPieceEvent n kl.1 kl.2 (caConst A) (caThr (caConst A) n) a <;> simp [E]

/-- Exact reduction of the C10 error term to the probability of the complementary
stopping/window event. -/
theorem sum_abs_syracZ_sub_mainHigh_eq (A : ℝ) (n : ℕ) :
    ∑ Y, |(syracZ n Y).toReal - mainHigh A n Y| =
      ∑' a : Fin n → ℕ, if mainEvent A n a then 0 else ((geomHalf.iid n) a).toReal := by
  rw [syracZ_eq_rev_fnat]
  simp_rw [mainHigh_eq_restrictedDensity]
  exact sum_abs_map_sub_restrictedDensity (geomHalf.iid n)
    (fun a => (fnat n a : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ pre a n)
    (mainEvent A n)

/-- **Obligation 1 (error term)**: the `L¹` mass of `syracZ − mainHigh` is polynomially small. This
is Tao (6.3), `P(Ē) ≤ n^{-A-1}`, plus the (6.4) event enlargements `E → Eₖ`: the events `E`/`Eₖ`/`Bₖ`
partition the good event, so the difference is the mass on the bad event, controlled by the §7/S3
sub-Gaussian tails (Lemma 2.2 + union bound). -/
theorem error_l1_high_bound (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, m ≤ n → n₀ ≤ n → 9 * n ≤ 10 * m →
      2 * ∑ Y, |(syracZ n Y).toReal - mainHigh A n Y| ≤ C * (m : ℝ) ^ (-A) := by
  sorry

end TaoCollatz
