import TaoCollatz.Sec6.MixingCore

/-! The bad-event/error branch of the §6 conditioning proof. -/

open scoped BigOperators ENNReal

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

/-- One step of a prefix sum in range: `pre a (m+1) = pre a m + a_m`. -/
theorem pre_succ {n : ℕ} (a : Fin n → ℕ) (m : ℕ) (hm : m < n) :
    pre a (m + 1) = pre a m + a ⟨m, hm⟩ := by
  unfold pre
  rw [Finset.sum_range_succ, dif_pos hm]

/-- The full sum of a transported tail is the full sum minus the preceding head. -/
theorem pre_cast_tail_eq_sub (j p n : ℕ) (e : j + p = n) (a : Fin n → ℕ) :
    pre (fun i : Fin p => a (Fin.cast e (Fin.natAdd j i))) p = pre a n - pre a j := by
  subst n
  simp only [Fin.cast_eq_self]
  have hsplit := pre_natAdd_split a (m := p) le_rfl
  omega

/-- A prefix of the transported tail is a difference of level-`n` prefix sums:
`pre vt s = pre a (j + s) − pre a j` for `s ≤ p` (generalises `pre_cast_tail_eq_sub`, `s = p`). -/
theorem pre_cast_tail_prefix (j p n s : ℕ) (hs : s ≤ p) (e : j + p = n) (a : Fin n → ℕ) :
    pre (fun i : Fin p => a (Fin.cast e (Fin.natAdd j i))) s = pre a (j + s) - pre a j := by
  subst n
  simp only [Fin.cast_eq_self]
  have hsplit := pre_natAdd_split a (m := s) hs
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

/-- Suffix sum: the total mass of the last `r` coordinates, `a_{n-r} + ⋯ + a_{n-1}`. -/
def sufSum {n : ℕ} (a : Fin n → ℕ) (r : ℕ) : ℕ := pre a n - pre a (n - r)

/-- **Packaging lemma for `globalGood ⊆ mainEvent`.** Given a cut `k < n` at which the suffix sums
straddle the threshold (`stopEvent`) and satisfy the lower-deviation window at every scale, the
`(k, sufSum a (k+1))` conditioning term fires: `mainPieceEvent` holds. All three constituents
(`pre vt (k+1) = l`, `stopEvent`, `condWindow`) reduce to facts about the suffix sums `sufSum a r`. -/
theorem mainPieceEvent_of (n k : ℕ) (C T : ℝ) (a : Fin n → ℕ) (hk : k < n)
    (hstop_lo : (sufSum a k : ℝ) ≤ T)
    (hstop_hi : T < (sufSum a (k + 1) : ℝ))
    (hwin : ∀ r, 1 ≤ r → r ≤ k + 1 →
      2 * (r : ℝ) - C * (Real.sqrt ((r : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ))
        ≤ (sufSum a r : ℝ)) :
    mainPieceEvent n k (sufSum a (k + 1)) C T a := by
  have hjn : n - 1 - k = n - (k + 1) := by omega
  have hmono : ∀ x y : ℕ, x ≤ y → pre a x ≤ pre a y := fun x y h => pre_mono_length a h
  -- vt is the reversed tail block; its prefix sums are differences of level-n prefix sums
  set vt : Fin (k + 1) → ℕ := fun i => a (Fin.cast (cutEq hk) (Fin.natAdd (n - 1 - k) i)) with hvt
  have hvt_full : pre vt (k + 1) = pre a n - pre a (n - 1 - k) :=
    pre_cast_tail_eq_sub (n - 1 - k) (k + 1) n (cutEq hk) a
  have hvt_pre : ∀ s, s ≤ k + 1 → pre vt s = pre a (n - 1 - k + s) - pre a (n - 1 - k) :=
    fun s hs => pre_cast_tail_prefix (n - 1 - k) (k + 1) n s hs (cutEq hk) a
  have hA : pre vt (k + 1) = sufSum a (k + 1) := by rw [hvt_full, sufSum, hjn]
  -- condWindow component
  have hwindow : condWindow (n - 1 - k) (k + 1) C (sufSum a (k + 1)) vt := by
    intro r hr1 hrp
    rw [show n - 1 - k + (k + 1) = n from cutEq hk]
    have hsr : k + 1 - r ≤ k + 1 := by omega
    have hpvt : pre vt (k + 1 - r) = pre a (n - r) - pre a (n - 1 - k) := by
      rw [hvt_pre _ hsr]; congr 2; omega
    have hnat : sufSum a (k + 1) = pre vt (k + 1 - r) + sufSum a r := by
      rw [hpvt, sufSum, sufSum, hjn]
      have h1 : pre a (n - (k + 1)) ≤ pre a (n - r) := hmono _ _ (by omega)
      have h2 : pre a (n - r) ≤ pre a n := hmono _ _ (by omega)
      omega
    have hcast : (sufSum a (k + 1) : ℝ) - (pre vt (k + 1 - r) : ℝ) = (sufSum a r : ℝ) := by
      have := congrArg (Nat.cast : ℕ → ℝ) hnat; push_cast at this ⊢; linarith
    rw [hcast]
    exact hwin r hr1 hrp
  -- stopEvent component
  have hstop : stopEvent (k + 1) T vt := by
    refine ⟨?_, ?_⟩
    · have hpvt1 : pre vt 1 = pre a (n - 1 - k + 1) - pre a (n - 1 - k) := hvt_pre 1 (by omega)
      have hnat : pre vt (k + 1) = pre vt 1 + sufSum a k := by
        rw [hvt_full, hpvt1, sufSum]
        have h1 : pre a (n - 1 - k) ≤ pre a (n - 1 - k + 1) := hmono _ _ (by omega)
        have h2 : pre a (n - 1 - k + 1) ≤ pre a n := hmono _ _ (by omega)
        have h3 : pre a (n - 1 - k + 1) = pre a (n - k) := by
          rw [show n - 1 - k + 1 = n - k from by omega]
        omega
      have hcast : (pre vt (k + 1) : ℝ) - (pre vt 1 : ℝ) = (sufSum a k : ℝ) := by
        have := congrArg (Nat.cast : ℕ → ℝ) hnat; push_cast at this ⊢; linarith
      rw [hcast]; exact hstop_lo
    · rw [hA]; exact hstop_hi
  -- assemble the dependent-if event
  unfold mainPieceEvent
  rw [dif_pos hk]
  exact ⟨hA, hwindow, hstop⟩

/-- `sufSum a 0 = 0`. -/
theorem sufSum_zero {n : ℕ} (a : Fin n → ℕ) : sufSum a 0 = 0 := by
  simp [sufSum]

/-- `sufSum a n = pre a n` (the full-length suffix is the whole vector). -/
theorem sufSum_full {n : ℕ} (a : Fin n → ℕ) : sufSum a n = pre a n := by
  have h0 : pre a 0 = 0 := by simp [pre]
  simp only [sufSum, Nat.sub_self, h0, Nat.sub_zero]

/-- Adding the next-from-top coordinate: an `M`-bound on every coordinate gives
`sufSum a (k+1) ≤ sufSum a k + M`. Used for the upper end of the `lRange` window. -/
theorem sufSum_succ_le_add {n : ℕ} (a : Fin n → ℕ) (k : ℕ) (hk : k < n)
    (M : ℝ) (hM : ∀ i : Fin n, (a i : ℝ) ≤ M) :
    (sufSum a (k + 1) : ℝ) ≤ (sufSum a k : ℝ) + M := by
  have hlt : n - 1 - k < n := by omega
  have hpre : pre a (n - k) = pre a (n - 1 - k) + a ⟨n - 1 - k, hlt⟩ := by
    rw [show n - k = (n - 1 - k) + 1 from by omega, pre_succ a (n - 1 - k) hlt]
  have hle2 : pre a (n - k) ≤ pre a n := pre_mono_length a (by omega)
  have heq : sufSum a (k + 1) = sufSum a k + a ⟨n - 1 - k, hlt⟩ := by
    simp only [sufSum, show n - (k + 1) = n - 1 - k from by omega]
    omega
  have hcoord := hM ⟨n - 1 - k, hlt⟩
  rw [heq]; push_cast; linarith

/-- **The (6.2) global good deviation event** (an ENLARGEMENT of Tao's `Eₖ`, per the pass-29 ruling —
never document it as equal). Three tail-measurable deviation constraints on the suffix sums:
(G1) the total mass exceeds the (6.6) threshold, so a stopping cut exists; (G2) no single coordinate
exceeds `2C·log n`, pinning the crossing value into the tight `lRange` window; (G3) every suffix sum
`a_{[n-r,n]}` sits above its lower-deviation window `2r − C(√(r log n) + log n)`. Its complement is a
finite union of one-sided large-deviation events, each controlled by `geomHalf_tail_bound`. -/
def globalGood (A : ℝ) (n : ℕ) (a : Fin n → ℕ) : Prop :=
  caThr (caConst A) n < (pre a n : ℝ)
  ∧ (∀ i : Fin n, (a i : ℝ) ≤ 2 * caConst A * Real.log (n : ℝ))
  ∧ (∀ r, 1 ≤ r → r ≤ n →
      2 * (r : ℝ) - caConst A * (Real.sqrt ((r : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ))
        ≤ (sufSum a r : ℝ))

noncomputable instance globalGood_decidablePred (A : ℝ) (n : ℕ) :
    DecidablePred (globalGood A n) := Classical.decPred _

/-- **THE inclusion `globalGood ⊆ mainEvent`** (the content of the C10 error node, per the directive).
Given the good event and `0 ≤ caThr` (a large-`n` regime fact the caller supplies via `n₀`), the
first-passage stopping cut `k` — the least `k` with `sufSum a (k+1) > T` — witnesses `mainEvent`: it
lands in `range n`, its valuation `l = sufSum a (k+1)` lies in the tight `lRange` window (lower end
from the crossing `T < l`, upper end from the coordinate cap G2), and `mainPieceEvent` fires via
`mainPieceEvent_of` (stopping straddle from the first-passage minimality, window from G3). -/
theorem globalGood_subset_mainEvent (A : ℝ) (n : ℕ) (a : Fin n → ℕ)
    (hTpos : 0 ≤ caThr (caConst A) n) (hg : globalGood A n a) :
    mainEvent A n a := by
  classical
  obtain ⟨hG1, hG2, hG3⟩ := hg
  set C := caConst A with hC
  set T := caThr C n with hTdef
  -- first-passage predicate
  set p : ℕ → Prop := fun r => T < (sufSum a r : ℝ) with hp
  have hpn : p n := by rw [hp]; simp only []; rw [sufSum_full]; exact hG1
  have hex : ∃ r, p r := ⟨n, hpn⟩
  have hp0 : ¬ p 0 := by
    rw [hp]; simp only [sufSum_zero, Nat.cast_zero]; exact not_lt.mpr hTpos
  set m0 := Nat.find hex with hm0
  have hm0spec : p m0 := Nat.find_spec hex
  have hm0le : m0 ≤ n := Nat.find_min' hex hpn
  have hm0pos : 1 ≤ m0 := by
    rcases Nat.eq_zero_or_pos m0 with h | h
    · exact absurd (h ▸ hm0spec) hp0
    · exact h
  set k := m0 - 1 with hk
  have hkm0 : k + 1 = m0 := by omega
  have hkn : k < n := by omega
  -- stopping straddle
  have hstop_hi : T < (sufSum a (k + 1) : ℝ) := by rw [hkm0]; exact hm0spec
  have hstop_lo : (sufSum a k : ℝ) ≤ T := by
    have hnpk : ¬ p k := Nat.find_min hex (by omega)
    rw [hp] at hnpk; exact not_lt.mp hnpk
  -- window at all scales ≤ k+1 ≤ n
  have hwin : ∀ r, 1 ≤ r → r ≤ k + 1 →
      2 * (r : ℝ) - C * (Real.sqrt ((r : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ))
        ≤ (sufSum a r : ℝ) :=
    fun r hr1 hrp => hG3 r hr1 (by omega)
  have hpiece : mainPieceEvent n k (sufSum a (k + 1)) C T a :=
    mainPieceEvent_of n k C T a hkn hstop_lo hstop_hi hwin
  -- the valuation lands in the tight window
  have hTexp : T = (n : ℝ) * Real.log 3 / Real.log 2 - C ^ 2 * Real.log (n : ℝ) := by
    rw [hTdef]; simp only [caThr]
  have hlow : ⌈(n : ℝ) * Real.log 3 / Real.log 2 - C ^ 2 * Real.log (n : ℝ)⌉₊ ≤ sufSum a (k + 1) := by
    apply Nat.ceil_le.mpr
    have : T ≤ (sufSum a (k + 1) : ℝ) := le_of_lt hstop_hi
    rw [hTexp] at this; exact this
  have hhigh : sufSum a (k + 1) ≤
      ⌊(n : ℝ) * Real.log 3 / Real.log 2 - (C ^ 2 - 2 * C) * Real.log (n : ℝ)⌋₊ := by
    apply Nat.le_floor
    have hstep := sufSum_succ_le_add a k hkn (2 * C * Real.log (n : ℝ)) hG2
    have hle : (sufSum a (k + 1) : ℝ) ≤ T + 2 * C * Real.log (n : ℝ) := by linarith
    rw [hTexp] at hle
    have hE : (n : ℝ) * Real.log 3 / Real.log 2 - C ^ 2 * Real.log (n : ℝ)
          + 2 * C * Real.log (n : ℝ)
        = (n : ℝ) * Real.log 3 / Real.log 2 - (C ^ 2 - 2 * C) * Real.log (n : ℝ) := by ring
    linarith [hle, hE]
  have hmem : (k, sufSum a (k + 1)) ∈ Finset.range n ×ˢ lRange C n := by
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr hkn, ?_⟩
    simp only [lRange, Finset.mem_Icc]
    exact ⟨hlow, hhigh⟩
  exact ⟨(k, sufSum a (k + 1)), hmem, hpiece⟩

/-! ### Marginal infrastructure for the (6.3) union bound

The complement `¬globalGood` is a finite union of one-sided large-deviation events on
prefix sums (`pre a n`), suffix sums (`sufSum a r`) and single coordinates (`a i`) of the iid
Geom(2) vector.  `geomHalf_tail_bound` controls each *once we know its marginal law*: under
`geomHalf.iid n` a length-`r` block sum is distributed as `iidSum geomHalf r`.  These lemmas
establish those marginals and the pushforward bridge that rewrites a masked probability into a
masked `iidSum` tail. -/

/-- `pre a r` as a sum over `Fin r` of the first-`r`-coordinate restriction (for `r ≤ n`). -/
theorem pre_eq_fin_sum_castLE {n : ℕ} (a : Fin n → ℕ) {r : ℕ} (h : r ≤ n) :
    pre a r = ∑ i : Fin r, a (Fin.castLE h i) := by
  rw [pre, ← Fin.sum_univ_eq_sum_range (fun i => if hh : i < n then a ⟨i, hh⟩ else 0) r]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dif_pos (lt_of_lt_of_le i.isLt h)]
  rfl

/-- **Iterated-iid collapses to the base at length 1.** -/
theorem iidSum_one {M : Type*} [AddCommMonoid M] (p : PMF M) : iidSum p 1 = p := by
  rw [iidSum_succ, iidSum_zero]
  simp only [PMF.pure_map, add_zero, PMF.bind_pure]

/-- **Prefix-block marginal** (the genuine (6.3) infrastructure): under `geomHalf.iid n`, the
prefix sum `pre a r` is distributed as `iidSum geomHalf r`, for `r ≤ n`.  Proof: `pre a r` factors
as `(∑ i, ·) ∘ (restrict to first r coords)`, and the prefix-restriction marginal `iid_map_castLE`
sends `geomHalf.iid n` to `geomHalf.iid r`. -/
theorem iidMap_pre (n r : ℕ) (h : r ≤ n) :
    (geomHalf.iid n).map (fun a : Fin n → ℕ => pre a r) = iidSum geomHalf r := by
  have hcomp : (fun a : Fin n → ℕ => pre a r)
      = (fun w : Fin r → ℕ => ∑ i, w i) ∘ (fun a : Fin n → ℕ => a ∘ Fin.castLE h) := by
    funext a
    simp only [Function.comp_apply]
    rw [pre_eq_fin_sum_castLE a h]
  rw [hcomp, ← PMF.map_comp, iid_map_castLE geomHalf r n h]
  rfl

/-- **Suffix-block marginal** (the (6.3) infrastructure for family G3): under `geomHalf.iid n`, the
suffix sum `sufSum a r` (the sum of the last `r` coordinates) is distributed as `iidSum geomHalf r`,
for `r ≤ n`.  Proof: `sufSum a r = pre (a ∘ Fin.rev) r` (`pre_comp_rev`), so it factors as
`(pre · r) ∘ (· ∘ Fin.rev)`; reversal preserves the iid law (`iid_map_rev`), then `iidMap_pre`. -/
theorem iidMap_suffix (n r : ℕ) (h : r ≤ n) :
    (geomHalf.iid n).map (fun a : Fin n → ℕ => sufSum a r) = iidSum geomHalf r := by
  have hsuf : (fun a : Fin n → ℕ => sufSum a r)
      = (fun b : Fin n → ℕ => pre b r) ∘ (fun a : Fin n → ℕ => a ∘ Fin.rev) := by
    funext a
    simp only [Function.comp_apply]
    rw [sufSum]
    have hrev := pre_comp_rev a h
    omega
  rw [hsuf, ← PMF.map_comp, iid_map_rev, iidMap_pre n r h]

/-- **Coordinate marginal**: under `p.iid n`, each single coordinate `a i` is distributed as `p`.
Proof: peel the head draw; coordinate `0` is the head (`pure`), coordinate `j+1` is the tail's
coordinate `j` (induction). -/
theorem iid_map_coord {α : Type*} (p : PMF α) :
    ∀ (n : ℕ) (i : Fin n), (p.iid n).map (fun a : Fin n → α => a i) = p := by
  intro n
  induction n with
  | zero => exact fun i => i.elim0
  | succ n IH =>
    intro i
    rw [show p.iid (n + 1) = p.bind fun a0 => (p.iid n).map (Fin.cons a0) from rfl, PMF.map_bind]
    refine Fin.cases ?_ (fun j => ?_) i
    · have hpt : (fun a0 => ((p.iid n).map (Fin.cons a0)).map (fun a : Fin (n + 1) → α => a 0))
          = fun a0 => PMF.pure a0 := by
        funext a0
        rw [PMF.map_comp, show ((fun a : Fin (n + 1) → α => a 0) ∘ Fin.cons a0)
            = Function.const (Fin n → α) a0 from by funext w; simp, PMF.map_const]
      rw [hpt, PMF.bind_pure]
    · have hpt : (fun a0 => ((p.iid n).map (Fin.cons a0)).map (fun a : Fin (n + 1) → α => a j.succ))
          = fun _ => p := by
        funext a0
        rw [PMF.map_comp, show ((fun a : Fin (n + 1) → α => a j.succ) ∘ Fin.cons a0)
            = fun w : Fin n → α => w j from by funext w; simp, IH j]
      rw [hpt, PMF.bind_const]

/-- **Pushforward bridge for masked probabilities.** A `good?`-masked probability sum over the base
space equals the corresponding masked sum over the pushforward `p.map φ`.  With `φ` a block sum and
`p.map φ = iidSum geomHalf r`, this turns `P(bad event on a block)` into an `iidSum` tail that
`geomHalf_tail_bound` dominates. -/
theorem masked_tsum_map {α β : Type*} (p : PMF α) (φ : α → β)
    (Q : β → Prop) [DecidablePred Q] :
    (∑' a, if Q (φ a) then 0 else (p a).toReal)
      = ∑' b, if Q b then 0 else ((p.map φ) b).toReal := by
  have key := PMF.tsum_map_mul p φ (fun b => if Q b then 0 else 1)
  -- convert both sides through `toReal_tsum_mul_ofReal`
  have hg : ∀ x : β, (0 : ℝ) ≤ if Q x then 0 else 1 := fun x => by
    by_cases h : Q x <;> simp [h]
  have hbridge : (∑' a, (p a).toReal * (if Q (φ a) then 0 else 1))
      = ∑' b, ((p.map φ) b).toReal * (if Q b then 0 else 1) := by
    rw [← PMF.toReal_tsum_mul_ofReal p (fun a => if Q (φ a) then 0 else 1) (fun a => hg _),
        ← PMF.toReal_tsum_mul_ofReal (p.map φ) (fun b => if Q b then 0 else 1) hg]
    congr 1
    rw [PMF.tsum_map_mul p φ (fun b => ENNReal.ofReal (if Q b then 0 else 1))]
  calc (∑' a, if Q (φ a) then 0 else (p a).toReal)
      = ∑' a, (p a).toReal * (if Q (φ a) then 0 else 1) := by
        refine tsum_congr fun a => ?_; by_cases h : Q (φ a) <;> simp [h]
    _ = ∑' b, ((p.map φ) b).toReal * (if Q b then 0 else 1) := hbridge
    _ = ∑' b, if Q b then 0 else ((p.map φ) b).toReal := by
        refine tsum_congr fun b => ?_; by_cases h : Q b <;> simp [h]

/-! ### The (6.3) union decomposition and the three per-event masses

`¬globalGood` fires only if one of its three deviation families fires: the total-mass deficit
(G1), some coordinate overshoot (G2), or some suffix-window deficit (G3).  The pointwise lemma
below dominates the `¬globalGood` indicator mass by the sum of the three indicator families; each
family mass is then bounded by `geomHalf_tail_bound` through the marginal law. -/

/-- **The (6.3) union bound, pointwise.** The mass an atom `a` contributes to `¬globalGood` is at
most the mass it contributes across the three deviation families (G1, the per-coordinate G2's over
`Fin n`, the per-scale G3's over `Icc 1 n`).  Every term is a nonnegative sub-mass of `P(a)`, and
`¬globalGood` forces at least one family into its "bad" branch. -/
theorem not_globalGood_pointwise_le (A : ℝ) (n : ℕ) (a : Fin n → ℕ) :
    (if globalGood A n a then (0 : ℝ) else ((geomHalf.iid n) a).toReal)
      ≤ (if caThr (caConst A) n < (pre a n : ℝ) then 0 else ((geomHalf.iid n) a).toReal)
        + (∑ i : Fin n, if (a i : ℝ) ≤ 2 * caConst A * Real.log (n : ℝ) then 0
            else ((geomHalf.iid n) a).toReal)
        + (∑ r ∈ Finset.Icc 1 n, if 2 * (r : ℝ) - caConst A *
            (Real.sqrt ((r : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ)) ≤ (sufSum a r : ℝ) then 0
            else ((geomHalf.iid n) a).toReal) := by
  classical
  set P : ℝ := ((geomHalf.iid n) a).toReal with hP
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  set t1 : ℝ := if caThr (caConst A) n < (pre a n : ℝ) then 0 else P with ht1def
  set g2 : Fin n → ℝ := fun i => if (a i : ℝ) ≤ 2 * caConst A * Real.log (n : ℝ) then 0 else P
    with hg2def
  set g3 : ℕ → ℝ := fun r => if 2 * (r : ℝ) - caConst A *
      (Real.sqrt ((r : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ)) ≤ (sufSum a r : ℝ) then 0
      else P with hg3def
  have ht1 : 0 ≤ t1 := by rw [ht1def]; split <;> [rfl; exact hP0]
  have hg2i : ∀ i, 0 ≤ g2 i := fun i => by rw [hg2def]; dsimp only; split <;> [rfl; exact hP0]
  have hg3r : ∀ r, 0 ≤ g3 r := fun r => by rw [hg3def]; dsimp only; split <;> [rfl; exact hP0]
  have hSt2 : 0 ≤ ∑ i : Fin n, g2 i := Finset.sum_nonneg fun i _ => hg2i i
  have hSt3 : 0 ≤ ∑ r ∈ Finset.Icc 1 n, g3 r := Finset.sum_nonneg fun r _ => hg3r r
  by_cases hgg : globalGood A n a
  · rw [if_pos hgg]
    exact add_nonneg (add_nonneg ht1 hSt2) hSt3
  · rw [if_neg hgg]
    by_cases h1 : caThr (caConst A) n < (pre a n : ℝ)
    · by_cases h2 : ∀ i : Fin n, (a i : ℝ) ≤ 2 * caConst A * Real.log (n : ℝ)
      · -- G1, G2 hold ⇒ G3 must fail
        have h3 : ¬ ∀ r, 1 ≤ r → r ≤ n →
            2 * (r : ℝ) - caConst A * (Real.sqrt ((r : ℝ) * Real.log (n : ℝ)) +
              Real.log (n : ℝ)) ≤ (sufSum a r : ℝ) := fun h3 => hgg ⟨h1, h2, h3⟩
        push_neg at h3
        obtain ⟨r, hr1, hrn, hr⟩ := h3
        have hmem : r ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hr1, hrn⟩
        have hval : g3 r = P := by rw [hg3def]; dsimp only; rw [if_neg (not_le.mpr hr)]
        calc P = g3 r := hval.symm
          _ ≤ ∑ r ∈ Finset.Icc 1 n, g3 r := Finset.single_le_sum (fun r _ => hg3r r) hmem
          _ ≤ (t1 + ∑ i : Fin n, g2 i) + ∑ r ∈ Finset.Icc 1 n, g3 r :=
              le_add_of_nonneg_left (add_nonneg ht1 hSt2)
      · -- G2 fails
        push_neg at h2
        obtain ⟨i, hi⟩ := h2
        have hval : g2 i = P := by rw [hg2def]; dsimp only; rw [if_neg (not_le.mpr hi)]
        calc P = g2 i := hval.symm
          _ ≤ ∑ i : Fin n, g2 i := Finset.single_le_sum (fun i _ => hg2i i) (Finset.mem_univ i)
          _ ≤ t1 + ∑ i : Fin n, g2 i := le_add_of_nonneg_left ht1
          _ ≤ (t1 + ∑ i : Fin n, g2 i) + ∑ r ∈ Finset.Icc 1 n, g3 r := le_add_of_nonneg_right hSt3
    · -- G1 fails
      have hval : t1 = P := by rw [ht1def]; rw [if_neg h1]
      calc P = t1 := hval.symm
        _ ≤ t1 + ∑ i : Fin n, g2 i := le_add_of_nonneg_right hSt2
        _ ≤ (t1 + ∑ i : Fin n, g2 i) + ∑ r ∈ Finset.Icc 1 n, g3 r := le_add_of_nonneg_right hSt3

/-! ### Shared tail-bound machinery for the three per-event families -/

/-- **Explicit-constant Geom(2) tail bound** (the `c = 1/400`, `C = 2` witness behind the
existential `geomHalf_tail_bound`).  `caConst_tail_exponent` (`A+3 ≤ caConst/400`) is tuned to this
`1/400`, so the concrete constant is what the per-event bounds consume. -/
theorem geomHalf_tail_bound_explicit (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∑' L : ℕ, if lam ≤ |(L : ℝ) - 2 * n| then ((iidSum geomHalf n) L).toReal else 0)
      ≤ 2 * Gweight (1 + n) (1 / 400 * lam) :=
  iidSum_nat_tail_of_quad geomHalf 2 (by norm_num)
    (fun t hlo hhi => le_trans (tiltZ_geomHalf_le_quad hlo hhi)
      (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg t]))) n lam hlam

/-- For `t ≤ x` (so `x ≥ t > 0`), the Gaussian weight collapses to twice a pure exponential:
`exp(−x²/t) ≤ exp(−x)` since `x²/t ≥ x`, and `exp(−|x|) = exp(−x)`. -/
theorem Gweight_le_two_exp (t x : ℝ) (ht : 0 < t) (hx : t ≤ x) :
    Gweight t x ≤ 2 * Real.exp (-x) := by
  have hx0 : 0 < x := lt_of_lt_of_le ht hx
  have hgauss : Real.exp (-(x ^ 2) / t) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ ht]
    nlinarith [hx, hx0.le]
  have habs : Real.exp (-|x|) = Real.exp (-x) := by rw [abs_of_pos hx0]
  rw [Gweight, habs]; linarith [hgauss]

/-- `exp(−k·log n) = n^{−k}` for `n > 0`. -/
theorem exp_neg_mul_log_eq_rpow (n : ℕ) (k : ℝ) (hn : 0 < (n : ℝ)) :
    Real.exp (-(k * Real.log (n : ℝ))) = (n : ℝ) ^ (-k) := by
  rw [Real.rpow_def_of_pos hn]; congr 1; ring

/-- `Real.log n` eventually exceeds any bound `L` (take `n ≥ exp L`). -/
theorem log_ge_of_large (L : ℝ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → L ≤ Real.log (n : ℝ) := by
  refine ⟨⌈Real.exp L⌉₊ + 1, fun n hn => ?_⟩
  have h1 : Real.exp L ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈Real.exp L⌉₊ ≤ n))
  calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
    _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos L) h1

/-- **Constant absorption**: a `κ·n^{−β}` bound with `β` at least a full unit above `A+2` is
eventually below `n^{−(A+2)}`, since `n^{β−(A+2)} ≥ n → ∞` swallows the constant `κ`. -/
theorem const_rpow_absorb (A κ β : ℝ) (hκ : 0 < κ) (hβ : A + 3 ≤ β) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → κ * (n : ℝ) ^ (-β) ≤ (n : ℝ) ^ (-(A + 2)) := by
  refine ⟨⌈κ⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hκn : κ ≤ (n : ℝ) := le_trans (Nat.le_ceil κ) (by exact_mod_cast (by omega : ⌈κ⌉₊ ≤ n))
  have hnle : (n : ℝ) ≤ (n : ℝ) ^ (β - (A + 2)) := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ (β - (A + 2)) := Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hκle : κ ≤ (n : ℝ) ^ (β - (A + 2)) := le_trans hκn hnle
  calc κ * (n : ℝ) ^ (-β) ≤ (n : ℝ) ^ (β - (A + 2)) * (n : ℝ) ^ (-β) :=
        mul_le_mul_of_nonneg_right hκle (Real.rpow_nonneg hnpos.le _)
    _ = (n : ℝ) ^ (-(A + 2)) := by
        rw [← Real.rpow_add hnpos]; congr 1; ring

/-- **(6.3) family G1 — the total-mass deficit.** `P(pre a n ≤ caThr)` is exponentially small: the
prefix sum `pre a n` has mean `2n` while `caThr ≈ n·log₂3 ≈ 1.585 n`, a linear deviation.  Via
`iidMap_pre` + `geomHalf_tail_bound` at `λ = 2n − caThr ≈ 0.415 n`, dominated by `n^{-(A+2)}`.
TODO(prove): the marginal rewrite `masked_tsum_map` + `iidMap_pre n n` then `geomHalf_tail_bound`. -/
theorem g1_mass_le (A : ℝ) (hA : 0 < A) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    (∑' a : Fin n → ℕ, if caThr (caConst A) n < (pre a n : ℝ) then 0
      else ((geomHalf.iid n) a).toReal) ≤ (n : ℝ) ^ (-(A + 2)) := by
  classical
  set C := caConst A with hCdef
  have hApos : (0 : ℝ) < A + 3 := by linarith
  have hcge : 1000 * (A + 3) ≤ C := by rw [hCdef]; unfold caConst; nlinarith [le_max_left A 0]
  have hCpos : 0 < C := by nlinarith [hApos]
  have hC2big : 400 * (A + 3) ≤ C ^ 2 := by nlinarith [hcge, hApos]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3lt : Real.log 3 < 2 * Real.log 2 := by
    rw [← show Real.log 4 = 2 * Real.log 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  set δ : ℝ := 2 - Real.log 3 / Real.log 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef, sub_pos, div_lt_iff₀ hlog2pos]; linarith
  set ε : ℝ := δ ^ 2 / (320000 * (A + 3)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεcancel : (A + 3) * ε = δ ^ 2 / 320000 := by rw [hεdef]; field_simp
  obtain ⟨nκ, hκ⟩ := const_rpow_absorb A 4 (A + 3) (by norm_num) (le_refl _)
  obtain ⟨nε, hεle⟩ := log_le_eps_mul_of_large ε hεpos
  refine ⟨max (max nκ nε) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnκle : nκ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnεle : nε ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  -- lam = 2n − caThr = nδ + C²·log n
  set lam : ℝ := 2 * (n : ℝ) - caThr C n with hlamdef
  have hlam_eq : lam = (n : ℝ) * δ + C ^ 2 * Real.log (n : ℝ) := by
    rw [hlamdef]; simp only [caThr, hδdef]; ring
  have hC2logn : 0 ≤ C ^ 2 * Real.log (n : ℝ) := mul_nonneg (sq_nonneg C) hlogn0
  have hnδ : 0 ≤ (n : ℝ) * δ := mul_nonneg hnpos.le hδpos.le
  have hlam_C2 : C ^ 2 * Real.log (n : ℝ) ≤ lam := by rw [hlam_eq]; linarith
  have hlam_nδ : (n : ℝ) * δ ≤ lam := by rw [hlam_eq]; linarith
  have hlam0 : 0 ≤ lam := le_trans hC2logn hlam_C2
  have hcaThr_le : caThr C n ≤ 2 * (n : ℝ) := by rw [hlamdef] at hlam0; linarith
  -- marginal rewrite: pre a n has law iidSum geomHalf n
  rw [masked_tsum_map (geomHalf.iid n) (fun a => pre a n)
        (fun x : ℕ => caThr C n < (x : ℝ)),
      iidMap_pre n n (le_refl n)]
  set g : ℕ → ℝ := fun b => ((iidSum geomHalf n) b).toReal with hgdef
  have hg0 : ∀ b, 0 ≤ g b := fun b => ENNReal.toReal_nonneg
  have hgsum : Summable g := ENNReal.summable_toReal (iidSum geomHalf n).tsum_coe_ne_top
  have hmask1 : ∀ Q : ℕ → Prop, ∀ _ : DecidablePred Q,
      Summable (fun b => if Q b then (0 : ℝ) else g b) := fun Q _ =>
    Summable.of_nonneg_of_le (fun b => by by_cases h : Q b <;> simp [h, hg0 b])
      (fun b => by by_cases h : Q b <;> simp [h, hg0 b]) hgsum
  have hmask2 : ∀ Q : ℕ → Prop, ∀ _ : DecidablePred Q,
      Summable (fun b => if Q b then g b else 0) := fun Q _ =>
    Summable.of_nonneg_of_le (fun b => by by_cases h : Q b <;> simp [h, hg0 b])
      (fun b => by by_cases h : Q b <;> simp [h, hg0 b]) hgsum
  -- dominate the good-mask by the deviation mask
  have hdom : (∑' b : ℕ, if caThr C n < (b : ℝ) then 0 else g b)
      ≤ ∑' b : ℕ, if lam ≤ |(b : ℝ) - 2 * (n : ℕ)| then g b else 0 := by
    refine Summable.tsum_le_tsum (fun b => ?_) (hmask1 _ _) (hmask2 _ _)
    by_cases h : caThr C n < (b : ℝ)
    · rw [if_pos h]; split
      · exact hg0 b
      · exact le_refl 0
    · rw [if_neg h]
      push_neg at h
      have hb : lam ≤ |(b : ℝ) - 2 * (n : ℕ)| := by
        have h1 : (b : ℝ) ≤ 2 * (n : ℝ) - lam := by rw [hlamdef]; push_cast; linarith
        have h2 : lam ≤ 2 * (n : ℝ) - (b : ℝ) := by push_cast; linarith
        calc lam ≤ 2 * (n : ℝ) - (b : ℝ) := h2
          _ = -((b : ℝ) - 2 * (n : ℕ)) := by push_cast; ring
          _ ≤ |(b : ℝ) - 2 * (n : ℕ)| := neg_le_abs _
      rw [if_pos hb]
  -- tail bound + split Gweight
  refine le_trans hdom (le_trans (geomHalf_tail_bound_explicit n lam hlam0) ?_)
  rw [Gweight, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 400 * lam)]
  -- bound each term by n^{-(A+3)}
  have hGexp : Real.exp (-(1 / 400 * lam)) ≤ (n : ℝ) ^ (-(A + 3)) := by
    refine le_trans (Real.exp_le_exp.mpr ?_)
      (le_of_eq (exp_neg_mul_log_eq_rpow n (A + 3) hnpos))
    have : 400 * (A + 3) * Real.log (n : ℝ) ≤ lam := by
      nlinarith [mul_le_mul_of_nonneg_right hC2big hlogn0, hlam_C2]
    have hd : (A + 3) * Real.log (n : ℝ) ≤ 1 / 400 * lam := by linarith
    simpa using neg_le_neg hd
  have hGgauss : Real.exp (-(1 / 400 * lam) ^ 2 / (1 + (n : ℕ))) ≤ (n : ℝ) ^ (-(A + 3)) := by
    refine le_trans (Real.exp_le_exp.mpr ?_)
      (le_of_eq (exp_neg_mul_log_eq_rpow n (A + 3) hnpos))
    rw [neg_div, neg_le_neg_iff]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + (n : ℕ))]
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    -- (A+3)·log n ≤ δ²·n/320000
    have hAe : (A + 3) * Real.log (n : ℝ) ≤ δ ^ 2 * (n : ℝ) / 320000 := by
      have h := hεle n hnεle
      have hcanc : (A + 3) * (ε * (n : ℝ)) = δ ^ 2 * (n : ℝ) / 320000 := by
        rw [← mul_assoc, hεcancel]; ring
      have := mul_le_mul_of_nonneg_left h hApos.le
      linarith [this, hcanc]
    have hlamsq : (n : ℝ) ^ 2 * δ ^ 2 ≤ lam ^ 2 := by nlinarith [hlam_nδ, hnδ, hlam0]
    have hlhs : (A + 3) * Real.log (n : ℝ) * (1 + (n : ℝ))
        ≤ δ ^ 2 * (n : ℝ) / 320000 * (1 + (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hAe (by positivity)
    have hrhs : δ ^ 2 * (n : ℝ) / 320000 * (1 + (n : ℝ)) ≤ (1 / 400 * lam) ^ 2 := by
      have hstep : (0 : ℝ) ≤ δ ^ 2 * (n : ℝ) * ((n : ℝ) - 1) :=
        mul_nonneg (mul_nonneg (sq_nonneg δ) hnpos.le) (by linarith)
      nlinarith [hlamsq, hstep]
    push_cast
    linarith [hlhs, hrhs]
  calc 2 * (Real.exp (-(1 / 400 * lam) ^ 2 / (1 + (n : ℕ))) + Real.exp (-(1 / 400 * lam)))
      ≤ 2 * ((n : ℝ) ^ (-(A + 3)) + (n : ℝ) ^ (-(A + 3))) := by
        gcongr
    _ = 4 * (n : ℝ) ^ (-(A + 3)) := by ring
    _ ≤ (n : ℝ) ^ (-(A + 2)) := hκ n hnκle

/-- **(6.3) family G2 — the per-coordinate overshoot.** For each `i`, `P(a i > 2·C_A·log n)` is
polynomially small: `a i` is a single Geom(2) draw (`iid_map_coord`, mean 2), and the deviation
`λ ≈ 2·C_A·log n` gives `geomHalf_tail_bound ≈ n^{-c·2·C_A}` with `c·C_A ≥ A+3`.  Uniform in `i`. -/
theorem g2_mass_le (A : ℝ) (hA : 0 < A) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ i : Fin n,
    (∑' a : Fin n → ℕ, if (a i : ℝ) ≤ 2 * caConst A * Real.log (n : ℝ) then 0
      else ((geomHalf.iid n) a).toReal) ≤ (n : ℝ) ^ (-(A + 2)) := by
  classical
  have hC3000 : 3000 ≤ caConst A := by unfold caConst; nlinarith [le_max_right A 0]
  have hCpos : 0 < caConst A := by linarith
  have hCexp : A + 3 ≤ caConst A / 200 := by
    have h := caConst_tail_exponent A; linarith
  obtain ⟨nκ, hκ⟩ := const_rpow_absorb A (4 * Real.exp (1 / 200)) (caConst A / 200)
    (by positivity) hCexp
  obtain ⟨nL, hL⟩ := log_ge_of_large 1
  refine ⟨max (max nκ nL) 1, fun n hn i => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnκle : nκ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnLle : nL ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hlogn1 : (1 : ℝ) ≤ Real.log (n : ℝ) := hL n hnLle
  set lam : ℝ := 2 * caConst A * Real.log (n : ℝ) - 2 with hlamdef
  have hlamge : (800 : ℝ) ≤ lam := by rw [hlamdef]; nlinarith [hC3000, hlogn1]
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  -- marginal rewrite: coordinate i has law geomHalf = iidSum geomHalf 1
  rw [masked_tsum_map (geomHalf.iid n) (fun a => a i)
        (fun x : ℕ => (x : ℝ) ≤ 2 * caConst A * Real.log (n : ℝ)),
      iid_map_coord geomHalf n i, ← iidSum_one geomHalf]
  set g : ℕ → ℝ := fun b => ((iidSum geomHalf 1) b).toReal with hgdef
  have hg0 : ∀ b, 0 ≤ g b := fun b => ENNReal.toReal_nonneg
  have hgsum : Summable g := ENNReal.summable_toReal (iidSum geomHalf 1).tsum_coe_ne_top
  have hmask1 : ∀ Q : ℕ → Prop, ∀ _ : DecidablePred Q,
      Summable (fun b => if Q b then (0 : ℝ) else g b) := fun Q _ =>
    Summable.of_nonneg_of_le (fun b => by by_cases h : Q b <;> simp [h, hg0 b])
      (fun b => by by_cases h : Q b <;> simp [h, hg0 b]) hgsum
  have hmask2 : ∀ Q : ℕ → Prop, ∀ _ : DecidablePred Q,
      Summable (fun b => if Q b then g b else 0) := fun Q _ =>
    Summable.of_nonneg_of_le (fun b => by by_cases h : Q b <;> simp [h, hg0 b])
      (fun b => by by_cases h : Q b <;> simp [h, hg0 b]) hgsum
  -- dominate the "good"-mask by the two-sided-deviation mask
  have hdom : (∑' b : ℕ, if (b : ℝ) ≤ 2 * caConst A * Real.log (n : ℝ) then 0 else g b)
      ≤ ∑' b : ℕ, if lam ≤ |(b : ℝ) - 2 * (1 : ℕ)| then g b else 0 := by
    refine Summable.tsum_le_tsum (fun b => ?_) (hmask1 _ _) (hmask2 _ _)
    by_cases h : (b : ℝ) ≤ 2 * caConst A * Real.log (n : ℝ)
    · rw [if_pos h]
      split
      · exact hg0 b
      · exact le_refl 0
    · rw [if_neg h]
      push_neg at h
      have hb : lam ≤ |(b : ℝ) - 2 * (1 : ℕ)| := by
        have : lam < (b : ℝ) - 2 * (1 : ℕ) := by push_cast; rw [hlamdef]; linarith
        exact le_of_lt (lt_of_lt_of_le this (le_abs_self _))
      rw [if_pos hb]
  -- tail bound + Gweight collapse
  have hxge : (2 : ℝ) ≤ 1 / 400 * lam := by linarith [hlamge]
  have htail : (∑' b : ℕ, if lam ≤ |(b : ℝ) - 2 * (1 : ℕ)| then g b else 0)
      ≤ 4 * Real.exp (-(1 / 400 * lam)) := by
    refine le_trans (geomHalf_tail_bound_explicit 1 lam hlam0) ?_
    have hGw : Gweight (1 + (1 : ℕ)) (1 / 400 * lam) ≤ 2 * Real.exp (-(1 / 400 * lam)) :=
      Gweight_le_two_exp (1 + (1 : ℕ)) (1 / 400 * lam) (by norm_num) (by push_cast; linarith [hxge])
    calc 2 * Gweight (1 + (1 : ℕ)) (1 / 400 * lam)
        ≤ 2 * (2 * Real.exp (-(1 / 400 * lam))) := by
          exact mul_le_mul_of_nonneg_left hGw (by norm_num)
      _ = 4 * Real.exp (-(1 / 400 * lam)) := by ring
  -- exp → rpow
  have hexpval : Real.exp (-(1 / 400 * lam)) = Real.exp (1 / 200) * (n : ℝ) ^ (-(caConst A / 200)) := by
    have hlamval : (1 / 400 : ℝ) * lam = caConst A / 200 * Real.log (n : ℝ) - 1 / 200 := by
      rw [hlamdef]; ring
    rw [hlamval, show -(caConst A / 200 * Real.log (n : ℝ) - 1 / 200)
          = 1 / 200 + -(caConst A / 200 * Real.log (n : ℝ)) from by ring,
      Real.exp_add, exp_neg_mul_log_eq_rpow n (caConst A / 200) hnpos]
  calc (∑' b : ℕ, if (b : ℝ) ≤ 2 * caConst A * Real.log (n : ℝ) then 0 else g b)
      ≤ 4 * Real.exp (-(1 / 400 * lam)) := le_trans hdom htail
    _ = (4 * Real.exp (1 / 200)) * (n : ℝ) ^ (-(caConst A / 200)) := by rw [hexpval]; ring
    _ ≤ (n : ℝ) ^ (-(A + 2)) := hκ n hnκle

/-- **(6.3) family G3 — the per-scale suffix-window deficit.** For each `r ∈ [1,n]`,
`P(sufSum a r < 2r − C_A(√(r log n)+log n))` is polynomially small: `sufSum a r` is a length-`r`
block sum (mean `2r`), the deviation is `λ = C_A(√(r log n)+log n)`.  The `√(r log n)` part feeds the
Gaussian factor `≤ n^{−c²C_A²/2}`, the `+log n` part feeds `exp(−cλ) ≤ n^{−(A+3)}` (this is why the
window carries the extra `log n`), so `Gweight ≤ 2 n^{−(A+2)}`.  Uniform in `r`.  Needs the SUFFIX
marginal `(geomHalf.iid n).map (sufSum · r) = iidSum geomHalf r` (a last-`r`-block analogue of
`iidMap_pre`, provable via `iid`'s exchangeability / `cexpect_iid_append` with trivial head). -/
theorem g3_mass_le (A : ℝ) (hA : 0 < A) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ r, 1 ≤ r → r ≤ n →
    (∑' a : Fin n → ℕ, if 2 * (r : ℝ) - caConst A *
        (Real.sqrt ((r : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ)) ≤ (sufSum a r : ℝ) then 0
      else ((geomHalf.iid n) a).toReal) ≤ (n : ℝ) ^ (-(A + 2)) := by
  classical
  set C := caConst A with hCdef
  have hApos : (0 : ℝ) < A + 3 := by linarith
  have hcge : 1000 * (A + 3) ≤ C := by rw [hCdef]; unfold caConst; nlinarith [le_max_left A 0]
  have hCpos : 0 < C := by nlinarith [hApos]
  have hC400 : 400 * (A + 3) ≤ C := by linarith [hcge]
  have hCsq : (1000 * (A + 3)) ^ 2 ≤ C ^ 2 := by
    have := mul_le_mul hcge hcge (by positivity) (by linarith)
    nlinarith [this]
  have hC2_320 : 320000 * (A + 3) ≤ C ^ 2 := by nlinarith [hCsq, hApos]
  obtain ⟨nκ, hκ⟩ := const_rpow_absorb A 4 (A + 3) (by norm_num) (le_refl _)
  obtain ⟨nL, hL⟩ := log_ge_of_large 1
  refine ⟨max (max nκ nL) 1, fun n hn r hr1 hrn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnκle : nκ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnLle : nL ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hLn1 : (1 : ℝ) ≤ Real.log (n : ℝ) := hL n hnLle
  have hLn0 : (0 : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hrR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hrR0 : (0 : ℝ) ≤ (r : ℝ) := by linarith
  have hrL0 : (0 : ℝ) ≤ (r : ℝ) * Real.log (n : ℝ) := mul_nonneg hrR0 hLn0
  set S : ℝ := Real.sqrt ((r : ℝ) * Real.log (n : ℝ)) with hSdef
  have hS0 : (0 : ℝ) ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = (r : ℝ) * Real.log (n : ℝ) := Real.sq_sqrt hrL0
  set lam : ℝ := C * (S + Real.log (n : ℝ)) with hlamdef
  have hlam0 : (0 : ℝ) ≤ lam := by
    rw [hlamdef]; exact mul_nonneg hCpos.le (add_nonneg hS0 hLn0)
  -- marginal rewrite: sufSum · r has law iidSum geomHalf r
  rw [masked_tsum_map (geomHalf.iid n) (fun a => sufSum a r)
        (fun x : ℕ => 2 * (r : ℝ) - lam ≤ (x : ℝ)),
      iidMap_suffix n r hrn]
  set g : ℕ → ℝ := fun b => ((iidSum geomHalf r) b).toReal with hgdef
  have hg0 : ∀ b, 0 ≤ g b := fun b => ENNReal.toReal_nonneg
  have hgsum : Summable g := ENNReal.summable_toReal (iidSum geomHalf r).tsum_coe_ne_top
  have hmask1 : ∀ Q : ℕ → Prop, ∀ _ : DecidablePred Q,
      Summable (fun b => if Q b then (0 : ℝ) else g b) := fun Q _ =>
    Summable.of_nonneg_of_le (fun b => by by_cases h : Q b <;> simp [h, hg0 b])
      (fun b => by by_cases h : Q b <;> simp [h, hg0 b]) hgsum
  have hmask2 : ∀ Q : ℕ → Prop, ∀ _ : DecidablePred Q,
      Summable (fun b => if Q b then g b else 0) := fun Q _ =>
    Summable.of_nonneg_of_le (fun b => by by_cases h : Q b <;> simp [h, hg0 b])
      (fun b => by by_cases h : Q b <;> simp [h, hg0 b]) hgsum
  -- dominate the good-mask by the two-sided deviation mask
  have hdom : (∑' b : ℕ, if 2 * (r : ℝ) - lam ≤ (b : ℝ) then 0 else g b)
      ≤ ∑' b : ℕ, if lam ≤ |(b : ℝ) - 2 * (r : ℕ)| then g b else 0 := by
    refine Summable.tsum_le_tsum (fun b => ?_) (hmask1 _ _) (hmask2 _ _)
    by_cases h : 2 * (r : ℝ) - lam ≤ (b : ℝ)
    · rw [if_pos h]; split
      · exact hg0 b
      · exact le_refl 0
    · rw [if_neg h]
      push_neg at h
      have hb : lam ≤ |(b : ℝ) - 2 * (r : ℕ)| := by
        have h2 : lam ≤ 2 * (r : ℝ) - (b : ℝ) := by linarith
        calc lam ≤ 2 * (r : ℝ) - (b : ℝ) := h2
          _ = -((b : ℝ) - 2 * (r : ℕ)) := by push_cast; ring
          _ ≤ |(b : ℝ) - 2 * (r : ℕ)| := neg_le_abs _
      rw [if_pos hb]
  refine le_trans hdom (le_trans (geomHalf_tail_bound_explicit r lam hlam0) ?_)
  rw [Gweight, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 400) hlam0)]
  -- exp term (from the `+ log n` part): exp(−λ/400) ≤ n^{−(A+3)}
  have hCS0 : (0 : ℝ) ≤ C * S := mul_nonneg hCpos.le hS0
  have hGexp : Real.exp (-(1 / 400 * lam)) ≤ (n : ℝ) ^ (-(A + 3)) := by
    refine le_trans (Real.exp_le_exp.mpr ?_)
      (le_of_eq (exp_neg_mul_log_eq_rpow n (A + 3) hnpos))
    have hd : (A + 3) * Real.log (n : ℝ) ≤ 1 / 400 * lam := by
      rw [hlamdef]; nlinarith [hC400, hLn0, hCS0]
    simpa using neg_le_neg hd
  -- Gaussian term (from the `√(r log n)` part): exp(−(λ/400)²/(1+r)) ≤ n^{−(A+3)}
  have hGgauss : Real.exp (-(1 / 400 * lam) ^ 2 / (1 + (r : ℕ))) ≤ (n : ℝ) ^ (-(A + 3)) := by
    refine le_trans (Real.exp_le_exp.mpr ?_)
      (le_of_eq (exp_neg_mul_log_eq_rpow n (A + 3) hnpos))
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + (r : ℕ))]
    -- λ² ≥ C²·r·log n  (drop the head `log n` from `S + log n`)
    have hlamsq : C ^ 2 * ((r : ℝ) * Real.log (n : ℝ)) ≤ lam ^ 2 := by
      rw [hlamdef, mul_pow]
      nlinarith [hS2, mul_nonneg (sq_nonneg C) (mul_nonneg hS0 hLn0),
        mul_nonneg (sq_nonneg C) (sq_nonneg (Real.log (n : ℝ)))]
    -- (A+3)·log n·(1+r) ≤ C²·r·log n/160000 ≤ λ²/160000 = (λ/400)²
    have hAL0 : (0 : ℝ) ≤ (A + 3) * Real.log (n : ℝ) := mul_nonneg hApos.le hLn0
    have hstep : (A + 3) * Real.log (n : ℝ) * (1 + (r : ℝ))
        ≤ C ^ 2 * ((r : ℝ) * Real.log (n : ℝ)) / 160000 := by
      have hA : (A + 3) * Real.log (n : ℝ) * (1 + (r : ℝ))
          ≤ 2 * ((A + 3) * Real.log (n : ℝ)) * (r : ℝ) := by nlinarith [hAL0, hrR1]
      have hB : 2 * ((A + 3) * Real.log (n : ℝ)) * (r : ℝ)
          ≤ C ^ 2 * ((r : ℝ) * Real.log (n : ℝ)) / 160000 := by nlinarith [hC2_320, hrL0]
      linarith [hA, hB]
    have hkey : (A + 3) * Real.log (n : ℝ) * (1 + (r : ℝ)) ≤ (1 / 400 * lam) ^ 2 := by
      have hlhs2 : (1 / 400 * lam) ^ 2 = lam ^ 2 / 160000 := by ring
      rw [hlhs2]; linarith [hstep, hlamsq]
    push_cast
    linarith [hkey]
  calc 2 * (Real.exp (-(1 / 400 * lam) ^ 2 / (1 + (r : ℕ))) + Real.exp (-(1 / 400 * lam)))
      ≤ 2 * ((n : ℝ) ^ (-(A + 3)) + (n : ℝ) ^ (-(A + 3))) := by gcongr
    _ = 4 * (n : ℝ) ^ (-(A + 3)) := by ring
    _ ≤ (n : ℝ) ^ (-(A + 2)) := hκ n hnκle

/-- **Large-`n` positivity of the (6.6) threshold.** `caThr C n = n·log₂3 − C²·log n ≥ 0` once
`n·log₂3 ≥ C²·log n`, i.e. `n/log n ≥ C²·log2/log3`; a standard `log n = o(n)` threshold (via
`log n ≤ 2√n`).  This is exactly the hypothesis `globalGood_subset_mainEvent` consumes. -/
theorem caThr_nonneg_large (A : ℝ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 ≤ caThr (caConst A) n := by
  set C := caConst A with hCdef
  have hC : 30 ≤ C := caConst_ge_thirty A
  have hD : 0 < C ^ 2 := by nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  obtain ⟨n₀, hn₀⟩ := log_le_eps_mul_of_large (C ^ 2)⁻¹ (inv_pos.mpr hD)
  refine ⟨n₀, fun n hn => ?_⟩
  have hlog := hn₀ n hn
  have hDn : C ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) := by
    calc C ^ 2 * Real.log (n : ℝ) ≤ C ^ 2 * ((C ^ 2)⁻¹ * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog hD.le
      _ = (n : ℝ) := by rw [← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul]
  have hratio : (n : ℝ) ≤ (n : ℝ) * Real.log 3 / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlog23 (Nat.cast_nonneg n)
  have hkey : C ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) * Real.log 3 / Real.log 2 := hDn.trans hratio
  rw [caThr]
  linarith

/-- **The remaining C10 tail estimate — a pure probability bound (Tao (6.3)–(6.4)).**
`P(¬globalGood) ≤ (C/2)·m^{-A}`, together with the large-`n` positivity `0 ≤ caThr` that the inclusion
`globalGood_subset_mainEvent` consumes; both are delivered by the same `n₀`. The bound is a union over
the finitely many one-sided large-deviation events making up `¬globalGood` — the total-mass deficit
`pre a n ≤ T` (G1), the per-coordinate overshoots `a_i > 2C log n` (G2), and the per-scale window
deficits `sufSum a r < 2r − C(√(r log n)+log n)` (G3) — each dominated by `geomHalf_tail_bound`, with
the `n → m` conversion paid out of `0.9n ≤ m ≤ n`. There is no structural content left: the event
algebra is discharged (`globalGood_subset_mainEvent`), only this probability estimate remains. -/
theorem prob_not_globalGood_le (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, m ≤ n → n₀ ≤ n → 9 * n ≤ 10 * m →
      0 ≤ caThr (caConst A) n ∧
      2 * (∑' a : Fin n → ℕ, if globalGood A n a then 0 else ((geomHalf.iid n) a).toReal)
        ≤ C * (m : ℝ) ^ (-A) := by
  classical
  obtain ⟨nA, hpos⟩ := caThr_nonneg_large A
  obtain ⟨n1, hg1⟩ := g1_mass_le A hA
  obtain ⟨n2, hg2⟩ := g2_mass_le A hA
  obtain ⟨n3, hg3⟩ := g3_mass_le A hA
  refine ⟨6, by norm_num, max (max nA n1) (max n2 n3) + 1, fun n m hmn hn hreg => ?_⟩
  -- unpack the combined threshold
  have ha1 : nA ≤ max nA n1 := le_max_left _ _
  have ha2 : n1 ≤ max nA n1 := le_max_right _ _
  have ha3 : n2 ≤ max n2 n3 := le_max_left _ _
  have ha4 : n3 ≤ max n2 n3 := le_max_right _ _
  have hb1 : max nA n1 ≤ max (max nA n1) (max n2 n3) := le_max_left _ _
  have hb2 : max n2 n3 ≤ max (max nA n1) (max n2 n3) := le_max_right _ _
  have hn1le : n1 ≤ n := by omega
  have hnAle : nA ≤ n := by omega
  have hn2le : n2 ≤ n := by omega
  have hn3le : n3 ≤ n := by omega
  have hn1' : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1'
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  refine ⟨hpos n hnAle, ?_⟩
  -- notation
  set P : (Fin n → ℕ) → ℝ := fun a => ((geomHalf.iid n) a).toReal with hPdef
  have hP0 : ∀ a, 0 ≤ P a := fun a => ENNReal.toReal_nonneg
  have hPsum : Summable P := ENNReal.summable_toReal (geomHalf.iid n).tsum_coe_ne_top
  -- the three families as summand functions
  set f1 : (Fin n → ℕ) → ℝ := fun a =>
    if caThr (caConst A) n < (pre a n : ℝ) then 0 else P a with hf1def
  set g2 : Fin n → (Fin n → ℕ) → ℝ := fun i a =>
    if (a i : ℝ) ≤ 2 * caConst A * Real.log (n : ℝ) then 0 else P a with hg2def
  set g3 : ℕ → (Fin n → ℕ) → ℝ := fun r a =>
    if 2 * (r : ℝ) - caConst A * (Real.sqrt ((r : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ))
        ≤ (sufSum a r : ℝ) then 0 else P a with hg3def
  -- summabilities
  have hmask : ∀ (Q : (Fin n → ℕ) → Prop) [DecidablePred Q],
      Summable (fun a => if Q a then (0 : ℝ) else P a) := by
    intro Q _
    exact Summable.of_nonneg_of_le (fun a => by by_cases h : Q a <;> simp [h, hP0 a])
      (fun a => by by_cases h : Q a <;> simp [h, hP0 a]) hPsum
  have hf1sum : Summable f1 := hmask _
  have hg2sum : ∀ i, Summable (g2 i) := fun i => hmask _
  have hg3sum : ∀ r, Summable (g3 r) := fun r => hmask _
  have hf2sum : Summable (fun a => ∑ i : Fin n, g2 i a) := summable_sum fun i _ => hg2sum i
  have hf3sum : Summable (fun a => ∑ r ∈ Finset.Icc 1 n, g3 r a) := summable_sum fun r _ => hg3sum r
  -- pointwise union bound ⇒ M ≤ ∑'(f1 + Σg2 + Σg3)
  have hMsum : Summable (fun a => if globalGood A n a then (0 : ℝ) else P a) := hmask _
  have hRHSsum : Summable (fun a => f1 a + (∑ i, g2 i a) + ∑ r ∈ Finset.Icc 1 n, g3 r a) :=
    (hf1sum.add hf2sum).add hf3sum
  have hMle : (∑' a, if globalGood A n a then (0 : ℝ) else P a)
      ≤ ∑' a, (f1 a + (∑ i, g2 i a) + ∑ r ∈ Finset.Icc 1 n, g3 r a) :=
    hMsum.tsum_le_tsum (fun a => not_globalGood_pointwise_le A n a) hRHSsum
  -- split the tsum
  have hsplit : (∑' a, (f1 a + (∑ i, g2 i a) + ∑ r ∈ Finset.Icc 1 n, g3 r a))
      = (∑' a, f1 a) + (∑ i, ∑' a, g2 i a) + ∑ r ∈ Finset.Icc 1 n, ∑' a, g3 r a := by
    rw [(hf1sum.add hf2sum).tsum_add hf3sum, hf1sum.tsum_add hf2sum,
      ← Summable.tsum_finsetSum (fun i _ => hg2sum i),
      ← Summable.tsum_finsetSum (fun r _ => hg3sum r)]
  -- per-family bounds
  have hB1 : (∑' a, f1 a) ≤ (n : ℝ) ^ (-(A + 2)) := hg1 n hn1le
  have hB2 : (∑ i : Fin n, ∑' a, g2 i a) ≤ (n : ℝ) * (n : ℝ) ^ (-(A + 2)) := by
    calc (∑ i : Fin n, ∑' a, g2 i a) ≤ ∑ _i : Fin n, (n : ℝ) ^ (-(A + 2)) :=
          Finset.sum_le_sum fun i _ => hg2 n hn2le i
      _ = (n : ℝ) * (n : ℝ) ^ (-(A + 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB3 : (∑ r ∈ Finset.Icc 1 n, ∑' a, g3 r a) ≤ (n : ℝ) * (n : ℝ) ^ (-(A + 2)) := by
    calc (∑ r ∈ Finset.Icc 1 n, ∑' a, g3 r a)
          ≤ ∑ _r ∈ Finset.Icc 1 n, (n : ℝ) ^ (-(A + 2)) :=
          Finset.sum_le_sum fun r hr => by
            rw [Finset.mem_Icc] at hr; exact hg3 n hn3le r hr.1 hr.2
      _ = (n : ℝ) * (n : ℝ) ^ (-(A + 2)) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  -- assemble M ≤ n^{-(A+2)} + 2·n·n^{-(A+2)}
  have hMfinal : (∑' a, if globalGood A n a then (0 : ℝ) else P a)
      ≤ (n : ℝ) ^ (-(A + 2)) + 2 * ((n : ℝ) * (n : ℝ) ^ (-(A + 2))) := by
    calc (∑' a, if globalGood A n a then (0 : ℝ) else P a)
        ≤ (∑' a, f1 a) + (∑ i, ∑' a, g2 i a) + ∑ r ∈ Finset.Icc 1 n, ∑' a, g3 r a := by
          rw [← hsplit]; exact hMle
      _ ≤ (n : ℝ) ^ (-(A + 2)) + (n : ℝ) * (n : ℝ) ^ (-(A + 2))
            + (n : ℝ) * (n : ℝ) ^ (-(A + 2)) := by
          gcongr <;> first | exact hB1 | exact hB2 | exact hB3
      _ = (n : ℝ) ^ (-(A + 2)) + 2 * ((n : ℝ) * (n : ℝ) ^ (-(A + 2))) := by ring
  -- n·n^{-(A+2)} = n^{-(A+1)}, and the whole thing ≤ 6·n^{-A} ≤ 6·m^{-A}
  have hnB : (n : ℝ) * (n : ℝ) ^ (-(A + 2)) = (n : ℝ) ^ (-(A + 1)) := by
    rw [show (-(A + 1) : ℝ) = 1 + -(A + 2) from by ring, Real.rpow_add hnpos, Real.rpow_one]
  have hexp1 : (n : ℝ) ^ (-(A + 2)) ≤ (n : ℝ) ^ (-(A + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hexp2 : (n : ℝ) ^ (-(A + 1)) ≤ (n : ℝ) ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hnm : (n : ℝ) ^ (-A) ≤ (m : ℝ) ^ (-A) := by
    rw [Real.rpow_neg hnpos.le, Real.rpow_neg hmpos.le, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hmpos _)
      (Real.rpow_le_rpow hmpos.le (by exact_mod_cast hmn) hA.le)
  -- final chain
  calc 2 * (∑' a, if globalGood A n a then (0 : ℝ) else P a)
      ≤ 2 * ((n : ℝ) ^ (-(A + 2)) + 2 * ((n : ℝ) * (n : ℝ) ^ (-(A + 2)))) := by
        linarith [hMfinal]
    _ = 2 * (n : ℝ) ^ (-(A + 2)) + 4 * ((n : ℝ) * (n : ℝ) ^ (-(A + 2))) := by ring
    _ = 2 * (n : ℝ) ^ (-(A + 2)) + 4 * (n : ℝ) ^ (-(A + 1)) := by rw [hnB]
    _ ≤ 2 * (n : ℝ) ^ (-(A + 1)) + 4 * (n : ℝ) ^ (-(A + 1)) := by gcongr
    _ = 6 * (n : ℝ) ^ (-(A + 1)) := by ring
    _ ≤ 6 * (m : ℝ) ^ (-A) := by
        have hchain : (n : ℝ) ^ (-(A + 1)) ≤ (m : ℝ) ^ (-A) := le_trans hexp2 hnm
        linarith

/-- **Obligation 1 (error term)**: the `L¹` mass of `syracZ − mainHigh` is polynomially small. Now a
thin wrapper: `sum_abs_syracZ_sub_mainHigh_eq` turns the `L¹` sum into `P(¬mainEvent)`, the proved
inclusion `globalGood_subset_mainEvent` bounds it by `P(¬globalGood)`, and the pure tail estimate
`prob_not_globalGood_le` finishes. This is Tao (6.3), `P(Ē) ≤ n^{-A-1}`, plus the (6.4) enlargements. -/
theorem error_l1_high_bound (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, m ≤ n → n₀ ≤ n → 9 * n ≤ 10 * m →
      2 * ∑ Y, |(syracZ n Y).toReal - mainHigh A n Y| ≤ C * (m : ℝ) ^ (-A) := by
  obtain ⟨C, hC, n₀, H⟩ := prob_not_globalGood_le A hA
  refine ⟨C, hC, n₀, fun n m hmn hn hreg => ?_⟩
  obtain ⟨hTpos, hbnd⟩ := H n m hmn hn hreg
  rw [sum_abs_syracZ_sub_mainHigh_eq]
  refine le_trans ?_ hbnd
  have hPsum : Summable fun a : Fin n → ℕ => ((geomHalf.iid n) a).toReal :=
    ENNReal.summable_toReal (geomHalf.iid n).tsum_coe_ne_top
  have hmaskM : ∀ a, (if mainEvent A n a then (0 : ℝ) else ((geomHalf.iid n) a).toReal)
      ≤ ((geomHalf.iid n) a).toReal :=
    fun a => by by_cases h : mainEvent A n a <;> simp [h, ENNReal.toReal_nonneg]
  have hmaskG : ∀ a, (if globalGood A n a then (0 : ℝ) else ((geomHalf.iid n) a).toReal)
      ≤ ((geomHalf.iid n) a).toReal :=
    fun a => by by_cases h : globalGood A n a <;> simp [h, ENNReal.toReal_nonneg]
  have hsummM : Summable fun a : Fin n → ℕ =>
      if mainEvent A n a then (0 : ℝ) else ((geomHalf.iid n) a).toReal :=
    Summable.of_nonneg_of_le
      (fun a => by by_cases h : mainEvent A n a <;> simp [h, ENNReal.toReal_nonneg]) hmaskM hPsum
  have hsummG : Summable fun a : Fin n → ℕ =>
      if globalGood A n a then (0 : ℝ) else ((geomHalf.iid n) a).toReal :=
    Summable.of_nonneg_of_le
      (fun a => by by_cases h : globalGood A n a <;> simp [h, ENNReal.toReal_nonneg]) hmaskG hPsum
  -- ¬mainEvent-mass ≤ ¬globalGood-mass, pointwise via the inclusion
  have hmono : (∑' a : Fin n → ℕ, if mainEvent A n a then 0 else ((geomHalf.iid n) a).toReal)
      ≤ ∑' a : Fin n → ℕ, if globalGood A n a then 0 else ((geomHalf.iid n) a).toReal := by
    refine hsummM.tsum_le_tsum (fun a => ?_) hsummG
    by_cases hgood : globalGood A n a
    · have hmain : mainEvent A n a := globalGood_subset_mainEvent A n a hTpos hgood
      simp [hmain, hgood]
    · rw [if_neg hgood]
      by_cases hmain : mainEvent A n a
      · simp [hmain, ENNReal.toReal_nonneg]
      · simp [hmain]
  exact mul_le_mul_of_nonneg_left hmono (by norm_num)

end TaoCollatz
