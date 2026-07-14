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
  sorry

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
