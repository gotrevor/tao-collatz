import TaoCollatz.Syracuse.SyracRV
import TaoCollatz.Prob.LocalInstances
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §4: valuation distribution ≈ `Geom(2)ⁿ` (node C5)

Paper anchors: Tao 2019 §4, Lemma 4.1, Proposition 1.9.
-/

namespace TaoCollatz

open scoped ENNReal

/- Uniform distribution on odd residues modulo `2ⁿ'`; at `n' = 0` there are no
odd residues, so the definition uses a harmless point mass on the trivial ring. -/
noncomputable def unifOddMod (n' : ℕ) : PMF (ZMod (2 ^ n')) :=
  if _h : n' = 0 then PMF.pure 0
  else PMF.ofFinset
    (fun z => if z.val % 2 = 1 then
        ((Finset.univ.filter fun w : ZMod (2 ^ n') => w.val % 2 = 1).card : ℝ≥0∞)⁻¹ else 0)
    (Finset.univ.filter fun z : ZMod (2 ^ n') => z.val % 2 = 1)
    (by
      have h2 : 1 < 2 ^ n' := by
        calc 1 < 2 := one_lt_two
          _ ≤ 2 ^ n' := Nat.le_self_pow _h 2
      haveI : Fact (1 < 2 ^ n') := ⟨h2⟩
      haveI : NeZero (2 ^ n') := ⟨by omega⟩
      have hmem : (1 : ZMod (2 ^ n')) ∈
          Finset.univ.filter fun z : ZMod (2 ^ n') => z.val % 2 = 1 := by
        simp [Finset.mem_filter, ZMod.val_one]
      rw [Finset.sum_congr rfl fun z hz =>
        if_pos (Finset.mem_filter.mp hz).2]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.mul_inv_cancel]
      · exact_mod_cast Finset.card_ne_zero_of_mem hmem
      · exact ENNReal.natCast_ne_top _)
    (by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [if_neg ha])
theorem factor_odd_iff_mod (E d : Nat) (hd : 0 < d) :
    (d ∣ E ∧ E / d % 2 = 1) ↔ E % (2 * d) = d := by
  constructor
  · rintro ⟨⟨q, rfl⟩, hq⟩
    rw [Nat.mul_comm d q, Nat.mul_div_left _ hd] at hq
    have hq' : q = 2 * (q / 2) + 1 := by omega
    rw [hq']
    have heq : d * (2 * (q / 2) + 1) = (2 * d) * (q / 2) + d := by ring
    rw [heq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · intro h
    have hdecomp := (Nat.mod_add_div E (2 * d)).symm
    rw [h] at hdecomp
    have hE : E = d * (2 * (E / (2 * d)) + 1) := by
      calc
        E = d + 2 * d * (E / (2 * d)) := hdecomp
        _ = d * (2 * (E / (2 * d)) + 1) := by ring
    constructor
    · exact ⟨_, hE⟩
    · rw [hE, Nat.mul_comm d, Nat.mul_div_left _ hd]
      omega

theorem valVec_eq_iff_mod (N n : Nat) (hN : N % 2 = 1) (a : Fin n -> Nat)
    (ha : ∀ i, 1 ≤ a i) :
    a = valVec N n ↔
      (3 ^ n * N + fnat n a) % (2 ^ (pre a n + 1)) = 2 ^ pre a n := by
  rw [← valVec_unique N n hN a ha]
  unfold Aff
  rw [factor_odd_iff_mod _ _ (by positivity)]
  simp only [pow_succ, Nat.mul_comm]

theorem valVec_eq_iff_mod' (N n : Nat) (hN : N % 2 = 1) (a : Fin n -> Nat)
    (ha : ∀ i, 1 ≤ a i) :
    valVec N n = a ↔
      (3 ^ n * N + fnat n a) % (2 ^ (pre a n + 1)) = 2 ^ pre a n := by
  rw [eq_comm, valVec_eq_iff_mod N n hN a ha]

noncomputable def valuationResidue (n : Nat) (a : Fin n -> Nat) :
    ZMod (2 ^ (pre a n + 1)) :=
  (3 ^ n : ZMod (2 ^ (pre a n + 1)))⁻¹ * (2 ^ pre a n - fnat n a)

theorem valuationResidue_spec (n : Nat) (a : Fin n -> Nat) :
    (3 ^ n : ZMod (2 ^ (pre a n + 1))) * valuationResidue n a + fnat n a =
      2 ^ pre a n := by
  unfold valuationResidue
  have hu : IsUnit (3 ^ n : ZMod (2 ^ (pre a n + 1))) := by
    exact ((ZMod.isUnit_iff_coprime _ _).2
      ((by decide : Nat.Coprime 3 2).pow_right (pre a n + 1))).pow n
  rw [← mul_assoc, ZMod.mul_inv_of_unit _ hu]
  ring

theorem valuationResidue_unique (n : Nat) (a : Fin n -> Nat) (z : ZMod (2 ^ (pre a n + 1)))
    (hz : (3 ^ n : ZMod (2 ^ (pre a n + 1))) * z + fnat n a = 2 ^ pre a n) :
    z = valuationResidue n a := by
  have hu : IsUnit (3 ^ n : ZMod (2 ^ (pre a n + 1))) := by
    exact ((ZMod.isUnit_iff_coprime _ _).2
      ((by decide : Nat.Coprime 3 2).pow_right (pre a n + 1))).pow n
  apply_fun (fun w : ZMod (2 ^ (pre a n + 1)) =>
    (3 ^ n : ZMod (2 ^ (pre a n + 1)))⁻¹ *
      (w - (fnat n a : ZMod (2 ^ (pre a n + 1))))) at hz
  simpa [valuationResidue, ← mul_assoc, ZMod.inv_mul_of_unit _ hu] using hz

theorem valVec_eq_iff_residue (N n : Nat) (hN : N % 2 = 1) (a : Fin n -> Nat)
    (ha : ∀ i, 1 ≤ a i) :
    valVec N n = a ↔
      (N : ZMod (2 ^ (pre a n + 1))) = valuationResidue n a := by
  rw [valVec_eq_iff_mod' N n hN a ha]
  constructor
  · intro h
    apply valuationResidue_unique
    have hc : ((3 ^ n * N + fnat n a : Nat) : ZMod (2 ^ (pre a n + 1))) =
        (2 ^ pre a n : Nat) := by
      rw [ZMod.natCast_eq_natCast_iff']
      rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]
      exact h
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
  · intro h
    have hc := congrArg
      (fun z : ZMod (2 ^ (pre a n + 1)) =>
        (3 ^ n : ZMod (2 ^ (pre a n + 1))) * z +
          (fnat n a : ZMod (2 ^ (pre a n + 1)))) h
    rw [valuationResidue_spec] at hc
    have hc' : ((3 ^ n * N + fnat n a : Nat) : ZMod (2 ^ (pre a n + 1))) =
        (2 ^ pre a n : Nat) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
    rw [ZMod.natCast_eq_natCast_iff'] at hc'
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))] at hc'
    exact hc'

theorem valuationResidue_odd (n : Nat) (a : Fin n -> Nat) (ha : ∀ i, 1 ≤ a i) :
    (valuationResidue n a).val % 2 = 1 := by
  have natCast_two (x : Nat) : (x : ZMod 2) = (x % 2 : Nat) := by
    rw [ZMod.natCast_eq_natCast_iff']
    simp only [Nat.mod_mod_of_dvd _ (dvd_refl 2)]
  have hpre : n ≤ pre a n := by
    unfold pre
    calc
      n = ∑ _i ∈ Finset.range n, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range n, if h : i < n then a ⟨i, h⟩ else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        rw [dif_pos hi]
        exact ha ⟨i, hi⟩
  let cast2 := ZMod.castHom (pow_dvd_pow 2 (show 1 ≤ pre a n + 1 by omega)) (ZMod 2)
  have hs := congrArg cast2 (valuationResidue_spec n a)
  have hfn : cast2 (fnat n a : ZMod (2 ^ (pre a n + 1))) =
      if n = 0 then 0 else 1 := by
    rw [map_natCast, natCast_two, fnat_mod_two_of_pos a ha]
    split_ifs <;> norm_num
  have hcast : cast2 (valuationResidue n a) = 1 := by
    rcases n with _ | n
    · norm_num [cast2, pre, fnat] at hs ⊢
      exact hs
    · have hp : cast2 (2 ^ pre a (n + 1) : ZMod (2 ^ (pre a (n + 1) + 1))) = 0 := by
        rw [map_pow]
        have h2 : cast2 (2 : ZMod (2 ^ (pre a (n + 1) + 1))) = 0 := by
          calc
            cast2 (2 : ZMod (2 ^ (pre a (n + 1) + 1))) = (2 : ZMod 2) :=
              ZMod.cast_natCast (pow_dvd_pow 2 (show 1 ≤ pre a (n + 1) + 1 by omega)) 2
            _ = 0 := by decide
        rw [h2, zero_pow (by omega : pre a (n + 1) ≠ 0)]
      simp only [map_add, map_mul, map_pow] at hs
      have hp' : cast2 (2 : ZMod (2 ^ (pre a (n + 1) + 1))) ^ pre a (n + 1) = 0 := by
        simpa only [map_pow] using hp
      have h3 : cast2 (3 : ZMod (2 ^ (pre a (n + 1) + 1))) = 1 := by
        calc
          cast2 (3 : ZMod (2 ^ (pre a (n + 1) + 1))) = (3 : ZMod 2) :=
            ZMod.cast_natCast (pow_dvd_pow 2 (show 1 ≤ pre a (n + 1) + 1 by omega)) 3
          _ = 1 := by decide
      rw [hfn, if_neg (by omega), hp', h3, one_pow, one_mul] at hs
      have hr : cast2 (valuationResidue (n + 1) a) = -1 :=
        eq_neg_of_add_eq_zero_left hs
      rw [hr]
      decide
  have hv : ((valuationResidue n a).val : ZMod 2) = 1 := by
    simpa [cast2] using hcast
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hv
  simpa using this

theorem card_zmod_two_pow_cast_fiber (n k : Nat) (hkn : k ≤ n) (r : ZMod (2 ^ k)) :
    (Finset.univ.filter fun z : ZMod (2 ^ n) =>
      ZMod.cast z = r).card = 2 ^ (n - k) := by
  let m := 2 ^ k
  let q := 2 ^ (n - k)
  have hpow : 2 ^ n = m * q := by
    dsimp [m, q]
    rw [← pow_add]
    congr 1
    omega
  let f : ZMod (2 ^ n) → Nat := fun z => z.val / m
  let g : Nat → ZMod (2 ^ n) := fun j => r.val + m * j
  rw [show 2 ^ (n - k) = (Finset.range q).card by simp [q]]
  apply Finset.card_nbij' f g
  · intro z hz
    change f z ∈ Finset.range q
    rw [Finset.mem_range]
    have hzlt : z.val < m * q := by simpa [← hpow] using z.val_lt
    exact (Nat.div_lt_iff_lt_mul (by positivity)).2 (by simpa [Nat.mul_comm] using hzlt)
  · intro j hj
    change j ∈ Finset.range q at hj
    change g j ∈ Finset.univ.filter fun z : ZMod (2 ^ n) => ZMod.cast z = r
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ _
    · rw [Finset.mem_range] at hj
      have hrlt : r.val < m := by simpa [m] using r.val_lt
      have hval : r.val + m * j < 2 ^ n := by
        rw [hpow]
        nlinarith
      have hg : g j = (r.val + m * j : Nat) := by simp [g, Nat.cast_add, Nat.cast_mul]
      rw [hg]
      rw [← ZMod.natCast_zmod_val r]
      rw [ZMod.cast_natCast (by simpa [m] using pow_dvd_pow 2 hkn)]
      rw [ZMod.natCast_eq_natCast_iff']
      simp [m, Nat.add_mod, Nat.mod_eq_of_lt hrlt]
  · intro z hz
    change z ∈ Finset.univ.filter (fun z : ZMod (2 ^ n) => ZMod.cast z = r) at hz
    rw [Finset.mem_filter] at hz
    have hcast := hz.2
    rw [← ZMod.natCast_zmod_val z, ← ZMod.natCast_zmod_val r] at hcast
    rw [ZMod.cast_natCast (by simpa [m] using pow_dvd_pow 2 hkn)] at hcast
    rw [ZMod.natCast_eq_natCast_iff'] at hcast
    have hrlt : r.val < m := by simpa [m] using r.val_lt
    have hmod : z.val % m = r.val := by
      simpa [m, Nat.mod_eq_of_lt hrlt] using hcast
    apply ZMod.val_injective
    simp only [f]
    have hzdecomp := (Nat.mod_add_div z.val m).symm
    rw [hmod] at hzdecomp
    have hlt : r.val + m * (z.val / m) < 2 ^ n := by
      rw [← hzdecomp]
      exact z.val_lt
    have hg : g (z.val / m) = (r.val + m * (z.val / m) : Nat) := by
      simp [g, Nat.cast_add, Nat.cast_mul]
    rw [hg, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    exact hzdecomp.symm
  · intro j hj
    change j ∈ Finset.range q at hj
    rw [Finset.mem_range] at hj
    simp only [f]
    have hrlt : r.val < m := by simpa [m] using r.val_lt
    have hval : r.val + m * j < 2 ^ n := by
      rw [hpow]
      nlinarith
    have hg : g j = (r.val + m * j : Nat) := by simp [g, Nat.cast_add, Nat.cast_mul]
    rw [hg, ZMod.val_natCast, Nat.mod_eq_of_lt hval]
    rw [Nat.add_mul_div_left _ _ (show 0 < m by simp [m]), Nat.div_eq_of_lt hrlt, zero_add]

/-- Re-exported from `Prob/Basic.lean`: the pointwise mass of an iid vector is the
product of its coordinate masses. -/
theorem iid_apply_eq_prod {α : Type*} (p : PMF α) (n : Nat) (v : Fin n → α) :
    p.iid n v = ∏ i, p (v i) := PMF.iid_apply_eq_prod p n v

theorem iid_geomHalf_apply_of_pos (n : Nat) (a : Fin n -> Nat) (ha : ∀ i, 1 ≤ a i) :
    (geomHalf.iid n) a = 2⁻¹ ^ pre a n := by
  rw [iid_apply_eq_prod]
  have hpre : pre a n = ∑ i, a i := by
    unfold pre
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => if h : i < n then a ⟨i, h⟩ else 0) n]
    apply Finset.sum_congr rfl
    intro i hi
    rw [dif_pos i.isLt]
  rw [hpre]
  let half : ℝ≥0∞ := 2⁻¹
  calc
    (∏ i : Fin n, geomHalf (a i)) = (∏ i : Fin n, half ^ a i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [geomHalf_apply, if_neg (by have := ha i; omega)]
    _ = half ^ (∑ i : Fin n, a i) := by
      simpa using Finset.prod_pow_eq_pow_sum Finset.univ a half

theorem zmod_two_pow_odd_iff_cast_one (n : Nat) (hn : 1 ≤ n) (z : ZMod (2 ^ n)) :
    z.val % 2 = 1 ↔ ZMod.cast z = (1 : ZMod 2) := by
  have hcast : (ZMod.cast z : ZMod 2) = (z.val : ZMod 2) := by
    calc
      (ZMod.cast z : ZMod 2) = ZMod.cast (z.val : ZMod (2 ^ n)) :=
        congrArg (fun w : ZMod (2 ^ n) => (ZMod.cast w : ZMod 2))
          (ZMod.natCast_zmod_val z).symm
      _ = (z.val : ZMod 2) :=
        ZMod.cast_natCast (R := ZMod 2) (pow_dvd_pow 2 hn) z.val
  rw [hcast]
  simpa using (ZMod.natCast_eq_natCast_iff' z.val 1 2).symm

theorem card_odd_zmod_two_pow (n : Nat) (hn : 1 ≤ n) :
    (Finset.univ.filter fun z : ZMod (2 ^ n) => z.val % 2 = 1).card = 2 ^ (n - 1) := by
  have heq : (Finset.univ.filter fun z : ZMod (2 ^ n) => z.val % 2 = 1) =
      Finset.univ.filter fun z : ZMod (2 ^ n) => ZMod.cast z = (1 : ZMod 2) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact zmod_two_pow_odd_iff_cast_one n hn z
  rw [heq]
  exact card_zmod_two_pow_cast_fiber n 1 hn (1 : ZMod 2)

theorem unifOddMod_apply_of_pos (n : Nat) (hn : 1 ≤ n) (z : ZMod (2 ^ n)) :
    unifOddMod n z = if z.val % 2 = 1 then (2 ^ (n - 1) : ℝ≥0∞)⁻¹ else 0 := by
  unfold unifOddMod
  rw [dif_neg (by omega)]
  rw [PMF.ofFinset_apply]
  congr 1
  rw [card_odd_zmod_two_pow n hn]
  norm_cast

theorem odd_and_valVec_eq_iff_cast (n n' : Nat) (a : Fin n -> Nat)
    (ha : ∀ i, 1 ≤ a i) (hL : pre a n < n') (z : ZMod (2 ^ n')) :
    (z.val % 2 = 1 ∧ valVec z.val n = a) ↔
      (ZMod.cast z : ZMod (2 ^ (pre a n + 1))) = valuationResidue n a := by
  have hkn : pre a n + 1 ≤ n' := by omega
  have hdvd : 2 ^ (pre a n + 1) ∣ 2 ^ n' := pow_dvd_pow 2 hkn
  have hcast : (ZMod.cast z : ZMod (2 ^ (pre a n + 1))) =
      (z.val : ZMod (2 ^ (pre a n + 1))) := by
    calc
      (ZMod.cast z : ZMod (2 ^ (pre a n + 1))) =
          ZMod.cast (z.val : ZMod (2 ^ n')) :=
        congrArg (fun w : ZMod (2 ^ n') =>
          (ZMod.cast w : ZMod (2 ^ (pre a n + 1))))
            (ZMod.natCast_zmod_val z).symm
      _ = (z.val : ZMod (2 ^ (pre a n + 1))) :=
        ZMod.cast_natCast (R := ZMod (2 ^ (pre a n + 1))) hdvd z.val
  constructor
  · rintro ⟨hzodd, hzval⟩
    rw [hcast]
    exact (valVec_eq_iff_residue z.val n hzodd a ha).mp hzval
  · intro hz
    have hzr : (z.val : ZMod (2 ^ (pre a n + 1))) = valuationResidue n a :=
      hcast.symm.trans hz
    have hmod := (ZMod.natCast_eq_natCast_iff' z.val (valuationResidue n a).val
      (2 ^ (pre a n + 1))).mp (hzr.trans (ZMod.natCast_zmod_val _).symm)
    have hrlt := (valuationResidue n a).val_lt
    rw [Nat.mod_eq_of_lt hrlt] at hmod
    have h2dvd : 2 ∣ 2 ^ (pre a n + 1) := by
      refine ⟨2 ^ pre a n, ?_⟩
      rw [pow_succ]
      omega
    have hzodd : z.val % 2 = 1 := by
      calc
        z.val % 2 = (z.val % 2 ^ (pre a n + 1)) % 2 :=
          (Nat.mod_mod_of_dvd z.val h2dvd).symm
        _ = (valuationResidue n a).val % 2 := by rw [hmod]
        _ = 1 := valuationResidue_odd n a ha
    exact ⟨hzodd, (valVec_eq_iff_residue z.val n hzodd a ha).mpr hzr⟩

theorem unifOddMod_map_valVec_apply (n n' : Nat) (a : Fin n -> Nat)
    (ha : ∀ i, 1 ≤ a i) (hL : pre a n < n') :
    ((unifOddMod n').map fun z => valVec z.val n) a = (geomHalf.iid n) a := by
  classical
  have hn' : 1 ≤ n' := by omega
  let c : ℝ≥0∞ := (2 ^ (n' - 1) : ℝ≥0∞)⁻¹
  rw [PMF.map_apply]
  have hterm : ∀ z : ZMod (2 ^ n'),
      (@ite ℝ≥0∞ (a = valVec z.val n) (Classical.propDecidable _)
        (unifOddMod n' z) 0) =
        if (ZMod.cast z : ZMod (2 ^ (pre a n + 1))) = valuationResidue n a then c else 0 := by
    intro z
    by_cases hz : (ZMod.cast z : ZMod (2 ^ (pre a n + 1))) = valuationResidue n a
    · obtain ⟨hzodd, hzval⟩ := (odd_and_valVec_eq_iff_cast n n' a ha hL z).mpr hz
      rw [if_pos hz, if_pos hzval.symm, unifOddMod_apply_of_pos n' hn' z, if_pos hzodd]
    · rw [if_neg hz]
      by_cases hzodd : z.val % 2 = 1
      · have hzval : valVec z.val n ≠ a := by
          intro heq
          exact hz ((odd_and_valVec_eq_iff_cast n n' a ha hL z).mp ⟨hzodd, heq⟩)
        rw [if_neg (Ne.symm hzval)]
      · rw [unifOddMod_apply_of_pos n' hn' z, if_neg hzodd]
        split_ifs <;> rfl
  refine (tsum_congr fun z => hterm z).trans ?_
  rw [tsum_fintype]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_zmod_two_pow_cast_fiber n' (pre a n + 1) (by omega) (valuationResidue n a)]
  have hexp : n' - 1 = pre a n + (n' - (pre a n + 1)) := by omega
  have hpowNat : 2 ^ (n' - 1) = 2 ^ pre a n * 2 ^ (n' - (pre a n + 1)) := by
    rw [hexp, pow_add]
  have hpowEN : (2 ^ (n' - 1) : ℝ≥0∞) =
      (2 ^ pre a n : ℝ≥0∞) * (2 ^ (n' - (pre a n + 1)) : ℝ≥0∞) := by
    exact_mod_cast hpowNat
  dsimp [c]
  rw [hpowEN]
  push_cast
  rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness))]
  rw [show (2 ^ (n' - (pre a n + 1)) : ℝ≥0∞) *
      ((2 ^ pre a n : ℝ≥0∞)⁻¹ * (2 ^ (n' - (pre a n + 1)) : ℝ≥0∞)⁻¹) =
      (2 ^ pre a n : ℝ≥0∞)⁻¹ * ((2 ^ (n' - (pre a n + 1)) : ℝ≥0∞) *
        (2 ^ (n' - (pre a n + 1)) : ℝ≥0∞)⁻¹) by ring,
    show (2 ^ (n' - (pre a n + 1)) : ℝ≥0∞) *
      (2 ^ (n' - (pre a n + 1)) : ℝ≥0∞)⁻¹ = 1 by
        exact ENNReal.mul_inv_cancel (by positivity) (by finiteness)]
  rw [mul_one, ENNReal.inv_pow]
  exact (iid_geomHalf_apply_of_pos n a ha).symm

theorem valVec_pos (N n : Nat) (hN : N % 2 = 1) (i : Fin n) : 1 ≤ valVec N n i := by
  unfold valVec
  apply one_le_padicValNat_of_dvd (by positivity)
  apply Nat.dvd_of_mod_eq_zero
  have hi : syr^[(i : Nat)] N % 2 = 1 := syr_iterate_odd N i hN
  omega

theorem iid_geomHalf_apply_eq_zero_of_not_pos (n : Nat) (a : Fin n -> Nat)
    (ha : ¬ ∀ i, 1 ≤ a i) : (geomHalf.iid n) a = 0 := by
  rw [iid_apply_eq_prod]
  push Not at ha
  obtain ⟨i, hi⟩ := ha
  have hai : a i = 0 := by omega
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [geomHalf_apply, if_pos hai]

theorem unifOddMod_map_valVec_apply_eq_zero_of_not_pos (n n' : Nat) (hn' : 1 ≤ n')
    (a : Fin n -> Nat) (ha : ¬ ∀ i, 1 ≤ a i) :
    ((unifOddMod n').map fun z => valVec z.val n) a = 0 := by
  classical
  rw [PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  split_ifs with hz
  · by_cases hzodd : z.val % 2 = 1
    · exfalso
      apply ha
      rw [hz]
      exact fun i => valVec_pos z.val n hzodd i
    · rw [unifOddMod]
      rw [dif_neg (by omega), PMF.ofFinset_apply]
      rw [if_neg hzodd]
  · rfl

theorem PMF.tsum_toReal_eq_one {α : Type*} (p : PMF α) :
    ∑' x, (p x).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x), p.tsum_coe,
    ENNReal.toReal_one]

theorem PMF.dTV_le_two_event {α : Type*} (p q : PMF α) (E : α -> Prop)
    [DecidablePred E] (heq : ∀ x, ¬ E x -> p x = q x) :
    p.dTV q ≤ 2 * ∑' x, if E x then (q x).toReal else 0 := by
  have hp : Summable fun x => (p x).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hq : Summable fun x => (q x).toReal :=
    ENNReal.summable_toReal q.tsum_coe_ne_top
  have event_summable (r : PMF α) (hr : Summable fun x => (r x).toReal) :
      Summable fun x => if E x then (r x).toReal else 0 :=
    Summable.of_nonneg_of_le (fun x => by by_cases hx : E x <;> simp [hx, ENNReal.toReal_nonneg])
      (fun x => by by_cases hx : E x <;> simp [hx, ENNReal.toReal_nonneg]) hr
  have comp_summable (r : PMF α) (hr : Summable fun x => (r x).toReal) :
      Summable fun x => if E x then 0 else (r x).toReal :=
    Summable.of_nonneg_of_le (fun x => by by_cases hx : E x <;> simp [hx, ENNReal.toReal_nonneg])
      (fun x => by by_cases hx : E x <;> simp [hx, ENNReal.toReal_nonneg]) hr
  have hsplit (r : PMF α) (hr : Summable fun x => (r x).toReal) :
      (∑' x, if E x then (r x).toReal else 0) +
        (∑' x, if E x then 0 else (r x).toReal) = 1 := by
    rw [← (event_summable r hr).tsum_add (comp_summable r hr)]
    calc
      (∑' x, ((if E x then (r x).toReal else 0) +
          (if E x then 0 else (r x).toReal))) = (∑' x, (r x).toReal) := by
        apply tsum_congr
        intro x
        split_ifs <;> ring
      _ = 1 := PMF.tsum_toReal_eq_one r
  have hcomp : (∑' x, if E x then 0 else (p x).toReal) =
      ∑' x, if E x then 0 else (q x).toReal := by
    apply tsum_congr
    intro x
    by_cases hx : E x
    · simp [hx]
    · simp [hx, heq x hx]
  have hevent : (∑' x, if E x then (p x).toReal else 0) =
      ∑' x, if E x then (q x).toReal else 0 := by
    have hp1 := hsplit p hp
    have hq1 := hsplit q hq
    rw [hcomp] at hp1
    linarith
  have hbound : ∀ x, |(p x).toReal - (q x).toReal| ≤
      (if E x then (p x).toReal else 0) + (if E x then (q x).toReal else 0) := by
    intro x
    by_cases hx : E x
    · rw [if_pos hx, if_pos hx]
      rw [abs_le]
      have hp0 : 0 ≤ (p x).toReal := ENNReal.toReal_nonneg
      have hq0 : 0 ≤ (q x).toReal := ENNReal.toReal_nonneg
      constructor <;> nlinarith
    · rw [if_neg hx, if_neg hx, heq x hx, sub_self, abs_zero, zero_add]
  have habs : Summable fun x => |(p x).toReal - (q x).toReal| :=
    Summable.of_nonneg_of_le (fun x => abs_nonneg _) hbound
      ((event_summable p hp).add (event_summable q hq))
  unfold PMF.dTV
  calc
    (∑' x, |(p x).toReal - (q x).toReal|) ≤
        ∑' x, ((if E x then (p x).toReal else 0) +
          (if E x then (q x).toReal else 0)) :=
      habs.tsum_le_tsum hbound ((event_summable p hp).add (event_summable q hq))
    _ = (∑' x, if E x then (p x).toReal else 0) +
        (∑' x, if E x then (q x).toReal else 0) := by
      rw [(event_summable p hp).tsum_add (event_summable q hq)]
    _ = 2 * ∑' x, if E x then (q x).toReal else 0 := by rw [hevent]; ring

theorem valVec_stable_below (N M n k : Nat) (hN : N % 2 = 1) (hM : M % 2 = 1)
    (hmod : N % 2 ^ k = M % 2 ^ k) (hL : pre (valVec N n) n < k) :
    valVec M n = valVec N n := by
  let a := valVec N n
  have ha : ∀ i, 1 ≤ a i := fun i => valVec_pos N n hN i
  have hkn : pre a n + 1 ≤ k := by
    dsimp [a]
    omega
  have hdvd : 2 ^ (pre a n + 1) ∣ 2 ^ k := pow_dvd_pow 2 hkn
  have hlow : M % 2 ^ (pre a n + 1) = N % 2 ^ (pre a n + 1) := by
    calc
      M % 2 ^ (pre a n + 1) = (M % 2 ^ k) % 2 ^ (pre a n + 1) :=
        (Nat.mod_mod_of_dvd M hdvd).symm
      _ = (N % 2 ^ k) % 2 ^ (pre a n + 1) := by rw [hmod]
      _ = N % 2 ^ (pre a n + 1) := Nat.mod_mod_of_dvd N hdvd
  have hNres : (N : ZMod (2 ^ (pre a n + 1))) = valuationResidue n a :=
    (valVec_eq_iff_residue N n hN a ha).mp rfl
  have hMN : (M : ZMod (2 ^ (pre a n + 1))) = (N : ZMod (2 ^ (pre a n + 1))) := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact hlow
  exact (valVec_eq_iff_residue M n hM a ha).mpr (hMN.trans hNres)

noncomputable def truncateVal (n k : Nat) (z : ZMod (2 ^ k)) : Option (Fin n -> Nat) :=
  if pre (valVec z.val n) n < k then some (valVec z.val n) else none

theorem truncateVal_natCast (N n k : Nat) (hN : N % 2 = 1) :
    truncateVal n k (N : ZMod (2 ^ k)) =
      if pre (valVec N n) n < k then some (valVec N n) else none := by
  rcases k with _ | k
  · simp [truncateVal]
  unfold truncateVal
  let M := ((N : ZMod (2 ^ (k + 1)))).val
  change (if pre (valVec M n) n < k + 1 then some (valVec M n) else none) = _
  have hmod : M % 2 ^ (k + 1) = N % 2 ^ (k + 1) := by
    dsimp [M]
    rw [ZMod.val_natCast]
    exact Nat.mod_mod _ _
  have hM : M % 2 = 1 := by
    have h2dvd : 2 ∣ 2 ^ (k + 1) := by
      rw [pow_succ]
      exact ⟨2 ^ k, by rw [mul_comm]⟩
    calc
      M % 2 = (M % 2 ^ (k + 1)) % 2 := (Nat.mod_mod_of_dvd M h2dvd).symm
      _ = (N % 2 ^ (k + 1)) % 2 := by rw [hmod]
      _ = N % 2 := Nat.mod_mod_of_dvd N h2dvd
      _ = 1 := hN
  by_cases hL : pre (valVec N n) n < k + 1
  · have hv := valVec_stable_below N M n (k + 1) hN hM hmod.symm hL
    simp [hv, hL]
  · have hLM : ¬pre (valVec M n) n < k + 1 := by
      intro h
      have hv := valVec_stable_below M N n (k + 1) hM hN hmod h
      rw [← hv] at h
      exact hL h
    simp [hL, hLM]

open Classical in
theorem PMF.dTV_map_le {α β : Type*} (p q : PMF α) (f : α → β) :
    (p.map f).dTV (q.map f) ≤ p.dTV q := by
  let r : α → ℝ := fun a => (p a).toReal - (q a).toReal
  have hp : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hq : Summable fun a => (q a).toReal :=
    ENNReal.summable_toReal q.tsum_coe_ne_top
  have hr : Summable r := hp.sub hq
  have habs : Summable fun a => |r a| := hr.abs
  have hreal (s : PMF α) (b : β) :
      ((s.map f) b).toReal = ∑' a, if b = f a then (s a).toReal else 0 := by
    rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
    · exact tsum_congr fun a => by
        rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    · intro a
      split
      · exact s.apply_ne_top a
      · exact ENNReal.zero_ne_top
  have hfiber (b : β) : Summable fun a => if b = f a then r a else 0 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun a => norm_nonneg _) ?_ habs)
    intro a
    split <;> simp [Real.norm_eq_abs]
  have hfiber_abs (b : β) : Summable fun a => if b = f a then |r a| else 0 := by
    refine Summable.of_nonneg_of_le (fun a => by positivity) ?_ habs
    intro a
    split <;> simp
  have hdiff (b : β) :
      ((p.map f) b).toReal - ((q.map f) b).toReal =
        ∑' a, if b = f a then r a else 0 := by
    have hpf : Summable fun a => if b = f a then (p a).toReal else 0 := by
      refine Summable.of_nonneg_of_le (fun a => by positivity) ?_ hp
      intro a
      split <;> simp [ENNReal.toReal_nonneg]
    have hqf : Summable fun a => if b = f a then (q a).toReal else 0 := by
      refine Summable.of_nonneg_of_le (fun a => by positivity) ?_ hq
      intro a
      split <;> simp [ENNReal.toReal_nonneg]
    rw [hreal p b, hreal q b, ← hpf.tsum_sub hqf]
    refine tsum_congr fun a => ?_
    dsimp only [r]
    split <;> simp
  have hpoint (b : β) :
      |((p.map f) b).toReal - ((q.map f) b).toReal| ≤
        ∑' a, if b = f a then |r a| else 0 := by
    rw [hdiff b]
    have hnorm : Summable fun a => ‖if b = f a then r a else 0‖ := by
      refine (hfiber_abs b).congr fun a => ?_
      split <;> simp [Real.norm_eq_abs]
    calc
      |∑' a, if b = f a then r a else 0| = ‖∑' a, if b = f a then r a else 0‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∑' a, ‖if b = f a then r a else 0‖ := norm_tsum_le_tsum_norm hnorm
      _ = ∑' a, if b = f a then |r a| else 0 := tsum_congr fun a => by
        split <;> simp [Real.norm_eq_abs]
  have hprod : Summable fun ba : β × α =>
      if ba.1 = f ba.2 then |r ba.2| else 0 := by
    have hswap : Summable fun ab : α × β =>
        if ab.2 = f ab.1 then |r ab.1| else 0 := by
      rw [summable_prod_of_nonneg (fun ab => by positivity)]
      constructor
      · intro a
        exact summable_of_ne_finset_zero (s := {f a}) fun b hb => by
          rw [if_neg (by simpa using hb)]
      · have hi : (fun a => ∑' b, if b = f a then |r a| else 0) = fun a => |r a| := by
          funext a
          rw [tsum_eq_single (f a)]
          · simp
          · intro b hb
            rw [if_neg hb]
        rw [hi]
        exact habs
    refine ((Equiv.prodComm β α).summable_iff.mpr hswap).congr fun ba => ?_
    rfl
  have hout : Summable fun b => ∑' a, if b = f a then |r a| else 0 :=
    (summable_prod_of_nonneg (fun ba : β × α => by positivity)).mp hprod |>.2
  have hcol (a : α) : Summable fun b => if b = f a then |r a| else 0 :=
    summable_of_ne_finset_zero (s := {f a}) fun b hb => by
      rw [if_neg (by simpa using hb)]
  unfold PMF.dTV
  calc
    (∑' b, |((p.map f) b).toReal - ((q.map f) b).toReal|) ≤
        ∑' b, ∑' a, if b = f a then |r a| else 0 :=
      (Summable.of_nonneg_of_le (fun b => abs_nonneg _) hpoint
        hout).tsum_le_tsum hpoint hout
    _ = ∑' a, ∑' b, if b = f a then |r a| else 0 :=
      (Summable.tsum_comm' hprod (fun b => hfiber_abs b) hcol).symm
    _ = ∑' a, |r a| := by
      refine tsum_congr fun a => ?_
      rw [tsum_eq_single (f a)]
      · simp
      · intro b hb
        rw [if_neg hb]
    _ = ∑' a, |(p a).toReal - (q a).toReal| := rfl

noncomputable def truncateVec (n k : Nat) (a : Fin n → Nat) : Option (Fin n → Nat) :=
  if pre a n < k then some a else none

theorem PMF.map_truncateVec_some {n : Nat} (p : PMF (Fin n → Nat)) (k : Nat)
    (a : Fin n → Nat) :
    (p.map (truncateVec n k)) (some a) = if pre a n < k then p a else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases hL : pre a n < k
  · rw [if_pos hL, tsum_eq_single a]
    · simp [truncateVec, hL]
    · intro b hb
      rw [if_neg]
      intro heq
      by_cases hbL : pre b n < k
      · simp only [truncateVec, hbL, if_pos, Option.some.injEq] at heq
        exact hb heq.symm
      · simp [truncateVec, hbL] at heq
  · rw [if_neg hL]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    split_ifs with heq
    · by_cases hbL : pre b n < k
      · simp only [truncateVec, hbL, if_pos, Option.some.injEq] at heq
        exact (hL (heq ▸ hbL)).elim
      · simp [truncateVec, hbL] at heq
    · rfl

theorem PMF.option_ext {α : Type*} (p q : PMF (Option α))
    (h : ∀ a, p (some a) = q (some a)) : p = q := by
  classical
  apply PMF.ext
  intro x
  rcases x with _ | a
  · let rp := ∑' x, @ite ℝ≥0∞ (x = none) (Classical.propDecidable _) 0 (p x)
    let rq := ∑' x, @ite ℝ≥0∞ (x = none) (Classical.propDecidable _) 0 (q x)
    have hrest : rp = rq := by
      dsimp only [rp, rq]
      apply tsum_congr
      intro x
      rcases x with _ | a
      · simp
      · simp [h a]
    have hp := ENNReal.tsum_eq_add_tsum_ite (f := fun x => p x) none
    have hq := ENNReal.tsum_eq_add_tsum_ite (f := fun x => q x) none
    rw [p.tsum_coe] at hp
    rw [q.tsum_coe] at hq
    change 1 = p none + rp at hp
    change 1 = q none + rq at hq
    have hq' : 1 = q none + rp :=
      hq.trans (congrArg (fun t => q none + t) hrest.symm)
    have hfinite : rp ≠ ∞ := by
      apply ne_top_of_le_ne_top ENNReal.one_ne_top
      calc
        rp ≤ p none + rp := le_add_self
        _ = 1 := hp.symm
    apply (ENNReal.add_right_inj hfinite).mp
    simpa only [add_comm] using hp.symm.trans hq'
  · exact h a

theorem truncated_uniform_eq_geom (n k : Nat) :
    (((unifOddMod k).map fun z => valVec z.val n).map (truncateVec n k)) =
      (geomHalf.iid n).map (truncateVec n k) := by
  apply PMF.option_ext
  intro a
  rw [PMF.map_truncateVec_some, PMF.map_truncateVec_some]
  by_cases hL : pre a n < k
  · rw [if_pos hL, if_pos hL]
    by_cases ha : ∀ i, 1 ≤ a i
    · exact unifOddMod_map_valVec_apply n k a ha hL
    · have hk : 1 ≤ k := by omega
      rw [unifOddMod_map_valVec_apply_eq_zero_of_not_pos n k hk a ha,
        iid_geomHalf_apply_eq_zero_of_not_pos n a ha]
  · rw [if_neg hL, if_neg hL]

theorem PMF.dTV_le_of_truncateVec {n : Nat} (p q : PMF (Fin n → Nat)) (k : Nat) :
    p.dTV q ≤ 2 * (p.map (truncateVec n k)).dTV (q.map (truncateVec n k)) +
      2 * ∑' a, if k ≤ pre a n then (q a).toReal else 0 := by
  classical
  let D : ℝ := (p.map (truncateVec n k)).dTV (q.map (truncateVec n k))
  let tail (r : PMF (Fin n → Nat)) : ℝ :=
    ∑' a, if k ≤ pre a n then (r a).toReal else 0
  have mass_summable (r : PMF (Fin n → Nat)) : Summable fun a => (r a).toReal :=
    ENNReal.summable_toReal r.tsum_coe_ne_top
  have tail_summable (r : PMF (Fin n → Nat)) :
      Summable fun a => if k ≤ pre a n then (r a).toReal else 0 :=
    Summable.of_nonneg_of_le
      (fun a => by split <;> simp [ENNReal.toReal_nonneg])
      (fun a => by split <;> simp [ENNReal.toReal_nonneg]) (mass_summable r)
  have low_summable (r : PMF (Fin n → Nat)) :
      Summable fun a => if pre a n < k then (r a).toReal else 0 :=
    Summable.of_nonneg_of_le
      (fun a => by split <;> simp [ENNReal.toReal_nonneg])
      (fun a => by split <;> simp [ENNReal.toReal_nonneg]) (mass_summable r)
  have diff_summable (r s : PMF (Fin n → Nat)) :
      Summable fun a => |(r a).toReal - (s a).toReal| :=
    ((mass_summable r).sub (mass_summable s)).abs
  have map_diff_summable : Summable fun x =>
      |((p.map (truncateVec n k)) x).toReal -
        ((q.map (truncateVec n k)) x).toReal| :=
    ((ENNReal.summable_toReal (p.map (truncateVec n k)).tsum_coe_ne_top).sub
      (ENNReal.summable_toReal (q.map (truncateVec n k)).tsum_coe_ne_top)).abs
  have hlow : (∑' a, if pre a n < k then |(p a).toReal - (q a).toReal| else 0) ≤ D := by
    have hcomp : (fun a => |((p.map (truncateVec n k)) (some a)).toReal -
        ((q.map (truncateVec n k)) (some a)).toReal|) =
        fun a => if pre a n < k then |(p a).toReal - (q a).toReal| else 0 := by
      funext a
      rw [PMF.map_truncateVec_some, PMF.map_truncateVec_some]
      by_cases hL : pre a n < k <;> simp [hL]
    rw [← hcomp]
    exact tsum_comp_le_tsum_of_inj map_diff_summable (fun x => abs_nonneg _)
      (Option.some_injective _)
  have hnone (r : PMF (Fin n → Nat)) :
      ((r.map (truncateVec n k)) none).toReal = tail r := by
    rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
    · dsimp only [tail]
      apply tsum_congr
      intro a
      by_cases hL : pre a n < k
      · simp [truncateVec, hL, show ¬k ≤ pre a n by omega]
      · simp [truncateVec, hL, show k ≤ pre a n by omega]
    · intro a
      split
      · exact r.apply_ne_top a
      · exact ENNReal.zero_ne_top
  have htailp : tail p ≤ tail q + D := by
    have hpoint : |((p.map (truncateVec n k)) none).toReal -
        ((q.map (truncateVec n k)) none).toReal| ≤ D := by
      dsimp only [D, PMF.dTV]
      exact map_diff_summable.le_tsum none (fun _ _ => abs_nonneg _)
    rw [hnone p, hnone q] at hpoint
    linarith [le_abs_self (tail p - tail q)]
  have hsplit : p.dTV q =
      (∑' a, if pre a n < k then |(p a).toReal - (q a).toReal| else 0) +
      (∑' a, if k ≤ pre a n then |(p a).toReal - (q a).toReal| else 0) := by
    unfold PMF.dTV
    rw [← (Summable.of_nonneg_of_le
      (fun a => by split <;> positivity)
      (fun a => by split <;> simp) (diff_summable p q)).tsum_add
      (Summable.of_nonneg_of_le
        (fun a => by split <;> positivity)
        (fun a => by split <;> simp) (diff_summable p q))]
    apply tsum_congr
    intro a
    by_cases hL : pre a n < k
    · have hn : ¬k ≤ pre a n := by omega
      simp [hL, hn]
    · have hn : k ≤ pre a n := Nat.le_of_not_gt hL
      simp [hL, hn]
  have hhigh : (∑' a, if k ≤ pre a n then |(p a).toReal - (q a).toReal| else 0) ≤
      tail p + tail q := by
    dsimp only [tail]
    have hs := (tail_summable p).add (tail_summable q)
    have hpoint : ∀ a,
        (if k ≤ pre a n then |(p a).toReal - (q a).toReal| else 0) ≤
          (if k ≤ pre a n then (p a).toReal else 0) +
            (if k ≤ pre a n then (q a).toReal else 0) := by
      intro a
      by_cases ha : k ≤ pre a n
      · simp only [ha, if_pos]
        rw [abs_le]
        have hp0 : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
        have hq0 : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
        constructor <;> linarith
      · simp [ha]
    have hsumdiff : Summable fun a =>
        if k ≤ pre a n then |(p a).toReal - (q a).toReal| else 0 :=
      Summable.of_nonneg_of_le (fun a => by positivity) hpoint hs
    calc
      (∑' a, if k ≤ pre a n then |(p a).toReal - (q a).toReal| else 0) ≤
          ∑' a, ((if k ≤ pre a n then (p a).toReal else 0) +
            (if k ≤ pre a n then (q a).toReal else 0)) :=
        hsumdiff.tsum_le_tsum hpoint hs
      _ = (∑' a, if k ≤ pre a n then (p a).toReal else 0) +
          ∑' a, if k ≤ pre a n then (q a).toReal else 0 :=
        (tail_summable p).tsum_add (tail_summable q)
  rw [hsplit]
  change _ ≤ 2 * D + 2 * tail q
  linarith

theorem PMF.map_congr_support {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hpa : p a = 0 := not_ne_iff.mp (mt (p.mem_support_iff a).mpr ha)
    simp [hpa]

theorem truncated_val_dTV_le (X : PMF Nat) (n k : Nat)
    (hodd : ∀ N ∈ X.support, N % 2 = 1) :
    ((X.map fun N => valVec N n).map (truncateVec n k)).dTV
        ((geomHalf.iid n).map (truncateVec n k)) ≤
      PMF.dTV (PMF.map (fun N => (N : ZMod (2 ^ k))) X) (unifOddMod k) := by
  let castMod : Nat → ZMod (2 ^ k) := fun N => (N : ZMod (2 ^ k))
  have hX : (X.map fun N => valVec N n).map (truncateVec n k) =
      (PMF.map castMod X).map (truncateVal n k) := by
    calc
      (X.map fun N => valVec N n).map (truncateVec n k) =
          X.map (truncateVec n k ∘ fun N => valVec N n) :=
        PMF.map_comp (p := X) (f := fun N => valVec N n) (truncateVec n k)
      _ = X.map (truncateVal n k ∘ castMod) := by
        apply PMF.map_congr_support
        intro N hN
        exact (truncateVal_natCast N n k (hodd N hN)).symm
      _ = (PMF.map castMod X).map (truncateVal n k) := by
        exact (PMF.map_comp (p := X) (f := castMod) (truncateVal n k)).symm
  have hU : ((unifOddMod k).map fun z => valVec z.val n).map (truncateVec n k) =
      (unifOddMod k).map (truncateVal n k) := by
    rw [PMF.map_comp]
    apply PMF.map_congr_support
    intro z hz
    rfl
  rw [hX, ← truncated_uniform_eq_geom n k, hU]
  change _ ≤ (PMF.map (fun z : ZMod (2 ^ k) => z) (PMF.map castMod X)).dTV
    (unifOddMod k)
  rw [show (fun z : ZMod (2 ^ k) => z) = id by rfl, PMF.map_id]
  exact PMF.dTV_map_le (PMF.map castMod X) (unifOddMod k) (truncateVal n k)

theorem PMF.expect_map_of_nonneg {α β : Type*} (p : PMF α) (f : α → β) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b) : (p.map f).expect g = p.expect (g ∘ f) := by
  unfold PMF.expect
  rw [← PMF.toReal_tsum_mul_ofReal (p.map f) g hg, PMF.tsum_map_mul]
  simpa only [Function.comp_apply] using
    PMF.toReal_tsum_mul_ofReal p (fun a => g (f a)) (fun a => hg (f a))

theorem pre_eq_fin_sum (a : Fin n → Nat) : pre a n = ∑ i, a i := by
  unfold pre
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if h : i < n then a ⟨i, h⟩ else 0) n]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos i.isLt]

theorem iid_geomHalf_overflow_eq (n k : Nat) :
    (∑' a : Fin n → Nat, if k ≤ pre a n then ((geomHalf.iid n) a).toReal else 0) =
      (∑' L : Nat, if k ≤ L then ((iidSum geomHalf n) L).toReal else 0) := by
  let E : Set Nat := {L | k ≤ L}
  have hmap := PMF.expect_map_of_nonneg (geomHalf.iid n) (fun a => ∑ i, a i)
    (Set.indicator E 1) (fun L => Set.indicator_nonneg (fun _ _ => zero_le_one) L)
  rw [show (geomHalf.iid n).map (fun a => ∑ i, a i) = iidSum geomHalf n from rfl] at hmap
  unfold PMF.expect at hmap
  simpa only [Function.comp_apply, E, Set.indicator, Set.mem_setOf_eq, Pi.one_apply,
    mul_ite, mul_one, mul_zero, pre_eq_fin_sum] using hmap.symm

theorem geomHalf_overflow_le_Gweight (c₀ c C : ℝ) (hc₀ : 0 < c₀)
    (htail : ∀ (n : Nat) (lam : ℝ), 0 ≤ lam →
      (∑' L : Nat, if lam ≤ |(L : ℝ) - 2 * n| then ((iidSum geomHalf n) L).toReal else 0) ≤
        C * Gweight (1 + n) (c * lam))
    (n k : Nat) (hsize : (2 + c₀) * n ≤ (k : ℝ)) :
    (∑' a : Fin n → Nat, if k ≤ pre a n then ((geomHalf.iid n) a).toReal else 0) ≤
      C * Gweight (1 + n) (c * (c₀ * n)) := by
  rw [iid_geomHalf_overflow_eq]
  have hdom : ∀ L : Nat,
      (if k ≤ L then ((iidSum geomHalf n) L).toReal else 0) ≤
        if c₀ * n ≤ |(L : ℝ) - 2 * n| then ((iidSum geomHalf n) L).toReal else 0 := by
    intro L
    by_cases hL : k ≤ L
    · have hLR : (k : ℝ) ≤ L := by exact_mod_cast hL
      have hdev : c₀ * n ≤ (L : ℝ) - 2 * n := by linarith
      rw [if_pos hL, if_pos (le_trans hdev (le_abs_self _))]
    · rw [if_neg hL]
      positivity
  have hsum : Summable fun L : Nat =>
      if c₀ * n ≤ |(L : ℝ) - 2 * n| then ((iidSum geomHalf n) L).toReal else 0 :=
    Summable.of_nonneg_of_le (fun L => by split <;> positivity)
      (fun L => by split <;> simp [ENNReal.toReal_nonneg])
      (ENNReal.summable_toReal (iidSum geomHalf n).tsum_coe_ne_top)
  exact le_trans ((Summable.of_nonneg_of_le (fun L => by split <;> positivity) hdom hsum).tsum_le_tsum
    hdom hsum) (htail n (c₀ * n) (mul_nonneg hc₀.le (Nat.cast_nonneg n)))

noncomputable def linearDecay (d : ℝ) : ℝ := min (d ^ 2 / 2) d

theorem linearDecay_pos {d : ℝ} (hd : 0 < d) : 0 < linearDecay d := by
  unfold linearDecay
  exact lt_min (div_pos (sq_pos_of_pos hd) (by norm_num)) hd

theorem Gweight_linear_le (d : ℝ) (hd : 0 < d) (n : Nat) :
    Gweight (1 + n) (d * n) ≤ 2 * Real.exp (-linearDecay d * n) := by
  rcases n with _ | n
  · norm_num [Gweight]
  have hn : (1 : ℝ) ≤ (n + 1 : Nat) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hden : 0 < (1 : ℝ) + (n + 1 : Nat) := by positivity
  have hd2 : 0 ≤ d ^ 2 / 2 := by positivity
  have hgamma1 : linearDecay d ≤ d ^ 2 / 2 := min_le_left _ _
  have hgamma2 : linearDecay d ≤ d := min_le_right _ _
  have hquad : linearDecay d * (n + 1 : Nat) ≤
      (d * (n + 1 : Nat)) ^ 2 / (1 + (n + 1 : Nat)) := by
    apply (le_div_iff₀ hden).2
    calc
      linearDecay d * (n + 1 : Nat) * (1 + (n + 1 : Nat)) ≤
          (d ^ 2 / 2) * (n + 1 : Nat) * (1 + (n + 1 : Nat)) := by gcongr
      _ ≤ (d ^ 2 / 2) * (n + 1 : Nat) * (2 * (n + 1 : Nat)) := by
        gcongr <;> linarith
      _ = (d * (n + 1 : Nat)) ^ 2 := by ring
  have hlin : linearDecay d * (n + 1 : Nat) ≤ |d * (n + 1 : Nat)| := by
    rw [abs_of_pos (mul_pos hd (by positivity))]
    gcongr
  unfold Gweight
  have he1 : Real.exp (-(d * (n + 1 : Nat)) ^ 2 / (1 + (n + 1 : Nat))) ≤
      Real.exp (-linearDecay d * (n + 1 : Nat)) :=
    Real.exp_le_exp.mpr (by
      rw [show -(d * (n + 1 : Nat)) ^ 2 / (1 + (n + 1 : Nat)) =
        -((d * (n + 1 : Nat)) ^ 2 / (1 + (n + 1 : Nat))) by ring]
      linarith)
  have he2 : Real.exp (-|d * (n + 1 : Nat)|) ≤
      Real.exp (-linearDecay d * (n + 1 : Nat)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp (-(d * (n + 1 : Nat)) ^ 2 / (1 + (n + 1 : Nat))) +
        Real.exp (-|d * (n + 1 : Nat)|) ≤
      Real.exp (-linearDecay d * (n + 1 : Nat)) +
        Real.exp (-linearDecay d * (n + 1 : Nat)) := add_le_add he1 he2
    _ = 2 * Real.exp (-linearDecay d * (n + 1 : Nat)) := by ring

noncomputable def finalDecay (d : ℝ) : ℝ := min (Real.log 2) (linearDecay d)

theorem finalDecay_pos {d : ℝ} (hd : 0 < d) : 0 < finalDecay d := by
  unfold finalDecay
  exact lt_min (Real.log_pos one_lt_two) (linearDecay_pos hd)

theorem exp_linearDecay_le_two_rpow (d : ℝ) (n : Nat) :
    Real.exp (-linearDecay d * n) ≤
      (2 : ℝ) ^ (-(finalDecay d / Real.log 2) * (n : ℝ)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have heq : Real.log 2 * (-(finalDecay d / Real.log 2) * (n : ℝ)) =
      -finalDecay d * n := by field_simp
  rw [heq]
  apply Real.exp_le_exp.mpr
  have hle : finalDecay d ≤ linearDecay d := min_le_right _ _
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

theorem two_rpow_neg_nat_le (d : ℝ) (hd : 0 < d) (n k : Nat)
    (hnk : (n : ℝ) ≤ k) :
    (2 : ℝ) ^ (-(k : ℝ)) ≤
      (2 : ℝ) ^ (-(finalDecay d / Real.log 2) * (n : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hrho : finalDecay d ≤ Real.log 2 := min_le_left _ _
  have hc1 : finalDecay d / Real.log 2 ≤ 1 := (div_le_one hlog).2 hrho
  have hc10 : 0 ≤ finalDecay d / Real.log 2 :=
    (div_nonneg (finalDecay_pos hd).le hlog.le)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- **Proposition 1.9.** The valuation vector of an odd distribution whose reduction
modulo `2ⁿ'` is close to uniform is exponentially close to `Geom(2)ⁿ`. -/
theorem valuation_dist (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 0 < K) :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧ ∀ (n n' : ℕ) (X : PMF ℕ),
      (2 + c₀) * n ≤ (n' : ℝ) →
      (∀ N ∈ X.support, N % 2 = 1) →
      PMF.dTV (X.map fun N => (N : ZMod (2 ^ n'))) (unifOddMod n') ≤ K * (2 : ℝ) ^ (-(n' : ℝ)) →
      PMF.dTV (X.map fun N => valVec N n) (PMF.iid geomHalf n)
        ≤ C * (2 : ℝ) ^ (-c₁ * (n : ℝ)) := by
  obtain ⟨c, hc, Ct, hCt, htail⟩ := geomHalf_tail_bound
  let d := c * c₀
  let c₁ := finalDecay d / Real.log 2
  let C := 2 * K + 4 * Ct
  have hd : 0 < d := mul_pos hc hc₀
  have hc₁ : 0 < c₁ := div_pos (finalDecay_pos hd) (Real.log_pos one_lt_two)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨c₁, C, hc₁, hC, ?_⟩
  intro n n' X hsize hodd hmod
  let P := X.map fun N => valVec N n
  let Q := geomHalf.iid n
  let T : ℝ := ∑' a : Fin n → Nat, if n' ≤ pre a n then (Q a).toReal else 0
  have htrunc : (P.map (truncateVec n n')).dTV (Q.map (truncateVec n n')) ≤
      K * (2 : ℝ) ^ (-(n' : ℝ)) := by
    exact (truncated_val_dTV_le X n n' hodd).trans hmod
  have hrec := PMF.dTV_le_of_truncateVec P Q n'
  have hoverG : T ≤ Ct * Gweight (1 + n) (c * (c₀ * n)) := by
    exact geomHalf_overflow_le_Gweight c₀ c Ct hc₀ htail n n' hsize
  have harg : c * (c₀ * (n : ℝ)) = d * n := by dsimp only [d]; ring
  have hoverExp : T ≤ 2 * Ct * Real.exp (-linearDecay d * n) := by
    calc
      T ≤ Ct * Gweight (1 + n) (c * (c₀ * n)) := hoverG
      _ = Ct * Gweight (1 + n) (d * n) := by rw [harg]
      _ ≤ Ct * (2 * Real.exp (-linearDecay d * n)) := by
        gcongr
        exact Gweight_linear_le d hd n
      _ = 2 * Ct * Real.exp (-linearDecay d * n) := by ring
  have hn'n : (n : ℝ) ≤ n' := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hresDecay := two_rpow_neg_nat_le d hd n n' hn'n
  have hgeomDecay := exp_linearDecay_le_two_rpow d n
  have hresDecay' : (2 : ℝ) ^ (-(n' : ℝ)) ≤
      (2 : ℝ) ^ (-c₁ * (n : ℝ)) := by simpa only [c₁] using hresDecay
  have hgeomDecay' : Real.exp (-linearDecay d * n) ≤
      (2 : ℝ) ^ (-c₁ * (n : ℝ)) := by simpa only [c₁] using hgeomDecay
  change P.dTV Q ≤ C * (2 : ℝ) ^ (-c₁ * (n : ℝ))
  have hpow0 : 0 ≤ (2 : ℝ) ^ (-c₁ * (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  calc
    P.dTV Q ≤ 2 * (P.map (truncateVec n n')).dTV (Q.map (truncateVec n n')) + 2 * T := hrec
    _ ≤ 2 * (K * (2 : ℝ) ^ (-(n' : ℝ))) +
        2 * (2 * Ct * Real.exp (-linearDecay d * n)) := by gcongr
    _ ≤ 2 * K * (2 : ℝ) ^ (-c₁ * (n : ℝ)) +
        4 * Ct * (2 : ℝ) ^ (-c₁ * (n : ℝ)) := by
      apply add_le_add
      · simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hresDecay' (mul_nonneg (by norm_num) hK.le)
      · have hm := mul_le_mul_of_nonneg_left hgeomDecay'
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCt.le)
        convert hm using 1 <;> ring
    _ = C * (2 : ℝ) ^ (-c₁ * (n : ℝ)) := by dsimp only [C]; ring

theorem two_rpow_decay_mono {c c' : ℝ} (hcc' : c ≤ c') (n : Nat) :
    (2 : ℝ) ^ (-c' * (n : ℝ)) ≤ (2 : ℝ) ^ (-c * (n : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- **Lemma 4.1.** Under the same hypotheses, the total valuation exceeds `n'`
with exponentially small probability. -/
theorem valuation_tail (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 0 < K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n n' : ℕ) (X : PMF ℕ),
      (2 + c₀) * n ≤ (n' : ℝ) →
      (∀ N ∈ X.support, N % 2 = 1) →
      PMF.dTV (X.map fun N => (N : ZMod (2 ^ n'))) (unifOddMod n') ≤ K * (2 : ℝ) ^ (-(n' : ℝ)) →
      (X.map fun N => pre (valVec N n) n).expect (Set.indicator {L | n' ≤ L} 1)
        ≤ C * (2 : ℝ) ^ (-c * (n : ℝ)) := by
  obtain ⟨cd, Cd, hcd, hCd, hdist⟩ := valuation_dist c₀ K hc₀ hK
  obtain ⟨ct, hct, Ct, hCt, htail⟩ := geomHalf_tail_bound
  let d := ct * c₀
  let cg := finalDecay d / Real.log 2
  let c := min cd cg
  let C := Cd + 2 * Ct
  have hd : 0 < d := mul_pos hct hc₀
  have hcg : 0 < cg := div_pos (finalDecay_pos hd) (Real.log_pos one_lt_two)
  have hc : 0 < c := lt_min hcd hcg
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨c, C, hc, hC, ?_⟩
  intro n n' X hsize hodd hmod
  let P := X.map fun N => valVec N n
  let Q := geomHalf.iid n
  let E : Set (Fin n → Nat) := {a | n' ≤ pre a n}
  let T : ℝ := Q.expect (Set.indicator E 1)
  have htarget :
      (X.map fun N => pre (valVec N n) n).expect (Set.indicator {L | n' ≤ L} 1) =
        P.expect (Set.indicator E 1) := by
    have hleft := PMF.expect_map_of_nonneg X (fun N => pre (valVec N n) n)
      (Set.indicator {L : Nat | n' ≤ L} 1)
      (fun L => Set.indicator_nonneg (fun _ _ => zero_le_one) L)
    have hright := PMF.expect_map_of_nonneg X (fun N => valVec N n)
      (Set.indicator E 1) (fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) a)
    rw [hleft, hright]
    apply tsum_congr
    intro N
    congr 1
  have hqevent : T =
      ∑' a : Fin n → Nat, if n' ≤ pre a n then (Q a).toReal else 0 := by
    dsimp only [T, E]
    unfold PMF.expect
    apply tsum_congr
    intro a
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, mul_ite, mul_one, mul_zero]
  have hdistPQ : P.dTV Q ≤ Cd * (2 : ℝ) ^ (-cd * (n : ℝ)) :=
    hdist n n' X hsize hodd hmod
  have hevent := PMF.abs_expect_indicator_sub_le_dTV P Q E
  have hTnonneg : 0 ≤ T := by
    dsimp only [T]
    exact tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hXevent : P.expect (Set.indicator E 1) ≤ T + P.dTV Q := by
    dsimp only [T] at hevent ⊢
    linarith [le_abs_self (P.expect (Set.indicator E 1) - Q.expect (Set.indicator E 1))]
  have hoverG : T ≤ Ct * Gweight (1 + n) (ct * (c₀ * n)) := by
    rw [hqevent]
    exact geomHalf_overflow_le_Gweight c₀ ct Ct hc₀ htail n n' hsize
  have harg : ct * (c₀ * (n : ℝ)) = d * n := by dsimp only [d]; ring
  have hoverExp : T ≤ 2 * Ct * Real.exp (-linearDecay d * n) := by
    calc
      T ≤ Ct * Gweight (1 + n) (ct * (c₀ * n)) := hoverG
      _ = Ct * Gweight (1 + n) (d * n) := by rw [harg]
      _ ≤ Ct * (2 * Real.exp (-linearDecay d * n)) := by
        gcongr
        exact Gweight_linear_le d hd n
      _ = 2 * Ct * Real.exp (-linearDecay d * n) := by ring
  have hgeom := exp_linearDecay_le_two_rpow d n
  have hcdmono : (2 : ℝ) ^ (-cd * (n : ℝ)) ≤ (2 : ℝ) ^ (-c * (n : ℝ)) :=
    two_rpow_decay_mono (min_le_left cd cg) n
  have hcgmono : (2 : ℝ) ^ (-cg * (n : ℝ)) ≤ (2 : ℝ) ^ (-c * (n : ℝ)) :=
    two_rpow_decay_mono (min_le_right cd cg) n
  have hgeom' : Real.exp (-linearDecay d * n) ≤ (2 : ℝ) ^ (-c * (n : ℝ)) :=
    hgeom.trans (by simpa only [cg] using hcgmono)
  rw [htarget]
  have hpow0 : 0 ≤ (2 : ℝ) ^ (-c * (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  calc
    P.expect (Set.indicator E 1) ≤ T + P.dTV Q := hXevent
    _ ≤ 2 * Ct * Real.exp (-linearDecay d * n) +
        Cd * (2 : ℝ) ^ (-cd * (n : ℝ)) := add_le_add hoverExp hdistPQ
    _ ≤ 2 * Ct * (2 : ℝ) ^ (-c * (n : ℝ)) +
        Cd * (2 : ℝ) ^ (-c * (n : ℝ)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hgeom' (mul_nonneg (by norm_num) hCt.le)
      · exact mul_le_mul_of_nonneg_left hcdmono hCd.le
    _ = C * (2 : ℝ) ^ (-c * (n : ℝ)) := by dsimp only [C]; ring

end TaoCollatz
