import TaoCollatz.Sec7.Setup
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# §7.2: the black set is a union of separated triangles (node X3)

Paper anchors: Tao 2019 §7.2, (7.11)–(7.15), Lemma 7.4.

`triangle` is the upper-left corner triangle (7.11) in the `(j,l)` lattice under the
`(log 9, log 2)` metric. `black_structure` (Lemma 7.4) — statement only (`sorry`).
-/

open scoped Real

namespace TaoCollatz

/-! ### θ-identity exactness and the weakly-black claims (paper p.38)

The recursions (7.13)/(7.14) hold mod ℤ (`θq_succ_j`/`θq_pred_l`). When the phase is
small enough that no wraparound can occur, they hold *exactly* in ℚ; the paper's
weakly-black claims (i)–(iii) are corollaries. These drive every case of Lemma 7.4. -/

/-- The phase is a signed fractional part, so `|θ| ≤ 1/2`. -/
theorem θq_abs_le_half (n ξ : ℕ) (j : ℕ) (l : ℤ) : |θq n ξ j l| ≤ 1 / 2 :=
  abs_sub_round _

/-- Exact form of (7.13): if `|θ(j,l)| < 1/18` there is no wraparound, so
`θ(j+1,l) = 9·θ(j,l)` exactly in ℚ. -/
theorem θq_succ_j_exact (n ξ : ℕ) (j : ℕ) (l : ℤ) (h : |θq n ξ j l| < 1 / 18) :
    θq n ξ (j + 1) l = 9 * θq n ξ j l := by
  obtain ⟨k, hk⟩ := θq_succ_j n ξ j l
  have h9 : |9 * θq n ξ j l| < 1 / 2 := by
    rw [abs_mul]; norm_num; linarith [abs_nonneg (θq n ξ j l)]
  have hk1 : |(k : ℚ)| < 1 := by
    have h1 : (k : ℚ) = θq n ξ (j + 1) l - 9 * θq n ξ j l := by linarith [hk]
    calc |(k : ℚ)| ≤ |θq n ξ (j + 1) l| + |9 * θq n ξ j l| := by
          rw [h1]; exact abs_sub _ _
      _ < 1 := by linarith [θq_abs_le_half n ξ (j + 1) l]
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hk1)
  rw [hk, hk0]; push_cast; ring

/-- Exact form of (7.14): if `|θ(j,l)| < 1/4` there is no wraparound, so
`θ(j,l-1) = 2·θ(j,l)` exactly in ℚ. -/
theorem θq_pred_l_exact (n ξ : ℕ) (j : ℕ) (l : ℤ) (h : |θq n ξ j l| < 1 / 4) :
    θq n ξ j (l - 1) = 2 * θq n ξ j l := by
  obtain ⟨k, hk⟩ := θq_pred_l n ξ j l
  have hk1 : |(k : ℚ)| < 1 := by
    have h1 : (k : ℚ) = θq n ξ j (l - 1) - 2 * θq n ξ j l := by linarith [hk]
    have h2 : |2 * θq n ξ j l| < 1 / 2 := by
      rw [abs_mul]; norm_num; linarith [abs_nonneg (θq n ξ j l)]
    calc |(k : ℚ)| ≤ |θq n ξ j (l - 1)| + |2 * θq n ξ j l| := by
          rw [h1]; exact abs_sub _ _
      _ < 1 := by linarith [θq_abs_le_half n ξ j (l - 1)]
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hk1)
  rw [hk, hk0]; push_cast; ring

/-- A point is *weakly black* (paper p.38) if `|θ(j,l)| ≤ 1/100`. -/
def weaklyBlack (n ξ : ℕ) (j : ℕ) (l : ℤ) : Prop := |θq n ξ j l| ≤ 1 / 100

/-- Black points are weakly black (`ε = 1/10⁴ ≤ 1/100`). -/
theorem weaklyBlack_of_black {n ξ : ℕ} {j : ℕ} {l : ℤ} (h : black n ξ j l) :
    weaklyBlack n ξ j l := by
  unfold black epsBW at h; unfold weaklyBlack; linarith

/-- **Claim (i), j-form**: weakly black at `(j,l)` and black at `(j+1,l)` force black
at `(j,l)`. -/
theorem black_of_weaklyBlack_succ_j {n ξ : ℕ} {j : ℕ} {l : ℤ}
    (hw : weaklyBlack n ξ j l) (hb : black n ξ (j + 1) l) : black n ξ j l := by
  have he := θq_succ_j_exact n ξ j l (lt_of_le_of_lt hw (by norm_num))
  unfold black at *; unfold epsBW at *
  rw [he, abs_mul] at hb
  rw [abs_of_nonneg (by norm_num : (0:ℚ) ≤ 9)] at hb
  linarith [abs_nonneg (θq n ξ j l)]

/-- **Claim (i), l-form**: weakly black at `(j,l)` and black at `(j,l-1)` force black
at `(j,l)`. -/
theorem black_of_weaklyBlack_pred_l {n ξ : ℕ} {j : ℕ} {l : ℤ}
    (hw : weaklyBlack n ξ j l) (hb : black n ξ j (l - 1)) : black n ξ j l := by
  have he := θq_pred_l_exact n ξ j l (lt_of_le_of_lt hw (by norm_num))
  unfold black at *; unfold epsBW at *
  rw [he, abs_mul] at hb
  rw [abs_of_nonneg (by norm_num : (0:ℚ) ≤ 2)] at hb
  linarith [abs_nonneg (θq n ξ j l)]

/-- **Claim (ii)**: if `(j+1,l)` and `(j,l-1)` are weakly black, so is `(j,l)`.
(Via the exact identity `θ(j,l) = θ(j+1,l) - 4·θ(j,l-1) - K`, `K ∈ ℤ` forced to `0`.) -/
theorem weaklyBlack_of_succ_j_pred_l {n ξ : ℕ} {j : ℕ} {l : ℤ}
    (h1 : weaklyBlack n ξ (j + 1) l) (h2 : weaklyBlack n ξ j (l - 1)) :
    weaklyBlack n ξ j l := by
  unfold weaklyBlack at *
  obtain ⟨k₁, hk₁⟩ := θq_succ_j n ξ j l
  obtain ⟨k₂, hk₂⟩ := θq_pred_l n ξ j l
  -- θ(j,l) + (k₁ - 4k₂) = θ(j+1,l) - 4·θ(j,l-1), which is ≤ 5/100 in absolute value
  have hcomb : θq n ξ j l + ((k₁ : ℚ) - 4 * k₂)
      = θq n ξ (j + 1) l - 4 * θq n ξ j (l - 1) := by
    rw [hk₁, hk₂]; ring
  have hsmall : |θq n ξ (j + 1) l - 4 * θq n ξ j (l - 1)| ≤ 5 / 100 := by
    calc |θq n ξ (j + 1) l - 4 * θq n ξ j (l - 1)|
        ≤ |θq n ξ (j + 1) l| + |4 * θq n ξ j (l - 1)| := abs_sub _ _
      _ ≤ 1 / 100 + 4 * (1 / 100) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℚ) ≤ 4)]
          have := abs_nonneg (θq n ξ j (l - 1))
          gcongr
      _ = 5 / 100 := by norm_num
  have hK : (k₁ : ℚ) - 4 * k₂ = 0 := by
    have habs : |(k₁ : ℚ) - 4 * k₂| < 1 := by
      have h5 : |θq n ξ j l + ((k₁ : ℚ) - 4 * k₂)| ≤ 5 / 100 := hcomb ▸ hsmall
      calc |(k₁ : ℚ) - 4 * k₂|
          = |θq n ξ j l + ((k₁ : ℚ) - 4 * k₂) - θq n ξ j l| := by ring_nf
        _ ≤ |θq n ξ j l + ((k₁ : ℚ) - 4 * k₂)| + |θq n ξ j l| := abs_sub _ _
        _ < 1 := by linarith [θq_abs_le_half n ξ j l]
    have : ((k₁ - 4 * k₂ : ℤ) : ℚ) = (k₁ : ℚ) - 4 * k₂ := by push_cast; ring
    have hz : k₁ - 4 * k₂ = 0 :=
      Int.abs_lt_one_iff.mp (by exact_mod_cast (this ▸ habs : |((k₁ - 4 * k₂ : ℤ) : ℚ)| < 1))
    rw [← this, hz]; norm_num
  -- so |θ(j,l)| ≤ 5/100; then (7.13) has no wraparound and |θ(j,l)| = |θ(j+1,l)|/9
  have h5 : |θq n ξ j l| ≤ 5 / 100 := by
    have := hcomb; rw [hK, add_zero] at this; rw [this]; exact hsmall
  have he := θq_succ_j_exact n ξ j l (lt_of_le_of_lt h5 (by norm_num))
  rw [he, abs_mul, abs_of_nonneg (by norm_num : (0:ℚ) ≤ 9)] at h1
  linarith

/-- **Claim (iii)** (stated at `(j+1,l)` to keep `j : ℕ`): if `(j,l)` and `(j+1,l-1)`
are weakly black, so is `(j+1,l)`. -/
theorem weaklyBlack_of_pred_j_pred_l {n ξ : ℕ} {j : ℕ} {l : ℤ}
    (h1 : weaklyBlack n ξ j l) (h2 : weaklyBlack n ξ (j + 1) (l - 1)) :
    weaklyBlack n ξ (j + 1) l := by
  unfold weaklyBlack at *
  -- from (7.13) exactly: θ(j+1,l) = 9θ(j,l), so |θ(j+1,l)| ≤ 9/100
  have he := θq_succ_j_exact n ξ j l (lt_of_le_of_lt h1 (by norm_num))
  have h9 : |θq n ξ (j + 1) l| ≤ 9 / 100 := by
    rw [he, abs_mul, abs_of_nonneg (by norm_num : (0:ℚ) ≤ 9)]; linarith
  -- then (7.14) exactly at (j+1,l): θ(j+1,l-1) = 2θ(j+1,l), so |θ(j+1,l)| ≤ 1/200
  have he2 := θq_pred_l_exact n ξ (j + 1) l (lt_of_le_of_lt h9 (by norm_num))
  rw [he2, abs_mul, abs_of_nonneg (by norm_num : (0:ℚ) ≤ 2)] at h2
  linarith

/-! ### (7.16): the phase lower bound and strip confinement

For `ξ` coprime to 3 and a point with `2j+1 ≤ n` (true of every strip point), multiplying
the phase argument by `3^{n-2j-1}` lands on `±1/3 mod ℤ`, so `|θ| ≥ 3^{-(n-2j)}`. Hence
black points (`|θ| ≤ ε = 10⁻⁴`) satisfy `n - 2j ≥ 9`. -/

/-- `sfrac` is unchanged by adding an integer. -/
theorem sfrac_add_int (x : ℚ) (m : ℤ) : sfrac (x + m) = sfrac x := by
  unfold sfrac; rw [round_add_intCast]; push_cast; ring

/-- `|sfrac x| ≤ |x|` (rounding can only move a point closer to `ℤ` than `0` does). -/
theorem abs_sfrac_le (x : ℚ) : |sfrac x| ≤ |x| := by
  rcases le_or_gt (1 / 2) |x| with h | h
  · exact le_trans (abs_sub_round x) h
  · have h' : |x| < 1 / 2 := h
    rw [abs_lt] at h'
    have hr : round x = 0 := by
      rw [round_eq]
      refine Int.floor_eq_zero_iff.mpr ⟨by linarith [h'.1], by linarith [h'.2]⟩
    unfold sfrac; rw [hr]; simp

/-- Absorbing a `ZMod`-external integer factor `ξ` into the `ZMod` element does not
change the phase. -/
theorem sfrac_phase_absorb (n ξ : ℕ) (X : ZMod (3 ^ n)) :
    sfrac ((ξ * X.val : ℚ) / 3 ^ n)
      = sfrac (((((ξ : ZMod (3 ^ n)) * X).val : ℕ) : ℚ) / 3 ^ n) := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  set Y := (ξ : ZMod (3 ^ n)) * X with hY
  have hdvd : ((3 : ℤ) ^ n) ∣ ((ξ * X.val : ℤ) - (Y.val : ℤ)) := by
    have hz : (((ξ * X.val : ℤ) - (Y.val : ℤ) : ℤ) : ZMod (3 ^ n)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hY]
      exact sub_self _
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (3 ^ n)).mp hz
    exact_mod_cast hd
  obtain ⟨t, ht⟩ := hdvd
  have h3 : (3 : ℚ) ^ n ≠ 0 := by positivity
  have hval : ((ξ * X.val : ℚ)) / 3 ^ n = ((Y.val : ℚ)) / 3 ^ n + t := by
    have : ((ξ * X.val : ℚ)) = (Y.val : ℚ) + 3 ^ n * t := by
      have := ht; push_cast
      have h2 : ((ξ * X.val : ℤ) : ℚ) = ((Y.val : ℤ) : ℚ) + ((3 : ℤ) ^ n * t : ℤ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (by linarith [ht] : (ξ * X.val : ℤ) = Y.val + 3 ^ n * t)
      push_cast at h2; linarith [h2]
    rw [this]; field_simp
  rw [hval, sfrac_add_int]

/-- **(7.16) core — phase lower bound.** For `ξ` coprime to 3 and `2j+1 ≤ n`,
`3^{-(n-2j)} ≤ |θ(j,l)|` for every `l`. -/
theorem θq_lower_bound (n ξ : ℕ) (hξ : ¬ 3 ∣ ξ) (j : ℕ) (l : ℤ) (h2j : 2 * j + 1 ≤ n) :
    (1 : ℚ) / 3 ^ (n - 2 * j) ≤ |θq n ξ j l| := by
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  set u : ZMod (3 ^ n) := (↑((u2 n) ^ (1 - l)) : ZMod (3 ^ n)) with hu
  set X : ZMod (3 ^ n) := (3 : ZMod (3 ^ n)) ^ (2 * j) * u with hX
  set X' : ZMod (3 ^ n) := (3 : ZMod (3 ^ n)) ^ (n - 1) * u with hX'
  -- X' = 3^{n-2j-1} · X
  have hXX' : X' = ((3 ^ (n - 2 * j - 1) : ℤ) : ZMod (3 ^ n)) * X := by
    rw [hX', hX]
    push_cast
    rw [show n - 1 = (n - 2 * j - 1) + 2 * j from by omega, pow_add]
    ring
  obtain ⟨m, hm⟩ := argRel n ξ (3 ^ (n - 2 * j - 1)) X X' hXX'
  obtain ⟨k, hk⟩ := sfrac_scale_of (3 ^ (n - 2 * j - 1)) _ _ m hm
  -- the scaled phase is exactly ±1/3
  have hthird : |sfrac ((ξ * X'.val : ℚ) / 3 ^ n)| = 1 / 3 := by
    rw [sfrac_phase_absorb]
    set z : ZMod (3 ^ n) := (ξ : ZMod (3 ^ n)) * u with hz
    have hYz : (ξ : ZMod (3 ^ n)) * X' = (3 : ZMod (3 ^ n)) ^ (n - 1) * z := by
      rw [hX', hz]; ring
    -- z is a unit, so 3 ∤ z.val
    have hcop3 : Nat.Coprime ξ 3 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hξ)
    have hzu : IsUnit z := by
      refine IsUnit.mul ?_ ((u2 n ^ (1 - l)).isUnit)
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.pow_right n hcop3
    obtain ⟨zu, hzu_eq⟩ := hzu
    have hzcop : Nat.Coprime z.val (3 ^ n) := by
      rw [← hzu_eq]; exact ZMod.val_coe_unit_coprime zu
    have hn1 : 1 ≤ n := by omega
    have h3z : ¬ 3 ∣ z.val := by
      intro hdvd
      have h3n : (3 : ℕ) ∣ 3 ^ n := dvd_pow_self 3 (by omega)
      have h31 := Nat.dvd_gcd hdvd h3n
      rw [Nat.Coprime] at hzcop
      rw [hzcop] at h31
      exact absurd (Nat.dvd_one.mp h31) (by norm_num)
    set w₀ : ℕ := z.val % 3 with hw₀
    have hw₀13 : w₀ = 1 ∨ w₀ = 2 := by
      have : w₀ < 3 := Nat.mod_lt _ (by norm_num)
      have : w₀ ≠ 0 := fun h => h3z (Nat.dvd_of_mod_eq_zero h)
      omega
    -- (ξ·X') = (3^{n-1}·w₀ : ℕ) in ZMod (3^n)
    have hzw : (3 : ZMod (3 ^ n)) ^ (n - 1) * z = ((3 ^ (n - 1) * w₀ : ℕ) : ZMod (3 ^ n)) := by
      have hdz : (3 : ℤ) ∣ ((z.val : ℤ) - w₀) := by
        have : z.val - w₀ = 3 * (z.val / 3) := by omega
        omega
      obtain ⟨t, ht⟩ := hdz
      have hzcast : z = ((z.val : ℕ) : ZMod (3 ^ n)) := (ZMod.natCast_zmod_val z).symm
      have hz3 : z = ((w₀ : ℕ) : ZMod (3 ^ n)) + 3 * ((t : ℤ) : ZMod (3 ^ n)) := by
        rw [hzcast]
        have : ((z.val : ℤ) : ZMod (3 ^ n)) = ((w₀ : ℤ) : ZMod (3 ^ n)) + 3 * (t : ZMod (3 ^ n)) := by
          have : (z.val : ℤ) = w₀ + 3 * t := by linarith [ht]
          rw [this]; push_cast; ring
        push_cast at this ⊢
        exact_mod_cast this
      rw [hz3]
      have h3n1 : (3 : ZMod (3 ^ n)) ^ (n - 1) * 3 = 0 := by
        have he : (3 : ZMod (3 ^ n)) ^ (n - 1) * 3 = (3 : ZMod (3 ^ n)) ^ n := by
          rw [← pow_succ]; congr 1; omega
        rw [he]
        have hns : ((3 ^ n : ℕ) : ZMod (3 ^ n)) = 0 := ZMod.natCast_self _
        push_cast at hns; exact_mod_cast hns
      push_cast
      have hexpand : (3 : ZMod (3 ^ n)) ^ (n - 1) * ((w₀ : ZMod (3 ^ n)) + 3 * (t : ZMod (3 ^ n)))
          = (3 : ZMod (3 ^ n)) ^ (n - 1) * (w₀ : ZMod (3 ^ n))
            + ((3 : ZMod (3 ^ n)) ^ (n - 1) * 3) * (t : ZMod (3 ^ n)) := by ring
      rw [hexpand, h3n1, zero_mul, add_zero]
    have hval : ((ξ : ZMod (3 ^ n)) * X').val = 3 ^ (n - 1) * w₀ := by
      rw [hYz, hzw]
      apply ZMod.val_natCast_of_lt
      have hw2 : w₀ ≤ 2 := by omega
      calc 3 ^ (n - 1) * w₀ ≤ 3 ^ (n - 1) * 2 := by
            exact Nat.mul_le_mul_left _ hw2
        _ < 3 ^ (n - 1) * 3 := by
            have : (0:ℕ) < 3 ^ (n - 1) := Nat.pow_pos (by norm_num)
            omega
        _ = 3 ^ n := by rw [← pow_succ]; congr 1; omega
    rw [hval]
    have hq : ((3 ^ (n - 1) * w₀ : ℕ) : ℚ) / 3 ^ n = (w₀ : ℚ) / 3 := by
      have hpow : (3 : ℚ) ^ n = 3 ^ (n - 1) * 3 := by
        rw [← pow_succ]; congr 1; omega
      push_cast
      rw [hpow]
      have h30 : (3 : ℚ) ^ (n - 1) ≠ 0 := by positivity
      field_simp
    rw [hq]
    rcases hw₀13 with h | h <;> rw [h] <;> unfold sfrac <;> push_cast
    · have hrd : round ((1 : ℚ) / 3) = 0 := by rw [round_eq]; norm_num
      rw [hrd]; norm_num
    · have hrd : round ((2 : ℚ) / 3) = 1 := by rw [round_eq]; norm_num
      rw [hrd]; norm_num
  -- assemble: |c·θ + k| = 1/3 with integer k forces |θ| ≥ 1/(3c)
  have hθeq : sfrac ((ξ * X.val : ℚ) / 3 ^ n) = θq n ξ j l := by
    rw [hX]; rfl
  have hcast : ((3 ^ (n - 2 * j - 1) : ℤ) : ℚ) = (3 : ℚ) ^ (n - 2 * j - 1) := by
    push_cast; ring
  rw [hθeq, hcast] at hk
  rw [hk] at hthird
  set θ := θq n ξ j l with hθ
  set c : ℚ := (3 : ℚ) ^ (n - 2 * j - 1) with hc
  have hcpos : (0 : ℚ) < c := by rw [hc]; positivity
  have hceq : 3 * c = 3 ^ (n - 2 * j) := by
    rw [hc, ← pow_succ']
    congr 1; omega
  by_contra hcon
  push_neg at hcon
  have hθc : |c * θ| < 1 / 3 := by
    rw [abs_mul, abs_of_pos hcpos]
    calc c * |θ| < c * (1 / 3 ^ (n - 2 * j)) :=
          mul_lt_mul_of_pos_left hcon hcpos
      _ = 1 / 3 := by
          rw [show (3:ℚ) ^ (n - 2 * j) = 3 * c from hceq.symm]
          field_simp
  rcases eq_or_ne k 0 with hk0 | hk0
  · rw [hk0] at hthird
    simp only [Int.cast_zero, add_zero] at hthird
    linarith [hθc]
  · have hk1 : (1 : ℚ) ≤ |(k : ℚ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      exact_mod_cast this
    have habs : |(k : ℚ)| ≤ |c * θ + (k : ℚ)| + |c * θ| := by
      calc |(k : ℚ)| = |(c * θ + (k : ℚ)) - c * θ| := by congr 1; ring
        _ ≤ |c * θ + (k : ℚ)| + |c * θ| := abs_sub _ _
    linarith [hθc, hk1, habs, hthird.le, hthird.ge]

/-- **(7.16) strip confinement, discrete form**: a black point with `2j+1 ≤ n`
(every strip point) satisfies `n - 2j ≥ 9` (since `3⁸ < 10⁴ = 1/ε ≤ 3^{n-2j}`). -/
theorem black_nine_le (n ξ : ℕ) (hξ : ¬ 3 ∣ ξ) {j : ℕ} {l : ℤ} (h2j : 2 * j + 1 ≤ n)
    (hb : black n ξ j l) : 9 ≤ n - 2 * j := by
  by_contra hcon
  push_neg at hcon
  have hle : |θq n ξ j l| ≤ epsBW := hb
  have hlb := θq_lower_bound n ξ hξ j l h2j
  have hpow : (3 : ℚ) ^ (n - 2 * j) ≤ 3 ^ 8 := by
    apply pow_le_pow_right₀ (by norm_num) (by omega)
  have h1 : (1 : ℚ) / 3 ^ 8 ≤ 1 / 3 ^ (n - 2 * j) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
  unfold epsBW at hle
  have : (1 : ℚ) / 3 ^ 8 ≤ 1 / 10 ^ 4 := le_trans h1 (le_trans hlb hle)
  norm_num at this

/-- The corner triangle with apex `(j₀, l₀)` and size `s` (paper (7.11)): points to the
lower-right of the apex within `(log 9)·Δj + (log 2)·Δl ≤ s`. -/
def triangle (j₀ : ℕ) (l₀ : ℤ) (s : ℝ) : Set (ℕ × ℤ) :=
  {p | j₀ ≤ p.1 ∧ p.2 ≤ l₀ ∧
    ((p.1 : ℝ) - j₀) * Real.log 9 + ((l₀ : ℝ) - p.2) * Real.log 2 ≤ s}

-- RATIFY-5 (resolved 2026-07-10 against paper pp.36–41 + harness check 8): the paper's
-- separation is between the triangle POINT SETS ("using the Euclidean metric on
-- [n/2] × ℤ ⊂ ℝ²"), not merely between top-left corners — Case 2's white-exit ring
-- (7.50)/(7.51) and Lemma 7.10's Σ-counting both consume set-separation. Statement
-- fixed accordingly (an earlier draft only separated corners). Separation is stated
-- squared to avoid `Real.sqrt`; disjointness of the union follows from set-separation
-- since `(1/10)·log(1/ε) > 0`. The union equality is parenthesized explicitly (an
-- un-parenthesized `= ⋃ t ∈ T, S t ∧ P` risks the `∧` parsing into the `⋃` body).
-- Numerically validated (exact ℚ arithmetic, l*/j* construction): check_blueprint
-- check 8 at (n,ξ,ε) = (30,7,9e-3), (26,101,1/101), (30,1,1e-4) — incl. giant
-- triangles of size ≈ n·log 3 from tiny |θ| corners.
/-- **Lemma 7.4.** For `ξ` not divisible by 3, the black set (within the strip
`j+1 ≤ n/2`) is a union of corner triangles whose point sets are pairwise
Euclidean-separated by `≥ (1/10)·log(1/ε)` and confined to
`j+1 ≤ n/2 - (1/10)·log(1/ε)`. -/
theorem black_structure (n ξ : ℕ) (hξ : ¬ 3 ∣ ξ) (hn : 1 ≤ n) :
    ∃ T : Set (ℕ × ℤ × ℝ),
      (∀ t ∈ T, 0 ≤ t.2.2) ∧
      ({p : ℕ × ℤ | p.1 + 1 ≤ n / 2 ∧ black n ξ p.1 p.2}
        = ⋃ t ∈ T, triangle t.1 t.2.1 t.2.2) ∧
      (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
        ∀ p ∈ triangle t.1 t.2.1 t.2.2, ∀ p' ∈ triangle t'.1 t'.2.1 t'.2.2,
        ((1 / 10 : ℝ) * Real.log (1 / (epsBW : ℝ))) ^ 2
          ≤ ((p.1 : ℝ) - p'.1) ^ 2 + ((p.2 : ℝ) - p'.2) ^ 2) ∧
      (∀ t ∈ T, ∀ p ∈ triangle t.1 t.2.1 t.2.2,
        (p.1 : ℝ) + 1 ≤ (n : ℝ) / 2 - (1 / 10 : ℝ) * Real.log (1 / (epsBW : ℝ))) := by
  sorry

end TaoCollatz
