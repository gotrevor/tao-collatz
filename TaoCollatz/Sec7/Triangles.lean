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

/-! ### (7.18): the exact scaling identity down-right of a point

Iterating the exact recursions: as long as the final scaled value stays below `1/2`,
no intermediate step wraps around, so `θ(j+a, l-b) = 9^a·2^b·θ(j,l)` exactly — the
equality case of (7.18), the triangle-fibre engine of Lemma 7.4 (numerically validated,
harness check 8 claim (2)). -/

/-- Iterated (7.13): if `9^a·|θ(j,l)| < 1/2` then `θ(j+a,l) = 9^a·θ(j,l)` exactly. -/
theorem θq_iterate_j (n ξ : ℕ) (j : ℕ) (l : ℤ) (a : ℕ)
    (h : (9 : ℚ) ^ a * |θq n ξ j l| < 1 / 2) :
    θq n ξ (j + a) l = 9 ^ a * θq n ξ j l := by
  induction a with
  | zero => simp
  | succ a IH =>
    have hmono : (9:ℚ) ^ a * |θq n ξ j l| ≤ 9 ^ (a + 1) * |θq n ξ j l| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply pow_le_pow_right₀ <;> norm_num
    have hIH := IH (lt_of_le_of_lt hmono h)
    have habs : |θq n ξ (j + a) l| = 9 ^ a * |θq n ξ j l| := by
      rw [hIH, abs_mul, abs_of_nonneg (by positivity : (0:ℚ) ≤ 9 ^ a)]
    have hsmall : |θq n ξ (j + a) l| < 1 / 18 := by
      rw [habs]
      nlinarith [pow_pos (show (0:ℚ) < 9 by norm_num) a, abs_nonneg (θq n ξ j l),
        h, pow_succ (9:ℚ) a]
    have hstep := θq_succ_j_exact n ξ (j + a) l hsmall
    have : j + (a + 1) = (j + a) + 1 := by omega
    rw [this, hstep, hIH]
    ring

/-- Iterated (7.14): if `2^b·|θ(j,l)| < 1/2` then `θ(j,l-b) = 2^b·θ(j,l)` exactly. -/
theorem θq_iterate_l (n ξ : ℕ) (j : ℕ) (l : ℤ) (b : ℕ)
    (h : (2 : ℚ) ^ b * |θq n ξ j l| < 1 / 2) :
    θq n ξ j (l - b) = 2 ^ b * θq n ξ j l := by
  induction b with
  | zero => simp
  | succ b IH =>
    have hmono : (2:ℚ) ^ b * |θq n ξ j l| ≤ 2 ^ (b + 1) * |θq n ξ j l| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply pow_le_pow_right₀ <;> norm_num
    have hIH := IH (lt_of_le_of_lt hmono h)
    have habs : |θq n ξ j (l - b)| = 2 ^ b * |θq n ξ j l| := by
      rw [hIH, abs_mul, abs_of_nonneg (by positivity : (0:ℚ) ≤ 2 ^ b)]
    have hsmall : |θq n ξ j (l - b)| < 1 / 4 := by
      rw [habs]
      nlinarith [pow_pos (show (0:ℚ) < 2 by norm_num) b, abs_nonneg (θq n ξ j l),
        h, pow_succ (2:ℚ) b]
    have hstep := θq_pred_l_exact n ξ j (l - b) hsmall
    have hcast : l - ((b : ℤ) + 1) = (l - b) - 1 := by ring
    rw [show ((b + 1 : ℕ) : ℤ) = (b : ℤ) + 1 from by push_cast; ring, hcast, hstep, hIH]
    ring

/-- **(7.18), equality form.** If `9^a·2^b·|θ(j,l)| < 1/2` then
`θ(j+a, l-b) = 9^a·2^b·θ(j,l)` exactly. -/
theorem θq_iterate_exact (n ξ : ℕ) (j : ℕ) (l : ℤ) (a b : ℕ)
    (h : (9 : ℚ) ^ a * 2 ^ b * |θq n ξ j l| < 1 / 2) :
    θq n ξ (j + a) (l - b) = 9 ^ a * 2 ^ b * θq n ξ j l := by
  have h2b : (1:ℚ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have h9a : (0:ℚ) < 9 ^ a := by positivity
  have hja : (9:ℚ) ^ a * |θq n ξ j l| < 1 / 2 := by
    nlinarith [abs_nonneg (θq n ξ j l)]
  have h1 := θq_iterate_j n ξ j l a hja
  have habs : |θq n ξ (j + a) l| = 9 ^ a * |θq n ξ j l| := by
    rw [h1, abs_mul, abs_of_nonneg (by positivity : (0:ℚ) ≤ 9 ^ a)]
  have h2 : (2:ℚ) ^ b * |θq n ξ (j + a) l| < 1 / 2 := by
    rw [habs]
    calc (2:ℚ) ^ b * (9 ^ a * |θq n ξ j l|) = 9 ^ a * 2 ^ b * |θq n ξ j l| := by ring
      _ < 1 / 2 := h
  have h3 := θq_iterate_l n ξ (j + a) l b h2
  rw [h3, h1]
  ring

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

/-- `sfrac` lands in `[-1/2, 1/2)`. (With `round q = ⌊q + 1/2⌋` the endpoint convention
is the mirror of the paper's `(-1/2, 1/2]`; only `|sfrac|` is ever used, and our phase
denominators `3^n` are odd so `±1/2` never occurs.) -/
theorem sfrac_mem (x : ℚ) : -(1 / 2) ≤ sfrac x ∧ sfrac x < 1 / 2 := by
  unfold sfrac
  rw [round_eq]
  constructor
  · linarith [Int.floor_le (x + 1 / 2)]
  · linarith [Int.lt_floor_add_one (x + 1 / 2)]

/-- `sfrac` fixes its own range: `sfrac x = x` for `x ∈ [-1/2, 1/2)`. -/
theorem sfrac_eq_self {x : ℚ} (h1 : -(1 / 2) ≤ x) (h2 : x < 1 / 2) : sfrac x = x := by
  unfold sfrac
  rw [round_eq]
  have : ⌊x + 1 / 2⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
  rw [this]; simp

/-- `sfrac` is idempotent. -/
theorem sfrac_idem (x : ℚ) : sfrac (sfrac x) = sfrac x :=
  sfrac_eq_self (sfrac_mem x).1 (sfrac_mem x).2

/-- **(7.18), inequality form, single j-step**: `|θ(j+1,l)| ≤ 9·|θ(j,l)|`
(unconditional). -/
theorem θq_succ_j_abs_le (n ξ : ℕ) (j : ℕ) (l : ℤ) :
    |θq n ξ (j + 1) l| ≤ 9 * |θq n ξ j l| := by
  obtain ⟨k, hk⟩ := θq_succ_j n ξ j l
  have hidem : θq n ξ (j + 1) l = sfrac (θq n ξ (j + 1) l) := by
    unfold θq; rw [sfrac_idem]
  calc |θq n ξ (j + 1) l| = |sfrac (θq n ξ (j + 1) l)| := by rw [← hidem]
    _ = |sfrac (9 * θq n ξ j l)| := by rw [hk, sfrac_add_int]
    _ ≤ |9 * θq n ξ j l| := abs_sfrac_le _
    _ = 9 * |θq n ξ j l| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℚ) ≤ 9)]

/-- **(7.18), inequality form, single l-step**: `|θ(j,l-1)| ≤ 2·|θ(j,l)|`
(unconditional). -/
theorem θq_pred_l_abs_le (n ξ : ℕ) (j : ℕ) (l : ℤ) :
    |θq n ξ j (l - 1)| ≤ 2 * |θq n ξ j l| := by
  obtain ⟨k, hk⟩ := θq_pred_l n ξ j l
  have hidem : θq n ξ j (l - 1) = sfrac (θq n ξ j (l - 1)) := by
    unfold θq; rw [sfrac_idem]
  calc |θq n ξ j (l - 1)| = |sfrac (θq n ξ j (l - 1))| := by rw [← hidem]
    _ = |sfrac (2 * θq n ξ j l)| := by rw [hk, sfrac_add_int]
    _ ≤ |2 * θq n ξ j l| := abs_sfrac_le _
    _ = 2 * |θq n ξ j l| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℚ) ≤ 2)]

/-- **(7.18), inequality form, iterated**: `|θ(j+a, l-b)| ≤ 9^a·2^b·|θ(j,l)|`
(unconditional; the equality case below `1/2` is `θq_iterate_exact`). -/
theorem θq_iterate_abs_le (n ξ : ℕ) (j : ℕ) (l : ℤ) (a b : ℕ) :
    |θq n ξ (j + a) (l - b)| ≤ 9 ^ a * 2 ^ b * |θq n ξ j l| := by
  have hstep_j : ∀ a' : ℕ, |θq n ξ (j + a') l| ≤ 9 ^ a' * |θq n ξ j l| := by
    intro a'
    induction a' with
    | zero => simp
    | succ a' IH =>
      calc |θq n ξ (j + (a' + 1)) l| = |θq n ξ ((j + a') + 1) l| := by
            rw [show j + (a' + 1) = (j + a') + 1 from by omega]
        _ ≤ 9 * |θq n ξ (j + a') l| := θq_succ_j_abs_le n ξ (j + a') l
        _ ≤ 9 * (9 ^ a' * |θq n ξ j l|) := by linarith [IH]
        _ = 9 ^ (a' + 1) * |θq n ξ j l| := by ring
  induction b with
  | zero => simpa using hstep_j a
  | succ b IH =>
    calc |θq n ξ (j + a) (l - (b + 1 : ℕ))|
        = |θq n ξ (j + a) ((l - b) - 1)| := by
          rw [show l - ((b + 1 : ℕ) : ℤ) = (l - b) - 1 from by push_cast; ring]
      _ ≤ 2 * |θq n ξ (j + a) (l - b)| := θq_pred_l_abs_le n ξ (j + a) (l - b)
      _ ≤ 2 * (9 ^ a * 2 ^ b * |θq n ξ j l|) := by linarith [IH]
      _ = 9 ^ a * 2 ^ (b + 1) * |θq n ξ j l| := by ring

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

/-! ### Upward-run termination: `l*` exists

Along an upward black run, each black point above lets us halve exactly
(`θ(j,l) = 2^t·θ(j,l+t)`), and the (7.16) lower bound caps `2^t ≤ ε·3^{n-2j}` — so
black runs terminate and the paper's `l*(j,l)` is well defined (p.38). -/

/-- Along an upward black run the phase doubles downward exactly:
if `(j, l+i)` is black for `1 ≤ i ≤ t` then `θ(j,l) = 2^t·θ(j,l+t)`. -/
theorem θq_up_run (n ξ : ℕ) (j : ℕ) (l : ℤ) (t : ℕ)
    (hb : ∀ i : ℕ, 1 ≤ i → i ≤ t → black n ξ j (l + i)) :
    θq n ξ j l = 2 ^ t * θq n ξ j (l + t) := by
  induction t with
  | zero => simp
  | succ t IH =>
    have hbt : black n ξ j (l + (t + 1 : ℕ)) := hb (t + 1) (by omega) le_rfl
    have hsmall : |θq n ξ j (l + (t + 1 : ℕ))| < 1 / 4 := by
      have : |θq n ξ j (l + (t + 1 : ℕ))| ≤ epsBW := hbt
      unfold epsBW at this; linarith
    have hstep := θq_pred_l_exact n ξ j (l + (t + 1 : ℕ)) hsmall
    have hcast : l + ((t + 1 : ℕ) : ℤ) - 1 = l + t := by push_cast; ring
    rw [hcast] at hstep
    rw [IH (fun i h1 h2 => hb i h1 (by omega)), hstep]
    ring

/-- **Upward black runs are short**: if `(j, l+i)` is black for all `0 ≤ i ≤ t`
(with `3 ∤ ξ`, `2j+1 ≤ n`), then `2^t ≤ ε·3^{n-2j}`. Hence `l*` exists. -/
theorem black_run_le (n ξ : ℕ) (hξ : ¬ 3 ∣ ξ) {j : ℕ} {l : ℤ} {t : ℕ}
    (h2j : 2 * j + 1 ≤ n) (hb : ∀ i : ℕ, i ≤ t → black n ξ j (l + i)) :
    (2 : ℚ) ^ t ≤ epsBW * 3 ^ (n - 2 * j) := by
  have hrun := θq_up_run n ξ j l t (fun i h1 h2 => hb i h2)
  have hlow := θq_lower_bound n ξ hξ j (l + t) h2j
  have hb0' : black n ξ j l := by simpa using hb 0 (by omega)
  have hb0 : |θq n ξ j l| ≤ epsBW := hb0'
  have habs : |θq n ξ j l| = 2 ^ t * |θq n ξ j (l + t)| := by
    rw [hrun, abs_mul, abs_of_nonneg (by positivity : (0:ℚ) ≤ 2 ^ t)]
  have hchain : (2:ℚ) ^ t * (1 / 3 ^ (n - 2 * j)) ≤ epsBW := by
    calc (2:ℚ) ^ t * (1 / 3 ^ (n - 2 * j))
        ≤ 2 ^ t * |θq n ξ j (l + t)| := by
          apply mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = |θq n ξ j l| := habs.symm
      _ ≤ epsBW := hb0
  have h3pos : (0:ℚ) < 3 ^ (n - 2 * j) := by positivity
  calc (2:ℚ) ^ t = (2 ^ t * (1 / 3 ^ (n - 2 * j))) * 3 ^ (n - 2 * j) := by
        field_simp
    _ ≤ epsBW * 3 ^ (n - 2 * j) := by
        apply mul_le_mul_of_nonneg_right hchain h3pos.le

/-- Some point at or above `l` in column `j` is white (black runs terminate). -/
theorem exists_white_above (n ξ : ℕ) (hξ : ¬ 3 ∣ ξ) (j : ℕ) (l : ℤ) (h2j : 2 * j + 1 ≤ n) :
    ∃ t : ℕ, ¬ black n ξ j (l + t) := by
  by_contra hall
  push_neg at hall
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (epsBW * 3 ^ (n - 2 * j))
    (by norm_num : (1 : ℚ) < 2)
  exact absurd (black_run_le n ξ hξ h2j (fun i _ => hall i)) (not_le.mpr ht)

/-! ### The corner map `(j,l) ↦ (j*, l*)` (paper pp.38–39)

`l*` is the top of the contiguous black run above `(j,l)`; `j*` is then the far left of
the contiguous black run at height `l*`. Both defined via `Nat.find` (black is a
decidable ℚ-comparison; runs terminate by `exists_white_above` upward and by hitting
`j = 0` leftward). Junk-guarded on the upward existence so the defs are total. -/

open Classical in
/-- Offset of the first white point at or above `l` in column `j` (junk `0` if the
column were all-black, which `exists_white_above` rules out in context). -/
noncomputable def upRun (n ξ : ℕ) (j : ℕ) (l : ℤ) : ℕ :=
  if h : ∃ t : ℕ, ¬ black n ξ j (l + t) then Nat.find h else 0

/-- `l*(j,l)` (paper p.39): the top of the contiguous black run above `(j,l)`. -/
noncomputable def lstar (n ξ : ℕ) (j : ℕ) (l : ℤ) : ℤ := l + upRun n ξ j l - 1

open Classical in
/-- Leftward run length at height `lstar`: the first offset `a` (`≤ j+1`) at which
`(j - a, l*)` is white or `a` exceeds `j` (so `j* = j - (leftRun - 1)`). -/
noncomputable def leftRun (n ξ : ℕ) (j : ℕ) (l : ℤ) : ℕ :=
  Nat.find (⟨j + 1, by omega⟩ : ∃ a : ℕ, j < a ∨ ¬ black n ξ (j - a) (lstar n ξ j l))

/-- `j*(j,l)` (paper p.39): the far-left column of the black run at height `l*`. -/
noncomputable def jstar (n ξ : ℕ) (j : ℕ) (l : ℤ) : ℕ := j - (leftRun n ξ j l - 1)

section CornerSpec

variable {n ξ : ℕ} {j : ℕ} {l : ℤ}

/-- Everything from `l` up to `l*` is black, provided `(j,l)` is black. -/
theorem black_of_le_lstar (hξ : ¬ 3 ∣ ξ) (h2j : 2 * j + 1 ≤ n) (hb : black n ξ j l)
    {l' : ℤ} (h1 : l ≤ l') (h2 : l' ≤ lstar n ξ j l) : black n ξ j l' := by
  classical
  have hex := exists_white_above n ξ hξ j l h2j
  unfold lstar at h2
  rw [upRun, dif_pos hex] at h2
  have hi : (l' - l).toNat < Nat.find hex := by omega
  have hmin := Nat.find_min hex hi
  rw [not_not] at hmin
  have hcast : l + ((l' - l).toNat : ℤ) = l' := by omega
  rw [hcast] at hmin
  exact hmin

/-- `(j,l)` black implies `l ≤ l*`. -/
theorem le_lstar (hξ : ¬ 3 ∣ ξ) (h2j : 2 * j + 1 ≤ n) (hb : black n ξ j l) :
    l ≤ lstar n ξ j l := by
  classical
  have hex := exists_white_above n ξ hξ j l h2j
  unfold lstar
  rw [upRun, dif_pos hex]
  have h0 : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso
      have hs := Nat.find_spec hex
      rw [h] at hs
      simp only [Nat.cast_zero, add_zero] at hs
      exact hs hb
    · exact h
  omega

/-- The point just above `l*` is white. -/
theorem white_above_lstar (hξ : ¬ 3 ∣ ξ) (h2j : 2 * j + 1 ≤ n) :
    ¬ black n ξ j (lstar n ξ j l + 1) := by
  classical
  have hex := exists_white_above n ξ hξ j l h2j
  unfold lstar
  rw [upRun, dif_pos hex]
  have hs := Nat.find_spec hex
  have hcast : l + (Nat.find hex : ℤ) - 1 + 1 = l + Nat.find hex := by ring
  rw [hcast]
  exact hs

/-- `0 < leftRun` whenever `(j,l)` is black (the corner search starts on a black point). -/
theorem leftRun_pos (hξ : ¬ 3 ∣ ξ) (h2j : 2 * j + 1 ≤ n) (hb : black n ξ j l) :
    0 < leftRun n ξ j l := by
  classical
  have hbl : black n ξ j (lstar n ξ j l) :=
    black_of_le_lstar hξ h2j hb (le_lstar hξ h2j hb) le_rfl
  rw [leftRun, Nat.find_pos]
  intro h
  rcases h with h | h
  · omega
  · simp only [Nat.sub_zero] at h
    exact h hbl

/-- The whole row from `j*` to `j` at height `l*` is black, provided `(j,l)` is black. -/
theorem black_of_jstar_le (hξ : ¬ 3 ∣ ξ) (h2j : 2 * j + 1 ≤ n) (hb : black n ξ j l)
    {j' : ℕ} (h1 : jstar n ξ j l ≤ j') (h2 : j' ≤ j) : black n ξ j' (lstar n ξ j l) := by
  classical
  have hpos := leftRun_pos hξ h2j hb
  unfold jstar at h1
  have ha : j - j' < leftRun n ξ j l := by omega
  rw [leftRun] at ha
  have hmin := Nat.find_min
    (⟨j + 1, by omega⟩ : ∃ a : ℕ, j < a ∨ ¬ black n ξ (j - a) (lstar n ξ j l)) ha
  push_neg at hmin
  have hj' : j - (j - j') = j' := by omega
  rw [hj'] at hmin
  exact hmin.2

/-- Left of `j*` on the `l*` row: either `j* = 0` or the next point left is white. -/
theorem jstar_maximal (hξ : ¬ 3 ∣ ξ) (h2j : 2 * j + 1 ≤ n) (hb : black n ξ j l) :
    jstar n ξ j l = 0 ∨ ¬ black n ξ (jstar n ξ j l - 1) (lstar n ξ j l) := by
  classical
  have hpos := leftRun_pos hξ h2j hb
  have hspec : j < leftRun n ξ j l ∨
      ¬ black n ξ (j - leftRun n ξ j l) (lstar n ξ j l) := by
    rw [leftRun]
    exact Nat.find_spec
      (⟨j + 1, by omega⟩ : ∃ a : ℕ, j < a ∨ ¬ black n ξ (j - a) (lstar n ξ j l))
  rcases hspec with h | h
  · left; unfold jstar; omega
  · rcases Nat.lt_or_ge j (leftRun n ξ j l) with haj | haj
    · left; unfold jstar; omega
    · right
      rw [show jstar n ξ j l - 1 = j - leftRun n ξ j l from by unfold jstar; omega]
      exact h

end CornerSpec

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
