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
