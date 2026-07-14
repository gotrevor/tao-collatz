import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat

/-!
# Collatz / Syracuse maps (node C1)

Paper anchors: Tao 2019 §1.1–1.2, equations (1.1), (1.2).

* `col`  — the Collatz map (1.1).
* `colMin` — the minimal orbit value `Colmin(N)`.
* `oddPart` — the odd part of `N` (division by the exact 2-power).
* `syr` — the Syracuse map (1.1): odd part of `3N+1`.
* `syrMin` — the minimal Syracuse-orbit value `Syrmin(N)`.

Cheap lemmas proved here; `colMin_eq_syrMin_oddPart` (paper (1.2)) is stated with `sorry`.
-/

namespace TaoCollatz

/-- The Collatz map (paper (1.1)): `3N+1` on odds, `N/2` on evens. -/
def col (N : ℕ) : ℕ := if N % 2 = 1 then 3 * N + 1 else N / 2

/-- `Colmin(N)`, the least value attained by the Collatz orbit of `N`. -/
noncomputable def colMin (N : ℕ) : ℕ := sInf (Set.range fun k => col^[k] N)

/-- Odd part of `N`: divide out the exact power of 2. -/
def oddPart (N : ℕ) : ℕ := N / 2 ^ (padicValNat 2 N)

/-- The Syracuse map (paper (1.1)): odd part of `3N+1`. -/
def syr (N : ℕ) : ℕ := oddPart (3 * N + 1)

/-- `Syrmin(N)`, the least value attained by the Syracuse orbit of `N`. -/
noncomputable def syrMin (N : ℕ) : ℕ := sInf (Set.range fun k => syr^[k] N)

/-- `2 ^ (padicValNat 2 N)` divides `N`. -/
theorem pow_padicValNat_two_dvd (N : ℕ) : 2 ^ (padicValNat 2 N) ∣ N :=
  pow_padicValNat_dvd

/-- Extracting the exact 2-power recovers `N`. -/
theorem two_pow_mul_oddPart (N : ℕ) : 2 ^ (padicValNat 2 N) * oddPart N = N :=
  Nat.mul_div_cancel' (pow_padicValNat_two_dvd N)

/-- The odd part is positive whenever `N` is. -/
theorem oddPart_pos {N : ℕ} (hN : 0 < N) : 0 < oddPart N := by
  rcases Nat.eq_zero_or_pos (oddPart N) with h | h
  · exact absurd (by rw [← two_pow_mul_oddPart N, h, Nat.mul_zero]) hN.ne'
  · exact h

/-- The odd part is odd whenever `N` is positive. -/
theorem oddPart_odd {N : ℕ} (hN : 0 < N) : oddPart N % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one (oddPart N) with h | h
  · -- if `oddPart N` were even, `2 ^ (v+1)` would divide `N`, contradiction
    exfalso
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
    apply pow_succ_padicValNat_not_dvd (p := 2) hN.ne'
    have hNeq : 2 ^ padicValNat 2 N * oddPart N = N := two_pow_mul_oddPart N
    exact ⟨k, by rw [pow_succ, mul_assoc, ← hk, hNeq]⟩
  · exact h

/-- The Syracuse map preserves positivity. -/
theorem syr_pos {N : ℕ} (hN : 0 < N) : 0 < syr N :=
  oddPart_pos (by positivity)

/-- The Syracuse map lands on odd numbers. -/
theorem syr_odd {N : ℕ} (_hN : N % 2 = 1) : syr N % 2 = 1 :=
  oddPart_odd (by positivity)

/-- The 2-power identity `2 ^ ν · syr N = 3N+1` (used in the (1.7) induction). -/
theorem two_pow_val_mul_syr {N : ℕ} (_hN : N % 2 = 1) :
    2 ^ padicValNat 2 (3 * N + 1) * syr N = 3 * N + 1 :=
  two_pow_mul_oddPart (3 * N + 1)

/-- Unconditional single-step identity (the version the (1.7) induction consumes). -/
theorem two_pow_val_mul_syr' (M : ℕ) :
    2 ^ padicValNat 2 (3 * M + 1) * syr M = 3 * M + 1 :=
  two_pow_mul_oddPart (3 * M + 1)

/-- `padicValNat 2` vanishes on odd numbers. -/
theorem padicValNat_two_of_odd {a : ℕ} (h : a % 2 = 1) : padicValNat 2 a = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat.eq_zero_of_not_dvd (by rw [Nat.dvd_iff_mod_eq_zero]; omega)

/-- The odd part of an odd number is itself. -/
theorem oddPart_of_odd {a : ℕ} (h : a % 2 = 1) : oddPart a = a := by
  unfold oddPart; rw [padicValNat_two_of_odd h, pow_zero, Nat.div_one]

/-- Doubling shifts the 2-adic valuation by one. -/
theorem padicValNat_two_two_mul {a : ℕ} (ha : 0 < a) :
    padicValNat 2 (2 * a) = padicValNat 2 a + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h22 : padicValNat 2 2 = 1 := padicValNat_self
  rw [padicValNat.mul (by norm_num) ha.ne', h22]; omega

/-- The odd part is invariant under doubling. -/
theorem oddPart_two_mul {a : ℕ} (ha : 0 < a) : oddPart (2 * a) = oddPart a := by
  have h1 : 2 ^ padicValNat 2 (2 * a) * oddPart (2 * a) = 2 * a := two_pow_mul_oddPart (2 * a)
  have h2 : 2 ^ padicValNat 2 a * oddPart a = a := two_pow_mul_oddPart a
  rw [padicValNat_two_two_mul ha, pow_succ] at h1
  have h3 : 2 ^ padicValNat 2 a * 2 * oddPart (2 * a) = 2 ^ padicValNat 2 a * 2 * oddPart a := by
    rw [h1, mul_comm (2 ^ padicValNat 2 a) 2, mul_assoc, h2]
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h3

/-- `col` preserves positivity. -/
theorem col_pos {N : ℕ} (hN : 0 < N) : 0 < col N := by
  unfold col; split_ifs with h <;> omega

/-- Every Collatz iterate of a positive start is positive. -/
theorem col_iterate_pos {N : ℕ} (hN : 0 < N) : ∀ k, 0 < col^[k] N := by
  intro k; induction k with
  | zero => simpa using hN
  | succ k ih => rw [Function.iterate_succ_apply']; exact col_pos ih

/-- Every Syracuse iterate of a positive start is positive. -/
theorem syr_iterate_pos {a : ℕ} (ha : 0 < a) : ∀ j, 0 < syr^[j] a := by
  intro j; induction j with
  | zero => simpa using ha
  | succ j ih => rw [Function.iterate_succ_apply']; exact syr_pos ih

/-- `col` halves down to the odd part in exactly `padicValNat 2 a` steps. -/
theorem col_iterate_oddPart : ∀ a : ℕ, 0 < a → col^[padicValNat 2 a] a = oddPart a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha
    by_cases hodd : a % 2 = 1
    · rw [padicValNat_two_of_odd hodd, Function.iterate_zero_apply, oddPart_of_odd hodd]
    · have ha2 : 0 < a / 2 := by omega
      have hlt : a / 2 < a := Nat.div_lt_self ha (by norm_num)
      have hxeq : 2 * (a / 2) = a := by omega
      have hval : padicValNat 2 a = padicValNat 2 (a / 2) + 1 := by
        conv_lhs => rw [← hxeq]
        rw [padicValNat_two_two_mul ha2]
      have hcol : col a = a / 2 := by unfold col; rw [if_neg hodd]
      have hop : oddPart (a / 2) = oddPart a := by
        conv_rhs => rw [← hxeq]
        rw [oddPart_two_mul ha2]
      rw [hval, Function.iterate_succ_apply, hcol, ih (a / 2) hlt ha2, hop]

/-- **Fact A**: every Syracuse iterate of `oddPart N` is a Collatz iterate of `N`. -/
theorem col_reaches_syr {N : ℕ} (hN : 0 < N) :
    ∀ j, ∃ k, col^[k] N = syr^[j] (oddPart N) := by
  intro j
  induction j with
  | zero => exact ⟨padicValNat 2 N, by rw [col_iterate_oddPart N hN, Function.iterate_zero_apply]⟩
  | succ j ih =>
    obtain ⟨k, hk⟩ := ih
    set M := syr^[j] (oddPart N) with hM
    have hModd : M % 2 = 1 := by
      rw [hM]; cases j with
      | zero => rw [Function.iterate_zero_apply]; exact oddPart_odd hN
      | succ j' => rw [Function.iterate_succ_apply']; exact oddPart_odd (by positivity)
    refine ⟨padicValNat 2 (3 * M + 1) + 1 + k, ?_⟩
    calc col^[padicValNat 2 (3 * M + 1) + 1 + k] N
        = oddPart (3 * M + 1) := by
          rw [Function.iterate_add_apply, hk, Function.iterate_succ_apply,
            show col M = 3 * M + 1 from by unfold col; rw [if_pos hModd],
            col_iterate_oddPart (3 * M + 1) (by positivity)]
      _ = syr M := rfl
      _ = syr^[j + 1] (oddPart N) := by
          rw [hM]; exact (Function.iterate_succ_apply' syr j (oddPart N)).symm

/-- **Invariant B**: the odd part of every Collatz iterate of `N` is a Syracuse iterate
of `oddPart N`. -/
theorem oddPart_col_iterate {N : ℕ} (hN : 0 < N) :
    ∀ k, ∃ j, oddPart (col^[k] N) = syr^[j] (oddPart N) := by
  intro k
  induction k with
  | zero => exact ⟨0, by rw [Function.iterate_zero_apply, Function.iterate_zero_apply]⟩
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih
    set x := col^[k] N with hx
    have hxpos : 0 < x := by rw [hx]; exact col_iterate_pos hN k
    rw [Function.iterate_succ_apply']
    by_cases hodd : x % 2 = 1
    · refine ⟨j + 1, ?_⟩
      have hox : oddPart x = x := oddPart_of_odd hodd
      calc oddPart (col x) = oddPart (3 * x + 1) := by
              rw [show col x = 3 * x + 1 from by unfold col; rw [if_pos hodd]]
        _ = syr x := rfl
        _ = syr (oddPart x) := by rw [hox]
        _ = syr^[j + 1] (oddPart N) := by
            rw [hj]; exact (Function.iterate_succ_apply' syr j (oddPart N)).symm
    · refine ⟨j, ?_⟩
      have hx2 : 0 < x / 2 := by omega
      have hxeq : 2 * (x / 2) = x := by omega
      have hop : oddPart (x / 2) = oddPart x := by
        conv_rhs => rw [← hxeq, oddPart_two_mul hx2]
      rw [show col x = x / 2 from by unfold col; rw [if_neg hodd], hop, hj]

/-- Paper (1.2): the Collatz minimum equals the Syracuse minimum of the odd part. -/
theorem colMin_eq_syrMin_oddPart {N : ℕ} (hN : 0 < N) :
    colMin N = syrMin (oddPart N) := by
  apply le_antisymm
  · -- `colMin N ≤ syrMin (oddPart N)`: `syrMin` is attained and reachable by `col`.
    have hne : (Set.range fun j => syr^[j] (oddPart N)).Nonempty := ⟨oddPart N, 0, rfl⟩
    obtain ⟨j, hj⟩ := Nat.sInf_mem hne
    obtain ⟨k, hk⟩ := col_reaches_syr hN j
    have hmem : syrMin (oddPart N) ∈ Set.range fun k => col^[k] N := by
      refine ⟨k, ?_⟩
      show col^[k] N = syrMin (oddPart N)
      rw [hk]; exact hj
    exact Nat.sInf_le hmem
  · -- `syrMin (oddPart N) ≤ colMin N`: `colMin` is attained; its odd part is a `syr` iterate.
    have hne : (Set.range fun k => col^[k] N).Nonempty := ⟨N, 0, rfl⟩
    obtain ⟨k, hk⟩ := Nat.sInf_mem hne
    obtain ⟨j, hj⟩ := oddPart_col_iterate hN k
    have h1 : syr^[j] (oddPart N) ≤ col^[k] N := by
      rw [← hj]; unfold oddPart; exact Nat.div_le_self _ _
    calc syrMin (oddPart N) ≤ syr^[j] (oddPart N) := Nat.sInf_le ⟨j, rfl⟩
      _ ≤ col^[k] N := h1
      _ = colMin N := hk

end TaoCollatz
