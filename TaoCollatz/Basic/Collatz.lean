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

/-- Paper (1.2): the Collatz minimum equals the Syracuse minimum of the odd part. -/
theorem colMin_eq_syrMin_oddPart {N : ℕ} (_hN : 0 < N) :
    colMin N = syrMin (oddPart N) := by
  sorry

end TaoCollatz
