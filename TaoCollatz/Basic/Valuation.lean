import TaoCollatz.Basic.Collatz
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Syracuse valuation vector and the `Fnat` integerification (node C2)

Paper anchors: Tao 2019 (1.3)–(1.8), (1.7), Lemma 2.1.

* `pre a m` — prefix sum `a_{[1,m]}` (paper convention; `a : Fin n → ℕ`).
* `valVec N n` — the `n`-Syracuse valuation vector `a⁽ⁿ⁾(N)` (1.8).
* `fnat n a` — the D2 integerification `2^|a| · F_n(a) ∈ ℕ` of the paper's affine offset.

The load-bearing result is `syr_iterate_key` (paper (1.7) × 2^|a|, entirely in ℕ):
```
2 ^ |a| · syr^[n] N = 3 ^ n · N + Fnat n a          (a = valVec N n)
```
proved by induction on `n`. Lemma 2.1 (uniqueness) is stated with `sorry`.
-/

namespace TaoCollatz

open Finset

/-- Prefix sum `a_{[1,m]} = a₁ + ⋯ + a_m` (paper convention, 0-indexed here). -/
def pre {n : ℕ} (a : Fin n → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, if h : i < n then a ⟨i, h⟩ else 0

/-- The `n`-Syracuse valuation vector `a⁽ⁿ⁾(N)`, paper (1.8):
`aᵢ = ν₂(3·syr^[i](N) + 1)`. -/
def valVec (N n : ℕ) : Fin n → ℕ := fun i => padicValNat 2 (3 * syr^[(i : ℕ)] N + 1)

/-- The D2 integerification `Fnat n a = 2^|a| · F_n(a) ∈ ℕ`, paper (1.5) scaled:
`∑ₘ 3^(n-1-m) · 2^(a_{[1,m]})`. -/
def fnat (n : ℕ) (a : Fin n → ℕ) : ℕ :=
  ∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * 2 ^ pre a m

/-- Prefix sum of the valuations along the Syracuse orbit (the ℕ-indexed form of
`pre (valVec N n)`, used for the (1.7) induction). -/
def valSum (N n : ℕ) : ℕ := ∑ i ∈ Finset.range n, padicValNat 2 (3 * syr^[i] N + 1)

@[simp] theorem valSum_zero (N : ℕ) : valSum N 0 = 0 := by simp [valSum]

theorem valSum_succ (N n : ℕ) :
    valSum N (n + 1) = valSum N n + padicValNat 2 (3 * syr^[n] N + 1) := by
  unfold valSum; rw [Finset.sum_range_succ]

/-- `pre (valVec N n) m = valSum N m` whenever `m ≤ n` (the guard is satisfied). -/
theorem pre_valVec {N n m : ℕ} (hmn : m ≤ n) : pre (valVec N n) m = valSum N m := by
  unfold pre valSum valVec
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos (lt_of_lt_of_le hi hmn)]

/-- `fnat n (valVec N n)` expressed with the ℕ-indexed prefix sums. -/
theorem fnat_valVec (N n : ℕ) :
    fnat n (valVec N n) = ∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * 2 ^ valSum N m := by
  unfold fnat
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  rw [pre_valVec (le_of_lt hm)]

/-- The recursion for the `Fnat` sum: peeling off the last prefix multiplies by 3
and adds the top-level `2^(valSum N n)`. -/
theorem fnatSum_succ (N n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), 3 ^ (n + 1 - 1 - m) * 2 ^ valSum N m)
      = 3 * (∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * 2 ^ valSum N m) + 2 ^ valSum N n := by
  rw [Finset.sum_range_succ]
  have hlast : n + 1 - 1 - n = 0 := by omega
  rw [hlast, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  have h1 : n + 1 - 1 - m = n - m := by omega
  have h2 : n - m = (n - 1 - m) + 1 := by omega
  rw [h1, h2, pow_succ]; ring

/-- Core induction for paper (1.7) × 2^|a|, in ℕ-indexed form. -/
theorem key_aux (N n : ℕ) :
    2 ^ valSum N n * syr^[n] N
      = 3 ^ n * N + ∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * 2 ^ valSum N m := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : 2 ^ padicValNat 2 (3 * syr^[n] N + 1) * syr (syr^[n] N)
          = 3 * syr^[n] N + 1 := two_pow_val_mul_syr' (syr^[n] N)
      rw [valSum_succ, pow_add, Function.iterate_succ_apply', mul_assoc, hstep,
          mul_add, mul_one,
          show 2 ^ valSum N n * (3 * syr^[n] N) = 3 * (2 ^ valSum N n * syr^[n] N) from by ring,
          ih, fnatSum_succ, pow_succ]
      ring

/-- **Paper (1.7) × 2^|a|, entirely in ℕ (node C2's heart).** For odd `N`:
`2 ^ |a| · syr^[n] N = 3 ^ n · N + Fnat n a`, where `a = valVec N n`. -/
theorem syr_iterate_key (N n : ℕ) (_hN : N % 2 = 1) :
    2 ^ pre (valVec N n) n * syr^[n] N = 3 ^ n * N + fnat n (valVec N n) := by
  rw [pre_valVec (le_refl n), fnat_valVec]
  exact key_aux N n

/-- The affine map `Aff_a(N) = (3^n·N + Fnat n a) / 2^(a_{[1,n]})` (paper (1.3),
guarded by the divisibility). -/
noncomputable def Aff (N n : ℕ) (a : Fin n → ℕ) : ℕ :=
  (3 ^ n * N + fnat n a) / 2 ^ pre a n

-- RATIFY-2: Lemma 2.1 (uniqueness), paper's `(Aff_a(N) ∈ 2ℕ+1) ↔ a = valVec N n` form,
-- guarded by the divisibility, with the positivity constraint `a i ≥ 1`. Judge against
-- the paper's Lemma 2.1 statement before grinding.
/-- **Lemma 2.1 (uniqueness).** For odd `N`, among vectors with every step `≥ 1`,
`valVec N n` is the unique one making the guarded affine value odd. -/
theorem valVec_unique (N n : ℕ) (hN : N % 2 = 1) (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) :
    (2 ^ pre a n ∣ 3 ^ n * N + fnat n a ∧ Aff N n a % 2 = 1) ↔ a = valVec N n := by
  sorry

end TaoCollatz
