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
proved by induction on `n`. Lemma 2.1 gives uniqueness of the valuation vector.
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

private def initVec {n : ℕ} (a : Fin (n + 1) → ℕ) : Fin n → ℕ :=
  fun i => a i.castSucc

private theorem pre_initVec {n : ℕ} (a : Fin (n + 1) → ℕ) (m : ℕ) (hm : m ≤ n) :
    pre a m = pre (initVec a) m := by
  unfold pre initVec
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hin : i < n := lt_of_lt_of_le hi hm
  rw [dif_pos (lt_trans hin (Nat.lt_succ_self n)), dif_pos hin]
  congr

private theorem pre_succ_initVec {n : ℕ} (a : Fin (n + 1) → ℕ) :
    pre a (n + 1) = pre (initVec a) n + a (Fin.last n) := by
  unfold pre
  rw [Finset.sum_range_succ]
  have hn : n < n + 1 := Nat.lt_succ_self n
  rw [dif_pos hn]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos (lt_trans hi hn), dif_pos hi]
  rfl

private theorem fnat_succ_initVec {n : ℕ} (a : Fin (n + 1) → ℕ) :
    fnat (n + 1) a = 3 * fnat n (initVec a) + 2 ^ pre (initVec a) n := by
  unfold fnat
  rw [Finset.sum_range_succ]
  have hlast : n + 1 - 1 - n = 0 := by omega
  rw [hlast, pow_zero, one_mul, pre_initVec a n (le_refl n), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  rw [pre_initVec a m (le_of_lt hm)]
  have h1 : n + 1 - 1 - m = (n - 1 - m) + 1 := by omega
  rw [h1, pow_succ]
  ring

/-- The integerified affine offset is odd for every nonempty positive valuation vector. -/
theorem fnat_mod_two_of_pos {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) :
    fnat n a % 2 = if n = 0 then 0 else 1 := by
  induction n with
  | zero => simp [fnat]
  | succ n ih =>
      rw [fnat_succ_initVec]
      have hb : ∀ i, 1 ≤ initVec a i := fun i => ha i.castSucc
      have hpre : n ≤ pre (initVec a) n := by
        unfold pre
        calc
          n = ∑ _i ∈ Finset.range n, 1 := by simp
          _ ≤ ∑ i ∈ Finset.range n,
              if h : i < n then initVec a ⟨i, h⟩ else 0 := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.mem_range] at hi
            rw [dif_pos hi]
            exact hb ⟨i, hi⟩
      rw [if_neg (by omega), Nat.add_mod, Nat.mul_mod, ih (initVec a) hb]
      by_cases hn : n = 0
      · subst n
        simp [pre]
      · rw [if_neg hn]
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hpow : 2 ^ pre (initVec a) n % 2 = 0 := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_trans hn1 hpre)
          rw [hk, pow_add]
          norm_num
        rw [hpow]

private theorem padicValNat_two_eq_of_mul_odd {x k q : ℕ} (h : 2 ^ k * q = x)
    (hq : q % 2 = 1) : padicValNat 2 x = k := by
  have hx : x ≠ 0 := by
    intro hx0
    have hq0 : q ≠ 0 := by omega
    exact (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) hq0) (h.trans hx0)
  apply le_antisymm
  · by_contra hn
    have hk : k + 1 ≤ padicValNat 2 x := by omega
    have hd := (Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := k + 1) (n := x)
      (by omega) hx).2 hk
    obtain ⟨c, hc⟩ := hd
    have heq : 2 ^ k * q = 2 ^ (k + 1) * c := h.trans hc
    have hc' : 2 * c = q := by
      have hp : 0 < 2 ^ k := by positivity
      simp only [pow_succ] at heq
      nlinarith
    omega
  · exact (Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := k) (n := x)
      (by omega) hx).1 ⟨q, h.symm⟩

private theorem valVec_unique_of (n : ℕ) : ∀ (N : ℕ), N % 2 = 1 →
    ∀ (a : Fin n → ℕ), (∀ i, 1 ≤ a i) →
      (2 ^ pre a n ∣ 3 ^ n * N + fnat n a ∧ Aff N n a % 2 = 1) →
      a = valVec N n := by
  induction n with
  | zero =>
      intro N hN a ha h
      funext i
      exact i.elim0
  | succ n ih =>
      intro N hN a ha h
      let b : Fin n → ℕ := initVec a
      let S := pre b n
      let x := a (Fin.last n)
      let E := 3 ^ n * N + fnat n b
      let q := Aff N (n + 1) a
      have hq : q % 2 = 1 := h.2
      have hfactor : 2 ^ pre a (n + 1) * q = 3 ^ (n + 1) * N + fnat (n + 1) a := by
        exact Nat.mul_div_cancel' h.1
      have hfactor' : 2 ^ S * (2 ^ x * q) = 2 ^ S + 3 * E := by
        dsimp [S, x, E, q] at *
        rw [pre_succ_initVec, pow_add, fnat_succ_initVec, pow_succ] at hfactor
        nlinarith
      have hd3E : 2 ^ S ∣ 3 * E := by
        have hxq : 1 ≤ 2 ^ x * q := by
          have hqpos : 0 < q := by omega
          have : 0 < 2 ^ x * q := Nat.mul_pos (by positivity) hqpos
          omega
        have hsplit : 2 ^ x * q = (2 ^ x * q - 1) + 1 := by omega
        refine ⟨2 ^ x * q - 1, ?_⟩
        rw [hsplit, mul_add, mul_one] at hfactor'
        omega
      have hdE : 2 ^ S ∣ E := by
        exact ((by decide : Nat.Coprime 2 3).pow_left S).dvd_of_dvd_mul_left hd3E
      let M := E / 2 ^ S
      have hEM : 2 ^ S * M = E := Nat.mul_div_cancel' hdE
      have hlastFactor : 2 ^ x * q = 3 * M + 1 := by
        have hp : 0 < 2 ^ S := by positivity
        nlinarith [hfactor', hEM]
      have hx : 1 ≤ x := ha (Fin.last n)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hx
      have hMmod : M % 2 = 1 := by
        have hd2 : 2 ∣ 3 * M + 1 := by
          refine ⟨2 ^ k * q, ?_⟩
          rw [← hlastFactor, hk, pow_add]
          ring
        have hz := Nat.dvd_iff_mod_eq_zero.mp hd2
        omega
      have hAffM : Aff N n b = M := by
        unfold Aff
        dsimp [S, E, M] at hEM ⊢
      have hbcond : 2 ^ pre b n ∣ 3 ^ n * N + fnat n b ∧ Aff N n b % 2 = 1 := by
        constructor
        · exact hdE
        · rw [hAffM]
          exact hMmod
      have hbpos : ∀ i, 1 ≤ b i := fun i => ha i.castSucc
      have hb : b = valVec N n := ih N hN b hbpos hbcond
      have hMorb : M = syr^[n] N := by
        have hkey := syr_iterate_key N n hN
        rw [← hb] at hkey
        have hEM' : 2 ^ pre b n * M = 3 ^ n * N + fnat n b := by
          simpa [S, E] using hEM
        exact Nat.eq_of_mul_eq_mul_left (by positivity) (hEM'.trans hkey.symm)
      have hxval : x = padicValNat 2 (3 * syr^[n] N + 1) := by
        rw [← hMorb]
        exact (padicValNat_two_eq_of_mul_odd hlastFactor hq).symm
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [x, valVec] using hxval
      · simpa [b, initVec, valVec] using congrFun hb j

/-- Every Syracuse iterate of an odd natural number is odd. -/
theorem syr_iterate_odd (N n : ℕ) (hN : N % 2 = 1) : syr^[n] N % 2 = 1 := by
  induction n with
  | zero => simpa using hN
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact syr_odd ih

-- RATIFY-2: Lemma 2.1 (uniqueness), paper's `(Aff_a(N) ∈ 2ℕ+1) ↔ a = valVec N n` form,
-- guarded by the divisibility, with the positivity constraint `a i ≥ 1`. Judge against
-- the paper's Lemma 2.1 statement before grinding.
/-- **Lemma 2.1 (uniqueness).** For odd `N`, among vectors with every step `≥ 1`,
`valVec N n` is the unique one making the guarded affine value odd. -/
theorem valVec_unique (N n : ℕ) (hN : N % 2 = 1) (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) :
    (2 ^ pre a n ∣ 3 ^ n * N + fnat n a ∧ Aff N n a % 2 = 1) ↔ a = valVec N n := by
  constructor
  · exact valVec_unique_of n N hN a ha
  · intro haeq
    subst a
    have hkey := syr_iterate_key N n hN
    constructor
    · exact ⟨syr^[n] N, hkey.symm⟩
    · unfold Aff
      rw [← hkey]
      rw [Nat.mul_comm (2 ^ pre (valVec N n) n) (syr^[n] N),
        Nat.mul_div_left _ (by positivity)]
      exact syr_iterate_odd N n hN

end TaoCollatz
