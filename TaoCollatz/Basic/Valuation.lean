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

/-- `valSum` is monotone in the length (all terms are nonnegative). -/
theorem valSum_mono (N : ℕ) {m n : ℕ} (h : m ≤ n) : valSum N m ≤ valSum N n := by
  unfold valSum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun i _ _ => Nat.zero_le _)

/-- Geometric-sum bound in ℕ: `∑_{j<n} 3^j ≤ 3^n`. -/
theorem geom_three_le (n : ℕ) : (∑ j ∈ Finset.range n, 3 ^ j) ≤ 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc (∑ j ∈ Finset.range n, 3 ^ j) + 3 ^ n ≤ 3 ^ n + 3 ^ n := Nat.add_le_add_right ih _
      _ ≤ 3 ^ n * 3 := by omega

/-- Reflected geometric-sum bound: `∑_{m<n} 3^{n-1-m} ≤ 3^n` (the `fnat` head coefficients). -/
theorem sum_three_pow_reflect_le (n : ℕ) :
    (∑ m ∈ Finset.range n, 3 ^ (n - 1 - m)) ≤ 3 ^ n := by
  rw [Finset.sum_range_reflect (fun j => 3 ^ j) n]
  exact geom_three_le n

/-- **`fnat` upper bound via the top valuation.** Since every prefix sum `valSum N m ≤ valSum N n`
(for `m ≤ n`) and `∑_{m<n} 3^{n-1-m} ≤ 3^n`:
`fnat n (valVec N n) ≤ 2^{valSum N n} · 3^n`. -/
theorem fnat_valVec_le (N n : ℕ) : fnat n (valVec N n) ≤ 2 ^ valSum N n * 3 ^ n := by
  rw [fnat_valVec]
  calc (∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * 2 ^ valSum N m)
      ≤ ∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) * 2 ^ valSum N n := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_range] at hm
        gcongr
        · norm_num
        · exact valSum_mono N hm.le
    _ = 2 ^ valSum N n * ∑ m ∈ Finset.range n, 3 ^ (n - 1 - m) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ 2 ^ valSum N n * 3 ^ n := by
        exact Nat.mul_le_mul_left _ (sum_three_pow_reflect_le n)

/-- **The descent bound** (the ℕ core of the (1.5)/(1.7) descent, node C7 step 4).  For odd `N`:
`2^{valSum N n} · Syr^{n}(N) ≤ 3^n·N + 2^{valSum N n}·3^n`.  Dividing by `2^{valSum N n}` gives
`Syr^{n}(N) ≤ 3^n·N / 2^{valSum N n} + 3^n`, the `O(3^n)` descent estimate. -/
theorem syr_descent_bound (N n : ℕ) (hN : N % 2 = 1) :
    2 ^ valSum N n * syr^[n] N ≤ 3 ^ n * N + 2 ^ valSum N n * 3 ^ n := by
  have hp : pre (valVec N n) n = valSum N n := pre_valVec (le_refl n)
  have hkey := syr_iterate_key N n hN
  rw [hp] at hkey
  rw [hkey]
  exact Nat.add_le_add_left (fnat_valVec_le N n) _

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

/-! ### The `Fnat` splitting identity (paper (1.26), integerified) — brick (a) for C10

For a valuation vector split at index `j` into its first `j` and last `p` coordinates, the
integerified affine offset splits as
`Fnat_{j+p}(a) = 3^p · Fnat_j(first j) + 2^{a_{[1,j]}} · Fnat_p(last p)`.
This is the algebraic heart of Tao's independent-split (1.5)/(1.26): once reduced mod `3ⁿ` it makes
the Syracuse character sum FACTOR (the second summand is a level-`p` Syracuse offset, independent of
the first `j` steps). Purely algebraic — no probability. -/

/-- The prefix sum of the first `j` coordinates agrees with the prefix sum of the whole vector,
for indices `m ≤ j`. -/
theorem pre_castAdd {j p : ℕ} (a : Fin (j + p) → ℕ) {m : ℕ} (hm : m ≤ j) :
    pre (fun i => a (Fin.castAdd p i)) m = pre a m := by
  unfold pre
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hij : i < j := lt_of_lt_of_le hi hm
  have hijp : i < j + p := lt_of_lt_of_le hij (Nat.le_add_right j p)
  rw [dif_pos hij, dif_pos hijp]
  congr 1

/-- The prefix sum through `j + m` splits as the first-`j` prefix plus the last-`p` prefix
(offset by `j`), for `m ≤ p`. -/
theorem pre_natAdd_split {j p : ℕ} (a : Fin (j + p) → ℕ) {m : ℕ} (hm : m ≤ p) :
    pre a (j + m) = pre a j + pre (fun i => a (Fin.natAdd j i)) m := by
  unfold pre
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hip : i < p := lt_of_lt_of_le hi hm
  have hjip : j + i < j + p := by omega
  rw [dif_pos hip, dif_pos hjip]
  congr 1

/-- **Paper (1.26), integerified** (brick a): the `Fnat` offset splits across a cut at index `j`
into `3^p · Fnat_j(first j coords) + 2^{a_{[1,j]}} · Fnat_p(last p coords)`. -/
theorem fnat_split {j p : ℕ} (a : Fin (j + p) → ℕ) :
    fnat (j + p) a
      = 3 ^ p * fnat j (fun i => a (Fin.castAdd p i))
        + 2 ^ pre a j * fnat p (fun i => a (Fin.natAdd j i)) := by
  unfold fnat
  rw [Finset.sum_range_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    rw [pre_castAdd a (le_of_lt hm)]
    have hexp : j + p - 1 - m = p + (j - 1 - m) := by omega
    rw [hexp, pow_add]; ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    rw [pre_natAdd_split a (le_of_lt hm), pow_add]
    have hexp : j + p - 1 - (j + m) = p - 1 - m := by omega
    rw [hexp]; ring

/-- Elementary 2-adic fact: `2ˢ·u = 2ᵗ·v` with `u,v` odd forces `s = t` and `u = v`. The atom of
the `Fnat` injectivity peel (each peel strips a `2^{a₀}` off an odd `Fnat` core). -/
theorem two_pow_odd_eq {s t u v : ℕ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v)
    (h : 2 ^ s * u = 2 ^ t * v) : s = t ∧ u = v := by
  wlog hst : s ≤ t generalizing s t u v
  · obtain ⟨h1, h2⟩ := this hv hu h.symm (not_le.mp hst).le
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [pow_add, mul_assoc] at h
  have hcancel : u = 2 ^ d * v := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) s) h
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp at hcancel; exact ⟨rfl, hcancel⟩
  · exact absurd (by rw [hcancel]; exact Dvd.dvd.mul_right (dvd_pow_self 2 hd.ne') v) hu

/-- First-coordinate prefix-sum peel: `a_{[1,m+1]} = a₀ + (tail a)_{[1,m]}`. -/
theorem pre_cons_head {n : ℕ} (a : Fin (n + 1) → ℕ) {m : ℕ} (hm : m ≤ n) :
    pre a (m + 1) = a 0 + pre (Fin.tail a) m := by
  unfold pre
  rw [Finset.sum_range_succ']
  have hf0 : (if h : (0:ℕ) < n + 1 then a ⟨0, h⟩ else 0) = a 0 := by
    rw [dif_pos (Nat.succ_pos n), Fin.zero_eta]
  rw [hf0, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hin : i < n := lt_of_lt_of_le hi hm
  rw [dif_pos (by omega : i + 1 < n + 1), dif_pos hin]
  rfl

/-- **Paper (1.5), first-coordinate form**: the `Fnat` offset peels off its first coordinate as
`Fnat_{n+1}(a) = 3ⁿ + 2^{a₀}·Fnat_n(tail a)`. The repo mirror of Tao's
`F_n(a₁,…,aₙ) = 3ⁿ2^{-a_{[1,n]}} + F_{n-1}(a₂,…,aₙ)` (cleared of `ℤ[1/2]`). Drives Lemma 6.2. -/
theorem fnat_cons {n : ℕ} (a : Fin (n + 1) → ℕ) :
    fnat (n + 1) a = 3 ^ n + 2 ^ (a 0) * fnat n (Fin.tail a) := by
  unfold fnat
  rw [Finset.sum_range_succ', Nat.add_sub_cancel]
  rw [add_comm]
  congr 1
  · rw [show pre a 0 = 0 from by simp [pre], pow_zero, mul_one, Nat.sub_zero]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    have hexp : n - (m + 1) = n - 1 - m := by omega
    rw [hexp, pre_cons_head a (le_of_lt hm), pow_add]
    ring

/-- **Lemma 6.2 (Injectivity of offsets), repo form on fixed total valuation.** Tao's key elementary
number-theory observation (paper Lemma 6.2: `Fₙ : (ℕ+1)ⁿ → ℤ[1/2]` injective), specialized to the
form the §6 Rényi/collision bound consumes: among positive-coordinate vectors with a *fixed* total
valuation `a_{[1,n]}`, the integer offset `Fnat n` determines the vector. (On `{pre = l}` the offset
`Fnat n a · 2⁻ˡ` used by `syracZ`/`tailDens` is injective iff `Fnat n` is; and Corollary 6.3's proof
invokes Lemma 6.2 exactly at equal valuations, via (6.13) `a_{[1,k+1]} = l`.) Proof: induct, peeling
the first coordinate with `fnat_cons`; the `2^{a₀}·(odd Fnat core)` factorization pins `a₀` and the
core via `two_pow_odd_eq` (`fnat_mod_two_of_pos`), and the fixed-valuation hypothesis discharges the
length-1 base. No `ℤ[1/2]` / 2-adic-valuation machinery: entirely `ℕ`-native. -/
theorem fnat_inj_fixed_val : ∀ (n : ℕ) (a a' : Fin n → ℕ),
    (∀ i, 1 ≤ a i) → (∀ i, 1 ≤ a' i) → pre a n = pre a' n → fnat n a = fnat n a' → a = a' := by
  intro n
  induction n with
  | zero => intro a a' _ _ _ _; exact funext (fun i => i.elim0)
  | succ n ih =>
      intro a a' ha ha' hpre hfnat
      rw [fnat_cons, fnat_cons] at hfnat
      have hFF : 2 ^ (a 0) * fnat n (Fin.tail a) = 2 ^ (a' 0) * fnat n (Fin.tail a') := by omega
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have h00 : a 0 = a' 0 := by
          have e1 : pre a 1 = a 0 := by simp [pre]
          have e2 : pre a' 1 = a' 0 := by simp [pre]
          rw [e1, e2] at hpre; exact hpre
        exact funext (fun i => by have hi : i = 0 := Fin.fin_one_eq_zero i; rw [hi]; exact h00)
      · have hodd : ∀ (b : Fin (n + 1) → ℕ), (∀ i, 1 ≤ b i) → ¬ 2 ∣ fnat n (Fin.tail b) := by
          intro b hb
          have hh := fnat_mod_two_of_pos (Fin.tail b) (fun i => hb i.succ)
          rw [if_neg (show n ≠ 0 by omega)] at hh
          omega
        obtain ⟨h0eq, hFeq⟩ := two_pow_odd_eq (hodd a ha) (hodd a' ha') hFF
        have hpretail : pre (Fin.tail a) n = pre (Fin.tail a') n := by
          have ea := pre_cons_head a (le_refl n)
          have ea' := pre_cons_head a' (le_refl n)
          rw [ea, ea', h0eq] at hpre; omega
        have htail := ih (Fin.tail a) (Fin.tail a') (fun i => ha i.succ) (fun i => ha' i.succ)
          hpretail hFeq
        exact funext (fun i => Fin.cases h0eq (fun j => congrFun htail j) i)

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
