import TaoCollatz.Basic.Valuation
import TaoCollatz.Prob.Geometric
import Mathlib.Data.ZMod.Basic

/-!
# The Syracuse random variable `Syrac(ℤ/3ⁿℤ)` (node C4)

Paper anchors: Tao 2019 (1.21), (1.22), (1.26), Lemma 1.12.

`syracZ n` is the law of the reduced Syracuse offset mod `3ⁿ`, in the **(1.26)
reversed** form (footnote 6; validated by the numeric harness, check 3/5). Statements:
the projection compatibility (1.22), the Lemma 1.12 recursion, and the (1.21) bridge
to `fnat`, all carry `sorry`.
-/

open scoped ENNReal

namespace TaoCollatz

/-- `Syrac(ℤ/3ⁿℤ)`, paper (1.26) reversed form: pushforward of `Geom(2)ⁿ` under
`a ↦ ∑ⱼ 3ʲ · 2⁻⁽ᵃ¹⁺⋯⁺ᵃⱼ⁺¹⁾` in `ZMod (3ⁿ)`. -/
noncomputable def syracZ (n : ℕ) : PMF (ZMod (3 ^ n)) :=
  (PMF.iid geomHalf n).map fun a =>
    ∑ j ∈ Finset.range n, (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre a (j + 1)

/-- Paper (1.22): reducing `Syrac(ℤ/3ⁿℤ)` mod `3ᵏ` gives `Syrac(ℤ/3ᵏℤ)`. -/
theorem syracZ_map_cast {k n : ℕ} (hkn : k ≤ n) :
    (syracZ n).map (ZMod.castHom (pow_dvd_pow 3 hkn) (ZMod (3 ^ k))) = syracZ k := by
  sorry

-- RATIFY-DRIFT: the "divide by 3" step of Lemma 1.12 is spelled in ℕ
-- (`(2^a · x.val - 1) / 3`, exact under the guard `(2^a · x.val) % 3 = 1`) rather than
-- with `(3 : ZMod (3^(n+1)))⁻¹`, because 3 is a zero-divisor there and `ZMod.inv` is
-- junk on non-units. Mathematical content identical (harness check 5 computes exactly
-- this ℕ form). Judge against paper Lemma 1.12.
/-- Lemma 1.12 recursion: the point mass of `Syrac(ℤ/3ⁿ⁺¹ℤ)` at `x` is obtained by
summing the appropriate `2⁻ᵃ`-weighted point masses of `Syrac(ℤ/3ⁿℤ)` over
`1 ≤ a ≤ 2·3ⁿ` with `2^a·x ≡ 1 (mod 3)`, normalized by `(1 - 2^{-2·3ⁿ})⁻¹`.
(Numeric harness check 5.) -/
theorem syracZ_recursion (n : ℕ) (x : ZMod (3 ^ (n + 1))) :
    (syracZ (n + 1)) x
      = (1 - 2⁻¹ ^ (2 * 3 ^ n))⁻¹ *
          ∑ a ∈ Finset.Icc 1 (2 * 3 ^ n),
            (if (2 ^ a * x.val) % 3 = 1
              then 2⁻¹ ^ a * (syracZ n) (((2 ^ a * x.val - 1) / 3 : ℕ) : ZMod (3 ^ n))
              else 0) := by
  sorry

/-- `pre a m` as a plain ℕ-indexed summand (the `dite`-guarded coordinate). -/
private def preNat {n : ℕ} (a : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then a ⟨i, h⟩ else 0

private theorem pre_eq_sum_preNat {n : ℕ} (a : Fin n → ℕ) (m : ℕ) :
    pre a m = ∑ i ∈ Finset.range m, preNat a i := rfl

/-- Reversal splits a prefix sum: the first `m` reversed coordinates plus the first
`n - m` forward coordinates cover the whole vector. (Exchangeability's ℕ backbone.) -/
private theorem pre_comp_rev {n : ℕ} (a : Fin n → ℕ) {m : ℕ} (hm : m ≤ n) :
    pre (a ∘ Fin.rev) m + pre a (n - m) = pre a n := by
  rw [pre_eq_sum_preNat, pre_eq_sum_preNat, pre_eq_sum_preNat]
  -- Rewrite the reversed summand into `preNat a (n-1-i)`.
  have hrev : ∀ i ∈ Finset.range m, preNat (a ∘ Fin.rev) i = preNat a (n - 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hin : i < n := lt_of_lt_of_le hi hm
    have hni : n - 1 - i < n := by omega
    unfold preNat
    rw [dif_pos hin, dif_pos hni]
    show a (Fin.rev ⟨i, hin⟩) = a ⟨n - 1 - i, hni⟩
    congr 1
    apply Fin.ext
    rw [Fin.val_rev]
    show n - (i + 1) = n - 1 - i
    omega
  rw [Finset.sum_congr rfl hrev]
  -- Reindex `∑_{i<m} preNat a (n-1-i)` to `∑_{i<m} preNat a (n-m+i)` (reflection).
  have hreflect : (∑ i ∈ Finset.range m, preNat a (n - 1 - i))
      = ∑ i ∈ Finset.range m, preNat a (n - m + i) := by
    rw [← Finset.sum_range_reflect (fun i => preNat a (n - m + i)) m]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    congr 1
    omega
  rw [hreflect]
  -- `∑_{i<m} preNat a (n-m+i) = ∑_{Ico (n-m) n} preNat a`, then merge with `[0, n-m)`.
  have hIco : (∑ i ∈ Finset.range m, preNat a (n - m + i))
      = ∑ i ∈ Finset.Ico (n - m) n, preNat a i := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.sub_sub_self hm]
  rw [hIco, add_comm, Finset.range_eq_Ico,
    Finset.sum_Ico_consecutive _ (Nat.zero_le _) (Nat.sub_le n m), Finset.range_eq_Ico]

/-- The reversal map on `iid` vectors preserves the law (exchangeability of iid). -/
private theorem iid_map_rev {α : Type*} (p : PMF α) (n : ℕ) :
    (p.iid n).map (fun a => a ∘ Fin.rev) = p.iid n := by
  classical
  ext v
  rw [PMF.map_apply, tsum_eq_single (v ∘ Fin.rev)]
  · rw [if_pos, PMF.iid_apply_eq_prod, PMF.iid_apply_eq_prod]
    · exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by
        rw [Function.comp_apply, Fin.revPerm_apply])
    · funext i; show v i = v (Fin.rev (Fin.rev i)); rw [Fin.rev_rev]
  · intro a ha
    rw [if_neg]
    intro heq
    apply ha
    funext i
    have := congrFun heq (Fin.rev i)
    simpa [Function.comp, Fin.rev_rev] using this.symm

/-- Paper (1.21) bridge: the reversed form agrees in law with the `fnat`-based offset
form `a ↦ (Fnat n a) · 2⁻⁽ᵃ¹⁺⋯⁺ᵃⁿ⁾` in `ZMod (3ⁿ)`. -/
theorem syracZ_eq_rev_fnat (n : ℕ) :
    syracZ n
      = (PMF.iid geomHalf n).map
          (fun a => (fnat n a : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ pre a n) := by
  -- `2` is a unit mod `3ⁿ`, so `2 * 2⁻¹ = 1`.
  have hunit : (2 : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ = 1 := by
    apply ZMod.mul_inv_of_unit
    rw [show (2 : ZMod (3 ^ n)) = ((2 : ℕ) : ZMod (3 ^ n)) from by norm_cast,
      ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right n (by decide)
  -- Pointwise: `g b = f (b ∘ rev)` where `f` is the (1.26)-reversed summand.
  have hkey : ∀ b : Fin n → ℕ,
      (fnat n b : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ pre b n
        = ∑ j ∈ Finset.range n,
            (3 : ZMod (3 ^ n)) ^ j
              * (2 : ZMod (3 ^ n))⁻¹ ^ pre (b ∘ Fin.rev) (j + 1) := by
    intro b
    rw [fnat, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    -- Left summand at reflected index `n-1-j`.
    have hj' : n - 1 - (n - 1 - j) = j := by omega
    rw [hj', Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat]
    -- Additive exponent identity: `pre (b∘rev) (j+1) + pre b (n-1-j) = pre b n`.
    have hsplit : pre (b ∘ Fin.rev) (j + 1) + pre b (n - 1 - j) = pre b n := by
      have := pre_comp_rev b (m := j + 1) (by omega)
      rwa [show n - (j + 1) = n - 1 - j from by omega] at this
    -- `3^j * 2^(pre b (n-1-j)) * (2⁻¹)^(pre b n) = 3^j * (2⁻¹)^(pre (b∘rev) (j+1))`.
    rw [mul_assoc]
    congr 1
    set P := pre b (n - 1 - j)
    set Q := pre (b ∘ Fin.rev) (j + 1)
    rw [← hsplit, pow_add,
      show (2 : ZMod (3 ^ n)) ^ P * ((2 : ZMod (3 ^ n))⁻¹ ^ Q * (2 : ZMod (3 ^ n))⁻¹ ^ P)
        = ((2 : ZMod (3 ^ n)) ^ P * (2 : ZMod (3 ^ n))⁻¹ ^ P) * (2 : ZMod (3 ^ n))⁻¹ ^ Q from by
          ring,
      ← mul_pow, hunit, one_pow, one_mul]
  -- Assemble via reversal-invariance of the iid law: `G = F ∘ (·∘rev)`.
  have hGF :
      (fun a : Fin n → ℕ => (fnat n a : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ pre a n)
        = ((fun b : Fin n → ℕ =>
              ∑ j ∈ Finset.range n,
                (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre b (j + 1))
            ∘ (fun a : Fin n → ℕ => a ∘ Fin.rev)) := funext hkey
  unfold syracZ
  rw [hGF, ← PMF.map_comp, iid_map_rev]

end TaoCollatz
