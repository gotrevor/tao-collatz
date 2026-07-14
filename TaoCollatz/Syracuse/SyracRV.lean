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

/-- `pre a m` as a plain ℕ-indexed summand (the `dite`-guarded coordinate). -/
private def preNat {n : ℕ} (a : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then a ⟨i, h⟩ else 0

private theorem pre_eq_sum_preNat {n : ℕ} (a : Fin n → ℕ) (m : ℕ) :
    pre a m = ∑ i ∈ Finset.range m, preNat a i := rfl

/-- The prefix-`k` marginal of an iid vector is again iid: pushing `p.iid n` forward
under restriction to the first `k` coordinates (`· ∘ Fin.castLE`) gives `p.iid k`. -/
private theorem iid_map_castLE {α : Type*} (p : PMF α) :
    ∀ (k n : ℕ) (h : k ≤ n),
      (p.iid n).map (fun a : Fin n → α => a ∘ Fin.castLE h) = p.iid k := by
  intro k
  induction k with
  | zero =>
      intro n _
      -- target `Fin 0 → α` is a subsingleton: the map is constant.
      rw [show (fun a : Fin n → α => a ∘ Fin.castLE (Nat.zero_le n))
            = Function.const _ (fun i : Fin 0 => i.elim0) from by
          funext a; funext i; exact i.elim0]
      rw [PMF.map_const]
      rfl
  | succ k ih =>
      intro n h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h' : k ≤ m := Nat.succ_le_succ_iff.mp h
      -- cons/castLE commutation: restricting `cons a0 w` to `k+1` prefix = `cons a0`
      -- of the `k`-prefix restriction of `w`.
      have hcons : ∀ (a0 : α) (w : Fin m → α),
          (Fin.cons a0 w : Fin (m + 1) → α) ∘ Fin.castLE h
            = Fin.cons a0 (w ∘ Fin.castLE h') := by
        intro a0 w
        funext i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · simp only [Function.comp_apply]
          rw [show Fin.castLE h (0 : Fin (k + 1)) = (0 : Fin (m + 1)) from by
            apply Fin.ext; simp, Fin.cons_zero, Fin.cons_zero]
        · simp only [Function.comp_apply]
          rw [show Fin.castLE h j.succ = (Fin.castLE h' j).succ from by
            apply Fin.ext; simp, Fin.cons_succ, Fin.cons_succ, Function.comp_apply]
      rw [show p.iid (m + 1) = p.bind fun a0 => (p.iid m).map (Fin.cons a0) from rfl,
        PMF.map_bind, show p.iid (k + 1) = p.bind fun a0 => (p.iid k).map (Fin.cons a0) from rfl]
      congr 1
      funext a0
      rw [PMF.map_comp, show (fun a : Fin (m + 1) → α => a ∘ Fin.castLE h) ∘ Fin.cons a0
          = Fin.cons a0 ∘ (fun w : Fin m → α => w ∘ Fin.castLE h') from by
        funext w; exact hcons a0 w, ← PMF.map_comp, ih m h']

/-- Paper (1.22): reducing `Syrac(ℤ/3ⁿℤ)` mod `3ᵏ` gives `Syrac(ℤ/3ᵏℤ)`. -/
theorem syracZ_map_cast {k n : ℕ} (hkn : k ≤ n) :
    (syracZ n).map (ZMod.castHom (pow_dvd_pow 3 hkn) (ZMod (3 ^ k))) = syracZ k := by
  set φ := ZMod.castHom (pow_dvd_pow 3 hkn) (ZMod (3 ^ k)) with hφ
  -- `2` is a unit mod `3ⁿ` and mod `3ᵏ`.
  have hunit : ∀ r : ℕ, (2 : ZMod (3 ^ r)) * (2 : ZMod (3 ^ r))⁻¹ = 1 := by
    intro r
    apply ZMod.mul_inv_of_unit
    rw [show (2 : ZMod (3 ^ r)) = ((2 : ℕ) : ZMod (3 ^ r)) from by norm_cast,
      ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right r (by decide)
  have hphi3 : φ (3 : ZMod (3 ^ n)) = (3 : ZMod (3 ^ k)) := map_ofNat φ 3
  have hphi2 : φ ((2 : ZMod (3 ^ n))⁻¹) = (2 : ZMod (3 ^ k))⁻¹ := by
    have h1 : (2 : ZMod (3 ^ k)) * φ ((2 : ZMod (3 ^ n))⁻¹) = 1 := by
      rw [show (2 : ZMod (3 ^ k)) = φ 2 from (map_ofNat φ 2).symm, ← map_mul, hunit n, map_one]
    calc φ ((2 : ZMod (3 ^ n))⁻¹)
        = 1 * φ ((2 : ZMod (3 ^ n))⁻¹) := (one_mul _).symm
      _ = ((2 : ZMod (3 ^ k))⁻¹ * 2) * φ ((2 : ZMod (3 ^ n))⁻¹) := by
          rw [mul_comm ((2 : ZMod (3 ^ k))⁻¹) 2, hunit k]
      _ = (2 : ZMod (3 ^ k))⁻¹ * ((2 : ZMod (3 ^ k)) * φ ((2 : ZMod (3 ^ n))⁻¹)) := by ring
      _ = (2 : ZMod (3 ^ k))⁻¹ := by rw [h1, mul_one]
  -- `3^j = 0` in `ZMod (3ᵏ)` for `j ≥ k`.
  have h3zero : ∀ j, k ≤ j → (3 : ZMod (3 ^ k)) ^ j = 0 := by
    intro j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [pow_add, show (3 : ZMod (3 ^ k)) ^ k = ((3 ^ k : ℕ) : ZMod (3 ^ k)) from by push_cast; ring,
      ZMod.natCast_self, zero_mul]
  -- prefix sums are unchanged by the restriction on the first `k` coordinates.
  have hpre : ∀ (a : Fin n → ℕ) (j : ℕ), j + 1 ≤ k →
      pre (a ∘ Fin.castLE hkn) (j + 1) = pre a (j + 1) := by
    intro a j hj
    rw [pre_eq_sum_preNat, pre_eq_sum_preNat]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hik : i < k := by omega
    have hin : i < n := lt_of_lt_of_le hik hkn
    unfold preNat
    rw [dif_pos hik, dif_pos hin]
    show a (Fin.castLE hkn ⟨i, hik⟩) = a ⟨i, hin⟩
    congr 1
  -- truncation: `φ (F_n a) = F_k (a ∘ castLE)`.
  have htrunc : ∀ a : Fin n → ℕ,
      φ (∑ j ∈ Finset.range n,
            (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre a (j + 1))
        = ∑ j ∈ Finset.range k,
            (3 : ZMod (3 ^ k)) ^ j * (2 : ZMod (3 ^ k))⁻¹ ^ pre (a ∘ Fin.castLE hkn) (j + 1) := by
    intro a
    rw [map_sum]
    -- push `φ` through each term.
    have hterm : ∀ j, φ ((3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre a (j + 1))
        = (3 : ZMod (3 ^ k)) ^ j * (2 : ZMod (3 ^ k))⁻¹ ^ pre a (j + 1) := by
      intro j
      rw [map_mul, map_pow, map_pow, hphi3, hphi2]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    -- split `range n` into `range k` and the vanishing tail.
    rw [← Finset.sum_range_add_sum_Ico _ hkn]
    rw [show (∑ j ∈ Finset.Ico k n,
          (3 : ZMod (3 ^ k)) ^ j * (2 : ZMod (3 ^ k))⁻¹ ^ pre a (j + 1)) = 0 from by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [h3zero j hj.1, zero_mul]]
    rw [add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hpre a j (by omega)]
  -- assembly.
  unfold syracZ
  rw [PMF.map_comp,
    show (φ ∘ fun a : Fin n → ℕ =>
          ∑ j ∈ Finset.range n,
            (3 : ZMod (3 ^ n)) ^ j * (2 : ZMod (3 ^ n))⁻¹ ^ pre a (j + 1))
        = (fun a' : Fin k → ℕ =>
              ∑ j ∈ Finset.range k,
                (3 : ZMod (3 ^ k)) ^ j * (2 : ZMod (3 ^ k))⁻¹ ^ pre a' (j + 1))
            ∘ (fun a : Fin n → ℕ => a ∘ Fin.castLE hkn) from by
      funext a; exact htrunc a,
    ← PMF.map_comp, iid_map_castLE]

/-- Peeling the head coordinate off a prefix sum: `pre a (m+1) = a 0 + pre (tail a) m`. -/
private theorem pre_succ_tail {n : ℕ} (a : Fin (n + 1) → ℕ) (m : ℕ) :
    pre a (m + 1) = a 0 + pre (Fin.tail a) m := by
  rw [pre_eq_sum_preNat, pre_eq_sum_preNat, Finset.sum_range_succ']
  have h0 : preNat a 0 = a 0 := by
    unfold preNat; rw [dif_pos (Nat.succ_pos n)]; rfl
  have hshift : ∀ i ∈ Finset.range m, preNat a (i + 1) = preNat (Fin.tail a) i := by
    intro i _
    unfold preNat Fin.tail
    by_cases hi : i < n
    · rw [dif_pos (by omega : i + 1 < n + 1), dif_pos hi]; rfl
    · rw [dif_neg (by omega : ¬ i + 1 < n + 1), dif_neg hi]
  rw [Finset.sum_congr rfl hshift, h0, add_comm]

/-- **Head-peel of the (1.26) offset (algebraic core of Lemma 1.12).** In `ZMod (3ⁿ⁺¹)`,
factoring out the first geometric coordinate `a 0`:
`Gₙ₊₁(a) = 2⁻ᵃ⁰ · (1 + 3·Ĝ(tail a))`, where `Ĝ` is the level-`n` offset formula
computed in `ZMod (3ⁿ⁺¹)`. -/
private theorem syracZ_offset_peel {n : ℕ} (a : Fin (n + 1) → ℕ) :
    (∑ j ∈ Finset.range (n + 1),
        (3 : ZMod (3 ^ (n + 1))) ^ j * (2 : ZMod (3 ^ (n + 1)))⁻¹ ^ pre a (j + 1))
      = (2 : ZMod (3 ^ (n + 1)))⁻¹ ^ a 0 *
          (1 + 3 * ∑ j ∈ Finset.range n,
              (3 : ZMod (3 ^ (n + 1))) ^ j
                * (2 : ZMod (3 ^ (n + 1)))⁻¹ ^ pre (Fin.tail a) (j + 1)) := by
  -- head term `f 0 = 2⁻ᵃ⁰`.
  have hhead : (3 : ZMod (3 ^ (n + 1))) ^ 0 * (2 : ZMod (3 ^ (n + 1)))⁻¹ ^ pre a (0 + 1)
      = (2 : ZMod (3 ^ (n + 1)))⁻¹ ^ a 0 := by
    rw [pow_zero, one_mul, pre_succ_tail, show pre (Fin.tail a) 0 = 0 from rfl, add_zero]
  -- each tail term factors as `2⁻ᵃ⁰ · (3 · 3ʲ · 2⁻ᵖʳᵉ)`.
  have hterm : ∀ k ∈ Finset.range n,
      (3 : ZMod (3 ^ (n + 1))) ^ (k + 1) * (2 : ZMod (3 ^ (n + 1)))⁻¹ ^ pre a (k + 1 + 1)
        = (2 : ZMod (3 ^ (n + 1)))⁻¹ ^ a 0
            * (3 * (3 ^ k * (2 : ZMod (3 ^ (n + 1)))⁻¹ ^ pre (Fin.tail a) (k + 1))) := by
    intro k _
    rw [pre_succ_tail a (k + 1), pow_add, pow_succ]
    ring
  rw [Finset.sum_range_succ', hhead, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

/-- **Geometric fold for a `P`-periodic weight (normalization core of Lemma 1.12).**
For `g` periodic with period `P`, the `2⁻ᵃ`-weighted sum over all `a` collapses to one
period times the geometric normalization `(1 − 2⁻ᴾ)⁻¹`. -/
private theorem geom_fold {P : ℕ} (hP : 0 < P) (g : ℕ → ℝ≥0∞)
    (hper : ∀ a, g (a + P) = g a) :
    ∑' a : ℕ, (2⁻¹ : ℝ≥0∞) ^ a * g a
      = (1 - (2⁻¹ : ℝ≥0∞) ^ P)⁻¹ * ∑ r ∈ Finset.range P, (2⁻¹ : ℝ≥0∞) ^ r * g r := by
  haveI : NeZero P := ⟨hP.ne'⟩
  have hperk : ∀ k r, g (k * P + r) = g r := by
    intro k r
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul, add_right_comm, hper, ih]
  rw [← (Nat.divModEquiv P).symm.tsum_eq (fun a => (2⁻¹ : ℝ≥0∞) ^ a * g a)]
  simp only [Nat.divModEquiv_symm_apply]
  rw [ENNReal.tsum_prod']
  have hinner : ∀ k : ℕ,
      (∑' r : Fin P, (2⁻¹ : ℝ≥0∞) ^ (k * P + (r : ℕ)) * g (k * P + (r : ℕ)))
        = ((2⁻¹ : ℝ≥0∞) ^ P) ^ k * ∑ r ∈ Finset.range P, (2⁻¹ : ℝ≥0∞) ^ r * g r := by
    intro k
    rw [tsum_fintype, ← Fin.sum_univ_eq_sum_range (fun r => (2⁻¹ : ℝ≥0∞) ^ r * g r) P,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [hperk k r, pow_add, mul_comm k P, pow_mul]
    ring
  rw [tsum_congr hinner, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

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
  -- DECOMPOSITION (algebraic core PROVED: `syracZ_offset_peel`, `pre_succ_tail`).
  -- Remaining route (probabilistic, multi-lap):
  --  (1) `syracZ (n+1) x = ∑' a₀:ℕ, geomHalf a₀ * (mass over tail w of {Gₙ₊₁(cons a₀ w) = x})`
  --      via `PMF.map_apply` + `iid_apply_eq_prod` / `tsum_iid_succ_mul`.
  --  (2) `syracZ_offset_peel`: `Gₙ₊₁(cons a₀ w) = 2⁻ᵃ⁰·(1 + 3·Ĝ(w))`, so `Gₙ₊₁ = x`
  --      ⟺ `1 + 3·Ĝ(w) = 2^{a₀}·x` in `ZMod 3ⁿ⁺¹` ⟺ [`2^{a₀}·x.val ≡ 1 (mod 3)` AND
  --      `Ĝ(w) = (2^{a₀}·x.val − 1)/3`]. The guard is exactly the `if` condition.
  --  (3) reduce `Ĝ(w) mod 3ⁿ = Gₙ(w)` (the `syracZ_map_cast`/`castHom` truncation, already
  --      built), so the tail-mass = `syracZ n (((2^{a₀}x.val−1)/3 : ℕ) : ZMod 3ⁿ)`.
  --  (4) FOLD the `a₀`-sum: `a₀ ↦ (2^{a₀}x.val−1)/3 mod 3ⁿ` is periodic with period
  --      `2·3ⁿ` (= multiplicative order of 2 mod 3ⁿ⁺¹), giving `∑_{a₀≥1} = (1−2^{−2·3ⁿ})⁻¹
  --      · ∑_{a₀=1}^{2·3ⁿ}` — the normalization. Needs `orderOf (2 : ZMod 3ⁿ⁺¹) = 2·3ⁿ`
  --      + a geometric-tail resummation over the residue.
  sorry

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
