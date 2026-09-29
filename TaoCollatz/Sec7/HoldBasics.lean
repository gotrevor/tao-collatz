/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7.Reduction
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Lemma 7.6 (node X5): basic properties of the holding time `Hold`

Paper anchor: Tao 2019 p.42, **Lemma 7.6** (Basic properties of holding time):
"The random variable `Hold` has exponential tail (in the sense of (2.3)), is not
supported in any coset of any proper subgroup of ℤ², and has mean `(4,16)`. In
particular, the conclusion of Lemma 2.2 holds for `Hold` with `μ⃗ = (4,16)`."

Status of the four clauses in this repository:

* **exponential tail** and the **"in particular" Lemma 2.2 conclusion**: already
  PROVED — the S3 engine establishes Lemma 2.2 for `hold` DIRECTLY by the
  Chernoff/MGF route of the paper's own proof ((7.29)–(7.30)):
  `hold_tail_bound` (`Sec7/HoldLocal.lean`, Lemma 2.2(ii)) and
  `hold_local_bound` (Lemma 2.2(i), mean `(4,16)` recentring). Those are the
  only clauses any downstream consumer uses quantitatively.
* **mean `(4,16)`**: `hold_mean_fst`, `hold_mean_snd` (this file). The paper's
  computation `𝔼Hold = (1, 𝔼Pascal) + (3/4)·𝔼Hold` is replaced by the direct
  sum over the explicit `geomQuarter`/`pascalNe3` construction of `hold`:
  `𝔼Hold = ∑_k Geom(4)(k)·(k, 3 + (k−1)·𝔼Pascal')` with `𝔼Pascal' = 13/3`
  (paper (7.29)), giving `(4, 3 + 3·13/3) = (4, 16)`.
* **aperiodicity**: `hold_aperiodic` (this file) — the support of `hold` is not
  contained in any coset of any proper subgroup of ℤ² (stated as: any subgroup
  containing all base-point differences of support points is `⊤`). The paper's
  witnesses: `Hold` attains `(1,3)` and `(1,3)+(1,b)` for every
  `b ∈ ℕ+2 \ {3}`; the differences `(1,2), (1,4), (1,5)` already generate ℤ².
-/

open scoped ENNReal

namespace TaoCollatz

/-! ### Generic iid mean calculus (ℝ≥0∞: no summability side conditions) -/

/-- Mean of a coordinate-sum observable over an iid vector: `n` times the
single-draw mean. ℝ≥0∞-valued, so unconditional. -/
theorem tsum_iid_sum_mul {α : Type*} (p : PMF α) (f : α → ℝ≥0∞) :
    ∀ n : ℕ, ∑' v : Fin n → α, (p.iid n) v * (∑ i, f (v i))
      = n * ∑' a, p a * f a := by
  intro n
  induction n with
  | zero => rw [PMF.tsum_iid_zero_mul p (fun v => ∑ i, f (v i))]; simp
  | succ n IH =>
    rw [PMF.tsum_iid_succ_mul p n (fun v : Fin (n + 1) → α => ∑ i, f (v i))]
    have hcons : ∀ (a : α) (w : Fin n → α),
        ∑ i, f ((Fin.cons a w : Fin (n + 1) → α) i) = f a + ∑ i, f (w i) := by
      intro a w
      rw [Fin.sum_univ_succ]
      simp
    have hinner : ∀ a : α,
        ∑' w : Fin n → α, (p.iid n) w * ∑ i, f ((Fin.cons a w : Fin (n + 1) → α) i)
          = f a + n * ∑' x, p x * f x := by
      intro a
      calc ∑' w : Fin n → α, (p.iid n) w * ∑ i, f ((Fin.cons a w : Fin (n + 1) → α) i)
          = ∑' w : Fin n → α,
              ((p.iid n) w * f a + (p.iid n) w * ∑ i, f (w i)) := by
            exact tsum_congr fun w => by rw [hcons, mul_add]
        _ = (∑' w : Fin n → α, (p.iid n) w * f a)
              + ∑' w : Fin n → α, (p.iid n) w * ∑ i, f (w i) :=
            ENNReal.tsum_add
        _ = f a + n * ∑' x, p x * f x := by
            rw [ENNReal.tsum_mul_right, (p.iid n).tsum_coe, one_mul, IH]
    calc ∑' a, p a * ∑' w : Fin n → α, (p.iid n) w * ∑ i, f ((Fin.cons a w : Fin (n + 1) → α) i)
        = ∑' a, (p a * f a + p a * (n * ∑' x, p x * f x)) :=
          tsum_congr fun a => by rw [hinner, mul_add]
      _ = (∑' a, p a * f a) + ∑' a, p a * (n * ∑' x, p x * f x) :=
          ENNReal.tsum_add
      _ = (∑' a, p a * f a) + n * ∑' x, p x * f x := by
          rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
      _ = (n + 1 : ℕ) * ∑' a, p a * f a := by push_cast; ring

/-- Bridge a real `HasSum` for the PMF-weighted observable to the ℝ≥0∞ tsum. -/
theorem tsum_mul_ofReal_eq {α : Type*} (p : PMF α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    {s : ℝ} (h : HasSum (fun x => (p x).toReal * f x) s) :
    ∑' x, p x * ENNReal.ofReal (f x) = ENNReal.ofReal s := by
  have hterm : ∀ x, p x * ENNReal.ofReal (f x)
      = ENNReal.ofReal ((p x).toReal * f x) := by
    intro x
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (p.apply_ne_top x)]
  rw [tsum_congr hterm,
    ← ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg ENNReal.toReal_nonneg (hf x))
      h.summable, h.tsum_eq]

/-! ### Single-draw means: `Geom(2)`, `Geom(4)`, `Pascal`, `Pascal'` -/

/-- Mean of `Geom(2)`: `∑ a·2⁻ᵃ = 2`. -/
theorem geomHalf_mean : ∑' a : ℕ, geomHalf a * (a : ℝ≥0∞) = 2 := by
  have hgeo : HasSum (fun a : ℕ => (a : ℝ) * 2⁻¹ ^ a) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one
      (𝕜 := ℝ) (r := 2⁻¹) (by rw [Real.norm_eq_abs]; norm_num)
    have h2 : ((2⁻¹ : ℝ)) / (1 - 2⁻¹) ^ 2 = 2 := by norm_num
    rw [h2] at h
    exact h
  have hfun : ∀ a : ℕ, (geomHalf a).toReal * (a : ℝ) = (a : ℝ) * 2⁻¹ ^ a := by
    intro a
    rw [geomHalf_toReal]
    rcases Nat.eq_zero_or_pos a with h0 | h1
    · simp [h0]
    · rw [if_neg (by omega), mul_comm]
  have h2 : ∑' a : ℕ, geomHalf a * ENNReal.ofReal (a : ℝ) = ENNReal.ofReal 2 :=
    tsum_mul_ofReal_eq geomHalf (fun a => (a : ℝ)) (fun a => Nat.cast_nonneg a)
      (by rw [show (fun a : ℕ => (geomHalf a).toReal * (a : ℝ))
        = fun a : ℕ => (a : ℝ) * 2⁻¹ ^ a from funext hfun]; exact hgeo)
  calc ∑' a : ℕ, geomHalf a * (a : ℝ≥0∞)
      = ∑' a : ℕ, geomHalf a * ENNReal.ofReal (a : ℝ) := by
        exact tsum_congr fun a => by rw [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal 2 := h2
    _ = 2 := by norm_num

/-- Mean of `Geom(4)` (paper `j ≡ Geom(4)`, p.41): `∑ k·4⁻¹(3/4)^{k−1} = 4`. -/
theorem geomQuarter_mean : ∑' k : ℕ, geomQuarter k * (k : ℝ≥0∞) = 4 := by
  have hgeo : HasSum (fun k : ℕ => (3⁻¹ : ℝ) * ((k : ℝ) * (3 / 4) ^ k)) 4 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one
      (𝕜 := ℝ) (r := 3 / 4) (by rw [Real.norm_eq_abs]; norm_num)
    have h4 : ((3 : ℝ) / 4) / (1 - 3 / 4) ^ 2 = 12 := by norm_num
    rw [h4] at h
    have h5 := h.mul_left (3⁻¹ : ℝ)
    have h6 : (3⁻¹ : ℝ) * 12 = 4 := by norm_num
    rw [h6] at h5
    exact h5
  have hfun : ∀ k : ℕ, (geomQuarter k).toReal * (k : ℝ)
      = (3⁻¹ : ℝ) * ((k : ℝ) * (3 / 4) ^ k) := by
    intro k
    rw [geomQuarter_toReal]
    rcases Nat.eq_zero_or_pos k with h0 | h1
    · simp [h0]
    · rw [if_neg (by omega)]
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      ring
  have h2 : ∑' k : ℕ, geomQuarter k * ENNReal.ofReal (k : ℝ) = ENNReal.ofReal 4 :=
    tsum_mul_ofReal_eq geomQuarter (fun k => (k : ℝ)) (fun k => Nat.cast_nonneg k)
      (by rw [show (fun k : ℕ => (geomQuarter k).toReal * (k : ℝ))
        = fun k : ℕ => (3⁻¹ : ℝ) * ((k : ℝ) * (3 / 4) ^ k) from funext hfun]; exact hgeo)
  calc ∑' k : ℕ, geomQuarter k * (k : ℝ≥0∞)
      = ∑' k : ℕ, geomQuarter k * ENNReal.ofReal (k : ℝ) := by
        exact tsum_congr fun k => by rw [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal 4 := h2
    _ = 4 := by norm_num

/-- Mean of `Pascal` = `Geom(2)+Geom(2)`: `4` (via `pascal_eq_map_iid`). -/
theorem pascal_mean : ∑' b : ℕ, pascal b * (b : ℝ≥0∞) = 4 := by
  rw [pascal_eq_map_iid, PMF.tsum_map_mul]
  have hfun : ∀ v : Fin 2 → ℕ, ((v 0 + v 1 : ℕ) : ℝ≥0∞)
      = ∑ i, ((v i : ℝ≥0∞)) := by
    intro v
    rw [Fin.sum_univ_two]
    push_cast
    ring
  rw [tsum_congr fun v => by rw [hfun]]
  rw [tsum_iid_sum_mul geomHalf (fun a => (a : ℝ≥0∞)) 2, geomHalf_mean]
  norm_num

/-- The mean of the tail-shifted `geomQuarter`: `∑ Geom(4)(k)·(k−1) = 3`. -/
theorem geomQuarter_mean_sub_one :
    ∑' k : ℕ, geomQuarter k * ((k - 1 : ℕ) : ℝ≥0∞) = 3 := by
  have hsplit : (1 : ℝ≥0∞) + ∑' k : ℕ, geomQuarter k * ((k - 1 : ℕ) : ℝ≥0∞)
      = 1 + 3 := by
    have h1 : (1 : ℝ≥0∞) = ∑' k : ℕ, geomQuarter k * 1 := by
      rw [tsum_congr fun k => mul_one (geomQuarter k), geomQuarter.tsum_coe]
    calc (1 : ℝ≥0∞) + ∑' k : ℕ, geomQuarter k * ((k - 1 : ℕ) : ℝ≥0∞)
        = (∑' k : ℕ, geomQuarter k * 1)
          + ∑' k : ℕ, geomQuarter k * ((k - 1 : ℕ) : ℝ≥0∞) := by rw [← h1]
      _ = ∑' k : ℕ, (geomQuarter k * 1 + geomQuarter k * ((k - 1 : ℕ) : ℝ≥0∞)) :=
          ENNReal.tsum_add.symm
      _ = ∑' k : ℕ, geomQuarter k * (k : ℝ≥0∞) := by
          refine tsum_congr fun k => ?_
          rcases Nat.eq_zero_or_pos k with h0 | h1
          · subst h0
            rw [show geomQuarter 0 = 0 from rfl]
            simp
          · rw [← mul_add]
            congr 1
            rw [show (1 : ℝ≥0∞) + ((k - 1 : ℕ) : ℝ≥0∞) = ((1 + (k - 1) : ℕ) : ℝ≥0∞)
              from by push_cast; ring]
            congr 1
            omega
      _ = 4 := geomQuarter_mean
      _ = 1 + 3 := by norm_num
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).mp hsplit

/-- Mean of `Pascal' = Pascal | (Pascal ≠ 3)` (paper (7.29)): `13/3`. -/
theorem pascalNe3_mean : ∑' b : ℕ, pascalNe3 b * (b : ℝ≥0∞) = 13 * 3⁻¹ := by
  -- split the `b = 3` atom (mass `4⁻¹`, contribution `3·4⁻¹`) off the Pascal mean
  have hp3 : pascal 3 = 4⁻¹ := by
    rw [show pascal 3 = ((3 - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 3 from rfl]
    rw [show ((3 - 1 : ℕ) : ℝ≥0∞) = 2 by norm_num, pow_succ', ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul, ← ENNReal.inv_pow]
    norm_num
  have hg3 : pascal 3 * ((3 : ℕ) : ℝ≥0∞) = 3 * 4⁻¹ := by
    rw [hp3, show ((3 : ℕ) : ℝ≥0∞) = 3 from by norm_num, mul_comm]
  have hsum0 :=
    (ENNReal.tsum_eq_add_tsum_ite (f := fun b : ℕ => pascal b * (b : ℝ≥0∞)) 3).symm.trans
      pascal_mean
  have hsum : pascal 3 * ((3 : ℕ) : ℝ≥0∞)
      + ∑' b, (if b = 3 then 0 else pascal b * (b : ℝ≥0∞)) = 4 := by
    rw [show (∑' b, (if b = 3 then 0 else pascal b * (b : ℝ≥0∞)))
      = ∑' x : ℕ, @ite ℝ≥0∞ (x = 3) (Classical.propDecidable (x = 3)) 0
          (pascal x * (x : ℝ≥0∞)) from
      tsum_congr fun x => by by_cases hx : x = 3 <;> simp [hx]]
    exact hsum0
  have hrest : ∑' b, (if b = 3 then 0 else pascal b * (b : ℝ≥0∞)) = 13 * 4⁻¹ := by
    have h34 : (3 : ℝ≥0∞) * 4⁻¹ + 13 * 4⁻¹ = 4 := by
      rw [← add_mul, show (3 : ℝ≥0∞) + 13 = 16 from by norm_num,
        show (16 : ℝ≥0∞) = 4 * 4 from by norm_num, mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by finiteness), mul_one]
    have hs := hsum
    rw [hg3] at hs
    exact (ENNReal.add_right_inj (show (3 : ℝ≥0∞) * 4⁻¹ ≠ ⊤ by finiteness)).mp
      (hs.trans h34.symm)
  have hfun : ∀ b : ℕ, pascalNe3 b * (b : ℝ≥0∞)
      = (4 * 3⁻¹) * (if b = 3 then 0 else pascal b * (b : ℝ≥0∞)) := by
    intro b
    by_cases hb3 : b = 3
    · subst hb3
      rw [show pascalNe3 3 = 0 from rfl, if_pos rfl]
      simp
    · rw [if_neg hb3]
      by_cases hb2 : b < 2
      · have hp : pascal b = 0 := by
          rw [show pascal b = if b < 2 then 0 else ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b from rfl,
            if_pos hb2]
        have hpn : pascalNe3 b = 0 := by
          rw [show pascalNe3 b = if b < 2 ∨ b = 3 then 0
            else (4 / 3) * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b) from rfl, if_pos (Or.inl hb2)]
        rw [hp, hpn]
        simp
      · have hp : pascal b = ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b := by
          rw [show pascal b = if b < 2 then 0 else ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b from rfl,
            if_neg hb2]
        have hpn : pascalNe3 b = (4 * 3⁻¹) * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b) := by
          rw [show pascalNe3 b = if b < 2 ∨ b = 3 then 0
            else (4 / 3) * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b) from rfl,
            if_neg (not_or.mpr ⟨hb2, hb3⟩), div_eq_mul_inv]
        rw [hp, hpn]
        ring
  rw [tsum_congr hfun, ENNReal.tsum_mul_left, hrest]
  rw [show (4 : ℝ≥0∞) * 3⁻¹ * (13 * 4⁻¹) = (13 * 3⁻¹) * (4 * 4⁻¹) from by ring,
    ENNReal.mul_inv_cancel (by norm_num) (by finiteness), mul_one]

/-! ### Lemma 7.6, mean clause: `𝔼 Hold = (4, 16)` -/

/-- **Lemma 7.6, mean clause, first coordinate** (paper p.42–43: `𝔼Hold = (4,16)`):
the ℝ≥0∞ form `∑ Hold(d)·d₁ = 4` (first coordinate is `Geom(4)`). -/
theorem hold_mean_fst_ennreal : ∑' d : ℕ × ℤ, hold d * (d.1 : ℝ≥0∞) = 4 := by
  rw [show (fun d : ℕ × ℤ => hold d * (d.1 : ℝ≥0∞))
    = fun d : ℕ × ℤ => hold d * ((fun k : ℕ => (k : ℝ≥0∞)) (Prod.fst d)) from rfl,
    ← PMF.tsum_map_mul hold Prod.fst (fun k : ℕ => (k : ℝ≥0∞)), hold_map_fst]
  exact geomQuarter_mean

/-- **Lemma 7.6, mean clause, second coordinate** (paper p.42–43): the ℝ≥0∞ form
`∑ Hold(d)·d₂ = 16 = 3 + 𝔼(j−1)·𝔼Pascal' = 3 + 3·(13/3)`. On the support the
second coordinate is `3 + Σ increments ≥ 3`, encoded via `Int.toNat`. -/
theorem hold_mean_snd_ennreal :
    ∑' d : ℕ × ℤ, hold d * ((d.2.toNat : ℕ) : ℝ≥0∞) = 16 := by
  rw [hold, PMF.tsum_bind_mul]
  have hinner : ∀ k : ℕ,
      ∑' d : ℕ × ℤ, ((pascalNe3.iid (k - 1)).map fun v => (k, (3 + ∑ i, v i : ℤ))) d
          * ((d.2.toNat : ℕ) : ℝ≥0∞)
        = 3 + ((k - 1 : ℕ) : ℝ≥0∞) * (13 * 3⁻¹) := by
    intro k
    rw [PMF.tsum_map_mul (pascalNe3.iid (k - 1))
      (fun v => ((k, 3 + ∑ i, (v i : ℤ)) : ℕ × ℤ))
      (fun d : ℕ × ℤ => ((d.2.toNat : ℕ) : ℝ≥0∞))]
    have hval : ∀ v : Fin (k - 1) → ℕ,
        ((((3 + ∑ i, (v i : ℤ)) : ℤ).toNat : ℕ) : ℝ≥0∞)
          = 3 + ∑ i, ((v i : ℝ≥0∞)) := by
      intro v
      have hnat : ((3 + ∑ i, (v i : ℤ)) : ℤ) = ((3 + ∑ i, v i : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hnat, Int.toNat_natCast]
      push_cast
      ring
    calc ∑' v : Fin (k - 1) → ℕ, (pascalNe3.iid (k - 1)) v
          * ((((3 + ∑ i, (v i : ℤ)) : ℤ).toNat : ℕ) : ℝ≥0∞)
        = ∑' v : Fin (k - 1) → ℕ, ((pascalNe3.iid (k - 1)) v * 3
            + (pascalNe3.iid (k - 1)) v * ∑ i, ((v i : ℝ≥0∞))) :=
          tsum_congr fun v => by rw [hval, mul_add]
      _ = (∑' v : Fin (k - 1) → ℕ, (pascalNe3.iid (k - 1)) v * 3)
            + ∑' v : Fin (k - 1) → ℕ, (pascalNe3.iid (k - 1)) v * ∑ i, ((v i : ℝ≥0∞)) :=
          ENNReal.tsum_add
      _ = 3 + ((k - 1 : ℕ) : ℝ≥0∞) * (13 * 3⁻¹) := by
          rw [ENNReal.tsum_mul_right, (pascalNe3.iid (k - 1)).tsum_coe, one_mul,
            tsum_iid_sum_mul pascalNe3 (fun a => (a : ℝ≥0∞)) (k - 1), pascalNe3_mean]
  rw [tsum_congr fun k => by rw [hinner k]]
  calc ∑' k : ℕ, geomQuarter k * (3 + ((k - 1 : ℕ) : ℝ≥0∞) * (13 * 3⁻¹))
      = (∑' k : ℕ, geomQuarter k * 3)
          + ∑' k : ℕ, geomQuarter k * ((k - 1 : ℕ) : ℝ≥0∞) * (13 * 3⁻¹) := by
        rw [← ENNReal.tsum_add]
        exact tsum_congr fun k => by rw [mul_add, mul_assoc]
    _ = 3 + 3 * (13 * 3⁻¹) := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, geomQuarter.tsum_coe,
          one_mul, geomQuarter_mean_sub_one]
    _ = 16 := by
        rw [show (3 : ℝ≥0∞) * (13 * 3⁻¹) = 13 * (3 * 3⁻¹) from by ring,
          ENNReal.mul_inv_cancel (by norm_num) (by finiteness), mul_one]
        norm_num

/-- **Lemma 7.6, mean clause (real form), first coordinate**: `𝔼[Hold₁] = 4`. -/
theorem hold_mean_fst : ∑' d : ℕ × ℤ, (hold d).toReal * (d.1 : ℝ) = 4 := by
  have h := hold_mean_fst_ennreal
  have hconv : ∑' d : ℕ × ℤ, hold d * ((d.1 : ℕ) : ℝ≥0∞)
      = ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal ((d.1 : ℕ) : ℝ) :=
    tsum_congr fun d => by rw [ENNReal.ofReal_natCast]
  rw [hconv] at h
  have := congrArg ENNReal.toReal h
  rw [PMF.toReal_tsum_mul_ofReal hold (fun d => ((d.1 : ℕ) : ℝ))
    (fun d => Nat.cast_nonneg _)] at this
  rw [this]
  norm_num

/-- **Lemma 7.6, mean clause (real form), second coordinate**: `𝔼[Hold₂] = 16`. -/
theorem hold_mean_snd : ∑' d : ℕ × ℤ, (hold d).toReal * (d.2 : ℝ) = 16 := by
  have h := hold_mean_snd_ennreal
  have hconv : ∑' d : ℕ × ℤ, hold d * ((d.2.toNat : ℕ) : ℝ≥0∞)
      = ∑' d : ℕ × ℤ, hold d * ENNReal.ofReal ((d.2.toNat : ℕ) : ℝ) :=
    tsum_congr fun d => by rw [ENNReal.ofReal_natCast]
  rw [hconv] at h
  have h2 := congrArg ENNReal.toReal h
  rw [PMF.toReal_tsum_mul_ofReal hold (fun d => ((d.2.toNat : ℕ) : ℝ))
    (fun d => Nat.cast_nonneg _)] at h2
  have hterm : ∀ d : ℕ × ℤ, (hold d).toReal * (d.2 : ℝ)
      = (hold d).toReal * ((d.2.toNat : ℕ) : ℝ) := by
    intro d
    by_cases hd : d ∈ hold.support
    · have h3 := hold_support_snd_ge d hd
      have h4 : ((d.2.toNat : ℕ) : ℝ) = (d.2 : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ d.2)
      rw [h4]
    · rw [PMF.mem_support_iff, not_not] at hd
      rw [hd]
      simp
  rw [tsum_congr hterm, h2]
  norm_num

/-! ### Lemma 7.6, aperiodicity clause -/

/-- Converse of `iid_support_coord`: coordinate-wise support membership puts the
vector in the iid support. -/
theorem iid_mem_support {α : Type*} (p : PMF α) :
    ∀ (n : ℕ) (v : Fin n → α), (∀ i, v i ∈ p.support) → v ∈ (p.iid n).support := by
  intro n
  induction n with
  | zero =>
    intro v _
    rw [show p.iid 0 = PMF.pure (fun i => i.elim0) from rfl, PMF.support_pure]
    exact funext fun i => i.elim0
  | succ n IH =>
    intro v hv
    rw [show p.iid (n + 1) = p.bind fun a => (p.iid n).map (Fin.cons a) from rfl,
      PMF.mem_support_bind_iff]
    refine ⟨v 0, hv 0, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨Fin.tail v, IH (Fin.tail v) fun i => hv i.succ, Fin.cons_self_tail v⟩

/-- `(1, 3) ∈ supp Hold` (the paper's `Hold = (1,3)` with probability `1/4`). -/
theorem hold_mem_support_one_three : ((1, 3) : ℕ × ℤ) ∈ hold.support := by
  rw [hold, PMF.mem_support_bind_iff]
  refine ⟨1, ?_, ?_⟩
  · rw [PMF.mem_support_iff]
    rw [show geomQuarter 1 = if (1 : ℕ) = 0 then 0 else 4⁻¹ * (3 * 4⁻¹) ^ (1 - 1) from rfl]
    norm_num
  · rw [PMF.mem_support_map_iff]
    refine ⟨fun i => i.elim0, ?_, by simp⟩
    exact iid_mem_support pascalNe3 0 _ (fun i => i.elim0)

/-- `(2, 3 + b) ∈ supp Hold` for every `b ≥ 2`, `b ≠ 3` (the paper's
`Hold = (1,3) + (1,b)` events). -/
theorem hold_mem_support_two (b : ℕ) (hb2 : 2 ≤ b) (hb3 : b ≠ 3) :
    ((2, (3 + b : ℤ)) : ℕ × ℤ) ∈ hold.support := by
  rw [hold, PMF.mem_support_bind_iff]
  refine ⟨2, ?_, ?_⟩
  · rw [PMF.mem_support_iff]
    rw [show geomQuarter 2 = if (2 : ℕ) = 0 then 0 else 4⁻¹ * (3 * 4⁻¹) ^ (2 - 1) from rfl]
    norm_num
  · rw [PMF.mem_support_map_iff]
    refine ⟨fun _ => b, ?_, ?_⟩
    · refine iid_mem_support pascalNe3 (2 - 1) _ (fun i => ?_)
      rw [PMF.mem_support_iff]
      rw [show pascalNe3 b = if b < 2 ∨ b = 3 then 0
        else (4 / 3) * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b) from rfl,
        if_neg (not_or.mpr ⟨Nat.not_lt.mpr hb2, hb3⟩)]
      refine mul_ne_zero (by norm_num) (mul_ne_zero ?_ ?_)
      · exact_mod_cast Nat.cast_ne_zero.mpr (show b - 1 ≠ 0 by omega)
      · exact pow_ne_zero _ (by norm_num)
    · simp

/-- **Lemma 7.6, aperiodicity clause** (paper p.42): the support of `Hold` is not
contained in any coset of any proper subgroup of `ℤ²`. Stated as: if a subgroup
`H ≤ ℤ²` contains `d − x` for every support point `d` (i.e. `supp Hold ⊆ x + H`),
then `H = ⊤`. Witnesses: `(1,3)` and `(2, 3+b)` for `b = 2, 4, 5`; the pairwise
differences `(1,2), (1,4), (1,5)` generate `ℤ²`. -/
theorem hold_aperiodic (H : AddSubgroup (ℤ × ℤ)) (x : ℤ × ℤ)
    (hsub : ∀ d ∈ hold.support, ((d.1 : ℤ), d.2) - x ∈ H) : H = ⊤ := by
  have e0 : ((1, 3) : ℤ × ℤ) - x ∈ H := hsub _ hold_mem_support_one_three
  have e2 : ((2, 5) : ℤ × ℤ) - x ∈ H := by
    have := hsub _ (hold_mem_support_two 2 le_rfl (by norm_num))
    exact_mod_cast this
  have e4 : ((2, 7) : ℤ × ℤ) - x ∈ H := by
    have := hsub _ (hold_mem_support_two 4 (by norm_num) (by norm_num))
    exact_mod_cast this
  have e5 : ((2, 8) : ℤ × ℤ) - x ∈ H := by
    have := hsub _ (hold_mem_support_two 5 (by norm_num) (by norm_num))
    exact_mod_cast this
  -- differences of support points: (1,2), (1,4), (1,5) ∈ H
  have d2 : ((1, 2) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem e2 e0
    simpa using this
  have d4 : ((1, 4) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem e4 e0
    simpa using this
  have d5 : ((1, 5) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem e5 e0
    simpa using this
  -- standard generators
  have g01 : ((0, 1) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem d5 d4
    simpa using this
  have g02 : ((0, 2) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem d4 d2
    simpa using this
  have g10 : ((1, 0) : ℤ × ℤ) ∈ H := by
    have := H.sub_mem d2 g02
    simpa using this
  rw [AddSubgroup.eq_top_iff']
  intro z
  have hz : z = z.1 • ((1, 0) : ℤ × ℤ) + z.2 • ((0, 1) : ℤ × ℤ) := by
    have h1 : z.1 • ((1, 0) : ℤ × ℤ) = (z.1, 0) := by
      rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul, mul_one, mul_zero]
    have h2 : z.2 • ((0, 1) : ℤ × ℤ) = (0, z.2) := by
      rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul, mul_one, mul_zero]
    rw [h1, h2, Prod.mk_add_mk, add_zero, zero_add]
  rw [hz]
  exact H.add_mem (H.zsmul_mem g10 z.1) (H.zsmul_mem g01 z.2)

end TaoCollatz
