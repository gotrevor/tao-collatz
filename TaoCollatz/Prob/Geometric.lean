import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import TaoCollatz.Prob.Basic

/-!
# Geometric / Pascal PMFs and the negative binomial (node S2)

Paper anchors: Tao 2019 Def 1.7, §2.

* `geomHalf` — `Geom(2)`: `P(a) = 2⁻ᵃ`, `a ≥ 1`.
* `geomQuarter` — `Geom(4)`-shaped: `P(a) = 4⁻¹·(3/4)^(a-1)`, `a ≥ 1`.
* `pascal` — law of `a₁+a₂` for two independent `Geom(2)`: `P(b) = (b-1)·2⁻ᵇ`, `b ≥ 2`.
* `pascalNe3` — `pascal` conditioned to avoid `b = 3` (§7 pairing).

All four normalization proofs (`HasSum … 1`) are **proved**: geometric sums for
`geomHalf`/`geomQuarter`; for `pascal` the `∑ n·rⁿ` closed form over ℝ lifted through
`ℝ≥0` to `ℝ≥0∞`; `pascalNe3` by splitting off the `b = 3` atom.

-- RATIFY-DRIFT: `pascal`/`pascalNe3` spell the coefficient `((b - 1 : ℕ) : ℝ≥0∞)`
-- (ℕ-subtraction, then cast) rather than the spec's ambiguous `(b - 1)` (which Lean
-- would read as ENNReal truncated subtraction `↑b - 1`). The two agree for every
-- unmasked `b ≥ 2`, so the mathematical content is identical.
-/

open scoped ENNReal NNReal

namespace TaoCollatz

/-- Reindex a `∑'` over ℕ whose zeroth term is suppressed to a shifted `∑'`. -/
theorem tsum_ite_zero_eq_succ (g : ℕ → ℝ≥0∞) :
    ∑' a : ℕ, (if a = 0 then 0 else g a) = ∑' n : ℕ, g (n + 1) := by
  rw [tsum_eq_zero_add' ENNReal.summable]; simp

/-- `Geom(2)`: `P(a) = 2⁻ᵃ` for `a ≥ 1` (paper Def 1.7). -/
noncomputable def geomHalf : PMF ℕ :=
  ⟨fun a => if a = 0 then 0 else 2⁻¹ ^ a, by
    have h : ∑' a : ℕ, (if a = 0 then (0 : ℝ≥0∞) else 2⁻¹ ^ a) = 1 := by
      rw [tsum_ite_zero_eq_succ (fun a => (2⁻¹ : ℝ≥0∞) ^ a),
        ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv,
        ENNReal.inv_mul_cancel (by norm_num) (by finiteness)]
    rw [← h]; exact ENNReal.summable.hasSum⟩

/-- `Geom(4)`-shaped law: `P(a) = 4⁻¹·(3/4)^(a-1)` for `a ≥ 1`. -/
noncomputable def geomQuarter : PMF ℕ :=
  ⟨fun a => if a = 0 then 0 else 4⁻¹ * (3 * 4⁻¹) ^ (a - 1), by
    have h : ∑' a : ℕ, (if a = 0 then (0 : ℝ≥0∞) else 4⁻¹ * (3 * 4⁻¹) ^ (a - 1)) = 1 := by
      rw [tsum_ite_zero_eq_succ (fun a => (4⁻¹ : ℝ≥0∞) * (3 * 4⁻¹) ^ (a - 1))]
      simp only [Nat.add_sub_cancel]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      have hden : (1 : ℝ≥0∞) - 3 * 4⁻¹ = 4⁻¹ := by
        apply ENNReal.sub_eq_of_eq_add (by finiteness)
        rw [show (4⁻¹ : ℝ≥0∞) + 3 * 4⁻¹ = (1 + 3) * 4⁻¹ from by ring,
          show (1 : ℝ≥0∞) + 3 = 4 from by norm_num,
          ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]
      rw [hden, inv_inv, ENNReal.inv_mul_cancel (by norm_num) (by finiteness)]
    rw [← h]; exact ENNReal.summable.hasSum⟩

/-- Pointwise real mass of `geomQuarter`: `4⁻¹·(3/4)^(a-1)` for `a ≥ 1`. -/
theorem geomQuarter_toReal (k : ℕ) :
    (geomQuarter k).toReal = if k = 0 then 0 else 4⁻¹ * (3 / 4 : ℝ) ^ (k - 1) := by
  have h : geomQuarter k
      = if k = 0 then (0 : ℝ≥0∞) else 4⁻¹ * (3 * 4⁻¹) ^ (k - 1) := rfl
  rw [h]
  split_ifs with h0
  · simp
  · rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_mul,
      ENNReal.toReal_inv]
    norm_num

/-- `geomQuarter` real masses sum to `1`. -/
theorem geomQuarter_tsum_toReal : ∑' k : ℕ, (geomQuarter k).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun k => geomQuarter.apply_ne_top k),
    geomQuarter.tsum_coe, ENNReal.toReal_one]

/-- `fun k => (geomQuarter k).toReal` is summable. -/
theorem geomQuarter_summable_toReal : Summable fun k : ℕ => (geomQuarter k).toReal :=
  ENNReal.summable_toReal geomQuarter.tsum_coe_ne_top

/-- Exact geometric tail: the `geomQuarter` mass beyond `t` is `(3/4)^t`. -/
theorem geomQuarter_tail (t : ℕ) :
    ∑' k : ℕ, (if t < k then (geomQuarter k).toReal else 0) = (3 / 4 : ℝ) ^ t := by
  have hinj : Function.Injective (fun i : ℕ => t + 1 + i) := add_right_injective (t + 1)
  have hzero : ∀ k ∉ Set.range (fun i : ℕ => t + 1 + i),
      (if t < k then (geomQuarter k).toReal else 0) = 0 := by
    intro k hk
    have hlt : ¬ t < k := fun h => hk ⟨k - (t + 1), by show t + 1 + (k - (t + 1)) = k; omega⟩
    rw [if_neg hlt]
  have heq : ((fun k => if t < k then (geomQuarter k).toReal else 0)
        ∘ (fun i : ℕ => t + 1 + i))
      = fun i : ℕ => (4⁻¹ * (3 / 4 : ℝ) ^ t) * (3 / 4 : ℝ) ^ i := by
    funext i
    simp only [Function.comp]
    rw [if_pos (by omega : t < t + 1 + i), geomQuarter_toReal,
      if_neg (by omega : ¬ t + 1 + i = 0),
      show t + 1 + i - 1 = t + i from by omega, pow_add]
    ring
  have hgeo : HasSum (fun i : ℕ => (3 / 4 : ℝ) ^ i) 4 := by
    have h := hasSum_geometric_of_lt_one (r := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hcomp : HasSum ((fun k => if t < k then (geomQuarter k).toReal else 0)
      ∘ (fun i : ℕ => t + 1 + i)) ((3 / 4 : ℝ) ^ t) := by
    rw [heq]
    have h := hgeo.mul_left (4⁻¹ * (3 / 4 : ℝ) ^ t)
    have hval : 4⁻¹ * (3 / 4 : ℝ) ^ t * 4 = (3 / 4 : ℝ) ^ t := by ring
    rwa [hval] at h
  exact ((hinj.hasSum_iff hzero).mp hcomp).tsum_eq

/-- Real-valued normalization for `pascal`: `∑_{b≥2} (b-1)·2⁻ᵇ = 1` over ℝ, from the
`∑ n·rⁿ = r/(1-r)²` closed form. -/
theorem pascalR_hasSum :
    HasSum (fun b : ℕ => if b < 2 then (0 : ℝ) else ((b - 1 : ℕ) : ℝ) * 2⁻¹ ^ b) 1 := by
  have hg : HasSum (fun n : ℕ => (n : ℝ) * 2⁻¹ ^ n) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 2⁻¹) (by
      rw [Real.norm_eq_abs]; norm_num)
    have hval : (2⁻¹ / (1 - 2⁻¹) ^ 2 : ℝ) = 2 := by norm_num
    rwa [hval] at h
  have hgeo : HasSum (fun n : ℕ => (2⁻¹ : ℝ) ^ n) 2 := by
    have h := hasSum_geometric_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)
    have hval : ((1 - 2⁻¹)⁻¹ : ℝ) = 2 := by norm_num
    rwa [hval] at h
  have he : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 0 1
  have hsum := (hg.sub hgeo).add he
  have hval : (2 : ℝ) - 2 + 1 = 1 := by norm_num
  rw [hval] at hsum
  have hfun : (fun b : ℕ => ((b : ℝ) * 2⁻¹ ^ b - 2⁻¹ ^ b) + if b = 0 then (1 : ℝ) else 0)
      = (fun b : ℕ => if b < 2 then (0 : ℝ) else ((b - 1 : ℕ) : ℝ) * 2⁻¹ ^ b) := by
    funext b
    match b with
    | 0 => norm_num
    | 1 => norm_num
    | (n + 2) =>
      have h2 : ¬ (n + 2 < 2) := by omega
      have h0 : ¬ (n + 2 = 0) := by omega
      simp only [if_neg h2, if_neg h0, add_zero]
      push_cast
      ring
  rwa [hfun] at hsum

/-- The `pascal` mass function is a probability distribution (lift of `pascalR_hasSum`
through `ℝ≥0` to `ℝ≥0∞`). -/
theorem pascalFun_hasSum :
    HasSum (fun b : ℕ => if b < 2 then (0 : ℝ≥0∞) else ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b) 1 := by
  set fnn : ℕ → ℝ≥0 := fun b => if b < 2 then 0 else ((b - 1 : ℕ) : ℝ≥0) * 2⁻¹ ^ b with hfnn
  have hR : HasSum (fun b => (fnn b : ℝ)) ((1 : ℝ≥0) : ℝ) := by
    have hfun : (fun b => (fnn b : ℝ))
        = (fun b : ℕ => if b < 2 then (0 : ℝ) else ((b - 1 : ℕ) : ℝ) * 2⁻¹ ^ b) := by
      funext b
      simp only [hfnn]
      by_cases hb : b < 2
      · rw [if_pos hb, if_pos hb, NNReal.coe_zero]
      · rw [if_neg hb, if_neg hb, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv,
          NNReal.coe_natCast, NNReal.coe_ofNat]
    rw [hfun]; push_cast; exact pascalR_hasSum
  have hNN : HasSum fnn 1 := NNReal.hasSum_coe.mp hR
  have hEN : HasSum (fun b => ((fnn b : ℝ≥0∞))) ((1 : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.hasSum_coe.mpr hNN
  have hfun2 : (fun b => ((fnn b : ℝ≥0∞)))
      = (fun b : ℕ => if b < 2 then (0 : ℝ≥0∞) else ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b) := by
    funext b
    simp only [hfnn]
    by_cases hb : b < 2
    · rw [if_pos hb, if_pos hb, ENNReal.coe_zero]
    · rw [if_neg hb, if_neg hb, ENNReal.coe_mul, ENNReal.coe_pow,
        ENNReal.coe_inv (by norm_num), ENNReal.coe_natCast, ENNReal.coe_ofNat]
  rw [hfun2] at hEN
  simpa using hEN

/-- `Pascal`: law of `a₁+a₂` for two iid `Geom(2)`; `P(b) = (b-1)·2⁻ᵇ` for `b ≥ 2`. -/
noncomputable def pascal : PMF ℕ :=
  ⟨fun b => if b < 2 then 0 else ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b, pascalFun_hasSum⟩

/-- The `pascalNe3` mass function is a probability distribution: split off the `b = 3`
atom (mass `4⁻¹`) from `pascal` and reweight by `4/3`. -/
theorem pascalNe3Fun_hasSum :
    HasSum (fun b : ℕ => if b < 2 ∨ b = 3 then (0 : ℝ≥0∞)
      else (4 / 3) * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b)) 1 := by
  set f : ℕ → ℝ≥0∞ := fun b => if b < 2 then 0 else ((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b with hf
  have hf1 : ∑' b, f b = 1 := pascalFun_hasSum.tsum_eq
  have hsplit : ∑' b, f b = f 3 + ∑' b, if b = 3 then 0 else f b := by
    have h := ENNReal.tsum_eq_add_tsum_ite (f := f) 3
    convert h using 4 with x
    by_cases hx : x = 3 <;> simp [hx]
  have hf3 : f 3 = 4⁻¹ := by
    simp only [hf]
    rw [if_neg (by omega), show ((3 - 1 : ℕ) : ℝ≥0∞) = 2 by norm_num, pow_succ',
      ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul,
      ← ENNReal.inv_pow]
    norm_num
  have hone : (4⁻¹ : ℝ≥0∞) + 3 * 4⁻¹ = 1 := by
    rw [show (4⁻¹ : ℝ≥0∞) + 3 * 4⁻¹ = (1 + 3) * 4⁻¹ from by ring,
      show (1 : ℝ≥0∞) + 3 = 4 from by norm_num,
      ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]
  have hS : ∑' b, (if b = 3 then 0 else f b) = 3 * 4⁻¹ := by
    have h1 : f 3 + ∑' b, (if b = 3 then 0 else f b) = f 3 + 3 * 4⁻¹ := by
      rw [← hsplit, hf1, hf3, hone]
    exact (ENNReal.add_right_inj (by rw [hf3]; finiteness)).mp h1
  have hg : (fun b : ℕ => if b < 2 ∨ b = 3 then (0 : ℝ≥0∞)
        else (4 / 3) * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b))
      = fun b => (4 / 3) * (if b = 3 then 0 else f b) := by
    funext b
    simp only [hf]
    by_cases hb3 : b = 3
    · subst hb3; norm_num
    · by_cases hb2 : b < 2
      · simp [hb2, hb3]
      · simp [hb2, hb3]
  rw [hg]
  have hval : ∑' b, (4 / 3 : ℝ≥0∞) * (if b = 3 then 0 else f b) = 1 := by
    rw [ENNReal.tsum_mul_left, hS, div_eq_mul_inv,
      show (4 : ℝ≥0∞) * 3⁻¹ * (3 * 4⁻¹) = (4 * 4⁻¹) * (3⁻¹ * 3) from by ring,
      ENNReal.mul_inv_cancel (by norm_num) (by finiteness),
      ENNReal.inv_mul_cancel (by norm_num) (by finiteness), one_mul]
  rw [← hval]
  exact ENNReal.summable.hasSum

/-- `Pascal` conditioned to avoid `b = 3` (§7 pairing); reweighted by `4/3`. -/
noncomputable def pascalNe3 : PMF ℕ :=
  ⟨fun b => if b < 2 ∨ b = 3 then 0 else (4 / 3) * (((b - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ b),
    pascalNe3Fun_hasSum⟩

/-- Definitional bridge: `pascal` is the pushforward of `geomHalf.iid 2` under summation
of the two coordinates. -/
theorem pascal_eq_map_iid :
    pascal = (PMF.iid geomHalf 2).map (fun v => v 0 + v 1) := by
  sorry

/-- Negative binomial exact point mass (paper §2): the law of the total `|Geom(2)ⁿ|`
puts mass `(L-1).choose (n-1)·2⁻ᴸ` at `L`, for `L, n ≥ 1`. -/
theorem negBinomial_apply (n L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    ((PMF.iid geomHalf n).map (fun v => ∑ i, v i)) L
      = (L - 1).choose (n - 1) * 2⁻¹ ^ L := by
  sorry

end TaoCollatz
