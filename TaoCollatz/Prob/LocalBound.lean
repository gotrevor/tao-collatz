import TaoCollatz.Prob.Geometric

/-!
# Lemma 2.2: local 2-D Gaussian-type bounds (node S3)

Paper anchors: Tao 2019, (2.2) p.14 (the Gaussian-type weights `G_n`), Lemma 2.2
(Chernoff type bound) pp.14–16, instantiated per design decision D5 at the four
distributions the argument consumes — `Geom(2)` (= `geomHalf`), `Geom(4)`-shaped
(= `geomQuarter`), `Pascal` (= `pascal`), and (in `Sec7/Unroll.lean`, where `hold`
lives) the 2-D `Hold` walk. The paper proves Lemma 2.2 for a general nondegenerate
`v : Zᵈ` with exponential tails via complexified MGF + contour shifting; per D5 we
avoid contour integration and will prove each instance by exponential tilting plus
the finite (`ZMod`) circle method, using the exact point masses available here
(`negBinomial_apply` for `Geom(2)` sums).

* `Gweight t x = exp(-x²/t) + exp(-|x|)` — paper (2.2), factored here from
  `Sec7/Unroll.lean` (Lemma 7.7 consumes it).
* `iidSum p n` — the law of `p`-iid `v₁ + ⋯ + vₙ` (paper `v_{[1,n]}`, (1.6)).
* `*_local_bound` — Lemma 2.2(i) at each d=1 distribution.
* `*_tail_bound` — Lemma 2.2(ii) at each d=1 distribution.

-- RATIFY-DRIFT (G-weight index): the paper's display uses `G_n`; we state every
-- bound with `Gweight (1 + n)`. Since `Gweight` is antitone in `x²/t`,
-- `G_n(x) ≤ G_{1+n}(x)` pointwise, so our conclusions are (very slightly) weaker
-- upper bounds, still of Gaussian type at the same scale — and this is exactly the
-- form Lemma 7.7 (`fpDist_location_bound`) consumes. It also sidesteps Lean's
-- `x/0 = 0` convention, under which `Gweight 0 x = 1 + exp(-|x|)` would NOT be the
-- paper's `G_0(x) = exp(-|x|)` (paper convention `exp(-∞) = 0`). The `n = 0` cases
-- are trivial point masses either way.
-- RATIFY-DRIFT (index set): sums of our ℕ-valued variables are stated over `L : ℕ`;
-- the paper's `L ∈ ℤ` adds only zero-mass points (all masses vanish for `L < n`).
-- Means: `geomHalf` has mean 2 (paper: `E|Geom(2)| = 2`, §1.4), `geomQuarter` and
-- `pascal` have mean 4 (§7.3; `pascal = Geom(2) + Geom(2)`).
-/

open scoped ENNReal

namespace TaoCollatz

/-- The Gaussian-type weight `G_t(x) = exp(-x²/t) + exp(-|x|)` (paper (2.2)). -/
noncomputable def Gweight (t x : ℝ) : ℝ := Real.exp (-(x ^ 2) / t) + Real.exp (-|x|)

theorem Gweight_pos (t x : ℝ) : 0 < Gweight t x :=
  add_pos (Real.exp_pos _) (Real.exp_pos _)

theorem Gweight_nonneg (t x : ℝ) : 0 ≤ Gweight t x := (Gweight_pos t x).le

theorem Gweight_le_two (t x : ℝ) (ht : 0 ≤ t) : Gweight t x ≤ 2 := by
  have h1 : Real.exp (-(x ^ 2) / t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, div_zero]
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) ht |>.trans_eq rfl
  have h2 : Real.exp (-|x|) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))
  calc Gweight t x ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

variable {M : Type*} [AddCommMonoid M]

/-- The law of the sum `v₁ + ⋯ + vₙ` of `n` iid copies of `p` (paper `v_{[1,n]}`),
for `p` on any additive commutative monoid (ℕ for the d=1 instances, `ℕ × ℤ` for
the `Hold` walk). -/
noncomputable def iidSum (p : PMF M) (n : ℕ) : PMF M :=
  (p.iid n).map fun v => ∑ i, v i

theorem iidSum_zero (p : PMF M) : iidSum p 0 = PMF.pure 0 := by
  rw [iidSum, show p.iid 0 = PMF.pure (fun i : Fin 0 => i.elim0) from rfl,
    PMF.pure_map]
  simp

/-- Peel the head draw off an iid sum: `S_{n+1} = a + S_n` in law. -/
theorem iidSum_succ (p : PMF M) (n : ℕ) :
    iidSum p (n + 1) = p.bind fun a => (iidSum p n).map (a + ·) := by
  rw [iidSum, show p.iid (n + 1) = p.bind fun a => (p.iid n).map (Fin.cons a) from rfl,
    PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [PMF.map_comp, iidSum, PMF.map_comp]
  have hf : ((fun v : Fin (n + 1) → M => ∑ i, v i) ∘ Fin.cons a)
      = ((a + ·) ∘ fun w : Fin n → M => ∑ i, w i) := by
    funext w
    simp only [Function.comp_apply]
    rw [Fin.sum_cons]
  rw [hf]

/-- Renewal additivity of iid sums: `S_{k+n} = S_k + S'_n` with the two blocks
independent. -/
theorem iidSum_add (p : PMF M) (k n : ℕ) :
    iidSum p (k + n) = (iidSum p k).bind fun s => (iidSum p n).map (s + ·) := by
  induction k with
  | zero =>
    rw [Nat.zero_add, iidSum_zero, PMF.pure_bind]
    have h : (fun x : M => (0 : M) + x) = id := funext fun x => zero_add x
    rw [h, PMF.map_id]
  | succ k IH =>
    rw [show k + 1 + n = (k + n) + 1 from by omega, iidSum_succ, iidSum_succ,
      PMF.bind_bind]
    refine congrArg _ (funext fun a => ?_)
    rw [IH, PMF.map_bind, PMF.bind_map]
    refine congrArg _ (funext fun s => ?_)
    simp only [Function.comp_apply]
    rw [PMF.map_comp]
    have hf : ((a + ·) ∘ (s + ·)) = ((a + s) + ·) := by
      funext x
      simp only [Function.comp_apply]
      rw [add_assoc]
    rw [hf]

/-- Iterated iid sums flatten: `n` iid copies of `S_k` sum to `S_{nk}`. -/
theorem iidSum_iidSum (p : PMF M) (k n : ℕ) :
    iidSum (iidSum p k) n = iidSum p (n * k) := by
  induction n with
  | zero => rw [Nat.zero_mul, iidSum_zero, iidSum_zero]
  | succ n IH =>
    rw [iidSum_succ, show (n + 1) * k = k + n * k from by ring, iidSum_add]
    refine congrArg _ (funext fun s => ?_)
    rw [IH]

/-- Additive pushforward commutes with iid sums (circle-method entry: apply with
`φ = mod-N reduction` to turn a lattice local mass into a finite-group mass). -/
theorem iidSum_map (p : PMF M) {M' : Type*} [AddCommMonoid M'] (φ : M → M')
    (hφ0 : φ 0 = 0) (hφ : ∀ a b, φ (a + b) = φ a + φ b) (n : ℕ) :
    (iidSum p n).map φ = iidSum (p.map φ) n := by
  induction n with
  | zero => rw [iidSum_zero, iidSum_zero, PMF.pure_map, hφ0]
  | succ n IH =>
    rw [iidSum_succ, iidSum_succ, PMF.map_bind, PMF.bind_map]
    refine congrArg _ (funext fun a => ?_)
    simp only [Function.comp_apply]
    rw [PMF.map_comp, ← IH, PMF.map_comp]
    have hf : (φ ∘ (a + ·)) = ((φ a + ·) ∘ φ) := by
      funext x
      simp only [Function.comp_apply]
      rw [hφ]
    rw [hf]

/-- `pascal` is the two-fold iid `Geom(2)` sum. -/
theorem pascal_eq_iidSum : pascal = iidSum geomHalf 2 := by
  rw [pascal_eq_map_iid, iidSum]
  have hf : (fun v : Fin 2 → ℕ => v 0 + v 1) = fun v : Fin 2 → ℕ => ∑ i, v i := by
    funext v
    rw [Fin.sum_univ_two]
  rw [hf]

/-- Exact point mass for iid `pascal` sums: the law of `|Geom(2)_{2n}|`
(paper §2 via `negBinomial_apply`; the leaf `pascal_local_bound` runs on this). -/
theorem iidSum_pascal_apply (n L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (iidSum pascal n) L = (L - 1).choose (2 * n - 1) * 2⁻¹ ^ L := by
  rw [pascal_eq_iidSum, iidSum_iidSum, show n * 2 = 2 * n from by ring]
  exact negBinomial_apply (2 * n) L (by omega) hL

/-- **Lemma 2.2(i) for `Geom(2)`** (paper p.15, displayed instance):
`P(|Geom(2)_n| = L) ≪ (n+1)^{-1/2} · G_n(c(L − 2n))`. -/
theorem geomHalf_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum geomHalf n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - 2 * n)) := by
  sorry

/-- **Lemma 2.2(ii) for `Geom(2)`** (paper p.15, displayed instance):
`P(||Geom(2)_n| − 2n| ≥ λ) ≪ G_n(cλ)`. -/
theorem geomHalf_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 2 * n| then ((iidSum geomHalf n) L).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  sorry

/-- **Lemma 2.2(i) for `Geom(4)`-shaped `geomQuarter`** (mean 4; §7.3 consumes this
through `Hold`'s first coordinate). -/
theorem geomQuarter_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum geomQuarter n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - 4 * n)) := by
  sorry

/-- **Lemma 2.2(ii) for `geomQuarter`**. -/
theorem geomQuarter_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 4 * n| then ((iidSum geomQuarter n) L).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  sorry

/-- **Lemma 2.2(i) for `Pascal`** (mean 4). Via `pascal_eq_map_iid`, `iidSum pascal n`
is the law of `|Geom(2)_{2n}|`, so this reduces to the exact negative-binomial point
mass `C(L-1, 2n-1)·2^{-L}` (`negBinomial_apply`) plus Stirling-type estimates. -/
theorem pascal_local_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n L : ℕ),
      ((iidSum pascal n) L).toReal
        ≤ C / Real.sqrt (1 + n) * Gweight (1 + n) (c * ((L : ℝ) - 4 * n)) := by
  sorry

/-- **Lemma 2.2(ii) for `Pascal`**. -/
theorem pascal_tail_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (lam : ℝ), 0 ≤ lam →
      (∑' L : ℕ, if lam ≤ |(L : ℝ) - 4 * n| then ((iidSum pascal n) L).toReal else 0)
        ≤ C * Gweight (1 + n) (c * lam) := by
  sorry

end TaoCollatz
