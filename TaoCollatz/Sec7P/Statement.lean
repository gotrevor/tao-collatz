/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import TaoCollatz.Sec7P.Bridge

/-!
# §7 at the pair-sum law `Pascal(p)`: the campaign pins (Sec7P)

Tao 2019 §7 bounds the (7.5) damping expectation over `b ~ Pascal^{⌊n/2⌋}`, where
`Pascal` is the law of the sum of two iid `Geom(1/2)` gaps.  This campaign proves the
same bound with the gaps tilted to `Geom(p)`, **uniformly in `p ∈ [1/5, 3/5]`**.  It is
the input node `PascalDampingDecay` of `gotrevor/collatz-moonshot`
(`CollatzMoonshot/Conjugacy/SliceSeven.lean`, branch `ren/conjugacy-ladder`), whose edge
`sliceCharDecay_of_pascalDampingDecay` carries it to slice character decay and on to
`BiasDecays`.

**The definitions below are copied verbatim from that node** (namespace aside), so a
later `require` at a SHA links the two by `rfl`.  They are not composed against the
paper; they are frozen campaign pins like the paper pins, and the differ watches them.

Paper-level transfer (moonshot research note §13): the deterministic half (the phase
field `θ`, Lemma 7.4's triangles, the white points) and Lemma 7.2's `|f(x,3)| = |cos πθ|`
do not involve `p`.  The holding time becomes `(1,3) + Σ_{i<K-1} (1, b'_i)` with
`K ~ Geom(q)`, `q = P(b = 3) = 2p²(1-p)`, mean `(1/q)·(1, 2/p)` (`(4,16)` at `p = 1/2`),
same support, same aperiodicity, exponential tails.  Every slope-sensitive step reduces
to `p·log₂ 3 < 1` (`≤ 0.951` on the window), with Tao's `0.8, 0.9` replaced by thresholds
strictly between `p·log₂ 3` and `1`.

## Pins

* `pascalDamping_half_decay` — the calibration pin: the `p = 1/2` case, which must follow
  from the proved §7 (`key_fourier_decay` / `renewal_white_encounters`) through a
  convention bridge (`fPair`/`xArg`/`pascalWeight` ↔ `fCond`/`xArg`/`pascal`).
* `pascal_damping_decay` — the campaign target, uniform on `p ∈ [1/5, 3/5]`.

The remaining target carries a `warningAsError` shield covering exactly its planted
`sorry`; its discharge removes the `sorry` and shield together.
-/

namespace TaoCollatz.Sec7P

open Filter Topology

/-- `e(−x/3^n)` for `x ∈ ℤ/3^n`. -/
noncomputable def charZ (n : ℕ) (x : ZMod (3 ^ n)) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / 3 ^ n))

/-- Tao's pair factor (7.4): `f(x, b) = (b−1)⁻¹ Σ_{a=1}^{b−1} e(−x(2^a + 3)/3^n)`, the conditional
expectation of the pair's character given its sum `b` (uniform over the `b − 1` splits, for any
gap law `Geom(p)`). -/
noncomputable def fPair (n : ℕ) (x : ZMod (3 ^ n)) (b : ℕ) : ℂ :=
  ((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), charZ n (x * (2 ^ a + 3))

/-- The argument `x_j = ξ · 3^{2j} · 2^{−s}` at prefix pair-sum `s` (0-indexed `j`). -/
noncomputable def xArg (n ξ j s : ℕ) : ZMod (3 ^ n) :=
  (ξ : ZMod (3 ^ n)) * 3 ^ (2 * j) * (2 : ZMod (3 ^ n))⁻¹ ^ s

/-- The pair-sum law `Pascal(p)`: the sum of two iid `Geom(p)` gaps on `{1, 2, …}`,
`P(b) = (b−1) p² (1−p)^{b−2}` for `b ≥ 2`. -/
noncomputable def pascalWeight (p : ℝ) (b : ℕ) : ℝ :=
  if 2 ≤ b then ((b : ℝ) - 1) * p ^ 2 * (1 - p) ^ (b - 2) else 0

/-- **Tao's (7.5) damping at `Pascal(p)`**:
`E_{b ~ Pascal(p)^{⌊n/2⌋}} ∏_j |f(x_j, b_j)|` with `x_j = ξ 3^{2j} 2^{−(b_0 + ⋯ + b_j)}`.
At `p = 1/2` this is the quantity Tao bounds by `n^{−A}` (his Props 7.1, 7.3). -/
noncomputable def pascalDamping (n : ℕ) (p : ℝ) (ξ : ℕ) : ℝ :=
  ∑' b : Fin (n / 2) → ℕ, (∏ j, pascalWeight p (b j)) *
    ∏ j : Fin (n / 2),
      ‖fPair n (xArg n ξ j (∑ i ∈ Finset.univ.filter (fun i : Fin (n / 2) => i ≤ j), b i)) (b j)‖

-- RATIFY-SEC7P-HALF
/-- **CAMPAIGN PIN (calibration).**  The `p = 1/2` case of
`pascal_damping_decay`.  It is Tao's Props 7.1/7.3 in this file's conventions, so it must
follow from the proved §7 (`renewal_white_encounters_at` through `cexpect_pairing` /
`prod_fCond_le_damping`'s chain) plus a convention bridge; it is the gate that proves the
copied definitions mean what the §7 library means. -/
theorem pascalDamping_half_decay :
    ∀ A > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n ξ : ℕ, 1 ≤ n → ¬ 3 ∣ ξ →
      pascalDamping n (1 / 2) ξ ≤ C * (n : ℝ) ^ (-A) := by
  classical
  intro A hA
  refine ⟨TaoCollatz.C_renewalWhite A, TaoCollatz.C_renewalWhite_pos A, ?_⟩
  intro n ξ hn hξ
  have hpair : pascalDamping n (1 / 2) ξ =
      (PMF.iid TaoCollatz.pascal (n / 2)).expect fun b =>
        ∏ j : Fin (n / 2),
          ‖TaoCollatz.fCond n ξ
            (TaoCollatz.xArg n (j : ℕ) (TaoCollatz.pre b ((j : ℕ) + 1))) (b j)‖ := by
    unfold pascalDamping PMF.expect
    apply tsum_congr
    intro b
    rw [PMF.iid_apply_eq_prod, ENNReal.toReal_prod]
    simp_rw [pascalWeight, pascalWeight_half_bridge]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [prefix_filter_eq_pre]
    unfold fPair TaoCollatz.fCond xArg TaoCollatz.xArg charZ
    congr 2
    apply Finset.sum_congr rfl
    intro a ha
    rw [show (ξ : ZMod (3 ^ n)) * 3 ^ (2 * (j : ℕ)) *
        (2 : ZMod (3 ^ n))⁻¹ ^ TaoCollatz.pre b ((j : ℕ) + 1) * (2 ^ a + 3) =
        (ξ : ZMod (3 ^ n)) * (3 ^ (2 * (j : ℕ)) *
          (2 : ZMod (3 ^ n))⁻¹ ^ TaoCollatz.pre b ((j : ℕ) + 1) * (2 ^ a + 3)) by ring]
    exact charZ_argument_bridge n ξ _
  rw [hpair]
  calc
    (PMF.iid TaoCollatz.pascal (n / 2)).expect (fun b =>
        ∏ j : Fin (n / 2),
          ‖TaoCollatz.fCond n ξ
            (TaoCollatz.xArg n (j : ℕ) (TaoCollatz.pre b ((j : ℕ) + 1))) (b j)‖)
      ≤ (PMF.iid TaoCollatz.pascal (n / 2)).expect (fun b =>
          Real.exp (-((TaoCollatz.epsBW : ℝ) ^ 3) *
            ((Finset.univ.filter fun j : Fin (n / 2) =>
              b j = 3 ∧ TaoCollatz.white n ξ (j : ℕ)
                ((TaoCollatz.pre b ((j : ℕ) + 1) : ℤ))).card : ℝ))) := by
        apply TaoCollatz.expect_mono_le
        · intro b
          exact Finset.prod_nonneg fun j _ => norm_nonneg _
        · exact TaoCollatz.prod_fCond_le_damping n ξ
        · intro b
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg (by
            have h : (0 : ℚ) ≤ TaoCollatz.epsBW := by
              unfold TaoCollatz.epsBW
              norm_num
            exact_mod_cast h) 3)) (Nat.cast_nonneg _)
    _ ≤ TaoCollatz.C_renewalWhite A * (n : ℝ) ^ (-A) :=
      TaoCollatz.renewal_white_encounters_at A hA n ξ hξ hn

set_option warningAsError false in
-- RATIFY-SEC7P
/-- ⚠️ **CAMPAIGN PIN — `sorry` until the Sec7P campaign discharges it.**  Tao's damping bound
at `Pascal(p)`, uniformly on `p ∈ [1/5, 3/5]`: the body of `PascalDampingDecay` in
`collatz-moonshot`, verbatim. -/
theorem pascal_damping_decay :
    ∀ A > (0 : ℝ), ∃ C > (0 : ℝ), ∀ p : ℝ, 1 / 5 ≤ p → p ≤ 3 / 5 → ∀ n ξ : ℕ, 1 ≤ n → ¬ 3 ∣ ξ →
      pascalDamping n p ξ ≤ C * (n : ℝ) ^ (-A) := by
  sorry

end TaoCollatz.Sec7P
