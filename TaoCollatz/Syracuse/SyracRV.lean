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

/-- Paper (1.21) bridge: the reversed form agrees in law with the `fnat`-based offset
form `a ↦ (Fnat n a) · 2⁻⁽ᵃ¹⁺⋯⁺ᵃⁿ⁾` in `ZMod (3ⁿ)`. -/
theorem syracZ_eq_rev_fnat (n : ℕ) :
    syracZ n
      = (PMF.iid geomHalf n).map
          (fun a => (fnat n a : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ pre a n) := by
  sorry

end TaoCollatz
