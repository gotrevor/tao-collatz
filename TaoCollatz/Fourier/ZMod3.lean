import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Fourier analysis on `ZMod (3ⁿ)` (node S4)

Paper anchors: Tao 2019 §6, (1.24).

* `eC` — the additive character `e(θ) = exp(2πiθ)`.
* `osc` — the oscillation functional (1.24): the `L¹` deviation of a density from its
  `3ᵐ`-scale conditional average.

`osc` takes the proof `hmn : m ≤ n` as an explicit argument so the `3ᵐ ∣ 3ⁿ` cast is
always well-formed. -- RATIFY: `hmn`-argument form (vs a `min`-guard).
-/

namespace TaoCollatz

/-- The additive character `e(θ) = exp(2πiθ)` on `ℚ` (paper `e(·)`). -/
noncomputable def eC (q : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (q : ℂ))

/-- Oscillation functional (paper (1.24)): the total deviation of `c : ZMod (3ⁿ) → ℝ`
from its average over `3ᵐ`-scale fibers. -/
noncomputable def osc (m n : ℕ) (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) : ℝ :=
  ∑ Y : ZMod (3 ^ n),
    |c Y - (3 : ℝ) ^ ((m : ℤ) - (n : ℤ)) *
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ n) =>
        ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y'
          = ZMod.castHom (pow_dvd_pow 3 hmn) (ZMod (3 ^ m)) Y), c Y'|

end TaoCollatz
