import TaoCollatz.Sec6.MixingCore

/-! The bad-event/error branch of the §6 conditioning proof. -/

open scoped BigOperators

namespace TaoCollatz

/-- **Obligation 1 (error term)**: the `L¹` mass of `syracZ − mainHigh` is polynomially small. This
is Tao (6.3), `P(Ē) ≤ n^{-A-1}`, plus the (6.4) event enlargements `E → Eₖ`: the events `E`/`Eₖ`/`Bₖ`
partition the good event, so the difference is the mass on the bad event, controlled by the §7/S3
sub-Gaussian tails (Lemma 2.2 + union bound). -/
theorem error_l1_high_bound (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, m ≤ n → n₀ ≤ n → 9 * n ≤ 10 * m →
      2 * ∑ Y, |(syracZ n Y).toReal - mainHigh A n Y| ≤ C * (m : ℝ) ^ (-A) := by
  sorry

end TaoCollatz
