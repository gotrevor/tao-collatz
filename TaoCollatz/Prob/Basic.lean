import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# PMF calculus: total variation, expectations, iid vectors (node S1)

Paper anchors: Tao 2019 §1.4, (1.9), (1.10). Design decision D1: all probability is
`PMF` + `tsum`; expectations are `∑' a, (p a).toReal • f a`, total variation is
`∑' a, |(p a).toReal - (q a).toReal|`. No measure theory.

Proved here: `dTV_comm`, `dTV_nonneg`. Paper (1.10) (indicator/expectation form) is
stated with `sorry`.
-/

namespace PMF

variable {α : Type*}

/-- Total variation distance (D1 form): `∑' a, |p a − q a|` over reals. -/
noncomputable def dTV (p q : PMF α) : ℝ := ∑' a, |(p a).toReal - (q a).toReal|

/-- Expectation of a real observable `f` under `p` (D1 form). -/
noncomputable def expect (p : PMF α) (f : α → ℝ) : ℝ := ∑' a, (p a).toReal * f a

/-- Expectation of a complex observable `f` under `p` (for character sums). -/
noncomputable def cexpect (p : PMF α) (f : α → ℂ) : ℂ := ∑' a, ((p a).toReal : ℂ) * f a

/-- The `n`-fold iid product of `p`, as a `PMF (Fin n → α)`. -/
noncomputable def iid (p : PMF α) : (n : ℕ) → PMF (Fin n → α)
  | 0 => PMF.pure (fun i => i.elim0)
  | n + 1 => p.bind fun a => (iid p n).map (Fin.cons a)

/-- Total variation is symmetric. -/
theorem dTV_comm (p q : PMF α) : dTV p q = dTV q p := by
  unfold dTV
  exact tsum_congr fun _ => abs_sub_comm _ _

/-- Total variation is nonnegative. -/
theorem dTV_nonneg (p q : PMF α) : 0 ≤ dTV p q :=
  tsum_nonneg fun _ => abs_nonneg _

/-- Paper (1.10), indicator/expectation form: the difference of event probabilities
under `p` and `q` is controlled by their total variation. -/
theorem abs_expect_indicator_sub_le_dTV (p q : PMF α) (E : Set α) :
    |p.expect (Set.indicator E 1) - q.expect (Set.indicator E 1)| ≤ p.dTV q := by
  sorry

end PMF
