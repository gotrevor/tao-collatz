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

open scoped ENNReal

namespace PMF

variable {α : Type*}

/-- Change of variables for `∑' b, (p.bind f) b * g b` (ℝ≥0∞: no summability side
conditions; Fubini and scalar-pull are unconditional). -/
theorem tsum_bind_mul {β : Type*} (p : PMF α) (f : α → PMF β) (g : β → ℝ≥0∞) :
    ∑' b, (p.bind f) b * g b = ∑' a, p a * ∑' b, f a b * g b := by
  simp only [PMF.bind_apply]
  calc ∑' b, (∑' a, p a * f a b) * g b
      = ∑' b, ∑' a, p a * f a b * g b :=
        tsum_congr fun b => ENNReal.tsum_mul_right.symm
    _ = ∑' a, ∑' b, p a * f a b * g b := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, f a b * g b := tsum_congr fun a => by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun b => mul_assoc _ _ _

/-- Pushforward change of variables: `∑' b, (p.map φ) b * g b = ∑' a, p a * g (φ a)`. -/
theorem tsum_map_mul {β : Type*} (p : PMF α) (φ : α → β) (g : β → ℝ≥0∞) :
    ∑' b, (p.map φ) b * g b = ∑' a, p a * g (φ a) := by
  rw [PMF.map, tsum_bind_mul]
  refine tsum_congr fun a => ?_
  congr 1
  rw [tsum_eq_single (φ a) (fun b hb => by simp [PMF.pure_apply, hb])]
  simp [PMF.pure_apply]

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

/-- Peel one coordinate off an `iid` vector tsum: the head is a fresh `p`-draw, the
tail restarts as `iid n` under `Fin.cons`. -/
theorem tsum_iid_succ_mul (p : PMF α) (n : ℕ) (h : (Fin (n + 1) → α) → ℝ≥0∞) :
    ∑' v : Fin (n + 1) → α, (p.iid (n + 1)) v * h v
      = ∑' a, p a * ∑' w : Fin n → α, (p.iid n) w * h (Fin.cons a w) := by
  rw [show p.iid (n + 1) = p.bind fun a => (p.iid n).map (Fin.cons a) from rfl,
    tsum_bind_mul]
  exact tsum_congr fun a => by rw [tsum_map_mul]

/-- The `iid 0` tsum collapses: the empty vector has full mass. -/
theorem tsum_iid_zero_mul (p : PMF α) (h : (Fin 0 → α) → ℝ≥0∞) :
    ∑' v : Fin 0 → α, (p.iid 0) v * h v = h (fun i => i.elim0) := by
  rw [tsum_eq_single (fun i => i.elim0)
    (fun v hv => absurd (funext fun i => i.elim0) hv)]
  rw [show p.iid 0 = PMF.pure (fun i => i.elim0) from rfl]
  simp [PMF.pure_apply]

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
