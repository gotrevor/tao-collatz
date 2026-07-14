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

/-- `toReal` bridge for a PMF-weighted `ofReal` tsum (no side conditions beyond
pointwise nonnegativity: every term is finite). -/
theorem toReal_tsum_mul_ofReal (p : PMF α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑' x, p x * ENNReal.ofReal (f x)).toReal = ∑' x, (p x).toReal * f x := by
  rw [ENNReal.tsum_toReal_eq
    (fun x => ENNReal.mul_ne_top (p.apply_ne_top x) ENNReal.ofReal_ne_top)]
  exact tsum_congr fun x => by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf x)]

/-- PMF-weighted `ofReal` sums of `≤ 1` observables are `≤ 1`. -/
theorem tsum_mul_ofReal_le_one (p : PMF α) (f : α → ℝ) (hf : ∀ x, f x ≤ 1) :
    ∑' x, p x * ENNReal.ofReal (f x) ≤ 1 := by
  calc ∑' x, p x * ENNReal.ofReal (f x)
      ≤ ∑' x, p x * 1 :=
        ENNReal.tsum_le_tsum fun x =>
          mul_le_mul_left' (ENNReal.ofReal_le_one.mpr (hf x)) _
    _ = 1 := by rw [tsum_congr fun x => mul_one (p x), p.tsum_coe]

/-- The empty iid vector carries full mass: expectations collapse. -/
theorem expect_iid_zero (p : PMF α) (h : (Fin 0 → α) → ℝ) :
    (p.iid 0).expect h = h (fun i => i.elim0) := by
  show ∑' v : Fin 0 → α, ((p.iid 0) v).toReal * h v = _
  rw [tsum_eq_single (fun i : Fin 0 => i.elim0)
    (fun v hv => absurd (funext fun i => i.elim0) hv)]
  rw [show p.iid 0 = PMF.pure (fun i => i.elim0) from rfl]
  simp [PMF.pure_apply]

/-- Peel one coordinate off an iid expectation of a `[0,1]`-valued observable. -/
theorem expect_iid_succ (p : PMF α) (n : ℕ) (h : (Fin (n + 1) → α) → ℝ)
    (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1) :
    (p.iid (n + 1)).expect h
      = ∑' a : α, (p a).toReal * (p.iid n).expect fun w => h (Fin.cons a w) := by
  show ∑' v : Fin (n + 1) → α, ((p.iid (n + 1)) v).toReal * h v = _
  rw [← toReal_tsum_mul_ofReal (p.iid (n + 1)) h h0,
    tsum_iid_succ_mul p n (fun v => ENNReal.ofReal (h v)),
    ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top (p.apply_ne_top a)
      (ne_top_of_le_ne_top (by simp)
        (tsum_mul_ofReal_le_one (p.iid n) _ (fun w => h1 _))))]
  refine tsum_congr fun a => ?_
  rw [ENNReal.toReal_mul, toReal_tsum_mul_ofReal (p.iid n) _ (fun w => h0 _)]
  rfl

/-- Pushforward can only merge mass: `p a ≤ (p.map f) (f a)`. With `f = mod-N
reduction` this is the free truncation step of the finite circle method. -/
theorem apply_le_map_apply {β : Type*} (p : PMF α) (f : α → β) (a : α) :
    p a ≤ (p.map f) (f a) := by
  classical
  rw [PMF.map_apply]
  calc p a = if f a = f a then p a else 0 := by rw [if_pos rfl]
    _ ≤ ∑' a', if f a = f a' then p a' else 0 := ENNReal.le_tsum a

/-- Every coordinate of a vector in the support of `p.iid n` lies in `p.support`. -/
theorem iid_support_coord (p : PMF α) :
    ∀ (n : ℕ) (v : Fin n → α), v ∈ (p.iid n).support → ∀ i, v i ∈ p.support := by
  intro n
  induction n with
  | zero => intro v _ i; exact i.elim0
  | succ n IH =>
    intro v hv i
    rw [show p.iid (n + 1) = p.bind fun a => (p.iid n).map (Fin.cons a) from rfl,
      PMF.mem_support_bind_iff] at hv
    obtain ⟨a, ha, hv⟩ := hv
    rw [PMF.mem_support_map_iff] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using IH w hw j

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
  have hp : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)
  have hq : Summable fun a => (q a).toReal :=
    ENNReal.summable_toReal (by rw [q.tsum_coe]; exact ENNReal.one_ne_top)
  have hnn : ∀ (r : PMF α) (a : α), 0 ≤ (r a).toReal * Set.indicator E 1 a := fun r a =>
    mul_nonneg ENNReal.toReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) a)
  have hle : ∀ (r : PMF α) (a : α), (r a).toReal * Set.indicator E 1 a ≤ (r a).toReal := by
    intro r a
    by_cases h : a ∈ E
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h, ENNReal.toReal_nonneg]
  have hpE : Summable fun a => (p a).toReal * Set.indicator E 1 a :=
    Summable.of_nonneg_of_le (hnn p) (hle p) hp
  have hqE : Summable fun a => (q a).toReal * Set.indicator E 1 a :=
    Summable.of_nonneg_of_le (hnn q) (hle q) hq
  have hkey : ∀ a,
      |(p a).toReal * Set.indicator E 1 a - (q a).toReal * Set.indicator E 1 a|
        ≤ |(p a).toReal - (q a).toReal| := by
    intro a
    rw [← sub_mul, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    by_cases h : a ∈ E
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  unfold expect dTV
  rw [← hpE.tsum_sub hqE]
  calc |∑' a, ((p a).toReal * Set.indicator E 1 a - (q a).toReal * Set.indicator E 1 a)|
      ≤ ∑' a, |(p a).toReal * Set.indicator E 1 a - (q a).toReal * Set.indicator E 1 a| := by
        have h := norm_tsum_le_tsum_norm
          (f := fun a => (p a).toReal * Set.indicator E 1 a
            - (q a).toReal * Set.indicator E 1 a)
          (by simpa only [Real.norm_eq_abs] using (hpE.sub hqE).abs)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∑' a, |(p a).toReal - (q a).toReal| :=
        ((hpE.sub hqE).abs).tsum_le_tsum hkey ((hp.sub hq).abs)

/-- The pointwise mass of an iid vector factorizes as the product of coordinate masses. -/
theorem iid_apply_eq_prod (p : PMF α) (n : Nat) (v : Fin n → α) :
    p.iid n v = ∏ i, p (v i) := by
  classical
  induction n with
  | zero =>
      have hv : v = fun i : Fin 0 => i.elim0 := by
        funext i
        exact i.elim0
      subst v
      rw [show p.iid 0 = PMF.pure (fun i : Fin 0 => i.elim0) from rfl]
      simp [PMF.pure_apply]
  | succ n ih =>
      rw [show p.iid (n + 1) = p.bind fun a => (p.iid n).map (Fin.cons a) from rfl,
        PMF.bind_apply]
      rw [tsum_eq_single (v 0)]
      · rw [PMF.map_apply]
        rw [tsum_eq_single (Fin.tail v)]
        · rw [if_pos (Fin.cons_self_tail v).symm, ih, Fin.prod_univ_succ]
          congr 1
        · intro w hw
          rw [if_neg]
          intro heq
          apply hw
          funext j
          exact (congrFun heq j.succ).symm
      · intro a ha
        rw [PMF.map_apply]
        rw [mul_eq_zero]
        right
        apply ENNReal.tsum_eq_zero.mpr
        intro w
        rw [if_neg]
        intro heq
        apply ha
        exact (congrFun heq 0).symm

end PMF
