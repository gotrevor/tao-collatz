-- Full Mathlib, not slices: `Challenge.lean` re-declares `cTao`/`tenTower`/`CTao` under
-- `import Mathlib`, and comparator demands *identical* elaborations, not defeq ones — a
-- narrower import set here can pick a different instance path and fail the harness with
-- "Const does not match" (see the comparator-harness recipe's №1 gotcha).
import Mathlib

/-!
# Explicit constants: the exponent `cTao` and the `tenTower` vocabulary

A Mathlib-only leaf (no TaoCollatz imports): the concrete exponent `cTao` and the
tower-of-tens vocabulary behind the concrete constant `CTao` (defined in
`Statement.lean`, the trusted surface, as Mathlib's `hyperoperation 4 10 63`; the
`tenTower` calculus here feeds the ceiling proof in `BigCTower.lean` and connects via
`tenTower_sixty_two_eq_hyperoperation`).  This file sits below the whole development so
the trusted surface and the proof engine share one definition.

The tower uses real powers, so even very large heights remain symbolic: Lean never
expands an astronomical natural numeral.
-/

namespace TaoCollatz

/-- The explicit exponent — OUR augmentation, beyond the paper: the collapse of the
development's witness min-tree, mirrored in exact arithmetic by `tools/check_blueprint.py`
(check 16). -/
noncomputable def cTao : ℝ := 1 / (640_000_000 * Real.log 2)

/-- `tenTower h` is a tower of `h + 1` tens, evaluated with `Real.rpow`.

Thus `tenTower 0 = 10`, `tenTower 1 = 10^10`, and
`tenTower 2 = 10^(10^10)`.
-/
noncomputable def tenTower : ℕ → ℝ
  | 0 => 10
  | h + 1 => (10 : ℝ) ^ tenTower h

@[simp] theorem tenTower_zero : tenTower 0 = 10 := rfl

@[simp] theorem tenTower_succ (h : ℕ) : tenTower (h + 1) = (10 : ℝ) ^ tenTower h := rfl

theorem tenTower_pos (h : ℕ) : 0 < tenTower h := by
  induction h with
  | zero => norm_num [tenTower]
  | succ h _ => rw [tenTower_succ]; positivity

theorem ten_le_tenTower (h : ℕ) : (10 : ℝ) ≤ tenTower h := by
  induction h with
  | zero => rfl
  | succ h ih =>
      rw [tenTower_succ]
      calc
        (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := by norm_num
        _ ≤ (10 : ℝ) ^ tenTower h :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem tenTower_one_le (h : ℕ) : (1 : ℝ) ≤ tenTower h :=
  le_trans (by norm_num) (ten_le_tenTower h)

theorem tenTower_exp_le_succ (h : ℕ) : Real.exp (tenTower h) ≤ tenTower (h + 1) := by
  rw [tenTower_succ, ← Real.exp_log (by norm_num : (0 : ℝ) < 10), ← Real.exp_mul]
  exact Real.exp_le_exp.mpr (by
    have hlog : (1 : ℝ) ≤ Real.log 10 :=
      (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10)).2
        (Real.exp_one_lt_three.le.trans (by norm_num))
    nlinarith [tenTower_pos h])

theorem tenTower_two_mul_le_succ (h : ℕ) : 2 * tenTower h ≤ tenTower (h + 1) :=
  le_trans Real.two_mul_le_exp (tenTower_exp_le_succ h)

theorem tenTower_le_succ (h : ℕ) : tenTower h ≤ tenTower (h + 1) := by
  have htwo := tenTower_two_mul_le_succ h
  have hpos := tenTower_pos h
  linarith

theorem tenTower_mono {h k : ℕ} (hhk : h ≤ k) : tenTower h ≤ tenTower k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hhk
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show h + (d + 1) = (h + d) + 1 by omega]
      exact (ih (by omega)).trans (tenTower_le_succ (h + d))

theorem tenTower_add_le_succ {x y : ℝ} (h : ℕ)
    (_hx : 0 ≤ x) (_hy : 0 ≤ y) (hxT : x ≤ tenTower h) (hyT : y ≤ tenTower h) :
    x + y ≤ tenTower (h + 1) := by
  calc
    x + y ≤ 2 * tenTower h := by linarith
    _ ≤ tenTower (h + 1) := tenTower_two_mul_le_succ h

theorem tenTower_sq_le_succ (h : ℕ) : tenTower h * tenTower h ≤ tenTower (h + 1) := by
  have hhalf : tenTower h ≤ Real.exp (tenTower h / 2) := by
    convert (Real.two_mul_le_exp (x := tenTower h / 2)) using 1
    all_goals ring
  calc
    tenTower h * tenTower h
        ≤ Real.exp (tenTower h / 2) * Real.exp (tenTower h / 2) := by
          have := (tenTower_pos h).le
          gcongr
    _ = Real.exp (tenTower h) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ tenTower (h + 1) := tenTower_exp_le_succ h

theorem tenTower_mul_le_succ {x y : ℝ} (h : ℕ)
    (_hx : 0 ≤ x) (_hy : 0 ≤ y) (hxT : x ≤ tenTower h) (hyT : y ≤ tenTower h) :
    x * y ≤ tenTower (h + 1) := by
  calc
    x * y ≤ tenTower h * tenTower h := by
      have := (tenTower_pos h).le
      gcongr
    _ ≤ tenTower (h + 1) := tenTower_sq_le_succ h

theorem exp_le_tenTower_succ {x : ℝ} (h : ℕ) (hxT : x ≤ tenTower h) :
    Real.exp x ≤ tenTower (h + 1) :=
  (Real.exp_le_exp.mpr hxT).trans (tenTower_exp_le_succ h)

theorem max_le_tenTower {x y : ℝ} (h : ℕ)
    (hxT : x ≤ tenTower h) (hyT : y ≤ tenTower h) :
    max x y ≤ tenTower h := max_le hxT hyT

theorem log_le_tenTower {x : ℝ} (h : ℕ) (hx : 0 ≤ x) (hxT : x ≤ tenTower h) :
    Real.log x ≤ tenTower h := (Real.log_le_self hx).trans hxT

theorem rpow_le_tenTower_add_two {x y : ℝ} (h : ℕ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxT : x ≤ tenTower h) (hyT : y ≤ tenTower h) :
    x ^ y ≤ tenTower (h + 2) := by
  have hT0 : 0 ≤ tenTower h := (tenTower_pos h).le
  have hT1 : 1 ≤ tenTower h := tenTower_one_le h
  calc
    x ^ y ≤ tenTower h ^ y := Real.rpow_le_rpow hx hxT hy
    _ ≤ tenTower h ^ tenTower h := Real.rpow_le_rpow_of_exponent_le hT1 hyT
    _ = Real.exp (Real.log (tenTower h) * tenTower h) := by
      rw [Real.rpow_def_of_pos (tenTower_pos h)]
    _ ≤ Real.exp (tenTower h * tenTower h) := by
      gcongr
      exact Real.log_le_self hT0
    _ ≤ Real.exp (tenTower (h + 1)) := by
      gcongr
      exact tenTower_sq_le_succ h
    _ ≤ tenTower ((h + 1) + 1) := tenTower_exp_le_succ (h + 1)
    _ = tenTower (h + 2) := by congr 1

theorem natCeil_le_tenTower_succ {x : ℝ} (h : ℕ)
    (hx : 0 ≤ x) (hxT : x ≤ tenTower h) :
    ((⌈x⌉₊ : ℕ) : ℝ) ≤ tenTower (h + 1) := by
  calc
    ((⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx).le
    _ ≤ tenTower h + tenTower h := by
      gcongr
      exact tenTower_one_le h
    _ = 2 * tenTower h := by ring
    _ ≤ tenTower (h + 1) := tenTower_two_mul_le_succ h

theorem ten_rpow_le_tenTower_succ {e : ℝ} (h : ℕ) (he : e ≤ tenTower h) :
    (10 : ℝ) ^ e ≤ tenTower (h + 1) := by
  rw [tenTower_succ]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) he

theorem ten_pow_le_tenTower_succ {e : ℕ} (h : ℕ) (he : (e : ℝ) ≤ tenTower h) :
    (10 : ℝ) ^ e ≤ tenTower (h + 1) := by
  rw [← Real.rpow_natCast]
  exact ten_rpow_le_tenTower_succ h he

/-! ## The batched level-budget calculus (Design B, Tier-1 tower tightening)

One tower level pays for an arbitrary polynomial *batch*, not one operation: a product
or sum of up to `tenTower h` operands each `≤ tenTower (h + 1)` lands at
`tenTower (h + 2)`, and a real power `x ^ t` with base `≤ tenTower (h + 1)` and
exponent `≤ tenTower h` likewise.  So the *nesting depth* of the constant DAG — never
its edge count — is what costs levels.  The per-operation `_succ` lemmas above remain
for singleton uses; the climb in `BigCTower.lean` should batch through these.

For leaf-level accounting (everything under `tenTower 2`), the `ten_pow` helpers below
track explicit `10 ^ (a : ℕ)` budgets, so a whole cluster of numeric constants is one
exponent sum away from `ten_pow_le_tenTower_succ`. -/

/-- Batched product: `k ≤ tenTower h` factors, each `≤ tenTower (h + 1)`, cost ONE
level, independent of `k`.  (`∏ ≤ (10 ^ tenTower h) ^ k = 10 ^ (tenTower h · k)` and
`tenTower h · k ≤ tenTower h ^ 2 ≤ tenTower (h + 1)`.) -/
theorem prod_le_tenTower_succ {ι : Type*} {s : Finset ι} {f : ι → ℝ} (h : ℕ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hfT : ∀ i ∈ s, f i ≤ tenTower (h + 1))
    (hcard : (s.card : ℝ) ≤ tenTower h) :
    ∏ i ∈ s, f i ≤ tenTower (h + 2) := by
  have hpow : ∏ i ∈ s, f i ≤ tenTower (h + 1) ^ s.card := by
    calc
      ∏ i ∈ s, f i ≤ ∏ _i ∈ s, tenTower (h + 1) := Finset.prod_le_prod hf0 hfT
      _ = tenTower (h + 1) ^ s.card := Finset.prod_const _
  refine hpow.trans ?_
  have heq : tenTower (h + 1) ^ s.card = (10 : ℝ) ^ (tenTower h * (s.card : ℝ)) := by
    rw [tenTower_succ, ← Real.rpow_natCast ((10 : ℝ) ^ tenTower h) s.card,
      ← Real.rpow_mul (by norm_num)]
  rw [heq]
  refine ten_rpow_le_tenTower_succ (h + 1) ?_
  calc
    tenTower h * (s.card : ℝ) ≤ tenTower h * tenTower h :=
      mul_le_mul_of_nonneg_left hcard (tenTower_pos h).le
    _ ≤ tenTower (h + 1) := tenTower_sq_le_succ h

/-- Batched sum: the additive twin of `prod_le_tenTower_succ`. -/
theorem sum_le_tenTower_succ {ι : Type*} {s : Finset ι} {f : ι → ℝ} (h : ℕ)
    (hfT : ∀ i ∈ s, f i ≤ tenTower (h + 1))
    (hcard : (s.card : ℝ) ≤ tenTower h) :
    ∑ i ∈ s, f i ≤ tenTower (h + 2) := by
  have hsum : ∑ i ∈ s, f i ≤ (s.card : ℝ) * tenTower (h + 1) := by
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul s f (tenTower (h + 1)) hfT
  refine hsum.trans ?_
  calc
    (s.card : ℝ) * tenTower (h + 1)
        ≤ tenTower h * tenTower (h + 1) :=
      mul_le_mul_of_nonneg_right hcard (tenTower_pos (h + 1)).le
    _ ≤ tenTower (h + 1) * tenTower (h + 1) :=
      mul_le_mul_of_nonneg_right (tenTower_le_succ h) (tenTower_pos (h + 1)).le
    _ ≤ tenTower (h + 2) := tenTower_sq_le_succ (h + 1)

/-- Batched real power: base `≤ tenTower (h + 1)`, exponent `≤ tenTower h` — one level,
not the two of `rpow_le_tenTower_add_two`. -/
theorem rpow_le_tenTower_succ {x t : ℝ} (h : ℕ)
    (hx : 0 ≤ x) (ht : 0 ≤ t) (hxT : x ≤ tenTower (h + 1)) (htT : t ≤ tenTower h) :
    x ^ t ≤ tenTower (h + 2) := by
  calc
    x ^ t ≤ tenTower (h + 1) ^ t := Real.rpow_le_rpow hx hxT ht
    _ = (10 : ℝ) ^ (tenTower h * t) := by
      rw [tenTower_succ, ← Real.rpow_mul (by norm_num)]
    _ ≤ tenTower (h + 2) := by
      refine ten_rpow_le_tenTower_succ (h + 1) ?_
      calc
        tenTower h * t ≤ tenTower h * tenTower h :=
          mul_le_mul_of_nonneg_left htT (tenTower_pos h).le
        _ ≤ tenTower (h + 1) := tenTower_sq_le_succ h

/-! ### Ten-power leaf accounting -/

/-- Multiply two explicit ten-power budgets: exponents add, no tower level spent. -/
theorem mul_le_ten_pow {x y : ℝ} {a b : ℕ} (hy : 0 ≤ y) (hxa : x ≤ (10 : ℝ) ^ a)
    (hyb : y ≤ (10 : ℝ) ^ b) : x * y ≤ (10 : ℝ) ^ (a + b) := by
  rw [pow_add]
  exact mul_le_mul hxa hyb hy (by positivity)

/-- Add two ten-power budgets at a common exponent: one decimal digit, never a level. -/
theorem add_le_ten_pow {x y : ℝ} {a : ℕ} (hxa : x ≤ (10 : ℝ) ^ a)
    (hya : y ≤ (10 : ℝ) ^ a) : x + y ≤ (10 : ℝ) ^ (a + 1) := by
  have hp : (0 : ℝ) < (10 : ℝ) ^ a := by positivity
  calc
    x + y ≤ 2 * (10 : ℝ) ^ a := by linarith
    _ ≤ (10 : ℝ) ^ (a + 1) := by rw [pow_succ]; nlinarith

/-- Monotonicity of ten-power budgets in the exponent. -/
theorem ten_pow_mono {a b : ℕ} (h : a ≤ b) : (10 : ℝ) ^ a ≤ (10 : ℝ) ^ b :=
  pow_le_pow_right₀ (by norm_num) h

/-- A natural number `≤ 10 ^ 10` sits under `tenTower 1`. -/
theorem natCast_le_tenTower_one {a : ℕ} (ha : a ≤ 10 ^ 10) : (a : ℝ) ≤ tenTower 1 := by
  calc
    (a : ℝ) ≤ ((10 ^ 10 : ℕ) : ℝ) := Nat.cast_le.mpr ha
    _ ≤ tenTower 1 := by norm_num [tenTower, Real.rpow_natCast]

/-- Cash out a ten-power budget with exponent `≤ 10 ^ 10` at `tenTower 2`. -/
theorem ten_pow_le_tenTower_two {a : ℕ} (ha : a ≤ 10 ^ 10) :
    (10 : ℝ) ^ a ≤ tenTower 2 :=
  ten_pow_le_tenTower_succ 1 (natCast_le_tenTower_one ha)

/-- A natural number `≤ 10 ^ 30` sits under `tenTower 2`. -/
theorem natCast_le_tenTower_two {a : ℕ} (ha : a ≤ 10 ^ 30) : (a : ℝ) ≤ tenTower 2 := by
  calc
    (a : ℝ) ≤ ((10 ^ 30 : ℕ) : ℝ) := Nat.cast_le.mpr ha
    _ = (10 : ℝ) ^ (30 : ℕ) := by push_cast; norm_num
    _ ≤ tenTower 2 := ten_pow_le_tenTower_two (by norm_num)

/-- Cash out a ten-power budget with exponent `≤ 10 ^ 30` at `tenTower 3`. -/
theorem ten_pow_le_tenTower_three {a : ℕ} (ha : a ≤ 10 ^ 30) :
    (10 : ℝ) ^ a ≤ tenTower 3 :=
  ten_pow_le_tenTower_succ 2 (natCast_le_tenTower_two ha)

/-- `exp` of an argument `≤ a` fits in the ten-power budget `10 ^ a`. -/
theorem exp_le_ten_pow {x : ℝ} {a : ℕ} (hxa : x ≤ (a : ℝ)) :
    Real.exp x ≤ (10 : ℝ) ^ a := by
  calc
    Real.exp x ≤ Real.exp a := Real.exp_le_exp.mpr hxa
    _ = Real.exp 1 ^ a := (Real.exp_one_pow a).symm
    _ ≤ (10 : ℝ) ^ a :=
      pow_le_pow_left₀ (Real.exp_pos 1).le
        (Real.exp_one_lt_d9.le.trans (by norm_num)) a

/-- The bridge to Mathlib's native tetration: `tenTower h` is `10↑↑(h+1)`,
i.e. `hyperoperation 4 10 (h+1)`. -/
theorem tenTower_eq_hyperoperation (h : ℕ) :
    tenTower h = ((hyperoperation 4 10 (h + 1) : ℕ) : ℝ) := by
  induction h with
  | zero => simp [tenTower, hyperoperation_ge_two_eq_self]
  | succ h ih =>
      have hrec : hyperoperation 4 10 (h + 1 + 1) = 10 ^ hyperoperation 4 10 (h + 1) := by
        rw [hyperoperation_recursion, hyperoperation_three]
      rw [tenTower_succ, ih, hrec]
      push_cast
      rw [Real.rpow_natCast]

/-- The instance the trusted surface uses: `tenTower 62` is `10↑↑63`, a right-associated
tower of exactly 63 tens. -/
theorem tenTower_sixty_two_eq_hyperoperation :
    tenTower 62 = ((hyperoperation 4 10 63 : ℕ) : ℝ) := by
  simpa using tenTower_eq_hyperoperation 62

/-- The instance the Tier-1 campaign pin uses: `tenTower 9` is `10↑↑10`, a
right-associated tower of exactly 10 tens. -/
theorem tenTower_nine_eq_hyperoperation :
    tenTower 9 = ((hyperoperation 4 10 10 : ℕ) : ℝ) := by
  simpa using tenTower_eq_hyperoperation 9

end TaoCollatz
