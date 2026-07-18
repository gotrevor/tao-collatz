-- Full Mathlib, not slices: `Challenge.lean` re-declares `cTao`/`tenTower`/`CTao` under
-- `import Mathlib`, and comparator demands *identical* elaborations, not defeq ones — a
-- narrower import set here can pick a different instance path and fail the harness with
-- "Const does not match" (see the comparator-harness recipe's №1 gotcha).
import Mathlib

/-!
# Explicit constants: the exponent `cTao` and the `tenTower` vocabulary

A Mathlib-only leaf (no TaoCollatz imports): the two ingredients needed to *state* the
fully-explicit Theorem 3.1 — the concrete exponent `cTao` and the tower-of-tens
vocabulary behind the concrete constant `CTao := tenTower 62` (defined in
`Statement.lean`, the trusted surface).  This file sits below the whole development so
the trusted surface and the proof engine (`ExplicitBigC.lean`, `BigCTower.lean`) share
one definition.

The tower uses real powers, so even very large heights remain symbolic: Lean never
expands an astronomical natural numeral.
-/

namespace TaoCollatz

/-- The explicit exponent — OUR augmentation, beyond the paper: the collapse of the
development's witness min-tree, mirrored in exact arithmetic by `tools/check_blueprint.py`
(check 16). -/
noncomputable def cTao : ℝ := 1 / (640000000 * Real.log 2)

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

end TaoCollatz
