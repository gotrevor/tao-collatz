import TaoCollatz.Statement

/-!
# The assembled explicit big-C theorem (Ruling II successor campaign)

Additive top layer per `BIG_C_EXPLICIT_BOUND_PLAN.md`: exhibit a CLOSED Lean term for the
development's multiplicative constant and prove the quantitative theorem at it, making NO
smallness claim.  `X_spine` is the fully assembled cutoff of the as-written proof route
(the X-chase closure of `tao_collatz_quantitative_spine_atCX`); the constant
`C_tao_assembled` is a tower — enormous, honest, and explicit in the precise sense of the
plan's explicitness contract (closed def bodies; no `Exists.choose`, no existential
interface on the final proof path).
-/

namespace TaoCollatz

/-- The fully assembled cutoff on the clean, as-written proof route (X-chase closure):
a pure passthrough of the C6a sum-form cutoff parameter. -/
noncomputable def X_spine : ℝ := X_syrSum

/-- Fixed-constant version of `tao_collatz_quantitative_spine_of_le`: weakening the
explicit spine to any positive exponent `c₀ ≤ c_ladder` with the constant held at the
closed `C_spine X_spine` (X-chase).  The bound is monotone in the exponent for
`log N₀ > 1` (i.e. `N₀ ≥ 3`), and the window `N₀ = 2` is absorbed by the second `max` arm
so the bound is `≤ 0 ≤ logProb`.  Body verbatim from the ∃-form, with the obtained `C`
replaced by `C_spine X_spine` via `tao_collatz_quantitative_spine_atCX`. -/
theorem tao_collatz_quantitative_spine_atCX_of_le {c₀ : ℝ} (hle : c₀ ≤ c_ladder) :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - max (C_spine X_spine) ((Real.log 2) ^ c₀) / (Real.log N₀) ^ c₀
        ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
  have h := tao_collatz_quantitative_spine_atCX
  rw [show X_spine = X_syrSum from rfl]
  set C : ℝ := C_spine X_syrSum with hCdef
  have hC : 0 < C := C_spine_pos X_syrSum
  intro N₀ x hN₀ hx
  have hlp : (0 : ℝ) ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
    unfold logProb logSum
    positivity
  rcases eq_or_lt_of_le hN₀ with hN₀2 | hN₀3
  · -- `N₀ = 2`: the enlarged `C` makes the bound nonpositive
    subst hN₀2
    push_cast
    have hpow : (0 : ℝ) < (Real.log 2) ^ c₀ :=
      Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
    have h1 : (1 : ℝ) ≤ max C ((Real.log 2) ^ c₀) / (Real.log 2) ^ c₀ :=
      (one_le_div hpow).2 (le_max_right _ _)
    linarith
  · -- `N₀ ≥ 3`: `log N₀ > 1`, so the bound is monotone in the exponent
    have hN₀3' : (3 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀3
    have hlog1 : (1 : ℝ) ≤ Real.log N₀ := by
      have h3 : (1 : ℝ) < Real.log 3 :=
        (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hN₀3'
      linarith
    have hpow0 : (0 : ℝ) < (Real.log N₀) ^ c₀ :=
      Real.rpow_pos_of_pos (by linarith) _
    have hpowc : (Real.log N₀) ^ c₀ ≤ (Real.log N₀) ^ c_ladder :=
      Real.rpow_le_rpow_of_exponent_le hlog1 hle
    have hbase := h N₀ x hN₀ hx
    have hmono : C / (Real.log N₀) ^ c_ladder ≤
        max C ((Real.log 2) ^ c₀) / (Real.log N₀) ^ c₀ := by
      calc C / (Real.log N₀) ^ c_ladder ≤ C / (Real.log N₀) ^ c₀ := by gcongr
        _ ≤ max C ((Real.log 2) ^ c₀) / (Real.log N₀) ^ c₀ := by
            gcongr
            exact le_max_left _ _
    linarith

/-- A closed multiplicative constant for the explicit-exponent theorem
(big-C campaign, Ruling II).  The second arm is exactly the `N₀ = 2` cost of weakening
`c_ladder` to `cTao` (see `tao_collatz_quantitative_spine_atCX_of_le`).  This term is a
TOWER — enormous and useless as a number, by design: the deliverable is explicitness
(closed def bodies all the way down), never smallness. -/
noncomputable def C_tao_assembled : ℝ :=
  max (C_spine X_spine) ((Real.log 2) ^ cTao)

theorem C_tao_assembled_pos : 0 < C_tao_assembled :=
  lt_max_of_lt_left (C_spine_pos X_spine)

end TaoCollatz
