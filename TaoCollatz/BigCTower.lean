import TaoCollatz.ExplicitBigC
import Mathlib.NumberTheory.ZetaValues

/-!
# A readable tower ceiling for the assembled constant

This file deliberately favors a short public statement over a tight bound.  The
`tenTower` vocabulary and its calculus live in `Basic/ExplicitConstants.lean` (a
Mathlib-only leaf below the trusted surface, so `Statement.lean` can state the
headline); this file chases the development's leaf constants up to
`C_tao_assembled ≤ tenTower 62`.
-/

namespace TaoCollatz

/-! ## The sole recursive growth step -/

/-- A convenient base for the cubic `encWindowIter` recurrence. -/
noncomputable def encWindowBase (A : ℝ) (K : ℕ) : ℝ :=
  (4 : ℝ) ^ A + K + 5

theorem encWindowBase_one_le (A : ℝ) (K : ℕ) : 1 ≤ encWindowBase A K := by
  unfold encWindowBase
  have hpow : 0 ≤ (4 : ℝ) ^ A := Real.rpow_nonneg (by norm_num) _
  have hK : (0 : ℝ) ≤ K := by positivity
  linarith

theorem encWindowIter_succ_cast_le (A : ℝ) (K i : ℕ) :
    ((encWindowIter A K (i + 1) : ℕ) : ℝ) + 1
      ≤ encWindowBase A K * (((encWindowIter A K i : ℕ) : ℝ) + 1) ^ 3 := by
  let x : ℝ := (encWindowIter A K i : ℕ)
  let q : ℝ := (4 : ℝ) ^ A
  have hx : 0 ≤ x := by positivity
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hy : 1 ≤ x + 1 := by linarith
  have hy3 : 1 ≤ (x + 1) ^ (3 : ℕ) := one_le_pow₀ hy
  have hxy3 : x ≤ (x + 1) ^ (3 : ℕ) := by
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx 3
    nlinarith [hx2, hx3]
  have hceil : ((⌈q * (1 + x) ^ (3 : ℕ)⌉₊ : ℕ) : ℝ)
      ≤ q * (1 + x) ^ (3 : ℕ) + 1 := by
    exact (Nat.ceil_lt_add_one (mul_nonneg hq (pow_nonneg (by linarith) 3))).le
  rw [encWindowIter_succ]
  push_cast
  change x + (↑⌈q * (1 + x) ^ (3 : ℕ)⌉₊ + K + 2) + 1
      ≤ (q + K + 5) * (x + 1) ^ (3 : ℕ)
  calc
    x + (↑⌈q * (1 + x) ^ (3 : ℕ)⌉₊ + K + 2) + 1
        ≤ x + (q * (1 + x) ^ (3 : ℕ) + 1 + K + 2) + 1 := by gcongr
    _ ≤ (x + 1) ^ (3 : ℕ) + q * (x + 1) ^ (3 : ℕ)
          + (K + 4) * (x + 1) ^ (3 : ℕ) := by
        rw [show (1 + x) ^ (3 : ℕ) = (x + 1) ^ (3 : ℕ) by ring]
        have hK : (0 : ℝ) ≤ K + 4 := by positivity
        nlinarith
    _ = (q + K + 5) * (x + 1) ^ (3 : ℕ) := by ring

theorem encWindowIter_cast_add_one_le (A : ℝ) (K i : ℕ) :
    ((encWindowIter A K i : ℕ) : ℝ) + 1
      ≤ encWindowBase A K ^ ((3 : ℕ) ^ (i + 1) - 1) := by
  induction i with
  | zero =>
      norm_num [encWindowIter]
      exact (encWindowBase_one_le A K).trans (le_abs_self _)
  | succ i ih =>
      calc
        ((encWindowIter A K (i + 1) : ℕ) : ℝ) + 1
            ≤ encWindowBase A K * (((encWindowIter A K i : ℕ) : ℝ) + 1) ^ 3 :=
          encWindowIter_succ_cast_le A K i
        _ ≤ encWindowBase A K *
              (encWindowBase A K ^ ((3 : ℕ) ^ (i + 1) - 1)) ^ 3 := by
          have hB : 0 ≤ encWindowBase A K := (encWindowBase_one_le A K).trans' zero_le_one
          gcongr
        _ = encWindowBase A K ^ (1 + 3 * ((3 : ℕ) ^ (i + 1) - 1)) := by
          rw [← pow_mul]
          calc
            encWindowBase A K *
                encWindowBase A K ^ (((3 : ℕ) ^ (i + 1) - 1) * 3)
                = encWindowBase A K ^ 1 *
                    encWindowBase A K ^ (((3 : ℕ) ^ (i + 1) - 1) * 3) := by rw [pow_one]
            _ = encWindowBase A K ^
                  (1 + (((3 : ℕ) ^ (i + 1) - 1) * 3)) := (pow_add _ _ _).symm
            _ = encWindowBase A K ^
                  (1 + 3 * ((3 : ℕ) ^ (i + 1) - 1)) := by
                    congr 2
                    omega
        _ ≤ encWindowBase A K ^ ((3 : ℕ) ^ ((i + 1) + 1) - 1) := by
          apply pow_le_pow_right₀ (encWindowBase_one_le A K)
          rw [pow_succ]
          have hp : 1 ≤ (3 : ℕ) ^ (i + 1) := one_le_pow₀ (by omega)
          omega

/-- Once its coefficient, additive parameter, and iteration count fit below one tower
level, the entire cubic recurrence fits six levels higher.  The height increase is
independent of the (possibly astronomical) number of iterations. -/
theorem encWindowIter_le_tenTower_add_six {A : ℝ} {K i : ℕ} (h : ℕ)
    (hA : 0 ≤ A) (hAT : A ≤ tenTower h)
    (hKT : (K : ℝ) ≤ tenTower h) (hiT : (i : ℝ) ≤ tenTower h) :
    ((encWindowIter A K i : ℕ) : ℝ) + 1 ≤ tenTower (h + 6) := by
  have h4T : (4 : ℝ) ≤ tenTower h :=
    (show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower h)
  have hq : (4 : ℝ) ^ A ≤ tenTower (h + 2) :=
    rpow_le_tenTower_add_two h (by norm_num) hA h4T hAT
  have hK2 : (K : ℝ) ≤ tenTower (h + 2) :=
    hKT.trans (tenTower_mono (by omega))
  have h52 : (5 : ℝ) ≤ tenTower (h + 2) :=
    (show (5 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower (h + 2))
  have hqK : (4 : ℝ) ^ A + K ≤ tenTower ((h + 2) + 1) :=
    tenTower_add_le_succ (h + 2) (Real.rpow_nonneg (by norm_num) _) (by positivity) hq hK2
  have hB : encWindowBase A K ≤ tenTower (h + 4) := by
    unfold encWindowBase
    exact tenTower_add_le_succ (h + 3) (by positivity) (by norm_num)
      (hqK.trans (tenTower_mono (by omega)))
      (h52.trans (tenTower_mono (by omega)))
  have hi1 : ((i + 1 : ℕ) : ℝ) ≤ tenTower (h + 1) := by
    push_cast
    exact tenTower_add_le_succ h (by positivity) (by norm_num) hiT (tenTower_one_le h)
  have h3 : (3 : ℝ) ≤ tenTower (h + 1) :=
    (show (3 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower (h + 1))
  have h3pow : ((3 : ℝ) ^ (i + 1 : ℕ)) ≤ tenTower (h + 3) := by
    rw [← Real.rpow_natCast]
    exact rpow_le_tenTower_add_two (h + 1) (by norm_num) (by positivity) h3 hi1
  have hE : (((3 : ℕ) ^ (i + 1) - 1 : ℕ) : ℝ) ≤ tenTower (h + 3) := by
    calc
      (((3 : ℕ) ^ (i + 1) - 1 : ℕ) : ℝ) ≤ (((3 : ℕ) ^ (i + 1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le ((3 : ℕ) ^ (i + 1)) 1
      _ = (3 : ℝ) ^ (i + 1 : ℕ) := by norm_num
      _ ≤ tenTower (h + 3) := h3pow
  have hBE : encWindowBase A K ^ ((3 : ℕ) ^ (i + 1) - 1)
      ≤ tenTower (h + 6) := by
    rw [← Real.rpow_natCast]
    exact rpow_le_tenTower_add_two (h + 4)
      ((encWindowBase_one_le A K).trans' zero_le_one) (by positivity) hB
      (hE.trans (tenTower_mono (by omega)))
  exact (encWindowIter_cast_add_one_le A K i).trans hBE

/-! ## Exact rates on the §7 constant spine -/

theorem c_holdLocal_eq : c_holdLocal = (1 : ℝ) / 400 := rfl

theorem c_renewalMass_eq : c_renewalMass = (1 : ℝ) / 1600 := by
  norm_num [c_renewalMass, c_holdLocal]

theorem gamma_holdStep_eq : gamma_holdStep = (1 : ℝ) / 1600 := by
  norm_num [gamma_holdStep, c_holdLocal]

theorem c_fpLocation_eq : c_fpLocation = (1 : ℝ) / 12800 := by
  norm_num [c_fpLocation, c_renewalMass_eq, gamma_holdStep_eq, min_def]

theorem c_fpHeight_eq : c_fpHeight = (1 : ℝ) / 25600 := by
  norm_num [c_fpHeight, c_fpLocation_eq]

theorem c_fpHeightTail_eq : c_fpHeightTail = (1 : ℝ) / 51200 := by
  norm_num [c_fpHeightTail, c_fpHeight_eq, min_def]

theorem c_fpColDev_eq : c_fpColDev = (1 : ℝ) / 327680000 := by
  norm_num [c_fpColDev, c_fpLocation_eq, min_def]

theorem c_fpColTail_eq : c_fpColTail = (1 : ℝ) / 327680000 := by
  norm_num [c_fpColTail, c_fpColDev_eq, min_def]

theorem c_encTri_eq : c_encTri = (1 : ℝ) / 51200 := by
  rw [c_encTri, c_fpHeightTail_eq]

theorem c_estarUnion_eq : c_estarUnion = (1 : ℝ) / 51200 := by
  rw [c_estarUnion, c_encTri_eq]

/-- The geometric-series quotient used repeatedly in §7 is at most `1 / c`.
This crude form follows directly from `1 + c ≤ exp c`. -/
theorem exp_neg_div_one_sub_exp_neg_le_inv {c : ℝ} (hc : 0 < c) :
    Real.exp (-c) / (1 - Real.exp (-c)) ≤ 1 / c := by
  have he1 : 1 < Real.exp c := (Real.one_lt_exp_iff).2 hc
  have hden : c ≤ Real.exp c - 1 := by linarith [Real.add_one_le_exp c]
  have heq : Real.exp (-c) / (1 - Real.exp (-c)) = 1 / (Real.exp c - 1) := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt (Real.exp_pos c), ne_of_gt (by linarith : 0 < Real.exp c - 1)]
  rw [heq]
  exact one_div_le_one_div_of_le hc hden

/-- A companion bound for the full geometric sum. -/
theorem one_div_one_sub_exp_neg_le {c : ℝ} (hc : 0 < c) :
    1 / (1 - Real.exp (-c)) ≤ 1 + 1 / c := by
  have hd : 0 < 1 - Real.exp (-c) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  calc
    1 / (1 - Real.exp (-c))
        = 1 + Real.exp (-c) / (1 - Real.exp (-c)) := by field_simp; ring
    _ ≤ 1 + 1 / c := by linarith [exp_neg_div_one_sub_exp_neg_le_inv hc]

/-! ## Coarse bounds below the cubic recurrence -/

private theorem thirty_le_tenTower_one : (30 : ℝ) ≤ tenTower 1 := by
  norm_num [tenTower, Real.rpow_natCast]

private theorem ten_pow_thirty_le_tenTower_two : (10 : ℝ) ^ (30 : ℕ) ≤ tenTower 2 :=
  ten_pow_le_tenTower_succ 1 thirty_le_tenTower_one

theorem C_holdLocal_le_tenTower_two : C_holdLocal ≤ tenTower 2 := by
  calc
    C_holdLocal ≤ (10 : ℝ) ^ (30 : ℕ) := by norm_num [C_holdLocal]
    _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two

private theorem C_renewalWeight_spine_le_ten_pow_thirty :
    C_renewalWeight ((c_holdLocal / 2) ^ 2 / 2) (c_holdLocal / 2 / 2)
      ≤ (10 : ℝ) ^ (30 : ℕ) := by
  have hs0 : 0 ≤ Real.sqrt (1280000 : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (1280000 : ℝ)) ^ 2 = 1280000 := by
    rw [Real.sq_sqrt]
    norm_num
  have hs : Real.sqrt (1280000 : ℝ) ≤ 2000 := by nlinarith
  norm_num [C_renewalWeight, c_holdLocal, min_def]
  nlinarith

private theorem C_renewalWeight_spine_le_tenTower_two :
    C_renewalWeight ((c_holdLocal / 2) ^ 2 / 2) (c_holdLocal / 2 / 2) ≤ tenTower 2 :=
  C_renewalWeight_spine_le_ten_pow_thirty.trans ten_pow_thirty_le_tenTower_two

theorem C_renewalMass_le_tenTower_three : C_renewalMass ≤ tenTower 3 := by
  have ha : 0 < (c_holdLocal / 2) ^ 2 / 2 := by
    have := c_holdLocal_pos
    positivity
  have hb : 0 < c_holdLocal / 2 / 2 := by
    have := c_holdLocal_pos
    positivity
  unfold C_renewalMass
  exact tenTower_mul_le_succ 2 C_holdLocal_pos.le
    (C_renewalWeight_pos ha hb).le
    C_holdLocal_le_tenTower_two C_renewalWeight_spine_le_tenTower_two

theorem C_holdStep_le_tenTower_three : C_holdStep ≤ tenTower 3 := by
  unfold C_holdStep
  have h2 : (2 : ℝ) ≤ tenTower 2 :=
    (show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)
  exact tenTower_mul_le_succ 2 (by norm_num) C_holdLocal_pos.le h2 C_holdLocal_le_tenTower_two

private theorem K_sqrtExp_spine_le_tenTower_two :
    K_sqrtExp (gamma_holdStep / 2) ≤ tenTower 2 := by
  calc
    K_sqrtExp (gamma_holdStep / 2) ≤ (10 : ℝ) ^ (30 : ℕ) := by
      norm_num [K_sqrtExp, gamma_holdStep_eq]
    _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two

/-- POC of the Design B batched calculus: the honest size of `C_fpLocation` is a plain
`10 ^ 74`.  Every factor carries an explicit `10 ^ a` budget and the exponents add
(`mul_le_ten_pow`); no tower level is spent at all. -/
theorem C_fpLocation_le_ten_pow : C_fpLocation ≤ (10 : ℝ) ^ (74 : ℕ) := by
  have ha : 0 < (c_holdLocal / 2) ^ 2 / 2 := by
    have := c_holdLocal_pos
    positivity
  have hb : 0 < c_holdLocal / 2 / 2 := by
    have := c_holdLocal_pos
    positivity
  have h1 : C_renewalMass ≤ (10 : ℝ) ^ (13 + 30 : ℕ) := by
    unfold C_renewalMass
    exact mul_le_ten_pow (C_renewalWeight_pos ha hb).le
      (by norm_num [C_holdLocal]) C_renewalWeight_spine_le_ten_pow_thirty
  have h2 : C_holdStep ≤ (10 : ℝ) ^ (14 : ℕ) := by
    norm_num [C_holdStep, C_holdLocal]
  have h3 : Real.exp (16 * gamma_holdStep) ≤ (10 : ℝ) ^ (1 : ℕ) :=
    exp_le_ten_pow (by norm_num [gamma_holdStep_eq])
  have h4 : 4 + 8 / gamma_holdStep ≤ (10 : ℝ) ^ (5 : ℕ) := by
    norm_num [gamma_holdStep_eq]
  have h4pos : (0 : ℝ) ≤ 4 + 8 / gamma_holdStep := by
    have := gamma_holdStep_pos
    positivity
  have h5 : 2 * Real.exp (4 * min (c_renewalMass / 2) (gamma_holdStep / 4))
      ≤ (10 : ℝ) ^ (1 + 1 : ℕ) :=
    mul_le_ten_pow (Real.exp_pos _).le (by norm_num)
      (exp_le_ten_pow (by norm_num [c_renewalMass_eq, gamma_holdStep_eq, min_def]))
  have h5pos : (0 : ℝ)
      ≤ 2 * Real.exp (4 * min (c_renewalMass / 2) (gamma_holdStep / 4)) := by
    positivity
  have h6 : K_sqrtExp (gamma_holdStep / 2) ≤ (10 : ℝ) ^ (9 : ℕ) := by
    norm_num [K_sqrtExp, gamma_holdStep_eq]
  have hgamma2 : 0 < gamma_holdStep / 2 := div_pos gamma_holdStep_pos two_pos
  have hprod : C_fpLocation ≤ (10 : ℝ) ^ (13 + 30 + 14 + 1 + 5 + (1 + 1) + 9 : ℕ) := by
    unfold C_fpLocation
    exact mul_le_ten_pow (K_sqrtExp_pos hgamma2).le
      (mul_le_ten_pow h5pos
        (mul_le_ten_pow h4pos
          (mul_le_ten_pow (Real.exp_pos _).le
            (mul_le_ten_pow C_holdStep_pos.le h1 h2) h3) h4) h5) h6
  exact hprod.trans (ten_pow_mono (by norm_num))

/-- The POC gate of the Tier-1 campaign: `C_fpLocation` at its honest height 2 (the
per-operation `_succ` climb charged 8). -/
theorem C_fpLocation_le_tenTower_two : C_fpLocation ≤ tenTower 2 :=
  C_fpLocation_le_ten_pow.trans (ten_pow_le_tenTower_two (by norm_num))

/-- The pre-tightening bound, kept as the interface the downstream climb still
consumes; now a corollary of the honest `tenTower 2` height. -/
theorem C_fpLocation_le_tenTower_eight : C_fpLocation ≤ tenTower 8 :=
  C_fpLocation_le_tenTower_two.trans (tenTower_mono (by omega))

/-! The geometric-ratio and row-sum helpers of the first-passage cluster, each with an
explicit ten-power budget (`ratio(c) = e^{-c}/(1-e^{-c}) ≤ 1/c`). -/

private theorem ratio_fpLocation_nonneg :
    0 ≤ Real.exp (-c_fpLocation) / (1 - Real.exp (-c_fpLocation)) := by
  have hd : 0 < 1 - Real.exp (-c_fpLocation) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith [c_fpLocation_pos]
  exact (div_pos (Real.exp_pos _) hd).le

private theorem ratio_fpLocation_le_ten_pow :
    Real.exp (-c_fpLocation) / (1 - Real.exp (-c_fpLocation)) ≤ (10 : ℝ) ^ (5 : ℕ) :=
  calc
    Real.exp (-c_fpLocation) / (1 - Real.exp (-c_fpLocation))
        ≤ 1 / c_fpLocation := exp_neg_div_one_sub_exp_neg_le_inv c_fpLocation_pos
    _ ≤ (10 : ℝ) ^ (5 : ℕ) := by norm_num [c_fpLocation_eq]

private theorem ratio_half_fpLocation_nonneg :
    0 ≤ Real.exp (-(c_fpLocation / 2)) / (1 - Real.exp (-(c_fpLocation / 2))) := by
  have hd : 0 < 1 - Real.exp (-(c_fpLocation / 2)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith [c_fpLocation_pos]
  exact (div_pos (Real.exp_pos _) hd).le

private theorem ratio_half_fpLocation_le_ten_pow :
    Real.exp (-(c_fpLocation / 2)) / (1 - Real.exp (-(c_fpLocation / 2)))
      ≤ (10 : ℝ) ^ (5 : ℕ) := by
  have hc : 0 < c_fpLocation / 2 := div_pos c_fpLocation_pos two_pos
  calc
    Real.exp (-(c_fpLocation / 2)) / (1 - Real.exp (-(c_fpLocation / 2)))
        ≤ 1 / (c_fpLocation / 2) := exp_neg_div_one_sub_exp_neg_le_inv hc
    _ ≤ (10 : ℝ) ^ (5 : ℕ) := by norm_num [c_fpLocation_eq]

private theorem K_rowG_fpLocation_le_ten_pow :
    K_rowG c_fpLocation ≤ (10 : ℝ) ^ (5 : ℕ) := by
  have hgeom := one_div_one_sub_exp_neg_le c_fpLocation_pos
  unfold K_rowG
  calc
    10 + 2 / (1 - Real.exp (-c_fpLocation)) + 4 / c_fpLocation
        ≤ 10 + 2 * (1 + 1 / c_fpLocation) + 4 / c_fpLocation := by
          rw [div_eq_mul_inv]
          gcongr
          simpa [one_div] using hgeom
    _ ≤ (10 : ℝ) ^ (5 : ℕ) := by norm_num [c_fpLocation_eq]

private theorem K_rowG_half_fpLocation_le_ten_pow :
    K_rowG (c_fpLocation / 2) ≤ (10 : ℝ) ^ (6 : ℕ) := by
  have hc : 0 < c_fpLocation / 2 := div_pos c_fpLocation_pos two_pos
  have hgeom := one_div_one_sub_exp_neg_le hc
  unfold K_rowG
  calc
    10 + 2 / (1 - Real.exp (-(c_fpLocation / 2))) + 4 / (c_fpLocation / 2)
        ≤ 10 + 2 * (1 + 1 / (c_fpLocation / 2)) + 4 / (c_fpLocation / 2) := by
          rw [div_eq_mul_inv]
          gcongr
          simpa [one_div] using hgeom
    _ ≤ (10 : ℝ) ^ (6 : ℕ) := by norm_num [c_fpLocation_eq]

private theorem K_intG_fpLocation_le_ten_pow :
    K_intG c_fpLocation ≤ (10 : ℝ) ^ (6 : ℕ) := by
  unfold K_intG
  exact (mul_le_ten_pow (K_rowG_pos c_fpLocation_pos).le
    (by norm_num : (2 : ℝ) ≤ (10 : ℝ) ^ (1 : ℕ)) K_rowG_fpLocation_le_ten_pow).trans
    (ten_pow_mono (by norm_num))

theorem C_fpCol_le_ten_pow : C_fpCol ≤ (10 : ℝ) ^ (79 : ℕ) := by
  unfold C_fpCol
  exact (mul_le_ten_pow ratio_fpLocation_nonneg C_fpLocation_le_ten_pow
    ratio_fpLocation_le_ten_pow).trans (ten_pow_mono (by norm_num))

theorem C_fpCol_le_tenTower_two : C_fpCol ≤ tenTower 2 :=
  C_fpCol_le_ten_pow.trans (ten_pow_le_tenTower_two (by norm_num))

theorem C_fpCol_le_tenTower_nine : C_fpCol ≤ tenTower 9 :=
  C_fpCol_le_tenTower_two.trans (tenTower_mono (by omega))

theorem C_fpHeight_le_ten_pow : C_fpHeight ≤ (10 : ℝ) ^ (84 : ℕ) := by
  unfold C_fpHeight
  exact (mul_le_ten_pow ratio_half_fpLocation_nonneg
    (mul_le_ten_pow (K_rowG_pos c_fpLocation_pos).le C_fpLocation_le_ten_pow
      K_rowG_fpLocation_le_ten_pow)
    ratio_half_fpLocation_le_ten_pow).trans (ten_pow_mono (by norm_num))

theorem C_fpHeight_le_tenTower_ten : C_fpHeight ≤ tenTower 10 :=
  (C_fpHeight_le_ten_pow.trans (ten_pow_le_tenTower_two (by norm_num))).trans
    (tenTower_mono (by omega))

theorem C_fpColDev_le_ten_pow : C_fpColDev ≤ (10 : ℝ) ^ (85 : ℕ) := by
  unfold C_fpColDev
  exact (mul_le_ten_pow ratio_fpLocation_nonneg
    (mul_le_ten_pow (K_rowG_pos (div_pos c_fpLocation_pos two_pos)).le
      C_fpLocation_le_ten_pow K_rowG_half_fpLocation_le_ten_pow)
    ratio_fpLocation_le_ten_pow).trans (ten_pow_mono (by norm_num))

theorem C_fpColDev_le_tenTower_ten : C_fpColDev ≤ tenTower 10 :=
  (C_fpColDev_le_ten_pow.trans (ten_pow_le_tenTower_two (by norm_num))).trans
    (tenTower_mono (by omega))

theorem C_fpHeightTail_le_ten_pow : C_fpHeightTail ≤ (10 : ℝ) ^ (85 : ℕ) := by
  unfold C_fpHeightTail
  exact add_le_ten_pow (C_fpHeight_le_ten_pow.trans (ten_pow_mono (by norm_num)))
    (by norm_num)

theorem C_fpHeightTail_le_tenTower_eleven : C_fpHeightTail ≤ tenTower 11 :=
  (C_fpHeightTail_le_ten_pow.trans (ten_pow_le_tenTower_two (by norm_num))).trans
    (tenTower_mono (by omega))

theorem C_fpColTail_le_ten_pow : C_fpColTail ≤ (10 : ℝ) ^ (86 : ℕ) := by
  unfold C_fpColTail
  exact add_le_ten_pow (C_fpColDev_le_ten_pow.trans (ten_pow_mono (by norm_num)))
    (by norm_num)

theorem C_fpColTail_le_tenTower_eleven : C_fpColTail ≤ tenTower 11 :=
  (C_fpColTail_le_ten_pow.trans (ten_pow_le_tenTower_two (by norm_num))).trans
    (tenTower_mono (by omega))

theorem C_encSep_le_ten_pow : C_encSep ≤ (10 : ℝ) ^ (89 : ℕ) := by
  have ht1 : 12 * C_fpCol ≤ (10 : ℝ) ^ (88 : ℕ) :=
    (mul_le_ten_pow C_fpCol_pos.le
      (by norm_num : (12 : ℝ) ≤ (10 : ℝ) ^ (2 : ℕ)) C_fpCol_le_ten_pow).trans
      (ten_pow_mono (by norm_num))
  have ht2 : 120 * C_fpCol * K_intG c_fpLocation ≤ (10 : ℝ) ^ (88 : ℕ) :=
    (mul_le_ten_pow (K_intG_pos c_fpLocation_pos).le
      (mul_le_ten_pow C_fpCol_pos.le
        (by norm_num : (120 : ℝ) ≤ (10 : ℝ) ^ (3 : ℕ)) C_fpCol_le_ten_pow)
      K_intG_fpLocation_le_ten_pow).trans (ten_pow_mono (by norm_num))
  unfold C_encSep
  exact add_le_ten_pow ht1 ht2

theorem C_encSep_le_tenTower_two : C_encSep ≤ tenTower 2 :=
  C_encSep_le_ten_pow.trans (ten_pow_le_tenTower_two (by norm_num))

theorem C_encSep_le_tenTower_twelve : C_encSep ≤ tenTower 12 :=
  C_encSep_le_tenTower_two.trans (tenTower_mono (by omega))

private theorem M_encTri_cast_le_ten_pow : (M_encTri : ℝ) ≤ (10 : ℝ) ^ (27 : ℕ) := by
  norm_num [M_encTri, S_apexProx, max_def]

/-- `C_encTri` is the first genuinely tower-tall constant of the cluster: its
`exp(c_fpHeightTail · M_encTri) ≈ exp(2×10²²)` term is honestly doubly exponential, so
the budget exponent is `10²⁷ + 4` and the height is 3, not 2. -/
theorem C_encTri_le_ten_pow : C_encTri ≤ (10 : ℝ) ^ (10 ^ 27 + 4 : ℕ) := by
  have hM0 : (0 : ℝ) ≤ (M_encTri : ℝ) := by positivity
  have harg : c_fpHeightTail * (M_encTri : ℝ) ≤ ((10 ^ 27 : ℕ) : ℝ) := by
    have h1 : c_fpHeightTail * (M_encTri : ℝ) ≤ 1 * (M_encTri : ℝ) := by
      rw [c_fpHeightTail_eq]
      exact mul_le_mul_of_nonneg_right (by norm_num) hM0
    calc
      c_fpHeightTail * (M_encTri : ℝ) ≤ (M_encTri : ℝ) := by linarith
      _ ≤ (10 : ℝ) ^ (27 : ℕ) := M_encTri_cast_le_ten_pow
      _ ≤ ((10 ^ 27 : ℕ) : ℝ) := by push_cast; norm_num
  have hexp : Real.exp (c_fpHeightTail * (M_encTri : ℝ))
      ≤ (10 : ℝ) ^ (10 ^ 27 : ℕ) := exp_le_ten_pow harg
  have ht1 : 100 * C_apexProx ≤ (10 : ℝ) ^ (10 ^ 27 : ℕ) :=
    le_trans (by norm_num [C_apexProx] :
        100 * C_apexProx ≤ (10 : ℝ) ^ (3 : ℕ)) (ten_pow_mono (by norm_num))
  have ht10 : (0 : ℝ) ≤ 100 * C_apexProx := by norm_num [C_apexProx]
  have ht3 : C_fpHeightTail ≤ (10 : ℝ) ^ (10 ^ 27 : ℕ) :=
    C_fpHeightTail_le_ten_pow.trans (ten_pow_mono (by norm_num))
  have ht4 : 432 * C_fpColTail / c_fpColTail ^ 3 ≤ (10 : ℝ) ^ (10 ^ 27 : ℕ) := by
    rw [show 432 * C_fpColTail / c_fpColTail ^ 3
      = (432 / c_fpColTail ^ 3) * C_fpColTail by ring]
    exact le_trans (mul_le_ten_pow C_fpColTail_pos.le
      (show 432 / c_fpColTail ^ 3 ≤ (10 : ℝ) ^ (29 : ℕ) by norm_num [c_fpColTail_eq])
      C_fpColTail_le_ten_pow) (ten_pow_mono (by norm_num))
  have ht5 : C_encSep * C_apexProx ≤ (10 : ℝ) ^ (10 ^ 27 : ℕ) :=
    le_trans (mul_le_ten_pow (by norm_num [C_apexProx]) C_encSep_le_ten_pow
      (show C_apexProx ≤ (10 : ℝ) ^ (1 : ℕ) by norm_num [C_apexProx]))
      (ten_pow_mono (by norm_num))
  have hpow : (10 : ℝ) ^ (10 ^ 27 + 4 : ℕ)
      = (10 : ℝ) ^ (4 : ℕ) * (10 : ℝ) ^ (10 ^ 27 : ℕ) := by
    rw [← pow_add]
    exact congrArg _ (Nat.add_comm _ 4)
  -- Opaque-variable the astronomically-exponented power BEFORE any arithmetic tactic
  -- runs: linarith/norm_num otherwise try to evaluate `10 ^ 10²⁷` as a numeral and
  -- panic the kernel (`Nat.pow exponent is too big`).
  generalize hB : (10 : ℝ) ^ (10 ^ 27 : ℕ) = B at hexp ht1 ht3 ht4 ht5 hpow
  unfold C_encTri
  rw [hpow]
  have hB0 : (0 : ℝ) ≤ B := le_trans ht10 ht1
  linarith

theorem C_encTri_le_tenTower_three : C_encTri ≤ tenTower 3 :=
  C_encTri_le_ten_pow.trans (ten_pow_le_tenTower_three (by norm_num))

theorem C_encTri_le_tenTower_fourteen : C_encTri ≤ tenTower 14 :=
  C_encTri_le_tenTower_three.trans (tenTower_mono (by omega))

theorem C_estarUnion_le_ten_pow : C_estarUnion ≤ (10 : ℝ) ^ (10 ^ 27 + 5 : ℕ) := by
  unfold C_estarUnion
  exact (mul_le_ten_pow C_encTri_pos.le
    (show (4 : ℝ) ≤ (10 : ℝ) ^ (1 : ℕ) by norm_num) C_encTri_le_ten_pow).trans
    (ten_pow_mono (by norm_num))

theorem C_estarUnion_le_tenTower_three : C_estarUnion ≤ tenTower 3 :=
  C_estarUnion_le_ten_pow.trans (ten_pow_le_tenTower_three (by norm_num))

theorem C_estarUnion_le_tenTower_fifteen : C_estarUnion ≤ tenTower 15 :=
  C_estarUnion_le_tenTower_three.trans (tenTower_mono (by omega))

private theorem sqrt_le_add_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ x + 1 := by
  have hs0 := Real.sqrt_nonneg x
  have hs2 := Real.sq_sqrt hx
  nlinarith [sq_nonneg (Real.sqrt x - 1 / 2)]

private theorem A0_estarUnion_le_ten_pow : A0_estarUnion ≤ (10 : ℝ) ^ (3 : ℕ) := by
  have harg : Real.log 2 / c_encTri ≤ 102400 := by
    have hlog : Real.log 2 ≤ 2 := (Real.log_le_self (by norm_num)).trans (by norm_num)
    rw [c_encTri_eq]
    norm_num
    nlinarith
  have harg0 : 0 ≤ Real.log 2 / c_encTri :=
    div_nonneg (Real.log_nonneg (by norm_num)) c_encTri_pos.le
  have hs : Real.sqrt (Real.log 2 / c_encTri) ≤ (10 : ℝ) ^ (3 : ℕ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · calc
        Real.log 2 / c_encTri ≤ 102400 := harg
        _ ≤ ((10 : ℝ) ^ (3 : ℕ)) ^ 2 := by norm_num
  unfold A0_estarUnion
  exact max_le (by norm_num) hs

private theorem one_le_log_four : (1 : ℝ) ≤ Real.log 4 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h4]
  linarith

private theorem two_fifths_le_log_sixteen_sub_log_ten :
    (2 / 5 : ℝ) ≤ 2 * Real.log 4 - Real.log 10 := by
  have h2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h5hi : Real.log 5 < (1.6094379126 : ℝ) := Real.log_five_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have h10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h4, h10]
  linarith

private theorem Kthr_estarScaled_le_ten_pow :
    Kthr_estarScaled C_estarUnion ≤ (10 : ℝ) ^ (10 ^ 27 + 14 : ℕ) := by
  let d : ℝ := 2 * Real.log 4 - Real.log 10
  have hd : (2 / 5 : ℝ) ≤ d := two_fifths_le_log_sixteen_sub_log_ten
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hL : (1 : ℝ) ≤ Real.log 4 := one_le_log_four
  have hden1 : (1 / 10 : ℝ) ≤ d ^ 2 * (Real.log 4) ^ 3 := by
    have hd2 : (2 / 5 : ℝ) ^ 2 ≤ d ^ 2 := by gcongr
    have hL3 : (1 : ℝ) ≤ (Real.log 4) ^ (3 : ℕ) := one_le_pow₀ hL
    calc
      (1 / 10 : ℝ) ≤ (2 / 5 : ℝ) ^ 2 * 1 := by norm_num
      _ ≤ d ^ 2 * (Real.log 4) ^ 3 := by gcongr
  have hden1pos : 0 < d ^ 2 * (Real.log 4) ^ 3 := by positivity
  have hinv1 : 1 / (d ^ 2 * (Real.log 4) ^ 3) ≤ 10 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 10) hden1
    norm_num at this ⊢
    exact this
  have hinv1' : (d ^ 2 * (Real.log 4) ^ 3)⁻¹ ≤ 10 := by
    simpa [one_div] using hinv1
  have hinv4 : 1 / (Real.log 4) ^ 3 ≤ 1 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ (Real.log 4) ^ (3 : ℕ) from one_le_pow₀ hL)
    norm_num at this ⊢
    exact this
  have hinv4' : ((Real.log 4) ^ 3)⁻¹ ≤ 1 := by simpa [one_div] using hinv4
  have hc1 : 3456000 / (d ^ 2 * (Real.log 4) ^ 3) ≤ (10 : ℝ) ^ (8 : ℕ) := by
    rw [div_eq_mul_inv]
    nlinarith
  have hc2 : 216000 / (Real.log 4) ^ 3 ≤ (10 : ℝ) ^ (6 : ℕ) := by
    rw [div_eq_mul_inv]
    nlinarith
  have ht1 : 3456000 * C_estarUnion / (d ^ 2 * (Real.log 4) ^ 3)
      ≤ (10 : ℝ) ^ (10 ^ 27 + 13 : ℕ) := by
    rw [show 3456000 * C_estarUnion / (d ^ 2 * (Real.log 4) ^ 3)
      = (3456000 / (d ^ 2 * (Real.log 4) ^ 3)) * C_estarUnion by ring]
    exact (mul_le_ten_pow C_estarUnion_pos.le hc1 C_estarUnion_le_ten_pow).trans
      (ten_pow_mono (by norm_num))
  have ht2 : 216000 * C_estarUnion / (Real.log 4) ^ 3
      ≤ (10 : ℝ) ^ (10 ^ 27 + 13 : ℕ) := by
    rw [show 216000 * C_estarUnion / (Real.log 4) ^ 3
      = (216000 / (Real.log 4) ^ 3) * C_estarUnion by ring]
    exact (mul_le_ten_pow C_estarUnion_pos.le hc2 C_estarUnion_le_ten_pow).trans
      (ten_pow_mono (by norm_num))
  unfold Kthr_estarScaled
  change 3456000 * C_estarUnion / (d ^ 2 * (Real.log 4) ^ 3)
      + 216000 * C_estarUnion / (Real.log 4) ^ 3
      ≤ (10 : ℝ) ^ (10 ^ 27 + 14 : ℕ)
  exact add_le_ten_pow ht1 ht2

private theorem one_le_C_encTri : (1 : ℝ) ≤ C_encTri := by
  have harg0 : 0 ≤ c_fpHeightTail * (M_encTri : ℝ) :=
    mul_nonneg c_fpHeightTail_pos.le (by positivity)
  have hexp : 1 ≤ Real.exp (c_fpHeightTail * (M_encTri : ℝ)) := Real.one_le_exp harg0
  have ht1 : 0 ≤ 100 * C_apexProx := by norm_num [C_apexProx]
  have ht3 : 0 ≤ C_fpHeightTail := C_fpHeightTail_pos.le
  have ht4 : 0 ≤ 432 * C_fpColTail / c_fpColTail ^ (3 : ℕ) :=
    div_nonneg (mul_nonneg (by norm_num) C_fpColTail_pos.le)
      (pow_nonneg c_fpColTail_pos.le 3)
  have ht5 : 0 ≤ C_encSep * C_apexProx :=
    mul_nonneg C_encSep_pos.le (by norm_num [C_apexProx])
  unfold C_encTri
  linarith

private theorem one_le_C_estarUnion : (1 : ℝ) ≤ C_estarUnion := by
  unfold C_estarUnion
  nlinarith [one_le_C_encTri]

private theorem Warg_estarScaled_le_ten_pow :
    Warg_estarScaled C_estarUnion c_estarUnion ≤ (10 : ℝ) ^ (10 ^ 27 + 20 : ℕ) := by
  have hinput0 : 0 ≤ 2000 * C_estarUnion :=
    mul_nonneg (by norm_num) C_estarUnion_pos.le
  have hinput1 : (1 : ℝ) ≤ 2000 * C_estarUnion := by
    nlinarith [one_le_C_estarUnion]
  have hlog0 : 0 ≤ Real.log (2000 * C_estarUnion) := Real.log_nonneg hinput1
  have hlog : Real.log (2000 * C_estarUnion) ≤ 2000 * C_estarUnion :=
    Real.log_le_self hinput0
  have hc0 : 0 ≤ c_estarUnion := c_estarUnion_pos.le
  have hc1 : c_estarUnion ≤ 1 := by norm_num [c_estarUnion_eq]
  have hterm : 16 * c_estarUnion * Real.log (2000 * C_estarUnion)
      ≤ 32000 * C_estarUnion := by
    calc
      16 * c_estarUnion * Real.log (2000 * C_estarUnion)
          ≤ 16 * 1 * (2000 * C_estarUnion) := by gcongr
      _ = 32000 * C_estarUnion := by ring
  have hlog10 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  have hlog10' : Real.log 10 ≤ 10 := Real.log_le_self (by norm_num)
  have hlog10sq : (Real.log 10) ^ (2 : ℕ) ≤ 100 := by nlinarith
  let num : ℝ := 16 * c_estarUnion * Real.log (2000 * C_estarUnion) + (Real.log 10) ^ 2
  have hnum0 : 0 ≤ num := by
    dsimp [num]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc0) hlog0) (sq_nonneg _)
  have hprod : 32000 * C_estarUnion ≤ (10 : ℝ) ^ (10 ^ 27 + 10 : ℕ) :=
    (mul_le_ten_pow C_estarUnion_pos.le
      (by norm_num : (32000 : ℝ) ≤ (10 : ℝ) ^ (5 : ℕ)) C_estarUnion_le_ten_pow).trans
      (ten_pow_mono (by norm_num))
  have hnum : num ≤ (10 : ℝ) ^ (10 ^ 27 + 11 : ℕ) := by
    dsimp [num]
    exact add_le_ten_pow (hterm.trans hprod)
      (((show (Real.log 10) ^ (2 : ℕ) ≤ (100 : ℝ) from hlog10sq).trans
        (by norm_num : (100 : ℝ) ≤ (10 : ℝ) ^ (2 : ℕ))).trans
        (ten_pow_mono (by norm_num)))
  have hinv0 : 0 ≤ (16 * c_estarUnion ^ (2 : ℕ))⁻¹ := by positivity
  have hinv : (16 * c_estarUnion ^ (2 : ℕ))⁻¹ ≤ (10 : ℝ) ^ (9 : ℕ) := by
    norm_num [c_estarUnion_eq]
  unfold Warg_estarScaled
  change num / (16 * c_estarUnion ^ (2 : ℕ)) ≤ (10 : ℝ) ^ (10 ^ 27 + 20 : ℕ)
  rw [div_eq_mul_inv]
  exact (mul_le_ten_pow hinv0 hnum hinv).trans (ten_pow_mono (by norm_num))

theorem A0_fewEstar_le_ten_pow : A0_fewEstar ≤ (10 : ℝ) ^ (10 ^ 27 + 22 : ℕ) := by
  have hone : (1 : ℝ) ≤ (10 : ℝ) ^ (10 ^ 27 + 22 : ℕ) :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10)
  have hWmax : max 0 (Warg_estarScaled C_estarUnion c_estarUnion)
      ≤ (10 : ℝ) ^ (10 ^ 27 + 20 : ℕ) :=
    max_le (le_trans (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ (0 : ℕ))
      (ten_pow_mono (by norm_num))) Warg_estarScaled_le_ten_pow
  have hWmax0 : 0 ≤ max 0 (Warg_estarScaled C_estarUnion c_estarUnion) := le_max_left _ _
  have hsqrt : Real.sqrt (max 0 (Warg_estarScaled C_estarUnion c_estarUnion))
      ≤ (10 : ℝ) ^ (10 ^ 27 + 21 : ℕ) :=
    (sqrt_le_add_one hWmax0).trans
      (add_le_ten_pow hWmax (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10)))
  unfold A0_fewEstar A0_estarScaled
  exact max_le
    (A0_estarUnion_le_ten_pow.trans (ten_pow_mono (by norm_num)))
    (max_le hone
      (max_le (Kthr_estarScaled_le_ten_pow.trans (ten_pow_mono (by norm_num)))
        (hsqrt.trans (ten_pow_mono (by norm_num)))))

theorem A0_fewEstar_le_tenTower_three : A0_fewEstar ≤ tenTower 3 :=
  A0_fewEstar_le_ten_pow.trans (ten_pow_le_tenTower_three (by norm_num))

theorem A0_fewEstar_le_tenTower_nineteen : A0_fewEstar ≤ tenTower 19 :=
  A0_fewEstar_le_tenTower_three.trans (tenTower_mono (by omega))

/-! ## The explicit cubic horizon at the exponent used by §6 -/

private theorem mainDecayExponent_37_le_tenTower_two :
    mainDecayExponent 3.7 ≤ tenTower 2 := by
  have hlog : Real.log 2 ≤ 2 := (Real.log_le_self (by norm_num)).trans (by norm_num)
  calc
    mainDecayExponent 3.7 ≤ (10 : ℝ) ^ (30 : ℕ) := by
      norm_num [mainDecayExponent, caConst, max_def]
      nlinarith
    _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two

private theorem ten_pow_three_thousand_le_tenTower_two :
    (10 : ℝ) ^ (3000 : ℕ) ≤ tenTower 2 := by
  apply ten_pow_le_tenTower_succ 1
  norm_num [tenTower, Real.rpow_natCast]

private theorem epsBW_cube_inv_le_tenTower_two :
    ((epsBW : ℝ) ^ (3 : ℕ))⁻¹ ≤ tenTower 2 := by
  calc
    ((epsBW : ℝ) ^ (3 : ℕ))⁻¹ = (10 : ℝ) ^ (3000 : ℕ) := by
      norm_num [epsBW, ← pow_mul]
    _ ≤ tenTower 2 := ten_pow_three_thousand_le_tenTower_two

private theorem K_fewWhite_main_le_tenTower_six :
    ((K_fewWhite (mainDecayExponent 3.7) : ℕ) : ℝ) ≤ tenTower 6 := by
  let A : ℝ := mainDecayExponent 3.7
  have hA0 : 0 ≤ A := (mainDecayExponent_pos 3.7 (by norm_num)).le
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hA3 : A + 3 ≤ tenTower 3 :=
    tenTower_add_le_succ 2 hA0 (by norm_num) hA
      ((show (3 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
  have hlog : Real.log 10 ≤ tenTower 3 :=
    (Real.log_le_self (by norm_num)).trans
      ((show (10 : ℝ) ≤ tenTower 3 from ten_le_tenTower 3))
  have hnum : (A + 3) * Real.log 10 ≤ tenTower 4 :=
    tenTower_mul_le_succ 3 (by positivity) (Real.log_nonneg (by norm_num))
      (hA3.trans (tenTower_mono (by omega))) hlog
  have hquot : ((A + 3) * Real.log 10) / (epsBW : ℝ) ^ (3 : ℕ)
      ≤ tenTower 5 := by
    rw [div_eq_mul_inv]
    have hnum0 : 0 ≤ (A + 3) * Real.log 10 :=
      mul_nonneg (by linarith) (Real.log_nonneg (by norm_num))
    have hinv0 : 0 ≤ ((epsBW : ℝ) ^ (3 : ℕ))⁻¹ := by
      have heps : (0 : ℝ) ≤ (epsBW : ℝ) := by norm_num [epsBW]
      exact inv_nonneg.2 (pow_nonneg heps 3)
    exact tenTower_mul_le_succ 4 hnum0 hinv0 hnum
      (epsBW_cube_inv_le_tenTower_two.trans (tenTower_mono (by omega)))
  unfold K_fewWhite
  change ((⌈((A + 3) * Real.log 10) / (epsBW : ℝ) ^ 3⌉₊ : ℕ) : ℝ) ≤ tenTower 6
  have harg0 : 0 ≤ ((A + 3) * Real.log 10) / (epsBW : ℝ) ^ (3 : ℕ) := by
    exact div_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by norm_num)))
      (pow_nonneg (by norm_num [epsBW]) 3)
  exact natCeil_le_tenTower_succ 5 harg0 hquot

private theorem R_fewWhite_main_le_tenTower_eleven :
    ((R_fewWhite (mainDecayExponent 3.7) : ℕ) : ℝ) ≤ tenTower 11 := by
  let A : ℝ := mainDecayExponent 3.7
  let K : ℕ := K_fewWhite A
  have hA0 : 0 ≤ A := (mainDecayExponent_pos 3.7 (by norm_num)).le
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hK : (K : ℝ) ≤ tenTower 6 := K_fewWhite_main_le_tenTower_six
  have hK1 : (K : ℝ) + 1 ≤ tenTower 7 :=
    tenTower_add_le_succ 6 (by positivity) (by norm_num) hK (tenTower_one_le 6)
  have hA5 : A + 5 ≤ tenTower 3 :=
    tenTower_add_le_succ 2 hA0 (by norm_num) hA
      ((show (5 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
  have hlog : Real.log 10 ≤ tenTower 3 :=
    (Real.log_le_self (by norm_num)).trans (ten_le_tenTower 3)
  have hprod : (A + 5) * Real.log 10 ≤ tenTower 4 :=
    tenTower_mul_le_succ 3 (by positivity) (Real.log_nonneg (by norm_num))
      hA5 hlog
  have hsum1 : ((K : ℝ) + 1) + (A + 5) * Real.log 10 ≤ tenTower 8 :=
    tenTower_add_le_succ 7 (by positivity) (by positivity) hK1
      (hprod.trans (tenTower_mono (by omega)))
  have hsum : ((K : ℝ) + 1) + (A + 5) * Real.log 10 + 2 ≤ tenTower 9 :=
    tenTower_add_le_succ 8 (by positivity) (by norm_num) hsum1
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 8))
  have hinv : (eps0_manyTri : ℝ)⁻¹ ≤ tenTower 2 := by
    calc
      (eps0_manyTri : ℝ)⁻¹ ≤ (10 : ℝ) ^ (30 : ℕ) := by
        norm_num [eps0_manyTri, p_whiteExit, min_def]
      _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two
  have hquot : (((K : ℝ) + 1) + (A + 5) * Real.log 10 + 2) / eps0_manyTri
      ≤ tenTower 10 := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ 9 (by positivity) (inv_nonneg.2 eps0_manyTri_pos.le) hsum
      (hinv.trans (tenTower_mono (by omega)))
  unfold R_fewWhite
  change ((⌈(((K : ℝ) + 1) + (A + 5) * Real.log 10 + 2) / eps0_manyTri⌉₊ : ℕ) : ℝ)
      ≤ tenTower 11
  exact natCeil_le_tenTower_succ 10 (div_nonneg (by positivity) eps0_manyTri_pos.le) hquot

private theorem P_fewWhite_main_add_one_le_tenTower_thirty_one :
    ((P_fewWhite (mainDecayExponent 3.7) : ℕ) : ℝ) + 1 ≤ tenTower 31 := by
  let A : ℝ := mainDecayExponent 3.7
  have hA0 : 0 ≤ A := (mainDecayExponent_pos 3.7 (by norm_num)).le
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hA00 : 0 ≤ A0_fewEstar := by
    unfold A0_fewEstar A0_estarScaled
    exact le_trans zero_le_one (le_trans (le_max_left _ _) (le_max_right _ _))
  have h2A : 2 * A ≤ tenTower 20 := by
    exact tenTower_mul_le_succ 19 (by norm_num) hA0
      ((show (2 : ℝ) ≤ tenTower 19 from
        (show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 19)))
      (hA.trans (tenTower_mono (by omega)))
  have hAenc : 2 * A + A0_fewEstar ≤ tenTower 21 :=
    tenTower_add_le_succ 20 (mul_nonneg (by norm_num) hA0) hA00 h2A
      (A0_fewEstar_le_tenTower_nineteen.trans (tenTower_mono (by omega)))
  have hK1 : ((K_fewWhite A + 1 : ℕ) : ℝ) ≤ tenTower 7 := by
    push_cast
    exact tenTower_add_le_succ 6 (by positivity) (by norm_num)
      K_fewWhite_main_le_tenTower_six (tenTower_one_le 6)
  have hR : ((R_fewWhite A : ℕ) : ℝ) ≤ tenTower 11 :=
    R_fewWhite_main_le_tenTower_eleven
  unfold P_fewWhite
  exact encWindowIter_le_tenTower_add_six 25
    (add_nonneg (mul_nonneg (by norm_num) hA0) hA00)
    (hAenc.trans (tenTower_mono (by omega)))
    (hK1.trans (tenTower_mono (by omega)))
    (hR.trans (tenTower_mono (by omega)))

private theorem B_fewWhite_main_le_tenTower_thirty_five :
    B_fewWhite (mainDecayExponent 3.7) ≤ tenTower 35 := by
  let A : ℝ := mainDecayExponent 3.7
  have hA0 : 0 ≤ A := (mainDecayExponent_pos 3.7 (by norm_num)).le
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hA00 : 0 ≤ A0_fewEstar := by
    unfold A0_fewEstar A0_estarScaled
    exact le_trans zero_le_one (le_trans (le_max_left _ _) (le_max_right _ _))
  have h2A : 2 * A ≤ tenTower 20 := by
    exact tenTower_mul_le_succ 19 (by norm_num) hA0
      ((show (2 : ℝ) ≤ tenTower 19 from
        (show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 19)))
      (hA.trans (tenTower_mono (by omega)))
  have hAenc : 2 * A + A0_fewEstar ≤ tenTower 21 :=
    tenTower_add_le_succ 20 (mul_nonneg (by norm_num) hA0) hA00 h2A
      (A0_fewEstar_le_tenTower_nineteen.trans (tenTower_mono (by omega)))
  have hpow4 : (4 : ℝ) ^ (2 * A + A0_fewEstar) ≤ tenTower 23 :=
    rpow_le_tenTower_add_two 21 (by norm_num)
      (add_nonneg (mul_nonneg (by norm_num) hA0) hA00)
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 21)) hAenc
  have hP1 : 1 + (P_fewWhite A : ℝ) ≤ tenTower 31 := by
    simpa [add_comm] using P_fewWhite_main_add_one_le_tenTower_thirty_one
  have hcube : (1 + (P_fewWhite A : ℝ)) ^ (3 : ℕ) ≤ tenTower 33 := by
    rw [← Real.rpow_natCast]
    exact rpow_le_tenTower_add_two 31 (by positivity) (by norm_num) hP1
      ((show (3 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 31))
  unfold B_fewWhite
  exact tenTower_mul_le_succ 34
    (Real.rpow_nonneg (by norm_num) _)
    (pow_nonneg (by positivity) 3)
    (hpow4.trans (tenTower_mono (by omega)))
    (hcube.trans (tenTower_mono (by omega)))

private theorem T_expRpow_main_colTail_cast_le_tenTower_fifteen :
    ((T_expRpow (mainDecayExponent 3.7) (c_fpColTail / 16960)
      (1 / (4 * C_fpColTail)) : ℕ) : ℝ) ≤ tenTower 15 := by
  let A : ℝ := mainDecayExponent 3.7
  let ρ : ℝ := c_fpColTail / 16960
  let δ : ℝ := 1 / (4 * C_fpColTail)
  have hA0 : 0 < A := mainDecayExponent_pos 3.7 (by norm_num)
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity [c_fpColTail_pos]
  have hρinv : ρ⁻¹ ≤ tenTower 2 := by
    calc
      ρ⁻¹ ≤ (10 : ℝ) ^ (30 : ℕ) := by
        dsimp [ρ]
        norm_num [c_fpColTail_eq]
      _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two
  have hδ0 : 0 < δ := by dsimp [δ]; positivity [C_fpColTail_pos]
  have hδinv : δ⁻¹ = 4 * C_fpColTail := by
    dsimp [δ]
    field_simp [ne_of_gt C_fpColTail_pos]
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := by
    rw [hδinv]
    unfold C_fpColTail
    nlinarith [C_fpColDev_pos]
  have hδinvT : δ⁻¹ ≤ tenTower 12 := by
    rw [hδinv]
    have h4 : (4 : ℝ) ≤ tenTower 11 :=
      (show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 11)
    exact tenTower_mul_le_succ 11 (by norm_num) C_fpColTail_pos.le h4
      C_fpColTail_le_tenTower_eleven
  have hε0 : 0 < ρ / (2 * A) := div_pos hρ0 (mul_pos two_pos hA0)
  have hbaseEq : 2 / (ρ / (2 * A)) = 4 * A * ρ⁻¹ := by
    field_simp [ne_of_gt hρ0, ne_of_gt hA0]
    ring
  have h4A : 4 * A ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) hA0.le
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hA
  have hbase : 2 / (ρ / (2 * A)) ≤ tenTower 4 := by
    rw [hbaseEq]
    exact tenTower_mul_le_succ 3 (by positivity) (inv_nonneg.2 hρ0.le)
      (h4A.trans (tenTower_mono (by omega)))
      (hρinv.trans (tenTower_mono (by omega)))
  have hbaseSq : (2 / (ρ / (2 * A))) ^ (2 : ℕ) ≤ tenTower 5 := by
    rw [pow_two]
    exact tenTower_mul_le_succ 4 (div_nonneg (by norm_num) hε0.le)
      (div_nonneg (by norm_num) hε0.le) hbase hbase
  have hlogLinCeil : ((⌈(2 / (ρ / (2 * A))) ^ (2 : ℕ)⌉₊ : ℕ) : ℝ)
      ≤ tenTower 6 := natCeil_le_tenTower_succ 5
        (pow_nonneg (div_nonneg (by norm_num) hε0.le) 2) hbaseSq
  have hTlog : ((T_logLin (ρ / (2 * A)) : ℕ) : ℝ) ≤ tenTower 7 := by
    unfold T_logLin
    push_cast
    exact tenTower_add_le_succ 6 (by positivity) (by norm_num) hlogLinCeil
      (tenTower_one_le 6)
  have hlogδ0 : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg hδinv1
  have hlogδ : Real.log δ⁻¹ ≤ tenTower 12 :=
    (Real.log_le_self (inv_nonneg.2 hδ0.le)).trans hδinvT
  have hρ2invEq : (ρ / 2)⁻¹ = 2 * ρ⁻¹ := by
    field_simp [ne_of_gt hρ0]
  have hρ2inv : (ρ / 2)⁻¹ ≤ tenTower 3 := by
    rw [hρ2invEq]
    exact tenTower_mul_le_succ 2 (by norm_num) (inv_nonneg.2 hρ0.le)
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hρinv
  have hExpArg : Real.log δ⁻¹ / (ρ / 2) ≤ tenTower 13 := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ 12 hlogδ0 (inv_nonneg.2 (div_nonneg hρ0.le (by norm_num)))
      hlogδ (hρ2inv.trans (tenTower_mono (by omega)))
  have hTexp : ((T_expNeg (ρ / 2) δ : ℕ) : ℝ) ≤ tenTower 14 := by
    unfold T_expNeg
    exact natCeil_le_tenTower_succ 13
      (div_nonneg hlogδ0 (div_nonneg hρ0.le (by norm_num))) hExpArg
  unfold T_expRpow
  change ((1 + T_logLin (ρ / (2 * A)) + T_expNeg (ρ / 2) δ : ℕ) : ℝ) ≤ tenTower 15
  push_cast
  have hhead : (1 : ℝ) + T_logLin (ρ / (2 * A)) ≤ tenTower 8 :=
    tenTower_add_le_succ 7 (by norm_num) (by positivity) (tenTower_one_le 7) hTlog
  exact tenTower_add_le_succ 14 (by positivity) (by positivity)
    (hhead.trans (tenTower_mono (by omega))) hTexp

private theorem T_colTail_main_cast_le_tenTower_thirty_four :
    ((T_colTail (mainDecayExponent 3.7) (P_fewWhite (mainDecayExponent 3.7)) : ℕ) : ℝ)
      ≤ tenTower 34 := by
  let A : ℝ := mainDecayExponent 3.7
  let P : ℕ := P_fewWhite A
  have hP1 : (P : ℝ) + 1 ≤ tenTower 31 :=
    P_fewWhite_main_add_one_le_tenTower_thirty_one
  have h400 : (400 : ℝ) ≤ tenTower 31 :=
    (show (400 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega)))
  have hp : 400 * ((P : ℝ) + 1) ≤ tenTower 32 :=
    tenTower_mul_le_succ 31 (by norm_num) (by positivity) h400 hP1
  have hp32 : 400 * ((P : ℝ) + 1) + 32 ≤ tenTower 33 :=
    tenTower_add_le_succ 32 (by positivity) (by norm_num) hp
      ((show (32 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega))))
  unfold T_colTail
  change ((400 * (P + 1) + 32 + T_expRpow A (c_fpColTail / 16960)
    (1 / (4 * C_fpColTail)) : ℕ) : ℝ) ≤ tenTower 34
  push_cast
  exact tenTower_add_le_succ 33 (by positivity) (by positivity) hp32
    (T_expRpow_main_colTail_cast_le_tenTower_fifteen.trans (tenTower_mono (by omega)))

/-! ## The remaining §7 thresholds -/

private theorem T_outStrip_cast_le_tenTower_seventeen :
    ((T_outStrip : ℕ) : ℝ) ≤ tenTower 17 := by
  let c : ℝ := c_fpLocation
  let a : ℝ := c ^ (2 : ℕ) / 20
  let D : ℝ := C_fpCol * ((1 - Real.exp (-a))⁻¹ + (1 - Real.exp (-c))⁻¹) + 1
  have hc0 : 0 < c := by dsimp [c]; exact c_fpLocation_pos
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hia : (1 - Real.exp (-a))⁻¹ ≤ tenTower 2 := by
    calc
      (1 - Real.exp (-a))⁻¹ ≤ 1 + 1 / a := by
        simpa [one_div] using one_div_one_sub_exp_neg_le ha0
      _ ≤ (10 : ℝ) ^ (30 : ℕ) := by
        dsimp [a, c]
        norm_num [c_fpLocation_eq]
      _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two
  have hic : (1 - Real.exp (-c))⁻¹ ≤ tenTower 2 := by
    calc
      (1 - Real.exp (-c))⁻¹ ≤ 1 + 1 / c := by
        simpa [one_div] using one_div_one_sub_exp_neg_le hc0
      _ ≤ (10 : ℝ) ^ (30 : ℕ) := by
        dsimp [c]
        norm_num [c_fpLocation_eq]
      _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two
  have hia0 : 0 ≤ (1 - Real.exp (-a))⁻¹ := by
    have : 0 < 1 - Real.exp (-a) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      linarith
    positivity
  have hic0 : 0 ≤ (1 - Real.exp (-c))⁻¹ := by
    have : 0 < 1 - Real.exp (-c) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      linarith
    positivity
  have hisum : (1 - Real.exp (-a))⁻¹ + (1 - Real.exp (-c))⁻¹ ≤ tenTower 3 :=
    tenTower_add_le_succ 2 hia0 hic0 hia hic
  have hprod : C_fpCol * ((1 - Real.exp (-a))⁻¹ + (1 - Real.exp (-c))⁻¹)
      ≤ tenTower 10 :=
    tenTower_mul_le_succ 9 C_fpCol_pos.le (add_nonneg hia0 hic0)
      C_fpCol_le_tenTower_nine (hisum.trans (tenTower_mono (by omega)))
  have hD : D ≤ tenTower 11 := by
    dsimp [D]
    exact tenTower_add_le_succ 10 (mul_nonneg C_fpCol_pos.le (add_nonneg hia0 hic0))
      (by norm_num) hprod (tenTower_one_le 10)
  have hD1 : 1 ≤ D := by
    dsimp [D]
    have hp : 0 ≤ C_fpCol *
        ((1 - Real.exp (-a))⁻¹ + (1 - Real.exp (-c))⁻¹) :=
      mul_nonneg C_fpCol_pos.le (add_nonneg hia0 hic0)
    linarith
  have h8D0 : 0 ≤ 8 * D := mul_nonneg (by norm_num) (le_trans zero_le_one hD1)
  have h8D1 : 1 ≤ 8 * D := by nlinarith
  have h8D : 8 * D ≤ tenTower 12 :=
    tenTower_mul_le_succ 11 (by norm_num) (le_trans zero_le_one hD1)
      ((show (8 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 11)) hD
  have hlog0 : 0 ≤ Real.log (8 * D) := Real.log_nonneg h8D1
  have hlog : Real.log (8 * D) ≤ tenTower 12 := log_le_tenTower 12 h8D0 h8D
  have hnum : 5 * Real.log (8 * D) ≤ tenTower 13 :=
    tenTower_mul_le_succ 12 (by norm_num) hlog0
      ((show (5 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 12)) hlog
  have hgamma : min c (c ^ (2 : ℕ) / 20) = (1 : ℝ) / 3276800000 := by
    dsimp [c]
    norm_num [c_fpLocation_eq, min_def]
  have hgamma0 : 0 < min c (c ^ (2 : ℕ) / 20) := by rw [hgamma]; norm_num
  have hgammaInv : (min c (c ^ (2 : ℕ) / 20))⁻¹ ≤ tenTower 2 := by
    rw [hgamma]
    norm_num only [one_div, inv_inv]
    exact (show (3276800000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hquot : 5 * Real.log (8 * D) / min c (c ^ (2 : ℕ) / 20) ≤ tenTower 14 := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ 13 (mul_nonneg (by norm_num) hlog0)
      (inv_nonneg.2 hgamma0.le) hnum
      (hgammaInv.trans (tenTower_mono (by omega)))
  have harg : 5 * Real.log (8 * D) / min c (c ^ (2 : ℕ) / 20) + 3 ≤ tenTower 15 :=
    tenTower_add_le_succ 14 (div_nonneg (mul_nonneg (by norm_num) hlog0) hgamma0.le)
      (by norm_num) hquot
      ((show (3 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 14))
  have hceil : ((Nat.ceil
      (5 * Real.log (8 * D) / min c (c ^ (2 : ℕ) / 20) + 3) : ℕ) : ℝ)
      ≤ tenTower 16 :=
    natCeil_le_tenTower_succ 15
      (add_nonneg (div_nonneg (mul_nonneg (by norm_num) hlog0) hgamma0.le) (by norm_num)) harg
  unfold T_outStrip T_gaussColTail
  change ((max 25 (Nat.ceil
      (5 * Real.log (8 * D) / min c (c ^ (2 : ℕ) / 20) + 3) + 1) : ℕ) : ℝ)
      ≤ tenTower 17
  push_cast
  apply max_le
  · exact (show (25 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega)))
  · have hadd : ((Nat.ceil
        (5 * Real.log (8 * D) / min c (c ^ (2 : ℕ) / 20) + 3) : ℕ) : ℝ) + 1
        ≤ 2 * tenTower 16 := by linarith [tenTower_one_le 16]
    exact hadd.trans (tenTower_two_mul_le_succ 16)

private theorem Cthr_fewWhite_main_cast_le_tenTower_thirty_eight :
    ((Cthr_fewWhite (mainDecayExponent 3.7) : ℕ) : ℝ) ≤ tenTower 38 := by
  let A : ℝ := mainDecayExponent 3.7
  have hA0 : 0 < A := by dsimp [A]; exact mainDecayExponent_pos 3.7 (by norm_num)
  have hA1 : 1 ≤ A := by
    dsimp [A]
    unfold mainDecayExponent
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hterm : 0 ≤ caConst 3.7 ^ 2 * Real.log 2 :=
      mul_nonneg (sq_nonneg _) hlog
    norm_num
    linarith
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hten30 : ((10 ^ 30 : ℕ) : ℝ) ≤ tenTower 38 := by
    have hcast : ((10 ^ 30 : ℕ) : ℝ) = (10 : ℝ) ^ (30 : ℕ) := by norm_num
    rw [hcast]
    exact ten_pow_thirty_le_tenTower_two.trans
      (tenTower_mono (show (2 : ℕ) ≤ 38 by norm_num))
  have hcol : ((T_colTail A (P_fewWhite A) : ℕ) : ℝ) ≤ tenTower 38 :=
    T_colTail_main_cast_le_tenTower_thirty_four.trans (tenTower_mono (by omega))
  have hg : ((g_manyTri : ℕ) : ℝ) ≤ tenTower 17 := by
    simpa [g_manyTri, T_whiteExitDeep] using T_outStrip_cast_le_tenTower_seventeen
  have h10g : (10 : ℝ) * (g_manyTri : ℝ) ≤ tenTower 18 := by
    exact tenTower_mul_le_succ 17 (by norm_num) (by positivity)
      (ten_le_tenTower 17) hg
  have hB0 : 0 ≤ B_fewWhite A := by unfold B_fewWhite; positivity
  have hBpow : B_fewWhite A ^ (2.5 : ℝ) ≤ tenTower 37 :=
    rpow_le_tenTower_add_two 35 hB0 (by norm_num)
      B_fewWhite_main_le_tenTower_thirty_five
      (show (2.5 : ℝ) ≤ tenTower 35 by
        exact (show (2.5 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 35))
  have hBceil : ((⌈B_fewWhite A ^ (2.5 : ℝ)⌉₊ : ℕ) : ℝ) ≤ tenTower 38 :=
    natCeil_le_tenTower_succ 37 (Real.rpow_nonneg hB0 _) hBpow
  have hAinv : A⁻¹ ≤ tenTower 2 := by
    have : A⁻¹ ≤ 1 := (inv_le_one₀ hA0).2 hA1
    exact this.trans (tenTower_one_le 2)
  have h500 : (500 : ℝ) ≤ tenTower 2 :=
    (show (500 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have h500pow : (500 : ℝ) ^ (1 / A) ≤ tenTower 4 := by
    rw [one_div]
    exact rpow_le_tenTower_add_two 2 (by norm_num) (inv_nonneg.2 hA0.le) h500 hAinv
  have h10pow : 10 * (500 : ℝ) ^ (1 / A) ≤ tenTower 5 :=
    tenTower_mul_le_succ 4 (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      (ten_le_tenTower 4) (h500pow.trans (tenTower_mono (by omega)))
  have hlast : ((⌈10 * (500 : ℝ) ^ (1 / A)⌉₊ : ℕ) : ℝ) ≤ tenTower 6 :=
    natCeil_le_tenTower_succ 5 (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
      h10pow
  unfold Cthr_fewWhite
  change ((max (max (10 ^ 30) (T_colTail A (P_fewWhite A)))
    (max (10 * g_manyTri)
      (max ⌈B_fewWhite A ^ (2.5 : ℝ)⌉₊ ⌈10 * (500 : ℝ) ^ (1 / A)⌉₊)) : ℕ) : ℝ)
      ≤ tenTower 38
  push_cast
  exact max_le (max_le hten30 hcol)
    (max_le (h10g.trans (tenTower_mono (show (18 : ℕ) ≤ 38 by norm_num)))
      (max_le hBceil (hlast.trans (tenTower_mono (by omega)))))

private theorem quarter_le_log_four_thirds : (1 : ℝ) / 4 ≤ Real.log (4 / 3) := by
  have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 / 3 by norm_num)
  norm_num at h ⊢
  linarith

private theorem log_four_thirds_inv_le_four : (Real.log (4 / 3))⁻¹ ≤ (4 : ℝ) := by
  have hlog : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  rw [inv_le_iff_one_le_mul₀ hlog]
  nlinarith [quarter_le_log_four_thirds]

private theorem K_geom_cast_le_tenTower_add_three {b : ℝ} (h : ℕ)
    (hb : 0 < b) (hbinv1 : 1 ≤ (b / 2)⁻¹) (hbinv : b⁻¹ ≤ tenTower h) :
    ((K_geom b : ℕ) : ℝ) ≤ tenTower (h + 3) := by
  have hxEq : (b / 2)⁻¹ = 2 * b⁻¹ := by field_simp [ne_of_gt hb]
  have hx0 : 0 ≤ (b / 2)⁻¹ := inv_nonneg.2 (div_nonneg hb.le (by norm_num))
  have hx : (b / 2)⁻¹ ≤ tenTower (h + 1) := by
    rw [hxEq]
    exact tenTower_mul_le_succ h (by norm_num) (inv_nonneg.2 hb.le)
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower h)) hbinv
  have hlog0 : 0 ≤ Real.log (b / 2)⁻¹ := Real.log_nonneg hbinv1
  have hlog : Real.log (b / 2)⁻¹ ≤ tenTower (h + 1) :=
    log_le_tenTower (h + 1) hx0 hx
  have hquot : Real.log (b / 2)⁻¹ / Real.log (4 / 3) ≤ tenTower (h + 2) := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ (h + 1) hlog0
      (inv_nonneg.2 (Real.log_pos (by norm_num)).le) hlog
      (log_four_thirds_inv_le_four.trans
        ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower (h + 1))))
  unfold K_geom
  exact natCeil_le_tenTower_succ (h + 2)
    (div_nonneg hlog0 (Real.log_pos (by norm_num)).le) hquot

private theorem T_powGeom_cast_le_tenTower_add_eight {k : ℕ} {b : ℝ} (h : ℕ)
    (hk : (k : ℝ) ≤ tenTower h) (hb : 0 < b)
    (hbinv1 : 1 ≤ (b / 2)⁻¹) (hbinv : b⁻¹ ≤ tenTower h) :
    ((T_powGeom k b : ℕ) : ℝ) ≤ tenTower (h + 8) := by
  let L : ℝ := Real.log (4 / 3)
  have hL0 : 0 < L := by dsimp [L]; exact Real.log_pos (by norm_num)
  have hLinv : L⁻¹ ≤ 4 := by dsimp [L]; exact log_four_thirds_inv_le_four
  have hk1 : (k : ℝ) + 1 ≤ tenTower (h + 1) :=
    tenTower_add_le_succ h (by positivity) (by norm_num) hk (tenTower_one_le h)
  have hbaseEq : 2 / (L / (2 * ((k : ℝ) + 1))) = 4 * ((k : ℝ) + 1) * L⁻¹ := by
    field_simp [ne_of_gt hL0]
    ring
  have h4k : 4 * ((k : ℝ) + 1) ≤ tenTower (h + 2) :=
    tenTower_mul_le_succ (h + 1) (by norm_num) (by positivity)
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower (h + 1))) hk1
  have hbase0 : 0 ≤ 2 / (L / (2 * ((k : ℝ) + 1))) := by positivity
  have hbase : 2 / (L / (2 * ((k : ℝ) + 1))) ≤ tenTower (h + 3) := by
    rw [hbaseEq]
    exact tenTower_mul_le_succ (h + 2) (by positivity) (inv_nonneg.2 hL0.le) h4k
      (hLinv.trans ((show (4 : ℝ) ≤ 10 by norm_num).trans
        (ten_le_tenTower (h + 2))))
  have hsq : (2 / (L / (2 * ((k : ℝ) + 1)))) ^ (2 : ℕ) ≤ tenTower (h + 4) := by
    rw [pow_two]
    exact tenTower_mul_le_succ (h + 3) hbase0 hbase0 hbase hbase
  have hceilSq : ((⌈(2 / (L / (2 * ((k : ℝ) + 1)))) ^ (2 : ℕ)⌉₊ : ℕ) : ℝ)
      ≤ tenTower (h + 5) :=
    natCeil_le_tenTower_succ (h + 4) (pow_nonneg hbase0 2) hsq
  have hxEq : (b / 2)⁻¹ = 2 * b⁻¹ := by field_simp [ne_of_gt hb]
  have hx0 : 0 ≤ (b / 2)⁻¹ := inv_nonneg.2 (div_nonneg hb.le (by norm_num))
  have hx : (b / 2)⁻¹ ≤ tenTower (h + 1) := by
    rw [hxEq]
    exact tenTower_mul_le_succ h (by norm_num) (inv_nonneg.2 hb.le)
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower h)) hbinv
  have hlog0 : 0 ≤ Real.log (b / 2)⁻¹ := Real.log_nonneg hbinv1
  have hlog : Real.log (b / 2)⁻¹ ≤ tenTower (h + 1) :=
    log_le_tenTower (h + 1) hx0 hx
  have hhalfInv : (L / 2)⁻¹ = 2 * L⁻¹ := by field_simp [ne_of_gt hL0]
  have hhalfInvT : (L / 2)⁻¹ ≤ tenTower (h + 1) := by
    rw [hhalfInv]
    exact tenTower_mul_le_succ h (by norm_num) (inv_nonneg.2 hL0.le)
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower h))
      (hLinv.trans ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower h)))
  have hquot : Real.log (b / 2)⁻¹ / (L / 2) ≤ tenTower (h + 2) := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ (h + 1) hlog0 (inv_nonneg.2 (div_nonneg hL0.le (by norm_num)))
      hlog hhalfInvT
  have hceilLog : ((⌈Real.log (b / 2)⁻¹ / (L / 2)⌉₊ : ℕ) : ℝ)
      ≤ tenTower (h + 3) :=
    natCeil_le_tenTower_succ (h + 2)
      (div_nonneg hlog0 (div_nonneg hL0.le (by norm_num))) hquot
  unfold T_powGeom
  change ((1 + (⌈(2 / (L / (2 * ((k : ℝ) + 1)))) ^ (2 : ℕ)⌉₊ + 1)
      + ⌈Real.log (b / 2)⁻¹ / (L / 2)⌉₊ : ℕ) : ℝ) ≤ tenTower (h + 8)
  push_cast
  have hs1 : (1 : ℝ) +
      ((⌈(2 / (L / (2 * ((k : ℝ) + 1)))) ^ (2 : ℕ)⌉₊ : ℕ) : ℝ)
      ≤ tenTower (h + 6) :=
    tenTower_add_le_succ (h + 5) (by norm_num) (by positivity)
      (tenTower_one_le (h + 5)) hceilSq
  have hs2 : (1 : ℝ) +
      ((⌈(2 / (L / (2 * ((k : ℝ) + 1)))) ^ (2 : ℕ)⌉₊ : ℕ) : ℝ) + 1
      ≤ tenTower (h + 7) :=
    tenTower_add_le_succ (h + 6) (by positivity) (by norm_num) hs1
      (tenTower_one_le (h + 6))
  exact tenTower_add_le_succ (h + 7) (by positivity) (by positivity)
    (by simpa [add_assoc] using hs2)
    (hceilLog.trans (tenTower_mono (by omega)))

private theorem deltaBW_le_two : deltaBW ≤ (2 : ℝ) := by
  have heps0 : 0 ≤ (epsBW : ℝ) := by norm_num [epsBW]
  have heps1 : (epsBW : ℝ) ≤ 1 := by
    have hepsEq : (epsBW : ℝ) = ((10 : ℝ) ^ (1000 : ℕ))⁻¹ := by
      norm_num [epsBW]
    rw [hepsEq]
    exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hcube : (epsBW : ℝ) ^ (3 : ℕ) ≤ 1 := pow_le_one₀ heps0 heps1
  have he : (epsBW : ℝ) ^ (3 : ℕ) / 2 ≤ 1 := by
    nlinarith
  have hexp : Real.exp ((epsBW : ℝ) ^ (3 : ℕ) / 2) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr he
  unfold deltaBW
  linarith [Real.exp_one_lt_three]

private theorem deltaBW_inv_le_tenTower_three : deltaBW⁻¹ ≤ tenTower 3 := by
  let e : ℝ := (epsBW : ℝ) ^ (3 : ℕ) / 2
  have he0 : 0 < e := by dsimp [e]; norm_num [epsBW]
  have heδ : e ≤ deltaBW := by
    dsimp [e]
    unfold deltaBW
    linarith [Real.add_one_le_exp ((epsBW : ℝ) ^ (3 : ℕ) / 2)]
  have hinv : deltaBW⁻¹ ≤ e⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le he0 heδ
  have heq : e⁻¹ = 2 * ((epsBW : ℝ) ^ (3 : ℕ))⁻¹ := by
    dsimp [e]
    field_simp [show (epsBW : ℝ) ^ (3 : ℕ) ≠ 0 by norm_num [epsBW]]
  have heT : e⁻¹ ≤ tenTower 3 := by
    rw [heq]
    exact tenTower_mul_le_succ 2 (by norm_num)
      (inv_nonneg.2 (pow_nonneg (by norm_num [epsBW]) 3))
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
      epsBW_cube_inv_le_tenTower_two
  exact hinv.trans heT

private theorem C_hold_main_cast_le_tenTower_eighteen :
    ((C_hold (mainDecayExponent 3.7) : ℕ) : ℝ) ≤ tenTower 18 := by
  let A : ℝ := mainDecayExponent 3.7
  let b₂ : ℝ := deltaBW / 3 * (2 : ℝ) ^ (-A)
  let b₃ : ℝ := deltaBW / 3 * (3 : ℝ) ^ (-A)
  have hA0 : 0 < A := by dsimp [A]; exact mainDecayExponent_pos 3.7 (by norm_num)
  have hA1 : 1 ≤ A := by
    dsimp [A]
    unfold mainDecayExponent
    have hterm : 0 ≤ caConst 3.7 ^ 2 * Real.log 2 :=
      mul_nonneg (sq_nonneg _) (Real.log_nonneg (by norm_num))
    norm_num
    linarith
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hAinv : A⁻¹ ≤ tenTower 2 :=
    ((inv_le_one₀ hA0).2 hA1).trans (tenTower_one_le 2)
  have h2A : (2 : ℝ) ^ A ≤ tenTower 4 :=
    rpow_le_tenTower_add_two 2 (by norm_num) hA0.le
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hA
  have h3A : (3 : ℝ) ^ A ≤ tenTower 4 :=
    rpow_le_tenTower_add_two 2 (by norm_num) hA0.le
      ((show (3 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hA
  have hb₂0 : 0 < b₂ := by dsimp [b₂]; positivity [deltaBW_pos]
  have hb₃0 : 0 < b₃ := by dsimp [b₃]; positivity [deltaBW_pos]
  have hb₂invEq : b₂⁻¹ = 3 * deltaBW⁻¹ * (2 : ℝ) ^ A := by
    have hp0 : 0 < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
    dsimp [b₂]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [ne_of_gt deltaBW_pos, ne_of_gt hp0]
  have hb₃invEq : b₃⁻¹ = 3 * deltaBW⁻¹ * (3 : ℝ) ^ A := by
    have hp0 : 0 < (3 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
    dsimp [b₃]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    field_simp [ne_of_gt deltaBW_pos, ne_of_gt hp0]
  have h3δinv : 3 * deltaBW⁻¹ ≤ tenTower 4 :=
    tenTower_mul_le_succ 3 (by norm_num) (inv_nonneg.2 deltaBW_pos.le)
      ((show (3 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 3))
      deltaBW_inv_le_tenTower_three
  have hb₂inv : b₂⁻¹ ≤ tenTower 5 := by
    rw [hb₂invEq]
    exact tenTower_mul_le_succ 4
      (mul_nonneg (by norm_num) (inv_nonneg.2 deltaBW_pos.le))
      (Real.rpow_nonneg (by norm_num) _)
      h3δinv h2A
  have hb₃inv : b₃⁻¹ ≤ tenTower 5 := by
    rw [hb₃invEq]
    exact tenTower_mul_le_succ 4
      (mul_nonneg (by norm_num) (inv_nonneg.2 deltaBW_pos.le))
      (Real.rpow_nonneg (by norm_num) _)
      h3δinv h3A
  have hb₂le : b₂ ≤ 1 := by
    have hp : (2 : ℝ) ^ (-A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    dsimp [b₂]
    have hp0 : 0 ≤ (2 : ℝ) ^ (-A) := Real.rpow_nonneg (by norm_num) _
    nlinarith [deltaBW_le_two]
  have hb₃le : b₃ ≤ 1 := by
    have hp : (3 : ℝ) ^ (-A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    dsimp [b₃]
    have hp0 : 0 ≤ (3 : ℝ) ^ (-A) := Real.rpow_nonneg (by norm_num) _
    nlinarith [deltaBW_le_two]
  have hb₂halfInv1 : 1 ≤ (b₂ / 2)⁻¹ :=
    (one_le_inv₀ (div_pos hb₂0 two_pos)).2 (by linarith)
  have hb₃halfInv1 : 1 ≤ (b₃ / 2)⁻¹ :=
    (one_le_inv₀ (div_pos hb₃0 two_pos)).2 (by linarith)
  have hK : ((K_hold A : ℕ) : ℝ) ≤ tenTower 8 := by
    unfold K_hold
    exact K_geom_cast_le_tenTower_add_three 5 hb₂0 hb₂halfInv1 hb₂inv
  have hkceil : ((⌈A⌉₊ : ℕ) : ℝ) ≤ tenTower 3 :=
    natCeil_le_tenTower_succ 2 hA0.le hA
  have hT : ((T_hold A : ℕ) : ℝ) ≤ tenTower 13 := by
    unfold T_hold
    exact T_powGeom_cast_le_tenTower_add_eight 5
      (hkceil.trans (tenTower_mono (by omega))) hb₃0 hb₃halfInv1 hb₃inv
  let u : ℝ := deltaBW / 3
  have hu0 : 0 < u := by dsimp [u]; positivity [deltaBW_pos]
  have hu2 : u ≤ 2 := by dsimp [u]; linarith [deltaBW_le_two]
  have hlogLower : u / 2 ≤ Real.log (1 + u) := by
    have hfrac := Real.le_log_one_add_of_nonneg hu0.le
    have hden : 0 < u + 2 := by linarith
    have hhalf : u / 2 ≤ 2 * u / (u + 2) := by
      rw [le_div_iff₀ hden]
      nlinarith
    exact hhalf.trans hfrac
  have hz0 : 0 < Real.log (1 + u) * A⁻¹ :=
    mul_pos (Real.log_pos (by linarith)) (inv_pos.2 hA0)
  have hgapLower : u / (2 * A) ≤ cHold A - 1 := by
    have hz : u / (2 * A) ≤ Real.log (1 + u) * A⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev]
      have := mul_le_mul_of_nonneg_right hlogLower (inv_nonneg.2 hA0.le)
      nlinarith
    have hexp := Real.add_one_le_exp (Real.log (1 + u) * A⁻¹)
    have hbasePos : 0 < 1 + deltaBW / 3 := by linarith [deltaBW_pos]
    unfold cHold
    rw [Real.rpow_def_of_pos hbasePos]
    change u / (2 * A) ≤ Real.exp (Real.log (1 + u) * A⁻¹) - 1
    linarith
  have hsmall0 : 0 < u / (2 * A) := div_pos hu0 (mul_pos two_pos hA0)
  have hgapInvRaw : (cHold A - 1)⁻¹ ≤ (u / (2 * A))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hsmall0 hgapLower
  have hsmallInvEq : (u / (2 * A))⁻¹ = 6 * A * deltaBW⁻¹ := by
    dsimp [u]
    field_simp [ne_of_gt deltaBW_pos, ne_of_gt hA0]
    ring
  have h6A : 6 * A ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) hA0.le
      ((show (6 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hA
  have hgapInv : (cHold A - 1)⁻¹ ≤ tenTower 4 := by
    apply hgapInvRaw.trans
    rw [hsmallInvEq]
    exact tenTower_mul_le_succ 3 (by positivity) (inv_nonneg.2 deltaBW_pos.le)
      h6A deltaBW_inv_le_tenTower_three
  have hbase : 1 + u ≤ tenTower 2 := by
    have hu : u ≤ 1 := by dsimp [u]; linarith [deltaBW_le_two]
    exact (show 1 + u ≤ 10 by linarith).trans (ten_le_tenTower 2)
  have hcHold : cHold A ≤ tenTower 4 := by
    have hbase0 : 0 ≤ 1 + deltaBW / 3 := by linarith [deltaBW_pos]
    unfold cHold
    exact rpow_le_tenTower_add_two 2 hbase0 (inv_nonneg.2 hA0.le)
      (by simpa [u] using hbase) hAinv
  have hcHold0 : 0 < cHold A := (one_lt_cHold A hA0).trans' zero_lt_one
  have hgap0 : 0 < cHold A - 1 := sub_pos.mpr (one_lt_cHold A hA0)
  have hKM : (K_hold A : ℝ) * cHold A ≤ tenTower 9 :=
    tenTower_mul_le_succ 8 (by positivity) hcHold0.le hK
      (hcHold.trans (tenTower_mono (by omega)))
  have hratio : (K_hold A : ℝ) * cHold A / (cHold A - 1) ≤ tenTower 10 := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ 9 (mul_nonneg (by positivity) hcHold0.le)
      (inv_nonneg.2 hgap0.le)
      hKM (hgapInv.trans (tenTower_mono (by omega)))
  have hM : ((M1_hold A : ℕ) : ℝ) ≤ tenTower 11 := by
    unfold M1_hold
    exact natCeil_le_tenTower_succ 10
      (div_nonneg (mul_nonneg (by positivity) hcHold0.le) hgap0.le) hratio
  unfold C_hold
  change ((K_hold A + M1_hold A + 2 * T_hold A + 4 : ℕ) : ℝ) ≤ tenTower 18
  push_cast
  have hKMsum : (K_hold A : ℝ) + M1_hold A ≤ tenTower 12 :=
    tenTower_add_le_succ 11 (by positivity) (by positivity)
      (hK.trans (tenTower_mono (by omega))) hM
  have h2T : (2 : ℝ) * T_hold A ≤ tenTower 14 :=
    tenTower_mul_le_succ 13 (by norm_num) (by positivity)
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 13)) hT
  have hs : (K_hold A : ℝ) + M1_hold A + 2 * T_hold A ≤ tenTower 15 :=
    tenTower_add_le_succ 14 (by positivity) (by positivity)
      (hKMsum.trans (tenTower_mono (by omega))) h2T
  exact tenTower_add_le_succ 17 (by positivity) (by norm_num)
    (hs.trans (tenTower_mono (by omega)))
    ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 17))

private theorem T_logLin_cast_le_tenTower_add_four {ε : ℝ} (h : ℕ)
    (hε : 0 < ε) (hεinv : ε⁻¹ ≤ tenTower h) :
    ((T_logLin ε : ℕ) : ℝ) ≤ tenTower (h + 4) := by
  have hbaseEq : 2 / ε = 2 * ε⁻¹ := by ring
  have hbase : 2 / ε ≤ tenTower (h + 1) := by
    rw [hbaseEq]
    exact tenTower_mul_le_succ h (by norm_num) (inv_nonneg.2 hε.le)
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower h)) hεinv
  have hbase0 : 0 ≤ 2 / ε := div_nonneg (by norm_num) hε.le
  have hsq : (2 / ε) ^ (2 : ℕ) ≤ tenTower (h + 2) := by
    rw [pow_two]
    exact tenTower_mul_le_succ (h + 1) hbase0 hbase0 hbase hbase
  have hceil : ((⌈(2 / ε) ^ (2 : ℕ)⌉₊ : ℕ) : ℝ) ≤ tenTower (h + 3) :=
    natCeil_le_tenTower_succ (h + 2) (pow_nonneg hbase0 2) hsq
  unfold T_logLin
  push_cast
  exact tenTower_add_le_succ (h + 3) (by positivity) (by norm_num) hceil
    (tenTower_one_le (h + 3))

private theorem T_expNeg_cast_le_tenTower_add_two {ρ b : ℝ} (h : ℕ)
    (hρ : 0 < ρ) (hb : 0 < b)
    (hρinv : ρ⁻¹ ≤ tenTower h) (hbinv : b⁻¹ ≤ tenTower h) :
    ((T_expNeg ρ b : ℕ) : ℝ) ≤ tenTower (h + 2) := by
  by_cases hlog0 : 0 ≤ Real.log b⁻¹
  · have hlog : Real.log b⁻¹ ≤ tenTower h :=
      log_le_tenTower h (inv_nonneg.2 hb.le) hbinv
    have hquot : Real.log b⁻¹ / ρ ≤ tenTower (h + 1) := by
      rw [div_eq_mul_inv]
      exact tenTower_mul_le_succ h hlog0 (inv_nonneg.2 hρ.le) hlog hρinv
    unfold T_expNeg
    exact natCeil_le_tenTower_succ (h + 1) (div_nonneg hlog0 hρ.le) hquot
  · have hquot : Real.log b⁻¹ / ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (le_of_not_ge hlog0) hρ.le
    unfold T_expNeg
    rw [Nat.ceil_eq_zero.mpr hquot]
    norm_num
    exact (tenTower_pos (h + 2)).le

private theorem T_logSq_cast_le_tenTower_add_three {b : ℝ} (h : ℕ)
    (hb : b ≤ tenTower h) : ((T_logSq b : ℕ) : ℝ) ≤ tenTower (h + 3) := by
  have hm0 : 0 ≤ max b 0 := le_max_right _ _
  have hm : max b 0 ≤ tenTower h := max_le hb (tenTower_pos h).le
  have hs : Real.sqrt (max b 0) ≤ tenTower (h + 1) := by
    calc
      Real.sqrt (max b 0) ≤ max b 0 + 1 := sqrt_le_add_one hm0
      _ ≤ tenTower (h + 1) := tenTower_add_le_succ h hm0 (by norm_num) hm
        (tenTower_one_le h)
  have he : Real.exp (Real.sqrt (max b 0)) ≤ tenTower (h + 2) :=
    exp_le_tenTower_succ (h + 1) hs
  unfold T_logSq
  exact natCeil_le_tenTower_succ (h + 2) (Real.exp_pos _).le he

private theorem delta_case2_pos : 0 < delta_case2 := by
  unfold delta_case2 p_whiteExit
  have hx : 0 < (epsBW : ℝ) ^ (3 : ℕ) := by norm_num [epsBW]
  have he : Real.exp (-(epsBW : ℝ) ^ (3 : ℕ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  positivity

private theorem delta_case2_le_one : delta_case2 ≤ 1 := by
  unfold delta_case2 p_whiteExit
  have he := (Real.exp_pos (-(epsBW : ℝ) ^ (3 : ℕ))).le
  nlinarith

private theorem delta_case2_inv_le_tenTower_three : delta_case2⁻¹ ≤ tenTower 3 := by
  let x : ℝ := (epsBW : ℝ) ^ (3 : ℕ)
  have hx0 : 0 < x := by dsimp [x]; norm_num [epsBW]
  have heps0 : 0 ≤ (epsBW : ℝ) := by norm_num [epsBW]
  have heps1 : (epsBW : ℝ) ≤ 1 := by
    have hepsEq : (epsBW : ℝ) = ((10 : ℝ) ^ (1000 : ℕ))⁻¹ := by
      norm_num [epsBW]
    rw [hepsEq]
    exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hx1 : x ≤ 1 := by dsimp [x]; exact pow_le_one₀ heps0 heps1
  have hexp : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hinvExp : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le (by linarith : 0 < 1 + x) hexp
  have hfrac : x / 2 ≤ x / (1 + x) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < 1 + x)]
    nlinarith
  have hident : x / (1 + x) = 1 - 1 / (1 + x) := by
    have hne : 1 + x ≠ 0 := ne_of_gt (by linarith : 0 < 1 + x)
    field_simp [hne]
    ring
  have hone : x / 2 ≤ 1 - Real.exp (-x) := by
    rw [hident] at hfrac
    linarith
  have hδ : 3 * x / 16 ≤ delta_case2 := by
    dsimp [x] at hone ⊢
    unfold delta_case2 p_whiteExit
    nlinarith
  have hsmall0 : 0 < 3 * x / 16 := by positivity
  have hinv : delta_case2⁻¹ ≤ (3 * x / 16)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hsmall0 hδ
  have heq : (3 * x / 16)⁻¹ = (16 / 3) * x⁻¹ := by
    field_simp [ne_of_gt hx0]
  have hraw : (3 * x / 16)⁻¹ ≤ 6 * x⁻¹ := by
    rw [heq]
    have hi0 : 0 ≤ x⁻¹ := inv_nonneg.2 hx0.le
    nlinarith
  apply hinv.trans (hraw.trans ?_)
  dsimp [x]
  exact tenTower_mul_le_succ 2 (by norm_num)
    (inv_nonneg.2 (pow_nonneg (by norm_num [epsBW]) 3))
    ((show (6 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
    epsBW_cube_inv_le_tenTower_two

private theorem geomDenInv_le_tenTower_succ {r : ℝ} (h : ℕ)
    (hr : 0 < r) (hrinv : r⁻¹ ≤ tenTower h) :
    (1 - Real.exp (-r))⁻¹ ≤ tenTower (h + 1) := by
  have hraw : (1 - Real.exp (-r))⁻¹ ≤ 1 + r⁻¹ := by
    simpa [one_div] using one_div_one_sub_exp_neg_le hr
  exact hraw.trans (tenTower_add_le_succ h (by norm_num) (inv_nonneg.2 hr.le)
    (tenTower_one_le h) hrinv)

private theorem log_one_add_half_inv_le_four_mul_inv {d : ℝ}
    (hd : 0 < d) (hd2 : d ≤ 2) :
    (Real.log (1 + d / 2))⁻¹ ≤ 4 * d⁻¹ := by
  let u : ℝ := d / 2
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu2 : u ≤ 2 := by dsimp [u]; linarith
  have hfrac := Real.le_log_one_add_of_nonneg hu0.le
  have hden : 0 < u + 2 := by linarith
  have hhalf : u / 2 ≤ 2 * u / (u + 2) := by
    rw [le_div_iff₀ hden]
    nlinarith
  have hlower : d / 4 ≤ Real.log (1 + d / 2) := by
    calc
      d / 4 = u / 2 := by dsimp [u]; ring
      _ ≤ Real.log (1 + u) := hhalf.trans hfrac
      _ = Real.log (1 + d / 2) := by rfl
  have hsmall0 : 0 < d / 4 := by positivity
  have hinv : (Real.log (1 + d / 2))⁻¹ ≤ (d / 4)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hsmall0 hlower
  calc
    (Real.log (1 + d / 2))⁻¹ ≤ (d / 4)⁻¹ := hinv
    _ = 4 * d⁻¹ := by field_simp [ne_of_gt hd]

private theorem T_fstMgf_main_case2_cast_le_tenTower_seventeen :
    ((T_fstMgf (mainDecayExponent 3.7) (min (delta_case2 / 8) 2) : ℕ) : ℝ)
      ≤ tenTower 17 := by
  let A : ℝ := mainDecayExponent 3.7
  let d : ℝ := min (delta_case2 / 8) 2
  let c : ℝ := c_fpLocation
  let C : ℝ := C_fpCol
  let ell : ℝ := Real.log (1 + d / 2)
  let g : ℝ := min c (c ^ (2 : ℕ) / 20)
  let q : ℝ := c ^ (2 : ℕ) / 40
  let r : ℝ := min q (c / 2)
  have hA0 : 0 < A := by dsimp [A]; exact mainDecayExponent_pos 3.7 (by norm_num)
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hdEq : d = delta_case2 / 8 := by
    dsimp [d]
    rw [min_eq_left]
    linarith [delta_case2_le_one]
  have hd0 : 0 < d := by rw [hdEq]; positivity [delta_case2_pos]
  have hd2 : d ≤ 2 := by dsimp [d]; exact min_le_right _ _
  have hdInvEq : d⁻¹ = 8 * delta_case2⁻¹ := by
    rw [hdEq]
    field_simp [ne_of_gt delta_case2_pos]
  have hdInv : d⁻¹ ≤ tenTower 4 := by
    rw [hdInvEq]
    exact tenTower_mul_le_succ 3 (by norm_num) (inv_nonneg.2 delta_case2_pos.le)
      ((show (8 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 3))
      delta_case2_inv_le_tenTower_three
  have hell0 : 0 < ell := by
    dsimp [ell]
    exact Real.log_pos (by linarith)
  have hellInvRaw : ell⁻¹ ≤ 4 * d⁻¹ := by
    dsimp [ell]
    exact log_one_add_half_inv_le_four_mul_inv hd0 hd2
  have hellInv : ell⁻¹ ≤ tenTower 5 :=
    hellInvRaw.trans (tenTower_mul_le_succ 4 (by norm_num) (inv_nonneg.2 hd0.le)
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 4)) hdInv)
  have hgEq : g = (1 : ℝ) / 3276800000 := by
    dsimp [g, c]
    norm_num [c_fpLocation_eq, min_def]
  have hg0 : 0 < g := by rw [hgEq]; norm_num
  have hgHalfInv : (g / 2)⁻¹ ≤ tenTower 2 := by
    rw [hgEq]
    norm_num only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv]
    exact (show (6553600000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hq1 : 2 * A / (g / 2) ≤ tenTower 4 := by
    rw [div_eq_mul_inv]
    have h2A : 2 * A ≤ tenTower 3 :=
      tenTower_mul_le_succ 2 (by norm_num) hA0.le
        ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hA
    exact tenTower_mul_le_succ 3 (mul_nonneg (by norm_num) hA0.le)
      (inv_nonneg.2 (div_nonneg hg0.le (by norm_num))) h2A
      (hgHalfInv.trans (tenTower_mono (by omega)))
  have hceil1 : ((⌈2 * A / (g / 2)⌉₊ : ℕ) : ℝ) ≤ tenTower 5 :=
    natCeil_le_tenTower_succ 4
      (div_nonneg (mul_nonneg (by norm_num) hA0.le) (div_nonneg hg0.le (by norm_num))) hq1
  have h50A : 50 * A ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) hA0.le
      ((show (50 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        ten_pow_thirty_le_tenTower_two) hA
  have hq2 : 50 * A / ell ≤ tenTower 6 := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ 5 (mul_nonneg (by norm_num) hA0.le)
      (inv_nonneg.2 hell0.le) (h50A.trans (tenTower_mono (by omega))) hellInv
  have hceil2 : ((⌈50 * A / ell⌉₊ : ℕ) : ℝ) ≤ tenTower 7 :=
    natCeil_le_tenTower_succ 6
      (div_nonneg (mul_nonneg (by norm_num) hA0.le) hell0.le) hq2
  have hlog2zero : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2 : Real.log 2 ≤ tenTower 2 :=
    (Real.log_le_self (by norm_num)).trans
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
  have hlog9one : 1 ≤ Real.log 9 :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 9)).2
      (Real.exp_one_lt_three.le.trans (by norm_num))
  have hlog9Inv : (Real.log 9)⁻¹ ≤ tenTower 2 :=
    ((inv_le_one₀ (Real.log_pos (by norm_num))).2 hlog9one).trans (tenTower_one_le 2)
  have hellLog9Inv : (ell * Real.log 9)⁻¹ ≤ tenTower 6 := by
    rw [mul_inv_rev]
    exact tenTower_mul_le_succ 5 (inv_nonneg.2 (Real.log_pos (by norm_num)).le)
      (inv_nonneg.2 hell0.le) (hlog9Inv.trans (tenTower_mono (by omega))) hellInv
  have hnum1a : 2 * A ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) hA0.le
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hA
  have hnum1 : 2 * A * Real.log 2 ≤ tenTower 4 :=
    tenTower_mul_le_succ 3 (mul_nonneg (by norm_num) hA0.le) hlog2zero hnum1a
      (hlog2.trans (tenTower_mono (by omega)))
  have hr1 : 2 * A * Real.log 2 / (ell * Real.log 9) ≤ tenTower 7 := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ 6 (mul_nonneg (mul_nonneg (by norm_num) hA0.le) hlog2zero)
      (inv_nonneg.2 (mul_nonneg hell0.le (Real.log_pos (by norm_num)).le))
      (hnum1.trans (tenTower_mono (by omega))) hellLog9Inv
  have hr2 : A / ell ≤ tenTower 6 := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ 5 hA0.le (inv_nonneg.2 hell0.le)
      (hA.trans (tenTower_mono (by omega))) hellInv
  let B : ℝ := max (max (2 * A * Real.log 2 / (ell * Real.log 9)) (A / ell)) 1
  have hB : B ≤ tenTower 7 := by
    dsimp [B]
    exact max_le (max_le hr1 (hr2.trans
      (tenTower_mono (show (6 : ℕ) ≤ 7 by norm_num))))
      (tenTower_one_le 7)
  have hlogSq : ((T_logSq B : ℕ) : ℝ) ≤ tenTower 10 :=
    T_logSq_cast_le_tenTower_add_three 7 hB
  have hrEq : r = (1 : ℝ) / 6553600000 := by
    dsimp [r, q, c]
    norm_num [c_fpLocation_eq, min_def]
  have hr0 : 0 < r := by rw [hrEq]; norm_num
  have hrInv : r⁻¹ ≤ tenTower 2 := by
    rw [hrEq]
    norm_num only [one_div, inv_inv]
    exact (show (6553600000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  let rho : ℝ := r * ell / (4 * A)
  have hrho0 : 0 < rho := by dsimp [rho]; positivity
  have hrhoInvEq : rho⁻¹ = 4 * A * r⁻¹ * ell⁻¹ := by
    dsimp [rho]
    field_simp [ne_of_gt hr0, ne_of_gt hell0, ne_of_gt hA0]
  have h4A : 4 * A ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) hA0.le
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hA
  have h4Ar : 4 * A * r⁻¹ ≤ tenTower 4 :=
    tenTower_mul_le_succ 3 (mul_nonneg (by norm_num) hA0.le) (inv_nonneg.2 hr0.le)
      h4A (hrInv.trans (tenTower_mono (by omega)))
  have hrhoInv : rho⁻¹ ≤ tenTower 6 := by
    rw [hrhoInvEq]
    exact tenTower_mul_le_succ 5 (by positivity) (inv_nonneg.2 hell0.le)
      (h4Ar.trans (tenTower_mono (by omega))) hellInv
  have hcHalf0 : 0 < c / 2 := by dsimp [c]; positivity [c_fpLocation_pos]
  have hcHalfInv : (c / 2)⁻¹ ≤ tenTower 2 := by
    have heq : (c / 2)⁻¹ = (25600 : ℝ) := by
      dsimp [c]
      norm_num [c_fpLocation_eq]
    rw [heq]
    exact (show (25600 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hqEq : q = (1 : ℝ) / 6553600000 := by
    dsimp [q, c]
    norm_num [c_fpLocation_eq]
  have hq0 : 0 < q := by rw [hqEq]; norm_num
  have hqInv : q⁻¹ ≤ tenTower 2 := by
    rw [hqEq]
    norm_num only [one_div, inv_inv]
    exact (show (6553600000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hgeomR : (1 - Real.exp (-q))⁻¹ ≤ tenTower 3 :=
    geomDenInv_le_tenTower_succ 2 hq0 hqInv
  have hgeomC : (1 - Real.exp (-(c / 2)))⁻¹ ≤ tenTower 3 :=
    geomDenInv_le_tenTower_succ 2 hcHalf0 hcHalfInv
  have hgeomR0 : 0 ≤ (1 - Real.exp (-q))⁻¹ := by
    have : 0 < 1 - Real.exp (-q) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      linarith
    positivity
  have hgeomC0 : 0 ≤ (1 - Real.exp (-(c / 2)))⁻¹ := by
    have : 0 < 1 - Real.exp (-(c / 2)) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      linarith
    positivity
  have hgeomSum : (1 - Real.exp (-q))⁻¹ + (1 - Real.exp (-(c / 2)))⁻¹
      ≤ tenTower 4 := tenTower_add_le_succ 3 hgeomR0 hgeomC0 hgeomR hgeomC
  have hAhalf : A / 2 ≤ tenTower 2 := by linarith [tenTower_pos 2]
  have hexpA : Real.exp (A / 2) ≤ tenTower 3 := exp_le_tenTower_succ 2 hAhalf
  have hCexp : C * Real.exp (A / 2) ≤ tenTower 10 :=
    tenTower_mul_le_succ 9 (by dsimp [C]; exact C_fpCol_pos.le) (Real.exp_pos _).le
      (by dsimp [C]; exact C_fpCol_le_tenTower_nine)
      (hexpA.trans (tenTower_mono (by omega)))
  have hprod : C * Real.exp (A / 2) *
      ((1 - Real.exp (-q))⁻¹ + (1 - Real.exp (-(c / 2)))⁻¹) ≤ tenTower 11 :=
    tenTower_mul_le_succ 10
      (mul_nonneg (by dsimp [C]; exact C_fpCol_pos.le) (Real.exp_pos _).le)
      (add_nonneg hgeomR0 hgeomC0) hCexp
      (hgeomSum.trans (tenTower_mono (by omega)))
  let den : ℝ := 2 * (C * Real.exp (A / 2) *
    ((1 - Real.exp (-q))⁻¹ + (1 - Real.exp (-(c / 2)))⁻¹))
  have hden0 : 0 < den := by
    dsimp [den]
    exact mul_pos two_pos (mul_pos
      (mul_pos (by dsimp [C]; exact C_fpCol_pos) (Real.exp_pos _))
      (add_pos_of_pos_of_nonneg (by
        have : 0 < 1 - Real.exp (-q) := by
          rw [sub_pos, Real.exp_lt_one_iff]
          linarith
        positivity) hgeomC0))
  have hden : den ≤ tenTower 12 := by
    dsimp [den]
    exact tenTower_mul_le_succ 11 (by norm_num)
      (mul_nonneg (mul_nonneg (by dsimp [C]; exact C_fpCol_pos.le) (Real.exp_pos _).le)
        (add_nonneg hgeomR0 hgeomC0))
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 11)) hprod
  let b : ℝ := d / den
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hbInvEq : b⁻¹ = den * d⁻¹ := by
    dsimp [b]
    field_simp [ne_of_gt hd0, ne_of_gt hden0]
  have hbInv : b⁻¹ ≤ tenTower 13 := by
    rw [hbInvEq]
    exact tenTower_mul_le_succ 12 hden0.le (inv_nonneg.2 hd0.le) hden
      (hdInv.trans (tenTower_mono (by omega)))
  have hExp : ((T_expNeg rho b : ℕ) : ℝ) ≤ tenTower 15 :=
    T_expNeg_cast_le_tenTower_add_two 13 hrho0 hb0
      (hrhoInv.trans (tenTower_mono (by omega))) hbInv
  have hs1 : (25 : ℝ) + (⌈2 * A / (g / 2)⌉₊ : ℕ) ≤ tenTower 6 :=
    tenTower_add_le_succ 5 (by norm_num) (by positivity)
      ((show (25 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega)))) hceil1
  have hs2 : (25 : ℝ) + (⌈2 * A / (g / 2)⌉₊ : ℕ)
      + (⌈50 * A / ell⌉₊ : ℕ) ≤ tenTower 8 :=
    tenTower_add_le_succ 7 (by positivity) (by positivity)
      (hs1.trans (tenTower_mono (by omega))) hceil2
  have hs3 : (25 : ℝ) + (⌈2 * A / (g / 2)⌉₊ : ℕ)
      + (⌈50 * A / ell⌉₊ : ℕ) + T_logSq B ≤ tenTower 11 :=
    tenTower_add_le_succ 10 (by positivity) (by positivity)
      (hs2.trans (tenTower_mono (by omega))) hlogSq
  have hfinal : ((25 + ⌈2 * A / (g / 2)⌉₊ + ⌈50 * A / ell⌉₊ + T_logSq B
      + T_expNeg rho b : ℕ) : ℝ) ≤ tenTower 17 := by
    push_cast
    exact tenTower_add_le_succ 16 (by positivity) (by positivity)
      (hs3.trans (tenTower_mono (by omega)))
      (hExp.trans (tenTower_mono (by omega)))
  unfold T_fstMgf T_mgfNumeric
  simpa [A, d, c, C, ell, g, q, r, rho, B, den, b, one_div] using hfinal

private theorem T_fstTail_main_case2_cast_le_tenTower_seventeen :
    ((T_fstTail (mainDecayExponent 3.7) (delta_case2 / 4) : ℕ) : ℝ)
      ≤ tenTower 17 := by
  let A : ℝ := mainDecayExponent 3.7
  let c : ℝ := c_fpLocation
  let C : ℝ := C_fpCol
  let g : ℝ := min c (c ^ (2 : ℕ) / 20)
  let d : ℝ := delta_case2 / 4
  let ε : ℝ := g / 2 / (16 * A)
  let ρ : ℝ := g / 2 / 16
  let s₁ : ℝ := c ^ (2 : ℕ) / 20 - g / 2
  let s₂ : ℝ := c - g / 2
  have hA0 : 0 < A := by dsimp [A]; exact mainDecayExponent_pos 3.7 (by norm_num)
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hc0 : 0 < c := by dsimp [c]; exact c_fpLocation_pos
  have hgEq : g = (1 : ℝ) / 3276800000 := by
    dsimp [g, c]
    norm_num [c_fpLocation_eq, min_def]
  have hg0 : 0 < g := by rw [hgEq]; norm_num
  have hgInv : g⁻¹ ≤ tenTower 2 := by
    rw [hgEq]
    norm_num only [one_div, inv_inv]
    exact (show (3276800000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hεInvEq : ε⁻¹ = 32 * A * g⁻¹ := by
    dsimp [ε]
    field_simp [ne_of_gt hg0, ne_of_gt hA0]
    ring
  have h32A : 32 * A ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) hA0.le
      ((show (32 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        ten_pow_thirty_le_tenTower_two) hA
  have hεInv : ε⁻¹ ≤ tenTower 4 := by
    rw [hεInvEq]
    exact tenTower_mul_le_succ 3 (mul_nonneg (by norm_num) hA0.le)
      (inv_nonneg.2 hg0.le) h32A (hgInv.trans (tenTower_mono (by omega)))
  have hLogLin : ((T_logLin ε : ℕ) : ℝ) ≤ tenTower 8 :=
    T_logLin_cast_le_tenTower_add_four 4 hε0 hεInv
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρInvEq : ρ⁻¹ = 32 * g⁻¹ := by
    dsimp [ρ]
    field_simp [ne_of_gt hg0]
    norm_num
  have hρInv : ρ⁻¹ ≤ tenTower 3 := by
    rw [hρInvEq]
    exact tenTower_mul_le_succ 2 (by norm_num) (inv_nonneg.2 hg0.le)
      ((show (32 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        ten_pow_thirty_le_tenTower_two) hgInv
  have hs₁Eq : s₁ = (1 : ℝ) / 6553600000 := by
    dsimp [s₁, g, c]
    norm_num [c_fpLocation_eq, min_def]
  have hs₂Eq : s₂ = (511999 : ℝ) / 6553600000 := by
    dsimp [s₂, g, c]
    norm_num [c_fpLocation_eq, min_def]
  have hs₁0 : 0 < s₁ := by rw [hs₁Eq]; norm_num
  have hs₂0 : 0 < s₂ := by rw [hs₂Eq]; norm_num
  have hs₁Inv : s₁⁻¹ ≤ tenTower 2 := by
    rw [hs₁Eq]
    norm_num only [one_div, inv_inv]
    exact (show (6553600000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hs₂Inv : s₂⁻¹ ≤ tenTower 2 := by
    calc
      s₂⁻¹ ≤ (10 : ℝ) ^ (30 : ℕ) := by rw [hs₂Eq]; norm_num
      _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two
  have hgeom1 : (1 - Real.exp (-s₁))⁻¹ ≤ tenTower 3 :=
    geomDenInv_le_tenTower_succ 2 hs₁0 hs₁Inv
  have hgeom2 : (1 - Real.exp (-s₂))⁻¹ ≤ tenTower 3 :=
    geomDenInv_le_tenTower_succ 2 hs₂0 hs₂Inv
  have hgeom10 : 0 ≤ (1 - Real.exp (-s₁))⁻¹ := by
    have : 0 < 1 - Real.exp (-s₁) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      linarith
    positivity
  have hgeom20 : 0 ≤ (1 - Real.exp (-s₂))⁻¹ := by
    have : 0 < 1 - Real.exp (-s₂) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      linarith
    positivity
  have hgeom : (1 - Real.exp (-s₁))⁻¹ + (1 - Real.exp (-s₂))⁻¹ ≤ tenTower 4 :=
    tenTower_add_le_succ 3 hgeom10 hgeom20 hgeom1 hgeom2
  have hCgeom : C * ((1 - Real.exp (-s₁))⁻¹ + (1 - Real.exp (-s₂))⁻¹)
      ≤ tenTower 10 :=
    tenTower_mul_le_succ 9 (by dsimp [C]; exact C_fpCol_pos.le)
      (add_nonneg hgeom10 hgeom20) (by dsimp [C]; exact C_fpCol_le_tenTower_nine)
      (hgeom.trans (tenTower_mono (by omega)))
  let den : ℝ := 1 + C * ((1 - Real.exp (-s₁))⁻¹ + (1 - Real.exp (-s₂))⁻¹)
  have hden0 : 0 < den := by
    have hp : 0 ≤ C * ((1 - Real.exp (-s₁))⁻¹ + (1 - Real.exp (-s₂))⁻¹) :=
      mul_nonneg (by dsimp [C]; exact C_fpCol_pos.le) (add_nonneg hgeom10 hgeom20)
    dsimp [den]
    linarith
  have hden : den ≤ tenTower 11 := by
    dsimp [den]
    exact tenTower_add_le_succ 10 (by norm_num)
      (mul_nonneg (by dsimp [C]; exact C_fpCol_pos.le) (add_nonneg hgeom10 hgeom20))
      (tenTower_one_le 10) hCgeom
  have hd0 : 0 < d := by dsimp [d]; positivity [delta_case2_pos]
  have hdInvEq : d⁻¹ = 4 * delta_case2⁻¹ := by
    dsimp [d]
    field_simp [ne_of_gt delta_case2_pos]
  have hdInv : d⁻¹ ≤ tenTower 4 := by
    rw [hdInvEq]
    exact tenTower_mul_le_succ 3 (by norm_num) (inv_nonneg.2 delta_case2_pos.le)
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 3))
      delta_case2_inv_le_tenTower_three
  let b : ℝ := d / den
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hbInvEq : b⁻¹ = den * d⁻¹ := by
    dsimp [b]
    field_simp [ne_of_gt hd0, ne_of_gt hden0]
  have hbInv : b⁻¹ ≤ tenTower 12 := by
    rw [hbInvEq]
    exact tenTower_mul_le_succ 11 hden0.le (inv_nonneg.2 hd0.le) hden
      (hdInv.trans (tenTower_mono (by omega)))
  have hExp : ((T_expNeg ρ b : ℕ) : ℝ) ≤ tenTower 14 :=
    T_expNeg_cast_le_tenTower_add_two 12 hρ0 hb0
      (hρInv.trans (tenTower_mono (by omega))) hbInv
  have hLogSq : ((T_logSq 16 : ℕ) : ℝ) ≤ tenTower 5 :=
    T_logSq_cast_le_tenTower_add_three 2
      ((show (16 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        ten_pow_thirty_le_tenTower_two)
  have hsA : (400 : ℝ) + T_logLin ε ≤ tenTower 9 :=
    tenTower_add_le_succ 8 (by norm_num) (by positivity)
      ((show (400 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega)))) hLogLin
  have hsB : (400 : ℝ) + T_logLin ε + T_expNeg ρ b ≤ tenTower 15 :=
    tenTower_add_le_succ 14 (by positivity) (by positivity)
      (hsA.trans (tenTower_mono (by omega))) hExp
  have hfinal : ((400 + T_logLin ε + T_expNeg ρ b + T_logSq 16 : ℕ) : ℝ)
      ≤ tenTower 17 := by
    push_cast
    exact tenTower_add_le_succ 16 (by positivity) (by positivity)
      (hsB.trans (tenTower_mono (by omega)))
      (hLogSq.trans (tenTower_mono (by omega)))
  unfold T_fstTail
  simpa [A, c, C, g, d, ε, ρ, s₁, s₂, den, b, one_div] using hfinal

private theorem T_holdTail_main_case2_cast_le_tenTower_eleven :
    ((T_holdTail (mainDecayExponent 3.7) (delta_case2 / 4) : ℕ) : ℝ)
      ≤ tenTower 11 := by
  let A : ℝ := mainDecayExponent 3.7
  let d : ℝ := delta_case2 / 4
  let ρ : ℝ := Real.log (4 / 3) / 8
  let ε : ℝ := ρ / (2 * A)
  have hA0 : 0 < A := by dsimp [A]; exact mainDecayExponent_pos 3.7 (by norm_num)
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity [Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)]
  have hρInvEq : ρ⁻¹ = 8 * (Real.log (4 / 3))⁻¹ := by
    dsimp [ρ]
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3))]
  have hρInv : ρ⁻¹ ≤ tenTower 2 := by
    rw [hρInvEq]
    have h32 : (8 : ℝ) * (Real.log (4 / 3))⁻¹ ≤ 32 := by
      nlinarith [log_four_thirds_inv_le_four]
    exact h32.trans ((show (32 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two)
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hεInvEq : ε⁻¹ = 2 * A * ρ⁻¹ := by
    dsimp [ε]
    field_simp [ne_of_gt hρ0, ne_of_gt hA0]
  have h2A : 2 * A ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) hA0.le
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hA
  have hεInv : ε⁻¹ ≤ tenTower 4 := by
    rw [hεInvEq]
    exact tenTower_mul_le_succ 3 (mul_nonneg (by norm_num) hA0.le)
      (inv_nonneg.2 hρ0.le) h2A (hρInv.trans (tenTower_mono (by omega)))
  have hLog : ((T_logLin ε : ℕ) : ℝ) ≤ tenTower 8 :=
    T_logLin_cast_le_tenTower_add_four 4 hε0 hεInv
  have hd0 : 0 < d := by dsimp [d]; positivity [delta_case2_pos]
  have hdInvEq : d⁻¹ = 4 * delta_case2⁻¹ := by
    dsimp [d]
    field_simp [ne_of_gt delta_case2_pos]
  have hdInv : d⁻¹ ≤ tenTower 4 := by
    rw [hdInvEq]
    exact tenTower_mul_le_succ 3 (by norm_num) (inv_nonneg.2 delta_case2_pos.le)
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 3))
      delta_case2_inv_le_tenTower_three
  have hExp : ((T_expNeg (ρ / 2) d : ℕ) : ℝ) ≤ tenTower 6 := by
    have hr2 : 0 < ρ / 2 := div_pos hρ0 two_pos
    have hr2InvEq : (ρ / 2)⁻¹ = 2 * ρ⁻¹ := by field_simp [ne_of_gt hρ0]
    have hr2Inv : (ρ / 2)⁻¹ ≤ tenTower 3 := by
      rw [hr2InvEq]
      exact tenTower_mul_le_succ 2 (by norm_num) (inv_nonneg.2 hρ0.le)
        ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hρInv
    exact T_expNeg_cast_le_tenTower_add_two 4 hr2 hd0
      (hr2Inv.trans (tenTower_mono (by omega))) hdInv
  have hs1 : (400 : ℝ) + T_logLin ε ≤ tenTower 9 :=
    tenTower_add_le_succ 8 (by norm_num) (by positivity)
      ((show (400 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega)))) hLog
  have hfinal : ((400 + T_logLin ε + T_expNeg (ρ / 2) d : ℕ) : ℝ)
      ≤ tenTower 11 := by
    push_cast
    exact tenTower_add_le_succ 10 (by positivity) (by positivity)
      (hs1.trans (tenTower_mono (by omega)))
      (hExp.trans (tenTower_mono (by omega)))
  unfold T_holdTail
  simpa [A, d, ρ, ε] using hfinal

private theorem T_edgeWeight_main_case2_cast_le_tenTower_twenty_five :
    ((T_edgeWeight (mainDecayExponent 3.7) delta_case2 : ℕ) : ℝ)
      ≤ tenTower 25 := by
  let A : ℝ := mainDecayExponent 3.7
  let d : ℝ := min (delta_case2 / 8) 2
  let g : ℝ := min c_fpLocation (c_fpLocation ^ (2 : ℕ) / 20)
  have hA0 : 0 < A := by dsimp [A]; exact mainDecayExponent_pos 3.7 (by norm_num)
  have hA : A ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have hdEq : d = delta_case2 / 8 := by
    dsimp [d]
    rw [min_eq_left]
    linarith [delta_case2_le_one]
  have hd0 : 0 < d := by rw [hdEq]; positivity [delta_case2_pos]
  have hdInvEq : d⁻¹ = 8 * delta_case2⁻¹ := by
    rw [hdEq]
    field_simp [ne_of_gt delta_case2_pos]
  have hdInv : d⁻¹ ≤ tenTower 4 := by
    rw [hdInvEq]
    exact tenTower_mul_le_succ 3 (by norm_num) (inv_nonneg.2 delta_case2_pos.le)
      ((show (8 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 3))
      delta_case2_inv_le_tenTower_three
  have hgEq : g = (1 : ℝ) / 3276800000 := by
    dsimp [g]
    norm_num [c_fpLocation_eq, min_def]
  have hg0 : 0 < g := by rw [hgEq]; norm_num
  have hgInv : g⁻¹ ≤ tenTower 2 := by
    rw [hgEq]
    norm_num only [one_div, inv_inv]
    exact (show (3276800000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have h200A : 200 * A ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) hA0.le
      ((show (200 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        ten_pow_thirty_le_tenTower_two) hA
  have hceil200 : ((⌈200 * A⌉₊ : ℕ) : ℝ) ≤ tenTower 4 :=
    natCeil_le_tenTower_succ 3 (mul_nonneg (by norm_num) hA0.le) h200A
  have h10A : 10 * A ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) hA0.le (ten_le_tenTower 2) hA
  have h10Ad : 10 * A / d ≤ tenTower 5 := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ 4 (mul_nonneg (by norm_num) hA0.le)
      (inv_nonneg.2 hd0.le) (h10A.trans (tenTower_mono (by omega))) hdInv
  have hceilD : ((⌈10 * A / d⌉₊ : ℕ) : ℝ) ≤ tenTower 6 :=
    natCeil_le_tenTower_succ 5
      (div_nonneg (mul_nonneg (by norm_num) hA0.le) hd0.le) h10Ad
  have h4A : 4 * A ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) hA0.le
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hA
  have h4Ag : 4 * A / g ≤ tenTower 4 := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ 3 (mul_nonneg (by norm_num) hA0.le)
      (inv_nonneg.2 hg0.le) h4A (hgInv.trans (tenTower_mono (by omega)))
  have hceilG : ((⌈4 * A / g⌉₊ : ℕ) : ℝ) ≤ tenTower 5 :=
    natCeil_le_tenTower_succ 4
      (div_nonneg (mul_nonneg (by norm_num) hA0.le) hg0.le) h4Ag
  have h1 := T_fstMgf_main_case2_cast_le_tenTower_seventeen
  have h2 := T_fstTail_main_case2_cast_le_tenTower_seventeen
  have h3 := T_holdTail_main_case2_cast_le_tenTower_eleven
  have hs1 : (T_fstMgf A d : ℝ) + T_fstTail A (delta_case2 / 4) ≤ tenTower 18 :=
    tenTower_add_le_succ 17 (by positivity) (by positivity) h1 h2
  have hs2 : (T_fstMgf A d : ℝ) + T_fstTail A (delta_case2 / 4)
      + T_holdTail A (delta_case2 / 4) ≤ tenTower 19 :=
    tenTower_add_le_succ 18 (by positivity) (by positivity) hs1
      (h3.trans (tenTower_mono (by omega)))
  have hs3 : (T_fstMgf A d : ℝ) + T_fstTail A (delta_case2 / 4)
      + T_holdTail A (delta_case2 / 4) + (⌈200 * A⌉₊ : ℕ) ≤ tenTower 20 :=
    tenTower_add_le_succ 19 (by positivity) (by positivity) hs2
      (hceil200.trans (tenTower_mono (by omega)))
  have hs4 : (T_fstMgf A d : ℝ) + T_fstTail A (delta_case2 / 4)
      + T_holdTail A (delta_case2 / 4) + (⌈200 * A⌉₊ : ℕ) + (⌈10 * A / d⌉₊ : ℕ)
      ≤ tenTower 21 :=
    tenTower_add_le_succ 20 (by positivity) (by positivity) hs3
      (hceilD.trans (tenTower_mono (by omega)))
  have hs5 : (T_fstMgf A d : ℝ) + T_fstTail A (delta_case2 / 4)
      + T_holdTail A (delta_case2 / 4) + (⌈200 * A⌉₊ : ℕ) + (⌈10 * A / d⌉₊ : ℕ)
      + (⌈4 * A / g⌉₊ : ℕ) ≤ tenTower 22 :=
    tenTower_add_le_succ 21 (by positivity) (by positivity) hs4
      (hceilG.trans (tenTower_mono (by omega)))
  have hfinal : ((T_fstMgf A d + T_fstTail A (delta_case2 / 4)
      + T_holdTail A (delta_case2 / 4) + ⌈200 * A⌉₊ + ⌈10 * A / d⌉₊
      + ⌈4 * A / g⌉₊ + 2 : ℕ) : ℝ) ≤ tenTower 25 := by
    push_cast
    exact tenTower_add_le_succ 24 (by positivity) (by norm_num)
      (hs5.trans (tenTower_mono (by omega)))
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 24))
  unfold T_edgeWeight
  simpa [A, d, g] using hfinal

private theorem Cthr_case2_main_cast_le_tenTower_twenty_five :
    ((Cthr_case2 (mainDecayExponent 3.7) : ℕ) : ℝ) ≤ tenTower 25 := by
  have hwhite : ((T_whiteExitDeep : ℕ) : ℝ) ≤ tenTower 17 := by
    simpa [T_whiteExitDeep] using T_outStrip_cast_le_tenTower_seventeen
  unfold Cthr_case2
  push_cast
  exact max_le (max_le
    (hwhite.trans
      (tenTower_mono (show (17 : ℕ) ≤ 25 by norm_num)))
    T_edgeWeight_main_case2_cast_le_tenTower_twenty_five)
    ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 25))

private theorem Cthr_dampingCol_main_cast_le_tenTower_thirty_eight :
    ((Cthr_dampingCol (mainDecayExponent 3.7) : ℕ) : ℝ) ≤ tenTower 38 := by
  unfold Cthr_dampingCol
  push_cast
  exact max_le (max_le Cthr_fewWhite_main_cast_le_tenTower_thirty_eight
    (T_colTail_main_cast_le_tenTower_thirty_four.trans (tenTower_mono (by omega))))
    (ten_le_tenTower 38)

private theorem Cthr_blackEdge_main_cast_le_tenTower_thirty_eight :
    ((Cthr_blackEdge (mainDecayExponent 3.7) : ℕ) : ℝ) ≤ tenTower 38 := by
  unfold Cthr_blackEdge
  push_cast
  exact max_le
    (Cthr_case2_main_cast_le_tenTower_twenty_five.trans (tenTower_mono (by omega)))
    Cthr_dampingCol_main_cast_le_tenTower_thirty_eight

private theorem Cthr_prop78_main_cast_le_tenTower_thirty_eight :
    ((Cthr_prop78 (mainDecayExponent 3.7) : ℕ) : ℝ) ≤ tenTower 38 := by
  unfold Cthr_prop78
  push_cast
  exact max_le (max_le
    (C_hold_main_cast_le_tenTower_eighteen.trans (tenTower_mono (by omega)))
    Cthr_blackEdge_main_cast_le_tenTower_thirty_eight)
    (tenTower_one_le 38)

private theorem C_polyDecay_main_le_tenTower_forty :
    C_polyDecay (mainDecayExponent 3.7) ≤ tenTower 40 := by
  let A : ℝ := mainDecayExponent 3.7
  have hA0 : 0 < A := by dsimp [A]; exact mainDecayExponent_pos 3.7 (by norm_num)
  have hbase0 : 0 ≤ ((max (Cthr_prop78 A) 1 : ℕ) : ℝ) := by positivity
  have hbase : ((max (Cthr_prop78 A) 1 : ℕ) : ℝ) ≤ tenTower 38 := by
    push_cast
    exact max_le Cthr_prop78_main_cast_le_tenTower_thirty_eight (tenTower_one_le 38)
  unfold C_polyDecay
  exact rpow_le_tenTower_add_two 38 hbase0 hA0.le hbase
    (mainDecayExponent_37_le_tenTower_two.trans (tenTower_mono (by omega)))

private theorem C_renewalWhite_le_tenTower_forty_two_of_bounds (A : ℝ)
    (hA0 : 0 < A) (hA : A ≤ tenTower 2)
    (hHold : ((C_hold A : ℕ) : ℝ) ≤ tenTower 18)
    (hPoly : C_polyDecay A ≤ tenTower 40) :
    C_renewalWhite A ≤ tenTower 42 := by
  have h2C : (2 : ℝ) * C_hold A ≤ tenTower 19 :=
    tenTower_mul_le_succ 18 (by norm_num) (by positivity)
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 18))
      hHold
  have hbase : ((2 * C_hold A + 2 : ℕ) : ℝ) ≤ tenTower 20 := by
    push_cast
    exact tenTower_add_le_succ 19 (by positivity) (by norm_num) h2C
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 19))
  have harm1 : (((2 * C_hold A + 2 : ℕ) : ℝ) ^ A) ≤ tenTower 22 :=
    rpow_le_tenTower_add_two 20 (by positivity) hA0.le hbase
      (hA.trans (tenTower_mono (by omega)))
  have hepsArg : (epsBW : ℝ) ^ (3 : ℕ) / 2 ≤ tenTower 2 := by
    have heps0 : 0 ≤ (epsBW : ℝ) := by norm_num [epsBW]
    have heps1 : (epsBW : ℝ) ≤ 1 := by
      have hepsEq : (epsBW : ℝ) = ((10 : ℝ) ^ (1000 : ℕ))⁻¹ := by
        norm_num [epsBW]
      rw [hepsEq]
      exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
    have hcube : (epsBW : ℝ) ^ (3 : ℕ) ≤ 1 := pow_le_one₀ heps0 heps1
    exact (show (epsBW : ℝ) ^ (3 : ℕ) / 2 ≤ 1 by nlinarith).trans
      (tenTower_one_le 2)
  have hexp : Real.exp ((epsBW : ℝ) ^ (3 : ℕ) / 2) ≤ tenTower 3 :=
    exp_le_tenTower_succ 2 hepsArg
  have h3A : (3 : ℝ) ^ A ≤ tenTower 4 :=
    rpow_le_tenTower_add_two 2 (by norm_num) hA0.le
      ((show (3 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hA
  have hp1 : C_polyDecay A * Real.exp ((epsBW : ℝ) ^ (3 : ℕ) / 2)
      ≤ tenTower 41 :=
    tenTower_mul_le_succ 40 (C_polyDecay_pos A).le (Real.exp_pos _).le
      hPoly
      (hexp.trans (tenTower_mono (by omega)))
  have harm2 : C_polyDecay A * Real.exp ((epsBW : ℝ) ^ (3 : ℕ) / 2)
      * (3 : ℝ) ^ A ≤ tenTower 42 :=
    tenTower_mul_le_succ 41 (mul_nonneg (C_polyDecay_pos A).le (Real.exp_pos _).le)
      (Real.rpow_nonneg (by norm_num) _) hp1 (h3A.trans (tenTower_mono (by omega)))
  unfold C_renewalWhite
  exact max_le (harm1.trans (tenTower_mono (show (22 : ℕ) ≤ 42 by norm_num))) harm2

private theorem C_renewalWhite_main_le_tenTower_forty_two :
    C_renewalWhite (mainDecayExponent 3.7) ≤ tenTower 42 :=
  C_renewalWhite_le_tenTower_forty_two_of_bounds (mainDecayExponent 3.7)
    (mainDecayExponent_pos 3.7 (by norm_num)) mainDecayExponent_37_le_tenTower_two
    C_hold_main_cast_le_tenTower_eighteen C_polyDecay_main_le_tenTower_forty

/-! ## §6 propagation -/

private theorem N_rpowAbsorb_cast_le_tenTower_add_two {κ : ℝ} (h : ℕ)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ tenTower h) :
    ((N_rpowAbsorb κ : ℕ) : ℝ) ≤ tenTower (h + 2) := by
  have hc : ((⌈κ⌉₊ : ℕ) : ℝ) ≤ tenTower (h + 1) :=
    natCeil_le_tenTower_succ h hκ0 hκ
  unfold N_rpowAbsorb
  push_cast
  exact tenTower_add_le_succ (h + 1) (by positivity) (by norm_num) hc
    (tenTower_one_le (h + 1))

private theorem N_logGe_cast_le_tenTower_add_three {L : ℝ} (h : ℕ)
    (hL : L ≤ tenTower h) : ((N_logGe L : ℕ) : ℝ) ≤ tenTower (h + 3) := by
  have he : Real.exp L ≤ tenTower (h + 1) := exp_le_tenTower_succ h hL
  have hc : ((⌈Real.exp L⌉₊ : ℕ) : ℝ) ≤ tenTower (h + 2) :=
    natCeil_le_tenTower_succ (h + 1) (Real.exp_pos _).le he
  unfold N_logGe
  push_cast
  exact tenTower_add_le_succ (h + 2) (by positivity) (by norm_num) hc
    (tenTower_one_le (h + 2))

private theorem log_three_div_log_two_le_159_over_100 :
    Real.log 3 / Real.log 2 ≤ (159 : ℝ) / 100 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h3 : Real.log 3 < (1.0986122888 : ℝ) := Real.log_three_lt_d9
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hlog2]
  nlinarith

private theorem gap_eight_fifths_inv_le_hundred :
    (8 / 5 - Real.log 3 / Real.log 2 : ℝ)⁻¹ ≤ 100 := by
  have hgap : (1 : ℝ) / 100 ≤ 8 / 5 - Real.log 3 / Real.log 2 := by
    linarith [log_three_div_log_two_le_159_over_100]
  have hsmall : (0 : ℝ) < 1 / 100 := by norm_num
  have hinv := one_div_le_one_div_of_le hsmall hgap
  norm_num at hinv ⊢
  exact hinv

private theorem gap_two_inv_le_four :
    (2 - Real.log 3 / Real.log 2 : ℝ)⁻¹ ≤ 4 := by
  have hgap : (1 : ℝ) / 4 ≤ 2 - Real.log 3 / Real.log 2 := by
    linarith [log_three_div_log_two_le_159_over_100]
  have hsmall : (0 : ℝ) < 1 / 4 := by norm_num
  have hinv := one_div_le_one_div_of_le hsmall hgap
  norm_num at hinv ⊢
  exact hinv

private theorem N_caWindow_37_cast_le_tenTower_six :
    ((N_caWindow 3.7 : ℕ) : ℝ) ≤ tenTower 6 := by
  let D : ℝ := caConst 3.7 ^ (2 : ℕ) - 2 * caConst 3.7
  have hDEq : D = 44876600 := by dsimp [D]; norm_num [caConst, max_def]
  have hD0 : 0 < D := by rw [hDEq]; norm_num
  have hD : D ≤ tenTower 2 := by
    rw [hDEq]
    exact (show (44876600 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  unfold N_caWindow
  change ((T_logLin D⁻¹ : ℕ) : ℝ) ≤ tenTower 6
  exact T_logLin_cast_le_tenTower_add_four 2 (inv_pos.2 hD0) (by simpa using hD)

private theorem N_condWindowB_ca37_cast_le_tenTower_eight :
    ((N_condWindowB (caConst 3.7) : ℕ) : ℝ) ≤ tenTower 8 := by
  let δ : ℝ := 8 / 5 - Real.log 3 / Real.log 2
  let C : ℝ := caConst 3.7
  let r : ℝ := δ / (4 * C)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    linarith [log_three_div_log_two_le_159_over_100]
  have hCeq : C = 6700 := by dsimp [C]; norm_num [caConst, max_def]
  have hC0 : 0 < C := by rw [hCeq]; norm_num
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hrInvEq : r⁻¹ = 4 * C * δ⁻¹ := by
    dsimp [r]
    field_simp [ne_of_gt hδ0, ne_of_gt hC0]
  have h4C : 4 * C ≤ tenTower 2 := by
    rw [hCeq]
    exact (show (4 : ℝ) * 6700 ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hrInv : r⁻¹ ≤ tenTower 3 := by
    rw [hrInvEq]
    exact tenTower_mul_le_succ 2 (mul_nonneg (by norm_num) hC0.le)
      (inv_nonneg.2 hδ0.le) h4C
      (gap_eight_fifths_inv_le_hundred.trans
        ((show (100 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
          ten_pow_thirty_le_tenTower_two))
  have hrSq0 : 0 < r ^ (2 : ℕ) := pow_pos hr0 2
  have hrSqInvEq : (r ^ (2 : ℕ))⁻¹ = r⁻¹ * r⁻¹ := by rw [pow_two, mul_inv_rev]
  have hrSqInv : (r ^ (2 : ℕ))⁻¹ ≤ tenTower 4 := by
    rw [hrSqInvEq]
    exact tenTower_mul_le_succ 3 (inv_nonneg.2 hr0.le) (inv_nonneg.2 hr0.le)
      hrInv hrInv
  unfold N_condWindowB
  change ((T_logLin (r ^ (2 : ℕ)) : ℕ) : ℝ) ≤ tenTower 8
  exact T_logLin_cast_le_tenTower_add_four 4 hrSq0 hrSqInv

private theorem N_caThrNonneg_37_cast_le_tenTower_six :
    ((N_caThrNonneg 3.7 : ℕ) : ℝ) ≤ tenTower 6 := by
  let C : ℝ := caConst 3.7
  have hCeq : C = 6700 := by dsimp [C]; norm_num [caConst, max_def]
  have hC0 : 0 < C := by rw [hCeq]; norm_num
  have hC2 : C ^ (2 : ℕ) ≤ tenTower 2 := by
    rw [hCeq]
    exact (show (6700 : ℝ) ^ (2 : ℕ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  unfold N_caThrNonneg
  change ((T_logLin ((C ^ (2 : ℕ))⁻¹) : ℕ) : ℝ) ≤ tenTower 6
  exact T_logLin_cast_le_tenTower_add_four 2 (inv_pos.2 (pow_pos hC0 2))
    (by rw [inv_inv]; exact hC2)

private theorem N_g1_37_cast_le_tenTower_eight :
    ((N_g1 3.7 : ℕ) : ℝ) ≤ tenTower 8 := by
  let δ : ℝ := 2 - Real.log 3 / Real.log 2
  let b : ℝ := δ ^ (2 : ℕ) / (320000 * ((3.7 : ℝ) + 3))
  have hδ0 : 0 < δ := by
    dsimp [δ]
    linarith [log_three_div_log_two_le_159_over_100]
  have hδInv : δ⁻¹ ≤ tenTower 2 :=
    gap_two_inv_le_four.trans
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hbInvEq : b⁻¹ = (320000 * ((3.7 : ℝ) + 3)) * (δ⁻¹ * δ⁻¹) := by
    dsimp [b]
    rw [pow_two]
    field_simp [ne_of_gt hδ0]
  have hden : 320000 * ((3.7 : ℝ) + 3) ≤ tenTower 2 :=
    (show 320000 * ((3.7 : ℝ) + 3) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hinvSq : δ⁻¹ * δ⁻¹ ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (inv_nonneg.2 hδ0.le) (inv_nonneg.2 hδ0.le) hδInv hδInv
  have hbInv : b⁻¹ ≤ tenTower 4 := by
    rw [hbInvEq]
    exact tenTower_mul_le_succ 3 (by norm_num) (by positivity)
      (hden.trans (tenTower_mono (by omega))) hinvSq
  have hlog : ((T_logLin b : ℕ) : ℝ) ≤ tenTower 8 :=
    T_logLin_cast_le_tenTower_add_four 4 hb0 hbInv
  have hrpow : ((N_rpowAbsorb 4 : ℕ) : ℝ) ≤ tenTower 4 :=
    N_rpowAbsorb_cast_le_tenTower_add_two 2 (by norm_num)
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
  unfold N_g1
  change ((max (max (N_rpowAbsorb 4) (T_logLin b)) 1 : ℕ) : ℝ) ≤ tenTower 8
  push_cast
  exact max_le (max_le (hrpow.trans (tenTower_mono (by omega))) hlog) (tenTower_one_le 8)

private theorem N_g2_cast_le_tenTower_six : ((N_g2 : ℕ) : ℝ) ≤ tenTower 6 := by
  have harg : (1 : ℝ) / 200 ≤ tenTower 2 :=
    (show (1 : ℝ) / 200 ≤ 1 by norm_num).trans (tenTower_one_le 2)
  have he : Real.exp ((1 : ℝ) / 200) ≤ tenTower 3 := exp_le_tenTower_succ 2 harg
  have hk : 4 * Real.exp ((1 : ℝ) / 200) ≤ tenTower 4 :=
    tenTower_mul_le_succ 3 (by norm_num) (Real.exp_pos _).le
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 3)) he
  have hr : ((N_rpowAbsorb (4 * Real.exp ((1 : ℝ) / 200)) : ℕ) : ℝ) ≤ tenTower 6 :=
    N_rpowAbsorb_cast_le_tenTower_add_two 4 (by positivity) hk
  have hl : ((N_logGe 1 : ℕ) : ℝ) ≤ tenTower 5 :=
    N_logGe_cast_le_tenTower_add_three 2 (tenTower_one_le 2)
  unfold N_g2
  push_cast
  exact max_le (max_le hr (hl.trans (tenTower_mono (by omega)))) (tenTower_one_le 6)

private theorem N_g3_cast_le_tenTower_five : ((N_g3 : ℕ) : ℝ) ≤ tenTower 5 := by
  have hr : ((N_rpowAbsorb 4 : ℕ) : ℝ) ≤ tenTower 4 :=
    N_rpowAbsorb_cast_le_tenTower_add_two 2 (by norm_num)
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
  have hl : ((N_logGe 1 : ℕ) : ℝ) ≤ tenTower 5 :=
    N_logGe_cast_le_tenTower_add_three 2 (tenTower_one_le 2)
  unfold N_g3
  push_cast
  exact max_le (max_le (hr.trans (tenTower_mono (by omega))) hl) (tenTower_one_le 5)

private theorem N_probGlobalGood_37_cast_le_tenTower_nine :
    ((N_probGlobalGood 3.7 : ℕ) : ℝ) ≤ tenTower 9 := by
  unfold N_probGlobalGood
  push_cast
  have hm1 : max ((N_caThrNonneg 3.7 : ℕ) : ℝ) ((N_g1 3.7 : ℕ) : ℝ)
      ≤ tenTower 8 := by
    exact max_le
      (N_caThrNonneg_37_cast_le_tenTower_six.trans (tenTower_mono (by omega)))
      N_g1_37_cast_le_tenTower_eight
  have hm2 : max ((N_g2 : ℕ) : ℝ) ((N_g3 : ℕ) : ℝ) ≤ tenTower 8 := by
    exact max_le (N_g2_cast_le_tenTower_six.trans (tenTower_mono (by omega)))
      (N_g3_cast_le_tenTower_five.trans (tenTower_mono (by omega)))
  have hm : max (max ((N_caThrNonneg 3.7 : ℕ) : ℝ) ((N_g1 3.7 : ℕ) : ℝ))
      (max ((N_g2 : ℕ) : ℝ) ((N_g3 : ℕ) : ℝ))
      ≤ tenTower 8 := by
    exact max_le hm1 hm2
  exact tenTower_add_le_succ 8 (by positivity) (by norm_num) hm (tenTower_one_le 8)

private theorem N_oscHigh_37_cast_le_tenTower_nine :
    ((N_oscHigh 3.7 : ℕ) : ℝ) ≤ tenTower 9 := by
  have hmain : ((N_oscMainHigh 3.7 : ℕ) : ℝ) ≤ tenTower 8 := by
    unfold N_oscMainHigh
    push_cast
    exact max_le
      ((show (40 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega))))
      (max_le (N_caWindow_37_cast_le_tenTower_six.trans (tenTower_mono (by omega)))
        N_condWindowB_ca37_cast_le_tenTower_eight)
  unfold N_oscHigh
  push_cast
  exact max_le (hmain.trans (tenTower_mono (by omega)))
    N_probGlobalGood_37_cast_le_tenTower_nine

private theorem S_zeta2_le_tenTower_two : S_zeta2 ≤ tenTower 2 := by
  have heq : S_zeta2 = Real.pi ^ (2 : ℕ) / 6 := by
    unfold S_zeta2
    calc
      (∑' k : ℕ, (k : ℝ) ^ (-(2 : ℝ))) =
          ∑' k : ℕ, (1 : ℝ) / (k : ℝ) ^ (2 : ℕ) := by
        apply tsum_congr
        intro k
        rw [Real.rpow_neg (Nat.cast_nonneg k)]
        simp [one_div]
      _ = Real.pi ^ (2 : ℕ) / 6 := hasSum_zeta_two.tsum_eq
  have hpiSq : Real.pi ^ (2 : ℕ) ≤ 16 := by
    nlinarith [Real.pi_pos.le, Real.pi_lt_four]
  rw [heq]
  exact (show Real.pi ^ (2 : ℕ) / 6 ≤ 3 by nlinarith).trans
    ((show (3 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))

private theorem C_oscMainHigh_37_le_tenTower_forty_four :
    C_oscMainHigh 3.7 ≤ tenTower 44 := by
  let B : ℝ := mainDecayExponent 3.7
  have hB0 : 0 < B := by dsimp [B]; exact mainDecayExponent_pos 3.7 (by norm_num)
  have hB : B ≤ tenTower 2 := mainDecayExponent_37_le_tenTower_two
  have h40B : (40 : ℝ) ^ B ≤ tenTower 4 :=
    rpow_le_tenTower_add_two 2 (by norm_num) hB0.le
      ((show (40 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        ten_pow_thirty_le_tenTower_two) hB
  have h3C : 3 * C_renewalWhite B ≤ tenTower 43 :=
    tenTower_mul_le_succ 42 (by norm_num) (C_renewalWhite_pos B).le
      ((show (3 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 42))
      C_renewalWhite_main_le_tenTower_forty_two
  unfold C_oscMainHigh
  exact tenTower_mul_le_succ 43 (mul_nonneg (by norm_num) (C_renewalWhite_pos B).le)
    (Real.rpow_nonneg (by norm_num) _) h3C (h40B.trans (tenTower_mono (by omega)))

private theorem C_oscHigh_37_le_tenTower_forty_five :
    C_oscHigh 3.7 ≤ tenTower 45 := by
  have hm : max (C_oscMainHigh 3.7) 6 ≤ tenTower 44 :=
    max_le C_oscMainHigh_37_le_tenTower_forty_four
      ((show (6 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 44))
  unfold C_oscHigh
  exact tenTower_mul_le_succ 44 (by norm_num) (by positivity)
    ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 44)) hm

private theorem C_fineScale_17_le_tenTower_forty_seven :
    C_fineScale 1.7 ≤ tenTower 47 := by
  have hbase : ((max 9 (N_oscHigh 3.7) : ℕ) : ℝ) ≤ tenTower 9 := by
    push_cast
    exact max_le
      ((show (9 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 9))
      N_oscHigh_37_cast_le_tenTower_nine
  have hpow : (((max 9 (N_oscHigh 3.7) : ℕ) : ℝ) ^ (1.7 : ℝ)) ≤ tenTower 11 :=
    rpow_le_tenTower_add_two 9 (by positivity) (by norm_num) hbase
      ((show (1.7 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 9))
  have harm1 : 2 * (((max 9 (N_oscHigh 3.7) : ℕ) : ℝ) ^ (1.7 : ℝ))
      ≤ tenTower 12 :=
    tenTower_mul_le_succ 11 (by norm_num) (Real.rpow_nonneg (by positivity) _)
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 11)) hpow
  have harm2 : C_oscHigh 3.7 * S_zeta2 ≤ tenTower 46 :=
    tenTower_mul_le_succ 45 (C_oscHigh_pos 3.7).le S_zeta2_nonneg
      C_oscHigh_37_le_tenTower_forty_five
      (S_zeta2_le_tenTower_two.trans (tenTower_mono (by omega)))
  unfold C_fineScale
  rw [show (1.7 : ℝ) + 2 = 3.7 by norm_num]
  exact tenTower_add_le_succ 46 (by positivity) (mul_nonneg (C_oscHigh_pos 3.7).le S_zeta2_nonneg)
    (harm1.trans (tenTower_mono (by omega))) harm2

private theorem C_mainZbridge_le_tenTower_forty_nine :
    C_mainZbridge ≤ tenTower 49 := by
  have hfactor : (1 / 200000 : ℝ) ^ (-(1.7 : ℝ)) ≤ tenTower 4 := by
    rw [Real.rpow_neg_eq_inv_rpow]
    have hbase : (1 / 200000 : ℝ)⁻¹ = 200000 := by norm_num
    rw [hbase]
    have hp : (200000 : ℝ) ^ (1.7 : ℝ) ≤ tenTower 4 :=
      rpow_le_tenTower_add_two 2 (by norm_num) (by norm_num)
        ((show (200000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
          ten_pow_thirty_le_tenTower_two)
        ((show (1.7 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
    exact hp
  have h4C : 4 * C_fineScale 1.7 ≤ tenTower 48 :=
    tenTower_mul_le_succ 47 (by norm_num) (C_fineScale_pos 1.7).le
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 47))
      C_fineScale_17_le_tenTower_forty_seven
  unfold C_mainZbridge
  exact tenTower_mul_le_succ 48 (mul_nonneg (by norm_num) (C_fineScale_pos 1.7).le)
    (Real.rpow_nonneg (by norm_num) _) h4C (hfactor.trans (tenTower_mono (by omega)))

/-! ## §5 and §3 constant propagation -/

private theorem C_valSumGeom_le_tenTower_two : C_valSumGeom ≤ tenTower 2 := by
  calc
    C_valSumGeom ≤ (10 : ℝ) ^ (30 : ℕ) := by
      norm_num [C_valSumGeom, C_valuationDistC, K_intTest, C_geomTail]
    _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two

private theorem C_fpApprox_le_tenTower_two : C_fpApprox ≤ tenTower 2 := by
  calc
    C_fpApprox ≤ (10 : ℝ) ^ (30 : ℕ) := by
      norm_num [C_fpApprox, C_windowReduce, C_affineReindex, C_steppedMid,
        C_goodTupleDev, C_passtimeWindow, C_passtimeInner, C_edgeMass,
        C_valSumGeom, C_valuationDistC, K_intTest, C_geomTail]
    _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two

private theorem C_perNHarm_le_tenTower_two : C_perNHarm ≤ tenTower 2 := by
  calc
    C_perNHarm ≤ (10 : ℝ) ^ (30 : ℕ) := by
      norm_num [C_perNHarm, C_epsPerNHarm, alpha]
    _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two

private theorem C_harmZfine_le_tenTower_two : C_harmZfine ≤ tenTower 2 := by
  calc
    C_harmZfine ≤ (10 : ℝ) ^ (30 : ℕ) := by
      norm_num [C_harmZfine, C_syracZsub, C_goodWhp, C_geomTail]
    _ ≤ tenTower 2 := ten_pow_thirty_le_tenTower_two

private theorem C_harmonicZ_le_tenTower_fifty : C_harmonicZ ≤ tenTower 50 := by
  unfold C_harmonicZ
  exact tenTower_add_le_succ 49 C_harmZfine_pos.le C_mainZbridge_pos.le
    (C_harmZfine_le_tenTower_two.trans (tenTower_mono (by omega)))
    C_mainZbridge_le_tenTower_forty_nine

private theorem C_perNTermEval_le_tenTower_fifty_one : C_perNTermEval ≤ tenTower 51 := by
  unfold C_perNTermEval
  exact tenTower_add_le_succ 50 C_perNHarm_pos.le C_harmonicZ_pos.le
    (C_perNHarm_le_tenTower_two.trans (tenTower_mono (by omega)))
    C_harmonicZ_le_tenTower_fifty

private theorem C_mainZ_le_tenTower_fifty_one : C_mainZ ≤ tenTower 51 := by
  have hfp1 : 1 + C_fpApprox ≤ tenTower 3 :=
    tenTower_add_le_succ 2 (by norm_num) C_fpApprox_pos.le (tenTower_one_le 2)
      C_fpApprox_le_tenTower_two
  have htail : 1000 * (1 + C_fpApprox) ≤ tenTower 4 :=
    tenTower_mul_le_succ 3 (by norm_num) (add_nonneg (by norm_num) C_fpApprox_pos.le)
      ((show (1000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega)))) hfp1
  have hrest : C_perNHarm + 1000 * (1 + C_fpApprox) ≤ tenTower 5 :=
    tenTower_add_le_succ 4 C_perNHarm_pos.le
      (mul_nonneg (by norm_num) (add_nonneg (by norm_num) C_fpApprox_pos.le))
      (C_perNHarm_le_tenTower_two.trans (tenTower_mono (by omega))) htail
  unfold C_mainZ
  calc
    C_perNHarm + C_harmonicZ + 1000 * (1 + C_fpApprox) =
        C_harmonicZ + (C_perNHarm + 1000 * (1 + C_fpApprox)) := by ring
    _ ≤ tenTower 51 := tenTower_add_le_succ 50 C_harmonicZ_pos.le
      (add_nonneg C_perNHarm_pos.le
        (mul_nonneg (by norm_num) (add_nonneg (by norm_num) C_fpApprox_pos.le)))
      C_harmonicZ_le_tenTower_fifty (hrest.trans (tenTower_mono (by omega)))

private theorem C_approxToZ_le_tenTower_fifty_three : C_approxToZ ≤ tenTower 53 := by
  have hcoef : 2 / Real.log (4 / 3) + 6000 ≤ tenTower 2 := by
    have hdiv : 2 / Real.log (4 / 3) ≤ 8 := by
      rw [div_eq_mul_inv]
      nlinarith [log_four_thirds_inv_le_four]
    exact (show 2 / Real.log (4 / 3) + 6000 ≤ (10 : ℝ) ^ (30 : ℕ) by
      nlinarith).trans ten_pow_thirty_le_tenTower_two
  have hterm1 : (2 / Real.log (4 / 3) + 6000) * C_perNTermEval ≤ tenTower 52 :=
    tenTower_mul_le_succ 51 (by positivity) C_perNTermEval_pos.le
      (hcoef.trans (tenTower_mono (by omega))) C_perNTermEval_le_tenTower_fifty_one
  have hterm2 : C_mainZ * 6000 ≤ tenTower 52 :=
    tenTower_mul_le_succ 51 C_mainZ_pos.le (by norm_num) C_mainZ_le_tenTower_fifty_one
      ((show (6000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega))))
  unfold C_approxToZ
  exact tenTower_add_le_succ 52
    (mul_nonneg (add_nonneg (by positivity) (by norm_num)) C_perNTermEval_pos.le)
    (mul_nonneg C_mainZ_pos.le (by norm_num)) hterm1 hterm2

private theorem C_windowStable_le_tenTower_fifty_four : C_windowStable ≤ tenTower 54 := by
  unfold C_windowStable
  exact tenTower_mul_le_succ 53 (by norm_num) C_approxToZ_pos.le
    ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 53))
    C_approxToZ_le_tenTower_fifty_three

private theorem C_stab_le_tenTower_fifty_six : C_stab ≤ tenTower 56 := by
  have h4fp : 4 * C_fpApprox ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 (by norm_num) C_fpApprox_pos.le
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
      C_fpApprox_le_tenTower_two
  have hhead : C_valSumGeom + 4 * C_fpApprox ≤ tenTower 4 :=
    tenTower_add_le_succ 3 C_valSumGeom_pos.le
      (mul_nonneg (by norm_num) C_fpApprox_pos.le)
      (C_valSumGeom_le_tenTower_two.trans (tenTower_mono (by omega))) h4fp
  have h2w : 2 * C_windowStable ≤ tenTower 55 :=
    tenTower_mul_le_succ 54 (by norm_num) C_windowStable_pos.le
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 54))
      C_windowStable_le_tenTower_fifty_four
  unfold C_stab
  exact tenTower_add_le_succ 55
    (add_nonneg C_valSumGeom_pos.le (mul_nonneg (by norm_num) C_fpApprox_pos.le))
    (mul_nonneg (by norm_num) C_windowStable_pos.le)
    (hhead.trans (tenTower_mono (by omega))) h2w

private theorem C_descLadder_le_tenTower_fifty_seven : C_descLadder ≤ tenTower 57 := by
  have hstep : C_descStep ≤ tenTower 57 := by
    unfold C_descStep
    exact tenTower_mul_le_succ 56 (by norm_num) C_stab_pos.le
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 56))
      C_stab_le_tenTower_fifty_six
  unfold C_descLadder
  exact max_le (C_valSumGeom_le_tenTower_two.trans (tenTower_mono (by omega))) hstep

private theorem c_valSumGeom_eq :
    c_valSumGeom = (1 / 32000000 : ℝ) / Real.log 2 := by
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogHalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlin400 : linearDecay (1 / 400 : ℝ) = 1 / 320000 := by
    unfold linearDecay
    rw [min_eq_left]
    · norm_num
    · norm_num
  have hlin4000 : linearDecay (1 / 4000 : ℝ) = 1 / 32000000 := by
    unfold linearDecay
    rw [min_eq_left]
    · norm_num
    · norm_num
  have hfin400 : finalDecay (1 / 400 : ℝ) = 1 / 320000 := by
    unfold finalDecay
    rw [min_eq_right]
    · exact hlin400
    · rw [hlin400]
      linarith
  have hfin4000 : finalDecay (1 / 4000 : ℝ) = 1 / 32000000 := by
    unfold finalDecay
    rw [min_eq_right]
    · exact hlin4000
    · rw [hlin4000]
      linarith
  have hcval : c_valuationDist 1 = (1 / 320000 : ℝ) / Real.log 2 := by
    unfold c_valuationDist c_geomTail
    norm_num
    exact hfin400
  unfold c_valSumGeom
  rw [hcval]
  have hsecond : finalDecay (c_geomTail * 0.1) / Real.log 2 =
      (1 / 32000000 : ℝ) / Real.log 2 := by
    rw [show c_geomTail * (0.1 : ℝ) = (1 / 4000 : ℝ) by norm_num [c_geomTail], hfin4000]
  rw [hsecond, min_eq_right]
  exact div_le_div_of_nonneg_right (by norm_num) hlog0.le

private theorem c_valSumTail_eq :
    c_valSumTail = (1 / 640000000 : ℝ) / Real.log 2 := by
  unfold c_valSumTail
  rw [c_valSumGeom_eq]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  ring

private theorem c_valSumTail_le_one_fifth : c_valSumTail ≤ (1 : ℝ) / 5 := by
  rw [c_valSumTail_eq, div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hlogHalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  nlinarith

private theorem c_fpApprox_eq_valSumTail : c_fpApprox = c_valSumTail := by
  have hsmall1 : c_valSumTail ≤ 1 := c_valSumTail_le_one_fifth.trans (by norm_num)
  unfold c_fpApprox c_windowReduce c_passtimeWindow c_passtimeInner c_affineReindex
    c_steppedMid c_goodTupleDev c_edgeMass c_earlyReturn c_truncation
  rw [min_eq_right (by norm_num : (1 / 5 : ℝ) ≤ 1),
    min_eq_left c_valSumTail_le_one_fifth, min_eq_right hsmall1]
  simpa only [min_self] using min_eq_left hsmall1

private theorem c_approxToZ_eq : c_approxToZ = (1 : ℝ) / 5 := by
  unfold c_approxToZ c_IyRatio c_perNTermEval c_perNHarm c_harmonicZ c_harmZfine
    c_mainZbridge
  norm_num [min_def]

private theorem c_stab_eq_valSumTail : c_stab = c_valSumTail := by
  unfold c_stab
  rw [c_fpApprox_eq_valSumTail, min_self, c_approxToZ_eq,
    min_eq_left c_valSumTail_le_one_fifth]

private theorem c_ladder_eq :
    c_ladder = (1 / 640000000 : ℝ) / Real.log 2 := by
  unfold c_ladder
  rw [c_stab_eq_valSumTail, min_self, c_valSumTail_eq]

private theorem c_ladder_inv_le_tenTower_two : c_ladder⁻¹ ≤ tenTower 2 := by
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ 2 := (Real.log_le_self (by norm_num)).trans (by norm_num)
  rw [c_ladder_eq]
  have heq : ((1 / 640000000 : ℝ) / Real.log 2)⁻¹ = 640000000 * Real.log 2 := by
    field_simp [ne_of_gt hlog0]
  rw [heq]
  exact (show 640000000 * Real.log 2 ≤ (10 : ℝ) ^ (30 : ℕ) by
    nlinarith).trans ten_pow_thirty_le_tenTower_two

private theorem log_alpha_inv_le_two_thousand : (Real.log alpha)⁻¹ ≤ (2000 : ℝ) := by
  have hx : (0 : ℝ) ≤ 1 / 1000 := by norm_num
  have hlower := Real.le_log_one_add_of_nonneg hx
  have halpha : Real.log alpha = Real.log (1 + (1 / 1000 : ℝ)) := by
    congr 1
    norm_num [alpha]
  rw [← halpha] at hlower
  have hlog0 : 0 < Real.log alpha := Real.log_pos (by norm_num [alpha])
  rw [inv_le_iff_one_le_mul₀ hlog0]
  nlinarith

private theorem descGeomFactor_le_tenTower_five :
    1 + (1 - alpha ^ (-c_ladder))⁻¹ ≤ tenTower 5 := by
  have ha0 : 0 < alpha := by norm_num [alpha]
  have ha1 : 1 < alpha := by norm_num [alpha]
  have hc0 : 0 < c_ladder := c_ladder_pos
  let z : ℝ := c_ladder * Real.log alpha
  have hz0 : 0 < z := by dsimp [z]; exact mul_pos hc0 (Real.log_pos ha1)
  have hpowEq : alpha ^ (-c_ladder) = Real.exp (-z) := by
    rw [Real.rpow_def_of_pos ha0]
    dsimp [z]
    congr 1
    ring
  have hzInvEq : z⁻¹ = (Real.log alpha)⁻¹ * c_ladder⁻¹ := by
    dsimp [z]
    rw [mul_inv_rev]
  have hzInv : z⁻¹ ≤ tenTower 3 := by
    rw [hzInvEq]
    exact tenTower_mul_le_succ 2 (inv_nonneg.2 (Real.log_pos ha1).le)
      (inv_nonneg.2 hc0.le)
      (log_alpha_inv_le_two_thousand.trans
        ((show (2000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
          ten_pow_thirty_le_tenTower_two)) c_ladder_inv_le_tenTower_two
  have hden : (1 - alpha ^ (-c_ladder))⁻¹ ≤ tenTower 4 := by
    rw [hpowEq]
    have hraw : (1 - Real.exp (-z))⁻¹ ≤ 1 + z⁻¹ := by
      simpa [one_div] using one_div_one_sub_exp_neg_le hz0
    exact hraw.trans
      (tenTower_add_le_succ 3 (by norm_num) (inv_nonneg.2 hz0.le)
        (tenTower_one_le 3) hzInv)
  exact tenTower_add_le_succ 4 (by norm_num) (by
    rw [hpowEq]
    have : 0 < 1 - Real.exp (-z) := by
      rw [sub_pos, Real.exp_lt_one_iff]
      linarith
    positivity) (tenTower_one_le 4) hden

private theorem C_descWhp_le_tenTower_fifty_nine : C_descWhp ≤ tenTower 59 := by
  have ha0 : 0 < alpha := by norm_num [alpha]
  have ha1 : 1 < alpha := by norm_num [alpha]
  have hcl : c_ladder = c_valSumTail := by
    unfold c_ladder
    rw [c_stab_eq_valSumTail, min_self]
  have hc1 : c_ladder ≤ 1 := by
    rw [hcl]
    exact c_valSumTail_le_one_fifth.trans (by norm_num)
  have hcpow : alpha ^ c_ladder ≤ tenTower 4 :=
    rpow_le_tenTower_add_two 2 ha0.le c_ladder_pos.le
      ((show alpha ≤ 10 by norm_num [alpha]).trans (ten_le_tenTower 2))
      (hc1.trans (tenTower_one_le 2))
  have hpowlt : alpha ^ (-c_ladder) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg ha1 (neg_lt_zero.mpr c_ladder_pos)
  have hfac0 : 0 ≤ 1 + (1 - alpha ^ (-c_ladder))⁻¹ := by
    have : 0 < 1 - alpha ^ (-c_ladder) := sub_pos.mpr hpowlt
    positivity
  have hp : C_descLadder * (1 + (1 - alpha ^ (-c_ladder))⁻¹) ≤ tenTower 58 :=
    tenTower_mul_le_succ 57 C_descLadder_pos.le hfac0
      C_descLadder_le_tenTower_fifty_seven
      (descGeomFactor_le_tenTower_five.trans (tenTower_mono (by omega)))
  unfold C_descWhp
  exact tenTower_mul_le_succ 58 (mul_nonneg C_descLadder_pos.le hfac0)
    (Real.rpow_nonneg ha0.le _)
    hp (hcpow.trans (tenTower_mono (by omega)))

private theorem C_windowBad_le_tenTower_sixty : C_windowBad ≤ tenTower 60 := by
  unfold C_windowBad
  exact tenTower_mul_le_succ 59 (by norm_num) C_descWhp_pos.le
    ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 59))
    C_descWhp_le_tenTower_fifty_nine

/-! ## The cutoff tree -/

private theorem X_windowBase_le_tenTower_four : X_windowBase ≤ tenTower 4 := by
  have hsmall : X_nZeroPos ≤ tenTower 2 := by
    unfold X_nZeroPos
    exact (show (2 : ℝ) ^ (11 : ℕ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hlarge : (2 : ℝ) ^ (2000 : ℝ) ≤ tenTower 4 :=
    rpow_le_tenTower_add_two 2 (by norm_num) (by norm_num)
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
      ((show (2000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        ten_pow_thirty_le_tenTower_two)
  unfold X_windowBase
  exact max_le (hsmall.trans (tenTower_mono (by omega))) hlarge

private theorem X_firstPassNonescape_le_tenTower_four : X_firstPassNonescape ≤ tenTower 4 := by
  have hintDev : X_intTestDev ≤ tenTower 4 := by
    unfold X_intTestDev
    exact max_le X_windowBase_le_tenTower_four (tenTower_one_le 4)
  have hintErr : X_intTestErr ≤ tenTower 4 := by
    unfold X_intTestErr
    exact max_le (max_le hintDev X_windowBase_le_tenTower_four)
      (max_le X_windowBase_le_tenTower_four
        (max_le (by
          unfold X_nZeroPos
          exact (show (2 : ℝ) ^ (11 : ℕ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
            (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega))))
          (tenTower_one_le 4)))
  have hintLog : X_intTestLogUnif ≤ tenTower 4 := by
    unfold X_intTestLogUnif
    exact max_le hintErr (tenTower_one_le 4)
  have hvalGeom : X_valSumGeom ≤ tenTower 4 := by
    unfold X_valSumGeom
    exact max_le hintLog (tenTower_one_le 4)
  have hrpowN : X_rpowNZero ≤ tenTower 2 := by
    unfold X_rpowNZero
    exact (show (2 : ℝ) ^ (20 : ℕ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hvalTail : X_valSumTail ≤ tenTower 4 := by
    unfold X_valSumTail
    exact max_le hvalGeom (hrpowN.trans (tenTower_mono (by omega)))
  have heps99 : X_rpowEps (0.99 : ℝ) (1 / 4 : ℝ) ≤ tenTower 4 := by
    unfold X_rpowEps
    apply max_le (tenTower_one_le 4)
    exact rpow_le_tenTower_add_two 2 (by norm_num) (by norm_num)
      ((show (1 / (1 / 4 : ℝ)) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
      ((show (1 / (1 - (0.99 : ℝ)) : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        ten_pow_thirty_le_tenTower_two)
  have heps20 : X_rpowEps (0.2 : ℝ) (1 / 4 : ℝ) ≤ tenTower 4 := by
    unfold X_rpowEps
    apply max_le (tenTower_one_le 4)
    exact rpow_le_tenTower_add_two 2 (by norm_num) (by norm_num)
      ((show (1 / (1 / 4 : ℝ)) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
      ((show (1 / (1 - (0.2 : ℝ)) : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
  have hdescentPow : X_descentPow ≤ tenTower 2 := by
    unfold X_descentPow
    exact (show (2 : ℝ) ^ (30 : ℕ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  have hpasses : X_descentPasses ≤ tenTower 4 := by
    unfold X_descentPasses
    exact max_le (max_le heps99 heps20)
      (max_le (hdescentPow.trans (tenTower_mono (by omega)))
        ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 4)))
  unfold X_firstPassNonescape
  exact max_le hvalTail hpasses

private theorem X_logRpowExp_le_tenTower_nine_of_bounds {p κ θ : ℝ}
    (hp0 : 0 < p) (hκ0 : 0 < κ) (hθ0 : 0 < θ)
    (hp : p ≤ tenTower 2) (hκinv : κ⁻¹ ≤ tenTower 2)
    (hθinv : θ⁻¹ ≤ tenTower 2) : X_logRpowExp p κ θ ≤ tenTower 9 := by
  let ε : ℝ := κ * θ / p
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hεInvEq : ε⁻¹ = p * κ⁻¹ * θ⁻¹ := by
    dsimp [ε]
    field_simp [ne_of_gt hp0, ne_of_gt hκ0, ne_of_gt hθ0]
  have hpκ : p * κ⁻¹ ≤ tenTower 3 :=
    tenTower_mul_le_succ 2 hp0.le (inv_nonneg.2 hκ0.le) hp hκinv
  have hεInv : ε⁻¹ ≤ tenTower 4 := by
    rw [hεInvEq]
    exact tenTower_mul_le_succ 3 (mul_nonneg hp0.le (inv_nonneg.2 hκ0.le))
      (inv_nonneg.2 hθ0.le) hpκ (hθinv.trans (tenTower_mono (by omega)))
  have hbase : 2 / ε ≤ tenTower 5 := by
    rw [div_eq_mul_inv]
    exact tenTower_mul_le_succ 4 (by norm_num) (inv_nonneg.2 hε0.le)
      ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 4)) hεInv
  have hbase0 : 0 ≤ 2 / ε := div_nonneg (by norm_num) hε0.le
  have hlogEps : X_logEpsMul ε ≤ tenTower 6 := by
    unfold X_logEpsMul
    rw [pow_two]
    exact tenTower_mul_le_succ 5 hbase0 hbase0 hbase hbase
  have hinner : max (X_logEpsMul ε) 1 ≤ tenTower 6 :=
    max_le hlogEps (tenTower_one_le 6)
  have hpow : (max (X_logEpsMul ε) 1) ^ (1 / θ) ≤ tenTower 8 := by
    rw [one_div]
    exact rpow_le_tenTower_add_two 6 (by positivity) (inv_nonneg.2 hθ0.le) hinner
      (hθinv.trans (tenTower_mono (by omega)))
  have harg : max ((max (X_logEpsMul ε) 1) ^ (1 / θ)) 1 ≤ tenTower 8 :=
    max_le hpow (tenTower_one_le 8)
  unfold X_logRpowExp
  change Real.exp (max ((max (X_logEpsMul ε) 1) ^ (1 / θ)) 1) ≤ tenTower 9
  exact exp_le_tenTower_succ 8 harg

private theorem c_valuationDist_one_div_twenty_inv_le_tenTower_two :
    (c_valuationDist 1 / 20)⁻¹ ≤ tenTower 2 := by
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ 2 := (Real.log_le_self (by norm_num)).trans (by norm_num)
  have hlin : linearDecay (1 / 400 : ℝ) = 1 / 320000 := by
    unfold linearDecay
    rw [min_eq_left] <;> norm_num
  have hfin : finalDecay (1 / 400 : ℝ) = 1 / 320000 := by
    unfold finalDecay
    rw [min_eq_right]
    · exact hlin
    · rw [hlin]
      linarith [Real.log_two_gt_d9]
  have hc : c_valuationDist 1 = (1 / 320000 : ℝ) / Real.log 2 := by
    unfold c_valuationDist c_geomTail
    norm_num
    exact hfin
  rw [hc]
  have heq : (((1 / 320000 : ℝ) / Real.log 2) / 20)⁻¹ =
      6400000 * Real.log 2 := by
    field_simp [ne_of_gt hlog0]
    norm_num
  rw [heq]
  exact (show 6400000 * Real.log 2 ≤ (10 : ℝ) ^ (30 : ℕ) by
    nlinarith).trans ten_pow_thirty_le_tenTower_two

private theorem X_logRpowExp_Gweight_le_tenTower_nine :
    X_logRpowExp 2 (K_Gweight c_geomTail) 0.2 ≤ tenTower 9 := by
  have hkEq : K_Gweight c_geomTail = (1 : ℝ) / 40000 := by
    norm_num [K_Gweight, c_geomTail, min_def]
  have hk0 : 0 < K_Gweight c_geomTail := K_Gweight_pos c_geomTail_pos
  have hkInv : (K_Gweight c_geomTail)⁻¹ ≤ tenTower 2 := by
    rw [hkEq]
    norm_num only [one_div, inv_inv]
    exact (show (40000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two
  exact X_logRpowExp_le_tenTower_nine_of_bounds (by norm_num) hk0 (by norm_num)
    ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2)) hkInv
    ((show ((0.2 : ℝ))⁻¹ ≤ 10 by norm_num).trans (ten_le_tenTower 2))

private theorem X_logRpowExp_valuation_le_tenTower_nine :
    X_logRpowExp 2 (c_valuationDist 1 / 20) 1 ≤ tenTower 9 := by
  have hk0 : 0 < c_valuationDist 1 / 20 := div_pos (c_valuationDist_pos one_pos) (by norm_num)
  exact X_logRpowExp_le_tenTower_nine_of_bounds (by norm_num) hk0 (by norm_num)
    ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
    c_valuationDist_one_div_twenty_inv_le_tenTower_two
    (by simpa using tenTower_one_le 2)

private theorem X_intTestLogUnif_le_tenTower_four : X_intTestLogUnif ≤ tenTower 4 := by
  have hintDev : X_intTestDev ≤ tenTower 4 := by
    unfold X_intTestDev
    exact max_le X_windowBase_le_tenTower_four (tenTower_one_le 4)
  have hintErr : X_intTestErr ≤ tenTower 4 := by
    unfold X_intTestErr
    exact max_le (max_le hintDev X_windowBase_le_tenTower_four)
      (max_le X_windowBase_le_tenTower_four
        (max_le (by
          unfold X_nZeroPos
          exact (show (2 : ℝ) ^ (11 : ℕ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
            (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega))))
          (tenTower_one_le 4)))
  unfold X_intTestLogUnif
  exact max_le hintErr (tenTower_one_le 4)

private theorem X_rpowNZero_le_tenTower_two : X_rpowNZero ≤ tenTower 2 := by
  unfold X_rpowNZero
  exact (show (2 : ℝ) ^ (20 : ℕ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
    ten_pow_thirty_le_tenTower_two

private theorem exp_le_tenTower_three_of_le_ten_pow_thirty {x : ℝ}
    (hx : x ≤ (10 : ℝ) ^ (30 : ℕ)) : Real.exp x ≤ tenTower 3 :=
  exp_le_tenTower_succ 2 (hx.trans ten_pow_thirty_le_tenTower_two)

private theorem exp_one_le_tenTower_three : Real.exp 1 ≤ tenTower 3 :=
  exp_le_tenTower_three_of_le_ten_pow_thirty (by norm_num)

private theorem exp_twenty_le_tenTower_three : Real.exp 20 ≤ tenTower 3 :=
  exp_le_tenTower_three_of_le_ten_pow_thirty (by norm_num)

private theorem exp_one_hundred_thousand_le_tenTower_three :
    Real.exp 100000 ≤ tenTower 3 :=
  exp_le_tenTower_three_of_le_ten_pow_thirty (by norm_num)

private theorem two_rpow_two_thousand_le_tenTower_four :
    (2 : ℝ) ^ (2000 : ℝ) ≤ tenTower 4 :=
  rpow_le_tenTower_add_two 2 (by norm_num) (by norm_num)
    ((show (2 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
    ((show (2000 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
      ten_pow_thirty_le_tenTower_two)

private theorem X_goodTupleDev_le_tenTower_nine : X_goodTupleDev ≤ tenTower 9 := by
  have hGweight : X_Gweight ≤ tenTower 3 := by
    unfold X_Gweight
    exact exp_twenty_le_tenTower_three
  unfold X_goodTupleDev
  exact max_le (X_intTestLogUnif_le_tenTower_four.trans (tenTower_mono (by omega)))
    (max_le X_logRpowExp_Gweight_le_tenTower_nine
      (max_le (X_rpowNZero_le_tenTower_two.trans (tenTower_mono (by omega)))
        (max_le X_logRpowExp_valuation_le_tenTower_nine
          (max_le (exp_twenty_le_tenTower_three.trans (tenTower_mono (by omega)))
            (hGweight.trans (tenTower_mono (by omega)))))))

private theorem X_goodTupleWhp_le_tenTower_nine : X_goodTupleWhp ≤ tenTower 9 := by
  unfold X_goodTupleWhp
  exact max_le X_goodTupleDev_le_tenTower_nine (tenTower_one_le 9)

private theorem X_edgeMass_le_tenTower_four : X_edgeMass ≤ tenTower 4 := by
  unfold X_edgeMass
  exact max_le (max_le two_rpow_two_thousand_le_tenTower_four
    X_windowBase_le_tenTower_four) two_rpow_two_thousand_le_tenTower_four

private theorem X_passtimeInner_le_tenTower_nine : X_passtimeInner ≤ tenTower 9 := by
  unfold X_passtimeInner X_edgeOfGood
  exact max_le
    (max_le (max_le X_goodTupleWhp_le_tenTower_nine
      (X_edgeMass_le_tenTower_four.trans (tenTower_mono (by omega))))
      (exp_one_hundred_thousand_le_tenTower_three.trans (tenTower_mono (by omega))))
    (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))

private theorem X_passtimeWindow_le_tenTower_nine : X_passtimeWindow ≤ tenTower 9 := by
  unfold X_passtimeWindow
  exact max_le (max_le
    (X_firstPassNonescape_le_tenTower_four.trans (tenTower_mono (by omega)))
    X_passtimeInner_le_tenTower_nine)
    (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))

private theorem X_windowReduce_le_tenTower_nine : X_windowReduce ≤ tenTower 9 := by
  unfold X_windowReduce
  exact max_le (max_le X_goodTupleWhp_le_tenTower_nine
    X_passtimeWindow_le_tenTower_nine)
    (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))

private theorem X_mZeroIy_le_tenTower_three : X_mZeroIy ≤ tenTower 3 := by
  unfold X_mZeroIy
  exact exp_one_hundred_thousand_le_tenTower_three

private theorem X_twoMZero_le_tenTower_three : X_twoMZero ≤ tenTower 3 := by
  unfold X_twoMZero
  exact exp_one_hundred_thousand_le_tenTower_three

private theorem X_slackKey_le_tenTower_three : X_slackKey ≤ tenTower 3 := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 2 ≤ 2 := (Real.log_le_self (by norm_num)).trans (by norm_num)
  have hbase0 : 0 ≤ 2 * Real.log 2 + 1 := by positivity
  have hbase : 2 * Real.log 2 + 1 ≤ 5 := by linarith
  have hp : (2 * Real.log 2 + 1) ^ (10 : ℕ) ≤ (5 : ℝ) ^ (10 : ℕ) := by
    gcongr
  unfold X_slackKey
  exact exp_le_tenTower_three_of_le_ten_pow_thirty
    (hp.trans (by norm_num))

private theorem X_stepbackReduce_le_tenTower_nine : X_stepbackReduce ≤ tenTower 9 := by
  have hscale : X_stepbackScale ≤ tenTower 3 := by
    unfold X_stepbackScale
    exact max_le X_mZeroIy_le_tenTower_three exp_one_hundred_thousand_le_tenTower_three
  have hsize : X_stepbackSize ≤ tenTower 3 := by
    unfold X_stepbackSize
    exact max_le (max_le hscale X_slackKey_le_tenTower_three) X_mZeroIy_le_tenTower_three
  have hfpm : X_fpmLeStepped ≤ tenTower 3 := by
    unfold X_fpmLeStepped
    exact max_le hsize X_mZeroIy_le_tenTower_three
  have hlog43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  let d : ℝ := (alpha - 1) / 100 * Real.log (4 / 3)
  have hd0 : 0 < d := by
    dsimp [d]
    exact mul_pos (by norm_num [alpha]) hlog43
  have hdInvEq : d⁻¹ = 100000 * (Real.log (4 / 3))⁻¹ := by
    dsimp [d]
    norm_num [alpha]
    ring
  have hdInv : d⁻¹ ≤ 400000 := by
    rw [hdInvEq]
    nlinarith [log_four_thirds_inv_le_four]
  have hbase0 : 0 ≤ 5 / d + 1 := by positivity
  have hbase : 5 / d + 1 ≤ tenTower 2 := by
    rw [div_eq_mul_inv]
    exact (show 5 * d⁻¹ + 1 ≤ tenTower 2 by
      have hnum : 5 * d⁻¹ + 1 ≤ (2000001 : ℝ) := by nlinarith
      exact hnum.trans ((show (2000001 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        ten_pow_thirty_le_tenTower_two))
  have hpow : (5 / d + 1) ^ (10 / 3 : ℝ) ≤ tenTower 4 :=
    rpow_le_tenTower_add_two 2 hbase0 (by norm_num) hbase
      ((show (10 / 3 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 2))
  have hearlySize : X_earlyReturnSize ≤ tenTower 5 := by
    unfold X_earlyReturnSize
    change Real.exp (max 1 ((5 / d + 1) ^ (10 / 3 : ℝ))) ≤ tenTower 5
    exact exp_le_tenTower_succ 4
      (max_le (tenTower_one_le 4) hpow)
  have hearly : X_earlyReturn ≤ tenTower 5 := by
    unfold X_earlyReturn
    exact max_le (max_le hearlySize
      (X_mZeroIy_le_tenTower_three.trans (tenTower_mono (by omega))))
      (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))
  have hstepped : X_steppedMid ≤ tenTower 9 := by
    unfold X_steppedMid
    exact max_le (max_le X_goodTupleWhp_le_tenTower_nine
      (hearly.trans (tenTower_mono (by omega))))
      (max_le (X_mZeroIy_le_tenTower_three.trans (tenTower_mono (by omega)))
        (exp_one_le_tenTower_three.trans (tenTower_mono (by omega))))
  unfold X_stepbackReduce
  exact max_le (hfpm.trans (tenTower_mono (by omega))) hstepped

private theorem X_fpApprox_le_tenTower_nine : X_fpApprox ≤ tenTower 9 := by
  have htrunc : X_truncation ≤ tenTower 3 := by
    unfold X_truncation
    exact exp_one_le_tenTower_three
  have htruncReindex : X_truncReindex ≤ tenTower 3 := by
    unfold X_truncReindex
    exact max_le htrunc (tenTower_one_le 3)
  have haffine : X_affineReindex ≤ tenTower 9 := by
    unfold X_affineReindex
    exact max_le (max_le X_stepbackReduce_le_tenTower_nine
      (htruncReindex.trans (tenTower_mono (by omega))))
      (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))
  unfold X_fpApprox
  exact max_le (max_le X_windowReduce_le_tenTower_nine haffine)
    (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))

private theorem exp_one_thousand_twenty_four_le_tenTower_three :
    Real.exp 1024 ≤ tenTower 3 :=
  exp_le_tenTower_three_of_le_ten_pow_thirty (by norm_num)

private theorem exp_two_hundred_thousand_le_tenTower_three :
    Real.exp 200000 ≤ tenTower 3 :=
  exp_le_tenTower_three_of_le_ten_pow_thirty (by norm_num)

private theorem X_cnBound_le_tenTower_three : X_cnBound ≤ tenTower 3 := by
  unfold X_cnBound
  exact exp_one_thousand_twenty_four_le_tenTower_three

private theorem X_NstarWindow_le_tenTower_three : X_NstarWindow ≤ tenTower 3 := by
  unfold X_NstarWindow
  exact max_le (exp_le_tenTower_three_of_le_ten_pow_thirty (by norm_num))
    X_twoMZero_le_tenTower_three

private theorem X_perNHarm_le_tenTower_four : X_perNHarm ≤ tenTower 4 := by
  have hlast :
      Real.exp (2 + 3 * ((3 : ℝ) / (1 / 10000)) + 2 * 3 / (alpha - 1)) ≤ tenTower 3 :=
    exp_le_tenTower_three_of_le_ten_pow_thirty (by norm_num [alpha])
  unfold X_perNHarm
  exact max_le
    (max_le X_windowBase_le_tenTower_four two_rpow_two_thousand_le_tenTower_four)
    (max_le
      (max_le (max_le
        (X_cnBound_le_tenTower_three.trans (tenTower_mono (by omega)))
        (exp_one_thousand_twenty_four_le_tenTower_three.trans (tenTower_mono (by omega))))
        (X_NstarWindow_le_tenTower_three.trans (tenTower_mono (by omega))))
      (max_le
        (exp_one_thousand_twenty_four_le_tenTower_three.trans (tenTower_mono (by omega)))
        (hlast.trans (tenTower_mono (by omega)))))

private theorem X_goodWhp_le_tenTower_nine : X_goodWhp ≤ tenTower 9 := by
  have hGweight : X_Gweight ≤ tenTower 3 := by
    unfold X_Gweight
    exact exp_twenty_le_tenTower_three
  unfold X_goodWhp
  exact max_le X_logRpowExp_Gweight_le_tenTower_nine
    (max_le (exp_twenty_le_tenTower_three.trans (tenTower_mono (by omega)))
      (hGweight.trans (tenTower_mono (by omega))))

private theorem X_harmonicZ_le_tenTower_nine : X_harmonicZ ≤ tenTower 9 := by
  have hsyrac : X_syracZsub ≤ tenTower 9 := by
    unfold X_syracZsub
    exact X_goodWhp_le_tenTower_nine
  have hfine : X_harmZfine ≤ tenTower 9 := by
    unfold X_harmZfine
    exact max_le (max_le
      (X_cnBound_le_tenTower_three.trans (tenTower_mono (by omega))) hsyrac)
      (exp_one_thousand_twenty_four_le_tenTower_three.trans (tenTower_mono (by omega)))
  have hmZeroLin : X_mZeroLin ≤ tenTower 3 := by
    unfold X_mZeroLin
    exact exp_two_hundred_thousand_le_tenTower_three
  have hbridge : X_mainZbridge ≤ tenTower 3 := by
    unfold X_mainZbridge
    exact max_le exp_two_hundred_thousand_le_tenTower_three
      (max_le X_twoMZero_le_tenTower_three
        (max_le hmZeroLin X_cnBound_le_tenTower_three))
  unfold X_harmonicZ
  exact max_le (max_le hfine (hbridge.trans (tenTower_mono (by omega))))
    (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))

private theorem X_IyCard_le_tenTower_three : X_IyCard ≤ tenTower 3 := by
  unfold X_IyCard
  exact exp_le_tenTower_three_of_le_ten_pow_thirty (by norm_num)

private theorem X_stab_le_tenTower_nine : X_stab ≤ tenTower 9 := by
  have hmain : X_mainZ ≤ tenTower 9 := by
    unfold X_mainZ
    exact max_le
      (max_le (X_perNHarm_le_tenTower_four.trans (tenTower_mono (by omega)))
        X_harmonicZ_le_tenTower_nine)
      (max_le X_fpApprox_le_tenTower_nine
        (max_le (X_IyCard_le_tenTower_three.trans (tenTower_mono (by omega)))
          ((exp_le_tenTower_three_of_le_ten_pow_thirty (by norm_num)).trans
            (tenTower_mono (by omega)))))
  have hperN : X_perNTermEval ≤ tenTower 9 := by
    unfold X_perNTermEval
    exact max_le (max_le
      (X_perNHarm_le_tenTower_four.trans (tenTower_mono (by omega)))
      X_harmonicZ_le_tenTower_nine)
      (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))
  have hratio : X_IyRatio ≤ tenTower 3 := by
    unfold X_IyRatio
    exact max_le X_IyCard_le_tenTower_three
      (exp_le_tenTower_three_of_le_ten_pow_thirty (by norm_num))
  have happ : X_approxToZ ≤ tenTower 9 := by
    unfold X_approxToZ
    exact max_le (max_le (max_le
      (hratio.trans (tenTower_mono (by omega))) hmain) hperN)
      (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))
  have hwindow : X_windowStable ≤ tenTower 9 := by
    unfold X_windowStable
    exact happ
  unfold X_stab
  exact max_le (max_le (max_le
    (X_firstPassNonescape_le_tenTower_four.trans (tenTower_mono (by omega)))
    X_fpApprox_le_tenTower_nine) hwindow)
    (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))

private theorem X_spine_le_tenTower_eleven : X_spine ≤ tenTower 11 := by
  have hstep : X_descStep ≤ tenTower 9 := by
    unfold X_descStep
    exact max_le X_stab_le_tenTower_nine
      (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))
  have hbase : X_descBase ≤ tenTower 4 := by
    unfold X_descBase
    exact max_le X_firstPassNonescape_le_tenTower_four
      ((show (0 : ℝ) ≤ 1 by norm_num).trans (tenTower_one_le 4))
  have hladder : X_descLadder ≤ tenTower 9 := by
    unfold X_descLadder
    exact max_le (max_le (hbase.trans (tenTower_mono (by omega))) hstep)
      (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))
  have hdesc : X_descWhp ≤ tenTower 11 := by
    have hinner : max X_descLadder (Real.exp 1) ≤ tenTower 9 :=
      max_le hladder (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))
    have hpow : (max X_descLadder (Real.exp 1)) ^ (alpha : ℝ) ≤ tenTower 11 :=
      rpow_le_tenTower_add_two 9 (by positivity) (by norm_num [alpha]) hinner
        ((show alpha ≤ 10 by norm_num [alpha]).trans (ten_le_tenTower 9))
    unfold X_descWhp
    exact max_le hpow (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))
  have hwindow : X_windowBad ≤ tenTower 11 := by
    have hinner : max X_windowBase 1 ≤ tenTower 4 :=
      max_le X_windowBase_le_tenTower_four (tenTower_one_le 4)
    have hpow : (max X_windowBase 1) ^ (alpha : ℝ) ≤ tenTower 6 :=
      rpow_le_tenTower_add_two 4 (by positivity) (by norm_num [alpha]) hinner
        ((show alpha ≤ 10 by norm_num [alpha]).trans (ten_le_tenTower 4))
    unfold X_windowBad
    exact max_le (max_le hdesc (hpow.trans (tenTower_mono (by omega))))
      (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))
  unfold X_spine X_syrSum
  exact max_le hwindow
    (exp_one_le_tenTower_three.trans (tenTower_mono (by omega)))

/-- Headline ceiling: `tenTower 62` is a right-associated tower containing exactly 63
copies of `10`, i.e. `10↑↑63`. -/
theorem C_tao_assembled_le_tenTower_sixty_two :
    C_tao_assembled ≤ tenTower 62 := by
  have hfirst : C_windowBad * alpha / (alpha - 1) ≤ tenTower 61 := by
    have heq : C_windowBad * alpha / (alpha - 1) = 1001 * C_windowBad := by
      norm_num [alpha]
      ring
    rw [heq]
    exact tenTower_mul_le_succ 60 (by norm_num) C_windowBad_pos.le
      ((show (1001 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega))))
      C_windowBad_le_tenTower_sixty
  have hX1 : (1 : ℝ) ≤ X_spine := by
    unfold X_spine X_syrSum
    exact le_trans (Real.one_le_exp (by norm_num)) (le_max_right _ _)
  have hlog0 : 0 ≤ Real.log X_spine := Real.log_nonneg hX1
  have hlog : Real.log X_spine ≤ tenTower 11 :=
    log_le_tenTower 11 (by positivity) X_spine_le_tenTower_eleven
  have hc1 : c_ladder ≤ 1 := by
    have hcl : c_ladder = c_valSumTail := by
      unfold c_ladder
      rw [c_stab_eq_valSumTail, min_self]
    rw [hcl]
    exact c_valSumTail_le_one_fifth.trans (by norm_num)
  have hlogPow : (Real.log X_spine) ^ c_ladder ≤ tenTower 13 :=
    rpow_le_tenTower_add_two 11 hlog0 c_ladder_pos.le hlog
      (hc1.trans (tenTower_one_le 11))
  have hsecond : 4 * max 1 ((Real.log X_spine) ^ c_ladder) ≤ tenTower 14 :=
    tenTower_mul_le_succ 13 (by norm_num) (by positivity)
      ((show (4 : ℝ) ≤ 10 by norm_num).trans (ten_le_tenTower 13))
      (max_le (tenTower_one_le 13) hlogPow)
  have hsyr : C_syrSum X_spine ≤ tenTower 61 := by
    unfold C_syrSum
    exact max_le hfirst (hsecond.trans (tenTower_mono (by omega)))
  have hspine : C_spine X_spine ≤ tenTower 62 := by
    unfold C_spine
    exact tenTower_mul_le_succ 61 (by norm_num) (C_syrSum_pos X_spine).le
      ((show (16 : ℝ) ≤ (10 : ℝ) ^ (30 : ℕ) by norm_num).trans
        (ten_pow_thirty_le_tenTower_two.trans (tenTower_mono (by omega)))) hsyr
  have hcTao0 : 0 < cTao := by
    unfold cTao
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hcTao1 : cTao ≤ 1 := by
    unfold cTao
    have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hden : (1 : ℝ) ≤ 640000000 * Real.log 2 := by nlinarith
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  have hlogTwo : Real.log 2 ≤ tenTower 2 :=
    ((Real.log_le_self (by norm_num)).trans (by norm_num : (2 : ℝ) ≤ 10)).trans
      (ten_le_tenTower 2)
  have hsmall : (Real.log 2) ^ cTao ≤ tenTower 4 :=
    rpow_le_tenTower_add_two 2 (Real.log_pos (by norm_num)).le hcTao0.le hlogTwo
      (hcTao1.trans (tenTower_one_le 2))
  unfold C_tao_assembled
  exact max_le hspine (hsmall.trans (tenTower_mono (by omega)))

/-- The two reportable parameters, in one kernel-checked statement: one may take
`c = 1/(640000000 log 2)` and `C = 10↑↑63`, a right-associated tower of exactly 63 tens. -/
theorem tao_collatz_assembled_readable_parameters :
    cTao = 1 / (640000000 * Real.log 2) ∧
      C_tao_assembled ≤ tenTower 62 :=
  ⟨rfl, C_tao_assembled_le_tenTower_sixty_two⟩

/-- A directly citable version of Theorem 3.1 with `C` equal to a tower of 63 tens. -/
theorem tao_collatz_quantitative_tower_of_sixty_three_tens :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - tenTower 62 / (Real.log N₀) ^ cTao
        ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
  intro N₀ x hN₀ hx
  have hbase := tao_collatz_quantitative_assembled N₀ x hN₀ hx
  have hN₀real : (1 : ℝ) < N₀ := by exact_mod_cast (show 1 < N₀ by omega)
  have hden : 0 < (Real.log N₀) ^ cTao :=
    Real.rpow_pos_of_pos (Real.log_pos hN₀real) _
  have hfrac : C_tao_assembled / (Real.log N₀) ^ cTao ≤
      tenTower 62 / (Real.log N₀) ^ cTao :=
    (div_le_div_iff_of_pos_right hden).2
      C_tao_assembled_le_tenTower_sixty_two
  linarith

end TaoCollatz
