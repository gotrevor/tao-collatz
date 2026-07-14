import TaoCollatz.Sec6.MixingCore

/-! The main-density branch of the §6 conditioning proof. -/

open scoped BigOperators

namespace TaoCollatz

/-- The tight valuation window used by `mainHigh` is nonempty-compatible for all sufficiently
large `n`: its quadratic-in-`C_A` logarithmic loss is eventually dominated by the linear main
term. This discharges the `hwin` hypothesis of `lRange_hbudget`; no numerical cutoff is exposed. -/
theorem eventually_ca_window (A : ℝ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ((caConst A) ^ 2 - 2 * caConst A) * Real.log (n : ℝ)
        ≤ (n : ℝ) * Real.log 3 / Real.log 2 := by
  let D : ℝ := (caConst A) ^ 2 - 2 * caConst A
  have hC : 30 ≤ caConst A := caConst_ge_thirty A
  have hD : 0 < D := by
    dsimp [D]
    nlinarith
  obtain ⟨n₀, hn₀⟩ := log_le_eps_mul_of_large D⁻¹ (inv_pos.mpr hD)
  refine ⟨n₀, fun n hn => ?_⟩
  have hlog := hn₀ n hn
  have hDn : D * Real.log (n : ℝ) ≤ (n : ℝ) := by
    calc
      D * Real.log (n : ℝ) ≤ D * (D⁻¹ * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog hD.le
      _ = (n : ℝ) := by rw [← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hratio : (n : ℝ) ≤ (n : ℝ) * Real.log 3 / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlog23 (Nat.cast_nonneg n)
  change D * Real.log (n : ℝ) ≤ _
  exact hDn.trans hratio

/-- Cancellation of the exponential factors in Tao's `(6.10)`: on the tight valuation window,
`sqrt (3^n * 2⁻ˡ)` costs only a polynomial in `n`.  The exponent here is deliberately loose
(`C² log 2` rather than half that value); the characteristic-function estimate is available at
arbitrarily large polynomial exponent, so this avoids an irrelevant square-root constant chase. -/
theorem lRange_sqrt_kernel_le (C : ℝ) (n l : ℕ) (hn : 1 ≤ n)
    (hl : l ∈ lRange C n) :
    Real.sqrt ((3 ^ n : ℝ) * (2 : ℝ)⁻¹ ^ l)
      ≤ (n : ℝ) ^ (C ^ 2 * Real.log 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlower : (n : ℝ) * Real.log 3 / Real.log 2 - C ^ 2 * Real.log (n : ℝ) ≤ (l : ℝ) := by
    rw [lRange, Finset.mem_Icc] at hl
    exact (Nat.le_ceil _).trans (by exact_mod_cast hl.1)
  have hexp_le : (n : ℝ) * Real.log 3 - (l : ℝ) * Real.log 2
      ≤ C ^ 2 * Real.log 2 * Real.log (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hlower hlog2.le
    field_simp at hmul
    nlinarith
  have hkernel : (3 ^ n : ℝ) * (2 : ℝ)⁻¹ ^ l
      ≤ (n : ℝ) ^ (C ^ 2 * Real.log 2) := by
    calc
      (3 ^ n : ℝ) * (2 : ℝ)⁻¹ ^ l =
          Real.exp ((n : ℝ) * Real.log 3 - (l : ℝ) * Real.log 2) := by
        rw [show (3 ^ n : ℝ) = Real.exp ((n : ℝ) * Real.log 3) by
              rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)],
            show (2 : ℝ)⁻¹ ^ l = Real.exp (-(l : ℝ) * Real.log 2) by
              rw [show (2 : ℝ)⁻¹ = Real.exp (-Real.log 2) by
                    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)],
                  ← Real.exp_nat_mul]
              congr 1
              ring
            ]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (C ^ 2 * Real.log 2 * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hexp_le
      _ = (n : ℝ) ^ (C ^ 2 * Real.log 2) := by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        ring
  refine (Real.sqrt_le_sqrt hkernel).trans ?_
  have hrpow1 : 1 ≤ (n : ℝ) ^ (C ^ 2 * Real.log 2) := by
    rw [← Real.rpow_zero (n : ℝ)]
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hn
    · positivity
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) (C ^ 2 * Real.log 2)]

/-- The tight valuation window contains only linearly many integers.  This intentionally uses the
coarse bound `2n+1`; together with `lRange_sqrt_kernel_le` it turns the entire `l`-sum into a
polynomial loss, which will be absorbed by asking `charFn_decay` for a larger exponent. -/
theorem lRange_card_le (A : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hwin : ((caConst A) ^ 2 - 2 * caConst A) * Real.log (n : ℝ)
      ≤ (n : ℝ) * Real.log 3 / Real.log 2) :
    (lRange (caConst A) n).card ≤ 2 * n + 1 := by
  let C := caConst A
  let x : ℝ := (n : ℝ) * Real.log 3 / Real.log 2
      - (C ^ 2 - 2 * C) * Real.log (n : ℝ)
  have hC : 30 ≤ C := caConst_ge_thirty A
  have hD : 0 ≤ C ^ 2 - 2 * C := by nlinarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hx0 : 0 ≤ x := by dsimp [x, C]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3lt : Real.log 3 < 2 * Real.log 2 := by
    rw [← show Real.log 4 = 2 * Real.log 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hx2n : x ≤ (2 * n : ℕ) := by
    have hratio : (n : ℝ) * Real.log 3 / Real.log 2 < 2 * (n : ℝ) := by
      rw [div_lt_iff₀ hlog2]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      nlinarith [mul_lt_mul_of_pos_left hlog3lt hnpos]
    dsimp [x]
    have hsub : 0 ≤ (C ^ 2 - 2 * C) * Real.log (n : ℝ) := mul_nonneg hD hlogn
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact (sub_le_self _ hsub).trans (le_of_lt hratio)
  have hfloor : ⌊x⌋₊ ≤ 2 * n := by
    exact_mod_cast (le_trans (Nat.floor_le hx0) hx2n)
  rw [lRange, Nat.card_Icc]
  change ⌊x⌋₊ + 1 - _ ≤ 2 * n + 1
  omega

/-- The complete tight-window entropy sum is polynomially bounded. -/
theorem sum_lRange_sqrt_kernel_le (A : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hwin : ((caConst A) ^ 2 - 2 * caConst A) * Real.log (n : ℝ)
      ≤ (n : ℝ) * Real.log 3 / Real.log 2) :
    ∑ l ∈ lRange (caConst A) n, Real.sqrt ((3 ^ n : ℝ) * (2 : ℝ)⁻¹ ^ l)
      ≤ (2 * n + 1 : ℕ) * (n : ℝ) ^ ((caConst A) ^ 2 * Real.log 2) := by
  calc
    ∑ l ∈ lRange (caConst A) n, Real.sqrt ((3 ^ n : ℝ) * (2 : ℝ)⁻¹ ^ l)
        ≤ ∑ _l ∈ lRange (caConst A) n,
            (n : ℝ) ^ ((caConst A) ^ 2 * Real.log 2) :=
      Finset.sum_le_sum (fun l hl => lRange_sqrt_kernel_le (caConst A) n l hn hl)
    _ = ((lRange (caConst A) n).card : ℝ)
          * (n : ℝ) ^ ((caConst A) ^ 2 * Real.log 2) := by simp
    _ ≤ (2 * n + 1 : ℕ) * (n : ℝ) ^ ((caConst A) ^ 2 * Real.log 2) := by
      gcongr
      exact_mod_cast lRange_card_le A n hn hwin

/-- Character-decay exponent requested from Proposition 1.17.  The extra terms explicitly pay for
the tight-window entropy loss, the `l`-count, and the `k`-count. -/
noncomputable def mainDecayExponent (A : ℝ) : ℝ :=
  A + (caConst A) ^ 2 * Real.log 2 + 3

theorem mainDecayExponent_pos (A : ℝ) (hA : 0 < A) : 0 < mainDecayExponent A := by
  unfold mainDecayExponent
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The explicit `A'`-absorption promised in the §6 plan: after one `n`-sized stopping-time sum and
the tight-window entropy sum, decay at `mainDecayExponent A` still leaves `n^{-A}`. -/
theorem main_polynomial_loss_absorbed (A : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * ((2 * n + 1 : ℕ) * (n : ℝ) ^ ((caConst A) ^ 2 * Real.log 2))
        * (n : ℝ) ^ (-mainDecayExponent A)
      ≤ 3 * (n : ℝ) ^ (-A) := by
  let x : ℝ := n
  let E : ℝ := (caConst A) ^ 2 * Real.log 2
  have hx : 0 < x := by dsimp [x]; exact_mod_cast hn
  have hcount : ((2 * n + 1 : ℕ) : ℝ) ≤ 3 * x := by
    dsimp [x]
    norm_num
    exact_mod_cast (by omega : 2 * n + 1 ≤ 3 * n)
  have hnonnegE : 0 ≤ x ^ E := Real.rpow_nonneg hx.le _
  have hnonnegB : 0 ≤ x ^ (-mainDecayExponent A) := Real.rpow_nonneg hx.le _
  calc
    (n : ℝ) * ((2 * n + 1 : ℕ) * (n : ℝ) ^ ((caConst A) ^ 2 * Real.log 2))
          * (n : ℝ) ^ (-mainDecayExponent A)
        ≤ x * (3 * x * x ^ E) * x ^ (-mainDecayExponent A) := by
      dsimp [x, E]
      gcongr
    _ = 3 * x ^ (-A - 1) := by
      rw [show x * (3 * x * x ^ E) * x ^ (-mainDecayExponent A) =
          3 * ((x * x) * x ^ E * x ^ (-mainDecayExponent A)) by ring]
      rw [show x * x = x ^ (2 : ℕ) by ring, ← Real.rpow_two,
        ← Real.rpow_add hx, ← Real.rpow_add hx]
      unfold mainDecayExponent E
      congr 2
      ring
    _ ≤ 3 * x ^ (-A) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le
      · simpa [x] using (show (1 : ℝ) ≤ n by exact_mod_cast hn)
      · linarith

/-- Canonical factorization of a nonzero residue modulo `3^j` into its exact power of three and a
cofactor that remains prime to three after descent to the residual modulus.  This is the arithmetic
core of the remaining `hunif` bookkeeping. -/
theorem zmod_three_factor {j : ℕ} (z : ZMod (3 ^ j)) (hz : z ≠ 0) :
    ∃ j' q : ℕ, ∃ η : ZMod (3 ^ j),
      ∃ hqj : q ≤ j, j' + q = j ∧ 1 ≤ q ∧
      z = (3 : ZMod (3 ^ j)) ^ j' * η ∧
      ¬3 ∣ (ZMod.castHom (pow_dvd_pow 3 hqj) (ZMod (3 ^ q)) η).val := by
  let j' := padicValNat 3 z.val
  let q := j - j'
  let a := Nat.divMaxPow z.val 3
  let η : ZMod (3 ^ j) := (a : ℕ)
  have hzval : z.val ≠ 0 := (ZMod.val_ne_zero z).mpr hz
  have hj'lt : j' < j := by
    by_contra h
    have hjj' : j ≤ j' := Nat.le_of_not_gt h
    have hdvd : 3 ^ j ∣ z.val :=
      (pow_dvd_pow 3 hjj').trans (pow_padicValNat_dvd (p := 3) (n := z.val))
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hzval) hdvd
    exact (not_le_of_gt z.val_lt) hle
  have hjq : j' + q = j := by dsimp [q]; omega
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hqj : q ≤ j := by omega
  have hfactor : z = (3 : ZMod (3 ^ j)) ^ j' * η := by
    rw [← ZMod.natCast_zmod_val z]
    have hnat : 3 ^ j' * a = z.val := Nat.pow_padicValNat_mul_divMaxPow 3 z.val
    calc
      (z.val : ZMod (3 ^ j)) = ((3 ^ j' * a : ℕ) : ZMod (3 ^ j)) :=
        congrArg (fun t : ℕ => (t : ZMod (3 ^ j))) hnat.symm
      _ = (3 : ZMod (3 ^ j)) ^ j' * (a : ZMod (3 ^ j)) := by push_cast; rfl
  refine ⟨j', q, η, hqj, hjq, hq, hfactor, ?_⟩
  intro hbad
  have hbad' : 3 ∣ a % 3 ^ q := by
    simpa [η, a, ZMod.castHom_apply, ZMod.cast_natCast, ZMod.val_natCast] using hbad
  have hmod : 3 ∣ 3 ^ q := by
    exact dvd_pow_self 3 (by omega)
  have ha3 : 3 ∣ a := by
    rw [← Nat.mod_add_div a (3 ^ q)]
    exact dvd_add hbad' (dvd_mul_of_dvd_left hmod _)
  exact (Nat.not_dvd_divMaxPow (by norm_num : 1 < 3) hzval) ha3

/-- A high frequency stays nonzero after projection to any level still above its forbidden
`3^(n-m)` divisibility threshold. -/
theorem highFreq_cast_ne_zero (m n j : ℕ) (hj : n - m ≤ j) (hjn : j ≤ n)
    (ξ : ZMod (3 ^ n)) (hξ : ξ ∈ highFreq m n) :
    ZMod.castHom (pow_dvd_pow 3 hjn) (ZMod (3 ^ j)) ξ ≠ 0 := by
  rw [highFreq, Finset.mem_filter] at hξ
  intro hz
  rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hz
  have hdvdj : 3 ^ j ∣ ξ.val := (ZMod.natCast_eq_zero_iff _ _).mp hz
  exact hξ.2 ((pow_dvd_pow 3 hj).trans hdvdj)

/-- Uniform head decay once the head length `j` exceeds the high-frequency cutoff `n-m` by a
residual margin `q₀`.  The exact `3`-valuation of `ξ` is peeled off; multiplication by `2⁻ˡ` is a
unit and therefore preserves the coprime cofactor. -/
theorem head_uniform_highFreq_of_margin (B : ℝ) (hB : 0 < B) :
    ∃ C > 0, ∀ (j p m l q₀ : ℕ), 1 ≤ q₀ → m ≤ j + p →
      (j + p - m) + q₀ ≤ j → ∀ ξ ∈ highFreq m (j + p),
      ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))‖
        ≤ C * (q₀ : ℝ) ^ (-B) := by
  obtain ⟨C, hC, hdecay⟩ := head_factor_norm_le_charFn B hB
  have htransport {j' q j p l : ℕ} (hjq : j' + q = j) (hq : 1 ≤ q)
      (ξ : ZMod (3 ^ (j + p))) (η : ZMod (3 ^ j))
      (hfreq : (2 : ZMod (3 ^ j))⁻¹ ^ l
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right j p)) (ZMod (3 ^ j)) ξ =
            (3 : ZMod (3 ^ j)) ^ j' * η)
      (hη3 : ¬3 ∣ (ZMod.castHom (pow_dvd_pow 3 (show q ≤ j by omega))
          (ZMod (3 ^ q)) η).val) :
      ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))‖
        ≤ C * (q : ℝ) ^ (-B) := by
    subst j
    exact hdecay j' q p l hq ξ η hfreq hη3
  refine ⟨C, hC, fun j p m l q₀ hq₀ hmn hmargin ξ hξ => ?_⟩
  rw [highFreq, Finset.mem_filter] at hξ
  have hnotdvd : ¬3 ^ (j + p - m) ∣ ξ.val := hξ.2
  have hξval : ξ.val ≠ 0 := by
    intro hz
    apply hnotdvd
    rw [hz]
    exact dvd_zero _
  let j' := padicValNat 3 ξ.val
  generalize hqdef : j - j' = q
  let a := Nat.divMaxPow ξ.val 3
  have hj'lt : j' < j + p - m := by
    by_contra h
    apply hnotdvd
    exact (pow_dvd_pow 3 (Nat.le_of_not_gt h)).trans
      (pow_padicValNat_dvd (p := 3) (n := ξ.val))
  have hj'j : j' ≤ j := by omega
  have hjq : j' + q = j := by omega
  have hq₀q : q₀ ≤ q := by omega
  have hq : 1 ≤ q := hq₀.trans hq₀q
  have hjpos : 0 < j := lt_of_lt_of_le (by omega : 0 < q₀) (le_trans hq₀q (by omega))
  let η : ZMod (3 ^ j) := (2 : ZMod (3 ^ j))⁻¹ ^ l * (a : ZMod (3 ^ j))
  have hcastξ :
      ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right j p)) (ZMod (3 ^ j)) ξ =
        (3 : ZMod (3 ^ j)) ^ j' * (a : ZMod (3 ^ j)) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    have hnat : 3 ^ j' * a = ξ.val := Nat.pow_padicValNat_mul_divMaxPow 3 ξ.val
    calc
      (ξ.val : ZMod (3 ^ j)) = ((3 ^ j' * a : ℕ) : ZMod (3 ^ j)) :=
        congrArg (fun t : ℕ => (t : ZMod (3 ^ j))) hnat.symm
      _ = (3 : ZMod (3 ^ j)) ^ j' * (a : ZMod (3 ^ j)) := by push_cast; rfl
  have hfreq :
      (2 : ZMod (3 ^ j))⁻¹ ^ l
          * ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right j p)) (ZMod (3 ^ j)) ξ =
        (3 : ZMod (3 ^ j)) ^ j' * η := by
    rw [hcastξ]
    dsimp [η]
    ring
  have ha3 : ¬3 ∣ a := Nat.not_dvd_divMaxPow (by norm_num) hξval
  have hu2 : IsUnit (2 : ZMod (3 ^ j)) := by
    rw [show (2 : ZMod (3 ^ j)) = ((2 : ℕ) : ZMod (3 ^ j)) by norm_cast,
      ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (by decide)
  have hua : IsUnit (a : ZMod (3 ^ j)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow (by decide) hjpos).mpr ha3
  have huη : IsUnit η := by
    dsimp [η]
    have hu2inv : IsUnit (2 : ZMod (3 ^ j))⁻¹ :=
      isUnit_of_dvd_one ⟨2, (ZMod.inv_mul_of_unit 2 hu2).symm⟩
    exact (hu2inv.pow l).mul hua
  have hqj : q ≤ j := by omega
  have huηq : IsUnit
      (ZMod.castHom (pow_dvd_pow 3 hqj) (ZMod (3 ^ q)) η) :=
    huη.map (ZMod.castHom (pow_dvd_pow 3 hqj) (ZMod (3 ^ q)))
  have hη3 : ¬3 ∣
      (ZMod.castHom (pow_dvd_pow 3 hqj) (ZMod (3 ^ q)) η).val := by
    let zq : ZMod (3 ^ q) :=
      ZMod.castHom (pow_dvd_pow 3 hqj) (ZMod (3 ^ q)) η
    have hzqunit : IsUnit zq := huηq
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow (p := 3) (d := q) (a := zq.val)
      (by decide) (by omega)).mp
    rw [ZMod.natCast_zmod_val zq]
    exact hzqunit
  have hbound :
      ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
          (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
            * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))‖
        ≤ C * (q : ℝ) ^ (-B) := by
    exact htransport hjq hq ξ η hfreq hη3
  refine hbound.trans ?_
  have hpow : (q : ℝ) ^ (-B) ≤ (q₀ : ℝ) ^ (-B) := by
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast (by omega : 0 < q₀)
    · exact_mod_cast hq₀q
    · linarith
  exact mul_le_mul_of_nonneg_left hpow hC.le

/-- For large `n`, the conditioning window has no support at cuts with `p = k+1 > 0.8n`.
The strict numerical gap is `8/5 - log 3 / log 2 > 0`, equivalently `3^5 < 2^8`.
This is what supplies a linear residual head margin for `head_uniform_highFreq_of_margin`. -/
theorem eventually_condWindowB_empty_p_gt (C : ℝ) (hC : 30 ≤ C) :
    ∃ n₀ : ℕ, ∀ (j p l : ℕ) (T : ℝ), n₀ ≤ j + p → 1 ≤ j + p →
      ((C ^ 2 - 2 * C) * Real.log ((j + p : ℕ) : ℝ)
        ≤ ((j + p : ℕ) : ℝ) * Real.log 3 / Real.log 2) →
      l ∈ lRange C (j + p) → 4 * (j + p) < 5 * p →
      ∀ vt, ¬ condWindowB j p C l T vt := by
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgaplog : 5 * Real.log 3 < 8 * Real.log 2 := by
    rw [← show Real.log ((3 : ℝ) ^ 5) = 5 * Real.log 3 by
      rw [Real.log_pow]; norm_num,
      ← show Real.log ((2 : ℝ) ^ 8) = 8 * Real.log 2 by
      rw [Real.log_pow]; norm_num]
    exact Real.log_lt_log (by positivity) (by norm_num)
  let δ : ℝ := 8 / 5 - Real.log 3 / Real.log 2
  have hδ : 0 < δ := by
    dsimp [δ]
    rw [sub_pos, div_lt_iff₀ hlog2]
    nlinarith
  let r : ℝ := δ / (4 * C)
  have hr : 0 < r := div_pos hδ (by positivity)
  have hδlt : δ < 8 / 5 := by
    dsimp [δ]
    have : 0 < Real.log 3 / Real.log 2 := div_pos (Real.log_pos (by norm_num)) hlog2
    linarith
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [div_le_one (by positivity : 0 < 4 * C)]
    nlinarith
  obtain ⟨n₀, hn₀⟩ := log_le_eps_mul_of_large (r ^ 2) (sq_pos_of_pos hr)
  refine ⟨n₀, fun j p l T hnlarge hn hwin hl hp vt hW => ?_⟩
  let n := j + p
  have hnpos : (0 : ℝ) < n := by dsimp [n]; exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlog : Real.log (n : ℝ) ≤ r ^ 2 * (n : ℝ) := by
    exact hn₀ n (by simpa [n] using hnlarge)
  have hpn : (p : ℝ) ≤ n := by dsimp [n]; norm_cast; omega
  have hsqrt : Real.sqrt ((p : ℝ) * Real.log (n : ℝ)) ≤ r * (n : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hmul : (p : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) * (r ^ 2 * (n : ℝ)) :=
        mul_le_mul hpn hlog hlogn (Nat.cast_nonneg n)
      nlinarith
  have hlogr : Real.log (n : ℝ) ≤ r * (n : ℝ) := by
    have hr2r : r ^ 2 ≤ r := by nlinarith
    exact hlog.trans (mul_le_mul_of_nonneg_right hr2r (Nat.cast_nonneg n))
  have herr : C * (Real.sqrt ((p : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ))
      ≤ δ / 2 * (n : ℝ) := by
    have hsum := add_le_add hsqrt hlogr
    have hmul := mul_le_mul_of_nonneg_left hsum hCpos.le
    dsimp [r] at hmul
    field_simp at hmul ⊢
    nlinarith
  have hD : 0 ≤ C ^ 2 - 2 * C := by nlinarith
  have hx0 : 0 ≤ (n : ℝ) * Real.log 3 / Real.log 2
      - (C ^ 2 - 2 * C) * Real.log (n : ℝ) := by
    simpa [n] using sub_nonneg.mpr hwin
  have hlupper : (l : ℝ) ≤ (n : ℝ) * Real.log 3 / Real.log 2 := by
    rw [lRange, Finset.mem_Icc] at hl
    have hlfloor : (l : ℝ) ≤
        (n : ℝ) * Real.log 3 / Real.log 2
          - (C ^ 2 - 2 * C) * Real.log (n : ℝ) :=
      (Nat.cast_le.mpr hl.2).trans (Nat.floor_le hx0)
    have hloss : 0 ≤ (C ^ 2 - 2 * C) * Real.log (n : ℝ) := mul_nonneg hD hlogn
    linarith
  have hp1 : 1 ≤ p := by omega
  have hwindow : 2 * (p : ℝ)
      - C * (Real.sqrt ((p : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ)) ≤ (l : ℝ) := by
    simpa [condWindow, n] using hW.1 p hp1 le_rfl
  have hpcast : (8 / 5 : ℝ) * (n : ℝ) < 2 * (p : ℝ) := by
    have : (4 : ℝ) * n < 5 * p := by exact_mod_cast hp
    nlinarith
  have hcoeff : Real.log 3 / Real.log 2 + δ / 2 < 8 / 5 := by
    rw [show Real.log 3 / Real.log 2 + δ / 2 = 8 / 5 - δ / 2 by
      dsimp [δ]
      ring]
    linarith
  have hupper2 : 2 * (p : ℝ) ≤
      (Real.log 3 / Real.log 2 + δ / 2) * (n : ℝ) := by
    calc
      2 * (p : ℝ) ≤ (l : ℝ) +
          C * (Real.sqrt ((p : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ)) := by
        linarith
      _ ≤ (n : ℝ) * Real.log 3 / Real.log 2 + δ / 2 * (n : ℝ) :=
        add_le_add hlupper herr
      _ = (Real.log 3 / Real.log 2 + δ / 2) * (n : ℝ) := by ring
  have hcoeffn := mul_lt_mul_of_pos_right hcoeff hnpos
  exact (not_lt_of_ge hupper2) (hcoeffn.trans hpcast)

/-- A windowed conditioned density is zero when its window predicate is empty. -/
theorem condDensW_eq_zero_of_empty (j p l : ℕ) (W : (Fin p → ℕ) → Prop) [DecidablePred W]
    (hW : ∀ vt, ¬ W vt) : condDensW j p l W = 0 := by
  funext Y
  simp [condDensW, hW]

/-- Replacing the residual length `⌊n/20⌋` by `n` costs at most `40^B` once `n ≥ 40`. -/
theorem div_twenty_rpow_neg_le (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 40 ≤ n) :
    ((n / 20 : ℕ) : ℝ) ^ (-B) ≤
      (40 : ℝ) ^ B * (n : ℝ) ^ (-B) := by
  have hq : 0 < n / 20 := by omega
  have hscale : (n : ℝ) / 40 ≤ (n / 20 : ℕ) := by
    have : n ≤ 40 * (n / 20) := by omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 40)).mpr
    exact_mod_cast (by simpa [mul_comm] using this)
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ) / 40)
    hscale (by linarith : -B ≤ 0)
  rw [Real.div_rpow (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 40),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 40), div_inv_eq_mul] at hpow
  simpa [mul_comm] using hpow

/-- **Obligation 1+2 (main term)**: the oscillation of the §6 main density is polynomially small in
the high regime. This is (6.10)+(6.11) [per-conditioning osc `≤ D·√(3ⁿ2⁻ˡ)`, obl-3 DONE] summed over
the `(k,l)` partition via `osc_mainDensity_le` [k-sum cast, DONE] with `D = C_A·q⁻ᴬ` [obl 2, `hunif`
from `head_factor_norm_le_charFn`], then the geometric `l`-sum `∑ √(2⁻ˡ)` + `k`-count + the constant
chase absorbing `n^{O(C_A²)}` into a larger characteristic-function exponent `A′`. -/
theorem osc_mainHigh_bound (A : ℝ) (hA : 0 < A) :
    ∃ C > 0, ∃ n₀ : ℕ, ∀ n m : ℕ, ∀ hmn : m ≤ n, n₀ ≤ n → 9 * n ≤ 10 * m →
      osc m n hmn (mainHigh A n) ≤ C * (m : ℝ) ^ (-A) := by
  let B := mainDecayExponent A
  have hB : 0 < B := mainDecayExponent_pos A hA
  obtain ⟨C, hC, hhead⟩ := head_uniform_highFreq_of_margin B hB
  obtain ⟨nwin, hnwin⟩ := eventually_ca_window A
  obtain ⟨ncut, hncut⟩ := eventually_condWindowB_empty_p_gt (caConst A) (caConst_ge_thirty A)
  let n₀ := max 40 (max nwin ncut)
  refine ⟨3 * C * (40 : ℝ) ^ B, by positivity, n₀,
    fun n m hmn hnlarge hreg => ?_⟩
  have hn40 : 40 ≤ n := le_trans (le_max_left 40 (max nwin ncut)) hnlarge
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnwin' : nwin ≤ n := le_trans (le_max_left nwin ncut)
    (le_trans (le_max_right 40 (max nwin ncut)) hnlarge)
  have hncut' : ncut ≤ n := le_trans (le_max_right nwin ncut)
    (le_trans (le_max_right 40 (max nwin ncut)) hnlarge)
  have hwindow := hnwin n hnwin'
  let q₀ := n / 20
  have hq₀ : 1 ≤ q₀ := by dsimp [q₀]; omega
  let D : ℝ := C * (q₀ : ℝ) ^ (-B)
  have hD : 0 ≤ D := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg q₀) _)
  have hmain : osc m n hmn (mainHigh A n) ≤
      ∑ k ∈ Finset.range n, ∑ l ∈ lRange (caConst A) n,
        D * Real.sqrt ((3 ^ n : ℝ) * (2 : ℝ)⁻¹ ^ l) := by
    unfold mainHigh
    apply osc_mainDensity_le n m hmn (caConst A) (caThr (caConst A) n)
      (fun _ => lRange (caConst A) n)
      (fun _ l => D * Real.sqrt ((3 ^ n : ℝ) * (2 : ℝ)⁻¹ ^ l))
    intro k hk l hl
    have hkn : k < n := Finset.mem_range.mp hk
    let j := n - 1 - k
    let p := k + 1
    by_cases hactive : 5 * p ≤ 4 * n
    · have hmargin : (j + p - m) + q₀ ≤ j := by
        dsimp [j, p, q₀]
        omega
      have hnative : m ≤ j + p := by
        dsimp [j, p]
        simpa [cutEq hkn] using hmn
      have hunif : ∀ ξ ∈ highFreq m (j + p),
          ‖(geomHalf.iid j).cexpect (fun vh => ZMod.stdAddChar
              (-((3 ^ p * ((fnat j vh : ZMod (3 ^ (j + p)))
                * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ pre vh j)
                * (2 : ZMod (3 ^ (j + p)))⁻¹ ^ l) * ξ)))‖ ≤ D := by
        exact hhead j p m l q₀ hq₀ hnative hmargin
      have hbudget : (l : ℝ) * Real.log 2
          + (caConst A * Real.log 2 + 5 / 4 * (caConst A * Real.log 2) ^ 2)
              * Real.log ((j + p : ℕ) : ℝ)
          + Real.log 4 < ((j + p : ℕ) : ℝ) * Real.log 3 := by
        simpa [j, p, cutEq hkn] using lRange_hbudget A n hn2 l hl hwindow
      have hterm := condDensWB_osc_le j p l m (caConst A) (caThr (caConst A) n)
        hnative D hD hunif hbudget
      simpa [j, p, cutEq hkn] using hterm
    · have hpbig : 4 * n < 5 * p := by omega
      have hempty : ∀ vt, ¬ condWindowB j p (caConst A) l (caThr (caConst A) n) vt := by
        apply hncut j p l (caThr (caConst A) n)
        · simpa [j, p, cutEq hkn] using hncut'
        · simpa [j, p, cutEq hkn] using hn1
        · simpa [j, p, cutEq hkn] using hwindow
        · simpa [j, p, cutEq hkn] using hl
        · simpa [j, p, cutEq hkn] using hpbig
      have hzero := condDensW_eq_zero_of_empty j p l
        (condWindowB j p (caConst A) l (caThr (caConst A) n)) hempty
      rw [hzero]
      simp [osc]
      positivity
  calc
    osc m n hmn (mainHigh A n) ≤
        ∑ k ∈ Finset.range n, ∑ l ∈ lRange (caConst A) n,
          D * Real.sqrt ((3 ^ n : ℝ) * (2 : ℝ)⁻¹ ^ l) := hmain
    _ = (n : ℝ) * (D *
          ∑ l ∈ lRange (caConst A) n,
            Real.sqrt ((3 ^ n : ℝ) * (2 : ℝ)⁻¹ ^ l)) := by
      rw [Finset.mul_sum]
      simp [Finset.mul_sum]
    _ ≤ (n : ℝ) * (D *
          ((2 * n + 1 : ℕ) * (n : ℝ) ^ ((caConst A) ^ 2 * Real.log 2))) := by
      gcongr
      exact sum_lRange_sqrt_kernel_le A n hn1 hwindow
    _ ≤ (n : ℝ) *
          ((C * (40 : ℝ) ^ B * (n : ℝ) ^ (-B)) *
            ((2 * n + 1 : ℕ) * (n : ℝ) ^ ((caConst A) ^ 2 * Real.log 2))) := by
      have hqscale := div_twenty_rpow_neg_le B hB n hn40
      have hDbound : D ≤ C * (40 : ℝ) ^ B * (n : ℝ) ^ (-B) := by
        dsimp [D, q₀]
        nlinarith [mul_le_mul_of_nonneg_left hqscale hC.le]
      gcongr
    _ ≤ 3 * C * (40 : ℝ) ^ B * (n : ℝ) ^ (-A) := by
      have habsorb := main_polynomial_loss_absorbed A n hn1
      have hC40 : 0 ≤ C * (40 : ℝ) ^ B := by positivity
      calc
        (n : ℝ) *
            ((C * (40 : ℝ) ^ B * (n : ℝ) ^ (-B)) *
              ((2 * n + 1 : ℕ) * (n : ℝ) ^ ((caConst A) ^ 2 * Real.log 2)))
            = (C * (40 : ℝ) ^ B) *
                ((n : ℝ) * ((2 * n + 1 : ℕ) *
                  (n : ℝ) ^ ((caConst A) ^ 2 * Real.log 2)) * (n : ℝ) ^ (-B)) := by ring
        _ ≤ (C * (40 : ℝ) ^ B) * (3 * (n : ℝ) ^ (-A)) :=
          mul_le_mul_of_nonneg_left (by simpa [B] using habsorb) hC40
        _ = 3 * C * (40 : ℝ) ^ B * (n : ℝ) ^ (-A) := by ring
    _ ≤ 3 * C * (40 : ℝ) ^ B * (m : ℝ) ^ (-A) := by
      have hmpos : (0 : ℝ) < m := by
        have : 1 ≤ m := by omega
        exact_mod_cast this
      have hpow : (n : ℝ) ^ (-A) ≤ (m : ℝ) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos hmpos (by exact_mod_cast hmn) (by linarith)
      gcongr

end TaoCollatz
