import TaoCollatz.Sec7.ManyTriangles

/-!
# §7 black-edge Q-assembly (downstream of the fpDist geometry kernels)

The (7.41)–(7.67) Proposition 7.8 assembly.  Relocated here (out of `BlackEdge.lean`)
so that `fpDist_white_exit` — the (7.50)/(7.51) Case-2 white-exit bound — can be
discharged from its now-proved deep sibling `fpDist_white_exit_deep`
(`ManyTriangles.lean`), which is strictly stronger (same conclusion, no `s ≤ m/log²m`
budget hypothesis, mass sharpened to `51/100 ≤ p₀`).  `ManyTriangles` imports
`BlackEdge`, so this file, downstream of `ManyTriangles`, sees both.

Every statement here is verbatim as it stood in `BlackEdge.lean` (frozen), only the
proof of `fpDist_white_exit` changed (`sorry` → derivation from the deep kernel).
-/

namespace TaoCollatz

open scoped ENNReal

set_option exponentiation.threshold 3000

/-- **The (7.50)/(7.51) white-exit bound** (paper p.48): starting the renewal
walk at a black edge point `(⌊n/2⌋-m, l)` whose phase point `(⌊n/2⌋-m-1, l)`
lies in triangle `t` of the family, with budget `s = l_Δ - l ≤ m/log²m`, the
first-passage endpoint is WHITE and IN-STRIP with probability `≥ p₀` for an
absolute `p₀ > 0` (uniform in `n, ξ, m, l, t`).

Route ((7.50): Lemma 7.7 puts the endpoint at `(j + s/4 + O((1+s)^{1/2}),
l_Δ + O(1))` with probability `≫ 1`; every endpoint exceeds height `l_Δ`
(`fpDist_support_snd_gt`), i.e. lies strictly above the triangle top; the
(7.11) slope bound `-O(1) ≤ (j'-j_Δ)log 9 ≤ s_Δ + O(1)` plus the family
separation put it outside every OTHER triangle, hence white by `cover`;
in-strip follows from `s/4 + O(√(1+s)) ≪ m`.

`_at` sibling (big-C campaign, step 2): the wrapper at the explicit deep
constants `p_whiteExit = 3/4`, `T_whiteExitDeep`; the budget hypothesis is
dropped on the floor exactly as in the `∃`-form's original proof. -/
theorem fpDist_white_exit_at :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamily n ξ, ∀ m : ℕ, T_whiteExitDeep ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      p_whiteExit ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) :=
  fun n ξ hξ F m hm hmn l hl t ht htmem s hs _hbudget =>
    fpDist_white_exit_deep_at n ξ hξ F m hm hmn l hl t ht htmem s hs

/-- **The (7.50)/(7.51) white-exit bound**, original `∃`-form: delegates to the
`_at` sibling at `p₀ = p_whiteExit = 3/4`, `Cthr = T_whiteExitDeep`. -/
theorem fpDist_white_exit :
    ∃ p₀ > (0 : ℝ), ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamily n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      p₀ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) :=
  ⟨p_whiteExit, lt_of_lt_of_le (by norm_num) p_whiteExit_ge, T_whiteExitDeep,
    fpDist_white_exit_at⟩

/-- `edgeWeight A m e ≤ 1` for `A ≥ 0`: each landing weight `max(·,1)^{-A} ≤ 1`
and `hold` is a PMF, so the average is `≤ 1`. -/
theorem edgeWeight_le_one {A : ℝ} (hA : 0 ≤ A) (m : ℕ) (e : ℕ × ℤ) :
    edgeWeight A m e ≤ 1 := by
  have hterm : ∀ d : ℕ × ℤ,
      (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ (hold d).toReal := by
    intro d
    have h1 : ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast Nat.le_max_right (m - e.1 - d.1) 1) (by linarith)
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg h1
  have hsummLHS : Summable (fun d : ℕ × ℤ =>
      (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      hterm hold_summable_toReal
  calc edgeWeight A m e
      = ∑' d : ℕ × ℤ, (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) := rfl
    _ ≤ ∑' d : ℕ × ℤ, (hold d).toReal := hsummLHS.tsum_le_tsum hterm hold_summable_toReal
    _ = 1 := hold_tsum_toReal

/-- `(m)^{-A} ≤ edgeWeight A m e` for `A ≥ 0`, `1 ≤ m`: each landing weight
`max(m − e₁ − d₁, 1)^{−A} ≥ m^{−A}` since `max(…) ≤ m` and `x ↦ x^{−A}` is
antitone; average against the PMF `hold` preserves it. -/
theorem rpow_neg_le_edgeWeight {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 1 ≤ m) (e : ℕ × ℤ) :
    (m : ℝ) ^ (-A) ≤ edgeWeight A m e := by
  have hterm : ∀ d : ℕ × ℤ,
      (hold d).toReal * (m : ℝ) ^ (-A)
        ≤ (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A) := by
    intro d
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    have hmax_le : ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
      have : (max (m - e.1 - d.1) 1 : ℕ) ≤ m := by omega
      exact_mod_cast this
    have hmax_pos : (0 : ℝ) < ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) := by
      have : 0 < (max (m - e.1 - d.1) 1 : ℕ) := by omega
      exact_mod_cast this
    exact Real.rpow_le_rpow_of_nonpos hmax_pos hmax_le (by linarith)
  have hsummL : Summable (fun d : ℕ × ℤ => (hold d).toReal * (m : ℝ) ^ (-A)) :=
    hold_summable_toReal.mul_right _
  have hsummR : Summable (fun d : ℕ × ℤ =>
      (hold d).toReal * ((max (m - e.1 - d.1) 1 : ℕ) : ℝ) ^ (-A)) :=
    Summable.of_nonneg_of_le
      (fun d => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (fun d => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast Nat.le_max_right (m - e.1 - d.1) 1) (by linarith)))
      hold_summable_toReal
  calc (m : ℝ) ^ (-A)
      = ∑' d : ℕ × ℤ, (hold d).toReal * (m : ℝ) ^ (-A) := by
        rw [tsum_mul_right, hold_tsum_toReal, one_mul]
    _ ≤ edgeWeight A m e := hsummL.tsum_le_tsum hterm hsummR

/-- **The Case-2 weight-degradation budget** `δ = c·p₀/2` (big-C campaign, step 2):
the (7.48) slack at the explicit white-exit mass `p₀ = p_whiteExit` and the
(7.47) gain `c = 1 - e^{-ε³}` at `ε = epsBW`. -/
noncomputable def delta_case2 : ℝ :=
  (1 - Real.exp (-(epsBW : ℝ) ^ 3)) * p_whiteExit / 2

/-- **`Q_black_edge_case2` threshold**, symbolic (big-C campaign, step 2):
`max (max Cw Ce) 2` with `Cw` the white-exit threshold and `Ce` the
weight-degradation threshold at `δ = delta_case2`. -/
noncomputable def Cthr_case2 (A : ℝ) : ℕ :=
  max (max T_whiteExitDeep (T_edgeWeight A delta_case2)) 2

/-- **Case 2 of Proposition 7.8** ((7.46)–(7.51) assembly, paper pp.46–48):
black edge start whose triangle-top budget satisfies `s ≤ m/log²m`. Route:
`Q_le_fpDist_expect` ((7.45) entry) + `Q_fp_endpoint_le` per endpoint, then
the (7.47) split `E[(1-(1-e^{-ε³})·1_W)·w] ≤ E[w] - (1-e^{-ε³})·m^{-A}·P(W)`
(using `w ≥ m^{-A}` pointwise), bounded via `fpDist_edgeWeight_le` (δ :=
`(1-e^{-ε³})·p₀/2`) and `fpDist_white_exit`:
`Q ≤ ((1+δ) - (1-e^{-ε³})·p₀)·m^{-A}·Q_{m-1} ≤ m^{-A}·Q_{m-1}`.

PROVED (node X8 assembly); `_at` sibling (big-C campaign, step 2): the two
kernel `obtain`s are replaced by the explicit `_at` kernels
(`fpDist_white_exit_at`, `fpDist_edgeWeight_le_at` at `δ = delta_case2`) and
the constant names `p₀/Cw/Ce` re-bound via `set`, body verbatim. -/
theorem Q_black_edge_case2_at (A : ℝ) (hA : 0 < A) :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr_case2 A ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  classical
  -- fixed constants: `ε = epsBW ≥ 0`, the white-exit gain `c = 1 - e^{-ε³} ∈ (0,1)`
  have hε0 : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  have hεpos : (0 : ℝ) < (epsBW : ℝ) := by
    have h0 : (0 : ℚ) < epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  have hc_pos : 0 < 1 - Real.exp (-(epsBW : ℝ) ^ 3) := by
    rw [sub_pos]; exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (pow_pos hεpos 3))
  have hc_le : 1 - Real.exp (-(epsBW : ℝ) ^ 3) ≤ 1 := by
    have := Real.exp_pos (-(epsBW : ℝ) ^ 3); linarith
  -- the white-exit mass `p₀ > 0` and the (7.48) weight-degradation with `δ = c·p₀/2`,
  -- both at the EXPLICIT constants (re-bound to the body's names via `set`)
  have hp₀pos : (0 : ℝ) < p_whiteExit := lt_of_lt_of_le (by norm_num) p_whiteExit_ge
  have hWhite := fpDist_white_exit_at
  have hEdge := fpDist_edgeWeight_le_at A hA
    ((1 - Real.exp (-(epsBW : ℝ) ^ 3)) * p_whiteExit / 2)
    (div_pos (mul_pos hc_pos hp₀pos) (by norm_num))
  unfold Cthr_case2 delta_case2
  set p₀ : ℝ := p_whiteExit with hp₀def
  set Cw : ℕ := T_whiteExitDeep with hCwdef
  set Ce : ℕ := T_edgeWeight A ((1 - Real.exp (-(epsBW : ℝ) ^ 3)) * p₀ / 2) with hCedef
  intro n ξ hξ F m hm hmn l hl t ht htmem s hs hbudget
  have hmCw : Cw ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmCe : Ce ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
  have hm1 : 1 ≤ m := by omega
  -- specialize the two kernels + the per-endpoint step (all with literal ε)
  have hwhite := hWhite n ξ hξ F m hmCw hmn l hl t ht htmem s hs hbudget
  have hedge := hEdge m hmCe s hbudget
  have hendpt : ∀ e : ℕ × ℤ,
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m + e.1) (l + e.2)
        ≤ (1 - (1 - Real.exp (-(epsBW : ℝ) ^ 3))
              * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2))
          * (edgeWeight A m e * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :=
    fun e => Q_fp_endpoint_le n ξ (epsBW : ℝ) A hA.le hε0 m hm1 hmn l e
  -- (7.45) entry, converted ℝ≥0∞ → ℝ
  have hstart_enn := Q_le_fpDist_expect (n / 2) (whiteSet n ξ) (epsBW : ℝ) hε0 s (n / 2 - m) l
  have hRne : (∑' e : ℕ × ℤ, fpDist s e
        * ENNReal.ofReal (Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m + e.1) (l + e.2)))
          ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.tsum_mul_ofReal_le_one (fpDist s) _ (fun e => Q_le_one _ _ _ hε0 _ _))
  have hRtoReal : (∑' e : ℕ × ℤ, fpDist s e
        * ENNReal.ofReal (Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m + e.1) (l + e.2))).toReal
      = ∑' e : ℕ × ℤ, (fpDist s e).toReal
          * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m + e.1) (l + e.2) :=
    PMF.toReal_tsum_mul_ofReal (fpDist s) _ (fun e => Q_nonneg _ _ _ _ _)
  have hstep1 : Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
      ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
          * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m + e.1) (l + e.2) := by
    have h := ENNReal.toReal_mono hRne hstart_enn
    rwa [ENNReal.toReal_ofReal (Q_nonneg _ _ _ _ _), hRtoReal] at h
  -- tidy scalar names (fold hedge, hendpt, goal; also hc_pos/hc_le)
  set c : ℝ := 1 - Real.exp (-(epsBW : ℝ) ^ 3) with hc
  set QM : ℝ := Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) with hQMdef
  set mA : ℝ := (m : ℝ) ^ (-A) with hmAdef
  -- basic sign/bound facts
  have hQM0 : 0 ≤ QM := Qm_nonneg _ _ _ _ _ _
  have hmA0 : 0 ≤ mA := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmA_le1 : mA ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1) (by linarith)
  have hf_nonneg : ∀ e : ℕ × ℤ, 0 ≤ (fpDist s e).toReal := fun _ => ENNReal.toReal_nonneg
  have hf_summable : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal) :=
    ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
  have hind0 : ∀ e : ℕ × ℤ,
      0 ≤ Set.indicator (whiteStrip n ξ) (1 : ℕ × ℤ → ℝ) (n / 2 - m + e.1, l + e.2) :=
    fun e => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hind1 : ∀ e : ℕ × ℤ,
      Set.indicator (whiteStrip n ξ) (1 : ℕ × ℤ → ℝ) (n / 2 - m + e.1, l + e.2) ≤ 1 := by
    intro e
    by_cases h : (n / 2 - m + e.1, l + e.2) ∈ whiteStrip n ξ
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hew_ge : ∀ e : ℕ × ℤ, mA ≤ edgeWeight A m e := fun e => rpow_neg_le_edgeWeight hA.le hm1 e
  -- a uniform summability helper for `fpDist · (bounded observable)`
  have hbound : ∀ g : ℕ × ℤ → ℝ, (∀ e, 0 ≤ g e) → (∀ e, g e ≤ 1) →
      Summable (fun e : ℕ × ℤ => (fpDist s e).toReal * g e) := by
    intro g hg0 hg1
    exact Summable.of_nonneg_of_le (fun e => mul_nonneg (hf_nonneg e) (hg0 e))
      (fun e => mul_le_of_le_one_right (hf_nonneg e) (hg1 e)) hf_summable
  have hsum_ew : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal * edgeWeight A m e) :=
    hbound _ (fun e => edgeWeight_nonneg A m e) (fun e => edgeWeight_le_one hA.le m e)
  have hsum_Qe : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal
      * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m + e.1) (l + e.2)) :=
    hbound _ (fun e => Q_nonneg _ _ _ _ _) (fun e => Q_le_one _ _ _ hε0 _ _)
  have hsum_indew : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal
      * (Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) * edgeWeight A m e)) :=
    hbound _ (fun e => mul_nonneg (hind0 e) (edgeWeight_nonneg A m e))
      (fun e => mul_le_one₀ (hind1 e) (edgeWeight_nonneg A m e) (edgeWeight_le_one hA.le m e))
  have hsum_indmA : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal
      * (Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) * mA)) :=
    hbound _ (fun e => mul_nonneg (hind0 e) hmA0)
      (fun e => mul_le_one₀ (hind1 e) hmA0 hmA_le1)
  have hsum_main : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal
      * ((1 - c * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2))
          * edgeWeight A m e)) :=
    (hsum_ew.sub (hsum_indew.mul_left c)).congr (fun e => by ring)
  -- the mixed tail is `≥ p₀·mA` (edgeWeight ≥ m^{-A}, then white-exit)
  have hindew_ge : p₀ * mA ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
      * (Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) * edgeWeight A m e) := by
    have hge : ∀ e : ℕ × ℤ,
        (fpDist s e).toReal
            * (Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) * mA)
          ≤ (fpDist s e).toReal
            * (Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) * edgeWeight A m e) :=
      fun e => mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hew_ge e) (hind0 e)) (hf_nonneg e)
    calc p₀ * mA
        ≤ (∑' e : ℕ × ℤ, (fpDist s e).toReal
            * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2)) * mA :=
          mul_le_mul_of_nonneg_right hwhite hmA0
      _ = ∑' e : ℕ × ℤ, (fpDist s e).toReal
            * (Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) * mA) := by
          rw [← tsum_mul_right]; exact tsum_congr (fun e => by ring)
      _ ≤ _ := hsum_indmA.tsum_le_tsum hge hsum_indew
  -- the main functional `∑ fpDist·(1 - c·1_W)·edgeWeight ≤ mA`
  have hSmain : ∑' e : ℕ × ℤ, (fpDist s e).toReal
      * ((1 - c * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2))
          * edgeWeight A m e) ≤ mA := by
    have hcong : ∀ e : ℕ × ℤ,
        (fpDist s e).toReal
            * ((1 - c * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2))
                * edgeWeight A m e)
          = (fpDist s e).toReal * edgeWeight A m e
            - c * ((fpDist s e).toReal
                * (Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2)
                    * edgeWeight A m e)) := fun e => by ring
    rw [tsum_congr hcong, Summable.tsum_sub hsum_ew (hsum_indew.mul_left c), tsum_mul_left]
    nlinarith [hedge, mul_le_mul_of_nonneg_left hindew_ge hc_pos.le, hmA0,
      mul_nonneg (mul_nonneg hc_pos.le hp₀pos.le) hmA0]
  -- assemble: Q ≤ ∑ fpDist·Q_endpoint ≤ QM·(main) ≤ QM·mA = mA·QM
  have hpt : ∀ e : ℕ × ℤ,
      (fpDist s e).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m + e.1) (l + e.2)
        ≤ QM * ((fpDist s e).toReal
            * ((1 - c * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2))
                * edgeWeight A m e)) := by
    intro e
    calc (fpDist s e).toReal * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m + e.1) (l + e.2)
        ≤ (fpDist s e).toReal
            * ((1 - c * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2))
                * (edgeWeight A m e * QM)) :=
          mul_le_mul_of_nonneg_left (hendpt e) (hf_nonneg e)
      _ = QM * ((fpDist s e).toReal
            * ((1 - c * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2))
                * edgeWeight A m e)) := by ring
  calc Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
      ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
          * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m + e.1) (l + e.2) := hstep1
    _ ≤ ∑' e : ℕ × ℤ, QM * ((fpDist s e).toReal
          * ((1 - c * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2))
              * edgeWeight A m e)) := hsum_Qe.tsum_le_tsum hpt (hsum_main.mul_left QM)
    _ = QM * ∑' e : ℕ × ℤ, (fpDist s e).toReal
          * ((1 - c * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2))
              * edgeWeight A m e) := tsum_mul_left
    _ ≤ QM * mA := mul_le_mul_of_nonneg_left hSmain hQM0
    _ = mA * QM := mul_comm _ _

/-- **Case 2 of Proposition 7.8**, original `∃`-form: delegates to the `_at`
sibling at `Cthr_case2 A = max (max T_whiteExitDeep (T_edgeWeight A delta_case2)) 2`. -/
theorem Q_black_edge_case2 (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) :=
  ⟨Cthr_case2 A, Q_black_edge_case2_at A hA⟩

/-- **The (7.41) edge bound for BLACK starts** (Cases 2–3 of Proposition 7.8,
paper (7.44)–(7.67), pp.46–49): the case split. The black phase point
`(⌊n/2⌋-m-1, l)` lies in a triangle of the family (`cover`); its budget
`s := l_Δ - l` is `≤ (log 9/log 2)·(m+1)` by (7.52); Case 2 handles
`s ≤ m/log²m`, Case 3 the rest. The Case 3 bound is an explicit argument so
the downstream X11 module can close the assembly without a cycle. -/
theorem Q_black_edge_of_case3 (A : ℝ) (hA : 0 < A)
    (hcase3 :
      ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
        ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
        ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
        ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
        (m : ℝ) / Real.log m ^ 2 < (s : ℝ) →
        (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
        Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
          ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ,
      1 ≤ n / 2 - m → (n / 2 - m, l) ∉ whiteSet n ξ →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  classical
  obtain ⟨C2, hC2⟩ := Q_black_edge_case2 A hA
  obtain ⟨C3, hC3⟩ := hcase3
  refine ⟨max C2 C3, fun n ξ hξ m hm hmn l h1 hnw => ?_⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨F⟩ := exists_triangleFamily n ξ hξ
  -- the phase point is black
  have hb : black n ξ (n / 2 - m - 1) l := by
    by_contra hw
    exact hnw ⟨h1, hw⟩
  -- hence lies in some triangle of the family
  have hmem0 : (n / 2 - m - 1, l) ∈
      {p : ℕ × ℤ | p.1 + 1 ≤ n / 2 ∧ black n ξ p.1 p.2} := ⟨by omega, hb⟩
  rw [F.cover] at hmem0
  simp only [Set.mem_iUnion, exists_prop] at hmem0
  obtain ⟨t, ht, hmem⟩ := hmem0
  -- the height budget
  have hl : l ≤ t.2.1 := hmem.2.1
  set s : ℕ := (t.2.1 - l).toNat with hs
  have hsZ : (s : ℤ) = t.2.1 - l := by omega
  -- (7.52): s·log 2 ≤ (m+1)·log 9
  have hbudget : (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 :=
    budget_le_of_mem_triangle F ht hmem (by omega)
  rcases le_or_gt (s : ℝ) ((m : ℝ) / Real.log m ^ 2) with hcase | hcase
  · exact hC2 n ξ hξ F m (le_trans (le_max_left _ _) hm) hmn l h1
      t ht hmem s hsZ hcase
  · exact hC3 n ξ hξ F m (le_trans (le_max_right _ _) hm) hmn l h1
      t ht hmem s hsZ hcase hbudget

/-- **Proposition 7.8 (Monotonicity)**, paper p.45: `Q_m ≤ Q_{m-1}` whenever
`C_{A,ε} ≤ m ≤ ⌊n/2⌋`, for a sufficiently large threshold `C_{A,ε}` depending only on
`A` (our `ε = epsBW` is a fixed numeral, D4). Uniform in `n, ξ`.

Proof: the `Qm m` sup splits. Interior points (`p₁ > ⌊n/2⌋ - m`) are admissible at
depth `m-1` with the same weight, so `le_Qm` bounds them by `Q_{m-1}` directly. Edge
points (`p₁ = ⌊n/2⌋ - m`, weight `m^A`) satisfy (7.41) `Q ≤ m^{-A}·Q_{m-1}`: white
starts by `Q_white_case1` (Case 1, proved), black starts by the supplied
`Q_black_edge` bound. -/
theorem prop_7_8_at (A : ℝ) (hA : 0 < A) (C2 : ℕ)
    (hC2 : ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, C2 ≤ m → m ≤ n / 2 →
        ∀ l : ℤ, 1 ≤ n / 2 - m → (n / 2 - m, l) ∉ whiteSet n ξ →
        Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
          ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, max (max (C_hold A) C2) 1 ≤ m → m ≤ n / 2 →
      Qm (n / 2) n ξ (epsBW : ℝ) A m ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  have hC1 := Q_white_case1_explicitC A hA
  set C1 := C_hold A with hC1def
  intro n ξ hξ m hm hmn
  have hmC1 : C1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmC2 : C2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hε0 : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hQM0 : 0 ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := Qm_nonneg _ _ _ _ _ _
  have hcancel : (m : ℝ) ^ A * (m : ℝ) ^ (-A) = 1 := by
    rw [← Real.rpow_add hm0, add_neg_cancel, Real.rpow_zero]
  refine Real.iSup_le (fun p => ?_) hQM0
  obtain ⟨⟨p1, l⟩, hp1, hpm⟩ := p
  have hp1' : 1 ≤ p1 := hp1
  have hpm' : n / 2 - m ≤ p1 := hpm
  show ((max (n / 2 - p1) 1 : ℕ) : ℝ) ^ A * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) p1 l
    ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)
  rcases eq_or_lt_of_le hpm' with heq | hlt
  · -- edge point: p1 = n/2 - m, weight = m^A
    have hp1eq : p1 = n / 2 - m := heq.symm
    have hwt : (max (n / 2 - p1) 1 : ℕ) = m := by omega
    have hedge : Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) p1 l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
      by_cases hw : (p1, l) ∈ whiteSet n ξ
      · have h := hC1 n ξ hξ m hmC1 hmn l (hp1eq ▸ hw)
        rw [hp1eq]
        calc Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
            ≤ Real.exp (-(epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A)
              * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := h
          _ ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
              apply mul_le_mul_of_nonneg_right _ hQM0
              have hexp : Real.exp (-(epsBW : ℝ) ^ 3 / 2) ≤ 1 := by
                rw [Real.exp_le_one_iff]
                have h3 : (0 : ℝ) ≤ (epsBW : ℝ) ^ 3 := by positivity
                linarith
              calc Real.exp (-(epsBW : ℝ) ^ 3 / 2) * (m : ℝ) ^ (-A)
                  ≤ 1 * (m : ℝ) ^ (-A) :=
                    mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hm0.le _)
                _ = (m : ℝ) ^ (-A) := one_mul _
      · exact hp1eq ▸ hC2 n ξ hξ m hmC2 hmn l (by omega) (hp1eq ▸ hw)
    calc ((max (n / 2 - p1) 1 : ℕ) : ℝ) ^ A * Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) p1 l
        ≤ ((max (n / 2 - p1) 1 : ℕ) : ℝ) ^ A
            * ((m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :=
          mul_le_mul_of_nonneg_left hedge (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (m : ℝ) ^ A * (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
          rw [hwt]; ring
      _ = Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by rw [hcancel, one_mul]
  · -- interior point: admissible at depth m-1 with the same weight
    exact le_Qm (n / 2) n ξ (epsBW : ℝ) A hA.le hε0 (m - 1) hp1 (by omega)

/-- `prop_7_8_of_black_edge`, original `∃`-form: delegates to the threshold-explicit
`prop_7_8_at` (big-C campaign, step 2; witness `max (max (C_hold A) C2) 1`). -/
theorem prop_7_8_of_black_edge (A : ℝ) (hA : 0 < A)
    (hblack :
      ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
        ∀ l : ℤ, 1 ≤ n / 2 - m → (n / 2 - m, l) ∉ whiteSet n ξ →
        Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
          ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      Qm (n / 2) n ξ (epsBW : ℝ) A m ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  obtain ⟨C2, hC2⟩ := hblack
  exact ⟨max (max (C_hold A) C2) 1, prop_7_8_at A hA C2 hC2⟩

/-- Paper (7.37), the consequence of (7.39) + Proposition 7.8 by forward induction on `m`:
`Q(j,l) ≪_A max(⌊n/2⌋ - j, 1)^{-A}`, uniformly in `n, ξ, j, l`. This is what feeds
(7.36) `E Q(Hold) ≪_A n^{-A}` and hence Proposition 7.3 in `Decay.lean`.
Threshold-explicit form (big-C campaign, step 2): the constant is `(max C0 1)^A` where
`C0` is the supplied Prop-7.8 threshold. -/
theorem Q_polynomial_decay_at (A : ℝ) (hA : 0 < A) (C0 : ℕ)
    (hC0 : ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, C0 ≤ m → m ≤ n / 2 →
        Qm (n / 2) n ξ (epsBW : ℝ) A m
          ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ (j : ℕ) (l : ℤ), 1 ≤ j →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l
        ≤ ((max C0 1 : ℕ) : ℝ) ^ A * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
  set Cb := max C0 1 with hCbdef
  have hCb1 : 1 ≤ Cb := le_max_right _ _
  have hCbR : (1 : ℝ) ≤ ((Cb : ℕ) : ℝ) := by exact_mod_cast hCb1
  have hCbA1 : (1 : ℝ) ≤ ((Cb : ℕ) : ℝ) ^ A := by
    calc (1 : ℝ) = (1 : ℝ) ^ A := (Real.one_rpow A).symm
      _ ≤ ((Cb : ℕ) : ℝ) ^ A := Real.rpow_le_rpow zero_le_one hCbR hA.le
  intro n ξ hξ j l hj
  have hε0 : (0 : ℝ) ≤ (epsBW : ℝ) := by
    have h0 : (0 : ℚ) ≤ epsBW := by unfold epsBW; norm_num
    exact_mod_cast h0
  -- the uniform bound Q_m ≤ Cb^A for 1 ≤ m ≤ n/2, by forward induction from (7.39)
  have hQmb : ∀ m : ℕ, 1 ≤ m → m ≤ n / 2 →
      Qm (n / 2) n ξ (epsBW : ℝ) A m ≤ ((Cb : ℕ) : ℝ) ^ A := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro hm1 hmn
      rcases le_or_gt m Cb with hle | hgt
      · calc Qm (n / 2) n ξ (epsBW : ℝ) A m ≤ (m : ℝ) ^ A := Qm_le_rpow _ _ _ _ hA.le _ hm1
          _ ≤ ((Cb : ℕ) : ℝ) ^ A :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) hA.le
      · have h78 := hC0 n ξ hξ m (by omega) hmn
        exact le_trans h78 (IH (m - 1) (by omega) (by omega) (by omega))
  rcases Nat.lt_or_ge j (n / 2) with hjlt | hjge
  · -- inside the strip: use le_Qm at depth m = n/2 - j, then the uniform bound
    have hle := Q_le_Qm (n / 2) n ξ (epsBW : ℝ) A hA.le hε0 (n / 2 - j) (l := l) hj
      (by omega)
    calc Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l
        ≤ ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A)
            * Qm (n / 2) n ξ (epsBW : ℝ) A (n / 2 - j) := hle
      _ ≤ ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) * (((Cb : ℕ) : ℝ) ^ A) :=
          mul_le_mul_of_nonneg_left (hQmb (n / 2 - j) (by omega) (by omega))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = ((Cb : ℕ) : ℝ) ^ A * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := mul_comm _ _
  · -- past the strip edge: Q ≤ 1 and the weight is 1
    have hw : (max (n / 2 - j) 1 : ℕ) = 1 := by omega
    calc Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l ≤ 1 := Q_le_one _ _ _ hε0 _ _
      _ ≤ ((Cb : ℕ) : ℝ) ^ A := hCbA1
      _ = ((Cb : ℕ) : ℝ) ^ A * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
          rw [hw, Nat.cast_one, Real.one_rpow, mul_one]

/-- `Q_polynomial_decay_of_prop_7_8`, original `∃`-form: delegates to the
threshold-explicit `Q_polynomial_decay_at` (big-C campaign, step 2). -/
theorem Q_polynomial_decay_of_prop_7_8 (A : ℝ) (hA : 0 < A)
    (hmono :
      ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
        Qm (n / 2) n ξ (epsBW : ℝ) A m
          ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :
    ∃ C > 0, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ (j : ℕ) (l : ℤ), 1 ≤ j →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l ≤ C * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
  obtain ⟨C0, hC0⟩ := hmono
  refine ⟨((max C0 1 : ℕ) : ℝ) ^ A, Real.rpow_pos_of_pos ?_ A,
    Q_polynomial_decay_at A hA C0 hC0⟩
  have h1 : (1 : ℕ) ≤ max C0 1 := le_max_right _ _
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1

end TaoCollatz
