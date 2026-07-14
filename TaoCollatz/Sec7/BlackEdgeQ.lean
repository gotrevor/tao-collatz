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

OPEN (node X8, the hardest Case-2 kernel): consumes `fpDist_location_bound`
(X6) and the geometric fight between the paper's `O(1)` exit-ring constants
and the fixed `ε = 10⁻⁴` separation `(1/10)·log(1/ε) ≈ 0.92` — numerically
validated ≈ 0.99 white-exit mass (harness check 9, 2026-07-10). -/
theorem fpDist_white_exit :
    ∃ p₀ > (0 : ℝ), ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamily n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      p₀ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) := by
  obtain ⟨p₀, hp₀, Cthr, h⟩ := fpDist_white_exit_deep
  exact ⟨p₀, by linarith, Cthr,
    fun n ξ hξ F m hm hmn l hl t ht htmem s hs _hbudget =>
      h n ξ hξ F m hm hmn l hl t ht htmem s hs⟩

/-- **Case 2 of Proposition 7.8** ((7.46)–(7.51) assembly, paper pp.46–48):
black edge start whose triangle-top budget satisfies `s ≤ m/log²m`. Route:
`Q_le_fpDist_expect` ((7.45) entry) + `Q_fp_endpoint_le` per endpoint, then
the (7.47) split `E[(1-(1-e^{-ε³})·1_W)·w] ≤ E[w] - (1-e^{-ε³})·m^{-A}·P(W)`
(using `w ≥ m^{-A}` pointwise), bounded via `fpDist_edgeWeight_le` (δ :=
`(1-e^{-ε³})·p₀/2`) and `fpDist_white_exit`:
`Q ≤ ((1+δ) - (1-e^{-ε³})·p₀)·m^{-A}·Q_{m-1} ≤ m^{-A}·Q_{m-1}`.

OPEN (node X8 assembly): mechanical once the two kernels above land; the
remaining work is `ℝ≥0∞`→`ℝ` bookkeeping across the fpDist tsum. -/
theorem Q_black_edge_case2 (A : ℝ) (hA : 0 < A) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
      ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 → ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      (s : ℝ) ≤ (m : ℝ) / Real.log m ^ 2 →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
        ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  sorry

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
  obtain ⟨F⟩ := exists_triangleFamily n ξ hξ hn1
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
theorem prop_7_8_of_black_edge (A : ℝ) (hA : 0 < A)
    (hblack :
      ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
        ∀ l : ℤ, 1 ≤ n / 2 - m → (n / 2 - m, l) ∉ whiteSet n ξ →
        Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) (n / 2 - m) l
          ≤ (m : ℝ) ^ (-A) * Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      Qm (n / 2) n ξ (epsBW : ℝ) A m ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1) := by
  obtain ⟨C1, hC1⟩ := Q_white_case1 A hA
  obtain ⟨C2, hC2⟩ := hblack
  refine ⟨max (max C1 C2) 1, fun n ξ hξ m hm hmn => ?_⟩
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

/-- Paper (7.37), the consequence of (7.39) + Proposition 7.8 by forward induction on `m`:
`Q(j,l) ≪_A max(⌊n/2⌋ - j, 1)^{-A}`, uniformly in `n, ξ, j, l`. This is what feeds
(7.36) `E Q(Hold) ≪_A n^{-A}` and hence Proposition 7.3 in `Decay.lean`. -/
theorem Q_polynomial_decay_of_prop_7_8 (A : ℝ) (hA : 0 < A)
    (hmono :
      ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
        Qm (n / 2) n ξ (epsBW : ℝ) A m
          ≤ Qm (n / 2) n ξ (epsBW : ℝ) A (m - 1)) :
    ∃ C > 0, ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ (j : ℕ) (l : ℤ), 1 ≤ j →
      Q (n / 2) (whiteSet n ξ) (epsBW : ℝ) j l ≤ C * ((max (n / 2 - j) 1 : ℕ) : ℝ) ^ (-A) := by
  obtain ⟨C0, hC0⟩ := hmono
  set Cb := max C0 1 with hCbdef
  have hCb1 : 1 ≤ Cb := le_max_right _ _
  have hCbR : (1 : ℝ) ≤ ((Cb : ℕ) : ℝ) := by exact_mod_cast hCb1
  have hCbA1 : (1 : ℝ) ≤ ((Cb : ℕ) : ℝ) ^ A := by
    calc (1 : ℝ) = (1 : ℝ) ^ A := (Real.one_rpow A).symm
      _ ≤ ((Cb : ℕ) : ℝ) ^ A := Real.rpow_le_rpow zero_le_one hCbR hA.le
  refine ⟨((Cb : ℕ) : ℝ) ^ A, Real.rpow_pos_of_pos (by linarith) A, ?_⟩
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


end TaoCollatz
