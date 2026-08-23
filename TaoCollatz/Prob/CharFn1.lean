import TaoCollatz.Prob.CharFn

/-!
# The d=1 finite circle method (node S3, d=1 local bounds)

Paper anchor: Tao 2019 Lemma 2.2 proof pp.15–16 at `d = 1`. Rather than
re-proving the Fourier machinery, everything is DERIVED from the 2-D module
`Prob/CharFn.lean` through the first-coordinate embedding
`embMod N L = (L mod N, 0)`: the embedded walk's characteristic function is
independent of the second frequency, so the 2-D inversion bound
`N⁻² ∑_{ξ}` collapses to `N⁻¹ ∑_j` — exactly the d=1 normalization, giving the
center bound `C/√(1+n)` at `N = ⌊√n⌋ + 1` (vs `C/(1+n)` in d=2).

* `embMod` — the additive embedding `ℕ → ZMod N × ZMod N`.
* `charFn_map_embMod_snd` — the embedded `charFn` is `ξ₂`-free.
* `iidSum_nat_apply_toReal_le` — the d=1 circle-method bound
  `P(S_n = L) ≤ N⁻¹ ∑_j ‖φ(j)‖ⁿ`.
* `charFn_embMod_decay_of_adjacent_atoms` — quadratic character decay from two
  atom-mass lower bounds at ADJACENT points `a, a+1` (constant `16μ²`; adjacency
  makes the 2-D triangle step unnecessary).
* `iidSum_nat_apply_le_center_of_decay` — the d=1 center bound `32c/√(1+n)`.
-/

open scoped ENNReal

namespace TaoCollatz

variable {N : ℕ} [NeZero N]

/-- The first-coordinate embedding `ℕ → ZMod N × ZMod N` (additive). -/
def embMod (N : ℕ) [NeZero N] (L : ℕ) : ZMod N × ZMod N := ((L : ZMod N), 0)

theorem embMod_zero : embMod N 0 = 0 := by
  rw [embMod]
  norm_num

theorem embMod_add (a b : ℕ) : embMod N (a + b) = embMod N a + embMod N b := by
  rw [embMod, embMod, embMod, Prod.mk_add_mk, add_zero]
  congr 1
  push_cast
  ring

/-- The embedded pushforward has no mass off the first-coordinate axis. -/
theorem map_embMod_apply_ne (p : PMF ℕ) {y : ZMod N × ZMod N} (hy : y.2 ≠ 0) :
    (p.map (embMod N)) y = 0 := by
  rw [PMF.map_apply]
  refine ENNReal.tsum_eq_zero.mpr fun L => ?_
  rw [if_neg]
  intro h
  exact hy (by rw [h]; rfl)

/-- The embedded characteristic function is independent of the second frequency. -/
theorem charFn_map_embMod_snd (p : PMF ℕ) (ξ : ZMod N × ZMod N) :
    charFn (p.map (embMod N)) ξ = charFn (p.map (embMod N)) (ξ.1, 0) := by
  rw [charFn, charFn]
  refine Finset.sum_congr rfl fun y _ => ?_
  rcases eq_or_ne y.2 0 with h2 | h2
  · congr 1
    rw [pairChar, pairChar]
    congr 1
    rw [h2]
    ring
  · rw [map_embMod_apply_ne p h2, ENNReal.toReal_zero, Complex.ofReal_zero,
      zero_mul, zero_mul]

/-- **The d=1 circle-method bound**: for any walk on `ℕ` and any modulus `N`,
`P(S_n = L) ≤ N⁻¹ ∑_j ‖φ(j)‖ⁿ` where `φ` is the embedded projected
characteristic function. -/
theorem iidSum_nat_apply_toReal_le (p : PMF ℕ) (n : ℕ) (N : ℕ) [NeZero N] (L : ℕ) :
    ((iidSum p n) L).toReal
      ≤ ((N : ℝ))⁻¹ * ∑ j : ZMod N, ‖charFn (p.map (embMod N)) (j, 0)‖ ^ n := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have hmap : (iidSum p n).map (embMod N) = iidSum (p.map (embMod N)) n :=
    iidSum_map p (embMod N) embMod_zero embMod_add n
  have hle : (iidSum p n) L ≤ (iidSum (p.map (embMod N)) n) (embMod N L) := by
    calc (iidSum p n) L
        ≤ ((iidSum p n).map (embMod N)) (embMod N L) :=
          PMF.apply_le_map_apply _ _ _
      _ = (iidSum (p.map (embMod N)) n) (embMod N L) := by rw [hmap]
  refine le_trans (ENNReal.toReal_mono (PMF.apply_ne_top _ _) hle) ?_
  refine le_trans (iidSum_apply_toReal_le (p.map (embMod N)) n (embMod N L)) ?_
  have hsum : ∑ ξ : ZMod N × ZMod N, ‖charFn (p.map (embMod N)) ξ‖ ^ n
      = (N : ℝ) * ∑ j : ZMod N, ‖charFn (p.map (embMod N)) (j, 0)‖ ^ n := by
    rw [Fintype.sum_prod_type]
    calc ∑ j : ZMod N, ∑ t : ZMod N, ‖charFn (p.map (embMod N)) (j, t)‖ ^ n
        = ∑ j : ZMod N, ∑ _t : ZMod N, ‖charFn (p.map (embMod N)) (j, 0)‖ ^ n := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
          rw [charFn_map_embMod_snd]
      _ = ∑ j : ZMod N, (N : ℝ) * ‖charFn (p.map (embMod N)) (j, 0)‖ ^ n := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      _ = (N : ℝ) * ∑ j : ZMod N, ‖charFn (p.map (embMod N)) (j, 0)‖ ^ n :=
          (Finset.mul_sum _ _ _).symm
  rw [hsum]
  refine le_of_eq ?_
  rw [← mul_assoc]
  congr 1
  field_simp

/-- **Quadratic character decay from two ADJACENT atoms** (d=1 (F3) analogue):
if the embedded projected walk keeps mass `≥ μ` at `embMod a` and
`embMod (a+1)` (`N ≥ 4`), its characteristic function decays like
`1 − 16μ²·(nd j / N)²`. Adjacency makes the difference character exactly
`e(j/N)`, so no triangle step is needed. Stated for an abstract PMF `r` on the
pair group so it applies verbatim to tilted projected walks. -/
theorem charFn_embMod_decay_of_adjacent_atoms (hN : 4 ≤ N)
    (r : PMF (ZMod N × ZMod N)) {μ : ℝ} (hμ : 0 ≤ μ) (a : ℕ)
    (hma : μ ≤ (r (embMod N a)).toReal) (hmb : μ ≤ (r (embMod N (a + 1))).toReal)
    (j : ZMod N) :
    ‖charFn r (j, 0)‖ ^ 2 ≤ 1 - 16 * μ ^ 2 * ((nd j : ℝ) / N) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hne : embMod N (a + 1) ≠ embMod N a := by
    intro h
    have h1 : ((a + 1 : ℕ) : ZMod N) = ((a : ℕ) : ZMod N) := congrArg Prod.fst h
    have h0 : ((1 : ℕ) : ZMod N) = 0 := by
      have hsub := sub_eq_zero.mpr h1
      calc ((1 : ℕ) : ZMod N) = ((a + 1 : ℕ) : ZMod N) - ((a : ℕ) : ZMod N) := by
            push_cast
            ring
        _ = 0 := hsub
    have hdvd := (ZMod.natCast_eq_zero_iff 1 N).mp h0
    have := Nat.le_of_dvd one_pos hdvd
    omega
  have hb := charFn_normSq_pair_bound r (j, 0) (embMod N (a + 1)) (embMod N a) hne
  have hdiff : embMod N (a + 1) - embMod N a = (((1 : ℕ) : ZMod N), (0 : ZMod N)) := by
    rw [embMod, embMod, Prod.mk_sub_mk, sub_zero]
    congr 1
    push_cast
    ring
  rw [hdiff] at hb
  have hpc : pairChar ((j : ZMod N), (0 : ZMod N)) (((1 : ℕ) : ZMod N), (0 : ZMod N))
      = ZMod.stdAddChar j := by
    rw [pairChar]
    congr 1
    push_cast
    ring
  rw [hpc] at hb
  have hJ := one_sub_re_stdAddChar_ge' j
  set u : ℝ := (nd j : ℝ) / N with hu
  have hu0 : 0 ≤ u := by positivity
  have h1R : 0 ≤ 1 - (ZMod.stdAddChar j).re := le_trans (by positivity) hJ
  have hm0 : (0 : ℝ) ≤ (r (embMod N a)).toReal := ENNReal.toReal_nonneg
  have hm1 : (0 : ℝ) ≤ (r (embMod N (a + 1))).toReal := ENNReal.toReal_nonneg
  have hmm : μ * μ ≤ (r (embMod N (a + 1))).toReal * (r (embMod N a)).toReal :=
    mul_le_mul hmb hma hμ hm1
  have hchain : 2 * (μ * μ) * (8 * u ^ 2) ≤ 1 - ‖charFn r (j, 0)‖ ^ 2 := by
    calc 2 * (μ * μ) * (8 * u ^ 2)
        ≤ 2 * (μ * μ) * (1 - (ZMod.stdAddChar j).re) :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
      _ ≤ 2 * ((r (embMod N (a + 1))).toReal * (r (embMod N a)).toReal)
            * (1 - (ZMod.stdAddChar j).re) := by
          have := mul_le_mul_of_nonneg_right hmm h1R
          nlinarith
      _ ≤ 1 - ‖charFn r (j, 0)‖ ^ 2 := by
          calc 2 * ((r (embMod N (a + 1))).toReal * (r (embMod N a)).toReal)
                * (1 - (ZMod.stdAddChar j).re)
              = 2 * (r (embMod N (a + 1))).toReal * (r (embMod N a)).toReal
                * (1 - (ZMod.stdAddChar j).re) := by ring
            _ ≤ 1 - ‖charFn r (j, 0)‖ ^ 2 := hb
  nlinarith [hchain]

/-- **The d=1 parametric center-regime local bound** (Gaussian summation at
`N = ⌊√n⌋ + 1`): any walk on `ℕ` whose embedded projected characteristic
functions decay like `1 − (nd j/N)²/c` uniformly in `N ≥ 4` has point masses
`≤ 32c/√(1+n)` — the d=1 normalization of `iidSum_apply_le_center_of_decay`
(one factor of `N`, hence `1/√n` instead of `1/n`). -/
theorem iidSum_nat_apply_le_center_of_decay (p : PMF ℕ) {c : ℝ} (hc : 1 ≤ c)
    (hdec : ∀ (N : ℕ) [NeZero N], 4 ≤ N → ∀ j : ZMod N,
      ‖charFn (p.map (embMod N)) (j, 0)‖ ^ 2 ≤ 1 - ((nd j : ℝ) / N) ^ 2 / c)
    (n : ℕ) (L : ℕ) :
    ((iidSum p n) L).toReal ≤ 32 * c / Real.sqrt (1 + (n : ℝ)) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have h1n : (0 : ℝ) < 1 + n := by positivity
  have hsq0 : (0 : ℝ) < Real.sqrt (1 + n) := Real.sqrt_pos.mpr h1n
  rcases le_or_gt n 8 with hn8 | hn9
  · -- small n: the trivial mass bound suffices
    have h1 : (((iidSum p n)) L).toReal ≤ 1 := by
      have := (iidSum p n).coe_le_one L
      calc (((iidSum p n)) L).toReal ≤ (1 : ℝ≥0∞).toReal :=
            ENNReal.toReal_mono ENNReal.one_ne_top this
        _ = 1 := ENNReal.toReal_one
    have hcast : (n : ℝ) ≤ 8 := by exact_mod_cast hn8
    refine le_trans h1 ?_
    rw [le_div_iff₀ hsq0]
    have hsqle : Real.sqrt (1 + (n : ℝ)) ≤ 3 := by
      rw [show (3 : ℝ) = Real.sqrt 9 from by
        rw [show (9 : ℝ) = 3 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    nlinarith
  · -- large n: circle method at N = √n + 1
    have hn9' : 9 ≤ n := hn9
    set N := n.sqrt + 1 with hN
    have : NeZero N := ⟨Nat.succ_ne_zero _⟩
    have hs3 : 3 ≤ n.sqrt := (Nat.le_sqrt.mpr (by omega))
    have hN4 : 4 ≤ N := by omega
    have hNlow : n + 1 ≤ N ^ 2 := Nat.lt_succ_sqrt' n
    have hNhigh : N ^ 2 ≤ 2 * n := by
      have h1 := Nat.sqrt_le' n
      have : N ^ 2 = n.sqrt ^ 2 + 2 * n.sqrt + 1 := by ring
      nlinarith [hs3, h1]
    have hNR : (0 : ℝ) < N := by
      have : 0 < N := by omega
      exact_mod_cast this
    set a : ℝ := (n : ℝ) / (4 * c * (N : ℝ) ^ 2) with ha
    have hNlowR : (n : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by exact_mod_cast hNlow
    have hNhighR : (N : ℝ) ^ 2 ≤ 2 * n := by exact_mod_cast hNhigh
    have ha0 : 0 < a := by
      rw [ha]
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      positivity
    have ha1 : a ≤ 1 := by
      rw [ha, div_le_one (by positivity)]
      nlinarith
    have ha_low : 1 / (8 * c) ≤ a := by
      rw [ha, le_div_iff₀ (by positivity)]
      have hkey : 1 / (8 * c) * (4 * c * (N : ℝ) ^ 2) = (N : ℝ) ^ 2 / 2 := by
        field_simp
        ring
      rw [hkey]
      linarith
    -- per-frequency exponential bound (single factor)
    have hfreq : ∀ j : ZMod N,
        ‖charFn (p.map (embMod N)) (j, 0)‖ ^ n
          ≤ Real.exp (-(a * ((nd j : ℝ)) ^ 2)) := by
      intro j
      have hdecay := hdec N hN4 j
      set D : ℝ := ((nd j : ℝ) / N) ^ 2 / c with hD
      have hD0 : 0 ≤ D := by positivity
      have hpow := pow_le_exp_of_sq_le_one_sub n (by omega) (norm_nonneg _) hD0
        (by rw [hD]; linarith)
      refine le_trans hpow (le_of_eq ?_)
      congr 1
      rw [hD, ha]
      field_simp
    have hmain := iidSum_nat_apply_toReal_le p n N L
    set g : ZMod N → ℝ := fun t => Real.exp (-(a * ((nd t : ℝ)) ^ 2)) with hg
    have hsum1 : ∑ j : ZMod N, ‖charFn (p.map (embMod N)) (j, 0)‖ ^ n
        ≤ ∑ t : ZMod N, g t :=
      Finset.sum_le_sum fun j _ => hfreq j
    have hg_bound : ∑ t : ZMod N, g t ≤ 32 * c := by
      calc ∑ t : ZMod N, g t ≤ 2 * (1 - Real.exp (-a))⁻¹ := sum_exp_neg_nd_sq_le ha0
        _ ≤ 2 * (2 / a) := by
            have := one_sub_exp_neg_inv_le ha0 ha1
            linarith
        _ = 4 / a := by ring
        _ ≤ 32 * c := by
            rw [div_le_iff₀ ha0]
            have hkey : 32 * c * (1 / (8 * c)) = 4 := by
              field_simp
              norm_num
            calc (4 : ℝ) = 32 * c * (1 / (8 * c)) := hkey.symm
              _ ≤ 32 * c * a := by
                  exact mul_le_mul_of_nonneg_left ha_low (by positivity)
    have hgnn : 0 ≤ ∑ t : ZMod N, g t :=
      Finset.sum_nonneg fun t _ => (Real.exp_pos _).le
    have hinvN : ((N : ℝ))⁻¹ ≤ (Real.sqrt (1 + (n : ℝ)))⁻¹ := by
      gcongr
      rw [show ((N : ℝ)) = Real.sqrt ((N : ℝ) ^ 2) from
        (Real.sqrt_sq hNR.le).symm]
      exact Real.sqrt_le_sqrt (by linarith)
    calc ((iidSum p n) L).toReal
        ≤ ((N : ℝ))⁻¹ * ∑ j : ZMod N, ‖charFn (p.map (embMod N)) (j, 0)‖ ^ n := hmain
      _ ≤ ((N : ℝ))⁻¹ * ∑ t : ZMod N, g t := by
          gcongr
      _ ≤ ((N : ℝ))⁻¹ * (32 * c) := by
          gcongr
      _ ≤ (Real.sqrt (1 + (n : ℝ)))⁻¹ * (32 * c) := by
          gcongr
      _ = 32 * c / Real.sqrt (1 + (n : ℝ)) := by
          rw [inv_mul_eq_div]

end TaoCollatz
