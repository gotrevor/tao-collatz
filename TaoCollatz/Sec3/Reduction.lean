import TaoCollatz.Basic.Collatz
import TaoCollatz.Basic.LogDensity
import TaoCollatz.Sec5.Stabilization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §3 reduction — the C6 intermediates (Thm 3.1 Syracuse form, Thm 1.6, the (1.2) bridge)

Pins for the §3 chain `Prop 1.11 ⟹ Thm 3.1 (Syracuse) ⟹ Thm 1.6 ⟹ Thm 1.3`, plus the
(1.2) odd-part reduction that converts each Syracuse claim to its Collatz form. Every
theorem here is a sorried STATEMENT (blueprint pin), written copy-not-compose against
arXiv:1909.03562v5 §1.2 (pp.4–5) and §3 (pp.16–18). Numeric traps: `check14`/`check15`
in `tools/check_blueprint.py`.

Pinned this lap (2026-07-15); NOT yet judge-ratified. JUDGE-FLAG: ratify-on-pin owed.

Statement notes for the judge (faithfulness choices, flagged, not silently made):
* `tao_syracuse` takes `f : ℕ → ℝ` with `Tendsto f atTop atTop` where the paper's
  `f : 2ℕ+1 → ℝ` has `lim_{N→∞} f(N) = ∞` along odd `N`. The two forms are equivalent:
  the conclusion only samples `f` at odd `N`, and any paper-`f` extends to all of `ℕ`
  (constantly on evens between consecutive odds) preserving the limit. This mirrors the
  frozen `tao_collatz` headline's rendering of Thm 1.3's hypothesis.
* Thm 3.1's two displays ("… or equivalently …", p.16) are BOTH pinned
  (`tao_syracuse_quantitative_sum`, `tao_syracuse_quantitative`): the sum form is what
  the dyadic covering argument produces and what the (1.2) pullback consumes; the
  probability form mirrors the frozen `tao_collatz_quantitative` headline. Their
  equivalence (normalize by the odd-window harmonic mass ≍ log x) is part of the C6
  proof obligation, not assumed.
-/

namespace TaoCollatz

open Filter

/-! ## Descent machinery for the §3 telescoping (worker-authored decomposition)

The paper's proof of Thm 3.1 (pp.17–18) iterates Prop 1.11 over dyadic-in-`α` scales. The
event `B_x` ("the orbit passes `x` and its passage location eventually reaches `≤ N₀`") is
`descentEvent`; its probability over the log-uniform window `[y, y^α]` is `descentProb`.
Deterministic orbit lemmas are proved here; the probabilistic recursion, base case, and
telescope are named sorries (each with its paper line). -/

/-- `Syrmin` can only rise along the orbit: the orbit of `syr^[k] N` is a tail of `N`'s. -/
theorem syrMin_le_syrMin_iterate (N k : ℕ) : syrMin N ≤ syrMin (syr^[k] N) := by
  apply le_csInf (Set.range_nonempty _)
  rintro b ⟨j, rfl⟩
  show syrMin N ≤ syr^[j] (syr^[k] N)
  rw [← Function.iterate_add_apply]
  exact Nat.sInf_le ⟨j + k, rfl⟩

/-- `Syrmin M ≤ M` (the orbit starts at `M`). -/
theorem syrMin_le_self (M : ℕ) : syrMin M ≤ M := Nat.sInf_le ⟨0, rfl⟩

/-- Passing a lower threshold implies passing a higher one. -/
theorem passes_mono {x x' N : ℕ} (h : x ≤ x') : passes x N → passes x' N :=
  fun ⟨n, hn⟩ => ⟨n, le_trans hn h⟩

/-- The passage location is at most the threshold (on passage). -/
theorem passLoc_le_of_passes {x N : ℕ} (h : passes x N) : passLoc x N ≤ x := by
  have hne : {n | syr^[n] N ≤ x}.Nonempty := h
  have hmem : syr^[passTime x N] N ≤ x := Nat.sInf_mem hne
  rw [passLoc, if_pos h]
  exact hmem

/-- A higher threshold is passed no later. -/
theorem passTime_anti {x x' N : ℕ} (hxx' : x ≤ x') (h : passes x N) :
    passTime x' N ≤ passTime x N := by
  have hne : {n | syr^[n] N ≤ x}.Nonempty := h
  have hmem : syr^[passTime x N] N ≤ x := Nat.sInf_mem hne
  exact Nat.sInf_le (le_trans hmem hxx')

/-- For `x ≤ x'` the `x`-passage location sits on the orbit of the `x'`-passage location,
so its `Syrmin` is at least as small (paper p.17: `SyrN(Pass_x) ⊆ SyrN(Pass_{x^α})`). -/
theorem syrMin_passLoc_anti {x x' N : ℕ} (hxx' : x ≤ x') (h : passes x N) :
    syrMin (passLoc x' N) ≤ syrMin (passLoc x N) := by
  have h' : passes x' N := passes_mono hxx' h
  have hloc' : passLoc x' N = syr^[passTime x' N] N := by rw [passLoc, if_pos h']
  have hloc : passLoc x N = syr^[passTime x N] N := by rw [passLoc, if_pos h]
  have hshift : passLoc x N = syr^[passTime x N - passTime x' N] (passLoc x' N) := by
    rw [hloc', ← Function.iterate_add_apply, hloc]
    congr 1
    have := passTime_anti hxx' h
    omega
  rw [hshift]
  exact syrMin_le_syrMin_iterate _ _

/-- The §3 descent event `B_x` (p.17): the orbit passes `≤ x`, and from the passage
location it eventually reaches `≤ N₀`. -/
def descentEvent (x N₀ : ℕ) : Set ℕ := {N | passes x N ∧ syrMin (passLoc x N) ≤ N₀}

/-- `B` is monotone in the threshold (the deterministic inclusion driving the recursion,
p.17: `T_x < ∞ ∧ Pass_x ∈ E_{N₀}` implies `B_{x^α}`). -/
theorem descentEvent_mono {x x' N₀ : ℕ} (hxx' : x ≤ x') :
    descentEvent x N₀ ⊆ descentEvent x' N₀ := by
  rintro N ⟨hp, hs⟩
  exact ⟨passes_mono hxx' hp, le_trans (syrMin_passLoc_anti hxx' hp) hs⟩

/-- On the descent event, `Syrmin(N) ≤ N₀` (p.18: `Syrmin(N_x) ≤ Syrmin(Pass) ≤ N₀`). -/
theorem syrMin_le_of_descentEvent {x N₀ N : ℕ} (h : N ∈ descentEvent x N₀) :
    syrMin N ≤ N₀ := by
  obtain ⟨hp, hs⟩ := h
  have hloc : passLoc x N = syr^[passTime x N] N := by rw [passLoc, if_pos hp]
  rw [hloc] at hs
  exact le_trans (syrMin_le_syrMin_iterate _ _) hs

/-- `ℙ(B_x)` over the log-uniform window `[y, y^α]`. -/
noncomputable def descentProb (x : ℕ) (y : ℝ) (N₀ : ℕ) : ℝ :=
  (logUnifOdd y (y ^ alpha)).expect (Set.indicator (descentEvent x N₀) 1)

/-- Complement identity for indicator expectations: `𝔼[1_S] = 1 − 𝔼[1_{Sᶜ}]`. -/
theorem expect_indicator_compl (P : PMF ℕ) (S : Set ℕ) :
    P.expect (Set.indicator S 1) = 1 - P.expect (Set.indicator Sᶜ 1) := by
  have hsumP : Summable fun N => (P N).toReal := ENNReal.summable_toReal P.tsum_coe_ne_top
  have hsum : ∀ V : Set ℕ, Summable fun N => (P N).toReal * Set.indicator V 1 N := by
    intro V
    refine Summable.of_nonneg_of_le (fun N => mul_nonneg ENNReal.toReal_nonneg
      (Set.indicator_nonneg (fun _ _ => zero_le_one) N)) (fun N => ?_) hsumP
    by_cases h : N ∈ V <;> simp [Set.indicator_apply, h]
  have hadd : P.expect (Set.indicator S 1) + P.expect (Set.indicator Sᶜ 1)
      = ∑' N, (P N).toReal := by
    unfold PMF.expect
    rw [← Summable.tsum_add (hsum S) (hsum Sᶜ)]
    refine tsum_congr fun N => ?_
    by_cases h : N ∈ S <;>
      simp [Set.indicator_apply, h]
  have htot : ∑' N, (P N).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun N => PMF.apply_ne_top _ _), P.tsum_coe,
      ENNReal.toReal_one]
  linarith [hadd, htot]

/-- Terms `(p N)·1_V(N)` are summable (dominated by the PMF mass). -/
theorem summable_indicator_term (p : PMF ℕ) (V : Set ℕ) :
    Summable fun N => (p N).toReal * Set.indicator V 1 N := by
  refine Summable.of_nonneg_of_le (fun N => mul_nonneg ENNReal.toReal_nonneg
    (Set.indicator_nonneg (fun _ _ => zero_le_one) N)) (fun N => ?_)
    (ENNReal.summable_toReal p.tsum_coe_ne_top)
  by_cases h : N ∈ V <;> simp [Set.indicator_apply, h]

/-- Indicator expectation of a pushforward is the expectation of the preimage indicator. -/
theorem expect_indicator_map (p : PMF ℕ) (f : ℕ → ℕ) (E : Set ℕ) :
    (p.map f).expect (Set.indicator E 1) = p.expect (Set.indicator (f ⁻¹' E) 1) := by
  classical
  rw [expect_indicator_toReal, expect_indicator_toReal]
  congr 1
  calc ∑' b, (if b ∈ E then (p.map f) b else 0)
      = ∑' b, ∑' a, (if b ∈ E then (if b = f a then p a else 0) else 0) := by
        refine tsum_congr fun b => ?_
        by_cases hbE : b ∈ E
        · simp only [if_pos hbE, PMF.map_apply]
          exact tsum_congr fun a => by congr
        · simp only [if_neg hbE, tsum_zero]
    _ = ∑' a, ∑' b, (if b ∈ E then (if b = f a then p a else 0) else 0) :=
        ENNReal.tsum_comm
    _ = ∑' a, (if a ∈ f ⁻¹' E then p a else 0) := by
        refine tsum_congr fun a => ?_
        rw [tsum_eq_single (f a) (fun b hb => by
          by_cases hbE : b ∈ E
          · rw [if_pos hbE, if_neg hb]
          · rw [if_neg hbE])]
        by_cases hE : f a ∈ E
        · rw [if_pos hE, if_pos rfl, if_pos (Set.mem_preimage.mpr hE)]
        · rw [if_neg hE, if_neg (fun h => hE (Set.mem_preimage.mp h))]

/-- Union subadditivity for indicator expectations. -/
theorem expect_indicator_union_le (p : PMF ℕ) (S T : Set ℕ) :
    p.expect (Set.indicator (S ∪ T) 1)
      ≤ p.expect (Set.indicator S 1) + p.expect (Set.indicator T 1) := by
  unfold PMF.expect
  rw [← Summable.tsum_add (summable_indicator_term p S) (summable_indicator_term p T)]
  refine Summable.tsum_le_tsum (fun N => ?_) (summable_indicator_term p (S ∪ T))
    ((summable_indicator_term p S).add (summable_indicator_term p T))
  have hnn : (0 : ℝ) ≤ (p N).toReal := ENNReal.toReal_nonneg
  by_cases hS : N ∈ S <;> by_cases hT : N ∈ T <;>
    simp [Set.indicator_apply, hS, hT] <;> linarith

/-- **One-scale recursion** (p.17, the display chain): `ℙ(B_x) ≤ ℙ(B_{x^α}) + O(log^{-c}x)`.
Route: `B_x ⊆ {Pass_x ∈ E}` up to the non-passage event (`stabilization` part 1, note
`1 ∈ E_{N₀}` since `passLoc = 1` off passage and `Syrmin 1 = 1 ≤ N₀`); swap windows by
`stabilization`'s dTV bound via `abs_expect_indicator_sub_le_dTV`; re-enter `B_{x^α}` by
`descentEvent_mono` (⌊x⌋₊ ≤ ⌊x^α⌋₊). -/
theorem descentProb_step :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ N₀ : ℕ, 1 ≤ N₀ →
      descentProb ⌊x⌋₊ (x ^ alpha) N₀
        ≤ descentProb ⌊x ^ alpha⌋₊ (x ^ alpha ^ 2) N₀ + C * (Real.log x) ^ (-c) := by
  obtain ⟨c, C, x₀, hc, hC, hstab⟩ := stabilization
  refine ⟨c, 2 * C, max x₀ (Real.exp 1), hc, by linarith, fun x hx N₀ hN₀ => ?_⟩
  have hx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) ≤ x := by
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr zero_le_one
      _ ≤ x := hxe
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx1
  obtain ⟨hesc, hdTV⟩ := hstab x hx₀
  -- rpow window identifications
  have hw1 : (x ^ alpha) ^ alpha = x ^ alpha ^ 2 := by rw [pow_two, Real.rpow_mul hx0]
  have hw2 : (x ^ alpha ^ 2) ^ alpha = x ^ alpha ^ 3 := by
    conv_rhs => rw [pow_succ, Real.rpow_mul hx0]
  set W₁ := logUnifOdd (x ^ alpha) (x ^ alpha ^ 2) with hW₁
  set W₂ := logUnifOdd (x ^ alpha ^ 2) (x ^ alpha ^ 3) with hW₂
  set E : Set ℕ := {M | syrMin M ≤ N₀} with hE
  set B₁ := descentEvent ⌊x⌋₊ N₀ with hB₁
  set B₂ := descentEvent ⌊x ^ alpha⌋₊ N₀ with hB₂
  -- error pieces from `stabilization`
  have hesc₂ : W₂.expect (Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1) ≤ C * x ^ (-c) := by
    have := hesc (x ^ alpha ^ 2) (Set.mem_insert_of_mem _ rfl)
    rwa [hw2] at this
  have hdTV' := PMF.abs_expect_indicator_sub_le_dTV
    (W₁.map (passLoc ⌊x⌋₊)) (W₂.map (passLoc ⌊x⌋₊)) E
  -- the two probability chains
  have hchain1 : descentProb ⌊x⌋₊ (x ^ alpha) N₀
      ≤ (W₂.map (passLoc ⌊x⌋₊)).expect (Set.indicator E 1) + C * (Real.log x) ^ (-c) := by
    have hsub : ∀ N ∈ W₁.support, N ∈ B₁ → N ∈ passLoc ⌊x⌋₊ ⁻¹' E := by
      rintro N _ ⟨_, hs⟩
      exact Set.mem_preimage.mpr hs
    have h1 : descentProb ⌊x⌋₊ (x ^ alpha) N₀
        ≤ W₁.expect (Set.indicator (passLoc ⌊x⌋₊ ⁻¹' E) 1) := by
      unfold descentProb
      rw [hw1]
      exact expect_mono_on_support W₁ B₁ _ hsub
    have h2 : W₁.expect (Set.indicator (passLoc ⌊x⌋₊ ⁻¹' E) 1)
        = (W₁.map (passLoc ⌊x⌋₊)).expect (Set.indicator E 1) :=
      (expect_indicator_map W₁ _ E).symm
    have h3 : (W₁.map (passLoc ⌊x⌋₊)).expect (Set.indicator E 1)
        ≤ (W₂.map (passLoc ⌊x⌋₊)).expect (Set.indicator E 1)
          + C * (Real.log x) ^ (-c) := by
      have := (abs_le.mp hdTV').2
      linarith [le_trans this hdTV]
    linarith
  have hchain2 : (W₂.map (passLoc ⌊x⌋₊)).expect (Set.indicator E 1)
      ≤ descentProb ⌊x ^ alpha⌋₊ (x ^ alpha ^ 2) N₀ + C * x ^ (-c) := by
    have h4 : (W₂.map (passLoc ⌊x⌋₊)).expect (Set.indicator E 1)
        = W₂.expect (Set.indicator (passLoc ⌊x⌋₊ ⁻¹' E) 1) :=
      expect_indicator_map W₂ _ E
    have hsub2 : ∀ N ∈ W₂.support, N ∈ passLoc ⌊x⌋₊ ⁻¹' E
        → N ∈ B₁ ∪ {N | ¬ passes ⌊x⌋₊ N} := by
      intro N _ hN
      by_cases hp : passes ⌊x⌋₊ N
      · exact Or.inl ⟨hp, Set.mem_preimage.mp hN⟩
      · exact Or.inr hp
    have h5 : W₂.expect (Set.indicator (passLoc ⌊x⌋₊ ⁻¹' E) 1)
        ≤ W₂.expect (Set.indicator (B₁ ∪ {N | ¬ passes ⌊x⌋₊ N}) 1) :=
      expect_mono_on_support W₂ _ _ hsub2
    have h6 := expect_indicator_union_le W₂ B₁ {N | ¬ passes ⌊x⌋₊ N}
    -- threshold bump `⌊x⌋ ≤ ⌊x^α⌋`
    have hxxa : x ≤ x ^ alpha := by
      calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ alpha := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num [alpha])
    have h7 : W₂.expect (Set.indicator B₁ 1) ≤ W₂.expect (Set.indicator B₂ 1) :=
      expect_mono_on_support W₂ B₁ B₂ fun N _ hN =>
        descentEvent_mono (Nat.floor_mono hxxa) hN
    have h8 : W₂.expect (Set.indicator B₂ 1)
        = descentProb ⌊x ^ alpha⌋₊ (x ^ alpha ^ 2) N₀ := by
      unfold descentProb
      rw [hw2]
    linarith [hesc₂]
  -- `x^{-c} ≤ (log x)^{-c}` for `x ≥ e`
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hlogpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le one_pos hlog1
  have herr : x ^ (-c) ≤ (Real.log x) ^ (-c) := by
    rw [Real.rpow_neg hx0, Real.rpow_neg hlogpos.le]
    refine inv_anti₀ (Real.rpow_pos_of_pos hlogpos _) ?_
    exact Real.rpow_le_rpow hlogpos.le (Real.log_le_self hx0) hc.le
  calc descentProb ⌊x⌋₊ (x ^ alpha) N₀
      ≤ (W₂.map (passLoc ⌊x⌋₊)).expect (Set.indicator E 1)
        + C * (Real.log x) ^ (-c) := hchain1
    _ ≤ descentProb ⌊x ^ alpha⌋₊ (x ^ alpha ^ 2) N₀ + C * x ^ (-c)
        + C * (Real.log x) ^ (-c) := by linarith [hchain2]
    _ ≤ descentProb ⌊x ^ alpha⌋₊ (x ^ alpha ^ 2) N₀
        + 2 * C * (Real.log x) ^ (-c) := by nlinarith [herr, hC]

/-- **Base case** (p.17 bottom): at scales `x ≤ N₀`, the event needs only passage —
`Syrmin(Pass) ≤ Pass ≤ ⌊x⌋ ≤ N₀` — so `first_passage_nonescape` gives `1 − O(x^{-c})`. -/
theorem descentProb_base :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ N₀ : ℕ, x ≤ (N₀ : ℝ) →
      1 - C * x ^ (-c) ≤ descentProb ⌊x⌋₊ (x ^ alpha) N₀ := by
  obtain ⟨c, C, x₀, hc, hC, hne⟩ := first_passage_nonescape
  refine ⟨c, C, max x₀ 0, hc, hC, fun x hx N₀ hxN₀ => ?_⟩
  have hx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hkey := hne x hx₀ (x ^ alpha) (Set.mem_insert _ _)
  have hfloor : ⌊x⌋₊ ≤ N₀ := by
    calc ⌊x⌋₊ ≤ ⌊(N₀ : ℝ)⌋₊ := Nat.floor_mono hxN₀
      _ = N₀ := Nat.floor_natCast N₀
  unfold descentProb
  rw [expect_indicator_compl]
  have hsub : ∀ N ∈ (logUnifOdd (x ^ alpha) ((x ^ alpha) ^ alpha)).support,
      N ∈ (descentEvent ⌊x⌋₊ N₀)ᶜ → N ∈ {N | ¬ passes ⌊x⌋₊ N} := by
    intro N _ hN
    by_contra hpass
    rw [Set.mem_setOf_eq, not_not] at hpass
    exact hN ⟨hpass, le_trans
      (le_trans (syrMin_le_self _) (passLoc_le_of_passes hpass)) hfloor⟩
  have hmono := expect_mono_on_support (logUnifOdd (x ^ alpha) ((x ^ alpha) ^ alpha))
    (descentEvent ⌊x⌋₊ N₀)ᶜ {N | ¬ passes ⌊x⌋₊ N} hsub
  linarith [le_trans hmono hkey]

/-- **Telescope** (p.18 top): iterating `descentProb_step` down `J ≈ log_α(log x/log N₀)`
scales from the base `y < N₀^{1/α}` and summing `∑_j (α^j log y)^{-c} ≪ log^{-c} N₀` gives
`ℙ(B_{x^{1/α}}) ≥ 1 − O(log^{-c}N₀)` — the window `[x, x^α]`, threshold `⌊x^{1/α}⌋`. -/
theorem descent_whp :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ : ℕ, ∀ x : ℝ, x₀ ≤ x → x₀ ≤ (N₀ : ℝ) →
      (N₀ : ℝ) ≤ x →
      1 - C * (Real.log N₀) ^ (-c) ≤ descentProb ⌊x ^ (alpha⁻¹)⌋₊ x N₀ := by
  sorry

/-- **Window bad-mass** ((3.1), p.18): on any window `[x, x^α]` with `N₀ ≤ x`, the harmonic
mass of `{Syrmin > N₀}` is `≪ log^{-c}N₀ · log x`. From `descent_whp` +
`syrMin_le_of_descentEvent` + `logUnifOdd_expect_indicator` + `windowMass_le_half_log`. -/
theorem window_bad_sum :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ : ℕ, ∀ x : ℝ, x₀ ≤ x → x₀ ≤ (N₀ : ℝ) →
      (N₀ : ℝ) ≤ x →
      ∑ N ∈ (logWindow x (x ^ alpha)).filter (· ∈ {N | N₀ < syrMin N}), (N : ℝ)⁻¹
        ≤ C * (Real.log N₀) ^ (-c) * Real.log x := by
  sorry

/-- **Theorem 3.1, Syracuse sum form** (Tao 2019 p.16, first display):
`∑_{N ∈ 2ℕ+1 ∩ [1,x], Syrmin(N) > N₀} 1/N ≪ log x / (log N₀)^c`. -/
-- RATIFY-C6a
theorem tao_syracuse_quantitative_sum :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      logSum {N | N₀ < syrMin N} (oddInterval x)
        ≤ C * Real.log x / (Real.log N₀) ^ c := by
  sorry

/-- **Theorem 3.1, Syracuse probability form** (Tao 2019 p.16, second display):
`ℙ(Syrmin(Log(2ℕ+1 ∩ [1,x])) ≤ N₀) ≥ 1 − O(log^{-c} N₀)`. -/
-- RATIFY-C6b
theorem tao_syracuse_quantitative :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ c ≤ logProb {N | syrMin N ≤ N₀} (oddInterval x) := by
  sorry

/-- **Theorem 1.6** (Tao 2019 p.4): for `f` with `f(N) → ∞`, almost all odd `N`
(log density on the odd window) satisfy `Syrmin(N) < f(N)`. -/
-- RATIFY-C6c (domain-of-`f` rendering flagged in the module docstring)
theorem tao_syracuse (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) :
    AlmostAllOdd fun N => (syrMin N : ℝ) < f N := by
  sorry

/-! ## The (1.2) odd-part reduction — bridge lemmas

Worker-authored internal decomposition (below the C6 pin, not paper-numbered displays):
the two forms of "by (1.2), pass to odd parts" used on p.5 (Thm 1.6 ⟹ Thm 1.3) and
p.16 ("In particular, by (1.2)…"). Both rest on the PROVED `colMin_eq_syrMin_oddPart`
and the 2-adic splitting `∑_{N ≤ x, oddPart N ∈ A} 1/N = ∑_a 2^{-a} ∑_{M ∈ A ∩ 2ℕ+1,
2^a M ≤ x} 1/M ≤ 2 ∑_{M ∈ A ∩ 2ℕ+1 ∩ [1,x]} 1/M`. -/

/-- Quantitative (1.2) pullback: the full-window log-mass of an odd-part preimage is at
most twice the odd-window log-mass of the set (geometric series over `ν₂`). Feeds the
Colmin forms of Thm 3.1 from the Syracuse forms. -/
theorem logSum_oddPart_pullback (A : Set ℕ) (x : ℕ) :
    logSum {N | oddPart N ∈ A} (posInterval x) ≤ 2 * logSum A (oddInterval x) := by
  classical
  unfold logSum
  set S := (posInterval x).filter (· ∈ {N | oddPart N ∈ A}) with hSdef
  set T := (oddInterval x).filter (· ∈ A) with hTdef
  have hmem : ∀ N ∈ S, 1 ≤ N ∧ N ≤ x ∧ oddPart N ∈ A := by
    intro N hN
    simp only [hSdef, posInterval, Finset.mem_filter, Finset.mem_range,
      Set.mem_setOf_eq, ge_iff_le] at hN
    exact ⟨hN.1.2, by omega, hN.2⟩
  -- reindex `N ↦ (ν₂ N, oddPart N)`; recover `N` via `2^{ν₂ N}·oddPart N = N`
  have hinj : ∀ a ∈ S, ∀ b ∈ S,
      (fun N => (padicValNat 2 N, oddPart N)) a
        = (fun N => (padicValNat 2 N, oddPart N)) b → a = b := by
    intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    rw [← two_pow_mul_oddPart a, ← two_pow_mul_oddPart b, hab.1, hab.2]
  have hmaps : ∀ N ∈ S, (padicValNat 2 N, oddPart N) ∈ Finset.range (x + 1) ×ˢ T := by
    intro N hN
    obtain ⟨h1, hxle, hA⟩ := hmem N hN
    have h0 : 0 < N := h1
    have hMle : oddPart N ≤ x := le_trans (Nat.div_le_self _ _) hxle
    have hvle : padicValNat 2 N ≤ x := by
      have h2 : 2 ^ padicValNat 2 N ≤ N := Nat.le_of_dvd h0 (pow_padicValNat_two_dvd N)
      have h3 : padicValNat 2 N < 2 ^ padicValNat 2 N := Nat.lt_two_pow_self
      omega
    simp only [Finset.mem_product, Finset.mem_range, hTdef, oddInterval,
      Finset.mem_filter, Set.mem_setOf_eq]
    exact ⟨by omega, ⟨by omega, oddPart_odd h0⟩, hA⟩
  have hTnn : (0 : ℝ) ≤ ∑ M ∈ T, (1 : ℝ) / M :=
    Finset.sum_nonneg fun M _ => by positivity
  calc ∑ N ∈ S, (1 : ℝ) / N
      = ∑ p ∈ S.image fun N => (padicValNat 2 N, oddPart N),
          (1 : ℝ) / ((2 : ℝ) ^ p.1 * p.2) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun N hN => ?_
        have hNR : (N : ℝ) = (2 : ℝ) ^ padicValNat 2 N * (oddPart N : ℝ) := by
          exact_mod_cast (two_pow_mul_oddPart N).symm
        rw [hNR]
    _ ≤ ∑ p ∈ Finset.range (x + 1) ×ˢ T, (1 : ℝ) / ((2 : ℝ) ^ p.1 * p.2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => by positivity
        intro p hp
        obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hp
        exact hmaps N hN
    _ = (∑ a ∈ Finset.range (x + 1), (1 / 2 : ℝ) ^ a) * ∑ M ∈ T, (1 : ℝ) / M := by
        rw [Finset.sum_product, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [div_pow, one_pow]; field_simp
    _ ≤ 2 * ∑ M ∈ T, (1 : ℝ) / M := by
        refine mul_le_mul_of_nonneg_right ?_ hTnn
        rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
        have hpnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (x + 1) := by positivity
        have hid : ((1 / 2 : ℝ) ^ (x + 1) - 1) / (1 / 2 - 1)
            = 2 - 2 * (1 / 2 : ℝ) ^ (x + 1) := by ring
        rw [hid]; linarith

/-- Qualitative (1.2) reduction (paper p.5, ¶ after Thm 1.6): an almost-all-odd property
pulls back along `oddPart` to an almost-all property on `ℕ+`. -/
theorem almostAllPos_oddPart_of_almostAllOdd (P : ℕ → Prop) (h : AlmostAllOdd P) :
    AlmostAllPos fun N => P (oddPart N) := by
  sorry

/-! ## Spine — the headlines from the intermediates

Sorried wiring theorems, byte-identical in statement to the two frozen
`Statement.lean` headlines. When these close, the frozen sorries discharge by `exact`
(the ONLY edit `Statement.lean` ever receives). Proof routes, per §3:
* quantitative spine: `tao_syracuse_quantitative_sum` + `logSum_oddPart_pullback` +
  `colMin_eq_syrMin_oddPart` + harmonic-mass bounds on `posInterval`.
* headline spine: apply `tao_syracuse` at `f̃(M) := inf {f N | N ≥ M}` (which still
  `→ ∞`), then `almostAllPos_oddPart_of_almostAllOdd` + `oddPart N ≤ N` gives
  `colMin N = syrMin (oddPart N) < f̃ (oddPart N) ≤ f N`. -/

/-- Spine for **Theorem 1.3**: statement identical to the frozen `tao_collatz`. -/
theorem tao_collatz_spine (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) :
    AlmostAllPos fun N => (colMin N : ℝ) < f N := by
  sorry

/-- Spine for **Theorem 3.1 (Colmin form)**: statement identical to the frozen
`tao_collatz_quantitative`. -/
theorem tao_collatz_quantitative_spine :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ c ≤ logProb {N | colMin N ≤ N₀} (posInterval x) := by
  sorry

end TaoCollatz
