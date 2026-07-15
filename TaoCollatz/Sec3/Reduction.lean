import TaoCollatz.Basic.Collatz
import TaoCollatz.Basic.LogDensity
import TaoCollatz.Sec5.Stabilization
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

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

/-- **Ladder iteration** of `descentProb_step` from `descentProb_base` (p.18 top): climbing
`j` scales up from a base scale `y ≤ N₀` costs the base error plus a geometric error sum
`∑_{i<j} (α^{-c})^i · (log y)^{-c}`. The scale after `j` climbs is `y^{α^j}`. -/
theorem descentProb_ladder :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ : ℕ, ∀ y : ℝ, x₀ ≤ y → y ≤ (N₀ : ℝ) → ∀ j : ℕ,
      1 - C * y ^ (-c)
        - C * (Real.log y) ^ (-c) * ∑ i ∈ Finset.range j, (alpha ^ (-c)) ^ i
        ≤ descentProb ⌊y ^ (alpha ^ j)⌋₊ ((y ^ (alpha ^ j)) ^ alpha) N₀ := by
  obtain ⟨cb, Cb, xb, hcb, hCb, hbase⟩ := descentProb_base
  obtain ⟨cs, Cs, xs, hcs, hCs, hstep⟩ := descentProb_step
  set c := min cb cs with hcdef
  have hc : 0 < c := lt_min hcb hcs
  set C := max Cb Cs with hCdef
  have hC : 0 < C := lt_of_lt_of_le hCb (le_max_left _ _)
  refine ⟨c, C, max (max xb xs) (Real.exp 1), hc, hC, fun N₀ y hy hyN j => ?_⟩
  have hyb : xb ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hys : xs ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hye : Real.exp 1 ≤ y := le_trans (le_max_right _ _) hy
  have hy1 : (1 : ℝ) ≤ y := by
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr zero_le_one
      _ ≤ y := hye
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy1
  have hL1 : (1 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hye
  have hL0 : (0 : ℝ) < Real.log y := lt_of_lt_of_le one_pos hL1
  have hN₀1 : 1 ≤ N₀ := by exact_mod_cast le_trans hy1 hyN
  have halpha1 : (1 : ℝ) ≤ alpha := by norm_num [alpha]
  have halpha0 : (0 : ℝ) < alpha := by norm_num [alpha]
  -- scale monotonicity: `y ≤ y^{α^j}`, and every ladder scale clears the thresholds
  have hpow1 : ∀ i : ℕ, (1 : ℝ) ≤ alpha ^ i := fun i => one_le_pow₀ halpha1
  have hscale : ∀ i : ℕ, y ≤ y ^ (alpha ^ i) := by
    intro i
    calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
      _ ≤ y ^ (alpha ^ i) := Real.rpow_le_rpow_of_exponent_le hy1 (hpow1 i)
  induction j with
  | zero =>
    have hb := hbase y hyb N₀ hyN
    have h0 : y ^ (alpha ^ (0 : ℕ)) = y := by rw [pow_zero, Real.rpow_one]
    rw [h0, Finset.sum_range_zero, mul_zero, sub_zero]
    have herr : Cb * y ^ (-cb) ≤ C * y ^ (-c) := by
      refine mul_le_mul (le_max_left _ _) ?_ (Real.rpow_nonneg hy0.le _) hC.le
      exact Real.rpow_le_rpow_of_exponent_le hy1 (by simp [hcdef, neg_le_neg_iff, min_le_left])
    linarith
  | succ j ih =>
    -- one `descentProb_step` at scale `x = y^{α^j}`
    have hxstep : xs ≤ y ^ (alpha ^ j) := le_trans hys (hscale j)
    have hs := hstep (y ^ (alpha ^ j)) hxstep N₀ hN₀1
    -- scale identities
    have hup : (y ^ (alpha ^ j)) ^ alpha = y ^ (alpha ^ (j + 1)) := by
      rw [← Real.rpow_mul hy0.le]
      congr 1
    have hup2 : (y ^ (alpha ^ j)) ^ (alpha ^ 2) = (y ^ (alpha ^ (j + 1))) ^ alpha := by
      rw [← Real.rpow_mul hy0.le, ← Real.rpow_mul hy0.le]
      congr 1
      ring
    rw [hup, hup2] at hs
    rw [hup] at ih
    -- error conversion: `Cs·(log y^{α^j})^{-cs} ≤ C·(α^{-c})^j·(log y)^{-c}`
    have hlogx : Real.log (y ^ (alpha ^ j)) = alpha ^ j * Real.log y :=
      Real.log_rpow hy0 _
    have hbase1 : (1 : ℝ) ≤ alpha ^ j * Real.log y := by
      nlinarith [hpow1 j, hL1]
    have hgeom : ((alpha ^ j : ℝ)) ^ (-c) = (alpha ^ (-c)) ^ j := by
      rw [← Real.rpow_natCast alpha j, ← Real.rpow_natCast (alpha ^ (-c)) j,
        ← Real.rpow_mul halpha0.le, ← Real.rpow_mul halpha0.le]
      congr 1
      ring
    have herrstep : Cs * Real.log (y ^ (alpha ^ j)) ^ (-cs)
        ≤ C * ((alpha ^ (-c)) ^ j * Real.log y ^ (-c)) := by
      rw [hlogx]
      have h1 : (alpha ^ j * Real.log y) ^ (-cs) ≤ (alpha ^ j * Real.log y) ^ (-c) :=
        Real.rpow_le_rpow_of_exponent_le hbase1 (neg_le_neg (min_le_right cb cs))
      have h2 : (alpha ^ j * Real.log y) ^ (-c)
          = (alpha ^ (-c)) ^ j * Real.log y ^ (-c) := by
        rw [Real.mul_rpow (pow_nonneg halpha0.le j) hL0.le, hgeom]
      have h3 : (0 : ℝ) ≤ (alpha ^ (-c)) ^ j * Real.log y ^ (-c) := by positivity
      calc Cs * (alpha ^ j * Real.log y) ^ (-cs)
          ≤ Cs * (alpha ^ j * Real.log y) ^ (-c) :=
            mul_le_mul_of_nonneg_left h1 hCs.le
        _ = Cs * ((alpha ^ (-c)) ^ j * Real.log y ^ (-c)) := by rw [h2]
        _ ≤ C * ((alpha ^ (-c)) ^ j * Real.log y ^ (-c)) :=
            mul_le_mul_of_nonneg_right (le_max_right Cb Cs) h3
    rw [Finset.sum_range_succ, mul_add, mul_comm (C * Real.log y ^ (-c)) ((alpha ^ (-c)) ^ j)]
    have := herrstep
    have hCL : C * Real.log y ^ (-c) * (alpha ^ (-c)) ^ j
        = C * ((alpha ^ (-c)) ^ j * Real.log y ^ (-c)) := by ring
    linarith [hs, ih]

/-- **Telescope** (p.18 top): iterating `descentProb_step` down `J ≈ log_α(log x/log N₀)`
scales from the base `y < N₀^{1/α}` and summing `∑_j (α^j log y)^{-c} ≪ log^{-c} N₀` gives
`ℙ(B_{x^{1/α}}) ≥ 1 − O(log^{-c}N₀)` — the window `[x, x^α]`, threshold `⌊x^{1/α}⌋`. -/
theorem descent_whp :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ : ℕ, ∀ x : ℝ, x₀ ≤ x → x₀ ≤ (N₀ : ℝ) →
      (N₀ : ℝ) ≤ x →
      1 - C * (Real.log N₀) ^ (-c) ≤ descentProb ⌊x ^ (alpha⁻¹)⌋₊ x N₀ := by
  obtain ⟨c, Cl, xl, hc, hCl, hlad⟩ := descentProb_ladder
  have halpha1 : (1 : ℝ) < alpha := by norm_num [alpha]
  have halpha0 : (0 : ℝ) < alpha := by linarith
  set r := alpha ^ (-c) with hrdef
  have hr0 : (0 : ℝ) < r := Real.rpow_pos_of_pos halpha0 _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg halpha1 (by linarith)
  have hr1' : (0 : ℝ) < 1 - r := by linarith
  set A := max xl (Real.exp 1) with hAdef
  have hAe : Real.exp 1 ≤ A := le_max_right _ _
  have hA1 : (1 : ℝ) ≤ A := by
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr zero_le_one
      _ ≤ A := hAe
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA1
  refine ⟨c, Cl * (1 + (1 - r)⁻¹) * alpha ^ c,
    max (A ^ alpha) (Real.exp 1), hc, ?_, fun N₀ x hx hN₀lb hN₀x => ?_⟩
  · have h1r : (0 : ℝ) < (1 - r)⁻¹ := by positivity
    have hac : (0 : ℝ) < alpha ^ c := Real.rpow_pos_of_pos halpha0 _
    positivity
  -- basic sizes
  · have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
    have hx1 : (1 : ℝ) ≤ x := by
      calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
        _ ≤ Real.exp 1 := Real.exp_le_exp.mpr zero_le_one
        _ ≤ x := hxe
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
    have hN₀e : Real.exp 1 ≤ (N₀ : ℝ) := le_trans (le_max_right _ _) hN₀lb
    have hN₀0 : (0 : ℝ) < (N₀ : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hN₀e
    have hLN1 : (1 : ℝ) ≤ Real.log N₀ := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN₀e
    have hLN0 : (0 : ℝ) < Real.log N₀ := lt_of_lt_of_le one_pos hLN1
    have hAα : A ^ alpha ≤ (N₀ : ℝ) := le_trans (le_max_left _ _) hN₀lb
    -- the base-window scale `z = x^{1/α}` and its log
    set z := x ^ (alpha⁻¹) with hzdef
    have hz0 : (0 : ℝ) < z := Real.rpow_pos_of_pos hx0 _
    have hlogz : Real.log z = alpha⁻¹ * Real.log x := Real.log_rpow hx0 _
    have hlogx_ge : Real.log N₀ ≤ Real.log x := Real.log_le_log hN₀0 hN₀x
    have hlogz_lb : Real.log N₀ / alpha ≤ Real.log z := by
      rw [hlogz, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hlogx_ge (by positivity)
    have hlogz0 : (0 : ℝ) < Real.log z := lt_of_lt_of_le (by positivity) hlogz_lb
    -- pick the number of ladder steps
    set R := Real.log z / Real.log N₀ with hRdef
    have hR0 : (0 : ℝ) < R := by positivity
    set j := ⌈Real.logb alpha R⌉₊ with hjdef
    have hαt : alpha ^ Real.logb alpha R = R :=
      Real.rpow_logb halpha0 (ne_of_gt halpha1) hR0
    have hαjR : R ≤ alpha ^ j := by
      calc R = alpha ^ Real.logb alpha R := hαt.symm
        _ ≤ alpha ^ ((j : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le halpha1.le (Nat.le_ceil _)
        _ = alpha ^ j := Real.rpow_natCast alpha j
    have hpj0 : (0 : ℝ) < alpha ^ j := pow_pos halpha0 j
    -- the base scale `y = z^{α^{-j}}`
    set y := z ^ ((alpha ^ j : ℝ)⁻¹) with hydef
    have hy0 : (0 : ℝ) < y := Real.rpow_pos_of_pos hz0 _
    have hyz : y ^ (alpha ^ j) = z := by
      rw [hydef, ← Real.rpow_mul hz0.le, inv_mul_cancel₀ hpj0.ne', Real.rpow_one]
    have hlogy : Real.log y = (alpha ^ j : ℝ)⁻¹ * Real.log z := Real.log_rpow hz0 _
    -- `y ≤ N₀`
    have hzR : Real.log z = R * Real.log N₀ := by rw [hRdef]; field_simp
    have hyN₀ : y ≤ (N₀ : ℝ) := by
      have hlog_le : Real.log y ≤ Real.log N₀ := by
        rw [hlogy, hzR, inv_mul_le_iff₀ hpj0]
        exact mul_le_mul_of_nonneg_right hαjR hLN0.le
      exact (Real.log_le_log_iff hy0 hN₀0).mp hlog_le
    -- `log y ≥ log N₀ / α` (scale lands in `[N₀^{1/α}, N₀]`)
    have hlogy_lb : Real.log N₀ / alpha ≤ Real.log y := by
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · rw [hlogy, hj0, pow_zero, inv_one, one_mul]; exact hlogz_lb
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hjpos
        have hklt : (k : ℝ) < Real.logb alpha R := by
          have : k < j := by omega
          exact_mod_cast Nat.lt_ceil.mp (by rw [← hjdef]; exact this)
        have hαk : (alpha : ℝ) ^ k < R := by
          calc (alpha : ℝ) ^ k = alpha ^ ((k : ℕ) : ℝ) := (Real.rpow_natCast alpha k).symm
            _ < alpha ^ Real.logb alpha R := by
                exact Real.rpow_lt_rpow_of_exponent_lt halpha1 hklt
            _ = R := hαt
        have hjk : j = k + 1 := by omega
        rw [hlogy, hjk, pow_succ, hzR]
        have hαk' : (alpha : ℝ) ^ k ≤ R := hαk.le
        have hposk : (0 : ℝ) < alpha ^ k := pow_pos halpha0 k
        have key : Real.log N₀ / alpha
            = (alpha ^ k * alpha)⁻¹ * (alpha ^ k * Real.log N₀) := by
          field_simp
        refine le_trans (le_of_eq key) ?_
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hαk' hLN0.le) (by positivity)
    -- `y ≥ A` (clears the ladder threshold and `e`)
    have hlogA : Real.log (A ^ alpha) = alpha * Real.log A := Real.log_rpow hA0 _
    have hlogN₀_A : alpha * Real.log A ≤ Real.log N₀ := by
      rw [← hlogA]; exact Real.log_le_log (by positivity) hAα
    have hyA : A ≤ y := by
      have : Real.log A ≤ Real.log y := by
        refine le_trans ?_ hlogy_lb
        rw [le_div_iff₀ halpha0]
        linarith
      exact (Real.log_le_log_iff hA0 hy0).mp this
    have hyxl : xl ≤ y := le_trans (le_max_left _ _) hyA
    have hye : Real.exp 1 ≤ y := le_trans hAe hyA
    have hLy1 : (1 : ℝ) ≤ Real.log y := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hye
    have hLy0 : (0 : ℝ) < Real.log y := lt_of_lt_of_le one_pos hLy1
    -- the ladder
    have hlad' := hlad N₀ y hyxl hyN₀ j
    have hz2 : z ^ alpha = x := by
      rw [hzdef, ← Real.rpow_mul hx0.le, inv_mul_cancel₀ (ne_of_gt halpha0),
        Real.rpow_one]
    rw [hyz, hz2] at hlad'
    -- error algebra: geometric sum + scale conversion to `log N₀`
    have hgeom : ∑ i ∈ Finset.range j, r ^ i ≤ (1 - r)⁻¹ := by
      rw [geom_sum_eq hr1.ne j]
      rw [div_le_iff_of_neg (by linarith : r - 1 < 0)]
      have : (0 : ℝ) ≤ r ^ j := pow_nonneg hr0.le j
      have hexp : (1 - r)⁻¹ * (r - 1) = -1 := by
        field_simp
        ring
      rw [hexp]; linarith
    have hyc : y ^ (-c) ≤ Real.log y ^ (-c) := by
      rw [Real.rpow_neg hy0.le, Real.rpow_neg hLy0.le]
      refine inv_anti₀ (Real.rpow_pos_of_pos hLy0 _) ?_
      exact Real.rpow_le_rpow hLy0.le (Real.log_le_self hy0.le) hc.le
    have hLyN : Real.log y ^ (-c) ≤ alpha ^ c * Real.log N₀ ^ (-c) := by
      have h1 : Real.log N₀ / alpha ≤ Real.log y := hlogy_lb
      have h2 : (0 : ℝ) < Real.log N₀ / alpha := by positivity
      have h3 : Real.log y ^ (-c) ≤ (Real.log N₀ / alpha) ^ (-c) := by
        rw [Real.rpow_neg hLy0.le, Real.rpow_neg h2.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos h2 _)
          (Real.rpow_le_rpow h2.le h1 hc.le)
      refine le_trans h3 (le_of_eq ?_)
      rw [Real.div_rpow hLN0.le halpha0.le, div_eq_mul_inv, ← Real.rpow_neg halpha0.le,
        neg_neg, mul_comm]
    -- assemble
    have hLyc0 : (0 : ℝ) ≤ Real.log y ^ (-c) := Real.rpow_nonneg hLy0.le _
    have hsum0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range j, r ^ i :=
      Finset.sum_nonneg fun i _ => pow_nonneg hr0.le i
    have herr : Cl * y ^ (-c) + Cl * Real.log y ^ (-c) * ∑ i ∈ Finset.range j, r ^ i
        ≤ Cl * (1 + (1 - r)⁻¹) * alpha ^ c * Real.log N₀ ^ (-c) := by
      have e1 : Cl * y ^ (-c) ≤ Cl * Real.log y ^ (-c) :=
        mul_le_mul_of_nonneg_left hyc hCl.le
      have e2 : Cl * Real.log y ^ (-c) * ∑ i ∈ Finset.range j, r ^ i
          ≤ Cl * Real.log y ^ (-c) * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
      have e3 : Cl * Real.log y ^ (-c) + Cl * Real.log y ^ (-c) * (1 - r)⁻¹
          = Cl * (1 + (1 - r)⁻¹) * Real.log y ^ (-c) := by ring
      have e4 : Cl * (1 + (1 - r)⁻¹) * Real.log y ^ (-c)
          ≤ Cl * (1 + (1 - r)⁻¹) * (alpha ^ c * Real.log N₀ ^ (-c)) := by
        refine mul_le_mul_of_nonneg_left hLyN ?_
        have : (0 : ℝ) < (1 - r)⁻¹ := by positivity
        positivity
      calc Cl * y ^ (-c) + Cl * Real.log y ^ (-c) * ∑ i ∈ Finset.range j, r ^ i
          ≤ Cl * Real.log y ^ (-c) + Cl * Real.log y ^ (-c) * (1 - r)⁻¹ := by
            linarith
        _ = Cl * (1 + (1 - r)⁻¹) * Real.log y ^ (-c) := e3
        _ ≤ Cl * (1 + (1 - r)⁻¹) * (alpha ^ c * Real.log N₀ ^ (-c)) := e4
        _ = Cl * (1 + (1 - r)⁻¹) * alpha ^ c * Real.log N₀ ^ (-c) := by ring
    linarith [hlad']

/-- **Window bad-mass** ((3.1), p.18): on any window `[x, x^α]` with `N₀ ≤ x`, the harmonic
mass of `{Syrmin > N₀}` is `≪ log^{-c}N₀ · log x`. From `descent_whp` +
`syrMin_le_of_descentEvent` + `logUnifOdd_expect_indicator` + `windowMass_le_half_log`. -/
theorem window_bad_sum :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ : ℕ, ∀ x : ℝ, x₀ ≤ x → x₀ ≤ (N₀ : ℝ) →
      (N₀ : ℝ) ≤ x →
      ∑ N ∈ (logWindow x (x ^ alpha)).filter (· ∈ {N | N₀ < syrMin N}), (N : ℝ)⁻¹
        ≤ C * (Real.log N₀) ^ (-c) * Real.log x := by
  classical
  obtain ⟨c, C, x₀d, hc, hC, hwhp⟩ := descent_whp
  obtain ⟨x₀z, hnonempty⟩ := logWindow_nonempty_of_large
  have halpha0 : (0 : ℝ) < alpha := by norm_num [alpha]
  have halpha1 : (1 : ℝ) < alpha := by norm_num [alpha]
  set M := max x₀z 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  refine ⟨c, 2 * C, max (max x₀d (M ^ alpha)) (Real.exp 1), hc, by linarith,
    fun N₀ x hx hN₀lb hN₀x => ?_⟩
  -- basic sizes
  have hxd : x₀d ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hN₀d : x₀d ≤ (N₀ : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN₀lb
  have hxMα : M ^ alpha ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) ≤ x := by
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr zero_le_one
      _ ≤ x := hxe
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hlogx0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le one_pos hlogx1
  have hN₀e : Real.exp 1 ≤ (N₀ : ℝ) := le_trans (le_max_right _ _) hN₀lb
  have hN₀0 : (0 : ℝ) < (N₀ : ℝ) := lt_of_lt_of_le (Real.exp_pos 1) hN₀e
  have hLN1 : (1 : ℝ) ≤ Real.log N₀ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN₀e
  have hLN0 : (0 : ℝ) < Real.log N₀ := lt_of_lt_of_le one_pos hLN1
  have hLNc : (0 : ℝ) ≤ (Real.log N₀) ^ (-c) := Real.rpow_nonneg hLN0.le _
  have hxa : x ≤ x ^ alpha := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ alpha := Real.rpow_le_rpow_of_exponent_le hx1 halpha1.le
  -- window nonemptiness, via the `x' = x^{1/α}` reparametrization
  have hxid : (x ^ alpha⁻¹) ^ alpha = x := by
    rw [← Real.rpow_mul hx0.le, inv_mul_cancel₀ halpha0.ne', Real.rpow_one]
  have hx'M : M ≤ x ^ alpha⁻¹ := by
    have h1 : (M ^ alpha) ^ alpha⁻¹ ≤ x ^ alpha⁻¹ :=
      Real.rpow_le_rpow (by positivity) hxMα (by positivity)
    rwa [← Real.rpow_mul hM0.le, mul_inv_cancel₀ halpha0.ne', Real.rpow_one] at h1
  have hx'z : x₀z ≤ x ^ alpha⁻¹ := le_trans (le_max_left _ _) hx'M
  have hne : (logWindow x (x ^ alpha)).Nonempty := by
    have := hnonempty (x ^ alpha⁻¹) hx'z ((x ^ alpha⁻¹) ^ alpha) (Set.mem_insert _ _)
    rwa [hxid] at this
  -- window mass: positive, and `≤ 2 log x`
  have hmass_pos : (0 : ℝ) < windowMass x (x ^ alpha) := by
    refine Finset.sum_pos (fun N hN => ?_) hne
    have hodd : N % 2 = 1 := (mem_logWindow_iff.mp hN).1
    have : (0 : ℕ) < N := by omega
    positivity
  have hmass_ub : windowMass x (x ^ alpha) ≤ 2 * Real.log x := by
    have h1 := windowMass_le_half_log hx1 hxa
    have hlogdiv : Real.log (x ^ alpha / x) = (alpha - 1) * Real.log x := by
      rw [Real.log_div (by positivity) hx0.ne', Real.log_rpow hx0]; ring
    have hx2 : (2 : ℝ) ≤ x := by
      have : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 1
        linarith
      linarith [hxe]
    have h2x : 2 / x ≤ 1 := by
      rw [div_le_one hx0]; exact hx2
    have halphale : alpha - 1 ≤ 2 := by norm_num [alpha]
    calc windowMass x (x ^ alpha) ≤ (1/2) * ((alpha - 1) * Real.log x) + 2 / x := by
          rw [← hlogdiv]; exact h1
      _ ≤ (1/2) * (2 * Real.log x) + 1 := by
          have := mul_le_mul_of_nonneg_right halphale hlogx0.le
          linarith
      _ ≤ 2 * Real.log x := by linarith
  -- the descent-event complement has probability ≤ C·(log N₀)^{-c}
  set B := descentEvent ⌊x ^ alpha⁻¹⌋₊ N₀ with hBdef
  have hwhp' := hwhp N₀ x hxd hN₀d hN₀x
  have hcompl : (logUnifOdd x (x ^ alpha)).expect (Set.indicator Bᶜ 1)
      ≤ C * (Real.log N₀) ^ (-c) := by
    have heq := expect_indicator_compl (logUnifOdd x (x ^ alpha)) B
    unfold descentProb at hwhp'
    linarith [heq, hwhp']
  -- convert to the reciprocal-sum form
  have hexpect_eq := logUnifOdd_expect_indicator_eq hne Bᶜ
  have hsum_compl : ∑ N ∈ (logWindow x (x ^ alpha)).filter (fun N => N ∈ Bᶜ), (N : ℝ)⁻¹
      ≤ C * (Real.log N₀) ^ (-c) * windowMass x (x ^ alpha) := by
    rw [hexpect_eq, div_le_iff₀ hmass_pos] at hcompl
    convert hcompl using 3
    rfl
  -- bad set ⊆ complement of the descent event
  have hsubset : (logWindow x (x ^ alpha)).filter (· ∈ {N | N₀ < syrMin N})
      ⊆ (logWindow x (x ^ alpha)).filter (fun N => N ∈ Bᶜ) := by
    intro N hN
    rw [Finset.mem_filter] at hN ⊢
    refine ⟨hN.1, fun hmem => ?_⟩
    have h1 : syrMin N ≤ N₀ := syrMin_le_of_descentEvent hmem
    have h2 : N₀ < syrMin N := hN.2
    omega
  have hbad_le : ∑ N ∈ (logWindow x (x ^ alpha)).filter (· ∈ {N | N₀ < syrMin N}), (N : ℝ)⁻¹
      ≤ ∑ N ∈ (logWindow x (x ^ alpha)).filter (fun N => N ∈ Bᶜ), (N : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset fun N _ _ => by positivity
  -- assemble
  calc ∑ N ∈ (logWindow x (x ^ alpha)).filter (· ∈ {N | N₀ < syrMin N}), (N : ℝ)⁻¹
      ≤ C * (Real.log N₀) ^ (-c) * windowMass x (x ^ alpha) := le_trans hbad_le hsum_compl
    _ ≤ C * (Real.log N₀) ^ (-c) * (2 * Real.log x) := by
        refine mul_le_mul_of_nonneg_left hmass_ub ?_
        positivity
    _ = 2 * C * (Real.log N₀) ^ (-c) * Real.log x := by ring

/-- **Theorem 3.1, Syracuse sum form** (Tao 2019 p.16, first display):
`∑_{N ∈ 2ℕ+1 ∩ [1,x], Syrmin(N) > N₀} 1/N ≪ log x / (log N₀)^c`. -/
-- RATIFY-C6a
theorem tao_syracuse_quantitative_sum :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      logSum {N | N₀ < syrMin N} (oddInterval x)
        ≤ C * Real.log x / (Real.log N₀) ^ c := by
  obtain ⟨c, Cw, xw, hc, hCw, hwbs⟩ := window_bad_sum
  have halpha1 : (1 : ℝ) < alpha := by norm_num [alpha]
  have halpha0 : (0 : ℝ) < alpha := by linarith
  have hden : (0 : ℝ) < alpha - 1 := by linarith
  set X := max xw (Real.exp 1) with hXdef
  have hXe : Real.exp 1 ≤ X := le_max_right _ _
  have hX1 : (1 : ℝ) ≤ X := by
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr zero_le_one
      _ ≤ X := hXe
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX1
  set K1 := max 1 ((Real.log X) ^ c) with hK1def
  have hK11 : (1 : ℝ) ≤ K1 := le_max_left _ _
  set C := max (Cw * alpha / (alpha - 1)) (4 * K1) with hCdef
  have hC0 : (0 : ℝ) < C := by
    have h1 : (0 : ℝ) < Cw * alpha / (alpha - 1) := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  refine ⟨c, C, hc, hC0, fun N₀ x hN₀2 hx2 => ?_⟩
  -- common size facts
  have hx2R : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hlogx0 : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hN₀2R : (2 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀2
  have hN₀0 : (0 : ℝ) < (N₀ : ℝ) := by linarith
  have hLN0 : (0 : ℝ) < Real.log N₀ := Real.log_pos (by linarith)
  have hLc0 : (0 : ℝ) < (Real.log N₀) ^ c := Real.rpow_pos_of_pos hLN0 _
  by_cases hbig : X ≤ (N₀ : ℝ)
  · -- large N₀
    by_cases hxN : x ≤ N₀
    · -- bad set empty: every N in the window has `syrMin N ≤ N ≤ x ≤ N₀`
      have h0 : logSum {N | N₀ < syrMin N} (oddInterval x) ≤ 0 := by
        unfold logSum
        rw [Finset.sum_filter]
        refine le_of_eq (Finset.sum_eq_zero fun N hN => if_neg ?_)
        rw [oddInterval, Finset.mem_filter, Finset.mem_range] at hN
        simp only [Set.mem_setOf_eq, not_lt]
        have := syrMin_le_self N
        omega
      have hRHS : (0 : ℝ) ≤ C * Real.log x / (Real.log N₀) ^ c := by positivity
      linarith
    · -- covering argument over the windows `[N₀^{α^k}, N₀^{α^{k+1}}]`
      push_neg at hxN
      have hN₀x : (N₀ : ℝ) < (x : ℝ) := by exact_mod_cast hxN
      have hLxL : Real.log N₀ < Real.log x := Real.log_lt_log hN₀0 hN₀x
      set R := Real.log x / Real.log N₀ with hRdef
      have hR0 : (0 : ℝ) < R := by positivity
      have hR1 : (1 : ℝ) < R := (one_lt_div hLN0).mpr hLxL
      have hlogb0 : (0 : ℝ) < Real.logb alpha R := Real.logb_pos halpha1 hR1
      set K := ⌈Real.logb alpha R⌉₊ with hKdef
      set z : ℕ → ℝ := fun k => (N₀ : ℝ) ^ (alpha ^ k) with hzdef
      have hz0 : z 0 = (N₀ : ℝ) := by simp [hzdef]
      have hzpos : ∀ k, (0 : ℝ) < z k := fun k => Real.rpow_pos_of_pos hN₀0 _
      have hzsucc : ∀ k, (z k) ^ alpha = z (k + 1) := by
        intro k
        simp only [hzdef]
        rw [← Real.rpow_mul hN₀0.le, ← pow_succ]
      have hlogz : ∀ k, Real.log (z k) = alpha ^ k * Real.log N₀ := by
        intro k
        simp only [hzdef]
        rw [Real.log_rpow hN₀0]
      have hzN₀ : ∀ k, (N₀ : ℝ) ≤ z k := by
        intro k
        have h1 : (N₀ : ℝ) = (N₀ : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        rw [h1]
        simp only [hzdef]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith)
          (one_le_pow₀ halpha1.le)
      -- top window covers `x`
      have hzK : (x : ℝ) ≤ z K := by
        have hRK : R ≤ alpha ^ K := by
          calc R = alpha ^ Real.logb alpha R :=
                (Real.rpow_logb halpha0 (ne_of_gt halpha1) hR0).symm
            _ ≤ alpha ^ ((K : ℕ) : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le halpha1.le (Nat.le_ceil _)
            _ = alpha ^ K := Real.rpow_natCast alpha K
        have hlog_le : Real.log x ≤ Real.log (z K) := by
          rw [hlogz K]
          calc Real.log x = R * Real.log N₀ := by rw [hRdef]; field_simp
            _ ≤ alpha ^ K * Real.log N₀ :=
                mul_le_mul_of_nonneg_right hRK hLN0.le
        exact (Real.log_le_log_iff hx0 (hzpos K)).mp hlog_le
      -- every bad `N` lands in some window
      have hstep : ∀ m : ℕ, ∀ N : ℕ, (N₀ : ℝ) < (N : ℝ) → (N : ℝ) ≤ z m →
          ∃ k, k < m ∧ z k ≤ (N : ℝ) ∧ (N : ℝ) ≤ z (k + 1) := by
        intro m
        induction m with
        | zero =>
          intro N hlt hle
          rw [hz0] at hle
          exact absurd hle (not_le.mpr hlt)
        | succ m ih =>
          intro N hlt hle
          rcases le_or_gt (z m) (N : ℝ) with hzm | hzm
          · exact ⟨m, Nat.lt_succ_self m, hzm, hle⟩
          · obtain ⟨k, hk, h1, h2⟩ := ih N hlt hzm.le
            exact ⟨k, Nat.lt_succ_of_lt hk, h1, h2⟩
      set W : ℕ → Finset ℕ :=
        fun k => (logWindow (z k) ((z k) ^ alpha)).filter (· ∈ {N | N₀ < syrMin N})
        with hWdef
      -- per-window bad-mass bound
      have hwin : ∀ k, ∑ N ∈ W k, ((N : ℝ))⁻¹
          ≤ Cw * (Real.log N₀) ^ (-c) * (alpha ^ k * Real.log N₀) := by
        intro k
        have hXzk : X ≤ z k := le_trans hbig (hzN₀ k)
        have hxwzk : xw ≤ z k := le_trans (le_max_left _ _) hXzk
        have hxwN₀ : xw ≤ (N₀ : ℝ) := le_trans (le_max_left _ _) hbig
        have := hwbs N₀ (z k) hxwzk hxwN₀ (hzN₀ k)
        rw [hlogz k] at this
        exact this
      -- cover: bad filter ⊆ ⋃_{k<K} W k
      have hsubset : (oddInterval x).filter (· ∈ {N | N₀ < syrMin N})
          ⊆ (Finset.range K).biUnion W := by
        intro N hN
        rw [Finset.mem_filter] at hN
        obtain ⟨hNi, hNbad⟩ := hN
        rw [oddInterval, Finset.mem_filter, Finset.mem_range] at hNi
        have hNbad' : N₀ < syrMin N := hNbad
        have hNN₀ : N₀ < N := lt_of_lt_of_le hNbad' (syrMin_le_self N)
        have hNlt : (N₀ : ℝ) < (N : ℝ) := by exact_mod_cast hNN₀
        have hNx : (N : ℝ) ≤ (x : ℝ) := by
          have : N ≤ x := by omega
          exact_mod_cast this
        obtain ⟨k, hkK, hzk, hzk1⟩ := hstep K N hNlt (le_trans hNx hzK)
        rw [Finset.mem_biUnion]
        refine ⟨k, Finset.mem_range.mpr hkK, ?_⟩
        rw [hWdef, Finset.mem_filter]
        refine ⟨mem_logWindow_iff.mpr ⟨hNi.2, hzk, ?_⟩, hNbad⟩
        rw [hzsucc k]
        exact hzk1
      -- sum over an overlapping cover is at most the sum of window sums
      have hbiu : ∀ u : Finset ℕ, ∑ N ∈ u.biUnion W, ((N : ℝ))⁻¹
          ≤ ∑ k ∈ u, ∑ N ∈ W k, ((N : ℝ))⁻¹ := by
        intro u
        induction u using Finset.induction_on with
        | empty => simp
        | insert a u ha ih =>
          rw [Finset.biUnion_insert, Finset.sum_insert ha]
          have hui := Finset.sum_union_inter (s₁ := W a) (s₂ := u.biUnion W)
            (f := fun N : ℕ => ((N : ℝ))⁻¹)
          have hnn : (0 : ℝ) ≤ ∑ N ∈ (W a) ∩ (u.biUnion W), ((N : ℝ))⁻¹ :=
            Finset.sum_nonneg fun N _ => by positivity
          linarith [ih]
      -- geometric sum
      have hgeom : ∑ k ∈ Finset.range K, (alpha : ℝ) ^ k ≤ alpha * R / (alpha - 1) := by
        have hK_le : (alpha : ℝ) ^ K ≤ alpha * R := by
          have h1 : ((K : ℕ) : ℝ) < Real.logb alpha R + 1 :=
            Nat.ceil_lt_add_one hlogb0.le
          calc (alpha : ℝ) ^ K = alpha ^ ((K : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
            _ ≤ alpha ^ (Real.logb alpha R + 1) :=
                Real.rpow_le_rpow_of_exponent_le halpha1.le h1.le
            _ = alpha * R := by
                rw [Real.rpow_add halpha0,
                  Real.rpow_logb halpha0 (ne_of_gt halpha1) hR0, Real.rpow_one]
                ring
        rw [geom_sum_eq (ne_of_gt halpha1) K, div_le_div_iff_of_pos_right hden]
        linarith [hK_le]
      -- assemble
      have hL_neg : (Real.log N₀) ^ (-c) = ((Real.log N₀) ^ c)⁻¹ :=
        Real.rpow_neg hLN0.le c
      have hLc : (0 : ℝ) ≤ (Real.log N₀) ^ (-c) := Real.rpow_nonneg hLN0.le _
      have hchain : logSum {N | N₀ < syrMin N} (oddInterval x)
          ≤ Cw * (Real.log N₀) ^ (-c) * Real.log N₀ * ∑ k ∈ Finset.range K, alpha ^ k := by
        unfold logSum
        simp_rw [one_div]
        rw [Finset.filter_congr_decidable]
        calc ∑ N ∈ (oddInterval x).filter (· ∈ {N | N₀ < syrMin N}), ((N : ℝ))⁻¹
            ≤ ∑ N ∈ (Finset.range K).biUnion W, ((N : ℝ))⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg hsubset fun N _ _ => by positivity
          _ ≤ ∑ k ∈ Finset.range K, ∑ N ∈ W k, ((N : ℝ))⁻¹ := hbiu _
          _ ≤ ∑ k ∈ Finset.range K,
                Cw * (Real.log N₀) ^ (-c) * (alpha ^ k * Real.log N₀) :=
              Finset.sum_le_sum fun k _ => hwin k
          _ = Cw * (Real.log N₀) ^ (-c) * Real.log N₀ * ∑ k ∈ Finset.range K, alpha ^ k := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun k _ => by ring
      have hLR : Real.log N₀ * R = Real.log x := by
        rw [hRdef]; field_simp
      calc logSum {N | N₀ < syrMin N} (oddInterval x)
          ≤ Cw * (Real.log N₀) ^ (-c) * Real.log N₀ * ∑ k ∈ Finset.range K, alpha ^ k :=
            hchain
        _ ≤ Cw * (Real.log N₀) ^ (-c) * Real.log N₀ * (alpha * R / (alpha - 1)) := by
            refine mul_le_mul_of_nonneg_left hgeom ?_
            positivity
        _ = Cw * alpha / (alpha - 1) * Real.log x / (Real.log N₀) ^ c := by
            rw [hL_neg, ← hLR]
            field_simp
        _ ≤ C * Real.log x / (Real.log N₀) ^ c := by
            have hAC : Cw * alpha / (alpha - 1) ≤ C := le_max_left _ _
            gcongr
  · -- small `N₀ < X`: trivial harmonic bound `logSum ≤ windowMass 1 x ≤ 4 log x`
    push_neg at hbig
    have hLK : (Real.log N₀) ^ c ≤ K1 := by
      have hNX : Real.log N₀ ≤ Real.log X := Real.log_le_log hN₀0 hbig.le
      rcases le_or_gt (Real.log N₀) 1 with hL1 | hL1
      · exact le_trans (Real.rpow_le_one hLN0.le hL1 hc.le) hK11
      · exact le_trans (Real.rpow_le_rpow hLN0.le hNX hc.le) (le_max_right _ _)
    have hharm : logSum {N | N₀ < syrMin N} (oddInterval x) ≤ windowMass 1 x := by
      unfold logSum windowMass
      simp_rw [one_div]
      rw [Finset.filter_congr_decidable]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun N _ _ => by positivity
      intro N hN
      rw [Finset.mem_filter] at hN
      have hNi := hN.1
      rw [oddInterval, Finset.mem_filter, Finset.mem_range] at hNi
      rw [mem_logWindow_iff]
      have h1 : 1 ≤ N := by omega
      have h2 : N ≤ x := by omega
      exact ⟨hNi.2, by exact_mod_cast h1, by exact_mod_cast h2⟩
    have hwm := windowMass_le_half_log (le_refl (1 : ℝ)) (le_trans one_le_two hx2R)
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlogx2 : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx2R
    have hdiv1 : Real.log ((x : ℝ) / 1) = Real.log x := by rw [div_one]
    have h4 : logSum {N | N₀ < syrMin N} (oddInterval x) ≤ 4 * Real.log x := by
      rw [hdiv1] at hwm
      have : (2 : ℝ) / 1 = 2 := by norm_num
      linarith [hharm, hwm]
    rw [le_div_iff₀ hLc0]
    have hCK : 4 * K1 ≤ C := le_max_right _ _
    nlinarith [h4, hLK, hlogx0, hK11, hLc0.le, hC0]

/-- The odd-window normalizer `D = logSum univ (oddInterval x)` is at least the `N = 1` term. -/
theorem one_le_logSum_univ_oddInterval {x : ℕ} (hx2 : 2 ≤ x) :
    (1 : ℝ) ≤ logSum Set.univ (oddInterval x) := by
  unfold logSum
  rw [Finset.filter_congr_decidable]
  have h1mem : 1 ∈ (oddInterval x).filter (· ∈ Set.univ) := by
    rw [Finset.mem_filter]
    refine ⟨?_, Set.mem_univ 1⟩
    rw [oddInterval, Finset.mem_filter, Finset.mem_range]
    omega
  calc (1 : ℝ) = (1 : ℝ) / ((1 : ℕ) : ℝ) := by norm_num
    _ ≤ ∑ N ∈ (oddInterval x).filter (· ∈ Set.univ), (1 : ℝ) / N :=
        Finset.single_le_sum (f := fun N : ℕ => (1 : ℝ) / N)
          (fun i _ => by positivity) h1mem

/-- **Odd-window harmonic lower bound**: `log x ≤ 8·D` where `D` is the odd-window normalizer.
Via the AP integral test on `logWindow 1 x` (whose first term `a ≤ 3`). -/
theorem log_le_eight_logSum_univ_oddInterval {x : ℕ} (hx2 : 2 ≤ x) :
    Real.log x ≤ 8 * logSum Set.univ (oddInterval x) := by
  have hx2R : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hD1 := one_le_logSum_univ_oddInterval hx2
  set D := logSum Set.univ (oddInterval x) with hDdef
  -- `D` is the odd-window mass of `[1, x]`
  have hwm_eq : D = windowMass 1 (x : ℝ) := by
    rw [hDdef]; unfold logSum windowMass
    simp_rw [one_div]
    rw [Finset.filter_congr_decidable]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext N
    rw [Finset.mem_filter, oddInterval, Finset.mem_filter, Finset.mem_range,
      mem_logWindow_iff]
    constructor
    · rintro ⟨⟨hlt, hodd⟩, -⟩
      have h1 : 1 ≤ N := by omega
      have h2 : N ≤ x := by omega
      exact ⟨hodd, by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨hodd, h1, h2⟩
      have h2' : N ≤ x := by exact_mod_cast h2
      exact ⟨⟨by omega, hodd⟩, Set.mem_univ N⟩
  rcases le_or_gt (Real.log x) 8 with h8 | h8
  · linarith
  · have hne : (logWindow 1 (x : ℝ)).Nonempty := by
      refine ⟨1, ?_⟩
      rw [mem_logWindow_iff]
      exact ⟨by omega, by norm_num, by exact_mod_cast (by linarith : (1 : ℝ) ≤ (x : ℝ))⟩
    obtain ⟨a, count, hcount0, hloa, halt, hxlt, hxle, hFeq⟩ :=
      logWindow_odd_ap one_pos hne
    have hinj : ∀ i ∈ Finset.range count, ∀ j ∈ Finset.range count,
        a + 2 * i = a + 2 * j → i = j := by intro i _ j _ h; omega
    have ha0 : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le one_pos hloa
    have ha3 : (a : ℝ) < 4 := by linarith
    have hharm := (abs_le.mp (harmonic_ap_integral_bound ha0 two_pos count)).1
    have hmass := windowMass_eq_ap_sum hFeq hinj
    have hac0 : (0 : ℝ) < (a : ℝ) + 2 * (count : ℝ) := by positivity
    have hlog_ge : Real.log x - Real.log 4
        ≤ Real.log (((a : ℝ) + 2 * (count : ℝ)) / (a : ℝ)) := by
      rw [Real.log_div hac0.ne' ha0.ne']
      have h1 : Real.log x ≤ Real.log ((a : ℝ) + 2 * (count : ℝ)) :=
        Real.log_le_log hx0 hxlt.le
      have h2 : Real.log (a : ℝ) ≤ Real.log 4 := Real.log_le_log ha0 ha3.le
      linarith
    have hlog4 : Real.log 4 < 2 := by
      have h2 : (2.7 : ℝ) < Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have h1 : (4 : ℝ) < Real.exp 2 := by nlinarith
      calc Real.log 4 < Real.log (Real.exp 2) := Real.log_lt_log (by norm_num) h1
        _ = 2 := Real.log_exp 2
    have hainv : (a : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; exact hloa
    have hD_ge : (1/2) * (Real.log x - 2) - 1 ≤ D := by
      rw [hwm_eq, hmass]
      have hkey : (2 : ℝ)⁻¹ * Real.log (((a : ℝ) + 2 * (count : ℝ)) / (a : ℝ)) - (a : ℝ)⁻¹
          ≤ ∑ i ∈ Finset.range count, ((a : ℝ) + 2 * (i : ℝ))⁻¹ := by linarith
      refine le_trans ?_ hkey
      nlinarith [hlog_ge, hlog4]
    linarith

/-- **Theorem 3.1, Syracuse probability form** (Tao 2019 p.16, second display):
`ℙ(Syrmin(Log(2ℕ+1 ∩ [1,x])) ≤ N₀) ≥ 1 − O(log^{-c} N₀)`. -/
-- RATIFY-C6b
theorem tao_syracuse_quantitative :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C / (Real.log N₀) ^ c ≤ logProb {N | syrMin N ≤ N₀} (oddInterval x) := by
  obtain ⟨c, Ca, hc, hCa, hsum⟩ := tao_syracuse_quantitative_sum
  refine ⟨c, 8 * Ca, hc, by linarith, fun N₀ x hN₀2 hx2 => ?_⟩
  -- size facts
  have hx2R : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hlogx0 : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hN₀2R : (2 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀2
  have hLN0 : (0 : ℝ) < Real.log N₀ := Real.log_pos (by linarith)
  have hLc0 : (0 : ℝ) < (Real.log N₀) ^ c := Real.rpow_pos_of_pos hLN0 _
  set D := logSum Set.univ (oddInterval x) with hDdef
  set G := logSum {N | syrMin N ≤ N₀} (oddInterval x) with hGdef
  set B := logSum {N | N₀ < syrMin N} (oddInterval x) with hBdef
  -- complement split: G + B = D
  have hsplit : G + B = D := by
    rw [hGdef, hBdef, hDdef]
    unfold logSum
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun N _ => ?_
    by_cases h : syrMin N ≤ N₀
    · have h1 : N ∈ {N | syrMin N ≤ N₀} := h
      have h2 : N ∉ {N | N₀ < syrMin N} := by simp only [Set.mem_setOf_eq]; omega
      rw [if_pos h1, if_neg h2, if_pos (Set.mem_univ N)]
      ring
    · have h1 : N ∉ {N | syrMin N ≤ N₀} := h
      have h2 : N ∈ {N | N₀ < syrMin N} := by simp only [Set.mem_setOf_eq]; omega
      rw [if_neg h1, if_pos h2, if_pos (Set.mem_univ N)]
      ring
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hBdef]; unfold logSum
    exact Finset.sum_nonneg fun N _ => by positivity
  have hD1 : (1 : ℝ) ≤ D := one_le_logSum_univ_oddInterval hx2
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hDlog : Real.log x ≤ 8 * D := log_le_eight_logSum_univ_oddInterval hx2
  -- the C6a bad-sum bound, converted through `D`
  have hB8 : B ≤ 8 * Ca * D / (Real.log N₀) ^ c := by
    calc B ≤ Ca * Real.log x / (Real.log N₀) ^ c := hsum N₀ x hN₀2 hx2
      _ ≤ Ca * (8 * D) / (Real.log N₀) ^ c := by gcongr
      _ = 8 * Ca * D / (Real.log N₀) ^ c := by ring
  -- assemble: `logProb = G/D = 1 − B/D ≥ 1 − 8Ca/L^c`
  unfold logProb
  rw [← hGdef, ← hDdef]
  have hGD : G = D - B := by linarith
  rw [hGD, sub_div, div_self hD0.ne']
  have hBD : B / D ≤ 8 * Ca / (Real.log N₀) ^ c := by
    have h1 : B / D ≤ (8 * Ca * D / (Real.log N₀) ^ c) / D := by gcongr
    calc B / D ≤ (8 * Ca * D / (Real.log N₀) ^ c) / D := h1
      _ = 8 * Ca / (Real.log N₀) ^ c := by field_simp
  linarith [hBD]

/-- **Theorem 1.6** (Tao 2019 p.4): for `f` with `f(N) → ∞`, almost all odd `N`
(log density on the odd window) satisfy `Syrmin(N) < f(N)`. -/
-- RATIFY-C6c (domain-of-`f` rendering flagged in the module docstring)
theorem tao_syracuse (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) :
    AlmostAllOdd fun N => (syrMin N : ℝ) < f N := by
  obtain ⟨cb, Cb, hcb, hCb, hq⟩ := tao_syracuse_quantitative
  unfold AlmostAllOdd
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- pick a fixed `N₀` with `Cb/(log N₀)^cb < ε/3`
  have hlogto : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrpowto : Tendsto (fun n : ℕ => (Real.log n) ^ cb) atTop atTop :=
    (tendsto_rpow_atTop hcb).comp hlogto
  have h0 : Tendsto (fun n : ℕ => Cb / (Real.log n) ^ cb) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hrpowto
  have hev : ∀ᶠ n : ℕ in atTop, Cb / (Real.log n) ^ cb < ε / 3 :=
    (tendsto_order.1 h0).2 (ε / 3) (by linarith)
  obtain ⟨N₀, hN₀2, hN₀ε⟩ : ∃ N₀ : ℕ, 2 ≤ N₀ ∧ Cb / (Real.log N₀) ^ cb < ε / 3 := by
    obtain ⟨n, hn⟩ := (hev.and (eventually_ge_atTop 2)).exists
    exact ⟨n, hn.2, hn.1⟩
  -- pick `M` past which `f > N₀`
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hf.eventually_gt_atTop (N₀ : ℝ))
  set SM := logSum Set.univ (oddInterval M) with hSMdef
  have hSM0 : (0 : ℝ) ≤ SM := by
    rw [hSMdef]; unfold logSum
    exact Finset.sum_nonneg fun N _ => by positivity
  -- eventual threshold in `x`
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((hlogto.eventually_gt_atTop (24 * SM / ε)).and (eventually_ge_atTop 2))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨hlogx_big, hx2⟩ := hX x hx
  -- per-`x` objects
  set D := logSum Set.univ (oddInterval x) with hDdef
  set Sgood := logSum {N | (syrMin N : ℝ) < f N} (oddInterval x) with hSgooddef
  set S1 := logSum {N | syrMin N ≤ N₀} (oddInterval x) with hS1def
  set S2 := logSum {N | N < M} (oddInterval x) with hS2def
  have hD1 : (1 : ℝ) ≤ D := one_le_logSum_univ_oddInterval hx2
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hDlog : Real.log x ≤ 8 * D := log_le_eight_logSum_univ_oddInterval hx2
  have hSgood0 : (0 : ℝ) ≤ Sgood := by
    rw [hSgooddef]; unfold logSum
    exact Finset.sum_nonneg fun N _ => by positivity
  have hS20 : (0 : ℝ) ≤ S2 := by
    rw [hS2def]; unfold logSum
    exact Finset.sum_nonneg fun N _ => by positivity
  -- `Sgood ≤ D`
  have hSgoodD : Sgood ≤ D := by
    rw [hSgooddef, hDdef]; unfold logSum
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_le_sum fun N _ => ?_
    rw [if_pos (Set.mem_univ N)]
    have h0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    split_ifs <;> linarith
  -- the split: `{syrMin ≤ N₀} ⊆ {good} ∪ {N < M}` termwise
  have hkey : S1 ≤ Sgood + S2 := by
    rw [hS1def, hSgooddef, hS2def]; unfold logSum
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun N _ => ?_
    by_cases h1 : N ∈ {N | syrMin N ≤ N₀}
    · rw [if_pos h1]
      have h1' : syrMin N ≤ N₀ := h1
      rcases le_or_gt M N with h2 | h2
      · have hgood : N ∈ {N | (syrMin N : ℝ) < f N} := by
          simp only [Set.mem_setOf_eq]
          have hs : (syrMin N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast h1'
          exact lt_of_le_of_lt hs (hM N h2)
        rw [if_pos hgood]
        have h0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
        split_ifs <;> linarith
      · have hsmall : N ∈ {N | N < M} := h2
        rw [if_pos hsmall]
        have h0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
        split_ifs <;> linarith
    · rw [if_neg h1]
      have h0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      split_ifs <;> linarith
  -- `S2 ≤ SM` (the small terms live in `oddInterval M`)
  have hS2SM : S2 ≤ SM := by
    rw [hS2def, hSMdef]; unfold logSum
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun N _ _ => by positivity
    intro N hN
    simp only [Finset.mem_filter] at hN ⊢
    obtain ⟨hNi, hNM⟩ := hN
    have hNM' : N < M := hNM
    simp only [oddInterval, Finset.mem_filter, Finset.mem_range] at hNi ⊢
    exact ⟨⟨by omega, hNi.2⟩, Set.mem_univ N⟩
  -- `S2/D < ε/3` from `24·SM/ε < log x ≤ 8D`
  have hS2D : S2 / D < ε / 3 := by
    have h1 : 24 * SM / ε < 8 * D := lt_of_lt_of_le hlogx_big hDlog
    have h2 : 24 * SM < 8 * D * ε := (div_lt_iff₀ hε).mp h1
    rw [div_lt_iff₀ hD0]
    nlinarith [hS2SM]
  -- quantitative bound at `N₀`
  have hq' : 1 - Cb / (Real.log N₀) ^ cb ≤ S1 / D := hq N₀ x hN₀2 hx2
  -- assemble
  have hp_eq : logProb {N | (syrMin N : ℝ) < f N} (oddInterval x) = Sgood / D := rfl
  have h2 : S1 / D ≤ Sgood / D + S2 / D := by
    rw [← add_div]
    gcongr
  have hp_ge : 1 - 2 * ε / 3 < Sgood / D := by
    have := hN₀ε
    linarith
  have hp_le : Sgood / D ≤ 1 := by
    rw [div_le_one hD0]
    exact hSgoodD
  rw [hp_eq, Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

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
