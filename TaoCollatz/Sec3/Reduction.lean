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

open Classical in
/-- **Indicator expectation formula** for the log-uniform window: the probability of `S`
is its harmonic mass in the window over the total window mass. -/
theorem logUnifOdd_expect_indicator {lo hi : ℝ} (h : (logWindow lo hi).Nonempty)
    (S : Set ℕ) :
    (logUnifOdd lo hi).expect (Set.indicator S 1)
      = (∑ N ∈ (logWindow lo hi).filter (· ∈ S), (N : ℝ)⁻¹) / windowMass lo hi := by
  sorry

/-- **One-scale recursion** (p.17, the display chain): `ℙ(B_x) ≤ ℙ(B_{x^α}) + O(log^{-c}x)`.
Route: `B_x ⊆ {Pass_x ∈ E}` up to the non-passage event (`stabilization` part 1, note
`1 ∈ E_{N₀}` since `passLoc = 1` off passage and `Syrmin 1 = 1 ≤ N₀`); swap windows by
`stabilization`'s dTV bound via `abs_expect_indicator_sub_le_dTV`; re-enter `B_{x^α}` by
`descentEvent_mono` (⌊x⌋₊ ≤ ⌊x^α⌋₊). -/
theorem descentProb_step :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ N₀ : ℕ, 1 ≤ N₀ →
      descentProb ⌊x⌋₊ (x ^ alpha) N₀
        ≤ descentProb ⌊x ^ alpha⌋₊ (x ^ alpha ^ 2) N₀ + C * (Real.log x) ^ (-c) := by
  sorry

/-- **Base case** (p.17 bottom): at scales `x ≤ N₀`, the event needs only passage —
`Syrmin(Pass) ≤ Pass ≤ ⌊x⌋ ≤ N₀` — so `first_passage_nonescape` gives `1 − O(x^{-c})`. -/
theorem descentProb_base :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ N₀ : ℕ, x ≤ (N₀ : ℝ) →
      1 - C * x ^ (-c) ≤ descentProb ⌊x⌋₊ (x ^ alpha) N₀ := by
  sorry

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
