import TaoCollatz.Sec5.FirstPassage
import TaoCollatz.Basic.Valuation

/-!
# §5 approximate first-passage formula (node C8 — Proposition 5.2)

Paper anchors: Tao 2019 §5 pp.22–25, Proposition 5.2 (the approximate formula (5.8)), with the
bookkeeping objects `n₀` (5.1), `m₀` (5.2), `𝒜⁽ⁿ'⁾` (5.11), `I_y` (5.9), `E'` (5.10) and the
`B_{n,y}` equivalence chain.

**This is node C8 — the RISK on the board** (diff 4, 15–30 laps, 75%). It is pinned here (statement
written with `sorry` so it compiles); the proof is owed. Per `blueprint_rules.md`, a pin is a
*claim*, not a fact — the judge ratifies and sets `\leanok`. Nothing here sets `\leanok`.

`C8.\uses{C2, C5, C7}` binds its **proof**. Its **statement** is written over the first-passage
definitions (`passes`, `passTime`, `passLoc`, `logUnifOdd`, `alpha`) and the affine map `Aff`
(1.3) / valuation vector `valVec` (1.8), **all of which already exist**, which is exactly why C8
is pinnable now, before a line of C7 is proved.

## What C8's proof needs from C7 (the deliverable of this pinning objective)

Reading Prop 5.2's proof (pp.22–25) against the blueprint edge `C8.\uses{C7}`: C7 is consumed at
**exactly one place — the (5.16) step**, pinned below as `approx_passtime_window`. That step bounds
`ℙ(T_x(N_y) ∉ I_y)`. The event `T_x(N_y) ∉ I_y` splits as
  `{¬ passes}  ∪  {passes ∧ T_x ∈ [m₀,n₀] but outside the interval I_y}`.
The **first** piece — the escape probability `ℙ(T_x(N_y) = ∞) ≪ x^{-c}` — is precisely
`first_passage_nonescape` (paper (1.19) / (5.5), node C7). The second piece is the integral-test
calculation over the log-uniform window plus (5.12). So **C8 consumes C7 as (1.19) essentially as
the blueprint states it**, entering through the `¬ passes` term of (5.16). The remaining machinery
of Prop 5.2 — (5.12) good-tuple union bound, the `B_{n,y}` equivalence, Lemma 2.1 affine bijection
— does **not** touch C7.
-/

open scoped ENNReal

namespace TaoCollatz

-- `nZero` (5.1) and `mZero` (5.2) live in `Sec5.FirstPassage` (shared with node C7).

/-- Paper (5.11): the good-tuple set `𝒜⁽ⁿ'⁾ ⊂ (ℕ+1)ⁿ'` — tuples `(a₁,…,a_{n'})` with every
`aᵢ ≥ 1` whose every prefix sum stays within `log^{0.6} x` of the mean `2n`:
`|a_{[1,n]} − 2n| < log^{0.6} x` for all `0 ≤ n ≤ n'`.  (`a_{[1,n]} = pre a n`.) -/
def goodTuple (x : ℝ) (n' : ℕ) (a : Fin n' → ℕ) : Prop :=
  (∀ i, 1 ≤ a i) ∧ ∀ n, n ≤ n' → |(pre a n : ℝ) - 2 * n| < Real.log x ^ (0.6 : ℝ)

/-- Prefix sums grow with the length argument (`pre a` is monotone). -/
theorem pre_mono {n : ℕ} (a : Fin n → ℕ) {m m' : ℕ} (h : m ≤ m') : pre a m ≤ pre a m' := by
  unfold pre
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Nat.zero_le _)
  intro x hx
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)

/-- **`fnat` upper bound** — `fnat k a < 3^k · 2^{a_{[1,k]}}` (the `F_k` integerification is dominated
by the trivial geometric bound: each summand `3^{k-1-m}·2^{a_{[1,m]}} ≤ 3^{k-1-m}·2^{a_{[1,k]}}` by
prefix monotonicity, and `∑_{m<k} 3^{k-1-m} = (3^k−1)/2 < 3^k`).  Needed for the (5.19) `(N*)⁻¹`
relative-error step: `fnat/(M·2^{pre}) < 3^k/M`, which is `O(x^{-c})` in the operating regime. -/
theorem fnat_lt_pow_mul (k : ℕ) (a : Fin k → ℕ) : fnat k a < 3 ^ k * 2 ^ pre a k := by
  unfold fnat
  have hpk : (1 : ℕ) ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  calc ∑ m ∈ Finset.range k, 3 ^ (k - 1 - m) * 2 ^ pre a m
      ≤ ∑ m ∈ Finset.range k, 3 ^ (k - 1 - m) * 2 ^ pre a k := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hle : pre a m ≤ pre a k := pre_mono a (Nat.le_of_lt (Finset.mem_range.mp hm))
        exact Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_right (by norm_num) hle)
    _ = (∑ m ∈ Finset.range k, 3 ^ (k - 1 - m)) * 2 ^ pre a k := by rw [Finset.sum_mul]
    _ = (∑ j ∈ Finset.range k, 3 ^ j) * 2 ^ pre a k := by
        rw [Finset.sum_range_reflect (fun j => 3 ^ j) k]
    _ < 3 ^ k * 2 ^ pre a k := by
        refine (Nat.mul_lt_mul_right (by positivity)).mpr ?_
        rw [Nat.geomSum_eq (by norm_num) k]
        omega

/-- Each entry of a vector is bounded by its full prefix sum: `a i ≤ pre a n'`. -/
theorem entry_le_pre {n' : ℕ} (a : Fin n' → ℕ) (i : Fin n') : a i ≤ pre a n' := by
  have h := Finset.single_le_sum (f := fun m => if h : m < n' then a ⟨m, h⟩ else 0)
    (fun m _ => Nat.zero_le _) (Finset.mem_range.mpr i.isLt)
  simpa [pre, i.isLt] using h

/-- **Good tuples form a finite set** (paper (5.11)).  The prefix constraint at `n = n'` forces
`pre a n' < 2n' + log^{0.6} x`, so every entry `a i ≤ pre a n'` is bounded by a fixed `K`; the good
set therefore injects into `Fin n' → Fin (K+1)`, a `Fintype`.  This underwrites the `∑'_ā`
summability used by the (5.18) reindex (`approxMainTerm`'s per-term `.toReal` sums correctly). -/
theorem goodTuple_finite (x : ℝ) (n' : ℕ) : {a : Fin n' → ℕ | goodTuple x n' a}.Finite := by
  classical
  set K : ℕ := ⌈(2 * n' : ℝ) + Real.log x ^ (0.6 : ℝ)⌉₊ with hK
  have hbound : ∀ a : Fin n' → ℕ, goodTuple x n' a → ∀ i, a i ≤ K := by
    intro a ha i
    have hg := ha.2 n' (le_refl n')
    have h1 : (pre a n' : ℝ) < 2 * n' + Real.log x ^ (0.6 : ℝ) := by
      have := (abs_lt.mp hg).2; linarith
    have h2 : (a i : ℝ) ≤ (pre a n' : ℝ) := by exact_mod_cast entry_le_pre a i
    have h4 : (a i : ℝ) ≤ (K : ℝ) := le_trans (le_of_lt (lt_of_le_of_lt h2 h1)) (Nat.le_ceil _)
    exact_mod_cast h4
  have hfin : Finite {a : Fin n' → ℕ // goodTuple x n' a} := by
    apply Finite.of_injective (β := Fin n' → Fin (K + 1))
      (fun a i => ⟨a.1 i, Nat.lt_succ_of_le (hbound a.1 a.2 i)⟩)
    intro a b hab
    apply Subtype.ext
    funext i
    have := congrFun hab i
    exact (Fin.mk.injEq _ _ _ _).mp this
  exact Set.finite_coe_iff.mp hfin

/-- **Real-valued two-sided bracket for the Syracuse iterate** (foundation for the (5.13)/(5.14)
orbit estimate).  From `syr_iterate_key` (`2^{valSum}·Syr^n N = 3^n N + Fnat`) and `fnat_valVec_le`
(`Fnat ≤ 2^{valSum}·3^n`), for odd `N`:
`3^n N / 2^{valSum N n} ≤ Syr^n N ≤ 3^n N / 2^{valSum N n} + 3^n`.
The main term `3^n N / 2^{valSum}` becomes `(3/4)^n N` once `valSum ≈ 2n` (the good-tuple prefix
control), and the additive `+3^n` is the lower-order rounding slack; both reindex legs consume this. -/
theorem syr_iterate_bracket (N n : ℕ) (hN : N % 2 = 1) :
    (3 ^ n * N : ℝ) / 2 ^ valSum N n ≤ (syr^[n] N : ℝ) ∧
      (syr^[n] N : ℝ) ≤ (3 ^ n * N : ℝ) / 2 ^ valSum N n + 3 ^ n := by
  have hkey := syr_iterate_key N n hN
  rw [pre_valVec (le_refl n)] at hkey
  have hle := fnat_valVec_le N n
  have hpos : (0 : ℝ) < 2 ^ valSum N n := by positivity
  have hkeyR : (2 ^ valSum N n : ℝ) * (syr^[n] N : ℝ)
      = (3 ^ n * N : ℝ) + (fnat n (valVec N n) : ℝ) := by exact_mod_cast hkey
  have hleR : (fnat n (valVec N n) : ℝ) ≤ (2 ^ valSum N n : ℝ) * 3 ^ n := by exact_mod_cast hle
  have hS : (syr^[n] N : ℝ)
      = ((3 ^ n * N : ℝ) + (fnat n (valVec N n) : ℝ)) / 2 ^ valSum N n :=
    eq_div_of_mul_eq hpos.ne' (by rw [mul_comm]; exact hkeyR)
  refine ⟨?_, ?_⟩
  · rw [hS]; gcongr
    exact le_add_of_nonneg_right (by positivity)
  · rw [hS, add_div]
    gcongr (3 ^ n * N : ℝ) / 2 ^ valSum N n + ?_
    rw [div_le_iff₀ hpos]; nlinarith [hleR]

/-- **`valSum` deviation on the good event.**  If `valVec N n'` is a good tuple and `n ≤ n'`, the
prefix valuation sum stays within `log^{0.6}x` of its mean `2n`: `|valSum N n − 2n| < log^{0.6}x`.
(`valSum N n = pre (valVec N n') n` for `n ≤ n'`, so this is directly the good-tuple prefix bound.) -/
theorem valSum_dev_on_good (x : ℝ) (N n' n : ℕ)
    (hgood : goodTuple x n' (valVec N n')) (hn : n ≤ n') :
    |(valSum N n : ℝ) - 2 * n| < Real.log x ^ (0.6 : ℝ) := by
  have h := hgood.2 n hn
  rwa [pre_valVec hn] at h

/-- **Two-sided `2^{valSum}` bracket on the good event** (rpow form).  From `valSum_dev_on_good`:
`2^{2n − log^{0.6}x} < 2^{valSum N n} < 2^{2n + log^{0.6}x}`.  Dividing `3^n N` by this turns the
`syr_iterate_bracket` main term `3^n N / 2^{valSum}` into `(3/4)^n N · 2^{∓log^{0.6}x}` — the
multiplicative orbit estimate the `E'` size window needs. -/
theorem two_rpow_valSum_bounds (x : ℝ) (N n' n : ℕ)
    (hgood : goodTuple x n' (valVec N n')) (hn : n ≤ n') :
    (2 : ℝ) ^ (2 * (n : ℝ) - Real.log x ^ (0.6 : ℝ)) < (2 : ℝ) ^ ((valSum N n : ℝ)) ∧
      (2 : ℝ) ^ ((valSum N n : ℝ)) < (2 : ℝ) ^ (2 * (n : ℝ) + Real.log x ^ (0.6 : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (valSum_dev_on_good x N n' n hgood hn)
  refine ⟨?_, ?_⟩
  · rw [Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]; linarith
  · rw [Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]; linarith

/-- **(5.13)/(5.14) multiplicative orbit estimate** (good-event two-sided bracket).  Combining
`syr_iterate_bracket` with `two_rpow_valSum_bounds`: for odd `N` with `valVec N n'` good and
`n ≤ n'`,
`3^n N / 2^{2n + log^{0.6}x} ≤ Syr^n N ≤ 3^n N / 2^{2n − log^{0.6}x} + 3^n`.
Since `2^{2n} = 4^n`, the main term is `(3/4)^n N · 2^{∓log^{0.6}x}` — exactly the `exp(O(log^{0.6}x))`
multiplicative window around `(3/4)^n N` the `E'` size bounds and both reindex legs consume. -/
theorem syr_iterate_good_bracket (x : ℝ) (N n' n : ℕ) (hN : N % 2 = 1)
    (hgood : goodTuple x n' (valVec N n')) (hn : n ≤ n') :
    (3 : ℝ) ^ n * N / 2 ^ (2 * (n : ℝ) + Real.log x ^ (0.6 : ℝ)) ≤ (syr^[n] N : ℝ) ∧
      (syr^[n] N : ℝ)
        ≤ (3 : ℝ) ^ n * N / 2 ^ (2 * (n : ℝ) - Real.log x ^ (0.6 : ℝ)) + 3 ^ n := by
  obtain ⟨hb_lo, hb_hi⟩ := syr_iterate_bracket N n hN
  obtain ⟨hB_lo, hB_hi⟩ := two_rpow_valSum_bounds x N n' n hgood hn
  rw [← Real.rpow_natCast (2 : ℝ) (valSum N n)] at hb_lo hb_hi
  refine ⟨le_trans ?_ hb_lo, le_trans hb_hi ?_⟩
  · gcongr
  · gcongr

/-- `(2:ℝ)^{2n} = 4^n` (rpow exponent `2·n`, natural base).  Reusable bridge for the orbit estimate. -/
theorem two_rpow_two_mul (n : ℕ) : (2 : ℝ) ^ (2 * (n : ℝ)) = (4 : ℝ) ^ n := by
  rw [show (2 : ℝ) * (n : ℝ) = (n : ℝ) + (n : ℝ) from by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  simp only [Real.rpow_natCast]
  rw [← mul_pow]; norm_num

/-- **(5.13)/(5.14) orbit estimate, clean `(3/4)^n N` form.**  The `syr_iterate_good_bracket`
main term `3^n N / 2^{2n ± L}` (`L = log^{0.6}x`) rewritten as `(3/4)^n N · 2^{∓L}` (since
`2^{2n}=4^n`).  This is the `exp(O(log^{0.6}x))` multiplicative window around `(3/4)^n N` directly. -/
theorem syr_iterate_good_bracket' (x : ℝ) (N n' n : ℕ) (hN : N % 2 = 1)
    (hgood : goodTuple x n' (valVec N n')) (hn : n ≤ n') :
    (3 / 4 : ℝ) ^ n * N * 2 ^ (-(Real.log x ^ (0.6 : ℝ))) ≤ (syr^[n] N : ℝ) ∧
      (syr^[n] N : ℝ) ≤ (3 / 4 : ℝ) ^ n * N * 2 ^ (Real.log x ^ (0.6 : ℝ)) + 3 ^ n := by
  obtain ⟨hlo, hhi⟩ := syr_iterate_good_bracket x N n' n hN hgood hn
  have hrw : ∀ s : ℝ, (3 : ℝ) ^ n * N / 2 ^ (2 * (n : ℝ) + s) = (3 / 4 : ℝ) ^ n * N * 2 ^ (-s) := by
    intro s
    have h2s : (2 : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) s).ne'
    have h4n : (4 : ℝ) ^ n ≠ 0 := by positivity
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), two_rpow_two_mul,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_pow]
    field_simp
  rw [hrw] at hlo
  have hup := hrw (-(Real.log x ^ (0.6 : ℝ)))
  rw [neg_neg] at hup
  rw [show 2 * (n : ℝ) - Real.log x ^ (0.6 : ℝ)
      = 2 * (n : ℝ) + (-(Real.log x ^ (0.6 : ℝ))) from by ring, hup] at hhi
  exact ⟨hlo, hhi⟩

/-- **Slack absorption** — the orbit estimate's `2^{log^{0.6}x}` multiplicative slack is dominated by
the `E'` window's `exp(log^{0.7}x)`, for `x` large.  Since `2^{log^{0.6}x} = exp(log 2·log^{0.6}x)`
and `log 2 ≤ log^{0.1}x` once `log x ≥ (log 2)^{10}`, we get `log 2·log^{0.6}x ≤ log^{0.7}x`.  This is
what lets the `exp(O(log^{0.6}x))` orbit window fit inside the `exp(±log^{0.7}x)` `E'` window. -/
theorem two_rpow_slack_le_exp :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) ≤ Real.exp (Real.log x ^ (0.7 : ℝ)) := by
  refine ⟨Real.exp ((Real.log 2) ^ (10 : ℕ)), Real.one_le_exp (by positivity), fun x hx => ?_⟩
  have hlogx : (Real.log 2) ^ (10 : ℕ) ≤ Real.log x := by
    rw [← Real.log_exp ((Real.log 2) ^ (10 : ℕ))]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hlogpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le (by positivity) hlogx
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- log 2 ≤ log^{0.1}x
  have hlog2le : Real.log 2 ≤ Real.log x ^ (0.1 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hlogx (by norm_num : (0 : ℝ) ≤ (0.1 : ℝ))
    rwa [← Real.rpow_natCast (Real.log 2) 10, ← Real.rpow_mul hl2,
      show ((10 : ℕ) : ℝ) * (0.1 : ℝ) = 1 from by norm_num, Real.rpow_one] at h
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  calc Real.log 2 * Real.log x ^ (0.6 : ℝ)
      ≤ Real.log x ^ (0.1 : ℝ) * Real.log x ^ (0.6 : ℝ) :=
        mul_le_mul_of_nonneg_right hlog2le (by positivity)
    _ = Real.log x ^ (0.7 : ℝ) := by
        rw [← Real.rpow_add hlogpos]; norm_num

/-- Lower endpoint of the interval `I_y` (5.9): `log(y/x)/log(4/3) + log^{0.8} x`. -/
noncomputable def IyLo (x y : ℝ) : ℝ :=
  Real.log (y / x) / Real.log (4 / 3) + Real.log x ^ (0.8 : ℝ)

/-- Upper endpoint of the interval `I_y` (5.9): `log(y^α/x)/log(4/3) − log^{0.8} x`. -/
noncomputable def IyHi (x y : ℝ) : ℝ :=
  Real.log (y ^ alpha / x) / Real.log (4 / 3) - Real.log x ^ (0.8 : ℝ)

open Classical in
/-- Paper (5.9): the summation range `I_y` as the natural numbers in `[IyLo, IyHi]`.  Bounded by
`range (n₀+1)` since `I_y ⊂ [m₀, n₀]` (the observation after (5.11)). -/
noncomputable def Iy (x y : ℝ) : Finset ℕ :=
  (Finset.range (nZero x + 1)).filter fun n => IyLo x y ≤ (n : ℝ) ∧ (n : ℝ) ≤ IyHi x y

/-- Paper (5.10): the set `E'` of odd naturals `M` with `T_x(M) = m₀`, `Pass_x(M) ∈ E`, and
`exp(−log^{0.7} x)·(4/3)^{m₀}·x ≤ M ≤ exp(log^{0.7} x)·(4/3)^{m₀}·x`. -/
def Eprime (x : ℝ) (E : Set ℕ) (M : ℕ) : Prop :=
  M % 2 = 1 ∧ passTime ⌊x⌋₊ M = mZero x ∧ passLoc ⌊x⌋₊ M ∈ E ∧
    Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x ≤ (M : ℝ) ∧
    (M : ℝ) ≤ Real.exp (Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x

open Classical in
-- RATIFY-C8-v2 (deep reflection 2026-07-15): the (5.8) main term, re-pinned against the paper's
-- EXACT reindex.  The v1 pin used the ℕ-truncating `Aff` pushforward UNGUARDED, which over-counts
-- (5.8) by a super-polylog factor (`tools/sandbox/tao_c8_truncation_probe.py`; DIRECTION.md CURRENT
-- DIRECTIVE 2026-07-15) and makes the old `truncation_error_bound` FALSE.  Tao's `ℙ(Aff_ā(N_y)=M)`
-- is the mass of the EXACT-affine event, non-empty only under the (5.18) congruence and then pinning
-- `N_y` to the single (5.19) value `2^{|ā|}(M−F)/3^{n−m₀}`, i.e. `3^{n−m₀}N + Fnat = M·2^{a_{[1,n−m₀]}}`.
/-- **Proposition 5.2 RHS**, the affine main term (5.8):
`∑_{n∈I_y} ∑_{ā∈𝒜⁽ⁿ⁻ᵐ⁰⁾} ∑_{M∈E'} ℙ(Aff_ā(N_y) = M)`.  The inner `∑_{ā}∑_{M}` are `tsum`s masked
by `goodTuple`/`Eprime`; `ℙ(Aff_ā(N_y) = M)` is the `logUnifOdd`-mass of the **exact** affine event
`{N : 3^{n−m₀}·N + Fnat_{n−m₀}(ā) = M · 2^{a_{[1,n−m₀]}}}` — Tao's (5.18)/(5.19) integrality guard,
which by Lemma 2.1 (`valVec_unique`) restricts the reindex to the true valuation vector (no truncation
coincidences).  This makes the reindex EXACT: `approxMainTerm = steppedMid` (`approxMainTerm_eq_steppedMid`). -/
noncomputable def approxMainTerm (x : ℝ) (E : Set ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Iy x y,
    ∑' (ā : Fin (n - mZero x) → ℕ), ∑' (M : ℕ),
      if goodTuple x (n - mZero x) ā ∧ Eprime x E M then
        (∑' N, if 3 ^ (n - mZero x) * N + fnat (n - mZero x) ā
                    = M * 2 ^ pre ā (n - mZero x)
               then (logUnifOdd y (y ^ alpha)) N else 0).toReal
      else 0

/-! ## Lemma 2.1 kernels for the (5.18) affine reindexing (the route-decisive assembly step)

The proof of (5.8) reindexes `ℙ((Syr^{n-m₀}N_y ∈ E') ∧ good)` into `∑_ā ∑_M ℙ(Aff_ā(N_y)=M)` via
Tao's Lemma 2.1 (`valVec_unique`, `Basic/Valuation.lean`).  Two facts drive the **main** (exact)
contribution `ā = valVec N k`; both are proved axiom-clean below.

✅ **The reindex is EXACT under RATIFY-C8-v2** (`approxMainTerm_eq_steppedMid`, axiom-clean).  Tao's
`ℙ(Aff_ā(N_y)=M)` is the mass of the EXACT-affine event `{N : 3^{n−m₀}N + fnat = M·2^{pre ā}}`, whose
divisibility guard (`2^{pre ā k} ∣ 3^k N + fnat k ā`) is precisely `valVec_unique`'s hypothesis; on it
`Aff N k ā = M` holds without truncation.  So `approxMainTerm = steppedMid` on the nose — the exact
`=` reindex is PROVED below.  (Historical: the v1 pin used the truncating `Aff` pushforward UNGUARDED,
over-counting (5.8) super-polylog — probe `19135→0–3`, `tools/sandbox/tao_c8_truncation_probe.py`; the
guarded re-pin repaired it.  Do NOT re-seed that truncating route.) -/

/-- **Lemma 2.1, generating direction.**  For odd `N`, the affine map at the true valuation vector
recovers the Syracuse iterate: `Aff N k (valVec N k) = syr^[k] N`.  (The guarded ℕ-division is exact
here: `2^{|valVec N k|}·syr^[k] N = 3^k N + fnat k (valVec N k)` — paper (1.7), `syr_iterate_key`.)
This is the exact/main contribution of the (5.18) reindexing; the truncation `ā ≠ valVec N k` terms
are the error absorbed in `O(log^{-c} x)`. -/
theorem aff_valVec_eq_syr (N k : ℕ) (hN : N % 2 = 1) :
    Aff N k (valVec N k) = syr^[k] N := by
  unfold Aff
  rw [← syr_iterate_key N k hN, Nat.mul_comm, Nat.mul_div_left _ (by positivity)]

-- The positivity hypothesis `valVec_unique` / Lemma 2.1 and the good-tuple set `𝒜⁽ⁿ'⁾` (5.11)
-- require on the reindexing vectors is already proved: `valVec_pos` (`Syracuse/ValuationDist.lean`)
-- gives `1 ≤ valVec N k i` for odd `N` (since `3·(odd)+1` is even).

/-! ## Shared `PMF.expect` / event glue for the C8 sub-lemmas -/

/-- Expectation of an event indicator dominated pointwise by a sum of two indicators is at most the
sum of their expectations (a binary union/subadditivity bound for `PMF.expect`). -/
theorem expect_le_add_of_indicator_le {α : Type*} (p : PMF α) (U S T : Set α)
    (h : ∀ a, Set.indicator U (1 : α → ℝ) a ≤ Set.indicator S 1 a + Set.indicator T 1 a) :
    p.expect (Set.indicator U 1) ≤
      p.expect (Set.indicator S 1) + p.expect (Set.indicator T 1) := by
  classical
  have hsumP : Summable fun a => (p a).toReal := ENNReal.summable_toReal p.tsum_coe_ne_top
  have ind01 : ∀ (V : Set α) a,
      (0 : ℝ) ≤ Set.indicator V (1 : α → ℝ) a ∧ Set.indicator V (1 : α → ℝ) a ≤ 1 := by
    intro V a
    refine ⟨Set.indicator_nonneg (fun _ _ => zero_le_one) a, ?_⟩
    rw [Set.indicator_apply]; split <;> simp
  have hsum : ∀ (V : Set α), Summable fun a => (p a).toReal * Set.indicator V (1 : α → ℝ) a := by
    intro V
    exact Summable.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (ind01 V a).1)
      (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (ind01 V a).2) hsumP
  show (∑' a, (p a).toReal * Set.indicator U 1 a) ≤
      (∑' a, (p a).toReal * Set.indicator S 1 a) + (∑' a, (p a).toReal * Set.indicator T 1 a)
  rw [← (hsum S).tsum_add (hsum T)]
  refine (hsum U).tsum_le_tsum (fun a => ?_) ((hsum S).add (hsum T))
  calc (p a).toReal * Set.indicator U 1 a
      ≤ (p a).toReal * (Set.indicator S 1 a + Set.indicator T 1 a) :=
        mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg
    _ = (p a).toReal * Set.indicator S 1 a + (p a).toReal * Set.indicator T 1 a := by ring

/-- Finset version of the union bound: an indicator dominated pointwise by a finite sum of
indicators has expectation at most the sum of the term expectations. -/
theorem expect_le_sum_of_indicator_le {α ι : Type*} (p : PMF α) (U : Set α)
    (s : Finset ι) (T : ι → Set α)
    (h : ∀ a, Set.indicator U (1 : α → ℝ) a ≤ ∑ i ∈ s, Set.indicator (T i) 1 a) :
    p.expect (Set.indicator U 1) ≤ ∑ i ∈ s, p.expect (Set.indicator (T i) 1) := by
  classical
  have hsumP : Summable fun a => (p a).toReal := ENNReal.summable_toReal p.tsum_coe_ne_top
  have ind01 : ∀ (V : Set α) a,
      (0 : ℝ) ≤ Set.indicator V (1 : α → ℝ) a ∧ Set.indicator V (1 : α → ℝ) a ≤ 1 := by
    intro V a
    refine ⟨Set.indicator_nonneg (fun _ _ => zero_le_one) a, ?_⟩
    rw [Set.indicator_apply]; split <;> simp
  have hsum : ∀ (V : Set α), Summable fun a => (p a).toReal * Set.indicator V (1 : α → ℝ) a := by
    intro V
    exact Summable.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (ind01 V a).1)
      (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (ind01 V a).2) hsumP
  have hsumRHS : Summable fun a => (p a).toReal * ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a := by
    refine Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun i _ => (ind01 (T i) a).1))
      (fun a => ?_) (hsumP.mul_right (s.card : ℝ))
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    calc ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a ≤ ∑ _i ∈ s, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (ind01 (T i) a).2
      _ = (s.card : ℝ) := by simp
  have hswap : (∑ i ∈ s, p.expect (Set.indicator (T i) 1))
      = ∑' a, (p a).toReal * ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a := by
    unfold PMF.expect
    rw [← Summable.tsum_finsetSum (fun i _ => hsum (T i))]
    exact tsum_congr fun a => by rw [Finset.mul_sum]
  rw [hswap]
  show (∑' a, (p a).toReal * Set.indicator U 1 a) ≤ _
  refine (hsum U).tsum_le_tsum (fun a => ?_) hsumRHS
  exact mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg

/-- For `x ≥ e` and `c > 0`, `x^{-c} ≤ (log x)^{-c}` (since `1 ≤ log x ≤ x`).  This is what lets the
escape term's `x^{-c}` bound (`first_passage_nonescape`) fold into the `(log x)^{-c}` target. -/
theorem escape_to_log {x c : ℝ} (hx : Real.exp 1 ≤ x) (hc : 0 < c) :
    x ^ (-c) ≤ (Real.log x) ^ (-c) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le one_pos hlog1
  have hle : Real.log x ≤ x := le_trans (Real.log_le_sub_one_of_pos hxpos) (by linarith)
  rw [Real.rpow_neg hxpos.le, Real.rpow_neg hlogpos.le, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogpos c)
    (Real.rpow_le_rpow hlogpos.le hle hc.le)

/-- On the odd support, `¬ goodTuple` is exactly the existence of a prefix `n ≤ n₀` whose valuation
sum `valSum N n` deviates from the mean `2n` by `≥ log^{0.6} x` (the positivity conjunct of
`goodTuple` is automatic for odd `N` by `valVec_pos`; `pre (valVec N n₀) n = valSum N n`). -/
theorem not_goodTuple_iff_prefix_dev {x : ℝ} {N n₀ : ℕ} (hN : N % 2 = 1) :
    ¬ goodTuple x n₀ (valVec N n₀) ↔
      ∃ n ∈ Finset.range (n₀ + 1), Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n| := by
  have hpos : ∀ i, 1 ≤ valVec N n₀ i := fun i => valVec_pos N n₀ hN i
  unfold goodTuple
  rw [not_and]
  constructor
  · intro h
    have hdev := h hpos
    push Not at hdev
    obtain ⟨n, hn, hge⟩ := hdev
    exact ⟨n, Finset.mem_range.mpr (by omega), by rwa [pre_valVec (by omega : n ≤ n₀)] at hge⟩
  · rintro ⟨n, hn, hge⟩ _
    rw [Finset.mem_range] at hn
    push Not
    exact ⟨n, by omega, by rw [pre_valVec (by omega : n ≤ n₀)]; exact hge⟩

/-! ### Analytic + marginal glue for the (5.12) core `goodTuple_prefix_dev_sum` (below)

These are the reusable bricks the good-tuple deviation sum needs: two elementary
`polynomial-in-log ≪ stretched-exponential` decay facts, an inline copy of the Sec6 prefix-block
marginal `iidMap_pre` (Sec6 is not imported here), the Gweight decay for a fixed threshold
`d·log^{0.6}x` over prefixes `n ≤ nZero x`, and the two-sided prefix analogue of
`iid_geomHalf_overflow_eq`. -/

/-- The `log_le_eps_mul_real` cutoff (X-chase): witness copied verbatim from its proof. -/
noncomputable def X_logEpsMul (ε : ℝ) : ℝ := (2 / ε) ^ 2

/-- Real-variable version of `log_le_eps_mul_of_large`: `log w ≤ ε w` for `w` large.
Universal-cutoff form (X-chase). -/
theorem log_le_eps_mul_real_atX {ε : ℝ} (hε : 0 < ε) :
    ∀ w : ℝ, X_logEpsMul ε ≤ w → Real.log w ≤ ε * w := by
  rw [show X_logEpsMul ε = (2 / ε) ^ 2 from rfl]
  intro w hw
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hsqrt_pos : 0 < Real.sqrt w := Real.sqrt_pos.mpr hwpos
  have hsq : Real.sqrt w ^ 2 = w := Real.sq_sqrt hwpos.le
  have hlog_le : Real.log w ≤ 2 * Real.sqrt w := by
    calc Real.log w = Real.log (Real.sqrt w ^ 2) := by rw [hsq]
      _ = 2 * Real.log (Real.sqrt w) := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 2 * (Real.sqrt w - 1) := by
          have := Real.log_le_sub_one_of_pos hsqrt_pos; linarith
      _ ≤ 2 * Real.sqrt w := by linarith [hsqrt_pos.le]
  have hsqrt_lb : 2 / ε ≤ Real.sqrt w := by
    calc 2 / ε = Real.sqrt ((2 / ε) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt w := Real.sqrt_le_sqrt hw
  have hcomb : 2 * Real.sqrt w ≤ ε * w := by
    have h1 : (2 : ℝ) ≤ ε * Real.sqrt w := by
      have := mul_le_mul_of_nonneg_left hsqrt_lb hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    calc 2 * Real.sqrt w ≤ (ε * Real.sqrt w) * Real.sqrt w :=
          mul_le_mul_of_nonneg_right h1 hsqrt_pos.le
      _ = ε * (Real.sqrt w ^ 2) := by ring
      _ = ε * w := by rw [hsq]
  linarith

/-- ∃-form of `log_le_eps_mul_real_atX` (X-chase: `w₀ := X_logEpsMul ε`). -/
theorem log_le_eps_mul_real {ε : ℝ} (hε : 0 < ε) :
    ∃ w₀ : ℝ, ∀ w : ℝ, w₀ ≤ w → Real.log w ≤ ε * w :=
  ⟨X_logEpsMul ε, log_le_eps_mul_real_atX hε⟩

/-- The `log_rpow_mul_exp_neg_le_one` cutoff (X-chase): witness copied verbatim from its
proof, at the explicit `X_logEpsMul` upstream. -/
noncomputable def X_logRpowExp (p κ θ : ℝ) : ℝ :=
  Real.exp (max ((max (X_logEpsMul (κ * θ / p)) 1) ^ (1/θ)) 1)

/-- Superpolynomial-decay core: for `p, κ, θ > 0`, once `x` is large,
`(log x)^p · exp(−κ·(log x)^θ) ≤ 1`.  (Polynomial-in-`log x` beaten by a stretched exponential.)
Universal-cutoff form (X-chase). -/
theorem log_rpow_mul_exp_neg_le_one_atX {p κ θ : ℝ} (hp : 0 < p) (hκ : 0 < κ) (hθ : 0 < θ) :
    ∀ x : ℝ, X_logRpowExp p κ θ ≤ x →
      (Real.log x) ^ p * Real.exp (-κ * (Real.log x) ^ θ) ≤ 1 := by
  have hs₀ := log_le_eps_mul_real_atX (ε := κ * θ / p) (by positivity)
  set s₀ : ℝ := X_logEpsMul (κ * θ / p) with hs₀def
  rw [show X_logRpowExp p κ θ = Real.exp (max ((max s₀ 1) ^ (1/θ)) 1) from rfl]
  intro x hx
  have hlogx : (max ((max s₀ 1) ^ (1/θ)) 1) ≤ Real.log x := by
    rw [← Real.log_exp (max ((max s₀ 1) ^ (1/θ)) 1)]
    exact Real.log_le_log (Real.exp_pos _) hx
  set w : ℝ := Real.log x with hwdef
  have hw1 : (1 : ℝ) ≤ w := le_trans (le_max_right _ _) hlogx
  have hwpos : 0 < w := lt_of_lt_of_le one_pos hw1
  have hwbig : (max s₀ 1) ^ (1/θ) ≤ w := le_trans (le_max_left _ _) hlogx
  set s : ℝ := w ^ θ with hsdef
  have hspos : 0 < s := Real.rpow_pos_of_pos hwpos θ
  have hsbig : max s₀ 1 ≤ s := by
    have hmono : ((max s₀ 1) ^ (1/θ)) ^ θ ≤ w ^ θ :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_max_of_le_right zero_le_one) _) hwbig hθ.le
    rwa [← Real.rpow_mul (le_max_of_le_right zero_le_one), one_div_mul_cancel hθ.ne',
      Real.rpow_one] at hmono
  have hkey : p * Real.log w ≤ κ * s := by
    have hs0 : s₀ ≤ s := le_trans (le_max_left _ _) hsbig
    have hlogs := hs₀ s hs0
    have hws : w = s ^ (1/θ) := by
      rw [hsdef, ← Real.rpow_mul hwpos.le, mul_one_div, div_self hθ.ne', Real.rpow_one]
    have hlogw : Real.log w = (1/θ) * Real.log s := by
      rw [hws, Real.log_rpow hspos]
    rw [hlogw]
    rw [show p * ((1/θ) * Real.log s) = (p/θ) * Real.log s by ring]
    have hpθ : 0 < p / θ := by positivity
    calc (p/θ) * Real.log s ≤ (p/θ) * ((κ * θ / p) * s) :=
          mul_le_mul_of_nonneg_left hlogs hpθ.le
      _ = κ * s := by field_simp [hp.ne', hθ.ne']
  have hexp : w ^ p ≤ Real.exp (κ * s) := by
    rw [Real.rpow_def_of_pos hwpos]
    exact Real.exp_le_exp.mpr (by rw [mul_comm (Real.log w) p]; exact hkey)
  calc w ^ p * Real.exp (-κ * s)
      ≤ Real.exp (κ * s) * Real.exp (-κ * s) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, show κ * s + -κ * s = 0 by ring, Real.exp_zero]

/-- ∃-form of `log_rpow_mul_exp_neg_le_one_atX` (X-chase: `x₀ := X_logRpowExp p κ θ`). -/
theorem log_rpow_mul_exp_neg_le_one {p κ θ : ℝ} (hp : 0 < p) (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (Real.log x) ^ p * Real.exp (-κ * (Real.log x) ^ θ) ≤ 1 :=
  ⟨X_logRpowExp p κ θ, log_rpow_mul_exp_neg_le_one_atX hp hκ hθ⟩

/-- Inline copy of `pre_eq_fin_sum_castLE` (lives in Sec6, not visible here). -/
theorem pre_eq_fin_sum_castLE' {n : ℕ} (a : Fin n → ℕ) {r : ℕ} (h : r ≤ n) :
    pre a r = ∑ i : Fin r, a (Fin.castLE h i) := by
  rw [pre, ← Fin.sum_univ_eq_sum_range (fun i => if hh : i < n then a ⟨i, hh⟩ else 0) r]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dif_pos (lt_of_lt_of_le i.isLt h)]
  rfl

/-- Inline copy of `iidMap_pre` (Sec6): under `geomHalf.iid n`, the prefix sum `pre a r` is
distributed as `iidSum geomHalf r`, for `r ≤ n`. -/
theorem iidMap_pre' (n r : ℕ) (h : r ≤ n) :
    (geomHalf.iid n).map (fun a : Fin n → ℕ => pre a r) = iidSum geomHalf r := by
  have hcomp : (fun a : Fin n → ℕ => pre a r)
      = (fun w : Fin r → ℕ => ∑ i, w i) ∘ (fun a : Fin n → ℕ => a ∘ Fin.castLE h) := by
    funext a; simp only [Function.comp_apply]; rw [pre_eq_fin_sum_castLE' a h]
  rw [hcomp, ← PMF.map_comp, iid_map_castLE geomHalf r n h]
  rfl

/-- The `Gweight_prefix_decay` rate (X-chase): the `κ`-witness copied verbatim from its proof. -/
noncomputable def K_Gweight (d : ℝ) : ℝ := min (4 * d ^ 2) d

theorem K_Gweight_pos {d : ℝ} (hd : 0 < d) : 0 < K_Gweight d :=
  lt_min (by positivity) hd

/-- The `Gweight_prefix_decay` cutoff (X-chase): witness copied verbatim from its proof. -/
noncomputable def X_Gweight : ℝ := Real.exp 20

/-- Universal-cutoff form of `Gweight_prefix_decay` (X-chase), at the explicit rate
`K_Gweight d` and cutoff `X_Gweight`. -/
theorem Gweight_prefix_decay_atX {d : ℝ} (hd : 0 < d) :
    ∀ x : ℝ, X_Gweight ≤ x → ∀ n : ℕ, n ≤ nZero x →
      Gweight (1 + n) (d * (Real.log x ^ (0.6:ℝ)))
        ≤ 2 * Real.exp (-(K_Gweight d) * (Real.log x ^ (0.2:ℝ))) := by
  rw [show X_Gweight = Real.exp 20 from rfl,
    show K_Gweight d = min (4 * d ^ 2) d from rfl]
  refine fun x hx n hn => ?_
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set L : ℝ := Real.log x with hLdef
  have hL20 : (20 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 20]; exact Real.log_le_log (Real.exp_pos _) hx
  have hLpos : 0 < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  set P02 : ℝ := L ^ (0.2 : ℝ) with hP02
  set P06 : ℝ := L ^ (0.6 : ℝ) with hP06
  have hP02pos : 0 < P02 := Real.rpow_pos_of_pos hLpos _
  have hP06pos : 0 < P06 := Real.rpow_pos_of_pos hLpos _
  have hP02ge1 : (1 : ℝ) ≤ P02 := Real.one_le_rpow hL1 (by norm_num)
  have hP0602 : P02 ≤ P06 := by
    rw [hP02, hP06]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hP06sq : P06 ^ 2 = L * P02 := by
    rw [hP06, hP02, ← Real.rpow_natCast (L ^ (0.6:ℝ)) 2, ← Real.rpow_mul hLpos.le,
      show (0.6:ℝ) * (2:ℕ) = 1.2 by push_cast; norm_num,
      show (1.2:ℝ) = 1 + 0.2 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := le_of_lt (by have := Real.log_two_gt_d9; linarith)
  have hnZ : (nZero x : ℝ) ≤ L / 5 := by
    have hfloor : (nZero x : ℝ) ≤ L / (10 * Real.log 2) := by
      rw [hLdef]; unfold nZero; exact Nat.floor_le (by positivity)
    refine le_trans hfloor
      ((div_le_div_iff_of_pos_left hLpos (by linarith) (by norm_num)).mpr (by linarith))
  have hnR : (n : ℝ) ≤ L / 5 := le_trans (by exact_mod_cast hn) hnZ
  have h1n4 : (1 : ℝ) + n ≤ L / 4 := by
    have h20 : (1 : ℝ) ≤ L / 20 := by linarith
    have : L / 5 + L / 20 ≤ L / 4 := by linarith
    linarith
  have h1npos : (0 : ℝ) < 1 + n := by positivity
  set κ : ℝ := min (4 * d ^ 2) d with hκdef
  have hκpos : 0 < κ := lt_min (by positivity) hd
  have hexpand : (d * P06) ^ 2 = d ^ 2 * (L * P02) := by rw [mul_pow, hP06sq]
  have hterm1 : Real.exp (-((d * P06) ^ 2) / (1 + n)) ≤ Real.exp (-κ * P02) := by
    apply Real.exp_le_exp.mpr
    have hκle : κ ≤ 4 * d ^ 2 := min_le_left _ _
    have hkey : κ * P02 * (1 + n) ≤ (d * P06) ^ 2 := by
      rw [hexpand]
      calc κ * P02 * (1 + n) ≤ 4 * d ^ 2 * P02 * (L / 4) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hκle hP02pos.le) h1n4 h1npos.le (by positivity)
        _ = d ^ 2 * (L * P02) := by ring
    rw [neg_div, neg_mul, neg_le_neg_iff, le_div_iff₀ h1npos]
    exact hkey
  have hterm2 : Real.exp (-|d * P06|) ≤ Real.exp (-κ * P02) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg (by positivity), neg_mul]
    have hκd : κ ≤ d := min_le_right _ _
    have hkey2 : κ * P02 ≤ d * P06 :=
      le_trans (mul_le_mul_of_nonneg_right hκd hP02pos.le) (mul_le_mul_of_nonneg_left hP0602 hd.le)
    linarith
  calc Gweight (1 + n) (d * P06)
      = Real.exp (-((d * P06) ^ 2) / (1 + n)) + Real.exp (-|d * P06|) := by simp only [Gweight]
    _ ≤ Real.exp (-κ * P02) + Real.exp (-κ * P02) := add_le_add hterm1 hterm2
    _ = 2 * Real.exp (-κ * P02) := by ring

/-- The prefix Gweight decay: for `d > 0`, each `Gweight (1+n) (d·log^{0.6} x)` with `n ≤ nZero x`
is bounded by a stretched exponential `2·exp(−κ·log^{0.2} x)`.  (Both the `exp(−·²/(1+n))` term
— using `1+n ≤ log x / 4` — and the `exp(−d·log^{0.6}x)` term dominate `exp(−κ log^{0.2}x)`.)
∃-form: delegates to `Gweight_prefix_decay_atX` (X-chase). -/
theorem Gweight_prefix_decay {d : ℝ} (hd : 0 < d) :
    ∃ κ x₀ : ℝ, 0 < κ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ n : ℕ, n ≤ nZero x →
      Gweight (1 + n) (d * (Real.log x ^ (0.6:ℝ)))
        ≤ 2 * Real.exp (-κ * (Real.log x ^ (0.2:ℝ))) :=
  ⟨K_Gweight d, X_Gweight, K_Gweight_pos hd, Gweight_prefix_decay_atX hd⟩

/-- Prefix analogue of `iid_geomHalf_overflow_eq`, two-sided: the prefix deviation mass under
`geomHalf.iid n₀` equals the `iidSum geomHalf n` deviation mass, for `n ≤ n₀`. -/
theorem iid_prefix_twosided_eq (n₀ n : ℕ) (h : n ≤ n₀) (lam : ℝ) :
    (∑' a : Fin n₀ → ℕ, if lam ≤ |(pre a n : ℝ) - 2 * n| then ((geomHalf.iid n₀) a).toReal else 0)
      = (∑' L : ℕ, if lam ≤ |(L : ℝ) - 2 * n| then ((iidSum geomHalf n) L).toReal else 0) := by
  let E : Set ℕ := {L | lam ≤ |(L : ℝ) - 2 * n|}
  have hmap := PMF.expect_map_of_nonneg (geomHalf.iid n₀) (fun a => pre a n)
    (Set.indicator E 1) (fun L => Set.indicator_nonneg (fun _ _ => zero_le_one) L)
  rw [iidMap_pre' n₀ n h] at hmap
  unfold PMF.expect at hmap
  simpa only [Function.comp_apply, E, Set.indicator, Set.mem_setOf_eq, Pi.one_apply,
    mul_ite, mul_one, mul_zero] using hmap.symm

-- `first_passage_approx` (RATIFY-C8, Prop 5.2 / (5.8)) is proved at the END of this file
-- (after its sub-lemmas `first_passage_window_reduce` + `first_passage_affine_reindex`).

/-! ## Named decomposition of C8 (route + probe)

Two probabilistic sub-lemmas carry the analytic content of Prop 5.2; the rest of the proof is
pointwise event algebra (the `B_{n,y}` chain and the Lemma 2.1 affine bijection). Pinning these as
named `sorry`s converts the orange C8 seam into visible, attackable holes. -/

/-! **Paper (5.12)** — the good-tuple union bound.  Outside an event of probability `≪ log^{-c} x`
(the paper takes `log^{-10} x`), the full length-`n₀` valuation vector of `N_y` lies in the
good-tuple set `𝒜⁽ⁿ⁰⁾`.  The union-bound skeleton (`expect_le_add_of_indicator_le` +
`expect_le_sum_of_indicator_le` + `not_goodTuple_iff_prefix_dev`) is proved in
`approx_good_tuple_whp`; the analytic per-prefix bound is `goodTuple_prefix_dev_sum`.
From (5.4) [C5 / Prop 1.9, axiom-clean] and Lemma 2.2 [S3, two-sided, axiom-clean] each prefix
deviates by `≥ log^{0.6} x` w.p. `≪ exp(−c log^{0.2} x)`; sum over the `n₀ + 1` prefixes.
**Does not use C7.** -/

/-- Effective-constants campaign: the `c`-witness of `goodTuple_prefix_dev_sum` — the (5.12)
prefix-deviation sum decays at the full rate `1`. -/
noncomputable def c_goodTupleDev : ℝ := 1

theorem c_goodTupleDev_pos : 0 < c_goodTupleDev := by norm_num [c_goodTupleDev]

/-- The (5.12) per-prefix deviation constant: `2·Ct + Cd` at `Ct = C_geomTail`,
`Cd = C_valuationDistC K_intTest` (big-C campaign, step 2).

(The `_atC` below is the **(5.12) analytic core** — the summed per-prefix deviation bound.
Each of the `n₀ + 1` prefixes `valSum N n` deviates from its mean `2n` by `≥ log^{0.6} x`
with probability `≪ exp(−c log^{0.2} x)` (transfer to `geomHalf.iid` via C5
`valuation_dist`, then the two-sided S3 `geomHalf_tail_bound`); the sum over prefixes is
still `≪ log^{-c} x`.  This is the ONLY analytic hole of `approx_good_tuple_whp` — the
union-bound skeleton around it is proved.) -/
noncomputable def C_goodTupleDev : ℝ := 2 * C_geomTail + C_valuationDistC K_intTest

theorem C_goodTupleDev_pos : 0 < C_goodTupleDev := by
  unfold C_goodTupleDev
  nlinarith [C_geomTail_pos, C_valuationDistC_pos K_intTest_pos]

/-- The `goodTuple_prefix_dev_sum` cutoff (X-chase): the witness max-tree copied verbatim
from the `_atC` proof, with the obtained locals replaced by their explicit upstream names
(`κ := K_Gweight c_geomTail`, `cq := c_valuationDist 1 / 20`). -/
noncomputable def X_goodTupleDev : ℝ :=
  max X_intTestLogUnif
    (max (X_logRpowExp 2 (K_Gweight c_geomTail) 0.2)
      (max X_rpowNZero
        (max (X_logRpowExp 2 (c_valuationDist 1 / 20) 1) (max (Real.exp 20) X_Gweight))))

/-- Universal-cutoff form of `goodTuple_prefix_dev_sum_atC` (X-chase). -/
theorem goodTuple_prefix_dev_sum_atCX :
    ∀ x : ℝ, X_goodTupleDev ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        ∑ n ∈ Finset.range (nZero x + 1),
            (logUnifOdd y (y ^ alpha)).expect
              (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
          ≤ C_goodTupleDev * (Real.log x) ^ (-c_goodTupleDev) := by
  rw [show c_goodTupleDev = 1 from rfl]
  have herr := integral_test_logUnif_atCX
  have hdist := valuation_dist_atC 1 K_intTest (by norm_num) K_intTest_pos
  have htail := geomHalf_tail_bound_atC
  set Cd : ℝ := C_valuationDistC K_intTest with hCddef
  have hCd : 0 < Cd := C_valuationDistC_pos K_intTest_pos
  set K : ℝ := K_intTest with hKdef
  have hK : 0 < K := K_intTest_pos
  set Ct : ℝ := C_geomTail with hCtdef
  have hCt : 0 < Ct := C_geomTail_pos
  set ct : ℝ := c_geomTail with hctdef
  have hct : 0 < ct := c_geomTail_pos
  set cd : ℝ := c_valuationDist 1 with hcddef
  have hcd : 0 < cd := c_valuationDist_pos one_pos
  have hκ : 0 < K_Gweight ct := K_Gweight_pos hct
  have hGdecay := Gweight_prefix_decay_atX (d := ct) hct
  have hA := log_rpow_mul_exp_neg_le_one_atX (p := 2) (κ := K_Gweight ct) (θ := 0.2)
    (by norm_num) hκ (by norm_num)
  have hcq : 0 < cd / 20 := by positivity
  have hqle := two_rpow_neg_nZero_le_atX hcd
  have hB := log_rpow_mul_exp_neg_le_one_atX (p := 2) (κ := cd / 20) (θ := 1)
    (by norm_num) hcq (by norm_num)
  set κ : ℝ := K_Gweight ct with hκdef
  set cq : ℝ := cd / 20 with hcqdef
  set x₀e : ℝ := X_intTestLogUnif with hx₀edef
  set x₀A : ℝ := X_logRpowExp 2 κ 0.2 with hx₀Adef
  set x₀q : ℝ := X_rpowNZero with hx₀qdef
  set x₀B : ℝ := X_logRpowExp 2 cq 1 with hx₀Bdef
  set x₀g : ℝ := X_Gweight with hx₀gdef
  rw [show C_goodTupleDev = 2 * Ct + Cd from rfl]
  rw [show X_goodTupleDev
      = max x₀e (max x₀A (max x₀q (max x₀B (max (Real.exp 20) x₀g)))) from rfl]
  intro x hx y hy
  simp only [max_le_iff] at hx
  obtain ⟨hxe, hxA, hxq, hxB, hx20, hxg⟩ := hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 20) hx20
  have hL20 : (20 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 20]; exact Real.log_le_log (Real.exp_pos _) hx20
  have hLpos : 0 < Real.log x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx20
  have hlam : (0 : ℝ) ≤ Real.log x ^ (0.6 : ℝ) := Real.rpow_nonneg hLpos.le _
  -- window preliminaries (mirror valSum_lower_geom)
  have hy1 : (1 : ℝ) ≤ y := by
    rcases hy with h | h <;> rw [h] <;>
      · rw [show (1 : ℝ) = (1 : ℝ) ^ (_ : ℝ) from (Real.one_rpow _).symm]
        exact Real.rpow_le_rpow (by norm_num) hx1 (by unfold alpha; positivity)
  have hyα1 : (1 : ℝ) ≤ y ^ alpha := by
    rw [show (1 : ℝ) = (1 : ℝ) ^ alpha from (Real.one_rpow _).symm]
    exact Real.rpow_le_rpow (by norm_num) hy1 (by unfold alpha; positivity)
  have hodd : ∀ N ∈ (logUnifOdd y (y ^ alpha)).support, N % 2 = 1 :=
    fun N hN => (logUnifOdd_support_le hyα1 hN).1
  have hsize : (2 + 1) * (nZero x : ℝ) ≤ ((3 * nZero x : ℕ) : ℝ) := le_of_eq (by push_cast; ring)
  have hmod : PMF.dTV ((logUnifOdd y (y ^ alpha)).map fun N => (N : ZMod (2 ^ (3 * nZero x))))
      (unifOddMod (3 * nZero x)) ≤ K * (2 : ℝ) ^ (-((3 * nZero x : ℕ) : ℝ)) := by
    rw [show ((3 * nZero x : ℕ) : ℝ) = 3 * (nZero x : ℝ) by push_cast; ring]
    exact herr x hxe y hy
  have hdistPQ := hdist (nZero x) (3 * nZero x) (logUnifOdd y (y ^ alpha)) hsize hodd hmod
  set P₀ : PMF (Fin (nZero x) → ℕ) := (logUnifOdd y (y ^ alpha)).map fun N => valVec N (nZero x)
    with hP₀def
  set Q₀ : PMF (Fin (nZero x) → ℕ) := geomHalf.iid (nZero x) with hQ₀def
  -- hdistPQ : P₀.dTV Q₀ ≤ Cd * 2^(-cd * n₀)
  -- STEP: per-prefix bound
  have hStep : ∀ n ∈ Finset.range (nZero x + 1),
      (logUnifOdd y (y ^ alpha)).expect
          (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
        ≤ Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ)) + P₀.dTV Q₀ := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hnle : n ≤ nZero x := by omega
    -- transfer to P₀
    have htarget : (logUnifOdd y (y ^ alpha)).expect
        (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
        = P₀.expect (Set.indicator
            {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1) := by
      rw [hP₀def, PMF.expect_map_of_nonneg (logUnifOdd y (y ^ alpha)) (fun N => valVec N (nZero x))
        (Set.indicator {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
        (fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) a)]
      unfold PMF.expect
      apply tsum_congr; intro N; congr 1
      simp only [Function.comp_apply, Set.indicator_apply, Set.mem_setOf_eq,
        pre_valVec hnle, Pi.one_apply]
    have hev := PMF.abs_expect_indicator_sub_le_dTV P₀ Q₀
      {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|}
    have hXe : P₀.expect (Set.indicator
          {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
        ≤ Q₀.expect (Set.indicator
          {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
          + P₀.dTV Q₀ := by
      have := le_abs_self (P₀.expect (Set.indicator
        {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
        - Q₀.expect (Set.indicator
        {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1))
      linarith [hev, this]
    have hQside : Q₀.expect (Set.indicator
          {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
        ≤ Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ)) := by
      have hexpand : Q₀.expect (Set.indicator
          {a : Fin (nZero x) → ℕ | Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|} 1)
          = ∑' a : Fin (nZero x) → ℕ,
              if Real.log x ^ (0.6 : ℝ) ≤ |(pre a n : ℝ) - 2 * n|
                then (Q₀ a).toReal else 0 := by
        unfold PMF.expect
        apply tsum_congr; intro a
        simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, mul_ite, mul_one, mul_zero]
      rw [hexpand, hQ₀def, iid_prefix_twosided_eq (nZero x) n hnle (Real.log x ^ (0.6 : ℝ))]
      exact htail n (Real.log x ^ (0.6 : ℝ)) hlam
    rw [htarget]; linarith [hXe, hQside]
  -- sum the steps
  have hsum1 := Finset.sum_le_sum hStep
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum1
  -- bound the Gweight sum by (n₀+1)·(Ct·2·exp(-κ·log^{0.2}x))
  have hGsum : ∑ n ∈ Finset.range (nZero x + 1), Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ))
      ≤ ((nZero x + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ)))) := by
    have hle : ∀ n ∈ Finset.range (nZero x + 1),
        Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ))
          ≤ Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) := fun n hn =>
      mul_le_mul_of_nonneg_left (hGdecay x hxg n (by rw [Finset.mem_range] at hn; omega)) hCt.le
    calc ∑ n ∈ Finset.range (nZero x + 1), Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ))
        ≤ ∑ _n ∈ Finset.range (nZero x + 1), Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) :=
          Finset.sum_le_sum hle
      _ = ((nZero x + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- (n₀+1 : ℝ) ≤ log x
  have hnZ5 : (nZero x : ℝ) ≤ Real.log x / 5 := by
    have hfloor : (nZero x : ℝ) ≤ Real.log x / (10 * Real.log 2) := by
      unfold nZero; exact Nat.floor_le (by positivity)
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := le_of_lt (by have := Real.log_two_gt_d9; linarith)
    exact le_trans hfloor
      ((div_le_div_iff_of_pos_left hLpos (by linarith) (by norm_num)).mpr (by linarith))
  have hn1L : ((nZero x + 1 : ℕ) : ℝ) ≤ Real.log x := by push_cast; linarith [hnZ5]
  -- the "shrink" step: log x · E ≤ (log x)^{-1} when (log x)^2 · E ≤ 1
  have shrink : ∀ E : ℝ, 0 ≤ E → (Real.log x) ^ (2 : ℝ) * E ≤ 1 →
      Real.log x * E ≤ (Real.log x) ^ (-(1 : ℝ)) := by
    intro E hE0 hE
    have h1 : (Real.log x) ^ (-(1 : ℝ)) * (Real.log x) ^ (2 : ℝ) = Real.log x := by
      rw [← Real.rpow_add hLpos]; norm_num
    calc Real.log x * E = ((Real.log x) ^ (-(1 : ℝ)) * (Real.log x) ^ (2 : ℝ)) * E := by rw [h1]
      _ = (Real.log x) ^ (-(1 : ℝ)) * ((Real.log x) ^ (2 : ℝ) * E) := by ring
      _ ≤ (Real.log x) ^ (-(1 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hLpos.le _)
      _ = (Real.log x) ^ (-(1 : ℝ)) := mul_one _
  -- A-term: the Gweight-decay sum contribution
  have hAterm : ((nZero x + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))))
      ≤ 2 * Ct * (Real.log x) ^ (-(1 : ℝ)) := by
    have hE0 : (0 : ℝ) ≤ Real.exp (-κ * Real.log x ^ (0.2 : ℝ)) := (Real.exp_pos _).le
    have hs := shrink _ hE0 (hA x hxA)
    calc ((nZero x + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))))
        = 2 * Ct * (((nZero x + 1 : ℕ) : ℝ) * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) := by ring
      _ ≤ 2 * Ct * (Real.log x * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn1L hE0) (by positivity)
      _ ≤ 2 * Ct * (Real.log x) ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_left hs (by positivity)
  -- B-term: the dTV contribution
  have hBterm : ((nZero x + 1 : ℕ) : ℝ) * (P₀.dTV Q₀) ≤ Cd * (Real.log x) ^ (-(1 : ℝ)) := by
    have hdtv : P₀.dTV Q₀ ≤ Cd * x ^ (-cq) :=
      le_trans hdistPQ (mul_le_mul_of_nonneg_left (hqle x hxq) hCd.le)
    have hxexp : x ^ (-cq) = Real.exp (-cq * (Real.log x) ^ (1 : ℝ)) := by
      rw [Real.rpow_one, Real.rpow_def_of_pos hxpos, mul_comm (Real.log x) (-cq)]
    have hE0 : (0 : ℝ) ≤ Real.exp (-cq * (Real.log x) ^ (1 : ℝ)) := (Real.exp_pos _).le
    have hs := shrink _ hE0 (hB x hxB)
    calc ((nZero x + 1 : ℕ) : ℝ) * (P₀.dTV Q₀)
        ≤ ((nZero x + 1 : ℕ) : ℝ) * (Cd * x ^ (-cq)) :=
          mul_le_mul_of_nonneg_left hdtv (by positivity)
      _ = Cd * (((nZero x + 1 : ℕ) : ℝ) * Real.exp (-cq * (Real.log x) ^ (1 : ℝ))) := by
          rw [hxexp]; ring
      _ ≤ Cd * (Real.log x * Real.exp (-cq * (Real.log x) ^ (1 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn1L hE0) hCd.le
      _ ≤ Cd * (Real.log x) ^ (-(1 : ℝ)) := mul_le_mul_of_nonneg_left hs hCd.le
  -- assemble
  calc ∑ n ∈ Finset.range (nZero x + 1),
          (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
      ≤ (∑ n ∈ Finset.range (nZero x + 1), Ct * Gweight (1 + n) (ct * Real.log x ^ (0.6 : ℝ)))
          + ((nZero x + 1 : ℕ) : ℝ) * (P₀.dTV Q₀) := hsum1
    _ ≤ ((nZero x + 1 : ℕ) : ℝ) * (Ct * (2 * Real.exp (-κ * Real.log x ^ (0.2 : ℝ))))
          + ((nZero x + 1 : ℕ) : ℝ) * (P₀.dTV Q₀) := by linarith [hGsum]
    _ ≤ 2 * Ct * (Real.log x) ^ (-(1 : ℝ)) + Cd * (Real.log x) ^ (-(1 : ℝ)) := by
        linarith [hAterm, hBterm]
    _ = (2 * Ct + Cd) * (Real.log x) ^ (-(1 : ℝ)) := by ring

/-- ∃-form of `goodTuple_prefix_dev_sum_atCX` (X-chase: `x₀ := X_goodTupleDev`). -/
theorem goodTuple_prefix_dev_sum_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        ∑ n ∈ Finset.range (nZero x + 1),
            (logUnifOdd y (y ^ alpha)).expect
              (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
          ≤ C_goodTupleDev * (Real.log x) ^ (-c_goodTupleDev) :=
  ⟨X_goodTupleDev, goodTuple_prefix_dev_sum_atCX⟩

/-- Original explicit-`c` form: delegates to `goodTuple_prefix_dev_sum_atC` (big-C
campaign, step 2: `C := C_goodTupleDev`). -/
theorem goodTuple_prefix_dev_sum_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        ∑ n ∈ Finset.range (nZero x + 1),
            (logUnifOdd y (y ^ alpha)).expect
              (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
          ≤ C * (Real.log x) ^ (-c_goodTupleDev) := by
  obtain ⟨x₀, h⟩ := goodTuple_prefix_dev_sum_atC
  exact ⟨C_goodTupleDev, x₀, C_goodTupleDev_pos, h⟩

theorem goodTuple_prefix_dev_sum :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        ∑ n ∈ Finset.range (nZero x + 1),
            (logUnifOdd y (y ^ alpha)).expect
              (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1)
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := goodTuple_prefix_dev_sum_explicit
  exact ⟨c_goodTupleDev, C, x₀, c_goodTupleDev_pos, hC, h⟩

/-- The `approx_good_tuple_whp` cutoff (X-chase): witness copied verbatim from the
`_atC` proof (`max x₀ 1` at the explicit upstream). -/
noncomputable def X_goodTupleWhp : ℝ := max X_goodTupleDev 1

/-- Universal-cutoff form of `approx_good_tuple_whp_atC` (X-chase). -/
theorem approx_good_tuple_whp_atCX :
    ∀ x : ℝ, X_goodTupleWhp ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
          ≤ C_goodTupleDev * (Real.log x) ^ (-c_goodTupleDev) := by
  have hsum := goodTuple_prefix_dev_sum_atCX
  set C : ℝ := C_goodTupleDev with hCdef
  have hC : 0 < C := C_goodTupleDev_pos
  set c : ℝ := c_goodTupleDev with hcdef
  have hc : 0 < c := c_goodTupleDev_pos
  set x₀ : ℝ := X_goodTupleDev with hx₀def
  rw [show X_goodTupleWhp = max x₀ 1 from rfl]
  refine fun x hx y hy => ?_
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hyα1 : (1 : ℝ) ≤ y ^ alpha := by
    have hy1 : (1 : ℝ) ≤ y := by
      rcases hy with h | h <;> rw [h] <;>
        · rw [show (1 : ℝ) = (1 : ℝ) ^ (_ : ℝ) from (Real.one_rpow _).symm]
          exact Real.rpow_le_rpow (by norm_num) hx1 (by unfold alpha; positivity)
    rw [show (1 : ℝ) = (1 : ℝ) ^ alpha from (Real.one_rpow _).symm]
    exact Real.rpow_le_rpow (by norm_num) hy1 (by unfold alpha; positivity)
  set P := logUnifOdd y (y ^ alpha) with hPdef
  have heven0 : P.expect (Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1) = 0 := by
    have hzero : ∀ a, (P a).toReal * Set.indicator {N : ℕ | ¬ (N % 2 = 1)} (1 : ℕ → ℝ) a = 0 := by
      intro a
      by_cases ha : P a = 0
      · rw [ha]; simp
      · have hmem : a ∈ P.support := ha
        have hodd : a % 2 = 1 := (logUnifOdd_support_le hyα1 hmem).1
        rw [Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq, not_not]; exact hodd)]; ring
    show ∑' a, (P a).toReal * Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1 a = 0
    simp_rw [hzero]; exact tsum_zero
  have hpw1 : ∀ N, Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} (1 : ℕ → ℝ) N ≤
      Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1 N +
      Set.indicator {N | ∃ n ∈ Finset.range (nZero x + 1),
        Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1 N := by
    intro N
    have h1 : (0 : ℝ) ≤ Set.indicator {N : ℕ | ¬ (N % 2 = 1)} (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    have h2 : (0 : ℝ) ≤ Set.indicator {N | ∃ n ∈ Finset.range (nZero x + 1),
        Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    by_cases hN : N ∈ {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))}
    · rw [Set.indicator_of_mem hN, Pi.one_apply]
      by_cases hodd : N % 2 = 1
      · have hmem : N ∈ {N | ∃ n ∈ Finset.range (nZero x + 1),
            Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} :=
          (not_goodTuple_iff_prefix_dev hodd).mp hN
        rw [Set.indicator_of_mem hmem, Pi.one_apply]; linarith
      · rw [Set.indicator_of_mem (show N ∈ {N : ℕ | ¬ (N % 2 = 1)} from hodd), Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hN]; linarith
  have hpw2 : ∀ N, Set.indicator {N | ∃ n ∈ Finset.range (nZero x + 1),
        Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} (1 : ℕ → ℝ) N ≤
      ∑ n ∈ Finset.range (nZero x + 1),
        Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1 N := by
    intro N
    by_cases hN : N ∈ {N | ∃ n ∈ Finset.range (nZero x + 1),
        Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|}
    · rw [Set.indicator_of_mem hN, Pi.one_apply]
      obtain ⟨n, hn, hdev⟩ := hN
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun k => Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N k : ℝ) - 2 * k|}
          (1 : ℕ → ℝ) N)
        (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) N) hn)
      rw [Set.indicator_of_mem (show N ∈ {M | Real.log x ^ (0.6 : ℝ) ≤ |(valSum M n : ℝ) - 2 * n|}
        from hdev), Pi.one_apply]
    · rw [Set.indicator_of_notMem hN]
      exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) N)
  calc P.expect (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
      ≤ P.expect (Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1)
          + P.expect (Set.indicator {N | ∃ n ∈ Finset.range (nZero x + 1),
              Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1) :=
        expect_le_add_of_indicator_le _ _ _ _ hpw1
    _ = P.expect (Set.indicator {N | ∃ n ∈ Finset.range (nZero x + 1),
              Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1) := by rw [heven0]; ring
    _ ≤ ∑ n ∈ Finset.range (nZero x + 1),
          P.expect (Set.indicator {N | Real.log x ^ (0.6 : ℝ) ≤ |(valSum N n : ℝ) - 2 * n|} 1) :=
        expect_le_sum_of_indicator_le _ _ _ _ hpw2
    _ ≤ C * (Real.log x) ^ (-c) := hsum x hx0 y hy

/-- ∃-form of `approx_good_tuple_whp_atCX` (X-chase: `x₀ := X_goodTupleWhp`). -/
theorem approx_good_tuple_whp_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
          ≤ C_goodTupleDev * (Real.log x) ^ (-c_goodTupleDev) :=
  ⟨X_goodTupleWhp, approx_good_tuple_whp_atCX⟩

/-- Sibling of `approx_good_tuple_whp` with the `c`-slot pinned to `c_goodTupleDev`
(passthrough); the original delegates here.  Now delegates to `approx_good_tuple_whp_atC`
(big-C campaign, step 2: `C := C_goodTupleDev`). -/
theorem approx_good_tuple_whp_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
          ≤ C * (Real.log x) ^ (-c_goodTupleDev) := by
  obtain ⟨x₀, h⟩ := approx_good_tuple_whp_atC
  exact ⟨C_goodTupleDev, x₀, C_goodTupleDev_pos, h⟩

theorem approx_good_tuple_whp :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := approx_good_tuple_whp_explicit
  exact ⟨c_goodTupleDev, C, x₀, c_goodTupleDev_pos, hC, h⟩

/-- **(5.16) edge half-width** `s(x) := log^{0.8} x`.  This is the multiplicative log-scale radius
around the window endpoints inside which the passage-time estimate (5.15) can push `T_x(N)` out of
`I_y`.  On the good event (5.15) gives `T_x(N) = log(N/x)/log(4/3) + O(log^{0.6}x)`, so `T_x(N) < IyLo`
forces `log(N/y) < log(4/3)·log^{0.8}x + O(log^{0.6}x) ≤ log^{0.8}x = s` (as `log(4/3) < 1`), and
symmetrically `T_x(N) > IyHi` forces `log(y^α/N) < s`. -/
noncomputable def sEdge (x : ℝ) : ℝ := Real.log x ^ (0.8 : ℝ)

/-- **(5.16) edge window** — the odd `N` within a multiplicative factor `exp(s x)` of an endpoint of
the log-uniform window `[y, y^α]`: either `N ≤ y·exp(s)` (lower edge) or `y^α·exp(−s) ≤ N` (upper
edge).  Off the support (`N > y^α`) the upper disjunct holds trivially, so `Edge` also absorbs the
"beyond the window" tail; the log-uniform mass of `Edge` is the integral-test quantity `≍ log^{-0.2}x`
(`passtime_edge_mass`). -/
noncomputable def Edge (x y : ℝ) : Set ℕ :=
  {N | (N : ℝ) ≤ y * Real.exp (sEdge x) ∨ y ^ alpha * Real.exp (- sEdge x) ≤ (N : ℝ)}

/-- The `passtime_edge_of_good` cutoff (X-chase): witness copied verbatim from its proof. -/
noncomputable def X_edgeOfGood : ℝ := Real.exp 100000

-- HEARTBEAT: the (5.15) interval-algebra proof carries ~40 chained `have`s over the orbit
-- estimate + three margin lemmas; the single proof term exceeds the default whnf budget.
set_option maxHeartbeats 1600000 in
/-- **(5.16) passage-time inclusion — the (5.15) estimate, PROVED.**  On the good-tuple event, if `N`
passes but its passage time lands outside `I_y`, then `N` is within a factor `exp(s x)` of a window
endpoint, i.e. `N ∈ Edge x y`.  This is the pointwise heart of (5.16): the orbit estimate (proved,
`syr_iterate_good_bracket'`) gives `T_x(N) = log(N/x)/log(4/3) + O(log^{0.6}x)` (5.15), and the two
endpoint inequalities `T_x < IyLo`, `T_x > IyHi` translate into the two edge disjuncts.
Route (owed): from `syr_iterate_good_bracket'` derive (a) `T_x(N) ≥ (log(N/x) − log2·log^{0.6}x)/log(4/3)`
(lower orbit bound ⇒ `Syr^{T} ≤ x` forces `T` large), and (b) `T_x(N) ≤ n*` for the explicit
`n* = ⌈(log(N/x) + O(log^{0.6}x))/log(4/3)⌉ ≤ nZero x` witnessing `Syr^{n*} ≤ x` (upper orbit bound,
absorbing the `+3^{n*}` rounding since `3^{n*} ≤ x/2` in range); then rearrange against `IyLo`/`IyHi`
(`log(4/3) > 0`) and `log(4/3)·log^{0.8}x + O(log^{0.6}x) ≤ log^{0.8}x` for `x` large.
Universal-cutoff form (X-chase). -/
theorem passtime_edge_of_good_atX :
    1 ≤ X_edgeOfGood ∧ ∀ x : ℝ, X_edgeOfGood ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ N : ℕ, N % 2 = 1 →
        goodTuple x (nZero x) (valVec N (nZero x)) →
        passes ⌊x⌋₊ N → passTime ⌊x⌋₊ N ∉ Iy x y → N ∈ Edge x y := by
  classical
  rw [show X_edgeOfGood = Real.exp 100000 from rfl]
  refine ⟨Real.one_le_exp (by norm_num), fun x hx y hy N hodd hgood hpass hTnotIy => ?_⟩
  -- positivity / basic
  have hxe : Real.exp 100000 ≤ x := hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (100000 : ℝ)]) hxe
  have hxpos : 0 < x := by linarith
  set ℓ := Real.log x with hℓdef
  have hℓbig : (100000 : ℝ) ≤ ℓ := by
    rw [hℓdef, ← Real.log_exp 100000]; exact Real.log_le_log (Real.exp_pos _) hxe
  have hℓpos : 0 < ℓ := by linarith
  -- constants
  have hb_lo : (0.693 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hb_hi : Real.log 2 < (0.694 : ℝ) := by have := Real.log_two_lt_d9; linarith
  have hb_pos : 0 < Real.log 2 := by linarith
  have hg_hi : Real.log (4 / 3) ≤ (1 / 3 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4/3 by norm_num); linarith
  have hg_lo : (1 / 4 : ℝ) ≤ Real.log (4 / 3) := by
    rw [show (4:ℝ)/3 = (3/4)⁻¹ by norm_num, Real.log_inv]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3/4 by norm_num); linarith
  have hg_pos : 0 < Real.log (4 / 3) := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
  -- u-substitution basis
  set u := ℓ ^ (0.2 : ℝ) with hudef
  have hupos : 0 < u := Real.rpow_pos_of_pos hℓpos _
  have hu10 : (10 : ℝ) ≤ u := by
    rw [hudef]
    have h1 : ((100000 : ℝ)) ^ (0.2 : ℝ) ≤ ℓ ^ (0.2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hℓbig (by norm_num)
    have h2 : ((100000 : ℝ)) ^ (0.2 : ℝ) = 10 := by
      rw [show (100000:ℝ) = (10:ℝ) ^ (5:ℕ) by norm_num, ← Real.rpow_natCast (10:ℝ) 5,
        ← Real.rpow_mul (by norm_num)]; norm_num
    linarith [h2 ▸ h1]
  have hu3 : ℓ ^ (0.6 : ℝ) = u ^ 3 := by
    rw [hudef, ← Real.rpow_natCast (ℓ ^ (0.2:ℝ)) 3, ← Real.rpow_mul hℓpos.le]; norm_num
  have hu4 : ℓ ^ (0.8 : ℝ) = u ^ 4 := by
    rw [hudef, ← Real.rpow_natCast (ℓ ^ (0.2:ℝ)) 4, ← Real.rpow_mul hℓpos.le]; norm_num
  have hu5 : ℓ = u ^ 5 := by
    rw [hudef, ← Real.rpow_natCast (ℓ ^ (0.2:ℝ)) 5, ← Real.rpow_mul hℓpos.le]; norm_num
  -- abbreviations for s = log^{0.8} x, L = log^{0.6} x
  set s := ℓ ^ (0.8 : ℝ) with hsdef
  set L := ℓ ^ (0.6 : ℝ) with hLdef
  have hspos : 0 < s := Real.rpow_pos_of_pos hℓpos _
  have hLpos : 0 < L := Real.rpow_pos_of_pos hℓpos _
  clear_value ℓ u s L
  -- the three margin inequalities (pure in ℓ,s,L), proved via u-substitution + nlinarith
  have hg1 : (1 - Real.log (4 / 3)) ≥ (2 / 3 : ℝ) := by linarith
  -- (i)   L·b ≤ s·(1-g)
  have hMargI : L * Real.log 2 ≤ s * (1 - Real.log (4 / 3)) := by
    have hinner : Real.log 2 ≤ u * (1 - Real.log (4 / 3)) := by nlinarith [hu10, hg_hi, hupos, hb_hi]
    rw [hu3, hu4]
    have hstep : u ^ 3 * Real.log 2 ≤ u ^ 3 * (u * (1 - Real.log (4 / 3))) :=
      mul_le_mul_of_nonneg_left hinner (pow_pos hupos 3).le
    nlinarith [hstep]
  -- (ii)  L·b + (b+g) ≤ s·(1-g)
  have hMargII : L * Real.log 2 + (Real.log 2 + Real.log (4 / 3)) ≤ s * (1 - Real.log (4 / 3)) := by
    have hinner : Real.log 2 + (Real.log 2 + Real.log (4 / 3)) ≤ u * (u * (1 - Real.log (4 / 3))) := by
      nlinarith [hu10, hg_hi, hupos, hb_hi, hg_lo]
    rw [hu3, hu4]
    have hstep : u ^ 3 * Real.log 2 ≤ u ^ 3 * (u * (1 - Real.log (4 / 3))) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hu10, hg_hi, hupos, hb_hi] :
        Real.log 2 ≤ u * (1 - Real.log (4 / 3))) (pow_pos hupos 3).le
    nlinarith [hstep, hinner, pow_pos hupos 3]
  -- (iii) b·L + (g+b) ≤ (30/1000)·ℓ + s   (the T ≤ ν margin)
  have hMargIII : L * Real.log 2 + (Real.log (4 / 3) + Real.log 2)
      ≤ (30 / 1000 : ℝ) * ℓ + s := by
    rw [hu3, hu4, hu5]
    have hbL : u ^ 3 * Real.log 2 ≤ u ^ 4 := by
      have : u ^ 3 * Real.log 2 ≤ u ^ 3 * 1 := by nlinarith [pow_pos hupos 3, hb_hi]
      nlinarith [this, hu10, pow_pos hupos 3]
    nlinarith [hbL, hu10, hg_hi, hb_hi, pow_pos hupos 4, pow_pos hupos 5]
  -- alpha facts
  have halpha1 : (1 : ℝ) ≤ alpha := by unfold alpha; norm_num
  have halpha_pos : (0 : ℝ) < alpha := by unfold alpha; norm_num
  have halpha3 : alpha ^ 3 ≤ (1004 / 1000 : ℝ) := by unfold alpha; norm_num
  have halpha_gt1 : (1 : ℝ) < alpha := by unfold alpha; norm_num
  have halpha_le2 : alpha ≤ alpha ^ 2 := by unfold alpha; norm_num
  -- sEdge x = s
  have hs_eq : sEdge x = s := by rw [sEdge, hsdef, hℓdef]
  -- unfold Edge and do contrapositive
  simp only [Edge, Set.mem_setOf_eq, hs_eq]
  by_contra hcon
  push Not at hcon
  obtain ⟨hIntLo, hIntHi⟩ := hcon
  -- y > 0
  have hy0 : 0 < y := by rcases hy with h | h <;> rw [h] <;> exact Real.rpow_pos_of_pos hxpos _
  set LY := Real.log y with hLYdef
  -- N positive
  have hNRpos : (0 : ℝ) < (N : ℝ) := lt_trans (mul_pos hy0 (Real.exp_pos s)) hIntLo
  -- log of interior bounds
  have hlogNlo : LY + s < Real.log (N : ℝ) := by
    have h := Real.log_lt_log (mul_pos hy0 (Real.exp_pos s)) hIntLo
    rwa [Real.log_mul hy0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  have hlogNhi : Real.log (N : ℝ) < alpha * LY + (-s) := by
    have h := Real.log_lt_log hNRpos hIntHi
    rwa [Real.log_mul (Real.rpow_pos_of_pos hy0 alpha).ne' (Real.exp_pos _).ne',
      Real.log_rpow hy0, Real.log_exp] at h
  -- log y ≤ alpha^2 · ℓ, hence alpha·log y ≤ alpha^3·ℓ
  have hlogy_le : LY ≤ alpha ^ 2 * ℓ := by
    rcases hy with h | h
    · rw [hLYdef, h, Real.log_rpow hxpos, ← hℓdef]
      calc alpha * ℓ = 1 * (alpha * ℓ) := (one_mul _).symm
        _ ≤ alpha * (alpha * ℓ) :=
            mul_le_mul_of_nonneg_right halpha1 (mul_nonneg halpha_pos.le hℓpos.le)
        _ = alpha ^ 2 * ℓ := by ring
    · rw [hLYdef, h, Real.log_rpow hxpos, ← hℓdef]
  have hlogN_ub : Real.log (N : ℝ) < (1004 / 1000 : ℝ) * ℓ - s := by
    have h1 : alpha * LY ≤ alpha ^ 3 * ℓ := by
      calc alpha * LY ≤ alpha * (alpha ^ 2 * ℓ) := mul_le_mul_of_nonneg_left hlogy_le halpha_pos.le
        _ = alpha ^ 3 * ℓ := by ring
    have h2 : alpha ^ 3 * ℓ ≤ (1004 / 1000 : ℝ) * ℓ := mul_le_mul_of_nonneg_right halpha3 hℓpos.le
    linarith
  -- ν bounds
  set ν := nZero x with hνdef
  have hνnn : (0 : ℝ) ≤ (ν : ℝ) := Nat.cast_nonneg _
  have h10b_pos : (0 : ℝ) < 10 * Real.log 2 := by linarith
  have hν_le : (ν : ℝ) * (10 * Real.log 2) ≤ ℓ := by
    have h : (ν : ℝ) ≤ ℓ / (10 * Real.log 2) := by
      rw [hνdef, hℓdef]; unfold nZero
      exact Nat.floor_le (div_nonneg (Real.log_nonneg hx1.le) (mul_nonneg (by norm_num) hb_pos.le))
    exact (le_div_iff₀ h10b_pos).mp h
  have hν_lb : ℓ < ((ν : ℝ) + 1) * (10 * Real.log 2) := by
    have h : ℓ / (10 * Real.log 2) < (ν : ℝ) + 1 := by
      rw [hνdef, hℓdef]; exact_mod_cast Nat.lt_floor_add_one _
    exact (div_lt_iff₀ h10b_pos).mp h
  clear_value ν
  -- ν·g lower bound (feeds step iii)
  have hgb : (34 / 1000 : ℝ) ≤ Real.log (4 / 3) / (10 * Real.log 2) := by
    rw [le_div_iff₀ h10b_pos]; linarith only [hg_lo, hb_hi]
  have hνg : (34 / 1000 : ℝ) * ℓ - Real.log (4 / 3) ≤ (ν : ℝ) * Real.log (4 / 3) := by
    have hfrac : ℓ / (10 * Real.log 2) - 1 < (ν : ℝ) := by
      have h := (div_lt_iff₀ h10b_pos).mpr hν_lb; linarith only [h]
    have h2 : ℓ / (10 * Real.log 2) * Real.log (4 / 3) - Real.log (4 / 3)
        ≤ (ν : ℝ) * Real.log (4 / 3) := by
      have := mul_le_mul_of_nonneg_right hfrac.le hg_pos.le; nlinarith only [this]
    have h3 : (34 / 1000 : ℝ) * ℓ ≤ ℓ / (10 * Real.log 2) * Real.log (4 / 3) := by
      have hm := mul_le_mul_of_nonneg_left hgb hℓpos.le
      calc (34 / 1000 : ℝ) * ℓ = ℓ * (34 / 1000) := by ring
        _ ≤ ℓ * (Real.log (4 / 3) / (10 * Real.log 2)) := hm
        _ = ℓ / (10 * Real.log 2) * Real.log (4 / 3) := by ring
    linarith only [h2, h3]
  -- 3^ν ≤ x/2  (feeds steps ii,iii)
  have h2ν : 2 * (ν : ℝ) ≤ ℓ - Real.log 2 := by
    have hprod : (0 : ℝ) ≤ (ν : ℝ) * (Real.log 2 - 0.693) :=
      mul_nonneg hνnn (by linarith only [hb_lo])
    nlinarith only [hν_le, hb_lo, hb_hi, hℓbig, hνnn, hprod]
  have h3ν : (3 : ℝ) ^ ν ≤ x / 2 := by
    have hlog : Real.log ((3 : ℝ) ^ ν) ≤ Real.log (x / 2) := by
      rw [Real.log_pow, Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0), ← hℓdef]
      have hle3 : (ν : ℝ) * Real.log 3 ≤ (ν : ℝ) * 2 := mul_le_mul_of_nonneg_left hlog3 hνnn
      linarith only [hle3, h2ν]
    exact (Real.log_le_log_iff (by positivity) (by linarith only [hxpos] : (0 : ℝ) < x / 2)).mp hlog
  -- rewriting helpers for the orbit slack exponent
  have hLval : Real.log x ^ (0.6 : ℝ) = L := by rw [← hℓdef, ← hLdef]
  have hsval : Real.log x ^ (0.8 : ℝ) = s := by rw [← hℓdef, ← hsdef]
  have hlog34 : Real.log (3 / 4) = -Real.log (4 / 3) := by
    rw [show (3 : ℝ) / 4 = (4 / 3)⁻¹ by norm_num, Real.log_inv]
  -- reusable log expansion for (3/4)^m · N · 2^e
  have hlogexp : ∀ (m : ℕ) (e : ℝ),
      Real.log ((3 / 4 : ℝ) ^ m * (N : ℝ) * (2 : ℝ) ^ e)
        = (m : ℝ) * Real.log (3 / 4) + Real.log (N : ℝ) + e * Real.log 2 := by
    intro m e
    rw [Real.log_mul (mul_pos (by positivity : (0:ℝ) < (3/4:ℝ)^m) hNRpos).ne'
          (by positivity : (0:ℝ) < (2:ℝ)^e).ne',
        Real.log_mul (by positivity : (0:ℝ) < (3/4:ℝ)^m).ne' hNRpos.ne',
        Real.log_pow, Real.log_rpow (by norm_num)]
  -- passage-time facts
  set T := passTime ⌊x⌋₊ N with hTdef
  have hne : {n | syr^[n] N ≤ ⌊x⌋₊}.Nonempty := hpass
  have hTmem : syr^[T] N ≤ ⌊x⌋₊ := Nat.sInf_mem hne
  have hxfloor_le : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hTmemR : (syr^[T] N : ℝ) ≤ x := le_trans (by exact_mod_cast hTmem) hxfloor_le
  -- N > ⌊x⌋₊  (so T ≥ 1)
  have hxα_gt : x < x ^ alpha := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hx1 halpha_gt1
    rwa [Real.rpow_one] at h
  have hyge : x ^ alpha ≤ y := by
    rcases hy with h | h
    · rw [h]
    · rw [h]; exact Real.rpow_le_rpow_of_exponent_le hx1.le halpha_le2
  have hNbig : ((⌊x⌋₊ : ℕ) : ℝ) < (N : ℝ) := by
    have h1 : x ^ alpha ≤ y * Real.exp s :=
      calc x ^ alpha = x ^ alpha * 1 := (mul_one _).symm
        _ ≤ y * Real.exp s := mul_le_mul hyge (Real.one_le_exp hspos.le) (by norm_num) hy0.le
    linarith only [hIntLo, hxα_gt, h1, hxfloor_le]
  have hT1 : 1 ≤ T := by
    rcases Nat.eq_zero_or_pos T with h0 | h
    · exfalso; rw [h0] at hTmem
      simp only [Function.iterate_zero, id] at hTmem
      have : (N : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hTmem
      linarith only [hNbig, this]
    · exact h
  -- STEP (iii): T ≤ ν
  obtain ⟨_, hUpν⟩ := syr_iterate_good_bracket' x N ν ν hodd hgood (le_refl _)
  rw [hLval] at hUpν
  have hmainν_half : (3 / 4 : ℝ) ^ ν * (N : ℝ) * 2 ^ L ≤ x / 2 := by
    have hlog : Real.log ((3 / 4 : ℝ) ^ ν * (N : ℝ) * 2 ^ L) ≤ Real.log (x / 2) := by
      rw [hlogexp ν L, hlog34, Real.log_div hxpos.ne' (by norm_num : (2:ℝ) ≠ 0), ← hℓdef]
      linarith only [hνg, hlogN_ub, hMargIII]
    exact (Real.log_le_log_iff
      (mul_pos (mul_pos (by positivity : (0:ℝ) < (3/4:ℝ)^ν) hNRpos) (by positivity : (0:ℝ) < (2:ℝ)^L))
      (by linarith only [hxpos] : (0:ℝ) < x/2)).mp hlog
  have hν_final : (syr^[ν] N : ℝ) ≤ x := le_trans hUpν (by linarith only [hmainν_half, h3ν])
  have hTν : T ≤ ν := by
    rw [hTdef]; exact Nat.sInf_le (Nat.le_floor hν_final)
  -- STEP (i): IyLo ≤ T
  have hIyLo : IyLo x y ≤ (T : ℝ) := by
    obtain ⟨hLoT, _⟩ := syr_iterate_good_bracket' x N ν T hodd hgood hTν
    rw [hLval] at hLoT
    have hle : (3 / 4 : ℝ) ^ T * (N : ℝ) * 2 ^ (-L) ≤ x := le_trans hLoT hTmemR
    have hlogle : (T : ℝ) * Real.log (3 / 4) + Real.log (N : ℝ) + (-L) * Real.log 2 ≤ ℓ := by
      rw [← hlogexp T (-L), hℓdef]
      exact Real.log_le_log
        (mul_pos (mul_pos (by positivity : (0:ℝ) < (3/4:ℝ)^T) hNRpos) (by positivity : (0:ℝ) < (2:ℝ)^(-L))) hle
    rw [hlog34] at hlogle
    have hTg : Real.log (N : ℝ) - L * Real.log 2 - ℓ ≤ (T : ℝ) * Real.log (4 / 3) := by
      nlinarith only [hlogle]
    have hkey : Real.log y - ℓ + s * Real.log (4 / 3) ≤ (T : ℝ) * Real.log (4 / 3) := by
      linarith only [hTg, hlogNlo, hMargI]
    rw [IyLo, hsval, Real.log_div hy0.ne' hxpos.ne', ← hℓdef, ← hLYdef,
      div_add' _ _ _ hg_pos.ne', div_le_iff₀ hg_pos]
    linarith only [hkey]
  -- STEP (ii): T ≤ IyHi
  have hIyHi : (T : ℝ) ≤ IyHi x y := by
    obtain ⟨_, hUpTm⟩ := syr_iterate_good_bracket' x N ν (T - 1) hodd hgood (by omega : T - 1 ≤ ν)
    rw [hLval] at hUpTm
    have hnm : ¬ (syr^[T - 1] N ≤ ⌊x⌋₊) := by
      intro hle
      have hh : passTime ⌊x⌋₊ N ≤ T - 1 := Nat.sInf_le hle
      rw [← hTdef] at hh; omega
    have hprevnat : ⌊x⌋₊ < syr^[T - 1] N := Nat.lt_of_not_le hnm
    have hprevR : x < (syr^[T - 1] N : ℝ) := by
      have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have h2 : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ (syr^[T - 1] N : ℝ) := by exact_mod_cast hprevnat
      linarith only [h1, h2]
    have h3Tm : (3 : ℝ) ^ (T - 1) ≤ x / 2 :=
      le_trans (pow_le_pow_right₀ (by norm_num) (by omega : T - 1 ≤ ν)) h3ν
    have hmain'half : x / 2 < (3 / 4 : ℝ) ^ (T - 1) * (N : ℝ) * 2 ^ L := by
      linarith only [hprevR, hUpTm, h3Tm]
    have hloglt : Real.log (x / 2)
        < (T : ℝ) * Real.log (3 / 4) - Real.log (3 / 4) + Real.log (N : ℝ) + L * Real.log 2 := by
      have h := Real.log_lt_log (by linarith only [hxpos] : (0:ℝ) < x/2) hmain'half
      rw [hlogexp (T - 1) L] at h
      rw [Nat.cast_sub hT1, Nat.cast_one] at h
      nlinarith only [h]
    rw [Real.log_div hxpos.ne' (by norm_num : (2:ℝ) ≠ 0), ← hℓdef, hlog34] at hloglt
    have hkey2 : (T : ℝ) * Real.log (4 / 3) ≤ alpha * Real.log y - ℓ - s * Real.log (4 / 3) := by
      nlinarith only [hloglt, hlogNhi, hMargII]
    rw [IyHi, hsval, Real.log_div (Real.rpow_pos_of_pos hy0 alpha).ne' hxpos.ne',
      Real.log_rpow hy0, ← hℓdef, ← hLYdef, le_sub_iff_add_le, le_div_iff₀ hg_pos]
    nlinarith only [hkey2]
  -- CONCLUDE: T ∈ Iy x y, contradicting hTnotIy
  have hTin : T ∈ Iy x y :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by rw [← hνdef]; omega), hIyLo, hIyHi⟩
  exact hTnotIy hTin

/-- ∃-form of `passtime_edge_of_good_atX` (X-chase: `x₀ := X_edgeOfGood`). -/
theorem passtime_edge_of_good :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ N : ℕ, N % 2 = 1 →
        goodTuple x (nZero x) (valVec N (nZero x)) →
        passes ⌊x⌋₊ N → passTime ⌊x⌋₊ N ∉ Iy x y → N ∈ Edge x y :=
  ⟨X_edgeOfGood, passtime_edge_of_good_atX.1, passtime_edge_of_good_atX.2⟩

open Classical in
/-- **Log-uniform indicator expectation as a window-mass ratio.**  For a nonempty window, the
`logUnifOdd` expectation of `𝟙_S` equals the `S`-restricted reciprocal sum over the window divided by
the total window mass `D = windowMass`.  This is the plumbing that turns a `Log`-scale probability into
the integral-test quantity `(∑_{N ∈ W ∩ S} 1/N)/D`. -/
theorem logUnifOdd_expect_indicator_eq {lo hi : ℝ} (h : (logWindow lo hi).Nonempty) (S : Set ℕ) :
    (logUnifOdd lo hi).expect (Set.indicator S 1)
      = (∑ N ∈ (logWindow lo hi).filter (fun N => N ∈ S), (N : ℝ)⁻¹) / windowMass lo hi := by
  classical
  -- every window element is a nonzero natural (odd), so `(N:ℝ≥0∞)⁻¹ ≠ ⊤`
  have hne : ∀ N ∈ logWindow lo hi, (N : ℝ≥0∞) ≠ 0 := by
    intro N hN
    simp only [logWindow, Finset.mem_filter] at hN
    have : N % 2 = 1 := hN.2.1
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  -- `D.toReal = windowMass`
  have hD : (∑ M ∈ logWindow lo hi, (M : ℝ≥0∞)⁻¹).toReal = windowMass lo hi := by
    rw [ENNReal.toReal_sum (fun M hM => ENNReal.inv_ne_top.mpr (hne M hM))]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  -- reduce the `tsum` to the finite window
  unfold PMF.expect
  rw [tsum_eq_sum (s := logWindow lo hi) (fun N hN => by
    rw [logUnifOdd_apply_of_nonempty h, if_neg hN, ENNReal.toReal_zero, zero_mul])]
  rw [Finset.sum_div, Finset.sum_filter]
  refine Finset.sum_congr rfl fun N hN => ?_
  have hPN : ((logUnifOdd lo hi) N).toReal = (N : ℝ)⁻¹ / windowMass lo hi := by
    rw [logUnifOdd_apply_of_nonempty h, if_pos hN, ENNReal.toReal_div, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, hD]
  rw [hPN, Set.indicator_apply]
  by_cases hS : N ∈ S <;> simp [hS]

/-- **Window normalizer grows like `log x`** — the integral-test denominator lower bound.
`windowMass y (y^α) = ∑_{N∈[y,y^α] odd} 1/N ≥ c·log x` for large `x`.  Sharper than `intTest_D_lower`
(which only needs a positive constant): here the `(α−1)/2·log y ≍ log x` growth is what makes the edge
slabs a `log^{-0.2}x` fraction of the whole window.  Proof: the window is the odd AP `{a+2i : i<count}`
(as in `intTest_D_lower`), so `harmonic_ap_integral_bound` gives
`windowMass ≥ ½·log((a+2·count)/a) − 1/a ≥ ½·((α−1)log y − 3/y) − 1/y`, and `log y ≥ α·log x`. -/
theorem windowMass_ge_clog_at :
    ∀ x : ℝ, (2:ℝ) ^ (2000:ℝ) ≤ x → ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
      (1 / 10000 : ℝ) * Real.log x ≤ windowMass y (y ^ alpha) := by
  intro x hx y hy
  have hx2000 : (2:ℝ) ^ (2000:ℝ) ≤ x := hx
  have hyset : y = x ^ alpha ∨ y = x ^ alpha ^ 2 := by simpa [Set.mem_insert_iff] using hy
  obtain ⟨hMy, h2y⟩ := window_arith hx2000 hyset
  -- basic size facts (mirrors intTest_D_lower)
  have hx1 : (1:ℝ) ≤ x := by
    refine le_trans ?_ hx2000
    rw [show (1:ℝ) = (2:ℝ) ^ (0:ℝ) from (Real.rpow_zero 2).symm]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxy : x ≤ y := by
    rcases hyset with h | h <;> rw [h] <;>
      · nth_rewrite 1 [show x = x ^ (1:ℝ) from (Real.rpow_one x).symm]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by unfold alpha; norm_num)
  have hy8 : (8:ℝ) ≤ y := by
    refine le_trans ?_ (le_trans hx2000 hxy)
    have h1 : (2:ℝ) ^ (3:ℝ) ≤ (2:ℝ) ^ (2000:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h2 : (2:ℝ) ^ (3:ℝ) = 8 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h2] at h1; exact h1
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le (by norm_num) hy8
  -- `log y ≥ α·log x`
  have hlogx0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hlogy_ge : alpha * Real.log x ≤ Real.log y := by
    rcases hyset with h | h
    · rw [h, Real.log_rpow hx0]
    · rw [h, Real.log_rpow hx0]
      have hmul : alpha * Real.log x ≤ alpha ^ 2 * Real.log x :=
        mul_le_mul_of_nonneg_right (by unfold alpha; nlinarith) hlogx0
      linarith
  have hlogxbig : (1000:ℝ) ≤ Real.log x := by
    have h1 : Real.log ((2:ℝ) ^ (2000:ℝ)) ≤ Real.log x := Real.log_le_log (by positivity) hx2000
    rw [Real.log_rpow (by norm_num)] at h1
    have hl2 : (0.6931:ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    nlinarith [h1, hl2]
  -- make `y^α` opaque (linarith chokes on the decimal-rpow atom)
  obtain ⟨Yα, hYα⟩ : ∃ Y : ℝ, y ^ alpha = Y := ⟨y ^ alpha, rfl⟩
  rw [hYα] at h2y ⊢
  have hyα0 : (0:ℝ) ≤ Yα := by linarith only [h2y, hy8]
  have hyαpos : (0:ℝ) < Yα := by linarith only [h2y, hy8]
  have hlogYα : Real.log Yα = alpha * Real.log y := by rw [← hYα, Real.log_rpow hy0]
  -- ===== AP decomposition of the window (mirrors intTest_D_lower) =====
  set ylo : ℕ := ⌈y⌉₊ with hylodef
  set yhi : ℕ := ⌊Yα⌋₊ with hyhidef
  have hylo_ge : y ≤ (ylo : ℝ) := Nat.le_ceil y
  have hylo_lt : (ylo : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
  have hyhi_le : (yhi : ℝ) ≤ Yα := Nat.floor_le hyα0
  have hyhi_gt : Yα - 1 < (yhi : ℝ) := by linarith [Nat.lt_floor_add_one Yα]
  have hex : ∃ N, ylo ≤ N ∧ N % 2 = 1 := ⟨2 * ylo + 1, by omega, by omega⟩
  set a : ℕ := Nat.find hex with hadef
  obtain ⟨haylo, haodd⟩ : ylo ≤ a ∧ a % 2 = 1 := Nat.find_spec hex
  have ha_lt : a < ylo + 2 := by
    by_contra hcon
    push Not at hcon
    exact Nat.find_min hex (show a - 2 < a by omega) ⟨by omega, by omega⟩
  have haR : (a : ℝ) < y + 3 := by
    have h1 : (a : ℝ) < (ylo : ℝ) + 2 := by exact_mod_cast ha_lt
    linarith [hylo_lt]
  have hay : y ≤ (a : ℝ) := le_trans hylo_ge (by exact_mod_cast haylo)
  have haleyα : (a : ℝ) < Yα := by linarith only [haR, h2y, hy8]
  have ha_yhi : a ≤ yhi := by rw [hyhidef]; exact Nat.le_floor haleyα.le
  set count : ℕ := (yhi - a) / 2 + 1 with hcountdef
  have hinj : ∀ i ∈ Finset.range count, ∀ j ∈ Finset.range count,
      a + 2 * i = a + 2 * j → i = j := by intro i _ j _ h; omega
  have hFeq : logWindow y Yα = (Finset.range count).image (fun i => a + 2 * i) := by
    ext N
    simp only [Finset.mem_image, Finset.mem_range, logWindow, Finset.mem_filter,
      Nat.lt_add_one_iff]
    constructor
    · rintro ⟨_, hNodd, hNy, hNyα⟩
      have hNylo : ylo ≤ N := by rw [hylodef]; exact Nat.ceil_le.mpr hNy
      have hNyhi : N ≤ yhi := by rw [hyhidef]; exact Nat.le_floor hNyα
      have haN : a ≤ N := Nat.find_min' hex ⟨hNylo, hNodd⟩
      refine ⟨(N - a) / 2, ?_, ?_⟩
      · have : (N - a) / 2 ≤ (yhi - a) / 2 := Nat.div_le_div_right (Nat.sub_le_sub_right hNyhi a)
        omega
      · omega
    · rintro ⟨i, hi, rfl⟩
      have hle_yhi : a + 2 * i ≤ yhi := by
        have hile : i ≤ (yhi - a) / 2 := by omega
        have hmul : 2 * i ≤ yhi - a := by
          calc 2 * i ≤ 2 * ((yhi - a) / 2) := by omega
            _ ≤ yhi - a := by omega
        omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h1 : a + 2 * i ≤ ⌊Yα⌋₊ := hle_yhi
        have h2 : ⌊Yα⌋₊ ≤ ⌈Yα⌉₊ := Nat.floor_le_ceil _
        omega
      · omega
      · push_cast
        have h0 : (0:ℝ) ≤ 2 * (i : ℝ) := by positivity
        linarith [hay, h0]
      · have hle2 : (a + 2 * i : ℕ) ≤ yhi := hle_yhi
        have hcst : ((a + 2 * i : ℕ) : ℝ) ≤ (yhi : ℝ) := by exact_mod_cast hle2
        linarith [hyhi_le, hcst]
  have hWM : windowMass y Yα = ∑ i ∈ Finset.range count, ((a : ℝ) + 2 * (i : ℝ))⁻¹ := by
    rw [windowMass, hFeq, Finset.sum_image hinj]
    apply Finset.sum_congr rfl; intro i _; push_cast; ring_nf
  -- ===== harmonic integral test on the AP =====
  have ha0R : (0:ℝ) < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hharm := harmonic_ap_integral_bound ha0R (by norm_num : (0:ℝ) < 2) count
  -- `a + 2·count ≥ yhi + 1 > Yα`
  have hcountnat : yhi + 1 ≤ a + 2 * count := by omega
  have hac : (yhi : ℝ) + 1 ≤ (a : ℝ) + 2 * (count : ℝ) := by exact_mod_cast hcountnat
  have hA2C_gt : Yα < (a : ℝ) + 2 * (count : ℝ) := by linarith only [hac, hyhi_gt]
  have hA2C_pos : (0:ℝ) < (a : ℝ) + 2 * (count : ℝ) := lt_trans hyαpos hA2C_gt
  -- lower-bound the log argument: `(a+2count)/a ≥ Yα/(y+3)`
  have hlog_lb : Real.log ((a : ℝ) + 2 * (count : ℝ)) - Real.log (a : ℝ)
      ≥ (alpha - 1) * Real.log y - 3 / y := by
    have hstep1 : Real.log ((a : ℝ) + 2 * (count : ℝ)) ≥ Real.log Yα :=
      Real.log_le_log hyαpos hA2C_gt.le
    have hstep2 : Real.log (a : ℝ) ≤ Real.log (y + 3) :=
      Real.log_le_log ha0R haR.le
    have hstep3 : Real.log (y + 3) ≤ Real.log y + 3 / y := by
      have hfac : y + 3 = y * (1 + 3 / y) := by field_simp
      rw [hfac, Real.log_mul hy0.ne' (by positivity)]
      have hlog1 : Real.log (1 + 3 / y) ≤ 3 / y := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 3/y by positivity)
        linarith
      linarith
    rw [hlogYα] at hstep1
    linarith [hstep1, hstep2, hstep3]
  -- assemble: `windowMass ≥ ½·logdiff − 1/a`
  have hWMlb : (1/2 : ℝ) * ((alpha - 1) * Real.log y - 3 / y) - (a:ℝ)⁻¹ ≤ windowMass y Yα := by
    rw [hWM]
    have h := (abs_le.mp hharm).1
    have hlogdiv : Real.log (((a:ℝ) + 2 * (count:ℝ)) / (a:ℝ))
        = Real.log ((a:ℝ) + 2 * (count:ℝ)) - Real.log (a:ℝ) :=
      Real.log_div hA2C_pos.ne' ha0R.ne'
    rw [hlogdiv] at h
    -- h : -(a⁻¹) ≤ (∑ …) − 2⁻¹·(log(a+2c) − log a)
    nlinarith [h, hlog_lb]
  -- close: `windowMass ≥ ½(α−1)log y − 5/(2y) ≥ (1/10000)·log x`
  have hyinv : y⁻¹ ≤ (8:ℝ)⁻¹ := inv_anti₀ (by norm_num) hy8
  have hainv2 : (a:ℝ)⁻¹ ≤ y⁻¹ := inv_anti₀ hy0 hay
  have hfinal : (1:ℝ) / 10000 * Real.log x
      ≤ (1/2 : ℝ) * ((alpha - 1) * Real.log y - 3 / y) - (a:ℝ)⁻¹ := by
    have h_ly : (1.001:ℝ) * Real.log x ≤ Real.log y := by
      have := hlogy_ge; unfold alpha at this; exact this
    have ha1 : alpha - 1 = (0.001:ℝ) := by unfold alpha; norm_num
    have hb2 : (a:ℝ)⁻¹ ≤ (8:ℝ)⁻¹ := le_trans hainv2 hyinv
    have hb1 : (3:ℝ) / y ≤ 3 / 8 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; nlinarith [hyinv]
    rw [ha1]
    nlinarith [h_ly, hlogxbig, hb1, hb2]
  calc (1:ℝ) / 10000 * Real.log x
      ≤ (1/2 : ℝ) * ((alpha - 1) * Real.log y - 3 / y) - (a:ℝ)⁻¹ := hfinal
    _ ≤ windowMass y Yα := hWMlb

/-- Original ∃-form of the window-normalizer growth bound: delegates to
`windowMass_ge_clog_at` (big-C campaign, step 2: `c := 1/10000`, cutoff `2^2000`). -/
theorem windowMass_ge_clog :
    ∃ c x₀ : ℝ, 0 < c ∧ ∀ x : ℝ, x₀ ≤ x → ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
      c * Real.log x ≤ windowMass y (y ^ alpha) :=
  ⟨1 / 10000, (2:ℝ) ^ (2000:ℝ), by norm_num, windowMass_ge_clog_at⟩

/-- **The log-uniform window is a finite odd arithmetic progression.**  For a nonempty window
`logWindow lo hi` (`lo > 0`), there are `a` (the least odd `≥ ⌈lo⌉`) and a length `count ≥ 1` with
`logWindow lo hi = {a, a+2, …, a+2(count−1)}`, and the endpoints straddle `[lo, hi]`:
`lo ≤ a < lo+3` and `hi < a+2·count ≤ hi+2`.  This packages the AP decomposition (previously inlined in
`intTest_D_lower`) so the integral test (`harmonic_ap_integral_bound`) can be applied uniformly to the
full window and to its edge slabs. -/
theorem logWindow_odd_ap {lo hi : ℝ} (hlo0 : 0 < lo) (hne : (logWindow lo hi).Nonempty) :
    ∃ (a count : ℕ), 0 < count ∧ lo ≤ (a : ℝ) ∧ (a : ℝ) < lo + 3 ∧
      hi < (a : ℝ) + 2 * (count : ℝ) ∧ (a : ℝ) + 2 * (count : ℝ) ≤ hi + 2 ∧
      logWindow lo hi = (Finset.range count).image (fun i => a + 2 * i) := by
  have hhi0 : (0:ℝ) < hi := by
    obtain ⟨N, hN⟩ := hne
    simp only [logWindow, Finset.mem_filter] at hN
    exact lt_of_lt_of_le hlo0 (le_trans hN.2.2.1 hN.2.2.2)
  set ylo : ℕ := ⌈lo⌉₊ with hylodef
  set yhi : ℕ := ⌊hi⌋₊ with hyhidef
  have hylo_ge : lo ≤ (ylo : ℝ) := Nat.le_ceil lo
  have hylo_lt : (ylo : ℝ) < lo + 1 := Nat.ceil_lt_add_one hlo0.le
  have hyhi_le : (yhi : ℝ) ≤ hi := Nat.floor_le hhi0.le
  have hyhi_gt : hi - 1 < (yhi : ℝ) := by linarith [Nat.lt_floor_add_one hi]
  have hex : ∃ N, ylo ≤ N ∧ N % 2 = 1 := ⟨2 * ylo + 1, by omega, by omega⟩
  set a : ℕ := Nat.find hex with hadef
  obtain ⟨haylo, haodd⟩ : ylo ≤ a ∧ a % 2 = 1 := Nat.find_spec hex
  have ha_lt : a < ylo + 2 := by
    by_contra hcon
    push Not at hcon
    exact Nat.find_min hex (show a - 2 < a by omega) ⟨by omega, by omega⟩
  have haR : (a : ℝ) < lo + 3 := by
    have h1 : (a : ℝ) < (ylo : ℝ) + 2 := by exact_mod_cast ha_lt
    linarith [hylo_lt]
  have hloa : lo ≤ (a : ℝ) := le_trans hylo_ge (by exact_mod_cast haylo)
  -- nonempty ⟹ `a ≤ yhi`
  obtain ⟨N₀, hN₀⟩ := hne
  simp only [logWindow, Finset.mem_filter, Finset.mem_range] at hN₀
  have hN₀ylo : ylo ≤ N₀ := by rw [hylodef]; exact Nat.ceil_le.mpr hN₀.2.2.1
  have haN₀ : a ≤ N₀ := Nat.find_min' hex ⟨hN₀ylo, hN₀.2.1⟩
  have hN₀yhi : N₀ ≤ yhi := by rw [hyhidef]; exact Nat.le_floor hN₀.2.2.2
  have ha_yhi : a ≤ yhi := le_trans haN₀ hN₀yhi
  set count : ℕ := (yhi - a) / 2 + 1 with hcountdef
  have hinj : ∀ i ∈ Finset.range count, ∀ j ∈ Finset.range count,
      a + 2 * i = a + 2 * j → i = j := by intro i _ j _ h; omega
  have hFeq : logWindow lo hi = (Finset.range count).image (fun i => a + 2 * i) := by
    ext N
    simp only [Finset.mem_image, Finset.mem_range, logWindow, Finset.mem_filter,
      Nat.lt_add_one_iff]
    constructor
    · rintro ⟨_, hNodd, hNlo, hNhi⟩
      have hNylo : ylo ≤ N := by rw [hylodef]; exact Nat.ceil_le.mpr hNlo
      have hNyhi : N ≤ yhi := by rw [hyhidef]; exact Nat.le_floor hNhi
      have haN : a ≤ N := Nat.find_min' hex ⟨hNylo, hNodd⟩
      refine ⟨(N - a) / 2, ?_, ?_⟩
      · have : (N - a) / 2 ≤ (yhi - a) / 2 := Nat.div_le_div_right (Nat.sub_le_sub_right hNyhi a)
        omega
      · omega
    · rintro ⟨i, hi_lt, rfl⟩
      have hle_yhi : a + 2 * i ≤ yhi := by
        have hile : i ≤ (yhi - a) / 2 := by omega
        have hmul : 2 * i ≤ yhi - a := by
          calc 2 * i ≤ 2 * ((yhi - a) / 2) := by omega
            _ ≤ yhi - a := by omega
        omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h1 : a + 2 * i ≤ yhi := hle_yhi
        have h2 : yhi ≤ ⌈hi⌉₊ := by rw [hyhidef]; exact Nat.floor_le_ceil _
        omega
      · omega
      · push_cast
        have h0 : (0:ℝ) ≤ 2 * (i : ℝ) := by positivity
        linarith [hloa, h0]
      · have hle2 : (a + 2 * i : ℕ) ≤ yhi := hle_yhi
        have hcst : ((a + 2 * i : ℕ) : ℝ) ≤ (yhi : ℝ) := by exact_mod_cast hle2
        linarith [hyhi_le, hcst]
  refine ⟨a, count, by omega, hloa, haR, ?_, ?_, hFeq⟩
  · -- `hi < a + 2·count`
    have hcountnat : yhi + 1 ≤ a + 2 * count := by omega
    have hac : (yhi : ℝ) + 1 ≤ (a : ℝ) + 2 * (count : ℝ) := by exact_mod_cast hcountnat
    linarith only [hac, hyhi_gt]
  · -- `a + 2·count ≤ hi + 2`
    have hcountnat : a + 2 * count ≤ yhi + 2 := by omega
    have hac : (a : ℝ) + 2 * (count : ℝ) ≤ (yhi : ℝ) + 2 := by exact_mod_cast hcountnat
    linarith only [hac, hyhi_le]

/-- **Window mass as an AP reciprocal sum** — glue for the integral test.  In the nonempty case
`windowMass lo hi = ∑_{i<count} 1/(a+2i)` for the AP data of `logWindow_odd_ap`. -/
theorem windowMass_eq_ap_sum {lo hi : ℝ} {a count : ℕ}
    (hFeq : logWindow lo hi = (Finset.range count).image (fun i => a + 2 * i))
    (hinj : ∀ i ∈ Finset.range count, ∀ j ∈ Finset.range count, a + 2 * i = a + 2 * j → i = j) :
    windowMass lo hi = ∑ i ∈ Finset.range count, ((a : ℝ) + 2 * (i : ℝ))⁻¹ := by
  rw [windowMass, hFeq, Finset.sum_image hinj]
  apply Finset.sum_congr rfl; intro i _; push_cast; ring_nf

/-- **Integral-test upper bound on a window mass.**  `windowMass lo hi ≤ ½·log(hi/lo) + 2/lo` for
`1 ≤ lo ≤ hi`.  (Empty window ⇒ `0 ≤` a nonnegative RHS; nonempty ⇒ AP + `harmonic_ap_integral_bound`,
with `a ≥ lo` and `a+2·count ≤ hi+2` giving `log((a+2count)/a) ≤ log(hi/lo) + 2/lo`.)  This is the
companion of `windowMass_ge_clog`; applied to the edge slabs it makes each a `½·s + O(1/lo)` mass. -/
theorem windowMass_le_half_log {lo hi : ℝ} (hlo1 : 1 ≤ lo) (hlohi : lo ≤ hi) :
    windowMass lo hi ≤ (1/2) * Real.log (hi / lo) + 2 / lo := by
  have hlo0 : (0:ℝ) < lo := lt_of_lt_of_le one_pos hlo1
  have hhi0 : (0:ℝ) < hi := lt_of_lt_of_le hlo0 hlohi
  have hlogpos : (0:ℝ) ≤ Real.log (hi / lo) :=
    Real.log_nonneg (by rw [le_div_iff₀ hlo0]; linarith)
  by_cases hne : (logWindow lo hi).Nonempty
  · obtain ⟨a, count, hcount0, hloa, haR, hHiLt, hHiLe, hFeq⟩ := logWindow_odd_ap hlo0 hne
    have hinj : ∀ i ∈ Finset.range count, ∀ j ∈ Finset.range count,
        a + 2 * i = a + 2 * j → i = j := by intro i _ j _ h; omega
    have ha0R : (0:ℝ) < (a : ℝ) := lt_of_lt_of_le hlo0 hloa
    have hA2C_pos : (0:ℝ) < (a : ℝ) + 2 * (count : ℝ) := by positivity
    rw [windowMass_eq_ap_sum hFeq hinj]
    have hharm := (abs_le.mp (harmonic_ap_integral_bound ha0R (by norm_num : (0:ℝ) < 2) count)).2
    have hlogdiv : Real.log (((a:ℝ) + 2 * (count:ℝ)) / (a:ℝ))
        = Real.log ((a:ℝ) + 2 * (count:ℝ)) - Real.log (a:ℝ) := Real.log_div hA2C_pos.ne' ha0R.ne'
    -- `log((a+2count)/a) ≤ log(hi/lo) + 2/lo`
    have hlogub : Real.log (((a:ℝ) + 2 * (count:ℝ)) / (a:ℝ)) ≤ Real.log (hi / lo) + 2 / lo := by
      have hnum : Real.log ((a:ℝ) + 2 * (count:ℝ)) ≤ Real.log (hi + 2) :=
        Real.log_le_log hA2C_pos hHiLe
      have hden : Real.log lo ≤ Real.log (a:ℝ) := Real.log_le_log hlo0 hloa
      have hsplit : Real.log (hi + 2) ≤ Real.log hi + 2 / lo := by
        have hfac : hi + 2 = hi * (1 + 2 / hi) := by field_simp
        rw [hfac, Real.log_mul hhi0.ne' (by positivity)]
        have h1 : Real.log (1 + 2 / hi) ≤ 2 / hi :=
          le_trans (Real.log_le_sub_one_of_pos (by positivity)) (by simp)
        have h2 : (2:ℝ) / hi ≤ 2 / lo := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ hlo0 hlohi) (by norm_num)
        linarith
      rw [hlogdiv, Real.log_div hhi0.ne' hlo0.ne']
      linarith [hnum, hden, hsplit]
    have hainv : (a:ℝ)⁻¹ ≤ (1/2) * (2 / lo) := by
      rw [show (1/2:ℝ) * (2 / lo) = 1 / lo from by ring, one_div]; exact inv_anti₀ hlo0 hloa
    -- `∑ ≤ 2⁻¹·log((a+2count)/a) + a⁻¹ ≤ ½(log(hi/lo)+2/lo) + ½·(2/lo)`
    nlinarith [hharm, hlogub, hainv]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [windowMass, hne, Finset.sum_empty]
    positivity

/-- Membership in `logWindow` is exactly: odd, and in `[lo, hi]` (the range bound is implied). -/
theorem mem_logWindow_iff {lo hi : ℝ} {N : ℕ} :
    N ∈ logWindow lo hi ↔ N % 2 = 1 ∧ lo ≤ (N : ℝ) ∧ (N : ℝ) ≤ hi := by
  simp only [logWindow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    have hle : (N : ℝ) ≤ (⌈hi⌉₊ : ℝ) := le_trans h3 (Nat.le_ceil hi)
    have : N ≤ ⌈hi⌉₊ := by exact_mod_cast hle
    omega

/-- **(5.16) integral-test edge mass — owed.**  The log-uniform mass of the edge window `Edge x y` is
`≪ log^{-c} x`.  This is Tao's "straightforward calculation using the integral test": the log-uniform
law puts mass `≈ log(b/a)/((α−1)log y)` on a sub-interval `[a,b] ⊂ [y, y^α]`, and each edge slab has
`log-width = s x = log^{0.8}x` while the normalizer is `(α−1)log y ≍ log x`, giving mass `≍ log^{-0.2}x`.
Route (owed): reuse `Sec5.FirstPassage`'s `windowMass`/`logUnifOdd_apply_of_nonempty`; bound the
edge-slab partial sum `∑_{N∈slab} 1/N` above by `log((b/a)) + O(1)` (sum ↔ integral, `AntitoneOn.sum_le_integral`
on `t ↦ 1/t`, `integral_inv`) and the full `windowMass` below by `(α−1)log y − O(1)`. -/
noncomputable def c_edgeMass : ℝ := 1/5

theorem c_edgeMass_pos : 0 < c_edgeMass := by norm_num [c_edgeMass]

/-- The (5.16) edge-mass constant: `2/cD` at `cD = 1/10000` (`windowMass_ge_clog_at`)
— big-C campaign, step 2. -/
noncomputable def C_edgeMass : ℝ := 2 / (1 / 10000)

theorem C_edgeMass_pos : 0 < C_edgeMass := by unfold C_edgeMass; norm_num

/-- The `passtime_edge_mass` cutoff (X-chase): witness copied verbatim from the `_atC`
proof (`xn := X_windowBase`, the `logWindow_nonempty_atX` cutoff). -/
noncomputable def X_edgeMass : ℝ :=
  max (max ((2:ℝ) ^ (2000:ℝ)) X_windowBase) ((2:ℝ) ^ (2000:ℝ))

/-- Universal-cutoff form of `passtime_edge_mass_atC` (X-chase). -/
theorem passtime_edge_mass_atCX :
    ∀ x : ℝ, X_edgeMass ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect (Set.indicator (Edge x y) 1)
          ≤ C_edgeMass * (Real.log x) ^ (-c_edgeMass) := by
  classical
  have hnon := logWindow_nonempty_atX
  have hDlb := windowMass_ge_clog_at
  set cD : ℝ := (1 / 10000 : ℝ) with hcDdef
  have hcD : 0 < cD := by rw [hcDdef]; norm_num
  set xD : ℝ := (2:ℝ) ^ (2000:ℝ) with hxDdef
  set xn : ℝ := X_windowBase with hxndef
  rw [show c_edgeMass = 1/5 from rfl, show C_edgeMass = 2/cD from rfl]
  rw [show X_edgeMass = max (max ((2:ℝ) ^ (2000:ℝ)) xn) xD from rfl]
  intro x hx y hy
  have hx2000 : (2:ℝ) ^ (2000:ℝ) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxn : xn ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxD : xD ≤ x := le_trans (le_max_right _ _) hx
  have hyset : y = x ^ alpha ∨ y = x ^ alpha ^ 2 := by simpa [Set.mem_insert_iff] using hy
  obtain ⟨hMy, h2y⟩ := window_arith hx2000 hyset
  have hx1 : (1:ℝ) ≤ x := by
    refine le_trans ?_ hx2000
    rw [show (1:ℝ) = (2:ℝ) ^ (0:ℝ) from (Real.rpow_zero 2).symm]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxy : x ≤ y := by
    rcases hyset with h | h <;> rw [h] <;>
      · nth_rewrite 1 [show x = x ^ (1:ℝ) from (Real.rpow_one x).symm]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by unfold alpha; norm_num)
  have hy8 : (8:ℝ) ≤ y := by
    refine le_trans ?_ (le_trans hx2000 hxy)
    have h1 : (2:ℝ) ^ (3:ℝ) ≤ (2:ℝ) ^ (2000:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h2 : (2:ℝ) ^ (3:ℝ) = 8 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h2] at h1; exact h1
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le (by norm_num) hy8
  have hy1 : (1:ℝ) ≤ y := le_trans (by norm_num) hy8
  have h1ltx : (1:ℝ) < x := by
    refine lt_of_lt_of_le ?_ hx2000
    rw [show (1:ℝ) = (2:ℝ) ^ (0:ℝ) from (Real.rpow_zero 2).symm]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hlogxpos : (0:ℝ) < Real.log x := Real.log_pos h1ltx
  have hlogx1386 : (1386:ℝ) ≤ Real.log x := by
    have h1 : Real.log ((2:ℝ) ^ (2000:ℝ)) ≤ Real.log x := Real.log_le_log (by positivity) hx2000
    rw [Real.log_rpow (by norm_num)] at h1
    have hl2 : (0.6931:ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    nlinarith [h1, hl2]
  have hyαy : y ≤ y ^ alpha := by
    nth_rewrite 1 [← Real.rpow_one y]
    exact Real.rpow_le_rpow_of_exponent_le hy1 (by unfold alpha; norm_num)
  have hyα0 : (0:ℝ) < y ^ alpha := Real.rpow_pos_of_pos hy0 alpha
  -- edge half-width facts (`sEdge x = log^{0.8} x`)
  have hs0 : (0:ℝ) ≤ sEdge x := by unfold sEdge; positivity
  have hexps_pos : (0:ℝ) < Real.exp (sEdge x) := Real.exp_pos _
  have hexps1 : (1:ℝ) ≤ Real.exp (sEdge x) := Real.one_le_exp_iff.mpr hs0
  have hs_half : sEdge x ≤ (1/2) * Real.log x := by
    unfold sEdge
    have hsplit : Real.log x ^ (-(0.2):ℝ) * Real.log x = Real.log x ^ (0.8:ℝ) := by
      nth_rewrite 2 [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add hlogxpos]; norm_num
    have hlog02ge2 : (2:ℝ) ≤ Real.log x ^ (0.2:ℝ) := by
      have h32 : ((32:ℝ))^(0.2:ℝ) = 2 := by
        rw [show (32:ℝ) = (2:ℝ) ^ (5:ℕ) by norm_num, ← Real.rpow_natCast (2:ℝ) 5,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
          show ((5:ℕ):ℝ) * (0.2:ℝ) = 1 by norm_num, Real.rpow_one]
      calc (2:ℝ) = (32:ℝ) ^ (0.2:ℝ) := h32.symm
        _ ≤ Real.log x ^ (0.2:ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith [hlogx1386]) (by norm_num)
    have hneg02 : Real.log x ^ (-(0.2):ℝ) ≤ 1/2 := by
      rw [Real.rpow_neg hlogxpos.le, show (1/2:ℝ) = (2:ℝ)⁻¹ from by norm_num]
      exact inv_anti₀ (by norm_num) hlog02ge2
    calc Real.log x ^ (0.8:ℝ) = Real.log x ^ (-(0.2):ℝ) * Real.log x := hsplit.symm
      _ ≤ (1/2) * Real.log x := mul_le_mul_of_nonneg_right hneg02 hlogxpos.le
  -- `2·exp(sEdge x) ≤ y^α` (so the upper edge slab lies above `1`)
  have hlog2half : Real.log 2 ≤ (1/2) * Real.log x := by
    have h := Real.log_two_lt_d9; nlinarith [hlogx1386, h]
  have h2expx : (2:ℝ) * Real.exp (sEdge x) ≤ x := by
    calc (2:ℝ) * Real.exp (sEdge x)
        = Real.exp (Real.log 2) * Real.exp (sEdge x) := by rw [Real.exp_log (by norm_num)]
      _ = Real.exp (Real.log 2 + sEdge x) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (by linarith [hs_half, hlog2half])
      _ = x := Real.exp_log hx0
  have h2exp : (2:ℝ) * Real.exp (sEdge x) ≤ y ^ alpha := le_trans h2expx (le_trans hxy hyαy)
  have hyαexp_pos : (0:ℝ) < y ^ alpha * Real.exp (-sEdge x) := mul_pos hyα0 (Real.exp_pos _)
  have h2SU : (2:ℝ) ≤ y ^ alpha * Real.exp (-sEdge x) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hexps_pos]; exact h2exp
  -- slab masses via the integral-test upper bound
  have hSL : windowMass y (y * Real.exp (sEdge x)) ≤ (1/2) * sEdge x + 2 / y := by
    have hle := windowMass_le_half_log hy1 (le_mul_of_one_le_right hy0.le hexps1)
    rwa [show y * Real.exp (sEdge x) / y = Real.exp (sEdge x) from by
      rw [mul_comm, mul_div_assoc, div_self hy0.ne', mul_one], Real.log_exp] at hle
  have hSU : windowMass (y ^ alpha * Real.exp (-sEdge x)) (y ^ alpha)
      ≤ (1/2) * sEdge x + 2 / (y ^ alpha * Real.exp (-sEdge x)) := by
    have hlohi : y ^ alpha * Real.exp (-sEdge x) ≤ y ^ alpha := by
      nth_rewrite 2 [← mul_one (y ^ alpha)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith [hs0])) hyα0.le
    have hle := windowMass_le_half_log (by linarith [h2SU]) hlohi
    have hlogeq : Real.log (y ^ alpha / (y ^ alpha * Real.exp (-sEdge x))) = sEdge x := by
      rw [Real.log_div hyα0.ne' hyαexp_pos.ne', Real.log_mul hyα0.ne' (Real.exp_ne_zero _),
        Real.log_exp]; ring
    rwa [hlogeq] at hle
  -- `2 ≤ sEdge x`
  have hspos : (2:ℝ) ≤ sEdge x := by
    unfold sEdge
    have h2 : ((2:ℝ) ^ (1.25:ℝ)) ^ (0.8:ℝ) = 2 := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), show (1.25:ℝ) * 0.8 = 1 by norm_num,
        Real.rpow_one]
    have h1 : (2:ℝ) ^ (1.25:ℝ) ≤ Real.log x := by
      have ha : (2:ℝ) ^ (1.25:ℝ) ≤ (2:ℝ) ^ ((4:ℕ):ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rw [Real.rpow_natCast] at ha; norm_num at ha; linarith [hlogx1386]
    calc (2:ℝ) = ((2:ℝ) ^ (1.25:ℝ)) ^ (0.8:ℝ) := h2.symm
      _ ≤ Real.log x ^ (0.8:ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  -- numerator (edge-slab reciprocal sum) ≤ `2·sEdge x`
  have hnum : (∑ N ∈ (logWindow y (y ^ alpha)).filter (fun N => N ∈ Edge x y), (N : ℝ)⁻¹)
      ≤ 2 * sEdge x := by
    have hsub : (logWindow y (y ^ alpha)).filter (fun N => N ∈ Edge x y) ⊆
        logWindow y (y * Real.exp (sEdge x)) ∪
          logWindow (y ^ alpha * Real.exp (-sEdge x)) (y ^ alpha) := by
      intro N hN
      rw [Finset.mem_filter] at hN
      obtain ⟨hNW, hNE⟩ := hN
      rw [mem_logWindow_iff] at hNW
      obtain ⟨hodd, hylo, hyhi⟩ := hNW
      simp only [Edge, Set.mem_setOf_eq] at hNE
      rw [Finset.mem_union, mem_logWindow_iff, mem_logWindow_iff]
      rcases hNE with hE | hE
      · exact Or.inl ⟨hodd, hylo, hE⟩
      · exact Or.inr ⟨hodd, hE, hyhi⟩
    have hunion : (∑ N ∈ (logWindow y (y ^ alpha)).filter (fun N => N ∈ Edge x y), (N : ℝ)⁻¹)
        ≤ windowMass y (y * Real.exp (sEdge x))
          + windowMass (y ^ alpha * Real.exp (-sEdge x)) (y ^ alpha) := by
      calc (∑ N ∈ (logWindow y (y ^ alpha)).filter (fun N => N ∈ Edge x y), (N : ℝ)⁻¹)
          ≤ ∑ N ∈ logWindow y (y * Real.exp (sEdge x)) ∪
              logWindow (y ^ alpha * Real.exp (-sEdge x)) (y ^ alpha), (N : ℝ)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun N _ _ => by positivity)
        _ ≤ (∑ N ∈ logWindow y (y * Real.exp (sEdge x)), (N : ℝ)⁻¹)
              + ∑ N ∈ logWindow (y ^ alpha * Real.exp (-sEdge x)) (y ^ alpha), (N : ℝ)⁻¹ := by
            rw [← Finset.sum_union_inter]
            exact le_add_of_nonneg_right (Finset.sum_nonneg (fun N _ => by positivity))
        _ = windowMass y (y * Real.exp (sEdge x))
              + windowMass (y ^ alpha * Real.exp (-sEdge x)) (y ^ alpha) := rfl
    have hb1 : (2:ℝ) / y ≤ 1 := (div_le_one hy0).mpr (show (2:ℝ) ≤ y by linarith only [hy8])
    have hb2 : (2:ℝ) / (y ^ alpha * Real.exp (-sEdge x)) ≤ 1 := (div_le_one hyαexp_pos).mpr h2SU
    linarith only [hunion, hSL, hSU, hb1, hb2, hspos]
  -- reduce the expectation to the ratio and close by dividing by `windowMass`
  rw [logUnifOdd_expect_indicator_eq (hnon x hxn y hy) (Edge x y)]
  have hWMpos : (0:ℝ) < windowMass y (y ^ alpha) :=
    lt_of_lt_of_le (by positivity) (hDlb x hxD y hy)
  rw [div_le_iff₀ hWMpos]
  have hLmul : Real.log x ^ (-(1/5):ℝ) * Real.log x = Real.log x ^ (0.8:ℝ) := by
    nth_rewrite 2 [← Real.rpow_one (Real.log x)]
    rw [← Real.rpow_add hlogxpos]; norm_num
  have hErpow : 2 / cD * Real.log x ^ (-(1/5):ℝ) * (cD * Real.log x)
      = 2 * Real.log x ^ (0.8:ℝ) := by
    rw [show 2 / cD * Real.log x ^ (-(1/5):ℝ) * (cD * Real.log x)
        = (cD / cD) * (2 * (Real.log x ^ (-(1/5):ℝ) * Real.log x)) from by ring,
      div_self (ne_of_gt hcD), one_mul, hLmul]
  calc (∑ N ∈ (logWindow y (y ^ alpha)).filter (fun N => N ∈ Edge x y), (N : ℝ)⁻¹)
      ≤ 2 * sEdge x := hnum
    _ = 2 * Real.log x ^ (0.8:ℝ) := rfl
    _ = 2 / cD * Real.log x ^ (-(1/5):ℝ) * (cD * Real.log x) := hErpow.symm
    _ ≤ 2 / cD * Real.log x ^ (-(1/5):ℝ) * windowMass y (y ^ alpha) :=
        mul_le_mul_of_nonneg_left (hDlb x hxD y hy) (by positivity)

/-- ∃-form of `passtime_edge_mass_atCX` (X-chase: `x₀ := X_edgeMass`). -/
theorem passtime_edge_mass_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect (Set.indicator (Edge x y) 1)
          ≤ C_edgeMass * (Real.log x) ^ (-c_edgeMass) :=
  ⟨X_edgeMass, passtime_edge_mass_atCX⟩

/-- Sibling of `passtime_edge_mass` with the `c`-slot pinned to `c_edgeMass`; `C` and the
threshold stay existential. The original delegates here.  Now delegates to
`passtime_edge_mass_atC` (big-C campaign, step 2: `C := C_edgeMass`). -/
theorem passtime_edge_mass_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect (Set.indicator (Edge x y) 1)
          ≤ C * (Real.log x) ^ (-c_edgeMass) := by
  obtain ⟨x₀, h⟩ := passtime_edge_mass_atC
  exact ⟨C_edgeMass, x₀, C_edgeMass_pos, h⟩

/-- **Paper (5.16), window term.**  On the event that `N_y` *does* pass, the passage time nonetheless
lands outside `I_y` only with probability `≪ log^{-c} x`.  Reduction (proved here): the event
`{passes ∧ T_x ∉ I_y}` is contained (up to the even-support null set) in `{¬ good tuple} ∪ Edge`, so
its mass is bounded by the good-tuple union bound (5.12, `approx_good_tuple_whp`) plus the integral-test
edge mass (`passtime_edge_mass`); the containment on the good event is `passtime_edge_of_good` (the
(5.15) estimate).  **Does not use C7's escape bound** — that is the *other* term of (5.16), discharged
in `approx_passtime_window`. -/
theorem passtime_edge_mass :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect (Set.indicator (Edge x y) 1)
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := passtime_edge_mass_explicit
  exact ⟨c_edgeMass, C, x₀, c_edgeMass_pos, hC, h⟩

noncomputable def c_passtimeInner : ℝ := min c_goodTupleDev c_edgeMass

theorem c_passtimeInner_pos : 0 < c_passtimeInner :=
  lt_min c_goodTupleDev_pos c_edgeMass_pos

/-- The (5.16) inner-window constant: `C_goodTupleDev + C_edgeMass` (big-C campaign,
step 2). -/
noncomputable def C_passtimeInner : ℝ := C_goodTupleDev + C_edgeMass

theorem C_passtimeInner_pos : 0 < C_passtimeInner :=
  add_pos C_goodTupleDev_pos C_edgeMass_pos

/-- The `passtime_window_inner` cutoff (X-chase): witness copied verbatim from the `_atC`
proof at the explicit upstream names. -/
noncomputable def X_passtimeInner : ℝ :=
  max (max (max X_goodTupleWhp X_edgeMass) X_edgeOfGood) (Real.exp 1)

/-- Universal-cutoff form of `passtime_window_inner_atC` (X-chase). -/
theorem passtime_window_inner_atCX :
    ∀ x : ℝ, X_passtimeInner ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} 1)
          ≤ C_passtimeInner * (Real.log x) ^ (-c_passtimeInner) := by
  classical
  have hgoodwhp := approx_good_tuple_whp_atCX
  have hmass := passtime_edge_mass_atCX
  have hx3one := passtime_edge_of_good_atX.1
  have hincl := passtime_edge_of_good_atX.2
  set x1 : ℝ := X_goodTupleWhp with hx1def
  set x2 : ℝ := X_edgeMass with hx2def
  set x3 : ℝ := X_edgeOfGood with hx3def
  set C1 : ℝ := C_goodTupleDev with hC1def
  set C2 : ℝ := C_edgeMass with hC2def
  have hC1 : 0 < C1 := C_goodTupleDev_pos
  have hC2 : 0 < C2 := C_edgeMass_pos
  set c1 : ℝ := c_goodTupleDev with hc1def
  set c2 : ℝ := c_edgeMass with hc2def
  have hc1 : 0 < c1 := c_goodTupleDev_pos
  have hc2 : 0 < c2 := c_edgeMass_pos
  rw [show c_passtimeInner = min c1 c2 from rfl,
    show C_passtimeInner = C1 + C2 from rfl,
    show X_passtimeInner = max (max (max x1 x2) x3) (Real.exp 1) from rfl]
  intro x hx y hy
  have hx1 : x1 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx2 : x2 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hxe
  -- `1 ≤ y^α` (log-uniform support needs the upper endpoint `≥ 1`)
  have hx1le : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hxe
  have hyα1 : (1 : ℝ) ≤ y ^ alpha := by
    have hy1 : (1 : ℝ) ≤ y := by
      rcases hy with h | h <;> rw [h] <;>
        · rw [show (1 : ℝ) = (1 : ℝ) ^ (_ : ℝ) from (Real.one_rpow _).symm]
          exact Real.rpow_le_rpow (by norm_num) hx1le (by unfold alpha; positivity)
    rw [show (1 : ℝ) = (1 : ℝ) ^ alpha from (Real.one_rpow _).symm]
    exact Real.rpow_le_rpow (by norm_num) hy1 (by unfold alpha; positivity)
  set P := logUnifOdd y (y ^ alpha) with hPdef
  -- the even set carries no `logUnifOdd`-mass
  have heven0 : P.expect (Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1) = 0 := by
    have hzero : ∀ a, (P a).toReal * Set.indicator {N : ℕ | ¬ (N % 2 = 1)} (1 : ℕ → ℝ) a = 0 := by
      intro a
      by_cases ha : P a = 0
      · rw [ha]; simp
      · have hmem : a ∈ P.support := ha
        have hodd : a % 2 = 1 := (logUnifOdd_support_le hyα1 hmem).1
        rw [Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq, not_not]; exact hodd)]; ring
    show ∑' a, (P a).toReal * Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1 a = 0
    simp_rw [hzero]; exact tsum_zero
  -- the "bad" set: not a good tuple, or in the edge window
  set Sgood : Set ℕ := {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} with hSgood
  set T : Set ℕ := {N | N ∈ Sgood ∨ N ∈ Edge x y} with hT
  -- pointwise: the target event is dominated by `¬odd ∪ T`
  have hpwUT : ∀ N, Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} (1 : ℕ → ℝ) N
      ≤ Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1 N + Set.indicator T 1 N := by
    intro N
    have h0odd : (0 : ℝ) ≤ Set.indicator {N : ℕ | ¬ (N % 2 = 1)} (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    have h0T : (0 : ℝ) ≤ Set.indicator T (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    by_cases hU : N ∈ {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y}
    · rw [Set.indicator_of_mem hU, Pi.one_apply]
      by_cases hodd : N % 2 = 1
      · have hNT : N ∈ T := by
          by_cases hg : goodTuple x (nZero x) (valVec N (nZero x))
          · exact Or.inr (hincl x hx3 y hy N hodd hg hU.1 hU.2)
          · exact Or.inl hg
        rw [Set.indicator_of_mem hNT, Pi.one_apply]; linarith
      · rw [Set.indicator_of_mem (show N ∈ {N : ℕ | ¬ (N % 2 = 1)} from hodd), Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hU]; linarith
  -- pointwise: `T` is dominated by `¬good ∪ Edge`
  have hpwT : ∀ N, Set.indicator T (1 : ℕ → ℝ) N
      ≤ Set.indicator Sgood 1 N + Set.indicator (Edge x y) 1 N := by
    intro N
    have h0g : (0 : ℝ) ≤ Set.indicator Sgood (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    have h0e : (0 : ℝ) ≤ Set.indicator (Edge x y) (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    by_cases hNT : N ∈ T
    · rw [Set.indicator_of_mem hNT, Pi.one_apply]
      rcases hNT with hg | he
      · rw [Set.indicator_of_mem hg, Pi.one_apply]; linarith
      · rw [Set.indicator_of_mem he, Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hNT]; linarith
  -- exponent-monotonicity closers
  have hmono1 : C1 * (Real.log x) ^ (-c1) ≤ C1 * (Real.log x) ^ (-(min c1 c2)) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog1 (by simp [neg_le_neg_iff])) hC1.le
  have hmono2 : C2 * (Real.log x) ^ (-c2) ≤ C2 * (Real.log x) ^ (-(min c1 c2)) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog1 (by simp [neg_le_neg_iff])) hC2.le
  calc P.expect (Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} 1)
      ≤ P.expect (Set.indicator {N : ℕ | ¬ (N % 2 = 1)} 1) + P.expect (Set.indicator T 1) :=
        expect_le_add_of_indicator_le _ _ _ _ hpwUT
    _ = P.expect (Set.indicator T 1) := by rw [heven0]; ring
    _ ≤ P.expect (Set.indicator Sgood 1) + P.expect (Set.indicator (Edge x y) 1) :=
        expect_le_add_of_indicator_le _ _ _ _ hpwT
    _ ≤ C1 * (Real.log x) ^ (-c1) + C2 * (Real.log x) ^ (-c2) := by
        have hg := hgoodwhp x hx1 y hy
        have hm := hmass x hx2 y hy
        rw [← hPdef] at hg hm
        exact add_le_add hg hm
    _ ≤ C1 * (Real.log x) ^ (-(min c1 c2)) + C2 * (Real.log x) ^ (-(min c1 c2)) :=
        add_le_add hmono1 hmono2
    _ = (C1 + C2) * (Real.log x) ^ (-(min c1 c2)) := by ring

/-- ∃-form of `passtime_window_inner_atCX` (X-chase: `x₀ := X_passtimeInner`). -/
theorem passtime_window_inner_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} 1)
          ≤ C_passtimeInner * (Real.log x) ^ (-c_passtimeInner) :=
  ⟨X_passtimeInner, passtime_window_inner_atCX⟩

/-- Sibling of `passtime_window_inner` with the `c`-slot pinned to `c_passtimeInner`; `C` and
the threshold stay existential. The original delegates here.  Now delegates to
`passtime_window_inner_atC` (big-C campaign, step 2: `C := C_passtimeInner`). -/
theorem passtime_window_inner_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} 1)
          ≤ C * (Real.log x) ^ (-c_passtimeInner) := by
  obtain ⟨x₀, h⟩ := passtime_window_inner_atC
  exact ⟨C_passtimeInner, x₀, C_passtimeInner_pos, h⟩

theorem passtime_window_inner :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} 1)
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := passtime_window_inner_explicit
  exact ⟨c_passtimeInner, C, x₀, c_passtimeInner_pos, hC, h⟩

noncomputable def c_passtimeWindow : ℝ := min c_valSumTail c_passtimeInner

theorem c_passtimeWindow_pos : 0 < c_passtimeWindow :=
  lt_min c_valSumTail_pos c_passtimeInner_pos

/-- **Paper (5.16)** — the passage time lands in the window `I_y` with probability `1 − O(log^{-c} x)`.
Equivalently the complement `{N : ¬(passes ∧ T_x ∈ I_y)}` has probability `≪ log^{-c} x`.

⚠️ **THIS is the C7 consumer.**  The complement event splits as the disjoint union
`{¬ passes} ∪ {passes ∧ T_x ∉ I_y}`.  The first term `ℙ(T_x(N_y) = ∞) = ℙ(¬ passes) ≪ x^{-c}` is
`first_passage_nonescape` (C7, paper (1.19)/(5.5), **proved axiom-clean**), folded into `log^{-c} x`
via `escape_to_log`.  The second term is `passtime_window_inner` (the integral-test window piece).
This lemma **wires C7 into C8** — the whole of C8's dependence on C7 — leaving only the window
integral test open.

The `C`-slot: `C_valSumGeom + C_passtimeInner` — the reified C7 constant plus the inner
window constant (big-C campaign, step 2). -/
noncomputable def C_passtimeWindow : ℝ := C_valSumGeom + C_passtimeInner

theorem C_passtimeWindow_pos : 0 < C_passtimeWindow :=
  add_pos C_valSumGeom_pos C_passtimeInner_pos

/-- Sibling of `approx_passtime_window` with the `c`/`C` slots pinned at
(`c_passtimeWindow`, `C_passtimeWindow`) — the `_atC` form (big-C campaign, step 2),
cutoff existential. -/
theorem approx_passtime_window_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1)
          ≤ C_passtimeWindow * (Real.log x) ^ (-c_passtimeWindow) := by
  obtain ⟨x₁, hesc⟩ := first_passage_nonescape_atC
  obtain ⟨x₂, hwin⟩ := passtime_window_inner_atC
  set C₁ : ℝ := C_valSumGeom with hC1def
  set C₂ : ℝ := C_passtimeInner with hC2def
  have hC₁ : 0 < C₁ := C_valSumGeom_pos
  have hC₂ : 0 < C₂ := C_passtimeInner_pos
  set c₁ : ℝ := c_valSumTail with hc1def
  set c₂ : ℝ := c_passtimeInner with hc2def
  have hc₁ : 0 < c₁ := c_valSumTail_pos
  have hc₂ : 0 < c₂ := c_passtimeInner_pos
  rw [show c_passtimeWindow = min c₁ c₂ from rfl,
    show C_passtimeWindow = C₁ + C₂ from rfl]
  refine ⟨max (max x₁ x₂) (Real.exp 1),
    fun x hx y hy => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hpw : ∀ N, Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} (1 : ℕ → ℝ) N ≤
      Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1 N +
      Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} 1 N := by
    intro N
    have h1 : (0 : ℝ) ≤ Set.indicator {N | ¬ passes ⌊x⌋₊ N} (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    have h2 : (0 : ℝ) ≤ Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    by_cases hN : N ∈ {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)}
    · rw [Set.indicator_of_mem hN, Pi.one_apply]
      rcases Classical.em (passes ⌊x⌋₊ N) with hp | hp
      · have hq : passTime ⌊x⌋₊ N ∉ Iy x y := fun hq => hN ⟨hp, hq⟩
        have hmemT : N ∈ {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} := ⟨hp, hq⟩
        rw [Set.indicator_of_mem hmemT, Pi.one_apply]; linarith
      · have hmemS : N ∈ {N | ¬ passes ⌊x⌋₊ N} := hp
        rw [Set.indicator_of_mem hmemS, Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hN]; linarith
  have hA : x ^ (-c₁) ≤ (Real.log x) ^ (-(min c₁ c₂)) :=
    le_trans (escape_to_log hxe hc₁)
      (Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_left c₁ c₂)))
  have hB : (Real.log x) ^ (-c₂) ≤ (Real.log x) ^ (-(min c₁ c₂)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_right c₁ c₂))
  calc (logUnifOdd y (y ^ alpha)).expect
          (Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1)
      ≤ (logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | ¬ passes ⌊x⌋₊ N} 1)
          + (logUnifOdd y (y ^ alpha)).expect
              (Set.indicator {N | passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∉ Iy x y} 1) :=
        expect_le_add_of_indicator_le _ _ _ _ hpw
    _ ≤ C₁ * x ^ (-c₁) + C₂ * (Real.log x) ^ (-c₂) :=
        add_le_add (hesc x hx1 y hy) (hwin x hx2 y hy)
    _ ≤ C₁ * (Real.log x) ^ (-(min c₁ c₂)) + C₂ * (Real.log x) ^ (-(min c₁ c₂)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hC₁.le) (mul_le_mul_of_nonneg_left hB hC₂.le)
    _ = (C₁ + C₂) * (Real.log x) ^ (-(min c₁ c₂)) := by ring

/-- Sibling of `approx_passtime_window` with the `c`-slot pinned to `c_passtimeWindow`;
the original delegates here.  Now delegates to `approx_passtime_window_atC` (big-C
campaign, step 2: `C := C_passtimeWindow`). -/
theorem approx_passtime_window_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1)
          ≤ C * (Real.log x) ^ (-c_passtimeWindow) := by
  obtain ⟨x₀, h⟩ := approx_passtime_window_atC
  exact ⟨C_passtimeWindow, x₀, C_passtimeWindow_pos, h⟩

/-! ## C8 assembly: the `first_passage_approx` (5.8) chain, decomposed

The assembly runs `ℙ(Pass_x(N_y) ∈ E)  →  firstPassMid  →  approxMainTerm`.  `firstPassMid` is the
probability restricted to the good-tuple × window event and partitioned by the passage time
`T_x(N_y) = n` over `n ∈ I_y` (paper (5.9)); it is the natural bridge between the raw passage
probability and the affine main term.  Two owed sub-lemmas carry the two legs:

* `first_passage_window_reduce` — the (5.12)+(5.16) whp reduction: replacing `{Pass ∈ E}` by its
  restriction to `good ∧ (passes ∧ T_x ∈ I_y)` and partitioning by `T_x = n` costs `O(log^{-c}x)`.
  Consumes the two PROVED whp lemmas `approx_good_tuple_whp` and `approx_passtime_window`.
* `first_passage_affine_reindex` — the (5.17) `B_{n,y}` event chain + (5.18) Lemma 2.1 affine
  reindexing (APPROXIMATE — truncation absorbed, see the module docstring).  This is the
  route-decisive leg against the pinned `approxMainTerm`.

`first_passage_approx` itself is then a triangle inequality over these two, mirroring the
`approx_passtime_window` combine. -/

open Classical in
/-- The bridge term for (5.8): the passage-location probability restricted to the good-tuple event
and partitioned by the passage time `T_x(N_y) = n` over the window `I_y` (5.9). -/
noncomputable def firstPassMid (x : ℝ) (E : Set ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Iy x y,
    (logUnifOdd y (y ^ alpha)).expect
      (Set.indicator {N | passTime ⌊x⌋₊ N = n ∧ passLoc ⌊x⌋₊ N ∈ E ∧
        goodTuple x (nZero x) (valVec N (nZero x))} 1)

theorem approx_passtime_window :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
        (logUnifOdd y (y ^ alpha)).expect
            (Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1)
          ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := approx_passtime_window_explicit
  exact ⟨c_passtimeWindow, C, x₀, c_passtimeWindow_pos, hC, h⟩

noncomputable def c_windowReduce : ℝ := min c_goodTupleDev c_passtimeWindow

theorem c_windowReduce_pos : 0 < c_windowReduce :=
  lt_min c_goodTupleDev_pos c_passtimeWindow_pos

/-- **(5.12)+(5.16) whp reduction** (owed) — the first leg of (5.8).  Passing from the raw
`ℙ(Pass_x(N_y) ∈ E)` to the restricted, `T_x`-partitioned `firstPassMid` costs `O(log^{-c} x)`:
the discarded mass lies in `{¬ good} ∪ {¬ (passes ∧ T_x ∈ I_y)}`, each `≪ log^{-c} x` by the two
PROVED whp lemmas `approx_good_tuple_whp` (5.12) and `approx_passtime_window` (5.16).  (On the
complementary good∩window event, `{Pass ∈ E}` is the disjoint union over `n ∈ I_y` of
`{T_x = n ∧ Pass ∈ E ∧ good}`, so the partition is exact there.)

The `C`-slot: `C_goodTupleDev + C_passtimeWindow` (big-C campaign, step 2). -/
noncomputable def C_windowReduce : ℝ := C_goodTupleDev + C_passtimeWindow

theorem C_windowReduce_pos : 0 < C_windowReduce :=
  add_pos C_goodTupleDev_pos C_passtimeWindow_pos

/-- Sibling of `first_passage_window_reduce` with the `c`/`C` slots pinned at
(`c_windowReduce`, `C_windowReduce`) — the `_atC` form (big-C campaign, step 2),
cutoff existential. -/
theorem first_passage_window_reduce_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
              - firstPassMid x E y|
            ≤ C_windowReduce * (Real.log x) ^ (-c_windowReduce) := by
  obtain ⟨xg, hgood⟩ := approx_good_tuple_whp_atC
  obtain ⟨xw, hwin⟩ := approx_passtime_window_atC
  set Cg : ℝ := C_goodTupleDev with hCgdef
  set Cw : ℝ := C_passtimeWindow with hCwdef
  have hCg : 0 < Cg := C_goodTupleDev_pos
  have hCw : 0 < Cw := C_passtimeWindow_pos
  set cg : ℝ := c_goodTupleDev with hcgdef
  set cw : ℝ := c_passtimeWindow with hcwdef
  have hcg : 0 < cg := c_goodTupleDev_pos
  have hcw : 0 < cw := c_passtimeWindow_pos
  rw [show c_windowReduce = min cg cw from rfl,
    show C_windowReduce = Cg + Cw from rfl]
  refine ⟨max (max xg xw) (Real.exp 1),
    fun x hx E hE y hy => ?_⟩
  have hxg : xg ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxw : xw ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  classical
  set P := logUnifOdd y (y ^ alpha) with hP
  -- the big restricted event
  set Sbig : Set ℕ := {N | passTime ⌊x⌋₊ N ∈ Iy x y ∧ passLoc ⌊x⌋₊ N ∈ E ∧
    goodTuple x (nZero x) (valVec N (nZero x))} with hSbig
  have hsum : ∀ (V : Set ℕ), Summable fun a => (P a).toReal * Set.indicator V 1 a := by
    intro V
    have hsumP : Summable fun a => (P a).toReal := ENNReal.summable_toReal P.tsum_coe_ne_top
    refine Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) a))
      (fun a => ?_) hsumP
    rw [Set.indicator_apply]; split
    · simp
    · simp
  -- Step 1: firstPassMid = P.expect (ind Sbig)
  have hcollapse : ∀ a, Set.indicator Sbig (1 : ℕ → ℝ) a
      = ∑ n ∈ Iy x y, Set.indicator {N | passTime ⌊x⌋₊ N = n ∧ passLoc ⌊x⌋₊ N ∈ E ∧
          goodTuple x (nZero x) (valVec N (nZero x))} 1 a := by
    intro a
    by_cases hP2 : passLoc ⌊x⌋₊ a ∈ E ∧ goodTuple x (nZero x) (valVec a (nZero x))
    · by_cases hT : passTime ⌊x⌋₊ a ∈ Iy x y
      · rw [Set.indicator_of_mem (show a ∈ Sbig from ⟨hT, hP2.1, hP2.2⟩), Pi.one_apply]
        rw [Finset.sum_eq_single (passTime ⌊x⌋₊ a)]
        · rw [Set.indicator_of_mem (show a ∈ {N | passTime ⌊x⌋₊ N = passTime ⌊x⌋₊ a ∧
            passLoc ⌊x⌋₊ N ∈ E ∧ goodTuple x (nZero x) (valVec N (nZero x))} from
            ⟨rfl, hP2.1, hP2.2⟩), Pi.one_apply]
        · intro n _ hne
          rw [Set.indicator_of_notMem]
          simp only [Set.mem_setOf_eq]; rintro ⟨he, _, _⟩; exact hne he.symm
        · intro hna; exact absurd hT hna
      · rw [Set.indicator_of_notMem (show a ∉ Sbig from fun h => hT h.1)]
        symm
        apply Finset.sum_eq_zero
        intro n hn
        rw [Set.indicator_of_notMem]
        simp only [Set.mem_setOf_eq]; rintro ⟨he, _, _⟩; exact hT (he ▸ hn)
    · rw [Set.indicator_of_notMem (show a ∉ Sbig from fun h => hP2 ⟨h.2.1, h.2.2⟩)]
      symm
      apply Finset.sum_eq_zero
      intro n _
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_setOf_eq]; rintro ⟨_, h2, h3⟩; exact hP2 ⟨h2, h3⟩
  have hmid : firstPassMid x E y = P.expect (Set.indicator Sbig 1) := by
    unfold firstPassMid PMF.expect
    rw [← hP]
    rw [← Summable.tsum_finsetSum (fun n _ => hsum _)]
    apply tsum_congr; intro a
    rw [hcollapse a, Finset.mul_sum]
  -- Step 2: pointwise domination indA ≤ ind Sbig + ind U23, ind U23 ≤ ind¬G + ind¬window
  set U23 : Set ℕ := {N | ¬ goodTuple x (nZero x) (valVec N (nZero x)) ∨
    ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} with hU23
  have hpw1 : ∀ N, Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} (1 : ℕ → ℝ) N ≤
      Set.indicator Sbig 1 N + Set.indicator U23 1 N := by
    intro N
    have h1 : (0 : ℝ) ≤ Set.indicator Sbig (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    have h2 : (0 : ℝ) ≤ Set.indicator U23 (1 : ℕ → ℝ) N :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) N
    by_cases hN : N ∈ {N | passLoc ⌊x⌋₊ N ∈ E}
    · rw [Set.indicator_of_mem hN, Pi.one_apply]
      by_cases hG : goodTuple x (nZero x) (valVec N (nZero x))
      · by_cases hT : passTime ⌊x⌋₊ N ∈ Iy x y
        · rw [Set.indicator_of_mem (show N ∈ Sbig from ⟨hT, hN, hG⟩), Pi.one_apply]; linarith
        · rw [Set.indicator_of_mem (show N ∈ U23 from Or.inr (fun h => hT h.2)), Pi.one_apply]
          linarith
      · rw [Set.indicator_of_mem (show N ∈ U23 from Or.inl hG), Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hN]; linarith
  have hpw2 : ∀ N, Set.indicator U23 (1 : ℕ → ℝ) N ≤
      Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1 N +
      Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1 N := by
    intro N
    have h1 : (0 : ℝ) ≤ Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))}
      (1 : ℕ → ℝ) N := Set.indicator_nonneg (fun _ _ => zero_le_one) N
    have h2 : (0 : ℝ) ≤ Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)}
      (1 : ℕ → ℝ) N := Set.indicator_nonneg (fun _ _ => zero_le_one) N
    by_cases hN : N ∈ U23
    · rw [Set.indicator_of_mem hN, Pi.one_apply]
      rcases hN with hg | hw
      · rw [Set.indicator_of_mem (show N ∈ {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))}
          from hg), Pi.one_apply]; linarith
      · rw [Set.indicator_of_mem (show N ∈ {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)}
          from hw), Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hN]; linarith
  -- combine
  have hAbound : P.expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
      ≤ P.expect (Set.indicator Sbig 1) + (P.expect (Set.indicator
          {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
        + P.expect (Set.indicator {N | ¬ (passes ⌊x⌋₊ N ∧ passTime ⌊x⌋₊ N ∈ Iy x y)} 1)) := by
    refine le_trans (expect_le_add_of_indicator_le P _ Sbig U23 hpw1) ?_
    gcongr
    exact expect_le_add_of_indicator_le P U23 _ _ hpw2
  -- firstPassMid ≤ P.expect (indA)  (ind Sbig ≤ indA pointwise)
  have hsub : Sbig ⊆ {N | passLoc ⌊x⌋₊ N ∈ E} := fun a ha => ha.2.1
  have hmidle : firstPassMid x E y ≤ P.expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1) := by
    rw [hmid]
    unfold PMF.expect
    refine (hsum Sbig).tsum_le_tsum
      (fun a => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg) (hsum _)
    exact Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le_one) a
  have hA : (Real.log x) ^ (-cg) ≤ (Real.log x) ^ (-(min cg cw)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_left cg cw))
  have hB : (Real.log x) ^ (-cw) ≤ (Real.log x) ^ (-(min cg cw)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_right cg cw))
  rw [abs_of_nonneg (by linarith [hmidle])]
  have hthis := hAbound
  rw [← hmid] at hthis
  calc P.expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1) - firstPassMid x E y
      ≤ Cg * (Real.log x) ^ (-cg) + Cw * (Real.log x) ^ (-cw) := by
        linarith [hgood x hxg y hy, hwin x hxw y hy, hthis]
    _ ≤ Cg * (Real.log x) ^ (-(min cg cw)) + Cw * (Real.log x) ^ (-(min cg cw)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hCg.le) (mul_le_mul_of_nonneg_left hB hCw.le)
    _ = (Cg + Cw) * (Real.log x) ^ (-(min cg cw)) := by ring

/-- Sibling of `first_passage_window_reduce` with the `c`-slot pinned to `c_windowReduce`;
the original delegates here.  Now delegates to `first_passage_window_reduce_atC` (big-C
campaign, step 2: `C := C_windowReduce`). -/
theorem first_passage_window_reduce_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
              - firstPassMid x E y|
            ≤ C * (Real.log x) ^ (-c_windowReduce) := by
  obtain ⟨x₀, h⟩ := first_passage_window_reduce_atC
  exact ⟨C_windowReduce, x₀, C_windowReduce_pos, h⟩

theorem first_passage_window_reduce :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
              - firstPassMid x E y|
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := first_passage_window_reduce_explicit
  exact ⟨c_windowReduce, C, x₀, c_windowReduce_pos, hC, h⟩

/-- **(5.17) step-back event inclusion — the EXACT forward direction.**  For any window index
`n ≥ m`, the first-passage event `{T_x N = n ∧ Pass_x N ∈ E}` is contained in the stepped-back
event `{T_x(Syr^{n-m}N) = m ∧ Pass_x(Syr^{n-m}N) ∈ E}`.  This is the pure event-algebra core of the
`B_{n,y}` chain: since `T_x N = n` already forces the orbit to stay `> x` for every step `< n`
(hence `< n-m`), stepping back `n-m` steps lands exactly at first-passage time `m` with the *same*
passage location.  Proved from `passTime_stepback`; no orbit *size* estimate is used here (that
enters only the reverse inclusion and the `E'` size window). -/
theorem firstPass_event_stepback_subset (x' : ℕ) (E : Set ℕ) (n m : ℕ) (hmn : m ≤ n) :
    {N | passes x' N ∧ passTime x' N = n ∧ passLoc x' N ∈ E}
      ⊆ {N | passTime x' (syr^[n - m] N) = m ∧ passLoc x' (syr^[n - m] N) ∈ E} := by
  intro N hN
  obtain ⟨hpass, hT, hL⟩ := hN
  have hk : n - m ≤ passTime x' N := by rw [hT]; omega
  obtain ⟨_, hTM, hLM⟩ := passTime_stepback x' N (n - m) hpass hk
  refine ⟨?_, ?_⟩
  · rw [hTM, hT]; omega
  · rw [hLM]; exact hL

open Classical in
/-- **The diagonal (`ā = valVec`) bridge for the (5.18) reindex.**  For each `n ∈ I_y`, the
`P`-probability of the stepped-back event `{good⁽ⁿ⁻ᵐ⁰⁾(valVec N (n−m₀)) ∧ Syr^{n−m₀}N ∈ E'}`.  This
is precisely the *main* (`ā = valVec N (n−m₀)`) contribution to `approxMainTerm`: by
`aff_valVec_eq_syr`, `Aff N (n−m₀) (valVec N (n−m₀)) = Syr^{n−m₀}N`, and by `valVec_unique` that ā is
the unique good vector making the affine value land oddly at `M = Syr^{n−m₀}N`.  `steppedMid` sits
between `firstPassMid` (the (5.17) event side) and `approxMainTerm` (the fixed-ā `tsum` side); it
splits the route-decisive leg into an *event* reduction and a *reindex* error. -/
noncomputable def steppedMid (x : ℝ) (E : Set ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Iy x y,
    (logUnifOdd y (y ^ alpha)).expect
      (Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧
        Eprime x E (syr^[n - mZero x] N)} 1)

/-- **Pushforward reorder (ℝ≥0∞, unconditional).**  Masking a pushforward mass by a predicate `q`
on the target and summing equals summing the source mass over `{N : q (φ N)}`.  This is the
reindex engine for the (5.18) step: `∑_M [q M] (P.map φ) M = ∑_N [q (φ N)] P N`.  No summability
side-conditions (ℝ≥0∞ Fubini via `PMF.tsum_map_mul`). -/
theorem map_mask_tsum (P : PMF ℕ) (φ : ℕ → ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (∑' M, if q M then (P.map φ) M else 0) = ∑' N, if q (φ N) then P N else 0 := by
  have h := PMF.tsum_map_mul P φ (fun M => if q M then (1 : ℝ≥0∞) else 0)
  simpa only [mul_ite, mul_one, mul_zero] using h

/-- **Pushforward reorder, real form.**  The `.toReal`-per-term masked pushforward sum (the shape
of `approxMainTerm`'s inner `∑_M` for a fixed good `ā`) equals the source-side masked mass, as a
real number.  Combines `map_mask_tsum` with `ENNReal.tsum_toReal_eq` (each masked mass `≤ 1 ≠ ⊤`). -/
theorem map_mask_tsum_toReal (P : PMF ℕ) (φ : ℕ → ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (∑' M, if q M then ((P.map φ) M).toReal else 0)
      = (∑' N, if q (φ N) then P N else 0).toReal := by
  rw [← map_mask_tsum P φ q]
  rw [ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun M => ?_
    split <;> simp
  · intro M
    split
    · exact PMF.apply_ne_top _ _
    · simp

open Classical in
/-- **Indicator expectation as a source mass.**  `P.expect (𝟙_S) = (∑_{N∈S} P N).toReal`.  Puts both
`steppedMid` (an indicator expectation) and `approxMainTerm` on the same `(∑' N …).toReal` footing for
the (5.18) exact reindex. -/
theorem expect_indicator_toReal (P : PMF ℕ) (S : Set ℕ) :
    P.expect (Set.indicator S 1) = (∑' N, if N ∈ S then P N else 0).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun N => by split; exacts [PMF.apply_ne_top _ _, by simp])]
  unfold PMF.expect
  refine tsum_congr fun N => ?_
  by_cases h : N ∈ S <;> simp [h]

open Classical in
/-- **The (5.18)/(5.19) EXACT reindex — `approxMainTerm = steppedMid`** (RATIFY-C8-v2 content).
With the divisibility-guarded `approxMainTerm` (paper's exact `Aff_ā`), Lemma 2.1 (`valVec_unique`)
collapses the reindex to the diagonal: for odd `N`, good `ā`, and `M` odd (from `Eprime`), the exact
affine relation `3^{n−m₀}N + Fnat = M·2^{|ā|}` holds **iff** `ā = valVec N (n−m₀)` (and then
`M = Syr^{n−m₀}N` by `aff_valVec_eq_syr`).  So each `N` contributes to exactly one `(ā,M)` term, and
the `(ā,M)`-sum reindexes to `steppedMid`'s single diagonal indicator — with **no** truncation error.
This is the honest replacement for the (deleted-in-spirit) FALSE `truncation_error_bound`; the sole
remaining reindex content is this exact bijection.  KEY INPUT: `valVec_unique` (`Basic/Valuation.lean`).
TODO(prove): reorder `∑'_ā ∑'_M ∑'_N` to `∑'_N`, apply `valVec_unique` (guard + `Eprime` oddness ⇒
`ā = valVec`) + `aff_valVec_eq_syr` to fix `M = Syr^{n−m₀}N`, matching `steppedMid`'s indicator mass
(`expect_indicator_toReal`); even `N` carry zero `logUnifOdd`-mass (`logUnifOdd_support_le`, needs `hy1`). -/
theorem approxMainTerm_eq_steppedMid (x : ℝ) (E : Set ℕ) (y : ℝ)
    (hy1 : (1 : ℝ) ≤ y ^ alpha) :
    approxMainTerm x E y = steppedMid x E y := by
  classical
  unfold approxMainTerm steppedMid
  refine Finset.sum_congr rfl fun n _ => ?_
  set k := n - mZero x with hk
  set P := logUnifOdd y (y ^ alpha) with hP
  set S : Set ℕ := {N | goodTuple x k (valVec N k) ∧ Eprime x E (syr^[k] N)} with hS
  -- `P N = 0` for even `N` (log-uniform-odd support).
  have hPodd : ∀ N : ℕ, N % 2 ≠ 1 → P N = 0 := by
    intro N hN
    by_contra hne
    exact hN (logUnifOdd_support_le hy1 (hne : N ∈ P.support)).1
  -- any `P`-dominated nonneg sum is `≤ 1` (instance-agnostic in the summand shape).
  have hmass_le : ∀ g : ℕ → ℝ≥0∞, (∀ N, g N ≤ P N) → (∑' N, g N) ≤ 1 :=
    fun g hg => le_trans (ENNReal.tsum_le_tsum hg) (le_of_eq P.tsum_coe)
  -- The (5.18)/(5.19) forcing: any good `ā`, odd `M`, with the exact affine relation IS the diagonal.
  have hforce : ∀ (N : ℕ), N % 2 = 1 → ∀ (ā : Fin k → ℕ) (M : ℕ),
      goodTuple x k ā → Eprime x E M →
      3 ^ k * N + fnat k ā = M * 2 ^ pre ā k → ā = valVec N k ∧ M = syr^[k] N := by
    intro N hodd ā M hg hE' haff
    have h2pos : 0 < 2 ^ pre ā k := by positivity
    have hdvd : 2 ^ pre ā k ∣ 3 ^ k * N + fnat k ā := ⟨M, by rw [haff, Nat.mul_comm]⟩
    have hAffM : Aff N k ā = M := by
      unfold Aff; rw [haff, Nat.mul_div_cancel _ h2pos]
    have hāeq : ā = valVec N k := (valVec_unique N k hodd ā hg.1).mp ⟨hdvd, by rw [hAffM]; exact hE'.1⟩
    refine ⟨hāeq, ?_⟩
    subst hāeq
    have hkey := syr_iterate_key N k hodd
    have hmm : M * 2 ^ pre (valVec N k) k = syr^[k] N * 2 ^ pre (valVec N k) k := by
      rw [← haff, ← hkey, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hmm
  -- Per-`N` collapse of the `(ā,M)` double sum to the diagonal indicator.
  have hperN : ∀ N : ℕ,
      (∑' (ā : Fin k → ℕ), ∑' (M : ℕ),
        (if goodTuple x k ā ∧ Eprime x E M
              ∧ 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k then P N else 0))
      = (if N ∈ S then P N else 0) := by
    intro N
    by_cases hodd : N % 2 = 1
    · by_cases hNS : N ∈ S
      · have hazero : ∀ ā : Fin k → ℕ, ā ≠ valVec N k →
            (∑' M : ℕ, if goodTuple x k ā ∧ Eprime x E M
                ∧ 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k then P N else 0) = 0 := by
          intro ā hā
          refine ENNReal.tsum_eq_zero.mpr fun M => if_neg ?_
          rintro ⟨hg, hE', haff⟩
          exact hā (hforce N hodd ā M hg hE' haff).1
        have hMzero : ∀ M : ℕ, M ≠ syr^[k] N →
            (if goodTuple x k (valVec N k) ∧ Eprime x E M
                ∧ 3 ^ k * N + fnat k (valVec N k) = M * 2 ^ pre (valVec N k) k then P N else 0) = 0 := by
          intro M hM
          refine if_neg ?_
          rintro ⟨hg, hE', haff⟩
          exact hM (hforce N hodd (valVec N k) M hg hE' haff).2
        have hcond : goodTuple x k (valVec N k) ∧ Eprime x E (syr^[k] N) ∧
            3 ^ k * N + fnat k (valVec N k) = syr^[k] N * 2 ^ pre (valVec N k) k :=
          ⟨hNS.1, hNS.2, by
            rw [Nat.mul_comm (syr^[k] N) (2 ^ pre (valVec N k) k)]
            exact (syr_iterate_key N k hodd).symm⟩
        rw [if_pos hNS, tsum_eq_single (valVec N k) hazero,
          tsum_eq_single (syr^[k] N) hMzero, if_pos hcond]
      · rw [if_neg hNS]
        refine ENNReal.tsum_eq_zero.mpr fun ā => ENNReal.tsum_eq_zero.mpr fun M => if_neg ?_
        rintro ⟨hg, hE', haff⟩
        obtain ⟨hāeq, hMeq⟩ := hforce N hodd ā M hg hE' haff
        subst hāeq; subst hMeq
        exact hNS ⟨hg, hE'⟩
    · rw [hPodd N hodd]; simp
  -- `if C then (∑' N …) else 0 = ∑' N, if C ∧ … else 0`, to expose the `N`-sum.
  have hEq : ∀ (ā : Fin k → ℕ) (M : ℕ),
      (if goodTuple x k ā ∧ Eprime x E M then
        (∑' N, if 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k then P N else 0) else 0)
      = ∑' N, (if goodTuple x k ā ∧ Eprime x E M
          ∧ 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k then P N else 0) := by
    intro ā M
    by_cases hC : goodTuple x k ā ∧ Eprime x E M
    · rw [if_pos hC]; exact tsum_congr fun N => by simp only [hC, true_and]
    · rw [if_neg hC]
      exact (ENNReal.tsum_eq_zero.mpr fun N => if_neg fun ⟨hg, hE', _⟩ => hC ⟨hg, hE'⟩).symm
  -- The ℝ≥0∞ core identity.
  have hcore : (∑' (ā : Fin k → ℕ), ∑' (M : ℕ),
        (if goodTuple x k ā ∧ Eprime x E M then
          (∑' N, if 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k then P N else 0) else 0))
      = ∑' N, (if N ∈ S then P N else 0) := by
    simp_rw [hEq]
    rw [show (∑' (ā : Fin k → ℕ), ∑' (M : ℕ), ∑' N,
          (if goodTuple x k ā ∧ Eprime x E M
              ∧ 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k then P N else 0))
        = ∑' (ā : Fin k → ℕ), ∑' N, ∑' (M : ℕ),
          (if goodTuple x k ā ∧ Eprime x E M
              ∧ 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k then P N else 0)
        from tsum_congr fun ā => ENNReal.tsum_comm]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun N => hperN N
  -- finiteness for the `.toReal` pulls
  have hFfin : ∀ (ā : Fin k → ℕ) (M : ℕ),
      (if goodTuple x k ā ∧ Eprime x E M then
        (∑' N, if 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k then P N else 0) else 0) ≠ ⊤ := by
    intro ā M; split
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top
        (hmass_le _ fun N => by split <;> first | exact le_rfl | exact zero_le)
    · simp
  have hGfin : ∀ ā : Fin k → ℕ,
      (∑' (M : ℕ), if goodTuple x k ā ∧ Eprime x E M then
        (∑' N, if 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k then P N else 0) else 0) ≠ ⊤ := by
    intro ā
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc (∑' (M : ℕ), if goodTuple x k ā ∧ Eprime x E M then
              (∑' N, if 3 ^ k * N + fnat k ā = M * 2 ^ pre ā k then P N else 0) else 0)
          ≤ ∑' (ā' : Fin k → ℕ), ∑' (M : ℕ), if goodTuple x k ā' ∧ Eprime x E M then
              (∑' N, if 3 ^ k * N + fnat k ā' = M * 2 ^ pre ā' k then P N else 0) else 0 :=
            ENNReal.le_tsum ā
      _ = ∑' N, (if N ∈ S then P N else 0) := hcore
      _ ≤ 1 := hmass_le _ fun N => by split <;> first | exact le_rfl | exact zero_le
  -- local `expect → sum` over the concrete `S` (so the `N ∈ S` decidability instance matches `hcore`).
  have hexp : P.expect (Set.indicator S 1) = (∑' N, if N ∈ S then P N else 0).toReal := by
    rw [ENNReal.tsum_toReal_eq (fun N => by split; exacts [PMF.apply_ne_top _ _, by simp])]
    unfold PMF.expect
    refine tsum_congr fun N => ?_
    by_cases h : N ∈ S <;> simp [h]
  -- assemble: rewrite the diagonal mass to the double sum, then pull `.toReal` termwise.
  rw [hexp, ← hcore, ENNReal.tsum_toReal_eq hGfin]
  refine tsum_congr fun ā => ?_
  rw [ENNReal.tsum_toReal_eq (hFfin ā)]
  refine tsum_congr fun M => ?_
  split <;> simp

open Classical in
/-- **`steppedMid ≤ approxMainTerm`** — immediate from the EXACT reindex
`approxMainTerm_eq_steppedMid` (they are equal under the RATIFY-C8-v2 guarded pin).  Retained as a
named lemma because `first_passage_truncation_reindex` consumes this `≤` direction. -/
theorem steppedMid_le_approxMainTerm (x : ℝ) (E : Set ℕ) (y : ℝ)
    (hy1 : (1 : ℝ) ≤ y ^ alpha) :
    steppedMid x E y ≤ approxMainTerm x E y :=
  le_of_eq (approxMainTerm_eq_steppedMid x E y hy1).symm

/-- **Good-tuple nesting** `𝒜⁽ⁿ²⁾ ⊂ 𝒜⁽ⁿ¹⁾` for `n₁ ≤ n₂` (paper's observation after (5.11)).  A
good valuation tuple of length `n₂` restricts to a good tuple of length `n₁ ≤ n₂`: entries and prefix
sums agree on the common prefix (`valVec`, `pre_valVec`), and the prefix constraint at each `k ≤ n₁`
is one of the constraints at `k ≤ n₂`.  This is exactly the `good⁽ⁿ⁰⁾ ⟹ good⁽ⁿ⁻ᵐ⁰⁾` drop used in the
(5.17) step-back forward inclusion. -/
theorem good_nested {x : ℝ} {N n₁ n₂ : ℕ} (hn : n₁ ≤ n₂)
    (hg : goodTuple x n₂ (valVec N n₂)) : goodTuple x n₁ (valVec N n₁) := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · exact hg.1 ⟨(i : ℕ), lt_of_lt_of_le i.isLt hn⟩
  · have hk2 : k ≤ n₂ := le_trans hk hn
    have h := hg.2 k hk2
    rw [pre_valVec hk2] at h
    rwa [pre_valVec hk]

/-- `I_y ⊂ [0, n₀]`: any summation index is `≤ n₀` (immediate from the `range (n₀+1)` filter). -/
theorem mem_Iy_le_nZero {x y : ℝ} {n : ℕ} (hn : n ∈ Iy x y) : n ≤ nZero x := by
  rw [Iy, Finset.mem_filter, Finset.mem_range] at hn; omega

/-- Real-interval bounds carried by any `n ∈ I_y`: `IyLo ≤ n ≤ IyHi` (the filter predicate). -/
theorem mem_Iy_bounds {x y : ℝ} {n : ℕ} (hn : n ∈ Iy x y) :
    IyLo x y ≤ (n : ℝ) ∧ (n : ℝ) ≤ IyHi x y := by
  rw [Iy, Finset.mem_filter] at hn; exact hn.2

/-- **Support-restricted monotonicity of `expect ∘ indicator`.**  If `S ⊆ T` *on the support* of `p`
(for every `a` with `p a ≠ 0`), then `p.expect (𝟙_S) ≤ p.expect (𝟙_T)`.  Weaker hypothesis than
`expect_mono_le` (which needs pointwise inclusion for ALL `a`): off-support points contribute `0`, so
inclusion there is irrelevant.  This is what lets the (5.17) forward inclusion `S_n ⊆ T_n` be verified
only for ODD `N` (the `logUnifOdd` support). -/
theorem expect_mono_on_support {α : Type*} (p : PMF α) (S T : Set α)
    (h : ∀ a ∈ p.support, a ∈ S → a ∈ T) :
    p.expect (Set.indicator S (1 : α → ℝ)) ≤ p.expect (Set.indicator T (1 : α → ℝ)) := by
  classical
  have hsum : ∀ V : Set α, Summable fun a => (p a).toReal * Set.indicator V (1 : α → ℝ) a := by
    intro V
    have hsumP : Summable fun a => (p a).toReal := ENNReal.summable_toReal p.tsum_coe_ne_top
    refine Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) a))
      (fun a => ?_) hsumP
    rw [Set.indicator_apply]; split
    · simp
    · simp
  unfold PMF.expect
  refine (hsum S).tsum_le_tsum (fun a => ?_) (hsum T)
  by_cases ha : p a = 0
  · simp [ha]
  · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    by_cases haS : a ∈ S
    · rw [Set.indicator_of_mem haS,
        Set.indicator_of_mem (h a ((PMF.mem_support_iff p a).mpr ha) haS)]
    · rw [Set.indicator_of_notMem haS]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) a

/-- **(5.17) interval brick** — every summation index `n ∈ I_y` satisfies `1 ≤ m₀ ≤ n`.  `m₀ ≈
(α−1)/100·log x ≈ 10⁻⁵·log x` while `IyLo ≈ log(y/x)/log(4/3) + log^{0.8}x ≥ (α−1)·log x/log(4/3) ≈
3·10⁻³·log x`, so `m₀ ≤ IyLo ≤ n` with room to spare; and `m₀ ≥ 1` once `log x ≥ 100/(α−1)`.  (Pure
interval arithmetic on the frozen `α`; reuses the `log(4/3) ∈ [1/4,1/3]` idiom.) -/
theorem mZero_le_of_mem_Iy :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
        1 ≤ mZero x ∧ mZero x ≤ n := by
  refine ⟨Real.exp 100000, Real.one_le_exp (by norm_num), fun x hx y hy n hn => ?_⟩
  have hxe : Real.exp 100000 ≤ x := hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (100000 : ℝ)]) hxe
  have hxpos : 0 < x := by linarith
  have hLbig : (100000 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 100000]; exact Real.log_le_log (Real.exp_pos _) hxe
  have hLnn : (0 : ℝ) ≤ Real.log x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  -- frozen α facts (concrete rationals — no decimal rpow poison)
  have ha1 : alpha - 1 = (1 : ℝ) / 1000 := by unfold alpha; norm_num
  have hagt : (1 : ℝ) < alpha := by unfold alpha; norm_num
  have hcoef : (alpha - 1) / 100 = (1 : ℝ) / 100000 := by rw [ha1]; norm_num
  -- log(4/3) ∈ (0, 1/3]
  have hg_hi : Real.log (4 / 3) ≤ (1 / 3 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4/3 by norm_num); linarith
  have hg_pos : 0 < Real.log (4 / 3) := by
    rw [show (4:ℝ)/3 = (3/4)⁻¹ by norm_num, Real.log_inv]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3/4 by norm_num); linarith
  -- 1 ≤ m₀
  have hmval : (1 : ℝ) ≤ (alpha - 1) / 100 * Real.log x := by rw [hcoef]; linarith
  have hm1 : 1 ≤ mZero x := by
    unfold mZero; exact Nat.le_floor (by exact_mod_cast hmval)
  -- (m₀ : ℝ) ≤ (α−1)/100 · log x
  have hmle : (mZero x : ℝ) ≤ (alpha - 1) / 100 * Real.log x := by
    unfold mZero
    exact Nat.floor_le (by rw [hcoef]; exact mul_nonneg (by norm_num) hLnn)
  -- log(y/x) ≥ (α−1) log x
  have hlogyx : (alpha - 1) * Real.log x ≤ Real.log (y / x) := by
    have hlogdiv : ∀ z : ℝ, Real.log (x ^ z / x) = (z - 1) * Real.log x := by
      intro z
      rw [Real.log_div (by positivity) (ne_of_gt hxpos), Real.log_rpow hxpos]; ring
    rcases hy with h | h
    · rw [h, hlogdiv alpha]
    · rw [h, hlogdiv (alpha ^ 2)]
      nlinarith [hLpos, mul_pos (show (0:ℝ) < alpha by linarith) (show (0:ℝ) < alpha - 1 by linarith)]
  -- assemble m₀ ≤ IyLo ≤ n
  have haLnn : (0 : ℝ) ≤ (alpha - 1) * Real.log x := mul_nonneg (by rw [ha1]; norm_num) hLnn
  have hIyLo_ge : (mZero x : ℝ) ≤ IyLo x y := by
    unfold IyLo
    have hlog08 : (0 : ℝ) ≤ Real.log x ^ (0.8 : ℝ) := Real.rpow_nonneg hLnn _
    have h3aL : (0 : ℝ) ≤ 3 * (alpha - 1) * Real.log x :=
      mul_nonneg (by rw [ha1]; norm_num) hLnn
    have hdiv : 3 * (alpha - 1) * Real.log x ≤ Real.log (y / x) / Real.log (4 / 3) := by
      rw [le_div_iff₀ hg_pos]
      nlinarith [hlogyx, mul_nonneg h3aL (sub_nonneg.mpr hg_hi)]
    have hbridge : (alpha - 1) / 100 * Real.log x ≤ 3 * (alpha - 1) * Real.log x := by
      nlinarith [haLnn]
    linarith [hmle, hbridge, hdiv, hlog08]
  have hnge : IyLo x y ≤ (n : ℝ) := (mem_Iy_bounds hn).1
  exact ⟨hm1, by exact_mod_cast le_trans hIyLo_ge hnge⟩

/-- The `two_mZero_le_of_mem_Iy` cutoff, symbolic (big-C campaign, step 2). -/
noncomputable def X_twoMZero : ℝ := Real.exp 100000

/-- **Fine/coarse scale separation** — every `n ∈ I_y` satisfies `2·m₀ ≤ n`, hence `m₀ ≤ n − m₀`.
This is exactly what lets `fine_scale_mixing` (Prop 1.14) be applied at the fine scale `n−m₀` with
coarse scale `m₀ ≤ n−m₀` in the (5.20) `Z`-reduction: since `m₀ ≈ (α−1)/100·log x ≈ 10⁻⁵·log x` while
`IyLo ≥ 3(α−1)·log x`, even `2m₀ ≤ IyLo ≤ n` with room to spare (`2·(α−1)/100 = (α−1)/50 ≤ 3(α−1)`).
(Same pure interval idiom as `mZero_le_of_mem_Iy`, strengthened to the factor `2`.)
`_at` sibling at `X_twoMZero` (big-C campaign, step 2). -/
theorem two_mZero_le_of_mem_Iy_at :
    ∀ x : ℝ, X_twoMZero ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
        2 * mZero x ≤ n := by
  unfold X_twoMZero
  intro x hx y hy n hn
  have hxe : Real.exp 100000 ≤ x := hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (100000 : ℝ)]) hxe
  have hxpos : 0 < x := by linarith
  have hLbig : (100000 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 100000]; exact Real.log_le_log (Real.exp_pos _) hxe
  have hLnn : (0 : ℝ) ≤ Real.log x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have ha1 : alpha - 1 = (1 : ℝ) / 1000 := by unfold alpha; norm_num
  have hcoef : (alpha - 1) / 100 = (1 : ℝ) / 100000 := by rw [ha1]; norm_num
  have hg_hi : Real.log (4 / 3) ≤ (1 / 3 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4/3 by norm_num); linarith
  have hg_pos : 0 < Real.log (4 / 3) := by
    rw [show (4:ℝ)/3 = (3/4)⁻¹ by norm_num, Real.log_inv]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3/4 by norm_num); linarith
  -- (m₀ : ℝ) ≤ (α−1)/100 · log x
  have hmle : (mZero x : ℝ) ≤ (alpha - 1) / 100 * Real.log x := by
    unfold mZero
    exact Nat.floor_le (by rw [hcoef]; exact mul_nonneg (by norm_num) hLnn)
  -- log(y/x) ≥ (α−1) log x
  have hlogyx : (alpha - 1) * Real.log x ≤ Real.log (y / x) := by
    have hlogdiv : ∀ z : ℝ, Real.log (x ^ z / x) = (z - 1) * Real.log x := by
      intro z
      rw [Real.log_div (by positivity) (ne_of_gt hxpos), Real.log_rpow hxpos]; ring
    rcases hy with h | h
    · rw [h, hlogdiv alpha]
    · rw [h, hlogdiv (alpha ^ 2)]
      nlinarith [hLpos, mul_pos (show (0:ℝ) < alpha by linarith) (show (0:ℝ) < alpha - 1 by linarith)]
  -- assemble 2·m₀ ≤ IyLo ≤ n
  have haLnn : (0 : ℝ) ≤ (alpha - 1) * Real.log x := mul_nonneg (by rw [ha1]; norm_num) hLnn
  have hIyLo_ge : (2 * mZero x : ℝ) ≤ IyLo x y := by
    unfold IyLo
    have hlog08 : (0 : ℝ) ≤ Real.log x ^ (0.8 : ℝ) := Real.rpow_nonneg hLnn _
    have h3aL : (0 : ℝ) ≤ 3 * (alpha - 1) * Real.log x :=
      mul_nonneg (by rw [ha1]; norm_num) hLnn
    have hdiv : 3 * (alpha - 1) * Real.log x ≤ Real.log (y / x) / Real.log (4 / 3) := by
      rw [le_div_iff₀ hg_pos]
      nlinarith [hlogyx, mul_nonneg h3aL (sub_nonneg.mpr hg_hi)]
    have hbridge : 2 * ((alpha - 1) / 100 * Real.log x) ≤ 3 * (alpha - 1) * Real.log x := by
      nlinarith [haLnn]
    linarith [hmle, hbridge, hdiv, hlog08]
  have hnge : IyLo x y ≤ (n : ℝ) := (mem_Iy_bounds hn).1
  exact_mod_cast le_trans hIyLo_ge hnge

open Classical in
/-- `two_mZero_le_of_mem_Iy`, original `∃`-form: delegates to the `_at` sibling at
`X_twoMZero` (big-C campaign, step 2). -/
theorem two_mZero_le_of_mem_Iy :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
        2 * mZero x ≤ n :=
  ⟨X_twoMZero, Real.one_le_exp (by norm_num), two_mZero_le_of_mem_Iy_at⟩

/-- Step-back pow split: `(3/4)^{n−m} = (4/3)^m · (3/4)^n` for `m ≤ n` (real, `(4/3)=(3/4)⁻¹`). -/
theorem pow_stepback_eq {m n : ℕ} (h : m ≤ n) :
    (3 / 4 : ℝ) ^ (n - m) = (4 / 3) ^ m * (3 / 4) ^ n := by
  have hsplit : (3 / 4 : ℝ) ^ n = (3 / 4) ^ m * (3 / 4) ^ (n - m) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, show (4 / 3 : ℝ) = (3 / 4)⁻¹ by norm_num, inv_pow]
  have : (3 / 4 : ℝ) ^ m ≠ 0 := by positivity
  field_simp

/-- `3^{n₀} ≤ x^{1/5}` for `x ≥ 1`: `n₀·log 3 ≤ (log x/(10 log 2))·log 3 ≤ (1/5) log x` since
`log 3 ≤ 2 log 2 = log 4`.  Bounds the `+3^{n−m₀}` rounding term of the orbit bracket. -/
theorem three_pow_nZero_le {x : ℝ} (hx1 : 1 ≤ x) : (3 : ℝ) ^ nZero x ≤ x ^ ((1 : ℝ) / 5) := by
  have hxpos : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hquot : 0 ≤ Real.log x / (10 * Real.log 2) := div_nonneg hlogx (by positivity)
  have hnf : (nZero x : ℝ) ≤ Real.log x / (10 * Real.log 2) := by
    unfold nZero; exact Nat.floor_le hquot
  have he : (3 : ℝ) ^ nZero x = Real.exp (Real.log 3 * (nZero x : ℝ)) := by
    rw [← Real.rpow_natCast (3 : ℝ) (nZero x), Real.rpow_def_of_pos (by norm_num)]
  have hx5 : x ^ ((1 : ℝ) / 5) = Real.exp (Real.log x * (1 / 5)) := Real.rpow_def_of_pos hxpos _
  rw [he, hx5]
  apply Real.exp_le_exp.mpr
  have hlog3le : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
    exact Real.log_le_log (by norm_num) (by norm_num)
  calc Real.log 3 * (nZero x : ℝ) ≤ Real.log 3 * (Real.log x / (10 * Real.log 2)) :=
        mul_le_mul_of_nonneg_left hnf hlog3.le
    _ ≤ (2 * Real.log 2) * (Real.log x / (10 * Real.log 2)) :=
        mul_le_mul_of_nonneg_right hlog3le hquot
    _ = Real.log x * (1 / 5) := by field_simp; ring

/-- **Slack core** for the (5.17) window: `2·log 2·log^{0.6}x + 1 ≤ log^{0.7}x` for `x` large
(`log^{0.7} = log^{0.6}·log^{0.1}`, and `log^{0.1}x ≥ 2 log 2 + 1` once `log x ≥ (2 log 2 + 1)^{10}`). -/
theorem slack_key :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ) + 1 ≤ (Real.log x) ^ (0.7 : ℝ) := by
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb : (0 : ℝ) ≤ 2 * Real.log 2 + 1 := by positivity
  have hb1 : (1 : ℝ) ≤ 2 * Real.log 2 + 1 := by linarith
  refine ⟨Real.exp ((2 * Real.log 2 + 1) ^ (10 : ℕ)), Real.one_le_exp (by positivity),
    fun x hx => ?_⟩
  have hL : (2 * Real.log 2 + 1) ^ (10 : ℕ) ≤ Real.log x := by
    rw [← Real.log_exp ((2 * Real.log 2 + 1) ^ (10 : ℕ))]; exact Real.log_le_log (Real.exp_pos _) hx
  have hL1 : (1 : ℝ) ≤ Real.log x := le_trans (one_le_pow₀ hb1) hL
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hL01 : (2 * Real.log 2 + 1) ≤ (Real.log x) ^ (0.1 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hL (by norm_num : (0 : ℝ) ≤ (0.1 : ℝ))
    rwa [← Real.rpow_natCast (2 * Real.log 2 + 1) 10, ← Real.rpow_mul hb,
      show ((10 : ℕ) : ℝ) * (0.1 : ℝ) = 1 by norm_num, Real.rpow_one] at h
  have hL06 : (1 : ℝ) ≤ (Real.log x) ^ (0.6 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hL06nn : (0 : ℝ) ≤ (Real.log x) ^ (0.6 : ℝ) := by linarith
  have hsplit : (Real.log x) ^ (0.7 : ℝ) = (Real.log x) ^ (0.6 : ℝ) * (Real.log x) ^ (0.1 : ℝ) := by
    rw [← Real.rpow_add hLpos]; norm_num
  rw [hsplit]
  nlinarith [hL01, hL06, hL06nn, mul_le_mul_of_nonneg_left hL01 hL06nn]

/-- Upper slack (from `slack_key`): `2^{2 log^{0.6}x} + 1 ≤ exp(log^{0.7}x)`.  (`2^{2t}=exp(2 log2·t)`,
and `exp(2log2 t)·e ≤ exp(log^{0.7})` with `e ≥ 2`, `2^{2t} ≥ 1`.) -/
theorem slack_upper {x : ℝ} (hLnn : 0 ≤ Real.log x)
    (hslack : 2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ) + 1 ≤ (Real.log x) ^ (0.7 : ℝ)) :
    (2 : ℝ) ^ (2 * (Real.log x) ^ (0.6 : ℝ)) + 1 ≤ Real.exp ((Real.log x) ^ (0.7 : ℝ)) := by
  have harg : (0 : ℝ) ≤ 2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) (Real.rpow_nonneg hLnn _)
  have heq : (2 : ℝ) ^ (2 * (Real.log x) ^ (0.6 : ℝ))
      = Real.exp (2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; ring
  rw [heq]
  have hmono : Real.exp (2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ)) * Real.exp 1
      ≤ Real.exp ((Real.log x) ^ (0.7 : ℝ)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hslack
  have hApos := Real.exp_pos (2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ))
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hA1 : (1 : ℝ) ≤ Real.exp (2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ)) := Real.one_le_exp harg
  nlinarith [hmono, hA1, he1, hApos]

/-- Lower slack (from `slack_key`): `exp(−log^{0.7}x) ≤ (3/8)·2^{−2 log^{0.6}x}`.  (`exp(2log2 t − log^{0.7})
≤ exp(−1) ≤ 3/8`, using `e ≥ 8/3`.) -/
theorem slack_lower {x : ℝ}
    (hslack : 2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ) + 1 ≤ (Real.log x) ^ (0.7 : ℝ)) :
    Real.exp (-(Real.log x) ^ (0.7 : ℝ)) ≤ (3 / 8) * (2 : ℝ) ^ (-(2 * (Real.log x) ^ (0.6 : ℝ))) := by
  have heq : (2 : ℝ) ^ (-(2 * (Real.log x) ^ (0.6 : ℝ)))
      = Real.exp (-(2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ))) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; ring
  rw [heq]
  have hle : -(Real.log x) ^ (0.7 : ℝ) ≤ -1 + -(2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ)) := by
    linarith
  calc Real.exp (-(Real.log x) ^ (0.7 : ℝ))
        ≤ Real.exp (-1 + -(2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ))) := Real.exp_le_exp.mpr hle
    _ = Real.exp (-1) * Real.exp (-(2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ))) := by
        rw [Real.exp_add]
    _ ≤ (3 / 8) * Real.exp (-(2 * Real.log 2 * (Real.log x) ^ (0.6 : ℝ))) := by
        have he8 : Real.exp (-1) ≤ 3 / 8 := by
          have he : (8 : ℝ) / 3 ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
          have hid : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_pos (-1), he, hid,
            mul_nonneg (Real.exp_pos (-1)).le (by linarith : (0 : ℝ) ≤ Real.exp 1 - 8 / 3)]
        exact mul_le_mul_of_nonneg_right he8 (Real.exp_pos _).le

/-- **(5.17) passage orbit-straddle core** — on `{T_x N = n ∧ good⁽ⁿ⁰⁾}` with `N` odd, `n ∈ I_y`, the
passage-scaled quantity `(3/4)^n·N` is pinned near `x`:
`(3/8)·x·2^{−log^{0.6}x} ≤ (3/4)^n·N ≤ x·2^{log^{0.6}x}`.
Upper: `Syr^n N ≤ ⌊x⌋ ≤ x` with the good bracket lower half.  Lower: `Syr^{n−1}N > ⌊x⌋ > x−1` (passage
minimality) with the good bracket upper half at `n−1`, absorbing the `+3^{n−1}` rounding via
`three_pow_nZero_le` (`3^{n−1} ≤ x^{1/5} ≤ x/2`).  This is the genuine first-passage content of the
size window; everything else is `±`-slack absorption (`slack_upper`/`slack_lower`). -/
theorem stepback_passage_scale :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
        ∀ N : ℕ, N % 2 = 1 → passTime ⌊x⌋₊ N = n →
          goodTuple x (nZero x) (valVec N (nZero x)) →
            (3 / 8) * x * (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ))) ≤ (3 / 4 : ℝ) ^ n * (N : ℝ) ∧
              (3 / 4 : ℝ) ^ n * (N : ℝ) ≤ x * (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) := by
  obtain ⟨xmz, _hxmz1, hmz⟩ := mZero_le_of_mem_Iy
  refine ⟨max xmz (Real.exp 100000), le_max_of_le_right (Real.one_le_exp (by norm_num)),
    fun x hx y hy n hn N hodd hT hgood => ?_⟩
  have hxmz : xmz ≤ x := le_trans (le_max_left _ _) hx
  have hxexp : Real.exp 100000 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hxexp
  have hxpos : (0 : ℝ) < x := by linarith
  have hLbig : (100000 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 100000]; exact Real.log_le_log (Real.exp_pos _) hxexp
  -- positivity of the slack factors
  have hs_pos : (0 : ℝ) < (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hsn_pos : (0 : ℝ) < (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcancel : (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ))) * (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  have hcancel2 : (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) * (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
  -- index facts
  obtain ⟨hm1, hmn⟩ := hmz x hxmz y hy n hn
  have hn1 : 1 ≤ n := le_trans hm1 hmn
  have hn_le_n0 : n ≤ nZero x := mem_Iy_le_nZero hn
  have hn1_le_n0 : n - 1 ≤ nZero x := le_trans (Nat.sub_le n 1) hn_le_n0
  -- passes N (from T_x N = n ≥ 1)
  have hpass : passes ⌊x⌋₊ N := by
    by_contra hnp
    have hempty : {k | syr^[k] N ≤ ⌊x⌋₊} = ∅ := by
      ext k; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hk => hnp ⟨k, hk⟩
    have hz : passTime ⌊x⌋₊ N = 0 := by unfold passTime; rw [hempty, Nat.sInf_empty]
    omega
  have hne : {k | syr^[k] N ≤ ⌊x⌋₊}.Nonempty := hpass
  have hTs : sInf {k | syr^[k] N ≤ ⌊x⌋₊} = n := hT
  -- passage: Syr^n N ≤ ⌊x⌋ and ⌊x⌋ < Syr^{n−1}N
  have hpassmem : syr^[n] N ≤ ⌊x⌋₊ := by
    have h := Nat.sInf_mem hne; rw [hTs] at h; exact h
  have hmin : ⌊x⌋₊ < syr^[n - 1] N := by
    by_contra hle
    push Not at hle
    have hmem : n - 1 ∈ {k | syr^[k] N ≤ ⌊x⌋₊} := hle
    have hle' : sInf {k | syr^[k] N ≤ ⌊x⌋₊} ≤ n - 1 := Nat.sInf_le hmem
    rw [hTs] at hle'; omega
  -- good bracket at n and n−1
  obtain ⟨hbn_lo, _hbn_hi⟩ := syr_iterate_good_bracket' x N (nZero x) n hodd hgood hn_le_n0
  obtain ⟨_hbn1_lo, hbn1_hi⟩ := syr_iterate_good_bracket' x N (nZero x) (n - 1) hodd hgood hn1_le_n0
  -- pow split for the n−1 bracket
  have hpow1 : (3 / 4 : ℝ) ^ (n - 1) = (4 / 3) * (3 / 4) ^ n := by
    have h := pow_stepback_eq (m := 1) (n := n) hn1; rwa [pow_one] at h
  rw [hpow1] at hbn1_hi
  -- x < Syr^{n−1}N
  have hx_lt : x < (syr^[n - 1] N : ℝ) := by
    have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (syr^[n - 1] N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hmin
    linarith
  -- 3^{n−1} ≤ x/2
  have h3half : (3 : ℝ) ^ (n - 1) ≤ x / 2 := by
    have hmono : (3 : ℝ) ^ (n - 1) ≤ (3 : ℝ) ^ nZero x := pow_le_pow_right₀ (by norm_num) hn1_le_n0
    have hx15 : (3 : ℝ) ^ nZero x ≤ x ^ ((1 : ℝ) / 5) := three_pow_nZero_le hx1
    have hx15half : x ^ ((1 : ℝ) / 5) ≤ x / 2 := by
      have hxd : (0 : ℝ) < x / 2 := by linarith
      rw [← Real.exp_log (Real.rpow_pos_of_pos hxpos _), ← Real.exp_log hxd]
      apply Real.exp_le_exp.mpr
      rw [Real.log_rpow hxpos, Real.log_div (ne_of_gt hxpos) (by norm_num)]
      have hlog2le1 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      nlinarith [hLbig, hlog2le1]
    linarith
  refine ⟨?_, ?_⟩
  · -- lower: (3/8)·x·2^{−L^{0.6}} ≤ (3/4)^n·N
    have hge2 : (3 / 8) * x ≤ (3 / 4 : ℝ) ^ n * N * (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) := by
      have hxlt2 := lt_of_lt_of_le hx_lt hbn1_hi
      nlinarith [hxlt2, h3half]
    have keyL : (3 / 4 : ℝ) ^ n * N * (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ))
        * (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ))) = (3 / 4 : ℝ) ^ n * N := by
      rw [mul_assoc, hcancel2, mul_one]
    have hfin := mul_le_mul_of_nonneg_right hge2 hsn_pos.le
    rw [keyL] at hfin
    exact hfin
  · -- upper: (3/4)^n·N ≤ x·2^{L^{0.6}}
    have hfloorx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxpos.le
    have hup1 : (3 / 4 : ℝ) ^ n * N * (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ))) ≤ x :=
      le_trans hbn_lo (le_trans (by exact_mod_cast hpassmem) hfloorx)
    have key : (3 / 4 : ℝ) ^ n * N * (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ)))
        * (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) = (3 / 4 : ℝ) ^ n * N := by
      rw [mul_assoc, hcancel, mul_one]
    have hup2 := mul_le_mul_of_nonneg_right hup1 hs_pos.le
    rw [key] at hup2
    exact hup2


/-- **(5.17) size-window brick** — on `{T_x N = n ∧ good⁽ⁿ⁰⁾}`, `N` odd, `n ∈ I_y`, the stepped-back
iterate `M = Syr^{n−m₀}N` lands in the `E'` size window `exp(±log^{0.7}x)·(4/3)^{m₀}·x`.  Assembled from
the passage core `stepback_passage_scale` (pinning `(3/4)^n·N ≍ x`), the good bracket at `k = n−m₀`
(`syr_iterate_good_bracket'`), the pow split `pow_stepback_eq` ((3/4)^{n−m₀}=(4/3)^{m₀}(3/4)^n), and the
`±`-slack absorption `slack_upper`/`slack_lower` (with `three_pow_nZero_le` for the `+3^{n−m₀}` term). -/
theorem stepback_size_window :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ), ∀ n ∈ Iy x y,
        ∀ N : ℕ, N % 2 = 1 → passTime ⌊x⌋₊ N = n →
          goodTuple x (nZero x) (valVec N (nZero x)) →
            Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x
                ≤ (syr^[n - mZero x] N : ℝ) ∧
              (syr^[n - mZero x] N : ℝ)
                ≤ Real.exp (Real.log x ^ (0.7 : ℝ)) * (4 / 3) ^ mZero x * x := by
  obtain ⟨xps, hxps1, hscale⟩ := stepback_passage_scale
  obtain ⟨xsk, _hxsk1, hsk⟩ := slack_key
  obtain ⟨xmz, _hxmz1, hmz⟩ := mZero_le_of_mem_Iy
  refine ⟨max (max xps xsk) xmz, le_max_of_le_left (le_max_of_le_left hxps1),
    fun x hx y hy n hn N hodd hT hgood => ?_⟩
  have hxps : xps ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxsk : xsk ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxmz : xmz ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans hxps1 hxps
  have hxpos : (0 : ℝ) < x := by linarith
  have hLnn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  -- positivity of the slack factors
  have hs_pos : (0 : ℝ) < (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hsn_pos : (0 : ℝ) < (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hQpos : (0 : ℝ) < (4 / 3 : ℝ) ^ mZero x := by positivity
  have hQ1 : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ mZero x := one_le_pow₀ (by norm_num)
  -- interval facts
  obtain ⟨_, hmn⟩ := hmz x hxmz y hy n hn
  have hk : n - mZero x ≤ nZero x := le_trans (Nat.sub_le _ _) (mem_Iy_le_nZero hn)
  -- good bracket at k = n − m₀, rewritten via the (3/4)^{n−m₀} split
  obtain ⟨hbr_lo, hbr_hi⟩ := syr_iterate_good_bracket' x N (nZero x) (n - mZero x) hodd hgood hk
  rw [pow_stepback_eq hmn] at hbr_lo hbr_hi
  -- passage scale
  obtain ⟨hsc_lo, hsc_hi⟩ := hscale x hxps y hy n hn N hodd hT hgood
  -- 3^{n−m₀} ≤ (4/3)^{m₀}·x
  have h3k : (3 : ℝ) ^ (n - mZero x) ≤ (4 / 3 : ℝ) ^ mZero x * x := by
    have hmono : (3 : ℝ) ^ (n - mZero x) ≤ (3 : ℝ) ^ nZero x :=
      pow_le_pow_right₀ (by norm_num) hk
    have hx15 : x ^ ((1 : ℝ) / 5) ≤ x := by
      have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) / 5 ≤ 1)
      rwa [Real.rpow_one] at this
    have hxle : x ≤ (4 / 3 : ℝ) ^ mZero x * x := by nlinarith [hQ1, hxpos]
    calc (3 : ℝ) ^ (n - mZero x) ≤ (3 : ℝ) ^ nZero x := hmono
      _ ≤ x ^ ((1 : ℝ) / 5) := three_pow_nZero_le hx1
      _ ≤ x := hx15
      _ ≤ (4 / 3 : ℝ) ^ mZero x * x := hxle
  -- square identities for the slack factors
  have hss : (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) * (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ))
      = (2 : ℝ) ^ (2 * Real.log x ^ (0.6 : ℝ)) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  have hssn : (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ))) * (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ)))
      = (2 : ℝ) ^ (-(2 * Real.log x ^ (0.6 : ℝ))) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  -- slack lemmas, folded to the squared factors
  have hSU : (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) * (2 : ℝ) ^ (Real.log x ^ (0.6 : ℝ)) + 1
      ≤ Real.exp (Real.log x ^ (0.7 : ℝ)) := by
    rw [hss]; exact slack_upper hLnn (hsk x hxsk)
  have hSL : Real.exp (-(Real.log x ^ (0.7 : ℝ)))
      ≤ (3 / 8) * ((2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ))) * (2 : ℝ) ^ (-(Real.log x ^ (0.6 : ℝ)))) := by
    rw [hssn]; exact slack_lower (hsk x hxsk)
  refine ⟨?_, ?_⟩
  · -- lower
    have hC := mul_nonneg (mul_nonneg hQpos.le hsn_pos.le) (sub_nonneg.mpr hsc_lo)
    have hD := mul_nonneg (mul_nonneg hQpos.le hxpos.le) (sub_nonneg.mpr hSL)
    nlinarith [hbr_lo, hC, hD]
  · -- upper
    have hA := mul_nonneg (mul_nonneg hQpos.le hs_pos.le) (sub_nonneg.mpr hsc_hi)
    have hB := mul_nonneg (mul_nonneg hQpos.le hxpos.le) (sub_nonneg.mpr hSU)
    nlinarith [hbr_hi, hA, hB, h3k]

open Classical in
/-- **(5.17) forward leg** — `firstPassMid ≤ steppedMid`, a deterministic event inclusion with NO
error.  For each `n ∈ I_y` the good-passage event
`S_n = {T_x N = n ∧ Pass_x N ∈ E ∧ good⁽ⁿ⁰⁾(N)}` embeds into the stepped-back diagonal event
`T_n = {good⁽ⁿ⁻ᵐ⁰⁾(N) ∧ E'(Syr^{n−m₀}N)}`, verified for odd `N` (`expect_mono_on_support`):
* the good-tuple index drops by `good_nested` (`n − m₀ ≤ n ≤ n₀`, `mem_Iy_le_nZero`);
* `passTime M = m₀`, `passLoc M = passLoc N ∈ E` are EXACT via `passTime_stepback` (using `m₀ ≤ n`,
  `mZero_le_of_mem_Iy`, and `passes N` from `T_x N = n ≥ 1`);
* `M % 2 = 1` from `syr_iterate_odd`;
* the `E'` size window is `stepback_size_window`.
Hence `S_n ⊆ T_n` on the odd support and the finite `I_y`-sum is monotone. -/
theorem firstPassMid_le_steppedMid :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          firstPassMid x E y ≤ steppedMid x E y := by
  obtain ⟨xw, hxw1, hwin⟩ := stepback_size_window
  obtain ⟨xi, _hxi1, hint⟩ := mZero_le_of_mem_Iy
  refine ⟨max xw xi, le_max_of_le_left hxw1, fun x hx E hE y hy => ?_⟩
  have hxw : xw ≤ x := le_trans (le_max_left _ _) hx
  have hxi : xi ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans hxw1 hxw
  have hyge1 : (1 : ℝ) ≤ y := by
    rcases hy with h | h
    · rw [h]; exact Real.one_le_rpow hx1 (by unfold alpha; norm_num)
    · rw [h]; exact Real.one_le_rpow hx1 (by positivity)
  have hy1 : (1 : ℝ) ≤ y ^ alpha := Real.one_le_rpow hyge1 (by unfold alpha; norm_num)
  unfold firstPassMid steppedMid
  refine Finset.sum_le_sum (fun n hn => ?_)
  refine expect_mono_on_support (logUnifOdd y (y ^ alpha)) _ _ (fun N hNsupp hNS => ?_)
  obtain ⟨hT, hL, hG⟩ := hNS
  have hNodd : N % 2 = 1 := (logUnifOdd_support_le hy1 hNsupp).1
  obtain ⟨hm1, hmn⟩ := hint x hxi y hy n hn
  have hn1 : 1 ≤ n := le_trans hm1 hmn
  have hpass : passes ⌊x⌋₊ N := by
    by_contra hnp
    have hempty : {k | syr^[k] N ≤ ⌊x⌋₊} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hk => hnp ⟨k, hk⟩
    have hz : passTime ⌊x⌋₊ N = 0 := by unfold passTime; rw [hempty, Nat.sInf_empty]
    omega
  have hk : n - mZero x ≤ passTime ⌊x⌋₊ N := by rw [hT]; omega
  obtain ⟨_hpassM, hTM, hLM⟩ := passTime_stepback ⌊x⌋₊ N (n - mZero x) hpass hk
  have hGnest : goodTuple x (n - mZero x) (valVec N (n - mZero x)) :=
    good_nested (le_trans (Nat.sub_le n (mZero x)) (mem_Iy_le_nZero hn)) hG
  refine ⟨hGnest, syr_iterate_odd N (n - mZero x) hNodd, ?_, ?_, ?_, ?_⟩
  · rw [hTM, hT]; omega
  · rw [hLM]; exact hL
  · exact (hwin x hxw y hy n hn N hNodd hT hG).1
  · exact (hwin x hxw y hy n hn N hNodd hT hG).2

/-- **`Eprime` forces the passage index** — the disjointness key for the (5.17) reverse leg.  If
`N` passes, `m₀ ≤ n`, and the step-back `Syr^{n−m₀}N` satisfies `E'` (in particular passes at time
`m₀`), and the step-back does not overshoot passage (`n − m₀ ≤ T_x N`), then `T_x N = n`.  Consequence:
the stepped-back events `T_n = {good⁽ⁿ⁻ᵐ⁰⁾ ∧ E'(Syr^{n−m₀}N)}` are **pairwise disjoint** in `n` (each
`N` lies in at most one, `n = T_x N`), so `∑_{n∈I_y} 𝟙_{T_n} ≤ 1` pointwise and the reverse-defect sum
`∑_n P(T_n ∖ S_n)` collapses to a single probability — no `O(log x)` blow-up from the `I_y` sum. -/
theorem eprime_forces_passTime {x : ℝ} {E : Set ℕ} {N n : ℕ}
    (hpass : passes ⌊x⌋₊ N) (hk : n - mZero x ≤ passTime ⌊x⌋₊ N) (hmn : mZero x ≤ n)
    (hE : Eprime x E (syr^[n - mZero x] N)) : passTime ⌊x⌋₊ N = n := by
  obtain ⟨_, hTM, _⟩ := passTime_stepback ⌊x⌋₊ N (n - mZero x) hpass hk
  have hEm : passTime ⌊x⌋₊ (syr^[n - mZero x] N) = mZero x := hE.2.1
  rw [hTM] at hEm
  omega

/-- **Reverse finite union bound for `PMF.expect`.**  If a finite sum of event indicators is
dominated pointwise by a single indicator `𝟙_U`, then the sum of the term expectations is at most
`E[𝟙_U]`.  (The mirror of `expect_le_sum_of_indicator_le`; used to collapse the reverse-defect
`∑_n E[𝟙_{¬good ∧ T_x=n}]` onto `E[𝟙_{¬good}]` via the `T_x N = n` disjointness across `n`.) -/
theorem sum_expect_le_of_indicator_ge {α ι : Type*} (p : PMF α) (s : Finset ι) (T : ι → Set α)
    (U : Set α)
    (h : ∀ a, ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a ≤ Set.indicator U 1 a) :
    ∑ i ∈ s, p.expect (Set.indicator (T i) 1) ≤ p.expect (Set.indicator U 1) := by
  classical
  have hsumP : Summable fun a => (p a).toReal := ENNReal.summable_toReal p.tsum_coe_ne_top
  have ind01 : ∀ (V : Set α) a,
      (0 : ℝ) ≤ Set.indicator V (1 : α → ℝ) a ∧ Set.indicator V (1 : α → ℝ) a ≤ 1 := by
    intro V a
    refine ⟨Set.indicator_nonneg (fun _ _ => zero_le_one) a, ?_⟩
    rw [Set.indicator_apply]; split <;> simp
  have hsum : ∀ (V : Set α), Summable fun a => (p a).toReal * Set.indicator V (1 : α → ℝ) a := by
    intro V
    exact Summable.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (ind01 V a).1)
      (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (ind01 V a).2) hsumP
  have hswap : (∑ i ∈ s, p.expect (Set.indicator (T i) 1))
      = ∑' a, (p a).toReal * ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a := by
    unfold PMF.expect
    rw [← Summable.tsum_finsetSum (fun i _ => hsum (T i))]
    exact tsum_congr fun a => by rw [Finset.mul_sum]
  rw [hswap]
  show (∑' a, (p a).toReal * ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a) ≤
      ∑' a, (p a).toReal * Set.indicator U 1 a
  have hsumLHS : Summable fun a => (p a).toReal * ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a := by
    refine Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun i _ => (ind01 (T i) a).1))
      (fun a => ?_) (hsumP.mul_right (s.card : ℝ))
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    calc ∑ i ∈ s, Set.indicator (T i) (1 : α → ℝ) a ≤ ∑ _i ∈ s, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (ind01 (T i) a).2
      _ = (s.card : ℝ) := by simp
  refine hsumLHS.tsum_le_tsum (fun a => ?_) (hsum U)
  exact mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg

/-- `Eprime` at a step-back time forces the base point to pass (given `1 ≤ m₀`): `E'` pins the
first-passage time of `Syr^{k}N` to `m₀ ≥ 1`, so `Syr^{k}N` — hence `N` itself — reaches `≤ ⌊x⌋`. -/
theorem passes_of_eprime {x : ℝ} {E : Set ℕ} {N k : ℕ} (hm : 1 ≤ mZero x)
    (hE : Eprime x E (syr^[k] N)) : passes ⌊x⌋₊ N := by
  have hT : passTime ⌊x⌋₊ (syr^[k] N) = mZero x := hE.2.1
  have hpassM : passes ⌊x⌋₊ (syr^[k] N) := by
    by_contra hnp
    have hempty : {j | syr^[j] (syr^[k] N) ≤ ⌊x⌋₊} = ∅ := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hj => hnp ⟨j, hj⟩
    have hz : passTime ⌊x⌋₊ (syr^[k] N) = 0 := by unfold passTime; rw [hempty, Nat.sInf_empty]
    omega
  obtain ⟨j, hj⟩ := hpassM
  exact ⟨j + k, by rw [Function.iterate_add_apply]; exact hj⟩

/-- **Early-return size contradiction** (the analytic core).  For `x` large, the `E′` size floor
`exp(−log^{0.7}x)·(4/3)^{m₀}·x` STRICTLY exceeds `(3/4)·x·2^{2log^{0.6}x} + x^{1/5}`.  Since
`m₀ = ⌊log x/100000⌋`, `(4/3)^{m₀} ≥ (3/4)·x^{log(4/3)/100000}`, so the floor grows like `x^{1+δ}`
(δ > 0) while the RHS grows like `x·exp(O(log^{0.6}x))` — sub-`x^{1+δ}`.  This is exactly why a good
orbit that already passed (`≤ x`, decreasing) can NEVER re-attain the `(4/3)^{m₀}x` floor. -/
theorem earlyReturn_size_contra : ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
    (3 / 4 : ℝ) * x * (2 : ℝ) ^ (2 * Real.log x ^ (0.6 : ℝ)) + x ^ ((1 : ℝ) / 5)
      < Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3 : ℝ) ^ mZero x * x := by
  have hβpos : (0 : ℝ) < (alpha - 1) / 100 := by unfold alpha; norm_num
  have hlg43pos : (0 : ℝ) < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hlg2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlg2le1 : Real.log 2 ≤ 1 := by
    have : Real.log 2 ≤ Real.log (Real.exp 1) :=
      Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
    rwa [Real.log_exp] at this
  have hlg43le1 : Real.log (4 / 3) ≤ 1 := by
    have : Real.log (4 / 3) ≤ Real.log (Real.exp 1) :=
      Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
    rwa [Real.log_exp] at this
  set θ := 5 / ((alpha - 1) / 100 * Real.log (4 / 3)) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  refine ⟨Real.exp (max 1 ((θ + 1) ^ (10 / 3 : ℝ))),
    Real.one_le_exp_iff.mpr (le_trans zero_le_one (le_max_left _ _)), fun x hx => ?_⟩
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx1 : (1 : ℝ) ≤ x :=
    le_trans (Real.one_le_exp_iff.mpr (le_trans zero_le_one (le_max_left _ _))) hx
  have hLge : max 1 ((θ + 1) ^ (10 / 3 : ℝ)) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  have hL1 : (1 : ℝ) ≤ Real.log x := le_trans (le_max_left _ _) hLge
  have hLpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  set L06 := Real.log x ^ (0.6 : ℝ) with hL06def
  set L07 := Real.log x ^ (0.7 : ℝ) with hL07def
  have hL07pos : (0 : ℝ) < L07 := Real.rpow_pos_of_pos hLpos _
  have h1L07 : (1 : ℝ) ≤ L07 := Real.one_le_rpow hL1 (by norm_num)
  have hL06nn : (0 : ℝ) ≤ L06 := (Real.rpow_pos_of_pos hLpos _).le
  have hL0607 : L06 ≤ L07 := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hm0R : (alpha - 1) / 100 * Real.log x - 1 < (mZero x : ℝ) := by
    have h := Nat.lt_floor_add_one ((alpha - 1) / 100 * Real.log x)
    have heq : (mZero x : ℝ) = (⌊(alpha - 1) / 100 * Real.log x⌋₊ : ℝ) := rfl
    rw [heq]; linarith
  have h43m0 : Real.exp (Real.log (4 / 3) * ((alpha - 1) / 100 * Real.log x - 1))
      ≤ (4 / 3 : ℝ) ^ mZero x := by
    rw [← Real.rpow_natCast (4 / 3 : ℝ) (mZero x),
      ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4 / 3) hm0R.le
  -- master polynomial inequality: sublinear LHS < linear RHS
  have hmaster : Real.log 2 + 2 * L06 * Real.log 2 + L07 + Real.log (4 / 3)
      < (alpha - 1) / 100 * Real.log (4 / 3) * Real.log x := by
    have hupper : Real.log 2 + 2 * L06 * Real.log 2 + L07 + Real.log (4 / 3) ≤ 5 * L07 := by
      nlinarith [hlg2le1, hlg43le1, hL0607, h1L07, hL06nn, hlg2pos.le,
        mul_le_mul_of_nonneg_left hlg2le1 hL06nn]
    have hL03 : θ < Real.log x ^ (0.3 : ℝ) := by
      have hpow : ((θ + 1) ^ (10 / 3 : ℝ)) ^ (0.3 : ℝ) = θ + 1 := by
        rw [← Real.rpow_mul (by positivity), show (10 / 3 : ℝ) * 0.3 = 1 by norm_num, Real.rpow_one]
      have hmono : ((θ + 1) ^ (10 / 3 : ℝ)) ^ (0.3 : ℝ) ≤ Real.log x ^ (0.3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hLge) (by norm_num)
      rw [hpow] at hmono; linarith
    have hLsplit : L07 * Real.log x ^ (0.3 : ℝ) = Real.log x := by
      rw [hL07def, ← Real.rpow_add hLpos, show (0.7 : ℝ) + 0.3 = 1 by norm_num, Real.rpow_one]
    have hkey : θ * ((alpha - 1) / 100 * Real.log (4 / 3)) = 5 := by
      rw [hθdef]; exact div_mul_cancel₀ 5 (by positivity)
    have hstepb : 5 * L07 < (alpha - 1) / 100 * Real.log (4 / 3) * Real.log x := by
      have hpos : (0 : ℝ) < (alpha - 1) / 100 * Real.log (4 / 3) := by positivity
      have h5 : 5 < Real.log x ^ (0.3 : ℝ) * ((alpha - 1) / 100 * Real.log (4 / 3)) := by
        nlinarith [mul_lt_mul_of_pos_right hL03 hpos, hkey]
      rw [← hLsplit]
      nlinarith [mul_lt_mul_of_pos_right h5 hL07pos]
    linarith [hupper, hstepb]
  -- exp conversions
  have hxexp : x = Real.exp (Real.log x) := (Real.exp_log hxpos).symm
  have hLHS : (3 / 4 : ℝ) * x * (2 : ℝ) ^ (2 * L06) + x ^ ((1 : ℝ) / 5)
      ≤ Real.exp (Real.log x + Real.log 2 + 2 * L06 * Real.log 2) := by
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 * L06) := Real.rpow_pos_of_pos (by norm_num) _
    have h2ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * L06) := Real.one_le_rpow (by norm_num) (by positivity)
    have hx15 : x ^ ((1 : ℝ) / 5) ≤ x := by
      have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) / 5 ≤ 1)
      rwa [Real.rpow_one] at this
    have hstep1 : (3 / 4 : ℝ) * x * (2 : ℝ) ^ (2 * L06) + x ^ ((1 : ℝ) / 5)
        ≤ 2 * x * (2 : ℝ) ^ (2 * L06) := by
      have hxx : x ^ ((1 : ℝ) / 5) ≤ x * (2 : ℝ) ^ (2 * L06) :=
        le_trans hx15 (le_mul_of_one_le_right hxpos.le h2ge1)
      nlinarith [hxx, mul_nonneg hxpos.le h2pos.le]
    have hexpeq : 2 * x * (2 : ℝ) ^ (2 * L06)
        = Real.exp (Real.log x + Real.log 2 + 2 * L06 * Real.log 2) := by
      have ha : (2 : ℝ) * (2 : ℝ) ^ (2 * L06) = (2 : ℝ) ^ (1 + 2 * L06) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      calc 2 * x * (2 : ℝ) ^ (2 * L06)
          = x * ((2 : ℝ) * (2 : ℝ) ^ (2 * L06)) := by ring
        _ = x * (2 : ℝ) ^ (1 + 2 * L06) := by rw [ha]
        _ = Real.exp (Real.log x) * Real.exp (Real.log 2 * (1 + 2 * L06)) := by
            rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← hxexp]
        _ = Real.exp (Real.log x + Real.log 2 * (1 + 2 * L06)) := (Real.exp_add _ _).symm
        _ = Real.exp (Real.log x + Real.log 2 + 2 * L06 * Real.log 2) := by congr 1; ring
    exact le_trans hstep1 hexpeq.le
  have hRHS : Real.exp (Real.log x + Real.log (4 / 3) * ((alpha - 1) / 100 * Real.log x - 1) - L07)
      ≤ Real.exp (-L07) * (4 / 3 : ℝ) ^ mZero x * x := by
    have key : Real.exp (-L07)
          * Real.exp (Real.log (4 / 3) * ((alpha - 1) / 100 * Real.log x - 1))
          * Real.exp (Real.log x)
        = Real.exp (Real.log x + Real.log (4 / 3) * ((alpha - 1) / 100 * Real.log x - 1) - L07) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [← key]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h43m0 (Real.exp_pos _).le) hxexp.ge
      (Real.exp_pos _).le (by positivity)
  refine lt_of_le_of_lt hLHS (lt_of_lt_of_le ?_ hRHS)
  rw [Real.exp_lt_exp]
  nlinarith [hmaster]

open Classical in
/-- **(5.17) reverse leg — the early-return event is EMPTY for large `x`** (PROVED modulo the analytic
size gap `earlyReturn_size_contra`).  Case B: a `good⁽ⁿ⁻ᵐ⁰⁾` orbit that already passed `≤ ⌊x⌋` at
`T_x N < n−m₀` decreases like `syr^[j]N ≈ (3/4)^j N`, so by step `n−m₀` it sits below
`(3/4)·x·2^{2log^{0.6}x}`, FAR under the `E′` floor `exp(−log^{0.7}x)(4/3)^{m₀}x ≈ x^{1+δ}`
(`earlyReturn_size_contra`).  Hence no odd `N` satisfies the event, every expectation is `0`, and the
sum is `0 ≤ log^{-1}x`.  (The `good` conjunct — available because `N ∈ T_n` — is what collapses this
from a genuine union-of-returns whp estimate to an emptiness argument.) -/
noncomputable def c_earlyReturn : ℝ := 1

theorem c_earlyReturn_pos : 0 < c_earlyReturn := by norm_num [c_earlyReturn]

/-- Sibling of `reverse_early_return_whp` with the `c`-slot pinned to `c_earlyReturn`; the
original delegates here. -/
theorem reverse_early_return_whp_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          ∑ n ∈ Iy x y, (logUnifOdd y (y ^ alpha)).expect
              (Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧ Eprime x E (syr^[n - mZero x] N) ∧
                passTime ⌊x⌋₊ N < n - mZero x} 1)
            ≤ 1 * (Real.log x) ^ (-c_earlyReturn) := by
  obtain ⟨xs, hxs1, hsize⟩ := earlyReturn_size_contra
  obtain ⟨xi, _hxi1, hint⟩ := mZero_le_of_mem_Iy
  rw [show c_earlyReturn = 1 from rfl]
  refine ⟨max (max xs xi) (Real.exp 1), fun x hx E hE y hy => ?_⟩
  have hxs : xs ≤ x := (le_max_left xs xi).trans ((le_max_left _ _).trans hx)
  have hxi : xi ≤ x := (le_max_right xs xi).trans ((le_max_left _ _).trans hx)
  have hexp : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx_gt1 : (1 : ℝ) < x := by linarith [Real.add_one_le_exp (1 : ℝ), hexp]
  have hx1 : (1 : ℝ) ≤ x := hx_gt1.le
  have hxpos : (0 : ℝ) < x := lt_trans one_pos hx_gt1
  have hlogpos : (0 : ℝ) < Real.log x := Real.log_pos hx_gt1
  have hyge1 : (1 : ℝ) ≤ y := by
    rcases hy with h | h
    · rw [h]; exact Real.one_le_rpow hx1 (by unfold alpha; norm_num)
    · rw [h]; exact Real.one_le_rpow hx1 (by positivity)
  have hyα1 : (1 : ℝ) ≤ y ^ alpha := Real.one_le_rpow hyge1 (by unfold alpha; norm_num)
  classical
  set P := logUnifOdd y (y ^ alpha) with hPdef
  have hzero : ∀ n ∈ Iy x y, P.expect (Set.indicator {N | goodTuple x (n - mZero x)
      (valVec N (n - mZero x)) ∧ Eprime x E (syr^[n - mZero x] N) ∧
      passTime ⌊x⌋₊ N < n - mZero x} 1) ≤ 0 := by
    intro n hn
    obtain ⟨hm1, hmn⟩ := hint x hxi y hy n hn
    refine le_trans (expect_mono_on_support P _ (∅ : Set ℕ) (fun N hNsupp hNS => ?_))
      (by simp [PMF.expect])
    obtain ⟨hgood, hE', hlt⟩ := hNS
    set k := n - mZero x with hk_def
    have hN : N % 2 = 1 := (logUnifOdd_support_le hyα1 hNsupp).1
    have hkn0 : k ≤ nZero x := le_trans (Nat.sub_le n (mZero x)) (mem_Iy_le_nZero hn)
    have hpass : passes ⌊x⌋₊ N := passes_of_eprime hm1 hE'
    have ht_le : passTime ⌊x⌋₊ N ≤ k := le_of_lt hlt
    have hne : {j | syr^[j] N ≤ ⌊x⌋₊}.Nonempty := hpass
    have htmem : syr^[passTime ⌊x⌋₊ N] N ≤ ⌊x⌋₊ := Nat.sInf_mem hne
    have htmemR : (syr^[passTime ⌊x⌋₊ N] N : ℝ) ≤ x :=
      le_trans (by exact_mod_cast htmem) (Nat.floor_le hxpos.le)
    obtain ⟨hblo_t, -⟩ := syr_iterate_good_bracket' x N k (passTime ⌊x⌋₊ N) hN hgood ht_le
    obtain ⟨-, hbhi_k⟩ := syr_iterate_good_bracket' x N k k hN hgood (le_refl k)
    set L06 := Real.log x ^ (0.6 : ℝ) with hL06
    have hs_pos : (0 : ℝ) < (2 : ℝ) ^ L06 := Real.rpow_pos_of_pos (by norm_num) L06
    have hEfloor : Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3 : ℝ) ^ mZero x * x
        ≤ (syr^[k] N : ℝ) := hE'.2.2.2.1
    -- (3/4)^t · N ≤ x · 2^{L06}
    have hI : (3 / 4 : ℝ) ^ (passTime ⌊x⌋₊ N) * N ≤ x * (2 : ℝ) ^ L06 := by
      have h1 : (3 / 4 : ℝ) ^ (passTime ⌊x⌋₊ N) * N * (2 : ℝ) ^ (-L06) ≤ x := le_trans hblo_t htmemR
      have h2 := mul_le_mul_of_nonneg_right h1 hs_pos.le
      rwa [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel,
        Real.rpow_zero, mul_one] at h2
    -- (3/4)^k ≤ (3/4) · (3/4)^t
    have hkt : (3 / 4 : ℝ) ^ k ≤ (3 / 4) * (3 / 4 : ℝ) ^ (passTime ⌊x⌋₊ N) := by
      rw [show k = passTime ⌊x⌋₊ N + (k - passTime ⌊x⌋₊ N) from (Nat.add_sub_cancel' ht_le).symm,
        pow_add]
      have hkt1 : (3 / 4 : ℝ) ^ (k - passTime ⌊x⌋₊ N) ≤ 3 / 4 := by
        have h1 : 1 ≤ k - passTime ⌊x⌋₊ N := by omega
        calc (3 / 4 : ℝ) ^ (k - passTime ⌊x⌋₊ N) ≤ (3 / 4 : ℝ) ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) h1
          _ = 3 / 4 := by norm_num
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (passTime ⌊x⌋₊ N), hkt1]
    -- (3/4)^k · N · 2^{L06} ≤ (3/4) · x · (2^{L06} · 2^{L06})
    have hpkNrs : (3 / 4 : ℝ) ^ k * N * (2 : ℝ) ^ L06
        ≤ (3 / 4) * x * ((2 : ℝ) ^ L06 * (2 : ℝ) ^ L06) := by
      have hstep : (3 / 4 : ℝ) ^ k * N ≤ (3 / 4) * (x * (2 : ℝ) ^ L06) := by
        calc (3 / 4 : ℝ) ^ k * N ≤ ((3 / 4) * (3 / 4 : ℝ) ^ (passTime ⌊x⌋₊ N)) * N :=
              mul_le_mul_of_nonneg_right hkt (Nat.cast_nonneg N)
          _ = (3 / 4) * ((3 / 4 : ℝ) ^ (passTime ⌊x⌋₊ N) * N) := by ring
          _ ≤ (3 / 4) * (x * (2 : ℝ) ^ L06) := mul_le_mul_of_nonneg_left hI (by norm_num)
      calc (3 / 4 : ℝ) ^ k * N * (2 : ℝ) ^ L06
          ≤ ((3 / 4) * (x * (2 : ℝ) ^ L06)) * (2 : ℝ) ^ L06 :=
            mul_le_mul_of_nonneg_right hstep hs_pos.le
        _ = (3 / 4) * x * ((2 : ℝ) ^ L06 * (2 : ℝ) ^ L06) := by ring
    have hss : (2 : ℝ) ^ L06 * (2 : ℝ) ^ L06 = (2 : ℝ) ^ (2 * L06) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    have h3k : (3 : ℝ) ^ k ≤ x ^ ((1 : ℝ) / 5) :=
      le_trans (pow_le_pow_right₀ (by norm_num) hkn0) (three_pow_nZero_le hx1)
    have hIV : Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3 : ℝ) ^ mZero x * x
        ≤ (3 / 4 : ℝ) * x * (2 : ℝ) ^ (2 * L06) + x ^ ((1 : ℝ) / 5) := by
      calc Real.exp (-Real.log x ^ (0.7 : ℝ)) * (4 / 3 : ℝ) ^ mZero x * x
          ≤ (3 / 4 : ℝ) ^ k * N * (2 : ℝ) ^ L06 + (3 : ℝ) ^ k := le_trans hEfloor hbhi_k
        _ ≤ (3 / 4) * x * ((2 : ℝ) ^ L06 * (2 : ℝ) ^ L06) + x ^ ((1 : ℝ) / 5) :=
            add_le_add hpkNrs h3k
        _ = (3 / 4) * x * (2 : ℝ) ^ (2 * L06) + x ^ ((1 : ℝ) / 5) := by rw [hss]
    exact absurd (lt_of_le_of_lt hIV (hsize x hxs)) (lt_irrefl _)
  calc ∑ n ∈ Iy x y, P.expect (Set.indicator {N | goodTuple x (n - mZero x)
          (valVec N (n - mZero x)) ∧ Eprime x E (syr^[n - mZero x] N) ∧
          passTime ⌊x⌋₊ N < n - mZero x} 1)
      ≤ ∑ _n ∈ Iy x y, (0 : ℝ) := Finset.sum_le_sum hzero
    _ = 0 := Finset.sum_const_zero
    _ ≤ 1 * (Real.log x) ^ (-(1 : ℝ)) :=
        mul_nonneg (by norm_num) (Real.rpow_nonneg hlogpos.le _)

/-- Sibling of `reverse_early_return_whp` with the `c`-slot pinned to `c_earlyReturn`; the
original delegates here.  Now delegates to `reverse_early_return_whp_atC` (big-C campaign,
step 2: `C := 1`). -/
theorem reverse_early_return_whp_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          ∑ n ∈ Iy x y, (logUnifOdd y (y ^ alpha)).expect
              (Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧ Eprime x E (syr^[n - mZero x] N) ∧
                passTime ⌊x⌋₊ N < n - mZero x} 1)
            ≤ C * (Real.log x) ^ (-c_earlyReturn) := by
  obtain ⟨x₀, h⟩ := reverse_early_return_whp_atC
  exact ⟨1, x₀, one_pos, h⟩

/-- **(5.17) reverse leg** — `steppedMid ≤ firstPassMid + O(log^{-c}x)`.  Proved down to ONE whp
core.  Pointwise, for each `n ∈ I_y` (so `1 ≤ m₀ ≤ n`), the stepped-back indicator is dominated by
three events:
`𝟙_{T_n} ≤ 𝟙_{S_n} + 𝟙_{¬good⁽ⁿ⁰⁾ ∧ T_x N = n} + 𝟙_{E′(Syr^{n−m₀}N) ∧ T_x N < n−m₀}`.
Indeed `N ∈ T_n` ⟹ `E′(Syr^{n−m₀}N)`, so `N` passes (`passes_of_eprime`); either `T_x N < n−m₀`
(the third, **early-return** set) or `n−m₀ ≤ T_x N`, in which case `passTime_stepback`+`E′` give
`T_x N = n` and `passLoc N ∈ E`, so `N ∈ S_n` when `good⁽ⁿ⁰⁾` else `N` is in the middle
(`¬good⁽ⁿ⁰⁾ ∧ T_x N = n`) set.  Summing:
* the **middle** sets collapse EXACTLY: `{T_x N = n}` are disjoint in `n`, so
  `∑_n 𝟙_{¬good⁽ⁿ⁰⁾ ∧ T_x N = n} ≤ 𝟙_{¬good⁽ⁿ⁰⁾}`, giving `≤ E[𝟙_{¬good}] ≤ C·log^{-c}`
  (`approx_good_tuple_whp` (5.12)) — no `I_y`-blow-up (`sum_expect_le_of_indicator_ge`);
* the **early-return** sets are the sole remaining whp hole (`reverse_early_return_whp`). -/
theorem reverse_early_return_whp :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          ∑ n ∈ Iy x y, (logUnifOdd y (y ^ alpha)).expect
              (Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧ Eprime x E (syr^[n - mZero x] N) ∧
                passTime ⌊x⌋₊ N < n - mZero x} 1)
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := reverse_early_return_whp_explicit
  exact ⟨c_earlyReturn, C, x₀, c_earlyReturn_pos, hC, h⟩

noncomputable def c_steppedMid : ℝ := min c_goodTupleDev c_earlyReturn

theorem c_steppedMid_pos : 0 < c_steppedMid :=
  lt_min c_goodTupleDev_pos c_earlyReturn_pos

/-- The (5.17) reverse-leg constant: `C_goodTupleDev + 1` (the early-return whp constant
is the numeral `1`) — big-C campaign, step 2. -/
noncomputable def C_steppedMid : ℝ := C_goodTupleDev + 1

theorem C_steppedMid_pos : 0 < C_steppedMid :=
  add_pos C_goodTupleDev_pos one_pos

/-- Sibling of `steppedMid_le_firstPassMid_add` with the `c`/`C` slots pinned at
(`c_steppedMid`, `C_steppedMid`) — the `_atC` form (big-C campaign, step 2), cutoff
existential. -/
theorem steppedMid_le_firstPassMid_add_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          steppedMid x E y
            ≤ firstPassMid x E y + C_steppedMid * (Real.log x) ^ (-c_steppedMid) := by
  obtain ⟨xg, hgood⟩ := approx_good_tuple_whp_atC
  obtain ⟨xe, hearly⟩ := reverse_early_return_whp_atC
  obtain ⟨xi, _hxi1, hint⟩ := mZero_le_of_mem_Iy
  set Cg : ℝ := C_goodTupleDev with hCgdef
  have hCg : 0 < Cg := C_goodTupleDev_pos
  set Ce : ℝ := (1 : ℝ) with hCedef
  have hCe : 0 < Ce := by rw [hCedef]; norm_num
  set cg : ℝ := c_goodTupleDev with hcgdef
  set ce : ℝ := c_earlyReturn with hcedef
  have hcg : 0 < cg := c_goodTupleDev_pos
  have hce : 0 < ce := c_earlyReturn_pos
  rw [show c_steppedMid = min cg ce from rfl, show C_steppedMid = Cg + Ce from rfl]
  refine ⟨max (max xg xe) (max xi (Real.exp 1)),
    fun x hx E hE y hy => ?_⟩
  have hxg : xg ≤ x := (le_max_left xg xe).trans ((le_max_left _ _).trans hx)
  have hxe : xe ≤ x := (le_max_right xg xe).trans ((le_max_left _ _).trans hx)
  have hxi : xi ≤ x := (le_max_left xi (Real.exp 1)).trans ((le_max_right _ _).trans hx)
  have hexp : Real.exp 1 ≤ x := (le_max_right xi (Real.exp 1)).trans ((le_max_right _ _).trans hx)
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hexp
  have hm : ∀ n ∈ Iy x y, 1 ≤ mZero x ∧ mZero x ≤ n := hint x hxi y hy
  classical
  unfold steppedMid firstPassMid
  set P := logUnifOdd y (y ^ alpha) with hPdef
  -- middle (¬good ∧ T_x=n) and early-return (E′ ∧ T_x<n−m₀) event families
  -- per-`n` ternary domination of the stepped-back indicator
  have hpern : ∀ n ∈ Iy x y,
      P.expect (Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧
          Eprime x E (syr^[n - mZero x] N)} 1)
        ≤ P.expect (Set.indicator {N | passTime ⌊x⌋₊ N = n ∧ passLoc ⌊x⌋₊ N ∈ E ∧
            goodTuple x (nZero x) (valVec N (nZero x))} 1)
          + (P.expect (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x)) ∧
              passTime ⌊x⌋₊ N = n} 1)
            + P.expect (Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧ Eprime x E (syr^[n - mZero x] N) ∧
              passTime ⌊x⌋₊ N < n - mZero x} 1)) := by
    intro n hn
    obtain ⟨hm1, hmn⟩ := hm n hn
    set Sn : Set ℕ := {N | passTime ⌊x⌋₊ N = n ∧ passLoc ⌊x⌋₊ N ∈ E ∧
      goodTuple x (nZero x) (valVec N (nZero x))} with hSn
    set Gn : Set ℕ := {N | ¬ goodTuple x (nZero x) (valVec N (nZero x)) ∧
      passTime ⌊x⌋₊ N = n} with hGn
    set Cn : Set ℕ := {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧
      Eprime x E (syr^[n - mZero x] N) ∧ passTime ⌊x⌋₊ N < n - mZero x} with hCn
    have hpw1 : ∀ N, Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧
          Eprime x E (syr^[n - mZero x] N)} (1 : ℕ → ℝ) N
        ≤ Set.indicator Sn 1 N + Set.indicator (Gn ∪ Cn) 1 N := by
      intro N
      have h1 : (0 : ℝ) ≤ Set.indicator Sn (1 : ℕ → ℝ) N :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) N
      have h2 : (0 : ℝ) ≤ Set.indicator (Gn ∪ Cn) (1 : ℕ → ℝ) N :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) N
      by_cases hT : N ∈ {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧
          Eprime x E (syr^[n - mZero x] N)}
      · rw [Set.indicator_of_mem hT, Pi.one_apply]
        obtain ⟨hGnm, hEp⟩ := hT
        by_cases hlt : passTime ⌊x⌋₊ N < n - mZero x
        · have hmemU : N ∈ Gn ∪ Cn := Or.inr ⟨hGnm, hEp, hlt⟩
          rw [Set.indicator_of_mem hmemU, Pi.one_apply]; linarith
        · push Not at hlt
          have hpass : passes ⌊x⌋₊ N := passes_of_eprime hm1 hEp
          have hPT : passTime ⌊x⌋₊ N = n := eprime_forces_passTime hpass hlt hmn hEp
          obtain ⟨_, _, hLM⟩ := passTime_stepback ⌊x⌋₊ N (n - mZero x) hpass hlt
          have hLE : passLoc ⌊x⌋₊ N ∈ E := by rw [← hLM]; exact hEp.2.2.1
          by_cases hG0 : goodTuple x (nZero x) (valVec N (nZero x))
          · have hmemS : N ∈ Sn := ⟨hPT, hLE, hG0⟩
            rw [Set.indicator_of_mem hmemS, Pi.one_apply]; linarith
          · have hmemU : N ∈ Gn ∪ Cn := Or.inl ⟨hG0, hPT⟩
            rw [Set.indicator_of_mem hmemU, Pi.one_apply]; linarith
      · rw [Set.indicator_of_notMem hT]; linarith
    have hpw2 : ∀ N, Set.indicator (Gn ∪ Cn) (1 : ℕ → ℝ) N
        ≤ Set.indicator Gn 1 N + Set.indicator Cn 1 N := by
      intro N
      have h1 : (0 : ℝ) ≤ Set.indicator Gn (1 : ℕ → ℝ) N :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) N
      have h2 : (0 : ℝ) ≤ Set.indicator Cn (1 : ℕ → ℝ) N :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) N
      by_cases hU : N ∈ Gn ∪ Cn
      · rw [Set.indicator_of_mem hU, Pi.one_apply]
        rcases hU with hG | hC
        · rw [Set.indicator_of_mem hG, Pi.one_apply]; linarith
        · rw [Set.indicator_of_mem hC, Pi.one_apply]; linarith
      · rw [Set.indicator_of_notMem hU]; linarith
    calc P.expect (Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧
            Eprime x E (syr^[n - mZero x] N)} 1)
        ≤ P.expect (Set.indicator Sn 1) + P.expect (Set.indicator (Gn ∪ Cn) 1) :=
          expect_le_add_of_indicator_le P _ Sn (Gn ∪ Cn) hpw1
      _ ≤ P.expect (Set.indicator Sn 1)
            + (P.expect (Set.indicator Gn 1) + P.expect (Set.indicator Cn 1)) := by
          gcongr
          exact expect_le_add_of_indicator_le P (Gn ∪ Cn) Gn Cn hpw2
  -- middle collapse: ∑_n E[𝟙_{¬good ∧ T_x=n}] ≤ E[𝟙_{¬good}]
  have hmid : ∑ n ∈ Iy x y, P.expect (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x)) ∧
        passTime ⌊x⌋₊ N = n} 1)
      ≤ P.expect (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1) := by
    have hptwise : ∀ N, ∑ n ∈ Iy x y, Set.indicator {N | ¬ goodTuple x (nZero x)
          (valVec N (nZero x)) ∧ passTime ⌊x⌋₊ N = n} (1 : ℕ → ℝ) N
        ≤ Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1 N := by
      intro N
      by_cases hNG : ¬ goodTuple x (nZero x) (valVec N (nZero x))
      · rw [Set.indicator_of_mem (show N ∈ {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))}
          from hNG), Pi.one_apply]
        calc ∑ n ∈ Iy x y, Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x)) ∧
                passTime ⌊x⌋₊ N = n} (1 : ℕ → ℝ) N
            ≤ ∑ n ∈ Iy x y, (if n = passTime ⌊x⌋₊ N then (1 : ℝ) else 0) := by
              refine Finset.sum_le_sum (fun n _ => ?_)
              by_cases hNn : N ∈ {N | ¬ goodTuple x (nZero x) (valVec N (nZero x)) ∧
                  passTime ⌊x⌋₊ N = n}
              · rw [Set.indicator_of_mem hNn, Pi.one_apply, if_pos hNn.2.symm]
              · rw [Set.indicator_of_notMem hNn]; split <;> norm_num
          _ ≤ 1 := by
              rw [Finset.sum_ite_eq' (Iy x y) (passTime ⌊x⌋₊ N) (fun _ => (1 : ℝ))]
              split <;> norm_num
      · rw [Set.indicator_of_notMem (show N ∉ {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))}
          from by simpa using hNG)]
        refine le_of_eq (Finset.sum_eq_zero (fun n _ => ?_))
        rw [Set.indicator_of_notMem (fun hmem => hNG hmem.1)]
    exact sum_expect_le_of_indicator_ge P (Iy x y)
      (fun n => {N | ¬ goodTuple x (nZero x) (valVec N (nZero x)) ∧ passTime ⌊x⌋₊ N = n})
      {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} hptwise
  -- early-return sum bound
  have hearlyx : ∑ n ∈ Iy x y, P.expect (Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧ Eprime x E (syr^[n - mZero x] N) ∧
        passTime ⌊x⌋₊ N < n - mZero x} 1) ≤ Ce * (Real.log x) ^ (-ce) := by
    rw [hPdef]; exact hearly x hxe E hE y hy
  have hgoodx : P.expect (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x))} 1)
      ≤ Cg * (Real.log x) ^ (-cg) := by rw [hPdef]; exact hgood x hxg y hy
  -- assemble
  calc ∑ n ∈ Iy x y, P.expect (Set.indicator {N | goodTuple x (n - mZero x)
          (valVec N (n - mZero x)) ∧ Eprime x E (syr^[n - mZero x] N)} 1)
      ≤ ∑ n ∈ Iy x y, (P.expect (Set.indicator {N | passTime ⌊x⌋₊ N = n ∧ passLoc ⌊x⌋₊ N ∈ E ∧
            goodTuple x (nZero x) (valVec N (nZero x))} 1)
          + (P.expect (Set.indicator {N | ¬ goodTuple x (nZero x) (valVec N (nZero x)) ∧
              passTime ⌊x⌋₊ N = n} 1)
            + P.expect (Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧ Eprime x E (syr^[n - mZero x] N) ∧
              passTime ⌊x⌋₊ N < n - mZero x} 1))) := Finset.sum_le_sum hpern
    _ = (∑ n ∈ Iy x y, P.expect (Set.indicator {N | passTime ⌊x⌋₊ N = n ∧ passLoc ⌊x⌋₊ N ∈ E ∧
            goodTuple x (nZero x) (valVec N (nZero x))} 1))
          + ((∑ n ∈ Iy x y, P.expect (Set.indicator {N | ¬ goodTuple x (nZero x)
              (valVec N (nZero x)) ∧ passTime ⌊x⌋₊ N = n} 1))
            + (∑ n ∈ Iy x y, P.expect (Set.indicator {N | goodTuple x (n - mZero x) (valVec N (n - mZero x)) ∧ Eprime x E (syr^[n - mZero x] N) ∧
              passTime ⌊x⌋₊ N < n - mZero x} 1))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ (∑ n ∈ Iy x y, P.expect (Set.indicator {N | passTime ⌊x⌋₊ N = n ∧ passLoc ⌊x⌋₊ N ∈ E ∧
            goodTuple x (nZero x) (valVec N (nZero x))} 1))
          + (Cg * (Real.log x) ^ (-cg) + Ce * (Real.log x) ^ (-ce)) :=
        add_le_add (le_refl _) (add_le_add (hmid.trans hgoodx) hearlyx)
    _ ≤ (∑ n ∈ Iy x y, P.expect (Set.indicator {N | passTime ⌊x⌋₊ N = n ∧ passLoc ⌊x⌋₊ N ∈ E ∧
            goodTuple x (nZero x) (valVec N (nZero x))} 1))
          + (Cg + Ce) * (Real.log x) ^ (-(min cg ce)) := by
        have hA : (Real.log x) ^ (-cg) ≤ (Real.log x) ^ (-(min cg ce)) :=
          Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_left cg ce))
        have hB : (Real.log x) ^ (-ce) ≤ (Real.log x) ^ (-(min cg ce)) :=
          Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_right cg ce))
        nlinarith [mul_le_mul_of_nonneg_left hA hCg.le, mul_le_mul_of_nonneg_left hB hCe.le]

/-- Sibling of `steppedMid_le_firstPassMid_add` with the `c`-slot pinned to `c_steppedMid`;
the original delegates here.  Now delegates to `steppedMid_le_firstPassMid_add_atC`
(big-C campaign, step 2: `C := C_steppedMid`). -/
theorem steppedMid_le_firstPassMid_add_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          steppedMid x E y ≤ firstPassMid x E y + C * (Real.log x) ^ (-c_steppedMid) := by
  obtain ⟨x₀, h⟩ := steppedMid_le_firstPassMid_add_atC
  exact ⟨C_steppedMid, x₀, C_steppedMid_pos, h⟩

/-- **(5.17) event reduction leg** — `|firstPassMid − steppedMid| ≤ O(log^{-c}x)`.  Assembled from the
two directional legs: the forward inclusion `firstPassMid ≤ steppedMid` (`firstPassMid_le_steppedMid`,
exact) and the reverse defect `steppedMid ≤ firstPassMid + O(log^{-c}x)`
(`steppedMid_le_firstPassMid_add`).  Since the forward gap is `0`, the absolute value collapses to the
reverse error. -/
theorem steppedMid_le_firstPassMid_add :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          steppedMid x E y ≤ firstPassMid x E y + C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := steppedMid_le_firstPassMid_add_explicit
  exact ⟨c_steppedMid, C, x₀, c_steppedMid_pos, hC, h⟩

/-- Sibling of `first_passage_stepback_reduce` with the `c`-slot pinned to `c_steppedMid`
(passthrough); the original delegates here. -/
theorem first_passage_stepback_reduce_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |firstPassMid x E y - steppedMid x E y|
            ≤ C_steppedMid * (Real.log x) ^ (-c_steppedMid) := by
  obtain ⟨x₁, _hx₁, hfwd⟩ := firstPassMid_le_steppedMid
  obtain ⟨x₂, hrev⟩ := steppedMid_le_firstPassMid_add_atC
  refine ⟨max x₁ x₂, fun x hx E hE y hy => ?_⟩
  have h1 := hfwd x (le_trans (le_max_left _ _) hx) E hE y hy
  have h2 := hrev x (le_trans (le_max_right _ _) hx) E hE y hy
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Sibling of `first_passage_stepback_reduce` with the `c`-slot pinned to `c_steppedMid`
(passthrough); the original delegates here.  Now delegates to
`first_passage_stepback_reduce_atC` (big-C campaign, step 2: `C := C_steppedMid`). -/
theorem first_passage_stepback_reduce_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |firstPassMid x E y - steppedMid x E y|
            ≤ C * (Real.log x) ^ (-c_steppedMid) := by
  obtain ⟨x₀, h⟩ := first_passage_stepback_reduce_atC
  exact ⟨C_steppedMid, x₀, C_steppedMid_pos, h⟩

/-- **(5.19) truncation error bound** — NOW TRIVIAL under RATIFY-C8-v2.  With the exact
divisibility-guarded `approxMainTerm`, `approxMainTerm = steppedMid` (`approxMainTerm_eq_steppedMid`),
so the reindex gap is identically `0`.  (Under the OLD unguarded ℕ-truncating pin this bound was
FALSE — the truncation over-counted by a super-polylog factor; that is exactly why the pin was
re-done.  See DIRECTION.md CURRENT DIRECTIVE 2026-07-15 and `tools/sandbox/tao_c8_truncation_probe.py`.)
Retained as a named lemma so `first_passage_truncation_reindex` keeps its interface. -/
theorem first_passage_stepback_reduce :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |firstPassMid x E y - steppedMid x E y|
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := first_passage_stepback_reduce_explicit
  exact ⟨c_steppedMid, C, x₀, c_steppedMid_pos, hC, h⟩

noncomputable def c_truncation : ℝ := 1

theorem c_truncation_pos : 0 < c_truncation := by norm_num [c_truncation]

/-- Sibling of `truncation_error_bound` with the `c`/`C` slots pinned at
(`c_truncation`, `1`) — the `_atC` form (big-C campaign, step 2). -/
theorem truncation_error_bound_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          approxMainTerm x E y - steppedMid x E y
            ≤ 1 * (Real.log x) ^ (-c_truncation) := by
  rw [show c_truncation = 1 from rfl]
  refine ⟨Real.exp 1, fun x hx E hE y hy => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp_iff.mpr (by norm_num)) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le one_pos hlog1
  have hone : ∀ b z : ℝ, 1 ≤ b → 0 ≤ z → (1 : ℝ) ≤ b ^ z := fun b z hb hz => by
    calc (1 : ℝ) = b ^ (0 : ℝ) := (Real.rpow_zero b).symm
      _ ≤ b ^ z := Real.rpow_le_rpow_of_exponent_le hb hz
  have haz : (0 : ℝ) ≤ alpha := by norm_num [alpha]
  have hy1 : (1 : ℝ) ≤ y ^ alpha := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hone _ alpha (hone x alpha hx1 haz) haz
    · exact hone _ alpha (hone x (alpha ^ 2) hx1 (by positivity)) haz
  rw [approxMainTerm_eq_steppedMid x E y hy1, sub_self, one_mul]
  exact Real.rpow_nonneg hlogpos.le _

/-- Sibling of `truncation_error_bound` with the `c`-slot pinned to `c_truncation`; the
original delegates here.  Now delegates to `truncation_error_bound_atC` (big-C campaign,
step 2: `C := 1`). -/
theorem truncation_error_bound_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          approxMainTerm x E y - steppedMid x E y
            ≤ C * (Real.log x) ^ (-c_truncation) := by
  obtain ⟨x₀, h⟩ := truncation_error_bound_atC
  exact ⟨1, x₀, one_pos, h⟩

theorem truncation_error_bound :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          approxMainTerm x E y - steppedMid x E y
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := truncation_error_bound_explicit
  exact ⟨c_truncation, C, x₀, c_truncation_pos, hC, h⟩

/-- Sibling of `first_passage_truncation_reindex` with the `c`-slot pinned to `c_truncation`
(passthrough); the original delegates here. -/
theorem first_passage_truncation_reindex_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |steppedMid x E y - approxMainTerm x E y|
            ≤ 1 * (Real.log x) ^ (-c_truncation) := by
  obtain ⟨x₀, herr⟩ := truncation_error_bound_atC
  refine ⟨max x₀ 1, fun x hx E hE y hy => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  -- `1 ≤ b^z` from `1 ≤ b`, `0 ≤ z` (via `b^0 = 1 ≤ b^z`)
  have hone : ∀ b z : ℝ, 1 ≤ b → 0 ≤ z → (1 : ℝ) ≤ b ^ z := fun b z hb hz => by
    calc (1 : ℝ) = b ^ (0 : ℝ) := (Real.rpow_zero b).symm
      _ ≤ b ^ z := Real.rpow_le_rpow_of_exponent_le hb hz
  have haz : (0 : ℝ) ≤ alpha := by norm_num [alpha]
  have hy1 : (1 : ℝ) ≤ y ^ alpha := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hone _ alpha (hone x alpha hx1 haz) haz
    · exact hone _ alpha (hone x (alpha ^ 2) hx1 (by positivity)) haz
  have hdom := steppedMid_le_approxMainTerm x E y hy1
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  exact herr x hx0 E hE y hy

/-- Sibling of `first_passage_truncation_reindex` with the `c`-slot pinned to `c_truncation`
(passthrough); the original delegates here.  Now delegates to
`first_passage_truncation_reindex_atC` (big-C campaign, step 2: `C := 1`). -/
theorem first_passage_truncation_reindex_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |steppedMid x E y - approxMainTerm x E y|
            ≤ C * (Real.log x) ^ (-c_truncation) := by
  obtain ⟨x₀, h⟩ := first_passage_truncation_reindex_atC
  exact ⟨1, x₀, one_pos, h⟩

/-- **(5.17) `B_{n,y}` event chain + (5.18) Lemma 2.1 affine reindexing** — the second,
route-decisive leg of (5.8).  For each `n ∈ I_y`, the event `{T_x(N_y)=n ∧ Pass∈E ∧ good}` equals
(step back `m₀` steps, (5.17)) `{Syr^{n−m₀}(N_y) ∈ E' ∧ good}`, whose probability the Lemma 2.1
affine bijection reindexes to `∑_{ā∈𝒜⁽ⁿ⁻ᵐ⁰⁾} ∑_{M∈E'} ℙ(Aff_ā(N_y)=M)` — the summand of
`approxMainTerm`.  Decomposed through the diagonal bridge `steppedMid`: the (5.17) event reduction
`first_passage_stepback_reduce` then the (5.18) truncation reindex `first_passage_truncation_reindex`
(APPROXIMATE — `Aff` uses truncating ℕ-division; truncation coincidences absorbed in `O(log^{-c}x)`,
module docstring).  The forward step-back inclusion `firstPass_event_stepback_subset` (EXACT) is the
proved core of the first leg. -/
theorem first_passage_truncation_reindex :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |steppedMid x E y - approxMainTerm x E y|
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := first_passage_truncation_reindex_explicit
  exact ⟨c_truncation, C, x₀, c_truncation_pos, hC, h⟩

noncomputable def c_affineReindex : ℝ := min c_steppedMid c_truncation

theorem c_affineReindex_pos : 0 < c_affineReindex :=
  lt_min c_steppedMid_pos c_truncation_pos

/-- The (5.17)+(5.18) affine-reindex constant: `C_steppedMid + 1` (big-C campaign,
step 2). -/
noncomputable def C_affineReindex : ℝ := C_steppedMid + 1

theorem C_affineReindex_pos : 0 < C_affineReindex :=
  add_pos C_steppedMid_pos one_pos

/-- Sibling of `first_passage_affine_reindex` with the `c`/`C` slots pinned at
(`c_affineReindex`, `C_affineReindex`) — the `_atC` form (big-C campaign, step 2),
cutoff existential. -/
theorem first_passage_affine_reindex_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |firstPassMid x E y - approxMainTerm x E y|
            ≤ C_affineReindex * (Real.log x) ^ (-c_affineReindex) := by
  obtain ⟨x₁, hsr⟩ := first_passage_stepback_reduce_atC
  obtain ⟨x₂, htr⟩ := first_passage_truncation_reindex_atC
  set C₁ : ℝ := C_steppedMid with hC1def
  have hC₁ : 0 < C₁ := C_steppedMid_pos
  set C₂ : ℝ := (1 : ℝ) with hC2def
  have hC₂ : 0 < C₂ := by rw [hC2def]; norm_num
  set c₁ : ℝ := c_steppedMid with hc1def
  set c₂ : ℝ := c_truncation with hc2def
  have hc₁ : 0 < c₁ := c_steppedMid_pos
  have hc₂ : 0 < c₂ := c_truncation_pos
  rw [show c_affineReindex = min c₁ c₂ from rfl,
    show C_affineReindex = C₁ + C₂ from rfl]
  refine ⟨max (max x₁ x₂) (Real.exp 1),
    fun x hx E hE y hy => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hA : (Real.log x) ^ (-c₁) ≤ (Real.log x) ^ (-(min c₁ c₂)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_left c₁ c₂))
  have hB : (Real.log x) ^ (-c₂) ≤ (Real.log x) ^ (-(min c₁ c₂)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_right c₁ c₂))
  calc |firstPassMid x E y - approxMainTerm x E y|
      ≤ |firstPassMid x E y - steppedMid x E y|
          + |steppedMid x E y - approxMainTerm x E y| := abs_sub_le _ _ _
    _ ≤ C₁ * (Real.log x) ^ (-c₁) + C₂ * (Real.log x) ^ (-c₂) :=
        add_le_add (hsr x hx1 E hE y hy) (htr x hx2 E hE y hy)
    _ ≤ C₁ * (Real.log x) ^ (-(min c₁ c₂)) + C₂ * (Real.log x) ^ (-(min c₁ c₂)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hC₁.le) (mul_le_mul_of_nonneg_left hB hC₂.le)
    _ = (C₁ + C₂) * (Real.log x) ^ (-(min c₁ c₂)) := by ring

/-- Sibling of `first_passage_affine_reindex` with the `c`-slot pinned to `c_affineReindex`;
the original delegates here.  Now delegates to `first_passage_affine_reindex_atC` (big-C
campaign, step 2: `C := C_affineReindex`). -/
theorem first_passage_affine_reindex_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |firstPassMid x E y - approxMainTerm x E y|
            ≤ C * (Real.log x) ^ (-c_affineReindex) := by
  obtain ⟨x₀, h⟩ := first_passage_affine_reindex_atC
  exact ⟨C_affineReindex, x₀, C_affineReindex_pos, h⟩

-- RATIFY-C8: paper Proposition 5.2 / (5.8), §5 pp.22–25.  Rendered against the numbered display;
-- the `O(log^{-c} x)` error is spelled as an explicit `∃ c C x₀` bound (design invariant D3).
/-- **Proposition 5.2** (approximate first-passage formula, paper (5.8)).  For every odd
`E ⊂ [1,x]` and `y ∈ {x^α, x^{α²}}`, the passage-location probability `ℙ(Pass_x(N_y) ∈ E)` agrees
with the affine main term `approxMainTerm` up to `O(log^{-c} x)`:
`ℙ(Pass_x(N_y) ∈ E) = ∑_{n∈I_y} ∑_{ā∈𝒜} ∑_{M∈E'} ℙ(Aff_ā(N_y) = M) + O(log^{-c} x)`.

This is node **C8**.  Proof: triangle inequality over the two owed legs
`first_passage_window_reduce` [(5.12)+(5.16) whp reduction to `firstPassMid`] and
`first_passage_affine_reindex` [(5.17) `B_{n,y}` chain + (5.18) affine reindexing to
`approxMainTerm`]. -/
theorem first_passage_affine_reindex :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |firstPassMid x E y - approxMainTerm x E y|
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := first_passage_affine_reindex_explicit
  exact ⟨c_affineReindex, C, x₀, c_affineReindex_pos, hC, h⟩

/-- Effective-constants campaign: the `c`-witness of `first_passage_approx` (C8). By the
step-1 branch trace this min collapses to the c7 value `c_valSumTail` (it contains it as a
sub-branch and every other leaf is `≥ 1/5`). -/
noncomputable def c_fpApprox : ℝ := min c_windowReduce c_affineReindex

theorem c_fpApprox_pos : 0 < c_fpApprox :=
  lt_min c_windowReduce_pos c_affineReindex_pos

/-- **The reified C8 constant**: `C_windowReduce + C_affineReindex` (big-C campaign,
step 2). -/
noncomputable def C_fpApprox : ℝ := C_windowReduce + C_affineReindex

theorem C_fpApprox_pos : 0 < C_fpApprox :=
  add_pos C_windowReduce_pos C_affineReindex_pos

/-- Sibling of the WATCHED `first_passage_approx` with the `c`/`C` slots pinned at
(`c_fpApprox`, `C_fpApprox`) — the `_atC` form (big-C campaign, step 2), cutoff
existential.  **This reifies C8.** -/
theorem first_passage_approx_atC :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
              - approxMainTerm x E y|
            ≤ C_fpApprox * (Real.log x) ^ (-c_fpApprox) := by
  obtain ⟨x₁, hwr⟩ := first_passage_window_reduce_atC
  obtain ⟨x₂, har⟩ := first_passage_affine_reindex_atC
  set C₁ : ℝ := C_windowReduce with hC1def
  set C₂ : ℝ := C_affineReindex with hC2def
  have hC₁ : 0 < C₁ := C_windowReduce_pos
  have hC₂ : 0 < C₂ := C_affineReindex_pos
  set c₁ : ℝ := c_windowReduce with hc1def
  set c₂ : ℝ := c_affineReindex with hc2def
  have hc₁ : 0 < c₁ := c_windowReduce_pos
  have hc₂ : 0 < c₂ := c_affineReindex_pos
  rw [show c_fpApprox = min c₁ c₂ from rfl, show C_fpApprox = C₁ + C₂ from rfl]
  refine ⟨max (max x₁ x₂) (Real.exp 1),
    fun x hx E hE y hy => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hA : (Real.log x) ^ (-c₁) ≤ (Real.log x) ^ (-(min c₁ c₂)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_left c₁ c₂))
  have hB : (Real.log x) ^ (-c₂) ≤ (Real.log x) ^ (-(min c₁ c₂)) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (min_le_right c₁ c₂))
  calc |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
          - approxMainTerm x E y|
      ≤ |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
            - firstPassMid x E y|
          + |firstPassMid x E y - approxMainTerm x E y| := abs_sub_le _ _ _
    _ ≤ C₁ * (Real.log x) ^ (-c₁) + C₂ * (Real.log x) ^ (-c₂) :=
        add_le_add (hwr x hx1 E hE y hy) (har x hx2 E hE y hy)
    _ ≤ C₁ * (Real.log x) ^ (-(min c₁ c₂)) + C₂ * (Real.log x) ^ (-(min c₁ c₂)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hC₁.le) (mul_le_mul_of_nonneg_left hB hC₂.le)
    _ = (C₁ + C₂) * (Real.log x) ^ (-(min c₁ c₂)) := by ring

/-- Sibling of the WATCHED `first_passage_approx` with the `c`-slot pinned to `c_fpApprox`;
the ratified original (byte-identical) delegates here.  Now delegates to
`first_passage_approx_atC` (big-C campaign, step 2: `C := C_fpApprox`). -/
theorem first_passage_approx_explicit :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
              - approxMainTerm x E y|
            ≤ C * (Real.log x) ^ (-c_fpApprox) := by
  obtain ⟨x₀, h⟩ := first_passage_approx_atC
  exact ⟨C_fpApprox, x₀, C_fpApprox_pos, h⟩

theorem first_passage_approx :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ E : Set ℕ, (∀ M ∈ E, M % 2 = 1 ∧ 1 ≤ M ∧ (M : ℝ) ≤ x) →
        ∀ y ∈ ({x ^ alpha, x ^ alpha ^ 2} : Set ℝ),
          |(logUnifOdd y (y ^ alpha)).expect (Set.indicator {N | passLoc ⌊x⌋₊ N ∈ E} 1)
              - approxMainTerm x E y|
            ≤ C * (Real.log x) ^ (-c) := by
  obtain ⟨C, x₀, hC, h⟩ := first_passage_approx_explicit
  exact ⟨c_fpApprox, C, x₀, c_fpApprox_pos, hC, h⟩

end TaoCollatz
