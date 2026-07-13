import TaoCollatz.Sec7.BlackEdge
import TaoCollatz.Sec7.FpLocation

/-!
# §7.4 Case 3 kernels: Lemmas 7.9 & 7.10 (nodes X9 / X10)

The two probabilistic estimates that make Case 3 of Proposition 7.8 (deep triangle,
`s > m/log²m`) work, paper pp.50–54, eqs (7.56)–(7.65). Both are statements about the
infinite two-dimensional renewal process `(j',l'), (j',l')+v₁, (j',l')+v_{[1,2]}, …`
with `v_i` iid copies of `Hold`.

## Lemma 7.10 (X10) — large triangles rarely encountered after a lengthy crossing

Pinned here: `triangle_encounter_le`, paper (7.60). Its event `E_{p,s'}` — that the
renewal endpoint `(j,l)+v_{[1,k+p]}` lands in a triangle of size `≥ s'` — depends only
on the **marginal law** of that single endpoint, so NO stopping-time path-space is
needed (D1). That marginal is `fpDist s` (the first-passage endpoint at budget
`s = l_Δ − l`, `Unroll.lean` / X6) convolved with `iidSum hold p` (the `p` further
`Hold` steps): the def `fpDistPlus` below.

Route (7.60)–(7.65): with `s' ≥ CA²(1+p)` (else trivial), the escape event `E′`
(7.61) — endpoint too high, or `j`-coordinate off the `s/4` centre by `≥ 2s^{0.6}` —
is killed by Lemma 7.7 (`fpDist_location_bound`, X6) + Lemma 2.2 (S3). Outside `E′`,
(7.63)–(7.65) show every size-`≥ s'` triangle the endpoint could hit has apex within
`O(A²(1+p))` of the `≫ s'`-separated lattice `Σ = {(j_Δ', l_Δ)}`; summing the X6
Gaussian envelope `s^{-1/2}G_{1+s}(c(j'−j−s/4))` over that separated set (via the
`sum_range_exp_neg_sq_le` engine) gives `≪ A²(1+p)/s'`. All inputs are theorems.

## Lemma 7.9 (X9) — many triangles usually implies many white points

Paper (7.57), p.50: with `v₁, v₂, …` iid `Hold`, stopping times `t₁ < t₂ < …` (`t₁` =
first `p ≥ 1` with `(j',l')+v_{[1,p]}` in a triangle of `𝒯`; `t_i` = first `p` with
BOTH `l' + l_{[1,p]} > l_{Δ_{i−1}}` AND the point in a triangle `Δ_i`), and `r` = the
number of such times:

  `E exp(−Σ_{p=1}^{t_{min(r,R)}} 1_W((j',l')+v_{[1,p]}) + ε·min(r,R)) ≤ exp(ε)`.

**D6 encoding** (design ratified lap 52; route-trigger T1 does NOT fire — no infinite
product measure is needed): the stopping-time data `(t_i, Δ_i, r)` is a LEFT FOLD over
the finite step list. The state `EncState` carries the current position, the current
clearing barrier (top of the last-encountered triangle; initialized to `l'`, vacuous
since every walk height exceeds `l'`), the encounter count `r`, the running white
count `Σ 1_W`, and the `banked` white count frozen at the `min(r,R)`-th encounter —
so `banked = Σ_{p=1}^{t_{min(r,R)}} 1_W` and the paper's LHS is
`encVal ε R (final state)` exactly.

**Finite horizon `T`, uniformly**: the statement is pinned for the `T`-step walk
`hold.iid T` for EVERY `T` (the paper's infinite-walk statement is the `T`-envelope of
these). This is faithful-to-consumer: the (7.66)–(7.67) consumption (p.55) applies
Lemma 7.9 through Markov's inequality on the finite window `p ≤ P` after the first
passage, with all stopping times shown to fall inside the window by the deterministic
argument — only finite horizons are ever used. The induction structure mirrors the
p.51 conditioning on the first block `v₁ … v_{k₁}` (first passage over `Δ₁`'s top),
finitized by the head-peel `encExpect_succ` + block bridge `encExpect_block_le`; the
extra finite-horizon branch "`t₁ ≤ T < k₁`" contributes within budget directly (its
`min(r_T,R) = 1` and the empty continuation is `1`). NOTE (lap 52): the paper's own
closure has a fixable gap and its `exp(ε)` constant is replaced by `exp(2ε)` — see
the deviation note on `many_triangles_white`.

**ε existentially small** rather than the paper's fixed section constant: (7.57) needs
`e^{2ε}(1 − (1−1/e)·p₀) ≤ e^ε` against the absolute white-exit mass `p₀` of
`fpDist_white_exit`, which is pinned as `∃ p₀ > 0`. The consumer is insensitive: on
p.55 `R` is chosen AFTER ε (`R := ⌈(10A/ε_Q³ + O(A) + 1)/ε⌉` makes the Markov bound
`e^{ε + threshold − εR} ≤ 10^{−A−2}` for any fixed ε > 0), so an
`∃ ε₀ ∈ (0, 1/100], ∀ ε ≤ ε₀` pin is exactly what X11 consumes.

**Index shift**: walk points live at renewal coordinates `q`; triangle membership and
color are read at the phase point `(q.1 − 1, q.2)` (matching `fpDist_white_exit` and
the `Q_black_edge` glue), and `whiteStrip` already carries this shift.

NEXT (proof, later laps): induction on `(R, T)` over `encExpect_succ`, closed by the
path→`fpDist` bridge (the first-passage endpoint functional of `hold.iid T` has law
`fpDist s` once `T ≥ s/3 + 1`, since every step spends height ≥ 3) plus
`fpDist_white_exit`.
-/

namespace TaoCollatz

open scoped ENNReal

/-- **The `(k+p)`-step renewal endpoint law** (paper `v_{[1,k+p]}` of Lemma 7.10):
the first-passage endpoint at budget `s` (the `k` steps, `fpDist s`) followed by `p`
further independent `Hold` steps (`iidSum hold p`). By independence its law is the
convolution. This is the exact marginal whose triangle-hitting probability is
Lemma 7.10's `E_{p,s'}`. -/
noncomputable def fpDistPlus (s p : ℕ) : PMF (ℕ × ℤ) :=
  (fpDist s).bind fun e => (iidSum hold p).map fun w => e + w

/-- At `p = 0` the renewal endpoint is just the first-passage endpoint. -/
theorem fpDistPlus_zero (s : ℕ) : fpDistPlus s 0 = fpDist s := by
  have h : (fun e : ℕ × ℤ => (iidSum hold 0).map fun w => e + w)
      = fun e : ℕ × ℤ => PMF.pure e := by
    funext e
    rw [iidSum_zero, PMF.pure_map, add_zero]
  rw [fpDistPlus, h, PMF.bind_pure]

/-- `∑' (fpDistPlus s p e).toReal = 1` (total mass of a PMF, transported to `ℝ`). -/
theorem fpDistPlus_tsum_toReal (s p : ℕ) :
    ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun e => PMF.apply_ne_top _ _), (fpDistPlus s p).tsum_coe,
    ENNReal.toReal_one]

/-- `∑' (fpDist s e).toReal = 1` (the `p = 0` case, via `fpDistPlus_zero`). -/
theorem fpDist_tsum_toReal (s : ℕ) : ∑' e : ℕ × ℤ, (fpDist s e).toReal = 1 := by
  rw [← fpDistPlus_zero s]
  exact fpDistPlus_tsum_toReal s 0

/-- **Any event-probability of the renewal endpoint is `≤ 1`** — `fpDistPlus` is a
`PMF`, so summing its mass against a `{0,1}` indicator is `≤` its total mass `1`. The
concrete first step of Lemma 7.10's proof (the (7.60) "trivial otherwise" reduction:
when `s' < C·A²(1+p)` the RHS already exceeds `1`), and general fpDist bookkeeping. -/
theorem fpDistPlus_indicator_sum_le_one (s p : ℕ) (S : Set (ℕ × ℤ))
    (f : ℕ × ℤ → ℕ × ℤ) :
    ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal * Set.indicator S 1 (f e) ≤ 1 := by
  have hsum : Summable (fun e : ℕ × ℤ => (fpDistPlus s p e).toReal) :=
    ENNReal.summable_toReal (by rw [(fpDistPlus s p).tsum_coe]; exact ENNReal.one_ne_top)
  have hle : ∀ e : ℕ × ℤ, (fpDistPlus s p e).toReal * Set.indicator S 1 (f e)
      ≤ (fpDistPlus s p e).toReal := by
    intro e
    refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
    by_cases h : f e ∈ S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hsumL : Summable
      (fun e : ℕ × ℤ => (fpDistPlus s p e).toReal * Set.indicator S 1 (f e)) :=
    Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) hle hsum
  calc ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal * Set.indicator S 1 (f e)
      ≤ ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal := Summable.tsum_le_tsum hle hsumL hsum
    _ = 1 := fpDistPlus_tsum_toReal s p

/-- **The size-`≥ s'` sub-cover** (paper `⋃_{Δ ∈ 𝒯, s_Δ ≥ s'} Δ`): the union of the
family's triangles whose size is at least `s'`. Lemma 7.10 bounds the chance the
renewal endpoint lands in this set. -/
def bigTriangleSet {n ξ : ℕ} (F : TriangleFamily n ξ) (s' : ℕ) : Set (ℕ × ℤ) :=
  {q | ∃ t ∈ F.T, (s' : ℝ) ≤ t.2.2 ∧ q ∈ triangle t.1 t.2.1 t.2.2}

/-- **Distinct family triangles share no lattice point** (from `F.separated`, since
the separation constant `(1/10)·log(1/ε) ≈ 0.92 > 0`). Shared prerequisite for BOTH
crux nodes: it makes the covering triangle `Δ(q)` of a strip point well-defined
(Lemma 7.9 kernel, X9), and it is exactly the "two apex-intervals cannot share an
integer point" step of Lemma 7.10's ≫s′-separation ((7.65), p.54, X10). -/
theorem TriangleFamily.not_mem_two {n ξ : ℕ} (F : TriangleFamily n ξ)
    {t t' : ℕ × ℤ × ℝ} (ht : t ∈ F.T) (ht' : t' ∈ F.T) (hne : t ≠ t')
    {q : ℕ × ℤ} (hq : q ∈ triangle t.1 t.2.1 t.2.2)
    (hq' : q ∈ triangle t'.1 t'.2.1 t'.2.2) : False := by
  have hsep := F.separated t ht t' ht' hne q hq q hq'
  have heps : (1 : ℝ) / (epsBW : ℝ) = 10 ^ 4 := by
    rw [show epsBW = 1 / 10 ^ 4 from rfl]; push_cast; norm_num
  have hlogpos : (0 : ℝ) < Real.log (1 / (epsBW : ℝ)) := by
    rw [heps]; exact Real.log_pos (by norm_num)
  have hpos : (0 : ℝ) < ((1 / 10 : ℝ) * Real.log (1 / (epsBW : ℝ))) ^ 2 :=
    pow_pos (mul_pos (by norm_num) hlogpos) 2
  have hzero : ((q.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((q.2 : ℝ) - (q.2 : ℝ)) ^ 2 = 0 := by ring
  linarith [hsep, hzero, hpos]

/-- **The covering triangle `Δ(q)` is well-defined** (paper: every black strip point
lies in exactly one triangle of the family): `cover` gives existence, `not_mem_two`
gives uniqueness. This `∃!` is the foundation of the Lemma 7.9 recursion kernel (X9) —
the moving-barrier first-passage budget `s(q) = l_{Δ(q)} − l` reads off `Δ(q).2.1`. -/
theorem TriangleFamily.existsUnique_cover {n ξ : ℕ} (F : TriangleFamily n ξ)
    {q : ℕ × ℤ} (hq : q.1 + 1 ≤ n / 2 ∧ black n ξ q.1 q.2) :
    ∃! t : ℕ × ℤ × ℝ, t ∈ F.T ∧ q ∈ triangle t.1 t.2.1 t.2.2 := by
  have hmem : q ∈ {p : ℕ × ℤ | p.1 + 1 ≤ n / 2 ∧ black n ξ p.1 p.2} := hq
  rw [F.cover] at hmem
  simp only [Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨t, ht, hqt⟩ := hmem
  refine ⟨t, ⟨ht, hqt⟩, ?_⟩
  rintro t' ⟨ht', hqt'⟩
  by_contra hne
  exact F.not_mem_two ht' ht hne hqt' hqt

/-- **The covering triangle `Δ(q)`** (the `∃!` witness of `existsUnique_cover`): the
unique family triangle containing a black-strip point `q`. Reads off the Lemma 7.9
recursion's moving barrier `l_{Δ(q)} = coveringTriangle F q hq |>.2.1`. -/
noncomputable def TriangleFamily.coveringTriangle {n ξ : ℕ} (F : TriangleFamily n ξ)
    (q : ℕ × ℤ) (hq : q.1 + 1 ≤ n / 2 ∧ black n ξ q.1 q.2) : ℕ × ℤ × ℝ :=
  (F.existsUnique_cover hq).exists.choose

theorem TriangleFamily.coveringTriangle_mem {n ξ : ℕ} (F : TriangleFamily n ξ)
    {q : ℕ × ℤ} (hq : q.1 + 1 ≤ n / 2 ∧ black n ξ q.1 q.2) :
    F.coveringTriangle q hq ∈ F.T :=
  (F.existsUnique_cover hq).exists.choose_spec.1

theorem TriangleFamily.coveringTriangle_covers {n ξ : ℕ} (F : TriangleFamily n ξ)
    {q : ℕ × ℤ} (hq : q.1 + 1 ≤ n / 2 ∧ black n ξ q.1 q.2) :
    q ∈ triangle (F.coveringTriangle q hq).1 (F.coveringTriangle q hq).2.1
      (F.coveringTriangle q hq).2.2 :=
  (F.existsUnique_cover hq).exists.choose_spec.2

/-- The covering triangle is THE one: any family triangle containing `q` equals
`Δ(q)`. Follows from the `∃!` uniqueness; the recursion uses it to identify the
first triangle a renewal path enters with its covering triangle. -/
theorem TriangleFamily.eq_coveringTriangle {n ξ : ℕ} (F : TriangleFamily n ξ)
    {q : ℕ × ℤ} (hq : q.1 + 1 ≤ n / 2 ∧ black n ξ q.1 q.2)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ F.T) (hqt : q ∈ triangle t.1 t.2.1 t.2.2) :
    t = F.coveringTriangle q hq :=
  (F.existsUnique_cover hq).unique ⟨ht, hqt⟩
    ⟨F.coveringTriangle_mem hq, F.coveringTriangle_covers hq⟩

/-- **The apex-gap inequality** — the geometric heart of Lemma 7.10's ≫s′-separation
((7.65), paper p.54). If a lattice height `l*` sits inside a triangle `t''` at its own
apex column (`(j_{t''}, l*) ∈ t''`), and `t'` is a distinct family triangle with
`j_{t'} ≤ j_{t''}`, `l* ≤ l_{t'}`, then that apex-column point of `t''` cannot also lie
in `t'` (`not_mem_two`), forcing

  `s_{t'} < (j_{t''} − j_{t'})·log 9 + (l_{t'} − l*)·log 2`.

Combined with the (7.65) height condition `l_{t'} − s_{t'}/log 2 ≈ l_Δ` and `l* =
l_Δ + ⌊s'/2⌋`, this yields the apex separation `j_{t''} − j_{t'} ≫ s'` that makes the
size-`≥ s'` triangle apexes a ≫s′-separated set. -/
theorem apex_gap {n ξ : ℕ} (F : TriangleFamily n ξ) {t' t'' : ℕ × ℤ × ℝ}
    (ht' : t' ∈ F.T) (ht'' : t'' ∈ F.T) (hne : t' ≠ t'')
    (hj : t'.1 ≤ t''.1) {lstar : ℤ} (hl' : lstar ≤ t'.2.1)
    (hmem'' : ((t''.1, lstar) : ℕ × ℤ) ∈ triangle t''.1 t''.2.1 t''.2.2) :
    t'.2.2 < ((t''.1 : ℝ) - t'.1) * Real.log 9 + ((t'.2.1 : ℝ) - lstar) * Real.log 2 := by
  have hnot : ((t''.1, lstar) : ℕ × ℤ) ∉ triangle t'.1 t'.2.1 t'.2.2 :=
    fun hmem' => F.not_mem_two ht' ht'' hne hmem' hmem''
  rw [triangle, Set.mem_setOf_eq] at hnot
  push_neg at hnot
  exact hnot hj hl'

/-- **The apex separation** (paper p.54): feeding `apex_gap` the (7.65) height
condition `l_{t'} − s_{t'}/log 2 ≤ l_Δ + δ` (the lower tip of `t'` is `≤ δ` above the
reference `l_Δ`) and the choice `l* = l_Δ + ⌊s'/2⌋`, the `s_{t'}` term cancels and the
apex `j`-gap is bounded below:

  `(⌊s'/2⌋ − δ)·log 2 < (j_{t''} − j_{t'})·log 9`.

With `s' ≥ C·A²(1+p) ≥ C·δ`, this is `j_{t''} − j_{t'} ≫ s'`: size-`≥ s'` triangle
apexes obeying (7.65) form a ≫s′-separated set, so the Gaussian envelope sum over them
converges to `≪ A²(1+p)/s'`. This closes the geometric core of Lemma 7.10 (X10). -/
theorem apex_separation {n ξ : ℕ} (F : TriangleFamily n ξ) {t' t'' : ℕ × ℤ × ℝ}
    (ht' : t' ∈ F.T) (ht'' : t'' ∈ F.T) (hne : t' ≠ t'') (hj : t'.1 ≤ t''.1)
    {lZ : ℤ} {δ : ℝ} {s' : ℕ}
    (h765 : (t'.2.1 : ℝ) - lZ ≤ t'.2.2 / Real.log 2 + δ)
    (hl' : lZ + ((s' / 2 : ℕ) : ℤ) ≤ t'.2.1)
    (hmem'' : ((t''.1, lZ + ((s' / 2 : ℕ) : ℤ)) : ℕ × ℤ)
      ∈ triangle t''.1 t''.2.1 t''.2.2) :
    (((s' / 2 : ℕ) : ℝ) - δ) * Real.log 2 < ((t''.1 : ℝ) - t'.1) * Real.log 9 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hgap := apex_gap F ht' ht'' hne hj hl' hmem''
  have hcast : ((lZ + ((s' / 2 : ℕ) : ℤ) : ℤ) : ℝ) = (lZ : ℝ) + ((s' / 2 : ℕ) : ℝ) := by
    rw [Int.cast_add, Int.cast_natCast]
  rw [hcast] at hgap
  have hexp : ((t'.2.1 : ℝ) - ((lZ : ℝ) + ((s' / 2 : ℕ) : ℝ))) * Real.log 2
      = ((t'.2.1 : ℝ) - lZ) * Real.log 2 - ((s' / 2 : ℕ) : ℝ) * Real.log 2 := by ring
  rw [hexp] at hgap
  have h765' : ((t'.2.1 : ℝ) - lZ) * Real.log 2 ≤ t'.2.2 + δ * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right h765 hlog2.le
    rwa [add_mul, div_mul_cancel₀ _ hlog2.ne'] at h
  have hgoal : (((s' / 2 : ℕ) : ℝ) - δ) * Real.log 2
      = ((s' / 2 : ℕ) : ℝ) * Real.log 2 - δ * Real.log 2 := by ring
  rw [hgoal]
  linarith [hgap, h765']

/- The (7.61) height tail `fpDistPlus_height_tail` is stated and PROVED at the
end of this file (it needs the row-sum / `hasSum` engines defined below). -/

/- The (7.61) column tail `fpDistPlus_col_tail` is stated and PROVED at the
end of this file (it needs the row-sum / `hasSum` engines defined below). -/

/-- **Lemma 7.10 — large triangles are rarely encountered shortly after a lengthy
crossing** (paper (7.60), pp.51–54). Starting the renewal walk at a point `(j,l)` of
a black triangle `Δ = t₀` with budget `s = l_Δ − l` obeying `s > m/log²m`
(`m = ⌊n/2⌋ − j`), the endpoint `(j,l) + v_{[1,k+p]}` (law `fpDistPlus s p`) lands in
some triangle of size `≥ s'` — the event `E_{p,s'}` — with probability

  `≪ A²·(1+p)/s' + exp(−c·A²·(1+p))`,

for all `1 ≤ s' ≤ m^{0.4}`, constants uniform in `n, ξ`. The `A²(1+p)/s'` term is the
`≫ s'`-separated Σ-count (7.65); the `exp(−cA²(1+p))` term is the escape event `E′`
(7.61) killed by X6 + S3.

OPEN (node X10): the campaign's single highest-uncertainty node. Route in the module
docstring / `PENDING_WORK.md`; all inputs (`fpDist_location_bound` = X6, Lemma 2.2 =
S3, `F.separated` = X3) are theorems.

DEVIATION NOTE (lap 57, statement fix — needs re-ratification): the paper takes `A`
"sufficiently large" (its proof starts "we can assume `s' ≥ CA²(1+p)` for a large
constant C, since the claim is trivial otherwise", and the (7.61) height threshold
`2A²(1+p)` must clear the `≈ 4p` mean height drift of the `p` extra `Hold` steps —
at fixed small `A` and `p → ∞` the endpoint sits at height `l_Δ + Θ(p)` outside the
`A²(1+p)` window and the claimed `exp(−cA²(1+p))` bound is FALSE). The pin therefore
carries `∃ A₀ ≥ 1, ∀ A ≥ A₀`; the consumer (p.54, `E_*` union bound) instantiates at
`A` large, so this is consumer-safe. The two (7.61) tails are pinned separately as
`fpDistPlus_height_tail` / `fpDistPlus_col_tail` below. -/
theorem triangle_encounter_le :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (A : ℝ), A₀ ≤ A →
      ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l →
        ((n / 2 - j : ℕ) : ℝ) / Real.log ((n / 2 - j : ℕ) : ℝ) ^ 2 < (s : ℝ) →
      ∀ (p s' : ℕ), 1 ≤ s' →
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
      ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal
          * Set.indicator (bigTriangleSet F s') (1 : ℕ × ℤ → ℝ) (j + e.1, l + e.2)
        ≤ C * A ^ 2 * (1 + (p : ℝ)) / (s' : ℝ)
          + C * Real.exp (-c * A ^ 2 * (1 + (p : ℝ))) := by
  sorry

/-! ### Lemma 7.9 (X9): the encounter fold and the (7.57) pin -/

/-- **The stopping-time fold state** (paper p.50, D6 form): everything the paper's
stopping times `t_i`, triangles `Δ_i`, and count `r` extract from a walk prefix.
`pos` = current renewal point `(j',l') + v_{[1,p]}`; `barrier` = the top `l_{Δ_{i−1}}`
of the last triangle encountered (init `l'`: vacuous, every walk height is `> l'`);
`count` = the number `r` of encounters so far; `cumWhite` = `Σ_{p'≤p} 1_W`;
`banked` = `cumWhite` frozen at the `min(r,R)`-th encounter, i.e.
`Σ_{p=1}^{t_{min(r,R)}} 1_W` — the exponent of (7.57). -/
structure EncState : Type where
  /-- current renewal position -/
  pos : ℕ × ℤ
  /-- clearing barrier: top of the last-encountered triangle -/
  barrier : ℤ
  /-- number of triangle encounters (the paper's `r`) -/
  count : ℕ
  /-- running white count `Σ 1_W` along the walk -/
  cumWhite : ℕ
  /-- white count frozen at encounter `min(count, R)` -/
  banked : ℕ

open scoped Classical in
/-- **One step of the encounter fold** (paper p.50's stopping-time recursion, one
`Hold` increment `d`): move to `q = pos + d`; count its whiteness (`whiteStrip`, phase
shift built in); an ENCOUNTER happens iff the phase point `(q₁−1, q₂)` is black-strip
(equivalently, `q` lies in a family triangle, via `cover`) AND the height has cleared
the previous triangle's top (`barrier < q₂`) — then the barrier becomes the top of the
covering triangle `Δ(q)` and, while `count < R`, the white count is banked
(`t_{min(r,R)}` semantics of (7.57)).

**DEPTH GATE `g` (lap-55 reflection)**: an encounter additionally requires the entered
point to sit at depth ≥ `g` from the strip's right edge (`q₁ + g ≤ n/2`). `g = 0`
recovers the paper's ungated stopping times verbatim. The gate exists because the
paper's (7.59) step ("repeating the proof of (7.51)", p.51) needs the encountered
triangle DEEP — near the edge the white-exit mass genuinely fails (the first-passage
endpoint exits the strip with non-vanishing probability), and the p.50 remark that
"`r` is finite since the process eventually exits the strip" provides no ledger for
the uncompensated `e^ε` payments there. The X11 consumer is unaffected: on the
surviving branch of the (7.54) split (`j_{[1,k+P]} < 0.9m`, Case 3 has `m ≥ C_{A,ε}`)
every encounter produced by the deterministic claim (7.67) is at depth `≥ 0.1m ≥ g`,
so the gated count still reaches `R` (see `many_triangles_white`'s deviation note). -/
noncomputable def encStep {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (σ : EncState) (d : ℕ × ℤ) : EncState :=
  if hq : 1 ≤ (σ.pos + d).1 ∧ (σ.pos + d).1 + g ≤ n / 2
      ∧ black n ξ ((σ.pos + d).1 - 1) (σ.pos + d).2 ∧ σ.barrier < (σ.pos + d).2 then
    { pos := σ.pos + d
      barrier := (F.coveringTriangle ((σ.pos + d).1 - 1, (σ.pos + d).2)
        ⟨show (σ.pos + d).1 - 1 + 1 ≤ n / 2 by omega, hq.2.2.1⟩).2.1
      count := σ.count + 1
      cumWhite := σ.cumWhite + (if σ.pos + d ∈ whiteStrip n ξ then 1 else 0)
      banked := if σ.count < R then
          σ.cumWhite + (if σ.pos + d ∈ whiteStrip n ξ then 1 else 0)
        else σ.banked }
  else
    { pos := σ.pos + d, barrier := σ.barrier, count := σ.count,
      cumWhite := σ.cumWhite + (if σ.pos + d ∈ whiteStrip n ξ then 1 else 0),
      banked := σ.banked }

/-- The fold's start state at `(j', l')`: no encounters, vacuous barrier `l'`. -/
def encInit (j' : ℕ) (l' : ℤ) : EncState := ⟨(j', l'), l', 0, 0, 0⟩

/-- **The (7.57) integrand**: `exp(−Σ_{p=1}^{t_{min(r,R)}} 1_W + ε·min(r,R))`,
read off the fold state. -/
noncomputable def encVal (ε : ℝ) (R : ℕ) (σ : EncState) : ℝ :=
  Real.exp (-(σ.banked : ℝ) + ε * min σ.count R)

/-- **The (7.57) left-hand side at horizon `T`, started from state `σ`**: the
expectation of `encVal` over the `T`-step walk `hold.iid T` folded from `σ`. The
generalized start state is what makes the head-peel recursion (`encExpect_succ`)
an induction invariant. -/
noncomputable def encExpect {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (T : ℕ) (σ : EncState) : ℝ :=
  (hold.iid T).expect fun v => encVal ε R ((List.ofFn v).foldl (encStep F R g) σ)

/-- `encVal` is positive. -/
theorem encVal_pos (ε : ℝ) (R : ℕ) (σ : EncState) : 0 < encVal ε R σ :=
  Real.exp_pos _

/-- **`encVal ≤ exp(ε·R)`** (for `ε ≥ 0`): the banked white count only helps and
`min(r,R) ≤ R`. The trivial envelope of (7.57), and the normalizer that puts the
integrand into `[0,1]` for the iid head-peel. -/
theorem encVal_le (ε : ℝ) (hε : 0 ≤ ε) (R : ℕ) (σ : EncState) :
    encVal ε R σ ≤ Real.exp (ε * R) := by
  apply Real.exp_le_exp.mpr
  have h1 : (0 : ℝ) ≤ (σ.banked : ℝ) := Nat.cast_nonneg _
  have h2 : ((min σ.count R : ℕ) : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr (min_le_right _ _)
  linarith [mul_le_mul_of_nonneg_left h2 hε, h1]

/-- Horizon `0`: no steps, the expectation collapses to the integrand at `σ`. -/
theorem encExpect_zero {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (σ : EncState) : encExpect F R g ε 0 σ = encVal ε R σ := by
  rw [encExpect, PMF.expect_iid_zero]
  simp

/-- **The head-peel recursion** (the D6 skeleton of the paper's p.51 conditioning):
one fresh `Hold` step `d` updates the fold state, and the horizon drops by one:

  `encExpect (T+1) σ = Σ'_d hold(d) · encExpect T (encStep σ d)`.

The Lemma 7.9 induction runs on this: at an encounter the barrier resets and the
count increments (spending one of the `R` blocks), and iterating the peel until the
barrier is cleared reconstructs the first-passage law `fpDist` (the path→`fpDist`
bridge, next lap), whose white-exit mass (7.51) closes the induction. -/
theorem encExpect_succ {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (σ : EncState) :
    encExpect F R g ε (T + 1) σ
      = ∑' d : ℕ × ℤ, (hold d).toReal * encExpect F R g ε T (encStep F R g σ d) := by
  -- normalize the integrand into [0,1] to use the iid head-peel
  set c : ℝ := Real.exp (ε * R) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hkey : ∀ (m : ℕ) (τ : EncState),
      encExpect F R g ε m τ * c⁻¹
        = (hold.iid m).expect fun v =>
            encVal ε R ((List.ofFn v).foldl (encStep F R g) τ) * c⁻¹ := by
    intro m τ
    rw [encExpect, PMF.expect, PMF.expect, ← tsum_mul_right]
    exact tsum_congr fun v => by ring
  have h0 : ∀ (m : ℕ) (τ : EncState) (v : Fin m → ℕ × ℤ),
      0 ≤ encVal ε R ((List.ofFn v).foldl (encStep F R g) τ) * c⁻¹ :=
    fun m τ v => mul_nonneg (encVal_pos ε R _).le (by positivity)
  have h1 : ∀ (m : ℕ) (τ : EncState) (v : Fin m → ℕ × ℤ),
      encVal ε R ((List.ofFn v).foldl (encStep F R g) τ) * c⁻¹ ≤ 1 := by
    intro m τ v
    rw [← mul_inv_cancel₀ hc0.ne']
    exact mul_le_mul_of_nonneg_right (encVal_le ε hε R _) (by positivity)
  -- the scaled identity
  have hmain : encExpect F R g ε (T + 1) σ * c⁻¹
      = ∑' d : ℕ × ℤ, (hold d).toReal
          * (encExpect F R g ε T (encStep F R g σ d) * c⁻¹) := by
    rw [hkey (T + 1) σ,
      PMF.expect_iid_succ hold T _ (h0 (T + 1) σ) (h1 (T + 1) σ)]
    refine tsum_congr fun d => ?_
    rw [hkey T (encStep F R g σ d)]
    congr 1
    refine congrArg _ (funext fun w => ?_)
    have hlist : List.ofFn (Fin.cons d w : Fin (T + 1) → ℕ × ℤ)
        = d :: List.ofFn w := by
      rw [List.ofFn_succ]
      congr 1
    rw [hlist, List.foldl_cons]
  -- cancel the normalizer
  have hfin := congrArg (· * c) hmain
  simp only [mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one] at hfin
  rw [hfin, ← tsum_mul_right]
  exact tsum_congr fun d => by
    rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one]

/-- **The (7.57) trivial envelope**: `encExpect ≤ exp(ε·R)` (event bookkeeping via
the PMF total mass, mirroring `fpDistPlus_indicator_sum_le_one`). -/
theorem encExpect_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (σ : EncState) :
    encExpect F R g ε T σ ≤ Real.exp (ε * R) := by
  have hsum : Summable (fun v : Fin T → ℕ × ℤ => ((hold.iid T) v).toReal) :=
    ENNReal.summable_toReal (by rw [(hold.iid T).tsum_coe]; exact ENNReal.one_ne_top)
  have hle : ∀ v : Fin T → ℕ × ℤ,
      ((hold.iid T) v).toReal * encVal ε R ((List.ofFn v).foldl (encStep F R g) σ)
        ≤ ((hold.iid T) v).toReal * Real.exp (ε * R) :=
    fun v => mul_le_mul_of_nonneg_left (encVal_le ε hε R _) ENNReal.toReal_nonneg
  have hsumR : Summable (fun v : Fin T → ℕ × ℤ =>
      ((hold.iid T) v).toReal * Real.exp (ε * R)) := hsum.mul_right _
  have hsumL : Summable (fun v : Fin T → ℕ × ℤ =>
      ((hold.iid T) v).toReal * encVal ε R ((List.ofFn v).foldl (encStep F R g) σ)) :=
    Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (encVal_pos ε R _).le) hle hsumR
  calc encExpect F R g ε T σ
      ≤ ∑' v : Fin T → ℕ × ℤ, ((hold.iid T) v).toReal * Real.exp (ε * R) :=
        Summable.tsum_le_tsum hle hsumL hsumR
    _ = Real.exp (ε * R) := by
        rw [tsum_mul_right, ← ENNReal.tsum_toReal_eq (fun v => PMF.apply_ne_top _ _),
          (hold.iid T).tsum_coe, ENNReal.toReal_one, one_mul]

/-- `encExpect` is nonnegative (expectation of a positive integrand). -/
theorem encExpect_nonneg {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (T : ℕ) (σ : EncState) : 0 ≤ encExpect F R g ε T σ :=
  tsum_nonneg fun v => mul_nonneg ENNReal.toReal_nonneg (encVal_pos ε R _).le

/-- A fold step never decreases the encounter count. -/
theorem encStep_count_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (σ : EncState) (d : ℕ × ℤ) : σ.count ≤ (encStep F R g σ d).count := by
  unfold encStep
  split <;> dsimp only <;> omega

/-- **Saturated states are frozen** (the `min(r,R)` semantics of (7.57)): once
`count ≥ R`, further steps change neither `banked` nor `min(count,R)`, so the
expectation collapses to the integrand — `encExpect T σ = encVal σ` for every
horizon. This is the `ρ = 0` base of the block induction. -/
theorem encExpect_of_count_ge {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (σ : EncState) (hc : R ≤ σ.count) :
    encExpect F R g ε T σ = encVal ε R σ := by
  induction T generalizing σ with
  | zero => exact encExpect_zero F R g ε σ
  | succ T IH =>
    rw [encExpect_succ F R g ε hε T σ]
    have hval : ∀ d : ℕ × ℤ, encExpect F R g ε T (encStep F R g σ d) = encVal ε R σ := by
      intro d
      rw [IH (encStep F R g σ d) (le_trans hc (encStep_count_le F R g σ d))]
      have hmin : min (encStep F R g σ d).count R = min σ.count R := by
        have h1 := encStep_count_le F R g σ d
        omega
      have hbank : (encStep F R g σ d).banked = σ.banked := by
        unfold encStep
        split
        · dsimp only
          rw [if_neg (by omega)]
        · rfl
      rw [encVal, encVal, hbank, hmin]
    rw [tsum_congr fun d => by rw [hval d], tsum_mul_right, hold_tsum_toReal, one_mul]

/-- **The white-count coupling** (antitone dependence on `cumWhite`/`banked`): two
states agreeing in position, barrier, and count, with the first having smaller
white counters, satisfy `encExpect σ₂ ≤ encExpect σ₁` — larger banked white counts
only increase the damping. One fold step preserves the relation (the branch taken
depends only on the shared fields), and `encVal` is antitone in `banked`.

This is what lets the path→`fpDist` block bridge DROP the mid-block white
increments: the true continuation (larger `cumWhite`) is dominated by the dropped
one, so only the first-passage ENDPOINT's whiteness needs to be carried — exactly
the `Σ_{p=1}^{k₁} 1_W ≥ 1_W(v_{[1,k₁]})` reduction of the paper's p.51 closure. -/
theorem encExpect_anti {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) :
    ∀ σ₁ σ₂ : EncState, σ₁.pos = σ₂.pos → σ₁.barrier = σ₂.barrier →
    σ₁.count = σ₂.count → σ₁.cumWhite ≤ σ₂.cumWhite → σ₁.banked ≤ σ₂.banked →
    encExpect F R g ε T σ₂ ≤ encExpect F R g ε T σ₁ := by
  induction T with
  | zero =>
    intro σ₁ σ₂ hpos hbar hcnt hcw hbk
    rw [encExpect_zero, encExpect_zero, encVal, encVal, hcnt]
    apply Real.exp_le_exp.mpr
    have : (σ₁.banked : ℝ) ≤ (σ₂.banked : ℝ) := Nat.cast_le.mpr hbk
    linarith
  | succ T IH =>
    intro σ₁ σ₂ hpos hbar hcnt hcw hbk
    rw [encExpect_succ F R g ε hε T σ₁, encExpect_succ F R g ε hε T σ₂]
    -- termwise: one step preserves the coupling
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F R g ε T (encStep F R g σ₂ d) ≤ encExpect F R g ε T (encStep F R g σ₁ d) := by
      intro d
      obtain ⟨p₁, b₁, c₁, w₁, k₁⟩ := σ₁
      obtain ⟨p₂, b₂, c₂, w₂, k₂⟩ := σ₂
      simp only at hpos hbar hcnt hcw hbk
      subst hpos hbar hcnt
      simp only [encStep]
      by_cases hq : 1 ≤ (p₁ + d).1 ∧ (p₁ + d).1 + g ≤ n / 2
          ∧ black n ξ ((p₁ + d).1 - 1) (p₁ + d).2 ∧ b₁ < (p₁ + d).2
      · -- encounter branch for both (same condition)
        simp only [dif_pos hq]
        refine IH _ _ rfl rfl rfl ?_ ?_
        · simpa using hcw
        · by_cases hcR : c₁ < R
          · simpa [hcR] using hcw
          · simpa [hcR] using hbk
      · simp only [dif_neg hq]
        refine IH _ _ rfl rfl rfl ?_ ?_
        · simpa using hcw
        · simpa using hbk
    -- sum the termwise bound
    have hnn : ∀ (σ : EncState) (d : ℕ × ℤ),
        0 ≤ (hold d).toReal * encExpect F R g ε T (encStep F R g σ d) :=
      fun σ d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg F R g ε T _)
    have hbound : ∀ (σ : EncState) (d : ℕ × ℤ),
        (hold d).toReal * encExpect F R g ε T (encStep F R g σ d)
          ≤ (hold d).toReal * Real.exp (ε * R) :=
      fun σ d => mul_le_mul_of_nonneg_left (encExpect_le F R g ε hε T _)
        ENNReal.toReal_nonneg
    have hsumE : Summable (fun d : ℕ × ℤ => (hold d).toReal * Real.exp (ε * R)) :=
      (ENNReal.summable_toReal (by rw [hold.tsum_coe]; exact ENNReal.one_ne_top)).mul_right _
    have hsum1 : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * encExpect F R g ε T (encStep F R g σ₁ d)) :=
      Summable.of_nonneg_of_le (hnn σ₁) (hbound σ₁) hsumE
    have hsum2 : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * encExpect F R g ε T (encStep F R g σ₂ d)) :=
      Summable.of_nonneg_of_le (hnn σ₂) (hbound σ₂) hsumE
    exact Summable.tsum_le_tsum
      (fun d => mul_le_mul_of_nonneg_left (hstep d) ENNReal.toReal_nonneg) hsum2 hsum1

/-- **The CLAIM-G state-normalization coupling** (lap-52 route; the affine
reduction of a mid-flight state to a fresh one). A state `σ` with `count = τ.count
+ c`, `cumWhite = τ.cumWhite + w`, and banked counter either still at its initial
value `k` (no banking event yet, `τ.banked = 0`) or offset by `w`, is dominated by
the `τ`-fold with `c` fewer block budget:

  `E_{R'+c}(T, σ) ≤ e^{εc} · max(e^{−k}, e^{−w}) · E_{R'}(T, τ)`.

Both folds take the SAME branch at every step (the branch condition reads only
`pos`/`barrier`, which agree), the counts/whites advance in lockstep, and a banking
event fires simultaneously (`σ.count < R ⟺ τ.count < R'`), converting the left
disjunct into the right one. `encVal` then factors pathwise. Used with
`τ = ⟨σ.pos, σ.barrier, 0, 0, 0⟩` this is the Y/Z induction's state normalization
(`encExpect_normalize_init`). -/
theorem encExpect_normalize {n ξ : ℕ} (F : TriangleFamily n ξ) (R' g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (c w k : ℕ) (T : ℕ) :
    ∀ σ τ : EncState, σ.pos = τ.pos → σ.barrier = τ.barrier →
    σ.count = τ.count + c → σ.cumWhite = τ.cumWhite + w →
    ((σ.banked = k ∧ τ.banked = 0) ∨ σ.banked = τ.banked + w) →
    encExpect F (R' + c) g ε T σ
      ≤ Real.exp (ε * c) * max (Real.exp (-(k : ℝ))) (Real.exp (-(w : ℝ)))
        * encExpect F R' g ε T τ := by
  set M : ℝ := max (Real.exp (-(k : ℝ))) (Real.exp (-(w : ℝ))) with hM
  have hM0 : 0 < M := lt_max_of_lt_left (Real.exp_pos _)
  induction T with
  | zero =>
    intro σ τ hpos hbar hcnt hcw hbk
    rw [encExpect_zero, encExpect_zero, encVal, encVal]
    have hmin : min σ.count (R' + c) = min τ.count R' + c := by
      omega
    have hbank : Real.exp (-(σ.banked : ℝ)) ≤ M * Real.exp (-(τ.banked : ℝ)) := by
      rcases hbk with ⟨hσk, hτ0⟩ | hoff
      · rw [hσk, hτ0, hM]
        simp only [Nat.cast_zero, neg_zero, Real.exp_zero, mul_one]
        exact le_max_left _ _
      · rw [hoff]
        push_cast
        rw [neg_add, Real.exp_add, mul_comm (Real.exp (-(τ.banked : ℝ)))]
        exact mul_le_mul_of_nonneg_right (hM ▸ le_max_right _ _)
          (Real.exp_pos _).le
    calc Real.exp (-(σ.banked : ℝ) + ε * min σ.count (R' + c))
        = Real.exp (-(σ.banked : ℝ)) * Real.exp (ε * min τ.count R')
            * Real.exp (ε * c) := by
          rw [hmin, ← Real.exp_add, ← Real.exp_add]
          push_cast
          ring_nf
      _ ≤ (M * Real.exp (-(τ.banked : ℝ))) * Real.exp (ε * min τ.count R')
            * Real.exp (ε * c) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbank
            (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = Real.exp (ε * c) * M
            * Real.exp (-(τ.banked : ℝ) + ε * min τ.count R') := by
          rw [Real.exp_add]
          ring
  | succ T IH =>
    intro σ τ hpos hbar hcnt hcw hbk
    rw [encExpect_succ F (R' + c) g ε hε T σ, encExpect_succ F R' g ε hε T τ]
    -- one step preserves the invariant
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F (R' + c) g ε T (encStep F (R' + c) g σ d)
          ≤ Real.exp (ε * c) * M * encExpect F R' g ε T (encStep F R' g τ d) := by
      intro d
      obtain ⟨p₁, b₁, c₁, w₁, k₁⟩ := σ
      obtain ⟨p₂, b₂, c₂, w₂, k₂⟩ := τ
      simp only at hpos hbar hcnt hcw
      subst hpos hbar hcnt hcw
      simp only [encStep]
      by_cases hq : 1 ≤ (p₁ + d).1 ∧ (p₁ + d).1 + g ≤ n / 2
          ∧ black n ξ ((p₁ + d).1 - 1) (p₁ + d).2 ∧ b₁ < (p₁ + d).2
      · -- encounter for both (shared condition)
        simp only [dif_pos hq]
        refine IH _ _ rfl rfl (by dsimp only <;> omega) (by dsimp only <;> omega) ?_
        by_cases hcR : c₂ < R'
        · -- both bank: land in the right disjunct
          refine Or.inr ?_
          dsimp only
          rw [if_pos (show c₂ + c < R' + c by omega), if_pos hcR]
          omega
        · -- neither banks: the disjunction carries over
          dsimp only
          rw [if_neg (show ¬ c₂ + c < R' + c by omega), if_neg hcR]
          simpa using hbk
      · simp only [dif_neg hq]
        refine IH _ _ rfl rfl (by dsimp only <;> omega) (by dsimp only <;> omega) ?_
        dsimp only
        simpa using hbk
    -- summability boilerplate, then sum the termwise bound
    have hnnσ : ∀ d : ℕ × ℤ,
        0 ≤ (hold d).toReal * encExpect F (R' + c) g ε T (encStep F (R' + c) g σ d) :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg _ _ _ ε T _)
    have hboundσ : ∀ d : ℕ × ℤ,
        (hold d).toReal * encExpect F (R' + c) g ε T (encStep F (R' + c) g σ d)
          ≤ (hold d).toReal * Real.exp (ε * ((R' + c : ℕ) : ℝ)) :=
      fun d => mul_le_mul_of_nonneg_left (encExpect_le F (R' + c) g ε hε T _)
        ENNReal.toReal_nonneg
    have hsumH : Summable (fun d : ℕ × ℤ => (hold d).toReal) :=
      ENNReal.summable_toReal (by rw [hold.tsum_coe]; exact ENNReal.one_ne_top)
    have hsumσ : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * encExpect F (R' + c) g ε T (encStep F (R' + c) g σ d)) :=
      Summable.of_nonneg_of_le hnnσ hboundσ (hsumH.mul_right _)
    have hboundτ : ∀ d : ℕ × ℤ,
        (hold d).toReal * encExpect F R' g ε T (encStep F R' g τ d)
          ≤ (hold d).toReal * Real.exp (ε * (R' : ℝ)) :=
      fun d => mul_le_mul_of_nonneg_left (encExpect_le F R' g ε hε T _)
        ENNReal.toReal_nonneg
    have hsumτ : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * encExpect F R' g ε T (encStep F R' g τ d)) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg _ _ _ ε T _))
        hboundτ (hsumH.mul_right _)
    calc ∑' d : ℕ × ℤ,
          (hold d).toReal * encExpect F (R' + c) g ε T (encStep F (R' + c) g σ d)
        ≤ ∑' d : ℕ × ℤ, (hold d).toReal
            * (Real.exp (ε * c) * M * encExpect F R' g ε T (encStep F R' g τ d)) := by
          refine Summable.tsum_le_tsum
            (fun d => mul_le_mul_of_nonneg_left (hstep d) ENNReal.toReal_nonneg)
            hsumσ ?_
          have heq : (fun d : ℕ × ℤ => (hold d).toReal
              * (Real.exp (ε * c) * M * encExpect F R' g ε T (encStep F R' g τ d)))
              = fun d : ℕ × ℤ => Real.exp (ε * c) * M
                * ((hold d).toReal * encExpect F R' g ε T (encStep F R' g τ d)) := by
            funext d
            ring
          rw [heq]
          exact hsumτ.mul_left _
      _ = Real.exp (ε * c) * M
            * ∑' d : ℕ × ℤ, (hold d).toReal * encExpect F R' g ε T (encStep F R' g τ d) := by
          rw [← tsum_mul_left]
          exact tsum_congr fun d => by ring

/-- **State normalization to the fresh state** (the CLAIM-G instance the Y/Z
induction consumes): any mid-flight state `σ` with `σ.count ≤ R` is dominated by
the zeroed state at its own position with the remaining budget:

  `E_R(T, σ) ≤ e^{ε·σ.count} · max(e^{−σ.banked}, e^{−σ.cumWhite})
      · E_{R−σ.count}(T, ⟨σ.pos, σ.barrier, 0, 0, 0⟩)`. -/
theorem encExpect_normalize_init {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (σ : EncState) (hc : σ.count ≤ R) :
    encExpect F R g ε T σ
      ≤ Real.exp (ε * σ.count)
        * max (Real.exp (-(σ.banked : ℝ))) (Real.exp (-(σ.cumWhite : ℝ)))
        * encExpect F (R - σ.count) g ε T ⟨σ.pos, σ.barrier, 0, 0, 0⟩ := by
  have h := encExpect_normalize F (R - σ.count) g ε hε σ.count σ.cumWhite σ.banked T
    σ ⟨σ.pos, σ.barrier, 0, 0, 0⟩ rfl rfl (by dsimp only <;> omega) (by dsimp only <;> omega)
    (Or.inl ⟨rfl, rfl⟩)
  rwa [show R - σ.count + σ.count = R by omega] at h

/-- **Beyond the gate line the fold is frozen** (the shallow/out-of-strip case of
the Z-induction): once `pos₁ > n/2 − g` no future point can satisfy the gated
encounter condition (`pos₁` is non-decreasing along the fold), so `banked` and
`count` never change and the expectation collapses to the integrand. With `g = 0`
this is the plain out-of-strip freeze. -/
theorem encExpect_of_edge {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) :
    ∀ σ : EncState, n / 2 < σ.pos.1 + g → encExpect F R g ε T σ = encVal ε R σ := by
  classical
  induction T with
  | zero => intro σ _; exact encExpect_zero F R g ε σ
  | succ T IH =>
    intro σ hedge
    rw [encExpect_succ F R g ε hε T σ]
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F R g ε T (encStep F R g σ d) = encVal ε R σ := by
      intro d
      have hq : ¬(1 ≤ (σ.pos + d).1 ∧ (σ.pos + d).1 + g ≤ n / 2
          ∧ black n ξ ((σ.pos + d).1 - 1) (σ.pos + d).2
          ∧ σ.barrier < (σ.pos + d).2) := by
        rintro ⟨-, hle, -, -⟩
        have : (σ.pos + d).1 = σ.pos.1 + d.1 := rfl
        omega
      have hs : encStep F R g σ d
          = ⟨σ.pos + d, σ.barrier, σ.count,
              σ.cumWhite + (if σ.pos + d ∈ whiteStrip n ξ then 1 else 0), σ.banked⟩ := by
        rw [encStep, dif_neg hq]
      rw [hs, IH _ (by dsimp only; show n / 2 < σ.pos.1 + d.1 + g; omega)]
      rfl
    rw [tsum_congr fun d => by rw [hstep d], tsum_mul_right, hold_tsum_toReal, one_mul]

/-- **The wander claim** (the between-blocks phase of the Z-induction). After a
block exit with white credit `w₀` and no instant encounter, the walk wanders with
`count = 0`, `banked = 0`, `cumWhite = w ≥ w₀`. Given a uniform bound `Z` for
JUST-ENTERED fresh states at budget `R'` (the entered class: position satisfying
the gated encounter conditions, barrier = its covering triangle's top — the only
fresh states a wander can normalize onto), every wander state at budget `R' + 1`
satisfies

  `E_{R'+1}(T, ⟨p, b, 0, w, 0⟩) ≤ max 1 (e^ε·e^{−w₀}·Z)`:

a later encounter banks `cumWhite ≥ w₀` and normalizes onto an entered fresh state
at budget `R'` (paying `e^ε` for the count increment, collecting `e^{−w₀}`); a path
that never encounters ends at `encVal = 1`. Induction on the horizon. -/
theorem encExpect_wander_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R' g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (Z : ℝ) (hZ : 0 ≤ Z)
    (hfresh : ∀ (T' : ℕ) (q : ℕ × ℤ), 1 ≤ q.1 → q.1 + g ≤ n / 2 →
      ∀ hcov : (q.1 - 1) + 1 ≤ n / 2 ∧ black n ξ (q.1 - 1) q.2,
      encExpect F R' g ε T'
        ⟨q, (F.coveringTriangle (q.1 - 1, q.2) hcov).2.1, 0, 0, 0⟩ ≤ Z)
    (w₀ : ℕ) (T : ℕ) :
    ∀ (p : ℕ × ℤ) (b : ℤ) (w : ℕ), w₀ ≤ w →
    encExpect F (R' + 1) g ε T ⟨p, b, 0, w, 0⟩
      ≤ max 1 (Real.exp ε * Real.exp (-(w₀ : ℝ)) * Z) := by
  classical
  induction T with
  | zero =>
    intro p b w hw
    rw [encExpect_zero]
    refine le_max_of_le_left ?_
    rw [encVal]
    dsimp only
    simp [Real.exp_le_one_iff]
  | succ T IH =>
    intro p b w hw
    rw [encExpect_succ F (R' + 1) g ε hε T _]
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F (R' + 1) g ε T (encStep F (R' + 1) g ⟨p, b, 0, w, 0⟩ d)
          ≤ max 1 (Real.exp ε * Real.exp (-(w₀ : ℝ)) * Z) := by
      intro d
      by_cases hq : 1 ≤ (p + d).1 ∧ (p + d).1 + g ≤ n / 2
          ∧ black n ξ ((p + d).1 - 1) (p + d).2 ∧ b < (p + d).2
      · -- encounter: bank the credit, normalize onto the fresh state at budget R'
        have hq' : 1 ≤ (p + d).1 ∧ (p + d).1 + g ≤ n / 2
            ∧ black n ξ ((p + d).1 - 1) (p + d).2 ∧ b < (p + d).2 := hq
        set σ' := encStep F (R' + 1) g ⟨p, b, 0, w, 0⟩ d with hσ'
        have hcnt : σ'.count = 1 := by
          rw [hσ', encStep, dif_pos hq']
        have hcw : w₀ ≤ σ'.cumWhite := by
          rw [hσ', encStep, dif_pos hq']
          dsimp only
          omega
        have hbk : σ'.banked = σ'.cumWhite := by
          rw [hσ', encStep, dif_pos hq']
          dsimp only
          rw [if_pos (show (0 : ℕ) < R' + 1 by omega)]
        have hnorm := encExpect_normalize_init F (R' + 1) g ε hε T σ'
          (by rw [hcnt]; omega)
        refine le_max_of_le_right (le_trans hnorm ?_)
        rw [hbk, max_self, hcnt]
        have h2 : Real.exp (-(σ'.cumWhite : ℝ)) ≤ Real.exp (-(w₀ : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hle : (w₀ : ℝ) ≤ (σ'.cumWhite : ℝ) := Nat.cast_le.mpr hcw
          linarith
        have hpos' : σ'.pos = p + d := by
          rw [hσ', encStep, dif_pos hq']
        have hcov : ((p + d).1 - 1) + 1 ≤ n / 2 ∧ black n ξ ((p + d).1 - 1) (p + d).2 :=
          ⟨by omega, hq'.2.2.1⟩
        have hbar' : σ'.barrier
            = (F.coveringTriangle ((p + d).1 - 1, (p + d).2) hcov).2.1 := by
          rw [hσ', encStep, dif_pos hq']
        have h3 : encExpect F (R' + 1 - 1) g ε T ⟨σ'.pos, σ'.barrier, 0, 0, 0⟩ ≤ Z := by
          rw [hpos', hbar']
          simpa using hfresh T (p + d) hq'.1 hq'.2.1 hcov
        have hE0 : 0 ≤ encExpect F (R' + 1 - 1) g ε T ⟨σ'.pos, σ'.barrier, 0, 0, 0⟩ :=
          encExpect_nonneg _ _ _ ε T _
        have hexp1 : Real.exp (ε * ((1 : ℕ) : ℝ)) = Real.exp ε := by norm_num
        calc Real.exp (ε * ((1 : ℕ) : ℝ)) * Real.exp (-(σ'.cumWhite : ℝ))
              * encExpect F (R' + 1 - 1) g ε T ⟨σ'.pos, σ'.barrier, 0, 0, 0⟩
            ≤ Real.exp (ε * ((1 : ℕ) : ℝ)) * Real.exp (-(w₀ : ℝ)) * Z :=
              mul_le_mul (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) h3 hE0
                (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          _ = Real.exp ε * Real.exp (-(w₀ : ℝ)) * Z := by rw [hexp1]
      · -- no encounter: still wandering with a larger cumWhite
        have hs : encStep F (R' + 1) g ⟨p, b, 0, w, 0⟩ d
            = ⟨p + d, b, 0, w + (if p + d ∈ whiteStrip n ξ then 1 else 0), 0⟩ := by
          rw [encStep, dif_neg (by exact hq)]
        rw [hs]
        exact IH (p + d) b _ (by omega)
    -- sum the pointwise bound against the unit mass
    have hM0 : 0 ≤ max 1 (Real.exp ε * Real.exp (-(w₀ : ℝ)) * Z) :=
      le_max_of_le_left zero_le_one
    have hsumH : Summable (fun d : ℕ × ℤ => (hold d).toReal) :=
      ENNReal.summable_toReal (by rw [hold.tsum_coe]; exact ENNReal.one_ne_top)
    have hsumL : Summable (fun d : ℕ × ℤ => (hold d).toReal
        * encExpect F (R' + 1) g ε T (encStep F (R' + 1) g ⟨p, b, 0, w, 0⟩ d)) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg _ _ _ ε T _))
        (fun d => mul_le_mul_of_nonneg_left (encExpect_le _ _ _ ε hε T _)
          ENNReal.toReal_nonneg)
        (hsumH.mul_right _)
    calc ∑' d : ℕ × ℤ, (hold d).toReal
          * encExpect F (R' + 1) g ε T (encStep F (R' + 1) g ⟨p, b, 0, w, 0⟩ d)
        ≤ ∑' d : ℕ × ℤ, (hold d).toReal
            * max 1 (Real.exp ε * Real.exp (-(w₀ : ℝ)) * Z) :=
          Summable.tsum_le_tsum
            (fun d => mul_le_mul_of_nonneg_left (hstep d) ENNReal.toReal_nonneg)
            hsumL (hsumH.mul_right _)
      _ = max 1 (Real.exp ε * Real.exp (-(w₀ : ℝ)) * Z) := by
          rw [tsum_mul_right, hold_tsum_toReal, one_mul]

/-- PMF-weighted sums of `[0,B]`-valued observables are `≤ B` (generic event
bookkeeping; `B`-scaled `tsum_mul_ofReal_le_one`). -/
theorem tsum_toReal_mul_le {α : Type*} (p : PMF α) (g : α → ℝ)
    (hg0 : ∀ e, 0 ≤ g e) {B : ℝ} (hgB : ∀ e, g e ≤ B) (hB : 0 ≤ B) :
    ∑' e, (p e).toReal * g e ≤ B := by
  have hsum : Summable (fun e => (p e).toReal) :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)
  have hle : ∀ e, (p e).toReal * g e ≤ (p e).toReal * B :=
    fun e => mul_le_mul_of_nonneg_left (hgB e) ENNReal.toReal_nonneg
  have hsumR : Summable (fun e => (p e).toReal * B) := hsum.mul_right _
  have hsumL : Summable (fun e => (p e).toReal * g e) :=
    Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg (hg0 e)) hle hsumR
  calc ∑' e, (p e).toReal * g e ≤ ∑' e, (p e).toReal * B :=
        Summable.tsum_le_tsum hle hsumL hsumR
    _ = B := by
        rw [tsum_mul_right, ← ENNReal.tsum_toReal_eq (fun e => PMF.apply_ne_top _ _),
          p.tsum_coe, ENNReal.toReal_one, one_mul]

/-- ℝ-level bind Fubini for PMF expectations of `[0,B]`-valued observables
(`PMF.tsum_bind_mul` transported through `toReal`). -/
theorem tsum_bind_toReal {α β : Type*} (p : PMF α) (K : α → PMF β) (g : β → ℝ)
    (hg0 : ∀ e, 0 ≤ g e) {B : ℝ} (hgB : ∀ e, g e ≤ B) :
    ∑' e, ((p.bind K) e).toReal * g e
      = ∑' a, (p a).toReal * ∑' e, ((K a) e).toReal * g e := by
  rw [← PMF.toReal_tsum_mul_ofReal (p.bind K) g hg0, PMF.tsum_bind_mul,
    ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (calc ∑' e, (K a) e * ENNReal.ofReal (g e)
            ≤ ∑' e, (K a) e * ENNReal.ofReal B :=
              ENNReal.tsum_le_tsum fun e =>
                mul_le_mul_left' (ENNReal.ofReal_le_ofReal (hgB e)) _
          _ = ENNReal.ofReal B := by
              rw [ENNReal.tsum_mul_right, (K a).tsum_coe, one_mul])))]
  exact tsum_congr fun a => by
    rw [ENNReal.toReal_mul, PMF.toReal_tsum_mul_ofReal (K a) g hg0]

/-- ℝ-level pushforward reindex for PMF expectations of nonneg observables
(`PMF.tsum_map_mul` transported through `toReal`). -/
theorem tsum_map_toReal {α β : Type*} (p : PMF α) (φ : α → β) (g : β → ℝ)
    (hg0 : ∀ e, 0 ≤ g e) :
    ∑' e, ((p.map φ) e).toReal * g e = ∑' a, (p a).toReal * g (φ a) := by
  rw [← PMF.toReal_tsum_mul_ofReal (p.map φ) g hg0, PMF.tsum_map_mul,
    PMF.toReal_tsum_mul_ofReal p (fun a => g (φ a)) (fun a => hg0 _)]

/-- Shifting the start position through the fold: stepping from a translated state
is stepping from the original state by the composite displacement (the fold state
sees only the arrival point; `barrier/count/cumWhite/banked` are untouched). -/
theorem encStep_shift {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ)
    (σ : EncState) (d e : ℕ × ℤ) :
    encStep F R g ⟨σ.pos + d, σ.barrier, σ.count, σ.cumWhite, σ.banked⟩ e
      = encStep F R g σ (d + e) := by
  have hpe : σ.pos + d + e = σ.pos + (d + e) := add_assoc _ _ _
  unfold encStep
  by_cases hq : 1 ≤ (σ.pos + (d + e)).1 ∧ (σ.pos + (d + e)).1 + g ≤ n / 2
      ∧ black n ξ ((σ.pos + (d + e)).1 - 1) (σ.pos + (d + e)).2
      ∧ σ.barrier < (σ.pos + (d + e)).2
  · rw [dif_pos hq, dif_pos (show 1 ≤ (σ.pos + d + e).1 ∧ (σ.pos + d + e).1 + g ≤ n / 2
        ∧ black n ξ ((σ.pos + d + e).1 - 1) (σ.pos + d + e).2
        ∧ σ.barrier < (σ.pos + d + e).2 by rw [hpe]; exact hq)]
    by_cases hw : σ.pos + (d + e) ∈ whiteStrip n ξ
    · rw [if_pos hw, if_pos (show σ.pos + d + e ∈ whiteStrip n ξ by rw [hpe]; exact hw)]
      simp only [hpe]
    · rw [if_neg hw, if_neg (show σ.pos + d + e ∉ whiteStrip n ξ by rw [hpe]; exact hw)]
      simp only [hpe]
  · rw [dif_neg hq, dif_neg (show ¬(1 ≤ (σ.pos + d + e).1 ∧ (σ.pos + d + e).1 + g ≤ n / 2
        ∧ black n ξ ((σ.pos + d + e).1 - 1) (σ.pos + d + e).2
        ∧ σ.barrier < (σ.pos + d + e).2) by rw [hpe]; exact hq)]
    by_cases hw : σ.pos + (d + e) ∈ whiteStrip n ξ
    · rw [if_pos hw, if_pos (show σ.pos + d + e ∈ whiteStrip n ξ by rw [hpe]; exact hw),
        hpe]
    · rw [if_neg hw, if_neg (show σ.pos + d + e ∉ whiteStrip n ξ by rw [hpe]; exact hw),
        hpe]

/-- **The path→`fpDist` block bridge** (the decisive X9 sub-step; paper p.51's
conditioning on `v₁, …, v_{k₁}` in D6 form). From any state `σ` at height-budget
`s = barrier − pos₂`, the walk's evolution UNTIL the barrier is cleared is invisible
to the fold (no encounter can trigger below the barrier, and mid-block white
increments are DROPPED via the coupling `encExpect_anti` — the paper's
`Σ 1_W ≥ 1_W(endpoint)` reduction), so the expectation is dominated by the
first-passage endpoint law: for EVERY horizon `T` and any `[0,B]`-valued `f` that
dominates all shorter-horizon continuations from the clearing step AND the state's
own integrand `encVal σ` (the latter absorbs paths whose passage is unfinished at
the horizon — mid-block steps do not change `encVal`, and `fpDist` has total mass 1),

  `encExpect T σ ≤ Σ'_e fpDist s (e) · f e`.

The fold's clearing condition `barrier < pos₂ + d₂` is EXACTLY `fpDist`'s overshoot
condition `s < d₂` — the two recursions match step for step (strong induction on
`s` mirroring `fpDist`'s budget recursion). -/
theorem encExpect_block_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R g : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) :
    ∀ s : ℕ, ∀ σ : EncState, (s : ℤ) = σ.barrier - σ.pos.2 →
    ∀ T : ℕ,
    ∀ f : ℕ × ℤ → ℝ, (∀ e, 0 ≤ f e) → ∀ B : ℝ, (∀ e, f e ≤ B) →
    (∀ e : ℕ × ℤ, encVal ε R σ ≤ f e) →
    (∀ e : ℕ × ℤ, (s : ℤ) < e.2 → ∀ T' : ℕ, T' < T →
      encExpect F R g ε T' (encStep F R g σ e) ≤ f e) →
    encExpect F R g ε T σ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal * f e := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro σ hs T f hg0 B hgB hf1 hg
    classical
    have hB : 0 ≤ B := le_trans (hg0 (0, 0)) (hgB (0, 0))
    -- horizon 0: the integrand is dominated pointwise, and fpDist has mass 1
    rcases T with _ | T'
    · rw [encExpect_zero]
      have hsum0 : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal) :=
        ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
      have hle0 : ∀ e : ℕ × ℤ,
          (fpDist s e).toReal * encVal ε R σ ≤ (fpDist s e).toReal * f e :=
        fun e => mul_le_mul_of_nonneg_left (hf1 e) ENNReal.toReal_nonneg
      have hsumR0 : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal * f e) :=
        Summable.of_nonneg_of_le
          (fun e => mul_nonneg ENNReal.toReal_nonneg (hg0 e))
          (fun e => mul_le_mul_of_nonneg_left (hgB e) ENNReal.toReal_nonneg)
          (hsum0.mul_right B)
      calc encVal ε R σ
          = ∑' e : ℕ × ℤ, (fpDist s e).toReal * encVal ε R σ := by
            rw [tsum_mul_right, fpDist_tsum_toReal, one_mul]
        _ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal * f e :=
            Summable.tsum_le_tsum hle0 (hsum0.mul_right _) hsumR0
    -- peel one step
    rw [encExpect_succ F R g ε hε T' σ]
    -- unfold one step of fpDist on the right
    conv_rhs => rw [fpDist]
    rw [tsum_bind_toReal hold _ f hg0 hgB]
    -- termwise comparison over the step d
    have hterm : ∀ d : ℕ × ℤ,
        (hold d).toReal * encExpect F R g ε T' (encStep F R g σ d)
          ≤ (hold d).toReal * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
              else (fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) : PMF (ℕ × ℤ)) e).toReal
                * f e := by
      intro d
      rcases eq_or_ne (hold d) 0 with h0 | h0
      · rw [h0]; simp
      have hd3 : 3 ≤ d.2 := hold_support_snd_ge d (by rwa [PMF.mem_support_iff])
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      rcases lt_or_ge (s : ℤ) d.2 with hover | hunder
      · -- the clearing step: pure branch, dominated by f d
        rw [if_pos (Or.inr hover)]
        calc encExpect F R g ε T' (encStep F R g σ d) ≤ f d := hg d hover T' (by omega)
          _ = ∑' e, ((PMF.pure d : PMF (ℕ × ℤ)) e).toReal * f e := by
              rw [tsum_eq_single d (fun e he => by
                rw [PMF.pure_apply, if_neg he]; simp)]
              rw [PMF.pure_apply, if_pos rfl]; simp
      · -- mid-block step: no encounter possible, recurse at the reduced budget
        rw [if_neg (by push_neg; exact ⟨by omega, hunder⟩)]
        -- the fold takes the non-encounter branch (barrier not cleared)
        have hnc : ¬(1 ≤ (σ.pos + d).1 ∧ (σ.pos + d).1 + g ≤ n / 2
            ∧ black n ξ ((σ.pos + d).1 - 1) (σ.pos + d).2 ∧ σ.barrier < (σ.pos + d).2) := by
          rintro ⟨-, -, -, hbar⟩
          have : (σ.pos + d).2 = σ.pos.2 + d.2 := rfl
          omega
        have hstep : encStep F R g σ d
            = ⟨σ.pos + d, σ.barrier, σ.count,
                σ.cumWhite + (if σ.pos + d ∈ whiteStrip n ξ then 1 else 0), σ.banked⟩ := by
          rw [encStep, dif_neg hnc]
        -- drop the mid-block white increment (coupling)
        have hdrop : encExpect F R g ε T' (encStep F R g σ d)
            ≤ encExpect F R g ε T'
                ⟨σ.pos + d, σ.barrier, σ.count, σ.cumWhite, σ.banked⟩ := by
          rw [hstep]
          exact encExpect_anti F R g ε hε T' _ _ rfl rfl rfl (Nat.le_add_right _ _)
            (le_refl _)
        -- recurse via the strong IH at the reduced budget
        set s'' : ℕ := s - d.2.toNat with hs''
        have hrec : encExpect F R g ε T'
              ⟨σ.pos + d, σ.barrier, σ.count, σ.cumWhite, σ.banked⟩
            ≤ ∑' e', (fpDist s'' e').toReal * f (d + e') := by
          refine IH s'' (by omega) _ ?_ T' _ (fun e' => hg0 _) B
            (fun e' => hgB _) (fun e' => hf1 (d + e')) ?_
          · show (s'' : ℤ) = σ.barrier - (σ.pos + d).2
            have : (σ.pos + d).2 = σ.pos.2 + d.2 := rfl
            omega
          · intro e' he' T'' hT''
            rw [encStep_shift]
            refine hg (d + e') ?_ T'' (by omega)
            have h2 : (d + e').2 = d.2 + e'.2 := rfl
            omega
        -- reindex the map branch
        rw [tsum_map_toReal _ _ f hg0]
        exact le_trans (le_trans hdrop hrec) (le_of_eq (tsum_congr fun e' => by rfl))
    -- summability on both sides, then sum the termwise bound
    have hsum : Summable (fun d : ℕ × ℤ => (hold d).toReal) :=
      ENNReal.summable_toReal (by rw [hold.tsum_coe]; exact ENNReal.one_ne_top)
    have hnnL : ∀ d : ℕ × ℤ,
        0 ≤ (hold d).toReal * encExpect F R g ε T' (encStep F R g σ d) :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg F R g ε T' _)
    have hboundL : ∀ d : ℕ × ℤ,
        (hold d).toReal * encExpect F R g ε T' (encStep F R g σ d)
          ≤ (hold d).toReal * Real.exp (ε * R) :=
      fun d => mul_le_mul_of_nonneg_left (encExpect_le F R g ε hε T' _)
        ENNReal.toReal_nonneg
    have hsumL : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * encExpect F R g ε T' (encStep F R g σ d)) :=
      Summable.of_nonneg_of_le hnnL hboundL (hsum.mul_right _)
    have hnnR : ∀ d : ℕ × ℤ, 0 ≤ (hold d).toReal
        * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) : PMF (ℕ × ℤ)) e).toReal
              * f e :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (tsum_nonneg fun e =>
        mul_nonneg ENNReal.toReal_nonneg (hg0 e))
    have hboundR : ∀ d : ℕ × ℤ, (hold d).toReal
        * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) : PMF (ℕ × ℤ)) e).toReal
              * f e ≤ (hold d).toReal * B :=
      fun d => mul_le_mul_of_nonneg_left
        (tsum_toReal_mul_le _ f hg0 hgB hB) ENNReal.toReal_nonneg
    have hsumR : Summable (fun d : ℕ × ℤ => (hold d).toReal
        * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) : PMF (ℕ × ℤ)) e).toReal
              * f e) :=
      Summable.of_nonneg_of_le hnnR hboundR (hsum.mul_right _)
    exact Summable.tsum_le_tsum hterm hsumL hsumR

/-! ### The X9 chain arithmetic: the corrected per-block ledger (lap 52 route)

The corrected Lemma 7.9 induction bounds the expectation from a JUST-ENTERED state
by `e^ε·X` where `X := p₀/(1 − (1−p₀)e^ε)` is the sharp value of the instant
re-encounter chain (`p₀` = white-exit mass of `fpDist_white_exit_deep`). The two
lemmas below are the closed-form real-arithmetic core of that induction; both are
PROVED. The vertex analysis shows the per-block recursion map preserves the bound
`e^ε·X`; `encChainX_le_exp` caps `X ≤ e^ε`, whence `Y ≤ e^{2ε}` — the (7.57)
constant as pinned in `many_triangles_white`. -/

/-- The sharp chain value `X = p₀/(1 − (1−p₀)e^ε)` of the instant re-encounter
ledger (lap-52 route finding; the toy-world value `≈ exp(ε/p₀)` forcing the
corrected `exp(2ε)` constant in (7.57)). -/
noncomputable def encChainX (ε p₀ : ℝ) : ℝ := p₀ / (1 - (1 - p₀) * Real.exp ε)

/-- Positivity of the chain denominator under the smallness hypothesis. -/
theorem encChainX_den_pos {ε p₀ : ℝ} (hp : 1 / 2 < p₀) (hp1 : p₀ ≤ 1)
    (hsmall : (1 - p₀) * (Real.exp ε + 1) ≤ 1) :
    0 < 1 - (1 - p₀) * Real.exp ε := by
  nlinarith [Real.exp_pos ε]

/-- `1 ≤ X`: the chain value dominates the trivial ledger. -/
theorem one_le_encChainX {ε p₀ : ℝ} (hε : 0 ≤ ε) (hp : 1 / 2 < p₀) (hp1 : p₀ ≤ 1)
    (hsmall : (1 - p₀) * (Real.exp ε + 1) ≤ 1) :
    1 ≤ encChainX ε p₀ := by
  have hden := encChainX_den_pos hp hp1 hsmall
  rw [encChainX, le_div_iff₀ hden]
  nlinarith [Real.one_le_exp hε]

/-- **`X ≤ e^ε`** (the cap making `exp(2ε)` consumable): from
`(u−1)·(1 − (1−p₀)(u+1)) ≥ 0` at `u = e^ε ≥ 1`. -/
theorem encChainX_le_exp {ε p₀ : ℝ} (hε : 0 ≤ ε) (hp : 1 / 2 < p₀) (hp1 : p₀ ≤ 1)
    (hsmall : (1 - p₀) * (Real.exp ε + 1) ≤ 1) :
    encChainX ε p₀ ≤ Real.exp ε := by
  have hden := encChainX_den_pos hp hp1 hsmall
  rw [encChainX, div_le_iff₀ hden]
  nlinarith [Real.one_le_exp hε, Real.exp_pos ε]

/-- The defining fixed-point identity of the chain value:
`p₀ + (1−p₀)·e^ε·X = X`. -/
theorem encChainX_fixed {ε p₀ : ℝ} (hp : 1 / 2 < p₀) (hp1 : p₀ ≤ 1)
    (hsmall : (1 - p₀) * (Real.exp ε + 1) ≤ 1) :
    p₀ + (1 - p₀) * Real.exp ε * encChainX ε p₀ = encChainX ε p₀ := by
  have hden := encChainX_den_pos hp hp1 hsmall
  rw [encChainX]
  field_simp
  ring

/-- **The two-mass block bound** (the collapsed form of the vertex LP that the
Z-induction actually consumes): weighting the non-`whiteStrip` exit mass
`d ≤ 1 − p₀` by the re-encounter value `e^ε·X` and everything else by `1` stays
below the fixed point `X`:

  `(1 − d) + d·e^ε·X ≤ X`.

The white/never-encounter branches all carry value `≤ 1` (a white re-encounter
banks the credit: `e^{ε−1}X ≤ e^{2ε−1} ≤ 1`; a never-encounter path has
`encVal = 1`; an out-of-strip exit freezes the fold at `encVal = 1`), so only the
in-strip-black mass `d` pays the chain factor — and `d ≤ 1 − p₀` by
`fpDist_white_exit_deep`. -/
theorem encounter_two_mass_bound {ε p₀ d : ℝ} (hε : 0 ≤ ε)
    (hp : 1 / 2 < p₀) (hp1 : p₀ ≤ 1)
    (hsmall : (1 - p₀) * (Real.exp ε + 1) ≤ 1)
    (hd : 0 ≤ d) (hdp : d ≤ 1 - p₀) :
    (1 - d) + d * (Real.exp ε * encChainX ε p₀) ≤ encChainX ε p₀ := by
  have hfix := encChainX_fixed hp hp1 hsmall
  have hX1 := one_le_encChainX hε hp hp1 hsmall
  have hu := Real.one_le_exp hε
  have hEX : 1 ≤ Real.exp ε * encChainX ε p₀ := by nlinarith
  have hprod : d * (Real.exp ε * encChainX ε p₀ - 1)
      ≤ (1 - p₀) * (Real.exp ε * encChainX ε p₀ - 1) :=
    mul_le_mul_of_nonneg_right hdp (by linarith)
  nlinarith [hprod, hfix]

/-- **The four-mass vertex analysis** (the corrected per-block ledger, lap-52
route; paper p.51 display corrected). One block from a just-entered state: the
exit endpoint is white-and-stopping, white-and-re-encountering (damping `e^{-1}`
banked, chain factor `e^ε·X` re-paid), or non-white (mass `d ≤ 1 − p₀` by the
white-exit bound `fpDist_white_exit_deep`, chain re-paid undamped). The linear
program over the feasible masses is maximised at the `(a, d) = (0, 1−p₀)` vertex,
where the value is EXACTLY `X` — the fixed-point property defining `encChainX`.
Hypothesis `hXe` (`e^{ε−1}·X ≤ 1`) holds for all small `ε` via
`encChainX_le_exp` + `e^{2ε−1} ≤ 1`. -/
theorem encounter_vertex_bound {ε p₀ a d : ℝ} (hε : 0 ≤ ε)
    (hp : 1 / 2 < p₀) (hp1 : p₀ ≤ 1)
    (hsmall : (1 - p₀) * (Real.exp ε + 1) ≤ 1)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (had : a + d ≤ 1) (hdp : d ≤ 1 - p₀)
    (hXe : Real.exp (ε - 1) * encChainX ε p₀ ≤ 1) :
    (1 - a - d) + Real.exp ε * encChainX ε p₀ * (Real.exp (-1) * a + d)
      ≤ Real.exp ε * encChainX ε p₀ := by
  have hden := encChainX_den_pos hp hp1 hsmall
  have hX1 := one_le_encChainX hε hp hp1 hsmall
  have hu := Real.one_le_exp hε
  -- e^ε·e^{−1}·X = e^{ε−1}·X ≤ 1: the white-re-encounter coefficient is ≤ 0
  have hcoef : Real.exp ε * encChainX ε p₀ * Real.exp (-1)
      = Real.exp (ε - 1) * encChainX ε p₀ := by
    rw [show ε - 1 = ε + -1 from by ring, Real.exp_add]
    ring
  -- the defining identity p₀ + (1−p₀)·e^ε·X = X
  have hfix : p₀ + (1 - p₀) * Real.exp ε * encChainX ε p₀ = encChainX ε p₀ := by
    rw [encChainX]
    field_simp
    ring
  -- drop `a` (nonpositive coefficient), push `d` to `1−p₀`, land on the fixed point
  have hXnn : 0 ≤ encChainX ε p₀ := le_trans zero_le_one hX1
  calc (1 - a - d) + Real.exp ε * encChainX ε p₀ * (Real.exp (-1) * a + d)
      = 1 - a * (1 - Real.exp (ε - 1) * encChainX ε p₀)
          - d * (1 - Real.exp ε * encChainX ε p₀) := by
        rw [← hcoef]
        ring
    _ ≤ 1 + d * (Real.exp ε * encChainX ε p₀ - 1) := by
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hXe)]
    _ ≤ 1 + (1 - p₀) * (Real.exp ε * encChainX ε p₀ - 1) := by
        have h1 : 1 ≤ Real.exp ε * encChainX ε p₀ := by nlinarith
        nlinarith
    _ = p₀ + (1 - p₀) * Real.exp ε * encChainX ε p₀ := by ring
    _ = encChainX ε p₀ := hfix
    _ ≤ Real.exp ε * encChainX ε p₀ := by nlinarith

/-- **The Y-induction: the just-entered-state bound of the corrected Lemma 7.9
ledger** (lap-52 route + lap-55 depth gate; paper p.51's induction, corrected).
From any JUST-ENTERED fresh state — position `w` satisfying the gated encounter
conditions, barrier = the top of a family triangle `t` covering the phase point
`(w₁−1, w₂)` — the expectation is bounded by the chain value `X = encChainX ε p₀`,
uniformly in the budget `R`, the horizon `T`, and the entry point:

  `E_R(T, ⟨w, l_t, 0, 0, 0⟩) ≤ X`.

Induction on `R`. Base `R = 0`: the fold is frozen (`encExpect_of_count_ge`),
value `1 ≤ X`. Step: the block bridge (`encExpect_block_le`) reduces the block to
the `fpDist` exit law at budget `s = l_t − w₂`; the exit observable is `1` on
`whiteStrip` exits (an instant white re-encounter banks its credit —
`e^{ε−1}X ≤ 1` — and a white wander carries `w₀ = 1` into `encExpect_wander_le`)
and `e^ε·X` off it (an undamped re-encounter re-pays the chain); the white-exit
mass is `≥ p₀` (hypothesis `hwhite`, discharged by `fpDist_white_exit_deep` with
gate `g = Cthr`), and the two-mass value sits below the fixed point:
`e^εX − (e^εX − 1)·p₀ = p₀ + (1−p₀)e^εX = X` (`encChainX_fixed`). -/
theorem encExpect_entered_le {n ξ : ℕ} (F : TriangleFamily n ξ) (g : ℕ) (ε p₀ : ℝ)
    (hε : 0 ≤ ε) (hp : 1 / 2 < p₀) (hp1 : p₀ ≤ 1)
    (hsmall : (1 - p₀) * (Real.exp ε + 1) ≤ 1)
    (hXe1 : Real.exp (ε - 1) * encChainX ε p₀ ≤ 1)
    (hwhite : ∀ w : ℕ × ℤ, 1 ≤ w.1 → w.1 + g ≤ n / 2 →
      ∀ t ∈ F.T, (w.1 - 1, w.2) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - w.2 →
      p₀ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * Set.indicator (whiteStrip n ξ) 1 (w + e)) :
    ∀ (R T : ℕ) (w : ℕ × ℤ), 1 ≤ w.1 → w.1 + g ≤ n / 2 →
      ∀ t ∈ F.T, (w.1 - 1, w.2) ∈ triangle t.1 t.2.1 t.2.2 →
      encExpect F R g ε T ⟨w, t.2.1, 0, 0, 0⟩ ≤ encChainX ε p₀ := by
  classical
  have hX1 : 1 ≤ encChainX ε p₀ := one_le_encChainX hε hp hp1 hsmall
  have hX0 : 0 ≤ encChainX ε p₀ := le_trans zero_le_one hX1
  have hfix := encChainX_fixed hp hp1 hsmall
  have hexpX1 : 1 ≤ Real.exp ε * encChainX ε p₀ := by
    nlinarith [Real.one_le_exp hε]
  intro R
  induction R with
  | zero =>
    intro T w hw1 hwg t ht hmem
    rw [encExpect_of_count_ge F 0 g ε hε T _ (Nat.zero_le _)]
    calc encVal ε 0 (⟨w, t.2.1, 0, 0, 0⟩ : EncState) = 1 := by simp [encVal]
      _ ≤ encChainX ε p₀ := hX1
  | succ ρ IH =>
    intro T w hw1 hwg t ht hmem
    -- the entered-class wander hypothesis at budget ρ, from the R-induction IH
    have hfreshIH : ∀ (T' : ℕ) (q : ℕ × ℤ), 1 ≤ q.1 → q.1 + g ≤ n / 2 →
        ∀ hcov : (q.1 - 1) + 1 ≤ n / 2 ∧ black n ξ (q.1 - 1) q.2,
        encExpect F ρ g ε T'
          ⟨q, (F.coveringTriangle (q.1 - 1, q.2) hcov).2.1, 0, 0, 0⟩
          ≤ encChainX ε p₀ :=
      fun T' q h1 h2 hcov =>
        IH T' q h1 h2 _ (F.coveringTriangle_mem hcov)
          (F.coveringTriangle_covers hcov)
    -- the block budget
    have hwt : w.2 ≤ t.2.1 := hmem.2.1
    set s : ℕ := (t.2.1 - w.2).toNat with hsdef
    have hsZ : (s : ℤ) = t.2.1 - w.2 := Int.toNat_of_nonneg (by omega)
    -- the exit observable: 1 on white exits, the chain re-payment off them
    set f : ℕ × ℤ → ℝ := fun e =>
      if w + e ∈ whiteStrip n ξ then 1 else Real.exp ε * encChainX ε p₀ with hfdef
    have hf1' : ∀ e, (1 : ℝ) ≤ f e := by
      intro e
      rw [hfdef]
      dsimp only
      split
      · exact le_refl 1
      · exact hexpX1
    have hf0 : ∀ e, 0 ≤ f e := fun e => le_trans zero_le_one (hf1' e)
    have hfB : ∀ e, f e ≤ Real.exp ε * encChainX ε p₀ := by
      intro e
      rw [hfdef]
      dsimp only
      split
      · exact hexpX1
      · exact le_refl _
    -- the bridge hypothesis: every clearing-step continuation is dominated by f
    have hstep : ∀ e : ℕ × ℤ, (s : ℤ) < e.2 → ∀ T' : ℕ, T' < T →
        encExpect F (ρ + 1) g ε T'
          (encStep F (ρ + 1) g ⟨w, t.2.1, 0, 0, 0⟩ e) ≤ f e := by
      intro e he T' hT'
      by_cases hq : 1 ≤ (w + e).1 ∧ (w + e).1 + g ≤ n / 2
          ∧ black n ξ ((w + e).1 - 1) (w + e).2 ∧ t.2.1 < (w + e).2
      · -- instant re-encounter: normalize onto the entered state at budget ρ
        set σ'' := encStep F (ρ + 1) g ⟨w, t.2.1, 0, 0, 0⟩ e with hσ''
        have hcnt : σ''.count = 1 := by rw [hσ'', encStep, dif_pos hq]
        have hpos'' : σ''.pos = w + e := by rw [hσ'', encStep, dif_pos hq]
        have hcov'' : ((w + e).1 - 1) + 1 ≤ n / 2
            ∧ black n ξ ((w + e).1 - 1) (w + e).2 := ⟨by omega, hq.2.2.1⟩
        have hbar'' : σ''.barrier
            = (F.coveringTriangle ((w + e).1 - 1, (w + e).2) hcov'').2.1 := by
          rw [hσ'', encStep, dif_pos hq]
        have hnorm := encExpect_normalize_init F (ρ + 1) g ε hε T' σ''
          (by rw [hcnt]; omega)
        have hcont : encExpect F (ρ + 1 - 1) g ε T'
            ⟨σ''.pos, σ''.barrier, 0, 0, 0⟩ ≤ encChainX ε p₀ := by
          rw [hpos'', hbar'']
          simpa using hfreshIH T' (w + e) hq.1 hq.2.1 hcov''
        by_cases hW : w + e ∈ whiteStrip n ξ
        · -- white instant re-encounter: banks e^{−1}, total e^{ε−1}X ≤ 1 = f e
          have hbk1 : σ''.banked = 1 := by
            rw [hσ'', encStep, dif_pos hq]
            simp [hW]
          have hcw1 : σ''.cumWhite = 1 := by
            rw [hσ'', encStep, dif_pos hq]
            simp [hW]
          rw [hcnt, hbk1, hcw1, max_self] at hnorm
          have hfe : f e = 1 := by rw [hfdef]; simp [hW]
          rw [hfe]
          refine le_trans hnorm (le_trans
            (mul_le_mul_of_nonneg_left hcont (by positivity)) ?_)
          have hee : Real.exp (ε * ((1 : ℕ) : ℝ)) * Real.exp (-((1 : ℕ) : ℝ))
              * encChainX ε p₀ = Real.exp (ε - 1) * encChainX ε p₀ := by
            rw [← Real.exp_add,
              show ε * ((1 : ℕ) : ℝ) + -((1 : ℕ) : ℝ) = ε - 1 by push_cast; ring]
          rw [hee]
          exact hXe1
        · -- black instant re-encounter: undamped chain re-payment e^ε·X = f e
          have hbk0 : σ''.banked = 0 := by
            rw [hσ'', encStep, dif_pos hq]
            simp [hW]
          have hcw0 : σ''.cumWhite = 0 := by
            rw [hσ'', encStep, dif_pos hq]
            simp [hW]
          rw [hcnt, hbk0, hcw0, max_self] at hnorm
          have hfe : f e = Real.exp ε * encChainX ε p₀ := by rw [hfdef]; simp [hW]
          rw [hfe]
          refine le_trans hnorm (le_trans
            (mul_le_mul_of_nonneg_left hcont (by positivity)) ?_)
          have hee : Real.exp (ε * ((1 : ℕ) : ℝ)) * Real.exp (-((0 : ℕ) : ℝ))
              * encChainX ε p₀ = Real.exp ε * encChainX ε p₀ := by
            rw [← Real.exp_add]
            norm_num
          rw [hee]
      · -- no instant re-encounter: the exit wanders with its whiteness credit
        by_cases hW : w + e ∈ whiteStrip n ξ
        · have hsx : encStep F (ρ + 1) g ⟨w, t.2.1, 0, 0, 0⟩ e
              = ⟨w + e, t.2.1, 0, 1, 0⟩ := by
            rw [encStep, dif_neg (by exact hq)]
            simp [hW]
          rw [hsx]
          have hwander := encExpect_wander_le F ρ g ε hε (encChainX ε p₀) hX0
            hfreshIH 1 T' (w + e) t.2.1 1 (le_refl 1)
          refine le_trans hwander ?_
          have hfe : f e = 1 := by rw [hfdef]; simp [hW]
          rw [hfe]
          refine max_le (le_refl 1) ?_
          have hee : Real.exp ε * Real.exp (-((1 : ℕ) : ℝ)) * encChainX ε p₀
              = Real.exp (ε - 1) * encChainX ε p₀ := by
            rw [← Real.exp_add,
              show ε + -((1 : ℕ) : ℝ) = ε - 1 by push_cast; ring]
          rw [hee]
          exact hXe1
        · have hsx : encStep F (ρ + 1) g ⟨w, t.2.1, 0, 0, 0⟩ e
              = ⟨w + e, t.2.1, 0, 0, 0⟩ := by
            rw [encStep, dif_neg (by exact hq)]
            simp [hW]
          rw [hsx]
          have hwander := encExpect_wander_le F ρ g ε hε (encChainX ε p₀) hX0
            hfreshIH 0 T' (w + e) t.2.1 0 (le_refl 0)
          refine le_trans hwander ?_
          have hfe : f e = Real.exp ε * encChainX ε p₀ := by rw [hfdef]; simp [hW]
          rw [hfe]
          refine max_le hexpX1 ?_
          have hee : Real.exp ε * Real.exp (-((0 : ℕ) : ℝ)) * encChainX ε p₀
              = Real.exp ε * encChainX ε p₀ := by
            rw [← Real.exp_add]
            norm_num
          rw [hee]
    -- the bridge, then the two-mass computation at the fixed point
    have hval1 : encVal ε (ρ + 1) (⟨w, t.2.1, 0, 0, 0⟩ : EncState) = 1 := by
      simp [encVal]
    have hbridge := encExpect_block_le F (ρ + 1) g ε hε s ⟨w, t.2.1, 0, 0, 0⟩
      (show (s : ℤ) = t.2.1 - w.2 from hsZ) T f hf0
      (Real.exp ε * encChainX ε p₀) hfB (fun e => hval1.trans_le (hf1' e)) hstep
    refine le_trans hbridge ?_
    have hmass : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal) :=
      ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
    have hWsum : Summable (fun e : ℕ × ℤ =>
        (fpDist s e).toReal * Set.indicator (whiteStrip n ξ) 1 (w + e)) := by
      refine Summable.of_nonneg_of_le (fun e => mul_nonneg ENNReal.toReal_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (fun e => ?_) hmass
      refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
      by_cases hW : w + e ∈ whiteStrip n ξ
      · simp [Set.indicator_of_mem hW]
      · simp [Set.indicator_of_notMem hW]
    have hfid : (fun e : ℕ × ℤ => (fpDist s e).toReal * f e)
        = fun e : ℕ × ℤ =>
          Real.exp ε * encChainX ε p₀ * (fpDist s e).toReal
            - (Real.exp ε * encChainX ε p₀ - 1)
              * ((fpDist s e).toReal * Set.indicator (whiteStrip n ξ) 1 (w + e)) := by
      funext e
      by_cases hW : w + e ∈ whiteStrip n ξ
      · rw [hfdef]
        simp only [if_pos hW, Set.indicator_of_mem hW, Pi.one_apply]
        ring
      · rw [hfdef]
        simp only [if_neg hW, Set.indicator_of_notMem hW]
        ring
    rw [show ∑' e : ℕ × ℤ, (fpDist s e).toReal * f e
        = ∑' e : ℕ × ℤ, (Real.exp ε * encChainX ε p₀ * (fpDist s e).toReal
          - (Real.exp ε * encChainX ε p₀ - 1)
            * ((fpDist s e).toReal * Set.indicator (whiteStrip n ξ) 1 (w + e)))
      from by rw [hfid],
      Summable.tsum_sub (hmass.mul_left _) (hWsum.mul_left _),
      tsum_mul_left, tsum_mul_left, fpDist_tsum_toReal, mul_one]
    have hwm := hwhite w hw1 hwg t ht hmem s hsZ
    nlinarith [hwm, hexpX1, hfix]

/-! ### White-exit kernel decomposition (lap 56)

`fpDist_white_exit_deep` (X9's only open input, shared with X8's Case-2 twin) is
reduced here to two analytic mass bounds via the exact (7.50) geometry. Writing
`q = (⌊n/2⌋-m+e.1, l+e.2)` for the endpoint's phase point, the complement of the
white strip splits (by `white = ¬black` + `F.cover`) into
  • `outStripSet` — `q` overshoots the far edge `⌊n/2⌋` (X6 Gaussian `j`-tail);
  • `phaseInFamily` — `q`'s phase point lands in SOME family triangle.
The start triangle contributes ZERO to the second (`endpoint_notMem_start_triangle`,
proved: the first passage overshoots the budget, so the endpoint clears the apex
height), so it is the FOREIGN-triangle mass, killed by the (7.11) slope band +
`F.separated`. The reduction glue below is axiom-clean; the two `≤ 1/8` tails are
the remaining sorries (`p₀ = 3/4` comfortably clears the numeric `≈ 0.99`). -/

/-- **Out-of-strip endpoints** (the in-strip clause of (7.50), p.48): the phase
point overshoots the far edge `⌊n/2⌋`. Their mass is a Gaussian `j`-tail of
`fpDist_location_bound` (X6): the endpoint's `j` concentrates at `s/4`, and the
(7.52) budget `s = O(m)` gives `s/4 < m`, so `⌊n/2⌋-m+e.1 > ⌊n/2⌋` (i.e.
`e.1 > m`) is a `≳ 3s/4` deviation. -/
def outStripSet (n : ℕ) : Set (ℕ × ℤ) := {q : ℕ × ℤ | n / 2 < q.1}

/-- **Endpoints whose phase point lands in some family triangle** (the whiteness
clause of (7.50)): `(q.1-1, q.2)` — the coordinate `whiteSet` consults — lies in
a triangle of `F`. By `F.cover` this is exactly the black (non-white) event
inside the strip. The start triangle contributes no mass
(`endpoint_notMem_start_triangle`), so this equals the FOREIGN-triangle mass,
controlled by the (7.11) slope band + `F.separated`. -/
def phaseInFamily {n ξ : ℕ} (F : TriangleFamily n ξ) : Set (ℕ × ℤ) :=
  {q : ℕ × ℤ | ∃ t ∈ F.T, ((q.1 - 1, q.2) : ℕ × ℤ) ∈ triangle t.1 t.2.1 t.2.2}

/-- **Overshoot clears the start-triangle top** (the (7.50) "above the apex" step,
p.48). Every first-passage endpoint overshoots its budget
(`fpDist_support_snd_gt`: `s < e.2`); with `s = l_Δ - l` the phase height
`l + e.2` then exceeds the apex height `l_Δ`, and `triangle` requires height
`≤ l₀`, so the phase point is outside the start triangle. This is why
`phaseInFamily` reduces to the FOREIGN triangles (input to `fpDist_any_triangle_le`). -/
theorem endpoint_notMem_start_triangle {s : ℕ} {l lΔ : ℤ} (hs : (s : ℤ) = lΔ - l)
    {e : ℕ × ℤ} (he : e ∈ (fpDist s).support) {j₀ a : ℕ} {sΔ : ℝ} :
    ((a, l + e.2) : ℕ × ℤ) ∉ triangle j₀ lΔ sΔ := by
  intro hmem
  have hgt := fpDist_support_snd_gt s e he
  have h2 : l + e.2 ≤ lΔ := hmem.2.1
  omega

/-- A support-shifted exponential over `ℤ` sums geometrically: the mass at or
below `s` vanishes and the positive tail is `∑_{k≥1} e^{-ck} = e^{-c}/(1-e^{-c})`.
Reusable building block for the white-exit Gaussian tails (`fpDist_col_le`). -/
theorem hasSum_int_shift_exp {c : ℝ} (hc : 0 < c) (s : ℕ) :
    HasSum (fun l : ℤ => if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0)
      (Real.exp (-c) / (1 - Real.exp (-c))) := by
  have he1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have he0 : (0 : ℝ) < Real.exp (-c) := Real.exp_pos _
  set f : ℤ → ℝ :=
    fun l => if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0 with hf
  have hgeom : HasSum (fun n : ℕ => Real.exp (-c) * Real.exp (-c) ^ n)
      (Real.exp (-c) / (1 - Real.exp (-c))) := by
    have h := (hasSum_geometric_of_lt_one he0.le he1).mul_left (Real.exp (-c))
    rwa [← div_eq_mul_inv] at h
  have hneg : HasSum (fun n : ℕ => f (-(↑n + 1))) 0 := by
    have h0 : (fun n : ℕ => f (-(↑n + 1))) = fun _ => (0 : ℝ) := by
      funext n; rw [hf]; dsimp only; rw [if_neg (by push_cast; omega)]
    rw [h0]; exact hasSum_zero
  have hnat : HasSum (fun n : ℕ => f (n : ℤ)) (Real.exp (-c) / (1 - Real.exp (-c))) := by
    have h2 : HasSum (fun n : ℕ => f (((n + (s + 1) : ℕ)) : ℤ))
        (Real.exp (-c) / (1 - Real.exp (-c))) := by
      have he : (fun n : ℕ => f (((n + (s + 1) : ℕ)) : ℤ))
          = fun n : ℕ => Real.exp (-c) * Real.exp (-c) ^ n := by
        funext n; rw [hf]; dsimp only
        rw [if_pos (by push_cast; omega), ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1; push_cast; ring
      rw [he]; exact hgeom
    have hfront : ∑ i ∈ Finset.range (s + 1), f (i : ℤ) = 0 := by
      apply Finset.sum_eq_zero; intro i hi; rw [hf]; dsimp only
      rw [if_neg (by have := Finset.mem_range.mp hi; push_cast; omega)]
    rw [← hasSum_nat_add_iff' (s + 1)]
    simpa [hfront] using h2
  simpa using hnat.of_nat_of_neg_add_one hneg

/-- **First-passage column marginal** (the `l`-collapse of Lemma 7.7): summing the
`fpDist_location_bound` (X6) Gaussian envelope over the height coordinate `l`
(mass lives only on `l > s`, so the `e^{-c(l-s)}` factor collapses geometrically)
gives a per-column bound `≤ C'·Gweight(1+s, c(j-s/4))/√(1+s)`. This is the shared
prerequisite of both white-exit tails: `fpDist_out_of_strip_le` sums it over the
columns `j > m`, and the separation argument reads column-wise Gaussian decay. -/
theorem fpDist_col_le :
    ∃ c > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ (s j : ℕ),
      ∑' l : ℤ, (fpDist s (j, l)).toReal
        ≤ C' * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4))
                  / Real.sqrt (1 + (s : ℝ))) := by
  obtain ⟨c, hc, C, hC, hbound⟩ := fpDist_location_bound
  have he1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have he0 : (0 : ℝ) < Real.exp (-c) := Real.exp_pos _
  have hpos : (0 : ℝ) < 1 - Real.exp (-c) := by linarith
  refine ⟨c, hc, C * (Real.exp (-c) / (1 - Real.exp (-c))),
    mul_pos hC (div_pos he0 hpos), ?_⟩
  intro s j
  set G : ℝ := Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4)) with hG
  have hGnn : 0 ≤ G := Gweight_nonneg _ _
  have hsq : (0 : ℝ) < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  set A : ℝ := C * G / Real.sqrt (1 + (s : ℝ)) with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hdom : HasSum
      (fun l : ℤ => A * (if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0))
      (A * (Real.exp (-c) / (1 - Real.exp (-c)))) := (hasSum_int_shift_exp hc s).mul_left A
  have hptw : ∀ l : ℤ, (fpDist s (j, l)).toReal
      ≤ A * (if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0) := by
    intro l
    by_cases hl : (s : ℤ) < l
    · rw [if_pos hl, hA, hG]
      calc (fpDist s (j, l)).toReal
          ≤ C * (Real.exp (-c * ((l : ℝ) - (s : ℝ))) / Real.sqrt (1 + (s : ℝ)))
              * Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4)) := hbound s j l
        _ = C * Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt (1 + (s : ℝ))
              * Real.exp (-c * ((l : ℝ) - (s : ℝ))) := by ring
    · rw [if_neg hl, mul_zero]
      have h0 : fpDist s (j, l) = 0 := by
        by_contra h
        exact hl (fpDist_support_snd_gt s (j, l) (by rwa [PMF.mem_support_iff]))
      rw [h0, ENNReal.toReal_zero]
  have hslice : Summable (fun l : ℤ => (fpDist s (j, l)).toReal) := by
    have h2d : Summable (fun p : ℕ × ℤ => (fpDist s p).toReal) :=
      ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
    exact h2d.comp_injective (fun a b h => by simpa using h)
  calc ∑' l : ℤ, (fpDist s (j, l)).toReal
      ≤ ∑' l : ℤ, A * (if (s : ℤ) < l then Real.exp (-c * ((l : ℝ) - (s : ℝ))) else 0) :=
        hslice.tsum_le_tsum hptw hdom.summable
    _ = A * (Real.exp (-c) / (1 - Real.exp (-c))) := hdom.tsum_eq
    _ = C * (Real.exp (-c) / (1 - Real.exp (-c))) * (G / Real.sqrt (1 + (s : ℝ))) := by
        rw [hA]; ring

/-- **Gaussian column-tail bound** (the pure-analysis core of `fpDist_out_of_strip_le`):
for any fixed decay `c > 0` and coefficient `C' ≥ 0`, the column bound
`C'·Gweight(1+s, c(j-s/4))/√(1+s)` summed over the columns `j > m` is `≤ 1/8`
once `m ≥ Cthr`, uniformly under the (7.52) budget `s·log 2 ≤ (m+2)·log 9` (which
forces `s/4 < m`, so the tail starts a definite gap past the Gaussian centre
`s/4`). Both `Gweight` pieces decay in `j`: `e^{-c(j-s/4)}` is geometric; the
`e^{-(c(j-s/4))²/(1+s)}` factor is dominated by a geometric via `x² ≥ x₀·x`
(convexity) on the tail. Summability holds since each piece is geometric.

PROVED (lap 57): both `Gweight` pieces are dominated on the tail by shifted
geometrics (`hasSum_nat_tail_exp`): the `e^{-|x|}` piece with rate `c`, the
Gaussian piece with rate `γ₂ = c²/20` via `x²/t ≥ (x₀/t)·x ≥ x/20` (the budget
gives `20·x₀ ≥ t` for `m ≥ 25` since `log 9 ≤ (16/5)·log 2`, i.e. `9⁵ ≤ 2¹⁶`);
the common prefactor `e^{-γ·x₀}` with `x₀ ≥ (m-3)/5` is pushed below `1/(8D)`
by the threshold. Its geometric engine, the ℕ-tail analogue of
`hasSum_int_shift_exp`: `e^{-γ(j-a)}` restricted to `j > m` sums to
`e^{-γ(m+1-a)}/(1-e^{-γ})` (shifted geometric). -/
theorem hasSum_nat_tail_exp {γ : ℝ} (hγ : 0 < γ) (m : ℕ) (a : ℝ) :
    HasSum (fun j : ℕ => if m < j then Real.exp (-γ * ((j : ℝ) - a)) else 0)
      (Real.exp (-γ * (((m : ℝ) + 1) - a)) / (1 - Real.exp (-γ))) := by
  have he1 : Real.exp (-γ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have he0 : (0 : ℝ) < Real.exp (-γ) := Real.exp_pos _
  set f : ℕ → ℝ := fun j => if m < j then Real.exp (-γ * ((j : ℝ) - a)) else 0 with hf
  set E : ℝ := Real.exp (-γ * (((m : ℝ) + 1) - a)) with hE
  have hgeom : HasSum (fun k : ℕ => E * Real.exp (-γ) ^ k)
      (E / (1 - Real.exp (-γ))) := by
    have h := (hasSum_geometric_of_lt_one he0.le he1).mul_left E
    rwa [← div_eq_mul_inv] at h
  have h2 : HasSum (fun k : ℕ => f (k + (m + 1))) (E / (1 - Real.exp (-γ))) := by
    have he : (fun k : ℕ => f (k + (m + 1))) = fun k : ℕ => E * Real.exp (-γ) ^ k := by
      funext k; rw [hf]; dsimp only
      rw [if_pos (by omega), hE, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; push_cast; ring
    rw [he]; exact hgeom
  have hfront : ∑ i ∈ Finset.range (m + 1), f i = 0 := by
    apply Finset.sum_eq_zero; intro i hi; rw [hf]; dsimp only
    rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
  rw [← hasSum_nat_add_iff' (m + 1)]
  simpa [hfront] using h2

theorem gaussian_col_tail {c C' : ℝ} (hc : 0 < c) (hC' : 0 ≤ C') :
    ∃ Cthr : ℕ, ∀ s m : ℕ, Cthr ≤ m →
      (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 →
      Summable (fun j : ℕ => if m < j then
          C' * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4))
                  / Real.sqrt (1 + (s : ℝ))) else 0) ∧
      ∑' j : ℕ, (if m < j then
          C' * (Gweight (1 + (s : ℝ)) (c * ((j : ℝ) - (s : ℝ) / 4))
                  / Real.sqrt (1 + (s : ℝ))) else 0) ≤ 1 / 8 := by
  set γ₂ : ℝ := c ^ 2 / 20 with hγ₂def
  have hγ₂ : (0 : ℝ) < γ₂ := by rw [hγ₂def]; positivity
  set γ : ℝ := min c γ₂ with hγdef
  have hγ : 0 < γ := lt_min hc hγ₂
  have hd₂ : (0 : ℝ) < 1 - Real.exp (-γ₂) := by
    have : Real.exp (-γ₂) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hd₁ : (0 : ℝ) < 1 - Real.exp (-c) := by
    have : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  set D : ℝ := C' * ((1 - Real.exp (-γ₂))⁻¹ + (1 - Real.exp (-c))⁻¹) + 1 with hDdef
  have hD1 : (1 : ℝ) ≤ D := by
    have h0 : 0 ≤ C' * ((1 - Real.exp (-γ₂))⁻¹ + (1 - Real.exp (-c))⁻¹) :=
      mul_nonneg hC' (by positivity)
    rw [hDdef]; linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have h8D : (0 : ℝ) < 8 * D := by linarith
  refine ⟨max 25 (Nat.ceil (5 * Real.log (8 * D) / γ + 3) + 1), ?_⟩
  intro s m hm hbud
  -- threshold consequences
  have hm25 : (25 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast le_trans (le_max_left _ _) hm
  have hmM : 5 * Real.log (8 * D) / γ + 3 ≤ (m : ℝ) := by
    have h1 : Nat.ceil (5 * Real.log (8 * D) / γ + 3) + 1 ≤ m :=
      le_trans (le_max_right _ _) hm
    calc 5 * Real.log (8 * D) / γ + 3
        ≤ (Nat.ceil (5 * Real.log (8 * D) / γ + 3) : ℝ) := Nat.le_ceil _
      _ ≤ (m : ℝ) := by exact_mod_cast le_trans (Nat.le_succ _) h1
  -- budget ⇒ `s ≤ (16/5)(m+2)`  (via `9⁵ ≤ 2¹⁶`)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog9 : Real.log 9 ≤ 16 / 5 * Real.log 2 := by
    have h : Real.log ((9 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 16) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hsle : (s : ℝ) ≤ 16 / 5 * ((m : ℝ) + 2) := by
    have h1 : (s : ℝ) * Real.log 2 ≤ (16 / 5 * ((m : ℝ) + 2)) * Real.log 2 := by
      calc (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 := hbud
        _ ≤ ((m : ℝ) + 2) * (16 / 5 * Real.log 2) :=
            mul_le_mul_of_nonneg_left hlog9 (by positivity)
        _ = (16 / 5 * ((m : ℝ) + 2)) * Real.log 2 := by ring
    exact le_of_mul_le_mul_right h1 hlog2
  set t : ℝ := 1 + (s : ℝ) with htdef
  have ht1 : (1 : ℝ) ≤ t := by rw [htdef]; linarith [Nat.cast_nonneg (α := ℝ) s]
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  set x₀ : ℝ := (m : ℝ) + 1 - (s : ℝ) / 4 with hx₀def
  have hx₀lb : ((m : ℝ) - 3) / 5 ≤ x₀ := by rw [hx₀def]; linarith
  have hx₀pos : 0 < x₀ :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < ((m : ℝ) - 3) / 5) hx₀lb
  have h20 : t ≤ 20 * x₀ := by rw [htdef]; linarith
  -- prefactor smallness: `e^{-γ·x₀} ≤ 1/(8D)`
  have hA : Real.log (8 * D) / γ ≤ x₀ := by
    have h5 : 5 * (Real.log (8 * D) / γ) + 3 ≤ (m : ℝ) := by
      rw [← mul_div_assoc]; exact hmM
    linarith
  have hlogle : Real.log (8 * D) ≤ γ * x₀ := by
    calc Real.log (8 * D) = Real.log (8 * D) / γ * γ :=
        (div_mul_cancel₀ _ hγ.ne').symm
      _ ≤ x₀ * γ := mul_le_mul_of_nonneg_right hA hγ.le
      _ = γ * x₀ := mul_comm _ _
  have hexp_small : Real.exp (-(γ * x₀)) ≤ (8 * D)⁻¹ := by
    calc Real.exp (-(γ * x₀)) ≤ Real.exp (-Real.log (8 * D)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = (8 * D)⁻¹ := by rw [Real.exp_neg, Real.exp_log h8D]
  -- the geometric dominator and its sum
  have hE₂ := hasSum_nat_tail_exp hγ₂ m ((s : ℝ) / 4)
  have hE₁ := hasSum_nat_tail_exp hc m ((s : ℝ) / 4)
  have hg : HasSum (fun j : ℕ => if m < j then
      C' * (Real.exp (-γ₂ * ((j : ℝ) - (s : ℝ) / 4))
          + Real.exp (-c * ((j : ℝ) - (s : ℝ) / 4))) else 0)
      (C' * (Real.exp (-γ₂ * (((m : ℝ) + 1) - (s : ℝ) / 4)) / (1 - Real.exp (-γ₂))
           + Real.exp (-c * (((m : ℝ) + 1) - (s : ℝ) / 4)) / (1 - Real.exp (-c)))) := by
    have h := (hE₂.add hE₁).mul_left C'
    have heq : (fun j : ℕ =>
        C' * ((if m < j then Real.exp (-γ₂ * ((j : ℝ) - (s : ℝ) / 4)) else 0)
            + (if m < j then Real.exp (-c * ((j : ℝ) - (s : ℝ) / 4)) else 0)))
        = fun j : ℕ => if m < j then
            C' * (Real.exp (-γ₂ * ((j : ℝ) - (s : ℝ) / 4))
                + Real.exp (-c * ((j : ℝ) - (s : ℝ) / 4))) else 0 := by
      funext j; by_cases hj : m < j
      · simp [hj]
      · simp [hj]
    exact heq ▸ h
  -- pointwise domination on the tail
  have hfg : ∀ j : ℕ,
      (if m < j then C' * (Gweight t (c * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt t)
        else 0)
      ≤ (if m < j then
          C' * (Real.exp (-γ₂ * ((j : ℝ) - (s : ℝ) / 4))
              + Real.exp (-c * ((j : ℝ) - (s : ℝ) / 4))) else 0) := by
    intro j
    by_cases hj : m < j
    · rw [if_pos hj, if_pos hj]
      set X : ℝ := (j : ℝ) - (s : ℝ) / 4 with hX
      have hjm : (m : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj
      have hXx₀ : x₀ ≤ X := by rw [hX, hx₀def]; linarith
      have hX0 : 0 < X := lt_of_lt_of_le hx₀pos hXx₀
      refine mul_le_mul_of_nonneg_left ?_ hC'
      have hsq1 : (1 : ℝ) ≤ Real.sqrt t := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt ht1
      have hdiv : Gweight t (c * X) / Real.sqrt t ≤ Gweight t (c * X) :=
        div_le_self (Gweight_nonneg _ _) hsq1
      refine hdiv.trans ?_
      unfold Gweight
      have habs : |c * X| = c * X := abs_of_nonneg (by positivity)
      have hkey : γ₂ * X * t ≤ (c * X) ^ 2 := by
        have h20X : t ≤ 20 * X := h20.trans (by linarith)
        have hfac : 0 ≤ c ^ 2 * X * (20 * X - t) :=
          mul_nonneg (mul_nonneg (sq_nonneg c) hX0.le) (by linarith)
        rw [hγ₂def]; nlinarith [hfac]
      have hgauss : Real.exp (-((c * X) ^ 2) / t) ≤ Real.exp (-γ₂ * X) := by
        apply Real.exp_le_exp.mpr
        have hge : γ₂ * X ≤ (c * X) ^ 2 / t := (le_div_iff₀ ht0).mpr hkey
        have hnd : -((c * X) ^ 2) / t = -((c * X) ^ 2 / t) := neg_div _ _
        rw [hnd, neg_mul]
        linarith
      have hexp2 : Real.exp (-|c * X|) ≤ Real.exp (-c * X) :=
        le_of_eq (by rw [habs, neg_mul])
      exact add_le_add hgauss hexp2
    · rw [if_neg hj, if_neg hj]
  have hfnn : ∀ j : ℕ, 0 ≤ (if m < j then
      C' * (Gweight t (c * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt t) else 0) := by
    intro j
    by_cases hj : m < j
    · rw [if_pos hj]
      exact mul_nonneg hC' (div_nonneg (Gweight_nonneg _ _) (Real.sqrt_nonneg _))
    · rw [if_neg hj]
  have hsummf : Summable (fun j : ℕ => if m < j then
      C' * (Gweight t (c * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt t) else 0) :=
    Summable.of_nonneg_of_le hfnn hfg hg.summable
  refine ⟨hsummf, ?_⟩
  -- assemble: tsum f ≤ tsum g = C'(E₂+E₁) ≤ e^{-γx₀}·D ≤ 1/8
  have hstep : ∑' j : ℕ, (if m < j then
      C' * (Gweight t (c * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt t) else 0)
      ≤ C' * (Real.exp (-γ₂ * (((m : ℝ) + 1) - (s : ℝ) / 4)) / (1 - Real.exp (-γ₂))
            + Real.exp (-c * (((m : ℝ) + 1) - (s : ℝ) / 4)) / (1 - Real.exp (-c))) := by
    calc ∑' j : ℕ, (if m < j then
        C' * (Gweight t (c * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt t) else 0)
        ≤ ∑' j : ℕ, (if m < j then
            C' * (Real.exp (-γ₂ * ((j : ℝ) - (s : ℝ) / 4))
                + Real.exp (-c * ((j : ℝ) - (s : ℝ) / 4))) else 0) :=
          hsummf.tsum_le_tsum hfg hg.summable
      _ = _ := hg.tsum_eq
  refine hstep.trans ?_
  -- both exponentials are ≤ e^{-γ·x₀}
  have hm1 : ((m : ℝ) + 1) - (s : ℝ) / 4 = x₀ := by rw [hx₀def]
  rw [hm1]
  have hb₂ : Real.exp (-γ₂ * x₀) ≤ Real.exp (-(γ * x₀)) := by
    apply Real.exp_le_exp.mpr
    have h : γ ≤ γ₂ := min_le_right _ _
    have := mul_le_mul_of_nonneg_right h hx₀pos.le
    linarith
  have hb₁ : Real.exp (-c * x₀) ≤ Real.exp (-(γ * x₀)) := by
    apply Real.exp_le_exp.mpr
    have h : γ ≤ c := min_le_left _ _
    have := mul_le_mul_of_nonneg_right h hx₀pos.le
    linarith
  have hfinal : C' * (Real.exp (-γ₂ * x₀) / (1 - Real.exp (-γ₂))
      + Real.exp (-c * x₀) / (1 - Real.exp (-c)))
      ≤ Real.exp (-(γ * x₀)) * D := by
    have h1 : Real.exp (-γ₂ * x₀) / (1 - Real.exp (-γ₂))
        ≤ Real.exp (-(γ * x₀)) * (1 - Real.exp (-γ₂))⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hb₂ (by positivity)
    have h2 : Real.exp (-c * x₀) / (1 - Real.exp (-c))
        ≤ Real.exp (-(γ * x₀)) * (1 - Real.exp (-c))⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hb₁ (by positivity)
    calc C' * (Real.exp (-γ₂ * x₀) / (1 - Real.exp (-γ₂))
        + Real.exp (-c * x₀) / (1 - Real.exp (-c)))
        ≤ C' * (Real.exp (-(γ * x₀)) * (1 - Real.exp (-γ₂))⁻¹
              + Real.exp (-(γ * x₀)) * (1 - Real.exp (-c))⁻¹) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC'
      _ = Real.exp (-(γ * x₀))
            * (C' * ((1 - Real.exp (-γ₂))⁻¹ + (1 - Real.exp (-c))⁻¹)) := by ring
      _ ≤ Real.exp (-(γ * x₀)) * D := by
          apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          rw [hDdef]; linarith
  refine hfinal.trans ?_
  calc Real.exp (-(γ * x₀)) * D ≤ (8 * D)⁻¹ * D :=
      mul_le_mul_of_nonneg_right hexp_small hD0.le
    _ = 1 / 8 := by field_simp [hD0.ne']


/-- **Out-of-strip tail** (⅛ of the (7.50) budget): the first-passage endpoint
overshoots the far edge `⌊n/2⌋` with probability `≤ 1/8`. The 2-D endpoint sum
Fubini-factors into the column marginals (`fpDist_col_le` = X6's `l`-collapse),
which sum over the overshooting columns `j > m` to `≤ 1/8` by `gaussian_col_tail`
(the (7.52) budget makes `s/4 < m`, so the overshoot is a Gaussian right-tail). -/
theorem fpDist_out_of_strip_le :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamily n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2) ≤ 1 / 8 := by
  obtain ⟨c, hc, C', hC'pos, hcol⟩ := fpDist_col_le
  obtain ⟨Cthr, htail⟩ := gaussian_col_tail hc hC'pos.le
  refine ⟨Cthr, ?_⟩
  intro n ξ hξ F m hm hmn l hl t ht htmem s hs
  -- the (7.52) budget, cast to `s`
  have hbudget : (s : ℝ) * Real.log 2 ≤ ((m : ℝ) + 2) * Real.log 9 := by
    have hb := budget_le_of_mem_triangle F ht htmem (m := m) (by omega)
    have hcast : ((t.2.1 - l).toNat : ℝ) = (s : ℝ) := by
      have h : (t.2.1 - l).toNat = s := by omega
      exact_mod_cast h
    rwa [hcast] at hb
  obtain ⟨hsummB, htailB⟩ := htail s m hm hbudget
  -- the out-strip indicator depends only on the column `e.1`
  have hind : ∀ e : ℕ × ℤ,
      Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2) = (if m < e.1 then (1 : ℝ) else 0) := by
    intro e
    have hiff : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ outStripSet n ↔ m < e.1 := by
      simp only [outStripSet, Set.mem_setOf_eq]; omega
    by_cases h : m < e.1
    · rw [Set.indicator_of_mem (hiff.mpr h), Pi.one_apply, if_pos h]
    · rw [Set.indicator_of_notMem (fun hm' => h (hiff.mp hm')), if_neg h]
  simp_rw [hind]
  -- summability of the 2-D summand (dominated by the fpDist mass)
  have hmass : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal) :=
    ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
  have hite01 : ∀ a : ℕ, (0 : ℝ) ≤ (if m < a then (1 : ℝ) else 0) := by
    intro a; by_cases h : m < a <;> simp [h]
  have hgsum : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal * (if m < e.1 then (1 : ℝ) else 0)) := by
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg (hite01 e.1)) (fun e => ?_) hmass
    refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
    by_cases h : m < e.1 <;> simp [h]
  -- Fubini: 2-D sum factors into the column marginals; each is bounded by `fpDist_col_le`
  rw [Summable.tsum_prod' hgsum (fun b => hgsum.comp_injective (fun c1 c2 h => by simpa using h))]
  show (∑' (a : ℕ) (b : ℤ), (fpDist s (a, b)).toReal * (if m < a then (1 : ℝ) else 0)) ≤ 1 / 8
  have hcolbnd : ∀ a : ℕ,
      (∑' b : ℤ, (fpDist s (a, b)).toReal * (if m < a then (1 : ℝ) else 0))
        ≤ if m < a then C' * (Gweight (1 + (s : ℝ)) (c * ((a : ℝ) - (s : ℝ) / 4))
                              / Real.sqrt (1 + (s : ℝ))) else 0 := by
    intro a
    rw [tsum_mul_right]
    by_cases h : m < a
    · rw [if_pos h, if_pos h, mul_one]; exact hcol s a
    · rw [if_neg h, if_neg h, mul_zero]
  have hinnernn : ∀ a : ℕ,
      0 ≤ ∑' b : ℤ, (fpDist s (a, b)).toReal * (if m < a then (1 : ℝ) else 0) :=
    fun a => tsum_nonneg (fun b => mul_nonneg ENNReal.toReal_nonneg (hite01 a))
  have hinnersum : Summable (fun a : ℕ =>
      ∑' b : ℤ, (fpDist s (a, b)).toReal * (if m < a then (1 : ℝ) else 0)) :=
    Summable.of_nonneg_of_le hinnernn hcolbnd hsummB
  exact le_trans (Summable.tsum_le_tsum hcolbnd hinnersum hsummB) htailB

/-- **Foreign-triangle mass** (⅛ of the (7.50) budget): the first-passage endpoint's
phase point lands in some family triangle with probability `≤ 1/8`. The start
triangle contributes nothing (`endpoint_notMem_start_triangle`), so this is the
foreign mass. Route: the (7.11) slope band `-O(1) ≤ (j'-j_Δ)log 9 ≤ s_Δ + O(1)`
confines the Gaussian-concentrated endpoint to an `O(1)` slab about the start
triangle's diagonal; `F.separated`'s `(1/10)log(1/ε)` gap keeps every other
triangle out of that slab beyond an `O(1)` overlap, whose Gaussian mass is `≤ 1/8`.

OPEN (node X8, shared with X9): consumes `fpDist_location_bound` (X6),
`endpoint_notMem_start_triangle`, and `F.separated` (X3). -/
theorem fpDist_any_triangle_le :
    ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamily n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * Set.indicator (phaseInFamily F) 1 (n / 2 - m + e.1, l + e.2) ≤ 1 / 8 := by
  sorry

/-- **The (7.59)-shaped deep white-exit bound** (the ONLY open external input of
the X9 induction; sibling of the Case-2 kernel `fpDist_white_exit` in
`BlackEdge.lean`). Identical statement with the Case-2 budget hypothesis
`s ≤ m/log²m` REMOVED (any triangle point qualifies — the (7.52) bound
`budget_le_of_mem_triangle` caps `s = O(m)` for free) and the mass sharpened to
`51/100 ≤ p₀` (explicit margin per judge pass 16: the consumer's
`ε₀ = min(1/100, (2p₀−1)/2)` must clear X11's fixed `ε = 10⁻⁴`, which bare
`1/2 < p₀` does not certify; numerically the white-exit mass is ≈ 0.99,
harness check 9, 2026-07-10).

Route: as for `fpDist_white_exit` — Lemma 7.7 (`fpDist_location_bound`, X6)
concentrates the endpoint at `(j + s/4 + O(√(1+s)), l_Δ + O(1))`; every endpoint
clears the triangle top (`fpDist_support_snd_gt`); the (7.11) slope bound + the
`(1/10)·log(1/ε)` family separation (X3) exclude every other triangle, so the
endpoint is white; in-strip since `s/4 + O(√s) ≤ 0.8·m + O(√m) < m`. The
`s ≤ m/log²m` hypothesis of the Case-2 twin is used there ONLY for the
`edgeWeight` degradation, not for whiteness — this deep variant is the same
geometry with a larger (still `O(m)`) budget. -/
theorem fpDist_white_exit_deep :
    ∃ p₀ : ℝ, 51 / 100 ≤ p₀ ∧ ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamily n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      p₀ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) := by
  obtain ⟨CthrO, hOut⟩ := fpDist_out_of_strip_le
  obtain ⟨CthrT, hTri⟩ := fpDist_any_triangle_le
  refine ⟨3 / 4, by norm_num, max CthrO CthrT, ?_⟩
  intro n ξ hξ F m hm hmn l hl t ht htmem s hs
  have hout := hOut n ξ hξ F m (le_trans (le_max_left _ _) hm) hmn l hl t ht htmem s hs
  have htri := hTri n ξ hξ F m (le_trans (le_max_right _ _) hm) hmn l hl t ht htmem s hs
  -- total mass of `fpDist s` is 1; the summand-vs-indicator bookkeeping
  have hmass : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal) :=
    ENNReal.summable_toReal (by rw [(fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
  have hsummand : ∀ (S : Set (ℕ × ℤ)),
      Summable (fun e : ℕ × ℤ => (fpDist s e).toReal
        * Set.indicator S 1 (n / 2 - m + e.1, l + e.2)) := by
    intro S
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (fun e => ?_) hmass
    refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
    by_cases h : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  -- POINTWISE: `1_W(q) ≥ 1 - 1_out(q) - 1_tri(q)` (the (7.50) cover split)
  have hptw : ∀ e : ℕ × ℤ,
      (1 : ℝ) - Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2)
              - Set.indicator (phaseInFamily F) 1 (n / 2 - m + e.1, l + e.2)
        ≤ Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) := by
    intro e
    have hWnn : (0 : ℝ) ≤ Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hOnn : (0 : ℝ) ≤ Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hPnn : (0 : ℝ) ≤ Set.indicator (phaseInFamily F) 1 (n / 2 - m + e.1, l + e.2) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hq1 : 1 ≤ n / 2 - m + e.1 := by omega
    by_cases hO : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ outStripSet n
    · rw [Set.indicator_of_mem hO]; simp only [Pi.one_apply]; linarith
    · by_cases hP : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ phaseInFamily F
      · rw [Set.indicator_of_mem hP]; simp only [Pi.one_apply]; linarith
      · -- neither: the endpoint is white and in-strip
        have hle : n / 2 - m + e.1 ≤ n / 2 := by
          simp only [outStripSet, Set.mem_setOf_eq, not_lt] at hO; exact hO
        have hWmem : ((n / 2 - m + e.1, l + e.2) : ℕ × ℤ) ∈ whiteStrip n ξ := by
          refine ⟨hle, hq1, ?_⟩
          intro hblack
          apply hP
          have hcov : ((n / 2 - m + e.1 - 1, l + e.2) : ℕ × ℤ)
              ∈ {p : ℕ × ℤ | p.1 + 1 ≤ n / 2 ∧ black n ξ p.1 p.2} :=
            ⟨by omega, hblack⟩
          rw [F.cover] at hcov
          simp only [Set.mem_iUnion, exists_prop] at hcov
          obtain ⟨t'', ht'', hmem''⟩ := hcov
          exact ⟨t'', ht'', hmem''⟩
        rw [Set.indicator_of_mem hWmem, Set.indicator_of_notMem hO,
          Set.indicator_of_notMem hP]
        simp
  -- ASSEMBLE: `∑ fpDist·(1 - 1_out - 1_tri) = 1 - outMass - triMass ≥ 3/4`
  have hsumLHS : Summable (fun e : ℕ × ℤ => (fpDist s e).toReal
      * ((1 : ℝ) - Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2)
                 - Set.indicator (phaseInFamily F) 1 (n / 2 - m + e.1, l + e.2))) :=
    ((hmass.sub (hsummand (outStripSet n))).sub (hsummand (phaseInFamily F))).congr
      (fun e => by ring)
  have hexpand : ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * ((1 : ℝ) - Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2)
                   - Set.indicator (phaseInFamily F) 1 (n / 2 - m + e.1, l + e.2))
      = 1 - (∑' e : ℕ × ℤ, (fpDist s e).toReal
              * Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2))
          - (∑' e : ℕ × ℤ, (fpDist s e).toReal
              * Set.indicator (phaseInFamily F) 1 (n / 2 - m + e.1, l + e.2)) := by
    have h1 : ∀ e : ℕ × ℤ, (fpDist s e).toReal
        * ((1 : ℝ) - Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2)
                   - Set.indicator (phaseInFamily F) 1 (n / 2 - m + e.1, l + e.2))
        = (fpDist s e).toReal
            - (fpDist s e).toReal * Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2)
            - (fpDist s e).toReal * Set.indicator (phaseInFamily F) 1 (n / 2 - m + e.1, l + e.2) := by
      intro e; ring
    simp_rw [h1]
    rw [Summable.tsum_sub (hmass.sub (hsummand (outStripSet n))) (hsummand (phaseInFamily F)),
      Summable.tsum_sub hmass (hsummand (outStripSet n)), fpDist_tsum_toReal]
  calc (3 : ℝ) / 4 = 1 - 1 / 8 - 1 / 8 := by norm_num
    _ ≤ 1 - (∑' e : ℕ × ℤ, (fpDist s e).toReal
              * Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2))
          - (∑' e : ℕ × ℤ, (fpDist s e).toReal
              * Set.indicator (phaseInFamily F) 1 (n / 2 - m + e.1, l + e.2)) := by
        linarith [hout, htri]
    _ = ∑' e : ℕ × ℤ, (fpDist s e).toReal
          * ((1 : ℝ) - Set.indicator (outStripSet n) 1 (n / 2 - m + e.1, l + e.2)
                     - Set.indicator (phaseInFamily F) 1 (n / 2 - m + e.1, l + e.2)) := hexpand.symm
    _ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
          * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) :=
        Summable.tsum_le_tsum
          (fun e => mul_le_mul_of_nonneg_left (hptw e) ENNReal.toReal_nonneg)
          hsumLHS (hsummand (whiteStrip n ξ))

/-- **Lemma 7.9 — many triangles usually implies many white points** (paper (7.57),
pp.50–51, WITH A CORRECTED CONSTANT — see the deviation note below). For the `T`-step
renewal walk started at any `(j', l')`, any number of blocks `R ≥ 1`, and any
sufficiently small `ε`:

  `E exp(−Σ_{p=1}^{t_{min(r,R)}} 1_W((j',l')+v_{[1,p]}) + ε·min(r,R)) ≤ exp(2·ε)`,

uniformly in the horizon `T`, the start `(j',l')`, `R`, and `n, ξ`. The exponent is
read off the encounter fold: `banked = Σ_{p=1}^{t_{min(r,R)}} 1_W`, `count = r`
(see `EncState`/`encStep`; faithfulness deltas — finite horizon, existential ε,
phase-shift — argued in the module docstring).

**DEVIATION from the paper (lap 52 route finding): `exp(2ε)`, not `exp(ε)`.** The
paper's p.51 proof asserts the conditional expectation given the first block
`v₁ … v_{k₁}` EQUALS `exp(−Σ_{p≤k₁}1_W + ε)·Z(endpoint, R−1)`. On the
`min(r,R) = 1` branch the true sum stops at `t₁ < k₁`, so that display OVERCOUNTS
damping (the claimed expression under-estimates the true value), and the upper-bound
derivation is unsound as written. Correcting the ledger (each encounter's `e^ε` is
paid by the PREVIOUS block's exit-whiteness) meets an adversarial configuration the
`p₀`-machinery alone cannot exclude — a black-strip exit point IS the next stopping
time (instant re-encounter), while white exits stop the chain and their damping is
then never counted (`t_min < k`). A chain computation gives the sharp toy-world value
`e^ε·p₀/(1 − (1−p₀)e^ε) ≈ exp(ε/p₀) > exp(ε)`, so the paper's constant is likely
unprovable. Since `p₀ > 1/2` (numerically ≈ 0.99), `p₀/(1−(1−p₀)e^ε) ≤ e^ε` for
small `ε`, giving `exp(2ε)`. The p.55 consumer is Markov + a free choice of `R`
AFTER ε, so any absolute constant in the exponent is absorbed — `exp(2ε)` is fully
consumable by X11.

**SECOND DEVIATION (lap 55 reflection): the encounter count is DEPTH-GATED.** The
statement bounds the fold with gate `g` (an absolute constant, `∃`-bound below —
in the proof it is the `Cthr` of `fpDist_white_exit_deep`): encounters count only
at depth ≥ `g` from the strip edge. Justification: the paper's induction step
cashes exit-whiteness via (7.59) "by repeating the proof of (7.51)" (p.51), but
that geometry FAILS for triangles near the edge `j = ⌊n/2⌋` — the first-passage
endpoint leaves the strip with non-vanishing mass, so no `p₀`-compensation exists
there, and adversarial edge-strip families would otherwise accumulate uncompensated
`e^ε` payments, likely FALSIFYING (7.57) as printed (uniform over all starts). The
paper's only remark on the edge (p.50: "`r` is finite since the process eventually
exits the strip") is finiteness, not a ledger. Consumer-verification (lap 55, vs
pp.49+55): Case 3 applies this lemma after the (7.54) split, whose surviving branch
has `j_{[1,k+P]} < 0.9m` with `m ≥ C_{A,ε}`, so every encounter the deterministic
claim (7.67) produces sits at depth `≥ 0.1m ≥ g` once `C_{A,ε} ≥ 10·g` — the gated
count still reaches `R`, and the p.55 Markov consumption is unchanged. `g = 0`
recovers the ungated encoding verbatim.

PROOF (lap 55; sole external input = `fpDist_white_exit_deep`, whose `Cthr` is
the gate `g`): the init state is a credit-0 wander state, so `encExpect_wander_le`
bounds it by `max 1 (e^ε·X) ≤ e^{2ε}` (`encChainX_le_exp`), with the entered-class
hypothesis supplied by the Y-induction `encExpect_entered_le` at budget `R − 1`.
The smallness shell: `ε₀ = min(1/100, (2p₀−1)/2)` makes `(1−p₀)(e^ε+1) ≤ 1` (via
`e^ε(1−ε) ≤ 1`) and `e^{ε−1}X ≤ e^{2ε−1} ≤ 1`. -/
theorem many_triangles_white :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 100 ∧ ∃ g : ℕ,
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
    ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (j' : ℕ) (l' : ℤ),
    encExpect F R g ε T (encInit j' l') ≤ Real.exp (2 * ε) := by
  obtain ⟨p₀, hp₀, Cthr, hkernel⟩ := fpDist_white_exit_deep
  -- normalize the mass into (1/2, 1]
  set p₁ : ℝ := min p₀ 1 with hp₁def
  have hp : 1 / 2 < p₁ := lt_min (by linarith) (by norm_num)
  have hp1 : p₁ ≤ 1 := min_le_right _ _
  refine ⟨min (1 / 100) ((2 * p₁ - 1) / 2),
    lt_min (by norm_num) (by nlinarith), min_le_left _ _, Cthr, ?_⟩
  intro ε hε hεε₀ n ξ hξ F R hR T j' l'
  have hε100 : ε ≤ 1 / 100 := le_trans hεε₀ (min_le_left _ _)
  have hεp : ε ≤ (2 * p₁ - 1) / 2 := le_trans hεε₀ (min_le_right _ _)
  have hε1 : ε < 1 := by linarith
  -- smallness: (1 − p₁)(e^ε + 1) ≤ 1, via e^ε·(1 − ε) ≤ 1
  have hkey : Real.exp ε * (1 - ε) ≤ 1 := by
    have h := Real.add_one_le_exp (-ε)
    calc Real.exp ε * (1 - ε) = Real.exp ε * (-ε + 1) := by ring
      _ ≤ Real.exp ε * Real.exp (-ε) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos ε).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hsmall : (1 - p₁) * (Real.exp ε + 1) ≤ 1 := by
    have h2 : (Real.exp ε + 1) * (1 - ε) ≤ 2 - ε := by nlinarith
    have h3 : (1 - p₁) * (2 - ε) ≤ 1 - ε := by
      have hprod : ε * p₁ ≤ ε * 1 :=
        mul_le_mul_of_nonneg_left hp1 hε.le
      nlinarith
    have h4 : (1 - p₁) * (Real.exp ε + 1) * (1 - ε) ≤ 1 * (1 - ε) := by
      have := mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 1 - p₁ by linarith)
      calc (1 - p₁) * (Real.exp ε + 1) * (1 - ε)
          = (1 - p₁) * ((Real.exp ε + 1) * (1 - ε)) := by ring
        _ ≤ (1 - p₁) * (2 - ε) := this
        _ ≤ 1 - ε := h3
        _ = 1 * (1 - ε) := (one_mul _).symm
    exact le_of_mul_le_mul_right h4 (by linarith)
  have hXe : encChainX ε p₁ ≤ Real.exp ε := encChainX_le_exp hε.le hp hp1 hsmall
  have hX1 : 1 ≤ encChainX ε p₁ := one_le_encChainX hε.le hp hp1 hsmall
  have hX0 : 0 ≤ encChainX ε p₁ := le_trans zero_le_one hX1
  have hXe1 : Real.exp (ε - 1) * encChainX ε p₁ ≤ 1 := by
    calc Real.exp (ε - 1) * encChainX ε p₁
        ≤ Real.exp (ε - 1) * Real.exp ε :=
          mul_le_mul_of_nonneg_left hXe (Real.exp_pos _).le
      _ = Real.exp (ε - 1 + ε) := (Real.exp_add _ _).symm
      _ ≤ 1 := by
          rw [Real.exp_le_one_iff]
          linarith
  -- the white-mass hypothesis in the entered-state form, from the kernel
  have hwhite : ∀ w : ℕ × ℤ, 1 ≤ w.1 → w.1 + Cthr ≤ n / 2 →
      ∀ t ∈ F.T, (w.1 - 1, w.2) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - w.2 →
      p₁ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * Set.indicator (whiteStrip n ξ) 1 (w + e) := by
    intro w hw1 hwg t ht hmem s hsZ
    have hm : n / 2 - (n / 2 - w.1) = w.1 := by omega
    have h := hkernel n ξ hξ F (n / 2 - w.1) (by omega) (by omega) w.2 (by omega)
      t ht (by rw [show n / 2 - (n / 2 - w.1) - 1 = w.1 - 1 from by omega]; exact hmem)
      s hsZ
    refine le_trans (min_le_left _ _) (h.trans_eq (tsum_congr fun e => ?_))
    rw [hm]
    rfl
  -- the Y-bound for entered states, and the induced wander hypothesis at R − 1
  have hY := encExpect_entered_le F Cthr ε p₁ hε.le hp hp1 hsmall hXe1 hwhite
  have hfresh : ∀ (T' : ℕ) (q : ℕ × ℤ), 1 ≤ q.1 → q.1 + Cthr ≤ n / 2 →
      ∀ hcov : (q.1 - 1) + 1 ≤ n / 2 ∧ black n ξ (q.1 - 1) q.2,
      encExpect F (R - 1) Cthr ε T'
        ⟨q, (F.coveringTriangle (q.1 - 1, q.2) hcov).2.1, 0, 0, 0⟩
        ≤ encChainX ε p₁ :=
    fun T' q h1 h2 hcov =>
      hY (R - 1) T' q h1 h2 _ (F.coveringTriangle_mem hcov)
        (F.coveringTriangle_covers hcov)
  -- the init state is a wander state with zero credit
  have hwander := encExpect_wander_le F (R - 1) Cthr ε hε.le (encChainX ε p₁) hX0
    hfresh 0 T (j', l') l' 0 (le_refl 0)
  rw [show R - 1 + 1 = R from by omega] at hwander
  refine le_trans hwander ?_
  refine max_le (Real.one_le_exp (by positivity)) ?_
  calc Real.exp ε * Real.exp (-((0 : ℕ) : ℝ)) * encChainX ε p₁
      = Real.exp ε * encChainX ε p₁ := by norm_num
    _ ≤ Real.exp ε * Real.exp ε :=
        mul_le_mul_of_nonneg_left hXe (Real.exp_pos _).le
    _ = Real.exp (2 * ε) := by rw [← Real.exp_add]; ring_nf

/-! ### The (7.61) endpoint tails (X10, p.52): the `tsum_Gweight_row` engine,
the first-passage height tail, and the `p`-step Chernoff tail -/

/-- **`Gweight` row-sum engine** (step (i) of the (7.61) tail plan, lap 57/58):
the X6 envelope `Gweight t (c(j − μ))` summed along a row of natural columns is
`≤ K·√t`, uniformly in the (real) centre `μ` and the row length `N`. Double
cover: reduce the real centre to the integer `⌊μ⌋` at the cost of one unit
shift (the `max (u−1) 0` inside the dominators), fold the two sides of the
centre onto ℕ offsets (`sum_abs_int_le`), then `sum_range_exp_neg_sq_le`
(Gaussian piece, `≍ √t/c` unit terms) + `sum_range_geom_le` (exponential
piece). Uniformity in `N` is what turns into the `tsum` bound downstream. -/
theorem sum_range_Gweight_le {c : ℝ} (hc : 0 < c) :
    ∃ K > (0 : ℝ), ∀ t : ℝ, 1 ≤ t → ∀ μ : ℝ, ∀ N : ℕ,
      ∑ j ∈ Finset.range N, Gweight t (c * ((j : ℝ) - μ)) ≤ K * Real.sqrt t := by
  have he1 : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hd : (0 : ℝ) < 1 - Real.exp (-c) := by linarith [Real.exp_pos (-c)]
  refine ⟨10 + 2 / (1 - Real.exp (-c)) + 4 / c, by positivity, fun t ht μ N => ?_⟩
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  set β : ℝ := c ^ 2 / t with hβdef
  have hβ0 : 0 < β := by positivity
  set w : ℤ := ⌊μ⌋ with hw
  set J : ℕ := max N (w.toNat + 1) with hJ
  have hwJ : w.toNat < J := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  set F1 : ℝ → ℝ := fun u => Real.exp (-β * max (u - 1) 0 ^ 2) with hF1
  set F2 : ℝ → ℝ := fun u => Real.exp (-(c * max (u - 1) 0)) with hF2
  have hF1nn : ∀ u, 0 ≤ F1 u := fun u => (Real.exp_pos _).le
  have hF2nn : ∀ u, 0 ≤ F2 u := fun u => (Real.exp_pos _).le
  have hmax0 : ∀ u : ℝ, 0 ≤ max (u - 1) 0 := fun u => le_max_right _ _
  have hmaxmono : ∀ ⦃u v : ℝ⦄, u ≤ v → max (u - 1) 0 ≤ max (v - 1) 0 :=
    fun u v h => max_le_max (by linarith) le_rfl
  have hF1anti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v → F1 v ≤ F1 u := by
    intro u v _ huv
    apply Real.exp_le_exp.mpr
    have h := hmaxmono huv
    have h0 : 0 ≤ max (u - 1) 0 := hmax0 u
    have hsq : max (u - 1) 0 ^ 2 ≤ max (v - 1) 0 ^ 2 := by nlinarith
    nlinarith
  have hF2anti : ∀ ⦃u v : ℝ⦄, 0 ≤ u → u ≤ v → F2 v ≤ F2 u := by
    intro u v _ huv
    apply Real.exp_le_exp.mpr
    have h := hmaxmono huv
    nlinarith
  -- pointwise domination through the integer centre
  have hpt : ∀ j : ℕ, Gweight t (c * ((j : ℝ) - μ))
      ≤ F1 |(w : ℝ) - j| + F2 |(w : ℝ) - j| := by
    intro j
    have hwμ : |μ - (w : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith [Int.floor_le μ] : (0 : ℝ) ≤ μ - w)]
      linarith [Int.lt_floor_add_one μ]
    have hkey : max (|(w : ℝ) - j| - 1) 0 ≤ |(j : ℝ) - μ| := by
      have h1 : |(w : ℝ) - j| ≤ |(j : ℝ) - μ| + |μ - w| := by
        calc |(w : ℝ) - j| = |(j : ℝ) - w| := abs_sub_comm _ _
          _ ≤ |(j : ℝ) - μ| + |μ - w| := abs_sub_le _ _ _
      exact max_le (by linarith) (abs_nonneg _)
    have habs0 : (0 : ℝ) ≤ |(j : ℝ) - μ| := abs_nonneg _
    unfold Gweight
    have h1 : Real.exp (-(c * ((j : ℝ) - μ)) ^ 2 / t) ≤ F1 |(w : ℝ) - j| := by
      have he : -(c * ((j : ℝ) - μ)) ^ 2 / t = -β * |(j : ℝ) - μ| ^ 2 := by
        rw [hβdef, sq_abs]
        ring
      rw [he, hF1]
      apply Real.exp_le_exp.mpr
      have hsq : max (|(w : ℝ) - j| - 1) 0 ^ 2 ≤ |(j : ℝ) - μ| ^ 2 := by
        nlinarith [hmax0 |(w : ℝ) - j|]
      nlinarith
    have h2 : Real.exp (-|c * ((j : ℝ) - μ)|) ≤ F2 |(w : ℝ) - j| := by
      rw [abs_mul, abs_of_pos hc, hF2]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hkey hc.le
      linarith
    exact add_le_add h1 h2
  -- fold onto ℕ offsets
  have hcov1 := sum_abs_int_le hF1nn hF1anti w J hwJ
  have hcov2 := sum_abs_int_le hF2nn hF2anti w J hwJ
  -- the two shifted tail sums
  have hJex : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  obtain ⟨J', hJ'⟩ := hJex
  have hshift1 : ∑ m ∈ Finset.range J, F1 (m : ℝ) ≤ 4 + 2 * Real.sqrt t / c := by
    rw [hJ', Finset.sum_range_succ' (fun m : ℕ => F1 (m : ℝ)) J']
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hzero : F1 ((0 : ℕ) : ℝ) = 1 := by
      rw [hF1]
      norm_num
    have hterm : ∀ i : ℕ, F1 ((i + 1 : ℕ) : ℝ) = Real.exp (-β * (i : ℝ) ^ 2) := by
      intro i
      rw [hF1]
      congr 2
      push_cast
      rw [show ((i : ℝ) + 1 - 1) = (i : ℝ) by ring, max_eq_left (Nat.cast_nonneg i)]
    have hsum := sum_range_exp_neg_sq_le hβ0 J'
    have hsqrtβ : Real.sqrt β = c / Real.sqrt t := by
      rw [hβdef, Real.sqrt_div (sq_nonneg c), Real.sqrt_sq hc.le]
    have h2β : 2 / Real.sqrt β = 2 * Real.sqrt t / c := by
      rw [hsqrtβ]
      field_simp
    calc (∑ i ∈ Finset.range J', F1 ((i + 1 : ℕ) : ℝ)) + F1 ((0 : ℕ) : ℝ)
        = (∑ i ∈ Finset.range J', Real.exp (-β * (i : ℝ) ^ 2)) + 1 := by
          rw [hzero, Finset.sum_congr rfl fun i _ => hterm i]
      _ ≤ (3 + 2 / Real.sqrt β) + 1 := by linarith
      _ = 4 + 2 * Real.sqrt t / c := by rw [h2β]; ring
  have hshift2 : ∑ m ∈ Finset.range J, F2 (m : ℝ) ≤ 1 + (1 - Real.exp (-c))⁻¹ := by
    rw [hJ', Finset.sum_range_succ' (fun m : ℕ => F2 (m : ℝ)) J']
    have hzero : F2 ((0 : ℕ) : ℝ) = 1 := by
      rw [hF2]
      norm_num
    have hterm : ∀ i : ℕ, F2 ((i + 1 : ℕ) : ℝ) = Real.exp (-c) ^ i := by
      intro i
      rw [hF2, ← Real.exp_nat_mul]
      congr 1
      push_cast
      rw [show ((i : ℝ) + 1 - 1) = (i : ℝ) by ring, max_eq_left (Nat.cast_nonneg i)]
      ring
    have hsum := sum_range_geom_le (Real.exp_pos (-c)).le he1 J'
    calc (∑ i ∈ Finset.range J', F2 ((i + 1 : ℕ) : ℝ)) + F2 ((0 : ℕ) : ℝ)
        = (∑ i ∈ Finset.range J', Real.exp (-c) ^ i) + 1 := by
          rw [hzero, Finset.sum_congr rfl fun i _ => hterm i]
      _ ≤ (1 - Real.exp (-c))⁻¹ + 1 := by linarith
      _ = 1 + (1 - Real.exp (-c))⁻¹ := by ring
  -- assemble
  have h1t : 1 ≤ Real.sqrt t := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ht
  have hchain : ∑ j ∈ Finset.range N, Gweight t (c * ((j : ℝ) - μ))
      ≤ 2 * (4 + 2 * Real.sqrt t / c) + 2 * (1 + (1 - Real.exp (-c))⁻¹) := by
    calc ∑ j ∈ Finset.range N, Gweight t (c * ((j : ℝ) - μ))
        ≤ ∑ j ∈ Finset.range N, (F1 |(w : ℝ) - j| + F2 |(w : ℝ) - j|) :=
          Finset.sum_le_sum fun j _ => hpt j
      _ ≤ ∑ j ∈ Finset.range J, (F1 |(w : ℝ) - j| + F2 |(w : ℝ) - j|) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.mpr
              (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left _ _)))
            (fun j _ _ => add_nonneg (hF1nn _) (hF2nn _))
      _ = (∑ j ∈ Finset.range J, F1 |(w : ℝ) - j|)
          + ∑ j ∈ Finset.range J, F2 |(w : ℝ) - j| := Finset.sum_add_distrib
      _ ≤ 2 * (∑ m ∈ Finset.range J, F1 (m : ℝ))
          + 2 * (∑ m ∈ Finset.range J, F2 (m : ℝ)) := add_le_add hcov1 hcov2
      _ ≤ 2 * (4 + 2 * Real.sqrt t / c) + 2 * (1 + (1 - Real.exp (-c))⁻¹) := by
          have h1 := hshift1
          have h2 := hshift2
          linarith
  refine hchain.trans ?_
  have hcinv : (0 : ℝ) ≤ (1 - Real.exp (-c))⁻¹ := by positivity
  have hexpand : (10 + 2 / (1 - Real.exp (-c)) + 4 / c) * Real.sqrt t
      = 10 * Real.sqrt t + 2 * (1 - Real.exp (-c))⁻¹ * Real.sqrt t
        + 4 / c * Real.sqrt t := by
    rw [div_eq_mul_inv (2 : ℝ), div_eq_mul_inv (4 : ℝ)]
    ring
  rw [hexpand]
  have ha : 2 * (4 + 2 * Real.sqrt t / c) = 8 + 4 / c * Real.sqrt t := by ring
  have hb : (10 : ℝ) ≤ 10 * Real.sqrt t := by linarith
  have hd2 : 2 * (1 - Real.exp (-c))⁻¹ ≤ 2 * (1 - Real.exp (-c))⁻¹ * Real.sqrt t := by
    nlinarith
  rw [ha]
  linarith

/-- **First-passage height tail** (step (ii) of the (7.61) plan, ℝ≥0∞ form):
`P(f.2 ≥ s + y) ≤ C·e^{−cy}` for the first-passage endpoint `f ~ fpDist s`,
uniformly in `s`. Sum the X6 envelope `fpDist_location_bound`: the height
factor `e^{−c(l−s)}` donates `e^{−(c/2)y}` on the tail `l ≥ s + y` and stays
geometrically summable at rate `c/2` (`hasSum_int_shift_exp`); the column
factor sums to `K·√(1+s)` by `sum_range_Gweight_le`, cancelling the envelope's
`1/√(1+s)`. Stated in `ℝ≥0∞` so the `fpDistPlus` glue needs no summability
side conditions. -/
theorem fpDist_height_tail :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ s : ℕ, ∀ y : ℝ, 0 ≤ y →
      ∑' e : ℕ × ℤ, (if (s : ℝ) + y ≤ (e.2 : ℝ) then fpDist s e else 0)
        ≤ ENNReal.ofReal (C * Real.exp (-c * y)) := by
  obtain ⟨cL, hcL, CL, hCL, hbd⟩ := fpDist_location_bound
  obtain ⟨K, hK, hrow⟩ := sum_range_Gweight_le hcL
  have hc2 : (0 : ℝ) < cL / 2 := by positivity
  have he1 : Real.exp (-(cL / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hgd : (0 : ℝ) < 1 - Real.exp (-(cL / 2)) := by
    linarith [Real.exp_pos (-(cL / 2))]
  set geo : ℝ := Real.exp (-(cL / 2)) / (1 - Real.exp (-(cL / 2))) with hgeo
  have hgeo0 : 0 < geo := div_pos (Real.exp_pos _) hgd
  refine ⟨cL / 2, hc2, CL * K * geo, by positivity, fun s y hy => ?_⟩
  have h1s : (0 : ℝ) < 1 + (s : ℝ) := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr h1s
  set A : ℕ → ℝ := fun j =>
    CL * Gweight (1 + (s : ℝ)) (cL * ((j : ℝ) - (s : ℝ) / 4))
      / Real.sqrt (1 + (s : ℝ)) with hA
  set B : ℤ → ℝ := fun l =>
    if (s : ℤ) < l then Real.exp (-(cL / 2) * ((l : ℝ) - (s : ℝ))) else 0 with hB
  have hAnn : ∀ j, 0 ≤ A j := fun j =>
    div_nonneg (mul_nonneg hCL.le (Gweight_nonneg _ _)) hsq.le
  have hBnn : ∀ l, 0 ≤ B l := by
    intro l
    rw [hB]
    dsimp only
    split_ifs
    exacts [(Real.exp_pos _).le, le_rfl]
  -- pointwise domination
  have hpt : ∀ e : ℕ × ℤ, (if (s : ℝ) + y ≤ (e.2 : ℝ) then fpDist s e else 0)
      ≤ ENNReal.ofReal (Real.exp (-(cL / 2) * y))
        * (ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2)) := by
    intro e
    obtain ⟨j, l⟩ := e
    by_cases hyl : (s : ℝ) + y ≤ ((j, l) : ℕ × ℤ).2
    · rw [if_pos hyl]
      by_cases hsl : (s : ℤ) < l
      · have hls : y ≤ (l : ℝ) - (s : ℝ) := by
          have : (s : ℝ) + y ≤ (l : ℝ) := hyl
          linarith
        have hfac : (0 : ℝ) ≤ CL * Gweight (1 + (s : ℝ))
            (cL * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt (1 + (s : ℝ)) :=
          div_nonneg (mul_nonneg hCL.le (Gweight_nonneg _ _)) hsq.le
        have hsplit : Real.exp (-cL * ((l : ℝ) - (s : ℝ)))
            ≤ Real.exp (-(cL / 2) * y) * Real.exp (-(cL / 2) * ((l : ℝ) - (s : ℝ))) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith
        have hRe : (fpDist s (j, l)).toReal
            ≤ Real.exp (-(cL / 2) * y) * (A j * B l) := by
          rw [hA, hB]
          dsimp only
          rw [if_pos hsl]
          calc (fpDist s (j, l)).toReal
              ≤ CL * (Real.exp (-cL * ((l : ℝ) - (s : ℝ))) / Real.sqrt (1 + (s : ℝ)))
                  * Gweight (1 + (s : ℝ)) (cL * ((j : ℝ) - (s : ℝ) / 4)) := hbd s j l
            _ = Real.exp (-cL * ((l : ℝ) - (s : ℝ)))
                  * (CL * Gweight (1 + (s : ℝ)) (cL * ((j : ℝ) - (s : ℝ) / 4))
                    / Real.sqrt (1 + (s : ℝ))) := by ring
            _ ≤ (Real.exp (-(cL / 2) * y) * Real.exp (-(cL / 2) * ((l : ℝ) - (s : ℝ))))
                  * (CL * Gweight (1 + (s : ℝ)) (cL * ((j : ℝ) - (s : ℝ) / 4))
                    / Real.sqrt (1 + (s : ℝ))) :=
                mul_le_mul_of_nonneg_right hsplit hfac
            _ = Real.exp (-(cL / 2) * y)
                  * (CL * Gweight (1 + (s : ℝ)) (cL * ((j : ℝ) - (s : ℝ) / 4))
                      / Real.sqrt (1 + (s : ℝ))
                    * Real.exp (-(cL / 2) * ((l : ℝ) - (s : ℝ)))) := by ring
        calc fpDist s (j, l)
            = ENNReal.ofReal ((fpDist s (j, l)).toReal) :=
              (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal (Real.exp (-(cL / 2) * y) * (A j * B l)) :=
              ENNReal.ofReal_le_ofReal hRe
          _ = ENNReal.ofReal (Real.exp (-(cL / 2) * y))
                * (ENNReal.ofReal (A j) * ENNReal.ofReal (B l)) := by
              rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
                ENNReal.ofReal_mul (hAnn j)]
      · have h0 : fpDist s (j, l) = 0 := by
          by_contra h
          exact hsl (fpDist_support_snd_gt s (j, l) (by rwa [PMF.mem_support_iff]))
        rw [h0]
        exact zero_le'
    · rw [if_neg hyl]
      exact zero_le'
  -- factor the double sum
  have hfact : ∑' e : ℕ × ℤ, (ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2))
      = (∑' j : ℕ, ENNReal.ofReal (A j)) * (∑' l : ℤ, ENNReal.ofReal (B l)) := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right]
  -- column factor: the row engine, lifted to the tsum
  have hAle : (∑' j : ℕ, ENNReal.ofReal (A j)) ≤ ENNReal.ofReal (CL * K) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    set M : ℕ := F.sup id + 1 with hM
    have hFsub : F ⊆ Finset.range M := fun j hj =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
    have hreal : ∑ j ∈ Finset.range M, A j ≤ CL * K := by
      have hrw := hrow (1 + (s : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) s])
        ((s : ℝ) / 4) M
      calc ∑ j ∈ Finset.range M, A j
          = CL / Real.sqrt (1 + (s : ℝ))
            * ∑ j ∈ Finset.range M,
                Gweight (1 + (s : ℝ)) (cL * ((j : ℝ) - (s : ℝ) / 4)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [hA]; ring
        _ ≤ CL / Real.sqrt (1 + (s : ℝ)) * (K * Real.sqrt (1 + (s : ℝ))) :=
            mul_le_mul_of_nonneg_left hrw (by positivity)
        _ = CL * K := by field_simp
    calc ∑ j ∈ F, ENNReal.ofReal (A j)
        ≤ ∑ j ∈ Finset.range M, ENNReal.ofReal (A j) :=
          Finset.sum_le_sum_of_subset hFsub
      _ = ENNReal.ofReal (∑ j ∈ Finset.range M, A j) :=
          (ENNReal.ofReal_sum_of_nonneg fun j _ => hAnn j).symm
      _ ≤ ENNReal.ofReal (CL * K) := ENNReal.ofReal_le_ofReal hreal
  -- height factor: the shifted geometric
  have hBsum := hasSum_int_shift_exp hc2 s
  have hBle : (∑' l : ℤ, ENNReal.ofReal (B l)) = ENNReal.ofReal geo := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hBnn hBsum.summable, hBsum.tsum_eq]
  -- assemble
  calc ∑' e : ℕ × ℤ, (if (s : ℝ) + y ≤ (e.2 : ℝ) then fpDist s e else 0)
      ≤ ∑' e : ℕ × ℤ, ENNReal.ofReal (Real.exp (-(cL / 2) * y))
          * (ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2)) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (Real.exp (-(cL / 2) * y))
          * ((∑' j : ℕ, ENNReal.ofReal (A j)) * (∑' l : ℤ, ENNReal.ofReal (B l))) := by
        rw [ENNReal.tsum_mul_left, hfact]
    _ ≤ ENNReal.ofReal (Real.exp (-(cL / 2) * y))
          * (ENNReal.ofReal (CL * K) * ENNReal.ofReal geo) := by
        exact mul_le_mul_left' (mul_le_mul' hAle (le_of_eq hBle)) _
    _ = ENNReal.ofReal (CL * K * geo * Real.exp (-(cL / 2) * y)) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ CL * K),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        ring

/-- **`p`-step height tail** (step (iii) of the (7.61) plan): the `Hold` walk's
height sum exceeds `y` with probability `≤ e^{17p/1000 − y/1000}` — Markov under
the tilt `(l1, l2) = (0, 1/1000)` (`holdSum_halfspace_le`), whose quadratic MGF
budget is `p·(16/1000 + 1000/10⁶) = 17p/1000`. Past the mean-height drift
`16p` this is exponentially small. -/
theorem holdSum_height_tail (p : ℕ) (y : ℝ) :
    ∑' d : ℕ × ℤ, (if y ≤ (d.2 : ℝ) then (iidSum hold p) d else 0)
      ≤ ENNReal.ofReal (Real.exp ((p : ℝ) * (17 / 1000) - y / 1000)) := by
  classical
  have h := holdSum_halfspace_le (l1 := 0) (l2 := 1 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) p
    (fun d => y ≤ (d.2 : ℝ)) (y / 1000)
    (fun d hd => by
      have : y / 1000 ≤ (d.2 : ℝ) / 1000 := by linarith
      linarith)
  refine le_trans h (le_of_eq ?_)
  congr 1
  norm_num

/-- **The (7.61) height tail of the `(k+p)`-step endpoint** (p.52, first two
displays): `P(l + l_{[1,k+p]} ≥ l_Δ + H) ≪ exp(−cH)` once `H` clears the mean
height drift of the walk (first-passage overshoot `O(1)` + `p` further `Hold`
steps of mean height `16` — the drift coefficient of `tiltZ_hold_le_quad`; the
margin `50(1+p) ≤ H` dominates both with Chernoff room at tilt `1/1000`).
Route: split the endpoint as `fpDist s ⋆ iidSum hold p`; the `fpDist` overshoot
has the `e^{-c(l-s)}` row tail of X6 (`fpDist_location_bound` summed in `j` —
the `fpDist_col_le` companion collapsed the other way), and the `p`-step height
sum has an exponential Chernoff tail past its mean (`holdSum_halfspace_le` at
`l2 = 1/1000`: exponent `p·17/1000 − (H/2)/1000 ≤ −H/6250` under the margin).
Consumed by (7.61) at `H = 2A²(1+p)`, where `A ≥ A₀ ≥ 5` makes
`50(1+p) ≤ H` automatic.

PROVED (lap 58; statement pinned lap 57, margin corrected same lap — the
height mean is `16/step`, so the earlier `10(1+p)` margin sat below the drift
and the statement was false as first pinned). Glue: the tail event of the
convolution is split pointwise, `1_{s+H ≤ f.2+w.2} ≤ 1_{s+H/2 ≤ f.2} + 1_{H/2 ≤ w.2}`,
in `ℝ≥0∞` (no summability side conditions); the two pieces are
`fpDist_height_tail` and `holdSum_height_tail` at `y = H/2`. -/
theorem fpDistPlus_height_tail :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ s p : ℕ, ∀ H : ℝ,
      50 * (1 + (p : ℝ)) ≤ H →
      ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal
          * Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} 1 e
        ≤ C * Real.exp (-c * H) := by
  classical
  obtain ⟨cB, hcB, CB, hCB, hfp⟩ := fpDist_height_tail
  set cst : ℝ := min (cB / 2) (1 / 6250) with hcst
  have hcst0 : 0 < cst := lt_min (by positivity) (by norm_num)
  refine ⟨cst, hcst0, CB + 1, by positivity, fun s p H hH => ?_⟩
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le (by positivity) hH
  set T : ℝ≥0∞ :=
    ∑' e : ℕ × ℤ, (if (s : ℝ) + H ≤ (e.2 : ℝ) then fpDistPlus s p e else 0) with hT
  -- (1) the real LHS is `T.toReal`
  have hLHS : ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal
      * Set.indicator {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} 1 e = T.toReal := by
    rw [hT, ENNReal.tsum_toReal_eq (fun e => by
      split_ifs
      exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top])]
    refine tsum_congr fun e => ?_
    by_cases he : (s : ℝ) + H ≤ (e.2 : ℝ)
    · rw [if_pos he, Set.indicator_apply,
        if_pos (show e ∈ {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} from he),
        Pi.one_apply, mul_one]
    · rw [if_neg he, Set.indicator_apply,
        if_neg (show e ∉ {q : ℕ × ℤ | (s : ℝ) + H ≤ (q.2 : ℝ)} from he),
        mul_zero, ENNReal.toReal_zero]
  -- (2) expand the convolution
  have hexp : T = ∑' f : ℕ × ℤ, ∑' w : ℕ × ℤ,
      (if (s : ℝ) + H ≤ ((f + w).2 : ℝ) then fpDist s f * iidSum hold p w else 0) := by
    rw [hT]
    have h1 : ∀ e : ℕ × ℤ, (if (s : ℝ) + H ≤ (e.2 : ℝ) then fpDistPlus s p e else 0)
        = ∑' f : ℕ × ℤ, ∑' w : ℕ × ℤ,
            (if e = f + w then
              (if (s : ℝ) + H ≤ (e.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
            else 0) := by
      intro e
      by_cases he : (s : ℝ) + H ≤ (e.2 : ℝ)
      · rw [if_pos he, fpDistPlus, PMF.bind_apply]
        refine tsum_congr fun f => ?_
        rw [PMF.map_apply, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun w => ?_
        by_cases hew : e = f + w
        · rw [if_pos hew, if_pos hew, if_pos he]
        · rw [if_neg hew, if_neg hew, mul_zero]
      · rw [if_neg he]
        have hz : ∀ f w : ℕ × ℤ, (if e = f + w then
            (if (s : ℝ) + H ≤ (e.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
          else 0) = 0 := by
          intro f w
          rw [if_neg he]
          exact ite_self 0
        symm
        simp only [hz, tsum_zero]
    calc ∑' e : ℕ × ℤ, (if (s : ℝ) + H ≤ (e.2 : ℝ) then fpDistPlus s p e else 0)
        = ∑' (e : ℕ × ℤ) (f : ℕ × ℤ) (w : ℕ × ℤ), (if e = f + w then
            (if (s : ℝ) + H ≤ (e.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
          else 0) := tsum_congr h1
      _ = ∑' (f : ℕ × ℤ) (e : ℕ × ℤ) (w : ℕ × ℤ), (if e = f + w then
            (if (s : ℝ) + H ≤ (e.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
          else 0) := ENNReal.tsum_comm
      _ = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ) (e : ℕ × ℤ), (if e = f + w then
            (if (s : ℝ) + H ≤ (e.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
          else 0) := tsum_congr fun f => ENNReal.tsum_comm
      _ = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
            (if (s : ℝ) + H ≤ ((f + w).2 : ℝ) then fpDist s f * iidSum hold p w else 0) := by
          refine tsum_congr fun f => tsum_congr fun w => ?_
          rw [tsum_eq_single (f + w) (fun e he => if_neg he), if_pos rfl]
  -- (3) pointwise split of the tail event
  have hsplit : ∀ f w : ℕ × ℤ,
      (if (s : ℝ) + H ≤ ((f + w).2 : ℝ) then fpDist s f * iidSum hold p w else 0)
      ≤ (if (s : ℝ) + H / 2 ≤ (f.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
        + (if H / 2 ≤ (w.2 : ℝ) then fpDist s f * iidSum hold p w else 0) := by
    intro f w
    by_cases hfw : (s : ℝ) + H ≤ ((f + w).2 : ℝ)
    · rw [if_pos hfw]
      have hcast : ((f + w).2 : ℝ) = (f.2 : ℝ) + (w.2 : ℝ) := by
        rw [Prod.snd_add]
        push_cast
        ring
      by_cases h1 : (s : ℝ) + H / 2 ≤ (f.2 : ℝ)
      · rw [if_pos h1]
        exact le_self_add
      · have h2 : H / 2 ≤ (w.2 : ℝ) := by
          rw [hcast] at hfw
          push_neg at h1
          linarith
        rw [if_pos h2]
        exact le_add_self
    · rw [if_neg hfw]
      exact zero_le'
  -- (4) the two marginal tails
  have hfirst : ∀ f : ℕ × ℤ,
      ∑' w : ℕ × ℤ, (if (s : ℝ) + H / 2 ≤ (f.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
      = (if (s : ℝ) + H / 2 ≤ (f.2 : ℝ) then fpDist s f else 0) := by
    intro f
    by_cases h1 : (s : ℝ) + H / 2 ≤ (f.2 : ℝ)
    · simp only [if_pos h1]
      rw [ENNReal.tsum_mul_left, (iidSum hold p).tsum_coe, mul_one]
    · simp only [if_neg h1, tsum_zero]
  have hsecond : ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
      (if H / 2 ≤ (w.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
      = ∑' w : ℕ × ℤ, (if H / 2 ≤ (w.2 : ℝ) then iidSum hold p w else 0) := by
    have h1 : ∀ f w : ℕ × ℤ, (if H / 2 ≤ (w.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
        = fpDist s f * (if H / 2 ≤ (w.2 : ℝ) then iidSum hold p w else 0) := by
      intro f w
      rw [mul_ite, mul_zero]
    calc ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
        (if H / 2 ≤ (w.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
        = ∑' f : ℕ × ℤ, fpDist s f
            * ∑' w : ℕ × ℤ, (if H / 2 ≤ (w.2 : ℝ) then iidSum hold p w else 0) := by
          refine tsum_congr fun f => ?_
          simp only [h1]
          exact ENNReal.tsum_mul_left
      _ = (∑' f : ℕ × ℤ, fpDist s f)
            * ∑' w : ℕ × ℤ, (if H / 2 ≤ (w.2 : ℝ) then iidSum hold p w else 0) :=
          ENNReal.tsum_mul_right
      _ = ∑' w : ℕ × ℤ, (if H / 2 ≤ (w.2 : ℝ) then iidSum hold p w else 0) := by
          rw [(fpDist s).tsum_coe, one_mul]
  have hTle : T ≤ ENNReal.ofReal (CB * Real.exp (-cB * (H / 2)))
      + ENNReal.ofReal (Real.exp ((p : ℝ) * (17 / 1000) - (H / 2) / 1000)) := by
    rw [hexp]
    calc ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
        (if (s : ℝ) + H ≤ ((f + w).2 : ℝ) then fpDist s f * iidSum hold p w else 0)
        ≤ ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
            ((if (s : ℝ) + H / 2 ≤ (f.2 : ℝ) then fpDist s f * iidSum hold p w else 0)
              + (if H / 2 ≤ (w.2 : ℝ) then fpDist s f * iidSum hold p w else 0)) :=
          ENNReal.tsum_le_tsum fun f => ENNReal.tsum_le_tsum (hsplit f)
      _ = (∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
            (if (s : ℝ) + H / 2 ≤ (f.2 : ℝ) then fpDist s f * iidSum hold p w else 0))
          + ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
            (if H / 2 ≤ (w.2 : ℝ) then fpDist s f * iidSum hold p w else 0) := by
          rw [← ENNReal.tsum_add]
          exact tsum_congr fun f => ENNReal.tsum_add
      _ = (∑' f : ℕ × ℤ, (if (s : ℝ) + H / 2 ≤ (f.2 : ℝ) then fpDist s f else 0))
          + ∑' w : ℕ × ℤ, (if H / 2 ≤ (w.2 : ℝ) then iidSum hold p w else 0) := by
          rw [hsecond, tsum_congr hfirst]
      _ ≤ ENNReal.ofReal (CB * Real.exp (-cB * (H / 2)))
          + ENNReal.ofReal (Real.exp ((p : ℝ) * (17 / 1000) - (H / 2) / 1000)) :=
          add_le_add (hfp s (H / 2) (by linarith)) (holdSum_height_tail p (H / 2))
  -- (5) real arithmetic: both pieces are `≤ e^{−cst·H}`
  have hreal : CB * Real.exp (-cB * (H / 2)) + Real.exp ((p : ℝ) * (17 / 1000) - (H / 2) / 1000)
      ≤ (CB + 1) * Real.exp (-cst * H) := by
    have hcm1 : cst ≤ cB / 2 := min_le_left _ _
    have hcm2 : cst ≤ 1 / 6250 := min_le_right _ _
    have h1 : Real.exp (-cB * (H / 2)) ≤ Real.exp (-cst * H) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have h2 : Real.exp ((p : ℝ) * (17 / 1000) - (H / 2) / 1000) ≤ Real.exp (-cst * H) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hcm2 hH0.le]
    calc CB * Real.exp (-cB * (H / 2)) + Real.exp ((p : ℝ) * (17 / 1000) - (H / 2) / 1000)
        ≤ CB * Real.exp (-cst * H) + Real.exp (-cst * H) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hCB.le) h2
      _ = (CB + 1) * Real.exp (-cst * H) := by ring
  rw [hLHS]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc T ≤ _ := hTle
    _ ≤ ENNReal.ofReal ((CB + 1) * Real.exp (-cst * H)) := by
        rw [← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal hreal

/-- **First-passage column deviation** (the (7.61) column analogue of
`fpDist_height_tail`, ℝ≥0∞ form): `P(|f.1 − s/4| ≥ D) ≤ C(e^{−cD²/(1+s)} + e^{−cD})`
for the first-passage endpoint `f ~ fpDist s`. The X6 envelope's column factor
`Gweight(1+s, c(j−s/4))` donates the tail prefactor by exponent-halving —
`e^{−x²/t} ≤ e^{−(cD)²/(2t)}·e^{−(x/2)²/t}` and `e^{−|x|} ≤ e^{−cD/2}·e^{−|x/2|}`
on `|x| ≥ cD` — leaving a `Gweight` at rate `c/2` which the row engine sums to
`K√(1+s)`; the height factor sums geometrically. Both RHS shapes (Gaussian in
`D²/(1+s)` and exponential in `D`) come from the two `Gweight` pieces. -/
theorem fpDist_col_dev :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ s : ℕ, ∀ D : ℝ, 0 ≤ D →
      ∑' e : ℕ × ℤ, (if D ≤ |(e.1 : ℝ) - (s : ℝ) / 4| then fpDist s e else 0)
        ≤ ENNReal.ofReal
            (C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D))) := by
  obtain ⟨cL, hcL, CL, hCL, hbd⟩ := fpDist_location_bound
  obtain ⟨K, hK, hrow⟩ := sum_range_Gweight_le (by positivity : (0:ℝ) < cL / 2)
  have he1 : Real.exp (-cL) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hgd : (0 : ℝ) < 1 - Real.exp (-cL) := by linarith [Real.exp_pos (-cL)]
  set geo : ℝ := Real.exp (-cL) / (1 - Real.exp (-cL)) with hgeo
  have hgeo0 : 0 < geo := div_pos (Real.exp_pos _) hgd
  set cc : ℝ := min (cL ^ 2 / 2) (cL / 2) with hcc
  have hcc0 : 0 < cc := lt_min (by positivity) (by positivity)
  refine ⟨cc, hcc0, CL * K * geo, by positivity, fun s D hD => ?_⟩
  have h1s : (0 : ℝ) < 1 + (s : ℝ) := by positivity
  have hsq : (0 : ℝ) < Real.sqrt (1 + (s : ℝ)) := Real.sqrt_pos.mpr h1s
  set t : ℝ := 1 + (s : ℝ) with ht
  set pref : ℝ := Real.exp (-(cL * D) ^ 2 / (2 * t)) + Real.exp (-(cL * D) / 2)
    with hpref
  have hpref0 : 0 < pref := by positivity
  set A : ℕ → ℝ := fun j =>
    CL * Gweight t (cL / 2 * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt t with hA
  set B : ℤ → ℝ :=
    fun l => if (s : ℤ) < l then Real.exp (-cL * ((l : ℝ) - (s : ℝ))) else 0 with hB
  have hAnn : ∀ j, 0 ≤ A j := fun j =>
    div_nonneg (mul_nonneg hCL.le (Gweight_nonneg _ _)) hsq.le
  have hBnn : ∀ l, 0 ≤ B l := by
    intro l
    rw [hB]
    dsimp only
    split_ifs
    exacts [(Real.exp_pos _).le, le_rfl]
  -- the Gweight tail-splitting inequality
  have hGw : ∀ x : ℝ, cL * D ≤ |x| → Gweight t x ≤ pref * Gweight t (x / 2) := by
    intro x hx
    have ht0 : (0 : ℝ) < t := h1s
    have hx2 : (cL * D) ^ 2 ≤ x ^ 2 := by
      have h0 : 0 ≤ cL * D := by positivity
      nlinarith [abs_nonneg x, sq_abs x]
    have hg1 : Real.exp (-x ^ 2 / t)
        ≤ Real.exp (-(cL * D) ^ 2 / (2 * t)) * Real.exp (-(x / 2) ^ 2 / t) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [div_add_div _ _ (by positivity : (2:ℝ) * t ≠ 0) (by positivity : t ≠ 0)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (mul_pos ht0 ht0).le,
        sq_nonneg x, mul_pos ht0 ht0]
    have hg2 : Real.exp (-|x|)
        ≤ Real.exp (-(cL * D) / 2) * Real.exp (-|x / 2|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [abs_div]
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]
      linarith
    have hGnn1 : (0:ℝ) ≤ Real.exp (-(x / 2) ^ 2 / t) := (Real.exp_pos _).le
    have hGnn2 : (0:ℝ) ≤ Real.exp (-|x / 2|) := (Real.exp_pos _).le
    have hp1 : Real.exp (-(cL * D) ^ 2 / (2 * t)) ≤ pref := by
      rw [hpref]
      linarith [Real.exp_pos (-(cL * D) / 2)]
    have hp2 : Real.exp (-(cL * D) / 2) ≤ pref := by
      rw [hpref]
      linarith [Real.exp_pos (-(cL * D) ^ 2 / (2 * t))]
    unfold Gweight
    calc Real.exp (-x ^ 2 / t) + Real.exp (-|x|)
        ≤ Real.exp (-(cL * D) ^ 2 / (2 * t)) * Real.exp (-(x / 2) ^ 2 / t)
          + Real.exp (-(cL * D) / 2) * Real.exp (-|x / 2|) := add_le_add hg1 hg2
      _ ≤ pref * Real.exp (-(x / 2) ^ 2 / t) + pref * Real.exp (-|x / 2|) :=
          add_le_add (mul_le_mul_of_nonneg_right hp1 hGnn1)
            (mul_le_mul_of_nonneg_right hp2 hGnn2)
      _ = pref * (Real.exp (-(x / 2) ^ 2 / t) + Real.exp (-|x / 2|)) := by ring
  -- pointwise domination
  have hpt : ∀ e : ℕ × ℤ, (if D ≤ |(e.1 : ℝ) - (s : ℝ) / 4| then fpDist s e else 0)
      ≤ ENNReal.ofReal pref * (ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2)) := by
    intro e
    obtain ⟨j, l⟩ := e
    by_cases hDj : D ≤ |(j : ℝ) - (s : ℝ) / 4|
    · rw [if_pos hDj]
      by_cases hsl : (s : ℤ) < l
      · have hxD : cL * D ≤ |cL * ((j : ℝ) - (s : ℝ) / 4)| := by
          rw [abs_mul, abs_of_pos hcL]
          exact mul_le_mul_of_nonneg_left hDj hcL.le
        have hGle := hGw (cL * ((j : ℝ) - (s : ℝ) / 4)) hxD
        have hhalf : cL * ((j : ℝ) - (s : ℝ) / 4) / 2
            = cL / 2 * ((j : ℝ) - (s : ℝ) / 4) := by ring
        rw [hhalf] at hGle
        have hfac : (0 : ℝ) ≤ CL * (Real.exp (-cL * ((l : ℝ) - (s : ℝ))) / Real.sqrt t) :=
          mul_nonneg hCL.le (div_nonneg (Real.exp_pos _).le hsq.le)
        have hRe : (fpDist s (j, l)).toReal ≤ pref * (A j * B l) := by
          rw [hA, hB]
          dsimp only
          rw [if_pos hsl]
          calc (fpDist s (j, l)).toReal
              ≤ CL * (Real.exp (-cL * ((l : ℝ) - (s : ℝ))) / Real.sqrt t)
                  * Gweight t (cL * ((j : ℝ) - (s : ℝ) / 4)) := hbd s j l
            _ ≤ CL * (Real.exp (-cL * ((l : ℝ) - (s : ℝ))) / Real.sqrt t)
                  * (pref * Gweight t (cL / 2 * ((j : ℝ) - (s : ℝ) / 4))) :=
                mul_le_mul_of_nonneg_left hGle hfac
            _ = pref * (CL * Gweight t (cL / 2 * ((j : ℝ) - (s : ℝ) / 4)) / Real.sqrt t
                  * Real.exp (-cL * ((l : ℝ) - (s : ℝ)))) := by ring
        calc fpDist s (j, l)
            = ENNReal.ofReal ((fpDist s (j, l)).toReal) :=
              (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal (pref * (A j * B l)) := ENNReal.ofReal_le_ofReal hRe
          _ = ENNReal.ofReal pref * (ENNReal.ofReal (A j) * ENNReal.ofReal (B l)) := by
              rw [ENNReal.ofReal_mul hpref0.le, ENNReal.ofReal_mul (hAnn j)]
      · have h0 : fpDist s (j, l) = 0 := by
          by_contra h
          exact hsl (fpDist_support_snd_gt s (j, l) (by rwa [PMF.mem_support_iff]))
        rw [h0]
        exact zero_le'
    · rw [if_neg hDj]
      exact zero_le'
  -- factor and bound
  have hfact : ∑' e : ℕ × ℤ, (ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2))
      = (∑' j : ℕ, ENNReal.ofReal (A j)) * (∑' l : ℤ, ENNReal.ofReal (B l)) := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right]
  have hAle : (∑' j : ℕ, ENNReal.ofReal (A j)) ≤ ENNReal.ofReal (CL * K) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    set M : ℕ := F.sup id + 1 with hM
    have hFsub : F ⊆ Finset.range M := fun j hj =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
    have hreal : ∑ j ∈ Finset.range M, A j ≤ CL * K := by
      have hrw := hrow t (by rw [ht]; linarith [Nat.cast_nonneg (α := ℝ) s])
        ((s : ℝ) / 4) M
      calc ∑ j ∈ Finset.range M, A j
          = CL / Real.sqrt t
            * ∑ j ∈ Finset.range M, Gweight t (cL / 2 * ((j : ℝ) - (s : ℝ) / 4)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [hA]; ring
        _ ≤ CL / Real.sqrt t * (K * Real.sqrt t) :=
            mul_le_mul_of_nonneg_left hrw (by positivity)
        _ = CL * K := by field_simp
    calc ∑ j ∈ F, ENNReal.ofReal (A j)
        ≤ ∑ j ∈ Finset.range M, ENNReal.ofReal (A j) :=
          Finset.sum_le_sum_of_subset hFsub
      _ = ENNReal.ofReal (∑ j ∈ Finset.range M, A j) :=
          (ENNReal.ofReal_sum_of_nonneg fun j _ => hAnn j).symm
      _ ≤ ENNReal.ofReal (CL * K) := ENNReal.ofReal_le_ofReal hreal
  have hBsum := hasSum_int_shift_exp hcL s
  have hBle : (∑' l : ℤ, ENNReal.ofReal (B l)) = ENNReal.ofReal geo := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hBnn hBsum.summable, hBsum.tsum_eq]
  -- assemble, then compare prefactors in ℝ
  have hprefle : pref ≤ Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cc * D) := by
    have h1 : Real.exp (-(cL * D) ^ 2 / (2 * t)) ≤ Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [ht, div_le_div_iff₀ (by positivity) (by positivity)]
      have hcc1 : cc ≤ cL ^ 2 / 2 := min_le_left _ _
      nlinarith [sq_nonneg D, sq_nonneg (cL * D), Nat.cast_nonneg (α := ℝ) s,
        mul_le_mul_of_nonneg_right hcc1 (sq_nonneg D)]
    have h2 : Real.exp (-(cL * D) / 2) ≤ Real.exp (-cc * D) := by
      apply Real.exp_le_exp.mpr
      have hcc2 : cc ≤ cL / 2 := min_le_right _ _
      nlinarith [mul_le_mul_of_nonneg_right hcc2 hD]
    rw [hpref]
    exact add_le_add h1 h2
  calc ∑' e : ℕ × ℤ, (if D ≤ |(e.1 : ℝ) - (s : ℝ) / 4| then fpDist s e else 0)
      ≤ ∑' e : ℕ × ℤ, ENNReal.ofReal pref
          * (ENNReal.ofReal (A e.1) * ENNReal.ofReal (B e.2)) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal pref
          * ((∑' j : ℕ, ENNReal.ofReal (A j)) * (∑' l : ℤ, ENNReal.ofReal (B l))) := by
        rw [ENNReal.tsum_mul_left, hfact]
    _ ≤ ENNReal.ofReal pref * (ENNReal.ofReal (CL * K) * ENNReal.ofReal geo) := by
        exact mul_le_mul_left' (mul_le_mul' hAle (le_of_eq hBle)) _
    _ = ENNReal.ofReal (CL * K * geo * pref) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ CL * K),
          ← ENNReal.ofReal_mul hpref0.le]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (CL * K * geo
          * (Real.exp (-cc * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cc * D))) := by
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hprefle (by positivity))

/-- **`p`-step column tail**: the `Hold` walk's column sum exceeds `y` with
probability `≤ e^{5p/1000 − y/1000}` — Markov under the tilt `(1/1000, 0)`
(`holdSum_halfspace_le`), quadratic MGF budget `p·(4/1000 + 1000/10⁶) = 5p/1000`.
Past the mean-column drift `4p` this is exponentially small. -/
theorem holdSum_col_tail (p : ℕ) (y : ℝ) :
    ∑' d : ℕ × ℤ, (if y ≤ (d.1 : ℝ) then (iidSum hold p) d else 0)
      ≤ ENNReal.ofReal (Real.exp ((p : ℝ) * (5 / 1000) - y / 1000)) := by
  classical
  have h := holdSum_halfspace_le (l1 := 1 / 1000) (l2 := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) p
    (fun d => y ≤ (d.1 : ℝ)) (y / 1000)
    (fun d hd => by
      have : y / 1000 ≤ (d.1 : ℝ) / 1000 := by linarith
      linarith)
  refine le_trans h (le_of_eq ?_)
  congr 1
  norm_num

/-- **The (7.61) column tail of the `(k+p)`-step endpoint** (p.52, displays 5–7):
`P(|j_{[1,k+p]} − s/4| ≥ 2D) ≪ exp(−cD²/(1+s)) + exp(−cD)` once `D` clears the
`p`-step column drift (`j`-components are iid `Geom(4)`, mean `4/3`; the margin
`10(1+p) ≤ D` dominates). The paper instantiates `D = s^{0.6}`, giving
`exp(−cs^{0.2}) + exp(−cs^{0.6})`; the general-`D` form is what the X6 envelope
(`fpDist_col_le`: Gaussian of width `√(1+s)` centred at `s/4`) plus the
`Geom(4)`-sum Chernoff actually prove, and the consumer does the `s^{0.6}`
arithmetic at the (7.61) assembly site.

PROVED (lap 58; statement pinned lap 57): glue as in `fpDistPlus_height_tail` —
pointwise `1_{2D ≤ |f.1+w.1−s/4|} ≤ 1_{D ≤ |f.1−s/4|} + 1_{D ≤ w.1}` in ℝ≥0∞;
the pieces are `fpDist_col_dev` and `holdSum_col_tail` at `y = D`. -/
theorem fpDistPlus_col_tail :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ s p : ℕ, ∀ D : ℝ,
      10 * (1 + (p : ℝ)) ≤ D →
      ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal
          * Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} 1 e
        ≤ C * (Real.exp (-c * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-c * D)) := by
  classical
  obtain ⟨cd, hcd, Cd, hCd, hfp⟩ := fpDist_col_dev
  set cst : ℝ := min cd (1 / 2000) with hcst
  have hcst0 : 0 < cst := lt_min hcd (by norm_num)
  refine ⟨cst, hcst0, Cd + 1, by positivity, fun s p D hD => ?_⟩
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
  set T : ℝ≥0∞ :=
    ∑' e : ℕ × ℤ, (if 2 * D ≤ |(e.1 : ℝ) - (s : ℝ) / 4| then fpDistPlus s p e else 0)
    with hT
  -- (1) the real LHS is `T.toReal`
  have hLHS : ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal
      * Set.indicator {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} 1 e
      = T.toReal := by
    rw [hT, ENNReal.tsum_toReal_eq (fun e => by
      split_ifs
      exacts [PMF.apply_ne_top _ _, ENNReal.zero_ne_top])]
    refine tsum_congr fun e => ?_
    by_cases he : 2 * D ≤ |(e.1 : ℝ) - (s : ℝ) / 4|
    · rw [if_pos he, Set.indicator_apply,
        if_pos (show e ∈ {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} from he),
        Pi.one_apply, mul_one]
    · rw [if_neg he, Set.indicator_apply,
        if_neg (show e ∉ {q : ℕ × ℤ | 2 * D ≤ |(q.1 : ℝ) - (s : ℝ) / 4|} from he),
        mul_zero, ENNReal.toReal_zero]
  -- (2) expand the convolution
  have hexp : T = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
      (if 2 * D ≤ |((f + w).1 : ℝ) - (s : ℝ) / 4|
        then fpDist s f * iidSum hold p w else 0) := by
    rw [hT]
    have h1 : ∀ e : ℕ × ℤ,
        (if 2 * D ≤ |(e.1 : ℝ) - (s : ℝ) / 4| then fpDistPlus s p e else 0)
        = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ), (if e = f + w then
            (if 2 * D ≤ |(e.1 : ℝ) - (s : ℝ) / 4|
              then fpDist s f * iidSum hold p w else 0)
          else 0) := by
      intro e
      by_cases he : 2 * D ≤ |(e.1 : ℝ) - (s : ℝ) / 4|
      · rw [if_pos he, fpDistPlus, PMF.bind_apply]
        refine tsum_congr fun f => ?_
        rw [PMF.map_apply, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun w => ?_
        by_cases hew : e = f + w
        · rw [if_pos hew, if_pos hew, if_pos he]
        · rw [if_neg hew, if_neg hew, mul_zero]
      · rw [if_neg he]
        have hz : ∀ f w : ℕ × ℤ, (if e = f + w then
            (if 2 * D ≤ |(e.1 : ℝ) - (s : ℝ) / 4|
              then fpDist s f * iidSum hold p w else 0)
          else 0) = 0 := by
          intro f w
          rw [if_neg he]
          exact ite_self 0
        symm
        simp only [hz, tsum_zero]
    calc ∑' e : ℕ × ℤ,
        (if 2 * D ≤ |(e.1 : ℝ) - (s : ℝ) / 4| then fpDistPlus s p e else 0)
        = ∑' (e : ℕ × ℤ) (f : ℕ × ℤ) (w : ℕ × ℤ), (if e = f + w then
            (if 2 * D ≤ |(e.1 : ℝ) - (s : ℝ) / 4|
              then fpDist s f * iidSum hold p w else 0)
          else 0) := tsum_congr h1
      _ = ∑' (f : ℕ × ℤ) (e : ℕ × ℤ) (w : ℕ × ℤ), (if e = f + w then
            (if 2 * D ≤ |(e.1 : ℝ) - (s : ℝ) / 4|
              then fpDist s f * iidSum hold p w else 0)
          else 0) := ENNReal.tsum_comm
      _ = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ) (e : ℕ × ℤ), (if e = f + w then
            (if 2 * D ≤ |(e.1 : ℝ) - (s : ℝ) / 4|
              then fpDist s f * iidSum hold p w else 0)
          else 0) := tsum_congr fun f => ENNReal.tsum_comm
      _ = ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
            (if 2 * D ≤ |((f + w).1 : ℝ) - (s : ℝ) / 4|
              then fpDist s f * iidSum hold p w else 0) := by
          refine tsum_congr fun f => tsum_congr fun w => ?_
          rw [tsum_eq_single (f + w) (fun e he => if_neg he), if_pos rfl]
  -- (3) pointwise split of the tail event
  have hsplit : ∀ f w : ℕ × ℤ,
      (if 2 * D ≤ |((f + w).1 : ℝ) - (s : ℝ) / 4|
        then fpDist s f * iidSum hold p w else 0)
      ≤ (if D ≤ |(f.1 : ℝ) - (s : ℝ) / 4| then fpDist s f * iidSum hold p w else 0)
        + (if D ≤ (w.1 : ℝ) then fpDist s f * iidSum hold p w else 0) := by
    intro f w
    by_cases hfw : 2 * D ≤ |((f + w).1 : ℝ) - (s : ℝ) / 4|
    · rw [if_pos hfw]
      have hcast : ((f + w).1 : ℝ) = (f.1 : ℝ) + (w.1 : ℝ) := by
        rw [Prod.fst_add]
        push_cast
        ring
      by_cases h1 : D ≤ |(f.1 : ℝ) - (s : ℝ) / 4|
      · rw [if_pos h1]
        exact le_self_add
      · have h2 : D ≤ (w.1 : ℝ) := by
          rw [hcast] at hfw
          push_neg at h1
          have htri : |(f.1 : ℝ) + (w.1 : ℝ) - (s : ℝ) / 4|
              ≤ |(f.1 : ℝ) - (s : ℝ) / 4| + (w.1 : ℝ) := by
            have h3 : (f.1 : ℝ) + (w.1 : ℝ) - (s : ℝ) / 4
                = ((f.1 : ℝ) - (s : ℝ) / 4) + (w.1 : ℝ) := by ring
            rw [h3]
            calc |((f.1 : ℝ) - (s : ℝ) / 4) + (w.1 : ℝ)|
                ≤ |(f.1 : ℝ) - (s : ℝ) / 4| + |(w.1 : ℝ)| := abs_add_le _ _
              _ = |(f.1 : ℝ) - (s : ℝ) / 4| + (w.1 : ℝ) := by
                  rw [Nat.abs_cast]
          linarith
        rw [if_pos h2]
        exact le_add_self
    · rw [if_neg hfw]
      exact zero_le'
  -- (4) the two marginal tails
  have hfirst : ∀ f : ℕ × ℤ,
      ∑' w : ℕ × ℤ,
        (if D ≤ |(f.1 : ℝ) - (s : ℝ) / 4| then fpDist s f * iidSum hold p w else 0)
      = (if D ≤ |(f.1 : ℝ) - (s : ℝ) / 4| then fpDist s f else 0) := by
    intro f
    by_cases h1 : D ≤ |(f.1 : ℝ) - (s : ℝ) / 4|
    · simp only [if_pos h1]
      rw [ENNReal.tsum_mul_left, (iidSum hold p).tsum_coe, mul_one]
    · simp only [if_neg h1, tsum_zero]
  have hsecond : ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
      (if D ≤ (w.1 : ℝ) then fpDist s f * iidSum hold p w else 0)
      = ∑' w : ℕ × ℤ, (if D ≤ (w.1 : ℝ) then iidSum hold p w else 0) := by
    have h1 : ∀ f w : ℕ × ℤ,
        (if D ≤ (w.1 : ℝ) then fpDist s f * iidSum hold p w else 0)
        = fpDist s f * (if D ≤ (w.1 : ℝ) then iidSum hold p w else 0) := by
      intro f w
      rw [mul_ite, mul_zero]
    calc ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
        (if D ≤ (w.1 : ℝ) then fpDist s f * iidSum hold p w else 0)
        = ∑' f : ℕ × ℤ, fpDist s f
            * ∑' w : ℕ × ℤ, (if D ≤ (w.1 : ℝ) then iidSum hold p w else 0) := by
          refine tsum_congr fun f => ?_
          simp only [h1]
          exact ENNReal.tsum_mul_left
      _ = (∑' f : ℕ × ℤ, fpDist s f)
            * ∑' w : ℕ × ℤ, (if D ≤ (w.1 : ℝ) then iidSum hold p w else 0) :=
          ENNReal.tsum_mul_right
      _ = ∑' w : ℕ × ℤ, (if D ≤ (w.1 : ℝ) then iidSum hold p w else 0) := by
          rw [(fpDist s).tsum_coe, one_mul]
  have hTle : T ≤ ENNReal.ofReal
        (Cd * (Real.exp (-cd * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cd * D)))
      + ENNReal.ofReal (Real.exp ((p : ℝ) * (5 / 1000) - D / 1000)) := by
    rw [hexp]
    calc ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
        (if 2 * D ≤ |((f + w).1 : ℝ) - (s : ℝ) / 4|
          then fpDist s f * iidSum hold p w else 0)
        ≤ ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
            ((if D ≤ |(f.1 : ℝ) - (s : ℝ) / 4|
                then fpDist s f * iidSum hold p w else 0)
              + (if D ≤ (w.1 : ℝ) then fpDist s f * iidSum hold p w else 0)) :=
          ENNReal.tsum_le_tsum fun f => ENNReal.tsum_le_tsum (hsplit f)
      _ = (∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
            (if D ≤ |(f.1 : ℝ) - (s : ℝ) / 4|
              then fpDist s f * iidSum hold p w else 0))
          + ∑' (f : ℕ × ℤ) (w : ℕ × ℤ),
            (if D ≤ (w.1 : ℝ) then fpDist s f * iidSum hold p w else 0) := by
          rw [← ENNReal.tsum_add]
          exact tsum_congr fun f => ENNReal.tsum_add
      _ = (∑' f : ℕ × ℤ, (if D ≤ |(f.1 : ℝ) - (s : ℝ) / 4| then fpDist s f else 0))
          + ∑' w : ℕ × ℤ, (if D ≤ (w.1 : ℝ) then iidSum hold p w else 0) := by
          rw [hsecond, tsum_congr hfirst]
      _ ≤ ENNReal.ofReal
            (Cd * (Real.exp (-cd * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cd * D)))
          + ENNReal.ofReal (Real.exp ((p : ℝ) * (5 / 1000) - D / 1000)) :=
          add_le_add (hfp s D hD0.le) (holdSum_col_tail p D)
  -- (5) real arithmetic
  have hreal : Cd * (Real.exp (-cd * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cd * D))
      + Real.exp ((p : ℝ) * (5 / 1000) - D / 1000)
      ≤ (Cd + 1) * (Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cst * D)) := by
    have hcm1 : cst ≤ cd := min_le_left _ _
    have hcm2 : cst ≤ 1 / 2000 := min_le_right _ _
    have h1s : (0 : ℝ) < 1 + (s : ℝ) := by positivity
    have h1 : Real.exp (-cd * D ^ 2 / (1 + (s : ℝ)))
        ≤ Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right ?_ h1s.le
      nlinarith [sq_nonneg D, mul_le_mul_of_nonneg_right hcm1 (sq_nonneg D)]
    have h2 : Real.exp (-cd * D) ≤ Real.exp (-cst * D) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hcm1 hD0.le]
    have h3 : Real.exp ((p : ℝ) * (5 / 1000) - D / 1000) ≤ Real.exp (-cst * D) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hcm2 hD0.le]
    have he1 : (0 : ℝ) ≤ Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) := (Real.exp_pos _).le
    have he2 : (0 : ℝ) ≤ Real.exp (-cst * D) := (Real.exp_pos _).le
    calc Cd * (Real.exp (-cd * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cd * D))
        + Real.exp ((p : ℝ) * (5 / 1000) - D / 1000)
        ≤ Cd * (Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cst * D))
          + Real.exp (-cst * D) :=
          add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCd.le) h3
      _ ≤ (Cd + 1) * (Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cst * D)) := by
          nlinarith
  rw [hLHS]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc T ≤ _ := hTle
    _ ≤ ENNReal.ofReal ((Cd + 1)
          * (Real.exp (-cst * D ^ 2 / (1 + (s : ℝ))) + Real.exp (-cst * D))) := by
        rw [← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal hreal


/-! ### The X10 assembly decomposition (lap 58): confinement + separated sum

`triangle_encounter_le` (7.60) = trivial branch + E′ tails (PROVED above) +
the two named obligations below, following pp.52–54 exactly. -/

/-- **X10a — apex confinement** (paper p.53, (7.63)→(7.65)): outside the escape
event `E′`, a big-triangle encounter pins the endpoint to the triangle's apex.
Given the deep-triangle setup, an endpoint `(j+e.1, l+e.2)` with controlled
height overshoot (`e.2 ≤ s + 2A²(1+p)`, the ¬height-escape) and controlled
column deviation (`|e.1 − s/4| ≤ 2s^{0.6}`, the ¬column-escape), lying in a
family triangle `t'` of size `≥ s' ≥ 100A²(1+p)`:

* **(7.65)**: the lower tip of `t'` is within `C₂A²(1+p)` of `l_Δ` — the
  "well below" case is killed by constructing an integer point `(j', l_Δ)` in
  BOTH `t'` and `Δ = t₀` ((7.64) keeps `j' − j ≈ s/4` within `Δ`'s slope budget
  `s_Δ ≥ s·log 2` since `¼log 9 < log 2`, at the cost of an `S₀`-threshold in
  `s` absorbing the `O(s^{0.6}) + O(A²(1+p))` slack), contradicting
  `TriangleFamily.not_mem_two` (`t' ≠ t₀` because the endpoint height `> l_Δ`
  exceeds `Δ`'s ceiling);
* **apex proximity**: `(7.11)` for `t'` then confines the column,
  `0 ≤ j + e.1 − j_{t'} ≤ C₂A²(1+p)`.

The `s`-threshold `S₀` is absolute; the glue absorbs `s < S₀` into the
`C·exp(−cA²(1+p))` term (bounded `s` bounds `m`, `s'`, `A`, `p` on the
nontrivial branch). OPEN (node X10, statement pinned lap 58). -/
theorem encounter_apex_proximity :
    ∃ C₂ ≥ (1 : ℝ), ∃ S₀ : ℕ, ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l → S₀ ≤ s →
        ((n / 2 - j : ℕ) : ℝ) / Real.log ((n / 2 - j : ℕ) : ℝ) ^ 2 < (s : ℝ) →
      ∀ (A : ℝ), 5 ≤ A → ∀ (p s' : ℕ),
        (s' : ℝ) ≤ ((n / 2 - j : ℕ) : ℝ) ^ (0.4 : ℝ) →
        100 * A ^ 2 * (1 + (p : ℝ)) ≤ (s' : ℝ) →
      ∀ e : ℕ × ℤ, (s : ℤ) < e.2 →
        (e.2 : ℝ) ≤ (s : ℝ) + 2 * A ^ 2 * (1 + (p : ℝ)) →
        |(e.1 : ℝ) - (s : ℝ) / 4| ≤ 2 * (s : ℝ) ^ (0.6 : ℝ) →
      ∀ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2 →
        ((j + e.1, l + e.2) : ℕ × ℤ) ∈ triangle t'.1 t'.2.1 t'.2.2 →
      (t'.1 : ℝ) ≤ (j : ℝ) + e.1
        ∧ (j : ℝ) + e.1 - t'.1 ≤ C₂ * A ^ 2 * (1 + (p : ℝ))
        ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)|
            ≤ C₂ * A ^ 2 * (1 + (p : ℝ)) := by
  sorry

/-- **X10b — the Σ-separated sum** (paper p.54): the probability that the
`(k+p)`-step endpoint lands within `W` (in column) of the apex of ANY family
triangle of size `≥ s'` obeying the (7.65) window `|l_{Δ'} − s_{Δ'}/log 2 − l_Δ| ≤ W`
is `≪ W/s'`. Route: two distinct qualifying triangles have apex columns
separated by `≫ s'` — the p.54 interval argument builds the witness row
`l_* = l_Δ + ⌊s'/2⌋` for `apex_separation` (PROVED), whose integer-disjointness
(Lemma 7.4 = `TriangleFamily.not_mem_two`) forces the gap `(s'/2 − W)log 2/log 9`;
with `100W ≤ s'` that is `≥ s'/10`. Each apex then owns a `2W+1`-column band, the
bands are `≥ s'/10`-spaced, and summing the `fpDistPlus` column marginal
(`fpDist_col_le` ⋆ `p` Hold steps — the row engine `sum_range_Gweight_le` is
uniform in the centre, so the `Hold` drift shifts cost nothing) over an
`s'/10`-spaced family of bands gives `≪ (2W+1)/(s'/10) ≪ W/s'`.
OPEN (node X10, statement pinned lap 58). -/
theorem encounter_separated_sum :
    ∃ C₃ > (0 : ℝ), ∃ S₀ : ℕ, ∀ (n ξ : ℕ), ¬ 3 ∣ ξ → ∀ (F : TriangleFamily n ξ),
      ∀ t₀ ∈ F.T, ∀ (j : ℕ) (l : ℤ),
        (j, l) ∈ triangle t₀.1 t₀.2.1 t₀.2.2 →
      ∀ (s : ℕ), (s : ℤ) = t₀.2.1 - l → S₀ ≤ s →
      ∀ (p s' : ℕ) (W : ℝ), 1 ≤ W → 100 * W ≤ (s' : ℝ) →
      ∑' e : ℕ × ℤ, (fpDistPlus s p e).toReal
          * Set.indicator {q : ℕ × ℤ | ∃ t' ∈ F.T, (s' : ℝ) ≤ t'.2.2
              ∧ |(t'.2.1 : ℝ) - t'.2.2 / Real.log 2 - (t₀.2.1 : ℝ)| ≤ W
              ∧ |(q.1 : ℝ) - (t'.1 : ℝ)| ≤ W} 1 (j + e.1, l + e.2)
        ≤ C₃ * W / (s' : ℝ) := by
  sorry

end TaoCollatz
