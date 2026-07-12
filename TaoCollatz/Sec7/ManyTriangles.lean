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

Paper (7.57): `E exp(−Σ_{p=1}^{t_{min(r,R)}} 1_W((j',l')+v_{[1,p]}) + ε·min(r,R)) ≤
exp(ε)`. This is a functional of the WHOLE walk (the stopping times `t_i` couple all
`v_i`), so — unlike 7.10 — it needs a recursion object, not a marginal. Design in
`PENDING_WORK.md` (lap 51): a budget recursion on `R` over a moving-barrier
first-passage kernel, closed by `fpDist_white_exit` (7.51). Deferred to next lap; the
prerequisite (pairwise triangle disjointness on lattice points, from `F.separated`) is
stated there. NOT pinned here to avoid an unfaithful statement (copy-not-compose).
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
S3, `F.separated` = X3) are theorems. -/
theorem triangle_encounter_le :
    ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (A : ℝ), 0 < A →
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

end TaoCollatz
