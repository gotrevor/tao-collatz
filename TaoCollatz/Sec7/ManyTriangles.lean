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
argument — only finite horizons are ever used. It is also faithful-to-proof: the p.51
induction on `R` conditions on the first block `v₁ … v_{k₁}` (first passage over
`Δ₁`'s top), which the head-peel recursion `encExpect_succ` below finitizes; the
extra finite-horizon branch "`t₁ ≤ T < k₁`" contributes `≤ e^ε·P(branch)` directly
(its `min(r_T,R) = 1` and the empty continuation is `1`), so the closure
`E 1_{r≠0} e^{−1_W(endpoint)} ≤ e^{−ε} P(r≠0)` via `fpDist_white_exit` (7.51) is
unchanged.

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
(`t_{min(r,R)}` semantics of (7.57)). -/
noncomputable def encStep {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ)
    (σ : EncState) (d : ℕ × ℤ) : EncState :=
  if hq : 1 ≤ (σ.pos + d).1 ∧ (σ.pos + d).1 ≤ n / 2
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
noncomputable def encExpect {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ) (ε : ℝ)
    (T : ℕ) (σ : EncState) : ℝ :=
  (hold.iid T).expect fun v => encVal ε R ((List.ofFn v).foldl (encStep F R) σ)

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
theorem encExpect_zero {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ) (ε : ℝ)
    (σ : EncState) : encExpect F R ε 0 σ = encVal ε R σ := by
  rw [encExpect, PMF.expect_iid_zero]
  simp

/-- **The head-peel recursion** (the D6 skeleton of the paper's p.51 conditioning):
one fresh `Hold` step `d` updates the fold state, and the horizon drops by one:

  `encExpect (T+1) σ = Σ'_d hold(d) · encExpect T (encStep σ d)`.

The Lemma 7.9 induction runs on this: at an encounter the barrier resets and the
count increments (spending one of the `R` blocks), and iterating the peel until the
barrier is cleared reconstructs the first-passage law `fpDist` (the path→`fpDist`
bridge, next lap), whose white-exit mass (7.51) closes the induction. -/
theorem encExpect_succ {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (σ : EncState) :
    encExpect F R ε (T + 1) σ
      = ∑' d : ℕ × ℤ, (hold d).toReal * encExpect F R ε T (encStep F R σ d) := by
  -- normalize the integrand into [0,1] to use the iid head-peel
  set c : ℝ := Real.exp (ε * R) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hkey : ∀ (m : ℕ) (τ : EncState),
      encExpect F R ε m τ * c⁻¹
        = (hold.iid m).expect fun v =>
            encVal ε R ((List.ofFn v).foldl (encStep F R) τ) * c⁻¹ := by
    intro m τ
    rw [encExpect, PMF.expect, PMF.expect, ← tsum_mul_right]
    exact tsum_congr fun v => by ring
  have h0 : ∀ (m : ℕ) (τ : EncState) (v : Fin m → ℕ × ℤ),
      0 ≤ encVal ε R ((List.ofFn v).foldl (encStep F R) τ) * c⁻¹ :=
    fun m τ v => mul_nonneg (encVal_pos ε R _).le (by positivity)
  have h1 : ∀ (m : ℕ) (τ : EncState) (v : Fin m → ℕ × ℤ),
      encVal ε R ((List.ofFn v).foldl (encStep F R) τ) * c⁻¹ ≤ 1 := by
    intro m τ v
    rw [← mul_inv_cancel₀ hc0.ne']
    exact mul_le_mul_of_nonneg_right (encVal_le ε hε R _) (by positivity)
  -- the scaled identity
  have hmain : encExpect F R ε (T + 1) σ * c⁻¹
      = ∑' d : ℕ × ℤ, (hold d).toReal
          * (encExpect F R ε T (encStep F R σ d) * c⁻¹) := by
    rw [hkey (T + 1) σ,
      PMF.expect_iid_succ hold T _ (h0 (T + 1) σ) (h1 (T + 1) σ)]
    refine tsum_congr fun d => ?_
    rw [hkey T (encStep F R σ d)]
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
theorem encExpect_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (σ : EncState) :
    encExpect F R ε T σ ≤ Real.exp (ε * R) := by
  have hsum : Summable (fun v : Fin T → ℕ × ℤ => ((hold.iid T) v).toReal) :=
    ENNReal.summable_toReal (by rw [(hold.iid T).tsum_coe]; exact ENNReal.one_ne_top)
  have hle : ∀ v : Fin T → ℕ × ℤ,
      ((hold.iid T) v).toReal * encVal ε R ((List.ofFn v).foldl (encStep F R) σ)
        ≤ ((hold.iid T) v).toReal * Real.exp (ε * R) :=
    fun v => mul_le_mul_of_nonneg_left (encVal_le ε hε R _) ENNReal.toReal_nonneg
  have hsumR : Summable (fun v : Fin T → ℕ × ℤ =>
      ((hold.iid T) v).toReal * Real.exp (ε * R)) := hsum.mul_right _
  have hsumL : Summable (fun v : Fin T → ℕ × ℤ =>
      ((hold.iid T) v).toReal * encVal ε R ((List.ofFn v).foldl (encStep F R) σ)) :=
    Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (encVal_pos ε R _).le) hle hsumR
  calc encExpect F R ε T σ
      ≤ ∑' v : Fin T → ℕ × ℤ, ((hold.iid T) v).toReal * Real.exp (ε * R) :=
        Summable.tsum_le_tsum hle hsumL hsumR
    _ = Real.exp (ε * R) := by
        rw [tsum_mul_right, ← ENNReal.tsum_toReal_eq (fun v => PMF.apply_ne_top _ _),
          (hold.iid T).tsum_coe, ENNReal.toReal_one, one_mul]

/-- `encExpect` is nonnegative (expectation of a positive integrand). -/
theorem encExpect_nonneg {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ) (ε : ℝ)
    (T : ℕ) (σ : EncState) : 0 ≤ encExpect F R ε T σ :=
  tsum_nonneg fun v => mul_nonneg ENNReal.toReal_nonneg (encVal_pos ε R _).le

/-- A fold step never decreases the encounter count. -/
theorem encStep_count_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ)
    (σ : EncState) (d : ℕ × ℤ) : σ.count ≤ (encStep F R σ d).count := by
  unfold encStep
  split <;> dsimp only <;> omega

/-- **Saturated states are frozen** (the `min(r,R)` semantics of (7.57)): once
`count ≥ R`, further steps change neither `banked` nor `min(count,R)`, so the
expectation collapses to the integrand — `encExpect T σ = encVal σ` for every
horizon. This is the `ρ = 0` base of the block induction. -/
theorem encExpect_of_count_ge {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (σ : EncState) (hc : R ≤ σ.count) :
    encExpect F R ε T σ = encVal ε R σ := by
  induction T generalizing σ with
  | zero => exact encExpect_zero F R ε σ
  | succ T IH =>
    rw [encExpect_succ F R ε hε T σ]
    have hval : ∀ d : ℕ × ℤ, encExpect F R ε T (encStep F R σ d) = encVal ε R σ := by
      intro d
      rw [IH (encStep F R σ d) (le_trans hc (encStep_count_le F R σ d))]
      have hmin : min (encStep F R σ d).count R = min σ.count R := by
        have h1 := encStep_count_le F R σ d
        omega
      have hbank : (encStep F R σ d).banked = σ.banked := by
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
theorem encExpect_anti {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) :
    ∀ σ₁ σ₂ : EncState, σ₁.pos = σ₂.pos → σ₁.barrier = σ₂.barrier →
    σ₁.count = σ₂.count → σ₁.cumWhite ≤ σ₂.cumWhite → σ₁.banked ≤ σ₂.banked →
    encExpect F R ε T σ₂ ≤ encExpect F R ε T σ₁ := by
  induction T with
  | zero =>
    intro σ₁ σ₂ hpos hbar hcnt hcw hbk
    rw [encExpect_zero, encExpect_zero, encVal, encVal, hcnt]
    apply Real.exp_le_exp.mpr
    have : (σ₁.banked : ℝ) ≤ (σ₂.banked : ℝ) := Nat.cast_le.mpr hbk
    linarith
  | succ T IH =>
    intro σ₁ σ₂ hpos hbar hcnt hcw hbk
    rw [encExpect_succ F R ε hε T σ₁, encExpect_succ F R ε hε T σ₂]
    -- termwise: one step preserves the coupling
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F R ε T (encStep F R σ₂ d) ≤ encExpect F R ε T (encStep F R σ₁ d) := by
      intro d
      obtain ⟨p₁, b₁, c₁, w₁, k₁⟩ := σ₁
      obtain ⟨p₂, b₂, c₂, w₂, k₂⟩ := σ₂
      simp only at hpos hbar hcnt hcw hbk
      subst hpos hbar hcnt
      simp only [encStep]
      by_cases hq : 1 ≤ (p₁ + d).1 ∧ (p₁ + d).1 ≤ n / 2
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
        0 ≤ (hold d).toReal * encExpect F R ε T (encStep F R σ d) :=
      fun σ d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg F R ε T _)
    have hbound : ∀ (σ : EncState) (d : ℕ × ℤ),
        (hold d).toReal * encExpect F R ε T (encStep F R σ d)
          ≤ (hold d).toReal * Real.exp (ε * R) :=
      fun σ d => mul_le_mul_of_nonneg_left (encExpect_le F R ε hε T _)
        ENNReal.toReal_nonneg
    have hsumE : Summable (fun d : ℕ × ℤ => (hold d).toReal * Real.exp (ε * R)) :=
      (ENNReal.summable_toReal (by rw [hold.tsum_coe]; exact ENNReal.one_ne_top)).mul_right _
    have hsum1 : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * encExpect F R ε T (encStep F R σ₁ d)) :=
      Summable.of_nonneg_of_le (hnn σ₁) (hbound σ₁) hsumE
    have hsum2 : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * encExpect F R ε T (encStep F R σ₂ d)) :=
      Summable.of_nonneg_of_le (hnn σ₂) (hbound σ₂) hsumE
    exact Summable.tsum_le_tsum
      (fun d => mul_le_mul_of_nonneg_left (hstep d) ENNReal.toReal_nonneg) hsum2 hsum1

/-- **Lemma 7.9 — many triangles usually implies many white points** (paper (7.57),
pp.50–51). For the `T`-step renewal walk started at any `(j', l')`, any number of
blocks `R ≥ 1`, and any sufficiently small `ε`:

  `E exp(−Σ_{p=1}^{t_{min(r,R)}} 1_W((j',l')+v_{[1,p]}) + ε·min(r,R)) ≤ exp(ε)`,

uniformly in the horizon `T`, the start `(j',l')`, `R`, and `n, ξ`. The exponent is
read off the encounter fold: `banked = Σ_{p=1}^{t_{min(r,R)}} 1_W`, `count = r`
(see `EncState`/`encStep`; faithfulness deltas — finite horizon, existential ε,
phase-shift — argued in the module docstring).

OPEN (node X9): proof = induction on `R` (paper p.51) over the head-peel
`encExpect_succ`: iterate the peel through the first block (until the barrier
clears); the block's endpoint law is `fpDist` (path→`fpDist` bridge, to be stated
next lap), whose white-exit mass `p₀` (`fpDist_white_exit`, (7.51), X8 kernel) gives
`E 1_{r≠0} exp(−1_W(endpoint)) ≤ (1 − (1−1/e)p₀)·P(r≠0) ≤ e^{−ε}·P(r≠0)` once
`e^ε ≤ (1 − (1−1/e)p₀)⁻¹`, closing `Z(R) ≤ P(r=0) + e^{2ε}·e^{−ε}·P(r≠0) ≤ e^ε`. -/
theorem many_triangles_white :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 100 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
    ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (j' : ℕ) (l' : ℤ),
    encExpect F R ε T (encInit j' l') ≤ Real.exp ε := by
  sorry

end TaoCollatz
