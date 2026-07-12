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
theorem encExpect_normalize {n ξ : ℕ} (F : TriangleFamily n ξ) (R' : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (c w k : ℕ) (T : ℕ) :
    ∀ σ τ : EncState, σ.pos = τ.pos → σ.barrier = τ.barrier →
    σ.count = τ.count + c → σ.cumWhite = τ.cumWhite + w →
    ((σ.banked = k ∧ τ.banked = 0) ∨ σ.banked = τ.banked + w) →
    encExpect F (R' + c) ε T σ
      ≤ Real.exp (ε * c) * max (Real.exp (-(k : ℝ))) (Real.exp (-(w : ℝ)))
        * encExpect F R' ε T τ := by
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
    rw [encExpect_succ F (R' + c) ε hε T σ, encExpect_succ F R' ε hε T τ]
    -- one step preserves the invariant
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F (R' + c) ε T (encStep F (R' + c) σ d)
          ≤ Real.exp (ε * c) * M * encExpect F R' ε T (encStep F R' τ d) := by
      intro d
      obtain ⟨p₁, b₁, c₁, w₁, k₁⟩ := σ
      obtain ⟨p₂, b₂, c₂, w₂, k₂⟩ := τ
      simp only at hpos hbar hcnt hcw
      subst hpos hbar hcnt hcw
      simp only [encStep]
      by_cases hq : 1 ≤ (p₁ + d).1 ∧ (p₁ + d).1 ≤ n / 2
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
        0 ≤ (hold d).toReal * encExpect F (R' + c) ε T (encStep F (R' + c) σ d) :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg _ _ ε T _)
    have hboundσ : ∀ d : ℕ × ℤ,
        (hold d).toReal * encExpect F (R' + c) ε T (encStep F (R' + c) σ d)
          ≤ (hold d).toReal * Real.exp (ε * ((R' + c : ℕ) : ℝ)) :=
      fun d => mul_le_mul_of_nonneg_left (encExpect_le F (R' + c) ε hε T _)
        ENNReal.toReal_nonneg
    have hsumH : Summable (fun d : ℕ × ℤ => (hold d).toReal) :=
      ENNReal.summable_toReal (by rw [hold.tsum_coe]; exact ENNReal.one_ne_top)
    have hsumσ : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * encExpect F (R' + c) ε T (encStep F (R' + c) σ d)) :=
      Summable.of_nonneg_of_le hnnσ hboundσ (hsumH.mul_right _)
    have hboundτ : ∀ d : ℕ × ℤ,
        (hold d).toReal * encExpect F R' ε T (encStep F R' τ d)
          ≤ (hold d).toReal * Real.exp (ε * (R' : ℝ)) :=
      fun d => mul_le_mul_of_nonneg_left (encExpect_le F R' ε hε T _)
        ENNReal.toReal_nonneg
    have hsumτ : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * encExpect F R' ε T (encStep F R' τ d)) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg _ _ ε T _))
        hboundτ (hsumH.mul_right _)
    calc ∑' d : ℕ × ℤ,
          (hold d).toReal * encExpect F (R' + c) ε T (encStep F (R' + c) σ d)
        ≤ ∑' d : ℕ × ℤ, (hold d).toReal
            * (Real.exp (ε * c) * M * encExpect F R' ε T (encStep F R' τ d)) := by
          refine Summable.tsum_le_tsum
            (fun d => mul_le_mul_of_nonneg_left (hstep d) ENNReal.toReal_nonneg)
            hsumσ ?_
          have heq : (fun d : ℕ × ℤ => (hold d).toReal
              * (Real.exp (ε * c) * M * encExpect F R' ε T (encStep F R' τ d)))
              = fun d : ℕ × ℤ => Real.exp (ε * c) * M
                * ((hold d).toReal * encExpect F R' ε T (encStep F R' τ d)) := by
            funext d
            ring
          rw [heq]
          exact hsumτ.mul_left _
      _ = Real.exp (ε * c) * M
            * ∑' d : ℕ × ℤ, (hold d).toReal * encExpect F R' ε T (encStep F R' τ d) := by
          rw [← tsum_mul_left]
          exact tsum_congr fun d => by ring

/-- **State normalization to the fresh state** (the CLAIM-G instance the Y/Z
induction consumes): any mid-flight state `σ` with `σ.count ≤ R` is dominated by
the zeroed state at its own position with the remaining budget:

  `E_R(T, σ) ≤ e^{ε·σ.count} · max(e^{−σ.banked}, e^{−σ.cumWhite})
      · E_{R−σ.count}(T, ⟨σ.pos, σ.barrier, 0, 0, 0⟩)`. -/
theorem encExpect_normalize_init {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) (σ : EncState) (hc : σ.count ≤ R) :
    encExpect F R ε T σ
      ≤ Real.exp (ε * σ.count)
        * max (Real.exp (-(σ.banked : ℝ))) (Real.exp (-(σ.cumWhite : ℝ)))
        * encExpect F (R - σ.count) ε T ⟨σ.pos, σ.barrier, 0, 0, 0⟩ := by
  have h := encExpect_normalize F (R - σ.count) ε hε σ.count σ.cumWhite σ.banked T
    σ ⟨σ.pos, σ.barrier, 0, 0, 0⟩ rfl rfl (by dsimp only <;> omega) (by dsimp only <;> omega)
    (Or.inl ⟨rfl, rfl⟩)
  rwa [show R - σ.count + σ.count = R by omega] at h

/-- **Beyond the right edge the fold is frozen** (the out-of-strip exit case of
the Z-induction): once `pos₁ > n/2` no future point can satisfy the encounter
condition (`pos₁` is non-decreasing along the fold), so `banked` and `count`
never change and the expectation collapses to the integrand. -/
theorem encExpect_of_edge {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (T : ℕ) :
    ∀ σ : EncState, n / 2 < σ.pos.1 → encExpect F R ε T σ = encVal ε R σ := by
  classical
  induction T with
  | zero => intro σ _; exact encExpect_zero F R ε σ
  | succ T IH =>
    intro σ hedge
    rw [encExpect_succ F R ε hε T σ]
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F R ε T (encStep F R σ d) = encVal ε R σ := by
      intro d
      have hq : ¬(1 ≤ (σ.pos + d).1 ∧ (σ.pos + d).1 ≤ n / 2
          ∧ black n ξ ((σ.pos + d).1 - 1) (σ.pos + d).2
          ∧ σ.barrier < (σ.pos + d).2) := by
        rintro ⟨-, hle, -, -⟩
        have : (σ.pos + d).1 = σ.pos.1 + d.1 := rfl
        omega
      have hs : encStep F R σ d
          = ⟨σ.pos + d, σ.barrier, σ.count,
              σ.cumWhite + (if σ.pos + d ∈ whiteStrip n ξ then 1 else 0), σ.banked⟩ := by
        rw [encStep, dif_neg hq]
      rw [hs, IH _ (by dsimp only; show n / 2 < σ.pos.1 + d.1; omega)]
      rfl
    rw [tsum_congr fun d => by rw [hstep d], tsum_mul_right, hold_tsum_toReal, one_mul]

/-- **The wander claim** (the between-blocks phase of the Z-induction). After a
block exit with white credit `w₀` and no instant encounter, the walk wanders with
`count = 0`, `banked = 0`, `cumWhite = w ≥ w₀`. Given a uniform bound `Z` for
fresh states at budget `R'`, every wander state at budget `R' + 1` satisfies

  `E_{R'+1}(T, ⟨p, b, 0, w, 0⟩) ≤ max 1 (e^ε·e^{−w₀}·Z)`:

a later encounter banks `cumWhite ≥ w₀` and normalizes onto a fresh state at
budget `R'` (paying `e^ε` for the count increment, collecting `e^{−w₀}`); a path
that never encounters ends at `encVal = 1`. Induction on the horizon. -/
theorem encExpect_wander_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R' : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (Z : ℝ) (hZ : 0 ≤ Z)
    (hfresh : ∀ (T' : ℕ) (q : ℕ × ℤ) (b : ℤ),
      encExpect F R' ε T' ⟨q, b, 0, 0, 0⟩ ≤ Z)
    (w₀ : ℕ) (T : ℕ) :
    ∀ (p : ℕ × ℤ) (b : ℤ) (w : ℕ), w₀ ≤ w →
    encExpect F (R' + 1) ε T ⟨p, b, 0, w, 0⟩
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
    rw [encExpect_succ F (R' + 1) ε hε T _]
    have hstep : ∀ d : ℕ × ℤ,
        encExpect F (R' + 1) ε T (encStep F (R' + 1) ⟨p, b, 0, w, 0⟩ d)
          ≤ max 1 (Real.exp ε * Real.exp (-(w₀ : ℝ)) * Z) := by
      intro d
      by_cases hq : 1 ≤ (p + d).1 ∧ (p + d).1 ≤ n / 2
          ∧ black n ξ ((p + d).1 - 1) (p + d).2 ∧ b < (p + d).2
      · -- encounter: bank the credit, normalize onto the fresh state at budget R'
        have hq' : 1 ≤ (p + d).1 ∧ (p + d).1 ≤ n / 2
            ∧ black n ξ ((p + d).1 - 1) (p + d).2 ∧ b < (p + d).2 := hq
        set σ' := encStep F (R' + 1) ⟨p, b, 0, w, 0⟩ d with hσ'
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
        have hnorm := encExpect_normalize_init F (R' + 1) ε hε T σ'
          (by rw [hcnt]; omega)
        refine le_max_of_le_right (le_trans hnorm ?_)
        rw [hbk, max_self, hcnt]
        have h2 : Real.exp (-(σ'.cumWhite : ℝ)) ≤ Real.exp (-(w₀ : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hle : (w₀ : ℝ) ≤ (σ'.cumWhite : ℝ) := Nat.cast_le.mpr hcw
          linarith
        have h3 : encExpect F (R' + 1 - 1) ε T ⟨σ'.pos, σ'.barrier, 0, 0, 0⟩ ≤ Z := by
          simpa using hfresh T σ'.pos σ'.barrier
        have hE0 : 0 ≤ encExpect F (R' + 1 - 1) ε T ⟨σ'.pos, σ'.barrier, 0, 0, 0⟩ :=
          encExpect_nonneg _ _ ε T _
        have hexp1 : Real.exp (ε * ((1 : ℕ) : ℝ)) = Real.exp ε := by norm_num
        calc Real.exp (ε * ((1 : ℕ) : ℝ)) * Real.exp (-(σ'.cumWhite : ℝ))
              * encExpect F (R' + 1 - 1) ε T ⟨σ'.pos, σ'.barrier, 0, 0, 0⟩
            ≤ Real.exp (ε * ((1 : ℕ) : ℝ)) * Real.exp (-(w₀ : ℝ)) * Z :=
              mul_le_mul (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) h3 hE0
                (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          _ = Real.exp ε * Real.exp (-(w₀ : ℝ)) * Z := by rw [hexp1]
      · -- no encounter: still wandering with a larger cumWhite
        have hs : encStep F (R' + 1) ⟨p, b, 0, w, 0⟩ d
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
        * encExpect F (R' + 1) ε T (encStep F (R' + 1) ⟨p, b, 0, w, 0⟩ d)) :=
      Summable.of_nonneg_of_le
        (fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg _ _ ε T _))
        (fun d => mul_le_mul_of_nonneg_left (encExpect_le _ _ ε hε T _)
          ENNReal.toReal_nonneg)
        (hsumH.mul_right _)
    calc ∑' d : ℕ × ℤ, (hold d).toReal
          * encExpect F (R' + 1) ε T (encStep F (R' + 1) ⟨p, b, 0, w, 0⟩ d)
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
theorem encStep_shift {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ)
    (σ : EncState) (d e : ℕ × ℤ) :
    encStep F R ⟨σ.pos + d, σ.barrier, σ.count, σ.cumWhite, σ.banked⟩ e
      = encStep F R σ (d + e) := by
  have hpe : σ.pos + d + e = σ.pos + (d + e) := add_assoc _ _ _
  unfold encStep
  by_cases hq : 1 ≤ (σ.pos + (d + e)).1 ∧ (σ.pos + (d + e)).1 ≤ n / 2
      ∧ black n ξ ((σ.pos + (d + e)).1 - 1) (σ.pos + (d + e)).2
      ∧ σ.barrier < (σ.pos + (d + e)).2
  · rw [dif_pos hq, dif_pos (show 1 ≤ (σ.pos + d + e).1 ∧ (σ.pos + d + e).1 ≤ n / 2
        ∧ black n ξ ((σ.pos + d + e).1 - 1) (σ.pos + d + e).2
        ∧ σ.barrier < (σ.pos + d + e).2 by rw [hpe]; exact hq)]
    by_cases hw : σ.pos + (d + e) ∈ whiteStrip n ξ
    · rw [if_pos hw, if_pos (show σ.pos + d + e ∈ whiteStrip n ξ by rw [hpe]; exact hw)]
      simp only [hpe]
    · rw [if_neg hw, if_neg (show σ.pos + d + e ∉ whiteStrip n ξ by rw [hpe]; exact hw)]
      simp only [hpe]
  · rw [dif_neg hq, dif_neg (show ¬(1 ≤ (σ.pos + d + e).1 ∧ (σ.pos + d + e).1 ≤ n / 2
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
first-passage endpoint law: for any horizon `T ≥ s/3 + 1` (enough steps to clear —
each `Hold` step spends height `≥ 3`) and any `[0,B]`-valued `g` dominating all
shorter-horizon continuations from the clearing step,

  `encExpect T σ ≤ Σ'_e fpDist s (e) · g e`.

The fold's clearing condition `barrier < pos₂ + d₂` is EXACTLY `fpDist`'s overshoot
condition `s < d₂` — the two recursions match step for step (strong induction on
`s` mirroring `fpDist`'s budget recursion). -/
theorem encExpect_block_le {n ξ : ℕ} (F : TriangleFamily n ξ) (R : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) :
    ∀ s : ℕ, ∀ σ : EncState, (s : ℤ) = σ.barrier - σ.pos.2 →
    ∀ T : ℕ, s / 3 + 1 ≤ T →
    ∀ g : ℕ × ℤ → ℝ, (∀ e, 0 ≤ g e) → ∀ B : ℝ, (∀ e, g e ≤ B) →
    (∀ e : ℕ × ℤ, (s : ℤ) < e.2 → ∀ T' : ℕ, T' < T →
      encExpect F R ε T' (encStep F R σ e) ≤ g e) →
    encExpect F R ε T σ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal * g e := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro σ hs T hT g hg0 B hgB hg
    classical
    have hB : 0 ≤ B := le_trans (hg0 (0, 0)) (hgB (0, 0))
    -- peel one step
    obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
    rw [encExpect_succ F R ε hε T' σ]
    -- unfold one step of fpDist on the right
    conv_rhs => rw [fpDist]
    rw [tsum_bind_toReal hold _ g hg0 hgB]
    -- termwise comparison over the step d
    have hterm : ∀ d : ℕ × ℤ,
        (hold d).toReal * encExpect F R ε T' (encStep F R σ d)
          ≤ (hold d).toReal * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
              else (fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) : PMF (ℕ × ℤ)) e).toReal
                * g e := by
      intro d
      rcases eq_or_ne (hold d) 0 with h0 | h0
      · rw [h0]; simp
      have hd3 : 3 ≤ d.2 := hold_support_snd_ge d (by rwa [PMF.mem_support_iff])
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      rcases lt_or_ge (s : ℤ) d.2 with hover | hunder
      · -- the clearing step: pure branch, dominated by g d
        rw [if_pos (Or.inr hover)]
        calc encExpect F R ε T' (encStep F R σ d) ≤ g d := hg d hover T' (by omega)
          _ = ∑' e, ((PMF.pure d : PMF (ℕ × ℤ)) e).toReal * g e := by
              rw [tsum_eq_single d (fun e he => by
                rw [PMF.pure_apply, if_neg he]; simp)]
              rw [PMF.pure_apply, if_pos rfl]; simp
      · -- mid-block step: no encounter possible, recurse at the reduced budget
        rw [if_neg (by push_neg; exact ⟨by omega, hunder⟩)]
        -- the fold takes the non-encounter branch (barrier not cleared)
        have hnc : ¬(1 ≤ (σ.pos + d).1 ∧ (σ.pos + d).1 ≤ n / 2
            ∧ black n ξ ((σ.pos + d).1 - 1) (σ.pos + d).2 ∧ σ.barrier < (σ.pos + d).2) := by
          rintro ⟨-, -, -, hbar⟩
          have : (σ.pos + d).2 = σ.pos.2 + d.2 := rfl
          omega
        have hstep : encStep F R σ d
            = ⟨σ.pos + d, σ.barrier, σ.count,
                σ.cumWhite + (if σ.pos + d ∈ whiteStrip n ξ then 1 else 0), σ.banked⟩ := by
          rw [encStep, dif_neg hnc]
        -- drop the mid-block white increment (coupling)
        have hdrop : encExpect F R ε T' (encStep F R σ d)
            ≤ encExpect F R ε T'
                ⟨σ.pos + d, σ.barrier, σ.count, σ.cumWhite, σ.banked⟩ := by
          rw [hstep]
          exact encExpect_anti F R ε hε T' _ _ rfl rfl rfl (Nat.le_add_right _ _)
            (le_refl _)
        -- recurse via the strong IH at the reduced budget
        set s'' : ℕ := s - d.2.toNat with hs''
        have hrec : encExpect F R ε T'
              ⟨σ.pos + d, σ.barrier, σ.count, σ.cumWhite, σ.banked⟩
            ≤ ∑' e', (fpDist s'' e').toReal * g (d + e') := by
          refine IH s'' (by omega) _ ?_ T' (by omega) _ (fun e' => hg0 _) B
            (fun e' => hgB _) ?_
          · show (s'' : ℤ) = σ.barrier - (σ.pos + d).2
            have : (σ.pos + d).2 = σ.pos.2 + d.2 := rfl
            omega
          · intro e' he' T'' hT''
            rw [encStep_shift]
            refine hg (d + e') ?_ T'' (by omega)
            have h2 : (d + e').2 = d.2 + e'.2 := rfl
            omega
        -- reindex the map branch
        rw [tsum_map_toReal _ _ g hg0]
        exact le_trans (le_trans hdrop hrec) (le_of_eq (tsum_congr fun e' => by rfl))
    -- summability on both sides, then sum the termwise bound
    have hsum : Summable (fun d : ℕ × ℤ => (hold d).toReal) :=
      ENNReal.summable_toReal (by rw [hold.tsum_coe]; exact ENNReal.one_ne_top)
    have hnnL : ∀ d : ℕ × ℤ,
        0 ≤ (hold d).toReal * encExpect F R ε T' (encStep F R σ d) :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg F R ε T' _)
    have hboundL : ∀ d : ℕ × ℤ,
        (hold d).toReal * encExpect F R ε T' (encStep F R σ d)
          ≤ (hold d).toReal * Real.exp (ε * R) :=
      fun d => mul_le_mul_of_nonneg_left (encExpect_le F R ε hε T' _)
        ENNReal.toReal_nonneg
    have hsumL : Summable (fun d : ℕ × ℤ =>
        (hold d).toReal * encExpect F R ε T' (encStep F R σ d)) :=
      Summable.of_nonneg_of_le hnnL hboundL (hsum.mul_right _)
    have hnnR : ∀ d : ℕ × ℤ, 0 ≤ (hold d).toReal
        * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) : PMF (ℕ × ℤ)) e).toReal
              * g e :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (tsum_nonneg fun e =>
        mul_nonneg ENNReal.toReal_nonneg (hg0 e))
    have hboundR : ∀ d : ℕ × ℤ, (hold d).toReal
        * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) : PMF (ℕ × ℤ)) e).toReal
              * g e ≤ (hold d).toReal * B :=
      fun d => mul_le_mul_of_nonneg_left
        (tsum_toReal_mul_le _ g hg0 hgB hB) ENNReal.toReal_nonneg
    have hsumR : Summable (fun d : ℕ × ℤ => (hold d).toReal
        * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) : PMF (ℕ × ℤ)) e).toReal
              * g e) :=
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

/-- **The (7.59)-shaped deep white-exit bound** (the ONLY open external input of
the X9 induction; sibling of the Case-2 kernel `fpDist_white_exit` in
`BlackEdge.lean`). Identical statement with the Case-2 budget hypothesis
`s ≤ m/log²m` REMOVED (any triangle point qualifies — the (7.52) bound
`budget_le_of_mem_triangle` caps `s = O(m)` for free) and the mass sharpened to
`p₀ > 1/2` (the chain cap `encChainX_le_exp` needs it; numerically the white-exit
mass is ≈ 0.99, harness check 9, 2026-07-10).

Route: as for `fpDist_white_exit` — Lemma 7.7 (`fpDist_location_bound`, X6)
concentrates the endpoint at `(j + s/4 + O(√(1+s)), l_Δ + O(1))`; every endpoint
clears the triangle top (`fpDist_support_snd_gt`); the (7.11) slope bound + the
`(1/10)·log(1/ε)` family separation (X3) exclude every other triangle, so the
endpoint is white; in-strip since `s/4 + O(√s) ≤ 0.8·m + O(√m) < m`. The
`s ≤ m/log²m` hypothesis of the Case-2 twin is used there ONLY for the
`edgeWeight` degradation, not for whiteness — this deep variant is the same
geometry with a larger (still `O(m)`) budget. -/
theorem fpDist_white_exit_deep :
    ∃ p₀ : ℝ, 1 / 2 < p₀ ∧ ∃ Cthr : ℕ, ∀ n ξ : ℕ, ¬ 3 ∣ ξ →
      ∀ F : TriangleFamily n ξ, ∀ m : ℕ, Cthr ≤ m → m ≤ n / 2 →
      ∀ l : ℤ, 1 ≤ n / 2 - m →
      ∀ t ∈ F.T, (n / 2 - m - 1, l) ∈ triangle t.1 t.2.1 t.2.2 →
      ∀ s : ℕ, (s : ℤ) = t.2.1 - l →
      p₀ ≤ ∑' e : ℕ × ℤ, (fpDist s e).toReal
        * Set.indicator (whiteStrip n ξ) 1 (n / 2 - m + e.1, l + e.2) := by
  sorry

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

OPEN (node X9): corrected proof route (recorded in `PENDING_WORK.md` lap 52):
two-level claim over fresh states — `Y(q, b, ρ) ≤ e^ε·X` for JUST-ENTERED states
(`X := p₀/(1−(1−p₀)e^ε)`) and `Z ≤ max(1, Y-bound)` for generic states — by
induction on `ρ` (remaining blocks) with an inner strong induction on `T`.
Per block: `encExpect_block_le` (proved) reduces to the `fpDist` exit law; the
four-mass vertex analysis over (white/nonwhite × re-encounter/not) closes with
`E ≤ P(NE) + e^εX·(e^{−1}·P(E∧w) + P(E∧nw))` and the white-exit mass
`P(w) ≥ p₀` from `fpDist_white_exit` ((7.51)/(7.59) variant, X8 kernel — the only
open input). The affine state-normalization is `encExpect_anti`-style coupling. -/
theorem many_triangles_white :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 100 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∀ n ξ : ℕ, ¬ 3 ∣ ξ → ∀ F : TriangleFamily n ξ,
    ∀ R : ℕ, 1 ≤ R → ∀ (T : ℕ) (j' : ℕ) (l' : ℤ),
    encExpect F R ε T (encInit j' l') ≤ Real.exp (2 * ε) := by
  sorry

end TaoCollatz
