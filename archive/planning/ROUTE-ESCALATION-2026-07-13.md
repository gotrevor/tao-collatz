# ROUTE ESCALATION — 2026-07-13 (lap 57): the ε=10⁻⁴ separation is VACUOUS; (7.50) whiteness unprovable as routed

> ✅ **CLOSED — HISTORICAL. Do not act on this document.** Both escalations it
> spawned are resolved: (1) the ε=10⁻⁴ vacuity was fixed by Trevor's altitude ruling
> (Remedy A, `epsBW = 10⁻⁹⁰`) and the real Lemma-7.4 separation landed in pass 23;
> (2) the follow-on "quantifier order" escalation was **downgraded by judge pass 24**
> — not altitude-class; the route is sound and the blocker was two throwaway constants.
> Current marching orders: **`HANDOFF-2026-07-13-e.md`** + **BLUEPRINT §2**. Kept for
> the record only.

**Trigger**: T2-class (DIRECTION.md route-level triggers), but firing on the
**(7.50)/(7.51) white-exit ring** (Case 2 of Prop 7.8, p.48), not just (7.65).
Found while attacking `fpDist_any_triangle_le` (the last sorry under
`fpDist_white_exit_deep`, X9's only open input and X8's Case-2 twin kernel).

## The finding (three steps, each machine-checkable)

1. **`F.separated` is vacuous at `epsBW = 10⁻⁴`.** The required squared
   separation is `((1/10)·log 10⁴)² ≈ 0.848 < 1`, while `triangle : Set (ℕ × ℤ)`
   is a set of lattice points and any two DISTINCT lattice points have squared
   distance `≥ 1`. This is not an accident of the statement: X3's
   `black_structure` PROVES its separation clause exactly this way —
   `Triangles.lean:1211-1231` ("the separation constant has square ≤ 1 ≤ any
   nonzero lattice distance squared", via `sep_const_sq_le_one` +
   `lattice_sq_dist_ge_one` + fibre-disjointness). **The Euclidean-separation
   content of Lemma 7.4 (paper pp.39–41) was never formalized** — the lattice
   shortcut was sound for the pinned statement but the statement carries no
   content beyond pairwise disjointness at this ε.

2. **(7.50)→(7.51) consumes real separation.** Tao's whiteness step: the
   first-passage endpoint lands outside Δ but at Euclidean distance `O(1)` from
   Δ (overshoot `h = l_{[1,k]} − s ≥ 1` above the top edge, geometric tail;
   column inside Δ's span whp by the `log2 − log9/4 ≈ 0.144` slope margin), and
   is then white because every OTHER triangle is `(1/10)log(1/ε)` away. This
   requires `(1/10)log(1/ε) > O(1)` — an implicit smallness demand on ε. At
   `ε = 10⁻⁴` the separation `0.921` is below even ONE lattice step, so a
   foreign triangle may legally sit at vertical distance 1 above Δ's top edge.
   `hold`'s height jump is `3 + Σ pascalNe3`, so the overshoot rows
   `h ∈ {1, …, O(1)}` each carry Θ(1) first-passage mass; singleton triangles
   tiling those rows are pairwise `≥ 1`-separated and disjoint from Δ, hence a
   legal `TriangleFamily` shape. Nothing in the repo (or the interface) bounds
   the real black set's density just above a triangle's top edge.

3. **Consequence**: `fpDist_any_triangle_le` (foreign mass ≤ 1/8), and hence the
   `51/100 ≤ p₀` pin of `fpDist_white_exit_deep`, is **unprovable from the
   `TriangleFamily` interface** — the adversarial family above captures ≥ 3/4
   of the mass. Worse, DIRECTION's fallback ("weaken the pin to any explicit
   `c₀ > 0`") also dies: with all overshoot rows capturable, NO positive lower
   bound on the white-exit mass follows from the interface. The kernel needs
   real separation content, at a constant exceeding the overshoot scale.

**Not affected**: X10's (7.65) Σ-count route — `apex_gap`/`apex_separation` are
proved from `not_mem_two` (disjointness only), which IS real content. The
out-of-strip half (`fpDist_out_of_strip_le`, PROVED this lap) is also fine.

## Remedy options (altitude decision — D4 is a frozen invariant)

- **(A) Shrink `epsBW` (D4 change) + formalize the REAL Lemma 7.4 separation.**
  Two coupled costs: (i) the lattice-vacuity proof of X3's separation clause
  dies the moment `sep² > 1` — the true fibre-transition argument (pp.39–41)
  must be formalized with the actual `(1/10)log(1/ε)` constant; (ii) every
  `epsBW`-numeral inequality repo-wide re-validates (T2 says numerics-check
  first). Required size: the (7.50) ring needs
  `foreign ≤ P(dist(endpoint, Δ) ≥ sep) ≤ C·e^{-c·sep} ≤ 1/8`, where the
  overshoot row-tail and the column-overhang tail both have honest geometric
  constants (heights jump ≥ 3; columns are `Geom(4)` sums, and for large `s`
  the `0.144·s` slope margin dominates). Estimate `sep ≈ 20–40`, i.e.
  `epsBW ≈ e^{-200}` to `e^{-400}` (`10⁻⁸⁷`–`10⁻¹⁷⁴`). All downstream ε-budgets
  stay explicit constants (the ε₀-floor `ε₀ ≥ epsBW` gets EASIER; the white
  gain `e^{-ε³}` gets weaker, inflating `C_{A,ε}` thresholds only).
- **(B) Bypass separation: prove a vertical white-gap lemma from the fibre
  structure** — e.g. "the O(1) rows above a maximal triangle's top edge within
  its column span are white", directly from `θq` growth (the top edge is where
  `9^a 2^b |θ*|` crosses ε; one more factor of 2 pushes it out). If TRUE this
  is exactly the content (7.50) needs, avoids touching D4/X3, and its scale is
  `log(1/ε)/log 2 ≈ 13` rows at the CURRENT ε — comfortably above the overshoot
  quantiles. **Probe first**: check on paper whether a point directly above the
  top edge has `|θ| > ε` forced (the fibre at `(j, l+1)` relates to the fibre at
  `(j, l)` by a factor-2 valuation shift — this is plausibly a 1-page argument
  and numerics-checkable via the existing exact-ℚ harness).
- **(C) Re-route Case 2 to avoid whiteness-after-exit entirely** (e.g. take the
  Case-3 machinery at `P = O(1)` for Case 2 too). Costly and off-paper; last
  resort.

## ADDENDUM (same lap): remedy (B) probed on paper — TRUE vertically, but a right-edge residue remains

**(B) is TRUE and elementary in the vertical direction.** The doubling relation
`2^h·θ(j, l+h) ≡ θ(j, l) (mod 1)` gives: if `(j,l)` is black and `(j,l+1)` is
not, then `θ(j,l+1) = (θ(j,l) ± 1)/2`, so `|θ(j,l+1)| ≥ (1−ε)/2` and inductively
`|θ(j,l+h)| ≥ (1−ε)/2^h` (nearest-integer distance halves at worst). Blackness
needs `≤ ε`, so the column above a run top is WHITE for all
`h ≤ log₂((1−ε)/ε) ≈ 13.28`, i.e. `h ∈ {1,…,13}` at `ε = 10⁻⁴`. Corner geometry
upgrades this to in-span exclusion: a foreign triangle `t''` (corner `(j*,l*)`)
containing a phase point at height `lΔ+h, h ≤ 13`, with `j*` inside Δ's
top-edge span, also contains `(j*, lΔ+h)` (drop the `Δj·log9` term from the
membership inequality), contradicting the white gap anchored at `(j*, lΔ) ∈ Δ`
(whose run top is `lΔ` by `corner_eq`). So foreign capture at `h ≤ 13` forces
`j*` — hence the phase column — RIGHT of Δ's top-edge span.

**The residue: the right edge has NO horizontal analogue.** Horizontally `θ`
multiplies by 9 per column and can wrap past `1/2` immediately, landing black
again 2 columns right of a run edge — no fixed gap at fixed ε. And the mass
reaching `O(1)` columns right of Δ's span is Θ(1) when `s` is small (`e.1 ≥ 1`
always; the span margin is only `≈ 0.315·s` columns, zero for `s ≤ 3`). Tao
(7.50) kills this side with the ε-separation as well; there is no fibre
substitute. NOTE: Tao's (7.51) only needs `p₀ ≫ 0` (the `> 1/2` /`51/100` pin
is formalization-internal — `encChainX` converges for any `p₀ > ~ε`, per
DIRECTION's fallback note), but even `p₀ > 0` fails while the right-edge hole
is open, so weakening the pin alone does NOT rescue the kernel.

**Sharpened remedy menu**:
- **(B+A-small) Hybrid**: prove the vertical white-gap lemma (above, ~1 page of
  Lean over `θq` doubling) + shrink ε only enough to give HORIZONTAL Euclidean
  separation `> the O(√(1+s))∧O(1) column overhang`, quantitatively
  `sep ≈ 5–10` ⟹ `ε ≈ e^{-50}`–`e^{-100}`, AND formalize the real Lemma-7.4
  separation at that ε (the lattice-vacuity proof dies at `sep > 1`). The
  white-gap lemma also caps the needed overshoot control at 13 rows with the
  CURRENT ε, keeping most numerics tame.
- **(A) full**: as above, `sep ≈ 20–40`, no white-gap lemma needed.
- Either way the real Lemma-7.4 separation proof (pp.39–41) is now on the
  critical path — it was never formalized.

**Recommendation**: altitude lap to rule (B+A-small) vs (A); both change D4 and
reopen X3's separation clause. The vertical white-gap lemma is common to the
preferred hybrid and is provable NOW against the current `epsBW` — a good
next-lap grind target if the ruling lands hybrid. Until the ruling, grind
X10 assembly (`triangle_encounter_le`), which is disjointness-based and
unaffected.

## Meanwhile (this lap and until ruled)

The white-exit kernel is BLOCKED on this ruling. Non-blocked crux work per the
directive: X10 assembly (`triangle_encounter_le`, step 2 — apex route is
disjointness-based and unaffected), and the shared row-tail lemma
`P(overshoot ≥ H) ≤ C·e^{-cH}` (needed by EVERY remedy's endgame).
