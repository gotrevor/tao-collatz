# PENDING WORK (kept current per lap; newest on top)

## Lap 35 (2026-07-12, sixth box session): (F4a) PARAMETRIC CENTER BOUND PROVED

`Sec7/Unroll.lean`: **`iidSum_apply_le_center_of_decay`** — the (E) Gaussian
summation generalized over the decay constant: any `p : PMF (ℕ × ℤ)` with
`‖charFn (p.map (modPair N)) ξ‖² ≤ 1 - (nd-sum)/c` uniformly in `N ≥ 4` has
`P(S_n = v) ≤ (32c)²/(1+n)` (a = n/(4cN²) ∈ [1/(8c), 1], sum ≤ 4/a ≤ 32c).
`holdSum_apply_le_center` is now the c = 768 instance ((32·768)² = 603979776,
unchanged). AXIOM-CLEAN.

**(F4b/F5) next — assemble hold_local_bound**:
1. (F4b) tilted center bound: apply `iidSum_apply_le_center_of_decay` to
   `tilt hold (expW2 l1 l2)` with c = 80000 (decay from `charFn_decay_of_atoms` at
   μ = 1/400 via `tilt_hold_apply_ge` transferred through modPair by
   `PMF.apply_le_map_apply`; 2μ² = 1/80000). Yields P_tilt(S̃_n = v) ≤ C₀/(1+n),
   C₀ = (32·80000)² = 2560000² = 6.5536e12.
2. (F5) tilting identity consumption: `iidSum_apply_eq_tilt` at p = hold, w = expW2:
   P(S_n = v) = P_λ(S̃_n = v)·Zⁿ·(w v)⁻¹, so
   (iidSum hold n v).toReal ≤ (C₀/(1+n))·(Z.toReal)ⁿ·e^{-λ·v}. Need in toReal:
   toReal of product (all finite), (expW2 l1 l2 v)⁻¹.toReal = e^{-(l1 v1 + l2 v2)}.
3. λ-optimization → Lemma 2.2(i) Gweight form: need log Z(λ) ≤ λ·(4,16) + K|λ|²
   on the box. Mean: E hold = (4, 16)? verify from paper p.42 (mean of Geom(4) is 4;
   E[second coord] = 3 + E[Σ_{i<k-1} pascalNe3] = 3 + 3·(16/3 - 1)? — compute; the
   claimed Gweight center is (n·4, n·16)). This needs the MGF second-order bound —
   candidate route: Z(λ)·e^{-λ·mean} ≤ exp(K|λ|²) via explicit rational arithmetic
   on the factor formula (hard); OR restate hold_local_bound with the Gweight
   centered at the true mean and ANY exponential decay rate c (statement already
   has ∃ c C — check LocalBound.lean statement shape first!).

## Lap 34 (2026-07-12, sixth box session): (F3b) TILTED ATOM MASSES PROVED

`Prob/Mgf.lean`: **`tiltZ_hold_le`** (Z_hold ≤ 221/25 on the box |λᵢ| ≤ 1/50 —
the ne_top domination series evaluated: 1 + (1 - 171/196)⁻¹; `tiltZ_hold_ne_top`
now a one-line corollary) and **`tilt_hold_apply_ge`** — tilted hold atoms keep
mass ≥ 1/400 in the window y₁ ≤ 2, 0 ≤ y₂ ≤ 8 (weight ≥ e^{-1/5} ≥ 4/5,
(1/32)(4/5)(25/221) = 5/1768 > 1/400). AXIOM-CLEAN. Gotcha: `inv_le_inv_of_le`
is gone — the antitone inverse lemma is `inv_anti₀ (hb : 0 < b) (hba : b ≤ a)`.

**(F4) next — tilted center bound**: `tiltHold l1 l2 := tilt hold (expW2 l1 l2) …`
(abbreviation to tame the proof-term arguments). Transfer the four atoms through
modPair (`PMF.apply_le_map_apply` + `tilt_hold_apply_ge` at (1,3),(2,5),(2,7),(2,8),
hold masses from hold_apply_* ≥ 1/32 in toReal) ⇒ `charFn_decay_of_atoms` at
μ = 1/400 ⇒ decay constant 2·(1/400)⁻²… = 1/80000. Then replay `holdSum_apply_le_center`
with 768 → 80000·(3/8)-ish: generalize the (E) Gaussian-summation proof over the
decay constant `c` (a = n/(4c·N²), threshold a ≥ 1/(8c), sum ≤ (4/a)² ⇒
C(c) = (32c)²) — refactor `holdSum_apply_le_center` into
`iidSum_apply_le_center_of_decay (r : PMF (ℕ × ℤ))` taking the parametric decay
as hypothesis. Then (F5) λ-optimization via the tilting identity
`iidSum_apply_eq_tilt`: P(S_n = v) = P_tilt(S_n = v)·Zⁿ·e^{-λ·v} ≤
(C/(1+n))·exp(n·log Z - λ·v); need log Z ≤ λ·mean + K|λ|² (mean (4,16)) or crude
sign-choice at |λ| = 1/50 for the Gweight branch ⇒ `hold_local_bound`.

## Lap 33 (2026-07-12, sixth box session): (F3a) PARAMETRIC CHARACTER DECAY

`Sec7/Unroll.lean`: **`charFn_decay_of_atoms`** — charFn_hold_decay abstracted over
an atom-mass lower bound `μ ≥ 0` at the four projected points (1,3),(2,5),(2,7),(2,8)
mod N: `‖charFn r ξ‖² ≤ 1 - 2μ²·((nd ξ₁/N)² + (nd ξ₂/N)²)`, any PMF r, N ≥ 4.
`charFn_hold_decay` re-derived as the μ = 1/32 instance (2·(1/32)² = 1/512 ≥ 1/768).
AXIOM-CLEAN. Gotcha: the old proof's final `nlinarith` blows the heartbeat budget
once μ is symbolic — pre-multiply the triangle bounds by μ² via
`mul_le_mul_of_nonneg_left … (sq_nonneg μ)` and finish with plain `linarith`.

**(F3b) next — tilted atom masses**: need `tiltZ_hold_le` (numeric UPPER bound on
the partition function on the box |λᵢ| ≤ 1/50, same geometric-sum route as
tiltZ_hold_ne_top: e^{λ₁+3λ₂}·Σ_k ratio^{k-1} with ratio ≤ 171/196 ⇒ Z ≤
(50/47)-ish·(1-171/196)⁻¹ explicit rational) and per-atom lower bounds
`(tilt hold (expW2 λ)) y ≥ hold(y)·e^{-|λ|·‖y‖₁}/Z ≥ μ₀` at the four points
(worst atom (2,8): (1/32)·e^{-10/50}/C). Then (F4) tilted center bound = (E) verbatim
+ charFn_decay_of_atoms at μ₀; (F5) λ-optimization (needs hold mean (4,16) or the
crude boundary-sign route) ⇒ `hold_local_bound`.

## Lap 32 (2026-07-12, sixth box session): (F2b) HOLD MGF FINITENESS PROVED

`Prob/Mgf.lean` (now imports Sec7/Holding): `exp_le_inv_one_sub` (e^x ≤ (1-x)⁻¹ on
[0,1)), `geom_closed_le` (monotone rational evaluation of r(1-r)⁻¹),
`tiltZ_geomHalf_le` (≤ 25/24 for λ ≤ 1/50), `pascalNe3_apply_two` (= 3⁻¹),
`tiltZ_pascalNe3_ne_zero`, **`tiltZ_pascalNe3_le`** (≤ 57/50 on |λ| ≤ 1/50 — the
b=3 atom removal is what pulls it below 4/3; cancel the atom via
ENNReal.add_le_add_iff_right, margin 625/432 ≤ 218/150), `expW2` 2-D weight (+
zero/add), **`tiltZ_hold_factor`** (conditional factorization: Σ_k gQ(k)·e^{λ₁k+3λ₂}
·Z_ne3^{k-1}, via tsum_bind_mul/tsum_map_mul + tiltZ_iidSum), `tiltZ_hold_ne_zero`,
**`tiltZ_hold_ne_top`** on the box |λᵢ| ≤ 1/50 (geometric domination, ratio
(3/4)(50/49)(57/50) = 171/196 < 1). ALL AXIOM-CLEAN. Paper (7.30) engine done.
Gotchas: `rw [ENNReal.ofReal_mul]` grabs the wrong (LHS) occurrence — rewrite
numeral⁻¹ → ofReal form FIRST then merge with ← ofReal_mul; `.not_le` field gone
(use `not_le.mpr`); gcongr side goals: pre-`have` the ofReal_le_ofReal facts and
let gcongr close by assumption; `unfold hold` where `rw [hold]` fails.

**(F3) next — tilted charFn decay**: refactor `charFn_hold_decay` into a parametric
version `charFn_decay_of_atoms (r : PMF (ZMod N × ZMod N)) (μ : ℝ) (hμ : 0 < μ)`
taking `μ ≤ min` of the four transferred atom masses at (1,3),(2,5),(2,7),(2,8) and
concluding `‖charFn r ξ‖² ≤ 1 - c·μ²·(nd² sum)` (the current proof's pair_transfer
step already isolates the masses — replace the four numerals by μ, constant becomes
explicit in μ). Then tilted hold atoms: (tilt hold w).apply at atom y =
hold(y)·w(y)/Z ≥ atom·e^{-|λ|·|y|}/Z with Z ≤ [bound from factor formula ≤ …] — need
a numeric UPPER bound on tiltZ hold on the box (same geometric sum: ≤ e^{3λ₂}·
Σ ≤ (50/47)·(1+(1-171/196)⁻¹)-ish — or simpler: atoms of tilt ≥ (1/4)·(min-e-power)
/Z with Z ≤ ofReal(C) — derive `tiltZ_hold_le` alongside). Then (F4) center bound
for the tilted walk (reuse (E) Gaussian summation verbatim — it consumed only the
decay + PMF-ness), (F5) λ-optimization: Z(λ)ⁿe^{-λ·v} ≤ Gaussian/exp factor via
log Z ≤ λ·(4,16) + K|λ|² on the box (needs E hold = (4,16) — mean computation) OR
the cruder route: pick λ = ±(1/50) signs to dominate direction, giving the exp(-c|·|)
Gweight branch only near the boundary. Design decision next lap.

## Lap 31 (2026-07-12, sixth box session): (F2a) d=1 MGFs PROVED — Prob/Mgf.lean NEW

`Prob/Tilt.lean` additions: **`tiltZ_map`** (partition functions push forward),
**`tiltZ_iidSum`** (`Z_{S_n} = Zⁿ`, one-line from the tilting identity + PMF mass 1).
`Prob/Mgf.lean` NEW: `expW λ a = ofReal e^{λa}` (+ zero/add), **`tiltZ_geomHalf`**
(exact geometric MGF `r(1-r)⁻¹`, `r = e^λ/2`, unconditional in ℝ≥0∞) + ne_zero/ne_top
(strip `e^λ < 2`), **`tiltZ_pascal`** (= square, via `pascal = iidSum geomHalf 2`),
`pascalNe3_eq_ite`, `pascal_apply_three` (= 4⁻¹), **`tiltZ_pascalNe3_add`** (atom
split: `Z_{pascalNe3} + 3⁻¹e^{3λ} = (4/3)Z_{pascal}`, no ℝ≥0∞ subtraction).
ALL AXIOM-CLEAN. Gotcha: `ENNReal.tsum_eq_add_tsum_ite` bakes in
`Classical.propDecidable`; match hand-written ites via `convert … using 3; funext;
split_ifs <;> rfl`.

**(F2b) next — hold MGF finiteness on the box |λ| ≤ 1/50**:
1. Numeric strip bound: `tiltZ pascalNe3 (expW λ) ≤ ofReal(4/3·((x/(1-x))² - x³/4·…))`
   — concretely from the split identity: Z_ne3 = (4/3)Z_pascal - 3⁻¹e^{3λ} (ENNReal
   sub OK since finite); for |λ| ≤ 1/50: x = e^λ/2 ∈ [49/100, 25/49],
   Z_gh = x/(1-x) ≤ 25/24, Z_pascal ≤ (25/24)², e^{3λ} ≥ (49/50)³ ⇒
   Z_ne3 ≤ (4/3)(25/24)² - 3⁻¹(49/50)³ < 1.135 (target: (3/4)e^{λ₁}Z_ne3 < 1 ⇒
   OK with e^{λ₁} ≤ 50/49: (3/4)(50/49)(1.135) ≈ 0.8686 < 1 ✓).
2. 2-D weight `expW2 (λ₁ λ₂) (d : ℕ × ℤ)` (needs ℤ version of expW for coord 2).
3. Factor `tiltZ hold` through hold's bind/map structure (hold_apply_pin route or
   direct tsum_prod' + tsum_bind_mul/tsum_map_mul): inner sum over increments =
   e^{3λ₂}·Z_ne3(λ₂)^{k-1} (tiltZ_iidSum on ℕ then push through the (3+Σ) map — mind
   the ℕ→ℤ cast: use tiltZ_map with the cast hom), outer = Σ_k gQ(k)e^{λ₁k}(…)^{k-1}
   geometric with ratio (3/4)e^{λ₁}Z_ne3 < 1 ⇒ tiltZ hold ≠ ∞ on the box.
Then (F3) tilted charFn decay (parametrize charFn_hold_decay by atom-mass lower
bounds), (F4) tilted center bound, (F5) λ-optimization ⇒ hold_local_bound.

## Lap 30 (2026-07-12, sixth box session): (F1) TILTING ENGINE PROVED — Prob/Tilt.lean NEW

Generic exponential tilting, entirely in ℝ≥0∞ (no convergence side conditions beyond
0 < Z < ∞): `tiltZ p w = Σ_d p d · w d` (partition function / MGF at the tilt),
`tilt p w` (the tilted PMF, direct subtype construction + ENNReal.mul_inv_cancel),
**`iidSum_tilt_apply`** (product-form tilting identity
`P_λ(S̃_n = v)·Zⁿ = P(S_n = v)·w v`, induction via iidSum_succ; weights recombine on
the diagonal v = a+e by w-multiplicativity), **`iidSum_apply_eq_tilt`**
(consumption form `P(S_n = v) = P_λ(S̃_n = v)·Zⁿ·(w v)⁻¹`). AXIOM-CLEAN.
Gotcha: hand-written `if v = a + e` needs `classical` (PMF.map_apply's ite is
classical); pushing constants into tsums is `← ENNReal.tsum_mul_left/right`.

**(F2) next — instantiate at hold**: w λ d := ENNReal.ofReal (exp (λ₁·d₁ + λ₂·d₂)).
Multiplicativity: ofReal_mul + exp_add. Need `tiltZ hold (w λ) < ∞` for λ in a box:
hold = geomQuarter ⊗ (3 + pascalNe3-sum) — second coordinate ≤ 3·(first coordinate
sum structure)? NO: second coord is 3+Σ of pascalNe3 which has geometric tail 3/4;
first coord geometric 1/4. MGF finite for λ₂ < log(4/3)/const, λ₁ < log 4 - λ₂-slack.
Concretely: tiltZ = Σ_k geomQuarter k · e^{λ₁k} · Π-structure — use hold's bind/map
form (Holding.lean) to factor the MGF as product of geometric MGFs (each a geometric
series). Then (F3): tilted atom masses ≥ half untilted for small λ-box ⇒
charFn decay for tilted hold (refactor charFn_hold_decay to take atom-mass lower
bounds as hypotheses, constant parametric); (F4): center bound for tilted walk;
(F5): optimize λ = clip((v - n·mean)/(Kn)) ⇒ Gweight factor ⇒ hold_local_bound.

## Lap 29 (2026-07-12, sixth box session): (E) GAUSSIAN SUMMATION PROVED — holdSum_apply_le_center

`Prob/CharFn.lean`: **`pow_le_exp_of_sq_le_one_sub`** (x² ≤ 1-D ⇒ xⁿ ≤ exp(-nD/4),
n ≥ 2; floor-of-n/2 absorbed into the 4), `sum_exp_neg_mul_le` (finite geometric
≤ (1-e^{-a})⁻¹ via geom_sum_eq + sign-flip), `sum_zmod_eq_sum_range` (val reindex,
sum_nbij'), **`sum_exp_neg_nd_sq_le`** (1-D Gaussian sum over ZMod N ≤ 2(1-e^{-a})⁻¹:
nd² ≥ nd, exp(-a·min) ≤ sum of the two val-halves, second half reflected by
sum_range_reflect), `one_sub_exp_neg_inv_le` ((1-e^{-a})⁻¹ ≤ 2/a on (0,1]).
`Sec7/Unroll.lean`: **`holdSum_apply_le_center`** — P(holdSum n = v) ≤ 603979776/(1+n)
for ALL n, v. At N = ⌊√n⌋+1 (N² ∈ [n+1, 2n], N ≥ 4 for n ≥ 9; n ≤ 8 by trivial mass
bound), a = n/(3072N²) ∈ [1/6144, 1]; per-frequency ‖φ‖ⁿ ≤ exp(-a·nd₁²)·exp(-a·nd₂²),
2-D sum factorizes into (1-D sum)² ≤ 24576², N⁻² ≤ (1+n)⁻¹. ALL AXIOM-CLEAN.
This is the center-regime core of Lemma 2.2(i) for Hold (node S3).

**(F) exponential tilting (next)**: off-center regime of `hold_local_bound`.
Plan (HANDOFF-2026-07-10-e item 2): tilted PMF hold_λ ∝ e^{λ·d} hold(d) for λ in a
fixed small box (needs MGF finiteness on a strip — the Lemma 7.6 engine, (7.30);
hold second-coordinate tail is pascalNe3/geometric so the MGF is finite for
λ₂ < log(4/3)-ish); identity P(S_n = v) = M(λ)ⁿ e^{-λ·v} P_λ(S̃_n = v); apply the
center bound to the tilted walk (its four atom masses are continuous in λ — a fixed
λ-box keeps them ≥ half the λ=0 values, so charFn_hold_decay generalizes with 768
doubled); optimize λ ≈ direction of (v - n·mean)/n. Alternatively do d=1 instances
(pascal_local_bound via iidSum_pascal_apply + Stirling; corpus
2026-06-19-mathlib-stirling-factorial-bounds.md) first — they are the same tilting
in one dimension and de-risk the design.

## Lap 28 (2026-07-10, fifth box session): (D) CHARACTER DECAY PROVED — charFn_hold_decay

`Prob/CharFn.lean`: `nd` (cyclic distance min(val, N-val)), **`nd_le_natAbs`** (any ℤ
representative bounds nd; emod/ediv case split, generalize-then-omega),
`exists_natAbs_eq_nd`, **`nd_sub_le`** (subadditivity via representatives),
`nd_cast`, `one_sub_re_stdAddChar_ge'` (Jordan in nd form).
`Sec7/Unroll.lean`: `pair_transfer` (helper) + **`charFn_hold_decay`**:
for N ≥ 4, `‖charFn (hold.map (modPair N)) ξ‖² ≤ 1 - ((nd ξ₁/N)² + (nd ξ₂/N)²)/768`.
Route: four atom masses through apply_le_map_apply, distinctness via N ∤ 1,2,3,
three pair anti-concentration bounds at differences (1,2),(0,2),(0,3), Jordan at the
pinned frequencies, nd-subadditivity triangle (ξ₁ = j₁ - j₂, ξ₂ = j₃ - j₂), linarith
assembly. ALL AXIOM-CLEAN. S3's 2-D kernel now needs only:

**(E) Gaussian summation (next lap)**: from `holdSum_toReal_le_charFn` +
`charFn_hold_decay`: P(holdSum n = v) ≤ N⁻² Σ_ξ (1 - (nd²-sum)/768N²·)^{n/2}...
concretely: ‖φ‖ⁿ = (‖φ‖²)^{n/2} ≤ (1 - D/768)^{n/2} ≤ exp(-nD/1536), D = (ndξ₁/N)²+(ndξ₂/N)².
Sum factorizes: N⁻²(Σ_{t : ZMod N} exp(-n(nd t/N)²/1536))². 1-D sum: index by
m = nd t ∈ [0, N/2], each m hit ≤ 2 times: ≤ 2Σ_{m≤N/2} exp(-nm²/(1536N²)).
At N = ⌈√n⌉+1 ≥ √n: n/N² ∈ [c,1], sum ≤ 2Σ_m exp(-m²·c/1536) = O(1) — bound the
series by geometric: exp(-am²) ≤ exp(-am) for m ≥ 1: Σ ≤ 1 + 1/(1-e^{-a}) etc.
→ **center-regime local bound**: P(holdSum n = v) ≤ C/(1+n) for ALL v (no Gweight
needed in center; the Gaussian factor of Lemma 2.2(i) comes from tilting (F) later).
Then state `hold_local_center` and wire toward `hold_local_bound`.

## Lap 27 (2026-07-10, fifth box session): (D) analytic core PROVED — pair bound + Jordan

`Prob/CharFn.lean`: `pairChar_conj`/`pairChar_mul_conj` (conjugate = negated argument),
`sum_toReal_eq_one` (finite PMF mass), **`charFn_normSq_pair_bound`** — the two-atom
anti-concentration bound `2·m₀·m₁·(1 - Re pairChar ξ (y₀-y₁)) ≤ 1 - ‖charFn r ξ‖²`
(double-sum expansion of normSq, all cross terms nonneg, single out (y₀,y₁)+(y₁,y₀));
**`one_sub_re_stdAddChar_ge`** — Jordan bound `8·(min(val, N-val)/N)² ≤ 1 - Re e(j/N)`
(cos → 2sin², Real.mul_le_sin both halves). Axiom-clean.

**(D) remaining assembly (next lap)**:
1. Push the four hold atoms through modPair N (apply_le_map_apply gives
   (hold.map (modPair N)) (y mod N) ≥ atom mass; equality not needed).
   Distinctness of images needs N ≥ 6 (atoms (2,5),(2,7),(2,8) differ in 2nd coord by
   2,3 < N; (1,3) vs (2,·) differ in 1st coord needs N ≥ 2; second coords 5,7,8 distinct
   mod N for N ≥ 6... actually 5≡8 mod 3 fine since 1st coords equal — need N ∤ 2, N ∤ 3,
   N ∤ 1 in coord combos: N ≥ 4 suffices for pairs used: check per-pair).
2. Per-pair: apply charFn_normSq_pair_bound with (y₀,y₁) ∈ {((2,5),(1,3)), ((2,7),(2,5)),
   ((2,8),(2,5))} — differences (1,2),(0,2),(0,3) — then Jordan at j = ξ·(1,2), ξ·(0,2),
   ξ·(0,3). Masses ≥ 1/16·1/4, 3/64·1/16, 1/32·1/16 → constants.
3. Triangle argument: dist(ξ₁/N,ℤ) + dist(ξ₂/N,ℤ) ≤ 2(d₁+d₂+d₃) where
   d_i = min-val-dist of the three pinned args (val arithmetic on ZMod: (ξ·(0,2)).val
   vs 2ξ₂.val mod N — work with the val-dist function zdist j := min(j.val, N-j.val)/N;
   key subadditivity: zdist(a+b) ≤ zdist a + zdist b, zdist(k·a) ≤ k·zdist a).
4. Combine: 1 - ‖φ‖² ≥ c·(zdist ξ₁² + zdist ξ₂²), c = 1/384-ish → ‖φ‖ ≤ exp(-c'·…),
   ‖φ‖ⁿ ≤ exp(-c'n(...)²).
5. (E): N⁻² Σ_ξ exp(-c'n·(zdist ξ₁²+zdist ξ₂²)) factorizes into 1-D sums; at N=⌈√n⌉+1
   the 1-D sum is O(1) (geometric domination); yields center-regime C/(1+n) bound.

## Lap 26 (2026-07-10, fifth box session): (D) nondegeneracy atoms PROVED

`Sec7/Holding.lean`: `hold_apply_pin` (first-coordinate pinning of hold atoms),
`hold_apply_two` (`hold (2, 3+b) = geomQuarter 2 · pascalNe3 b`), `pascalNe3_toReal`,
and the four numeric atoms `hold_apply_one_three/two_five/two_seven/two_eight`
(masses 1/4, 1/16, 3/64, 1/32 at (1,3),(2,5),(2,7),(2,8)). Difference set
{(1,2),(0,2),(0,3)} affinely generates ℤ² — the nondegeneracy input for (D).
All axiom-clean.

**(D) continued — next lap plan** (decay of `‖charFn (hold.map (modPair N)) ξ‖`):
1. `normSq_charFn_pair_bound`: for r : PMF (pair group) and atoms y₀ y₁,
   `‖charFn r ξ‖² ≤ 1 - 2·(r y₀).toReal·(r y₁).toReal·(1 - Re(pairChar ξ (y₀ - y₁)))`
   — expand `normSq (Σ m_y u_y)` as double sum (`Finset.sum_mul_sum` + `Complex.re` map_sum),
   `Σ_y m_y = 1` on finite group (PMF tsum_coe → Finset), drop nonneg off-pair terms
   (1 - Re(u ū') ≥ 0 via Complex.re_le_norm, norms 1).
2. `Re pairChar = cos(2π(ξ·w).val/N)` via ZMod.toCircle_apply + Complex.exp_re? — or
   avoid cos: `1 - Re(stdAddChar j) ≥ 8·(min j.val (N - j.val)/N)²` directly
   (1 - cos(2πt) = 2 sin²(πt), Jordan |sin πt| ≥ 2·dist(t,ℤ)).
3. Push hold atoms through modPair: (hold.map (modPair N)) y ≥ hold-atom mass at a
   preimage (apply_le_map_apply! already proved). For N ≥ 9 the four atoms map to
   DISTINCT pairs — mind collisions for small N (N ≤ 8 handle by crude bound or n small).
4. Assemble: three pair-terms give `1 - ‖φ‖² ≥ c·dist(ξ/N, ℤ²)²` (elementary triangle
   argument on t·(1,2), t·(0,2), t·(0,3); constant ≈ 1/384), then `‖φ‖ⁿ ≤ exp(-cn·dist²)`.
5. (E) Gaussian summation at N = ⌈√n⌉+1 → center-regime C/n local bound.

## Lap 25 (2026-07-10, fifth box session): (C2)+(C3) PROVED — finite Fourier inversion + charFn powers

`Prob/CharFn.lean` NEW, fully proved, axiom-clean: `sum_stdAddChar_mul` (1-D
orthogonality via `AddChar.mulShift` primitivity), `pairChar` product character +
norm/add lemmas, `sum_pairChar` (2-D orthogonality = product of 1-D), `charFn` (the
characteristic function, finite sum), **`charFn_inversion`** (exact Fourier inversion
for PMFs on `ZMod N × ZMod N`), `apply_toReal_le_sum_norm_charFn` (triangle form),
`toReal_bind_apply`/`sum_map_mul_complex` (finite-type PMF calculus),
`charFn_bind`/`charFn_map_add`/**`charFn_iidSum`** (r-hat of iid sum = r-hat^n),
**`iidSum_apply_toReal_le`** (`P(S_n = x) ≤ N⁻² ∑_ξ ‖r̂ ξ‖ⁿ`). In Unroll:
**`holdSum_toReal_le_charFn`** — the composite bound for the Hold walk, every N.

**Remaining for `hold_local_bound`** (all analysis, no more structure):
(D) character decay: `‖charFn (hold.map (modPair N)) ξ‖ ≤ exp(-c·‖ξ/N‖_dist²)` for
ξ ≠ 0 — from two/three explicit hold atoms (e.g. hold(1,3)=1/4, hold(2,4)=(4/3)(3/16)·(1/4)?
compute exact small atoms) via the two-atom identity `‖p·z₁+q·z₂+…‖ ≤ 1 - pq(1-cos θ)`
where θ = angle between atom characters; nondegeneracy: atoms (1,3),(2,5),(2,6) span ℤ²
affinely → the char cannot be unimodular-aligned unless ξ = 0. NOTE `hold` support lives
in ℕ×ℤ with unbounded coords; charFn is of the PROJECTED PMF, sum finite — decay constant
must be uniform in N: expect `1 - ‖φ‖ ≥ c·dist(ξ/N, 0)²` with dist = distance of
(ξ₁.val/N, ξ₂.val/N) to ℤ².
(E) Gaussian summation `N⁻² ∑_ξ (1 - c·dist²)^... ≤ C/n` at `N = ⌈√n⌉+1` — sum of
`exp(-cn·dist(ξ/N,ℤ²)²)` over the N² frequencies.
(F) exponential tilting wrapper (off-center regime) + Hold MGF strip finiteness
(= Lemma 7.6 engine, (7.30)). Center regime (i.e. |v - n(4,16)| ≤ √n) needs no tilt:
(D)+(E) alone give `≤ C/n ≤ C·Gweight/(1+n)` there. Do the untilted center case FIRST.

## Lap 24 (2026-07-10, fifth box session): circle-method probe — iidSum generic + mod-N entry PROVED

`iidSum` GENERALIZED to any `AddCommMonoid` (same proofs, omega→add_assoc);
`iidSum_map` (additive pushforward commutes with iid sums), `PMF.apply_le_map_apply`
(pushforward merges mass — the free-truncation observation: upper bounds via mod-N
reduction need NO tail argument), `holdSum_eq_iidSum` (Prod.fst_sum/snd_sum bridge),
`modPair`, and **`holdSum_le_modPair`** — circle-method step 1 for `hold_local_bound`:
`P(Hold_[1,n] = v) ≤ P(iid walk on ZMod N × ZMod N = v mod N)` for EVERY `N`. All
axiom-clean.

**Remaining S3 decomposition for `hold_local_bound`** (route now concrete):
(C2) finite Fourier inversion bound on `ZMod N × ZMod N`: `(r x).toReal ≤ N⁻² ∑_ξ
‖charFn r ξ‖` with `charFn r ξ := ∑_y (r y).toReal • eC((ξ₁ y₁ + ξ₂ y₂)/N)` (finite
sums; orthogonality of roots of unity — check mathlib `ZMod.dft`/`AddChar` inversion
or prove directly from geometric sums of `eC`);
(C3) `charFn (iidSum r n) ξ = (charFn r ξ)^n` (convolution multiplicativity via
`iidSum_succ` + cexpect product splitting);
(D) character decay `‖charFn (hold.map (modPair N)) ξ‖ ≤ exp(-c ‖ξ/N‖²)` for ξ ≠ 0
(the analytic crux; from hold's explicit mass: `hold (1, 3) = 1/4`, `hold (2, b)`
atoms give nondegeneracy in both directions — two-atom |φ|² identity);
(E) Gaussian summation `N⁻² ∑_ξ exp(-cn‖ξ/N‖²) ≤ C/n` with `N ≈ ⌈√n⌉`;
(F) exponential tilting wrapper for the off-center/exp regime + Hold MGF finiteness
on a strip (= Lemma 7.6 engine, (7.30)).
Choose N per (j,l)? No — N only enters (E); pick `N = ⌈√n⌉ + 1` uniformly.

## Lap 23 (2026-07-10, fifth box session): d=1 warm-up PROVED — negBinomial_apply + pascal_eq_map_iid

**Done (axiom-clean)**: `negBinomial_apply` — exact negative-binomial point mass
`P(|Geom(2)_n| = L) = C(L-1, n-1)·2^{-L}` by induction on `n` over the iid peel
(`tsum_iid_succ_mul`), convolution step = reindexed hockey stick
(`sum_range_choose_col`, `sum_Ico_choose_shift`); `pascal_eq_map_iid` — `pascal` IS
the 2-fold `Geom(2)` sum, immediate from `negBinomial_apply` at `n = 2` plus a
sum-zero support argument (`iid_geomHalf_sum_zero`, generic `PMF.iid_support_coord`
added to Prob/Basic). These give S3's Pascal instance an exact formula to work from:
`iidSum pascal n` = law of `|Geom(2)_{2n}|`, mass `C(L-1, 2n-1)·2^{-L}`.

**NEXT (S3 continued, per session mission)**: (a) the `iidSum pascal n =
iidSum geomHalf (2n)` splice (iid concat lemma) so `pascal_local_bound` reduces to
binomial estimates on `C(L-1, 2n-1)·2^{-L}` (Stirling recipe in corpus:
2026-06-19-mathlib-stirling-factorial-bounds.md); (b) probe the ZMod circle-method
decomposition for `hold_local_bound` (finite Fourier inversion on `ZMod N × ZMod N`,
exponential-tail truncation replaces the paper's `[-π,π]²` integral — no measure
theory); state the key intermediate lemmas.

## Lap 22 (2026-07-10, fifth box session): S3 front OPENED — Lemma 2.2 statements pinned

`Prob/LocalBound.lean` NEW: `Gweight` (2.2) factored from Unroll + `Gweight_pos/
_nonneg/_le_two`, `iidSum`, and Lemma 2.2(i)(ii) STATED (sorries) for `geomHalf`
(mean 2), `geomQuarter` (mean 4), `pascal` (mean 4): `*_local_bound` =
`C/√(1+n)·Gweight(1+n)(c(L-μn))`, `*_tail_bound` = indicator-tsum `≤ C·Gweight(1+n)(cλ)`.
`Sec7/Unroll.lean`: `holdSum` + `hold_local_bound`/`hold_tail_bound` (d=2, mean (4,16),
sup-norm; RATIFY-DRIFT notes: Gweight(1+n) vs G_n, ℕ index set, sup vs Euclidean norm).
Judge should ratify these vs paper pp.14-16 + p.42.

## Lap 21 (2026-07-10, fourth box session): Lemma 7.7 D6 layer — `fpDist` + (7.45) inequality

`Sec7/Unroll.lean` extended (all proved, axiom-clean, except the one named sorry):
* `fpDist : ℕ → PMF (ℕ × ℤ)` — the first-passage endpoint distribution (paper
  `v_{[1,k]}`, (7.44)) by budget recursion mirroring `Qstop`; normalization free
  from PMF combinators. Junk guard `d.2 ≤ 0` fires only on hold-null atoms.
* `fpDist_support_fst_pos`, `fpDist_support_snd_gt` — endpoints move right and
  overshoot the budget (`s < e₂`).
* `Q_le_fpDist_expect` — the (7.45) inequality in ℝ≥0∞ form:
  `ofReal (Q j l) ≤ Σ' e, fpDist s e · ofReal (Q (j+e₁) (l+e₂))` for every budget s.
  Strong induction over `Q_rec`, damping dropped (each factor ≤ 1). This is Case 2's
  (7.46) entry and Case 3's (7.53) at P = 0.
* `Gweight t x = exp(-x²/t) + exp(-|x|)` (paper (2.2)) and
  **`fpDist_location_bound` — Lemma 7.7 stated as the NEW NAMED SORRY** (X6):
  `(fpDist s (j,l)).toReal ≤ C·(e^{-c(l-s)}/√(1+s))·Gweight (1+s) (c(j-s/4))`,
  unconditional (LHS vanishes for l ≤ s by the support lemma).
  Numeric sanity: MC at s=40 → mode j ∈ {10,11,12} ≈ s/4+1, l ∈ {41,42,43} ✓.

**Attack routes for `fpDist_location_bound`** (the paper's pp.43–44 proof):
union bound over the last step (mirror: one `fpDist` unfold), `Hold` exponential
tail (Lemma 7.6 — provable from geomQuarter/pascalNe3 MGFs, finite products), and
the 2-D local bound Lemma 2.2 for iid `Hold` sums (node S3, the real wall; D5:
exponential tilting + circle method — `P(S_k = v) = (2π)^{-2} M(λ)^k e^{-λ·v} ∫|φ_λ|^k`).
NOTE: `fpDist` has no k-index — the D6 route needs a k-free reformulation of the
union bound, e.g. induction on s with the Gaussian weight as the induction invariant
(the paper's (7.33) reduction is already k-summed, which suits this form).

## Laps 18–20 (2026-07-10, fourth box session): X5 FULLY CLOSED — all three bridge sorries PROVED

**Done (axiom-clean)**: `hold_tsum_step` (7.29), `bridge_renewal` (7.27)≡(7.28),
`bridge_vector` (7.26)/(7.28). `Sec7/Bridge.lean` is now sorry-free;
**Proposition 7.3 (`renewal_white_encounters`) is fully proved modulo the single
Q-side sorry `Q_black_edge`** (its `#print axioms` sorryAx traces only through
`Q_polynomial_decay` → `prop_7_8` → `Q_black_edge`).

Infrastructure added (reusable): `PMF.tsum_bind_mul`/`tsum_map_mul`/
`tsum_iid_succ_mul`/`tsum_iid_zero_mul` (ℝ≥0∞ change-of-variables calculus),
`PMF.toReal_tsum_mul_ofReal`/`tsum_mul_ofReal_le_one`/`expect_iid_zero`/
`expect_iid_succ` (real expectation peeling for [0,1] observables) in
`Prob/Basic.lean`; `hold_tsum_expand`, `hold_tsum_step_real`, `pre_cons`,
`bridge_vector_gen` in `Sec7/Bridge.lean`. `bridge_renewal` gained a `0 ≤ ε`
hypothesis (Q_le_one summability).

Gotchas: `(3 + ∑ i, v i : ℤ)` elaborates cast-of-sum OR sum-of-casts depending on
context — spell `(3 : ℤ) + ∑ i, (v i : ℤ)` explicitly to match `hold`'s def;
`Fin.cons_succ` needs `(α := fun _ => ℕ)`; `congr 1` after `Fin.sum_univ_succ`
closes the i=0 head definitionally (don't bullet it); `if_congr` with `refine ?_`
holes gets stuck on Decidable instances — build the `Iff` in a `have` first;
`unfold PMF.expect; dsimp only` to beta-reduce before `rw [← tsum_mul_left]`.

**NEXT (the wall): `Q_black_edge` (Monotone.lean) — Lemma 7.7 D6 statement design.**
Handoff item 4: state the Chernoff/Gaussian first-passage endpoint bound over the
`Qstop` recursion (no infinite sequences; mirror the `Qstop` branch structure).
Paper Lemma 7.7 p.42–44, (7.30)–(7.33), Gaussian-type upper bound `G_k`. Then the
(7.50)/(7.51) white-exit constant (consumes proved `black_structure`) and Lemma
7.9's induction (X9) for the deep case. Parallel threads if blocked:
`key_fourier_decay` X1/X2 chain; S3 negative-binomial in Geometric.lean.

## After lap 11 (2026-07-10, third box session): `hold_weight_expect` PROVED

**Done** (axiom-clean): the (7.43) Case-1 geometric-expectation leaf
`hold_weight_expect` — `E[max(m-d₁,1)^{-A}] ≤ exp(ε³/2)·m^{-A}` for `m ≥ C_A`.
Chain: `hold_map_fst` (first marginal of `hold` is `geomQuarter`, by PMF monad laws) →
`hold_fst_marginal`/`hold_tsum_fst` (ℕ×ℤ-tsum marginalization via `ENNReal.tsum_prod'`)
in `Sec7/Holding.lean`; `geomQuarter_toReal`/`_tsum_toReal`/`_summable_toReal`/
`geomQuarter_tail` (exact tail `(3/4)^t`, injective-shift `hasSum`) in
`Prob/Geometric.lean`; then in `Monotone.lean` the three-region split
(head `k ≤ K` weight `(m-K)^{-A} ≤ (1+δ/3)m^{-A}` via `c := (1+δ/3)^{1/A}`;
middle `K < k ≤ m/2` mass `(3/4)^K ≤ (δ/3)2^{-A}` and weight `≤ 2^A m^{-A}`;
tail `k > m/2` mass `(3/4)^{m/2} ≤ (δ/3)m^{-A}` via
`summable_norm_pow_mul_geometric_of_norm_lt_one` → tendsto → threshold `T`).

**Lap 12 addendum**: `Q_white_case1` (Case 1 proper, (7.41)–(7.43)) PROVED,
axiom-clean — one `Q_rec` step at the white start pulls `exp(-ε³)`, `Q_le_Qm` at
depth `m-1` bounds each hold-atom landing (`half - (half-m+d₁) = m - d₁` by omega),
`hold_weight_expect` gives the `exp(ε³/2)m^{-A}` expectation, and
`exp(-ε³)·exp(ε³/2) = exp(-ε³/2)`. X7's remaining open pieces: Case 2 (black start,
paper (7.44) — needs the triangle/renewal input), the `prop_7_8` assembly from the
two cases, then `Q_polynomial_decay` by induction on `m` from (7.39) + Prop 7.8.

**Original route note (superseded)**: consume `Q_rec` + `Q_le_Qm` +
`hold_weight_expect`. Route: one step of `Q_rec` at the white start `(n/2 - m, l)`
pulls `exp(-ε³)`; each hold-atom `d` lands at `j = n/2 - m + d₁` with
`n/2 - (m-1) ≤ j` (d₁ ≥ 1), so `Q_le_Qm` (depth `m-1`) bounds the landed value by
`max(n/2 - j, 1)^{-A}·Q_{m-1}`; note `n/2 - (n/2 - m + d₁) = m - d₁` (ℕ, m ≤ n/2),
matching `hold_weight_expect`'s weight; needs `Qm_nonneg` to pull the constant
`Q_{m-1}` out of the tsum. Combine: `exp(-ε³)·exp(ε³/2) = exp(-ε³/2)`.
Then Case 2 (paper (7.44), black start) and the Prop 7.8 induction (X9).
Judge follow-up (b) DONE (lap 13): `check12` in `tools/check_blueprint.py` — the
(7.36)-bridge. Pascal-column DP (mirrors `renewal_white_encounters` LHS) vs
hold-jump DP (mirrors `E Q(Hold)` with the D6 recursion + `whiteSet` adapter);
agreement 1e-11 at n=14/16, incl. amplified damping (1/e, 0.5) where any
coordinate off-by-one would show at O(1). Renewal identity (7.26)≡(7.27) and the
paper-vs-0-based seam are pinned end-to-end. All judge follow-ups now closed.

## Lap 14 (2026-07-10): (7.45) unrolling — `Qstop`/`Qstop_eq` PROVED (X8/X9 entry)

New `Sec7/Unroll.lean` (axiom-clean): `hold_support_snd_ge`/`hold_zero_of_snd_lt`
(second coord of `hold` ≥ 3), `Qstop half W ε s j l` — the D6 stopped value (well-
founded on the height budget `s`; a step with `d₂ > s` = the paper's first passage
`l_{[1,k]} > s` lands on plain `Q`), and `Qstop_eq : Qstop s j l = Q j l` (∀ s) —
paper (7.45) verbatim, by strong induction on `s` over `Q_rec`. No stopping-time
measure theory needed. Case 2 (X8) and Lemma 7.9 (X9) both enter through this:
pick `s := l_Δ - l` per triangle; the overshoot branch's endpoint is what the
white-exit bound (7.50)/(7.51) + `Q_le_Qm` control.

**X8 next steps**: (a) a `Qstop_le` bound isolating the overshoot-branch endpoint
expectation (Case 2's (7.46)); (b) the endpoint-distribution facts need Lemma 7.7
(Chernoff for the 2D renewal walk) — the genuinely hard probabilistic kernel;
(c) the white-exit constant (7.50)/(7.51) consumes Lemma 7.4's structure
(`black_structure` proved) + 7.7. **X9**: `Z R j l` recursion on `R` over `Qstop`.

## Lap 15 (2026-07-10): `prop_7_8` ASSEMBLED — open core narrowed to `Q_black_edge`

`prop_7_8` (Prop 7.8, Q_m ≤ Q_{m-1}) is now PROVED modulo one named sorry:
`Q_black_edge` (Monotone.lean) — the (7.41) edge bound for black starts
(Cases 2–3, paper (7.44)–(7.67)). The assembly: `Real.iSup_le` over the `Qm m`
sup; interior points (`p₁ > half - m`) drop to `Q_{m-1}` via `le_Qm` at depth
`m-1` (same weight); edge points (`p₁ = half - m`, weight `m^A`) use
`Q_white_case1` (white) or `Q_black_edge` (black), with the `m^A·m^{-A}` rpow
cancellation. Gotcha: the sup-subtype projections `(⟨(p1,l),_⟩).1` block omega —
normalize with defeq `have`/`show` bridges first.

**The X7→X11 chain now rests entirely on `Q_black_edge`**, whose route is:
`Qstop_eq` (proved) + Lemma 7.7 Chernoff (X6, the hard probabilistic kernel) +
white-exit (7.50)/(7.51) (consumes `black_structure`, proved) for Case 2; +
Lemma 7.9 induction (X9) for Case 3. Next: state Lemma 7.7 (D6 form) and the
Case 2/3 split of `Q_black_edge`; then `Q_polynomial_decay` from `prop_7_8` +
`Qm_le_rpow` by forward induction on m (tractable now).

## Lap 16 (2026-07-10): `Q_polynomial_decay` PROVED (from prop_7_8)

(7.37) closed: forward induction on `m` — below the threshold `Cb := max C0 1`
use `Qm_le_rpow` ((7.39)); above, `prop_7_8` steps down; gives the uniform bound
`Q_m ≤ Cb^A`, then `Q_le_Qm` at depth `n/2 - j` (strip interior) or `Q_le_one`
(past the edge, weight 1). Constant `C := Cb^A`. Depends on `Q_black_edge` via
`prop_7_8` — the whole §7.4 chain is now a cone over that single sorry.
Gotcha: standalone `have h := Q_le_Qm ...` needs `(l := l)` (implicit `l`
unconstrained). Next: the (7.36) seam in Decay.lean (E Q(Hold) ≪ n^{-A} from
`Q_polynomial_decay` + `hold_tsum_fst`-style Geom(4) tail), or start Lemma 7.7's
D6 statement for `Q_black_edge`.

## Lap 17 (2026-07-10): Prop 7.3 (`renewal_white_encounters`) ASSEMBLED — X5 seam named

New `Sec7/Bridge.lean`: `Rcol` (the per-column D6 form of the (7.28) product) and
`renewal_white_encounters` (MOVED from Holding.lean) now PROVED modulo three named
X5 sorries, all numerically pre-validated by harness check12:
- `bridge_vector` — iid-Pascal-vector expectation = `Rcol 0 0` (induction on length
  peeling `Fin.cons`; `pre (cons a v) (i+1) = a + pre v i`, `Fin.succ` filter reindex);
- `hold_tsum_step` — the (7.29) one-column self-similarity of `hold` in tsum/ℝ≥0∞ form
  (split `geomQuarter` at `k = 1`, peel one `pascalNe3` off `PMF.iid`);
- `bridge_renewal` — `Rcol j l = Σ' d, hold(d)·Q((j,l)+d)` (downward induction on
  `half - j` via `hold_tsum_step` + `Q_rec`; boundary `j ≥ half` needs `d₁ ≥ 1`).
The analytic assembly (trivial small-n bound; `Q_polynomial_decay` pointwise +
`hold_weight_expect` at `m = n/2` + `(n/2)^{-A} ≤ 3^A n^{-A}`) is fully proved.

**Open ledger for the §7 probability side is now**: `Q_black_edge` (X8/X10 kernel) +
the three X5 bridge sorries + `key_fourier_decay`'s reduction chain (X1/X2, Fourier
side) + upstream S-chain. Next: prove `hold_tsum_step` (most mechanical of the three),
then `bridge_renewal`, then `bridge_vector`.

## After laps 6–10 (2026-07-10, second box session): **X3 HEAD CLOSED — Lemma 7.4 PROVED**

`black_structure` is now a theorem, `#print axioms` = `[propext, Classical.choice,
Quot.sound]`. The whole chain, all in `Sec7/Triangles.lean`:
`θq_left_run` → `θq_fibre_eq` (exact ℚ fibre identity `θ(j,l) = 9^{j-j*}2^{l*-l}θ*`)
→ `fibre_le_eps`/`corner_phase_pos`/`black_mem_corner_triangle` (Δ*-membership) →
`wb_row_left/right` + `white_row_above` (Claim (*) Cases 2–3 engine) + `lstar_eq_of`/
`jstar_eq_of` (Nat.find corner characterization) → `black_of_mem_corner_triangle`
(Δ* black) + `corner_triangle_confined`/`_strip` (confinement, log numerics) →
`corner_eq` (corner invariance = fibre equality) → assembly via `cornerTriple` image,
`lattice_sq_dist_ge_one`, `sep_const_sq_le_one` (`10¹² ≤ 2⁴⁰` trick for
`(1/10)log(10⁴) < 1`). Note: at ε = 10⁻⁴ the separation conjunct reduces to lattice
disjointness — Case 1 proper was not needed for Lemma 7.4 itself (our fibre identity is
exact where the paper's (7.18) is an inequality). Also done: `unifOddMod` normalization
(judge follow-up a).

**Judge follow-ups still open**: (b) the (7.36)-bridge harness check in
`tools/check_blueprint.py` (judge item 9); (c) Case 1 proper statement per judge item 8
spec (needed for the Q-recursion / Lemma 7.9 series, NOT for Lemma 7.4 — see above).

**Next hardest open obligations** (X3 done → move up the chain): Lemma 7.9 induction
skeleton over `Q_rec` (X9) consuming `Q_white_contract`/Case 1; the (7.45) unrolling
statement design (X8); S3's d=1 negative-binomial half; `renewal_white_encounters`
(Prop 7.3) probabilistic side.

## After lap 5 (2026-07-10)

**Done** (axiom-clean): (a) (7.18) inequality forms — `sfrac_mem`/`sfrac_eq_self`/
`sfrac_idem`, `θq_succ_j_abs_le`, `θq_pred_l_abs_le`, `θq_iterate_abs_le`
(`|θ(j+a,l-b)| ≤ 9^a 2^b |θ(j,l)|` unconditional); (b) the corner map:
`exists_white_above` (via `black_run_le` + archimedean), defs `upRun`/`lstar`/
`leftRun`/`jstar` (Nat.find, classical), spec lemmas `black_of_le_lstar`, `le_lstar`,
`white_above_lstar`, `leftRun_pos`, `black_of_jstar_le`, `jstar_maximal`.
NOTE: our `sfrac` range is `[-1/2, 1/2)` (mirror of the paper's `(-1/2, 1/2]`);
only `|sfrac|` is used and denominators are odd, so no discrepancy — documented at
`sfrac_mem`.

**X3 next**: the corner triangle fibre. Key lemma to state and prove next
(paper (7.17)–(7.18) + Claim (*) — the heart of Lemma 7.4):
  `theorem mem_corner_triangle`: for black (j,l) in the strip, with (j*,l*) its corner
  and s* := log(ε/|θ(j*,l*)|) ≥ 0: `9^(j-j*)·2^(l*-l)·|θ*| ≤ ε` (i.e. (j,l) ∈ Δ* as a
  ℚ-inequality — the ℝ-log triangle membership is monotone algebra on top).
  Route: |θ(j,l)| ≤ ε (black) and θ(j,l) = 9^(j-j*)2^(l*-l)θ* by θq_iterate_exact
  — but the iterate goes from the corner DOWN to (j,l): need the scale < 1/2 premise,
  which needs Claim (*) Case-1-style reasoning (if the scaled value exceeded ε it
  wraps...). Careful: the correct paper route is (7.18) with equality "whenever the
  RHS is strictly less than 1/2". Plan: prove by strong induction down the run using
  the run lemmas (each step black keeps values ≤ ε ≤ 1/4, so exact steps apply and the
  product never wraps). Concretely: (j,l) black, everything between (j,l*)..(j,l) black
  (black_of_le_lstar column) and (j*,l*)..(j,l*) black (row) — then iterate exact steps
  along row then column, all values staying ≤ ε.
  CAUTION: intermediate points of Δ* are NOT all on the row/column path; but the paper's
  Δ* membership only needs the (j,l)↔corner relation, and the run lemmas give exactly
  the path needed. |θ(j,l)| = 2^(l*-l)|θ(j,l*)| (θq_up_run) and
  |θ(j,l*)| = 9^(j-j*)|θ(j*,l*)| (row version of up_run — NEEDS a leftward run-exact
  lemma `θq_left_run`, same proof shape as θq_up_run using θq_succ_j_exact on black row
  points: TO WRITE).
  Then fibre equality Δ* = {p : black, corner p = (j*,l*)} and Claim (*) cases.

## After lap 4 (2026-07-10)

**Done** (axiom-clean): `θq_iterate_j`, `θq_iterate_l`, `θq_iterate_exact` — the (7.18)
equality-case scaling `θ(j+a, l-b) = 9^a·2^b·θ(j,l)` when the final scale is < 1/2 (the
triangle-fibre engine); `θq_up_run` (upward black run ⇒ exact doubling downward) and
`black_run_le` (`2^t ≤ ε·3^{n-2j}` caps upward black runs ⇒ paper's l* exists).

**X3 remaining for `black_structure`**: (a) leftward run at l* (j*-existence — runs
hit j=0 or a white point; finite by construction, no analytic input needed);
(b) DEFINE the corner map + triangle size (`s* := log(ε/|θ*|)` — lives in ℝ, ties ℚ-θ
to the ℝ-triangle (7.11)); (c) fibre equivalence via `θq_iterate_exact` both directions
(Claim (*) Cases 1–3 using claims (i)–(iii)); (d) assemble. This is now bounded work but
a lot of it — decompose into named sorries inside Triangles.lean when starting assembly.

## After lap 3 (2026-07-10)

**Done**: (7.16) formalized — `θq_lower_bound` (`3^{-(n-2j)} ≤ |θ(j,l)|` for ξ coprime
to 3, `2j+1 ≤ n`, via the ±1/3-mod-ℤ 3-adic argument: `sfrac_phase_absorb` +
`abs_sfrac_le` + argRel scaling) and `black_nine_le` (black ⇒ `n - 2j ≥ 9`). All
axiom-clean. This is the strip-confinement input to Lemma 7.4's conjunct 4.

**Next attack on X3 (`black_structure`)**: with (7.16) + claims (i)–(iii) in hand, the
remaining Lemma 7.4 ingredients are (a) l*-existence: an upward black run from a black
point terminates (uses `black_nine_le` at growing powers via `θq_pred_l_exact` doubling:
|θ(j,l')| = 2^{l-l'}|θ(j,l)| forces whiteness once above ε... paper argument p.38 uses
3^{n+1-2j}2^{l-l'}ε ≥ 1/3 — formalize as: black run upward of length > log₂(3^{n-2j}ε)
impossible); (b) j*-existence (leftward run hits j=1); (c) the Δ* fibre equivalence
(7.17)/(7.18) — the equality case identity |θ(j',l')| = 9^{Δj}2^{Δl}|θ*| when RHS < 1/2,
provable by induction from the two exact lemmas.

## After lap 2 (2026-07-10)

**Done this lap** (all `#print axioms`-clean, build green):
- `Sec7/Triangles.lean`: θ-identity exactness (`θq_succ_j_exact`, `θq_pred_l_exact` —
  no-wraparound forms of (7.13)/(7.14)) and the paper-p.38 weakly-black claims
  (i) j-form + l-form, (ii), (iii) (`black_of_weaklyBlack_succ_j/pred_l`,
  `weaklyBlack_of_succ_j_pred_l`, `weaklyBlack_of_pred_j_pred_l`). These are the engine
  of every case of Lemma 7.4's Claim (*).
- `Sec7/Monotone.lean`: `Q_white_contract` (Case 1 warm-up) and `Qm_le_rpow` (7.39,
  the Prop 7.8 induction base) proved.

**Crux state / next attack** (hardest-first):
1. **X3 — Lemma 7.4 `black_structure`**: claims (i)–(iii) now proved. Next: formalize
   (7.16)-strip confinement (`black → j ≤ n/2 - (1/10)log(1/ε)`; needs the "ξ·3^{n-1}·…
   is 1/3 or 2/3 mod 1" 3-adic step), then l*/j* existence (finite runs: the check-8
   argument — upward black runs terminate since 3^{n+1-2j}2^{l-l'}ε ≥ 1/3 fails), then
   the (7.17)/(7.18) triangle-fibre equivalence. Decompose into named sub-sorries in
   Triangles.lean next lap.
2. **X8 Case 2 / X9 Lemma 7.9 skeleton**: (7.45) iterate of `Q_rec` (unrolling along the
   first-passage time) is the next structural lemma; needs a finitized stopping-time
   unrolling over `Q` — statement design work.
3. **S3 (Lemma 2.2)**: untouched; awaits D5 tilting route. Consider starting the d=1
   exact-formula half (negative binomial Gaussian bounds) as an independent thread.

**Notes / traps recorded**: triangle sizes are NOT O(log 1/ε) (giant triangles exist,
harness check 8); Lemma 7.4 separation is between point SETS (statement fixed lap 1).
