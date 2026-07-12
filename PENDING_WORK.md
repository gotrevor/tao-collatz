# PENDING WORK (kept current per lap; newest on top)

## Lap 56 (review + crux advance): white-exit kernel DECOMPOSED; reduction glue + overshoot exclusion PROVED

Review: X9 `many_triangles_white` verified CLOSED modulo exactly
`fpDist_white_exit_deep` (`#print axioms` = trust base + `sorryAx`;
`encExpect_entered_le` axiom-clean). Directive promoted the shared white-exit
kernel to THE active move; STATUS + DIRECTION refreshed (commit `2d9747c`).

**Crux advance** (`Sec7/ManyTriangles.lean`, commit pending): `fpDist_white_exit_deep`
is now **PROVED** from a clean (7.50)-geometry decomposition. The old monolithic
sorry → two named analytic sub-sorries + one proved helper + axiom-clean glue:

- **`endpoint_notMem_start_triangle`** (PROVED, axiom-clean): the (7.50) "clears
  the apex" step. `fpDist_support_snd_gt` gives `s < e.2`; with `s = l_Δ - l` the
  phase height `l+e.2 > l_Δ`, and `triangle` needs height `≤ l₀`, so the endpoint
  is outside the START triangle. This is why `phaseInFamily` = the FOREIGN mass.
- **`outStripSet` / `phaseInFamily`** (new defs): the two complement pieces of the
  white strip. Split via `white = ¬black` + `F.cover`: an endpoint is bad ⟺ its
  phase point overshoots `⌊n/2⌋` (out-of-strip) OR its phase point (`(q.1-1,q.2)`)
  lands in some family triangle (non-white). Cover needs `p.1+1 ≤ n/2`, supplied
  by ¬out + `1 ≤ n/2-m+e.1`.
- **Reduction glue** (PROVED, axiom-clean): pointwise `1_W(q) ≥ 1 - 1_out(q) -
  1_tri(q)`, then `∑ fpDist·(1-1_out-1_tri) = 1 - outMass - triMass` (via
  `Summable.tsum_sub` + `fpDist_tsum_toReal`) `≥ 1 - 1/8 - 1/8 = 3/4`, and
  `tsum_le_tsum` lifts the pointwise bound. `p₀ := 3/4 > 1/2` clears the chain cap
  comfortably (numeric white-exit mass ≈ 0.99, harness check 9).

**Next attack — the two residual analytic sub-sorries** (both consume X6
`fpDist_location_bound`; both are the SAME geometry shared with X8's Case-2 twin):

1. **`fpDist_out_of_strip_le`** (`≤ 1/8`): Gaussian `j`-tail. From X6,
   `(fpDist s (j,l)).toReal ≤ (D·K)·exp(-cF·(l-s))/√(1+s)·Gweight(1+s, cF·(j-s/4))`.
   Sum over `j = ⌊n/2⌋-m+e.1 > ⌊n/2⌋` (i.e. `e.1 > m`) and all `l`. The budget
   `s·log2 ≤ (m+2)·log9` (derive via `budget_le_of_mem_triangle` at the phase
   point `(⌊n/2⌋-m-1, l)`, `hjm : ⌊n/2⌋ ≤ (⌊n/2⌋-m-1)+1+m`) gives `s/4 ≤ 0.8m`,
   so `e.1 > m` is a `≥ ~0.2m ≥ ~3s/4·(…)` right-deviation of a Gaussian centered
   at `s/4` with scale `√(1+s)` — tail `≤ 1/8` for `m ≥ Cthr`. PROBE FIRST: does
   X6's `Gweight` sum over a half-line give an explicit exp-small bound? (check
   `Gweight` def + any existing `∑ Gweight` lemma in `FpLocation`/`LocalBound`.)
2. **`fpDist_any_triangle_le`** (`≤ 1/8`): the separation fight. `phaseInFamily`
   mass = foreign mass (start excluded). Each foreign triangle t'' is
   `(1/10)log(1/ε) ≈ 0.92` from t (`F.separated`); the (7.11) slope band confines
   the endpoint to an `O(1)` slab about t's diagonal; sum the Gaussian envelope
   over the `≫`-separated foreign apexes (reuse the `apex_separation` +
   Gaussian-AP engine that X10 uses). This is the genuinely hard half.

**Derive X8's twin**: `fpDist_white_exit` (BlackEdge.lean) has the SAME conclusion
+ the extra `s ≤ m/log²m` hyp (unused for whiteness). Once the two sub-sorries
land, `fpDist_white_exit` follows by discarding that hyp and reusing the same
decomposition (or citing `fpDist_white_exit_deep` directly — `p₀ = 3/4 > 0`).

## Lap 55 (cont-2): **LEMMA 7.9 CLOSED (modulo its one kernel)** — `many_triangles_white` PROVED

Directive step 2 done in the same lap as the design. The (7.57) pin is now a
THEOREM; `#print axioms many_triangles_white` = trust base + `sorryAx` via
exactly `fpDist_white_exit_deep` (the pinned external input, directive step 3).
New machinery, all verified `[propext, Classical.choice, Quot.sound]`:

- `encExpect_block_le` GENERALIZED: the `s/3 + 1 ≤ T` horizon hypothesis is
  REPLACED by `∀ e, encVal ε R σ ≤ f e` — the bridge now holds at EVERY horizon
  (short-horizon leftovers keep `encVal` constant mid-block and `fpDist` has
  mass 1, so the pointwise domination absorbs them). This removed the entire
  small-`T` case split the lap-54 plan was stuck on.
- `encExpect_wander_le` hfresh RESTRICTED to the entered class (`∀ hcov`-form
  over `coveringTriangle` — proof-irrelevance makes the barrier field equation
  rewrite cleanly). This kills the divergent general-fresh Z-channel: wander
  encounters always normalize onto ENTERED states.
- **`encExpect_entered_le` (the Y-induction, AXIOM-CLEAN)**: entered states are
  ≤ `encChainX ε p₀`, by induction on the budget `R`; per block the bridge maps
  exits through `f = 1_W + e^εX·1_{¬W}`; instant re-encounters normalize via
  `encExpect_normalize_init` (white banks `e^{ε−1}X ≤ 1`), wander exits carry
  their credit into the wander lemma; the fixed point
  `e^εX − (e^εX−1)p₀ = X` (`encChainX_fixed`) closes the induction. The white
  mass `≥ p₀` enters as HYPOTHESIS `hwhite`, so this theorem is clean.
- `many_triangles_white`: init = credit-0 wander state; `ε₀ := min(1/100,
  (2p₁−1)/2)` with `p₁ := min p₀ 1`; smallness via `e^ε(1−ε) ≤ 1`; final bound
  `max 1 (e^ε·X) ≤ e^{2ε}` via `encChainX_le_exp`. Gate `g := Cthr` of the
  kernel — exactly what makes `hwhite` available at every gated encounter.
- `fpDist_tsum_toReal` helper.

**Note for the judge**: `encounter_two_mass_bound` / `encounter_vertex_bound`
ended up NOT consumed by the final gluing (the fixed-point computation is done
inline via `encChainX_fixed` in `encExpect_entered_le`); they remain as the
ledger's documentation/alternate route.

**Next (directive step 3)**: `fpDist_white_exit_deep` — X9's only remaining
input; prove GENERAL then derive X8's `fpDist_white_exit`. Route: X6
`fpDist_location_bound` concentration + `fpDist_support_snd_gt` top-clearing +
X3 separation excludes other triangles + in-strip via `s = O(m)` ((7.52)).
Then X10 (fpDistPlus location bound first).

## Lap 55 (cont): DEPTH-GATED FOLD LANDED — directive step 1 done, X9 gluing unblocked

`encStep`/`encExpect` now carry a gate `g : ℕ`: the encounter condition's strip
conjunct is `q₁ + g ≤ n/2` (so `g = 0` IS the previously-ratified encoding,
definitionally). All ten fold lemmas threaded and re-verified
`[propext, Classical.choice, Quot.sound]` (real runs): succ/le/of_count_ge/anti/
normalize(_init)/of_edge/wander_le/shift/block_le. `encExpect_of_edge` is now the
SHALLOW freeze (`n/2 < pos₁ + g ⟹ encExpect = encVal`) — exactly the near-edge
case of the Z-induction. `many_triangles_white` re-pinned with `∃ g : ℕ` and a
SECOND DEVIATION docstring (near-edge gate; paper anchors (7.59)/p.50/p.51 +
consumer verification vs (7.54)/p.55). **Judge: re-ratification requested** — the
encounter-fold encoding and the (7.57) pin both changed (pass-12 tripwire
anticipated this).

Gotcha: the block bridge's observable was named `g` (`∀ g : ℕ × ℤ → ℝ`) and
shadowed the gate — renamed to `f` inside `encExpect_block_le` only.

**Next (directive step 2)**: the Z-induction gluing of `many_triangles_white`,
per the lap-54 cont-4 plan, now with the near-edge branch discharged by
`encExpect_of_edge` (frozen, value = encVal ≤ e^{ε·count−banked}; entering states
have banked ≥ ... handle via the normalized fresh-state shape) and every gated
encounter deep enough for `fpDist_white_exit_deep`. Fresh states: `Z(ρ) := sup`
over `⟨q, b, 0, 0, 0⟩` of `E_ρ`; induction on ρ; per block `encExpect_block_le`
with the two-mass split (`encounter_two_mass_bound`, monotone in Z above the
fixed point); white mass from `fpDist_white_exit_deep` (still the open external
input — directive step 3).

## Reflection — 2026-07-12 (lap 55, deep reflection; strong-model altitude pass)

### Route verdict: **CONTINUE** — no registered trigger has fired

- **T1** (D6 finitization forces measure theory): tested and CLEARED in lap 52 —
  the encounter-fold encoding carried the head-peel recursion, block bridge,
  CLAIM-G coupling, all proved axiom-clean. No infinite-product measure anywhere.
- **T2** (ε = 10⁻⁴ separation too weak for the (7.65) Σ-sum): re-grounded against
  the actual pp.52–54 text this lap. The ≫s′ separation of Σ comes from Lemma
  7.4's *integer-disjointness* of apex intervals plus (7.60) `s′ ≥ CA²(1+p)` —
  NOT from the raw 0.92 constant — and that geometric core is already PROVED
  (`apex_gap`, `apex_separation`, `not_mem_two`). T2 is unlikely to fire; keep it
  registered until the Σ-sum closes in Lean.
- **False-summit check**: laps 50–54 closed X6, X1, X2, X5 as whole nodes, each
  re-verified clean this lap with real `#print axioms` runs. No recurring
  "almost-cracked" claim; the one confidence downgrade (X9 75→70) had a concrete
  cause (the confirmed paper gap). This is real motion, not circling.
- **Destination check**: no prior art (web-checked 2026-07-12; nothing beyond
  unrelated conditional/full-conjecture Collatz artifacts). Full discharge
  remains the realistic endpoint: every kernel attacked so far has fallen, and
  nothing on the remaining path looks generational.

### The load-bearing finding: X9's near-edge regime is a STATEMENT-truth risk

The lap-54 "NEEDS DESIGN" caveat is sharper than recorded. `fpDist_location_bound`
is unconditional in `s`, but the white-exit lower bound genuinely FAILS at depth
`m < Cthr` (the endpoint's `j`-advance `≈ s/4 = O(m)` can leave the strip: the
whiteStrip mass really does collapse near the edge — it is not merely
unprovable-with-current-tools). Since `many_triangles_white` quantifies over ALL
starts and ALL `TriangleFamily` instances, an adversarial family stacked along
the drift line in the edge strip can chain near-edge encounters whose `e^ε`
payments have no white-exit compensation. **The pinned `exp(2ε)` is plausibly
FALSE as stated.** The paper's own proof glosses exactly this: its (7.59) step
says "repeating the proof of (7.51)" — but (7.51)'s geometry needs the triangle
deep. This is a second literature hole adjacent to the judge-confirmed banking
gap (pass 9).

Two fixes, BOTH verified this lap against the actual consumer (pp.49 + 55 read
in full):

1. **Depth-gated fold (RECOMMENDED — keeps `exp(2ε)`)**: change `encStep` to
   count an encounter only when the covering triangle sits at depth
   `≥ Cthr` (equivalently `pos₁ ≤ n/2 − Cthr` at encounter time, `Cthr` = the
   white-exit threshold). Consumer-safe: in Case 3 the surviving branch of the
   (7.54) split has `j_{[1,k+P]} < 0.9m`, so the walk stays at depth `≥ 0.1m ≥
   Cthr` (Case 3 has `m ≥ C_{A,ε}`) throughout the (7.67) window — every
   encounter the deterministic claim produces IS deep, so `r ≥ R` still holds
   with the gated count. Cost: rework `encStep` + re-prove ~3 short lemmas
   (`encExpect_of_edge` → `encExpect_of_shallow`: below the gate the fold's
   count/banked freeze, so `encExpect = encVal`), and judge re-ratification of
   the encoding (pass-12 tripwire anticipated an edit here).
2. **∃C re-pin (FALLBACK)**: `encExpect ≤ C` for an absolute `C`. Provable with
   machinery on hand: `pos₁` strictly increases per step (Hold's first coord
   ≥ 1), so the walk spends ≤ `Cthr` steps below the gate line, hence ≤ `Cthr`
   uncompensated encounters, hence a pathwise factor `e^{ε·Cthr}`; total
   `C = e^{2ε + ε·Cthr}`, uniform in `n, ξ, F, R, T, start`. Consumer absorbs
   it: p.55 applies Markov at threshold `10^A`, giving `P(F_*) ≤ C·10^{−A−2}`,
   and Prop 7.3's `∀A` quantifier eats any absolute constant (the paper's
   (7.56) target is "say"-slack).

Either way the X9 assembly becomes downhill — all other ingredients
(`encExpect_block_le`, `encounter_vertex_bound`, `encExpect_normalize(_init)`,
`encExpect_wander_le`, two-mass bound, chain fixed point) are proved. The
two-mass ledger generalizes monotonically to any `Z ≥ encChainX` (the vertex
inequality `p₀ + (1−p₀)e^εZ ≤ Z` is monotone in `Z` above the fixed point), so
mixing the deep bound with a larger edge constant costs nothing.

### Second finding: the p₀ > 1/2 certification burden is softer than recorded

The paper only ever proves white-exit mass "`≫ 1`" at (7.59) — it never needs
1/2. Our corrected ledger needs `p₀ > 1/2` only for the *clean* `exp(2ε)`
constant: for any certified absolute `c₀ > ~ε` the chain value is
`exp(O(ε/c₀))` — absolute, hence consumable by the same p.55 argument. So if
certifying `p₀ > 1/2` through X6's (non-sharp) Gaussian constants fights,
`fpDist_white_exit_deep` may be weakened to `∃p₀ > 0` plus an explicit numeral
`c₀` (e.g. 1/100) without route damage. Judge pass-9's rider stands but is a
constant-quality question, not feasibility.

### X10 re-rated (up): volume, not novelty

Read pp.52–54 in full against the Lean state. The proof is: (7.60) triviality
reduction; escape event E′ = two tail bounds (Lemma 7.7 = X6 ✓ + Lemma 2.2 = S3
✓, applied to `fpDistPlus`); the (7.63)–(7.65) geometric implication (elementary,
apex core already proved); the Σ mass sum = per-point Gaussian location bound
summed over a ≫s′-separated set = `(1/s′)` × the existing Gaussian-AP engine
(`sum_range_exp_neg_sq_le` family). ONE genuinely new prerequisite: a
**fpDistPlus location bound** — Lemma 7.7's bound convolved with `p` extra iid
Hold steps ("(7.48) as before", then Lemma 2.2 for the `l`-tail of the added
steps). Name it, prove it first; the rest is assembly. Confidence 70% → ~78%.

### KEEP / STOP / bookkeeping

- **KEEP**: hardest-first inside §7; per-lemma `#print axioms` verification; the
  judge's statement-ratification loop (it caught the banking gap — it is
  earning its cost); committing every green build.
- **STOP**: carrying the stale "24/26 open sorries" number — ground truth is
  **20** (7 crux: BlackEdge ×4, ManyTriangles ×3; 13 spine stubs). Also stop
  listing X4/X7 as open in prose: `Holding/Monotone/Bridge.lean` are sorry-free;
  their blueprint rows deserve ✅ at the next judge pass.
- **Kernel merge (architecture)**: prove `fpDist_white_exit_deep` GENERAL and
  derive X8's `fpDist_white_exit` from it (its extra `s ≤ m/log²m` hypothesis is
  used only for edgeWeight degradation, per its own docstring) — collapses two
  open kernels into one obligation.

### Priority order (binding version in DIRECTION.md)

1. X9 near-edge design: implement the depth-gated fold (fallback: ∃C re-pin);
   flag the edited statement for judge re-ratification; then close
   `many_triangles_white`.
2. `fpDist_white_exit_deep` (then derive the X8 twin).
3. X10: fpDistPlus location bound → E′ → separated-Σ assembly.
4. X11 assembly (`Q_black_edge_case3` internals) + X8 assembly.
5. C8 pin (last RED) opportunistically; spine stubs stay frozen.


## Lap 54 (cont-4): X9 gluing pieces PROVED — wander claim, edge freeze, two-mass bound, fixed point

**Route simplification found while gluing (supersedes the four-mass LP shape):**
the LP collapses to TWO masses. White-credit branches are all ≤ 1 pathwise
(white re-encounter banks the credit: `e^{ε−1}X ≤ e^{2ε−1} ≤ 1`; never-encounter
ends at `encVal = 1`; out-of-strip exit freezes at `encVal = 1` since `pos₁` is
non-decreasing so `pos₁ > n/2` kills the encounter condition forever). Only the
in-strip-black instant-re-encounter mass `d` pays `e^ε·X`, and
`d ≤ 1 − P(whiteStrip exit) ≤ 1 − p₀`. Proved axiom-clean this pass:
- `encChainX_fixed`: `p₀ + (1−p₀)e^εX = X`.
- `encounter_two_mass_bound`: `(1−d) + d·e^εX ≤ X` for `d ≤ 1−p₀`.
- `encExpect_of_edge`: `pos₁ > n/2 ⟹ encExpect = encVal` (fold frozen).
- `encExpect_wander_le`: between-blocks wander with credit `w₀`:
  `E_{R'+1}(T, ⟨p,b,0,w,0⟩) ≤ max 1 (e^ε e^{−w₀} Z)` given fresh-state bound `Z`
  at budget `R'` (T-induction; encounter branch via `encExpect_normalize_init`
  handled ABSTRACTLY — set σ' := encStep …, prove count/banked/cumWhite field
  equations, never name the coveringTriangle barrier).

**Remaining for `many_triangles_white`** (the Z-induction on budget ρ):
`Z(ρ) := sup over fresh states E_ρ(T, ⟨pos,bar,0,0,0⟩) ≤ X` by induction on ρ:
base ρ=0 frozen (`encExpect_of_count_ge`, encVal=1 ≤ X); step: block bridge
`encExpect_block_le` (s := (bar − pos₂).toNat; for non-in-triangle fresh states
s=0 works) with `g e :=` case-split on the endpoint `pos+e`: (i) instant
encounter (encStep enters count 1) → normalize → `e^ε e^{−1_W} Z(ρ−1)`;
(ii) no encounter, in-strip → wander claim with w₀ = 1_W(endpoint);
(iii) `pos₁+e₁ > n/2` → edge freeze value 1. Uniform g-bound:
`g e ≤ if (pos+e) ∈ whiteStrip then 1 else e^ε·X` — the white instant-encounter
case needs `e^{ε−1}X ≤ 1` (`hXe` of the vertex lemma, holds for ε ≤ 1/4 say);
then `Σ' fpDist·g ≤ (1−d) + d e^εX ≤ X` via `encounter_two_mass_bound` with the
white mass from `fpDist_white_exit_deep`. CAVEAT to verify while gluing: the
fresh state entering the Z-claim comes from an encounter at q with (q₁−1, q₂) in
triangle t — matching `fpDist_white_exit_deep`'s start shape needs m := n/2 − q₁
≥ Cthr; for q₁ > n/2 − Cthr (near the edge) the white-exit bound is unavailable —
handle by a separate edge-strip argument (endpoints there leave the strip in
O(Cthr) blocks... or weaken: for those states use the trivial value ≤ e^εX and
argue they only occur ≤ once? NEEDS DESIGN — this is the open faithfulness risk
of the gluing, alongside the p₀-vs-strip-height bookkeeping inside
fpDist_white_exit_deep itself). Then `many_triangles_white` = init case:
s=0 block + `g ≤ e^εX` uniformly + `X ≤ e^ε` ⟹ `≤ e^{2ε}`.


## Lap 54 (cont-3): **CLAIM-G coupling PROVED** — `encExpect_normalize` + `_init` axiom-clean

The X9 state-normalization is done: `encExpect_normalize` (invariant induction —
both folds branch identically off shared pos/barrier; counts/whites advance in
lockstep; banking fires simultaneously since `σ.count < R'+c ⟺ τ.count < R'`;
`encVal` factors pathwise as `e^{εc}·max(e^{−k},e^{−w})·encVal_τ`) and its
consumer instance `encExpect_normalize_init`
(`E_R(T,σ) ≤ e^{ε·σ.count}·max(e^{−banked},e^{−cumWhite})·E_{R−count}(T, fresh σ.pos)`).

**X9 assembly inventory now**: PROVED = encExpect_succ, encExpect_anti,
encExpect_block_le, encExpect_of_count_ge (ρ=0 base), encounter_vertex_bound +
encChainX cap, encExpect_normalize(_init). OPEN = `fpDist_white_exit_deep`
(external, X8-geometry) + the final Y/Z gluing induction inside
`many_triangles_white` (induction on remaining budget ρ = R − count via
`encExpect_of_count_ge` base; per-block: `encExpect_block_le` with
`g e := ` the normalized continuation, vertex-split the fpDist endpoint mass by
(whiteStrip × re-encounter) into the `encounter_vertex_bound` LP; whiteness mass
≥ p₀ from `fpDist_white_exit_deep`). The gluing needs the event-mass bookkeeping:
express `Σ' fpDist·g` split into the four masses — next sub-step.

Gotcha: `refine ... (by dsimp only; omega)` dies with "No goals" when `dsimp`
closes a goal that unification already made rfl; `(by dsimp only <;> omega)` is
vacuous-safe.


## Lap 54 (cont-2): X9 assembly opened — chain arithmetic PROVED, white-exit input named

`ManyTriangles.lean` gains the lap-52 route's real-arithmetic core, all PROVED
axiom-clean: `encChainX` (the sharp instant-re-encounter chain value
`X = p₀/(1−(1−p₀)e^ε)`), `encChainX_den_pos`, `one_le_encChainX`,
`encChainX_le_exp` (the cap making exp(2ε) consumable), and
**`encounter_vertex_bound`** — the four-mass vertex analysis: the per-block
linear program is maximised at `(a,d) = (0, 1−p₀)` where the value is EXACTLY
`X` (the fixed-point identity `p₀ + (1−p₀)e^εX = X`). Plus ONE new named sorry:
**`fpDist_white_exit_deep`** ((7.59)-shaped, sibling of the Case-2 kernel with
the `s ≤ m/log²m` hypothesis removed and mass sharpened to `p₀ > 1/2`; route in
docstring — same geometry, budget O(m) via (7.52)). src sorry count 24→25 by
decomposition (progress, not regression).

**Remaining X9 gap** (`many_triangles_white` sorry): the Y/Z two-level induction
gluing `encExpect_block_le` (proved) + `encounter_vertex_bound` (proved) +
`fpDist_white_exit_deep` (open) + the CLAIM-G state-normalization coupling
(encExpect_anti-style fold induction, statement in lap-52 entry). That coupling
is the next X9 sub-step to formalize.


## Lap 54 (cont): **X2 CLOSED** — `white_cos_bound` (Lemma 7.2 sharp half) PROVED; Sec7/White.lean sorry-free

Chain (all mathlib-elementary): white ⟹ `ε < |θ| ≤ 1/2` (sfrac = `abs_sub_round`)
⟹ `cos(πθ) ≥ 0` ⟹ `|cos πθ| ≤ 1 − 2θ²` (`Real.cos_le_one_sub_mul_cos_sq`,
Jordan-type; `2/π²·(πθ)² = 2θ²` exactly) `≤ 1 − 2ε² ≤ 1 + (−ε³) ≤ exp(−ε³)`
(`Real.add_one_le_exp`), numerics at ε = 1/10⁴ by nlinarith.
**Prop 1.17's sorry surface is now EXACTLY the Prop 7.8 chain** (BlackEdge ×4,
ManyTriangles ×2). Next: X9 R-induction assembly (lap-52 route), X10 Σ-count
(lap-51 route), pin C8 (last RED statement).


## Lap 54 (2026-07-12): **X5 CLOSED (RED→GREEN in one lap)** — Lemma 7.6 (p.42, Hold basics) fully machine-checked

New `Sec7/HoldBasics.lean`, SORRY-FREE, axiom-clean. Clause map: exponential
tail + the "in particular" Lemma 2.2 conclusion were already S3's
`hold_tail_bound`/`hold_local_bound` (direct Chernoff route (7.29)-(7.30));
this lap added **mean (4,16)** (`hold_mean_fst`/`hold_mean_snd`, via generic
`tsum_iid_sum_mul` + `geomHalf_mean`=2, `pascal_mean`=4, `pascalNe3_mean`=13/3
(paper (7.29)), `geomQuarter_mean`=4, `geomQuarter_mean_sub_one`=3) and
**aperiodicity** (`hold_aperiodic`: supp Hold ⊆ x+H forces H=⊤; witnesses
(1,3),(2,5),(2,7),(2,8) → differences (1,2),(1,4),(1,5) generate ℤ²; converse
support lemma `iid_mem_support` added to go with `iid_support_coord`).

**Node status**: the ONLY remaining RED statement-less node is **C8** (§5 first
passage). Next per handoff-h: X2 `white_cos_bound` (cheapest Prop-1.17 shrink),
pin C8, then X9/X10 assemblies (routes in lap-51/52 entries).

Gotchas (corpus-worthy): writing `f (Fin.cons a w i)` in your own statement
fails elaboration (motive metavar) — ascribe `(Fin.cons a w : Fin (n+1) → α) i`;
`ENNReal.tsum_eq_add_tsum_ite` bakes in `Classical.propDecidable`, mismatching
your `instDecidableEqNat` ite — bridge via `by_cases <;> simp`; never backward-rw
an equation whose RHS numeral occurs inside inverses (`rw [← h] with h : a+b=4`
hits the `4` in `4⁻¹`) — use `.trans h.symm` + `ENNReal.add_right_inj`.


## Lap 53 (2026-07-12): **X1 CLOSED (RED→GREEN in one lap)** — (7.4)/(7.5) pairing PROVED; Prop 1.17 a theorem over {X2, Prop 7.8 chain}

**Final state**: `Sec7/Reduction.lean` is SORRY-FREE. `cexpect_pairing` (the (7.5)
crux) proved axiom-clean via: cexpect calculus (`cexpect_bind`/`cexpect_map`/
`cexpect_iid_succ`/`cexpect_norm_le`/`cexpect_const_mul`), `tsum_geom_pair`
(head-pair reindex through the injective zero-extension `(a₀,a₁)↦(a₀+a₁,a₁)` +
`Summable.tsum_prod'`), and `cexpect_pairing_gen` (strong induction, two-coordinate
peel; the ZMod (1.26)-sum split closed by `linear_combination` over the 2-unit
cancellation `inv2_cancel`). Prop 7.1 + Prop 1.17 now rest ONLY on
`white_cos_bound` (X2, elementary: white ⟹ |θ|>ε ⟹ |cos πθ| ≤ e^{-ε³}) and the
Prop 7.8 chain. **X2 is now the cheapest way to shrink Prop 1.17's sorry
surface** — a good small-lap target alongside the X9/X10 assemblies.

Gotchas this lap (for the corpus): `Function.Injective.tsum_eq` wants
`support ⊆ range` but `Function.Injective.summable_iff` wants the ∀-form;
`rw` of numeral-shape `1 = 0+1` under `Fin.cons` breaks motives (state `pre`
equations at syntactic `0+1`/`0+1+1` instead); `set`-bound local defs make
`rw [hsplit]` close goals by set-defeq (a following `simp only [hdef]` then
errors "no goals").

### (superseded lap-53 entry below)
## Lap 53 (2026-07-12): X1 = §7.1 reduction chain RED→YELLOW — Prop 1.17 now a theorem over the §7 sorries

New `Sec7/Reduction.lean` (statements ratifiable vs paper pp.33–35, (7.1)–(7.6)):
- PROVED axiom-clean: `eC_norm/eC_add/eC_intCast/eC_char_add` (additive character
  algebra on `ZMod 3^n`), `fCond_norm_le_one` (7.6), `norm_one_add_eC_neg`
  (half-angle), **`fCond_three_norm` = Lemma 7.2 exactly** (`|f(x,3)| = |cos πθ|`,
  via `χ(7x)=χ(5x)χ(2x)` and `2·xArg = 3^{2j}u2^{1-l}` unit algebra),
  `cexpect_map` (PMF pushforward seam, Fubini via `Summable.tsum_comm'`),
  `expect_mono_le`, `prod_fCond_le_damping` (product ≤ exp(−ε³·#white), consumes
  X2 `white_cos_bound`).
- PIN (the one new sorry): **`cexpect_pairing`** = paper (7.4)/(7.5): `‖S_χ(n)‖ ≤
  E_{b~Pascal^{n/2}} ∏_j ‖fCond(xArg(j, pre b (j+1)), b_j)‖`.
- `key_fourier_decay` (Prop 7.1) MOVED Holding→Reduction and PROVED from
  `cexpect_pairing` + damping + `renewal_white_encounters` (Prop 7.3, proved).
- `charFn_decay` (**Prop 1.17**, Decay.lean) PROVED from Prop 7.1 + `cexpect_map`
  (syracZ is definitionally the (1.26) reversed pushforward).

**Next attack on `cexpect_pairing`** (route in its docstring): induction peeling
TWO `geomHalf` coordinates per step, generalizing over (pair index offset j₀,
accumulated prefix L, phase multiplier 3^{2j₀}2^{-L}): the (1.26) sum splits via
`eC_char_add` into head-pair factor × tail; reindex the head double sum by
`b = a₁+a₂` (uniform over b−1 pairs = `pascal b`; `pascal_eq_map_iid` is the
model); the tail depends on the head only through `b`. Odd-n leftover: peel the
final lone coordinate with `‖g‖ ≤ 1` (triangle ineq). Infrastructure that exists:
`expect_iid_succ`/`tsum_iid_succ_mul` (Prob/Basic), `bridge_vector_gen`
(Bridge.lean) is the direct template — same fold shape, but over pairs and with a
complex product instead of a real exponential. Estimated 1–2 laps.

**Node status after lap 53**: un-pinned RED remaining = X5 (Lemma 7.6 joint tail,
paper p.42: renewal steps have mean (4,16), joint exponential tail, aperiodicity —
needed by X11 assembly) and C8 (§5 first passage). X10 next steps unchanged
(lap-51 entry); X9 R-induction assembly unchanged (lap-52 entry).


## Lap 52 (cont): **ROUTE FINDING — paper's Lemma 7.9 proof has a gap; pin corrected to `exp(2ε)`**

While assembling the R-induction the closure ledger was worked in full detail.
**Finding (flag to host judge):**
1. The paper's p.51 display "conditional expectation given `v₁…v_{k₁}` EQUALS
   `exp(−Σ_{p≤k₁}1_W + ε)·Z(endpoint, R−1)`" is FALSE on the `min(r,R)=1` branch:
   there the true sum stops at `t₁ < k₁`, so the display overcounts damping and
   under-estimates the value — invalid as a step in an upper-bound proof.
2. Correcting the ledger (each encounter's `e^ε` paid by the previous block's
   exit-whiteness) meets an adversarial configuration not excluded by `p₀`-type
   inputs: black-strip exits ARE instant re-encounters (`t_{i+1} = k_i`), while
   white exits stop the chain and their damping is then never counted. Sharp toy
   value: chains of instant re-encounters give
   `E = e^ε·p₀/(1−(1−p₀)e^ε) ≈ exp(ε/p₀) > exp(ε)`.
   So (7.57) with `exp(ε)` is likely UNPROVABLE (perhaps false as stated).
3. **Fix**: pin `≤ exp(2ε)` (valid since `p₀ > 1/2`: `X := p₀/(1−(1−p₀)e^ε) ≤ e^ε`
   for small ε). Consumer-safe: p.55 uses only Markov + a choice of `R` AFTER ε,
   so absolute exponent constants wash out. `many_triangles_white` updated.

**Corrected proof route (next laps), all inputs now identified:**
- Two-level claim over fresh states, induction on remaining blocks ρ, inner strong
  induction on T:
  - `Y(entry-state, ρ) ≤ e^ε·X` for just-entered states (count incremented, barrier
    = covering-triangle top): via `encExpect_block_le` (PROVED) reduce to the fpDist
    exit law; four-mass vertex analysis over (white/nonwhite)×(re-enc/not):
    `E ≤ P(NE) + e^εX(e^{−1}P(E∧w) + P(E∧nw))`, optimum at the
    `d = P(E∧nw) ≤ 1−p₀` vertex forces exactly `X ≥ p₀/(1−(1−p₀)e^ε)`.
  - `Z(generic, ρ) ≤ P₀ + (1−P₀)·supY ≤ e^{2ε}`.
- State normalization σ ↦ fresh: the CLAIM-G coupling
  `E_R(T,σ) ≤ e^{ε(σ.c−τ.c)}·max(e^{−(σ.bk−τ.bk)}, e^{−(σ.cw−τ.cw)})·E_{R'}(T,τ)`
  (same pos/barrier, R−σ.c = R'−τ.c) — provable by the encExpect_anti-style fold
  induction (branches depend only on shared fields; enc equalizes Δbk = Δcw).
- White-exit input: needs a (7.59)-shaped variant of `fpDist_white_exit` WITHOUT
  the Case-2 `s ≤ m/log²m` hypothesis (any family triangle, budget `s = O(m)` via
  (7.52)); the pinned X8 kernel has the restrictive hypothesis — plan: generalize
  the kernel statement when proving it (the route (7.50)+(7.11)+separation does not
  use `s ≤ m/log²m` for whiteness, only for the weight bound), or add
  `fpDist_white_exit_deep` as a sibling sorry.
- Also needed: `encNE`-style no-encounter mass functional if the sharp
  `P₀ + (1−P₀)supY` split is formalized (a simpler indicator fold), or concede the
  cruder `Z ≤ supY ⊔ 1` bound (check it still yields `e^{2ε}` — it does:
  `max(1, e^εX) = e^εX ≤ e^{2ε}`), avoiding the extra functional entirely.

## Lap 52 (2026-07-12): **X9 = Lemma 7.9 PINNED (RED→YELLOW)** — encounter-fold encoding, T1 does NOT fire

`DIRECTION.md` mandate 2 executed. All in `Sec7/ManyTriangles.lean`, green,
new proved decls axiom-clean (`#print axioms` checked).

### The D6 encoding decision (recorded per directive; ratified against pp.50–51, 55)
- **No infinite-product measure needed (route-trigger T1 does NOT fire).**
  The ONLY consumption of Lemma 7.9 is p.55 — Markov on the finite window after
  the first passage (`(j',l') := (j,l)+v_{[1,k]}`, horizon `P`), with all stopping
  times inside the window by the deterministic (7.67) argument. So (7.57) is
  pinned for the FINITE `T`-step walk `hold.iid T`, uniformly in `T` (existing
  `PMF.iid` head-peel machinery, `Prob/Basic.lean`). Finite path space is D1-safe.
- **Stopping times = a left fold**: `EncState` (pos, barrier, count, cumWhite,
  banked) with `encStep`: encounter ⟺ phase point `(q₁−1, q₂)` black-strip AND
  `barrier < q₂`; new barrier := top of `Δ(q)` via `coveringTriangle`; `banked`
  freezes `cumWhite` at encounter `min(r,R)`. So `banked = Σ_{p=1}^{t_min(r,R)} 1_W`
  EXACTLY and (7.57)'s integrand is `encVal ε R (final) = exp(−banked + ε·min(count,R))`.
- **ε existentially small** (`∃ ε₀ ∈ (0,1/100]`), not the fixed section constant:
  closure needs `e^{2ε}(1−(1−1/e)p₀) ≤ e^ε` against the EXISTENTIAL `p₀` of
  `fpDist_white_exit`; consumer insensitive (p.55 picks `R` after ε:
  `R := ⌈(10A/ε_Q³+O(A)+1)/ε⌉` re-closes (7.66)).
- **Index shift**: encounters/white read at phase point `(q₁−1, q₂)`, matching
  `fpDist_white_exit` + `Q_black_edge` glue + `whiteStrip`.

### Proved this lap (axiom-clean)
`encVal_le` (envelope `≤ e^{εR}`), `encExpect_zero` (base), **`encExpect_succ`**
(head-peel recursion `encExpect (T+1) σ = Σ'_d hold(d) · encExpect T (encStep σ d)`
— the p.51 first-block conditioning finitized; proof normalizes by `e^{−εR}` into
`expect_iid_succ`'s `[0,1]` window, then cancels), `encExpect_le`.
PIN: `many_triangles_white` (7.57) — the X9 sorry.

### NEXT for X9 (the proof; in order)
1. **Path→`fpDist` bridge** (decisive): from an encounter state (pos `q` in a
   triangle with top `b`, budget `s = (b − q.2).toNat`), iterating `encExpect_succ`
   until the barrier clears reconstructs `fpDist s` (passage time ≤ `s/3+1`,
   `hold_support_snd_ge`). Bridge at the level of `encExpect` (carry the integrand),
   NOT bare laws; mid-block white damping ≤ 1 may be DROPPED (we prove `≤`). Strong
   induction on `s` mirroring `fpDist`'s budget recursion.
2. **Induction on `R`** (p.51 shape): `Z(R,σ) ≤ P(no encounter) + e^{2ε}·
   E[1_enc e^{−1_W(fp endpoint)}]·sup Z(R−1)`, closed by `fpDist_white_exit`
   (`≤ 1−(1−1/e)p₀ ≤ e^{−ε}`). Truncation branch `t₁ ≤ T < k₁`: `min(r_T,R)=1`,
   value ≤ e^ε directly. `fpDist_white_exit` (X8 kernel) is the only open input —
   needed ONLY at the final closure; do bridge + skeleton first.
3. X11 consumption: Markov over the window + deterministic (7.67) pigeonhole
   (needs 7.10's size bound + (7.11) exit-time bound).

### X10 unchanged (Σ-count assembly = its next step; see lap-51 entry)

## Lap 51 (2026-07-12, REVIEW lap): course-correct to §7-tail de-risk; pin Lemma 7.10, design Lemma 7.9

**Direction set** (see `DIRECTION.md` CURRENT DIRECTIVE): S3 + X6 closed; X8 Case-2
is YELLOW (pinned+routed, kernels unblocked). The last RED §7 nodes are X9/X10
(Lemmas 7.9/7.10 — no Lean statement). Per BLUEPRINT §2 de-risk-breadth-first, pin
X9/X10 (red→yellow) BEFORE grinding X8 to completion. X8 kernels demoted to
finish-when-downhill. Read paper pp.50–54 this lap; both lemma statements captured
verbatim below.

### X10 = Lemma 7.10 (7.60) — PIN THIS (single-marginal, directly expressible)
Paper: `(j,l) ∈ black triangle Δ`, `s := l_Δ − l > m/log²m` (`m = ⌊n/2⌋ − j`),
`k` = first-passage time (Lemma 7.7), `p ∈ ℕ`, `1 ≤ s' ≤ m^{0.4}`. `E_{p,s'}` =
event `(j,l)+v_{[1,k+p]}` lies in a triangle `Δ' ∈ 𝒯` of size `s_{Δ'} ≥ s'`. Then
`P(E_{p,s'}) ≪ A²(1+p)/s' + exp(−cA²(1+p))` (constants uniform in n,ξ).
- **Key win**: `v_{[1,k+p]}` has an explicit MARGINAL law: `fpDist s` (the
  first-passage endpoint, X6 machinery) convolved with `iidSum hold p` (p more
  Hold steps). NO stopping-time path-space needed. Define
  `fpDistPlus s p := (fpDist s).bind (e ↦ (iidSum hold p).map (e + ·))`.
- `E_{p,s'}` = the set `{q | ∃ t ∈ F.T, (s':ℝ) ≤ t.2.2 ∧ q ∈ triangle t.1 t.2.1 t.2.2}`
  pulled back by `e ↦ (j+e.1, l+e.2)` — the `bigTriangleSet F s'` def.
- Statement (in new `Sec7/ManyTriangles.lean`): `∃ C c > 0, ∀ A > 0, ∀ … ,
  Σ' e, (fpDistPlus s p e).toReal · 1_{bigTriangleSet}(j+e.1,l+e.2)
  ≤ C·A²(1+p)/s' + C·exp(−c·A²(1+p))`.
- **Proof step 0 DONE (lap 51)**: `fpDistPlus_indicator_sum_le_one` (event prob ≤ 1
  via PMF total mass) + `fpDistPlus_tsum_toReal` — discharges the (7.60) "trivial
  otherwise" regime (`s' < C·A²(1+p)` ⟹ RHS > 1 ≥ LHS), and is general bookkeeping.
- **Apex geometry DONE (lap 51, axiom-clean)**: `apex_gap` — the "two intervals
  share no integer" step (`not_mem_two`: apex-column point of t'' at height l*
  cannot lie in t') ⟹ `s_{t'} < (j''−j')log9 + (l_{t'}−l*)log2`; and `apex_separation`
  — feeding it the (7.65) condition `l_{t'} − s_{t'}/log2 ≤ l_Δ + δ` + `l* =
  l_Δ + ⌊s'/2⌋`, the `s_{t'}` term CANCELS, giving `(⌊s'/2⌋−δ)log2 < (j''−j')log9`,
  i.e. the ≫s'-separation `j''−j' ≫ s'`. The geometric core of (7.63)–(7.65) is closed.
- **Route** remaining Σ-count assembly (all analytic, inputs are theorems):
  (i) derive the (7.65) height condition `l_{t'} − s_{t'}/log2 = l_Δ + O(A²(1+p))`
  for triangles the endpoint could hit outside E′ (from `fpDist_location_bound` X6 +
  (7.11)); (ii) turn `apex_separation` into "size-≥s' apexes obeying (7.65) form a
  ≫s'-separated ℤ-set Σ"; (iii) sum the X6 Gaussian envelope
  `s^{-1/2}G_{1+s}(c(j'−j−s/4))` over Σ ⟹ `≪ A²(1+p)/s'` via `sum_range_exp_neg_sq_le`;
  (iv) the E′ escape event (7.61) killed by X6 + Lemma 2.2 ⟹ `exp(−cA²(1+p))`.

### X9 = Lemma 7.9 (7.57) — DESIGN recorded, pin next lap (needs recursion object)
Paper: iid Hold `v₁,v₂,…`; stopping times `t₁,…,t_r` (`t₁` = first entry into a
triangle; `t_i` = first time after clearing `Δ_{i−1}`'s top that re-enters a
triangle); `r` = #triangles encountered. Then `E exp(−Σ_{p=1}^{t_{min(r,R)}}
1_W((j',l')+v_{[1,p]}) + ε·min(r,R)) ≤ exp(ε)` for any `(j',l')`, `R ≥ 1`.
- **Encoding problem**: LHS is a functional of the WHOLE infinite walk (stopping
  times couple all `v_i`). D1 forbids the product measure. D6 finitizes via the
  proof's own induction on R (p.51): condition on the first block up to the first
  passage `k₁` over the FIRST triangle's top → recursion `Z(·,R) ≤ P(r=0) +
  ∫ K((j',l'),dq)·Z(q,R−1)`, `Z(·,0)=1`, where `K` = the first-triangle
  first-passage sub-law carrying `exp(−Σ_{p=1}^{k₁}1_W + ε)`.
- **Kernel `K` = the decisive new object.** Recommended encoding (B1): the
  first-triangle first-passage is a plain renewal first-passage to the MOVING
  barrier `= top of the triangle currently covering q` (monotone-height insight
  from X6 ⟹ no barrier condition). Reuse `fpDist`-style budget recursion with a
  position-dependent budget `s(q) = l_{Δ(q)} − l`, `Δ(q)` = the (unique) triangle
  covering `q` via `cover`.
- **Prerequisites DONE (lap 51, both axiom-clean)**:
  `TriangleFamily.not_mem_two` (distinct family triangles share no lattice point,
  from `F.separated` const `≈ 0.92 > 0`; also serves 7.10's (7.65) ≫s′-separation)
  and `TriangleFamily.existsUnique_cover` (every black-strip point lies in exactly
  one family triangle — `cover` existence + `not_mem_two` uniqueness ⟹ `∃!`). The
  covering triangle `Δ(q)` is now well-defined.
  NEXT for X9: (a) turn `existsUnique_cover` into a function `Δ : (strip pt) → T`
  (via `Classical.choose` / `ExistsUnique.choose`) + its spec lemmas; (b) the moving-
  barrier budget `s(q) := (Δ(q).2.1 − q.2).toNat`; (c) the `Z` budget recursion on R
  (mirror `Qstop`/`fpDist` recursion shape, `Unroll.lean`); (d) pin (7.57), close by
  induction on R using `fpDist_white_exit` (7.51).
- Induction close (once pinned): `Σ_{p=1}^{k₁}1_W ≥ 1_W(endpoint)` +
  `fpDist_white_exit` (7.51, X8 open kernel) ⟹ `Z(·,R) ≤ exp(ε)`. So 7.9 CONSUMES
  the open `fpDist_white_exit`; 7.10 does not — pin 7.10 first.
- **Route-trigger T1** (`DIRECTION.md`): if K provably needs an infinite-product
  measure (D1 unbreakable), escalate — do not import measure theory.

### NEXT after this lap
Pin 7.10 (this lap) → probe its (7.63)–(7.65) Σ-counting sub-step → pin the
triangle-disjointness lemma + `Δ(q)` + `Z` recursion + Lemma 7.9 (next lap) →
then X8 finish-when-downhill / X11 Case-3 assembly consuming 7.9+7.10.

## Lap 50 (2026-07-12, seventh box session): **LEMMA 7.7 PROVED — NODE X6 CLOSED**

`fpDist_location_bound` is a theorem, axiom-clean. FpLocation.lean is now
SORRY-FREE: the full chain first-passage decomposition → renewal Gaussian
bound → last-step convolution is machine-checked. New machinery (all
numerically validated before formalizing; 200k-trial clean):
- `hold_step_bound` — one hold step ≤ C₇·e^{-γ|d₁-4|}e^{-γ|d₂-16|}
  (hold_local_bound at n=1 + `Gweight_two_le`: Gw 2 x ≤ 4e^{-x/2}, elementary
  via e^{-x/2} ≥ 1/2 on x ≤ 1 — no ExponentialBounds import needed);
  `iidSum_one_apply`.
- `sum_abs_int_le` — step-1 AP sum with ℤ (possibly negative) centre,
  q := w.toNat, abs_cases+omega per branch.
- `conv_Gweight_exp` — discrete Gaussian×exponential convolution: pointwise
  near/far split at |w-μ|/2, output decay min(c/2, γ/4), constant 4+8/γ.
- `Gweight_shift` — recentring by δ costs 2e^{c|δ|} and half the constant
  (case split |X| ≤ 2|δ| via Gweight_le_two vs |X+δ| ≥ |X|/2).
- `sum_sqrt_exp_le` — Σ_{m≤s} e^{-γ(s-m)}/√(1+m) ≤ (2(1+1/γ)+64/γ²)/√(1+s)
  (Finset.sum_range_reflect for the geometric reindex — no nbij needed).
- Assembly: fpDist ≤ renewal⋆hold truncated to the finite box
  range(j+1) ×ˢ Icc 0 s (`renewalMass_zero_of_snd_neg`/`renewalMass_ne_top`
  kill the complement, tsum_eq_single collapses the step), ENNReal→ℝ via
  toReal_mono + toReal_sum, then per-m: j₁-convolution → shift to centre
  j-s/4 at scale 1+s (δ = (s-m)/4-4, e^{c₉(s-m)/4} absorbed since c₉ ≤ γ/4)
  → m-sum. Final c = min(min(c₆/2,γ/4)/2, γ), C = C₆C₇e^{16γ}(4+8/γ)·2e^{4c₉}K.
  l ≤ s case free via fpDist_support_snd_gt.

Gotchas this lap:
- In a huge proof context (giant tsum equalities in scope) plain
  linarith/nlinarith hit isDefEq TIMEOUTS — use `linarith only [facts]`.
- `positivity` can't see `Gweight` nonnegativity — pass
  `mul_nonneg (by positivity) (Gweight_nonneg _ _)` explicitly.
- `hstep (a, b)` leaves unreduced `((a,b)).1` projections in the
  instantiated statement — `dsimp only at h` before rw.
- `tsum_eq_single` side-goal order: the `if_pos` equality goal comes FIRST,
  the ∀ b' ≠ b vanishing goal second.
- `Prod.ext` via `exact` leaves component mvars (`?m.1 = ?m.1`) — use
  `apply Prod.ext` then `show`-pinned component goals.
- `abs_add` → `abs_add_le` (mathlib rename); tuple type ascription must be
  `((a : ℕ), b)` not `(a : ℕ, b)`.
- `Real.one_le_sqrt` needs `1 ≤ x` — `positivity` can't produce it; use
  `le_add_of_nonneg_right (Nat.cast_nonneg m)`.

NEXT (X8 Case-2 kernels, per lap-46 pin): `fpDist_edgeWeight_le`
((7.48)/(7.49)) — consume fpDist_location_bound j-concentration + Geom(4)
tail via edgeWeight; then `fpDist_white_exit` ((7.50)/(7.51)) — endpoint
localization + family separation; then `Q_black_edge_case2` assembly; X9
Lemma 7.9 skeleton for Case 3.

## Lap 49 (2026-07-12, seventh box session): **renewalMass_bound PROVED** (X6 step 2 COMPLETE)

The renewal Gaussian bound (paper p.44 first display) is a theorem,
axiom-clean: `renewalMass (j,l) ≤ C/√(1+l) · Gweight(1+l)(c(j-l/4))` with
`c = c₀/4`, `C = C₀·C₅` off `hold_local_bound`'s `(c₀, C₀)`. All four pinned
route steps landed in FpLocation.lean exactly as validated numerically:
- `sum_abs_AP_le` — two-branch reindex at `q = w/16` (Finset.sum_image with
  the have-key trick from the corpus; k ↦ q-k / k-q-1).
- `iidSum_hold_snd_zero` + `renewalMass_toReal_eq` — support truncation at
  `k ≤ ⌊l/3⌋` (induction on iidSum_succ_apply + hold_zero_of_snd_lt), tsum →
  Finset sum → toReal-distributed.
- `Gweight_factor` — the AB+CD ≤ (A+C)(B+D) peel: `Gw(1+k)(c₁y) ≤
  Gw(1+l)(c₁/2·x)·(e^{-(c₁²/2)z²/(1+k)} + e^{-(c₁/2)z})` from
  `|x| + (3/4)z ≤ y` (via y² ≥ x² + z²/2), `1+k ≤ 1+l`.
- `renewal_weight_sum_le` — the k-sum envelope `Σ (1+k)⁻¹W_k ≤ C₅/√(1+l)`,
  `C₅ = 32/ε² + 256 + 4/b + 8/√a`, `ε = min(a/8,b/2)`: edge region `k < ⌊l/32⌋`
  killed by `exp_neg_le_four_div_sq` (one application suffices:
  `2(1+l)²e^{-εl} ≤ 32/ε²`), central region by `1/(1+k) ≤ 32/(1+l)` +
  `sum_abs_AP_le` + `sum_range_exp_neg_sq_le` (with `√β·√(1+l) = 16√a`) +
  geometric.

Gotchas this lap:
- `div_le_div_iff` → `div_le_div_iff₀` (mathlib rename); `div_add_div_same`
  gone — use `(add_div _ _ _).symm`.
- `rw [neg_mul, neg_div, neg_mul, neg_div]`: when both sides share the SAME
  numerator, the first `neg_mul` rewrites both sides at once and the second
  fails; chain is `[neg_mul, neg_div, neg_div]`.
- linarith atom traps: `2*(2/√β)` vs `4/√β` and `2*(1/(16b))` vs `1/(8b)` are
  UNRELATED atoms — supply `by ring` bridge equations as hypotheses.
- A single `rw [div_le_div_iff₀ h1 h2] at hA ⊢` cannot hit two locations with
  different denominators (rule elaborated once); rewrite separately or bridge
  with ring equations.
- `Nat.cast_le.mpr (α := ℝ)` fails (named arg goes to Iff.mpr); ascribe the
  `have` type instead.
- omega handles `l.toNat`, `t/3`, `t/32` mixed ℕ/ℤ goals natively — all the
  truncation index arithmetic here was pure `omega`.

NEXT (X6 step 3, the last FpLocation sorry): `fpDist_location_bound` =
`fpDist_le_renewal_conv` + `renewalMass_bound` at the pre-passage point
`(j₁,l₁)`, `l₁ ≤ s` + one `hold` step for the overshoot `(j-j₁, l-l₁)` with
`hold_local_bound`/`hold_tail_bound` at n = 1, split `l₁ ≤ s/2` vs `> s/2`
(paper p.44 closing paragraph). Sub-steps: (a) toReal the ≤-inequality of
fpDist_le_renewal_conv (tsum on the right is finite: renewalMass ≤ 1+stepMass
bounded? — no: bound it by the CONVOLUTION's value directly: each term
renewalMass(p)·hold(e-p) ≤ hold(e-p) is false; instead truncate p-support:
p₂ ≤ s and hold(e-p) ≠ 0 forces e₂-p₂ ≥ 3 and p = e - d with d in hold's
support, so the p-sum is a finite sum over d.1 ≤ j, use toReal_mono +
tsum ≤ over finite index); (b) exp(-c(l-s)) factor comes from hold_tail_bound
n=1 on the overshoot when l - l₁ is large, else from the trivial bound 1
absorbed by adjusting c (for l ≤ s the LHS is 0 via fpDist_support_snd_gt —
handle first). Then X8 Case-2 kernels consume this.

## Lap 48 (2026-07-12, seventh box session): renewalMass_bound TOOLKIT LANDED (X6 step 2 in progress)

Numeric validation done FIRST (python): factorization chain
Gw(1+k, c1*y_k) <= Gw(1+l, c4*x) * W_k for y_k=|j-4k|+|l-16k|, x=j-l/4,
W_k = e^{-a z^2/(1+k)} + e^{-b z}, z=|l-16k|; c1=c0/2, c4=c1/2, a=c1^2/2,
b=c1/2 (c0=1/400 from hold_local_bound) — 200k random trials clean; k-sum
envelope numeric max C5 ~ 500/sqrt(1+l) (Lean-shaped derivation ~6e14, fine).

PROVED this lap (FpLocation.lean, axiom-clean via build):
- `Gweight_anti` (antitone in |x|), `exp_neg_le_four_div_sq` (e^{-u} <= 4/u^2
  from e^{u/2} >= 1+u/2 squared), `one_sub_exp_neg_inv_le_one_add`
  ((1-e^{-u})^{-1} <= 1+1/u), `sum_range_geom_le`,
- **`sum_range_exp_neg_sq_le`**: Sum_{m<N} e^{-beta m^2} <= 3 + 2/sqrt(beta) —
  integral-free M-split (M ~ 1/sqrt(beta) unit terms + m^2 >= Mm geometric
  tail). This is the Gaussian AP sum engine for the renewal k-sum.

REMAINING for renewalMass_bound (route fixed, see lap-47 entry + python):
1. `sum_abs_AP_le`: Sum_{k<N} f(|w-16k|) <= 2 Sum_{m<N} f(16m), f antitone
   nonneg, hypothesis w < 16N. Two branches at q := w/16 (Int ediv):
   16k<=w: z >= 16(q-k), reindex i=q-k via Finset.sum_image (i <= q < N);
   16k>w: z >= 16(k-q-1), i=k-q-1. filter split + sum_le_sum + sum_image +
   sum_le_sum_of_subset_of_nonneg.
2. `iidSum_hold_snd_zero`: (3k:Z) > q.2 -> iidSum hold k q = 0 (induction on
   k via iidSum_succ_apply + hold_zero_of_snd_lt) => k-sum truncates at
   K := l.toNat/3, renewalMass = Finset sum (tsum_eq_sum), 1+k <= 1+l.
3. Per-k: hold_local_bound + ||v||inf >= y/2 + Gweight_anti + the AB+CD <=
   (A+C)(B+D) factorization => P_k <= C0/(1+k) * Gw(1+l,c4 x) * W_k.
4. k-sum: split k < L/32 (z > l/2: W_k <= e^{-(a/8)l}+e^{-(b/2)l}, times
   (l+1) terms, kill by exp_neg_le_four_div_sq: (1+l)^{3/2}e^{-eps l} <=
   6/eps^2 constant) vs k >= L/32 (1/(1+k) <= 32/(1+l), quadratic via
   sum_abs_AP_le + sum_range_exp_neg_sq_le at beta = 256a/(1+l), linear via
   sum_abs_AP_le + sum_range_geom_le). C5 symbolic in a,b; C := C0*C5.

## Lap 47 (2026-07-12, seventh box session): X6 CRACKED OPEN — FIRST-PASSAGE RENEWAL DECOMPOSITION PROVED

NEW `Sec7/FpLocation.lean` (imports HoldLocal; `fpDist_location_bound` moved
here from Unroll). KEY STRUCTURAL INSIGHT formalized: hold steps strictly
increase height (`hold_support_snd_ge`), so a path reaching `p` with
`p.2 <= s` automatically kept ALL partial sums <= s — the first-passage
decomposition needs NO barrier condition, just the PLAIN renewal measure.

PROVED (axiom-clean):
- `renewalMass p := Sum_k iidSum hold k p`, `stepMass`, `renewalMass_eq`
  (delta_0 + stepMass peel via tsum_eq_zero_add' ENNReal.summable),
  `iidSum_succ_apply`, `stepMass_eq_conv` (renewal recursion U = d0 + hold*U).
- `tsum_delta_chain`, `tsum_conv_reindex` — reusable ENNReal delta-convolution
  Fubini helpers (collapse intermediate landing points / reindex p = d + q).
- **`fpDist_le_renewal_conv`**: fpDist s e <= Sum_{p.2<=s} renewalMass p *
  hold(e-p) (delta form). Budget strong induction; INEQUALITY suffices for all
  consumers (upper bounds; (7.50) lower bound = complement since fpDist is a
  PMF). This is X6 step 1 of 3.

OPEN (X6 steps 2-3, both statements pinned with route docstrings):
- `renewalMass_bound`: U(j,l) <= C/sqrt(1+l) * Gweight(1+l)(c(j-l/4)).
  ATTACK: insert hold_local_bound per k, sum in k over three regions
  16(k-1) in [l/2,2l] / < l/2 / > 2l (paper p.44 "routine calculation").
  VALIDATE the envelope numerically in python FIRST (c=1/400 upstream;
  region-2/3 terms need Gweight quadratic-vs-linear case split).
- `fpDist_location_bound` (Lemma 7.7): assembly = fpDist_le_renewal_conv +
  renewalMass_bound at (j1,l1) + hold_local/tail at n=1 for overshoot step,
  split l1 <= s/2 vs > s/2.

Gotchas this lap:
- PMF.map_apply/pure_apply produce `Classical.propDecidable` ites that do NOT
  match hand-written ites (instDecidableEqProd): "synthesized instance not
  defeq". Bridge: `map_apply_ite` proved via `tsum_congr fun a => by congr`
  (congr closes Decidable mismatches via Subsingleton). if_pos/if_neg/by_cases
  are instance-agnostic; only calc-LHS/rw pattern matching breaks.
- `rw [zero_mul]` etc rewrite ALL occurrences of the matched instantiation at
  once — chained duplicate rewrites then fail "pattern not found".
- `exact zero_le _` fails where `zero_le` resolves with implicit arg; plain
  `exact zero_le` works (ℝ≥0∞).

## Lap 46 (2026-07-12, seventh box session): X8/X10 STATEMENT DESIGN — Q_black_edge DECOMPOSED

NEW `Sec7/BlackEdge.lean` (imports Monotone + Unroll; Bridge now imports it;
`Q_black_edge`/`prop_7_8`/`Q_polynomial_decay` moved here from Monotone).
Cases 2-3 of Prop 7.8 (paper (7.44)-(7.67), pp.46-49) pinned as named decls:

PROVED (axiom-clean):
- `TriangleFamily` (bundled Lemma 7.4 data) + `exists_triangleFamily`.
- `Q_fp_endpoint_le` — the (7.46) endpoint step: one Q_rec at the
  first-passage endpoint exposes white damping in subtraction form
  `1 - (1-e^{-eps^3})*1_{whiteStrip}` times `edgeWeight * Qm(m-1)`;
  out-of-strip endpoints absorbed via `edgeWeight_of_deep` + `one_le_Qm`.
- `budget_le_of_mem_triangle` — (7.52): s*log2 <= (m+2)*log9 via lattice
  extent point `(j_D + floor(s_D/log9), l_D)` + confinement (floor slack
  vs paper's m; Case 3 only needs s = O(m)).
- `Q_black_edge` — the case split GLUE: black point -> cover -> triangle,
  s := (l_D - l).toNat, split at m/log^2 m. No longer a monolithic sorry.

OPEN (4 new named sorries replacing the old 1 — deliberate decomposition):
1. `fpDist_edgeWeight_le` ((7.42)+(7.48)/(7.49)): E[edgeWeight] <= (1+delta)m^{-A}
   for s <= m/log^2 m. Consumes fpDist_location_bound (X6) j-concentration
   + Geom(4) tail. NEXT ATTACK: prove X6 first (its inputs hold_local_bound/
   hold_tail_bound are theorems since lap 42) — union bound over last step,
   mirror the paper Lemma 7.7 proof p.43-44 (sum in k of k^{-1}G_k(c(j'-(k-1)4,
   s'-(k-1)16)) with the three-region split).
2. `fpDist_white_exit` ((7.50)/(7.51)): white-in-strip exit mass >= p0 absolute.
   Hardest Case-2 kernel: endpoint at (j+s/4+O(sqrt(1+s)), l_D+O(1)) via X6,
   above-top by fpDist_support_snd_gt, outside other triangles via family
   separation vs the fixed eps=1e-4 ring constants (MC-validated 0.99).
3. `Q_black_edge_case2` assembly: mechanical (7.47) split once 1+2 land
   (delta := (1-e^{-eps^3})p0/2; w >= m^{-A} pointwise for the subtraction).
4. `Q_black_edge_case3` ((7.53)-(7.67)): the X9/X10/X11 subtree — Lemma 7.9
   induction on r over the Q-recursion, Lemma 7.10 separated-Sigma counting,
   P-step iterate of (7.35), 0.9m Chernoff split. NEXT: pin Lemma 7.9's
   statement (stopping times t_i over fpDist iterates, r = #triangles met).

Gotchas: anonymous-constructor membership under Set.indicator_of_mem needs a
named `have hmem : _ ∈ whiteStrip ...` (expected-type inference fails inline);
`linarith` missed `0 <= (1/10)*log(10^4)` from `0 <= log(10^4)` (atom mismatch)
— use `mul_nonneg` directly.

**Red-queue state after this lap** (BLUEPRINT §2 steering): S3 GREEN (lap 45),
X8/X10 statements PINNED (this lap). Next reds: X6 (fpDist_location_bound —
now the single blocker for BOTH Case-2 kernels), X9 (Lemma 7.9 skeleton),
X1 (key_fourier_decay chain), X5 (Bridge x3), C8.

## Lap 45 (2026-07-12, seventh box session): ALL THREE d=1 LOCAL BOUNDS PROVED — **NODE S3 FULLY GREEN**

**`geomHalf_local_bound`, `geomQuarter_local_bound`, `pascal_local_bound` are
theorems** (axiom-clean). With laps 41-44, ALL EIGHT Lemma 2.2 obligations
(hold local+tail, 3× d=1 local, 3× d=1 tail) are machine-checked. Machinery
(LocalInstances.lean):
- `iidSum_nat_local_of_quad` — GENERIC d=1 Lemma 2.2(i): any PMF ℕ with mean
  m ≤ 4, quad MGF bound (K = 1000, box 1/200), and two adjacent atoms
  a, a+1 ≤ 3 of mass ≥ 3/16 gets the local bound (c = 1/400, C = 128).
  Chain: tilted atoms keep mass ≥ 1/6 (weights ≥ e^{-3/200}, Z ≤ 209/200,
  validated 0.1767 ≥ 1/6), decay c = 4 via adjacent-atom lemma, tilted center
  128/√(1+n), tilting identity + signed clip + Gweight evenness (`Gweight_abs`).
- signed `chernoff_clip_le` MOVED HoldLocal → LocalInstances.
- instances: geomHalf (m=2, atoms 1,2), geomQuarter (m=4, atoms 1,2; mass at 2
  EXACTLY 3/16), pascal (m=4, atoms 2,3, both 1/4).
Gotcha: λ is a token — cannot appear in hypothesis names (hλlo fails to parse).

**S3 CLOSED. Next per operator red queue** (BLUEPRINT §2 steering: statement
pinned + route validated + hardest sub-step probed):
1. (X8/X10) `Q_black_edge` (Sec7/Monotone.lean:489) — statement design for
   Prop 7.8 Cases 2/3, eqs (7.46)-(7.53) pp.46-48, over Qstop/fpDist. READ THE
   PAPER PAGES FIRST (papers/ dir has the PDF; also SUMMARY pdf).
2. (X9) Lemma 7.9 induction skeleton over Q_rec consuming Q_white_contract.
3. (X1) key_fourier_decay reduction chain (Fourier side).
4. (X5) three bridge sorries in Sec7/Bridge.lean (hold_tsum_step most
   mechanical: split geomQuarter at k=1, peel one pascalNe3 off PMF.iid).
5. (C8) + X6 `fpDist_location_bound` (Unroll.lean:624) — now UNBLOCKED: it
   consumes hold_local_bound/hold_tail_bound which are theorems as of today.
   Check whether X6 is actually the fastest way to spend the analytic win.

## Lap 44 (2026-07-12, seventh box session): d=1 CIRCLE METHOD BUILT (CharFn1.lean)

NEW `Prob/CharFn1.lean` — the ENTIRE d=1 Fourier engine derived from the 2-D
module via the first-coordinate embedding `embMod N L = (L mod N, 0)` (zero
re-proving of Fourier machinery):
- `charFn_map_embMod_snd` — embedded charFn is ξ₂-free (mass off the axis is 0),
  so the 2-D inversion `N⁻² Σ_ξ` collapses to `N⁻¹ Σ_j`;
- `iidSum_nat_apply_toReal_le` — P(S_n = L) ≤ N⁻¹ Σ_j ‖φ(j)‖ⁿ;
- `charFn_embMod_decay_of_adjacent_atoms` — decay 1 − 16μ²(nd j/N)² from atom
  masses ≥ μ at ADJACENT a, a+1 (no triangle step; abstract r, so applies to
  tilted projected walks);
- `iidSum_nat_apply_le_center_of_decay` — the d=1 center bound 32c/√(1+n) at
  N = ⌊√n⌋+1 (mirror of the 2-D Gaussian summation, single factor).
All axiom-clean (checked via full-build warnings only; #print pending next lap
commit). Gotchas: field_simp overshoots `ring` (drop it / add norm_num);
`(embMod N L).2 = 0` needs explicit rfl after rw.

**NEXT — assemble the three d=1 local bounds** (LocalInstances.lean sorries):
per walk p ∈ {geomHalf (atoms 1,2; masses 1/2,1/4), geomQuarter (atoms 1,2;
1/4,3/16), pascal (atoms 2,3; 1/4,1/4)}:
1. Tilted atom-mass lower bounds (mirror tilt_hold_apply_ge, easier):
   tilt p (expW λ) at atom d: p_d·e^{λd}/Z ≥ p_d·e^{-3/200}/Z; Z ≤ quad(1/200)
   ≤ 1.03 ⇒ tilted mass ≥ (3/16)·0.985/1.03 ≥ 1/6 uniform ⇒ μ = 1/6,
   c = (16μ²)⁻¹ = 9/4... use c = 4 (≥ 1 and ≥ (16μ²)⁻¹). VALIDATE numerically.
   Transfer through map: PMF.apply_le_map_apply to (tilt p).map (embMod N).
2. Tilted center bound: iidSum_nat_apply_le_center_of_decay at the tilted walk
   (c uniform on box) ⇒ P_tilt(S̃_n = L) ≤ 128/√(1+n)-ish =: C₀/√(1+n).
3. d=1 Chernoff bridge (mirror holdSum_apply_le_chernoff, 1-D weights expW):
   P(S_n = L) ≤ C₀/√(1+n)·e^{n(mλ+1000λ²) − λL} via iidSum_apply_eq_tilt +
   quad bounds (already proved: tiltZ_{geomHalf,geomQuarter,pascal}_le_quad).
   Note tiltZ_expW_ne_zero gives hZ0; hZt from quad bound.
4. Assembly = hold_local_bound pattern verbatim with √(1+n) and 1-D clip
   (chernoff_clip_le SIGNED version is in HoldLocal — either import or the
   nonneg one + case split on sign of dev; dev = L − mn ∈ ℝ signed: need the
   SIGNED clip: move chernoff_clip_le from HoldLocal to LocalInstances, or
   restate; then Gweight matching via exp_neg_min_le_Gweight + |dev| symmetry:
   exponent bound uses min(dev²/4000n, |dev|/400) — matches Gweight(c·(L−mn))
   since Gweight is even in its argument (|·| and square) — CHECK: Gweight t x
   uses x² and |x| only ⇒ Gweight(c·dev) = Gweight(c·|dev|) ✓ need tiny lemma
   Gweight_abs or just work with x = c*(L−mn) directly, matching hold pattern
   where M was ‖dev‖ ≥ 0 — here pass |dev| and rewrite by evenness).
   Consider a GENERIC `iidSum_nat_local_of_quad_center` mirroring
   iidSum_nat_tail_of_quad to do all three at once (hypotheses: quad bound +
   tilted center bound). Then S3 FULLY GREEN.

## Lap 43 (2026-07-12, seventh box session): ALL THREE d=1 TAIL BOUNDS PROVED

**`geomHalf_tail_bound`, `geomQuarter_tail_bound`, `pascal_tail_bound` are
theorems** (axiom-clean), in NEW `Prob/LocalInstances.lean` (statements moved
from LocalBound.lean — proofs need the Mgf engine, which imports LocalBound;
NOTE at old site; shared `chernoff_clip_le_nonneg` + `exp_neg_min_le_Gweight`
moved here from HoldLocal, which now imports this module). Machinery:
- `tiltZ_expW_ne_zero` — Z ≠ 0 generic on PMF ℕ (weights positive, mass 1);
- 1-D quadratic MGF bounds, uniform K = 1000 (validated numerically):
  `tiltZ_geomHalf_le_quad` (K = 8 tight, envelope E = 1+λ+2λ² through
  frac_closed_le), `tiltZ_pascal_le_quad` (square of geomHalf),
  `tiltZ_geomQuarter_le_quad` (transfer of tiltZ_hold_fst_le via NEW
  `tiltZ_geomQuarter_eq` = hold_map_fst + tiltZ_map);
- `iidSum_nat_halfspace_le` — generic 1-D one-sided Markov under tilt;
- `iidSum_nat_tail_of_quad` — GENERIC d=1 Lemma 2.2(ii): any PMF ℕ with
  Z ≤ 1+mλ+1000λ² on |λ| ≤ 1/200 gets the tail bound (c = 1/400, C = 2);
  the three instances are 3-liners over it.
Gotcha: degree-4 envelope nlinarith needs box-product×λ² hints
(mul_nonneg (1/200±λ) (sq_nonneg λ)).

**S3 ledger now: only the three d=1 LOCAL bounds remain** (sorries in
LocalInstances.lean): geomHalf/geomQuarter/pascal_local_bound. They need the
d=1 center bound C/√(1+n): a single-ZMod circle-method analogue of
`iidSum_apply_le_center_of_decay` (CharFn.lean) — same proof shape, ONE charFn
decay factor, N = ⌊√n⌋+1 gives C·N⁻¹... wait C/N with N ~ √n ✓. Steps:
1. `iidSum_nat_apply_le_center_of_decay (p : PMF ℕ) (c) (hdec : ∀ N [NeZero N],
   4 ≤ N → ∀ ξ : ZMod N, ‖charFn (p.map (Nat.cast) : PMF (ZMod N)) ξ‖^2 ≤
   1 - ((nd ξ : ℝ)/N)^2/c) : ((iidSum p n) v).toReal ≤ (32·c... )/sqrt(1+n)` —
   mirror the 2-D proof in CharFn.lean (read `iidSum_apply_le_center_of_decay`
   first; the 1-D version drops one factor and the constant becomes 32c/√ not
   (32c)²/n).
2. charFn decay for the TILTED 1-D walks from atom masses: need two atoms at
   distance 1 (geomHalf: masses at 1,2 = 1/2,1/4; tilted ≥ ~1/5 on box;
   geomQuarter: atoms 1,2; pascal: atoms 2,3) — reuse `charFn_decay_of_atoms`?
   That one is 2-D (ZMod N × ZMod N); check if a 1-D atom-decay lemma exists in
   CharFn.lean or needs writing (mirror).
3. Tilted-walk assembly identical to hold_local_bound (1-D chernoff bridge +
   clip + Gweight; all shared pieces already factored).
Then S3 is fully GREEN. After that: operator red queue (2) X8/X10 statement
design Prop 7.8 Cases 2/3 (7.46)-(7.53); (3) X9 Lemma 7.9 skeleton; (4) X1;
(5) X5 bridge sorries; (6) C8.

## Lap 42 (2026-07-12, seventh box session): `hold_tail_bound` PROVED — S3 2-D SIDE COMPLETE

**Lemma 2.2(ii) for `Hold` is a theorem** (axiom-clean), same lap-41 engine, no
center bound needed. In `Sec7/HoldLocal.lean`:
- `chernoff_clip_le_nonneg` — sign-exposing clip variant (μ ≥ 0 when dev ≥ 0);
- `exp_neg_min_le_Gweight` — factored Gweight branch matching (n ≥ 1, x ≥ 0);
- `holdSum_halfspace_le` — one-sided Markov under the tilt: region mass ≤
  e^{n·quad(λ) − a} when the tilt weight ≥ e^a on the region (tiltZ_iidSum +
  tiltZ_hold_le_quad + termwise Markov);
- `hold_tail_bound` — c = 1/400, C = 4: sup-norm tail ⊆ 4 sign-pattern
  half-spaces (le_max_iff + le_abs), each with tilt ±μ in the matching
  coordinate; all four exponents collapse to 1000nμ² − μ·lam; ℝ↔ℝ≥0∞ via
  ENNReal.tsum_toReal_eq + apply_ite; n = 0 point mass separate.
Gotchas: `zero_le _` in term position fails in ℝ≥0∞ (use `bot_le`); `set`-atoms
must be re-folded (rw [hB]) after toReal_ofReal unfolds them; `(0:ℕ×ℤ).1` needs
`Prod.fst_zero` simp before norm-num on the norm.

**BOTH Lemma 2.2 instances for Hold done: `hold_local_bound` + `hold_tail_bound`.**

**NEXT — the six d=1 instances in Prob/LocalBound.lean** (geomHalf/geomQuarter/
pascal × local/tail; sorries at :153,:161,:169,:176,:185,:192), now mechanical
with the same pattern:
- tail bounds (easier, do first): 1-D `iidSum_halfspace_le` analogue of
  `holdSum_halfspace_le` generic in a PMF ℕ with a 1-D quad MGF bound; need 1-D
  quadratic bounds for geomHalf (mean 2), geomQuarter (mean 4), pascal (mean 4)
  from the closed forms `tiltZ_geomHalf`/`tiltZ_pascal` (already in Mgf.lean —
  check exact names/envelopes; validate constants numerically first).
- local bounds: need 1-D center bound C/√(1+n) — NOTE the d=1 statements have
  1/√(1+n) not 1/(1+n): the circle-method center bound
  `iidSum_apply_le_center_of_decay` is d=2-specific (product of two coords).
  Check what exists for d=1 (charFn decay in 1-D + N = ⌊√n⌋+1 gives C/√n) —
  likely a 1-D analogue of `iidSum_apply_le_center_of_decay` must be stated
  (same proof shape, single ZMod factor). Then the assembly is identical.
Then Lemma 7.6/7.7 (X6) consume hold_local/tail (`fpDist_location_bound`,
Unroll.lean:624 area) — and the X5 bridge sorries + Q_black_edge remain the
other red nodes (X8/X10, X9, X1, C8 per operator queue).

## Lap 41 (2026-07-12, seventh box session): (F5) DONE — `hold_local_bound` PROVED

**S3's Lemma 2.2(i) for `Hold` is a machine-checked theorem** (axiom-clean), in
`Sec7/HoldLocal.lean` (statement MOVED there from Unroll.lean — the proof consumes
`tiltHold_apply_le_center`, which imports Unroll; a NOTE at the old site points
across). Three pieces, exactly per the lap-40 plan:
- `holdSum_apply_le_chernoff` — the Chernoff bridge: tilting identity
  `iidSum_apply_eq_tilt` + `tiltHold_apply_le_center` + `tiltZ_hold_le_quad`
  + `1+u ≤ e^u`, all `toReal` bookkeeping (`ENNReal.toReal_mul` unconditional;
  weight-inverse via `ENNReal.ofReal_inv_of_pos` + `Real.exp_neg`).
- `chernoff_clip_le` — per-coordinate λ-clip: exponent ≤ −min(dev²/(4000n), |dev|/400)
  (central λ = dev/2000n exact; tail λ = ±1/200, n/40 ≤ |dev|/400).
- `hold_local_bound` — c = 1/400, C = C₀ = 6553600000000; n = 0 point-mass case
  separate; sup-norm max coordinate dominates (other coord's exponent ≤ 0);
  Gaussian branch (M/400)²/(1+n) ≤ M²/4000n, exp branch exact.
Gotcha: `div_le_div_iff` is now `div_le_div_iff₀` (corpus had it).

**NEXT — `hold_tail_bound` (2.2(ii), now the sorry in HoldLocal.lean)**: direct
Chernoff tail, same ingredients, NO center bound: for the half-space
{λ ≤ ‖dev‖∞}, split by which coordinate/sign achieves the sup (4 half-lines ×
2 coords); for a fixed sign pattern use the 1-D Markov/Chernoff:
Σ_{tail} P ≤ Z(λ)ⁿ e^{-λ·(threshold)} with the SAME clip choice at dev = ±lam
(deviation threshold), summing the tilted PMF's tail mass ≤ 1. Concretely:
tail mass ≤ Σ over 4 sign-patterns of e^{n·quad(λ) − λ·(mean shift ± lam)} with
λ clipped as in chernoff_clip_le at dev = lam ⇒ each term ≤ e^{−min(lam²/4000n,
lam/400)} ⇒ ≤ 4·Gweight branch; C = 4 (plus n = 0 edge). Statement's tsum-if:
bound the indicator sum by tilted change-of-measure per point (pointwise
`iidSum_apply_eq_tilt` + e^{-λ·v} ≤ e^{-λ·threshold} on the half-space, tilted
masses sum ≤ 1 via `PMF.tsum_coe`). Then the 6 d=1 LocalBound instances
(mechanical now — same pattern, 1-D closed forms already proved).

## Lap 40 (2026-07-12, sixth box session): (G2c) 2-D MGF BOUND PROVED — (G2) COMPLETE

`Prob/Mgf.lean`: `ennreal_le_of_sq_le_sq` (x² ≤ y² → x ≤ y, via ENNReal.mul_lt_mul
contrapositive) and **`tiltZ_hold_le_quad`** — on |λᵢ| ≤ 1/200:
`Z(λ₁,λ₂) ≤ ofReal(1 + 4λ₁ + 16λ₂ + 1000(λ₁²+λ₂²))`. K = 1000 validated
numerically (K ≤ 700 fails; the CS-doubled cross term 256λ₁λ₂ vs 128λ₁λ₂ costs
−128λ₁λ₂, absorbed). AXIOM-CLEAN. The full Lemma-2.2 Chernoff MGF estimate with
exact mean (4,16) is machine-checked.

**(F5) next — final assembly of `hold_local_bound`** (in Sec7/HoldLocal.lean):
1. Bridge lemma: for λ in the 1/200-box, v = (j,l), n:
   ((iidSum hold n) v).toReal ≤ (C₀/(1+n))·(1+4λ₁+16λ₂+1000|λ|²)ⁿ·e^{-λ·v}
   from iidSum_apply_eq_tilt (needs expW2 v ≠ 0,∞ ✓ ofReal exp) +
   tiltHold_apply_le_center (box 1/200 ⊂ 1/50 ✓) + tiltZ_hold_le_quad; toReal of
   the product; (1+u)ⁿ ≤ e^{nu} for the Z-power (u ≥ -1: Real.add_one_le_exp +
   pow mono) ⇒ exponent n(4λ₁+16λ₂+1000|λ|²) - λ·v = -λ·dev + 1000n|λ|²,
   dev = (j-4n, l-16n).
2. λ-choice per coordinate: λᵢ = clip(devᵢ/(2000n), 1/200). Exponent
   = Σᵢ (1000nλᵢ² - λᵢdevᵢ); per coord: if |devᵢ| ≤ 10n: = -devᵢ²/(4000n);
   else: = -(1/200)|devᵢ| + 1000n/40000 ≤ -(1/200)|devᵢ| + |devᵢ|/40·... check:
   1000n(1/200)² = n/40 ≤ |devᵢ|/400 (n ≤ |devᵢ|/10) ⇒ exponent ≤ -|devᵢ|(1/200 -
   1/400) = -|devᵢ|/400.
3. Gweight matching (sup norm ‖dev‖∞ = max): total exponent ≤ per-max-coord
   bound; case split on which regime the MAX coordinate is in:
   - max coord central (≤ 10n): P ≤ C₀/(1+n)·e^{-‖dev‖²/(4000n)}·e^{+slack from
     other coord ≤ 0} (other coord exponent ≤ 0 by choice at optimum... careful:
     with per-coordinate independent optimization each term is ≤ 0, so total
     ≤ max-coord term) ⇒ Gaussian branch: need -‖dev‖²/(4000n) ≤ -(c‖dev‖)²/(1+n):
     c = 1/100 say with 1+n ≥ n... (c²/(1+n) ≤ 1/(4000n) ⇔ c² ≤ (1+n)/(4000n):
     c = 1/64 ok since (1+n)/4000n ≥ 1/4000).
   - max coord tail: e^{-‖dev‖∞/400} ⇒ exp branch with c = 1/400.
   Gweight t x = exp(-x²/t) + exp(-|x|) ≥ each branch. Statement c existential:
   pick c = 1/400 uniform: Gaussian branch exp(-dev²/(4000n)) ≤ exp(-(dev/400)²/(1+n))?
   (1/4000n ≥ 1/160000(1+n) ⇔ 160000(1+n) ≥ 4000n ✓). n = 0 edge: dev = v-0 …
   check n=0 separately (iidSum 0 = pure 0; mass at v≠0 is 0, at 0: dev=(0,0),
   Gweight ≥ 1 ⇒ need C ≥ 1 ✓).
   ℤ-coordinate signs: l - 16n ∈ ℤ, first coord j - 4n could be negative in ℝ ✓
   all real arithmetic.

## Lap 39 (2026-07-12, sixth box session): (G2b-2) SECOND-COORD MGF BOUND PROVED

`Prob/Mgf.lean`: **`tiltZ_hold_snd`** (closed form Z(0,μ) = (e^{3μ}/4)·
(1-(3/4)Z_ne3(μ))⁻¹ on the 1/50 strip), **`tiltZ_pascalNe3_le_poly`**
(Z_ne3 ≤ 1+(13/3)μ+30μ² — atom-cancel pattern symbolic in μ; the cleared
inequality is TIGHT at μ=0, diff = μ²(26/3 - 76μ - …); nlinarith needs box-product
hints mul_nonneg (h1·h2)·μ² etc.), **`tiltZ_hold_snd_le`** (Z(0,μ) ≤ 1+16μ+400μ²
on |μ| ≤ 1/100 — mean 16 first order exact). AXIOM-CLEAN. Gotchas:
`pow_le_pow_left` is now `pow_le_pow_left₀`; positivity can't see through
`set E := …` atoms (use nlinarith [sq_nonneg μ] with the box); exp(3μ) = (exp μ)³
via `← Real.exp_nat_mul; norm_num`.

**BOTH 1-D LEGS DONE. (G2c) next — combine into the 2-D bound**:
`tiltZ_hold_le_quad {l1 l2} (box |λᵢ| ≤ 1/200)`:
Z(λ₁,λ₂) ≤ ofReal(√((1+8λ₁+128λ₁²)(1+32λ₂+1600λ₂²)))… avoid the square root:
statement Z² ≤ ofReal((1+4·(2λ₁)+32(2λ₁)²)·(1+16(2λ₂)+400(2λ₂)²)) directly from
tiltZ_expW2_sq_le + fst_le/snd_le (ofReal_mul merges) — then keep the SQUARED form
through the Chernoff assembly: P(S=v) ≤ P_tilt·Zⁿ·w(v)⁻¹ gives P² ≤ P_tilt²·Z^{2n}
·w(v)⁻² — no: better square-root helper after all: `le_ofReal_of_sq_le`:
x² ≤ ofReal(a·b) (a,b ≥ 0) → x ≤ ofReal(√a·√b)?? Cleanest: x ≤ ofReal r where
r² ≥ ab: choose r = 1+4λ₁+16λ₂+K|λ|² and prove RATIONAL inequality
(1+8λ₁+128λ₁²)(1+32λ₂+1600λ₂²) ≤ (1+4λ₁+16λ₂+K(λ₁²+λ₂²))² by nlinarith (first
order: 8λ₁+32λ₂ = 2(4λ₁+16λ₂) ✓ matches); K to be found numerically (cross term
8·32λ₁λ₂ vs 2·4·16λ₁λ₂ = 128λ₁λ₂ SAME ✓; so K ≈ 128+16²/…: validate numerically,
K ~ 700?). Helper x ≤ y from x² ≤ y², y = ofReal ≠ 0,∞: contrapositive +
ENNReal.pow_lt_pow_left (see lap 37 entry).
Then (F5) assembly per lap 36 entry.

## Lap 38 (2026-07-12, sixth box session): (G2b-1) FIRST-COORD MGF BOUND PROVED

`Prob/Mgf.lean`: `exp_le_one_add_add_two_sq` (e^u ≤ 1+u+2u², u ≤ 1/2, via
(1-u)⁻¹), `frac_closed_le` (monotone evaluation of a(1-r)⁻¹, free numerator),
**`tiltZ_hold_fst`** (EXACT closed form Z(μ,0) = (e^μ/4)(1-(3/4)e^μ)⁻¹, every μ),
**`tiltZ_hold_fst_le`** (Z(μ,0) ≤ ofReal(1+4μ+32μ²) on |μ| ≤ 1/100 — mean 4 first
order exact). AXIOM-CLEAN. Numerics validated pre-formalization: env1 margin
comfortable, K₁ = 32 (even 16 works); box 1/100 (box 1/25 FAILS for the second
coordinate — K₂ would blow past 600).

**(G2b-2) next — second-coordinate closed form + bound** (numerics already
validated: K₂ = 400 works at box 1/100 with E = 1+u+2u² envelope; (3/4)S < 1 holds):
1. `tiltZ_hold_snd` closed form: Z(0,μ) = ofReal(e^{3μ}/4)·(1-(3/4)·Z_ne3(μ))⁻¹ —
   wait, Z_ne3 is ℝ≥0∞-valued; state as = ofReal(e^{3μ}/4) * (1 - (3·4⁻¹)*tiltZ
   pascalNe3 (expW μ))⁻¹ (ENNReal form, from tiltZ_hold_factor at l1 = 0 + geometric
   sum — needs ENNReal.tsum_geometric on ratio (3/4)Z_ne3 which needs no side
   condition, both sides ∞ together).
2. `tiltZ_pascalNe3_le_poly`: Z_ne3(μ) ≤ ofReal((4/3)(X/(1-X))² - (1/3)(1+3μ)),
   X = E/2 — from tiltZ_pascalNe3_add: cancel the atom term via
   ENNReal.add_le_add_iff_right (pattern of tiltZ_pascalNe3_le, now symbolic);
   uses e^{3μ} ≥ 1+3μ (add_one_le_exp) on the subtracted side and
   Z_pascal = Z_gh² ≤ ofReal((X'/(1-X'))²) (tiltZ_pascal + geom_closed_le square).
3. `tiltZ_hold_snd_le`: ≤ ofReal(1+16μ+400μ²) on |μ| ≤ 1/100: frac_closed_le with
   numerator e^{3μ} ≤ E³ (pow of envelope) wait e^{3μ} = (e^μ)³ ≤ E³ ✓, ratio
   (3/4)S; the final real inequality E³/4 ≤ (1+16μ+400μ²)(1-(3/4)S(μ)) after
   clearing (1-X)² — nlinarith, may need staged haves (degree 8; if nlinarith
   stalls: intermediate bound S ≤ rational quadratic first, numerically:
   S(u) ≈ 1+(13/3)·3u?? no: S'(0) = 13/3·... just S ≤ 1 + 13u + 60u² check
   numerically then chain).
4. Combine via tiltZ_expW2_sq_le + sqrt-free helper (x² ≤ ofReal(a)·ofReal(b) →
   x ≤ ofReal(√(ab)) avoided: state target Z ≤ ofReal(exp(4λ₁+16λ₂+K̄|λ|²)) and
   verify square: need x ≤ y from x² ≤ y²: ENNReal.pow_le_pow_iff_left or
   contrapositive with pow_lt_pow_left, y = ofReal exp ≠ 0).
Then (F5) final assembly (see lap 36 entry).

## Lap 37 (2026-07-12, sixth box session): (G2a) CAUCHY–SCHWARZ MGF SPLIT PROVED

`Prob/Tilt.lean`: **`tsum_mul_mul_sq_le`** — weighted Cauchy–Schwarz
`(Σ p·u·v)² ≤ (Σ p·u²)(Σ p·v²)` entirely in ℝ≥0∞ (double-sum expansion + pointwise
AM–GM `ennreal_mul_le_sq_add_sq_div_two`; no summability side conditions —
mathlib's Hölder is ℝ≥0-only with summability hypotheses).
`Prob/Mgf.lean`: `expW2_eq_mul`, `expW2_sq`, **`tiltZ_expW2_sq_le`** —
`Z(λ₁,λ₂)² ≤ Z(2λ₁,0)·Z(0,2λ₂)`. KEY DESIGN WIN: CS preserves the first-order
(mean) term exactly (AM–GM would not), so the 2-D second-order bound (G2) reduces
to two 1-D closed-form bounds and the hold mean identities (G1) are NOT needed as
separate tsum computations. AXIOM-CLEAN. Gotchas: `ℝ≥0` notation needs
`open scoped NNReal` (use `NNReal` verbatim otherwise); `zero_le _` fails in
ENNReal term mode — use `bot_le`; `ENNReal.div_eq_top` disjuncts are
(num ≠ 0 ∧ den = 0) | (num = ∞ ∧ den ≠ ∞).

**(G2b) next — the two 1-D second-order bounds** (in Mgf.lean), target box
|μ| ≤ 1/25 (doubled tilt):
1. Closed form `tiltZ hold (expW2 μ 0) = (1/4)e^μ(1-(3/4)e^μ)⁻¹` — from
   tiltZ_hold_factor at l2 = 0 (tiltZ pascalNe3 (expW 0) = 1 by PMF mass; need
   tiltZ_one lemma) + geometric series; mean 4 built in.
2. Closed form `tiltZ hold (expW2 0 μ) = (1/4)e^{3μ}(1-(3/4)Z_ne3(μ))⁻¹` with
   Z_ne3(μ) = (4/3)(x/(1-x))² - (1/3)e^{3μ}, x = e^μ/2 (tiltZ_pascalNe3_add,
   ENNReal sub OK since finite); mean 16 built in.
3. Numeric second-order bounds via envelope 1+u ≤ e^u ≤ 1+u+u² (|u| ≤ 1/8 say;
   3μ ∈ [-3/25, 3/25] ok): `Z(μ,0) ≤ ofReal(exp(4μ + K₁μ²))` and
   `Z(0,μ) ≤ ofReal(exp(16μ + K₂μ²))` — prove first `≤ ofReal(1 + 4μ + K₁μ²)` by
   cross-multiplied nlinarith (denominators positive on box), then 1+x ≤ eˣ.
   Numeric check (do BEFORE formalizing, corpus rule): K₁ ≥ ~32, K₂ ≥ ~600?
   compute margins numerically first.
4. Combine: Z(λ)² ≤ e^{8λ₁+4K₁λ₁²}·e^{32λ₂+4K₂λ₂²} ⇒ Z ≤ e^{4λ₁+16λ₂+2K̄|λ|²}
   via ENNReal sqrt-free helper `x² ≤ ofReal(a²) → x ≤ ofReal(a)` (contrapositive
   + ENNReal.pow_lt_pow_left).
Then (F5): assembly with iidSum_apply_eq_tilt + tiltHold_apply_le_center +
per-coordinate λ-clip ⇒ hold_local_bound.

## Lap 36 (2026-07-12, sixth box session): (F4b) TILTED CENTER BOUND PROVED

`Sec7/HoldLocal.lean` NEW (imports Unroll + Mgf; the S3 assembly module):
**`tilt_hold_map_mass`** (four atoms ≥ 1/400 after tilt + mod-N projection) and
**`tiltHold_apply_le_center`** — `P_λ(S̃_n = v) ≤ (32·80000)²/(1+n)` uniformly on
the tilt box |λᵢ| ≤ 1/50 (charFn_decay_of_atoms at μ = 1/400 ⇒ c = 80000 ⇒
iidSum_apply_le_center_of_decay). AXIOM-CLEAN, compiled first try — the parametric
chain (F3a)+(F3b)+(F4a) composed with zero friction.

**(F5) next — the Chernoff assembly for `hold_local_bound`** (in HoldLocal.lean):
1. (G1) hold mean identities: `∑' d, hold d * d.1 = 4`, `∑' d, hold d * d.2.toNat
   = 16` (second coord ≥ 3 on support so ℕ-valued; both as ENNReal tsums; via
   hold's bind/map structure + geometric means: E gQ = 4, E pascalNe3 = 13/3,
   E[3 + (k-1)-fold] = 3 + 3·(13/3) = 16).
2. (G2) second-order MGF bound: `tiltZ hold (expW2 λ) ≤ ofReal (1 + 4λ₁ + 16λ₂
   + K(λ₁²+λ₂²))` on a shrunk box |λᵢ| ≤ δ (δ = 1/100, K explicit): pointwise
   `e^u ≤ 1 + u + u²e^{|u|}/2` (u = λ·d), then Σ hold(d)·u² e^{|u|} ≤
   |λ|²·Σ hold(d)(d₁+|d₂|)² e^{δ(d₁+|d₂|)} ≤ |λ|²·(2/δ²)·Σ hold(d) e^{2δ(d₁+d₂)}
   (x² ≤ (2/δ²)e^{δx}; d₂ ≥ 3 ≥ 0 on support so |d₂| = d₂) = |λ|²·(2/δ²)·
   tiltZ hold (expW2 2δ 2δ) ≤ |λ|²·(2/δ²)·(221/25) with 2δ = 1/50. Mean term from
   (G1). All in ENNReal/ofReal carefully, or via toReal with finiteness.
3. (F5) assembly: `iidSum_apply_eq_tilt` (consumption form) + `tiltHold_apply_le_center`
   ⇒ P(S_n = (j,l)) ≤ C₀/(1+n) · (Z e^{-λ·(4,16)})ⁿ · e^{-λ·dev}, dev = (j-4n, l-16n);
   (G2) ⇒ (Ze^{-λ·mean})ⁿ ≤ exp(nK|λ|²) [need e^{-λ·(4,16)}-multiplied form: restate
   (G2) as Z ≤ ofReal(exp(4λ₁+16λ₂+K|λ|²)) via 1+x ≤ eˣ]. Choose λ = clip:
   center |devᵢ| ≤ 4Kδn: λᵢ = devᵢ/(4Kn) ⇒ exponent ≤ -|dev|²/(8Kn) ⇒ Gaussian
   branch of Gweight (constant c ≤ 1/√(8K·2) etc); else λᵢ = ±δ·sign(devᵢ) ⇒
   ≤ exp(-δ‖dev‖₁/2)-ish ⇒ exp branch. Case split per coordinate — 2-D clip is
   componentwise, exponent separates: nK(λ₁²+λ₂²) - λ₁dev₁ - λ₂dev₂ optimizes
   per-coordinate independently. Gweight consumes sup-norm ‖dev‖_∞; exponent
   bound gives per-coord products ⇒ take the max coord for the bound.

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
