# STATUS — tao-collatz 📊

**First-anywhere Lean 4 formalization of Tao 2019 "Almost all Collatz orbits
 attain almost bounded values" (Thm 1.3).** · **Build**: 🟢 green (3282 jobs) ·
**Updated**: review lap · 2026-07-14 · `7e2398f`

## Where it stands

Multi-month campaign; the §7 crux (Prop 1.17) is the risk concentration and is
under active assault. **Both pinnacle kernels are done and axiom-clean**: X9
(Lemma 7.9 `many_triangles_white`) and X10 (Lemma 7.10 `triangle_encounter_le`),
alongside S3, X3, X6, X1, X2, X5, X4/X7. **X8 / Case-2 is now COMPLETE and
axiom-clean** — both kernels (`fpDist_edgeWeight_le`, `fpDist_white_exit`) and the
assembly `Q_black_edge_case2` verify `[propext, choice, Quot.sound]`. The §7
monotonicity chain now hinges on **EXACTLY ONE sorry**: X11 `Q_black_edge_case3`
(`Case3.lean:1062`) — confirmed the sole `sorryAx` carrier under `prop_7_8`.
Its three bridges (`fstar_markov`, `fpDist_walk_eq_fpDistPlus`,
`bigTriangle_walk_le`) are all proved and axiom-clean; the remaining assembly is
X11a `estar_union_le` (sum the per-`p` bridge over the horizon) → X11c
`few_whites_le` → the X11d body. Beyond §7: 6 deliberate spine stubs
(`SyracRV` ×3, `FirstPassage` ×2, `MixingFromDecay` ×1, `Collatz` ×1) plus the
2 headline sorries in `Statement.lean`. **9 actual proof `sorry`s remain in
`TaoCollatz/` total** (2 headline + 1 crux + 6 spine).

## What's happened (newest first)

- **review lap (2026-07-14)**: direction confirmed sound — recent laps drove
  straight at the X11 crux, not side-leaves. `#print axioms` re-run: X8
  `Q_black_edge_case2`/`fpDist_white_exit`, X9 `many_triangles_white`, X10
  `triangle_encounter_le`, and all three X11 bridges verify trust-base-only;
  `prop_7_8` carries `sorryAx` solely via `Q_black_edge_case3`. Directive
  narrowed to closing X11 (X11a → X11c → X11d); STATUS refreshed.
- **lap D-box cont8–12 (2026-07-14)**: **X8 / Case-2 CLOSED** —
  `fpDist_white_exit` proved via kernel-merge relocation (new `BlackEdgeQ.lean`),
  `Q_black_edge_case2` assembled. **X11 crux opened**: three axiom-clean bridges
  landed — `fstar_markov` (7.56 Markov, X9-discharged), `fpDist_walk_eq_fpDistPlus`
  (7.53→7.54 walk→fpDistPlus), `bigTriangle_walk_le` (per-`p` E∗ term, validates
  X11a composes with X10). Next = `estar_union_le` (X11a).
- **lap D-box cont1–7 (2026-07-14)**: X8 first-coord MGF engine —
  `fpDist_fst_mgf_le`/`_general`, `fpDist_fst_tail_le`, `hold_fst_tail_le`,
  `fpDist_edgeWeight_le` (the (7.48) weight-degradation crux) all axiom-clean.

- **lap 59 (2026-07-13, X11 LOCALIZATION DE-RISK)**: replaced the false
  fixed-Euclidean-radius idea and the speculative packing route with the paper's
  actual quantifier order. Proved `fpDist ≤ stepMass`; then proved an explicit
  negative-drift Chernoff tail for `16*j-5*l` by summing every positive renewal
  time (`-39/400000` MGF exponent/step), including the checked numerical bound
  `P(40000000 ≤ 16*j-5*l) ≤ 1/16`. Combined X6's height tail with a chosen
  integer `Y` (`≤1/16`) to obtain `exists_fpDist_localization_box` (`≤1/8`
  total). Proved the parameterized deterministic bridge
  `phaseInFamily_support_imp_localization_bad` using `9^5 < 2^16`, and closed all
  foreign-mass bookkeeping in `fpDist_any_triangle_le_of_localization_box`.
  **The sole residue is now a quantifier-order/configuration obligation**:
  choose/parameterize `epsBW` after this box so Lemma 7.4 separation exceeds
  `sqrt(X²+Y²)`. Targeted build green.
- **lap 58 (2026-07-13, X11 HARDEST GEOMETRY)**: executed the D4 change
  `epsBW = 10⁻⁹⁰` and fully formalized Lemma 7.4 Claim (*) Cases 1--3.
  `black_structure` now proves genuine pairwise set separation
  `(1/10)log(1/ε) = 9 log 10 ≈ 20.7`; the former sub-unit lattice-spacing
  shortcut is gone and `Triangles.lean` is sorry-free. Added exact-rational
  near-corner scale bounds, weak row/column propagation, and the checked
  `phaseInFamily_support_imp_margin`: foreign capture forces either vertical
  overshoot `> 14` or horizontal clearance more than 14 columns past the top
  face. Full `lake build` green after the epsilon sweep. **Remaining X11 risk is
  sharply isolated**: `fpDist_any_triangle_le` must exploit foreign-triangle
  shape/packing. A crude distance-tail union bound is insufficient at separation
  20.7 (renewal harness: distance-tail about 0.27 versus the required 0.125), so
  do not resurrect that route without either a packing lemma or a stronger D4
  altitude.
- **lap 57 (2026-07-13, X11 RISK BURN-DOWN)**: collapsed X11 from four
  unresolved interfaces to one authoritative gate, `Q_black_edge_case3`, after
  all checked support in `Case3.lean`. Replaced the import-cycle-prone upstream
  placeholder with locally checked parameterized assemblies in `BlackEdge.lean`; the
  public `Q_black_edge` → Proposition 7.8 → polynomial-decay chain now consumes
  the sole downstream gate directly. The gate owns the finite union/numerical
  join and depends on the single upstream geometry gate
  `fpDist_any_triangle_le`.
- **lap 56 (2026-07-12, REVIEW + crux advance)**: verified X9 CLOSED modulo
  exactly `fpDist_white_exit_deep`; route **CONTINUE**, no trigger; Aristotle
  idle. Then **PROVED `fpDist_white_exit_deep`** from the (7.50)-geometry
  decomposition: `endpoint_notMem_start_triangle` (overshoot clears the apex,
  axiom-clean) + `outStripSet`/`phaseInFamily` complement split via
  `white=¬black` + `F.cover` + axiom-clean tsum reduction glue; residual =
  two named `≤ 1/8` analytic tails (`fpDist_out_of_strip_le`,
  `fpDist_any_triangle_le`), both X6-Gaussian. `p₀ = 3/4`.
- **lap 55 (2026-07-12, DEEP REFLECTION)**: route verdict **CONTINUE** (T1
  cleared lap 52; T2 source-grounded as unlikely — the (7.65) separation comes
  from Lemma 7.4 integer-disjointness, already proved as `apex_separation`).
  Read pp.49–55 against the X9/X10/X11 pins. **Found the X9 near-edge
  statement-truth risk** + two consumable fixes verified against the actual
  p.49/p.55 consumer; **softened the p₀ > 1/2 burden** (paper only needs ≫1;
  any certified c₀ > ~ε is consumable); re-rated X10 up (precedented volume).
  Re-ran `#print axioms` on 16 headline decls — all clean. New directive:
  X9 depth-gate → close 7.9 → white-exit kernel → X10. No prior art (re-checked).
- **lap 54 cont (2026-07-12)**: **X2 CLOSED** — `white_cos_bound` proved;
  `Sec7/White.lean` sorry-free. X9 assembly opened: chain arithmetic
  (`encChainX` fixed point, `encounter_vertex_bound` LP), CLAIM-G coupling
  (`encExpect_normalize(_init)`), gluing pieces (wander, edge freeze, two-mass)
  all proved axiom-clean; `fpDist_white_exit_deep` pinned as X9's only external
  input.
- **lap 54 (2026-07-12)** `9321b5c`: **X5 CLOSED** — Lemma 7.6 (Hold basics,
  p.42) fully machine-checked: mean (4,16) + aperiodicity proved axiom-clean in
  new `Sec7/HoldBasics.lean`.
- **lap 53 (2026-07-12)** `ade5d6d`: **X1 CLOSED** — `cexpect_pairing`
  ((7.4)/(7.5)) proved axiom-clean; Prop 7.1 `key_fourier_decay` and Prop 1.17
  `charFn_decay` now theorems over the Prop 7.8 chain. `Sec7/Reduction.lean`
  sorry-free.
- **lap 52 (cont)** `0ba065f`: **encExpect_block_le PROVED** (path→fpDist block
  bridge) + **ROUTE FINDING**: the paper's Lemma 7.9 proof has a gap (p.51
  banking display false on the min(r,R)=1 branch); pin corrected exp(ε)→exp(2ε),
  judge-confirmed (pass 9), consumer-safe.
- **lap 52 (2026-07-12)** `1c9b2c8`: **Lemma 7.9 (X9) PINNED, RED→YELLOW** —
  `EncState`/`encStep` encounter fold, `many_triangles_white` (7.57) pin,
  head-peel recursion proved. T1 does not fire.
- **lap 51 (2026-07-12, review)**: course-correction; DIRECTION.md created; §7
  tail de-risk directive set; X10 pinned with geometric core (`apex_gap`,
  `apex_separation`) proved.
- **lap 50 (2026-07-12)** `5f469e9`: **LEMMA 7.7 PROVED, X6 CLOSED** —
  `fpDist_location_bound` axiom-clean (unconditional in `s`); both X8 Case-2
  kernels unblocked.
- **laps 46–49 (2026-07-12)**: X6 renewal machinery (`renewalMass_bound`,
  Gaussian AP engine, first-passage renewal decomposition); X8/X10
  `Q_black_edge` decomposed into 4 named sub-sorries.
- **lap 45 (2026-07-12)**: **S3 FULLY GREEN** — all 8 Lemma 2.2 obligations
  machine-checked (judge pass 5).
- **laps 36–44**: the S3 analytic engine (2-D MGF/tilting, circle method,
  tilted center bound).
- **earlier**: X3 (Lemma 7.4 triangles, judge-verified), Q-recursion / Qstop /
  fpDist D6 machinery, PMF/Fourier/tilting support layers.

## Outstanding

### Short-term (mirror PENDING_WORK top)
- **X11a `estar_union_le`** (NEXT crux sub-lemma): sum the proved per-`p`
  `bigTriangle_walk_le` over `p ∈ range(T+1)` at `s'=⌈4^A(1+p)³⌉`. Needs
  `Σ_p (1+p)^{-2} ≤ 2` (telescoping) for the `1/s'` terms + geometric
  `Σ_p exp(−c·A²(1+p))` with the comparison `exp(−cA²) ≤ const·A²·4^{-A}` for
  `A ≥ A₀`. Net E∗-mass `≤ C'·A²·4^{-A}`.
- **X11c `few_whites_le`**, then **X11d body** `Q_black_edge_case3` — see
  PENDING_WORK top for the full X11 attack path.

### Long-term
- After X11 lands: `Q_black_edge → prop_7_8 → Q_polynomial_decay` go clean and
  §7 monotonicity is done; assemble Prop 1.17 → C10 → C9 → C6 → headline.
- 🗂️ `ManyTriangles.lean` split (BLUEPRINT §2, 5k+ lines) — queued, pure moves;
  do only when off the X11 critical path.
- C8 pin (Prop 5.2, §5) — the last RED statement-less node; opportunistic.
- Spine stubs: `SyracRV` ×3, `FirstPassage` ×2, `MixingFromDecay` ×1,
  `Collatz` ×1 (6 stub sorries, downstream of the crux, deliberately deferred).

### To completion
Close X11 `Q_black_edge_case3` → §7 crux assembles → Prop 1.17 → Prop 1.14 →
C10 → C9 → C6 → Thm 1.3; discharge the 6 spine `sorry`s; `#print axioms` on the
`Statement` headline = trust base only.

## Axiom ledger (fidelity spine)

The headline theorems are NOT yet assembled — the spine (§1–§6) is stubbed while
the §7 crux is built bottom-up. Ledger re-run this review lap (2026-07-14, real
`#print axioms` at `7e2398f`):

| headline / node | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Statement` Thm 1.3 / Thm 3.1 | Thm 1.3 (uncond.) | `sorry` (spine not assembled) | 🔜 stub — downstream of crux |
| S3 `hold_local_bound` / `hold_tail_bound` | Lemma 2.2(i)(ii) Hold | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X3 `black_structure` | Lemma 7.4 | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X6 `fpDist_location_bound` | Lemma 7.7 | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X1 `cexpect_pairing` | (7.4)/(7.5) | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X2 `white_cos_bound` / `fCond_three_norm` | Lemma 7.2 | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X5 `hold_mean_fst` / `hold_aperiodic` | Lemma 7.6 | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X9 `many_triangles_white` (Lemma 7.9) | (7.57) pp.50–51 | `[propext, choice, Quot.sound]` | 🟢 CLOSED, clean |
| X10 `triangle_encounter_le` (Lemma 7.10) | (7.65) pp.52–54 | `[propext, choice, Quot.sound]` | 🟢 CLOSED, clean |
| X8 `Q_black_edge_case2` (Prop 7.8 Case 2) | (7.46)–(7.51) | `[propext, choice, Quot.sound]` | 🟢 CLOSED, clean |
| X11 `Q_black_edge_case3` (Prop 7.8 Case 3) | (7.53)–(7.67) | `sorry` (3 bridges clean) | 🟡 sole open §7 crux |
| `prop_7_8` (Prop 7.8 Monotonicity) | §7 headline | trust base + `sorryAx` | 🟡 theorem over the single open X11 sorry |

Math-axiom count on every completed node = **0** (trust base only). No 🔴
(open-conjecture) axioms anywhere — correct, since Thm 1.3 is unconditional. No
🟡/🟠 *cited* axioms in use: the crux is being PROVED, not cited. The remaining
work is `sorry`-discharge (1 crux + 6 spine + 2 headline), not axiom-discharge.

## Pointers
DIRECTION.md (binding directive) · BLUEPRINT.md (frozen node ledger §2) ·
newest `HANDOFF-2026-07-14-e.md` · PENDING_WORK.md (X11 attack path, newest top) ·
papers/literature-review.md (route-facing source synthesis) ·
paper `papers/tao-2019-almost-all-orbits.pdf`.
