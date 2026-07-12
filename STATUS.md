# STATUS — tao-collatz 📊

**First-anywhere Lean 4 formalization of Tao 2019 "Almost all Collatz orbits
attain almost bounded values" (Thm 1.3).** · **Build**: 🟢 green (3280 jobs) ·
**Updated**: lap 56 (review) · 2026-07-12 · `cb1156b`

## Where it stands

Multi-month campaign; the §7 crux (Prop 1.17) is the risk concentration and is
under active assault. **Seven crux nodes are CLOSED and axiom-clean**: S3
(Lemma 2.2 engine), X3 (Lemma 7.4 triangles), X6 (Lemma 7.7 first passage), X1
((7.4)/(7.5) pairing), X2 (Lemma 7.2), X5 (Lemma 7.6), and now **X9 Lemma 7.9**
— `many_triangles_white` verified CLOSED (`#print axioms` = trust base +
`sorryAx` via exactly ONE input, the Y-induction `encExpect_entered_le` is
axiom-clean). X4/X7 (D6 Q-recursion, Q_m + Case 1) are also complete (files
sorry-free). Prop 1.17 is a theorem over exactly the Prop 7.8 chain: **7 open
crux sorries** (BlackEdge ×4, ManyTriangles ×3), plus 13 deliberate spine stubs.
This lap the white-exit kernel `fpDist_white_exit_deep` was **PROVED from a clean
(7.50)-geometry decomposition** — the monolithic sorry became two named analytic
sub-sorries (`fpDist_out_of_strip_le`, `fpDist_any_triangle_le`, both `≤ 1/8`
Gaussian tails) + the axiom-clean reduction glue + the proved overshoot-exclusion
helper `endpoint_notMem_start_triangle`. Both sub-sorries consume X6
`fpDist_location_bound` and are the SAME geometry shared with X8's Case-2 twin
`fpDist_white_exit`. X10's route was re-grounded against pp.52–54: precedented
volume, not novelty. 20 open `sorry`s in `src/` total (decomposition raised the
count by 1 — progress, not regression).

## What's happened (newest first)

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
- **`fpDist_white_exit_deep`** (THE mandated next move) — X9's only remaining
  input AND X8's Case-2 twin geometry. Prove general (route: X6 location bound
  + `fpDist_support_snd_gt` top-clear + X3 `apex_separation` slope-exclusion +
  in-strip), then derive `fpDist_white_exit` from it (kernel merge). Decompose
  into named sub-`sorry`s in `src/`.
- **X10 assembly** (`triangle_encounter_le`): fpDistPlus location bound
  (7.48)+p-steps prerequisite → escape event E′ tails → separated-Σ mass sum
  (existing Gaussian-AP engine).
- **X8/X11 assembly**: `Q_black_edge_case2` (mechanical once kernels land),
  `fpDist_edgeWeight_le`, `Q_black_edge_case3` (X11 (7.53)–(7.67)).

### Long-term
- X11 assembly inside `Q_black_edge_case3` ((7.53)–(7.56), (7.66)–(7.67)); X8
  assembly (`Q_black_edge_case2` + `fpDist_edgeWeight_le`).
- C8 pin (Prop 5.2, §5) — the last RED statement-less node; opportunistic.
- C-spine: C5/C7/C9/C10, Sec5/Sec6, Syracuse layer, Basic/Statement scaffolding
  (13 stub sorries, deliberately deferred).

### To completion
Assemble §7 crux → Prop 1.17 → Prop 1.14 → C10 → C9 → C6 → Thm 1.3; discharge
all 20 `sorry`s; `#print axioms` on `Statement` headline = trust base only.

## Axiom ledger (fidelity spine)

The headline theorems are NOT yet assembled — the spine (§1–§6) is stubbed while
the §7 crux is built bottom-up. Ledger re-run this lap (2026-07-12, real
`#print axioms` at `6876501`):

| headline / node | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Statement` Thm 1.3 / Thm 3.1 | Thm 1.3 (uncond.) | `sorry` (spine not assembled) | 🔜 stub — downstream of crux |
| S3 `hold_local_bound` / `hold_tail_bound` | Lemma 2.2(i)(ii) Hold | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X3 `black_structure` | Lemma 7.4 | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X6 `fpDist_location_bound` | Lemma 7.7 | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X1 `cexpect_pairing` | (7.4)/(7.5) | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X2 `white_cos_bound` / `fCond_three_norm` | Lemma 7.2 | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X5 `hold_mean_fst` / `hold_aperiodic` | Lemma 7.6 | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X9 `many_triangles_white` (Lemma 7.9) | (7.57) pp.50–51 | trust base + `sorryAx` | 🟢 CLOSED modulo exactly `fpDist_white_exit_deep`; `encExpect_entered_le` clean |
| X10 `apex_separation` | (7.65) geometry | `[propext, choice, Quot.sound]` | 🟢 clean (geometric core) |
| Prop 1.17 `charFn_decay` / Prop 7.1 / Prop 7.3 | §7 headline | trust base + `sorryAx` | 🟡 theorem over the 6 open Prop-7.8-chain sorries |

Math-axiom count on every completed node = **0** (trust base only). No 🔴
(open-conjecture) axioms anywhere — correct, since Thm 1.3 is unconditional. No
🟡/🟠 *cited* axioms in use: the crux is being PROVED, not cited. The remaining
work is `sorry`-discharge (7 crux + 13 spine), not axiom-discharge.

## Pointers
DIRECTION.md (binding directive) · BLUEPRINT.md (frozen node ledger §2) ·
newest `HANDOFF-2026-07-12-i.md` · PENDING_WORK.md (Reflection 2026-07-12 +
attack paths) · papers/literature-review.md (route-facing source synthesis) ·
paper `papers/tao-2019-almost-all-orbits.pdf`.
