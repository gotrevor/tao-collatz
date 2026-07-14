# STATUS — tao-collatz 📊

**First-anywhere Lean 4 formalization of Tao 2019 "Almost all Collatz orbits
 attain almost bounded values" (Thm 1.3).** · **Build**: 🟢 green (3285 jobs) ·
**Updated**: review lap · 2026-07-14 · `1c3ee3d`

## Where it stands

**🏆 §7 — the campaign's stated 65–75% risk concentration ("the paper's
pinnacle", X8/X9/X10/X11) — is CLOSED and axiom-clean.** Review-lap `#print
axioms`: `prop_7_8`, `Q_black_edge`, `Q_polynomial_decay`, `charFn_decay`
(Prop 1.17), `key_fourier_decay` (Prop 7.1) all = `[propext, choice, Quot.sound]`.
All of SyracRV, S3, X1–X10, X11 done and clean. **The content spine now has
EXACTLY TWO open heroic sorries** (+ 2 frozen headline stubs): C10
`fine_scale_mixing` (Prop 1.14, §6, `MixingFromDecay.lean:377`) and C9
`stabilization` (Prop 1.11, §5, `FirstPassage.lean:81`, consumes C10). The
current crux is **C10** — upstream on the critical path `C10 → C9 → C6 →
Statement`, and NOT a new kernel: its two hard ingredients (the CS/Parseval
bridge `osc_le_sqrt_highfreq`, and `charFn_decay`) are already proved
axiom-clean, so C10 is the §6 conditioning *assembly* that plugs decay into the
bridge on a conditioned density `g`. **4 real proof `sorry`s remain total** (2
headline + C10 + C9).

## What's happened (newest first)

- **review lap (2026-07-14)**: **§7 CROSSED** — inventory found only 4 live
  sorries (2 headline + C10 + C9); `#print axioms` confirms `prop_7_8` +
  full §7 chain (Q_black_edge, Q_polynomial_decay, charFn_decay,
  key_fourier_decay) all trust-base clean. DIRECTION.md CURRENT DIRECTIVE +
  STATUS were stale (pointed at the now-closed X11); both rewritten. New
  frontier = C10 `fine_scale_mixing` via the fruit-8 conditioning route.
- **lap fruit-8 (2026-07-15)**: C10 Cauchy–Schwarz/Parseval bridge
  `osc_le_sqrt_highfreq` FULLY PROVED, axiom-clean (8 reusable lemmas). Naive
  `highfreq_l2_le` route REFUTED (raw high-freq L² mass GROWS ≈0.46n, exact DP)
  → remapped to Tao's §6 conditioning of the density; `fine_scale_mixing`
  reverted to a documented `sorry` on the correct route.
- **lap fruit-7 (2026-07-14)**: Parseval on `ZMod N` PROVED (`Fourier/Parseval.lean`,
  node S4); full C10 route mapped; `fine_scale_mixing` decomposed into
  `osc_le_sqrt_highfreq` + `highfreq_l2_le`.
- **lap fruit-6 (2026-07-14)**: Lemma 1.12 `syracZ_recursion` PROVED — **all of
  SyracRV closed**, axiom-clean.
- **§7 close-out (2026-07-14)**: X11 `Q_black_edge_case3` + the two Case-3
  sorries (`few_white_mass_le`, `col_tail_mass_le`) proved; X10 `_rpow` split
  landed; `prop_7_8` → `Q_polynomial_decay` axiom-clean.
- **review lap (2026-07-14, earlier)**: direction confirmed sound — recent laps drove
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

### Short-term (mirror PENDING_WORK top — C10 fruit-8 route)
- **brick (d)** (START HERE, mechanical): generalize `osc_le_sqrt_highfreq` +
  helpers (`densC`,`devC`,`condAvgC`,`sum_norm_sq_devC_eq`,…) from
  `fun Y=>(syracZ n Y).toReal` to an arbitrary real `c : ZMod (3^n)→ℝ`
  (proofs never used syracZ-ness) — unblocks applying the proved bridge to the
  conditioned density `g`.
- **brick (a)** the independent `F`-split `Xₙ = F_{k+1}(…) + 3^{k+1}2^{-l}F_{n-k-1}(…)`
  on `Cₖ,ₗ` as a Lean identity ((1.5)/(1.26)); **brick (b)** independence ⟹
  char-sum factorization; then the conditioning events + `charFn_decay` on the
  2nd factor + triangle reassembly. See PENDING_WORK fruit-8.

### Long-term
- After C10 lands: attack C9 `stabilization` (Prop 1.11, §5) — consumes C10 —
  then assemble C6 → the two `Statement.lean` headlines.
- 🗂️ `ManyTriangles.lean` split (BLUEPRINT §2, 5k+ lines) — queued, pure moves;
  off the critical path, opportunistic only.

### To completion
Close C10 `fine_scale_mixing` → C9 `stabilization` → C6 → wire the two
`Statement.lean` headlines; `#print axioms tao_collatz` = trust base only.

## Axiom ledger (fidelity spine)

The two headline theorems are NOT yet assembled — the §1–§6 spine feeds into
`Statement` only after C10/C9/C6 land. §7 (the crux) is fully closed. Ledger
re-run this review lap (2026-07-14, real `#print axioms` at `1c3ee3d`):

| headline / node | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Statement` Thm 1.3 / Thm 3.1 | Thm 1.3 (uncond.) | `sorry` (spine not assembled) | 🔜 stub — discharges when C10/C9/C6 land |
| C10 `fine_scale_mixing` (Prop 1.14) | §6 fine-scale mixing | trust base + `sorryAx` | 🟡 **current crux** — bridge+charFn_decay proved, needs §6 conditioning assembly |
| C9 `stabilization` (Prop 1.11) | §5 first-passage stab. | trust base + `sorryAx` | 🟡 downstream of C10; narrow only |
| `charFn_decay` (Prop 1.17) | key char-sum decay | `[propext, choice, Quot.sound]` | 🟢 done, clean (C10's analytic input) |
| `key_fourier_decay` (Prop 7.1) | (7.1) Fourier decay | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| `prop_7_8` / `Q_black_edge` / `Q_polynomial_decay` | Prop 7.8 monotonicity | `[propext, choice, Quot.sound]` | 🟢 **§7 CLOSED, clean** |
| X8/X9/X10/X11 kernels | Lemmas 7.6–7.10, (7.46)–(7.67) | `[propext, choice, Quot.sound]` | 🟢 all CLOSED, clean |
| S3/X1/X2/X3/X5/X6 + all SyracRV | Lemma 2.2, 7.2, 7.4, 7.6, 7.7, 1.12 | `[propext, choice, Quot.sound]` | 🟢 done, clean |

Math-axiom count on every completed node = **0** (trust base only). No 🔴
(open-conjecture) axioms anywhere — correct, since Thm 1.3 is unconditional. No
🟡/🟠 *cited* axioms: the two remaining nodes (C10, C9) are being PROVED, not
cited. Remaining work is `sorry`-discharge (C10 crux + C9 + 2 headline), not
axiom-discharge.

## Pointers
DIRECTION.md (binding directive) · BLUEPRINT.md (frozen node ledger §2) ·
newest `HANDOFF-2026-07-15-0300.md` · PENDING_WORK.md (fruit-8 C10 attack path,
newest top) · papers/literature-review.md (route-facing source synthesis) ·
paper `papers/tao-2019-almost-all-orbits.pdf`.
