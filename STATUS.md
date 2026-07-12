# STATUS — tao-collatz 📊

**First-anywhere Lean 4 formalization of Tao 2019 "Almost all Collatz orbits
attain almost bounded values" (Thm 1.3).** · **Build**: 🟢 green (3276 jobs) ·
**Updated**: lap 52 · 2026-07-12 · `0ba065f`

## Where it stands

Multi-month campaign; the §7 crux (Prop 1.17) is the risk concentration and is
under active assault. **Two of the three hard crux kernels are CLOSED and
axiom-clean**: S3 (Lemma 2.2 local/tail bounds for Hold + 3 d=1 walks, laps 22–45)
and X6 (Lemma 7.7 first-passage location, laps 47–50). X3 (Lemma 7.4 triangles)
also done. The critical path `S3✓ → X6✓ → {X8, X10} → X11 → C10 → …` now sits at
the §7.4 case analysis: X8 Case 2 is YELLOW (statements pinned + routed, two
kernels open but unblocked by X6); **X10 and X9 (Lemmas 7.10/7.9) are now BOTH
pinned (YELLOW)** — 7.10 with its geometric core (apex separation) proved, 7.9 via
the finite-horizon encounter-fold encoding with the head-peel recursion proved and
route-trigger T1 confirmed NOT to fire. No RED statement-less node remains on the
§7 critical path; the risk is now concentrated in the pinned sorries themselves. The C-spine (§1–§6) and the
Syracuse/Statement scaffolding are deliberately still stubbed — downstream of the
crux, cheap once §7 lands. 24 open `sorry`s in `src/`.

## What's happened (newest first)

- **lap 52 (cont)** `0ba065f`: **encExpect_block_le PROVED** (path→fpDist block
  bridge, the X9 crux sub-step) + **ROUTE FINDING**: the paper's Lemma 7.9 proof
  has a gap (min(r,R)=1 branch of the p.51 conditional display); corrected chain
  ledger gives exp(ε/p₀) — pin corrected to exp(2ε), consumer-safe. Coupling +
  frozen-state lemmas proved. See HANDOFF-2026-07-12-f.
- **lap 52 (2026-07-12)** `1c9b2c8`: **Lemma 7.9 (X9) PINNED, RED→YELLOW** —
  `EncState`/`encStep` encounter fold (stopping times as a left fold over
  `hold.iid T`, finite horizon uniformly in T), `many_triangles_white` (7.57) pin,
  `encExpect_succ` head-peel recursion + envelope lemmas proved axiom-clean.
  Read pp.48–55: T1 does not fire (consumer only uses finite windows). Next:
  path→fpDist bridge, then the R-induction (closure blocked only on
  `fpDist_white_exit`).
- **lap 51 (2026-07-12, review)**: fresh-mind course-correction. Verified build
  green + S3/X3/X6 axiom-clean via real `#print axioms`. Read paper pp.50–54
  (Lemmas 7.9/7.10). Set CURRENT DIRECTIVE: de-risk §7 tail (pin 7.10 then 7.9)
  breadth-first; relegated X8 completion to finish-when-downhill. Created
  DIRECTION.md + STATUS.md. Key finding: 7.10 is single-marginal (directly
  pinnable via `fpDist∘iidSum`), 7.9 needs a stopping-time→recursion encoding.
- **lap 50 (2026-07-12)** `5f469e9`: **LEMMA 7.7 PROVED, X6 CLOSED** —
  `fpDist_location_bound` axiom-clean, FpLocation.lean sorry-free (hold_step_bound,
  conv_Gweight_exp, Gweight_shift, renewal-conv assembly). Both X8 Case-2 kernels
  unblocked.
- **lap 49 (2026-07-12)** `dbe1626`: `renewalMass_bound` PROVED (renewal Gaussian
  bound `U(j,l) ≤ C/√(1+l)·Gweight(1+l)(c(j−l/4))`).
- **lap 48 (2026-07-12)**: renewal-sum toolkit (`sum_range_exp_neg_sq_le` Gaussian
  AP engine, factorization chain) proved + numerically validated.
- **lap 47 (2026-07-12)** `14669cb`: X6 cracked open — first-passage renewal
  decomposition (`fpDist_le_renewal_conv`); NO barrier condition needed (monotone
  height kills it — plain renewal measure suffices).
- **lap 46 (2026-07-12)**: X8/X10 `Q_black_edge` decomposed (BlackEdge.lean);
  case-split glue + (7.46) endpoint step + (7.52) budget bound PROVED; 4 named
  sub-sorries replace the monolith.
- **lap 45 (2026-07-12)** `14669cb`←`d59e14a`: **S3 FULLY GREEN** — all 3 d=1 local
  bounds proved; all 8 Lemma 2.2 obligations machine-checked (judge pass 5).
- **laps 41–44 (2026-07-12)**: `hold_local_bound` + `hold_tail_bound` + d=1 circle
  method (CharFn1.lean) + 3 d=1 tail bounds; the 2-D MGF/tilting engine completed.
- **laps 36–40 (2026-07-12)**: tilted center bound + Cauchy–Schwarz MGF split +
  2-D quadratic MGF bound (K=1000) — the S3 analytic engine.
- **earlier**: X3 (Lemma 7.4 triangles, judge-verified), Q-recursion / Qstop /
  fpDist D6 machinery, PMF/Fourier/tilting support layers.

## Outstanding

### Short-term (mirror PENDING_WORK top)
- **Pin Lemma 7.10 (X10)** (7.60): `P(E_{p,s'}) ≤ C·A²(1+p)/s' + C·exp(-c·A²(1+p))`
  over the `fpDist∘iidSum` renewal endpoint. Route (7.60)–(7.65).
- **Design + pin Lemma 7.9 (X9)** (7.57): stopping-time expectation as a recursion
  on R over the renewal machinery (D6).
- X8 Case-2 kernels (`fpDist_edgeWeight_le`, `fpDist_white_exit`) — finish-when-
  downhill only; both now consume the proven `fpDist_location_bound`.

### Long-term
- X11 Case-3 assembly (7.53)–(7.67); X1 `key_fourier_decay` chain; X2 sharp white
  cancellation (White.lean); X5 Hold basics / Bridge ×3.
- C-spine: C8 (Prop 5.2 approx formula), C5/C7/C9/C10, Sec5/Sec6, Syracuse layer,
  Basic/Statement scaffolding.

### To completion
Assemble §7 crux → Prop 1.17 → Prop 1.14 → C10 → C9 → C6 → Thm 1.3; discharge all
24 `sorry`s; `#print axioms` on `Statement` headline = trust base only.

## Axiom ledger (fidelity spine)

The headline theorems are NOT yet assembled — the spine (§1–§6) is stubbed while
the §7 crux is built bottom-up, so the ledger tracks the COMPLETED crux nodes
(ground truth) plus the headline's stub status.

| headline / node | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Statement` Thm 1.3 / Thm 3.1 | Thm 1.3 (uncond.) | `sorry` (spine not assembled) | 🔜 stub — downstream of crux |
| S3 `hold_local_bound` / `hold_tail_bound` | Lemma 2.2(i)(ii) Hold | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| S3 `geomHalf/geomQuarter/pascal_*_bound` | Lemma 2.2 d=1 | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X3 `black_structure` | Lemma 7.4 | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| X6 `fpDist_location_bound` | Lemma 7.7 | `[propext, choice, Quot.sound]` | 🟢 done, clean |

Math-axiom count on every completed node = **0** (trust base only). No 🔴
(open-conjecture) axioms anywhere — correct, since Thm 1.3 is unconditional. No 🟡
project-scale cited axioms are in use: the crux is being PROVED, not cited. The
remaining work is `sorry`-discharge, not axiom-discharge.

## Pointers
DIRECTION.md (binding directive) · BLUEPRINT.md (frozen node ledger §2) ·
newest `HANDOFF-2026-07-12-d.md` · PENDING_WORK.md (attack paths) · paper
`papers/tao-2019-almost-all-orbits.pdf`.
