# STATUS — tao-collatz 📊

**First-anywhere Lean 4 formalization of Tao 2019 "Almost all Collatz orbits
 attain almost bounded values" (Thm 1.3).** · **Build**: 🟢 green (3285 jobs) ·
**Updated**: deep reflection lap · 2026-07-14 · `f96a728`

## Where it stands

**🏆 §7 (the campaign's stated 65–75% risk concentration) is CLOSED and
axiom-clean**; all of SyracRV, S3, X1–X11 done and clean. **The content spine
has EXACTLY TWO open heroic sorries** (+ 2 frozen headline stubs): C10
`fine_scale_mixing` (Prop 1.14, §6, `MixingFromDecay.lean:1459`) and C9
`stabilization` (Prop 1.11, §5, `FirstPassage.lean:81`, consumes C10). The crux
is **C10** on the critical path `C10 → C9 → C6 → Statement`. Seventeen C10
support bricks are banked axiom-clean (Plancherel chain, osc calculus, Lemma
6.2 + mod-3ⁿ wrapper, marginalization, head-factor reindex onto `charFn_decay`).
The 2026-07-14 deep reflection **refuted the recorded obligation-3 endgame**
(the "window ⟹ per-prefix" implication is false in-regime) and re-aimed it at
the suffix-form window kernel with the tight stopping-rule l-window — the
paper's own (6.8) display is too lossy (hole #3, JUDGE-FLAGged); margins now
verified numerically (0.4805 vs 0.693 per C_A²·log n, closes for C_A ≥ 10).
**4 real proof `sorry`s remain total** (2 headline + C10 + C9).

## What's happened (newest first)

- **deep reflection (2026-07-14, `f96a728`)**: route CONTINUE (no trigger
  fired; T3/T4 registered). **Caught a false summit**: fruit-23's "one
  remaining analytic implication" for obligation 3 is unprovable — the
  per-prefix hypothesis fails at `m=0` for `p ≈ 0.79n` (coeff 1.42 > 1.10).
  Re-aimed at `fnat_lt_of_suffix_window` (suffix form + TIGHT l-window; paper's
  (6.8) shown too lossy — source hole #3, documented in literature-review, judge
  to ratify). Added missing obligation 0 (the (6.1)/(1.22) regime telescope for
  `m < 0.9n`). Ledger re-run at `f96a728`: 4 `sorryAx` carriers exactly; all 18
  checked support nodes trust-base clean.- **review lap (2026-07-14)**: **§7 CROSSED** — inventory found only 4 live
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
- **earlier (laps 36–56, 2026-07-12)**: X9/X10/X11 pins + kernels (laps 51–56,
  incl. the lap-55 deep reflection's X9 near-edge finding and the 7.9
  exp(ε)→exp(2ε) correction); X1/X2/X5/X6 closed; S3 fully green (laps 36–45,
  2-D MGF/tilting + circle method); before that X3, Q-recursion/Qstop/fpDist
  D6 machinery, PMF/Fourier/tilting support layers.

## Outstanding

### Short-term (mirror PENDING_WORK top — Reflection 2026-07-14)
- **`fnat_lt_of_suffix_window`** (START HERE, route-decisive): the corrected
  obligation-3 kernel — tight l-window + suffix (6.12) bounds ⟹
  `fnat p vt < 3^(j+p)`; ε=1/4 Young, explicit `C_A ≥ 10`, `n ≥ n₀`. Spec in
  PENDING_WORK Reflection section. Do NOT attempt the refuted per-prefix form.
- Then: windowed-indicator generalization of `condDens`/`tailDens` (serves
  obligations 1+3) → windowed `tailDens ≤ 2^{-l}` (obl 3 CLOSED) → event
  scaffold + `P(Ē)` (obl 1) → `hunif` (obl 2) → regime telescope (obl 0).

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
re-run this deep-reflection lap (2026-07-14, real `#print axioms` at `f96a728`;
18 support nodes checked incl. all new C10 bricks — every completed node
trust-base only):

| headline / node | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Statement` Thm 1.3 / Thm 3.1 | Thm 1.3 (uncond.) | `sorry` (spine not assembled) | 🔜 stub — discharges when C10/C9/C6 land |
| C10 `fine_scale_mixing` (Prop 1.14) | §6 fine-scale mixing | trust base + `sorryAx` | 🟡 **current crux** — 17 bricks banked clean; obligations 0–3 scoped, obl-3 kernel re-aimed (suffix window, tight l-bound) by 07-14 reflection |
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
DIRECTION.md (binding directive; reflection course-correction 2026-07-14) ·
BLUEPRINT.md (frozen node ledger §2) · newest `HANDOFF-2026-07-15-1600.md` (reflection; real date 07-14) ·
PENDING_WORK.md (Reflection 2026-07-14 top: obl-3 spec + triggers) ·
papers/literature-review.md (source synthesis; Cor 6.3 hole #3) ·
paper `papers/tao-2019-almost-all-orbits.pdf`.
