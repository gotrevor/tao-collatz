# STATUS — tao-collatz 📊

**First-anywhere Lean 4 formalization of Tao 2019 "Almost all Collatz orbits
 attain almost bounded values" (Thm 1.3).** · **Build**: 🟢 green (3293 jobs) ·
**Updated**: review lap · 2026-07-14 · `e0913ce`

## Where it stands

**🏆 §7 (the campaign's 65–75% risk concentration) and 🏆 C10 `fine_scale_mixing`
(Prop 1.14, the §6 crux) are both CLOSED and axiom-clean** — re-verified this lap
(`fine_scale_mixing`, `error_l1_high_bound`, `prob_not_globalGood_le` all
`[propext, Classical.choice, Quot.sound]` at `e0913ce`). The campaign order is
**C10 → C8(pin) → C7(prove) → C8(close) → C9**; C10 is done and **C8 is pinned +
routed** (`first_passage_approx`, RATIFY-C8). The **live target is C7 =
`first_passage_nonescape`** (Prop (1.19), `Sec5/FirstPassage.lean`), down to
**2 sub-sorries**: the crux `integral_test_logUnif` and the downstream-mechanical
`valSum_lower_tail`. **Key review finding**: the C7 crux is the *elementary integral
test* (AP-count + sum↔integral comparison), for which mathlib already has the
machinery — NOT the from-scratch dynamical equidistribution the last handoff feared.
**6 working sorries** (2×C7, 3×C8, 1×C9) + 2 frozen headline stubs.

## What's happened (newest first)

- **review lap (2026-07-14, `e0913ce`)**: route CONTINUE, no trigger fired.
  Verified pass-29 obj 1 (C10) + obj 2 (C8 pin) DONE — C10 chain re-run
  axiom-clean. Frontier = C7's 2 sub-sorries. **Reframed the C7 crux**:
  `integral_test_logUnif` is the elementary integral test (`SumIntegralComparisons`
  + `CardIntervalMod` + `integral_inv` all in mathlib), not a missing
  equidistribution theorem. DIRECTIVE re-aimed at attacking the integral test FIRST
  (hardest-first), not the downstream mechanical `valSum_lower_tail`. STATUS +
  PENDING refreshed; attack plan in PENDING top.
- **grind laps C7 (2026-07-14, `65d8cce`→`e0913ce`)**: C7 decomposed +
  assembled. `first_passage_nonescape` proved MODULO the integral test — the
  descent leaves are axiom-clean: `syr_descent_bound` (the ℕ descent core,
  `Basic/Valuation.lean`), `descent_passes`, `descent_pow_bounds` (`log3/log2 ≤
  8/5` via `3^5=243≤256=2^8`), plus reusable helpers `logUnifOdd_support_le`,
  `rpow_le_eps_mul_of_lt_one`. C7 down to 2 sorries.
- **grind laps C10-close + C8-pin (2026-07-14, `405f026`→`f42f0fb`)**: C10
  CLOSED — `g3_mass_le` (suffix-window deficit) proved via the suffix marginal
  `iidMap_suffix`; `MixingError.lean` sorry-free; `fine_scale_mixing` axiom-clean.
  C8 PINNED + ROUTED: new `Sec5/ApproxFormula.lean` (`first_passage_approx` =
  (5.8), defs `nZero`/`mZero`/`goodTuple`/`Iy`/`Eprime`/`approxMainTerm`; 2 named
  sub-sorries). C8's proof consumes C7 at exactly one place (`approx_passtime_window`).
- **grind laps C10 tail (2026-07-14/15)**: `globalGood ⊆ mainEvent` proved
  (the inclusion IS the node's content), (6.3) union bound + marginal law in;
  the C10 error node reduced to `prob_not_globalGood_le` then closed.
- **review lap (2026-07-15, `4eabb35`)** [pre-C10-close]: obl-3 analytic content
  (`fnat_lt_of_suffix_window`, `tailDensW_le_single_mass`, injectivity) verified
  DONE + axiom-clean; frontier advanced to the §6 assembly (since completed).
- **deep reflection (2026-07-14, `f96a728`)**: caught a false summit in the obl-3
  attack line (per-prefix hypothesis false at `m=0`); re-aimed at the suffix-form
  window kernel with the TIGHT l-window (paper's (6.8) shown too lossy — source
  hole #3); added the missing regime-telescope obligation 0.
- **review lap (2026-07-14, earlier)**: §7 CROSSED — `prop_7_8` + full §7 chain
  (Q_black_edge, Q_polynomial_decay, charFn_decay, key_fourier_decay) all
  trust-base clean. New frontier = C10 via the conditioning route.
- **§7 close-out (2026-07-14)**: X11 `Q_black_edge_case3` + the two Case-3 sorries
  proved; X10 `_rpow` split landed; `prop_7_8` → `Q_polynomial_decay` axiom-clean.
- **lap fruit-6/7/8 (2026-07-14/15)**: all of SyracRV closed (`syracZ_recursion`);
  Parseval on `ZMod N` (node S4); C10 Cauchy–Schwarz/Parseval bridge
  `osc_le_sqrt_highfreq` proved; raw-density route REFUTED → conditioning route.
- **earlier (laps 36–59, 2026-07-12/13)**: X8/X9/X10/X11 pins + kernels (Lemma
  7.4 separation at `epsBW=10⁻¹⁰⁰⁰`, localization box, MGF/renewal harness);
  X1/X2/X3/X5/X6 closed; S3 fully green (2-D MGF/tilting + circle method).

## Outstanding

### Short-term (mirror PENDING_WORK top — review lap 2026-07-14)
- **C7 crux `integral_test_logUnif` (`FirstPassage.lean:104`)** — START HERE.
  The elementary integral test `dTV(N_y mod 2^{n'}, unifOddMod) ≤ K·2^{-n'}`.
  Decompose into: `intTest_numeric` (`2^{6n₀} ≤ x^{1.001}`, cheap, prove first) +
  `intTest_class_dev` (the analytic heart: sum↔integral per odd residue class) +
  `intTest_D_lower` + the dTV assembly. Full plan: PENDING top.
- **THEN `valSum_lower_tail` (`:118`)** — downstream of the crux + mechanical
  (clone `valuation_tail`'s upper-tail via two-sided `geomHalf_tail_bound`).

### Long-term
- Close C8 (feed C7 into `approx_passtime_window`; then `approx_good_tuple_whp` +
  `first_passage_approx` assembly), then C9 `stabilization` (Prop 1.11, consumes
  C10 + C8), then C6 → the two `Statement.lean` headlines.
- 🗂️ `ManyTriangles.lean` split (BLUEPRINT §2, 5k+ lines) — off critical path,
  opportunistic only.

### To completion
Close C7 → C8 → C9 `stabilization` → C6 → wire the two `Statement.lean` headlines;
`#print axioms tao_collatz` = trust base only.

## Axiom ledger (fidelity spine)

The two headline theorems are NOT yet assembled — the §1–§6 spine feeds into
`Statement` only after C7/C8/C9/C6 land. §7 and C10 (the two crux concentrations)
are closed and clean. Ledger re-run this review lap (real `#print axioms` at
`e0913ce`):

| headline / node | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Statement` Thm 1.3 / Thm 3.1 | Thm 1.3 (uncond.) | `sorry` (spine not assembled) | 🔜 stub — discharges when C7/C8/C9/C6 land |
| C10 `fine_scale_mixing` (Prop 1.14) | §6 fine-scale mixing | `[propext, choice, Quot.sound]` | 🟢 **CLOSED, clean** (was the §6 crux); judge to flip `\leanok` |
| C8 `first_passage_approx` (Prop 5.2 / (5.8)) | §5 approx formula | trust base + `sorryAx` (3 sub-sorries) | 🟡 PINNED + routed; proof consumes C7 at one place |
| C7 `first_passage_nonescape` (1.19) | `P(T_x(N_y)=∞) ≪ x^{-c}` | trust base + `sorryAx` (2 sub-sorries) | 🟡 **current target**; descent DONE, crux = the integral test |
| C9 `stabilization` (Prop 1.11) | §5 first-passage stab. | trust base + `sorryAx` | 🟡 downstream of C10 + C8; narrow only |
| `charFn_decay` (Prop 1.17) / `key_fourier_decay` (Prop 7.1) | char/Fourier decay | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| `prop_7_8` / `Q_black_edge` / `Q_polynomial_decay` + X8–X11 kernels | Prop 7.8 + Lemmas 7.6–7.10 | `[propext, choice, Quot.sound]` | 🟢 **§7 CLOSED, clean** |
| S3/X1/X2/X3/X5/X6 + all SyracRV + C5 `valuation_dist` | Lemma 2.2, 7.2, 7.4, 1.9, 1.12 | `[propext, choice, Quot.sound]` | 🟢 done, clean |

Math-axiom count on every completed node = **0** (trust base only). No 🔴
(open-conjecture) axioms anywhere — correct, since Thm 1.3 is unconditional. No
🟡/🟠 *cited* axioms: the open nodes (C7, C8, C9) are being PROVED, not cited.
Remaining work is `sorry`-discharge (C7 crux + C8 + C9 + 2 headline), not
axiom-discharge.

## Pointers
DIRECTION.md (binding directive; review-lap update 2026-07-14 on top) ·
BLUEPRINT.md (frozen node ledger §2) · newest baton `HANDOFF-2026-07-14-2117.md` (HEAD `061cc65`) ·
PENDING_WORK.md (review-lap 2026-07-14 top: C7 integral test attack plan) ·
papers/literature-review.md (source synthesis) ·
paper `papers/tao-2019-almost-all-orbits.pdf`.
