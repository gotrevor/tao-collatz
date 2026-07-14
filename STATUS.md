# STATUS — tao-collatz 📊

**First-anywhere Lean 4 formalization of Tao 2019 "Almost all Collatz orbits
 attain almost bounded values" (Thm 1.3).** · **Build**: 🟢 green (3322 jobs) ·
**Updated**: review lap · 2026-07-14 · `810518b`

## Where it stands

**🏆 §7 (the campaign's 65–75% risk concentration), 🏆 C10 `fine_scale_mixing`
(Prop 1.14, the §6 crux), and 🏆 C7 `first_passage_nonescape` (Prop (1.19)) are all
CLOSED and axiom-clean** — re-verified this lap (`fine_scale_mixing` and
`first_passage_nonescape` both `[propext, Classical.choice, Quot.sound]` at
`810518b`). The campaign order is **C10 → C8(pin) → C7(prove) → C8(close) → C9**;
objectives 1–3 (C10, C8-pin, C7-prove) are all DONE. The **live target is now the
C8-close leg = `first_passage_approx`** (Prop 5.2 / (5.8), `Sec5/ApproxFormula.lean`),
down to **3 named sub-sorries**: the assembly `first_passage_approx` (:97, the
(5.8) Lemma-2.1 affine reindexing — the route-decisive piece), `approx_good_tuple_whp`
(:116, (5.12) good-tuple union bound, **does not use C7**), and
`approx_passtime_window` (:132, (5.16), **the C7 consumer** — its `{¬passes}` term is
now the proved `first_passage_nonescape`). **4 working sorries** (3×C8, 1×C9) + 2
frozen headline stubs.

## What's happened (newest first)

- **review lap (2026-07-14, `810518b`)**: route CONTINUE, no trigger fired. **C7
  PROVED + axiom-clean** — `first_passage_nonescape` (1.19) = `[propext, choice,
  Quot.sound]` (re-verified). Grind laps since `e0913ce` closed the integral test
  (`intTest_class_dev` via the AP-reindexing bridge `classMass_ap_form`; `intTest_D_lower`
  window normalizer ≥ 1/8; `window_arith`) AND `valSum_lower_tail` (5.5). Live target
  advances to the **C8-close** leg. DIRECTION retargeted; hardest-first = the C8
  assembly's affine reindexing. STATUS + PENDING refreshed.
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
- **C8 assembly `first_passage_approx` (`ApproxFormula.lean:97`)** — START HERE
  (hardest-first). The (5.8) equality: collapse `ℙ(Pass_x(N_y) ∈ E)` to
  `approxMainTerm` via the Lemma-2.1 affine (`Aff`) pushforward reindexing + the
  `B_{n,y}` event-algebra chain. This is the only piece that can falsify the pinned
  `approxMainTerm` def, so probe it first. Decompose into named sub-sorries.
- **`approx_passtime_window` (`:132`)** — (5.16), the C7 consumer. First term
  `{¬passes}` = `first_passage_nonescape` (PROVED); second term `{passes ∧ T_x∉I_y}`
  is the integral-test window calc (reuse C7's `classMass`/`windowMass` machinery).
- **`approx_good_tuple_whp` (`:116`)** — (5.12) union bound over `n₀+1` prefixes from
  C5 (`valuation_dist`) + S3 (`geomHalf_tail_bound`, two-sided). Does NOT use C7.

### Long-term
- Close C8 (assembly + the two whp sub-lemmas), then C9 `stabilization` (Prop 1.11,
  `FirstPassage.lean:1351`, consumes C10 + C8), then C6 → the two `Statement.lean`
  headlines.
- 🗂️ `ManyTriangles.lean` split (BLUEPRINT §2, 5k+ lines) — off critical path,
  opportunistic only.

### To completion
Close C7 → C8 → C9 `stabilization` → C6 → wire the two `Statement.lean` headlines;
`#print axioms tao_collatz` = trust base only.

## Axiom ledger (fidelity spine)

The two headline theorems are NOT yet assembled — the §1–§6 spine feeds into
`Statement` only after C8/C9/C6 land. §7, C10, and C7 (the crux concentrations plus
the first-passage non-escape) are closed and clean. Ledger re-run this review lap
(real `#print axioms` at `810518b`):

| headline / node | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Statement` Thm 1.3 / Thm 3.1 | Thm 1.3 (uncond.) | `sorry` (spine not assembled) | 🔜 stub — discharges when C8/C9/C6 land |
| C10 `fine_scale_mixing` (Prop 1.14) | §6 fine-scale mixing | `[propext, choice, Quot.sound]` | 🟢 **CLOSED, clean** (was the §6 crux); judge to flip `\leanok` |
| C7 `first_passage_nonescape` (1.19) | `P(T_x(N_y)=∞) ≪ x^{-c}` | `[propext, choice, Quot.sound]` | 🟢 **CLOSED, clean** (integral test + (5.5) done); judge to flip `\leanok` |
| C8 `first_passage_approx` (Prop 5.2 / (5.8)) | §5 approx formula | trust base + `sorryAx` (3 sub-sorries) | 🟡 **current target**; C7 now available for the (5.16) consumer |
| C9 `stabilization` (Prop 1.11) | §5 first-passage stab. | trust base + `sorryAx` | 🟡 downstream of C10 + C8; after C8 |
| `charFn_decay` (Prop 1.17) / `key_fourier_decay` (Prop 7.1) | char/Fourier decay | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| `prop_7_8` / `Q_black_edge` / `Q_polynomial_decay` + X8–X11 kernels | Prop 7.8 + Lemmas 7.6–7.10 | `[propext, choice, Quot.sound]` | 🟢 **§7 CLOSED, clean** |
| S3/X1/X2/X3/X5/X6 + all SyracRV + C5 `valuation_dist` | Lemma 2.2, 7.2, 7.4, 1.9, 1.12 | `[propext, choice, Quot.sound]` | 🟢 done, clean |

Math-axiom count on every completed node = **0** (trust base only). No 🔴
(open-conjecture) axioms anywhere — correct, since Thm 1.3 is unconditional. No
🟡/🟠 *cited* axioms: the open nodes (C8, C9) are being PROVED, not cited.
Remaining work is `sorry`-discharge (C8 + C9 + 2 headline), not axiom-discharge.

## Pointers
DIRECTION.md (binding directive; review-lap update 2026-07-14 `810518b` on top) ·
BLUEPRINT.md (frozen node ledger §2) · newest baton `HANDOFF-2026-07-15-C7-complete.md` (HEAD `3e4d94e`) ·
PENDING_WORK.md (review-lap 2026-07-14 top: C8 close attack plan) ·
papers/literature-review.md (source synthesis) ·
paper `papers/tao-2019-almost-all-orbits.pdf`.
