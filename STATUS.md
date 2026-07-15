# STATUS — tao-collatz 📊

**First-anywhere Lean 4 formalization of Tao 2019 "Almost all Collatz orbits
 attain almost bounded values" (Thm 1.3).** · **Build**: 🟢 green (3323 jobs) ·
**Updated**: review lap · 2026-07-15 · `fef0c38`

## Where it stands

**🏆 §7 (the campaign's 65–75% risk concentration), 🏆 C10 `fine_scale_mixing`
(Prop 1.14, the §6 crux), and 🏆 C7 `first_passage_nonescape` (Prop (1.19)) are all
CLOSED and axiom-clean** (`[propext, Classical.choice, Quot.sound]`). The pass-30
false-summit is REPAIRED: `approxMainTerm` was re-pinned RATIFY-C8-v2 (exact affine guard)
and the reindex `approxMainTerm_eq_steppedMid` is PROVED axiom-clean, so `steppedMid` — not
the truncating `Aff` — carries (5.8). **C8 = `first_passage_approx` (Prop 5.2 / (5.8)) now
rests on exactly ONE sorry** (kernel-checked this lap): the (5.17) **reverse** leg
`steppedMid_le_firstPassMid_add` (`Sec5/ApproxFormula.lean:2602`). Its two siblings are
closed — `passtime_window_inner` (5.16) proved, and the (5.17) **forward** leg
`firstPassMid_le_steppedMid` proved axiom-clean (a DETERMINISTIC `S_n ⊆ T_n` inclusion, no
error). All C8 error now lives in the reverse leg. Campaign order
`C10 ✅ → C8(pin ✅) → C7 ✅ → C8 close (1 hole) → C9 → C6 → headline` STANDS.
**Census = 4 sorries + 0 orange** (C8 reverse leg, C9 `stabilization`, 2 frozen headline stubs).

## What's happened (newest first)

- **review lap (2026-07-15, `fef0c38`)**: route CONTINUE, no trigger fired. Inventory
  kernel-verified: C8 `first_passage_approx` = trust base + ONE `sorryAx` (the 5.17 reverse
  leg); `passtime_window_inner` + the 5.17 forward leg both CLOSED since the pass-30 snapshot.
  Narrowed the directive to `steppedMid_le_firstPassMid_add` and recorded the CaseA(exact,
  disjoint)/CaseB(early-return) split — correcting the handoff's claim that
  `approx_passtime_window` alone bounds the reverse defect (it misses returns with `T_x N ∈ Iy`).
  Then decomposed the reverse leg in `src/` (see next commit). DIRECTION/STATUS refreshed.
- **grind laps C8 (5.17) (2026-07-15, `eabcb16`→`fef0c38`)**: closed the (5.17) FORWARD leg.
  `firstPassMid_le_steppedMid` proved axiom-clean via `stepback_passage_scale`/
  `stepback_size_window`/`expect_mono_on_support`; `eprime_forces_passTime` (the disjointness
  key) proved; helpers `good_nested`/`mZero_le_of_mem_Iy`/`slack_*`/`three_pow_nZero_le` banked.
  C8 reverse leg is the sole remaining C8 hole.
- **deep reflection (2026-07-15, `95436f9`)**: route **CONTINUE-with-correction**; **T5
  FIRED**. Re-verified C10 + C7 axiom-clean at `95436f9`. **Caught a false summit in the
  C8 close:** grind laps `d8a9d57`→`95436f9` built the `steppedMid`/`approxMainTerm`
  reindex (mechanical layer + orbit estimate, all axiom-clean) on a **defective pin** — the
  ℕ-truncating `Aff` drops Tao's (5.18) congruence, so `truncation_error_bound` is FALSE
  (source read pp.22–25 + `tao_c8_truncation_probe.py`). Mandated: RE-PIN `approxMainTerm`
  with the exact-affine guard (RATIFY-C8-v2), delete `truncation_error_bound`, re-wire onto
  the exact Lemma-2.1 reindex. Wrote lit-review §5 (was absent); DIRECTION/PENDING/STATUS
  refreshed; probe saved to `tools/sandbox/`.
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

## Outstanding

### Short-term (mirror PENDING_WORK top — review lap 2026-07-15)
- **`steppedMid_le_firstPassMid_add` (`ApproxFormula.lean:2602`)** — C8's LAST hole, the
  (5.17) reverse leg. Reverse defect `∑_{n∈Iy} E[𝟙_{T_n∖S_n}]` splits pointwise CaseA
  (`n−m₀ ≤ T_x N`) ⊎ CaseB (`n−m₀ > T_x N`). **Case A** collapses exactly to
  `E[𝟙_{¬good⁽ⁿ⁰⁾}] ≤ C log^{-c}` (`approx_good_tuple_whp`, PROVED) via `passTime_stepback`
  ⟹ `T_x N = n` (disjoint). **Case B** = the genuine early-return event → named sorry
  `reverse_early_return_whp` (a union-of-returns whp estimate; NOT covered by
  `approx_passtime_window` alone). Prove Case A + wiring now; isolate Case B honestly.
- Then **C9 `stabilization`** (`FirstPassage.lean:1399`, Prop 1.11, consumes C10 ✅ + C8),
  then **C6** (§3 reduction) → wire the 2 `Statement.lean` headlines.

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
(real `#print axioms` at `fef0c38`). The pass-30 `approxMainTerm` fidelity flag is CLEARED:
re-pinned RATIFY-C8-v2 (exact affine guard) and `approxMainTerm_eq_steppedMid` proved
axiom-clean, so C8's remaining debt is pure `sorry`-discharge (the reverse leg), not fidelity:

| headline / node | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Statement` Thm 1.3 / Thm 3.1 | Thm 1.3 (uncond.) | `sorry` (spine not assembled) | 🔜 stub — discharges when C8/C9/C6 land |
| C10 `fine_scale_mixing` (Prop 1.14) | §6 fine-scale mixing | `[propext, choice, Quot.sound]` | 🟢 **CLOSED, clean** (was the §6 crux); judge to flip `\leanok` |
| C7 `first_passage_nonescape` (1.19) | `P(T_x(N_y)=∞) ≪ x^{-c}` | `[propext, choice, Quot.sound]` | 🟢 **CLOSED, clean** (integral test + (5.5) done); judge to flip `\leanok` |
| C8 `first_passage_approx` (Prop 5.2 / (5.8)) | §5 approx formula | trust base + `sorryAx` (1 sub-sorry) | 🟡 **current target**: RATIFY-C8-v2 exact reindex PROVED; window (5.16) + forward leg (5.17) CLOSED. ONE hole = `steppedMid_le_firstPassMid_add` (5.17 reverse leg). Pin-fidelity flag CLEARED |
| C9 `stabilization` (Prop 1.11) | §5 first-passage stab. | trust base + `sorryAx` | 🟡 downstream of C10 + C8; after C8 |
| `charFn_decay` (Prop 1.17) / `key_fourier_decay` (Prop 7.1) | char/Fourier decay | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| `prop_7_8` / `Q_black_edge` / `Q_polynomial_decay` + X8–X11 kernels | Prop 7.8 + Lemmas 7.6–7.10 | `[propext, choice, Quot.sound]` | 🟢 **§7 CLOSED, clean** |
| S3/X1/X2/X3/X5/X6 + all SyracRV + C5 `valuation_dist` | Lemma 2.2, 7.2, 7.4, 1.9, 1.12 | `[propext, choice, Quot.sound]` | 🟢 done, clean |

Math-axiom count on every completed node = **0** (trust base only). No 🔴
(open-conjecture) axioms anywhere — correct, since Thm 1.3 is unconditional. No
🟡/🟠 *cited* axioms: the open nodes (C8, C9) are being PROVED, not cited.
Remaining work is pure `sorry`-discharge (C8 reverse leg + C9 + 2 headline) — the pass-30
`approxMainTerm` re-pin is DONE, so no fidelity debt remains.

## Pointers
DIRECTION.md (binding directive; **review-lap refresh 2026-07-15 `fef0c38` on top** —
objective narrowed to C8 reverse leg) · BLUEPRINT.md (frozen node ledger §2) · newest baton
`HANDOFF-2026-07-15-C8-5.17-forward-leg-closed.md` (HEAD `fef0c38`) · PENDING_WORK.md
(top: reverse-leg CaseA/CaseB attack plan) · papers/literature-review.md (source synthesis) ·
paper `papers/tao-2019-almost-all-orbits.pdf`.
