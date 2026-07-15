# STATUS — tao-collatz 📊

**First-anywhere Lean 4 formalization of Tao 2019 "Almost all Collatz orbits
 attain almost bounded values" (Thm 1.3).** · **Build**: 🟢 green (3324 jobs) ·
**Updated**: review lap · 2026-07-15 · `5514f13`

## Where it stands

**🏆 §7 (the campaign's 65–75% risk concentration), 🏆 C10 `fine_scale_mixing`
(Prop 1.14, the §6 crux), 🏆 C7 `first_passage_nonescape` (Prop (1.19)), and 🏆 C8
`first_passage_approx` (Prop 5.2 / (5.8)) are all CLOSED and axiom-clean**
(`[propext, Classical.choice, Quot.sound]`, kernel-verified this lap). The live node is
**C9 `stabilization` (Prop 1.11)**. Its route-decisive leaf `perNTerm_eval` — the sole C10
consumer of the affine main term — is **PROVED** from two named sub-sorries, isolating all of
C10's C9-involvement to ONE hole: `harmonic_to_Z` (Tao (5.20), `Sec5/Stabilization.lean:348`).
Campaign order `C10 ✅ → C8 ✅ → C7 ✅ → C9 (live) → C6 → headline` STANDS.
**Census = 6 sorries + 0 orange** (4 C9 holes in `Stabilization.lean` — `harmonic_to_Z`,
`perNTerm_harmonic_approx`, `Iy_count_ratio`, `mainZ_bound` — plus the 2 frozen `Statement.lean`
headline stubs). Hardest-first this lap = `harmonic_to_Z`, the C10 seam.

## What's happened (newest first)

- **review lap (2026-07-15, `5514f13`)**: route CONTINUE, no trigger fired (T5 RESOLVED
  by the successful C8 re-pin). Kernel-verified: **C8 `first_passage_approx` now
  `[propext, choice, Quot.sound]`** (was 🟡 with 1 sorryAx last review) — C8 CLOSED. `perNTerm_eval`
  = trust base + sorryAx via its 2 sub-sorries only. Build green (3324), 6 sorries + 0 orange.
  Directive **retargeted from C8's (closed) reverse leg to C9's `harmonic_to_Z`** (the C10 seam,
  hardest-first) with a mandated B1 (geomHalf→syracZ reindex) / B2 (fine_scale_mixing scale bridge)
  decomposition. STATUS + DIRECTION refreshed.
- **grind laps C9 `perNTerm_eval` (2026-07-15, `3247d22`→`eeb96c6`→`5514f13`)**: the C10-consumer
  crux DECOMPOSED + PROVED from 2 sub-sorries, all bricks axiom-clean. `perNTerm_pointmass` (5.19
  affine reindex → single point mass); `logUnifOdd_apply_toReal` (point-mass value = `(N*)⁻¹/D_y`);
  `windowMass_estimate` (`|D_y − (α−1)/2·log y| ≤ 3`); `fnat_lt_pow_mul` (numerator bound). Defined
  `perNHarmonic` (5.20 LHS); split into `perNTerm_harmonic_approx` (A, 5.19) + `harmonic_to_Z`
  (B, 5.20 = C10 seam); proved the assembly triangle. C10 isolated to `harmonic_to_Z`.
- **grind laps C9 assembly (2026-07-15, `12d62f0`→`f327547`→`663ac1d`)**: C9 spine wired —
  `stabilization ← approxMainTerm_window_stable ← approxMainTerm_to_Z ← {perNTerm_eval, Iy_count_ratio,
  mainZ_bound}`. Ribs `dTV_passLoc_event_witness` (Hahn sign-split) + rib 2 proved axiom-clean;
  `stabilization` relocated to `Sec5/Stabilization.lean` (byte-identical statement; JUDGE-FLAG open).
- **grind laps C8 close (2026-07-15, `d0e3ac9`→`0bea9d1`)**: **C8 CLOSED axiom-clean.** The (5.17)
  reverse leg `steppedMid_le_firstPassMid_add` proved — the Case-B early-return event proved EMPTY
  (`earlyReturn_size_contra`), reducing the reverse defect to Case A = `E[𝟙_{¬good⁽ⁿ⁰⁾}]` bounded by
  PROVED `approx_good_tuple_whp`. `first_passage_approx` → `[propext, choice, Quot.sound]`.
- **review lap (2026-07-15, `fef0c38`)**: narrowed to C8's reverse leg; recorded the CaseA(exact,
  disjoint)/CaseB(early-return) split. (Superseded — C8 now closed.)
- **grind laps C8 (5.17) forward (2026-07-15, `eabcb16`→`fef0c38`)**: (5.17) FORWARD leg
  `firstPassMid_le_steppedMid` proved axiom-clean (deterministic `S_n ⊆ T_n` inclusion);
  `eprime_forces_passTime` disjointness key proved.
- **deep reflection (2026-07-15, `95436f9`)**: **T5 FIRED** — caught the C8 false summit (ℕ-truncating
  `Aff` drops Tao's (5.18) congruence). Mandated RATIFY-C8-v2 exact-affine re-pin. RESOLVED this lap.
- **review lap (2026-07-14, `810518b`)**: **C7 PROVED + axiom-clean** — `first_passage_nonescape` (1.19).
  Integral test + (5.5) done. Live target advanced to the C8-close leg.
- **grind laps C10-close + C8-pin (2026-07-14, `405f026`→`f42f0fb`)**: **C10 CLOSED** — `g3_mass_le`
  proved via the suffix marginal `iidMap_suffix`; `fine_scale_mixing` axiom-clean. C8 PINNED + ROUTED.
- **review lap (2026-07-14, `e0913ce`)**: verified pass-29 C10 + C8-pin done; reframed the C7 crux as
  the elementary integral test. DIRECTIVE re-aimed at the integral test first.
- **§7 close-out (2026-07-14)**: X11 `Q_black_edge_case3` + Case-3 sorries proved; `prop_7_8` →
  `Q_polynomial_decay` axiom-clean. §7 CROSSED — the 65–75% risk concentration cleared.

## Outstanding

### Short-term (mirror PENDING_WORK top — review lap 2026-07-15)
- **`harmonic_to_Z` (`Stabilization.lean:348`, Tao (5.20))** — C9's route-decisive hole, THE SOLE C10
  CONSUMER. `|perNHarmonic x E n − mainZ x E| ≤ C·log^{-c}`. Decompose into: **(B1)** geomHalf→syracZ
  reindex `∑_ā[good ∧ congr] 2^{−pre ā} = (syracZ(n−m₀))(M mod 3^{n−m₀}).toReal` up to `approx_good_tuple_whp`
  (via `syracZ_eq_rev_fnat`); **(B2)** scale bridge `3^{n−m₀}·syracZ(n−m₀)(M) ≈ 3^{m₀}·syracZ(m₀)(M mod 3^{m₀})`
  via `fine_scale_mixing`'s `osc` (Lemma 5.3, C10) + `syracZ_map_cast`, summed over `M∈E'` to `mainZ`.
- Then the 3 self-contained C9 leaves: **`perNTerm_harmonic_approx`** (5.19 analytic, no C10),
  **`Iy_count_ratio`** (5.9 lattice count), **`mainZ_bound`** (`|mainZ|≤C`). Then C9 axiom-clean.
- Then **C6** (§3 reduction, Thm 1.3⟸1.6⟸3.1⟸Prop 1.11) → wire the 2 `Statement.lean` headlines.

### Long-term
- Close C9 `stabilization` (Prop 1.11), then C6 → the two `Statement.lean` headlines.
- 🗂️ `ManyTriangles.lean` split (BLUEPRINT §2, 5k+ lines) — off critical path, opportunistic only.

### To completion
Close C9 `harmonic_to_Z` + 3 leaves → C6 → wire the two `Statement.lean` headlines;
`#print axioms tao_collatz` = trust base only.

## Axiom ledger (fidelity spine)

The two headline theorems are NOT yet assembled — the §1–§6 spine feeds into `Statement` only after
C9/C6 land. §7, C10, C7, **and C8** are closed and clean. Ledger re-run this review lap (real
`#print axioms` at `5514f13`).

| headline / node | paper claim | `#print axioms` shows | status |
|---|---|---|---|
| `Statement` Thm 1.3 / Thm 3.1 | Thm 1.3 (uncond.) | `sorry` (spine not assembled) | 🔜 stub — discharges when C9/C6 land |
| C10 `fine_scale_mixing` (Prop 1.14) | §6 fine-scale mixing | `[propext, choice, Quot.sound]` | 🟢 **CLOSED, clean** (§6 crux); judge to flip `\leanok` |
| C7 `first_passage_nonescape` (1.19) | `P(T_x(N_y)=∞) ≪ x^{-c}` | `[propext, choice, Quot.sound]` | 🟢 **CLOSED, clean**; judge to flip `\leanok` |
| C8 `first_passage_approx` (Prop 5.2 / (5.8)) | §5 approx formula | `[propext, choice, Quot.sound]` | 🟢 **CLOSED, clean** (this lap) — RATIFY-C8-v2 exact reindex + all 3 (5.16)/(5.17) legs proved; judge to flip `\leanok` |
| C9 `stabilization` (Prop 1.11) | §5 first-passage stab. | trust base + `sorryAx` | 🟡 **live target**: 4 holes; route-decisive = `harmonic_to_Z` (C10 seam, 5.20). `perNTerm_eval` (sole C10 consumer of the affine main term) PROVED from 2 sub-sorries |
| `charFn_decay` (Prop 1.17) / `key_fourier_decay` (Prop 7.1) | char/Fourier decay | `[propext, choice, Quot.sound]` | 🟢 done, clean |
| `prop_7_8` / `Q_black_edge` / `Q_polynomial_decay` + X8–X11 kernels | Prop 7.8 + Lemmas 7.6–7.10 | `[propext, choice, Quot.sound]` | 🟢 **§7 CLOSED, clean** |
| S3/X1/X2/X3/X5/X6 + all SyracRV + C5 `valuation_dist` | Lemma 2.2, 7.2, 7.4, 1.9, 1.12 | `[propext, choice, Quot.sound]` | 🟢 done, clean |

Math-axiom count on every completed node = **0** (trust base only). No 🔴 (open-conjecture) axioms
anywhere — correct, since Thm 1.3 is unconditional. No 🟡/🟠 *cited* axioms: the only open node (C9,
plus the 2 headline stubs) is being PROVED, not cited. Remaining work is pure `sorry`-discharge
(C9's 4 holes + 2 headline). No fidelity debt: C8's pass-30 `approxMainTerm` re-pin is DONE and CLOSED.

## Pointers
DIRECTION.md (binding directive; **review-lap refresh 2026-07-15 `5514f13` on top** — objective =
C9 `harmonic_to_Z`, the C10 seam) · BLUEPRINT.md (frozen node ledger §2) · newest baton
`HANDOFF-2026-07-15-C9-perNTerm-eval-proved.md` (HEAD `5514f13`) · PENDING_WORK.md (top: C9
`harmonic_to_Z` seam / B1+B2 decomposition) · papers/literature-review.md (source synthesis) ·
paper `papers/tao-2019-almost-all-orbits.pdf`.
