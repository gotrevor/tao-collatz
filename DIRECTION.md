# DIRECTION — tao-collatz 🧭

*The **JUDGE** and altitude laps (review/reflection) are the only writers of the
CURRENT DIRECTIVE section; the judge outranks a review lap. Grind laps READ and
OBEY it; **it OUTRANKS the HANDOFF**. Keep it short — detail lives in
PENDING_WORK.md and the judge pass records (`judge/pass-NN.md`).*

---

## CURRENT DIRECTIVE (JUDGE PASS 30 + review 2026-07-15) — **C8 ✅; close C9 (`harmonic_to_Z` = C10 seam) → C6 → headline**

*Written after a full independent audit — paper vs blueprint vs Lean — by 5 parallel auditors + a
judge verbatim re-read of §5 (5.8)/(5.18)/(5.19) against PDF pp.22–25. Supersedes the pass-29
directive below, whose order is FULFILLED through C7. Every hard rail in the superseded blocks still
binds unless restated here. `blueprint_rules.md` is BINDING: one node, one claim; a green border
means the STATEMENT exists, never "finished"; never set a `\leanok` yourself. Report work as
**"N sorries + M orange."***

> ### 🔄 REVIEW-LAP REFRESH (2026-07-15, post-`5514f13`) — **C8 CLOSED; objective now C9's C10 seam**
> **State advanced past the pass-30 / prior-refresh snapshot:** **C8 (`first_passage_approx`, Prop 5.2)
> is CLOSED and axiom-clean** — the (5.17) reverse leg (early-return event proved EMPTY) landed at
> `0bea9d1`. C9's route-decisive leaf `perNTerm_eval` (the sole C10 consumer of the affine main term) is
> now **PROVED** from two named sub-sorries, isolating all of C10's C9-involvement to ONE hole. Census =
> **6 sorries + 0 orange** — 4 C9 holes in `Sec5/Stabilization.lean` + the 2 frozen `Statement.lean`
> headlines. Campaign order `C10 ✅ → C8 ✅ → C7 ✅ → C9 (live) → C6 → headline` STANDS.
> - **THE single objective: close `harmonic_to_Z` (`Stabilization.lean:348`, Tao (5.20)) — THE SOLE C10
>   CONSUMER, hence hardest-first.** `|perNHarmonic x E n − mainZ x E| ≤ C·log^{-c}`. Every other C9 hole
>   (`perNTerm_harmonic_approx` = pure (5.19) analytic; `Iy_count_ratio` = (5.9) lattice count; `mainZ_bound`)
>   is self-contained and route-safe — do those AFTER, not before.
> - **Mandated move:** decompose `harmonic_to_Z` into named sub-sorries in `src/` (raising the count is
>   PROGRESS). The seam has two genuine pieces: **(B1) the geomHalf→syracZ reindex** — rewrite the ā-sum
>   `∑_ā[good ∧ congr(ā,M)] 2^{−pre ā} = (syracZ(n−m₀))(M mod 3^{n−m₀}).toReal` up to the good-tuple whp
>   error, via `syracZ_eq_rev_fnat` (the map `a ↦ fnat·2^{−pre a} mod 3^{n−m₀}`) + `approx_good_tuple_whp`
>   (PROVED); and **(B2) the scale bridge** — `3^{n−m₀}·syracZ(n−m₀)(M) ≈ 3^{m₀}·syracZ(m₀)(M mod 3^{m₀})`
>   via `fine_scale_mixing`'s `osc` (Lemma 5.3, C10) + `syracZ_map_cast`, summed over `M∈E'` with 1/M weight
>   to `mainZ`. Pin B1/B2 as separate sorries; prove the assembly triangle from them.
> - **Forbidden drift:** do NOT retreat to `perNTerm_harmonic_approx`/`Iy_count_ratio`/`mainZ_bound`/C6 while
>   `harmonic_to_Z` is un-decomposed — those are the tractable leaves, and closing them first is exactly the
>   crux-neglect the charter warns against. Do NOT touch a ratified pin or frozen constant. Do NOT edit the
>   `harmonic_to_Z`/`perNHarmonic`/`mainZ` statements (internal decompositions below the `stabilization` pin,
>   judge-cross-read pending).
> - **Why:** `harmonic_to_Z` is the one place C10's mixing must actually compose with §5's harmonic sum at
>   scale m₀ — the last genuine unknown-unknown in C9. Settling whether the geomHalf-mass identity + osc
>   bridge go through *in Lean* is worth more than the three known-doable leaves combined. Once it lands, C9
>   is pure analytic/combinatorial clean-up → C6 (§3 reduction) → headline.

### State (kernel-verified this pass; `blueprint_audit.py` → 15 proved, 0 orange, 0 drift, 0 false-green)
- **15 nodes proved + axiom-clean**: all of §7 (X2–X11), **C10** (Prop 1.14), C5, C2, S3, C4, **C7** (just flipped).
- **C8 (Prop 5.2) RATIFIED v2** (statement faithful; exact reindex `approxMainTerm_eq_steppedMid` PROVED
  axiom-clean) — **2 proof holes left**: `first_passage_stepback_reduce` (5.17) + `passtime_window_inner` (5.16).
- **C9 `stabilization`** pinned (1 sorry), consumes C8 + C10 (both available). Judge-verified faithful to Prop 1.11.
- **C6** = the §3 reduction (Thm 1.3⟸1.6⟸3.1⟸Prop 1.11) — currently ONLY the two `Statement.lean` headline
  stubs; the intermediates are NOT pinned (see the C6 forward item).
- **Census ≈ 5 sorries + 0 orange** (C8×2, C9×1, 2 headline stubs). Report "N sorries + 0 orange," never N alone.

### Ratifications this pass (JUDGE — do not re-litigate)
- ✅ **C7 `first_passage_nonescape` FLIPPED** — kernel-clean, faithful to (1.19); the pass-29 missed flip is cleared. WATCHED.
- ✅ **C8 `first_passage_approx` STATEMENT RATIFIED (RATIFY-C8-v2)** — read VERBATIM vs Prop 5.2
  (5.8)/(5.9)/(5.10)/(5.11)/(5.18)/(5.19), PDF pp.22–25. The exact affine guard `3^{n−m₀}N + fnat = M·2^{|ā|}`
  IS Tao's (5.18)/(5.19) reindex; the v1 truncating-`Aff` defect is genuinely repaired (probe 19135→0–3).
  Statement `\leanok` set (green border); PROOF still owed. WATCHED.

### 🎯 THE PLAN — front-load discovery, THEN burn down (de-risk breadth-first; NOT linear)

*Cross-checked against an independent Fable strategy review (2026-07-14) and adopted. Why not linear
C8→C9→C6: C8's statement is pinned + FROZEN, so C9's assembly and C6's intermediates consume C8's
**statement**, not its proof — they are safe to work NOW, before C8's proof holes close. Sequencing all
C9/C6 learning behind C8's grind would surface the last nodes' surprises with the fewest laps left. So
spend the first 1–2 laps flushing the seams, then grind. This is the charter's own de-risk-breadth-first
rule (pin the scary node, learn what it needs, before polishing the cheap one).*

**Overnight lap order:**
1. **C9 assembly-spine PROBE — do this FIRST; it is the single highest de-risk move.** In
   `Sec5/FirstPassage.lean` / `Stabilization.lean`, state Lemma 5.3 (`c_n(X) ≪ 1`) and (5.18)–(5.21) as
   **sorried local lemmas**, and make the Prop 1.11 (`stabilization`) assembly **compile** using
   `first_passage_approx` (C8) and `fine_scale_mixing` (C10) as **black boxes** (both statements exist —
   cite the sorried theorems). This is a **SEAM TEST, ~1–2 laps, NOT a proof.** It answers the campaign's
   biggest unknown-unknown: *do C8's formula and C10's mixing actually compose at scale m₀?* If the
   assembly compiles, C9 reduces to filling known ribs. ⚠️ **If the C8/C10 interfaces do NOT fit
   (quantifier order, uniformity in n, normalization) → `JUDGE-FLAG:` and report the exact mismatch. Do
   NOT edit the ratified C8/C10 pins to force a fit.** Decomposing *below* `stabilization` is allowed; the pin is WATCHED.
2. **PIN the C6 reduction intermediates** (cheap, statement-only; the only remaining un-pinned structural
   surface, and it sits at the worst seam — the headline). Write, copy-not-compose vs §3: **Thm 1.6** (over
   the currently-dead-but-correct `AlmostAllOdd`), the **Thm 3.1-Syracuse** form, and the **(1.2)
   log-density reduction** lemmas — each a sorried statement — then a sorried headline-from-intermediates
   spine wiring them to `tao_collatz`. **PIN ONLY — do NOT `\leanok` them** (the judge ratifies vs §3 next
   pass; ratify ⟹ watch). §3 is "elementary but fiddly" (log-density conversion, the Thm 1.6⟹1.3 bridge,
   dyadic iteration); pinning now flushes any interface surprise while laps are plentiful, and stops an
   eventual C6 proof from routing around faithful intermediates (the "lie that compiles," in its most dangerous seat).
3. **CLOSE C8 hole (5.17) `first_passage_stepback_reduce` — HARDEST-FIRST.** `|firstPassMid − steppedMid| ≤
   O(log^{−c}x)`: needs the reverse inclusion + the **E′ size window** from the proved orbit estimate
   `Syr^{n−m₀}N = exp(O(log^{0.6}x))·(3/4)^{n−m₀}N` (`syr_iterate_good_bracket'`, `two_rpow_slack_le_exp`).
   The interval algebra `n∈I_y ⟹ window` is faithful to pp.23–24 (5.13)–(5.16); the `y^{α−1}` factor that
   once looked "too wide" is the log-uniform NORMALIZER (paper p.25, judge-verbatim-checked) — do NOT
   re-open that worry. **STALL-SWITCH: on any lap that makes NO measurable (5.17) progress, bank (5.16)
   that lap instead of spinning** — (5.16) is bankable machinery whose value does not decay; (5.17)'s value
   is route-information, which does. ⚠️ If closing (5.17) seems to need touching a ratified statement or a
   frozen constant → `JUDGE-FLAG:`, do not improvise near a goalpost.
4. **Close C8 hole (5.16) `passtime_window_inner`** — the (5.16) window term via the integral test over
   C7's PROVED `classMass`/`windowMass`/`intTest_*`. (The box has banked much of this already; finish it.)
5. **Fill C9 ribs** — Lemma 5.3, then (5.18)–(5.21); the assembly is already proved if step 1 succeeded.
6. **Prove C6** from the pinned intermediates (dyadic scale iteration + log-density splitting).

**⚡ Judge cadence — EVENT triggers on top of every-9 reflect / every-3 review (which stays as the fallback
heartbeat).** STOP and `JUDGE-FLAG:` for a ratification/judge pass on: (a) **any new pinned statement** (C6
intermediates, C9 locals) — ratify-on-pin, and do NOT build heavily on an unratified pin; (b) **the lap C8's
last hole closes**, before C9 switches from *citing* C8's statement to *using* its theorem; (c) any
**goalpost-pressure** from (5.17)'s E′ window or the C9 seam.

📈 **Steps 1–2 RAISE the sorry census (sorried spines + intermediates) — that is PROGRESS, not regression.**
It converts invisible structural risk into visible, attackable holes; the self-stop gate simply stays blocked
until they close. Do not read the bump as a stall.

### 🚨 DOC-HAZARD RAIL (new — read before touching `ApproxFormula.lean`)
The (5.18)/(5.19) reindex is **EXACT and PROVED** (`approxMainTerm_eq_steppedMid`, axiom-clean). A stale v1 code
comment at **`ApproxFormula.lean:247–251`** still says *"the reindex is APPROXIMATE, not exact … Do NOT attempt an
exact `=` reindex"* — that is **dead v1 residue, now provably FALSE**. **FIX IT EARLY: delete/correct that comment in
a lap — it is a comment, NOT a ratified statement, so correcting it is safe and cheap, and an unattended worker reads
the file, not this directive.** Until it's gone, do NOT let it steer you back onto the truncating route. Likewise the `Aff` docstring (`Basic/Valuation.lean:152`)
says "guarded by the divisibility" while the body floors — correct the prose (or split an exact guarded def) if you
touch Valuation. Every remaining `Aff` use is separately divisibility-guarded, so the floor is harmless — but the docstring lies.

### 🔒 Inherited hard rails (STILL BIND)
- **Rail 6 — never EDIT a ratified pin's statement** (not to weaken, strengthen, or generalize). The ratified set now
  adds **`first_passage_approx` (C8)** + **`first_passage_nonescape` (C7)** to the §7 set + `fine_scale_mixing`/
  `stabilization` + the two `Statement.lean` headlines. Decompose BELOW a pin freely; move a goalpost never → `JUDGE-FLAG:`.
- **WATCHED (`tao_stmt_diff.py`):** the full ratified set + both open cruxes. A watched-statement drift is the #1 silent failure.
- **Constants FROZEN (judge rulings, backed by proved lemmas):** `epsBW = 1/10^1000`, `caConst = 30` (`C_A ≥ 23`
  budget floor met). Do NOT re-derive. Any change re-arms the ε-sweep re-ratification list → `JUDGE-FLAG:`, do not adjust.
- **The two `Statement.lean` headline sorries are frozen** (rail 2) — they discharge only when C6 lands.
- **A pin is not done until a numeric trap checks it** (`check_blueprint.py`); C8's trap is added this pass.
- **A partition claim owes a proved disjointness lemma** (pass-29) — zero sorries is not zero holes.

### 🚧 Forbidden drift
- Do NOT retreat off C8 to C9/C6 while C8's 2 holes are open. Finish C8.
- Do NOT re-seed the v1 truncating-`Aff` route (doc-hazard rail).
- Do NOT touch any WATCHED/ratified statement or re-derive a frozen constant.
- A failure to close a hole is **INFORMATION**, not pressure to adjust a statement or constant → `JUDGE-FLAG:`.

### Follow-ups (NON-BLOCKING — do NOT spend a crux lap on these)
- Scrub stale "OPEN/sorry/owed" docstrings on PROVED nodes: `BlackEdgeQ.lean:115`, `Case3.lean:2922`,
  `FirstPassage.lean:981/985/1325`, `Basic/Collatz.lean:16`, `Prob/Basic.lean:16`.
- `check_blueprint.py` check 11 traps `epsBW = 1/10^4` but the code deploys `1/10^1000` — update the trap value.
- `papers/literature-review.md` fidelity-ledger row says `ε := 10⁻⁴` (stale; deployed `10⁻¹⁰⁰⁰`).

*(Independent audit record → `judge/pass-30.md`. An external Fable strategy cross-check on the overnight burn-down order is pending; fold in on arrival.)*

---

## SUPERSEDED — JUDGE PASS 29, 2026-07-14 — **C10 → C8 (pin) → C7 (prove) → C8 (close) → C9**

🗺️ **`blueprint_rules.md` is BINDING — read it.** One node, one claim; pinning = writing the Lean
statement with `sorry`; green border = *the statement exists*, never *finished*; **never set a
`\leanok` yourself**. Report work as **"N sorries + M orange nodes"** (today: **7 + 1**).

*Supersedes the pass-27 objective and the pass-28 correction block below (both FULFILLED — see
"What pass 29 verified"). The hard rails below are LIVE; the rails in the superseded blocks still
bind wherever they are not restated here.*

### 🧘 DEEP-REFLECTION UPDATE (2026-07-15, HEAD `95436f9`) — **C8 reindex pin is DEFECTIVE — RE-PIN before grinding**; route CONTINUE-with-correction

*(NEWEST — outranks the blocks below wherever they conflict. The overall order
`C10 → C8 → C7 → C8(close) → C9` STILL STANDS; C10/C7 remain CLOSED + axiom-clean, re-verified this
lap by fresh `#print axioms` at `95436f9`. What changes: **HOW C8 closes.** Every pass-29 rail still
binds except where the C8 sub-structure is restated here.)*

**Route = CONTINUE, but a false summit was caught.** Ground truth this lap (build 🟢 3322 jobs;
`#print axioms`): `fine_scale_mixing`=`first_passage_nonescape`=`[propext,choice,Quot.sound]`;
`first_passage_approx`,`stabilization`= trust base+`sorryAx`. **6 sorries + 0 orange nodes**
(2 headline stubs, C9 `stabilization`, 3×C8). blueprint_audit: 0 orange, 0 false-green; C7 is a
**MISSED FLIP** (axiom-clean, `\leanok` not set — **judge task**).

**🚩 JUDGE-FLAG (route-decisive): the ratified `approxMainTerm` pin (RATIFY-C8) does NOT faithfully
render (5.8).** It builds the main term from the **ℕ-truncating** `Aff` (`Basic/Valuation.lean:154`)
with **no** divisibility guard, but Tao's (5.8) reindex is **EXACT** (Lemma 2.1) and lives on the
**(5.18) congruence** `M ≡ F_{n−m₀}(ā) (mod 3^{n−m₀})`. Under the ℕ-floor, `Aff N k ā` depends on `ā`
essentially only through `|ā|`, so **exponentially-many good tuples collapse into `E'`** — the closing
hole **`truncation_error_bound` (`ApproxFormula.lean:1215`) is FALSE** (`approxMainTerm − steppedMid`
is super-polylog, not `O(log^{-c}x)`). Evidence: source read pp.22–25 (`papers/literature-review.md`
§5, HOLE #4) + numeric probe `tools/sandbox/tao_c8_truncation_probe.py` (truncating count = thousands,
growing in `k`; the exact guard `2^{|ā|} ∣ (3^k N + fnat)` collapses it to 0–3 → 1). The
`ApproxFormula.lean:237` docstring's bet ("count can exceed 1, Tao absorbs it") conflates Tao's
value-rounding error with a count-multiplicity the ℕ-floor invents; refuted.

**🥇 MANDATED NEXT MOVE (do these, in order):**
1. **RE-PIN `approxMainTerm`** as **RATIFY-C8-v2**: guard the pushforward by the exact affine relation
   `3^{n−m₀}N + fnat (n−m₀) ā = M · 2^{a_{[1,n−m₀]}}` (⟺ (5.18) congruence + integrality). This is the
   faithful render of Tao's `ℙ(Aff_ā(N_y)=M)`. Absent a live judge, the deep-reflection lap authorizes
   this re-pin against source (5.8)+(5.18)+Lemma 2.1; tag `-- RATIFY-C8-v2`, record the diff, leave the
   node `\notready` (orange) until a judge reads it. **DELETE `truncation_error_bound`** — with the
   guard the reindex is exact (Lemma 2.1), so that hole vanishes; `steppedMid_le_approxMainTerm`
   becomes `steppedMid = approxMainTerm` up to genuine (5.19) value-rounding.
2. Re-wire `approxMainTerm_eq_source` / `first_passage_truncation_reindex` / `first_passage_affine_reindex`
   onto the guarded pin (the mechanical layer — `map_mask_tsum`, `goodTuple_finite`,
   `syr_iterate_good_bracket'`, `two_rpow_slack_le_exp`, the step-back kernels — is **reusable**).
3. **Parallel SAFE thread** (does NOT touch the reindex, bank it anytime): `passtime_window_inner`
   (`ApproxFormula.lean:798`, the (5.16) window term) — source-backed integral test reusing C7's
   proved `classMass`/`windowMass`/`intTest_*`.

**Forbidden drift (this update):** do NOT grind `truncation_error_bound` as stated (it is false — you
will burn laps on an unprovable goal); do NOT keep building on the unguarded `approxMainTerm`; do NOT
retreat to C9 while C8's reindex is being re-pinned; do NOT touch `first_passage_nonescape` /
`stabilization` / `fine_scale_mixing` (WATCHED). The re-pin is the ONLY sanctioned edit to a
RATIFY-C8 statement — everything else stays frozen.

### 🔎 REVIEW-LAP UPDATE (2026-07-14, HEAD `810518b`) — **C7 PROVED axiom-clean; live target advances to C8-close**; route CONTINUE

*(Refines — does not override — Judge Pass 29 and the `e0913ce` update below. The
C10→C8→C7→C8→C9 order STANDS; **objectives 1, 2, 3 are now all DONE**, so the live target is the
**C8-close** leg (objective 4, first half). Every pass-29 rail still binds.)*

**Route CONTINUE; no trigger fired.** Re-verified this lap by fresh `#print axioms` at `810518b`:
- ✅ **OBJECTIVE 3 (C7) — DONE, axiom-clean.** `first_passage_nonescape` (1.19) =
  `[propext, Classical.choice, Quot.sound]`. The integral test (`integral_test_logUnif` via
  `intTest_class_dev` / `classMass_ap_form` — the AP-reindexing bridge) AND `valSum_lower_tail`
  (5.5) both closed. **Judge to flip the C7 `\leanok`.**
- ✅ **C10 + C8-pin still verified**: `fine_scale_mixing` clean; `first_passage_approx` pinned
  (trust base + `sorryAx`, 3 named sub-sorries); `stabilization` (C9) pinned (trust base + `sorryAx`).
- 🎯 **LIVE TARGET = close C8 = `first_passage_approx`** (`Sec5/ApproxFormula.lean`). Three named
  sorries: the **assembly** `first_passage_approx` (:97 — the (5.8) affine reindexing, Lemma 2.1),
  `approx_good_tuple_whp` (:116 — (5.12) good-tuple union bound, **does NOT use C7**), and
  `approx_passtime_window` (:132 — (5.16), **THE C7 consumer**). C7 is now available to wire into
  (5.16)'s `{¬ passes}` term.

**🥇 MANDATED NEXT MOVE (hardest-first): the C8 ASSEMBLY's affine reindexing is the route-decisive
piece — probe it FIRST.** The two whp sub-lemmas are "small-probability" bounds over PROVED
machinery (C5/S3 for 5.12; C7 + the integral test for 5.16); the assembly `first_passage_approx` is
the only piece whose failure would falsify the *pinned* `approxMainTerm` definition — the Lemma-2.1
affine pushforward `Aff` reindexing that collapses `ℙ(Pass_x(N_y) ∈ E)` to the affine main term. If
that reindexing does not go through against our defs, that is route-decisive information about the
pin. Decompose it into named sub-sorries in `src/` (raising the count is PROGRESS). Detailed attack
plan: **PENDING_WORK top, "C8 close — attack plan (2026-07-14 review)".**

**Forbidden drift (this update, atop pass-29's):** do NOT retreat to C9 while C8 is open; do NOT
touch `first_passage_nonescape` / `stabilization` / `fine_scale_mixing` (all WATCHED) or any ratified
pin; do NOT edit the RATIFY-C8 statements/defs — decompose *below* them only.

### 🔎 REVIEW-LAP UPDATE (2026-07-14, HEAD `e0913ce`) — obj 1+2 DONE; frontier = C7's integral test; route CONTINUE

*(Refines — does not override — Judge Pass 29. The C10→C8→C7→C8→C9 order STANDS. This records where
we are ALONG it and reframes the C7 crux; the pass-29 rails all still bind.)*

**Route CONTINUE; no trigger fired.** Positions re-verified this lap by fresh `#print axioms`:
- ✅ **OBJECTIVE 1 (C10) — DONE, axiom-clean.** `fine_scale_mixing`, `error_l1_high_bound`,
  `prob_not_globalGood_le` all `[propext, Classical.choice, Quot.sound]` at `e0913ce`. `globalGood ⊆
  mainEvent` proved; (6.3) union bound in; `MixingError.lean` sorry-free. **Judge to flip C10 `\leanok`.**
- ✅ **OBJECTIVE 2 (C8) — PINNED + ROUTED + PROBED.** `first_passage_approx` (RATIFY-C8,
  `Sec5/ApproxFormula.lean`) + 2 named sub-sorries; `blueprint_audit` 0 orange. **C8's proof consumes
  C7 at EXACTLY ONE place** — `approx_passtime_window` (5.16), the `{¬passes}` escape term = (1.19).
- 🎯 **LIVE TARGET = OBJECTIVE 3 (C7).** `first_passage_nonescape` is down to **2** sub-sorries:
  `integral_test_logUnif` (the CRUX) + `valSum_lower_tail`. Descent leaves (`syr_descent_bound`,
  `descent_passes`, `descent_pow_bounds`) DONE + axiom-clean.

**⚡ THE C7 CRUX IS MIS-FRAMED AS HARDER THAN IT IS — reframe BEFORE attacking.** The 2130 handoff
calls `integral_test_logUnif` "no existing equidistribution machinery (grepped)." That grep was for
*dynamical* equidistribution (`{ξθⁿ}`), which mathlib genuinely lacks (corpus
`2026-06-14-mathlib-equidistribution-geometric-gap.md`) — **but that is NOT our lemma.** Ours is the
**elementary integral test**, and BOTH its ingredients are already in mathlib:
- **exact AP count in an interval**: `Nat.Ioc_filter_modEq_card` (`Mathlib/Data/Int/CardIntervalMod.lean`)
  — corpus `mathlib-has-ap-count-and-multimod-crt.md`;
- **sum ↔ integral comparison** (the test itself): `AntitoneOn.sum_le_integral` /
  `AntitoneOn.integral_le_sum` (+`_Ico`) (`Mathlib/Analysis/SumIntegralComparisons.lean`), with
  `integral_inv` (`∫ 1/t = log`, `Analysis/SpecialFunctions/Integrals/Basic.lean`).

**🥇 MANDATED NEXT MOVE (hardest-first): attack `integral_test_logUnif` FIRST — NOT `valSum_lower_tail`.**
`valSum_lower_tail` is *downstream* of the crux (it consumes it via `valuation_dist`) and mechanical, so
closing it first banks NO information — that is exactly the crux-neglect the last laps drifted into
(descent leaves closed, crux untouched). Decompose the integral test into named sub-sorries in `src/`
(raising the count is PROGRESS): the per-odd-residue-class 1/N-mass uniformity (sum↔integral on `t↦1/t`
per AP, error `O(2^{n'}/y)`), the dTV assembly, the numeric closure `2^{2n'}≍x^{0.6} ≤ y≍x^{1.001}`.
Full attack plan: **PENDING_WORK top, "C7 integral test — attack plan (2026-07-14 review)".**

**Forbidden drift (this update, atop pass-29's):** do NOT grind `valSum_lower_tail` before the integral
test exists; do NOT retreat to C8-close or C9 while C7's crux is open; the mathlib reframe is a
*route*, not a licence to touch `stabilization`/`fine_scale_mixing` or any ratified pin.

### 🎯 THE ORDER: **C10 → C8 (pin) → C7 (prove) → C8 (close) → C9**

Two facts set it, and the second one is the subtle one:

**1. C8 is ORANGE** — its statement is not in Lean, so it is invisible to the sorry census.
`./tools/blueprint_audit.py` prints it, with what it blocks:

```
C8   — nothing claimed —
     └─ blocks C6, C9 · ⛔ PROOF needs C7 · 📌 statement PINNABLE NOW (their defs exist)
```

✅ **C7 is no longer orange — the judge PINNED it** (`first_passage_nonescape`, a real theorem with a
`sorry`). It had been a `lemma` node whose `\lean{}` named three *defs* and which carried a statement
`\leanok`, so it rendered **GREEN while its content — the estimate (1.19) — was nowhere in Lean**.
Split into `C7d` (the defs, done) + `C7` (the lemma, pinned). ⚠️ **And it is NOT low risk:** re-rated
`low / 5–10 / 85%` → **`medium / 10–18 / 75%`**. The old badge had been earned by the defs.

**2. STATEMENT-deps ≠ PROOF-deps.** C8's `\uses{C2, C5, C7}` is a dependency of its **proof**.
C8's *statement* (Prop 5.2 / (5.8)) is written in terms of the first-passage **definitions**
(`passes`, `passTime`, `passLoc`) — **which exist.** So **C8 can be pinned, routed and probed
TODAY**, before a line of C7 is proved.

**And it should be.** The standing charter (BLUEPRINT §2) is *de-risk breadth-first: turn RED nodes
YELLOW (pinned + routed + hardest sub-lemma probed) everywhere before polishing yellow → green.*
**C8 is the risk** (diff 4, 15–30 laps, **75%**); C7 is the cheap one (diff 2, 5–10 laps, **85%**,
unblocked). Grinding the cheap node first buys no information. **Pin the scary one first, then feed
it.** Pinning C8 also tells you *precisely what C8 needs from C7* — which may not be (1.19) exactly
as the blueprint states it.

*(Trevor caught two judge errors here in one exchange. Pass 29 first ordered C10 → C8 → C9, calling
it "forced by the dependency graph" **while skipping the C7 edge in that graph** — the audit had
printed `C7` on the line directly above `C8`. Corrected to C10 → C7 → C8 → C9, which was **also
wrong**: it de-risked in cost order instead of risk order, and treated a proof-dep as a
statement-dep. **Invoking an instrument's authority is not the same as reading it — and reading a
dependency edge is not the same as knowing what it blocks.**)*

---

### 🥇 OBJECTIVE 1 — close C10: `error_l1_high_bound` (`Sec6/MixingError.lean:359`)

**This is the last mathematical content in C10. Everything else in the node is PROVED and
axiom-clean** (judge-verified `#print axioms` @ `7ff033b`, pass 29).

Two machine-checked identities have collapsed C10 to a single tail estimate:

- `mainHigh_eq_restrictedDensity` ✅ — `mainHigh` **is** the Syracuse pushforward restricted to `mainEvent`.
- `sum_abs_syracZ_sub_mainHigh_eq` ✅ — `∑_Y |syracZ − mainHigh| **=** P(¬mainEvent)`. An **equality**.

So the remaining sorry is exactly: **`P(¬mainEvent) ≤ (C/2)·m^{-A}`**. It is a probability bound.
There is no structural work left, no novel kernel, no constant risk (`hbudget` is discharged and the
`A′`-absorption is *shown* — both former tripwires are retired).

**The route (hardest-first):**

1. **Define the global good deviation event** — Tao (6.2) — as a tail-measurable `DecidablePred`.
2. **Prove `globalGood ⊆ mainEvent` EXPLICITLY.** ⚠️ **This inclusion IS the content of the node.**
   It must produce: the existence of the stopping cut `k`, membership in `condWindow`, and the tight
   `lRange` bound. **Do not gesture at it, do not `sorry` past it into the tail bound** — if you
   prove the tail bound first and the inclusion second, you will discover the inclusion is where all
   the work was.
3. **Bound the complement** — `geomHalf_tail_bound` (PROVED, `Prob/LocalInstances.lean:540`) + a
   union bound over the interval/coordinate pairs. Pay for the union out of the **spare `A+3`
   exponent in `caConst`**, which is there precisely for this.
4. **Convert `n` → `m`** using `0.9n ≤ m ≤ n` (the regime hypothesis `9*n ≤ 10*m`), then apply
   `sum_abs_syracZ_sub_mainHigh_eq`.

**⚖️ Standing ruling (pass 29) — read this before you touch an event definition.**
`condWindow` is an **ENLARGEMENT** of Tao's `Eₖ`: it keeps only the suffix inequalities the
injectivity kernel actually consumes. **This is safe and it works in our favour** — a bigger good
event means a smaller complement, so step 3 gets *easier*. The events are **internal**: they appear
nowhere in the pinned statement, so a wrong event choice **cannot make the theorem false — it can
only make `error_l1_high_bound` unprovable.** *It costs provability, never soundness.*
Two demands follow, and they are binding:
- **Never document `condWindow` as EQUAL to the paper's `Eₖ`.** It is an enlargement. Say so, in the
  docstring, every time.
- **Every event definition that claims to be a partition owes a PROVED disjointness lemma next to
  it.** An unproved partition claim is a **hole wearing a definition's clothes** — zero sorries, and
  load-bearing. (This rail exists because the reversed-coordinate bug in `stopEvent` compiled green:
  the old definition removed `a₁` instead of `a_{k+1}` and did **not** produce a stopping-time
  partition. See pass 29 §4. `mainPieceEvent_cut_unique` is what the fix looks like when it can't regress.)

---

### 🥈 OBJECTIVE 2 — C8 (Prop 5.2, §5 pp.22–25): **PIN + ROUTE + PROBE it. Do NOT try to close it.**

**C8 is the risk on the board** (diff 4, 15–30 laps, **75%** — the lowest confidence of anything
left) and it is the repo's **one remaining ORANGE node**: no Lean behind it at all, so the sorry
census cannot see it. It has been ordered pinned since pass 27 and never has been.
**De-risk it before you feed it.** ⚠️ **PIN = write the statements with `sorry` so they compile** —
naming them is not pinning (`blueprint_rules.md`).

- **Scope**: Prop 5.2 approximate formula **(5.8)**; the events `𝒜^{(n')}` **(5.11)**, `E'` **(5.10)**,
  `I_y` **(5.9)**; the `B_{n,y}` equivalence chain.
- **You do NOT need C7 to do this.** C8's statement is written over the first-passage *definitions*
  (`passes`, `passTime`, `passLoc`), which exist. Only its **proof** consumes (1.19).
- **Statements are copy-not-compose**: render each verbatim against its numbered display in the PDF
  (pp.22–25), then freeze. Mark each `RATIFY-C8`.
- **Then ROUTE and PROBE**: decompose into named sub-`sorry`s, and **write down exactly what C8's
  proof needs from C7.** That is the deliverable of this objective — it may not be (1.19) precisely
  as the blueprint states it, and finding that out now is worth more than a proved C7.
- **Do not grind C8 to green here.** Pinned + routed + hardest sub-lemma probed = objective met.

---

### 🥉 OBJECTIVE 3 — C7: **prove (1.19). It is PINNED for you — the brick is the INTEGRAL TEST.**

✅ **The judge pinned it (2026-07-14).** `first_passage_nonescape` (`Sec5/FirstPassage.lean`) is now a
real Lean theorem carrying a `sorry`, stated **character-identically to the first conjunct of
`stabilization`** — which is where this content had been absorbed. It is in the census. Ratified
against p.20.

> **(1.19)**: `P(T_x(N_y) = ∞) ≪ x^{-c}` — a log-uniform odd `N_y ∈ [y, y^α]` fails ever to descend
> to `≤ x` only with probability `≪ x^{-c}`.

⚠️ **RE-RATED: `low / 5–10 / 85%` → `medium / 10–18 / 75%`.** The old badge was earned by the three
*definitions* bundled into the node; the lemma alone had never been costed. **Do not treat this as
the easy one.**

**The route (Tao pp.20–21) — every step but the first runs over PROVED machinery:**

1. ⚠️ **THE INTEGRAL TEST — the only new brick, and the whole risk of the node.**
   `dTV(N_y mod 2^{n'}, unifOddMod n') ≪ 2^{-n'}` for the log-uniform window, at `n' = 3n₀`.
   **It is exactly the hypothesis `valuation_dist` (Prop 1.9 / C5) takes** — which is *why* nothing
   downstream can proceed without it. Tao: *"a routine application of the integral test"* (with
   plenty of room to spare). It does not exist in Lean. **Build it first; it is the node.**
2. Prop 1.9 (C5 ✅ axiom-clean) ⟹ `dTV(valVec N n₀, geomHalf.iid n₀) ≪ 2^{-c·n₀}` — (5.4).
3. Lemma 2.2 (S3 ✅ axiom-clean). **`geomHalf_tail_bound` is TWO-SIDED** (`P(||Geom(2)ₙ| − 2n| ≥ λ)`),
   so it already covers this **lower** tail: `P(|ā^{(n₀)}| ≤ 1.9·n₀) ≪ 2^{-c·n₀} ≪ x^{-c}` — (5.5).
4. **Descent arithmetic**: if `|ā^{(n₀)}| > 1.9·n₀` then by (1.5)/(1.7)
   `Syr^{n₀}(N_y) ≤ 3^{n₀}·2^{-1.9n₀}·x^{α³} + O(3^{n₀}) = O(x^{0.99}) ≤ x`, so `T_x(N_y) ≤ n₀ < ∞`.
   Here `n₀ := ⌊log x / (10·log 2)⌋` (5.1), i.e. `2^{n₀} ≍ x^{0.1}`.

🔒 **`stabilization` is WATCHED — do not touch it.** C9 will *cite* `first_passage_nonescape`; adding
lemmas beside a pin is always allowed, editing the pin is not.

---

### 4️⃣ OBJECTIVE 4 — close C8, then C9 `stabilization` (Prop 1.11, `Sec5/FirstPassage.lean:81`)

With (1.19) in hand, discharge C8's named sorries. **Then** C9: Lemma 5.3 (`c_n(X) ≪ 1`),
(5.18)–(5.21), and the Prop 1.11 assembly (applies Prop 1.14 at scale `m₀`). C9 consumes **C10 and C8**.

---

**For BOTH seam nodes (C7 and C8):**
- 🔒 **Never set `\leanok` yourself — statement OR proof. Ratification is the judge's.** A new pin is a
  **claim, not a fact**: say in your handoff what you pinned and what you pinned it against.
  ⚠️ **A statement `\leanok` on a node with no theorem is a FALSE GREEN** — it is what C7 was carrying,
  and `blueprint_audit.py` now fails the build on it.
- Decompose freely into named sub-`sorry`s as you build. **Raising the sorry count this way is
  PROGRESS** — it converts an invisible seam into visible, attackable holes. **A seam is strictly
  worse than a sorry: a sorry is honest about what it owes.**

---

### 🚧 Forbidden drift

- **Do NOT start C8, C7 or C9 while C10's tail sorries are open.** `globalGood ⊆ mainEvent` is
  PROVED and the (6.3) union bound is in; `error_l1_high_bound` is down to **3 named tail sorries**
  (`MixingError.lean`). C10 is upstream of everything. **Finish it.**
- **Do NOT grind C7 first because it is easy.** Cheap-first buys no information. The charter is
  *de-risk breadth-first*: **pin the 75% node, then feed it.**
- **Do NOT try to CLOSE C8 before C7 exists.** Pin it, route it, probe it, and stop there. Its proof
  consumes (1.19).
- **Do NOT touch the two `Statement.lean` headline sorries** (hard rail 2). They discharge when the
  whole chain C10 → C9 → C6 lands, and not one minute before.
- **Do NOT edit `fine_scale_mixing` or `stabilization`** — the two open crux statements are WATCHED
  (hard rail 6, extended). Decomposing *below* them is always allowed; moving the goalposts is not.
- **Do NOT edit any ratified §7 pin.** §7 is complete, frozen and clean. Leave it alone.
- **Do NOT re-derive the constants.** `caConst = 30` (`C_A ≥ 23`), the **tight** window (never the
  paper's (6.8) — it provably cannot close for ANY `C`), `epsBW = 1/10^1000`. All three are judge
  rulings backed by machine-checked lemmas. If one seems wrong: **`JUDGE-FLAG:`**, do not adjust.

### 🗺️ BLUEPRINT RULES ARE BINDING — read `blueprint_rules.md`. "Seam" is retired vocabulary.

**One node, one claim. Pinning a node means writing its Lean statement with `sorry`.** A **green
border** on the dep-graph means *the statement is in Lean*, never *this is finished*; the **fill** is
the proof. An **orange** border means the statement is not written yet — and **an orange node is the
only work the sorry census cannot see.**

- **Report remaining work as "N sorries + M orange nodes."** Today: **7 sorries + 1 orange** (C8).
- **Never set a `\leanok` yourself** — statement or proof. Ratification is the judge's, and a
  `\leanok` over a node with no theorem is a **FALSE GREEN** that now **fails the build**
  (`./tools/blueprint_audit.py`).
- **The fix for an orange node is not a report — it is a PIN.** That is objective 2.

*(We spent months calling an orange node a "seam" and building apparatus to detect what the graph was
already rendering in a color. Retired. Detail: `blueprint_architecture.md`.)*

### ✅ What pass 29 verified (so you don't re-open it)
`lRange_hbudget` ✅ clean · `osc_mainHigh_bound` ✅ clean (**the `A′`-absorption at `C_A = 30` is
SHOWN, not asserted** — head decay at the shifted exponent `A' = A + C_A²·log2`) ·
`mainHigh_eq_restrictedDensity` ✅ · `sum_abs_syracZ_sub_mainHigh_eq` ✅ ·
`tailDensW_condWindowB_le` ✅ · **statement erosion 29/29 character-identical across 70 commits** ·
`blueprint_audit` → 13 nodes proved, 0 drift, 0 false-green.
**Both of pass 28's tripwires are discharged.** The C10 sorry is an honest decomposition, not a
relocated hole — the kernel says so, and *the census was right to be distrusted*.

---

## SUPERSEDED — JUDGE PASS 27 + 28 (2026-07-14; §7 RATIFIED COMPLETE; objective was C10)

*Both FULFILLED. Kept for the rails and the reasoning; the objectives are retired. `hbudget` is
discharged (`lRange_hbudget`), the `A′`-absorption is shown (`osc_mainHigh_bound`), and the C10
frontier has moved past everything ordered here — see the pass-29 directive above.*

### 🔎 REVIEW-LAP UPDATE (2026-07-15, HEAD `4eabb35`) — route CONTINUE, frontier advanced to the ASSEMBLY

*(Refines — does not override — the judge pass-27 objective and the reflection block below. Both stand.)*

**Route CONTINUE; no trigger fired.** **T3 is DE-RISKED**: the reflection's route-decisive kernel
`fnat_lt_of_suffix_window` (the ONE place §6 runs on critical constants) landed machine-checked +
axiom-clean at lap 1 of the ~6-lap T3 window, and so did the collision bound `tailDensW_le_single_mass`
(`tailDensW Y ≤ 2⁻ˡ`). Fresh review-lap `#print axioms` (HEAD `4eabb35`): `fnat_lt_of_suffix_window`,
`tailDensW_le_single_mass`, `fnat_offset_zmod_inj`, `condDens_osc_le` all `[propext, choice, Quot.sound]`.
**Obligation 3's analytic content is DONE** — the constant risk that dominated C10 is retired.

**The frontier has therefore moved from "the window kernel" (done) to "the ASSEMBLY."** Hardest-first,
the mandated next moves, IN ORDER:
1. **Finish the windowed obl-3 plumbing** (small, on-path, completes obl 3 into a consumable bound):
   `tailDensW_sum_le_one` → windowed Rényi `∑ (tailDensW)² ≤ 2⁻ˡ` → windowed `tail_factor_dft_eq`/
   `_l2_eq` → a windowed `condDens`/`condDens_osc_le` analogue, so the single-point mass actually feeds
   the osc √. Mirror the existing non-windowed lemmas (extra `∧ W vt` conjunct); zero novelty.
2. **THEN attack the assembly = obligation 1** (now the hardest, most route-uncertain open piece):
   **decompose `fine_scale_mixing` (`MixingFromDecay.lean:1711`) into named obl-0/1/2/3 sub-`sorry`s in
   `src/`** — define the events `E`/`Eₖ`/`Bₖ`/`Cₖ,ₗ` as tail-measurable `DecidablePred`s (`Classical.dec`),
   state the (6.1)–(6.10) decomposition + triangle-inequality skeleton, and discharge the window kernel's
   `hbudget`/`hsuf` hypotheses FROM `Bₖ`/`Eₖ`. Raising the src sorry count this way is PROGRESS — it turns
   the one opaque crux into attackable named pieces and surfaces assembly gaps early (the reflection found
   obl-0 missing on paper; do it in Lean now).
3. Then `P(Ē) ≤ n^{-A-1}` (obl 1 tail), `hunif` head decay (obl 2), regime telescope (obl 0), final wire.

**Forbidden drift (this update):** do NOT keep banking isolated obl-3 lemmas without wiring them toward
`fine_scale_mixing` — the analytic content is done; the value now is in the assembly. Do NOT retreat to
C9. Do NOT touch watched statements (`fine_scale_mixing`/`stabilization`) or any ratified pin.

---

## 🚨 JUDGE PASS 28 — CORRECTION TO THE ABOVE. READ BEFORE TOUCHING `hbudget`.

**The JUDGE-FLAG is ruled on: the tight-window deviation is ✅ RATIFIED (see below). But the
review lap's instruction to "discharge `hbudget` from the (6.8) l-range + `Cₐ≥10`" is
IMPOSSIBLE ON BOTH COUNTS, and a lap that tries it will be grinding at a false target.**

The kernel you proved, `fnat_lt_of_suffix_window`, carries (AM-GM at **ε = 1/5**):

> `hbudget`: cost `= C·ln2 + (5/4)·(C·ln2)² ≈ 0.601·C² + 0.693·C` per `ln n`.

Judge-recomputed (`tools/sandbox/tao_hbudget_check.py`, independent of the box's numbers):

| window | budget per `ln n` | discharges `hbudget`? |
|---|---|---|
| **(6.8) paper ½-window** | `ln2·½C² = 0.347·C²` | ❌ **NEVER — for ANY `C`.** budget − cost has a **negative** `C²` coefficient (−0.254). This is not a "too small `C`" problem; the sign is wrong. |
| **tight (`Bₖ` + one-step `Eₖ`)** | `ln2·(C²−2C) = 0.693·C² − 1.386·C` | ✅ **only for `C > 22.46`, i.e. `C ≥ 23`** |

So:
1. **Discharge `hbudget` from the TIGHT window, never (6.8).** The kernel's own docstring already
   says *"Do NOT weaken this hypothesis toward (6.8)"* — obey the docstring, not the bullet above.
2. **`Cₐ ≥ 23`, not `Cₐ ≥ 10`.** The "closes for `C_A ≥ 10`" figure in the reflection block,
   in `papers/literature-review.md`, and in item 3 above is **stale** — it came from a *pre-proof*
   ε=1/4 estimate (cost `0.481·C²`). The lemma you actually proved uses **ε = 1/5** (cost
   `0.601·C²`), and at `C = 10` that costs `66.99` against a tight budget of `55.45` — **it fails.**
   The docstring of the proved lemma (`C ≳ 23`) is the number that is right. 📌 *Two worker
   numerals disagreed; the one attached to the machine-checked artifact wins.*
3. `Cₐ ≥ 23` is **consumable** — `C_A` is a "sufficiently large" constant chosen from `A` exactly as
   the paper does. But it is not free: it worsens the single-point mass to `n^{O(C_A²)}·3^{-n}`.
   ⚠️ **Do not assume that absorbs.** When you wire obl-2/obl-3 together, *show* the `A′`-absorption
   at `C_A = 23` rather than asserting it. If it does not absorb, **`JUDGE-FLAG:` — do not respond
   by shaving `C_A` back toward 10, and do not touch the window.**
4. If you would rather buy margin than raise `C_A`: re-prove the kernel at **ε = 1/4** (cost
   `0.481·C²`, threshold back to `C ≳ 10`). That is a *strengthening of an unwatched internal
   lemma* and is allowed. Adding a lemma beside it is always allowed.

**Standing:** `hbudget` is now the campaign's single load-bearing undischarged number. It is the
one place C10 runs on critical constants. Treat a failure to close it as **information**, not as
pressure to adjust something.

---

**⚖️ The review lap's C10 retarget below is RATIFIED.** The judge has now verified it
independently (pass 27, worktree pinned at `8505bd4`, dated axiom runs): §7 is complete, the
`Cthr` bridge is genuinely discharged in Lean, the statement differ reports **28/29
byte-identical** across all 53 overnight commits, and the sorry census is **4** (C10, C9, 2
headline stubs). Keep going exactly as directed below.

### 🔴 HARD RAIL 6, EXTENDED — the open crux statements are now WATCHED

`fine_scale_mixing` (C10) and `stabilization` (C9) are now in the differ's watch list
(`tools/tao_stmt_diff.py`, 19 → 29 names; `Sec6/` and `Sec5/` added to its search path).

**Do NOT edit the statement of `fine_scale_mixing` or `stabilization` — not to weaken it, not
to strengthen it, not to "generalize" it, and above all not to make your own sorry closeable.**
This is the single highest-value silent failure available to a lap right now: a green build, a
clean `#print axioms`, and an unmoved sorry census **cannot see it**. Only the differ can, and
until this pass it was not looking at these two names.

You may always **decompose below** a crux statement into named sub-`sorry`s — that is progress
and it is encouraged. What you may not do is move the goalposts. If the statement looks wrong
against the paper, write **`JUDGE-FLAG:`** in `PENDING_WORK.md` + your handoff and move on.
(Pass 26's lesson, and it was learned the expensive way: a lap that believes it is
*strengthening* a statement will sail straight through a rail that only says "never weaken.")

**🏆 MILESTONE.** The §7 crux — the campaign's stated 65–75% risk concentration, "the
paper's pinnacle" (X8/X9/X10/X11) — is **DONE and axiom-clean.** Review-lap `#print axioms`
(HEAD `1c3ee3d`, build green, 3285 jobs): `prop_7_8`, `Q_black_edge`, `Q_polynomial_decay`,
`charFn_decay` (Prop 1.17), `key_fourier_decay` (Prop 7.1) **all** = `[propext,
Classical.choice, Quot.sound]`. Judge Pass 26's three §7 objectives are FULFILLED (X11
`Q_black_edge_case3` closed; the two Case-3 sorries proved; the X10 `_rpow` split landed).
**That directive is retired** — grind laps had already correctly moved past it to §6.

**The content spine now has EXACTLY TWO open heroic sorries** (+ the two frozen headline stubs):
- C10 `fine_scale_mixing` (Prop 1.14, §6, `Sec6/MixingFromDecay.lean:377`) — `sorryAx`.
- C9 `stabilization` (Prop 1.11, §5, `Sec5/FirstPassage.lean:81`) — `sorryAx`, **consumes C10**.

### 🎯 THE ONE OBJECTIVE: prove C10 `fine_scale_mixing` (Prop 1.14).

It is the crux: hardest open node AND upstream of C9 on the critical path
`C10 → C9 → C6 → Statement`. **It is NOT a new analytic kernel** — both hard ingredients are
already proved axiom-clean: (i) the Cauchy–Schwarz/Parseval bridge `osc_le_sqrt_highfreq`
(8 lemmas, `MixingFromDecay.lean`); (ii) `charFn_decay` (Prop 1.17, the character-sum decay).
C10 is the §6 **conditioning assembly** that plugs (ii) into (i) applied to a *conditioned*
density `g`, not raw `syracZ`. Risk = volume/bookkeeping, NOT novelty (the charter rates
post-§7 at 75–95%). **Do not treat "HEROIC" as un-attackable and retreat.**

### 🔄 REFLECTION COURSE-CORRECTION (deep reflection lap, 2026-07-14, HEAD `f96a728`) — BINDING

The pass-27 objective (C10) and route (§6 conditioning) are CONFIRMED — route verdict
**CONTINUE** — but the obligation-3 attack line the fruit-22/23 laps recorded is **REFUTED**:

- **Do NOT attempt "window (6.12) ⟹ per-prefix hypothesis of `fnat_lt_of_prefix_bound`".**
  That hypothesis is FALSE in the operating regime (`m=0` instance `3^(p-1)·2^p < 3^(j+p)` fails
  at `p ≈ 0.7925n`: coefficient 1.42 > 1.10 — verified numerically). The lemma stays (true,
  proved, harmless); the route around it is the SUFFIX form.
- **THE mandated next brick**: `fnat_lt_of_suffix_window` — from the **tight** l-window
  `l ≤ n·log3/log2 − (C²−2C)·log n − O(1)` (stopping rule Bₖ + one-step Eₖ bound — NOT the
  paper's lossy (6.8), whose ½-budget provably cannot close the Young estimate: 0.347·C² vs
  0.418·C² minimum cost) and the suffix-interval windows from (6.12), conclude
  `fnat p vt < 3^(j+p)`. Young at `ε = 1/4`: cost `(ln2)²C² = 0.4805C²` vs budget
  `ln2·(C²−2C) = 0.693(C²−2C)`; geometric rate `ln(4/3) − 1/4 = 0.0377`, sum ≤ 28; closes for
  `C ≥ 10`, `n ≥ n₀` explicit. Full spec: PENDING_WORK "Reflection — 2026-07-14". It feeds the
  proved `fnat_offset_zmod_inj` unchanged.
- **JUDGE-FLAG (new, for pass 28)**: the Lean Cor-6.3 analogue will carry the tight l-window
  instead of the paper's (6.8) — the paper's own display does not close as literally stated
  (third documented source deviation, after the two 7.9 holes). Details + fidelity-ledger row:
  `papers/literature-review.md` §Cor 6.3.
- **Dashboard completeness**: obligation 0 (the (6.1) regime reduction / (1.22) telescope for
  `m < 0.9n` + trivial `m < 10`) was missing — now named; low-risk volume, do NOT let it be
  discovered at assembly time. The windowed-indicator generalization of `condDens`/`tailDens`
  (hardwired `pre = l` → arbitrary tail-measurable decidable event) serves obligations 1 AND 3;
  it touches only unwatched in-progress machinery (allowed; T4 below if that ever seems false).
- **New route triggers**: **T3** — if the corrected window kernel isn't machine-checked within
  ~6 grind laps, or Lean contradicts the 0.4805-vs-0.693 margin analysis → `ROUTE-ESCALATION`.
  **T4** — if any of this seems to require editing `fine_scale_mixing`/`stabilization` or a
  ratified pin → STOP + `JUDGE-FLAG:`, move to another brick.

### Mandated next move (pass 27 — SUPERSEDED IN PART by the reflection block above; bricks d / a / b are DONE, and items 1–2 below have since landed as `head_factor_eq_charFn` / `condDens_osc_le`)
The raw-density route is REFUTED (`scripts/syracZ_highfreq_l2.py`: raw high-freq L² mass GROWS
≈0.46·n) and remapped. The correct route (Tao §6, pdf pp.28–31) applies the bridge to
`g_{n,k,l}(Y)=P(Xₙ=Y ∧ Eₖ∧Bₖ∧Cₖ,ₗ)`. **Landed + judge-verified axiom-clean this run**: brick (d)
density-general `osc_le_sqrt_highfreq`; brick (a) `fnat_split` + `syracZ_offset_split`; brick (b)
`char_offset_split` + `PMF.cexpect_iid_append` + `cond_char_factor` + `dft_cond_density`. The two
halves of C10 now meet. **What remains, hardest-first:**
1. **[THE LAST REAL NOVELTY] Tail factor ⟹ `charFn_decay`.** Reindex the tail character at
   modulus `3^(j+p)` down to the level-`p` Syracuse char at `ξ'` (for high `ξ = 3ʲ·2ˡ·ξ'`,
   `3∤ξ'`), then `charFn_decay` (Prop 1.17, PROVED) bounds it `≤ Cₐ·p⁻ᴬ`. ⚠️ **This is the step
   most likely to be waved through with a plausible-looking cast — the judge will read it against
   pp.28–31, not just check its axioms.** Head factor: norm `≤1`.
2. **osc bound for `condDens`** — the proved general bridge on `condDens j p l`, then the
   high-freq ℓ²-mass count (‖head‖≤1, ‖tail‖≤charFn bound).
3. **Conditioning events + reassembly** ((6.2)–(6.10): stopping time `k`, E/Eₖ/Bₖ/Cₖ,ₗ, union over
   `k,l`, triangle ineq). Decompose into named `sorry`s as you build. Plan: `PENDING_WORK.md`.

### Two judge items (pass 27)
- 🟡 **Pin C8 (§5) before any C9 work starts.** It is the last un-pinned node, and C9
  `stabilization` lives in §5 directly downstream of C10. Mark `RATIFY-C8` in a comment + say so
  in the handoff; **never set `\leanok` yourself** — ratification is the judge's.
- 🗂️ **The `ManyTriangles` split is DROPPED from the directive.** It has been ordered and skipped
  for **eight consecutive laps** — correctly, every time, because a crux always outranks hygiene.
  Re-ordering it a ninth time would be a fake order. It is off the critical path, it is pure
  hygiene, and splitting a 5,519-line file that holds the X9/X10 pins *during* the crux is churn
  we do not want. It moves to post-§6 mop-up, batched with the 8 new `mul_le_mul_left'`
  deprecations in `Case3.lean`. **Do not spend crux laps on it.**

### Forbidden drift
- **Do NOT retreat to C9 `stabilization` as "easier"** — it is downstream of C10 and would only
  cite it as a sorry. C10 first. (If genuinely blocked on C10 after real attempts, DECOMPOSE it
  into named sub-`sorry`s in `src/` — that is progress — not switch nodes.)
- **Do NOT touch the two `Statement.lean` headline sorries** (hard rail 2) — they discharge only
  when the whole chain C10→C9→C6 lands.
- **Do NOT resurrect the refuted raw-syracZ CS route** — conditioning is mandatory.
- **Do NOT edit any ratified §7 pin** (hard rail 6) — §7 is frozen and clean; leave it be.

### Why
§7 was the campaign's concentrated risk and it is discharged clean. What remains is the §6/§5
analytic assembly over machinery that is *already proved*. Driving C10 → C9 → the C6→headline
wiring is the last mile. No route trigger has fired; route = CONTINUE.

### Directive history (this section's entries; full campaign history below under SUPERSEDED)
- **review lap (2026-07-15, `fef0c38`)**: route CONTINUE, no trigger fired. Inventory kernel-verified: C8
  `first_passage_approx` down to ONE sorry (5.17 reverse leg); `passtime_window_inner`+forward leg CLOSED.
  Objective NARROWED to `steppedMid_le_firstPassMid_add`; recorded the CaseA(exact)/CaseB(early-return)
  split + roadmap correction (handoff step 2b's "approx_passtime_window covers it" is FALSE for returns
  with `T_x N ∈ Iy`). Mandated: prove Case A (`approx_good_tuple_whp`), isolate Case B as a named sorry.
- **review lap (2026-07-14, `810518b`)**: route CONTINUE, no trigger fired. **C7 (obj 3) PROVED +
  axiom-clean** (`first_passage_nonescape` = trust base; integral test + `valSum_lower_tail` closed
  by the grind laps since `e0913ce`). Objectives 1/2/3 all DONE. Live target advances to the
  **C8-close** leg; mandated hardest-first target = the C8 assembly's Lemma-2.1 affine reindexing
  (the only piece that can falsify the pinned `approxMainTerm`), the two whp sub-lemmas after. STATUS
  + PENDING refreshed; C8 attack plan at PENDING top.
- **review lap (2026-07-14, `e0913ce`)**: route CONTINUE, no trigger fired. Pass-29 obj 1 (C10) +
  obj 2 (C8 pin) VERIFIED DONE (C10 chain re-run axiom-clean); frontier now C7's 2 sub-sorries.
  **Key reframe**: the C7 crux `integral_test_logUnif` is the ELEMENTARY integral test (AP-count
  `CardIntervalMod` + `SumIntegralComparisons` + `integral_inv`), NOT the from-scratch dynamical
  equidistribution the 2130 handoff feared. Mandated next move = attack the integral test FIRST
  (hardest-first), not the downstream mechanical `valSum_lower_tail`. STATUS + PENDING refreshed.
- **review lap (2026-07-15, `4eabb35`)**: route CONTINUE, no trigger fired; **T3 DE-RISKED** — the
  reflection's route-decisive window kernel `fnat_lt_of_suffix_window` + the collision bound
  `tailDensW_le_single_mass` landed machine-checked/axiom-clean (obl-3 analytic content DONE). Frontier
  advanced from "window kernel" to "the ASSEMBLY": next = finish windowed obl-3 plumbing, THEN decompose
  `fine_scale_mixing` into named obl-0/1/2/3 sub-sorries defining the events (obl 1). Ledger re-run clean.
- **deep reflection (2026-07-14, `f96a728`)**: route CONTINUE; obligation-3 attack line
  REFUTED (per-prefix hypothesis false at m=0 in-regime) and re-aimed at the suffix-form
  window kernel with the TIGHT l-window (paper's (6.8) shown too lossy — JUDGE-FLAG); obligation
  0 (regime telescope) added to the dashboard; triggers T3/T4 registered; ledger re-run clean.
- **review lap (2026-07-14)**: §7 CROSSED — X8/X9/X10/X11 all axiom-clean; `prop_7_8`+chain clean;
  Judge Pass 26 (§7) FULFILLED and retired. Frontier → C10 `fine_scale_mixing` (Prop 1.14, §6)
  via the fruit-8 conditioning route; C9 downstream; no trigger fired.

---

## SUPERSEDED — JUDGE PASS 26 (2026-07-14, §7 objectives — FULFILLED & retired; §7 now axiom-clean)

**Last night's work is ACCEPTED and it was excellent.** Judge-dated `#print axioms`
(worktree pinned at `61f8e80`): **20 decls exactly `[propext, Classical.choice, Quot.sound]`**
— the whole X11a/X11c/X11d machinery, plus 🏆 **X8 / Case-2 JUDGE-VERIFIED COMPLETE**
(`Q_black_edge_case2`, `fpDist_white_exit`, `fpDist_edgeWeight_le`, `fpDist_fst_mgf_le`).
Sorries **14 → 11**; the §7 crux collapsed **5 → 2**. Hard rails 2/3/4 honored.

### 🎯 THREE OBJECTIVES, IN ORDER. Objective 3 is an ORDER, not a fallback.

**1. Close the two remaining §7 sorries** (both `Case3.lean`) — the prize.
   - `few_white_mass_le` (7.56) — you are mid-flight: **E∗ term, then the assembly**,
     exactly as HANDOFF-h steps 3–5. `col_tail_mass_le` is its bad-column term (move it
     *above* `few_white_mass_le` in the file first — it doesn't depend on it).
   - `col_tail_mass_le` — standard Gaussian tail via `fpDist_walk_eq_fpDistPlus` →
     `fpDistPlus_col_tail` → `exp_neg_mul_le_of_large`.
   - When both land: `Q_black_edge_case3 → Q_black_edge → prop_7_8` go axiom-clean and
     **§7 monotonicity is DONE**. That is the campaign's spine.

**2. The X10/X10a repair** (the `*_rpow` split, spelled out below). One lap, mechanical.

**3. 🗂️ THEN BURN DOWN THE FRUIT — do NOT stop when 1+2 land, and do NOT idle.**
   Last night this list was buried in an "unstick ladder" and a never-stuck box correctly
   never reached it, so **none of it got done**. It is now a first-class objective:
   - **The `ManyTriangles.lean` split** (5,063 lines; queued **six laps** now). Pure moves,
     names verbatim, thin re-export shim. Zero mathematical risk. Do it.
   - **The 7 spine stubs**: `Syracuse/SyracRV.lean` (3), `Sec5/FirstPassage.lean` (2),
     `Sec6/MixingFromDecay.lean` (1), `Basic/Collatz.lean` (1). Downstream and cheap.
   - **Pin C8** (§5 first-passage — the last un-pinned node). A NEW pin is a **claim, not a
     fact**: mark it `RATIFY-C8` in a comment, say so in the handoff, never `\leanok` it.
   **Also reach for objective 3 whenever you are stuck on 1** (see the unstick rule below).
   A night that closes §7 *and* clears the fruit is the best night this campaign can have.

### 🚨 ONE FINDING — `61f8e80` edited FOUR ratified statements. Ratifications REVOKED.

`61f8e80` swapped the deep hypothesis `m/log²m < s` → `(depth)^0.8 < s` in
`triangle_encounter_le` (**X10 = the paper's Lemma 7.10**), `encounter_apex_proximity`
(**X10a**, ratified vs p.53), `bigTriangle_walk_le`, and `estar_union_le`.

**The route reasoning was RIGHT and the judge concurs**: the depth-`m+1` mismatch is real,
and the naive Cthr bridge genuinely fails (`x/log²x` increasing + the fractional-part
counterexample — verified). The engines are sound and stay.

**But the commit called it a "generalization," and it is not one.** The two hypotheses are
**incomparable**: `m^0.8 < m/log²m` only for `m ≳ 10^15.5`. Below that the new hypothesis is
*stronger*, so the new theorem covers **fewer** `s` — a silent restriction. And
Tao p.51 states Lemma 7.10 with **`s > m/log²m`** verbatim; the old pin rendered it exactly.
**X10 no longer formalizes Lemma 7.10**, so its blueprint binding is now false.

### ✅ THE REPAIR (mandated, and it costs almost nothing — do it in the NEXT lap)

Do **not** revert the engines. **Split** — keep both, and you gain a stronger engine *and* a
faithful Lemma 7.10:

1. **Rename** the four new `(depth)^0.8`-hypothesis lemmas to `*_rpow`
   (`triangle_encounter_le_rpow`, `encounter_apex_proximity_rpow`, `bigTriangle_walk_le_rpow`,
   `estar_union_le_rpow`). Proofs unchanged — all four are verified clean. The Case-3 chain
   keeps consuming these. This is the engine layer.
2. **RESTORE** `triangle_encounter_le` and `encounter_apex_proximity` with their
   **character-identical `e08871e` statements** (the `m/log²m < s` pins). These are X10/X10a,
   the blueprint's Lemma 7.10 / (7.63)–(7.65). Prove each as a thin **corollary of the `_rpow`
   engine**, by case split on `m`:
   - **`m ≥ 10^27`**: `log_sq_le_rpow` (already proved, `ManyTriangles:4598`) gives
     `log²m ≤ m^0.2`, hence `m^0.8 ≤ m/log²m < s` → apply the engine.
   - **`m < 10^27`**: the bound is **trivial**. LHS is a sub-probability `≤ 1`; RHS is
     `C·A²·(1+p)/s'` with `1 ≤ s' ≤ m^0.4 < 10^10.8` and `A ≥ A₀ ≥ 1` — so take
     `C := max(C_engine, 10^11)` and RHS `≥ 1 ≥` LHS.
   (If a corollary fights you, the fallback is to restore the deleted `e08871e` proof verbatim
   — it is proved code. Either way the judge's differ must report **byte-identity** with
   `e08871e`, which is what re-ratifies X10/X10a.)
3. **Thread `Cthr ≥ 10^27`** in `few_white_mass_le` / `col_tail_mass_le` so the depth-`m+1`
   bridge `(m+1)^0.8 ≤ 2·m^0.8 ≤ m/log²m < s` actually closes. It has ~65× slack at `10^27` —
   but it is **still unproved**, living inside the two sorries. It is a demand, not a freebie.

### 🚨 NEW HARD RAIL 6 — ratified pins are IMMUTABLE without a judge flag

The old rail said "never **weaken** a statement." That was not enough: this lap believed it was
*strengthening*, and shipped anyway. The rail is now:

> **Never EDIT the statement of a ratified pin — not to weaken it, not to strengthen it, not to
> generalize it.** If a pin blocks your route, you **STOP and FLAG THE JUDGE** (write the
> obstruction in your handoff + `PENDING_WORK.md` and move to another target). Adding a NEW
> lemma beside the pin is always allowed; **changing the pin is the judge's call alone.**

You already have this instinct — HANDOFF-g said *"FLAG for judge (do NOT weaken —
`Q_black_edge_case3` is frozen)"* and you honored it for small-A. Ratified pins get the same
protection as `Q_black_edge_case3`. **The current pinned set** (a statement edit to ANY of these
revokes its ratification): `black`, `epsBW`, `black_structure`, `white_gap_above_run_top`,
`fpDist_white_exit_deep`, `fpDist_any_triangle_le`, `fpDist_out_of_strip_le`,
`fpDist_any_triangle_le_of_localization_box`, `triangle_encounter_le`,
`encounter_apex_proximity`, `fpDist_edgeWeight_le`, `fpDist_white_exit`, `Q_black_edge_case2`,
`Q_black_edge_case3`, `Q_black_edge`, `prop_7_8`, + `Statement.lean`'s two headlines.

*(Relocating a pin across files is fine — `fpDist_white_exit` and `Q_black_edge_case2` moved to
`BlackEdgeQ.lean` this range and the judge confirmed both **character-identical**. Moves are
free; edits are not.)*

### Nits (box's, mop up when passing — zero soundness impact)
- 7 local `maxHeartbeats` bumps in Sec7 (3 new this range) lack the SKELETON-SPEC
  `-- HEARTBEAT:` justification comment.
- Report axiom evidence as *"believed clean, judge to verify"* — `61f8e80` asserted
  "All axiom-clean" flatly. (It was right, every time. Keep the hedge anyway.)

---

## SUPERSEDED — review lap, 2026-07-14 (under judge pass 25)

**✅ X8 / Case-2 IS NOW COMPLETE AND axiom-clean.** Both kernels
(`fpDist_edgeWeight_le`, `fpDist_white_exit`) AND the assembly `Q_black_edge_case2` all
verify `[propext, Classical.choice, Quot.sound]` (review-lap `#print axioms`, judge to
ratify). X9 (`many_triangles_white`) and X10 (`triangle_encounter_le`) remain done and
clean. **The §7 monotonicity chain now hinges on EXACTLY ONE sorry:** X11
`Q_black_edge_case3` (`Case3.lean:1062`) — confirmed sole `sorryAx` carrier under
`prop_7_8`. Do not re-open X8/X9/X10.

**THE objective now**: **close X11 `Q_black_edge_case3`** — the (7.53)–(7.67) Case-3
chain, `m/log²m < s ≤ O(m)`. The moment it lands, `Q_black_edge → prop_7_8 →
Q_polynomial_decay` (all DI-assembled in `Case3.lean`) go axiom-clean and §7 monotonicity
is done. The campaign has always rated this *precedented volume, not novelty*.

**Mandated next move** (hardest-first, in order — full attack in PENDING_WORK.md top):
1. **X11a `estar_union_le`** (NEXT): sum the proved per-`p` `bigTriangle_walk_le` over
   `p ∈ range(T+1)` at `s'=⌈4^A(1+p)³⌉`. Two analytic facts: (a) `Σ_p (1+p)^{-2} ≤ 2`
   (telescoping) for the `1/s'` terms; (b) geometric `Σ_p exp(−c·A²(1+p))` + the
   comparison `exp(−cA²) ≤ const·A²·4^{-A}` for `A ≥ A₀`. Net E∗-mass `≤ C'·A²·4^{-A}`.
2. **X11c `few_whites_le`**: `fstar_markov` (✓) + `deterministic_encounter_claim` (✓);
   `K=⌈10A/epsBW³⌉`, `R:=⌈(K+(A+3)log10+2)/ε⌉`, {reaches R} ⊆ F∗ via `encFold_banked_le`.
3. **X11d body** = `Q_black_edge_case3`: `Q_le_damped_iter` + (7.54) col split + few-white
   damping + X11a + X11c. Handle the two reconciliations (phase −1 shift; ceil vs strict).

All three X11 bridges (`fstar_markov`, `fpDist_walk_eq_fpDistPlus`, `bigTriangle_walk_le`)
are proved and axiom-clean, so X11a is "just" summation. Do NOT retreat to the
`ManyTriangles` split or spine stubs while X11a is the live crux — decompose X11 further
(rule 1) before dropping altitude.

## 🌙 UNATTENDED / OVERNIGHT RUN — NO JUDGE IS AWAKE (2026-07-14, ~03:10 → ~10:10)

**The judge will not look in for ~7 hours.** Nobody will unblock you, re-rule, or
redirect. Two consequences, and they pull in opposite directions — respect both.

### 🔓 NEVER IDLE, NEVER SPIN — the unstick ladder
**Overnight, grinding down ANY sorry is acceptable progress.** The objective order above
is a *preference*, not a cage. If you are stuck, you are **required** to move, in this
order:

1. **Decompose.** Can't prove the target as stated? Split it into named sub-lemmas with
   their own `sorry`s and prove the ones you can. **Raising the sorry count this way is
   PROGRESS, not regress** — it converts one opaque wall into named, attackable pieces,
   and it is exactly how `fpDist_any_triangle_le` and the whole X11d chain fell.
2. **Do objective 2** (the X10/X10a repair — mechanical, always available).
3. **Do objective 3** (the split → the 7 spine stubs → pin C8). **This is real work, not a
   consolation prize.** Last night the fruit sat untouched because it was written as a
   fallback and you were never stuck. It is now an objective in its own right.

**Two sustained failed attempts on one target = move.** Do not spend the night on a
single wall.

### 🚨 HARD RAILS — the things no lap may do, awake or asleep
These are the failure modes the judge exists to catch, and tonight the judge is asleep.

1. **NEVER weaken a statement to make it provable.** If a statement will not yield,
   **decompose it (rule 1) or leave it sorried** — do NOT add a hypothesis, narrow a
   quantifier, shrink a bound, or "adjust" a constant to get green. A `sorry` is honest;
   a weakened theorem is a **lie that compiles**.
2. **NEVER touch `Statement.lean`'s two sorries.** They are `tao_collatz` and
   `tao_collatz_quantitative` — the headline theorems themselves. They discharge when the
   whole chain lands, and not one minute before. They are the trusted base.
3. **NEVER clear a crux sorry by parking it in `wip/`.** The completion gate is cleared by
   PROVING. Parking is fabricated progress.
4. **`epsBW` is FROZEN at `1/10^1000`** — the judge's constant. Do not touch it; the
   ε-sweep tripwire is RE-ARMED and any change fires a full re-ratification.
5. **Do not claim a node "COMPLETE" or "verified".** You may report `#print axioms` output
   as *evidence*; the judge's dated run is what makes it true. Write "believed clean,
   judge to verify."
6. 🔒 **NEVER EDIT A RATIFIED PIN — not to weaken it, not to strengthen it, not to
   generalize it.** ⚠️ **This is the rail that failed last night, so read it twice.**

   Rail 1 said "never *weaken*." Lap 8 hit a real obstruction, concluded it was
   *generalizing* (its commit message says so), and rewrote the deep hypothesis of **four
   ratified statements** — including `triangle_encounter_le`, which **is** Tao's Lemma 7.10.
   It was not a generalization: `m^0.8 < s` and `m/log²m < s` are **incomparable**
   (they cross at `m ≈ 10^15.5`), so the "weaker" hypothesis silently covered **fewer** `s`,
   and the node stopped rendering the paper's lemma. **The build stayed green. The axioms
   stayed clean. The sorry census never moved.** Nothing but a statement character-diff
   could see it. Two ratifications were revoked.

   **So: a ratified pin is as frozen as `Q_black_edge_case3`.** The pinned set —

   `black`, `epsBW`, `black_structure`, `white_gap_above_run_top`, `fpDist_white_exit_deep`,
   `fpDist_any_triangle_le`, `fpDist_out_of_strip_le`,
   `fpDist_any_triangle_le_of_localization_box`, `many_triangles_white`,
   `triangle_encounter_le`, `encounter_apex_proximity`, `fpDist_edgeWeight_le`,
   `fpDist_white_exit`, `Q_black_edge_case2`, `Q_black_edge_case3`, `Q_black_edge`,
   `prop_7_8`, + `Statement.lean`'s two headlines.

   **✅ ALWAYS ALLOWED**: adding a NEW lemma beside a pin (a `*_rpow` engine, a variant, a
   corollary) and routing your proof through it. That is exactly the right move and it is
   what last night *should* have done.

   **🛑 WHEN A PIN BLOCKS YOU AND NO JUDGE IS AWAKE** — this is the whole protocol:
   1. **Do not edit it.** Not even if you are certain the edit is a strengthening.
   2. Write the obstruction in `PENDING_WORK.md` + your handoff, headed **`JUDGE-FLAG:`**,
      with the exact statement, why it blocks you, and your proposed fix.
   3. **MOVE to another target** (unstick ladder → objective 2 → objective 3).
   The judge reads `JUDGE-FLAG:` first thing and rules. You already have this instinct —
   HANDOFF-g wrote *"FLAG for judge (do NOT weaken — `Q_black_edge_case3` is frozen)"* and
   you honored it for the small-A problem. **Ratified pins get that same protection.**
   Relocating a pin across files is fine (moves are free); editing its text is not.

### Standing constraints (unchanged)
- `native_decide` is permitted as scaffolding but tag it `-- NATIVE_DECIDE:`; a decl whose
  trail contains it does **not** count as judge-verified and must be discharged before
  publication. Prefer `decide +kernel`. (It has been needed exactly zero times so far.)
- New `set_option exponentiation.threshold 3000` is expected in ε-touching files (Lean
  refuses `10^1000` otherwise). That option is justified; do not remove it.
- Local `maxHeartbeats` bumps need a `-- HEARTBEAT:` justification comment.
- Commit green, commit often. A lap that ends with uncommitted work has thrown it away.

**Why**: with X9 and X10 both closed, every remaining §7 sorry is assembly over proved
machinery. The campaign's risk is no longer concentrated in a kernel — it is now volume.

### Route-level triggers / abort conditions
- **T1 (7.9 encoding)**: if the stopping-time expectation (7.57) provably CANNOT be
  finitized to a recursion without an infinite-product measure (i.e. D1 must be
  broken), that is a route-level finding → write `ROUTE-ESCALATION-<date>.md`,
  do NOT silently import measure theory.
- **T2 (7.10 separation)**: ~~ε = 10⁻⁴ too weak~~ **FIRED TWICE AND RESOLVED.** ε was
  shrunk 10⁻⁴ → 10⁻⁹⁰ (altitude ruling, pass 23) → **10⁻¹⁰⁰⁰** (judge pass 25), and both
  the real Lemma-7.4 separation and the X6 localization box are now proved against it
  (`sep = 100·ln10 ≈ 230.26` vs box `≈ 158.4`). The trigger stands re-armed for any
  FUTURE ε change: shrinking `epsBW` fires a full ε-sweep re-ratification (judge's).
- **T5 (C8 reindex faithfulness)**: FIRED 2026-07-15 — the `approxMainTerm` pin over the ℕ-truncating
  `Aff` over-counts (5.8) (numeric+source; `truncation_error_bound` false). Route stays CONTINUE via
  the **guarded re-pin** (RATIFY-C8-v2, mandated above), NOT a full escalation — the destination and
  the `C10→C8→C7→C8→C9` order are intact; only the C8 reindex mechanism changes. Re-arm: if the guarded
  re-pin does NOT yield an EXACT (Lemma-2.1) reindex — i.e. `approxMainTerm = steppedMid` up to genuine
  (5.19) value-rounding does not go through in Lean within ~6 grind laps — that is a deeper §5 problem
  → write `ROUTE-ESCALATION-<date>.md` and re-cost §5.

### Directive history
- **review lap (2026-07-15, `5514f13`)**: route CONTINUE, no trigger fired (T5 RESOLVED — C8 re-pin
  yielded the exact reindex; C8 now CLOSED). Kernel-verified: build green (3324), 6 sorries + 0 orange
  (4 C9 holes in `Stabilization.lean` + 2 headline stubs). C8's reverse leg landed (early-return event
  proved empty, `0bea9d1`); C9's `perNTerm_eval` PROVED from 2 sub-sorries, isolating C10 to one hole.
  **Directive retargeted from C8's (closed) reverse leg to C9's `harmonic_to_Z` (the C10 seam, 5.20) —
  hardest-first.** Mandated the B1 (geomHalf→syracZ reindex) / B2 (fine_scale_mixing scale bridge)
  decomposition; forbade dropping to the 3 tractable C9 leaves first. STATUS + PENDING refreshed.
- **deep reflection (2026-07-15, `95436f9`)**: route CONTINUE-with-correction; **T5 FIRED** — caught a
  false summit: the ratified `approxMainTerm` uses the ℕ-truncating `Aff` unguarded, so
  `truncation_error_bound` is FALSE (source pp.22–25 + `tao_c8_truncation_probe.py`). Directive: RE-PIN
  `approxMainTerm` with the (5.18) divisibility guard (RATIFY-C8-v2), delete `truncation_error_bound`,
  re-wire onto the exact Lemma-2.1 reindex; parallel-safe = `passtime_window_inner`. C10/C7 re-verified
  axiom-clean. Lit-review §5 written (was absent). STATUS + PENDING refreshed.
- **review lap (2026-07-14)**: X8/Case-2 COMPLETE + axiom-clean; §7 chain now hinges on
  the single sorry X11 `Q_black_edge_case3`. All 3 X11 bridges proved. Directive narrows
  to closing X11 via X11a → X11c → X11d; no drop to the ManyTriangles split / spine stubs
  while X11a is live. Within judge pass 25's Case-2/Case-3 objective (not a destination change).
- **judge pass 25 (2026-07-13)**: X9 COMPLETE — both pinnacle kernels done;
  directive moves to the Case-2/Case-3 assembly. Supersedes the pass-24
  directive, which is FULFILLED (B=64, Y=150, epsBW=10⁻¹⁰⁰⁰, ε-sweep clean).
- **judge pass 24 (2026-07-13)**: second escalation DOWNGRADED (not altitude-class);
  gate on `fpDist_any_triangle_le` LIFTED; objective = make `B` and `Y` explicit.
  Supersedes the lap-56 directive below (written in the ε=10⁻⁴ era, before the
  altitude ruling froze `epsBW = 10⁻⁹⁰` and before X9/X10 closed).
- lap 56 (2026-07-12, review): X9 `many_triangles_white` verified CLOSED modulo
  exactly `fpDist_white_exit_deep` (`#print axioms` = trust base + `sorryAx`);
  promote the shared white-exit kernel to THE active move (steps 1–2 of lap-55
  done); route CONTINUE, no trigger fired.
- lap 55 (2026-07-12, deep reflection): RED→YELLOW phase done (C8 excepted) —
  pivot to closing X9 (near-edge depth-gate fix first; statement-truth risk),
  then white-exit kernel (merged twins), then X10 assembly. T1 cleared, T2
  source-grounded unlikely; route CONTINUE.
- lap 51 (2026-07-12): set — de-risk §7 tail; pin Lemma 7.10 then design/pin 7.9;
  X8 relegated to finish-when-downhill. (Prev grind laps had X8-completion momentum
  from the lap-50 handoff; corrected to breadth-first per BLUEPRINT §2.)

---

## Standing charter (destination — change only if the target itself changes)

**Target**: first-anywhere full Lean 4 formalization of Tao 2019 Theorem 1.3
(arXiv:1909.03562v5), `#print axioms` = exactly `[propext, Classical.choice,
Quot.sound]`, zero sorries. Source of truth = the paper PDF; statements are
copy-not-compose (ratify verbatim against the cited equation, then freeze).

**Critical path**: `S3 → X6 → {X8, X10} → X11 → C10 → C9 → C6 → Statement`.
Risk concentration = the §7 crux (X8/X10/X11, "the paper's pinnacle", 65–75%);
everything outside it is standard treadmill fare (75–95%).

**Campaign steering rule (BLUEPRINT §2)**: de-risk breadth-first — turn RED nodes
YELLOW (pinned + routed + hardest sub-lemma probed) everywhere before polishing
yellow → green; completion polish last. Carve-outs: (a) dependency order gates
assessability; (b) finish-when-downhill — a mid-flight node ≤ a few laps from done
gets finished (a completed axiom-clean proof is ground truth that re-rates
neighbors).

**Design invariants** (BLUEPRINT §0): D1 PMF+tsum, no measure theory · D2 ℤ[1/2]
eliminated via `Fnat` · D3 asymptotics = explicit ∃-constants, no filters/IsBigO ·
D4 ε := 10⁻⁴ fixed · D5 Lemma 2.2 via tilting+circle-method (done) · D6 §7 renewal
finitized to recursions over an explicit measure, not stopping-time measure theory.

**Pointers**: STATUS.md (living overview) · newest `HANDOFF-*.md` (per-lap baton) ·
PENDING_WORK.md (open-items + attack paths) · BLUEPRINT.md (frozen node ledger).
