# DIRECTION — tao-collatz 🧭

*The **JUDGE** and altitude laps (review/reflection) are the only writers of the
CURRENT DIRECTIVE section; the judge outranks a review lap. Grind laps READ and
OBEY it; **it OUTRANKS the HANDOFF**. Keep it short — detail lives in
PENDING_WORK.md and the judge pass records (`judge/pass-NN.md`).*

---

## CURRENT DIRECTIVE (JUDGE PASS 26, 2026-07-14 — supersedes the review-lap directive below)

**The night's work is ACCEPTED on the mathematics and is excellent.** Judge-dated
`#print axioms` (worktree pinned at `61f8e80`): **20 decls exactly
`[propext, Classical.choice, Quot.sound]`** — the whole X11a/X11c/X11d machinery, plus
🏆 **X8 / Case-2 now JUDGE-VERIFIED COMPLETE** (`Q_black_edge_case2`, `fpDist_white_exit`,
`fpDist_edgeWeight_le`, `fpDist_fst_mgf_le` all clean). Sorries **14 → 11**; the §7 crux
collapsed **5 → 2** (`few_white_mass_le`, `col_tail_mass_le`). Hard rails 2/3/4 honored:
`Statement.lean` untouched, `epsBW` frozen, zero `native_decide`, nothing parked in `wip/`.
**Keep going on `few_white_mass_le` — the E∗ term + assembly, exactly as HANDOFF-h step 3.**

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

## 🌙 UNATTENDED / OVERNIGHT RUN — NO JUDGE IS AWAKE (2026-07-13 → 07-14 morning)

**The judge will not look in for ~8 hours.** Nobody will unblock you, re-rule, or
redirect. Two consequences, and they pull in opposite directions — respect both.

### 🔓 NEVER IDLE, NEVER SPIN — the unstick ladder
**Overnight, grinding down ANY sorry is acceptable progress.** The mandated order above
is a *preference*, not a cage. If you are stuck, you are **required** to move, in this
order:

1. **Decompose.** Can't prove the target as stated? Split it into named sub-lemmas with
   their own `sorry`s and prove the ones you can. **Raising the sorry count this way is
   PROGRESS, not regress** — it converts one opaque wall into named, attackable pieces,
   and it is exactly how `fpDist_any_triangle_le` finally fell.
2. **Move down the mandated list** (X8 → X11 → the split).
3. **🗂️ Do the `ManyTriangles` split.** Mechanical, zero-risk, high-payoff, and it has
   been queued for four laps. An unattended night is the *ideal* time for it.
4. **Take a spine stub.** ✅ **The old "no spine leaves" ban is LIFTED for this run.**
   Fair game: `Syracuse/SyracRV.lean` (3), `Sec5/FirstPassage.lean` (2),
   `Sec6/MixingFromDecay.lean` (1), `Basic/Collatz.lean` (1). These are downstream and
   cheap; a night spent clearing them is a night well spent.
5. **Pin C8** (§5 first-passage — the last un-pinned node). Allowed as statement work,
   but a NEW pin is a **claim, not a fact**: mark it `RATIFY-C8` in a comment and say so
   in your handoff. The judge ratifies against pp.22–25. Never mark it `\leanok`.

**Two sustained failed attempts on one target = move.** Do not spend the night on a
single wall.

### 🚨 HARD RAILS — the things no lap may do, awake or asleep
These are the failure modes the judge exists to catch, and tonight the judge is asleep.

1. **NEVER weaken a statement to make it provable.** This is the cardinal sin. If a
   statement will not yield, **decompose it (rule 1) or leave it sorried** — do NOT add a
   hypothesis, narrow a quantifier, shrink a bound, or "adjust" a constant to get green.
   A `sorry` is honest; a weakened theorem is a **lie that compiles**. Any pinned
   statement you edit has its ratification REVOKED and will be reverted.
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

### Directive history
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
