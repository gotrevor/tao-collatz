# DIRECTION — tao-collatz 🧭

*The **JUDGE** and altitude laps (review/reflection) are the only writers of the
CURRENT DIRECTIVE section; the judge outranks a review lap. Grind laps READ and
OBEY it; **it OUTRANKS the HANDOFF**. Keep it short — detail lives in
PENDING_WORK.md and the judge pass records (`judge/pass-NN.md`).*

---

## CURRENT DIRECTIVE (judge pass 25, 2026-07-13)

**✅ THE PREVIOUS DIRECTIVE IS FULFILLED.** X9 / Lemma 7.9 is **COMPLETE and
axiom-clean** — `fpDist_any_triangle_le`, `fpDist_white_exit_deep`, and
`many_triangles_white` all verified `[propext, Classical.choice, Quot.sound]` by dated
judge runs; `ManyTriangles.lean` has **zero sorries**. `B = 64`, `Y = 150`, the box
`√(51²+150²) ≈ 158.4` fits under `sep ≈ 230.26` at `epsBW = 10⁻¹⁰⁰⁰`, and the ε-sweep
re-ratification fired and discharged clean. **Both pinnacle kernels (X9, X10) are done.**
Do not re-open any of it.

**THE objective now**: **the Case-2 / Case-3 assembly** — the last 5 crux sorries, and
the material the campaign has always rated *precedented volume, not novelty*. Prop 1.17
is a theorem over exactly this chain.

**Mandated next move** (in order):
1. **X8 / Case 2** (already in flight — keep going):
   `fpDist_fst_mgf_le` (`BlackEdge.lean:318`, the decomposed core) →
   `fpDist_edgeWeight_le` (341) → `fpDist_white_exit` (369) → `Q_black_edge_case2` (457).
   `fpDist_white_exit` is the **Case-2 twin** of the now-proved deep kernel: same
   geometry, budget hypothesis `s ≤ m/log²m` added. **Derive it from
   `fpDist_white_exit_deep` if you can** — the kernel-merge was always the plan, and the
   deep variant is now a theorem, so this should be much cheaper than it was.
2. **X11 / Case 3**: `Q_black_edge_case3` (`Case3.lean:941`) — the (7.53)–(7.67) chain.
   X9 and X10 are both available and clean, so its two hardest inputs are now ground truth.
3. **🗂️ The `ManyTriangles.lean` split** (BLUEPRINT §2) — **still not done**, now 5,204
   lines, and you have been editing that file anyway, against your own written plan. Pure
   moves, zero statement/proof edits, names verbatim. Take the lap; you are paying for it
   on every elaboration.

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
