# DIRECTION — tao-collatz 🧭

*The **JUDGE** and altitude laps (review/reflection) are the only writers of the
CURRENT DIRECTIVE section; the judge outranks a review lap. Grind laps READ and
OBEY it; **it OUTRANKS the HANDOFF**. Keep it short — detail lives in
PENDING_WORK.md and the judge pass records (`judge/pass-NN.md`).*

---

## CURRENT DIRECTIVE (judge pass 24, 2026-07-13)

**THE objective**: close the X9 white-exit kernel by making **two throwaway
constants explicit**. `fpDist_white_exit_deep` is X9's only open input, and it now
reduces (already proved: `fpDist_any_triangle_le_of_localization_box`) to ONE
inequality — `√(X²+Y²) < sep`, with `sep = (1/10)·ln(1/epsBW) = 9·ln10 ≈ 20.72`
and `X = ⌈(5Y+B)/16⌉`.

**⛔→✅ THE ESCALATION GATE IS LIFTED.** Any doc telling you
`fpDist_any_triangle_le` is "ESCALATION-GATED, do not touch"
(`HANDOFF-2026-07-13-d.md`) or describing a live route crisis
(`ROUTE-ESCALATION-2026-07-13.md`) is **superseded**. Judge pass 24 re-read the
paper's p.48 localization argument: the route is sound, the committed geometry is
faithful, and the blocker is arithmetic, not mathematics. **Do not re-litigate the
escalation. Do not re-derive the diagnosis.**

**Mandated next move** (in order — full detail in `HANDOFF-2026-07-13-e.md`):
1. **🗂️ The queued `ManyTriangles.lean` split** (BLUEPRINT §2) — pure moves, zero
   statement/proof edits, names verbatim. ~5,200 lines; every edit re-elaborates
   all of it. Overdue; do it first, in a lap of its own.
2. **`B ≈ 42`** — sharpen `fpDist_linear_tail` (`Sec7/FpLocation.lean:366`). It
   ships `B = 4·10⁷` because it bounds the `16j−5l` MGF with a crude *quadratic*
   penalty that near-cancels the −16/step drift, capping the tilt at `1/20000`
   (true ceiling `0.213`). The step law has an **exact** MGF (`geomQuarter` ¼(¾)^{k−1}
   × `pascalNe3`). Keep the lemma's `e^{−θB}·M/(1−M)` shape; only the MGF input
   changes. Any `B ≤ 250` suffices — do not over-optimize.
3. **`Y = 139`** — re-prove `fpDist_height_tail` (`Sec7/ManyTriangles.lean:2522`)
   **OFF X6**. Its radius is *existential* today (it sums X6's envelope, whose
   `(cL,CL)` are `∃`-bound), so the box is not even a number — **this is the real
   blocker**. Do NOT make X6's constants explicit (that re-opens a completed node).
   Use: `fpDist_le_renewal_conv` + **heights strictly increase** (`Δl = 3 + Σv ≥ 3`,
   so each level is visited at most once ⟹ renewal mass per level `≤ 1`, no renewal
   theorem) + `Δl`'s exact MGF.
4. **Close the tail**: with `B`,`Y` numerals, feed `exists_fpDist_localization_box`
   + the box inequality into `fpDist_any_triangle_le_of_localization_box`.

Numerics (targets, not proofs — a Lean proof may ship lossier constants, which is
fine): `tools/tao_linear_tail.py`, `tools/tao_height_tail.py`.

**⚖️ `epsBW` RULING — PRE-AUTHORIZED (judge, 2026-07-13 20:15, after `B = 64` landed).**
`epsBW` is the judge's constant, never a worker's. To keep you from stalling at the Lap-D
gate, the judge issues it now, **conditionally**:

> **`epsBW : ℚ := 1 / 10 ^ 1000`** (`sep = 100·ln 10 ≈ 230.26`) is authorized **iff** the
> constants you have actually PROVED satisfy **`B ≤ 250` and `Y ≤ 200`**. That envelope
> keeps the box `≤ √(79² + 200²) ≈ 215 < 230`, so the inequality closes with margin.

If your proved constants land inside that envelope, execute the change. If **either**
constant lands outside it, **STOP** — do not pick your own numeral, do not "just make ε
smaller." Report the real numbers and the judge re-issues.

Execution rules for the D4-change lap (same doctrine as the first ε ruling):
- **A dedicated lap.** Change the numeral and make ONLY the mechanical numeral repairs
  needed to get the build green. **No route work in that lap** — a mixed lap forfeits the
  judge's cheap sweep verification.
- The judge re-runs the **ε-sweep re-ratification** at the boundary (all seven armed items;
  each was verified monotone-good at smaller ε in pass 23). Expect nothing to break — but
  the sweep is not optional, and `#print axioms` re-runs on X2/X3/X10 are the judge's, not
  yours to claim.
- Do **not** re-open `epsBW` as a parameter — that remedy is ruled out.
- Do **not** introduce a `Real.exp`-valued ε; the frozen rational power of ten is doctrine.
- ⚠️ Downstream note (not your problem now, but do not "helpfully" fix it): Case 3's
  `10A/ε³` and `R = ⌊A²/ε⁴⌋` inflate with the exponent. They are **existential** in every pin
  we hold, so this costs nothing. Leave them existential.

**Forbidden drift**:
- No spine leaves (SyracRV / ValuationDist / Basic / Statement / Sec5 / Sec6 / Prob
  stubs) — downstream, cheap later.
- No edits to pinned/ratified statements. An edit revokes ratification.
- If steps 1–4 are done or blocked, work the BlackEdge crux sorries
  (`fpDist_edgeWeight_le`, `fpDist_white_exit`, `Q_black_edge_case2`) or Case3's
  `Q_black_edge_case3`. Do not idle on the gated tail.

**Why**: X9's kernel is the last route-decisive blocker on Prop 1.17's Case-3 chain
(X10 is complete and axiom-clean). Pass 24 showed the remaining obstruction is two
lossy constants — a `10⁶×` loss in `B`, and an existential `Y` — not a redesign.
Closing it re-rates the whole Case-3 subtree with ground truth.

### Route-level triggers / abort conditions
- **T1 (7.9 encoding)**: if the stopping-time expectation (7.57) provably CANNOT be
  finitized to a recursion without an infinite-product measure (i.e. D1 must be
  broken), that is a route-level finding → write `ROUTE-ESCALATION-<date>.md`,
  do NOT silently import measure theory.
- **T2 (7.10 separation)**: if the fixed `ε = 10⁻⁴` separation constant
  `(1/10)log(1/ε) ≈ 0.92` is too weak to make the ≫s'-separated Σ-sum converge in
  (7.65) at the pinned constants, shrink ε (D4) and re-validate — this touches
  finitely many inequalities, numerics-checkable first.

### Directive history
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
