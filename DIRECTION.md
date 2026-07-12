# DIRECTION — tao-collatz 🧭

*Altitude laps (review/reflection) are the ONLY writers of the CURRENT DIRECTIVE
section. Grind laps READ and OBEY it; it OUTRANKS the HANDOFF. Keep it short —
detail lives in PENDING_WORK.md.*

---

## CURRENT DIRECTIVE (lap 51 review, 2026-07-12)

**THE objective**: de-risk the §7 crux TAIL (X9 Lemma 7.9, X10 Lemma 7.10) by
turning it from RED → YELLOW — statement pinned against the paper + route
validated + hardest sub-step probed. This is the last un-pinned stretch on the
critical path `S3✓ → X6✓ → {X8, X10} → X11 → C10 → …`.

**Mandated next move** (in order):
1. **Pin Lemma 7.10 (X10), (7.60)** — the campaign's single highest-uncertainty
   node (diff 5, conf 65%). It is DIRECTLY expressible: its event `E_{p,s'}` is a
   *single-marginal* probability of the renewal endpoint `(j,l)+v_{[1,k+p]}`,
   whose law is `fpDist s` convolved with `iidSum hold p` — NO path-space needed.
   Pin `P(E_{p,s'}) ≤ C·A²(1+p)/s' + C·exp(-c·A²(1+p))` with a (7.60)–(7.65)
   route docstring. Probe the hardest sub-step (the ≫s'-separated Σ counting,
   (7.63)–(7.65)).
2. **Design + pin Lemma 7.9 (X9), (7.57)** — needs the stopping-time renewal
   expectation as a RECURSION on R (D1 forbids measure theory; D6 finitizes to a
   recursion over `fpDist`/`Q`). Record the encoding design in PENDING_WORK first;
   pin only a FAITHFUL statement (copy-not-compose — an unfaithful pin is worse
   than none).

**Forbidden drift**:
- Do NOT grind X8's Case-2 kernels (`fpDist_edgeWeight_le`, `fpDist_white_exit`)
  or the Case-2/3 assembly to completion. X8 is already YELLOW (pinned + routed,
  kernels unblocked by X6). It is *finish-when-downhill secondary* only — touch it
  only if a kernel is clearly ≤1 lap AND X9/X10 pinning is already done this lap.
- Do NOT sink the lap into off-§7 leaves (SyracRV / ValuationDist / Basic /
  Statement / Sec5/Sec6 stubs). Those are downstream of the crux and cheap later.

**Why**: the expedition verdict is binary (full-discharge-or-abandon), so laps buy
the most by reducing the odds of a LATE FATAL WALL. X10 is the likeliest such wall
(the paper's pinnacle, "separated-Σ counting"). The decisive unknown for the whole
Case-3 subtree (X9/X10/X11) is whether the paper's stopping-time/renewal-process
arguments survive the D1-no-measure-theory + D6-finitization translation. Pinning
+ probing 7.9/7.10 tests exactly that, and is worth more than completing an already
de-risked X8. A fired route-trigger (see below) means ESCALATE, not grind.

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
