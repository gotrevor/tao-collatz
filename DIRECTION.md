# DIRECTION — tao-collatz 🧭

*Altitude laps (review/reflection) are the ONLY writers of the CURRENT DIRECTIVE
section. Grind laps READ and OBEY it; it OUTRANKS the HANDOFF. Keep it short —
detail lives in PENDING_WORK.md.*

---

## CURRENT DIRECTIVE (lap 56 review, 2026-07-12)

**THE objective**: prove the **white-exit kernel** `fpDist_white_exit_deep` —
now X9's ONLY open input (`many_triangles_white` verified closed modulo exactly
it, `#print axioms` = trust base + `sorryAx` via that one sorry) AND the geometry
shared by X8's Case-2 twin `fpDist_white_exit`. This is the route-decisive
blocker: if `p₀ > 1/2` cannot be certified through X6's constants vs the
ε=10⁻⁴ separation, the ∃C fallback re-pin is forced (a redesign), so it is
hardest-first. Steps 1–2 of the lap-55 directive (depth gate, close
`many_triangles_white`) are DONE.

**Mandated next move** (in order):
1. **`fpDist_white_exit_deep`** (THE active move). Prove it GENERAL, then DERIVE
   X8's `fpDist_white_exit` from it (kernel merge — the Case-2 budget hypothesis
   `s ≤ m/log²m` is used downstream ONLY for `edgeWeight`, per the docstring).
   Route (both twins share it): Lemma 7.7 `fpDist_location_bound` (X6, PROVED)
   concentrates the endpoint at `(j+s/4+O(√(1+s)), l_Δ+O(1))`;
   `fpDist_support_snd_gt` clears the triangle top; (7.11) slope + X3
   `apex_separation` exclude every other triangle → white; in-strip since
   `s/4+O(√s) ≪ m`. Decompose into named sub-`sorry`s in `src/` (support-clears,
   slope-excludes-others, in-strip, mass≥p₀) — that RAISES the src count and is
   the progress. If certifying `p₀ > 1/2` through X6's constants fights, any
   explicit `c₀ > ~ε` suffices (chain value `exp(O(ε/c₀))` consumable) — weaken
   the pin, don't stall; but the deep variant is pinned at 1/2 for the chain cap
   `encChainX_le_exp`, so the weakening propagates to `many_triangles_white`.
2. **X10 assembly** (`triangle_encounter_le`): FIRST name and prove the
   fpDistPlus location bound (Lemma 7.7 ⋆ p iid Hold steps); then E′ tails
   (X6+S3 applications); then the separated-Σ mass sum (existing Gaussian-AP
   engine + proved `apex_separation`).
3. **X8/X11 assembly**: `Q_black_edge_case2` (mechanical once both kernels land),
   then `fpDist_edgeWeight_le`, then `Q_black_edge_case3` (X11 (7.53)–(7.67)).

**Forbidden drift**:
- No spine leaves (SyracRV / ValuationDist / Basic / Statement / Sec5 / Sec6 /
  Prob stubs) — downstream, cheap later.
- No `fpDist_edgeWeight_le` grinding before the white-exit twins land (Case-2-only,
  not route-decisive).
- C8 pinning is allowed as statement-work variety, at most one lap, never
  displacing steps 1–3.

**Why**: the reflection's ground-truth read (pp.49–55 + the compiler) shows the
remaining §7 risk is concentrated in (a) the X9 near-edge statement question —
the only place a ratified pin might be *false*, hence fix-first — and (b) the
white-exit kernel shared by X9/X8. X10, previously rated the summit, is
precedented volume (conf ~78%): its geometric core and analytic engines are
already proved. Closing X9 whole re-rates the entire Case-3 subtree with ground
truth.

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
