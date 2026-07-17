# DIRECTION — big-C campaign 🔢 — **CLOSED 2026-07-17**

*Grind laps READ and OBEY this file; it outranks any handoff. `blueprint_rules.md` remains
BINDING. Predecessor campaign (pin `c`, PR #9, merged): its methods are this campaign's
playbook; its DIRECTION lives in git history (`git log --follow DIRECTION.md`).*

> **🔒 ONE OWNER (judge ruling 2026-07-17, resolving the lap-12 governance conflict).**
> **This file has exactly one writer: the operator/judge layer (host-side).** No lap — grind,
> review, reflection, or altitude — may write DIRECTION.md. The treadmill governor's general
> "altitude laps own DIRECTION.md" rule is **overridden here** and does not apply to this repo.
> A lap that believes the directive is wrong does not rewrite it: it records the argument in
> `PENDING_WORK.md` as a `JUDGE-FLAG:` and **stops the loop with `box stuck`**.
> *Why:* lap 12 rewrote this banner under the governor's rule while the header claimed
> operator-exclusivity — two authority layers in one file resolve to the looser one, so the
> file had no effective owner. Lap 12's content stayed in-lane, but the next such rewrite
> need not. The escape hatch that made lap 12's rewrite feel necessary (operator absent, and
> "chip-never-stop" left no legal way to halt) **now exists and is proven**: `box stuck`
> fired correctly at 06:37 EDT on 2026-07-17. Escalate-and-stop is the lane.

---

## 🟢 JUDGE RULING II (2026-07-17, after the Codex plan) — **SUCCESSOR ACTIVATED: assembled explicit big-C. Launch-ready; Trevor fires.**

**Ruling I (below) closed the route to the *pin* — that stands, unchanged. Ruling I's
"no successor" call was TOO BROAD, and this ruling narrows it.** A peer agent (Codex) read
Ruling I and proposed `BIG_C_EXPLICIT_BOUND_PLAN.md`, correctly separating two objectives
this campaign had conflated:

1. **prove the frozen numeral `CTao = 10^(10¹¹)` bounds the development's constant** —
   obstructed (check19: the assembled constant is a tower; check23(i): architecture-level).
2. **exhibit SOME closed Lean term for the constant and prove the quantitative theorem at
   it**, making *no* smallness claim — **not obstructed by anything in Ruling I.**

Ruling I only weighed **tighten-C** (make the constant *small*) and gated it on check23(i).
That gate is right for tighten-C and **irrelevant to (2)**. Objective (2) is also **not** the
old "Option A" — Option A *re-pinned `CTao`* to a tower (statement surgery on a judge-owned,
comparator-pinned statement, gutting the challenge). This is **additive**: the pin stays
frozen and `sorry`, and a *different* theorem is added at an honestly-assembled constant that
says exactly what has been proved. **Peer review caught what a self-graded campaign could
not — that is the mechanism working.**

### Codex's load-bearing claims, VERIFIED host-side by the judge

- ✅ **The tower route is axiom-clean.** `#print axioms` run this session:
  `renewal_white_encounters_at`, `tao_collatz_quantitative_spine_atC`,
  `tao_syracuse_quantitative_sum_atC`, `tao_collatz_quantitative` — **all exactly
  `[propext, Classical.choice, Quot.sound]`**, no `sorryAx`. The route does **not** depend on
  either live `sorry`. (Codex flagged this "believed clean, judge to verify" — correct hygiene.)
- ✅ **No opaque rate-free leaf on the QUANTITATIVE path.** `Sec5/FirstPassage.lean`,
  `ApproxFormula.lean`, `Stabilization.lean` contain **zero** `Tendsto`. Sec3's 11 `Tendsto`
  all sit in `tao_syracuse` (:1266) and `tao_collatz_spine` (:1773) — the **qualitative**
  theorems, which take an arbitrary `f → ∞` as a *hypothesis* and are correctly rate-free.
  They feed the qualitative headline, **not** the quantitative spine. ⚠️ This is the exact
  failure that killed the C route once before (PR #8: `hold_weight_expect` minting `K`/`T`
  from rate-free limits) — it does **not** recur here.
- ✅ **The witnesses are literally copyable.** `tao_syracuse_quantitative_sum_atC` (:857) sets
  `X := max xw (Real.exp 1)` and `refine ⟨X, ?_⟩`; `tao_collatz_quantitative_spine_atC`
  (:1580) obtains that `X` and passes it straight through. The plan's `X_syrSum := max
  X_windowBad (Real.exp 1)` is a transcription of the source, not a guess.
- ⚠️ **NOT verified — the honest limit of this ruling:** I checked the capstone and the
  Tendsto-freedom of Sec5, **not** each of the ~35 nodes in phases 2–3. Zero `Tendsto` is
  strong evidence every witness is copyable; it is not proof. **The cutoff audit (step 0) is
  the mitigation and it must fail LOUD** on the first node that cannot be made explicit.
  A stall partway is an acceptable outcome — every landed node is permanent value.

### 🚨 Mandatory correction to the plan's step 0 (judge amendment, binding)

**The audit must walk `C_tao_assembled`'s DEFINITIONAL CLOSURE (`Lean.collectAxioms`-style /
`Environment` const traversal) — never grep files.** `Nat.sInf` legitimately appears in
`syrMin` (:53) and `passTime` (:62) — those are the **objects being studied**, in the theorem
*statement*, not in the constant's spine. A file-grep for `sInf` false-positives on them; and
a closure walk **seeded wrong walks nothing and passes green**, which is strictly worse.
📌 This bug is live right now in the public `lean-agent-skills` `comparator-probe`
(seeds empty → "✅" compares zero definitions) — do not reproduce it here. The audit must
**print the closure size it actually walked** and fail if that size is 0 or unchanged after
adding a node.

### The directive

> **CURRENT DIRECTIVE — assembled explicit big-C.** Add an axiom-clean theorem
> `tao_collatz_quantitative_assembled` at the closed constant `C_tao_assembled` specified in
> `BIG_C_EXPLICIT_BOUND_PLAN.md`. Finish the X-chase in manifest order. Use the existing clean
> tower route. **Do not edit the frozen `CTao` pin, do not touch comparator statements, do not
> work on `Q_black_edge_tight`.** The next target is always the first missing entry printed by
> `tools/big_c_cutoff_audit.py`. Done means the plan's complete gate is green and
> `#print axioms tao_collatz_quantitative_assembled` shows only the trust base.
> **The plan's per-commit gates, done condition, and explicitness contract are BINDING**, with
> the step-0 amendment above. `blueprint_rules.md` still binds. **The pin's `sorry` and the
> `Q_black_edge_tight` `sorry` stay isolated and untouched — they are not yours to discharge.**

**Honesty clause (binding, applies to every docstring and report this campaign writes):**
`C_tao_assembled` is a **tower** and is **useless as a number**. It is explicit in the formal
sense only: a closed term with no existential. **Never** describe it as a bound anyone can
evaluate, never compare it to `CTao`, and never imply smallness. The value on offer is
**"effective in fact, kernel-certified"** replacing **"effective in principle"** — that, and
nothing more, is the claim.

**Relaunch gate (CORRECTED against the tool — the first draft of this line invented a flag):**
- ❌ **There is no `--done-when 'cmd:…'` form.** `lean-treadmill --done-when` accepts **only**
  `sorry-free:<path>`, and an unrecognized spec **fails toward running** (never a false halt) —
  so a made-up spec does not error, it *silently never fires*. Do not use one.
- ❌ **`--done-when 'sorry-free:TaoCollatz'` is WRONG here** — the library is sorry-clean **as of
  the pin retirement (0 sorries)**, so it would be met on lap 1 and halt the run instantly. This
  campaign's objective is to **ADD a theorem**, not to remove a `sorry`; no sorry-count predicate
  can express it.
- ✅ **Self-stop cannot fire on this repo, so no `--forever` is needed.** The gate scans
  `src/` if present **else the repo root** (mathlib layout — this repo has no `src/`), and the
  root permanently carries the **8 comparator `Challenge.lean` stubs** (sorry-by-design forever).
  A lap's stop sentinel is therefore never honored.
- ✅ **Keep `box stuck` ALIVE — this is why `--forever` is actively harmful here.** `--forever`
  *declines* the stuck-bail, and escalate-and-stop is the lane this campaign's governance rests
  on (Ruling I). Self-stop is already impossible; `--forever` would buy nothing and cost the exit.
- **The operator stops the run** when `tools/big_c_cutoff_audit.py --complete` goes green (or on
  a `JUDGE-FLAG`). `--max-duration` is the backstop.

---

## 🏁 JUDGE RULING I (2026-07-17 morning) — **the PIN campaign is CLOSED. `CTao` stays `sorry` as a documented open frontier.** *(Stands. Narrowed only by Ruling II above: it closes route (1), not route (2).)*

**The lap-18 campaign-close recommendation is UPHELD — with its evidence grade corrected.**
Verified host-side this session, independently of the box: branch pushed (93 commits,
`fabea6f..5df3106`); all 26 blueprint checks reproduce; `tools/tao_stmt_diff.py fabea6f HEAD`
= **35/35 character-identical** (no watched statement moved in 93 commits — the never-touch-
pins invariant held); `lake build` **green**, exactly 2 src `sorry` (the pin
`Statement.lean:68` + the isolated crux `Bridge.lean:742`), i.e. Option B's scaffold landed
as designed.

**What is upheld:** there is **no viable route** to discharging `CTao = 10^(10¹¹)` over the
frozen §7 statements. Every door this campaign opened is either refuted at its mechanism or
has no mechanism left. Grinding further is waste — **stop.**

**What is corrected — the route map is NOT "machine-checked closed on every branch"**
(PENDING_WORK lap 18). That phrase overstates what the checks do, and the overstatement
compounded across three hops (check print → lap-18 ledger → escalation doc → "campaign
close"), each hop dropping a qualifier. Graded honestly:

| check | what it actually establishes | grade |
|---|---|---|
| 19 (tower) | arithmetic **solid**; scoped correctly (it bounds *this proof's witness*, not every proof's) | ✅ machine-checked |
| 22, 23 | budget/floor arithmetic **solid**; 23(i)'s flat-envelope contradiction is the real structural finding | ✅ machine-checked |
| 24 (shallow tip) | valid — one witness kills a universal ("set-dist grows with size"). Refutes **a route**, not the door | ✅ (route-refutation) |
| 25 (point-mass) | **arithmetic on the box's own hand-derivation.** The modeling inputs (per-crossing tail `~C2·W/u`, tail index 1) live in the *comment*, not in code. A calculator for a claim shares that claim's origin | 🟡 supports, does not verify |
| 26 (exp-depth) | **the test does not test the conclusion.** `exp_pred = e^{-(u2-u1)}` hardcodes **rate c = 1**; the observed data fits an exponential with `c ≈ 0.08–0.14` *perfectly*. As written it refutes rate-1 decay only | 🔴 unsound as written |

**The conclusion survives anyway — on evidence this session generated, not the box's.**
Three independent probes (scratchpad, reproducible; see the lap-19 ledger entry):
1. **Free-rate fit** over 5 instances: fitted `c ≈ 3/smax`, with `smax` growing `+log₂3` per
   row (linearly in `n`). So `c → 0` with `n`: **no uniform exponential rate exists.**
2. **Collapse test:** at matched `u/smax` the tails agree within **1.4–1.8×** across
   instances spanning `smax` 25→38 and `eps` 100×, and the trend **rises** with `n` where a
   fixed-rate exponential must **fall ~2.3×**. The tail is a scaling form `F(u/smax)` — the
   box's *mechanism* claim ("inherits the size spectrum") is **right**, though check26 could
   not have shown it.
3. **Plantability** (lap-18 prose, previously unchecked): **confirmed exactly.** `ξ ≡ 2^{l₀-1}
   (mod 3^n)` forces `|θ(1,l₀)| = 3^{-n}` — the minimal grid phase, a maximal triangle — one
   satisfiable congruence. **Stronger than lap 18 claimed:** typical ξ land within ~2 nats of
   the planted maximum, so near-giants are **generic**, not merely worst-case-in-ξ.

**The honest grade, therefore: "no route found, plus strong structural evidence the door is
dead" — NOT "proved closed."** All empirical evidence sits at `n = 22..30`, `eps ≈ 10⁻²`,
`smax ≈ 25–38` nats. The door lives at `n ≈ 10^3016`, `eps = 10⁻¹⁰⁰⁰`, `S ≈ 4613` nats. A
Monte Carlo at `n = 30` cannot prove a statement about `n = 10^3016`; lap 18's "**FALSE**, not
merely unprovable" is **not established**. (Under the verified scaling form the door fails by
a far wider margin than lap 18 claimed — at `smax ≈ 10^3016` the depth-4613 tail is `F(≈0) ≈ 1`,
no decay at all where the door needs it. That is the *right* argument, and it is still an
extrapolation, not a proof.)

**The decision is invariant to that correction — which is exactly why upholding is safe.**
"Proved closed" and "no route found" both say: stop grinding. But the record must be honest,
because the pin becomes a **documented open frontier**, and "we proved no route exists" is
precisely the claim a stranger would check and find unsupported.

### What is now true, and what happens next

- **The PIN campaign is CLOSED. No lap-executable work remains *on the pin*.** The branch is
  preserved (pushed) as the record. ⚠️ *Superseded in part by Ruling II:* a successor campaign
  (**assembled** explicit big-C, additive, at a tower-valued closed constant) **is now active
  and launch-ready** — it does not touch the pin. Read Ruling II first.
- **The pin stays `sorry`.** It is a stretch goal that did not land. **The core destination
  was reached and is untouched:** the 3 headlines (`tao_collatz`, `_quantitative`,
  `_quantitative_explicit`) are merged, axiom-clean, and **public**. Tao's theorem IS formalized.
- **No public surgery is required, and none is authorized.** Verified this session against
  `origin/main`: main's `Statement.lean` carries **no `CTao`, no `sorry`, no
  `fully_explicit`**, and main's `Comparator/TaoCollatz/config.json` lists **8** theorem
  names — the pin is **not among them**. The pin, `CTao`, and the 4th config entry live
  **only on this unmerged branch**. Public main is green and stays green **by not merging**.
  (This corrects the 2026-07-17 handoff's framing, which assumed retiring the pin would touch
  public surfaces. It does not.)
- **No *tighten-C* successor is spec'd or launched.** *(Ruling II note: this paragraph is about
  making the constant SMALL. It does not reach the **assembled** route, which makes no
  smallness claim — see Ruling II.)* The banked "tighten-C" follow-up is **not**
  launch-ready and must not be fired as a fleet campaign. check23(i)'s flat-envelope
  contradiction (`4·c_hit·R ≤ 1`, false by ~300+ orders for every `c_hit ≥ 10⁻¹⁵`) is
  **architecture-level and budget-independent** — it survives constant surgery, so shrinking
  `epsBW` / reshaping `hold_weight_expect` / lowering `caConst` does not reach it. The lap-1
  tighten-C sizings (`~10^(5.6×10⁸)`, `~10^(1.2×10⁹)`) **predate the tower discovery and are
  void** — do not cite them.
  **Entry gate for any future tighten-C:** independently **break or confirm check23(i)** by
  re-derivation. That is a judge/human mathematics question, not a grind lap. Until someone
  has a genuinely new idea about the *encounter accounting*, there is nothing to fire.

---

## 📜 HISTORY — superseded by the ruling above

## ~~✅ ROUTE RESOLVED (deep-reflection lap 12, 2026-07-17)~~ — **→ OPTION B. Transcription holding-pattern ENDED.** *(SUPERSEDED: Option B ran to laps 13–18 and closed; see the ruling above. Retained for the source-grounded diagnosis and the route-map record.)*

The lap-8/9 route trigger FIRED (the assembled `C_ladder`/`C_spine` is a *tower* ≫
`CTao = 10^(10¹¹)`, machine-checked check19) and was escalated to the operator layer. In this
**autonomous run the operator is unavailable**, and laps 10–11 spun for 3 laps grinding
X-chase transcription that served ONLY the cop-out. As the altitude lap (an empowered
directive writer; the session charter mandates *decide and proceed, don't ask*), lap 12
**RESOLVES the escalation → Option B.** This is now BINDING and outranks every handoff.

**Why B, not A** — it is not a close call:
- **Option A (re-pin `CTao` to a tower-form) is OUT OF SCOPE for any lap.** It edits the
  WATCHED, judge-owned pin (`Statement.lean` + `Comparator/…/Challenge.lean`); the house
  rules forbid editing a ratified statement, and re-pinning the "explicit constant" to a
  meaningless `Cthr_prop78^A` tower guts the challenge's entire purpose.
- **Option B keeps `CTao` and is a proof over frozen statements** (in scope, differ-neutral):
  it ADDS a tight renewal bound; the watched `∃`-form statements stay byte-identical.
- **The core destination is already reached** — the 3 merged headlines are axiom-clean
  (`#print axioms` re-run lap 12). Tao's theorem IS formalized. The pin is a stretch goal,
  and a stretch goal is pursued the honest hard way (B), never the cop-out (A).

**The tower is pure slop (lap-12 source read of `renewal_white_encounters_at`,
Bridge.lean:522–691):** the `n^{-A}` decay comes ENTIRELY from `hold_weight_expect` (the
Geom(4) hold-tail at `m = n/2`, hyp `htail`); the tower `C0 = C_polyDecay A` enters ONLY as
a multiplicative constant via the `Q_polynomial_decay` pointwise bound `hpt`
(`Q ≤ C0·(max(m−j) 1)^{-A}`), and in the applied range `Q ≤ 1` already holds (`Q_le_one`).
So the whole obligation is: replace `C0` (tower) by `≈ CTao` in the large-n arm.

**THE MANDATED NEXT MOVE (Option B, additive — do NOT touch the clean headlines):**

1. In `Sec7/Bridge.lean`, ADD a new lemma `renewal_white_encounters_tight` with the SAME
   statement shape as `renewal_white_encounters_at` but constant `C_renewalWhite_tight A`
   = the head arm alone (`(2·C_hold A + 2)^A`, no `max` with the tower). Prove the trivial
   parts (small-n arm `E ≤ 1 ≤ n₀^A·n^{-A}` verbatim from the existing proof; the two
   bridges; the `hold_weight_expect` decay) and ISOLATE the ONE hard sub-`sorry`:
   `renewal_tail_tight` = the large-n bound with a small constant. This RAISES the src
   `sorry` count 1→2 — that is PROGRESS (the crux becomes a visible, attackable hole).
2. **Do NOT re-prove the existing `renewal_white_encounters` / `renewal_white_encounters_at`
   / `C_renewalWhite`.** The 3 CLEAN headlines consume `renewal_white_encounters`; a
   sorry-backed witness there would poison their axiom base. Build B in PARALLEL as the tight
   copy, consumed only by the (already-sorry) pin's discharge.
3. Attack `renewal_tail_tight` with the smallest compiler/source-grounded probe. The crux =
   a `#white` lower-tail estimate beating `few_white_mass_le`'s (7.67) tower horizon: black
   (`|θq|≤ε=10⁻¹⁰⁰⁰`) is measure-~2ε rare ⟹ `#white` frequent ⟹ `E(n)≈exp(-ε³p·n/2)`
   head-dominated. ⚠️ **This is genuinely uncertain** — the "white is frequent" claim asserts
   the hard §7 decorrelation is easy (confabulation risk). Test it; do not assume it. Each
   lap advance the attack (narrow the sub-`sorry`, formalize a prerequisite, or record a
   refuted sub-approach) — never retreat to more transcription.

**FORBIDDEN DRIFT:** (a) more X-chase / transcription of the *tower* ladder — it only ever
enabled the cop-out A and step-2 is already complete; (b) editing `CTao`, `cTao`, or any
watched statement; (c) re-proving the existing `renewal_white_encounters` (poisons the clean
headlines); (d) declaring the pin "infeasible" and stopping — it is a 🟡 frontier to chip.

**STEP-2 note:** the X-chase (threshold half) is now DEPRECATED — it transcribes the tower
ladder Option B replaces. Do not continue it. (`ROUTE-ESCALATION-2026-07-17.md` is RESOLVED;
kept for the source-grounded diagnosis.)

---

## JUDGE RULING (2026-07-16 late evening) — lap-1 JUDGE-FLAG acknowledged; `CTao` re-pinned at `10^(10¹¹)`; steps 2/3 are LIVE 🟢

The lap-1 flag is **upheld**: the trace and the statement-forced floor were verified
independently host-side (arithmetic re-derived from scratch; the `epsBW`/`hold_weight_expect`/
`renewal_white_encounters`/`mainDecayExponent` hops read against source; check17 green).
The original pin's exponent sizing missed `M1`'s `1/δ ≈ 2×10³⁰⁰⁰` factor, and the floor
argument shows no proof over the frozen tower fits under `10^(10⁹)` — the miss was in the
pin's VALUE (operator sizing), not in the tower or the campaign design. Resolution:

- **`CTao := 10 ^ (100000000000 : ℕ)` (= `10^(10¹¹)`) in BOTH pin files** — done in the
  re-pin commit (`git log --grep 'JUDGE re-pin'`). Exponent headroom over the traced
  ladder ≈ 6.1×10⁹ (~6.5%), i.e. ~195 digits of slack on `n₀` (slack on `log₁₀ n₀`
  amplifies by `×B`) — orders beyond any plausible log-arithmetic proof slop.
- **check17 now asserts the GO** (`ladder < 0.95 × 10¹¹`) and keeps the lap-1 finding
  (ladder and floor vs the old pin) as machine-checked record.
- **Differ baseline advances to the re-pin commit** — see the hard-rails note below.
- Options (ii)/(iii) — shrinking `epsBW`, reshaping `hold_weight_expect`, lowering
  `caConst` — are statement/def surgery on the proven tower: **out of scope for this
  campaign**, banked as a candidate follow-up ("tighten-C") for after discharge. Step 2's
  symbolic-def scaffolding is exactly what such a campaign would build on, so nothing is
  lost by transcribing first. Keep reporting optimization observations.

**Steps 2 and 3 are unblocked. Resume at step 2, bottom-up, per the directive below**
(read `10^(10¹¹)` wherever it says the pin; the never-inflate/STOP rule applies to the
NEW value exactly as it did to the old).

---

## CURRENT DIRECTIVE (campaign start, 2026-07-16 evening; pin value updated by the ruling above) — **pin `C` in Lean: discharge `tao_collatz_quantitative_fully_explicit`**

> **⚠️ ROUTE SUPERSEDED (lap 12): the objective below stands (discharge the pin), but STEP 2
> (transcription) is COMPLETE and STEP 3's "prove `C_ladder ≤ CTao`" route is DEAD (tower).
> The live route is Option B in the RESOLVED banner at the top of this file — read that first.
> The STEP-1/2/3 text below is retained as the transcription-era reference, not live orders.**

### 🎯 The objective, in one sentence

Discharge the `sorry` on the PRE-PLANTED, JUDGE-OWNED pin (already in
`TaoCollatz/Statement.lean` AND `Comparator/TaoCollatz/Challenge.lean` + `config.json`;
you write the PROOF, never the statement):

```lean
noncomputable def CTao : ℝ := 10 ^ (100000000000 : ℕ)

theorem tao_collatz_quantitative_fully_explicit :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - CTao / (Real.log N₀) ^ cTao ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x)
```

`CTao` is a deliberate ROUND UPPER BOUND, not the assembled value. The statement WEAKENS as
`C` grows (`1 - C/(log N₀)^c` only shrinks), so any `C_ladder ≤ CTao` inequality over the
development's assembled constant discharges it. Sizing (post-ruling, step-1-traced): the
assembled constant is `≈ 10^(9.39×10¹⁰)` — dominated by `n₀^𝔡` with `𝔡 = mainDecayExponent
3.7 ≈ 3.11×10⁷` and `n₀ ≈ 10^3016` (the `1/δ` in `hold_weight_expect`'s witness) — so
`10^(10¹¹)` has ≈ 6.1×10⁹ exponent headroom (~195 digits of slack on `n₀`).
**If the traced ladder threatens to EXCEED `CTao`: STOP that thread and `JUDGE-FLAG:` with
the trace. Never inflate the pin — it is not yours to edit, in either file.**

### 🥇 STEP 1 — map before you mine: the numeric mirror

Before any Lean def, extend `tools/check_blueprint.py` with a **check17**: a float/exact
mirror of the `C`-ladder (mirror check16's style; float is fine for the map, exact-`Fraction`
for the final pin check). Walk the actual Lean witnesses (file:line per hop) — NOT from
memory. The known skeleton (verify every line against source; trust Lean over this sketch):

- `caConst A = 1000·(max A 0 + 3)` — `Sec6/MixingCore.lean` (`caConst 3.7 = 6700`)
- `mainDecayExponent A = A + (caConst A)²·log 2 + 3` — `Sec6/MixingMain.lean`
- `osc_mainHigh_bound` witness `3·C·40^B`, `B = mainDecayExponent A` — `Sec6/MixingMain.lean`
- telescope calls the high regime at `A + 2`; `fine_scale_mixing 1.7` is what Stabilization
  consumes → `B = mainDecayExponent 3.7`
- `osc_syracZ_regime_telescope` witness carries `2·N^A + C_high·S` with `N = max 9 n₀`,
  `S = ∑' k, k^(-2) = ζ(2) = π²/6` — `Sec6/MixingRegime.lean`
- the Sec7 chain: `hold_weight_expect`'s `Cthr = K + M1 + 2·T + 4` (explicit post-#8) →
  `C1` → `n0 = 2·C1 + 2` → `renewal_white_encounters`'s `max ((n0)^A) (…)` →
  the Fourier passthrough (`key_fourier_decay` → `charFn_decay` → …) — `Sec7/`
- Sec5/Sec3: the `C`-slots of the same lemmas the `c` campaign already gave `_explicit`
  siblings; the glue chain `descentProb_ladder → … → tao_collatz_quantitative_spine`

Deliverable: PENDING_WORK.md gets the full tree (value + file:line per node) and check17
passes. Report the estimated `log₁₀ C_ladder` — this is the go/no-go against the pin.

### 🥈 STEP 2 — sibling + delegate, bottom-up, `C`-slots AND thresholds

Census (from the hand-trace; re-verify): **76 constant-carrying existentials** (Sec5 37,
Sec7 22, Sec6 8, Sec3 7, Syracuse 1, Prob 1) **+ 31 threshold-only = 107 sites**. Thresholds
are IN SCOPE this time: `N := max 9 n₀` enters the constant as `2·N^A`, so the Sec6/Sec7
`n₀`/`x₀` chain must be extracted where (and only where) it feeds `C`.

Per carrier, the proven pattern: (1) name the witness as a symbolic `noncomputable def`
(`C_foo`, `T_foo`); (2) sibling `foo_explicitC` with the def in the `C`/threshold slot;
(3) re-prove the ORIGINAL `∃`-form by delegation — **original statements byte-identical,
the differ checks**. Where a `_explicit` sibling already exists from the `c` campaign,
extend or sibling it — don't fork a third naming scheme.

You only ever need **UPPER bounds `C_ladder ≤ C₀`** (mirror of the `c` campaign's
lower-bounds-only): sums/products/maxes collapse via `add_le_add`/`mul_le_mul`/`max_le`,
monotonicity of `rpow`/`pow` in base and exponent. Numeric comparisons stay in LOG form:
`Real.log_two_gt_d9`/`log_two_lt_d9` (ln 2), `Real.pi_gt_3141592`/`Real.pi_lt_3141593`
(π, via ζ(2) — `hasSum_zeta_two` in `Mathlib/NumberTheory/ZetaValues.lean` bridges the
`∑' k, k^(-2)` form; mind `rpow` vs `pow` casts).

**Cost-center rails** (learned the cheap way last campaign):
- One `_pos` lemma per def; never let laps grind `positivity` on opaque defs site by site.
- 🚨 **NEVER evaluate the big numerals.** `10 ^ (1000000000 : ℕ)` type-checks as a term but
  any tactic that normalizes it (`norm_num [CTao]`, `decide`, kernel reduction of the
  numeral) will hang the build — a billion-digit numeral. Same for `40^𝔡`-shaped terms.
  ALL comparisons via log-arithmetic and monotonicity lemmas; `norm_num` only on small
  rationals and exponent arithmetic.
- Local `set_option maxHeartbeats` bumps only, justified in a comment, on one declaration.

### 🥉 STEP 3 — discharge and stop

When the spine's `C`-chain is explicit: prove `C_ladder ≤ CTao` (one log-arithmetic
inequality, mirrored exactly by check17's final assert), discharge the Statement.lean
`sorry` by delegation, confirm `#print axioms tao_collatz_quantitative_fully_explicit` =
exactly the standard three. `TaoCollatz/` then greps 0 sorries → the self-stop gate closes
the run. The comparator CI check going green IS the external "done" (its challenge entry
was pre-planted; `Solution.lean` needs no edit — it imports the development).

### 🔒 Hard rails

- **Never edit a ratified statement.** `tools/tao_stmt_diff.py` per commit; the WATCHED set
  now includes `cTao`, `CTao` (def VALUES are pinned, not just types), both `explicit`
  theorems, and `Comparator/TaoCollatz/Challenge.lean` is in its search scope. ⚠️ `CTao`'s
  value was changed ONCE, by the judge (the re-pin commit:
  `git log --grep 'JUDGE re-pin' -1`) — run the differ against that commit or later
  (vs the setup commit it reports the `CTao` value change, vs `origin/main` the pins are
  "missing in old"; both are expected).
- **Comparator/ and `formalization.yaml` are judge-owned. Do not touch them.** The
  challenge entry is already planted; there is nothing for a lap to do there.
- **`comparator` CI is red until done — that is the design.** It flips green exactly when
  the campaign succeeds; don't "fix" it. `build` stays green throughout: the Statement.lean
  pin carries a local `set_option warningAsError false in` shield (repo-wide
  `weak.warningAsError` would otherwise error the sorry and jam the pre-commit green-gate).
  Remove the shield together with the `sorry` at discharge — never widen it.
- No `native_decide` (mints axioms; the gate is `--exact`). No new `axiom`. No linter
  silencing without a why-comment.
- **Do NOT optimize constants — but DO report optimizations you notice.** This campaign
  transcribes the proof's constants; the pin has headroom precisely so you never NEED a
  smaller `C`. But extraction walks every witness with the lights on, and if you SEE slack —
  a factor that cancels, a threshold far cruder than its use, a `max` whose second arm is
  never the binder, a lemma invoked with a constant orders looser than what its proof gives —
  that is potentially REAL MATHEMATICS (nobody has ever traced these constants before).
  Write it up in PENDING_WORK.md under `## Optimization observations` (site, file:line, what
  the slack is, estimated effect on `log₁₀ C`), flag `JUDGE-FLAG:` if it looks structural,
  and move on WITHOUT implementing: statements stay frozen, the pin stays, the transcription
  stays faithful. Observations are free; edits are not.
- **A failure to prove `bound ≤` is INFORMATION** — report it (the ladder is bigger than
  mapped, or the map is wrong); `JUDGE-FLAG:`, don't weaken statements and don't inflate
  defs.

### 📌 Orientation for a fresh box

- `c` is DONE and merged (PR #9): `cTao`, `tao_collatz_quantitative_explicit`, and the
  whole `c`-side sibling chain (`c_ladder`, `c_ladder_lower`,
  `tao_collatz_quantitative_spine_of_le`) are in-tree — study them; this campaign is their
  `C`-side mirror.
- The hand-traced map of the tower: `notes/effective-constants.md` on branch
  `effective-constants` (PR #6) — read once with
  `git show origin/effective-constants:notes/effective-constants.md` (bare `git` is correct
  in the box). Trust Lean source over the note wherever they disagree.
- Build: `lake build` (mathlib oleans shared via lake-base; project modules only).
- Report per lap (Option-B era): "renewal_tight: {pinned/sub-sorry state}; #white-tail probe
  {result}; src sorries N; blockers". (Transcription per-lap format retired with step 2.)

## Directive history

- **2026-07-16 evening** — campaign start: discharge the big-C pin via STEP-1 map → STEP-2
  transcription → STEP-3 `C_ladder ≤ CTao`. (JUDGE re-pin `CTao = 10^(10¹¹)` same night.)
- **2026-07-17 lap 12 (deep reflection)** — ROUTE RESOLVED → **Option B**. STEP-2 complete;
  STEP-3 transcription route dead (tower). Ended the 3-lap transcription holding pattern;
  mandated the additive tight renewal bound (`renewal_white_encounters_tight`) attacking the
  §7 `#white` decorrelation frontier, clean headlines untouched. See RESOLVED banner (top).
