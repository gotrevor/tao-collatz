# Plan: drive the reported constant down from `10↑↑63` to `~10↑↑4`

**Owner of this doc**: operator/judge brief for a **Fable-architect → Fable-treadmill** pair.
**Baseline**: `origin/main` @ `4dde699` (post-#10; `CTao := hyperoperation 4 10 63`, `BigCTower.lean` 3256 lines).
**Nature**: ADDITIVE reporting/tightening.  It changes the *reported ceiling* on the already
axiom-clean constant.  It does **not** reopen the ratified mathematics.

---

## 1. BLUF: `10↑↑63` is proof slop, not math

The honestly-assembled constant `C_tao_assembled` is a **height-3 tower**,
`≈ 10^(10^(10^3010))`, i.e. strictly between `10↑↑3` and `10↑↑4`.  The other **~59 tower
levels** in the current `C_tao_assembled ≤ tenTower 62` ceiling are pure per-operation
rounding.  This plan removes the slop and re-pins `CTao` at the honest height.

**Target headline**: `CTao := hyperoperation 4 10 4` (`= 10↑↑4`), with a tighter
`10^(10^(10^3010))` recorded alongside.  Nothing else about the theorem moves.

### Why this is true (the honest-floor argument, all source-verified)

The ceiling climb from leaves to `tenTower 62` is bought by **242 per-operation `_succ`
steps** in `BigCTower.lean`:

| primitive | count | what it charges |
|---|---|---|
| `tenTower_mul_le_succ` | 132 | +1 level per multiply |
| `tenTower_add_le_succ` | 72 | +1 level per add |
| `rpow_le_tenTower_add_two` | 27 | +2 levels per `x^A` |
| `exp_le_tenTower_succ` | 11 | +1 level per `exp` |

**None of these operations raises a tower's height.**  A product of two things
`≤ tenTower h` is `≤ (tenTower h)² ≤ tenTower(h+1)` at *worst*, and batched across a whole
level it is **+0** (`(tenTower h)^k = 10^(k·tenTower(h-1)) ≤ 10^(tenTower h) = tenTower(h+1)`
for any `k` we ever use).  Every leaf constant is `≤ 10^30` (see the ubiquitous
`ten_pow_thirty_le_tenTower_two`), so all 132 multiplies together still live at `tenTower 2`.
Same story for the adds, the number-powers, and the `exp`s of small arguments.

**Exactly one site generates genuine height**: the cubic `encWindowIter` recurrence
`enc(i+1) ≈ 4^A·enc(i)³` over `R ≈ 10^3010` steps, giving `B^(3^R)` with `log₁₀log₁₀ ≈ 10^3010`
= **2 real levels** above its `~10^3010` base = **3 total**.  Even that lemma
(`encWindowIter_le_tenTower_add_six`) rounds its true +2 up to +6.

**Machine anchor already in the repo**: `tools/check_blueprint.py` `check19` computes
`log₁₀log₁₀ C_renewalWhite ≈ 10^3009.5`, and `C_tao_assembled` inherits that height
*multiplicatively* (no extra level).  So the floor is real and it is height 3.

### Bonus finding: the top exponent is human-shaped too

`3010 = 3 × 1000 + slack`, where `epsBW = 1/10^1000` (a hand-picked black-set width) enters
as `epsBW⁻³ = 10^3000` (`BigCTower.lean:727`).  So the base `10` is cosmetic **and** the top
`3010` traces to a chosen `ε`.  The base-free content is simply:

> **`log log log C ≲ 3010`**, and `3010 = 3 · epsBW⁻¹-exponent`.

Worth stating in a docstring / the blueprint node once the height lands.  (Re-basing to a
"natural" base like `ln 4 = 2 ln 2` was considered and rejected: a smaller base just spends
*more* levels to express the same value, so it polishes slop rather than removing it.  Kill
the height first; the base question then dissolves into the `log-log-log` statement above.)

---

## 2. The design task (FABLE-ARCHITECT)

Design a **height-preserving calculus** so a batch of polynomial operations costs zero tower
levels, and re-express the `BigCTower.lean` climb in it.  Two candidate designs; **prototype
B first** (fast, low-code, gets `63 → ~5`), then decide whether A is worth it for the tight
`10↑↑4` / `10^(10^(10^3010))` headline.

**Design B — batched level-budget (recommended first).**
Add to `Basic/ExplicitConstants.lean` a small bank of *batched* lemmas that charge one level
for an arbitrary-length polynomial combination, not one per op:
- `prod_le_tenTower_succ`: `(∀ i, xᵢ ≤ tenTower h) → (k ≤ tenTower h) → ∏ xᵢ ≤ tenTower (h+1)`
  (proof: `∏ ≤ (tenTower h)^k = 10^(k·tenTower(h-1)) ≤ 10^(tenTower h)`; mild side-condition on `k`, always met).
- `sum_le_tenTower_succ` (the additive twin), `rpow_batch` (`x ≤ tenTower h → x^t ≤ tenTower (h+1)` for `t ≤ tenTower h`), and a `max` passthrough.
Then each *level of nesting depth* in the constant DAG costs +1, not each edge.  The DAG's
genuine tower-height is 3 (+2 for the cubic recurrence's real double-exp), so the climb lands
around `tenTower 4-5`.  Minimal new vocabulary; re-uses the existing `tenTower`.

**Design A — real-topped tower carrier (tight version).**
Define `tenTowerR : ℕ → ℝ → ℝ`, `tenTowerR 0 x = x`, `tenTowerR (h+1) x = 10^(tenTowerR h x)`
(a tower of `h` tens topped by a real `x`).  Prove the closure calculus once: `mul`/`add`/
`pow`(by a real)/`max` stay at height `h` and only move the top real `x` by a controlled
amount; `10^·` / `exp` lift `h → h+1`.  Carry the whole climb in `tenTowerR`.  This mirrors
`check17`/`check19`'s float trace exactly and yields the tight `tenTowerR 3 3010 = 10^(10^(10^3010))`.
Bridge to the headline via `tenTowerR 3 3010 ≤ tenTower 3` (since `3010 < 10^10`) and a new
`tenTower_three_eq_hyperoperation` (generalize the existing `tenTower_sixty_two_eq_hyperoperation`).

**POC gate (do this before any grind — it proves the whole thesis on one node).**
Take the `C_fpLocation ≤ tenTower 8` cluster (`BigCTower.lean:244`), which climbs `2 → 8` on
five `tenTower_mul_le_succ` over factors each `≤ 10^30` or `≤ tenTower 3`.  Re-prove it as
`C_fpLocation ≤ tenTower 2` (or `3`) in the new calculus.  If it lands, the thesis is proven
and the rest is mechanical.  If it fights, `JUDGE-FLAG` before spending laps downstream.

**Architect deliverables**: the calculus lemmas in `Basic/ExplicitConstants.lean`; the POC
node re-proved; a fresh single-owner `DIRECTION.md` DIRECTIVE for the grind (one owner per the
DIRECTION banner rules); `check28` in `tools/check_blueprint.py` = a log/log-log mirror of the
full `C_tao_assembled` max-tree that prints its height and asserts `≤ 3` with a mutation trap
(extend `check19`; **resolve which arm of each `max` wins in log-space** — do not assume, a
`log`-bearing arm could in principle reduce a level).

---

## 3. The grind task (FABLE-TREADMILL)

Once the calculus + POC land, convert the climb **bottom-up, cluster by cluster**, one commit
per node or small cluster.  Roughly the order in `BigCTower.lean`:

1. Sec5 leaves + first-passage cluster (`C_holdLocal`, `C_renewalMass`, `C_fpLocation`,
   `C_fpCol`, `C_fpHeight*`, `C_encSep`, `C_encTri`, `C_estarUnion`, `A0_fewEstar`).
2. The cubic-recurrence node (`encWindowIter_le_tenTower_add_six`): retighten `+6 → +2`.
3. Sec6 mixing + Sec3 spine climb (lines ~740-3256, the part that runs `19 → 62`).
4. `C_tao_assembled_le`: restate RHS `tenTower 62 → tenTower 3`; re-pin `CTao` in
   `Statement.lean` to `hyperoperation 4 10 4`; update `tao_collatz_quantitative_fully_explicit`.

Each step is `positivity` + the batched calculus lemma + the child's tightened bound.  The
tower numeral stays **symbolic** throughout (never `norm_num`/`decide`/`native_decide` on it —
it hangs; log-arithmetic only, as `check17`/`check19` do).

---

## 4. Guardrails

**FROZEN — do not touch** (these are the ratified mathematics; the differ watches them):
- Every paper pin (the 24 numbered claims / §7 lemmas).
- `C_tao_assembled` (the **definition**), `X_spine`, `tao_collatz_quantitative_assembled`.
- `tao_collatz`, `tao_collatz_quantitative`, `cTao`, `tao_collatz_quantitative_explicit`.

**INTENTIONALLY MOVED DOWN** (expected differ hits; the judge ratifies the new value against
`check28`):
- `CTao`'s value (`10↑↑63 → 10↑↑4`), the RHS of the ceiling theorem (`tenTower 62 → tenTower 3`),
  and the constant inside `tao_collatz_quantitative_fully_explicit`.

**This move is monotone-safe.**  The theorem reads `1 - C/(log N₀)^c ≤ logProb{…}`; a *smaller*
`C` makes the lower bound *larger*, i.e. the statement strictly **stronger**.  So re-pinning
down cannot weaken anything, and the tightened `C_tao_assembled ≤ tenTower 3` is exactly what
re-derives `fully_explicit` at the new pin.  (Same doctrine as the binder-deletion ruling:
monotone, compiler-adjudicated changes are safe; guard provenance, not logical strength.)

**Axioms**: end state `#print axioms` on the headlines must stay `[propext, Classical.choice,
Quot.sound]` (it will — this is real-analysis inequalities over an already-clean constant).
**Comparator**: the `build` + `comparator` required checks must stay green; `CTao`/`tenTower`
live in `Challenge.lean` too, so update the challenge in lockstep and re-run
`scripts/comparator-probe` locally.

---

## 5. How to run it

- **Branch**: this plan is on `tier1-tower-tightening` (off `4dde699`).  Architect + treadmill
  work here (or a worktree off it via `lean-create-worktree`).
- **Fire order**: Trevor fires the **Fable-architect** session first (calculus + POC + DIRECTIVE
  + `check28`).  On a green POC, Trevor fires the **Fable-treadmill** for the grind.
- **`--done-when`**: this ADDS/tightens a theorem, it does not remove a sorry (library is 0 and
  stays 0), so a `sorry-free:` gate does not apply.  Gate on `--max-duration` + operator stop,
  or a `check_blueprint`/audit predicate.  Self-stop cannot fire (comparator stubs at root), so
  no `--forever`; keep `box stuck` as the escalate lane.
- **Report on completion**: the new theorem statement + the explicit height (`tenTower 3` /
  `10^(10^(10^3010))`) + `#print axioms` + the `check28` line + a green comparator run.

## 6. Follow-ons (out of scope here, noted for the map)

- **Tier 2** (research, ~65%, weeks): even the honest height-3 tower is slop from
  `few_white_mass_le`'s crude `(7.67)` triangle-exit horizon (`Q_polynomial_decay` is vacuous
  in the applied range).  A real decorrelation / lower-tail estimate on the white-point count
  would collapse the *triple* exponential to a *single* one, `≈ 10^(9.4×10^10)`.  The log-space
  calculus built here is the natural frame for it.  See `ROUTE-ESCALATION-2026-07-17.md` Option B.
- Blueprint/docstring: once the height lands, record the base-free `log log log C ≲ 3010` form
  and the `epsBW⁻³` provenance on the relevant node.
