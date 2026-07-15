# Handoff: C7 COMPLETE — first_passage_nonescape (1.19) axiom-clean; next is C8-close then C9

**Real date**: 2026-07-15 (~clock-skew; match by HEAD). **Branch** `main`, **HEAD `3e4d94e`**.
Build 🟢 green (full `lake build`, 3322 jobs, pre-commit verified). Tree clean.
**Read `DIRECTION.md` first** — its CURRENT DIRECTIVE (Judge Pass 29 + review updates) outranks this
doc. Order: **C10 ✅ → C8 (pin ✅) → C7 (prove ✅ this session) → C8 close → C9**.

## What this session did: closed all of C7 (5 → 0 working sorries in the C7 chain)

Every lemma below is `#print axioms`-clean `[propext, Classical.choice, Quot.sound]` (verified).
All in `TaoCollatz/Sec5/FirstPassage.lean`.

1. **`window_arith`** — the one analytic input to the three counting lemmas: for `x ≥ 2^2000`,
   `y ∈ {x^α, x^{α²}}`, the modulus `M = 2^{3n₀} ≤ y` and `2y ≤ y^α` (log/rpow; `2^{3n₀}≍x^{0.3} ≪ y`).
2. **`classMass_ap_form`** — the AP-reindexing bridge: `{N∈[y,y^α]:N≡r (mod M)}` **is** the AP
   `{a+M·i:i<count}` (a = least member ≥⌈y⌉ via `Nat.find`, `count=(⌊y^α⌋−a)/M+1`); ZMod↔mod bridge,
   oddness absorbed, sum via `Finset.sum_image`. ⟹ **`intTest_class_dev` axiom-clean** (the crux).
3. **`logWindow_nonempty_of_large`** — explicit odd witness `k+(k+1)%2`, `k=⌈y⌉₊`.
4. **`intTest_D_lower`** — `windowMass ≥ 1/8` via the odd-AP-image of `logWindow` (same core, M=2).
   ⟹ **`intTest_error` + `integral_test_logUnif` axiom-clean** — the integral test is COMPLETE.
5. **`valSum_lower_tail`** (paper (5.5)) — via three helpers: `geomHalf_underflow_le_Gweight`
   (lower-tail analogue of overflow), `two_rpow_neg_nZero_le` (the (5.1) `2^{-c n₀}≤x^{-c/20}`
   conversion), `valSum_lower_geom` (`integral_test_logUnif → valuation_dist` (5.4), event pushed
   to the Geom-side underflow, difference by dTV).

⟹ **`first_passage_nonescape` (1.19) is axiom-clean — C7 DONE.** Judge should flip the C7 `\leanok`.

## → NEXT (per DIRECTION order): CLOSE C8, then C9

**C8 = `first_passage_approx` + named sub-sorries** in `TaoCollatz/Sec5/ApproxFormula.lean`
(3 sorries at :97, :116, :132; RATIFY-C8, pinned last session). C8's proof consumes C7 at exactly
ONE place — `approx_passtime_window` (5.16), the `{¬passes}` escape term = (1.19), which is now
`first_passage_nonescape`, **proved and axiom-clean**. So the input C8 was waiting on EXISTS.
Read `ApproxFormula.lean:1-135` + PENDING_WORK's C8 route notes; wire `first_passage_nonescape`
into the (5.16) escape term, then discharge the other two named sorries (the `B_{n,y}` chain / event
algebra). C8 is the board's RISK (diff 4, 75%) — expect real work, decompose further if needed.

**C9 = `stabilization` stub** at `FirstPassage.lean:1343` (the ONLY remaining sorry in FirstPassage).
Prop 1.11 assembly; consumes C10 (✅) + C8. Do AFTER C8.

## Sorry census
- **FirstPassage.lean: 1 sorry** (`stabilization`, C9). C7 chain fully proved.
- **ApproxFormula.lean: 3 sorries** (C8) — the live frontier.
- Plus headline/other-node stubs elsewhere (Statement, Sec7/*, Sec6/MixingCore, Prob/Basic,
  Basic/Collatz) — not on the immediate C8→C9 path.

## Rails / notes
- **Banked gotcha** (also in auto-memory `lean-linarith-decimal-rpow-poison`): `linarith` FAILS when
  a hyp in scope holds `y ^ alpha` (alpha := 1.001, a decimal `OfScientific` def) or a big literal
  rpow like `2^(2000:ℝ)` — its preprocessing tries to evaluate them. Fixes: make the term opaque via
  `obtain ⟨Y, hY⟩ : ∃ Y, y^alpha = Y := ⟨_, rfl⟩; rw [hY] at ...` (NOT `set` — it zeta-unfolds), and
  use `linarith only [...]` to keep poison atoms out of scope.
- Watched statements (`fine_scale_mixing`/`stabilization` header) + all ratified pins UNTOUCHED.
  Never set `\leanok` yourself.
- `git-safe` at `/Users/gotrevor/personal/bin/git-safe` (`export PATH="$HOME/personal/bin:$PATH"`).
- Axiom-check recipe: write `TaoCollatz/ZZ_ax_check.lean` importing the module with `#print axioms
  <name>`, `lake env lean` it, then delete (don't leave it — breaks the build tree). Same for scratch
  `ZZ_*_check.lean` single-lemma typecheck files — always `rm -f` after.
- Pre-existing `info: Error in Linarith.normalizeDenominatorsLHS` at `Prob/CharFn1.lean:166` is an
  info-level non-error (build stays EXIT 0); not from this session.
