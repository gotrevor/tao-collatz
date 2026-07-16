# Judge pass 25 (2026-07-13, Ren/Opus — lap boundary) — 🏆 **X9 / LEMMA 7.9 COMPLETE**; ε-SWEEP DISCHARGED AT 10⁻¹⁰⁰⁰; SUSPENSIONS LIFTED

Scope: treadmill laps 1–3 (opus, medium→high), 16 commits, `be46621..e08871e`.
The pass-24 unblock executed end to end. **The second pinnacle kernel is a theorem.**

## 🏆 The headline: `fpDist_any_triangle_le` is PROVED — X9 closes

The tail that has been blocked since pass 18 (route escalation), re-blocked at
pass 23 (the "quantifier-order altitude escalation"), and downgraded at pass 24
is now a **theorem, axiom-clean**. With it, the X9 kernel and headline fall.

**Dated runs (2026-07-13, all exactly `[propext, Classical.choice, Quot.sound]`):**

| decl | meaning |
|---|---|
| `fpDist_any_triangle_le` | the foreign-triangle tail — **the blocked one** |
| `fpDist_white_exit_deep` | the X9 kernel it feeds (ratification SUSPENDED since pass 18 — now moot: it is PROVED) |
| `many_triangles_white` | **X9 / Lemma 7.9 headline, end-to-end** |

`ManyTriangles.lean` now has **zero sorries**. X9 is the **eleventh verified node**
and the **second of the two pinnacle kernels** (X10 was the first, pass 20).

## How the two constants actually landed (vs pass-24's targets)

| constant | pass-24 target | box proved | budget | verdict |
|---|---|---|---|---|
| `B` (transverse threshold) | ≈ 42 | **64** | ≤ 250 | ✅ inside |
| `Y` (overshoot radius) | 139 | **150** | ≤ 200 | ✅ inside |

Box: `X = ⌈(5·150 + 64)/16⌉ = 51`, `√(51² + 150²) ≈ **158.4**` vs
`sep = 100·ln10 ≈ **230.26**` — fits with ~45% margin.

- `B`: `4·10⁷ → 64`, via a genuinely **exact** `Hold` MGF closed form
  (`tiltZ_hold_closed`, new in `Prob/Mgf.lean`), freeing the tilt from the
  quadratic box's `θ = 1/20000` to `θ = 1/16`. Verified clean, and — as pass 24
  predicted — **with no `native_decide`** (it is pure real-analysis over `exp`).
- `Y`: existential → **150**, via exactly the pass-24 route: `fpDist_le_renewal_conv`
  + **strictly-increasing heights** ⟹ `renewal_level_le_one` (each height level is
  visited at most once, so renewal mass per level `≤ 1` — no renewal theorem, no
  local limit law) + `Δl`'s exact MGF. `renewal_level_le_one` verified clean.
  **X6's envelope constants were left existential** — the completed node was not
  re-opened, as directed.

## The D4 numeral change: pre-authorized ruling EXECUTED correctly ✅

`epsBW : ℚ := 1/10^90 → 1/10^1000` (`7803117`), in a **dedicated lap** with no route
work mixed in, exactly as the doctrine requires. The box correctly checked its proved
constants against the judge's envelope (`B ≤ 250`, `Y ≤ 200`) before firing.

**Statement integrity — character-diffed across the change (`tools/sandbox/tao_stmt_diff.py`):**
all **12** pinned statements **byte-identical** — `black_structure`,
`white_gap_above_run_top`, `fpDist_white_exit_deep`, `fpDist_any_triangle_le`,
`fpDist_out_of_strip_le`, `fpDist_any_triangle_le_of_localization_box`,
`triangle_encounter_le`, `fpDist_edgeWeight_le`, `fpDist_white_exit`,
`Q_black_edge_case2`, `black`, and `epsBW`'s *type*. `Triangles.lean` changed 120
lines — **all proof-body arithmetic re-running at the new numeral**, zero statement
drift. The only value that changed is `epsBW` itself, by design.

## 🔔 ε-SWEEP RE-RATIFICATION — FIRED AND DISCHARGED at 10⁻¹⁰⁰⁰ ✅

The armed tripwire ran. **Dated runs, all exactly the clean triple:**
`black_structure` (X3) · `fCond_three_norm`, `white_cos_bound` (X2) ·
`triangle_encounter_le`, `encounter_apex_proximity`, `encounter_separated_sum` (X10) ·
`white_gap_above_run_top` · `fpDist_out_of_strip_le`.

**The verified-node ledger survives the second D4 change intact.** Pass-23's finding
that every sweep item is monotone-good at smaller ε held up under a 910-order-of-
magnitude drop. **The tripwire RE-ARMS** for any future `epsBW` change (same list).

## Suspensions LIFTED 🔓

- **`fpDist_white_exit_deep`** — ratification SUSPENDED since pass 18 (its *truth* at
  the frozen ε was no longer judge-believed), re-suspended on new grounds at pass 23.
  **Now moot in the strongest possible way: it is PROVED, axiom-clean.** A proof
  settles truth; the suspension is lifted, not merely re-instated.
- **`fpDist_any_triangle_le`** — was sorried with its obligation documented. Proved.

**Zero open suspensions in the campaign for the first time since pass 13.**

## Sorry trail after this pass (14, unchanged — but the composition moved)

`ManyTriangles.lean`: **0**. The count held at 14 only because X8's decomposition
opened a new named sub-goal as the tail closed (−1 / +1).

**5 crux** (all now in the Case-2/Case-3 assembly, none in X9/X10):
`fpDist_fst_mgf_le` (NEW, BlackEdge:318 — X8's decomposed core),
`fpDist_edgeWeight_le` (341), `fpDist_white_exit` (369), `Q_black_edge_case2` (457),
`Q_black_edge_case3` (Case3:941).
**9 deliberate spine stubs**: Basic/Collatz, Sec5 ×2, Sec6, Statement ×2, SyracRV ×3.

`tao_collatz` still carries `sorryAx` — correct, and expected until the trail clears.

## Hygiene / registry

- 🔵 **New `set_option exponentiation.threshold 3000`** in four Sec7 files. **Required**
  (Lean's guard would otherwise refuse to elaborate `10^1000`) and **not** a
  correctness-linter silencing — but it is a new option in trusted files, so it is
  logged here and added to the `/lean-review` registry as a *justified* option.
- 🚩 **The 🗂️ `ManyTriangles` split is STILL not done** (5,204 lines), and the box has
  now edited that file anyway — against its own written plan ("do the split before
  editing that file"). Not a correctness issue; it is a throughput tax the box keeps
  paying. Directive stands.
- X8 is now in flight (`fpDist_fst_mgf_le` decomposed, `gaussExp_col_tail` proved,
  X6 hoisted up to `FpLocation` so BlackEdge can see it).

## State

- **Eleven verified nodes**: S3, X1, X2, X3, X5, X6, **X9** 🆕, X10, C2, C5 (+X4/X7 files
  sorry-free).
- **Both pinnacle kernels (X9, X10) are complete and axiom-clean.**
- Prop 1.17's remaining trail is the Case-2/Case-3 assembly — the material the campaign
  always rated as *precedented volume*, not novelty.
