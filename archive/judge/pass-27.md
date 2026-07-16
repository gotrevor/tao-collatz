# Judge pass 27 — 2026-07-14 (overnight run #2 boundary; treadmill STILL RUNNING)

**Scope**: overnight run #2, laps 1–6, **53 commits**, `4f51542..8505bd4`. Judged mid-run: the
box was on lap 6 with ~3h30m left, so this pass ran in a worktree **pinned at `8505bd4`**
(`~/src/tao-collatz-judge27`, CoW `.lake`, build green 3285 jobs). Every axiom figure below is
from that pinned build, dated **2026-07-14 08:08 EDT**.

## Verdict in one line

🏆 **§7 IS COMPLETE AND JUDGE-VERIFIED — the campaign's stated 65–75% risk concentration is
retired.** Pass 26's one unverified step (the `Cthr` bridge) is **discharged in Lean, not on the
judge's napkin**. Zero statement erosion across 53 commits. Sorries **11 → 4**, all by proving.
The frontier moves to **C10 (§6)**.

## 1. What the night earned (verified, not claimed)

**Dated `#print axioms` — 24 decls exactly `[propext, Classical.choice, Quot.sound]`:**

- 🏆 **§7 spine CLOSED**: `prop_7_8`, `Q_black_edge`, `Q_black_edge_case3`, `Q_black_edge_case2`,
  `Q_polynomial_decay`. The X11 gate is discharged; `prop_7_8` no longer carries `sorryAx`.
- **§7 Case-3 leaves (the two sorries pass 26 left)**: `few_white_mass_le` (7.56),
  `col_tail_mass_le` (7.54). **Both clean.**
- **§7 exports**: `charFn_decay` (Prop 1.17), `key_fourier_decay` (Prop 7.1).
- **X10 / X10a pins survive the night**: `triangle_encounter_le`, `encounter_apex_proximity`,
  `many_triangles_white` — still clean, still character-identical (the pass-26 repair holds).
- **Reduction floor (new)**: `colMin_eq_syrMin_oddPart` (paper (1.2), Collatz→Syracuse) +
  the SyracRV identities `syracZ_recursion` (Lemma 1.12), `syracZ_eq_rev_fnat` (1.21),
  `syracZ_map_cast` (1.22).
- **C10 machinery (new)**: `osc_le_sqrt_highfreq` (CS/Parseval bridge, now density-general),
  `fnat_split`, `syracZ_offset_split`, `char_offset_split`, `PMF.cexpect_iid_append`,
  `cond_char_factor`, `dft_cond_density`, `dft_condDens_eq_cond_char`.

**`sorryAx` (expected)**: `tao_collatz`, `tao_collatz_quantitative` — the two headline stubs.
The spine is not assembled; that is correct and by design.

**Sorry census 11 → 4** (`lean-sorry`, pinned tree): `Sec5/FirstPassage.lean:81`
(C9 `stabilization`), `Sec6/MixingFromDecay.lean:573` (C10 `fine_scale_mixing`),
`Statement.lean:24,31` (headline stubs). **The drop came entirely from proving — nothing was
parked in `wip/`** (`wip/` is empty; the self-stop gate correctly reads ⛔).

## 2. 🔓 THE `Cthr` BRIDGE IS DISCHARGED — the one step this pass existed to check

Pass 26 flagged it in capitals: the Case-3 consumer sits at depth `m+1`, and
`m/log²m < s ⟹ (m+1)/log²(m+1) < s` **genuinely fails**. The chain closes only by threading a
largeness constant, "**which closes on the judge's arithmetic, and that is not the same as
closing in Lean. Do not accept `few_white_mass_le` without seeing the `Cthr` largeness
discharged.**"

**It is discharged.** `Case3.lean:2011–2068`, inside `few_white_estar_mass_le`, kernel-checked:

| step | line | content |
|---|---|---|
| largeness in | 2007 | `hmC : (10:ℝ)^30 ≤ m` (from the `Cthr` hypothesis) |
| succ bound | 2014 | `(m+1)^0.8 ≤ 2·m^0.8` (via `m+1 ≤ 2m`) |
| log control | 2032 | `log²m ≤ 400·m^0.1` (via `Real.log_le_rpow_div` at `0.05`) |
| **the crux** | 2043 | `800 ≤ m^0.1` ← **this is where the largeness is consumed** |
| product | 2051 | `(m+1)^0.8 · log²m ≤ 800·m^0.9 ≤ m` |
| bridge | 2063 | `(m+1)^0.8 ≤ m/log²m`, then `< s` by the paper hypothesis |
| depth id | 2066 | `n/2 − (n/2−m−1) = m+1` |

Then `estar_union_le_rpow` applies at depth `m+1`. No `sorry`, no axiom, kernel-checked.

🔎 **A finding worth keeping: 10^27 would NOT have worked.** The largeness is consumed at
`800 ≤ m^0.1`. At the handoff's `Cthr = 10^27` that gives `m^0.1 ≈ 501 < 800` — **the route
fails.** The box independently baked **`10^30`** into `few_white_estar_mass_le`
(`Case3.lean:1945`), which gives `m^0.1 = 1000 ≥ 800`. The judge's napkin constant was too
small by three orders of magnitude and the *worker's* constant is what carried the proof.
Lesson: a judge-supplied numeral is a hypothesis too. It gets checked like everything else.

✅ Also confirmed: `few_white_mass_le` carries the **paper-faithful** deep hypothesis
`(m:ℝ)/Real.log m^2 < s` (`Case3.lean:2253`). The weaker `m^0.8` `_rpow` form stayed where pass
26 put it — in the *engines*, never in the §7 leaf.

## 3. Statement erosion: 28/29 character-identical, 1 benign

`./tools/tao_stmt_diff.py 4f51542 8505bd4` over the **extended** 29-name list (see §5):

- **28/29 byte-identical**, including every §7 pin, both headline stubs, and — critically —
  **both open crux statements** (`fine_scale_mixing`, `stabilization`). *The box did not weaken
  its own targets to make them closeable.* That is the single most valuable negative result here.
- **1 change, benign, ratified**: `colMin_eq_syrMin_oddPart` went `(_hN : 0 < N)` →
  `(hN : 0 < N)`. Identical `Prop` — same hypothesis, same conclusion. The underscore dropped
  only because the proof now *uses* the hypothesis. No erosion. **Ratified.**

**HARD RAIL 6 held.** 53 unattended commits, zero edits to a ratified pin, zero `JUDGE-FLAG:`
raised (i.e. no lap hit a wall it was forbidden to route around).

## 4. `/lean-review` — ⚠️ 8 flags, all 🔵

🔴 tier is **empty across 53 commits**: no new `maxHeartbeats`/`maxRecDepth`, no `native_decide`,
no new `axiom`, no `unsafe`/`partial`/`implemented_by`/`extern`/`opaque`, no silenced linters, no
bare `#print axioms`, **no Prop-valued `def`s** (the laundered-hole smell the axiom gate cannot
see). For a 53-commit unattended night this is a disciplined diff.

🔵 **8 new deprecations**, all `mul_le_mul_left'` → `mul_le_mul_right`, all in `Case3.lean`
(2495, 2496, 2691, 2692, 2766, 2830, 2834, 2913). Batch with the standing nit (7 pre-existing
Sec7 `maxHeartbeats` bumps lacking `-- HEARTBEAT:` comments). Post-work mop-up; blocks nothing.

## 5. 🔧 System fix: the differ was aimed at the finished half of the proof

**Pass 26's lesson has a sequel.** That pass fixed the differ's blind spot by growing the list to
19 names. But those 19 are **§7 + `Statement` only** — and §7 is now *done*. The guard was
pointing at the part of the proof nobody is editing any more, and was **blind to the part
actively being worked on**:

- `fine_scale_mixing` (C10) and `stabilization` (C9) — **the repo's two live sorries** — were
  unwatched, and their files (`Sec6/`, `Sec5/`) were not even in `SEARCH_FILES`. **A lap
  weakening the very statement it is trying to prove is the highest-value silent failure
  available right now**, and no instrument would have seen it.
- `charFn_decay` (Prop 1.17) was unwatched — and it is *C10's analytic input*, so it sits
  directly upstream of live work. A lap that finds C10 hard could "adjust" it.
- The reduction floor (`colMin_eq_syrMin_oddPart`, the SyracRV identities) was unwatched.

**Fixed this pass**: `PINNED_NAMES` 19 → **29**, `SEARCH_FILES` 8 → **13** (adds `Sec7/Decay`,
`Sec7/Reduction`, `Sec6/MixingFromDecay`, `Sec5/FirstPassage`, `Basic/Collatz`,
`Syracuse/SyracRV`).

📌 **New distinction, written into the tool: WATCHED ≠ RATIFIED.** A name in `PINNED_NAMES`
means *the differ reports any change to it*. Ratification is the judge's separate reading
against the PDF. Watching an un-ratified statement (like the two open sorries) is strictly
good — **it is how we see the frontier move.** The old list conflated the two, which is
precisely why it only ever guarded finished work.

🔁 **Standing rule, now generalized**: ratify a statement ⟹ add it that same pass (pass 26). **And
when the frontier moves, move the guard with it** (pass 27). A guard that only covers completed
nodes is a guard that has stopped working.

## 6. Objective scorecard vs the pass-26 directive

| # | Objective | Result |
|---|---|---|
| 1 | Close the two §7 sorries | ✅ **DONE** — both proved, both clean, §7 CLOSED |
| 2 | The X10/X10a repair | ✅ **DONE** (first lap, `4f51542`; holds — pins still byte-identical) |
| 3 | Burn down the fruit | ⚠️ **1 of 3** — the 7 spine stubs are ✅ **eaten** (SyracRV 1.12/1.21/1.22, §5 `logUnifOdd`, Collatz (1.2), S4 Parseval — 25 commits). But `ManyTriangles.lean` is **still 5,519 lines** (unsplit, **8th lap queued**), and **C8 is still unpinned** (no `RATIFY-C8` marker). |

The valuable two-thirds happened. The box ate the *math* fruit and left the *hygiene* fruit —
which, given it also closed §7 and opened C10, is the right trade. But note the pattern: **the
split has now been ordered and skipped for eight consecutive laps.** It is not going to happen
as a side-objective. Either it gets its own lap with nothing else in the directive, or it gets
dropped from the directive honestly. Pretending to order it is the worst of the three.

## 7. Rulings

- ✅ **§7 RATIFIED COMPLETE.** X11 / `Q_black_edge_case3` joins the verified ledger. With X8
  (pass 26) that makes **§7 fully closed and machine-verified**. Thirteen+ verified nodes.
- ✅ **`few_white_mass_le` + `col_tail_mass_le` RATIFIED** (statements paper-faithful, proofs
  clean, `Cthr` bridge seen and checked). Both added to the watch list.
- ✅ **`colMin_eq_syrMin_oddPart` RATIFIED** (paper (1.2)); binder change benign.
- ✅ **SyracRV identities RATIFIED** (Lemma 1.12, (1.21), (1.22)).
- 🔓 **ZERO open suspensions.** Zero `JUDGE-FLAG:`s. `epsBW` still frozen at `1/10^1000`
  (unchanged, differ-confirmed) — the ε-sweep tripwire did not fire.
- 🟡 **C8 (§5) remains the last un-pinned node.** Now genuinely blocking: C9 `stabilization`
  lives in §5 and is next-but-one on the critical path. **Pin C8 before C9 work starts**, or a
  lap will be proving toward an unratified target.

## 8. What pass 28 must check

1. **C10 statement integrity first.** `fine_scale_mixing` is now watched — run the differ before
   anything else. The box is under maximum pressure on exactly this statement.
2. **The tail-factor reindex** (`charFn_decay` at modulus `3^(j+p)` → level-`p` char at `ξ'`) is
   C10's "last real novelty" by the box's own account. It is the step most likely to be waved
   through with a plausible-looking cast. Read it against pp.28–31, do not just check axioms.
3. **Pin C8** against pp.22–25.
4. Whether the `ManyTriangles` split happened, and if not, decide honestly (own lap, or drop it).

---
*Judge passes 1–23 by Ren/Fable; 24–27 by Ren/Opus. Pass 27 run mid-flight against a worktree
pinned at `8505bd4` while overnight run #2 continued in the shared tree.*
