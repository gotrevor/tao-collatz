# Judge seat handoff — read this first 🪷⚖️

You are picking up the **architect/judge** role for the tao-collatz expedition
(formalizing Tao 2019, arXiv:1909.03562v5, "almost all Collatz orbits attain
almost bounded values"). This file is the entry point — everything else lives in
the repo docs it points to. **A compacted or fresh session can rebuild the whole
seat from here; nothing important lives only in a context window.**

## The role in one paragraph

Workers (treadmill box laps, and sometimes external OpenAI Codex sessions) produce
Lean; the judge **verifies and records**. The judge's currency is: (1) **statement
faithfulness** — every pinned statement is ratified against the paper PDF
(`papers/tao-2019-almost-all-orbits.pdf`), and any edit to a ratified statement
REVOKES ratification until re-diffed/re-read; (2) **dated axiom runs** — proof
status exists ONLY via a judge-run `#print axioms` on the host (`lake env lean` on
a scratch file, `import TaoCollatz` + `open TaoCollatz`; clean = exactly
`[propext, Classical.choice, Quot.sound]`). **Worker claims are hypotheses.** Green
build ≠ faithful proof; textual sorry-census ≠ transitive trail (pass 22 caught a
"finished" theorem resting on a sorry in an *untouched* file — only the axiom run
sees that).

## Protocol documents (the source of truth)

1. **`EXECUTABILITY.md` → "Judge loop — standing ops"** — the per-pass recipe
   (diff → ratify → blueprint flips → rebuild → scoped commit → pass record).
2. **`EXECUTABILITY.md` → "Live judge state"** — verified ledger, suspensions,
   tripwires, escalations. Refresh every pass.
3. **`EXECUTABILITY.md` → "Campaign log"** — index of `judge/pass-NN.md`.
   **Next pass number: 26.**
4. **`DIRECTION.md` → CURRENT DIRECTIVE** — **the judge writes this; it OUTRANKS the
   HANDOFF and every grind lap re-reads it each lap.** This is the live steering
   channel: edit it mid-run to redirect the next lap.
5. **`BLUEPRINT.md` §2** — node ledger + operator directives to workers.
6. **`blueprint/src/content.tex`** — the node ledger the outside world sees.
   Rebuild with `bash blueprint/build.sh`, never bare `leanblueprint web`.

## Judge tools (in-repo, written by the judge)

- `tools/tao_stmt_diff.py` — character-diffs PINNED statements across a commit.
  **Run this on any commit that touches a ratified file.** It is what proved the
  D4 numeral change didn't erode a single statement.
- `tools/tao_linear_tail.py`, `tools/tao_height_tail.py` — the pass-24 numerics
  (exact step-law MGFs; optimize the tilt and print the localization box).

## Where things stand (post-pass-25, 2026-07-13 evening)

- **ELEVEN verified nodes** (dated runs): S3, X1, X2, X3, X5, X6, **X9**, X10, C2, C5
  (+ X4/X7 files sorry-free). 🏆 **BOTH pinnacle kernels (X9, X10) are COMPLETE.**
- **Passes 24–25 closed the campaign's longest-running block.** The "second
  altitude-class escalation" (pass 23) was **downgraded, not escalated**: a p.48
  re-read showed the paper's O(1) localization is a distance *from Δ* (the walk
  drifts *along* the triangle, since slope 1/4 < log2/log9) and is ε-free. The route
  was always sound; the blocker was two throwaway constants. `B`: 4·10⁷ → **64**
  (exact `Hold` MGF, not a quadratic bound). `Y`: existential → **150**
  (`renewal_level_le_one` — heights increase by ≥3, so each level is visited at most
  once ⟹ renewal mass per level ≤ 1; **X6 was NOT re-opened**).
- **`epsBW` is FROZEN at `1/10^1000`** (judge's constant, pre-authorized pass 25 on a
  `B ≤ 250`/`Y ≤ 200` envelope). `sep = 100·ln10 ≈ 230.26` vs box `≈ 158.4`.
  🔔 **ε-sweep tripwire RE-ARMED**: any future `epsBW` change fires a full
  re-ratification (list in `judge/pass-18.md`; it has fired and discharged twice).
- 🔓 **ZERO open suspensions** (first time since pass 13).
- **Sorry trail: 14.** 5 crux, all now Case-2/Case-3 assembly:
  `fpDist_fst_mgf_le`, `fpDist_edgeWeight_le`, `fpDist_white_exit`,
  `Q_black_edge_case2` (BlackEdge), `Q_black_edge_case3` (Case3). Plus 9 spine stubs.
  Remaining §7 work is **precedented volume, not novelty**.
- **C8 (§5) is the last un-pinned node** — ratify vs pp.22–25 when statements land.
- 🗂️ **The `ManyTriangles.lean` split is STILL queued** (5,204 lines) — the one
  directive the box keeps ignoring. Pure moves; verify via sorry census + name-based
  axiom runs.

## 🌙 IN FLIGHT RIGHT NOW (2026-07-13 ~22:00 → 06:37)

**A treadmill is running unattended overnight** (opus/high, review-every-5, ~11 laps,
`until 06:37`). `DIRECTION.md` carries an **overnight clause**: the "no spine leaves"
ban is LIFTED, an **unstick ladder** (2 failed attempts on a target ⟹ MOVE), and
**hard rails** — never weaken a statement to make it provable (decompose or leave it
sorried), never touch `Statement.lean`'s two headline sorries, never park a crux sorry
in `wip/`, never self-declare a node verified.

**FIRST THING IN THE MORNING — the boundary pass (pass 26):**
1. `lean-treadmill status tao-collatz --commits 20` — read the night's commits.
2. **`sandbox tao_stmt_diff.py`** (point `REV_OLD/REV_NEW` at the night's range) —
   **statement erosion is the #1 unattended risk.** A weakened theorem compiles green.
3. Dated `#print axioms` on everything it claims. Its claims are hypotheses.
4. `lean-sorry TaoCollatz` — census; check that any count *rise* is honest decomposition
   (good) and not a crux parked in `wip/` (fabricated progress).
5. `/lean-review` over the whole range.
6. Record `judge/pass-26.md`, refresh Live judge state + Campaign log, rotate
   `DIRECTION.md`'s CURRENT DIRECTIVE.

## Hard rules (host/human constraints, not repo facts)

- **NEVER launch or offer to launch a treadmill.** Trevor fires them. Prep it
  launch-ready, hand over the command, stop. Read-only `lean-treadmill status`/`list`
  are fine.
- **Public words are Trevor's**: never post to Zulip / GitHub-upstream / anywhere
  outward; draft and hand over.
- **`epsBW` and altitude-class calls are the JUDGE's**, not the operator's. Trevor has
  explicitly said he has no stake in the numeral — do not manufacture his authority to
  give a directive weight. Say "the judge dictates it."
- **`native_decide` is permitted as scaffolding** (Trevor, 2026-07-13) but must be
  tagged `-- NATIVE_DECIDE:`, does NOT count as judge-verified, and is discharged
  before publication. Prefer `decide +kernel`. It has been needed **zero** times.
- Paper gaps: document in-repo (`formalization-literature-holes.md`), never announce.
- Bare `git` is hook-blocked — use `git-safe`. Judge commits: `git-safe commit
  --no-verify` scoped to verified files. Boxes cannot push; **the judge pushes.**
- `Statement.lean` is the trusted base; its two sorries are the headline stubs, not
  holes to fix.

*Judge passes 1–23 by Ren/Fable; 24–25 by Ren/Opus. Updated at the pass-25 boundary,
2026-07-13.*
