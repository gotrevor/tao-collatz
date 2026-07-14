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
   **Next pass number: 27.**
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

## Where things stand (post-pass-26, 2026-07-14 morning)

- **TWELVE verified nodes** (dated runs): S3, X1, X2, X3, X5, X6, **X8** (new, pass 26),
  X9, X10*, C2, C5 (+ X4/X7 files sorry-free). 🏆 Both pinnacle kernels (X9, X10) are proved.
- ✅ **The X10/X10a deviation is CLOSED** (pass-26 finding → discharged same day, `4f51542`).
  An unattended lap rewrote the deep hypothesis of the Lemma-7.10 pins `m/log²m < s` →
  `m^0.8 < s`, calling it a "generalization." It is not one — the hypotheses are
  **incomparable** (they cross at `m ≈ 10^15.5`; below that the new form covers *fewer* `s`)
  and Tao p.51 states Lemma 7.10 with `s > m/log²m` verbatim. Repair = **split, don't
  revert**: the four weaker-hypothesis lemmas live on as `*_rpow` **engines**, both pins were
  **restored character-identically** and re-proved as corollaries. Differ: **19/19
  byte-identical**; dated runs on both pins + all four engines clean. **Ratifications
  RESTORED, `\leanok` back up.** Full story: `judge/pass-26.md` §2 + §4b.
- **§7 now hinges on exactly TWO sorries**: `few_white_mass_le` (7.56) + `col_tail_mass_le`
  (both `Case3.lean`). Repo total 11 (2 crux + 2 headline stubs + 7 spine).
- ⚠️ **THE ONE UNVERIFIED STEP — check this first.** The Case-3 consumer sits at depth
  `m+1`, and `m/log²m < s ⟹ (m+1)/log²(m+1) < s` **genuinely fails** (`x/log²x` increasing;
  fractional-part counterexample). The chain closes only by threading **`Cthr ≥ 10^27`**, so
  that `(m+1)^0.8 ≤ 2·m^0.8 ≤ m/log²m < s` (≈65× slack). **That bridge is still UNPROVED** —
  it lives inside `few_white_mass_le`, the sorry being assembled right now. It closes on the
  judge's arithmetic, which is *not* the same as closing in Lean. It is exactly the kind of
  step an assembly quietly assumes. **Do not accept `few_white_mass_le` without seeing the
  `Cthr` largeness discharged.**
- 🔒 **HARD RAIL 6 (new)**: *never EDIT a ratified pin — not to weaken, not to strengthen,
  not to generalize; flag the judge.* The 19-name pinned set is listed inline in DIRECTION
  and enforced by `tools/tao_stmt_diff.py` (which now takes revs as argv and searches
  across files, so a relocation reports as a move). **Ratify a statement ⟹ add it to that
  list in the same pass** — pass 26's near-miss was X10a's rewrite going unreported because
  its name simply wasn't in the dict.
- 🧰 **Judge a LIVE treadmill from a pinned worktree.** The box bind-mounts the repo and
  commits `git add -A` (it swept pass-25's docs into its own commit). Use
  `lean-create-worktree tao-collatz ~/src/tao-collatz-judgeNN --start-point <range-end>`
  (CoW `.lake`, builds in ~2 min) and run every `#print axioms` there.
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
- 🔓 **ZERO open suspensions.**
- **C8 (§5) is the last un-pinned node** — ratify vs pp.22–25 when statements land.
- 🗂️ **The `ManyTriangles.lean` split is STILL queued** (now ~5,500 lines) — queued for
  **seven laps**. It is now **objective 3** in DIRECTION, not a fallback. Pure moves;
  verify via sorry census + name-based axiom runs.

## 🌙 IN FLIGHT RIGHT NOW — overnight run #2 (2026-07-14 ~03:10 → ~10:45)

`lean-treadmill tao-collatz --max-duration 7h --effort high --model opus --review-every 5`
(Trevor fired it; the judge never does.) `DIRECTION.md` carries **three objectives**:

1. **Close the two §7 sorries** — `few_white_mass_le` (E∗ term + assembly, HANDOFF-h steps
   3–5), then `col_tail_mass_le`. When both land, `Q_black_edge_case3 → Q_black_edge →
   prop_7_8` go axiom-clean and **§7 monotonicity is DONE**.
2. **The X10/X10a repair** — ✅ already discharged, first lap (`4f51542`).
3. **🗂️ Burn down the fruit** — the `ManyTriangles` split, the 7 spine stubs, pin C8.
   **This is an ORDER, not a fallback.** *Last night's lesson*: the fruit sat in an
   "unstick ladder" reachable only when stuck; the box was never stuck, so it correctly
   touched **none** of it. Fixed — but **verify it actually got done this time.**

Plus **HARD RAIL 6** (new): *never EDIT a ratified pin — not to weaken, not to strengthen,
not to generalize.* When a pin blocks a lap and no judge is awake, it writes a
**`JUDGE-FLAG:`** in `PENDING_WORK.md` + its handoff and **moves on**. Adding a lemma
*beside* a pin is always allowed (that is how the `*_rpow` engines were born). Grep for
`JUDGE-FLAG:` first thing — it means a lap hit a wall it was forbidden to route around.

**FIRST THING IN THE MORNING — the boundary pass (pass 27):**
0. **Spin a pinned worktree** — the box is live in the shared tree:
   `lean-create-worktree tao-collatz ~/src/tao-collatz-judge27 --start-point <HEAD>`
   (CoW `.lake`, builds in ~2 min). Run every axiom check *there*.
1. `lean-treadmill status tao-collatz --commits 30` — read the night's commits.
2. **`./tools/tao_stmt_diff.py <last-judged> <HEAD>`** — **statement erosion is the #1
   unattended risk; it fired for real on pass 26.** A restricted theorem compiles green,
   keeps clean axioms, and never moves the sorry census. The differ is the ONLY instrument
   that sees it. It takes the revs as argv and watches **19 pinned names across all files**
   (so a relocation reports as a *move*, not a deletion).
3. Dated `#print axioms` on everything it claims. **Worker claims are hypotheses.**
4. ⚠️ **Verify the `Cthr ≥ 10^27` bridge** if `few_white_mass_le` landed (see above). This
   is the one step most likely to be silently assumed.
5. `lean-sorry TaoCollatz` — census; a count *rise* is honest decomposition (good), a crux
   in `wip/` is fabricated progress (bad).
6. **Did objective 3 happen?** `git log --oneline -- TaoCollatz/Syracuse TaoCollatz/Sec5
   TaoCollatz/Sec6 TaoCollatz/Basic` and `wc -l TaoCollatz/Sec7/ManyTriangles.lean`.
7. `/lean-review` over the whole range. (Standing nit: 7 local `maxHeartbeats` bumps in
   Sec7 lack `-- HEARTBEAT:` comments. Trevor: low risk, mop up in post.)
8. Record `judge/pass-27.md`, refresh Live judge state + Campaign log, rotate
   `DIRECTION.md`'s CURRENT DIRECTIVE, **and add any newly-ratified statement to the
   differ's `PINNED_NAMES` in the same pass** (that list *is* the guard).

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

## The one lesson pass 26 bought (do not re-learn it)

**A green build cannot see a statement deviation.** A restricted theorem compiles. A
weakened theorem compiles. A theorem that has quietly stopped matching the paper compiles,
keeps a clean `#print axioms`, and never budges the sorry census — because `#print axioms`
certifies the **proof**, never the **statement**.

The only instruments are (a) a character-diff against a ratified baseline and (b) a human
reading the PDF. **Both are yours.** And the differ only sees names that are *in its list* —
pass 26's near-miss was `encounter_apex_proximity` being rewritten with the tool silent,
because nobody had added it. **Ratify a statement ⟹ add it to `PINNED_NAMES` that same pass.**

Corollary for directives: *"never weaken a statement"* is not a sufficient rail. A worker
that believes it is **strengthening** will sail straight through it. Say **"never edit a
ratified pin"** and give it somewhere to go instead (`JUDGE-FLAG:` + move on).

*Judge passes 1–23 by Ren/Fable; 24–26 by Ren/Opus. Updated at the pass-26 boundary +
addendum, 2026-07-14 (overnight run #2 in flight).*
