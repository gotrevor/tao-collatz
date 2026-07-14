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
   **Next pass number: 28.**
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

## Where things stand (post-pass-27, 2026-07-14 morning)

- 🏆🏆 **§7 IS COMPLETE AND JUDGE-VERIFIED (pass 27) — the campaign's stated 65–75% risk
  concentration is RETIRED.** `prop_7_8` no longer carries `sorryAx`. All of X1/X2/X3/X5/X6/
  X8/X9/X10/X11 + the §7 spine (`Q_black_edge_case3`, `Q_black_edge`, `Q_polynomial_decay`)
  and both exports (`charFn_decay` Prop 1.17, `key_fourier_decay` Prop 7.1) are axiom-clean on
  dated runs. Plus the **reduction floor**: `colMin_eq_syrMin_oddPart` (paper (1.2)) + the
  SyracRV identities (Lemma 1.12, (1.21), (1.22)). With S3/C2/C5 that is **13+ verified nodes**.
- ✅ **The `Cthr` bridge — pass 26's ONE unverified step — is DISCHARGED** (pass 27), kernel-
  checked at `Case3.lean:2011–2068`: `(m+1)^0.8 ≤ 2m^0.8`, `log²m ≤ 400·m^0.1`, hence
  `(m+1)^0.8·log²m ≤ 800·m^0.9 ≤ m`, then `< s` by the paper hypothesis. **And the judge's own
  numeral was WRONG**: the largeness is consumed at `800 ≤ m^0.1`, which at pass-26's `10^27`
  reads `501 < 800` — *the route fails*. The box independently baked **`10^30`** and **its
  constant is what carried the proof.** 📌 **A judge-supplied numeral is a hypothesis too.**
- ✅ **The X10/X10a deviation is CLOSED** (pass-26 finding → discharged `4f51542`, holds at
  pass 27 — both pins still byte-identical). An unattended lap had rewritten the deep
  hypothesis `m/log²m < s` → `m^0.8 < s`, calling it a "generalization." It is not one — the
  hypotheses are **incomparable** (they cross at `m ≈ 10^15.5`) and Tao p.51 states Lemma 7.10
  with `s > m/log²m` verbatim. Repair = **split, don't revert**: the weaker-hypothesis lemmas
  live on as `*_rpow` **engines**; both pins restored character-identically as corollaries.
- **The repo now hinges on exactly TWO sorries** (+2 frozen headline stubs): **C10**
  `fine_scale_mixing` (Prop 1.14, §6, `Sec6/MixingFromDecay.lean:573`) and **C9**
  `stabilization` (Prop 1.11, §5, `Sec5/FirstPassage.lean:81`, consumes C10). Critical path:
  **C10 → C9 → C6 → Statement**. Census **4**, down from 11, all cleared by *proving*.
- 🔒 **HARD RAIL 6 — and its pass-27 EXTENSION.** *Never EDIT a ratified pin — not to weaken,
  not to strengthen, not to generalize; flag the judge.* **Extended: that now covers the two
  OPEN crux statements** (`fine_scale_mixing`, `stabilization`). A lap weakening the very
  statement it is trying to prove is the highest-value silent failure available — a green
  build, a clean `#print axioms`, and an unmoved sorry census **cannot see it**.
- 🔧 **The differ was aimed at the finished half of the proof (pass-27 system fix).** Pass 26
  grew it to 19 names — but all 19 were §7 + `Statement`, and §7 is now *done*. The two live
  sorries were **unwatched, in files it did not even search**. Now **29 names / 13 files**,
  with a documented distinction: **WATCHED ≠ RATIFIED** (a name in the list means the differ
  *reports changes*; ratification is the judge's separate reading against the PDF — so watching
  an un-ratified statement is strictly good, it is how you *see* the frontier move).
  📌 **Ratify ⟹ watch (pass 26). And when the frontier moves, MOVE THE GUARD WITH IT (pass 27).**
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
- 🔓 **ZERO open suspensions.** Zero `JUDGE-FLAG:`s outstanding.
- 🟡 **C8 (§5) is the last un-pinned node — and it is now BLOCKING.** C9 `stabilization` lives
  in §5, directly downstream of C10 on the critical path. **Pin it vs pp.22–25 before C9 work
  starts**, or a lap will be proving toward an unratified target.
- 🗂️ **The `ManyTriangles.lean` split is DROPPED from the directive (pass 27).** It was ordered
  and skipped for **eight consecutive laps** — correctly every time, because a crux outranks
  hygiene. Re-ordering it a ninth time would be a fake order. It is off the critical path, and
  splitting the 5,519-line file that holds the X9/X10 pins *during* the crux is churn we do not
  want. Moved to post-§6 mop-up, batched with the 8 new `mul_le_mul_left'` deprecations in
  `Case3.lean`. 📌 *If you order something three times and it never happens, the order is wrong
  — not the worker.*

## 🌙 IN FLIGHT RIGHT NOW — overnight run #2 (2026-07-14 ~03:10 → ~11:27)

`lean-treadmill tao-collatz --max-duration 7h --effort high --model opus --review-every 5`
(Trevor fired it; the judge never does.) **Pass 27 judged laps 1–6 mid-run** (53 commits,
`4f51542..8505bd4`) and rotated `DIRECTION.md` to a single objective:

**🎯 THE ONE OBJECTIVE: prove C10 `fine_scale_mixing` (Prop 1.14, §6).** Not a new analytic
kernel — both hard ingredients are proved and clean (the density-general CS/Parseval bridge
`osc_le_sqrt_highfreq`, and `charFn_decay`). C10 is the §6 **conditioning assembly**. Bricks
d/a/b all landed overnight and are judge-verified clean. **What remains** (per DIRECTION):
1. **[the last real novelty] tail factor ⟹ `charFn_decay`** — reindex the tail char at modulus
   `3^(j+p)` down to the level-`p` char at `ξ'`. ⚠️ *The step most likely to be waved through
   with a plausible-looking cast. Read it against pp.28–31; do not just check its axioms.*
2. **osc bound for `condDens`**; 3. **conditioning events + reassembly** ((6.2)–(6.10)).

**HARD RAIL 6, EXTENDED (pass 27)**: *never EDIT a ratified pin — not to weaken, not to
strengthen, not to generalize* — **and that now covers the two OPEN crux statements**
(`fine_scale_mixing`, `stabilization`), which are in the differ's watch list. When a pin blocks
a lap and no judge is awake, it writes a **`JUDGE-FLAG:`** in `PENDING_WORK.md` + its handoff
and **moves on**. Adding a lemma *beside* a pin is always allowed (that is how the `*_rpow`
engines were born), and decomposing *below* a crux into named sub-`sorry`s is encouraged. Grep
for `JUDGE-FLAG:` first thing — it means a lap hit a wall it was forbidden to route around.

**THE BOUNDARY PASS (pass 28) — the recipe, in order:**
0. **Spin a pinned worktree** — the box is live in the shared tree:
   `lean-create-worktree ~/src/tao-collatz ~/src/tao-collatz-judgeNN --start-point <HEAD>`
   (note: **absolute path** for the base, CoW `.lake`, builds in ~2 min). Run every axiom check
   *there*. ⚠️ A `judge/pass-NN` worktree may already exist from the prior pass — reuse it
   (`git-safe -C <wt> checkout --detach <pin>`), don't fight it.
1. `lean-treadmill status tao-collatz --commits 30` — read the night's commits.
1b. **📖 READ THE LAPS' OWN HANDOFFS** — `ls -t HANDOFF-*.md | head -5`, plus
   `PENDING_WORK.md`'s top. **Do this BEFORE you rule on anything they did.** ⚠️ *This step
   exists because pass 26's judge skipped it and Trevor had to intervene.* The machine
   evidence (diff, axioms, census) tells you **what** changed; only the handoffs tell you
   **what the lap was thinking**, and the verdict often turns on that. Pass 26's X10 edit
   read as a careless rail violation until the handoffs showed the lap had *planned* the
   `Cthr` bridge, *tried* it, hit a genuine fractional-part counterexample, and pivoted
   deliberately. That reframe is the whole reason the ruling became "split, don't revert"
   (keeping a stronger engine) instead of a revert that would have thrown the insight away.
   **A worker's reasoning is evidence. Read it, then judge it — in that order.**
   (Corollary: a lap that hit a wall it was forbidden to route around leaves a
   **`JUDGE-FLAG:`** — grep for it.)
2. **`./tools/tao_stmt_diff.py <last-judged> <HEAD>`** — **statement erosion is the #1
   unattended risk; it fired for real on pass 26.** A restricted theorem compiles green,
   keeps clean axioms, and never moves the sorry census. The differ is the ONLY instrument
   that sees it. It takes the revs as argv and watches **29 names across 13 files** (so a
   relocation reports as a *move*, not a deletion). ⚠️ **`fine_scale_mixing` (C10) is the
   name to look at first** — it is the statement the box is under the most pressure to
   quietly make provable.
3. Dated `#print axioms` on everything it claims. **Worker claims are hypotheses.**
4. ⚠️ **Read the C10 tail-factor reindex against pp.28–31** (the `3^(j+p)` → level-`p` char
   at `ξ'` step). By the box's own account it is C10's last real novelty, which makes it the
   step most likely to be waved through with a plausible-looking cast. *This slot is where
   pass 27 put the `Cthr` bridge — and the bridge checked out. Keep using the slot.*
5. `lean-sorry TaoCollatz` — census; a count *rise* is honest decomposition (good), a crux
   in `wip/` is fabricated progress (bad). Baseline after pass 27: **4**.
6. **Is C8 pinned yet?** (`grep -rn RATIFY-C8 TaoCollatz/`) — it blocks C9.
7. `/lean-review` over the whole range. (Standing nits: 7 pre-existing `maxHeartbeats` bumps
   in Sec7 lack `-- HEARTBEAT:` comments, + 8 `mul_le_mul_left'` deprecations in `Case3.lean`.
   Trevor: low risk, mop up in post.)
8. Record `judge/pass-NN.md`, refresh Live judge state + Campaign log, rotate
   `DIRECTION.md`'s CURRENT DIRECTIVE, **and add any newly-ratified statement to the
   differ's `PINNED_NAMES` in the same pass** (that list *is* the guard).
   📌 **And check the guard still points at the frontier.** Pass 27's finding: the differ's
   19 names were all §7 + `Statement` — correct for pass 26, *obsolete the moment §7 closed*,
   leaving the two live sorries unwatched. **A guard that only covers completed nodes has
   stopped working.** When the frontier moves, move the guard with it, in the same pass.

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

**And the judge's own failure mode, from the same pass: judging the artifact without
reading the reasoning.** Verify with machines, but *understand* with the handoffs — a
worker's stated reasoning is evidence, and skipping it turns a sound-route-wrong-move into
a rail violation you'd wrongly revert. Machine-check everything; read before you rule.

## The two lessons pass 27 bought

**1. A guard that only covers completed nodes has stopped working.** Pass 26 fixed the differ's
blind spot by growing its list to 19 names — every one of them §7 or `Statement`. That was
right *that day*. But the moment §7 closed, the guard was pointing at the part of the proof
nobody was editing any more, and was blind to the two live sorries — the statements a lap is
under the most pressure to quietly make provable. **The guard must follow the frontier, and
"ratify ⟹ watch" is only half the rule; the other half is "when the frontier moves, move the
guard."** Watching an un-ratified statement is not a category error — it is how you *see* the
frontier move.

**2. A judge-supplied numeral is a hypothesis too.** Pass 26 handed the box `Cthr ≥ 10^27` as
the constant that closes the depth-`m+1` bridge, and wrote it into the handoff in bold. It is
**wrong** — the largeness is consumed at `800 ≤ m^0.1`, and `(10^27)^0.1 ≈ 501 < 800`. The box
worked out that it needed `10^30` and used that instead. The judge's arithmetic got checked by
the worker, which is exactly the right direction for it to fail in — but *only* because the
proof was kernel-checked rather than accepted on the judge's say-so. **Hold your own numbers to
the standard you hold theirs.**

*Judge passes 1–23 by Ren/Fable; 24–27 by Ren/Opus. Updated at the pass-27 boundary,
2026-07-14 (overnight run #2 still in flight, until ~11:27).*
