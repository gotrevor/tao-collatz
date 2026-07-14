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

**And the judge's own failure mode, from the same pass: judging the artifact without
reading the reasoning.** Verify with machines, but *understand* with the handoffs — a
worker's stated reasoning is evidence, and skipping it turns a sound-route-wrong-move into
a rail violation you'd wrongly revert. Machine-check everything; read before you rule.

*Judge passes 1–23 by Ren/Fable; 24–26 by Ren/Opus. Updated at the pass-26 boundary +
addendum, 2026-07-14 (overnight run #2 in flight).*
