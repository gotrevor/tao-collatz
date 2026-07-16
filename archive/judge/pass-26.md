# Judge pass 26 — 2026-07-14 (overnight boundary; treadmill STILL RUNNING)

**Scope**: treadmill laps 4–8, 47 commits, `e08871e..61f8e80` (~2,800 added Lean lines
across `BlackEdge.lean`, the new `BlackEdgeQ.lean`, `Case3.lean`, `ManyTriangles.lean`).
Judged mid-run: the box was on lap 8 with ~4h left, so this pass was run **in a worktree
pinned at `61f8e80`** (`~/src/tao-collatz-judge26`, CoW `.lake`) rather than in the shared
tree the box is live-editing. Every axiom figure below is from that pinned build.

## Verdict in one line

🏆 **X8 / Case-2 is COMPLETE and judge-verified**, the §7 crux collapsed **5 → 2**, and 20
decls are axiom-clean — **but `61f8e80` edited FOUR ratified statements, including the
paper's Lemma 7.10. Two ratifications are REVOKED.** The route reasoning behind the edit was
right; the edit itself was not the box's to make.

## 1. What the night earned (all verified, not claimed)

**Dated `#print axioms` — 20 decls exactly `[propext, Classical.choice, Quot.sound]`:**

- 🏆 **X8 / Case-2**: `Q_black_edge_case2`, `fpDist_white_exit`, `fpDist_edgeWeight_le`,
  `fpDist_fst_mgf_le`. The review lap's "believed clean, judge to ratify" is now **ratified**.
  **X8 is a COMPLETE NODE — the twelfth.**
- **X9 survives its neighbours moving**: `many_triangles_white`, `fpDist_white_exit_deep`,
  `fpDist_any_triangle_le` all still clean under the X10-chain hypothesis change.
- **X11a/X11c**: `estar_union_le`, `bigTriangle_walk_le`, `fstar_markov`,
  `deterministic_encounter_or_bigTriangle`, `bigTriangle_of_encounter`,
  `reaches_fewWhite_mass_le_ten`.
- **X11d pointwise layer**: `few_white_pointwise_dichotomy`, `few_white_pointwise_split`,
  `few_white_reach_mass_le`, `pathSum_fst_le`, `pathSum_depth_le`.
- **X10 chain (new forms)**: `triangle_encounter_le`, `encounter_apex_proximity` — clean, i.e.
  the new statements are *theorems*. They are simply not the paper's (see §2).

**`sorryAx` (conditional, as expected)**: `damping_column_mass_le`,
`damped_iter_expectation_le`, `damping_expectation_le`, `few_white_mass_le`,
`col_tail_mass_le`, `Q_black_edge_case3`, `Q_black_edge`, `prop_7_8` — all tracing to exactly
the two open sorries.

**Sorry census 14 → 11**: §7 crux **5 → 2** (`few_white_mass_le` (7.56) `Case3:1722`,
`col_tail_mass_le` `Case3:1869`) + `Statement.lean` ×2 (headline stubs) + 7 spine stubs.
The drop came from **proving**, not parking.

**Hard rails 2/3/4 honored**: `Statement.lean` untouched; nothing parked in `wip/`;
`epsBW` character-identical at `1/10^1000`; **zero** `native_decide` (still needed zero times).

**Relocation audit**: `fpDist_white_exit` and `Q_black_edge_case2` moved
`BlackEdge.lean → BlackEdgeQ.lean` — judge-diffed **character-identical**. Ratifications
survive the move (pass-20 precedent).

## 2. 🚨 The finding — `61f8e80` rewrote the deep hypothesis of four ratified lemmas

`61f8e80` ("X11d (7.56): generalize deep hyp to (depth)^0.8<s across X10 chain") swapped

```
((n / 2 - j : ℕ) : ℝ) / Real.log ((n / 2 - j : ℕ) : ℝ) ^ 2 < (s : ℝ)   -- m/log²m < s
        ->  ((n / 2 - j : ℕ) : ℝ) ^ (0.8 : ℝ) < (s : ℝ)                -- m^0.8 < s
```

in **`triangle_encounter_le`** (X10 = Lemma 7.10), **`encounter_apex_proximity`** (X10a,
ratified vs p.53 at pass 19), `bigTriangle_walk_le`, and `estar_union_le`.

### The route reasoning was RIGHT — judge concurs

The frozen `Q_black_edge_case3` places its triangle at row `n/2−m−1`, i.e. **depth `m+1`**,
while its regime hypothesis is `m/log²m < s` (for `m`). Applying the old X10 there needs
`(m+1)/log²(m+1) < s`, and **that does not follow**: `x/log²x` is increasing, and the gap
`(m+1)/log²(m+1) − m/log²m ≈ 1/log²m < 1`, so when `m/log²m` sits just under an integer the
natural `s` clears the old threshold but not the shifted one. HANDOFF-h had planned to
"bridge via Cthr"; lap 8 tried it, found the fractional-part counterexample, and pivoted.
**Judge-verified: the obstruction is real and no largeness rescues the naive bridge.**
The four `(depth)^0.8` lemmas are sound, proved, and clean. **They stay.**

### But it is NOT a "generalization", and it broke the paper binding

The two hypotheses are **incomparable**. `m^0.8 ≤ m/log²m ⟺ log²m ≤ m^0.2`, which holds only
for **m ≳ 10^15.5** (crossover computed exactly). Below that the new hypothesis is *stronger*,
so the new theorem covers **fewer** `s` — a silent restriction, invisible to a green build.

And **Tao p.51 states Lemma 7.10 with `s > m/log²m` verbatim** (m = ⌊n/2⌋ − j):

> *Lemma 7.10 (Large triangles are rarely encountered shortly after a lengthy crossing). Let
> (j,l) be an element of a black triangle Δ with s := l_Δ − l obeying **s > m/log²m** … and
> 1 ≤ s′ ≤ m^0.4 … Then P(E_{p,s′}) ≪ A²(1+p)/s′ + exp(−cA²(1+p)).*

The old pin rendered that hypothesis exactly (and the *conclusion* is still verbatim-faithful —
only the hypothesis moved). So **X10 no longer formalizes Lemma 7.10**, and the blueprint's
`\lean{triangle_encounter_le}` binding for the node is now false.

**Ruling: `triangle_encounter_le` and `encounter_apex_proximity` ratifications are REVOKED.**
Blueprint statement-`\leanok` + proof-`\leanok` come down for X10/X10a until repaired.

### The repair — split, don't revert (mandated in DIRECTION)

The campaign can keep the *stronger* engine **and** recover a faithful Lemma 7.10, cheaply:

1. Rename the four new lemmas `*_rpow` (the engine layer the Case-3 chain consumes).
2. Restore `triangle_encounter_le` / `encounter_apex_proximity` at their character-identical
   `e08871e` statements, proved as **corollaries of the `_rpow` engine**:
   - **m ≥ 10^27**: `log_sq_le_rpow` (already proved, `ManyTriangles:4598`) gives
     `log²m ≤ m^0.2` ⟹ `m^0.8 ≤ m/log²m < s` → apply engine.
   - **m < 10^27**: **trivial**. LHS is a sub-probability ≤ 1; RHS is `C·A²(1+p)/s'` with
     `1 ≤ s' ≤ m^0.4 < 10^10.8` and `A ≥ A₀ ≥ 1`, so `C := max(C_engine, 10^11)` forces
     RHS ≥ 1 ≥ LHS.
   (Judge checked both branches before mandating; ~92%. Fallback: restore the deleted
   `e08871e` proof verbatim — it is proved code.)
3. **Demand**: thread `Cthr ≥ 10^27` through `few_white_mass_le` / `col_tail_mass_le` so the
   depth-`m+1` bridge `(m+1)^0.8 ≤ 2·m^0.8 ≤ m/log²m < s` actually closes (~65× slack at
   `10^27`). It is currently **unproved**, living inside the two open sorries.

**Not a literature hole.** The depth-`m+1` off-by-one is an artifact of *our* encoding (the
`n/2−m−1` row) meeting explicit constants, not an error in Tao — the paper's `≪` notation
absorbs an O(1) shift in `m` legitimately. Do not add it to the gap ledger.

## 3. 🔧 System fixes (this pass caught X10 by luck)

- **The differ's PINNED list was the blind spot.** `encounter_apex_proximity` was rewritten and
  `tao_stmt_diff.py` said *nothing* — the name simply wasn't in the dict. `triangle_encounter_le`
  was caught only because it happened to be listed. Rewrote the tool: **19 pinned names**
  (adding X10a, the frozen Case-3 spine `Q_black_edge_case3`/`Q_black_edge`/`prop_7_8`,
  `many_triangles_white`, and `Statement.lean`'s two headlines), searched **across all files**
  so a relocation reports as a *move* rather than a deletion, and it now takes the rev range as
  argv. **When the judge ratifies a statement, it goes in that list in the same pass.**
- **New HARD RAIL 6 in DIRECTION**: *never EDIT a ratified pin — not to weaken, not to
  strengthen, not to generalize.* The old rail only said "never weaken," and this lap sincerely
  believed it was strengthening. Adding a lemma beside a pin is always allowed; changing the pin
  is the judge's call alone. The pinned set is listed inline in DIRECTION so a grind lap can
  check itself without a round-trip.
- **Judging a live treadmill**: the box bind-mounts the repo and commits with `git add -A`, so it
  will sweep judge docs mid-write (it swept pass-25's into `19ea98d`). Judge in a pinned
  worktree; write docs in one shot; commit promptly.

## 4. Nits (box's, zero soundness impact)

- 7 local `maxHeartbeats` bumps in Sec7 (3 new this range: 4M/2M/1M in `BlackEdge.lean`) lack
  the SKELETON-SPEC `-- HEARTBEAT:` justification comment. Trevor: low risk, mop up in post.
- `61f8e80` asserted "All axiom-clean" flatly rather than "believed clean, judge to verify."
  It was right every time — keep the hedge anyway.

## 4b. ✅ ADDENDUM — the X10/X10a repair is DISCHARGED (2026-07-14, same day)

The first lap of overnight run #2 did the repair as its opening move (`4f51542`, "split
`_rpow` engines + restore Lemma 7.10/X10a pins"), before touching objective 1 — the right
call, and its handoff says so: *"judge pass 26 repair DONE; NEXT = few_white_mass_le
assembly."*

**Machine-checked, not claimed:**
- **`tao_stmt_diff.py e08871e HEAD` → 19/19 character-identical.** `triangle_encounter_le`
  and `encounter_apex_proximity` are byte-identical to the pre-deviation baseline. That was
  the stated re-ratification condition, and it is met.
- **Dated `#print axioms`** (worktree pinned at `b9fa428`) — all exactly
  `[propext, Classical.choice, Quot.sound]`: both restored pins, all four engines
  (`triangle_encounter_le_rpow`, `encounter_apex_proximity_rpow`, `bigTriangle_walk_le_rpow`,
  `estar_union_le_rpow`), and the completed nodes X9 (`many_triangles_white`,
  `fpDist_any_triangle_le`) + X8 (`Q_black_edge_case2`, `fpDist_white_exit`) which survive
  the refactor untouched.
- **`ManyTriangles.lean` has ZERO sorries** — the pins were restored by *proving*, not by
  sorrying. `Case3.lean` still holds exactly the two crux sorries. Spine unchanged:
  `Q_black_edge_case3` / `prop_7_8` carry `sorryAx` from those two alone.

⚖️ **X10 + X10a ratifications RESTORED. Blueprint `\leanok` back up.** Net position: the
campaign gained a strictly stronger engine layer *and* kept a faithful Lemma 7.10 — a better
outcome than either the revert or the mutation.

**Still open from §2 (demand 3):** thread `Cthr ≥ 10^27` so the depth-`m+1` bridge
`(m+1)^0.8 ≤ 2·m^0.8 ≤ m/log²m < s` actually closes. It remains **unproved**, inside
`few_white_mass_le` — which is exactly the sorry now being assembled. Verify it on the next
boundary; do not let it be assumed.

## 5. State after this pass

- **TWELVE verified nodes**: S3, X1, X2, X3, X5, X6, **X8** (new), X9, X10*, C2, C5, X4/X7 files.
  *X10's **proof** is clean but its **statement** is deviated — node is COMPLETE-but-UNRATIFIED
  pending the §2 repair. It is the only node in that state.
- **§7 hinges on exactly two sorries**: `few_white_mass_le` (7.56) + `col_tail_mass_le`.
- **Zero open suspensions** (the X10/X10a revocation is a *repair task*, not a suspension —
  the mathematics is not in doubt, the paper binding is).
- `epsBW` frozen at `1/10^1000`; ε-sweep tripwire remains ARMED.
- C8 (§5) still the last un-pinned node.
