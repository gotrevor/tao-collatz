# Judge pass 29 — 2026-07-14 · boundary pass · `8505bd4..7ff033b` (70 commits)

**Judged in the shared tree** (`lean-treadmill list` → *no running treadmills*; Codex idle; working
tree clean at `7ff033b`). Dated `#print axioms` run 2026-07-14, build cached green.

**Verdict: the range is ACCEPTED, and it is the best range of the campaign since §7 closed.
All three of pass 28's open questions resolve in the work's favour — including the two tripwires.**

---

## 1. The three pass-28 questions, answered by the kernel

Dated run @ `7ff033b`:

| decl | axioms | meaning |
|---|---|---|
| `lRange_hbudget` | ✅ clean triple | **Tripwire #1 discharged.** |
| `osc_mainHigh_bound` | ✅ clean triple | **Tripwire #2 discharged — the A′-absorption is SHOWN.** |
| `mainHigh_eq_restrictedDensity` | ✅ clean triple | `mainHigh` *is* the restricted pushforward. |
| `sum_abs_syracZ_sub_mainHigh_eq` | ✅ clean triple | the error term *equals* `P(¬mainEvent)`. |
| `tailDensW_condWindowB_le` | ✅ clean triple | obl-3 at the full window. |
| `fine_scale_mixing` | 🔴 `sorryAx` | C10 **not** closed — via `error_l1_high_bound` only. |
| `error_l1_high_bound` | 🔴 `sorryAx` | the single remaining C10 hole. |
| `stabilization` | 🔴 `sorryAx` | C9, downstream, untouched. |

### 🔴 Q1 — "Is C10 actually closed, or was the sorry relocated to launder the census?"
**Neither. It is an honest decomposition, and an unusually good one.** The `sorry` moved from
`MixingFromDecay.lean` to a *named* lemma in a new file (`Sec6/MixingError.lean:359`) whose statement
is exactly the quantitative obligation that remains. The census drop 6 → 4 is real work, not
bookkeeping. **Do not let this pass as vindication of the census** — it was right to distrust it; the
instrument that settled it was `#print axioms`, exactly as pass 28 said it would be.

### 🔴 Q2 — `hbudget`
`lRange_hbudget` is axiom-clean **and it is no longer floating**: it is *consumed inside* a proved
theorem (`osc_mainHigh_bound`). A discharge that nothing consumes is a claim; a discharge a proved
theorem depends on is a fact. `C_A = caConst = 30`, tight window, as ruled.

### ⚠️ Q3 — the A′-absorption at `C_A = 30`
Pass 28: *"'absorbed by taking A′ large' is an assertion, not a proof. Make the lap show it."*
**The lap showed it.** `osc_mainHigh_bound` is axiom-clean, and it carries the absorption: the head
decays at the **shifted exponent** `A' = A + C_A²·log 2` (≈ A+624 at C=30), which is what pays for the
`n^{O(C_A²)}` single-point mass that raising `C_A` to 30 bought. `charFn_decay` holds for *every* A′,
so the shift is free. **The judge's stated worry is retired, in Lean.**

---

## 2. What C10 now is — one probabilistic statement, and nothing else

Two machine-checked identities collapse the whole node:

- `mainHigh_eq_restrictedDensity` — `mainHigh` **is** the Syracuse pushforward restricted to `mainEvent`.
- `sum_abs_syracZ_sub_mainHigh_eq` — `∑_Y |syracZ − mainHigh| **=** P(¬mainEvent)`. An **equality**, not a bound.

So `error_l1_high_bound` is, exactly: **`P(¬mainEvent) ≤ (C/2)·m^{-A}`**. Everything else in C10 is
proved. The structural half of §6 is done; what is left is a tail estimate.

---

## 3. ⚖️ RULING — Codex asked for judge attention on `condWindow` being an *enlargement* of Tao's `Eₖ`

Codex's note: *"`condWindow` encodes the suffix inequalities actually consumed by the injectivity
proof; it is an enlargement of the paper's full interval event, not literally all of `Eₖ`."*

**✅ Safe — and the reason generalizes, so record it.**

The event definitions (`condWindow`, `stopEvent`, `condWindowB`, `mainPieceEvent`, `mainEvent`) are
**internal**. They appear nowhere in the pinned statement `fine_scale_mixing`, and they reach the
theorem through exactly two *proved* facts: the exact identity above, and the osc bound
`tailDensW_condWindowB_le` — which is proved **from** the enlarged window, not from the paper's.

> **A wrong internal event choice cannot make the theorem false. It can only make
> `error_l1_high_bound` unprovable. It costs provability, never soundness.**

This is pass 28's principle, mirrored. There, an internal window was *restricted* (ours ⊂ the
paper's) ⟹ a weaker lemma ⟹ risk lived at the call site. Here the good event is *enlarged* ⟹ the
complement is *smaller* ⟹ the remaining tail bound is **easier**, not harder — provided the osc bound
holds on the enlarged event, which is machine-checked. **The enlargement is working for us.**

**But Codex's caution converts into a standing demand, and it is the right one:**

1. **Never document `condWindow` as equal to Tao's `Eₖ`.** It is an enlargement. Say so.
2. **The closing lap must PROVE `globalGood ⊆ mainEvent` explicitly.** Do not gesture at it. That
   inclusion *is* the remaining content — everything downstream of it is already proved.

*The hazard here is pass 28's hazard — a lap grinding at an impossible target — not unsoundness.*

---

## 4. 🐛 The `stopEvent` reversed-coordinate bug — a real faithfulness catch, nearly lost

Codex found and fixed a genuine encoding bug. The tail block is stored **reversed**,
`(a_{k+1}, …, a₁)`, so Tao's `a[1,k]` is `pre vt p − pre vt 1` — **not** `pre vt (p−1)`. The old
definition removed `a₁` instead of `a_{k+1}`, and **did not produce the claimed stopping-time
partition**: the events would not have been disjoint. It compiles green either way.

It is documented in the `stopEvent` docstring (`MixingCore.lean:2169`) — but the commit that fixed it
(`a6ebbb3`) says only *"C10: formalize the stopping partition."* **A finding of this class nearly
went into the record as a five-word commit message.** The disjointness is now *proved*
(`mainPieceEvent_cut_unique`, `mainPieceEvent_index_unique`), which is the machine-checkable form of
the fix and the reason it cannot silently regress.

### 📌 The transferable lesson — a convention that has bitten twice is a HAZARD, not a convention

The D2 reversed-coordinate convention (Tao's footnote-6 variable reversal) was already known well
enough to be **encoded as a trap in the numeric harness** — and it bit anyway, in a new place, deep
into the campaign, in the one definition whose entire job was to be a partition.

**The guard is not vigilance. It is a proved lemma.** New standing rule:

> **Every event definition that claims to be a partition owes a proved disjointness/exhaustiveness
> lemma sitting next to it.** An unproved partition claim is a **seam wearing a definition's
> clothes** — zero sorries, and load-bearing.

That is the same disease the seams (C7/C8) have, one level down. The sorry census cannot see either.

---

## 5. Instruments

- **Statement erosion: 29/29 character-identical** across all 70 commits
  (`./tools/tao_stmt_diff.py 8505bd4 7ff033b`), `fine_scale_mixing` and `stabilization` included.
  **HARD RAIL 6 held through a two-worker range** (treadmill boxes + Codex).
- **`./tools/blueprint_audit.py`** → **13 nodes proved + axiom-clean · 0 drift · 0 false-green ·
  2 seams** (C7 defs-only, C8 nothing at all). The ledger is honest.
- **Baseline: 4 sorries + 2 seams** — C10 `error_l1_high_bound`, C9 `stabilization`, 2 headline stubs;
  seams C7, C8. *Never state this as "4" alone.*
- Differ hardened this pass: `:= by` → `:=` (a proof going term-mode) no longer fires a false
  RATIFICATION-REVOKED on `fine_scale_mixing`. **An over-sensitive guard gets muted, and a muted
  guard is how a real deviation walks through.**

---

## 6. The campaign, re-aimed (Trevor, 2026-07-14): **C10 → C8 → C9**

That order is **forced by the dependency graph**, not chosen: C9 `stabilization` (Prop 1.11) consumes
**both** C10 and C8, and **C8 is a seam with nothing behind it** — no theorem, no sorry, invisible to
the census. Pass 27 ordered C8 pinned before any C9 work starts; it still is not. Doing C9 before C8
would mean proving Prop 1.11 against an unpinned §5, which is how you discover at assembly time that
the thing you cited does not say what you needed.

Written into `DIRECTION.md` as the current directive. Next pass: **30.**

---

*Judge: Ren/Opus, 2026-07-14. Passes 1–23 Ren/Fable; 24–29 Ren/Opus. Workers this range: the
treadmill boxes + an external Codex session.*
