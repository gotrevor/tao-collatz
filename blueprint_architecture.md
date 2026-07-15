# Blueprint architecture 🏗️

*The reasoning behind [`blueprint_rules.md`](blueprint_rules.md), the failure modes that produced
them, and the how-to. Read this when you are adding nodes, changing the audit, or wondering why a
rule exists. The rules file is the one you must obey; this one is why.*

---

## 1. What this actually is

We use **[leanblueprint](https://github.com/PatrickMassot/leanblueprint)** (plasTeX), the same tool
FLT, PFR, and Sphere Eversion use. It is not homegrown. Source: `blueprint/src/content.tex`.
Build: `./blueprint/build.sh` (which chains `leanblueprint web` + our `annotate_dep_graph.py`
overlay — never run `leanblueprint web` bare, it wipes the overlay).

The dependency graph is generated. **Its colors are the API**, and they mean:

| DOT | rendered | meaning |
|---|---|---|
| `color="#FFAA33"` | 🟠 orange border | `\notready` / no `\leanok` — **the statement is not in Lean** |
| `color=green`, no fill | 🟢 green border | `\leanok` on the statement — **it is in Lean** (usually carrying `sorry`) |
| `color=green, fillcolor="#1CAC78"` | 🟢 filled | `\leanok` inside the proof — **done** |
| pale tint (ours) | risk overlay | `\lapsrisk{laps}{risk}{conf}`, applied only where no status fill exists |

That is the whole model, and it is the one a reader intuits on sight: **border = does the statement
exist; fill = is it proved.** Our job is to not lie to it.

## 2. The failure mode this file exists to prevent

**A node can owe a proof while naming no theorem.** It then has **zero sorries and is not done** —
invisible to `lean-sorry`, invisible to `#print axioms`, invisible to a green build. The only
instrument that sees it is the dep-graph, which renders it **orange**.

We spent months calling this a "**seam**" and building apparatus to detect it. That vocabulary is
**retired**: a seam is just *an orange node*, and the graph was already showing us. Inventing a word
for a color we were already rendering is how a simple system grows a second, worse one on top.

**The real fix is not detection. It is the pin** (rule: pinning = writing the `sorry`-stub). A
pinned node cannot be invisible. Do that consistently and the category ceases to exist.

## 3. Case study — C7, and why *two* instruments lied at once (2026-07-14, judge pass 29)

C7's block was a `\begin{lemma}` whose `\lean{}` named **three definitions** (`passes`, `passTime`,
`passLoc`) and which carried **`\leanok`**. Its actual content was the estimate **(1.19)**,
`P(T_x(N_y) = ∞) ≪ x^{-c}` — **nowhere in Lean.**

Two independent displays both reported on the wrong half of the node:

- **The border went green**, because the *defs* were formalized. It said *"finished — route around
  me."* A reader did exactly that, correctly, and was misled.
- **The risk badge said `low / 5–10 laps / 85%`**, and that estimate had been earned largely by the
  defs already being written. Split out, the lemma alone re-rates to **`medium / 10–18 / 75%`** —
  its one real brick, the integral test, had never been costed.

Meanwhile `blueprint_audit.py` *simultaneously* listed C7 as unfinished, and nothing reconciled the
two — because its false-green gate only ever checked **proof** `\leanok`s, never statement ones.

And there was a third thing hiding underneath: **(1.19) had been absorbed into a *downstream* node's
statement** as the first conjunct of `stabilization` (C9). That is *how* a node ends up owing a proof
while naming no theorem — its content gets written down somewhere else, as part of something bigger.

> 📌 **Two lessons, and they generalize past this repo:**
> **A node that mixes definitions with an estimate will report on whichever half is done.**
> **Content absorbed into a downstream statement leaves a hole upstream that no instrument can see.**

Fixed: split into `C7d` (definition node, done) + `C7` (the lemma, pinned as
`first_passage_nonescape` with a `sorry`, character-identical to the conjunct it was hiding in).

## 3b. Case study — C8, and why a pin needs a numeric trap (2026-07-14, reflection lap)

C8's v1 pin rendered Prop 5.2 (5.8), `∑ ℙ(Aff_ā(N_y) = M)`, by reusing the existing `Aff`
(`Basic/Valuation.lean`):

```lean
noncomputable def Aff (N n : ℕ) (a : Fin n → ℕ) : ℕ := (3 ^ n * N + fnat n a) / 2 ^ pre a n
```

That is **ℕ floor-division**, and its docstring claimed *"paper (1.3), guarded by the divisibility."*
**The docstring lied about the body** — there is no guard. Tao's `Aff_ā` (1.3) is *exact* division,
meaningful (by Lemma 2.1) only at the true valuation vector. Floor-division makes the result depend
on `ā` essentially only through the denominator exponent `|ā|`, so exponentially-many good tuples
collapse onto one `M`. The closing lemma `truncation_error_bound` (error is `O(log^{-c}x)`) is
therefore **FALSE** — the error is super-polylog.

The top-level statement *looked* like (5.8), so "copy-not-compose" appeared satisfied. The infidelity
was one layer down, in a reused definition whose name and docstring both read correctly.

**What saw it, and what did not.** Blind: the green build, `#print axioms` (`sorryAx` is about
proof-completeness, not faithfulness), the sorry census (it counts a pinned node but cannot see a
*wrong* one), the statement differ (the statement was born wrong and never changed), and
`blueprint_audit` (existence + axioms, not semantics). The **only** things that could see it were a
human reading pp.22–25 against the Lean object and a **numeric instance probe** —
`19135` collapsed tuples vs the true `0–3`. A reflection lap (Opus) did both.

> 📌 **The lesson, and the rule it created.** The campaign's D8 statement-trap harness
> (`tools/check_blueprint.py`) is built for *exactly* this — but it did not cover C8, so the trap got
> written five laps late as a throwaway. **A `sorry`-stub makes a node visible; a numeric trap makes
> it faithful.** Rule (`blueprint_rules.md` §"A pin is not done until a numeric trap checks it"):
> every pin ships with an entry in `check_blueprint.py`. Two sub-rules the failure forced: *copy-not-
> compose reaches the definitions a statement rests on*, and *a definition's docstring is a claim
> held to its code — read the body.*

There is also a deeper structural point. The discipline correctly kept C8 **orange** (unratified),
but nothing stopped the box building ~5 laps of proof machinery on the unratified pin before the
reflection lap caught it. **Unratified pins get built upon.** A numeric trap is what makes that safe:
it is the check that stands in for paper-ratification while the judge is still asleep.

## 4. The audit gates (`./tools/blueprint_audit.py`, run in CI)

It **derives** node status from `content.tex` + a **live kernel run** (`lake env lean`,
`#print axioms` on every declaration, defs included). Nothing is hand-maintained. It fails the build
on:

| gate | what it catches |
|---|---|
| **FALSE GREEN** | a `\leanok` *proof* the kernel does not back (`sorryAx`, or the decl is absent) |
| **FALSE STATEMENT-GREEN** | a `\leanok` *statement* on a proof-owing node with **no theorem** — the C7 lie |

And it reports (without failing): **DRIFT** (blueprint names a declaration Lean does not have),
**MISSED FLIP** (everything is axiom-clean but the proof `\leanok` was never set — the blueprint is
*understating* real progress), and **orange nodes**, each annotated with what it blocks and whether
its block is on the **statement** or only the **proof**.

⚠️ **A parser that reads TeX must strip `%` comments first.** Ours did not, so a line of *prose*
containing the string `\leanok` re-greened the node it was merely discussing — found when the comment
written to *document* C7's false green silently re-created it. **An instrument its own documentation
can corrupt is not an instrument.**

## 5. Adding or changing a node

1. Write the Lean **statement** first, with `sorry`. Verbatim against the paper's numbered display.
   Tag it `-- RATIFY-<node>`.
2. Add the block to `content.tex`: right environment (`definition` vs `lemma`/`proposition` — **one
   node, one claim**), `\lean{}` naming exactly its declarations, `\uses{}`, `\lapsrisk{}`.
   **Leave `\leanok` off** — the judge sets it.
3. Run `./tools/blueprint_audit.py`. It must pass.
4. Judge: read the statement against the PDF, set the statement `\leanok`, **add the name to
   `tools/tao_stmt_diff.py`'s watch list** — *ratify ⟹ watch* — and rebuild with `./blueprint/build.sh`.
5. When the proof lands axiom-clean, the judge sets the `\leanok` *inside* the proof.

## 6. `\lapsrisk` — the risk overlay

`\lapsrisk{laps}{risk}{conf}` in `content.tex` is the single source of truth for the estimate; the
overlay (`blueprint/annotate_dep_graph.py`) tints, labels, and tooltips the node from it, and never
overrides a real status fill. **Re-rate a node when you split it** — an estimate made for a bundle
is not an estimate of its parts, and C7's proves it.
