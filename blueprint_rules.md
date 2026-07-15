# Blueprint rules 🗺️

*Brief, and always loaded. The reasoning, the failure modes, and the how-to live in
[`blueprint_architecture.md`](blueprint_architecture.md).*

The blueprint is the map of the campaign. These rules are what keep the map honest. They are
short because they have to be obeyed by every agent, every lap, without re-derivation.

---

## The one rule

> **One node, one claim.** A node's `\lean{}` names *exactly* the declarations that **are** its
> content — no more, no fewer.

Everything below follows from it.

## Pinning a node means writing its Lean statement with `sorry`

Not "naming it." Not "planning it." **Writing it, so it compiles.**

```lean
theorem first_passage_nonescape : … := by sorry   -- ← this IS the pin
```

A pinned node enters the sorry census. An unpinned node does not exist to any instrument except
the dep-graph's color. **Pin early.** Raising the sorry count by pinning is **progress**, not
regress: it converts invisible work into a visible, attackable hole.

## The three states, and what each one renders as

| the node | in TeX | dep-graph | in the sorry census? |
|---|---|---|---|
| **statement not written yet** | no `\leanok` (or `\notready`) | 🟠 **orange border** | ❌ **no — INVISIBLE** |
| **statement pinned, proof owed** | `\leanok` on the statement; the Lean theorem exists, carrying `sorry` | 🟢 **green border**, unfilled | ✅ yes |
| **done** | `\leanok` *inside* `\begin{proof}`, kernel-clean | 🟢 **green fill** | n/a |

**A green border means "the statement is in Lean," never "this is finished."** The *fill* is the
proof.

*(There is a fourth, transient state: **pinned but not yet ratified** — the worker has written the
Lean statement with `sorry`, and the judge has not yet read it against the paper. Leave the node
`\notready`, so it stays **orange** until ratification. That **understates** progress, which is the
safe direction, and it costs nothing: the statement is already in the census, so no work is hidden.
The judge clears it by reading the statement and setting the `\leanok`.)*

## The consequence that matters

**An orange node is the ONLY work the sorry census cannot see.** So:

- **Report remaining work as "N sorries + M orange nodes."** Never the sorry count alone — it
  understates the distance to done, and it is the number everyone quotes.
- The fix for an orange node is not a report, it is a **pin**. Pin it and the gap closes itself.

## A pin is not done until a NUMERIC TRAP checks it 🎯

**Writing the `sorry`-stub makes a node visible. It does not make it faithful.** A statement can be
*born wrong* — a green build, a counted `sorry`, an unmoved differ, and clean axioms all survive a
statement that does not say what the paper says. No mechanical instrument sees it. Two things can:
a human reading the paper against the Lean, and a **numeric instance check**.

So: **every pin ships with an entry in `tools/check_blueprint.py`** — a finite, exact-arithmetic
instance that the intended object passes and a plausible-wrong rendering *fails*. This is not
optional and not "later":

- It fires in the **same lap** the pin is written, not five laps later after machinery has piled on top.
- It makes an unratified pin **safe to build on** — instance-checked even before the judge ratifies it.
- It is the only guard against the highest-value silent failure: *composing on a definition whose
  name looks right but whose body is wrong.*

**A pin with no numeric trap is a claim no instrument can check. Treat it as not-yet-pinned.**
(This rule is written in blood: the C8 v1 pin rendered (5.8) on the ℕ-truncating `Aff` — floor
division where Tao's `Aff_ā` is exact — collapsing thousands of tuples onto one `M`. A one-screen
probe caught it, `19135` vs `0–3`. `check_blueprint.py` existed the whole time; C8 simply was not in
it. See `blueprint_architecture.md`.)

## Six hard rules

1. **Never set `\leanok` yourself.** Statement or proof. **Ratification is the judge's** — a new
   pin is a *claim*, not a fact. Say in your handoff what you pinned and what you pinned it against.
2. **A `\leanok` on a node with no theorem is a FALSE GREEN.** It paints the node finished while
   its content is absent, and a reader who trusts the border routes around it.
   `./tools/blueprint_audit.py` **fails the build** on this. So does a `\leanok` proof the kernel
   does not back.
3. **Statement-`\uses` ≠ proof-`\uses`.** A node's `\uses{}` mostly binds its **proof**. If the
   upstream node's *definitions* exist, **you can pin the statement today** — a proof-dependency
   does **not** block a pin. *This is what lets a scary node be de-risked before a cheap one.*
4. **Statements are copy-not-compose — and this reaches the DEFINITIONS a statement rests on, not
   just its top line.** Render each verbatim against its numbered display in the PDF, mark it
   `RATIFY-<node>`, then freeze. **A pinned statement is faithful only if every non-trivial
   definition it invokes is itself faithful** (ratified, or paper-verbatim). Reusing a plausibly-named
   `def` whose body is subtly wrong hides a wrong object behind a right-looking statement — the C8
   failure. **Never edit a ratified pin** — not to weaken it, not to strengthen it, not to
   generalize it. Blocked? Write `JUDGE-FLAG:` and move on.
5. **A definition's docstring is a claim, held to its code.** `Aff`'s docstring said *"guarded by the
   divisibility"* while its body floored — the reader trusts the prose, the compiler runs the code,
   and the gap is invisible. When you reuse a `def`, read its **body**, not its docstring.
6. **A definition node is not a lemma node.** If a block has defs *and* an estimate, it is **two
   nodes**. Gluing them makes the border and the risk badge report on whichever half is done.

## Why the discipline pays

- **The sorry census becomes the honest distance-to-done.** No hidden work, so no need to track a
  second, invisible category of it.
- **Parallel work becomes safe.** A `sorry`-stub is a *contract*: someone can build on top of your
  node before you have proved it, and the compiler enforces the interface. This is how a
  hundred-node blueprint carries many hands at once.
- **The dep-graph stops lying**, and you can steer by looking at it.
