# tao-collatz — always-loaded context

Formalizing Tao 2019, *Almost all orbits of the Collatz map attain almost bounded values*
(arXiv:1909.03562v5), in Lean 4 + mathlib. Target: Theorem 1.3, zero sorries, zero axioms beyond
`[propext, Classical.choice, Quot.sound]`.

## Read these, in this order

1. **`DIRECTION.md` → CURRENT DIRECTIVE.** The judge writes it. **It outranks every handoff**, and it
   is re-read every lap — so it is also how a running treadmill gets redirected mid-flight.
2. The newest `HANDOFF-*.md` — the previous lap's baton.
3. `PENDING_WORK.md` — open items and attack paths.

The judge's seat: **`judge/JUDGE.md`** (standing brief) → newest `judge/HANDOFF-JUDGE-*.md` (live state).

## The blueprint rules — binding

@blueprint_rules.md

*(Reasoning, failure modes, how-to: `blueprint_architecture.md`.)*

## House rules

- **Statements are copy-not-compose.** Render verbatim against the paper's numbered display, tag
  `-- RATIFY-<node>`, then freeze. **Never edit a ratified pin** — not to weaken, not to strengthen,
  not to generalize. Blocked? Write **`JUDGE-FLAG:`** in `PENDING_WORK.md` + your handoff, and move on.
- **A `sorry` is honest; a weakened theorem is a lie that compiles.** If a statement will not yield,
  **decompose it** into named sub-`sorry`s and prove what you can. **Raising the sorry count that way
  is PROGRESS.**
- **Never claim a node "COMPLETE" or "verified."** Report `#print axioms` output as *evidence* and
  write *"believed clean, judge to verify."* The judge's dated run is what makes it true.
- **Report remaining work as "N sorries + M orange nodes"** — never the sorry count alone (see the
  blueprint rules above; the census cannot see an unpinned node).
- Prefer **`decide +kernel`** over `native_decide` (which trusts the compiler and plants an axiom).
  If you must, tag it `-- NATIVE_DECIDE:`.
- Local `maxHeartbeats` bumps need a `-- HEARTBEAT:` justification comment.
- **Commit green, commit often.** A lap that ends with uncommitted work has thrown it away.
- Bare `git` is hook-blocked → use `git-safe`.
