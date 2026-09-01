/-
Comparator SOLUTION for TaoCollatz.

Imports the development and declares NOTHING (the "strong pattern"): every
constant the challenge names — the definitions, the anchor theorems, AND the two
headlines — is already present under its real fully-qualified name.
`TaoCollatz.Statement` supplies the headlines (and pulls in the full proof spine);
`Basic.Anchors` supplies the non-vacuity anchors. `leanprover/comparator` checks
each `theorem_names` entry in `config.json` is proved here against definitions
byte-identical to `Challenge.lean`'s Mathlib-only rendering.
-/
import TaoCollatz.Statement
import TaoCollatz.Basic.Anchors
