/-
Comparator SOLUTION for TaoCollatz.

Imports the development and declares NOTHING (the "strong pattern"): every
constant the challenge names — the definitions AND the anchor theorems — is
already present under its real fully-qualified name via `TaoCollatz.Basic.Anchors`
(which pulls in `Basic.Collatz` and `Basic.LogDensity`). `leanprover/comparator`
checks each `theorem_names` entry in `config.json` is proved here against
definitions byte-identical to `Challenge.lean`'s Mathlib-only rendering.
-/
import TaoCollatz.Basic.Anchors
