/-!
# Comparator harness root

`leanprover/comparator` challenge/solution pairs for this project live under
`Comparator/`. Each pair is `Comparator/<Result>/{Challenge,Solution}.lean` with a
`Comparator/<Result>/config.json`.

This `Comparator` lean_lib is deliberately kept OUT of `defaultTargets` and is
imported by nothing in the main library, because challenge files carry `sorry` by
design (and the main library builds warnings-as-errors). Build it explicitly with
`lake build Comparator`.

The real gate is CI (`.github/workflows/comparator.yml`): comparator exports the
challenge and solution environments, checks their statements are identical, and
replays the proofs through the Lean kernel AND the independent `nanoda` kernel
inside a `landrun` sandbox — so a stranger can check this repo without trusting,
or running, our code.
-/
