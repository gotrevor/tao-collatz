# TaoCollatz

A complete Lean 4 formalization of Terence Tao's
**"Almost all orbits of the Collatz map attain almost bounded values"**
([arXiv:1909.03562](https://arxiv.org/abs/1909.03562), *Forum of Mathematics, Pi*, 2022).

**Headline theorems** (`TaoCollatz/Statement.lean`, the repo's only trusted statement surface):

- `TaoCollatz.tao_collatz` — **Theorem 1.3**: for any `f : ℕ → ℝ` with `f(N) → ∞`,
  almost all `N` (in logarithmic density) satisfy `Colmin(N) < f(N)`.
- `TaoCollatz.tao_collatz_quantitative` — **Theorem 3.1** (`Colmin` form): the log-probability
  that `Colmin(N) ≤ N₀` on `[1, x]` is at least `1 − C/(log N₀)^c`.

Both are **sorry-free and axiom-clean**: `#print axioms` yields exactly
`[propext, Classical.choice, Quot.sound]` (kernel-checked across all 114 blueprint
declarations by `tools/blueprint_audit.py`, 2026-07-15).

## Verify it yourself — without trusting this repo

The [`leanprover/comparator`](https://github.com/leanprover/comparator) harness lets you check
the result against an independent, Mathlib-only rendering of every definition the headlines
are stated in:

- `Comparator/TaoCollatz/Challenge.lean` — the **human audit surface**: the trusted vocabulary
  (`col`, `colMin`, log density, `AlmostAllPos`) re-declared from scratch over plain Mathlib,
  five non-vacuity anchors, and the two headline statements. Read this one small file against
  the paper; comparator machine-checks everything else.
- CI (`.github/workflows/comparator.yml`) replays the proofs through Lean's kernel **and the
  independent `nanoda` kernel** (`enable_nanoda: true`), enforces the three-axiom whitelist,
  and runs sandboxed under `landrun`.
- Local pre-flight of the statement-identity check: `scripts/comparator-probe`.

Provenance metadata: [`formalization.yaml`](formalization.yaml).

## How it was built

This is an **AI-authored formalization**, built by autonomous Claude (Anthropic) agent runs
over a human-ratified skeleton: statements were pinned verbatim against the paper's numbered
displays and frozen; a machine-audited dependency blueprint (below) tracked every node; an
autonomous "treadmill" ground out the proofs under a build-green + axiom-clean gate, with
periodic judge passes re-reading statements against the PDF. The full lap-by-lap history is
preserved in `archive/handoff/` and `judge/`.

Trusted base for a skeptical reader: `TaoCollatz/Statement.lean` (the statements),
`Comparator/TaoCollatz/Challenge.lean` (the independent rendering), and the kernel.
Everything else is machinery.

## Blueprint

The dependency blueprint (per-node status, paper cross-references, dep graph) lives in
`blueprint/`; rebuild locally with `./blueprint/build.sh`, or browse it on GitHub Pages
once deployed (`.github/workflows/docs.yml`).

## Build

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build           # the development (warnings-as-errors)
lake build Comparator  # the comparator harness (challenge stubs carry sorry by design)
```

Toolchain and Mathlib pin live in `lean-toolchain` / `lake-manifest.json` (Lean v4.31.0).

## License

[Apache License 2.0](LICENSE). Copyright 2026 Trevor Morris.
