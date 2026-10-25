# DIRECTION — Sec7P: Tao §7 at the pair-sum law `Pascal(p)`, uniform on `p ∈ [1/5, 3/5]` 🌀

*Grind laps READ and OBEY this file; it outranks any handoff.  `blueprint_rules.md` remains
BINDING except where this file scopes it.  `SEC7P-PLAN.md` (this branch) is the campaign
spec — read it in full before lap-1 work; where this file is terse, the plan governs.  The
predecessor campaign (Tier-1 tower tightening, complete 2026-07-18) lives in git history
(`git log --follow DIRECTION.md`).*

> **🔒 ONE OWNER (standing ruling, 2026-07-17).**  This file has exactly one writer: the
> operator/judge layer (host-side).  No lap — grind, review, reflection, or altitude — may
> write DIRECTION.md.  A lap that believes the directive is wrong records the argument in
> `PENDING_WORK.md` as a `JUDGE-FLAG:` and stops the loop with `box stuck`.

---

## 🎯 CURRENT DIRECTIVE (operator, 2026-10-25) — discharge the two Sec7P pins

**This is new mathematics, not formalization.**  Tao proves the §7 damping bound at
`p = 1/2`; nobody has it uniformly on a window of tilts.  It is the input node of a live
research chain in `gotrevor/collatz-moonshot` (`PascalDampingDecay` ⇒ `SliceCharDecay` ⇒
`TruncatedSyracMixing` ⇒ `BiasDecays`).  The paper-level transfer is in `SEC7P-PLAN.md` §1;
it is a sketch, so treat each step as a claim to check, and a step that fails as a finding
to record precisely (`JUDGE-FLAG:` with the failing inequality), never to paper over.

**The pins are planted** in `TaoCollatz/Sec7P/Statement.lean` (plant commit: `git log --grep
'plant the Sec7P'`): five definitions copied verbatim from the moonshot node, and

- `pascalDamping_half_decay` — **calibration**: the `p = 1/2` case.
- `pascal_damping_decay` — **target**: `∀ A > 0, ∃ C > 0, ∀ p ∈ [1/5, 3/5], ∀ n ≥ 1,
  ∀ ξ (3 ∤ ξ), pascalDamping n p ξ ≤ C · n^{-A}`.  `C` is chosen **before** `p`: every
  constant in the proof must be uniform on the window.

You write the PROOFS, never these statements.

**Work order:**

1. **Calibration gate (binding).**  Discharge `pascalDamping_half_decay` from the proved §7
   (`renewal_white_encounters_at`, `cexpect_pairing`'s machinery, `prod_fCond_le_damping`) via
   a convention bridge in `TaoCollatz/Sec7P/Bridge.lean`: `charZ`/`fPair`/`Sec7P.xArg` ↔
   `eC`/`fCond`/`xArg` (ξ moves from the character into the argument; `e` is 1-periodic),
   prefix sum `Σ_{i ≤ j} b i` ↔ `pre b (j+1)`, `pascalWeight (1/2)` ↔ `(pascal b).toReal`,
   the `tsum` over `Fin (n/2) → ℕ` ↔ `(PMF.iid pascal (n/2)).expect`.  State the bridge for
   **general** `p` wherever it does not need `p = 1/2` — step 4 reuses it.  Green gate
   unlocks step 2.  If it fights (the conventions do not match): `JUDGE-FLAG:` with the
   exact mismatch + `box stuck`.  Never grind downstream on a failed gate.
2. **The p-probability layer** (`Sec7P/Prob.lean`, `Sec7P/HoldBasics.lean`,
   `Sec7P/Holding.lean`): `geomP p`, `pascalP p`, `pascalNe3P p` as `PMF`s; the holding law
   `holdP p`; mean `(1/q)·(1, 2/p)` with `q = 2p²(1-p)`; support ⊇ Tao's (hence aperiodicity);
   exponential tail — **each with window-uniform constants** (plan §2).
3. **Prop 7.3 at `Pascal(p)`**, bottom-up through the plan §3 module order, each a
   p-parametrised copy-and-generalize of the corresponding `Sec7/` module into `Sec7P/`,
   importing the p-free modules (`Setup`, `Triangles`, `White`, `Reduction`'s p-free part)
   unchanged.  Decompose into named sub-`sorry`s freely — raising the Sec7P sorry count by
   decomposition is progress.
4. **Assemble** `pascal_damping_decay` = pairing bound at `p` (bridge, step 1) +
   `prod_fCond_le_damping` (p-free) + Prop 7.3 at `p` (step 3).  Discharge LAST.

**Operator rulings, recorded — do not relitigate in-lap:**

- **Copy-and-generalize into `Sec7P/`; existing files are read-only** (except one `import`
  line per new module in `TaoCollatz.lean`).  The summit library stays byte-identical; a
  post-campaign refactor (generalizing `Sec7/` itself) is a coordinator call, not lap work.
- **`ε` is the lap's choice.**  The target is `ε`-free.  If the window needs a smaller `ε`
  (e.g. Lemma 7.4's separation vs a p-dependent localization box), define `blackP`/`whiteP`
  at a new `ε` in `Sec7P/` — never edit `epsBW`.
- **Existential constants are fine.**  No explicit-constant (`_at` / big-C) machinery this
  campaign; prove `∃ C` forms.  Window-uniformity is the only constant discipline.
- **Legibility matters** — named lemmas, docstrings that say which paper step a lemma
  generalizes and how `p` enters.  No copy-paste sprawl where a `p`-general lemma would do.

## 🔒 Hard rails (the differ adjudicates)

- **FROZEN**: every pin `tools/tao_stmt_diff.py` watches — the 39 summit pins and the 7
  Sec7P pins (5 defs + 2 theorems).  Run `tools/tao_stmt_diff.py <plant-commit> HEAD` every
  commit; it must print **46/46 character-identical** for the whole campaign.
- **Read-only paths**: `TaoCollatz/` outside `Sec7P/` (bar the import lines), `Comparator/`,
  `BLUEPRINT.md`, `blueprint/**`, `judge/**`, `DIRECTION.md`, `STATUS.md`, `tools/`.
  Sec7P nodes are tracked in `SEC7P-PLAN.md` §4's node table (the lap may edit that table),
  not in the blueprint; blueprint reconciliation is the coordinator's after the campaign.
- **Sorries live only in `TaoCollatz/Sec7P/`.**  Every Sec7P `sorry` carries its own
  `set_option warningAsError false in` shield (CI builds warnings-as-errors); a discharge
  removes the `sorry` and its shield together.  `./tools/blueprint_audit.py` must stay green.
- **`pascalDamping` is a `tsum`**: summability is something you prove (weights are a
  probability, factors are `≤ 1`), never something you exploit.
- **Axioms**: at discharge, `#print axioms pascal_damping_decay` (and `_half_decay`) =
  exactly `[propext, Classical.choice, Quot.sound]`.  No `native_decide`; `-- HEARTBEAT:`
  on any local bump.
- **Branch `ren/sec7p-pascal` only.**  Commit + push there.  Never touch `main`.

## 🛑 Stop discipline

- **Primary: `--done-when sorry-free:TaoCollatz/Sec7P`** — the host halts the run when the
  Sec7P directory is sorry-free.  With "discharge LAST", that is campaign completion.
- `--require-decls` guards the five defs and both pins against deletion.
- `box stuck` is the escalate lane (failed calibration gate, a transfer step that is false
  as stated, an unanswered `JUDGE-FLAG`).  `--max-duration` is the backstop.

## 📝 Report per lap

"sec7p: calibration {state}; prob-layer {k}/{total}; Prop 7.3@p modules {k}/{total};
Sec7P sorries {n}; differ 46/46 {yes/no}; blockers".
