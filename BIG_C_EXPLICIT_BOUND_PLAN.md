# Explicit big-C restart plan — assembled tower route

**Status:** launch-ready proposal, not a live directive. `DIRECTION.md` currently closes the
old `CTao = 10^(10¹¹)` campaign and forbids further grind work. Only the operator/judge may
activate this plan by replacing that directive. Until then, workers stop after reading it.

## Decision

The stopped campaign mixed two different objectives:

1. prove that the frozen, small numeral `CTao = 10^(10¹¹)` bounds the development's
   multiplicative constant; and
2. exhibit some closed Lean term for a multiplicative constant and prove the quantitative
   theorem at that term.

The evidence in checks 19 and 23 obstructs the first route through the frozen §7 proof. It
does **not** obstruct the second. The existing proof already carries an explicit tower
constant through `C_renewalWhite`, `C_fineScale`, `C_stab`, `C_windowBad`, and finally
`C_spine X`. Fresh `#print axioms` output for `renewal_white_encounters_at` and
`tao_collatz_quantitative_spine_atC` is exactly
`[propext, Classical.choice, Quot.sound]`; the route is believed clean, judge to verify. The
only non-closed input left is the cutoff parameter `X` supplied by
`tao_syracuse_quantitative_sum_atC`.

The restart therefore finishes the abandoned **X-chase**, defines the resulting closed
tower-valued constant, and proves an additive theorem at that constant. It does not touch the
frozen pin, does not use `Q_black_edge_tight`, and does not need new §7 mathematics.

## Exact deliverable

Add `TaoCollatz/ExplicitBigC.lean`, importing `TaoCollatz.Statement`, with declarations of
this shape (names are part of the plan):

```lean
namespace TaoCollatz

/-- The fully assembled cutoff on the clean, as-written proof route. -/
noncomputable def X_spine : ℝ := X_syrSum

/-- A closed multiplicative constant for the explicit-exponent theorem.

The second arm is exactly the `N₀ = 2` cost of weakening `c_ladder` to `cTao`.
-/
noncomputable def C_tao_assembled : ℝ :=
  max (C_spine X_spine) ((Real.log 2) ^ cTao)

theorem C_tao_assembled_pos : 0 < C_tao_assembled := by
  ...

theorem tao_collatz_quantitative_assembled :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - C_tao_assembled / (Real.log N₀) ^ cTao
        ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
  ...

end TaoCollatz
```

`C_tao_assembled` is allowed to be enormous. The deliverable is **explicit** in the precise
formal sense below; no decimal estimate or smallness claim is part of this campaign.

### Explicitness contract

The transitive cutoff/constant spine feeding `C_tao_assembled` must contain:

- only closed `def` bodies assembled from numerals, arithmetic, `max`, `Nat.ceil`, `Real.exp`,
  `Real.log`, and real powers;
- no `Classical.choose`, `Exists.choose`, `sInf`, or opaque witness selector;
- no theorem whose interface still returns an existential cutoff used by the final proof.

`noncomputable` is expected because the term uses real analysis; it is not permission to hide
an existential witness.

## Why this route is unblocked

- The multiplicative constant surface is already complete through `C_spine X`.
- Fresh kernel output for the existing tower route shows only the trust base and no
  `sorryAx`; it does not depend on either current `sorry` (believed clean, judge to verify).
- The prior X-chase already landed the ten bottom nodes in
  `Sec5/FirstPassage.lean`: `X_nZeroPos`, `X_windowBase`, `X_intTestDev`, `X_intTestErr`,
  `X_intTestLogUnif`, `X_valSumGeom`, `X_rpowNZero`, `X_valSumTail`, and their `_atX`/`_atCX`
  consumers.
- A source read found no opaque `Tendsto` leaf on the remaining path. Every current witness is
  an explicit `max`/power/exponential expression already written in a proof body. The work is
  copy-the-witness, name it, and delegate.
- The final exponent weakening is already proved existentially in
  `tao_collatz_quantitative_spine_of_le`; the fixed-constant sibling is the same `N₀ = 2`
  split with `C` held at `C_spine X_spine`.

The stopped Option-B theorem `Q_black_edge_tight` is off-path. Do not try to prove, weaken,
or consume it.

## Work order

Each item below is one commit unless the file build makes a smaller split useful. At every
node, use the same rail:

1. Copy the current existential witness expression verbatim into `X_<name>` after replacing
   upstream local witness names by their already-defined `X_*` names.
2. Add `foo_atX` or `foo_atCX` with a universal cutoff:
   `∀ x, X_foo ≤ x → ...`.
3. Reuse the current proof body after replacing its `obtain ⟨x₀, ...⟩` inputs by the explicit
   upstream siblings.
4. Re-prove the old `_atC` existential by the one-line delegate
   `⟨X_foo, foo_atCX⟩`. Its statement remains character-identical.
5. Build the edited file, run the watched-statement differ, then commit green.

### 0. Install the frontier guard

Add `tools/big_c_cutoff_audit.py` with an ordered manifest of every declaration below. It
must fail when:

- a required `X_*` or `_atCX` declaration is absent;
- a completed `_atCX` proof calls the corresponding existential `_atC` theorem;
- the final explicitness closure contains `Classical.choose`, `Exists.choose`, or `sInf`;
- `C_tao_assembled` or `tao_collatz_quantitative_assembled` is absent at completion.

In normal mode the audit validates the completed manifest prefix, prints the first missing
entry, and exits zero. It exits nonzero on a regression inside that prefix. A `--complete`
mode additionally requires every manifest entry and the final theorem; it stays red until the
last commit. Every lap takes the first missing entry printed in normal mode, so there is no
route-selection question left for the treadmill.

### 1. Finish `Sec5/FirstPassage.lean`

Add, in this order:

1. `X_rpowEps (θ ε)` from the existing witness
   `max 1 ((1 / ε) ^ (1 / (1 - θ)))`, plus `rpow_le_eps_mul_of_lt_one_atX`.
2. `X_descentPow := (2 : ℝ) ^ (30 : ℕ)`, plus `descent_pow_bounds_atX`.
3. `X_descentPasses`, exactly the current
   `max (max xa xb) (max xc 2)` with the two `X_rpowEps` instances and
   `X_descentPow`, plus `descent_passes_atX`.
4. `X_firstPassNonescape := max X_valSumTail X_descentPasses`, plus
   `first_passage_nonescape_atCX`; make `first_passage_nonescape_atC` delegate.

This is the first lap's mandatory target. It was already the next step in the lap-11 handoff
before the X-chase was deprecated for the small-pin campaign.

### 2. Close the C8 cutoff spine in `Sec5/ApproxFormula.lean`

Process these existing `_atC` declarations bottom-up, giving each an `X_*` definition and an
`_atCX` sibling. The order is binding:

1. `goodTuple_prefix_dev_sum`
2. `approx_good_tuple_whp`
3. `passtime_edge_mass`
4. `passtime_window_inner`
5. `approx_passtime_window`
6. `first_passage_window_reduce`
7. `reverse_early_return_whp`
8. `steppedMid_le_firstPassMid_add`
9. `first_passage_stepback_reduce`
10. `truncation_error_bound`
11. `first_passage_truncation_reindex`
12. `first_passage_affine_reindex`
13. `first_passage_approx`

Reuse the explicit leaves already present (`X_twoMZero`, `X_mZeroLin`, `X_cnBound`,
`X_windowBase`, and `X_valSumTail`). Do not simplify witness expressions during this pass;
copy-not-compose applies to cutoff witnesses too.

### 3. Close the C9 cutoff spine in `Sec5/Stabilization.lean`

Process these existing `_atC` declarations in order:

1. `perNTerm_harmonic_approx`
2. `good_tuple_whp_iid`
3. `syracZ_sub_perNGoodMass_bound`
4. `perNHarmonic_eq_harmZfine_approx`
5. `harmonic_to_Z`
6. `mainZ_bound`
7. `perNTerm_eval`
8. `Iy_count_ratio`
9. `approxMainTerm_to_Z`
10. `approxMainTerm_window_stable`
11. `stabilization`

Name the capstone cutoff `X_stab`. Existing closed leaves include `X_cnBound`,
`X_mZeroLin`, `X_mainZbridge`, and the explicit Sec6/Sec7 `N_*`/`T_*` chain. The current
proof bodies already display every max-tree to copy.

### 4. Close the Sec3 cutoff spine

In `Sec3/Reduction.lean`, add universal-cutoff siblings and definitions in this order:

1. `X_descStep` / `descentProb_step_atCX`
2. `X_descBase` / `descentProb_base_atCX`
3. `X_descLadder` / `descentProb_ladder_atCX`
4. `X_descWhp` / `descent_whp_atCX`
5. `X_windowBad` / `window_bad_sum_atCX`
6. `X_syrSum := max X_windowBad (Real.exp 1)` /
   `tao_syracuse_quantitative_sum_atCX`
7. `tao_collatz_quantitative_spine_atCX`, using `X_syrSum` directly instead of obtaining
   an existential `X`.

Keep `X_spine := X_syrSum` in the final additive file so the public name describes its use,
not the internal Sec3 construction.

The old `_atC` declarations continue to delegate and remain watched-statement neutral.

### 5. Expose the closed constant and theorem

Create `TaoCollatz/ExplicitBigC.lean` and add it to `TaoCollatz.lean` after the
`TaoCollatz.Statement` import.

First add a fixed-constant version of the existing exponent-weakening proof:

```lean
theorem tao_collatz_quantitative_spine_atCX_of_le
    {c₀ : ℝ} (hle : c₀ ≤ c_ladder) :
    ∀ N₀ x : ℕ, 2 ≤ N₀ → 2 ≤ x →
      1 - max (C_spine X_spine) ((Real.log 2) ^ c₀) /
          (Real.log N₀) ^ c₀
        ≤ logProb {N | colMin N ≤ N₀} (Finset.Icc 1 x) := by
  ...
```

Port the proof of `tao_collatz_quantitative_spine_of_le` verbatim, replacing its obtained
`C` and theorem with `C_spine X_spine` and
`tao_collatz_quantitative_spine_atCX`. Then define `C_tao_assembled` and close
`tao_collatz_quantitative_assembled` with `c_ladder_lower`.

Do **not** edit `CTao`, `tao_collatz_quantitative_fully_explicit`, or either comparator pin.
The new result is additive and says exactly what has been proved.

### 6. Add the numeric and structural traps

Add check 27 to `tools/check_blueprint.py` in the same commit as the new theorem.

The check must:

- mirror the full `X_*` max-tree from the Lean def bodies at a finite exact-arithmetic toy
  instance;
- assert that the correct tree selects an intentionally non-first leaf, while variants
  omitting that leaf or swapping a `max` for a `min` fail;
- mirror `C_tao_assembled = max (C_spine X_spine) ((log 2)^cTao)` structurally without
  attempting to materialize the tower;
- invoke `tools/big_c_cutoff_audit.py --complete` and require a clean explicitness closure.

Register the additive theorem as one new blueprint sub-node in this same pass. Leave it
unratified/orange; workers never set `\leanok`.

## Per-commit gates

After every Lean commit:

```text
lake env lean <edited-file>
python3 tools/tao_stmt_diff.py fabea6f HEAD
python3 tools/big_c_cutoff_audit.py
python3 tools/check_blueprint.py
git-safe status --short
```

The cutoff audit's normal mode must be green and report the next not-yet-implemented manifest
entry; `--complete` is reserved for the final gate. The edited Lean file, statement differ,
and all existing blueprint checks must always be green before commit.

At each phase boundary, run `lake build`. At completion also run the blueprint audit, the
sorry census, and fresh kernel queries for:

```text
#print axioms TaoCollatz.tao_collatz_quantitative_assembled
#print axioms TaoCollatz.tao_collatz
#print axioms TaoCollatz.tao_collatz_quantitative
#print axioms TaoCollatz.tao_collatz_quantitative_explicit
```

## Done condition

The successor campaign is done only when all of the following hold:

- `tao_collatz_quantitative_assembled` exists with no existential exponent or constant;
- `C_tao_assembled` satisfies the explicitness contract;
- its axiom print is exactly the repository trust base
  `[propext, Classical.choice, Quot.sound]` and contains no `sorryAx`;
- `lake build`, checks 1–27, `big_c_cutoff_audit.py --complete`, and the
  watched-statement differ pass;
- the two pre-existing sorries remain isolated and are not dependencies of the new theorem;
- the new blueprint node is reported orange until the judge ratifies it. Before ratification,
  report remaining work as **2 sorries + 1 orange node**; after ratification, **2 sorries +
  0 orange nodes**.

No claim that `C_tao_assembled ≤ CTao` is required or permitted in this campaign.

## Draft successor directive for the operator/judge

The operator may copy the following into `DIRECTION.md`; workers may not do so themselves:

> **CURRENT DIRECTIVE — assembled explicit big-C.** Add an axiom-clean theorem
> `tao_collatz_quantitative_assembled` at the closed constant `C_tao_assembled` specified in
> `BIG_C_EXPLICIT_BOUND_PLAN.md`. Finish the X-chase in manifest order. Use the existing
> clean tower route. Do not edit the frozen `CTao` pin, do not touch comparator statements,
> and do not work on `Q_black_edge_tight`. The next target is always the first missing entry
> printed by `tools/big_c_cutoff_audit.py`. Done means the plan's complete gate is green and
> `#print axioms tao_collatz_quantitative_assembled` shows only the trust base.
