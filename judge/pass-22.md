# Judge pass 22 (2026-07-13, Ren/Fable — external contribution cross-check, working tree) — C5 / PROP 1.9 + LEMMA 4.1 COMPLETE ✅

Scope: uncommitted working-tree changes by an external **OpenAI Codex** session —
`TaoCollatz/Syracuse/ValuationDist.lean` (+1,152/−24) and
`TaoCollatz/Basic/Valuation.lean` (+31, the parity helper `fnat_mod_two_of_pos`).
Claim: "C5 finished — valuation_dist and valuation_tail complete."
Same protocol as pass 21: untrusted foreign code, statement diff, fresh
faithfulness read, hygiene scan, dated runs. Judge committed after verification.

## The catch: a transitively-laundered hole, found by the dated run 🎯

`lean-sorry` said both files were sorry-free and the build was green — but the
first dated axiom run returned **`valuation_tail` depends on `sorryAx`**. The
proof consumes `PMF.abs_expect_indicator_sub_le_dTV` (paper (1.10),
`Prob/Basic.lean:154`), a hole parked since the early campaign, OUTSIDE the
changed files. Textual censuses are per-file; only `#print axioms` sees the
transitive trail. **The judge discharged (1.10) same pass** (host work, no box
in flight): `|Σ(p−q)·1_E| ≤ Σ|p−q|·1_E ≤ Σ|p−q|` — tsum triangle inequality
via `norm_tsum_le_tsum_norm` + `Summable.tsum_le_tsum`, summability from
`ENNReal.summable_toReal` on `PMF.tsum_coe`. Prob/Basic elaborates clean;
one fewer parked hole repo-wide (21 → 17 sorries with codex's two and C2's).

## Statements: character-untouched + freshly re-read vs the paper ✅

No signature lines in the removed diff; constituent `unifOddMod`'s body
unchanged (docstring reworded only); `geomHalf`/`PMF.iid`/`PMF.dTV`/
`PMF.expect`/`pre`/`valVec` all in untouched files or pure-addition diffs. The
early-campaign ratification therefore carries over; a dormant pin consumed by a
1,000-line foreign proof earned a fresh read anyway:

- **`valuation_dist` vs Prop 1.9 (p.7)**: `∀ c₀ K > 0, ∃ c₁ C > 0, ∀ n n' X`,
  hypotheses `(2+c₀)n ≤ n'`, odd support, `dTV(X mod 2^n', unifOddMod n') ≤
  K·2^{−n'}`; conclusion `dTV(valVec X n, Geom(2)^⊗n) ≤ C·2^{−c₁n}`. Matches
  the paper's quantifier logic exactly — c₁ and the implied constants "permitted
  to depend on c₀", and the hypothesis's ≪-constant K quantified with C
  allowed to depend on it. Uniform in n, n', X as consumers require (p.24's
  application). RATIFICATION CONFIRMED.
- **`valuation_tail` vs Lemma 4.1 (p.22)**: `ℙ(|a⁽ⁿ⁾(N)| ≥ n') ≤ C·2^{−cn}`
  as expectation-of-indicator under the same hypothesis block. CONFIRMED.

## Route (read + spot-traced) — paper §4 with one sound reordering

Residue classification: `factor_odd_iff_mod` + `valVec_eq_iff_mod` turn
"valVec = a" into a single residue of N mod `2^{|a|+1}` — the p.24 consumption
of Lemma 2.1, built directly on pass-21's `valVec_unique` (C2 → C5 chain).
Truncated comparison: fiber counting (`card_zmod_two_pow_cast_fiber`), exact
match of the uniform pushforward with `Geom(2)^⊗n` point masses below level n'
(`unifOddMod_map_valVec_apply`, `truncated_uniform_eq_geom`); data processing
`PMF.dTV_map_le` carries the mod-2^{n'} hypothesis through truncation
(`truncateVal`/`truncateVec`, `PMF.dTV_le_of_truncateVec`). Overflow: geometric-
side tail via the S2 engine (`geomHalf_overflow_le_Gweight` + decay lemmas).
**Route note**: Lemma 4.1 is *derived from* Prop 1.9 + the geometric tail —
reverse of the paper's proof order, sound and non-circular (the overflow control
in Prop 1.9's proof lives on the pure `Geom(2)^⊗n` side, not on the valVec
pushforward; 4.1 then follows from `ℙ_P(E) ≤ ℙ_Q(E) + dTV(P,Q)` = (1.10)).

## Dated runs (2026-07-13, host, post-(1.10)-discharge) — all exactly the clean triple ✅

`valuation_dist`, `valuation_tail`, `valVec_pos`, `fnat_mod_two_of_pos`,
`unifOddMod_map_valVec_apply`, `truncated_val_dTV_le`, `PMF.dTV_map_le` — all
`[propext, Classical.choice, Quot.sound]`. Full `lake build` green (3,281 jobs);
both changed modules elaborate silently.

## Hygiene (/lean-review, 1,183 added lines)

✅ CLEAN. No `maxHeartbeats`, no `native_decide`, no `axiom`/`unsafe`/`partial`/
`opaque`, no silenced linters, no Prop-def laundering, no bare `#print axioms`.
Bonus: codex added `valVec_pos` — resolving pass-21's armed membership nit
unprompted.

## State after this pass

- **C5 is the NINTH verified-complete node.** Blueprint: proof-leanok + proof
  block, badge dropped; `valuation_tail`, `unifOddMod`, `valVec_pos` added to
  `\lean{}`.
- Downstream unlocked: C5 feeds C8 (§5, the β-series spine) — together with C2
  both of C8's C-side inputs are now verified; C8 remains the last un-pinned
  node.
- §-wide sorry count 21 → 17 (8 files). Judge role note: the (1.10) discharge
  is judge-authored host work (treadmill stopped, no in-flight box) — recorded
  here for provenance; dated runs re-run after it.
