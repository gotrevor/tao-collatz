# Judge pass 21 (2026-07-13, Ren/Fable — external contribution cross-check, working tree) — C2 / LEMMA 2.1 COMPLETE ✅

Scope: an **uncommitted working-tree change** to `TaoCollatz/Basic/Valuation.lean`
(+155/−2) produced by an external **OpenAI Codex** session, claiming C2 finished.
Not a treadmill lap; no lap number. Treated as untrusted foreign-agent code:
full read of every added line, statement diff, ratification, dated runs.

## Claim verified ✅

- **Statement untouched**: the pinned `valVec_unique` iff is diff-context only;
  the 2 removed lines are the `sorry` and its "stated with sorry" docstring
  caveat. `lean-sorry`: Valuation.lean now 0 sorries.
- **Statement RATIFIED vs paper Lemma 2.1 (p.14)** — this resolves the node's
  open RATIFY-2 (`% TODO-PRECISE` in the C2 node, now removed). The paper: "Let
  N ∈ 2ℕ+1, n ∈ ℕ. Then ~a⁽ⁿ⁾(N) is the unique tuple ~a in (ℕ+1)ⁿ for which
  Aff_~a(N) ∈ 2ℕ+1." Our pin: for odd N and `a` with all entries ≥ 1,
  `2^pre a n ∣ 3^n N + fnat n a ∧ Aff N n a % 2 = 1 ↔ a = valVec N n` — the
  divisibility ∧ odd-quotient conjunction is exactly "the D2-integerified Aff is
  an odd natural" (ℕ-division exact + odd). ⚠️ One noted gap, NOT a blocker:
  the paper's membership half (valVec's own entries ≥ 1, i.e. ~a⁽ⁿ⁾ ∈ (ℕ+1)ⁿ)
  has no companion lemma. Consumer-safe: the iff is applied at candidate tuples
  that carry the hypothesis by construction (p.14's consumption at line "the
  event ~a⁽ⁿ⁾(N) = ~a occurs precisely when Aff_~a(N) is an odd integer"). A
  one-liner via `syr_iterate_odd` (3·odd+1 is even so ν₂ ≥ 1) if any consumer
  ever needs it — armed as a nit.
- **Proof route = the paper's own** (p.14 induction peeling the last entry):
  truncation recursions `pre_initVec`/`pre_succ_initVec`/`fnat_succ_initVec`,
  coprime-2-3 cancellation to get `2^S ∣ E`, quotient identified with
  `syr^[n] N` via `syr_iterate_key`, last entry extracted by
  `padicValNat_two_eq_of_mul_odd`. Key steps hand-traced (hfactor′ ledger,
  oddness of M, the padicValNat extraction) — sound. Backward direction from
  `syr_iterate_key` + new `syr_iterate_odd` (Syracuse iterates of odd stay odd),
  which is the paper's "clear from (1.7)".

## Dated runs (2026-07-13, host, `lake env lean`) — exactly the clean triple ✅

`syr_iterate_key`, `valVec_unique`, `syr_iterate_odd` — all
`[propext, Classical.choice, Quot.sound]`. Full `lake build TaoCollatz` green
(3,281 jobs); Valuation.lean standalone elaboration emits zero warnings.

## Hygiene (/lean-review over the 148 added lines)

✅ CLEAN. No `maxHeartbeats`, no `native_decide` (one kernel `decide` on
`Nat.Coprime 2 3` — fine), no `axiom`/`unsafe`/`partial`/`implemented_by`, no
silenced linters, no Prop-def laundering, no bare `#print axioms`. Helpers are
`private` (good namespace hygiene).

## State after this pass

- **C2 is the EIGHTH verified-complete node** (first in the C-series
  support layer). Blueprint: proof-leanok + proof block, badge dropped
  (`valVec_unique`, `syr_iterate_odd` added to `\lean{}`); RATIFY-2 TODO
  removed.
- Downstream: C4 (`uses C2, S1`), C5 (`uses C2, S2`), C8 (`uses C2, C5, C7`)
  now have their C2 input fully discharged.
- Committed by the judge (the external session left the tree dirty; boxes/
  agents can't push). Credit: proof authored by OpenAI Codex, judge-verified.
