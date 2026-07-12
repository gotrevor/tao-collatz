## Judge pass 9 (2026-07-12 ~17:15 EDT, Ren/Fable + p.51 re-derivation — handoff `7498d67`) — PAPER GAP CONFIRMED, X9 RE-RATIFIED AT exp(2ε) ⚖️🕳️

Scope: lap 52 tail (`ceb59e1`…`7498d67`): `encExpect_block_le` (path→`fpDist` block
bridge) proved, then ROUTE FINDING `0ba065f` — the box, working the R-induction closure
in full detail, claims the paper's own Lemma 7.9 proof has a gap and corrected the pin
`exp(ε)` → `exp(2ε)`. A ratified-statement edit ⇒ leanok REVOKED pending re-ratification.

**Gap claim VERIFIED by independent re-derivation** (against the p.51 text read in pass
8; confidence ~90%):
- The paper's display asserts E[(7.57) integrand | v₁…v_{k₁}] **equals**
  `exp(−Σ_{p≤k₁} 1_W + ε)·Z(endpoint, R−1)` — banking white damping through the END of
  the first block (k₁ = first passage over Δ₁'s top).
- But the true (7.57) sum stops at `t_{min(r,R)}`; on futures where the chain stops
  (r = 1) that is `t₁ < k₁` (strict: at t₁ the point is inside Δ₁, below its top). The
  discrepancy term is typically the k₁ exit-whiteness itself — the very term the
  induction then cashes via (7.59) with probability ≥ p₀ ≈ 0.99. So the display
  UNDER-states the true conditional expectation on exactly the typical stopped branch;
  an upper-bound chain built on it is unsound as written. (Also noted: the display's
  factorization drops the instant-re-encounter case t₂ = k₁ — absorbed by the corrected
  ledger's four-mass vertex analysis.)
- Toy-chain algebra CHECKED: corrected ledger's just-entered-state value
  X = e^ε·p₀/(1−(1−p₀)e^ε) ≈ exp(ε/p₀) > exp(ε) for p₀ < 1, so the paper's constant is
  likely unprovable by the natural ledger; X ≤ exp(2ε) ⟺ p₀ ≥ 1/2 (with small-ε margin,
  absorbed by ∃ε₀).

**Verdict: X9 re-RATIFIED at exp(2ε)** — the corrected statement still implies what the
paper's sole consumer needs (p.55 is Markov with R chosen after ε; absolute exponent
constants wash out — same rider as pass 8, checked at X11 time). Statement-`\leanok`
restored with the deviation documented in the node + the theorem docstring.

**NEW RIDERS**:
- **p₀ ≥ 1/2 certification burden**: the 2ε constant hard-codes p₀ ≥ 1/2, but X8's
  `fpDist_white_exit` is pinned only `∃p₀ > 0`. Either the white-exit proof certifies
  p₀ ≥ 1/2 (Monte Carlo ≈ 0.99 says the math is there; certifying it in Lean is a real
  numerics burden) or X9 re-loosens to an ∃C exponent form (equally consumable).
- **Watch for the (7.59)-shaped white-exit variant** the corrected route needs (white
  exit WITHOUT the Case-2 budget hypothesis) — a new statement pin to ratify when it
  lands; read (7.59)'s context pp.50–51 again at that point.

**Axiom checks (boundary, dated this pass)** — all TEN lap-52 encounter-fold decls
exactly `[propext, Classical.choice, Quot.sound]`: `encExpect_succ`, `encExpect_zero`,
`encVal_le`, `encExpect_le`, `encExpect_nonneg`, `encStep_count_le`,
`encExpect_of_count_ge`, `encExpect_anti`, `encExpect_block_le`,
`fpDistPlus_tsum_toReal`. Queue cleared.

**Bookkeeping**: X9 node prose updated (2ε + deviation + riders), conf 75% → 70% (the
gap adds the p₀-certification unknown); BLUEPRINT.md row updated; KB
`formalization-literature-holes.md` **entry #5** written (flavor: stronger than a
glossed step — the printed display is false as an equality in the load-bearing
direction — weaker than a theorem erratum; the theorem is unaffected). First
literature-hole found by the treadmill *in Tao*.
