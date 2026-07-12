## Judge pass 2 (2026-07-10 afternoon, Ren/Fable + PDF pp.42-46)

Scope: the statement surface landed by box sessions 3-4 (laps 11-21).

1. **Lemma 7.7 / X6 — RATIFIED.** `fpDist_location_bound` matches the p.43 display
   verbatim: `fpDist s (j,l) ≤ C · e^{-c(l-s)}/√(1+s) · G_{1+s}(c(j - s/4))`, with
   `Gweight t x = exp(-x²/t) + exp(-|x|)` exactly the paper's `G` (restated inline in
   Lemma 7.7 itself). Lean is unconditional in `l` where the paper takes `l > s` —
   sound, since `fpDist_support_snd_gt` (proved) kills the LHS for `l ≤ s`. The
   `fpDist` budget recursion is exactly `v_{[1,k]}` at the first passage `l_{[1,k]} > s`
   ((7.44)); support facts proved. Its `∃ c > 0` form is the faithful reading of the
   paper's `≪` with absolute constants.
2. **Prop 7.8 cluster / X7 — RATIFIED** vs pp.45-46: (7.37)→`Q_polynomial_decay`
   (the `1 ≤ j` is the paper's own domain `(ℕ+1)×ℤ`), (7.38)→`Qm` (re-confirmed),
   (7.39)→`Qm_le_rpow`, (7.40)→`prop_7_8` (∃-threshold = "sufficiently large C_{A,ε}",
   ε fixed by D4), (7.41)-restricted-to-black→`Q_black_edge` (stated, the open X8/X10
   kernel; `1 ≤ n/2 - m` is the paper's `j ∈ ℕ+1`), (7.43)→`Q_white_case1` verbatim
   including the `e^{-ε³/2}` constant. The `prop_7_8` assembly (edge split white/black +
   interior via `le_Qm`) mirrors the paper's proof frame on p.45.
3. **Lemma 7.6 mean vector — arithmetic CONFIRMED** (p.42-43): `E Hold = (4,16)` via
   `E Pascal = 4`; consistent with `fpDist_location_bound`'s `j ≈ s/4` centering and
   the (7.29)/(7.30) checks already in the harness.
4. **`Qstop`/`Q_le_fpDist_expect` (Unroll.lean) — design SOUND, machine-proved**, so
   no statement-trap surface: `Qstop_eq` certifies the D6 unrolling is literally `Q`,
   and `Q_le_fpDist_expect` (the (7.46)-entry inequality) drops the accumulated
   damping factors (each ≤ 1) — valid for an upper bound; Case 2's gain must then come
   from the endpoint's whiteness ((7.50)/(7.51)), matching the paper's route.
5. **⚠️ Box label drift.** Box commits/handoffs use "X5" for the Prop 7.3 bridge seams
   (`bridge_vector`/`bridge_renewal`/`hold_tsum_step`, now proved in `Bridge.lean`) —
   those are **X4** content in the ledger/blueprint. Ledger X5 = **Lemma 7.6 basics**
   (joint exponential tail, aperiodicity, mean (4,16) as Lean decls) and is genuinely
   OPEN — nothing landed under that scope. Read box labels with suspicion; ratify by
   declaration.
6. **`renewal_white_encounters` — statement re-confirmed** after its move to
   `Bridge.lean` (only a harmless `1 ≤ n` guard added). Now proved modulo
   `Q_black_edge` only.

Blueprint statuses flipped accordingly: X6, X7 statement-`\leanok` (18 green / 7 orange:
S3 C8 X1 X5 X8 X9 X10). Proof-`\leanok` unchanged (X3 only) — everything downstream of
`Q_black_edge` inherits its `sorryAx`.

