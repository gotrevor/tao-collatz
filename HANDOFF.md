# HANDOFF — big-C campaign, lap 1 (2026-07-17)

**Read `DIRECTION.md` first — it outranks this file. Then the lap-1 entry in
`PENDING_WORK.md`, which is this lap's whole content.**

## State

- **DIRECTION step 1 is DONE and the verdict is NO-GO: the campaign is halted on a
  JUDGE-FLAG.** The traced C-ladder is `≈ 10^(9.39×10¹⁰)`, exceeding the pin
  `CTao = 10^(10⁹)` by ~94× in the exponent. The trace (file:line per hop) is in
  `PENDING_WORK.md`; the machine-checked mirror is `check17` in
  `tools/check_blueprint.py` (all checks green).
- The overflow is **structural, not witness slop**: any constant satisfying the frozen
  `renewal_white_encounters` statement at `A = mainDecayExponent 3.7 ≈ 3.11×10⁷` is
  forced `≥ 10^(9.36×10¹⁰)` (floor argument in the ledger). The dominant term is
  `M1 ≈ K·3B/δ` in `hold_weight_expect`'s witness, `δ = exp(epsBW³/2)−1 ≈ 0.5×10⁻³⁰⁰⁰`
  — the `1/δ` factor the pin's `10^(2–3×10⁸)` sizing missed.
- Steps 2/3 NOT started, per DIRECTION's never-inflate/STOP rule. Statements untouched;
  differ green vs setup commit (35/35 character-identical); blueprint audit green;
  `lean-sorry -c TaoCollatz` still 1 (the pin, by design).

## Self-stop gate note (for the host/operator)

`box done` was signalled lap 1 and DECLINED by the repo-wide gate: "10 open sorries".
All 10 are governance-gated — 1 is the `Statement.lean` CTao pin (undischargeable over
the frozen tower, per the JUDGE-FLAG), 9 are the `Comparator/TaoCollatz/Challenge.lean`
stubs, which are judge-owned (DIRECTION: "Comparator/ … Do not touch them"; comparator
CI red-until-done is the design). No lap can lower this count without violating
DIRECTION. The run needs an operator stop or a `--done-when` scoped away from
`Comparator/`; relaunched laps will find no in-scope proof work until the flag clears.

## For the next lap

- **Blocked on the operator/judge answering the JUDGE-FLAG** (re-pin at `10^(10^11)`+ /
  shrink `epsBW` / def surgery — options and sizing formula in the ledger entry).
- Until then there is no in-scope proof work: step 2's sibling/delegate program would
  transcribe toward a pin that cannot be met. Do NOT start it; do NOT touch the pin.
- If idle work is wanted that survives any judge decision: the step-2 pattern applied to
  the Sec7 leaves BELOW `hold_weight_expect` (naming `K`, `M1`, `T`, `Cthr` as
  `noncomputable def`s with `_pos` lemmas) is transcription that stays valid under every
  flag resolution except a full statement redesign — but it is speculative; prefer
  waiting for the flag to clear.
