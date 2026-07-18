# HANDOFF — Tier-1 tower tightening, laps 1–10 done (2026-07-18) 🗼

**Read `DIRECTION.md` first (unchanged, still governs); `TIER1-TOWER-TIGHTENING-PLAN.md`
is the spec; `PENDING_WORK.md` has the per-lap ledger (laps 1–10, incl. all gotchas).**

Branch `tier1-tower-tightening`, HEAD `68712f0`, build GREEN, differ **39/39** vs plant
`b7825fc` at every commit, `TaoCollatz/` census = **1** (the planted pin, untouched).
No uncommitted edits.

## Done (laps 1–10)

1. Laps 1–6 (see prior ledger): calculus bank, POC gate (`C_fpLocation ≤ tT2`),
   first-passage cluster at `10^74…10^89`, cubic node `+6 → +2` + exact rpow form,
   fewWhite core exact (`K ≤ 10^3011`, `R ≤ 10^3045`, `P+1 ≤ 10^(10^(10^3047))`,
   `B ≤ 10^(10^(10^3049))`).
2. **Lap 7**: `T_colTail ≤ 10^(10^(10^3048))`, `Cthr_fewWhite ≤ 10^(10^(10^3050))`
   (⌈B^2.5⌉ arm); level-1 `T_expRpow ≤ 10^120`, `T_outStrip ≤ 10^126`; bank
   `ten3_mono`, `ten_pow_le_ten3`.
3. **Lap 8**: `C_hold ≤ 10^6020` level-1 (`deltaBW⁻¹ ≤ 10^3001`; K_hold's log via
   `log_mul`+`log_rpow`, NOT `log_le_self`).
4. **Lap 9**: level-1 kit (`T_logLin/T_expNeg/T_logSq-small/geomDenInv`);
   `delta_case2⁻¹ ≤ 10^3001`; `T_fstTail ≤ 10^6191`, `T_holdTail ≤ 10^6006`;
   **`T_fstMgf ≤ 10^(10^3020)` — the case-2 chain's only level-2 arm** (`T_logSq B`,
   `B ≈ 10^3014`, is `exp(√B)`); `T_edgeWeight`/`Cthr_case2 ≤ 10^(10^3021)`.
5. **Lap 10**: `Cthr_dampingCol/blackEdge/prop78 ≤ 10^(10^(10^3050))`,
   `C_polyDecay ≤ L3(3051)` (`^A` = +8 top digits),
   **`C_renewalWhite ≤ 10^(10^(10^3052))` — the whole §7 chain at honest height.**

All new lemmas are `private … _le_ten_pow / _le_ten_rpow / _le_ten3` beside their old
`_le_tenTower_N` cousins in `TaoCollatz/BigCTower.lean`; nothing downstream edited,
nothing watched touched. Honest ceiling remains **tenTower 4** (established lap 5;
tT3 is false since log₁₀³C ≈ 3052 > 10).

## Next (in order; plan §3)

1. **Sec6/Sec3 spine at honest heights**: `C_mainZ … C_windowBad`, `X_*`, `X_spine`
   (current climbs live at BigCTower.lean §"§6 propagation" onward, tT43→62). Per
   lap-5 sizing the X_* are small; only the C-chain rides `C_renewalWhite`'s L3(3052).
   Reuse the level-1 kit + `ten3_mono`/`ten_pow_le_ten3`/`ten_pow_le_ten_rpow_level2`
   lifts; expect final `C_tao_assembled ≤ 10^(10^(10^~3055))`.
2. **Ceiling**: new theorem `C_tao_assembled ≤ tenTower 4` (lift via
   `ten_rpow_rpow_ten_pow_le_tenTower_four`, σ ≤ 10^10 ✓) alongside the frozen
   `…_le_tenTower_sixty_two`; bridge `tenTower 4 ≤ tenTower 9 = CTao` via
   `tenTower_nine_eq_hyperoperation`.
3. **`check28`** in `tools/check_blueprint.py`: log/log-log mirror of the full
   max-tree, prints + asserts the height, mutation-trapped; resolve max arms in
   log-space (extend check19).
4. **Discharge the pin LAST**: remove `Statement.lean`'s `sorry` + its
   `warningAsError` shield in one commit → host `--done-when sorry-free:TaoCollatz`
   ends the run. Record base-free `log log log C ≲ 3052` + epsBW⁻³ provenance in the
   ceiling docstrings (DIRECTION plan §6).

## Hard-won gotchas (details in PENDING_WORK.md laps 7–10)

- **linarith/ring/norm_num on `(10:ℝ)^(3016:ℕ)`-sized npow atoms** hits the
  `exponentiation.threshold 256` wall or silently fails (`ring` evaluates numerals!).
  Use pure lemma chains (`add_le_ten_pow (le_refl _) …`), `simp only [add_assoc]`
  for reassociation, or `generalize hX : … = X` + `linarith only [h…]`.
- A `(X.trans (ten_pow_mono _)).trans (lift _)` chain leaves the intermediate
  exponent as an unresolvable metavariable — name the intermediate `have` with an
  explicit `10^k` type.
- `ten_pow_le_ten_rpow_level2` requires `σ ≥ 30` (with `σ ≥ 2` it is FALSE — the
  10^30 cast must fit under `10^σ`).
- For `log` of a level-2 quantity (`2^A`, `e^{A/2}`), never `log_le_self` (returns
  level-2); route through `Real.log_mul` + `Real.log_rpow` to stay level-1.
