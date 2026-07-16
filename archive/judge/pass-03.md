## Judge pass 3 (2026-07-12, Ren/Fable + PDF pp.14-15)

Scope: the S3 statement surface from box session 5 (laps 22-28).

1. **Lemma 2.2(i)(ii) instances — ALL RATIFIED** vs the pp.14-15 statement + p.15
   displayed Geom(2) instance. Scalar instances (`Prob/LocalBound.lean`):
   `geomHalf_*` (mean 2n), `geomQuarter_*` / `pascal_*` (mean 4n) — each pairs
   (i) point mass `≤ C/√(1+n)·G(c(L-nμ))` with (ii) the tail bound as an
   indicator-tsum (which IS `P(|S_n - nμ| ≥ λ)`). The d=2 Hold pair
   (`Sec7/Unroll.lean`): correct `(n+1)^{-d/2} = C/(1+n)` prefactor, mean `n(4,16)`
   (confirmed at Lemma 7.6, p.42-43), Euclidean norm fed to the scalar `G` — faithful
   since the paper's `G_n(x)` for `x ∈ ℝ^d` depends only on `|x|`.
2. **The `G_{1+n}`-for-`G_n` index is constants-equivalent** (`G_{1+n}/G_n ≤ e` on the
   Gaussian regime, both `≍ e^{-|x|}` beyond) and dodges the paper's `exp(-∞) = 0`
   convention at `n = 0`; the paper itself states Lemma 7.7 with `G_{1+s}`. Accepted.
3. **Domain ℕ (resp. ℕ×ℤ) for the paper's ℤ (resp. ℤ²)** — sound: the summands are
   supported there, missing lattice points carry zero mass on the LHS.
4. **D5 route machinery (proved, no statement risk)**: `iidSum` calculus,
   `negBinomial_apply` exact point mass, circle-method core (`Prob/CharFn.lean`
   finite Fourier inversion on `ZMod N × ZMod N`), `hold` nondegeneracy atoms,
   `charFn_hold_decay`. All machine-checked; they are proof plumbing for the six
   `sorry`d instance statements above.

Blueprint: S3 statement-`\leanok` (19 green / 6 orange: C8 X1 X5 X8 X9 X10). Risk
tint/lapsrisk unchanged — S3's PROOF remains risk kernel 1.

### Ops note (2026-07-12): battery + clamshell beats caffeinate
Box session 6 (`2d245fb5dac5`) sat ~40h in suspended animation because the MacBook
went to battery + lid-closed (caffeinate cannot assert through clamshell-on-battery;
nothing userland can). Unlike the 07-10 mid-stream API kill, this stall was a clean
PAUSE: the container and its 90k context survived, and the lap resumed by itself on
wake. Distinct failure modes: sleep mid-API-stream = dead turn needing relaunch;
sleep between requests = free pause. No tooling change warranted — the fix is
operational (leave the lid open / on AC for overnight runs).

