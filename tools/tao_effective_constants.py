#!/usr/bin/env -S uv run --quiet python3
r"""Effective constants of Theorem 3.1 (`tao_collatz_quantitative`).

The quantitative headline is

    ∃ c C, ∀ N₀ x, 2 ≤ N₀ → 2 ≤ x →
        1 - C / (log N₀)^c ≤ logProb {N | colMin N ≤ N₀} [1,x]

and every existential in the proof is witnessed by an *explicit* closed-form real
term (blueprint D3: no `IsBigO`, no filters, no non-constructive choice on the
load-bearing path). So `c` and `C` are effective -- this script just evaluates the
witness tower and lets you poke at the knobs.

The tower (top -> bottom), each layer's transform to the constants:

    spine                       C := 16 * Ca                          Sec3/Reduction.lean:1335
    tao_syracuse_quantitative   Ca := max(Cw*α/(α-1), 4*max(1,(logX)^c))            :690
    window_bad_sum              Cw := 2 * C_dw                                       :571
    descent_whp                 C_dw := M * (1 + (1-α^-c)^-1) * α^c                  :410
    descentProb_ladder          M := max(C_fpne, 2*C_stab),  c := min(c_fpne,c_stab) :314

Both `c` branches bottom out at the SAME §5 kernel (a loopback), so
`c = c_fpne = c_stab = 1/(640_000_000 · ln2) ≈ 2.25e-9`, built from:
  geomHalf tail const 1/400  (Prob/LocalInstances.lean:540)
    · 0.1 scaling             (valSum_lower_geom)
    → linearDecay = min(d²/2, d)  (Syracuse/ValuationDist.lean:921)  [the d²/2 floor is the ~1e-9]
    / ln2                     (finalDecay, ValuationDist.lean:965)
    / 20                      (two_rpow_neg_nZero_le, FirstPassage.lean:1186)

`C_fpne = 44` is a clean literal; the size lives entirely in the glue constants up
top (α = 1.001) and in `C_stab`. `C_stab` reduces to literals except ONE §6 leaf,
`Cfsm = fine_scale_mixing(1.7)` (Prop 1.14, Sec6/MixingFromDecay.lean:29), which
enters only *linearly* -- passed here as a parameter (default 1).

Usage:
    tools/tao_effective_constants.py               # report at α=1.001, Cfsm=1
    tools/tao_effective_constants.py --alpha 1.1   # single point
    tools/tao_effective_constants.py --cfsm 100
    tools/tao_effective_constants.py --sweep       # α- and c-sensitivity tables

Nothing here is load-bearing for the proof; it reads the frozen witness expressions.
Change a knob, see how low C goes. See notes/effective-constants.md for the writeup.
"""
from __future__ import annotations

import argparse
import math

LN2 = math.log(2.0)

# ---------------------------------------------------------------------------
# Leaf literals (each is a `refine ⟨…⟩` witness; file:line in the comment).
# ---------------------------------------------------------------------------
CT = 1.0 / 400          # geomHalf_tail_bound        Prob/LocalInstances.lean:540
CT_CONST = 2.0          #   "" (the C side)          Prob/LocalInstances.lean:540
GEOM_SCALE = 0.1        # d := ct·0.1 in valSum_lower_geom
NZERO_DIV = 20.0        # two_rpow_neg_nZero_le       FirstPassage.lean:1186
C_DEV = 2.0             # intTest_class_dev           FirstPassage.lean:685
D0 = 1.0 / 8            # intTest_D_lower             FirstPassage.lean:763
CW_PRIME = 3.0          # windowMass_estimate         FirstPassage.lean:897
CD_MASS = 1.0 / 10000   # windowMass_ge_clog          ApproxFormula.lean:1151
CCN = 4.0               # cn_bound                    Stabilization.lean:617
C_IY = 6000.0           # Iy_count_ratio (C side)     Stabilization.lean:2541
MIX_A = 1.7             # the A in fine_scale_mixing 1.7


def linear_decay(d: float, *, quadratic: bool = True) -> float:
    """min(d²/2, d) -- the d²/2 branch is what throttles c to ~1e-9 at small d."""
    return min(d * d / 2.0, d) if quadratic else d


def final_decay(d: float, *, quadratic: bool = True) -> float:
    return min(LN2, linear_decay(d, quadratic=quadratic))


def exponent_c(*, ct: float = CT, geom_scale: float = GEOM_SCALE,
               nzero_div: float = NZERO_DIV, quadratic: bool = True) -> float:
    """The frozen exponent. c = finalDecay(ct·scale)/ln2 / 20."""
    d = ct * geom_scale
    return final_decay(d, quadratic=quadratic) / LN2 / nzero_div


# ---------------------------------------------------------------------------
# The multiplicative constant C, evaluated layer by layer.
# ---------------------------------------------------------------------------
def constant_C(alpha: float, cfsm: float, c: float, *, logX: float = 1e6):
    """Return (C, waterfall dict). Faithful to the witness tower."""
    # --- §5 first-passage base branch: C_fpne = 44 (all literals) ------------
    K = C_DEV / D0                       # intTest_error: K = c/D₀ = 16
    Cd = 2 * K + 4 * CT_CONST            # valuation_dist: 2K + 4·Ct = 40
    C7 = Cd + 2 * CT_CONST               # valSum_lower_geom C side = 44
    C_fpne = C7

    # --- C8 = first_passage_approx (all literals) ---------------------------
    edge = 2.0 / CD_MASS                 # passtime_edge_mass: 2/cD = 20000
    passtime_inner = C7 + edge           # good_tuple(44) + edge
    Cw_apw = C7 + passtime_inner         # approx_passtime_window
    C1_fpa = C7 + Cw_apw                 # first_passage_window_reduce = 20132
    stepback = C7 + 1.0                  # steppedMid…: good_tuple + reverse_early(1)
    C2_fpa = stepback + 1.0              # + truncation(1) = 46
    C8 = C1_fpa + C2_fpa                 # 20178

    # --- §5→§6 stabilization step: C_stab (α- and Cfsm-dependent) ------------
    CH = CCN                             # perNHarmonic_le = Ccn = 4
    Cw2 = 2 * CT_CONST                   # good_tuple_whp_iid = 4
    # Cε carries TWO α blowups: 3·Cw'/cD (=90000) and 2·Cw'/(α-1)
    C_eps = 2.0 + 3 * (CW_PRIME / CD_MASS) + 2 * CW_PRIME / (alpha - 1.0)
    CA = C_eps * CH
    mix_pow = 200000.0 ** MIX_A          # (1/200000)^(-1.7) ≈ 1.03e9
    CB = CCN * Cw2 + CCN * cfsm * mix_pow
    C2_toZ = CA + CB
    Cz = CA + CB + 1000.0 * (1.0 + C8)
    C_toZ = (2.0 / math.log(4.0 / 3.0) + C_IY) * C2_toZ + Cz * C_IY
    C_stab = C7 + 4 * C8 + 4 * C_toZ     # 2·Cs = 4·C_toZ

    # --- ladder → whp → window → syracuse → spine ---------------------------
    M = max(C_fpne, 2 * C_stab)
    # reciprocal factor, via expm1 to dodge catastrophic cancellation:
    #   1 - α^(-c) = -expm1(-c·ln α)
    recip = 1.0 / (-math.expm1(-c * math.log(alpha)))
    whp_factor = (1.0 + recip) * (alpha ** c)
    C_dw = M * whp_factor
    Cw_wbs = 2 * C_dw
    term1 = Cw_wbs * alpha / (alpha - 1.0)
    term2 = 4.0 * max(1.0, logX ** c)
    Ca = max(term1, term2)
    C = 16 * Ca

    wf = {
        "C_fpne (base kernel)": C_fpne,
        "C8 (first_passage_approx)": C8,
        "C_stab": C_stab,
        "M = max(44, 2·C_stab)": M,
        "α/(α-1)": alpha / (alpha - 1.0),
        "(1-α^-c)^-1 [reciprocal]": recip,
        "whp_factor": whp_factor,
        "Ca (syracuse)": Ca,
        "term2 (dominated)": term2,
        "C (headline)": C,
    }
    return C, wf


def report(alpha: float, cfsm: float) -> None:
    c = exponent_c()
    C, wf = constant_C(alpha, cfsm, c)
    print(f"  α = {alpha:<12g}  Cfsm = {cfsm:g}")
    print(f"  c = 1/(640_000_000·ln2) = {c:.4e}")
    print(f"  C ≈ {C:.3e}")
    print("  waterfall:")
    for k, v in wf.items():
        print(f"    {k:<32} {v:.4e}")


def sweep(cfsm: float) -> None:
    c0 = exponent_c()
    print("\nα-sensitivity (Cfsm = %g, c frozen at %.3e):" % (cfsm, c0))
    print(f"    {'α':>8}  {'α/(α-1)':>12}  {'(1-α^-c)^-1':>14}  {'C':>12}")
    for alpha in (1.001, 1.01, 1.1, 1.5, 2.0, 4.0):
        C, wf = constant_C(alpha, cfsm, c0)
        print(f"    {alpha:>8g}  {wf['α/(α-1)']:>12.3e}  "
              f"{wf['(1-α^-c)^-1 [reciprocal]']:>14.3e}  {C:>12.3e}")

    print("\nc-sensitivity (α = 1.001, Cfsm = %g):" % cfsm)
    print("  (c is throttled to ~1e-9 by the d²/2 floor; a better local-limit")
    print("   estimate that reached the linear branch would lift it ~1000×.)")
    print(f"    {'c':>12}  {'(1-α^-c)^-1':>14}  {'C':>12}   note")
    variants = [
        (exponent_c(), "frozen (d²/2 floor, ÷20)"),
        (exponent_c(nzero_div=1.0), "drop the ÷20"),
        (exponent_c(quadratic=False), "linear branch instead of d²/2"),
        (exponent_c(quadratic=False, nzero_div=1.0), "linear + no ÷20"),
        (0.5, "hypothetical c = 1/2"),
    ]
    for cval, note in variants:
        C, _ = constant_C(1.001, cfsm, cval)
        recip = 1.0 / (-math.expm1(-cval * math.log(1.001)))
        print(f"    {cval:>12.3e}  {recip:>14.3e}  {C:>12.3e}   {note}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--alpha", type=float, default=1.001,
                    help="window exponent (Lean: FirstPassage.lean:116, frozen 1.001)")
    ap.add_argument("--cfsm", type=float, default=1.0,
                    help="fine_scale_mixing(1.7) constant (unextracted §6 leaf)")
    ap.add_argument("--sweep", action="store_true", help="print sensitivity tables")
    args = ap.parse_args()

    print("Effective constants of tao_collatz_quantitative (Theorem 3.1)\n")
    report(args.alpha, args.cfsm)
    if args.sweep:
        sweep(args.cfsm)
    print("\n(These read the frozen witness tower; edit the Lean knobs noted above")
    print(" to actually drive them down. See notes/effective-constants.md.)")


if __name__ == "__main__":
    main()
