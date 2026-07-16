#!/usr/bin/env -S uv run --quiet python3
r"""Effective constants of Theorem 3.1 (`tao_collatz_quantitative`).

The quantitative headline is

    ∃ c C, ∀ N₀ x, 2 ≤ N₀ → 2 ≤ x →
        1 - C / (log N₀)^c ≤ logProb {N | colMin N ≤ N₀} [1,x]

WHAT THIS IS. Every constant-carrying lemma on the path is stated `∃ c C x₀ : ℝ`, and
`Exists` is a `Prop` -- the witness cannot be projected back out of the compiled proof.
So this script is NOT an extraction. It is a hand transcription of the `refine ⟨…⟩`
witness expressions, re-implemented in Python. It can silently drift from the Lean;
nothing in CI ties the two together. Evidence tier: "traced by hand", well below
anything the kernel certifies. See notes/effective-constants.md.

WHAT IS KNOWN.
  c <= 1/(640_000_000 · ln 2) ≈ 2.25e-9.  <= and not =: c = min(c7, c8, cs') and only the
    c7 branch is traced, so this bounds c above. Equality needs c8 >= c7 and cs' >= c7,
    which nobody has shown. exponent_c() below computes the c7 branch.
  C is NOT currently effective: `hold_weight_expect` (Sec7/Monotone.lean:163) pulls its
    threshold `T` out of a rate-free `Filter.eventually_atTop`, and that constant flows
    all the way to the spine via fine_scale_mixing. Until Monotone.lean:142,163 are given
    explicit witnesses, no UPPER bound on Cfsm is readable from the proof.

    Be precise about what that means. The mathematics is effective -- t^k·(3/4)^t → 0 has
    an elementary explicit rate, and nothing in Tao's argument is non-constructive. It is
    this PROOF TEXT that throws the rate away. There is no barrier in principle, only a
    lemma someone has to write. "C is not effective" is a claim about the current Lean.

  And only the UPPER direction is blocked. A FLOOR needs no unblocking at all -- see
  cfsm_floor_log10 below, which rides on hold_weight_expect's stated `1 <= Cthr`:
    Cfsm ≳ 10^(6.86e7), so C ≳ 10^(7e7).
  NOT the ~1e30 an earlier version of this script reported by setting Cfsm := 1. That
  default was a placeholder, never derived; it understated C by ~70 million orders of
  magnitude. For Cfsm to be ≈ 1 you would need C_head ≈ 10^-(5e7), when it is provably
  ≥ 4^𝔡 = 10^(1.87e7).

The tower (top -> bottom), each layer's transform (declaration lines):

    spine                       C := 16 * Ca                          Sec3/Reduction.lean:1331
    tao_syracuse_quantitative   Ca := max(Cw*α/(α-1), 4*max(1,(logX)^c))            :669
    window_bad_sum              Cw := 2 * C_dw                                       :558
    descent_whp                 C_dw := M * (1 + (1-α^-c)^-1) * α^c                  :392
    descentProb_ladder          M := max(Cb, Cs),  c := min(cb, cs)                  :303

`c` is built from (verified):
  geomHalf tail const 1/400  (Prob/LocalInstances.lean:540, witness :544)
    · 0.1 scaling             (valSum_lower_geom, FirstPassage.lean:1211)
    → linearDecay = min(d²/2, d)  (Syracuse/ValuationDist.lean:921)  [d²/2 floor = the ~1e-9]
    / ln2                     (finalDecay, ValuationDist.lean:965; division at :1213)
    / 20                      (two_rpow_neg_nZero_le, FirstPassage.lean:1182)

α IS NOT A KNOB. Its exact value is welded into load-bearing lemmas that become FALSE if it
moves (`alpha ^ 3 ≤ 1.01` at FirstPassage.lean:1365; `alpha - 1 = 0.001` at
Stabilization.lean:2605; and three more). The proof exploits α ≈ 1 -- the window [x, x^α]
must be narrow, which is why Tao fixes α = 1.001 at (1.18). An earlier version of this
script swept α to 4.0 and reported C dropping to 5.4e24; that was arithmetic on the shape
of the bound, not a property of the formalization. The --alpha flag is kept only so you can
see which factors α feeds, and it is NOT a claim that any other value verifies.

Usage:
    tools/tao_effective_constants.py                    # c exactly; C's floor; the waterfall
    tools/tao_effective_constants.py --glue             # c-sensitivity of the glue factors
    tools/tao_effective_constants.py --cfsm-log10 0     # pretend Cfsm = 1 (the old default)
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
GEOM_SCALE = 0.1        # d := ct·0.1 in valSum_lower_geom     FirstPassage.lean:1211
NZERO_DIV = 20.0        # two_rpow_neg_nZero_le       FirstPassage.lean:1182
C_DEV = 2.0             # intTest_class_dev           FirstPassage.lean:689  (witness ⟨2, …⟩)
D0 = 1.0 / 8            # intTest_D_lower             FirstPassage.lean:765  (witness ⟨1/8, …⟩)
CW_PRIME = 3.0          # windowMass_estimate         FirstPassage.lean:897
CD_MASS = 1.0 / 10000   # windowMass_ge_clog          ApproxFormula.lean:1151
CCN = 4.0               # cn_bound                    Stabilization.lean:617
C_IY = 6000.0           # Iy_count_ratio (C side)     Stabilization.lean:2541
MIX_A = 1.7             # the A in fine_scale_mixing 1.7       Stabilization.lean:2088
ALPHA = 1.001           # alpha                       FirstPassage.lean:116


def linear_decay(d: float, *, quadratic: bool = True) -> float:
    """min(d²/2, d) -- the d²/2 branch is what throttles c to ~1e-9 at small d."""
    return min(d * d / 2.0, d) if quadratic else d


def final_decay(d: float, *, quadratic: bool = True) -> float:
    return min(LN2, linear_decay(d, quadratic=quadratic))


def exponent_c(*, ct: float = CT, geom_scale: float = GEOM_SCALE,
               nzero_div: float = NZERO_DIV, quadratic: bool = True) -> float:
    """The c7 branch: finalDecay(ct·scale)/ln2 / 20 = 1/(640_000_000·ln2).

    This bounds the headline c ABOVE (c = min(c7, c8, cs'), and only c7 is traced).

    `valSum_lower_geom` (FirstPassage.lean:1215) sets c := min cd cg with
    cd = 1/(320_000·ln2) and cg = 1/(32_000_000·ln2); cg is ~100× smaller, so the min is cg.
    """
    d = ct * geom_scale
    return final_decay(d, quadratic=quadratic) / LN2 / nzero_div


# ---------------------------------------------------------------------------
# Cfsm -- the blocked §6 constant. Only a floor is readable.
# ---------------------------------------------------------------------------
def cfsm_floor_log10() -> float:
    """log10 of a FLOOR on Cfsm = fine_scale_mixing(1.7), from the §6 definitions.

    A floor, not a value -- and note it needs NO unblocking. A lower bound only needs
    C₁ >= 1, which hold_weight_expect states outright; only an UPPER bound waits on `T`.
    It still ignores the (2·C₁+2)^𝔡 term at its true C₁ (~10^3000, driven by
    epsBW = 1/10^1000), which the blocker hides. The real Cfsm is larger.

        caConst A           = 1000 * (max A 0 + 3)              Sec6/MixingCore.lean:2327
        mainDecayExponent A = A + (caConst A)^2 * ln 2 + 3      Sec6/MixingMain.lean:142
        osc_mainHigh_bound  = ⟨3 * C * 40^B, …⟩, B := mainDecayExponent A     :469
        telescope calls the high regime at A + 2               Sec6/MixingRegime.lean:48
        fine_scale_mixing consumed at A = 1.7                  Sec5/Stabilization.lean:2088
    """
    B = MIX_A + 2.0
    ca = 1000.0 * (max(B, 0.0) + 3.0)
    d = B + ca ** 2 * LN2 + 3.0
    # C_head >= 4^d: hold_weight_expect states 1 <= Cthr, so n0 = 2*C1+2 >= 4, and
    # renewal_white_encounters' witness is max((n0)^A, ...) >= 4^A -- then four pure
    # passthrough layers carry it to osc_mainHigh_bound unchanged. None of this needs
    # the blocked `T`: a LOWER bound only needs C1 >= 1, which the statement gives.
    #   Cfsm >= 2*Cm*zeta(2), Cm = 3*C_head*40^d  =>  6*(pi^2/6)*160^d
    return math.log10(6.0 * (math.pi ** 2 / 6.0)) + d * math.log10(4.0 * 40.0)


# ---------------------------------------------------------------------------
# The multiplicative constant C. Linear in Cfsm, so we return C(0) and dC/dCfsm.
# ---------------------------------------------------------------------------
def constant_C_parts(alpha: float, c: float, *, logX: float = 1e6):
    """Return (C_at_cfsm_0, slope, waterfall). C(Cfsm) = C_at_cfsm_0 + slope·Cfsm.

    Faithful to the witness tower. Evaluated at Cfsm = 0 and 1 and differenced, because
    the true Cfsm overflows a float by ~70 million orders of magnitude.
    """
    def _C(cfsm: float):
        # --- §5 first-passage base branch: C_fpne = 44 (all literals) --------
        K = C_DEV / D0                       # intTest_error: K = c/D₀ = 16
        Cd = 2 * K + 4 * CT_CONST            # valuation_dist: 2K + 4·Ct = 40
        C7 = Cd + 2 * CT_CONST               # valSum_lower_geom C side = 44
        C_fpne = C7

        # --- C8 = first_passage_approx (all literals) ------------------------
        edge = 2.0 / CD_MASS                 # passtime_edge_mass: 2/cD = 20000
        passtime_inner = C7 + edge           # good_tuple(44) + edge
        Cw_apw = C7 + passtime_inner         # approx_passtime_window
        C1_fpa = C7 + Cw_apw                 # first_passage_window_reduce = 20132
        stepback = C7 + 1.0                  # steppedMid…: good_tuple + reverse_early(1)
        C2_fpa = stepback + 1.0              # + truncation(1) = 46
        C8 = C1_fpa + C2_fpa                 # 20178

        # --- §5→§6 stabilization step: C_stab (α- and Cfsm-dependent) --------
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

        # --- ladder → whp → window → syracuse → spine ------------------------
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
        return C, {
            "C_fpne (base kernel)": C_fpne,
            "C8 (first_passage_approx)": C8,
            "α/(α-1)": alpha / (alpha - 1.0),
            "(1-α^-c)^-1 [reciprocal]": recip,
            "whp_factor": whp_factor,
            "term2 (dominated)": term2,
        }

    C0, wf = _C(0.0)
    C1, _ = _C(1.0)
    return C0, C1 - C0, wf


def report(alpha: float, cfsm_log10: float) -> None:
    c = exponent_c()
    C0, slope, wf = constant_C_parts(alpha, c)

    print(f"  α = {alpha:<10g}  (FirstPassage.lean:116 -- structural, not a knob)")
    print(f"  c ≤ 1/(640_000_000·ln2) = {c:.4e}      [c7 branch; c is a min -- see docstring]")
    print()
    print("  C = C₀ + slope·Cfsm, with")
    print(f"    C₀    = {C0:.3e}   (the Cfsm-free part)")
    print(f"    slope = {slope:.3e}   (Cfsm enters linearly)")
    print()

    floor = cfsm_floor_log10()
    log10_C = math.log10(slope) + cfsm_log10
    if cfsm_log10 >= floor - 1e-9:
        print(f"  Cfsm ≳ 10^{floor:.3e}   (needs no unblocking; rides on `1 <= Cthr`)")
        print(f"  ==> C ≳ 10^{log10_C:.3e}")
    else:
        print(f"  Cfsm = 10^{cfsm_log10:g}  <-- BELOW the readable floor 10^{floor:.3e}.")
        print(f"      This is a hypothetical, not a bound. C would be ~10^{log10_C:.3e}.")
    print()
    print("  glue waterfall (the factors Cfsm gets multiplied by):")
    for k, v in wf.items():
        print(f"    {k:<32} {v:.4e}")

    # Non-vacuity: C/(log N₀)^c < 1 needs c·ln(ln N₀) > ln C.
    need = log10_C * math.log(10) / c
    print()
    print(f"  non-vacuity: needs ln(ln N₀) > {need:.3e}, i.e. N₀ > exp(exp({need:.2e})).")
    print("    The bound says nothing about any N₀ anyone will ever write down.")


def glue_sensitivity(alpha: float) -> None:
    """What a sharper local-limit estimate would buy -- in the glue only."""
    print("\nc-sensitivity of the glue (C₀ and slope; Cfsm is independent of c):")
    print("  The d²/2 branch of linearDecay at d = 1/4000 is what turns 1/4000 into")
    print("  1/32_000_000; plus a bare ÷20. Neither is a deep barrier. But note the")
    print("  payoff is ~1000× against a 10^(5e7) tower -- i.e. nothing. Fixing c is")
    print("  worth doing for honesty, not for size.")
    print(f"\n    {'c':>12}  {'(1-α^-c)^-1':>14}  {'slope':>12}   note")
    variants = [
        (exponent_c(), "frozen (d²/2 floor, ÷20)"),
        (exponent_c(nzero_div=1.0), "drop the ÷20"),
        (exponent_c(quadratic=False), "linear branch instead of d²/2"),
        (exponent_c(quadratic=False, nzero_div=1.0), "linear + no ÷20"),
        (0.5, "hypothetical c = 1/2"),
    ]
    for cval, note in variants:
        _, slope, _ = constant_C_parts(alpha, cval)
        recip = 1.0 / (-math.expm1(-cval * math.log(alpha)))
        print(f"    {cval:>12.3e}  {recip:>14.3e}  {slope:>12.3e}   {note}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--alpha", type=float, default=ALPHA,
                    help="window exponent (FirstPassage.lean:116). NOT a free knob -- "
                         "other values do not verify; see the module docstring.")
    ap.add_argument("--cfsm-log10", type=float, default=None,
                    help="log10 of fine_scale_mixing(1.7). Defaults to the readable floor. "
                         "The true value is BLOCKED at Sec7/Monotone.lean:163.")
    ap.add_argument("--glue", action="store_true",
                    help="c-sensitivity of the glue factors")
    args = ap.parse_args()

    cfsm_log10 = cfsm_floor_log10() if args.cfsm_log10 is None else args.cfsm_log10

    print("Effective constants of tao_collatz_quantitative (Theorem 3.1)")
    print("  (a hand trace of the witness tower, NOT an extraction -- see docstring)\n")
    report(args.alpha, cfsm_log10)
    if args.glue:
        glue_sensitivity(args.alpha)
    print("\n  c: traceable.  C: blocked at Sec7/Monotone.lean:163 (rate-free `T`).")
    print("  See notes/effective-constants.md for the full trace and the fix.")


if __name__ == "__main__":
    main()
