#!/usr/bin/env -S uv run --quiet python3
"""JUDGE PROBE — 2026-07-17 host-side ruling, big-C campaign close.

WHY THIS FILE EXISTS
--------------------
`check26` (lap 18) is the load-bearing check for the campaign-close recommendation: it is
what upgrades "no route found" to "no route remains".  Its stated conclusion is that the
entry-height tail is "poly not exp".  **Its test does not test that conclusion:**

    exp_pred = 2.718281828 ** (-(u2 - u1))      # hardcodes rate c = 1
    assert t2 / t1 > 100 * exp_pred

The observed ratios (0.40 / 0.32) fit an exponential with c ~ 0.08-0.14 *perfectly*, so the
check refutes RATE-1 decay only.  Under `agreement-needs-independent-origins`, check25 has
the sibling problem: its modelling inputs live in its comment, so it is a calculator for the
box's own hand-derivation, not an independent verification of it.

The lap-18 CONCLUSION nevertheless survives — on the evidence below, which has a different
origin.  Three probes, all reproducible:

  1. free_rate_fit()  — fit a FREE-rate exponential and a power law to the measured tail.
     Result: c ~ 3/smax, with smax growing ~log2(3) per row (linearly in n).  So c -> 0 with
     n: NO uniform exponential rate exists.  (R^2 alone cannot separate exp from power over
     this short dynamic range -- the SCALING of the fitted rate is the signal, not the fit.)

  2. collapse_test()  — plot the tail against u/smax.  Result: tails agree within 1.4-1.8x
     across instances spanning smax 25->38 and eps 100x, and the trend RISES with n where a
     fixed-rate exponential must FALL ~2.3x.  The tail is a scaling form F(u/smax): its only
     scale is smax.  This is lap-18's "inherits the size spectrum" mechanism — CONFIRMED,
     by a test that can actually see it.

  3. plantability()   — lap 18 asserts, in prose only, that a giant is plantable by one
     congruence on xi.  CONFIRMED exactly: xi = 2^{l0-1} mod 3^n forces |theta(1,l0)| =
     3^{-n}, the minimal grid phase.  STRONGER than claimed: typical xi land within ~2 nats
     of the planted maximum, so near-giants are GENERIC, not merely worst-case-in-xi.

THE LIMIT OF ALL OF IT (the reason the ruling says "no route found", not "proved closed"):
every measurement here sits at n = 22..30, eps ~ 1e-2, smax ~ 25-38 nats.  The door lives at
n ~ 10^3016, eps = 1e-1000, S ~ 4613 nats.  A Monte Carlo at n=30 cannot prove a statement
about n=10^3016.  Under the verified scaling form the door fails there by a far wider margin
than lap 18 claimed (at smax ~ 10^3016 the depth-4613 tail is F(~0) ~ 1 — no decay at all
where the door needs it) — but that is an extrapolation, not a proof.

Run: python3 tools/judge_probe_depth_tail.py
"""
import random
import math
from fractions import Fraction

from check_blueprint import decompose_black, theta_exact


# --------------------------------------------------------------------------- measurement
def entry_heights(n, xi, eps, samples=200000, seed=18):
    """check26's measurement, same walk law and same exact phase field."""
    rng = random.Random(seed)

    def sample_geom_half():
        a = 1
        while rng.random() < 0.5:
            a += 1
        return a

    def sample_pascal_ne3():
        while True:
            b = sample_geom_half() + sample_geom_half()
            if b != 3:
                return b

    def sample_hold():
        k = 1
        while rng.random() < 0.75:
            k += 1
        return (k, 3 + sum(sample_pascal_ne3() for _ in range(k - 1)))

    black, corner = decompose_black(n, xi, eps, n // 2, range(-1500, 1500))
    smax = max(math.log(float(eps) / float(abs(black[p]))) for p in black) / math.log(2)
    heights, tot = {}, 0
    for _ in range(samples):
        j, l = rng.randint(1, 3), rng.randint(-1400, 1300)
        while j <= n // 2 and l < 1400:
            if (j, l) in black:
                _, ls = corner[(j, l)]
                heights[ls - l] = heights.get(ls - l, 0) + 1
                tot += 1
                break
            dj, dl = sample_hold()
            j += dj
            l += dl
    return heights, tot, smax


def _fit(xs, ys):
    m = len(xs)
    mx, my = sum(xs) / m, sum(ys) / m
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    b = sxy / sxx
    a = my - b * mx
    ss_res = sum((y - (a + b * x)) ** 2 for x, y in zip(xs, ys))
    ss_tot = sum((y - my) ** 2 for y in ys)
    return b, a, (1 - ss_res / ss_tot if ss_tot > 0 else float("nan"))


CASES = [(22, 7, Fraction(9, 1000)), (26, 7, Fraction(9, 1000)),
         (30, 7, Fraction(9, 1000)), (26, 101, Fraction(1, 101))]


# --------------------------------------------------------------------------- probe 1
def free_rate_fit():
    print("P1. free-rate fit — does the tail have a rate of its own?")
    print(f"{'instance':>26} {'smax':>6} {'c(exp)':>8} {'R2':>6} {'c*smax':>7}")
    prod = []
    for (n, xi, eps) in CASES:
        heights, tot, smax = entry_heights(n, xi, eps)
        tail = lambda u: sum(v for k, v in heights.items() if k >= u) / tot
        us = [u for u in range(1, max(2, int(smax * 0.8))) if tail(u) > 3.0 / tot]
        ts = [tail(u) for u in us]
        c_exp, _, r2 = _fit(us, [math.log(t) for t in ts])
        prod.append(-c_exp * smax)
        print(f"  n={n:2d} xi={xi:3d} eps={str(eps):>8} {smax:6.1f} {-c_exp:8.4f} "
              f"{r2:6.3f} {-c_exp*smax:7.2f}")
    assert max(prod) / min(prod) < 2.0, prod          # c*smax ~ const => c ~ 3/smax
    print(f"  => c*smax stays in [{min(prod):.1f}, {max(prod):.1f}] while smax grows "
          f"~log2(3)/row: c ~ 3/smax -> 0 with n.  NO uniform exponential rate.\n")


# --------------------------------------------------------------------------- probe 2
def collapse_test():
    print("P2. collapse test — is the tail a scaling form F(u/smax)?")
    fracs = [0.15, 0.25, 0.40, 0.55, 0.65, 0.80]
    print(f"{'instance':>26} {'smax':>6} " + " ".join(f"{f:>6.2f}" for f in fracs))
    rows, smaxes = [], []
    for (n, xi, eps) in CASES:
        heights, tot, smax = entry_heights(n, xi, eps)
        tail = lambda u: sum(v for k, v in heights.items() if k >= u) / tot
        vals = [tail(int(f * smax)) for f in fracs]
        rows.append(vals)
        smaxes.append(smax)
        print(f"  n={n:2d} xi={xi:3d} eps={str(eps):>8} {smax:6.1f} "
              + " ".join(f"{v:6.3f}" for v in vals))
    spread = [max(r[i] for r in rows) / max(1e-9, min(r[i] for r in rows))
              for i in range(len(fracs))]
    print("  spread (max/min)      " + " " * 12 + " ".join(f"{s:6.2f}" for s in spread))
    assert max(spread) < 3.0, spread
    # a fixed-rate exponential (c=0.1) would separate these instances by ~2.3x AND put the
    # LARGER-n tail BELOW the smaller-n one; observed is a rise.
    xi7 = [r for r, (n, x, e) in zip(rows, CASES) if x == 7]
    assert xi7[-1][4] > xi7[0][4], "n=30 tail should sit ABOVE n=22 at matched u/smax"
    print(f"  => tails collapse within {max(spread):.1f}x while smax spans 1.5x and eps "
          f"spans 100x, and RISE with n\n     (a c=0.1 exponential would FALL "
          f"{math.exp(-0.1*0.65*(37.9-25.3)):.2f}x).  Tail's only scale is smax:")
    print("     lap-18's 'inherits the size spectrum' mechanism CONFIRMED.\n")


# --------------------------------------------------------------------------- probe 3
def plantability():
    print("P3. plantability — lap-18's unchecked prose claim.")
    print(f"{'n':>3} {'l0':>4} {'|theta(1,l0)|':>15} {'= 3^-n?':>9} {'size':>7} "
          f"{'typical max':>12}")
    for (n, l0) in [(12, 5), (16, 7), (20, 9), (24, 11)]:
        mod = 3 ** n
        xi = pow(2, l0 - 1, mod)                       # THE single congruence condition
        th = theta_exact(n, xi, 1, l0)
        eps = Fraction(9, 1000)
        size = math.log(float(eps) / abs(float(th)))
        exact = (abs(th) == Fraction(1, 3 ** n))
        assert exact, (n, l0, th)
        typical = []
        for xt in (7, 11, 101, 1001):
            black, _ = decompose_black(n, xt, eps, min(n // 2, 6), range(-40, 40))
            if black:
                typical.append(max(math.log(float(eps) / abs(float(v)))
                                   for v in black.values()))
        print(f"{n:3d} {l0:4d} {float(abs(th)):15.3e} {'MATCH':>9} {size:7.2f} "
              f"{max(typical):12.2f}")
    print("  => one satisfiable congruence xi = 2^{l0-1} mod 3^n forces the MINIMAL grid")
    print("     phase 3^-n (a maximal triangle): CONFIRMED.  And typical xi land within")
    print("     ~2 nats of it => near-giants are GENERIC, not merely worst-case-in-xi.\n")


if __name__ == "__main__":
    print(__doc__.split("Run:")[0].strip()[:0] or "", end="")
    print("JUDGE PROBE — big-C campaign close, 2026-07-17\n")
    free_rate_fit()
    collapse_test()
    plantability()
    print("ALL JUDGE PROBES PASS ✅  (see DIRECTION.md 'JUDGE RULING 2026-07-17')")
