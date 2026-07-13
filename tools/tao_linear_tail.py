#!/usr/bin/env -S uv run --quiet python3
"""Honest Chernoff constant for the fpDist transverse tail  P(16j - 5l >= B) <= 1/16.

Step law `hold` (TaoCollatz/Sec7/Holding.lean):
    k ~ geomQuarter : P(k) = (1/4)(3/4)^(k-1), k >= 1          (mean 4)
    dl = 3 + sum_{i=1}^{k-1} v_i,  v ~ pascalNe3               (mean 13/3)
    pascalNe3: P(b) = (4/3)(b-1) 2^-b, b >= 2, b != 3          (Pascal(2,1/2) minus the b=3 atom)
  => mean (4, 16), and Z := 16k - 5*dl has drift 16*4 - 5*16 = -16 per step.

Chernoff over all passage times (the renewal domination the Lean proof already uses):
    P(Z >= B) <= sum_{k>=1} e^{-thB} M(th)^k = e^{-thB} * M/(1-M),   M(th) = E[e^{th Z_step}] < 1
  => B >= (1/th) * ln(16 * M/(1-M)).

Current Lean lemma uses a crude QUADRATIC MGF bound, forcing th = 1/20000 and shipping B = 4e7.
Question: what does the EXACT geometric MGF give?
"""
import math


def phi(th: float) -> float:
    """E[exp(-5*th*v)], v ~ pascalNe3. Always finite (v >= 0, exponent negative)."""
    s = 0.0
    for b in range(2, 4000):
        if b == 3:
            continue
        s += (4.0 / 3.0) * (b - 1) * 2.0 ** (-b) * math.exp(-5.0 * th * b)
    return s


def M(th: float) -> float:
    """E[exp(th*Z_step)] = e^{-15th} * (1/4) e^{16th} / (1 - (3/4) e^{16th} phi(th))."""
    denom = 1.0 - 0.75 * math.exp(16.0 * th) * phi(th)
    if denom <= 0:
        return math.inf
    return math.exp(-15.0 * th) * 0.25 * math.exp(16.0 * th) / denom


def B_needed(th: float) -> float:
    m = M(th)
    if not (0 < m < 1):
        return math.inf
    return math.log(16.0 * m / (1.0 - m)) / th


# critical tilt: (3/4) e^{16th} phi(th) -> 1
lo, hi = 1e-9, 1.0
for _ in range(200):
    mid = (lo + hi) / 2
    if 0.75 * math.exp(16 * mid) * phi(mid) < 1.0:
        lo = mid
    else:
        hi = mid
th_c = lo
print(f"critical tilt th_c            = {th_c:.6f}   (Lean's current tilt = {1/20000:.6f})")

best = min(((B_needed(t), t) for t in [th_c * i / 2000 for i in range(1, 2000)]), key=lambda p: p[0])
B_star, th_star = best
print(f"optimal tilt th*              = {th_star:.6f}")
print(f"M(th*)                        = {M(th_star):.6f}   (< 1 required)")
print(f"minimal B for tail <= 1/16    = {B_star:.1f}        (Lean ships B = 4e7)")
print(f"  => improvement factor       = {4e7 / B_star:.3g}x")

# What the localization box then costs.  X = ceil((5Y + B)/16); need sqrt(X^2+Y^2) < sep.
# sep = (1/10) * ln(1/eps) ; eps = 10^-d  =>  sep = d * ln(10) / 10 = 0.230259 * d
print()
for Y in (2, 5, 10, 20):
    X = math.ceil((5 * Y + B_star) / 16)
    box = math.hypot(X, Y)
    d_needed = box * 10 / math.log(10)
    print(f"  Y={Y:2d}  ->  X={X:4d}   box=sqrt(X^2+Y^2)={box:7.1f}   "
          f"needs eps = 10^-{math.ceil(d_needed):d}   (today: 10^-90, sep={0.230259*90:.1f})")

print()
X_now = math.ceil((5 * 5 + 4e7) / 16)
print(f"for comparison, TODAY's box (B=4e7, Y=5): X={X_now:.3g}, "
      f"needs eps = 10^-{math.ceil(math.hypot(X_now,5)*10/math.log(10)):d}  <-- the 'infeasible numeral' claim")

# --- cross-checks against the shape the Lean lemma already ships -------------
# Lean: P(Z>=B) <= exp(-B/20000) * M/(1-M) with M = exp(-39/400000).  Same shape as ours.
th_lean = 1.0 / 20000
M_lean = math.exp(-39 / 400000)          # their crude quadratic per-step exponent
B_lean_own = math.log(16 * M_lean / (1 - M_lean)) / th_lean
print()
print("CROSS-CHECKS")
print(f"  their own bound at their own tilt needs B >= {B_lean_own:,.0f}  (they ship 4e7 = {4e7/B_lean_own:.0f}x more)")
print(f"  EXACT MGF at their tilt th=1/20000:  M={M(th_lean):.8f} vs their M={M_lean:.8f}"
      f"  -> B >= {B_needed(th_lean):,.0f}")
print(f"  EXACT MGF at optimal tilt:                                        -> B >= {B_star:.1f}")
