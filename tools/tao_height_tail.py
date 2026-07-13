#!/usr/bin/env -S uv run --quiet python3
"""Explicit overshoot radius Y for  P(endpoint height >= s + Y) <= 1/16  -- WITHOUT X6.

The existing `fpDist_height_tail` routes through X6's `fpDist_location_bound`, whose
constants (cL, CL) are EXISTENTIAL -> Y is not a numeral -> the box inequality
sqrt(X^2+Y^2) < sep cannot be discharged.  Claim: Y is explicit by an elementary route
the file already has the pieces for.

Route (all three ingredients already in-repo):
  1. `fpDist_le_renewal_conv`:  fpDist s e <= sum_{p : p.2 <= s} renewal(p) * hold(e - p)
     (the endpoint = a pre-passage point below the budget line + ONE hold step).
  2. **Heights strictly increase**: hold's height increment is dl = 3 + sum v >= 3 > 0,
     so the walk visits each height level AT MOST ONCE
       => renewal mass at any fixed height level h is  R(h) <= 1.   (no renewal theorem!)
  3. The step height law has an exact MGF.

  P(height >= s+Y) <= sum_{u>=0} R(s-u) * P(dl >= Y+u)
                   <= sum_{u>=0} P(dl >= Y+u)
                   <= E[e^{mu*dl}] * e^{-mu*Y} / (1 - e^{-mu})     (Chernoff + geometric sum)

Step law:  k ~ geomQuarter (1/4)(3/4)^{k-1};  dl = 3 + sum_{i=1}^{k-1} v_i;  v ~ pascalNe3.
  pascalNe3 MGF:  phi(mu) = (4/3) * [ x^2/(1-x)^2 - 2x^3 ],  x = e^mu / 2   (x < 1)
  E[e^{mu*dl}] = e^{3mu} * (1/4) / (1 - (3/4) phi(mu)),   valid while (3/4) phi(mu) < 1
"""
import math


def phi(mu: float) -> float:
    """E[exp(mu*v)], v ~ pascalNe3 = Pascal(2,1/2) minus the b=3 atom, renormalized."""
    x = math.exp(mu) / 2.0
    if x >= 1.0:
        return math.inf
    return (4.0 / 3.0) * (x * x / (1 - x) ** 2 - 2 * x**3)


def mgf_dl(mu: float) -> float:
    """E[exp(mu*dl)]."""
    p = phi(mu)
    if not math.isfinite(p) or 0.75 * p >= 1.0:
        return math.inf
    return math.exp(3 * mu) * 0.25 / (1 - 0.75 * p)


def Y_needed(mu: float) -> float:
    """Smallest Y with  E[e^{mu dl}] e^{-mu Y} / (1 - e^{-mu}) <= 1/16."""
    m = mgf_dl(mu)
    if not math.isfinite(m):
        return math.inf
    return math.log(16.0 * m / (1 - math.exp(-mu))) / mu


# sanity: mean of dl should be 16
mean_v = (4.0 / 3.0) * sum((b - 1) * 2.0**-b * b for b in range(2, 4000) if b != 3)
mean_k = 4.0
print(f"mean v  = {mean_v:.6f}  (expect 13/3 = {13/3:.6f})")
print(f"mean dl = 3 + (E[k]-1)*E[v] = {3 + (mean_k - 1) * mean_v:.4f}   (expect 16)")

# critical mu: (3/4) phi(mu) -> 1
lo, hi = 1e-9, math.log(2) - 1e-12
for _ in range(300):
    mid = (lo + hi) / 2
    if 0.75 * phi(mid) < 1.0:
        lo = mid
    else:
        hi = mid
mu_c = lo
print(f"critical tilt mu_c = {mu_c:.6f}   (hard ceiling ln2 = {math.log(2):.6f})")

best_Y, best_mu = min(((Y_needed(mu_c * i / 4000), mu_c * i / 4000) for i in range(1, 4000)),
                      key=lambda p: p[0])
Y_star = math.ceil(best_Y)
print(f"optimal tilt mu*   = {best_mu:.6f}")
print(f"minimal Y for overshoot tail <= 1/16:  {best_Y:.2f}  ->  Y = {Y_star}")

# --- the box, with BOTH constants now explicit -------------------------------
B = 42          # from tao_linear_tail.py (exact-MGF transverse tail)
X = math.ceil((5 * Y_star + B) / 16)
box = math.hypot(X, Y_star)
sep_90 = 9 * math.log(10)      # (1/10)*ln(10^90)
print()
print(f"BOX with explicit constants:  B = {B},  Y = {Y_star}  ->  X = ceil((5Y+B)/16) = {X}")
print(f"  box = sqrt(X^2 + Y^2) = {box:.2f}")
print(f"  sep at the ruled eps = 10^-90:  9*ln10 = {sep_90:.2f}")
print(f"  => box < sep ?  {'YES -- CLOSES AT THE RULED EPSILON, no D4 change' if box < sep_90 else 'NO'}")
if box >= sep_90:
    d = math.ceil(box * 10 / math.log(10))
    print(f"  smallest power-of-ten eps that clears it: 10^-{d}  (sep = {0.230259*d:.1f})")
