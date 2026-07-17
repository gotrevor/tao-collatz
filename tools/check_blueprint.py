#!/usr/bin/env -S uv run --quiet python3
"""D8 numeric sanity harness for the Tao-Collatz blueprint.

Brute-force-verifies finite instances of delicate blueprint statements BEFORE
their Lean forms are ratified (statement-trap killer). Exact rational arithmetic.

Checks:
  1. Fnat integerification identity (D2 / paper (1.7)):
       2^|a| * syr^[n](N) = 3^n * N + Fnat(n, a)   for the valuation vector a of N
  2. colMin(N) = syrMin(oddPart(N))                (paper (1.2))
  3. Syrac(Z/9Z) distribution == paper p.10 table  (via BOTH (1.21) and (1.26) forms)
  4. Negative binomial: P(|Geom(2)^n| = L) = C(L-1, n-1) * 2^-L
  5. Lemma 1.12 recursion reproduces the Z/3Z and Z/9Z tables
  6. Lemma 7.4 qualitative scan: black set at (n, xi, eps) decomposes into
     upper-left-corner triangles separated in j (visual/structural spot check)
"""
from fractions import Fraction
from math import comb, floor, log
import random

def nu2(m: int) -> int:
    a = 0
    while m % 2 == 0:
        m //= 2; a += 1
    return a

def syr(n: int) -> int:
    m = 3 * n + 1
    return m >> nu2(m)

def col(n: int) -> int:
    return 3 * n + 1 if n % 2 else n // 2

def orbit_min(f, n, steps):
    best = n
    for _ in range(steps):
        n = f(n); best = min(best, n)
    return best

def valuation_vector(N: int, n: int) -> list[int]:
    """a^(n)(N) per (1.8): a_i = nu2(3*Syr^{i-1}(N)+1)."""
    a, cur = [], N
    for _ in range(n):
        a.append(nu2(3 * cur + 1)); cur = syr(cur)
    return a

def fnat(n: int, a: list[int]) -> int:
    """Fnat n a = sum_{m=0}^{n-1} 3^(n-1-m) * 2^(a[0]+...+a[m-1])  (D2)."""
    tot, pref = 0, 0
    for m in range(n):
        tot += 3 ** (n - 1 - m) * 2 ** pref
        pref += a[m]
    return tot

def check1():
    rng = random.Random(2026)
    for _ in range(500):
        N = rng.randrange(1, 10**6) * 2 + 1
        n = rng.randrange(0, 25)
        a = valuation_vector(N, n)
        cur = N
        for _ in range(n):
            cur = syr(cur)
        assert 2 ** sum(a) * cur == 3 ** n * N + fnat(n, a), (N, n, a)
    print("1. Fnat identity  2^|a|*syr^n(N) = 3^n*N + Fnat   OK (500 random cases)")

def check2():
    for N in range(1, 3000):
        odd = N >> nu2(N)
        cm = orbit_min(col, N, 500)
        sm = orbit_min(syr, odd, 200)
        assert cm == sm, (N, cm, sm)
    print("2. colMin(N) == syrMin(oddPart N)                 OK (N < 3000)")

def syrac_dist_direct(n: int, reversed_form: bool, amax: int = 400):
    """Distribution of Syrac(Z/3^n Z) by direct summation over tuples.

    (1.21): F_n(a) mod 3^n = 2^{-|a|} Fnat(n,a);  (1.26) reversed:
    sum_j 3^j 2^{-a[0..j]}.  2^{-1} taken as inverse of 2 mod 3^n."""
    mod = 3 ** n
    inv2 = pow(2, -1, mod)
    dist = [Fraction(0)] * mod
    # weight 2^-|a|; truncate each a_i at amax (tail negligible vs 1/63 checks)
    def rec(i, tup):
        if i == n:
            if reversed_form:
                v, pref = 0, 0
                for j in range(n):
                    pref += tup[j]
                    v = (v + 3 ** j * pow(inv2, pref, mod)) % mod
            else:
                v = (fnat(n, list(tup)) * pow(inv2, sum(tup), mod)) % mod
            dist[v] += Fraction(1, 2 ** sum(tup))
            return
        for ai in range(1, amax):
            rec(i + 1, tup + (ai,))
    if n == 0:
        rec(0, ())
        return dist
    if n == 1:
        per1 = 2  # ord(2 mod 3)
        for r in range(per1):
            a0 = r + 1
            mass = Fraction(2 ** per1, 2 ** a0 * (2 ** per1 - 1))
            dist[pow(inv2, a0, mod) % mod] += mass
        return dist
    # n == 2: nested loops with exact geometric tail folding via period 2*3^(n-1)=6
    # exploit periodicity of 2^{-a} mod 9: period 6 in each coordinate
    per = 2 * 3 ** (n - 1)
    tail = [Fraction(0)] * per  # total mass of a ≡ r (mod per), a ≥ 1
    for r in range(per):
        # sum_{k: a=r+1+k*per} 2^-a  where a≥1, a≡(r+1) mod per
        a0 = r + 1
        tail[r] = Fraction(2 ** per, 2 ** a0 * (2 ** per - 1))
    for r1 in range(per):
        for r2 in range(per):
            a1, a2 = r1 + 1, r2 + 1
            if reversed_form:
                v = (pow(inv2, a1, mod) + 3 * pow(inv2, a1 + a2, mod)) % mod
            else:
                v = ((3 * 2 ** a2 + 1) * pow(inv2, a1 + a2, mod)) % mod  # Fnat(2,a)=3+2^{a1}? see note
            # NOTE: Fnat(2,[a1,a2]) = 3 + 2^{a1};  F_2 = 2^{-a1-a2}(3 + 2^{a1}) -- wait, recompute:
            # Fnat n a = sum_m 3^{n-1-m} 2^{pref(m)}; n=2: m=0: 3^1*2^0=3; m=1: 3^0*2^{a1}=2^{a1}.
            v2 = ((3 + 2 ** a1) * pow(inv2, a1 + a2, mod)) % mod
            if not reversed_form:
                v = v2
            dist[v] += tail[r1] * tail[r2]
    return dist

def check3():
    paper = [Fraction(k, 63) for k in [0, 8, 16, 0, 11, 4, 0, 2, 22]]
    for rev in (False, True):
        d = syrac_dist_direct(2, reversed_form=rev)
        assert sum(d) == 1, sum(d)
        assert d == paper, (rev, [str(x) for x in d])
    print("3. Syrac(Z/9Z) == paper table (both (1.21) & (1.26) forms)  OK  [8/63,16/63,...]")

def check4():
    rng = random.Random(7)
    for _ in range(200):
        n = rng.randrange(1, 8)
        L = rng.randrange(1, 40)
        # brute force count of compositions of L into n positive parts, weight 2^-L
        cnt = 0
        def rec(i, s):
            nonlocal cnt
            if i == n:
                cnt += (s == L); return
            for ai in range(1, L - s - (n - i - 1) + 1):
                rec(i + 1, s + ai)
        rec(0, 0)
        expect = comb(L - 1, n - 1) if L >= n else 0
        assert cnt == expect, (n, L, cnt, expect)
    print("4. P(|Geom(2)^n| = L) = C(L-1,n-1) 2^-L (composition count)  OK")

def check5():
    # Lemma 1.12: P(Syrac(Z/3^{n+1}) = x) = [sum_{1<=a<=2*3^n : 2^a x = 1 mod 3} 2^-a
    #             P(Syrac(Z/3^n) = (2^a x - 1)/3)] / (1 - 2^{-2*3^n})
    d1 = syrac_dist_direct(1, reversed_form=False)   # Z/3: expect [0, 1/3, 2/3]
    assert d1 == [Fraction(0), Fraction(1, 3), Fraction(2, 3)], d1
    per = 2 * 3
    d2 = [Fraction(0)] * 9
    for x in range(9):
        s = Fraction(0)
        for a in range(1, per + 1):
            if (pow(2, a, 3) * x) % 3 == 1:
                y = (pow(2, a, 27) * x - 1) % 27
                assert y % 3 == 0
                s += Fraction(1, 2 ** a) * d1[(y // 3) % 3]
        d2[x] = s / (1 - Fraction(1, 2 ** per))
    paper = [Fraction(k, 63) for k in [0, 8, 16, 0, 11, 4, 0, 2, 22]]
    assert d2 == paper, [str(v) for v in d2]
    print("5. Lemma 1.12 recursion reproduces Z/3 and Z/9 tables       OK")

def theta(j, l, n, xi):
    """theta(j,l) = signed frac part of xi*3^{2j-2}*(2^{-l+1} mod 3^n)/3^n  (7.8)."""
    mod = 3 ** n
    v = (xi * pow(3, 2 * j - 2, mod) * pow(pow(2, -1, mod), l - 1, mod)) % mod
    f = Fraction(v, mod)
    return f - 1 if f > Fraction(1, 2) else f  # in (-1/2, 1/2]

def check6(n=14, xi=1, eps=0.02):
    half = n // 2
    black = set()
    lo, hi = -3 * n, 3 * n
    for j in range(1, half + 1):
        for l in range(lo, hi):
            if abs(theta(j, l, n, xi)) <= eps:
                black.add((j, l))
    # structural claims from Lemma 7.4 (qualitative):
    #  (a) black points confined to j <= n/2 - (1/10) log(1/eps)  [via (7.16)]
    jmax_claim = half - log(1 / eps) / (10 * log(3))  # (7.16): 3^{n+1-2j} eps >= 1/3
    bad = [p for p in black if p[0] > half - 1 and abs(theta(p[0], p[1], n, xi)) <= eps]
    #  (b) columns: per j, black l-values form contiguous runs (triangle vertical sections)
    runs_ok = True
    for j in set(p[0] for p in black):
        ls = sorted(l for (jj, l) in black if jj == j)
        # allowed: multiple runs (different triangles) but each run contiguous & separated
        gaps = [b - a for a, b in zip(ls, ls[1:])]
        # no isolated singletons *adjacent* to another run closer than 2 (weak check)
        runs = 1 + sum(1 for g in gaps if g > 1)
        if runs > 6:
            runs_ok = False
    print(f"6. Lemma 7.4 scan n={n} xi={xi} eps={eps}: {len(black)} black pts, "
          f"j-range {min((p[0] for p in black), default='-')}-{max((p[0] for p in black), default='-')} "
          f"(claim j <~ {jmax_claim:.1f}), column-runs sane: {runs_ok}")

# ---------------------------------------------------------------------------
# §7 kernel de-risk checks (added 2026-07-10, first box lap). Anchors:
# pairing identity p.33, (7.4)-(7.9), Lemma 7.4 pp.36-41, Case 2 (7.44)-(7.51),
# Lemma 7.10 pp.51-54. Conventions match the Lean skeleton:
#   paper j (1-indexed) = Lean j + 1;  white point of index j is (j, b_{[1,j]}).
# ---------------------------------------------------------------------------
import cmath

def theta_exact(n: int, xi: int, j: int, l: int) -> Fraction:
    """theta(j,l) (7.8), EXACT: signed frac of xi*3^{2j-2}*(2^{-l+1} mod 3^n)/3^n,
    valued in (-1/2, 1/2]. Paper-indexed j >= 1, l in Z."""
    mod = 3 ** n
    v = (xi * pow(3, 2 * j - 2, mod) * pow(2, -(l - 1), mod) if l >= 1
         else xi * pow(3, 2 * j - 2, mod) * pow(2, 1 - l, mod)) % mod
    f = Fraction(v, mod)
    return f - 1 if f > Fraction(1, 2) else f

def chi(n: int, xi: int, num: int, k: int) -> complex:
    """chi(x) (7.1) for x = num / 2^k in Z[1/2]: e^{-2 pi i xi (x mod 3^n)/3^n}."""
    mod = 3 ** n
    v = (xi * num * pow(2, -k, mod)) % mod
    return cmath.exp(-2j * cmath.pi * v / mod)

def f_cond(n: int, xi: int, num: int, k: int, b: int) -> complex:
    """f(x,b) (7.4) with x = num/2^k: E(chi(x(2^{a2}+3)) | a1+a2=b); a2 uniform on [1,b-1]."""
    return sum(chi(n, xi, num * (2 ** a2 + 3), k) for a2 in range(1, b)) / (b - 1)

def check7():
    """Coordinate-convention anchor for Prop 7.3 / renewal_white_encounters.

    (a) pairing identity p.33 (exact, Fractions);
    (b) (7.7): chi(3^{2j-2} 2^{-l+1}) = e^{-2 pi i theta(j,l)};
    (c) |f(3^{2j-2} 2^{-b_{[1,j]}}, 3)| = |cos(pi*theta(j, b_{[1,j]}))|  -- the white
        point tested by index j is EXACTLY (j, b_{[1,j]}) = Lean (j_lean, pre b (j_lean+1));
    (d) end-to-end: |S_chi(n)| <= E prod_j |f| <= E exp(-eps^3 #white encounters).
    """
    rng = random.Random(11)
    # (a) pairing identity: sum_{m=1}^n 3^{m-1} 2^{-a_[1,m]}
    #     = sum_{j in [n/2]} 3^{2j-2} 2^{-b_[1,j]} (2^{a_2j}+3)  (+ 3^{n-1}2^{-a_[1,n]} if n odd)
    for _ in range(300):
        n = rng.randrange(2, 12)
        a = [rng.randrange(1, 12) for _ in range(n)]
        lhs = sum(Fraction(3 ** (m - 1), 2 ** sum(a[:m])) for m in range(1, n + 1))
        b = [a[2 * j - 2] + a[2 * j - 1] for j in range(1, n // 2 + 1)]
        rhs = sum(Fraction(3 ** (2 * j - 2), 2 ** sum(b[:j])) * (2 ** a[2 * j - 1] + 3)
                  for j in range(1, n // 2 + 1))
        if n % 2 == 1:
            rhs += Fraction(3 ** (n - 1), 2 ** sum(a))
        assert lhs == rhs, (n, a)
    # (b) + (c)
    for _ in range(400):
        n = rng.randrange(2, 9)
        xi = rng.choice([x for x in range(1, 3 ** n) if x % 3 != 0])
        j = rng.randrange(1, max(n // 2, 1) + 1)
        l = rng.randrange(-30, 60)
        th = theta_exact(n, xi, j, l)
        num, k = 3 ** (2 * j - 2), l - 1
        if k < 0:
            num, k = num * 2 ** (-k), 0
        assert abs(chi(n, xi, num, k) - cmath.exp(-2j * cmath.pi * float(th))) < 1e-9
        fv = f_cond(n, xi, 3 ** (2 * j - 2) * (2 ** max(0, -l)), max(l, 0), 3)
        assert abs(abs(fv) - abs(cmath.cos(cmath.pi * float(th)))) < 1e-9, (n, xi, j, l)
    # (d) end-to-end at n = 4 (even: no g factor), truncated a_i <= amax
    eps = Fraction(1, 10 ** 4)
    for xi in (1, 5, 7, 20):
        n, amax = 4, 14
        import itertools
        S = 0 + 0j; rhs = 0.0; mass = Fraction(0)
        for a in itertools.product(range(1, amax + 1), repeat=n):
            w = Fraction(1, 2 ** sum(a))
            mass += w
            num = sum(3 ** (m - 1) * 2 ** (sum(a) - sum(a[:m])) for m in range(1, n + 1))
            S += float(w) * chi(n, xi, num, sum(a))
            b = [a[0] + a[1], a[2] + a[3]]
            cnt = sum(1 for j in (1, 2)
                      if b[j - 1] == 3 and abs(theta_exact(n, xi, j, sum(b[:j]))) > eps)
            rhs += float(w) * 2.718281828459045 ** (-float(eps) ** 3 * cnt)
        err = float(1 - mass) * 1.05  # truncated tail, |chi|<=1
        assert abs(S) <= rhs + 2 * err, (xi, abs(S), rhs, err)
    print("7. §7 pairing identity, (7.7), |f|=|cos(pi theta)|, |S_chi| <= E exp(-eps^3 #W)  OK")

def decompose_black(n: int, xi: int, eps: Fraction, jmax: int, lwin: range):
    """Implement the paper's l*/j* construction (pp.38-39) on the actual black set,
    EXACTLY (rational theta).  Returns (blacks, corners) where corners maps each black
    point in the window to its triangle corner (j*, l*), plus theta* values."""
    black = {}
    for j in range(1, jmax + 1):
        for l in lwin:
            th = theta_exact(n, xi, j, l)
            if abs(th) <= eps:
                black[(j, l)] = th
    corner = {}
    for (j, l) in black:
        lstar = l
        while (j, lstar + 1) in black:
            lstar += 1
        jstar = j
        while jstar > 1 and (jstar - 1, lstar) in black:
            jstar -= 1
        corner[(j, l)] = (jstar, lstar)
    return black, corner

def check8(n=30, xi=7, eps=Fraction(9, 1000), jmax=None, L=1500):
    """Lemma 7.4, full structural validation at a concrete instance (EXACT arithmetic).

    Builds the l*/j* decomposition and verifies, for every triangle with corner
    (j*,l*), |theta*| = eps*exp(-s*):
      (1) lattice-triangle (7.11) with size s* = log(eps/|theta*|) equals EXACTLY
          the set of black points sharing that corner, via the exact test
          9^{j-j*} 2^{l*-l} |theta*| <= eps  (equality case of (7.18));
      (2) member phases obey the (7.18) EQUALITY |theta(j,l)| = 9^{dj} 2^{dl} |theta*|
          whenever rhs < 1/2;
      (3) pairwise Euclidean separation of triangle point-SETS >= (1/10) log(1/eps);
      (4) strip confinement j <= n/2 - (1/10) log(1/eps).
    Window-edge triangles are excluded from completeness claims."""
    jmax = jmax or n // 2
    lwin = range(-L, L)
    black, corner = decompose_black(n, xi, eps, jmax, lwin)
    margin = 80  # exclude anything near the l-window edge
    safe = lambda p: -L + margin <= p[1] <= L - 1 - margin
    tris = {}
    for p, c in corner.items():
        tris.setdefault(c, set()).add(p)
    n_checked = 0
    logeps_inv = log(1 / float(eps))
    for (js, ls), members in tris.items():
        if not all(safe(p) for p in members) or not safe((js, ls)):
            continue
        n_checked += 1
        tstar = abs(black[(js, ls)])
        assert tstar <= eps and tstar > 0
        # (1) exact triangle membership == corner fibre; size s* = log(eps/theta*)
        sstar = log(float(eps) / float(tstar))
        smax_j = int(sstar / log(9)) + 2
        smax_l = int(sstar / log(2)) + 3
        tri_pts = set()
        for j in range(js, min(js + smax_j + 1, jmax + 1)):
            for l in range(ls - smax_l, ls + 1):
                if 9 ** (j - js) * 2 ** (ls - l) * tstar <= eps:
                    tri_pts.add((j, l))
        assert tri_pts == members, ((js, ls), sorted(tri_pts ^ members))
        # (2) equality case of (7.18)
        for (j, l) in members:
            scaled = 9 ** (j - js) * 2 ** (ls - l) * tstar
            if scaled < Fraction(1, 2):
                assert abs(black[(j, l)]) == scaled, ((js, ls), (j, l))
        # (4) strip confinement
        for (j, l) in members:
            assert j <= n / 2 - logeps_inv / 10, ((js, ls), (j, l), n)
    # (3) pairwise set separation (only fully-safe triangles, brute force over pairs)
    keys = [c for c, ms in tris.items() if all(safe(p) for p in ms) and safe(c)]
    sep2 = (logeps_inv / 10) ** 2
    for i in range(len(keys)):
        for k in range(i + 1, len(keys)):
            c1, c2 = keys[i], keys[k]
            if (c1[0] - c2[0]) ** 2 + (c1[1] - c2[1]) ** 2 > (200) ** 2:
                continue
            d2 = min((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2
                     for p in tris[c1] for q in tris[c2])
            assert d2 >= sep2, (c1, c2, d2, sep2)
    sizes = sorted(round(log(float(eps) / float(abs(black[c]))), 2) for c in keys)
    print(f"8. Lemma 7.4 EXACT decomposition n={n} xi={xi} eps={eps}: "
          f"{len(black)} black pts -> {n_checked} triangles validated "
          f"(partition/equality/separation/strip), sizes up to {sizes[-1] if sizes else 0}")
    return black, {c: tris[c] for c in keys}

def check9(n=30, xi=7, eps=Fraction(9, 1000), samples=4000):
    """Case 2 white-exit probability (7.50)/(7.51), Monte Carlo.

    From a shallow start inside a triangle, run the renewal walk with iid Hold
    steps to first passage above l_Delta, and record whether the passage location
    is white. Paper claims this probability is >> 1 (absolute constant).
    Also reports the Lemma 7.9 epsilon-site: need c0 >= (1-e^{-eps})/(1-1/e)."""
    rng = random.Random(2027)
    # re-run the (check8-validated) decomposition to get a triangle inventory
    black, corner = decompose_black(n, xi, eps, n // 2, range(-1500, 1500))
    tris = {}
    for p, c in corner.items():
        tris.setdefault(c, set()).add(p)
    big = sorted(tris.items(), key=lambda kv: -len(kv[1]))[:6]

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

    total_ok = 0; total = 0
    for (js, ls), members in big:
        # shallow starts: l within 3 of l_Delta (Case 2 regime s <= m/log^2 m)
        starts = [p for p in members if ls - p[1] <= 3]
        for _ in range(samples // len(big)):
            j, l = rng.choice(starts)
            s = ls - l
            jj, ll = j, l
            while ll - l <= s:  # first passage: l_[1,k] > s
                dj, dl = sample_hold()
                jj += dj; ll += dl
            if jj <= n // 2:
                th = theta_exact(n, xi, jj, ll)
                total += 1
                total_ok += (abs(th) > eps)
    c0 = total_ok / total
    need = (1 - 2.718281828 ** (-1e-4)) / (1 - 1 / 2.718281828)
    assert c0 > 0.5, c0   # empirically the exit is white with high probability
    assert c0 >= need
    print(f"9. Case 2 white-exit Monte Carlo: P(exit in W) ~= {c0:.3f} over {total} walks "
          f"(needs >= {need:.2e} for Lemma 7.9 with eps=1e-4)  OK")

def check10(n=30, xi=7, eps=Fraction(9, 1000)):
    """Lemma 7.10 deterministic core: row-interval disjointness + Sigma separation.

    (i) at every level l, the j-extents (rows) of distinct triangles are disjoint
        integer intervals (this is the mechanism behind the 'no common integer
        point' step on p.54);
    (ii) for pairs of triangles with size >= s' whose bottom tips are aligned
        within 10 (the (7.65) configuration), corner j's are >= (log2/(2 log9)) s'
        - O(alignment) apart."""
    black, corner = decompose_black(n, xi, eps, n // 2, range(-1500, 1500))
    tris = {}
    for p, c in corner.items():
        tris.setdefault(c, set()).add(p)
    rows = {}  # level -> list of (corner, jmin, jmax)
    for c, ms in tris.items():
        by_l = {}
        for (j, l) in ms:
            by_l.setdefault(l, []).append(j)
        for l, js in by_l.items():
            js.sort()
            assert js == list(range(js[0], js[-1] + 1)), (c, l, js)  # rows contiguous
            rows.setdefault(l, []).append((c, js[0], js[-1]))
    for l, ivs in rows.items():
        ivs.sort(key=lambda t: t[1])
        for (c1, a1, b1), (c2, a2, b2) in zip(ivs, ivs[1:]):
            assert b1 < a2, (l, c1, c2)  # (i) disjoint rows
    log2, log9 = log(2), log(9)
    sizes = {c: log(float(eps) / float(abs(black[c]))) for c in tris}
    checked_pairs = 0
    for sp in (2.0, 4.0, 6.0):
        cand = [c for c in tris if sizes[c] >= sp]
        for i in range(len(cand)):
            for k in range(i + 1, len(cand)):
                c1, c2 = cand[i], cand[k]
                tip1 = c1[1] - sizes[c1] / log2
                tip2 = c2[1] - sizes[c2] / log2
                if abs(tip1 - tip2) <= 10:
                    gap = abs(c1[0] - c2[0])
                    lower = (log2 / (2 * log9)) * sp - (log2 / log9) * 10 - 1
                    assert gap >= lower, (sp, c1, c2, gap, lower)
                    checked_pairs += 1
    print(f"10. Lemma 7.10 core: rows disjoint at every level; {checked_pairs} aligned "
          f"big-triangle pairs obey the Sigma j-separation bound  OK")

def check11():
    """Every §7 usage site of the D4 constant eps = 1/10^4 (and the 1/100 weakly-black
    threshold), as concrete numeric inequalities."""
    e = 1e-4
    assert 0 < e < 1 / 100                                   # standing hypothesis §7
    # Lemma 7.2 Taylor site: |theta| > eps => cos(pi theta) <= exp(-eps^3)
    ths = [e * (1 + k / 500) for k in range(1, 2000)] + [0.01, 0.1, 0.25, 0.5]
    for th in ths:
        assert abs(cmath.cos(cmath.pi * th)) <= 2.718281828 ** (-e ** 3), th
    l2, l9, l18 = log(2), log(9), log(18)
    # Claim (*) Case 1 (p.39): eps^{1 - log18/10} in (eps, 1/2)
    assert 0 < 1 - l18 / 10 and e ** (1 - l18 / 10) < 0.5 and e ** (1 - l18 / 10) > e
    # Case 2 (p.40): eps^{1-log2/10} and eps^{1-log9/10} <= 1/100 (weakly black)
    assert e ** (1 - l2 / 10) <= 1 / 100 and e ** (1 - l9 / 10) <= 1 / 100
    # Case 3 (p.40): eps^{1-(log9+log2)/10} <= 1/100
    assert e ** (1 - l18 / 10) <= 1 / 100
    # weakly-black claims (i)-(iii) (p.38): threshold arithmetic at 1/100
    assert 1 / 100 + 4 / 100 <= 5 / 100 + 1e-15 and 9 * (5 / 100) < 0.5
    assert 9 * (1 / 100) < 0.5 and 2 * (9 / 100) < 0.5
    # strip constant (7.16): black => j <= n/2 + 1/2 - log(1/eps)/(2 log 3); need
    # this to be <= n/2 - (1/10) log(1/eps), i.e. (1/2 - l2? no:) numeric:
    L = log(1 / e)
    assert 0.5 - L / (2 * log(3)) <= -L / 10
    # Case 1 of Prop 7.8 (7.43): exp(-eps^3/2) sanity: exp(-e^3) <= 1 - e^3/4... wait,
    # (7.46)->(7.47) uses exp(-eps^3/2) <= 1 - eps^3/4: check
    assert 2.718281828 ** (-e ** 3 / 2) <= 1 - e ** 3 / 4
    # Figure 3 slope room: E Hold = (4,16) mean slope 16/4 = 4 > log9/log2
    assert 16 / 4 > l9 / l2
    print("11. eps = 1/10^4 survives every §7 usage site (7.2, Claim (*) Cases 1-3, "
          "weakly-black constants, (7.16) strip, (7.47), slope)  OK")

def check12(n=14, xi=1, eps=Fraction(2, 100), damp=None, B=44, tol=1e-9):
    """(7.36)-bridge check (judge item 9, 2026-07-09 directive).

    Two INDEPENDENT computations of the same expectation:
      side A (pascal columns, mirrors `renewal_white_encounters` LHS):
        E_{b iid Pascal} damp^{#{j in [1,half] : b_j = 3, (j, b_[1,j]) in W}}
        via a per-column DP  A(j,l) = sum_b P(b) * fac * A(j+1, l+b);
      side B (hold jumps, mirrors Decay.lean's seam E Q(Hold) with the D6
        recursion (7.34)/(7.35) and the `whiteSet` adapter):
        sum_d P(Hold=d) Q(d)  with  Q(j,l) = fac(j,l) * E Q((j,l)+Hold),
        Q = 1 past the strip; hold atoms with d1 > half - j hit the boundary
        regardless of l, so the k-tail (3/4)^{half-j} is EXACT.
    Agreement pins the renewal identity (7.26)==(7.27) + the paper-vs-0-based
    coordinate seam end-to-end (this is the check that would have caught the
    whiteSet off-by-one mechanically).  W(jp,l) := |theta(jp,l)| > eps for
    paper columns 1..half (Lean: white n xi (jp-1) l).
    damp: per-encounter factor; default exp(-eps^3) (the statement's value) —
    ALSO run with an amplified damp (e.g. 1/e) so a coordinate bug shows at O(1).
    B: pascal/pascalNe3 truncation (tails tracked into the tolerance budget)."""
    half = n // 2
    lam = damp if damp is not None else 2.718281828459045 ** (-float(eps) ** 3)

    from functools import lru_cache

    @lru_cache(maxsize=None)
    def is_white(jp: int, l: int) -> bool:
        return jp >= 1 and abs(theta_exact(n, xi, jp, l)) > eps

    # --- side A: pascal-column DP ------------------------------------------
    pascal_p = {b: (b - 1) / 2.0 ** b for b in range(2, B + 1)}
    pascal_tail = 1.0 - sum(pascal_p.values())

    @lru_cache(maxsize=None)
    def A(j: int, l: int) -> float:
        if j >= half:
            return 1.0
        tot = pascal_tail  # tail columns: b > B >= 4 so b != 3 => factor 1, A ~ 1
        for b, pb in pascal_p.items():
            fac = lam if (b == 3 and is_white(j + 1, l + b)) else 1.0
            tot += pb * fac * A(j + 1, l + b)
        return tot

    VA = A(0, 0)

    # --- side B: hold-jump DP ----------------------------------------------
    # pascalNe3 (7.29): P(b) = (4/3)(b-1)/2^b, b >= 2, b != 3
    ne3 = {b: (4.0 / 3.0) * (b - 1) / 2.0 ** b for b in range(2, B + 1) if b != 3}
    ne3_tail = 1.0 - sum(ne3.values())
    # second-coordinate distribution of Hold given d1 = k: 3 + (k-1)-fold conv
    dist = [{}, {3: 1.0}]                                # dist[k][dl] for k >= 1
    for k in range(2, half + 1):
        prev, cur = dist[k - 1], {}
        for s, ps in prev.items():
            for b, pb in ne3.items():
                cur[s + b] = cur.get(s + b, 0.0) + ps * pb
        dist.append(cur)
    pk = {k: 0.25 * 0.75 ** (k - 1) for k in range(1, half + 1)}

    @lru_cache(maxsize=None)
    def Q(j: int, l: int) -> float:
        if j > half:
            return 1.0
        fac = lam if is_white(j, l) else 1.0             # whiteSet adapter (1<=j guard)
        tot = 0.75 ** (half - j)                          # exact k-tail (Q = 1 there)
        for k in range(1, half - j + 1):
            for dl, pdl in dist[k].items():
                tot += pk[k] * pdl * Q(j + k, l + dl)
        return fac * tot

    VB = 0.75 ** half                                     # Hold atoms with d1 > half
    for k in range(1, half + 1):
        for dl, pdl in dist[k].items():
            VB += pk[k] * pdl * Q(k, dl)

    err = abs(VA - VB)
    budget = 4 * half * (pascal_tail + half * ne3_tail)   # crude truncation budget
    assert err <= max(tol, 10 * abs(budget)), (VA, VB, err)
    print(f"12. (7.36)-bridge n={n} xi={xi} eps={eps} damp={lam:.6g}: "
          f"E_pascal = {VA:.12f}  vs  E Q(Hold) = {VB:.12f}  (|diff| = {err:.2e})  OK")

def check13():
    # C8 / Prop 5.2 (5.8) exact-reindex trap (added judge pass 30, 2026-07-14).
    # The pin approxMainTerm renders P(Aff_a(N_y)=M) as the mass of the EXACT affine event
    #   3^k N + fnat(k,a) = M * 2^{|a|}            (Tao (5.18)/(5.19), Lemma 2.1),
    # NOT the N-truncating Aff = floor((3^k N + fnat)/2^{|a|}).  Under truncation, Aff depends on
    # `a` essentially only through |a|, collapsing exponentially many good tuples into one M-window,
    # so the old truncation_error_bound would be FALSE.  This trap pins the gap on a finite
    # instance: the exact-divisibility count is O(1) while the truncating count is huge.  A future
    # v1-style regression (dropping the divisibility guard) trips `guard_cnt <= 5`.
    from itertools import product
    def pre(a, m): return sum(a[:m])
    def good(a, k, thr): return all(abs(pre(a, n) - 2 * n) <= thr for n in range(1, k + 1))
    k, N, W, thr = 8, 7, 4.0, 3
    true_val = N
    for _ in range(k):
        true_val = syr(true_val)
    lo, hi = true_val / W, true_val * W
    trunc_cnt = guard_cnt = 0
    for a in product(range(1, 6), repeat=k):
        if not good(a, k, thr):
            continue
        num = 3 ** k * N + fnat(k, a)
        den = 2 ** pre(a, k)
        if lo <= num // den <= hi:            # truncating (floor) Aff in the E' window
            trunc_cnt += 1
            if num % den == 0:                # the EXACT (5.18) divisibility guard
                guard_cnt += 1
    assert guard_cnt <= 5, (k, N, guard_cnt)          # exact reindex is O(1) (Lemma 2.1 bijection)
    assert trunc_cnt >= 100, (k, N, trunc_cnt)        # truncation over-counts (5.8) grossly
    assert trunc_cnt >= 50 * (guard_cnt + 1), (k, N, trunc_cnt, guard_cnt)
    print(f"13. C8 (5.8) exact reindex: trunc={trunc_cnt} >> exact-guard={guard_cnt} (k={k} N={N})  OK")


def check14():
    # C6 §3 pins (2026-07-15): Thm 3.1 Syracuse forms + AlmostAllOdd normalizer.
    # logSum A (oddInterval x) = sum_{N odd, 1<=N<=x, N in A} 1/N; logProb normalizes by the
    # ODD-window mass, NOT the full [1,x] mass.  Plausible-wrong renderings this traps:
    #   (a) normalizing the odd-window probability by full-window (Finset.Icc 1 x) mass (gives ~1/2, not 1);
    #   (b) the two Thm 3.1 displays not being complementary (sum-form vs 1 - prob-form).
    x = 30_000
    S_odd = sum(Fraction(1, N) for N in range(1, x + 1, 2))
    S_all = sum(Fraction(1, N) for N in range(1, x + 1))
    # (a) the sure event on the odd window has logProb EXACTLY 1 under the intended
    # normalizer; under the wrong (full-window) normalizer it is ~ 1/2.
    assert S_odd / S_odd == 1
    assert S_odd / S_all < Fraction(7, 10), float(S_odd / S_all)
    # log-uniformity sanity: residue 1 mod 4 carries ~half the odd-window mass (the
    # constant term drifts at finite x: 0.568 at x=3e4).  A full-window-normalized
    # wrong rendering would sit near 1/4 — the bracket separates the two.
    S_1mod4 = sum(Fraction(1, N) for N in range(1, x + 1, 4))
    assert Fraction(45, 100) < S_1mod4 / S_odd < Fraction(65, 100), float(S_1mod4 / S_odd)
    # (b) display equivalence, Fraction-exact, on a NON-degenerate synthetic bad set
    # {N : syrMin-proxy > N0} := {N : N > N0} (syrMin itself is 1 for every small odd N,
    # which would make the bad set empty and the check vacuous):
    N0 = 137
    bad = sum(Fraction(1, N) for N in range(1, x + 1, 2) if N > N0)
    good = sum(Fraction(1, N) for N in range(1, x + 1, 2) if N <= N0)
    assert bad / S_odd == 1 - good / S_odd                    # sum form <-> 1 - prob form
    # and the real bad set IS empty at small scale (all odd N <= 3000 reach 1):
    for N in range(1, 3001, 2):
        assert orbit_min(syr, N, 400) == 1, N
    print(f"14. C6 Thm 3.1 forms: odd-window normalizer + display equivalence      OK (x={x})")

def check15():
    # C6 (1.2) pullback trap: logSum {N | oddPart N in A} (Finset.Icc 1 x)
    #                           <= 2 * logSum A (oddInterval x)
    # via sum_{N<=x, oddPart N in A} 1/N = sum_a 2^-a sum_{M in A odd, M<=x/2^a} 1/M.
    # The trap checks BOTH directions: the intended constant 2 holds (exactly), and the
    # bound is nearly attained (ratio > 1.8), so a plausible-wrong rendering with
    # constant 1 (forgetting the geometric series over nu2) FAILS.
    x = 2 ** 16
    for label, A in [("M%3==1", lambda M: M % 3 == 1),
                     ("M<=999", lambda M: M <= 999),
                     ("all",    lambda M: True)]:
        lhs = sum(Fraction(1, N) for N in range(1, x + 1) if A(N >> nu2(N)))
        rhs_half = sum(Fraction(1, M) for M in range(1, x + 1, 2) if A(M))
        assert lhs <= 2 * rhs_half, (label, float(lhs), float(rhs_half))
        assert lhs > Fraction(18, 10) * rhs_half, (label, float(lhs / rhs_half))
    print(f"15. C6 (1.2) oddPart pullback: constant 2 exact and >1.8-tight          OK (x=2^16)")


def check16():
    # Effective-constants campaign (2026-07-16, DIRECTION step 3): exact-arithmetic mirror
    # of the c_* witness min-tree (Sec5 + Sec3 glue) and the cTao pin in Statement.lean.
    #   cTao := 1/(640000000 * ln 2)
    # Every tree value is either a rational q, or r/ln2 for rational r.  Represent as
    # (r, kind) with kind in {"rat", "overlog"} and compare decisively under BOTH endpoints
    # of the d9 bracket ln 2 in (0.6931471803, 0.6931471808) (Real.log_two_gt_d9/lt_d9,
    # the same facts the Lean proof of c_ladder_lower uses).
    Llo, Lhi = Fraction(6931471803, 10**10), Fraction(6931471808, 10**10)

    def le(a, b):
        """Decisive a <= b under both ln2 endpoints; raises if the bracket can't decide."""
        (ra, ka), (rb, kb) = a, b
        if ka == kb:
            return ra <= rb
        if ka == "overlog":                    # ra/L <= rb  <=>  ra <= rb*L
            lo, hi = ra <= rb * Llo, ra <= rb * Lhi
        else:                                  # ra <= rb/L  <=>  ra*L <= rb
            lo, hi = ra * Lhi <= rb, ra * Llo <= rb
        assert lo == hi, ("ln2 bracket indecisive", a, b)
        return lo

    def vmin(a, b):
        return a if le(a, b) else b

    rat = lambda q: (Fraction(q), "rat")
    overlog = lambda r: (Fraction(r), "overlog")

    def linearDecay(d):                        # ValuationDist.lean:921
        return min(d * d / 2, d)
    def finalDecay(d, wrong=False):            # ValuationDist.lean:965 (min with ln 2)
        ld = min(d / 2, d) if wrong else linearDecay(d)   # `wrong` forgets the square — trap
        assert ld <= Llo                       # so the min with ln2 is the rational branch
        return ld

    def ladder(wrong=False):
        c_geomTail = Fraction(1, 400)                                     # LocalInstances:540
        c_valuationDist1 = overlog(finalDecay(c_geomTail * 1, wrong))     # ValuationDist:999
        cg = overlog(finalDecay(c_geomTail * Fraction(1, 10), wrong))     # FirstPassage:1210
        c_valSumGeom = vmin(c_valuationDist1, cg)
        c_valSumTail = (c_valSumGeom[0] / 20, c_valSumGeom[1])            # FirstPassage:1323
        # c8 chain (ApproxFormula.lean)
        c_goodTupleDev, c_edgeMass, c_earlyReturn, c_truncation = rat(1), rat(Fraction(1, 5)), rat(1), rat(1)
        c_passtimeInner = vmin(c_goodTupleDev, c_edgeMass)                # :1673
        c_passtimeWindow = vmin(c_valSumTail, c_passtimeInner)            # :1792
        c_windowReduce = vmin(c_goodTupleDev, c_passtimeWindow)           # :1895
        c_steppedMid = vmin(c_goodTupleDev, c_earlyReturn)                # :3073
        c_affineReindex = vmin(c_steppedMid, c_truncation)                # :3362
        c_fpApprox = vmin(c_windowReduce, c_affineReindex)                # :3425
        # cs chain (Stabilization.lean)
        c_perNHarm, c_harmZfine, c_mainZbridge = rat(Fraction(3, 10)), rat(Fraction(3, 10)), rat(1)
        c_harmonicZ = vmin(c_harmZfine, c_mainZbridge)                    # :2185
        c_perNTermEval = vmin(c_perNHarm, c_harmonicZ)                    # :2554
        c_IyRatio = rat(Fraction(2, 10))
        c_approxToZ = vmin(c_IyRatio, c_perNTermEval)                     # :2712
        c_stab = vmin(vmin(c_valSumTail, c_fpApprox), c_approxToZ)        # :2880
        return vmin(c_valSumTail, c_stab)                                 # Reduction:324

    cTao = overlog(Fraction(1, 640_000_000))
    lad = ladder()
    # (a) the tree collapses EXACTLY onto the pinned value (binding branch c_valSumTail):
    assert lad == cTao, lad
    # (b) c_ladder_lower's content: cTao <= every leaf, decisively under the bracket:
    for leaf in [overlog(Fraction(1, 320_000)), overlog(Fraction(1, 32_000_000)),
                 rat(1), rat(Fraction(1, 5)), rat(Fraction(2, 10)), rat(Fraction(3, 10))]:
        assert le(cTao, leaf), leaf
    # (c) trap: the plausible-wrong linearDecay (min(d/2, d), square forgotten — the same
    # born-wrong family as the C8 Aff floor) yields a DIFFERENT ladder, so the pin's value
    # is sensitive to the definition bodies it rests on:
    assert ladder(wrong=True) != cTao
    assert ladder(wrong=True) == overlog(Fraction(1, 160_000))
    # (d) float sanity of the headline number (NB: the lap-1 ledger's "≈2.2547e-9" was a
    # float slip; the true value is 2.25421e-9 — caught by this very check):
    assert abs(float(cTao[0]) / log(2) - 2.25421e-9) < 5e-14
    print("16. cTao min-tree: collapses to 1/(640000000·ln2); lower-bounds all leaves OK")


def check17():
    # Big-C campaign (2026-07-17, DIRECTION step 1): log10-space float mirror of the
    # C-ladder, walked off the ACTUAL Lean witnesses (file:line per hop).  This is the
    # go/no-go map against the pin CTao = 10^(10^9) — and the verdict is NO-GO: the
    # traced ladder is 10^(9.39e10), EXCEEDING the pin by a factor ~94 in the exponent.
    # The check asserts the trace (so the flag is machine-checked), NOT ladder <= pin.
    from math import log10
    ln2, ln3, ln43 = log(2), log(3), log(4 / 3)

    # --- exponent tower (Sec6) ---
    # Stabilization.lean:2118 consumes fine_scale_mixing 1.7;
    # MixingRegime.lean:48 telescope calls the high regime at A+2 = 3.7;
    # MixingMain.lean:465 osc_mainHigh_bound obtains head_uniform_highFreq_of_margin at
    #   B := mainDecayExponent 3.7, with caConst A = 1000*(max A 0 + 3)  (MixingCore.lean)
    #   and mainDecayExponent A = A + (caConst A)^2 * log 2 + 3          (MixingMain.lean:142)
    A_high = 3.7
    ca = 1000 * (A_high + 3)                     # caConst 3.7 = 6700
    B = A_high + ca ** 2 * ln2 + 3               # ≈ 3.1115e7
    assert abs(B - 3.11154e7) < 1e2, B
    # head chain is pure passthrough at the SAME exponent B:
    #   head_uniform_highFreq_of_margin (MixingMain.lean:240) <- head_factor_norm_le_charFn
    #   (MixingCore.lean:1076) <- charFn_decay (Sec7/Decay.lean:18) <- key_fourier_decay
    #   (Sec7/Reduction.lean:930) <- renewal_white_encounters (Sec7/Bridge.lean:507)
    #   <- hold_weight_expect (Sec7/Monotone.lean:246), each literally obtain⟨C⟩;refine⟨C,…⟩.

    # --- hold_weight_expect's explicit witness Cthr = K + M1 + 2T + 4 (Monotone.lean:246) ---
    # epsBW = 1/10^1000 (Sec7/Setup.lean:97); delta := exp(epsBW^3/2) - 1 ≈ 0.5e-3000.
    log10_delta = log10(0.5) - 3000
    # K: geom_three_quarters_lt (Monotone.lean:180) at b = delta/3 * 2^-B gives
    #   K = ceil( ln((b/2)^-1) / ln(4/3) ) = ceil( (ln(6/delta) + B ln2) / ln(4/3) )
    K = ((log(6) - log10_delta * log(10)) + B * ln2) / ln43
    assert abs(K - 7.50e7) < 1e6, K
    # M1 = ceil(K*c/(c-1)) (Monotone.lean:283) with c = (1+delta/3)^(1/B), so
    #   c/(c-1) ≈ 3B/delta — THE 1/delta ≈ 2e3000 FACTOR THE PIN'S SIZING MISSED.
    log10_M1 = log10(K) + log10(3 * B) - log10_delta
    assert abs(log10_M1 - 3016.15) < 0.05, log10_M1
    # T: pow_mul_geom_lt_of_large (Monotone.lean:196) at k=ceil(B), b = delta/3*3^-B:
    #   T = 1 + ceil((4(B+1)/ln(4/3))^2) + ceil(ln((b/2)^-1)/(ln(4/3)/2)) ≈ 1.87e17 — tiny vs M1.
    T = (4 * (B + 1) / ln43) ** 2 + ((log(6) - log10_delta * log(10)) + B * ln3) / (ln43 / 2)
    assert T < 2e17
    # Cthr ≈ M1; n0 := 2*Cthr + 2 (Bridge.lean:517)
    log10_n0 = log10(2) + log10_M1
    # renewal_white_encounters witness: max(n0^B, C0*exp(eps^3/2)*3^B) >= n0^B (Bridge.lean:518)
    log10_head = log10_n0 * B
    assert abs(log10_head - 9.3859e10) < 1e7, log10_head
    # osc_mainHigh_bound witness 3*C_head*40^B (MixingMain.lean:469); high regime doubles it
    # (MixingFromDecay.lean:16); telescope adds 2N^A + C_high*zeta(2) (MixingRegime.lean:55);
    # Sec5/Sec3 glue multiplies by ~4e14*2*16 (notes/effective-constants.md) — all additive
    # noise in log10 next to log10_head:
    log10_ladder = log10(3) + log10_head + B * log10(40) + log10(2) + log10(1.645) + 15.2
    assert abs(log10_ladder - 9.3908e10) < 1e7, log10_ladder
    # (a) THE FINDING: the traced ladder EXCEEDS the pin CTao = 10^(10^9) ~94-fold in exponent:
    PIN_EXP = 1e9
    assert log10_ladder > 90 * PIN_EXP, log10_ladder
    # (b) and it is NOT witness slop: any C satisfying renewal_white_encounters' frozen
    # statement at A=B obeys C >= sup_n exp(-eps^3*n/2)*n^B  (since #white <= n/2, the
    # damping expectation is >= exp(-eps^3 n/2)); at n = 2B/eps^3 that floor is 10^(9.36e10):
    log10_floor = B * (log10(2 * B) + 3000 - log10(2.718281828459045))
    assert log10_floor > 90 * PIN_EXP, log10_floor
    assert log10_floor < log10_ladder
    # (c) trap/diagnosis: under the sizing assumption that C1 is T-dominated (M1's 1/delta
    # term missed), the ladder DOES fit under the pin — pinpointing the single responsible
    # term (M1 = ceil(K*c/(c-1)), Monotone.lean:283):
    log10_ladder_noM1 = log10(2 * T) * B + B * log10(40)
    assert log10_ladder_noM1 < PIN_EXP, log10_ladder_noM1
    print("17. big-C ladder: log10 C_ladder ≈ %.4e  >  pin exponent 1e9 (×%.0f) — "
          "JUDGE-FLAGGED (forced floor %.4e; M1's 1/δ≈2e3000 is the term)"
          % (log10_ladder, log10_ladder / PIN_EXP, log10_floor))


if __name__ == "__main__":
    check1(); check2(); check3(); check4(); check5(); check6()
    check7()
    check8(); check8(n=26, xi=101, eps=Fraction(1, 101))
    check8(n=30, xi=1, eps=Fraction(1, 10 ** 4))  # the D4 value itself
    check9(); check10(); check11()
    check12()                                     # statement-faithful damping
    check12(damp=1.0 / 2.718281828459045)         # amplified: O(1)-sensitive seam
    check12(n=16, xi=7, damp=0.5)                 # second geometry
    check13()                                     # C8 (5.8) exact-reindex trap
    check14(); check15()                          # C6 §3 pins (Thm 3.1 forms, (1.2) pullback)
    check16()                                     # cTao explicit-exponent min-tree
    check17()                                     # big-C ladder map (JUDGE-FLAGGED: > pin)
    print("ALL CHECKS PASS ✅")
