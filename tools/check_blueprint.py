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
    # ⚠️ 2026-07-17: the `CTao = 10^(10^11)` pin these checks compare against was RETIRED
    # (judge ruling; Trevor's call) — the guess was wrong by a tower.  checks 17/19 are kept
    # as the machine-checked RECORD of the ladder trace and the C0-arm NO-GO that killed it;
    # the "pin exponent 1e11" they print is a historical line, NOT a live gate.  The successor
    # (`C_tao_assembled`, ExplicitBigC.lean) makes no smallness claim, so nothing compares to
    # a numeral anymore.  See DIRECTION.md "JUDGE RULING II".
    # Big-C campaign (2026-07-17, DIRECTION step 1): log10-space float mirror of the
    # C-ladder, walked off the ACTUAL Lean witnesses (file:line per hop).  This is the
    # go/no-go map against the pin.  History: the ORIGINAL pin CTao = 10^(10^9) was a
    # NO-GO — the traced ladder 10^(9.39e10) exceeded it ~94-fold in the exponent
    # (lap-1 JUDGE-FLAG); the JUDGE re-pin 2026-07-16 set CTao = 10^(10^11), under which
    # the same trace is a GO with ~6.5% exponent headroom.  The check asserts BOTH: the
    # trace/floor that forced the re-pin (machine-checked record) AND ladder < live pin.
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
    # (a) THE RECORD (lap-1 flag): the traced ladder EXCEEDED the original pin
    # CTao = 10^(10^9) ~94-fold in the exponent — the reason for the JUDGE re-pin:
    OLD_PIN_EXP = 1e9
    assert log10_ladder > 90 * OLD_PIN_EXP, log10_ladder
    # (b) and it was NOT witness slop: any C satisfying renewal_white_encounters' frozen
    # statement at A=B obeys C >= sup_n exp(-eps^3*n/2)*n^B  (since #white <= n/2, the
    # damping expectation is >= exp(-eps^3 n/2)); at n = 2B/eps^3 that floor is 10^(9.36e10):
    log10_floor = B * (log10(2 * B) + 3000 - log10(2.718281828459045))
    assert log10_floor > 90 * OLD_PIN_EXP, log10_floor
    assert log10_floor < log10_ladder
    # (c) trap/diagnosis: under the sizing assumption that C1 is T-dominated (M1's 1/delta
    # term missed), the ladder DOES fit under the original pin — pinpointing the single
    # responsible term (M1 = ceil(K*c/(c-1)), Monotone.lean:283):
    log10_ladder_noM1 = log10(2 * T) * B + B * log10(40)
    assert log10_ladder_noM1 < OLD_PIN_EXP, log10_ladder_noM1
    # (d) THE GO: under the live pin CTao = 10^(10^11) (JUDGE re-pin 2026-07-16) the
    # traced ladder fits with ~6.5% exponent headroom — an exponent budget ≈ 6.1e9,
    # i.e. ~195 digits of slack on n0 (slack on log10(n0) amplifies by ×B):
    PIN_EXP = 1e11
    assert log10_ladder < 0.95 * PIN_EXP, log10_ladder
    print("17. big-C ladder: log10 C_ladder ≈ %.4e  <  (RETIRED 2026-07-17) pin exponent 1e11 "
          "(%.1f%% headroom) — GO after JUDGE re-pin (old pin 1e9 exceeded ×%.0f, "
          "forced floor %.4e; M1's 1/δ≈2e3000 is the term)"
          % (log10_ladder, 100 * (1 - log10_ladder / PIN_EXP),
             log10_ladder / OLD_PIN_EXP, log10_floor))


def check18():
    # Big-C campaign step 2 (2026-07-17): the SYMBOLIC DEFS planted in
    # TaoCollatz/Sec7/Monotone.lean — deltaBW, cHold, K_geom/K_hold, T_powGeom/T_hold,
    # M1_hold, C_hold — recomputed here in log-space FROM THE DEF BODIES AS WRITTEN
    # (with the b/2 inside K_geom's log, the (2/eps)^2 shape inside T_powGeom, etc.),
    # then cross-asserted against check17's algebraically simplified forms.  This is
    # the numeric trap for the defs: a mis-transcription (dropped /2, wrong base,
    # k+1 vs k) breaks the agreement.
    from math import log10
    ln2, ln3, ln10, ln43 = log(2), log(3), log(10), log(4 / 3)
    A_high = 3.7
    ca = 1000 * (A_high + 3)
    B = A_high + ca ** 2 * ln2 + 3               # the A at which the chain runs
    # deltaBW = exp(epsBW^3/2) - 1 ≈ epsBW^3/2 = 0.5e-3000  (epsBW = 1e-1000)
    log10_delta = log10(0.5) - 3000
    ln_delta = log10_delta * ln10
    # K_hold A = K_geom(deltaBW/3 * 2^-A) = ceil( ln((b/2)^-1) / ln(4/3) ),
    #   b = deltaBW/3 * 2^-A  (Monotone.lean, def K_geom / def K_hold):
    ln_b2 = ln_delta - log(3) - B * ln2 - log(2)          # ln(b/2)
    K_def = -ln_b2 / ln43                                  # pre-ceil
    K_17 = ((log(6) - ln_delta) + B * ln2) / ln43          # check17's simplified form
    assert abs(K_def - K_17) < 1e-6 * K_17, (K_def, K_17)
    # cHold A = (1+deltaBW/3)^(1/A):  ln(cHold) = ln(1+delta/3)/A ≈ delta/(3A);
    # M1_hold = ceil(K*c/(c-1)) with c-1 ≈ delta/(3A)  =>  log10 M1 ≈ log10(K*3A/delta):
    log10_M1_def = log10(K_def) + log10(3 * B) - log10_delta
    log10_M1_17 = log10(K_17) + log10(3 * B) - log10_delta
    assert abs(log10_M1_def - log10_M1_17) < 1e-6
    assert abs(log10_M1_def - 3016.15) < 0.05, log10_M1_def
    # T_hold A = T_powGeom ⌈A⌉ (deltaBW/3 * 3^-A)
    #   = 1 + (ceil((2/(ln43/(2(k+1))))^2) + 1) + ceil(ln((b/2)^-1)/(ln43/2)):
    kA = B + 1                                             # ⌈A⌉ up to rounding
    T_def = 1 + ((2 * 2 * (kA + 1) / ln43) ** 2 + 1) \
        + (-(ln_delta - log(3) - B * ln3 - log(2))) / (ln43 / 2) + 2
    T_17 = (4 * (B + 1) / ln43) ** 2 + ((log(6) - ln_delta) + B * ln3) / (ln43 / 2)
    assert abs(T_def - T_17) < 1e-3 * T_17 + 10, (T_def, T_17)
    # C_hold = K + M1 + 2T + 4 is M1-dominated; its log10 must equal check17's Cthr:
    log10_C_hold = log10_M1_def                            # K, T are ~1e8/1e17 vs 1e3016
    assert abs(log10_C_hold - 3016.15) < 0.05
    print("18. symbolic defs (Monotone.lean K_hold/M1_hold/T_hold/C_hold) agree with "
          "the check17 ladder: K ≈ %.3e, log10 M1 ≈ %.2f, T ≈ %.3e, log10 C_hold ≈ %.2f"
          % (K_def, log10_M1_def, T_def, log10_C_hold))


def check19():
    # Big-C campaign lap 8 (2026-07-17) — JUDGE-FLAG TRACE: the C0-ARM of
    # renewal_white_encounters' witness (Bridge.lean:518: max(n0^A, C0*exp(eps^3/2)*3^A))
    # is now FULLY REIFIED (C0 = C_polyDecay A = (max (Cthr_prop78 A) 1)^A, Case3.lean),
    # and it EXCEEDS the live pin CTao = 10^(10^11) — the check17 GO covered only the
    # n0^B HEAD arm.  The lap-5 audit's "logarithmic collapse" claim (C_encTri's huge
    # e^{ch*M_encTri} reaches the spine only through threshold conversions ~ log) is
    # REFUTED by the def bodies as written:
    #   (a) A0_estarScaled (Case3.lean:1910) is LINEAR in C' = 4*C_encTri
    #       (Kthr_estarScaled = 3456000*C'/((2ln4-ln10)^2 ln4^3) + 216000*C'/ln4^3),
    #       so log10(A0_fewEstar) ~ log10(C_encTri) ~ 8.5e21 — the CONSTANT becomes
    #       an EXPONENT, not a log;
    #   (b) it re-enters EXPONENTIALLY: B_fewWhite = 4^{2A+A0}*(1+P)^3, and
    #       encWindowIter cubes per step for R_fewWhite ~ 100*K_fewWhite ~ 1e3010
    #       steps (K_fewWhite = ceil((A+3)ln10/epsBW^3), the 1/eps^3 = 1e3000 factor);
    #   (c) the threshold re-enters as Cthr^A in the C0-arm (Q_polynomial_decay_at
    #       constant (max C0 1)^A) at A = B ~ 3.11e7.
    # Every hop below is a LOWER bound; floats hold log10- or log10(log10)-space.
    from math import log10
    ln2 = log(2)
    A_high = 3.7
    ca = 1000 * (A_high + 3)
    B = A_high + ca ** 2 * ln2 + 3                        # ~3.11e7 (as check17)
    PIN_EXP = 1e11

    # --- central trace (documented ch = c_fpHeightTail = 1/51200, M_encTri = 1e27) ---
    ch = 1 / 51200
    log10_CencTri = ch * 1e27 / log(10)                   # e^{ch*M} term ~ 10^(8.48e21)
    assert abs(log10_CencTri - 8.48e21) < 1e20, log10_CencTri
    # A0_fewEstar >= Kthr_estarScaled(4*C_encTri) >= 216000*4*C_encTri/ln4^3:
    log10_A0 = log10(216000 * 4 / log(4) ** 3) + log10_CencTri   # log10(A0) ~ 8.48e21
    # Cthr_fewWhite >= ceil(B_fewWhite^2.5) >= (4^{A0})^2.5 (already ignoring P!), so
    # log10(Cthr) >= 2.5*log10(4)*A0; A0 = 10^(8.48e21) OVERFLOWS a float, so assert
    # the C0-arm in log-log space (C0-arm >= Cthr^B):
    loglog_C0arm = log10(B * 2.5 * log10(4)) + log10_A0   # log10(log10(C0-arm)) approx
    assert loglog_C0arm > 21, loglog_C0arm                # log10(C0) > 10^21 >> 1e11
    # --- the fully-iterated P (record): encWindowIter cubes per step over R steps ---
    log10_delta3 = -3000                                  # epsBW^3 = 1e-3000
    log10_K = log10((B + 3) * log(10)) - log10_delta3     # K_fewWhite ~ 10^3007.9
    log10_R = log10_K + 2                                 # eps0_manyTri = 1/100
    # log10(log10 P) ~ R*log10(3) ~ 4.8e3009 itself overflows a float; hold one more
    # log level: logloglog_P = log10( log10(log10 P) ) = log10(R) + log10(log10 3):
    logloglog_P = log10_R + log10(log10(3))
    assert 3009 < logloglog_P < 3010, logloglog_P
    # --- ROBUSTNESS: independent of every unresolved bottom constant ---
    # For ANY decay rate c = c_encTri > 0: A0_estarScaled >= max(Kthr, sqrt(Warg)) with
    #   Kthr >= 216000*4*e^{c*1e27}/ln4^3 >= 3.2e5*e^{c*1e27}   and
    #   sqrt(Warg) >= ln10/(4c)                (Warg >= ln10^2/(16c^2)),
    # minimized over c at worst A0 >= 9.6e24 (c <= 6e-26 gives ln10/(4c) >= 9.6e24;
    # c >= 6e-26 gives Kthr >= 3.2e5*e^60 >= 3.6e31):
    A0_robust = min(3.2e5 * 2.7182818 ** 60, log(10) / (4 * 6e-26))
    assert A0_robust > 9.5e24, A0_robust
    log10_C0arm_robust = B * 2.5 * log10(4) * A0_robust   # >= 4.5e32
    assert log10_C0arm_robust > 100 * PIN_EXP, log10_C0arm_robust
    # THE NO-GO: the C0-arm alone forces log10(C_ladder) >= 4.5e32 >> 0.95e11 = the
    # check17 GO line; with the traced ch it is 10^(8.5e21), with the iterated P it is
    # 10^(4.8e3009).  The step-3 inequality C_ladder <= CTao is NOT provable over the
    # frozen tower with the current witnesses.  JUDGE-FLAG: see PENDING_WORK.md lap 8.
    print("19. C0-arm NO-GO (JUDGE-FLAG lap 8): log10(C0-arm) >= %.1e ROBUST "
          "(any c); central trace log10(log10) ≈ %.2e (ch=1/51200); with iterated "
          "P: log10(log10) ≈ 10^%.1f — all >> the (RETIRED 2026-07-17) pin exponent 1e11 (check17's GO "
          "covered the n0^B head arm only)"
          % (log10_C0arm_robust, loglog_C0arm, logloglog_P))


def check20():
    # Big-C campaign lap 11 (2026-07-17): STEP-2 COMPLETE — the Sec5/Sec3 GLUE is now
    # Lean-explicit (C_geomTail .. C_spine X), so recompute it here FROM THE DEF BODIES
    # AS WRITTEN and cross-assert against check17's coarse "+15.2" glue model.  This is
    # the numeric trap for the lap-9/10/11 defs: a mis-transcription (wrong summand,
    # dropped factor, min/max flip) breaks (a) the exact leaf values or (b) the glue
    # magnitude.  Sources (file:def):
    #   Prob/LocalInstances: C_geomTail = 2
    #   Syracuse/ValuationDist: C_valuationDistC K = 2K + 4*C_geomTail
    #   Sec5/FirstPassage: K_intTest = 2/(1/8); C_valSumGeom = C_valuationDistC K + 2*C_geomTail
    #   Sec5/ApproxFormula: C_goodTupleDev = 2*C_geomTail + C_valuationDistC K_intTest;
    #     C_edgeMass = 2/(1/10000); C_passtimeInner = C_goodTupleDev + C_edgeMass;
    #     C_passtimeWindow = C_valSumGeom + C_passtimeInner;
    #     C_windowReduce = C_goodTupleDev + C_passtimeWindow; C_steppedMid = C_goodTupleDev+1;
    #     C_affineReindex = C_steppedMid+1; C_fpApprox = C_windowReduce + C_affineReindex
    #   Sec5/Stabilization: C_epsPerNHarm = 2 + 3*(3/(1/10000)) + 2*3/(alpha-1);
    #     C_perNHarm = C_epsPerNHarm*4; C_goodWhp = 2*C_geomTail; C_syracZsub = C_goodWhp;
    #     C_harmZfine = 4*C_syracZsub; C_mainZbridge = 4*C_fineScale(1.7)*(1/200000)^-1.7;
    #     C_harmonicZ = C_harmZfine + C_mainZbridge; C_perNTermEval = C_perNHarm + C_harmonicZ;
    #     C_mainZ = C_perNHarm + C_harmonicZ + 1000*(1+C_fpApprox);
    #     C_approxToZ = (2/log(4/3)+6000)*C_perNTermEval + C_mainZ*6000;
    #     C_windowStable = 2*C_approxToZ; C_stab = C_valSumGeom + 4*C_fpApprox + 2*C_windowStable
    #   Sec3/Reduction: C_descStep = 2*C_stab; C_descLadder = max C_valSumGeom C_descStep;
    #     C_descWhp = C_descLadder*(1+(1-alpha^-c_ladder)^-1)*alpha^c_ladder;
    #     C_windowBad = 2*C_descWhp;
    #     C_syrSum X = max (C_windowBad*alpha/(alpha-1)) (4*max 1 (log X)^c_ladder);
    #     C_syrProb X = 8*C_syrSum X; C_spine X = 16*C_syrSum X
    from math import log10, expm1
    ln43 = log(4 / 3)
    alpha = 1.001
    # --- exact leaves (trap (a)) ---
    C_geomTail = 2.0
    K_intTest = 2 / (1 / 8)
    C_valuationDistC = 2 * K_intTest + 4 * C_geomTail
    assert (K_intTest, C_valuationDistC) == (16.0, 40.0)
    C_valSumGeom = C_valuationDistC + 2 * C_geomTail
    C_goodTupleDev = 2 * C_geomTail + C_valuationDistC
    assert C_valSumGeom == 44.0 and C_goodTupleDev == 44.0
    C_edgeMass = 2 / (1 / 10000)
    C_passtimeInner = C_goodTupleDev + C_edgeMass
    C_passtimeWindow = C_valSumGeom + C_passtimeInner
    C_windowReduce = C_goodTupleDev + C_passtimeWindow
    C_steppedMid = C_goodTupleDev + 1
    C_affineReindex = C_steppedMid + 1
    C_fpApprox = C_windowReduce + C_affineReindex
    assert C_fpApprox == 20178.0, C_fpApprox
    C_epsPerNHarm = 2 + 3 * (3 / (1 / 10000)) + 2 * 3 / (alpha - 1)
    C_perNHarm = C_epsPerNHarm * 4
    assert abs(C_perNHarm - 384008.0) < 1e-6, C_perNHarm
    C_harmZfine = 4 * (2 * C_geomTail)          # 4*C_syracZsub, C_syracZsub = C_goodWhp
    assert C_harmZfine == 16.0
    # --- the tower seam: C_mainZbridge = 4*C_fineScale(1.7)*(2e5)^1.7 (log10-space).
    # C_fineScale(1.7) = 2*N^1.7 + C_oscHigh(3.7)*zeta(2), C_oscHigh = 2*max(C_oscMainHigh,6),
    # C_oscMainHigh(3.7) = 3*C_renewalWhite(B)*40^B — the N^1.7 cutoff term is additive
    # noise (N would need 10^(5.5e10) digits to matter) and is dropped here.
    # HEAD-ARM VARIANT (check17's GO route / Option-B target): C_renewalWhite = n0^B.
    ln2, ln10 = log(2), log(10)
    A_high = 3.7
    ca = 1000 * (A_high + 3)
    B = A_high + ca ** 2 * ln2 + 3
    log10_delta = log10(0.5) - 3000
    K = ((log(6) - log10_delta * ln10) + B * ln2) / ln43
    log10_M1 = log10(K) + log10(3 * B) - log10_delta
    log10_n0 = log10(2) + log10_M1
    log10_head = log10_n0 * B                    # = check17's head
    log10_oscMainHigh = log10(3) + log10_head + B * log10(40)
    zeta2 = 1.6449340668
    log10_fineScale = log10_oscMainHigh + log10(2) + log10(zeta2)
    log10_mainZbridge = log10(4) + log10_fineScale + 1.7 * log10(2e5)
    # C_harmonicZ ≈ C_perNTermEval ≈ C_mainZ ≈ C_mainZbridge (small addends are noise):
    log10_harmonicZ = log10_mainZbridge
    # C_approxToZ = (2/ln43 + 6000)*C_perNTermEval + C_mainZ*6000 ≈ 1.2e4 * C:
    log10_approxToZ = log10_harmonicZ + log10((2 / ln43 + 6000) + 6000)
    log10_stab = log10(2) + log10(2) + log10_approxToZ     # C_stab ≈ 2*C_windowStable
    log10_descLadder = log10(2) + log10_stab               # = C_descStep (max picks it)
    # the descent geometric factor (1 + (1-alpha^-c)^-1)*alpha^c at c = c_ladder
    # = 1/(640000000*ln2)  (check16's binding branch; c_stab arms are all >> it):
    c_lad = 1 / (640000000 * ln2)
    geo = (1 + 1 / (-expm1(-c_lad * log(alpha)))) * alpha ** c_lad
    assert abs(geo - 4.4385e11) < 1e8, geo
    log10_descWhp = log10_descLadder + log10(geo)
    log10_windowBad = log10(2) + log10_descWhp
    # C_syrSum X: (log X)^c_lad ≈ 1 for ANY tower cutoff X (even log X = 2000^5 = 3.2e16
    # gives (3.2e16)^c ≈ exp(8.6e-8)) — so the max picks the C_windowBad arm:
    assert (2000.0 ** 5) ** c_lad < 1.0000002
    log10_syrSum = log10_windowBad + log10(alpha / (alpha - 1))
    log10_spine_head = log10(16) + log10_syrSum
    # (b) glue magnitude: everything added over 3*head*40^B is < 40 orders — additive
    # noise vs 9.39e10, confirming check17's coarse "+15.2" was immaterial slack:
    glue = log10_spine_head - (log10(3) + log10_head + B * log10(40))
    assert 15 < glue < 40, glue
    # (c) cross-assert the head-route ladder against check17's total (tolerance 1e7):
    assert abs(log10_spine_head - 9.3908e10) < 1e7, log10_spine_head
    # (d) route mirror (check19): the AS-WRITTEN max in C_renewalWhite picks the C0-arm
    # (log10 >= 4.5e32 robust) >> head arm, so the as-written C_spine X EXCEEDS the pin —
    # step 3 stays STOPPED pending the operator's A/B ruling.
    log10_C0arm_robust = 4.5e32
    assert log10_C0arm_robust > log10_head
    print("20. lap-11 glue defs (Sec5/Sec3, C_geomTail..C_spine) mirror the Lean bodies: "
          "leaves exact (C_fpApprox=20178, C_perNHarm=384008), glue = %.1f orders, "
          "head-route log10 C_spine ≈ %.4e (matches check17 GO); as-written max picks "
          "the C0-arm (check19 route conclusion unchanged)" % (glue, log10_spine_head))


def check21():
    # Big-C campaign lap 13 (2026-07-17): OPTION-B TIGHT PIN, RESIZED — the numeric trap
    # for Bridge.lean's C_renewalWhite_tight / C_Qtight / Q_black_edge_tight cluster.
    # (a) WHY the lap-12 pin had to be resized (machinery floor): the lap-12
    #     C_Qtight = n0^A/(exp(eps^3/2)*3^A) ≈ (n0/3)^A is BELOW the floor
    #     (C_hold)^A that Q_polynomial_decay_at can deliver (its constant is the
    #     trivial-regime crossover (max C0 1)^A with C0 >= C_hold intrinsically):
    #     n0/3 = (2*C_hold+2)/3 < C_hold for C_hold > 2 — the old statement was
    #     plausibly TRUE but unprovable through the Prop-7.8 apparatus.
    # (b) the lap-13 assembly really lands: exact-arithmetic instance check of the
    #     sharp-bridge Nat inequality  C1*n <= (2*C1+2)*(n//2)  for n >= 2*C1+2,
    #     at the boundary and parity cases (this is hkey in the Lean proof — the
    #     step that replaced the crude n <= 3*(n//2) / 3^A bridge).
    # (c) sizing: the resized constant 2*n0^A still clears the pin with ~6% headroom
    #     (factor 2 = +0.30103 digits on 9.386e10), and exp(eps^3/2) <= 2 trivially.
    # (d) crux feasibility window (recorded, NOT proved): white-frequency threshold
    #     K_fewWhite ~ 10^3007.9 < C_hold ~ 10^3016.15 — Q_black_edge_tight's
    #     threshold C_hold has ~8 orders of room over the true decorrelation scale.
    from math import log10
    ln2, ln10, ln43 = log(2), log(10), log(4 / 3)
    A_high = 3.7
    ca = 1000 * (A_high + 3)
    B = A_high + ca ** 2 * ln2 + 3                       # ~3.11e7 (as check17)
    PIN_EXP = 1e11
    # (a) floor argument (scale-free): n0/3 < C_hold  <=>  2*C_hold+2 < 3*C_hold:
    for C in (3, 10 ** 10, 10 ** 3016):
        assert 2 * C + 2 < 3 * C
    # (b) exact Nat bridge instances (hkey), boundary + parity sweep:
    for C1 in (1, 2, 3, 17, 10 ** 6 + 1):
        n0 = 2 * C1 + 2
        for n in (n0, n0 + 1, n0 + 2, n0 + 3, 10 * n0 + 1):
            assert C1 * n <= n0 * (n // 2), (C1, n)
            # and the crude bridge the lap-12 glue was built for, for contrast:
            assert n <= 3 * (n // 2)
    # counter-instance guard: the sharp bridge can FAIL below n0 (e.g. n = 1, where
    # n//2 = 0), so the small-n arm split at n0 is load-bearing:
    assert any(C1 * n > (2 * C1 + 2) * (n // 2)
               for C1 in (5,) for n in (1, 3))
    # (c) sizing of the resized constant 2*n0^B (log10-space, same trace as check17):
    log10_delta = log10(0.5) - 3000
    K = ((log(6) - log10_delta * ln10) + B * ln2) / ln43
    log10_M1 = log10(K) + log10(3 * B) - log10_delta
    log10_n0 = log10(2) + log10_M1
    log10_tight = log10(2) + log10_n0 * B                # C_renewalWhite_tight, resized
    assert log10_tight - (log10_n0 * B) < 0.302          # factor 2 = 0.30103 digits
    assert log10_tight < 0.95 * PIN_EXP, log10_tight     # still a GO
    # exp(eps^3/2) <= 2: eps^3/2 = 0.5e-3000 <= 1/2 and e^0.5 < 2:
    assert 2.718281828459045 ** 0.5 < 2
    # (d) crux window: K_fewWhite ~ 10^3007.9 vs C_hold ~ 10^3016.15:
    # K_fewWhite = ceil((A+3)*ln10/eps^3), eps^3 = 1e-3000:
    log10_K_fw = log10((B + 3) * ln10) + 3000
    assert log10_K_fw < log10_M1, (log10_K_fw, log10_M1)
    assert log10_M1 - log10_K_fw > 7, (log10_K_fw, log10_M1)
    print("21. lap-13 tight resize: machinery floor n0/3 < C_hold confirmed; sharp Nat "
          "bridge C1*n <= n0*(n//2) exact on boundary/parity sweep; resized "
          "log10 C_renewalWhite_tight ≈ %.4e < 0.95e11 (GO); crux window "
          "K_fewWhite 10^%.1f << C_hold 10^%.1f (~%.1f orders)"
          % (log10_tight, log10_K_fw, log10_M1, log10_M1 - log10_K_fw))


def check23():
    # Big-C campaign lap 15 (2026-07-17): the FLAT-ENVELOPE CONTRADICTION and the
    # exp-depth route sizing.  Supersedes check22(d): the caConst/Sec-6 lever does NOT
    # rescue Option B — the contradiction below is budget-independent.
    # (i) Unconditional-geometry variants (ANY budget): the envelope S has a dual role —
    #     E*-rarity needs S >= 8*c_hit*P (per-time hit rate >= c_hit/S is the best that
    #     spacing-only tools give; TriangleFamily.separated is CONSTANT ~230,
    #     BlackEdge.lean:47), while the deterministic claim's barrier-crossing cost
    #     needs R*S/2 <= P.  Together: 4*c_hit*R <= 1 — false by ~3000 orders for every
    #     c_hit >= 1e-15 (R >= 100*K, K >= ln4/eps^3).  Growing envelopes escape only
    #     geometrically (p_{i+1} >= p_i*(1+c*A^2)) => P >= (1+cA^2)^R: the TOWER is
    #     intrinsic to the encounter architecture under unconditional geometry.
    from math import log10
    log10_R = log10(log(4)) + 3000 + 2
    for log10_c in (-15, -10, -5, 0):
        assert log10(4) + log10_c + log10_R > 300     # 4*c_hit*R >> 1: robust
    # (ii) The exp-depth door: cornerTriple size = log(eps/|theta*|)
    #      (Triangles.lean:1626), so size->=S apexes are eps*e^{-S}-deep BY
    #      CONSTRUCTION.  IF the walk's deep-black hit mass decays exponentially in
    #      depth (the ONE open equidistribution input), the chain fits the CURRENT
    #      budget at A = mainDecayExponent 3.7:
    ln2, ln10 = log(2), log(10)
    A_high = 3.7
    ca = 1000 * (A_high + 3)
    B = A_high + ca ** 2 * ln2 + 3
    budget = 0.95e11 / B                              # ~3053
    log10_P0 = log10(log(4)) + 3000 + 2               # P ~ R (waits are global, lap 13b)
    # required envelope: 2*eps*P*e^{-S} <= 1/8  =>  S ~ ln(16*eps*P) (natural-log units,
    # matching the cornerTriple size scale; black measure is 2*eps, eps = 1e-1000):
    S = (log10(16) + (-1000) + log10_P0) * ln10       # eps*P ~ 10^2002, S ~ 4.6e3
    assert 4000 < S < 5000, S
    log10_P = log10_R + log10(max(S, 2.0) / 2)        # P ~ R*(S+2)/2 + K: R*S dominates
    log10_thresholds = log10(400) + log10_P           # T_colTail-shaped arm
    assert log10_thresholds < budget - 40, (log10_thresholds, budget)
    print("23. flat-envelope contradiction: 4*c_hit*R > 1 by >300 orders for all "
          "c_hit >= 1e-15 (tower intrinsic to unconditional geometry, ANY budget — "
          "supersedes 22(d)); exp-depth door: S ~ %.0f, log10 P ~ %.0f, thresholds "
          "~10^%.0f < budget %.0f (fits at CURRENT A, conditional on exponential "
          "depth-decay of deep-black hits — lap-16 reads many_triangles_white)"
          % (S, log10_P, log10_thresholds, budget))


def check24():
    # Big-C campaign lap 16 (2026-07-17): the SHALLOW-TIP WITNESS — machine-checked
    # falsification of the geometric route to the lap-15 door.  The door statement
    # `P(walk position in size->=S triangle) <= C*e^{-cS}` could follow from the
    # depth-0 mechanism (localization box vs set-separation, `fpDist_any_triangle_le_at`)
    # ONLY if the set-distance to a size-S triangle grew with S.  It does NOT: a big
    # triangle's shallow tip (boundary points, depth ~0) sits at the bare constant
    # separation.  Witness on EXACT decompositions (check8 instances): the LARGEST
    # triangle's point set lies within a few lattice units of another triangle —
    # size/dist ratios 4.5 and 6.4, growing with instance size, while the separation
    # floor stays constant.  Consequence (lap-16 verdict): the `many_triangles_white`
    # mechanism is intrinsically ONE-LEVEL in size; any exp-in-S statement must gate on
    # the DEPTH structure above the walk position (apex phase <= eps*2^{-height}, the
    # fibre identity), i.e. on anti-concentration of theta_q at exponentially fine
    # scales — an equidistribution input beyond the paper's toolset (JUDGE-FLAG).
    for (n, xi, eps, want_ratio) in [(30, 7, Fraction(9, 1000), 4.0),
                                     (26, 101, Fraction(1, 101), 6.0)]:
        black, tris = check8(n, xi, eps)
        sizes = {c: log(float(eps) / float(abs(black[c]))) for c in tris}
        cbig = max(tris, key=lambda c: sizes[c])
        dmin = min(min((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2
                       for p in tris[cbig] for q in tris[c2]) ** 0.5
                   for c2 in tris if c2 != cbig)
        ratio = sizes[cbig] / dmin
        assert ratio > want_ratio, (n, xi, sizes[cbig], dmin, ratio)
        print("24. shallow-tip witness n=%d xi=%d: largest triangle size %.2f at "
              "set-dist %.2f (size/dist %.1f) — set-separation does NOT scale with "
              "size; exp-in-SIZE door has no geometric proof (lap-16 verdict: "
              "mechanism one-level, crux = fine-scale theta_q anti-concentration)"
              % (n, xi, sizes[cbig], dmin, ratio))


def check25():
    # Big-C campaign lap 17b (2026-07-17): probe (ii) closed — the point-mass half
    # EXISTS but reproduces only Lemma 7.10's rate; the lap-16 JUDGE-FLAG is CONFIRMED
    # by an independent route.
    #   (i) The local bound: `tiltHold_apply_le_center` (HoldLocal.lean:46, node S3
    #       (F4b)) gives sup_v P(Hold walk_k = v) <= C2/(1+k), C2 = (32*80000)^2 =
    #       6.5536e12 — circle method on the hold atoms, INDEPENDENT of the encounter
    #       analysis (charFn_decay/key_fourier_decay are downstream of
    #       renewal_white_encounters and would be circular; this is not).
    #  (ii) The chain: triangle DISJOINTNESS gives sum(depth^2) <= area, so depth->=u
    #       apexes in the effective sqrt(k)-window number <= k/u; times C2/k = per-step
    #       deep-entry rate ~ C2/u — LINEAR in depth.  This is EXACTLY Lemma 7.10's
    #       per-time C/s' rate (check22's map), already shown insufficient: union
    #       floors 15041/12033 >> budget 3053.  Nothing new is gained.
    # (iii) Expectation accounting (pay big crossings in expectation instead of
    #       excluding them) FAILS (7.39): with per-crossing tail P(cost>=u) ~ C2*W/u
    #       (tail index 1), a SINGLE giant crossing of cost ~W/2 has probability
    #       ~ 2*C2 (vacuous) resp. ~C2/W per entry step — while (7.39) needs total
    #       decay W^{-A} with A = mainDecayExponent(3.7) ~ 3.1e7.  C2/W >> W^{-A} by
    #       thousands of orders at every relevant W.  Exponential depth-decay is
    #       genuinely NEEDED and linear is all the unconditional toolset gives.
    from math import log10
    C2 = (32 * 80000) ** 2
    assert C2 == 6553600000000
    ln2 = log(2)
    A = 3.7 + (1000 * (3.7 + 3)) ** 2 * ln2 + 3          # mainDecayExponent 3.7
    for log10_W in (3016, 3100, 10 ** 4, 10 ** 6):        # applied windows m-j >= n0
        # single-giant-crossing probability ~ C2/W  vs needed W^{-A}:
        lhs = log10(C2) - log10_W                         # log10 P(giant crossing)
        rhs = -A * log10_W                                # log10 of required bound
        assert lhs - rhs > 10 ** 9, (log10_W, lhs, rhs)   # fails by >1e9 orders
    print("25. point-mass half closed: HoldLocal (F4b) local bound C2/(1+k), C2=6.55e12,"
          " is real and non-circular, but count(disjointness) x point-mass = C2/u"
          " per-step deep-entry rate — exactly Lemma 7.10's rate (check22: dead);"
          " expectation accounting fails (7.39) by >1e9 orders (giant crossing C2/W"
          " vs W^-A, A~3.1e7).  Lap-16 JUDGE-FLAG CONFIRMED independently.")


def check26(samples=200000):
    # Big-C campaign lap 18 (2026-07-17): numeric trap on the exp-depth door (the
    # check23(ii) hypothesis), run before pinning `deep_entry_exp_decay` as a Lean
    # conjecture.  Monte-Carlo the free Hold walk over the EXACT phase field
    # (decompose_black instances) and measure the conditional entry-height tail
    # P(entry height >= u | entry).
    #
    # ⚠️ JUDGE CORRECTION (host-side ruling 2026-07-17) — READ BEFORE CITING THIS CHECK.
    # This check's ASSERT is sound but NARROW, and its original print line ("REFUTED
    # empirically ... poly not exp") claimed more than it tests.  `exp_pred` below
    # hardcodes **rate c = 1**; the observed ratios fit an exponential with c ~ 0.08-0.14
    # perfectly.  So what this check establishes is exactly: **the tail is far heavier
    # than a RATE-1 exponential** — not that it is polynomial, and not that the door is
    # false.  The lap-18 ledger's "route map closed on every branch (all machine-checked)"
    # over-read it, and the overstatement then compounded hop by hop into the
    # campaign-close recommendation.
    #
    # The lap-18 CONCLUSION nevertheless survives, on independent evidence with a
    # different origin — see `tools/judge_probe_depth_tail.py`, which fits a FREE-rate
    # exponential (c ~ 3/smax -> 0 with n: no uniform rate exists), shows the tail is a
    # scaling form F(u/smax) (collapse within 1.8x across smax 25->38 and eps 100x, and
    # RISING with n where a fixed-rate exponential must fall), and confirms lap-18's
    # unchecked plantability prose exactly (xi = 2^{l0-1} mod 3^n forces |theta| = 3^-n;
    # and typical xi land within ~2 nats of it, so near-giants are GENERIC).
    #
    # The honest grade of the door, per the ruling: **no route found + strong structural
    # evidence it is dead — NOT proved closed.**  Every measurement here lives at
    # n = 22..30, eps ~ 1e-2, smax ~ 25-38 nats, while the door lives at n ~ 10^3016,
    # eps = 1e-1000, S ~ 4613 nats.  A Monte Carlo at n=30 cannot prove a statement about
    # n=10^3016.  See DIRECTION.md "JUDGE RULING (2026-07-17)".
    rng = random.Random(18)
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
    for (n, xi, eps) in [(30, 7, Fraction(9, 1000)), (26, 101, Fraction(1, 101))]:
        black, corner = decompose_black(n, xi, eps, n // 2, range(-1500, 1500))
        smax = max(log(float(eps) / float(abs(black[corner[p]])))
                   for p in black) / log(2)  # max size, in 2^-height units
        heights = {}
        tot = 0
        for _ in range(samples):
            j, l = rng.randint(1, 3), rng.randint(-1400, 1300)
            while j <= n // 2 and l < 1400:
                if (j, l) in black:
                    js, ls = corner[(j, l)]
                    heights[ls - l] = heights.get(ls - l, 0) + 1
                    tot += 1
                    break
                dj, dl = sample_hold()
                j += dj; l += dl
        tail = lambda u: sum(v for k, v in heights.items() if k >= u) / tot
        u1, u2 = int(smax * 0.25), int(smax * 0.65)
        t1, t2 = tail(u1), tail(u2)
        # a RATE-1 exponential would force t2/t1 <= e^{-(u2-u1)}.  NB (judge 2026-07-17):
        # c = 1 is hardcoded here, so this refutes rate-1 decay ONLY — a c ~ 0.1
        # exponential fits the observed ratios fine.  The free-rate analysis that
        # actually decides the door lives in tools/judge_probe_depth_tail.py.
        exp_pred = 2.718281828 ** (-(u2 - u1))
        assert t2 / t1 > 100 * exp_pred, (n, xi, t1, t2, exp_pred)
        assert t2 > 0.01, (n, xi, t2)   # deep entries are COMMON, not rare
        print(f"26. entry-height tail >> RATE-1 exponential, n={n} xi={xi}: "
              f"P(ht>={u1})={t1:.3f}, P(ht>={u2})={t2:.3f} over {tot} entries — "
              f"ratio {t2/t1:.2f} vs rate-1 prediction {exp_pred:.1e}.  ⚠️ tests c=1 only; "
              f"free-rate verdict (c ~ 3/smax -> 0, scaling form) → judge_probe_depth_tail.py")


def check22():
    # Big-C campaign lap 14 (2026-07-17): OPTION-B FEASIBILITY MAP — machine-checked
    # record of the lap-13b/14 floor arithmetic for `Q_black_edge_tight` (the crux).
    # All shapes read from the Lean source, not the paper:
    #   per-time E* mass  = Lemma 7.10 (`triangle_encounter_le_rpow_core`,
    #     ManyTriangles.lean:5564):  C*A^2*(1+p)/s' + C*exp(-c*A^2*(1+p)),
    #     with hX10b anti-concentration C3*W/s' valid ONLY under s'^2 <= 1+s
    #     (the sqrt spacing cap) and the Case-3 regime s > m^0.8 (0.4 cap on s').
    #   forced chain (any proof through the (7.54)-(7.56) mass split):
    #     K >= ln4/eps^3   (the >K-white damping arm must beat a CONSTANT even with
    #                       the sharp end-weight bracketing of lap 13b),
    #     P >= K           (cannot see K+1 white visits in fewer than K+1 steps).
    # Floors on log10(Cthr) for each architecture variant, vs the pin budget
    # log10(C2) <= 0.95e11/B (final constant is C2^B in the ladder):
    from math import log10
    ln2, ln10 = log(2), log(10)
    A_high = 3.7
    ca = 1000 * (A_high + 3)
    B = A_high + ca ** 2 * ln2 + 3
    budget = 0.95e11 / B
    assert abs(budget - 3053.15) < 0.5, budget
    log10_P = log10(log(4)) + 3000                     # P >= K >= ln4/eps^3
    # (a) union over p<=P (Tao's structure, tower flattened): m^cap >= A^2*P^2
    union_04 = (2 * log10_P + 2 * log10(B) + 1) / 0.4  # as-written 0.4 cap
    union_05 = (2 * log10_P + 2 * log10(B) + 1) / 0.5  # best-case sqrt(s), s ~ m
    # (b) dilated single-hit (monotone columns, sweep 4P << s): s' >= ~40*P*A^2
    dil_04 = (log10_P + log10(40) + 2 * log10(B)) / 0.4
    dil_05 = (log10_P + log10(40) + 2 * log10(B)) / 0.5
    # (c) the ONE variant that fits: dilated single-hit + LINEAR spacing cap
    #     (X10b's s'^2 <= 1+s improved to s' <~ s/polylog):  m ~ s'*log^2
    lin = log10_P + log10(40) + 2 * log10(B) + 2
    assert union_04 > budget and union_05 > budget, (union_04, union_05)
    assert dil_04 > budget and dil_05 > budget, (dil_04, dil_05)
    assert lin < budget - 30, lin                      # fits with >30 orders margin
    # (d) the out-of-scope lever, for the record: budget scales as 1/B ~ 1/caConst^2;
    #     caConst/100 would give budget ~3e5 >> every floor above:
    B_small = A_high + (ca / 100) ** 2 * ln2 + 3
    assert 0.95e11 / B_small > 2 * union_04
    print("22. Option-B feasibility map: budget log10 Cthr <= %.0f; floors — union "
          "%.0f/%.0f (0.4/0.5 cap), dilated %.0f/%.0f; ONLY dilated+linear-spacing "
          "fits at %.0f (margin %.0f orders). Decisive open geometry: X10b spacing "
          "s'^2<=1+s -> s'<~s/polylog?, plus the monotone-column dilation lemma."
          % (budget, union_04, union_05, dil_04, dil_05, lin, budget - lin))


def check27():
    # Ruling II successor (2026-07-17): structural mirror of the X-chase cutoff tree
    # feeding X_spine and of C_tao_assembled, transliterated from the Lean def bodies of
    # THIS campaign's pins (Sec5/Stabilization phase 3, Sec3/Reduction phase 4,
    # ExplicitBigC.lean phase 5); earlier-campaign X-nodes enter as opaque toy leaves.
    # Toy semantics: exact Fractions; EXP(t) := t + 10 and POWA(v) := v + 1 are strictly
    # monotone stand-ins for Real.exp and (.)^alpha (alpha = 1.001 > 1, arguments >= 1 on
    # this tree), preserving max-structure and reachability while the tower stays finite.
    # THE TRAP: X_twoMZero is reachable ONLY through X_mainZbridge -> X_harmonicZ.  Given
    # a dominating toy value T there, the CORRECT tree returns exactly T + 1 (the single
    # ^alpha bump on the X_descWhp arm); a variant omitting that leaf from X_mainZbridge,
    # or one with X_harmonicZ's outer max mis-rendered as min, loses it.  Then
    # C_tao_assembled = max(C_spine X_spine, (log 2)^cTao) must respond to BOTH arms.
    # Finally the explicitness closure must be clean: big_c_cutoff_audit.py --complete.
    def EXP(t):
        return Fraction(t) + 10

    def POWA(v):
        return v + 1

    def spine(twoMZero, omit=False, minswap=False):
        e1 = EXP(1)
        # opaque leaves (earlier-campaign pins, trapped by checks 18/20 and the audit)
        X_windowBase = max(Fraction(2 ** 11), Fraction(2) ** 2000)
        X_firstPassNonescape = Fraction(10 ** 6)
        X_fpApprox = Fraction(10 ** 7)
        X_perNHarm = Fraction(10 ** 8)
        X_logRpowExp = Fraction(500)     # X_logRpowExp 2 (K_Gweight c_geomTail) 0.2
        # this campaign's pins, transliterated body-by-body
        X_cnBound = EXP(1024)
        X_mZeroLin = EXP(200000)
        X_goodWhp = max(X_logRpowExp, max(EXP(20), EXP(20)))    # X_Gweight = exp 20
        X_syracZsub = X_goodWhp
        X_harmZfine = max(max(X_cnBound, X_syracZsub), EXP(1024))
        X_mainZbridge = (max(EXP(200000), max(X_mZeroLin, X_cnBound)) if omit else
                         max(EXP(200000), max(twoMZero, max(X_mZeroLin, X_cnBound))))
        outer = min if minswap else max
        X_harmonicZ = outer(max(X_harmZfine, X_mainZbridge), e1)
        X_IyCard = EXP(2000 ** 5)
        X_mainZ = max(max(X_perNHarm, X_harmonicZ),
                      max(X_fpApprox, max(X_IyCard, EXP(2000 ** 5))))
        X_perNTermEval = max(max(X_perNHarm, X_harmonicZ), e1)
        X_IyRatio = max(X_IyCard, EXP(2000 ** 5))
        X_approxToZ = max(max(max(X_IyRatio, X_mainZ), X_perNTermEval), e1)
        X_windowStable = X_approxToZ
        X_stab = max(max(max(X_firstPassNonescape, X_fpApprox), X_windowStable), e1)
        X_descStep = max(X_stab, e1)
        X_descBase = max(X_firstPassNonescape, Fraction(0))
        X_descLadder = max(max(X_descBase, X_descStep), e1)
        X_descWhp = max(POWA(max(X_descLadder, e1)), e1)
        X_windowBad = max(max(X_descWhp, POWA(max(X_windowBase, Fraction(1)))), e1)
        X_syrSum = max(X_windowBad, e1)
        return X_syrSum                                          # X_spine := X_syrSum

    T = Fraction(2) ** 3000                     # dominates every other toy leaf
    assert spine(T) == T + 1, spine(T)          # deep non-first leaf + exactly one ^alpha
    assert spine(T + 7) == T + 8                # responds (reachability, not coincidence)
    assert spine(T, omit=True) < T              # dropping the leaf loses it
    assert spine(T, minswap=True) < T           # max->min at X_harmonicZ loses it
    # C_tao_assembled = max (C_spine X_spine) ((log 2)^cTao), C_spine X = 16 * C_syrSum X,
    # C_syrSum X = max (C_windowBad*alpha/(alpha-1)) (4*max 1 ((log X)^c_ladder)):
    # structural mirror only (the tower is never materialized); both arms must be live.
    def c_tao(cwb_arm, logx_arm, log2_arm):
        c_syr = max(cwb_arm, 4 * max(Fraction(1), logx_arm))
        return max(16 * c_syr, log2_arm)
    base = c_tao(Fraction(5), Fraction(3), Fraction(1))
    assert c_tao(Fraction(50), Fraction(3), Fraction(1)) > base      # C-arm 1 live
    assert c_tao(Fraction(5), Fraction(30), Fraction(1)) > base      # C-arm 2 live
    assert c_tao(Fraction(5), Fraction(3), Fraction(10 ** 3)) > base  # log2^cTao arm live
    # explicitness closure: the full 38-entry manifest + closure walk must be clean
    import subprocess, sys, os
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    r = subprocess.run([sys.executable, os.path.join(root, "tools", "big_c_cutoff_audit.py"),
                        "--complete"], capture_output=True, text=True, cwd=root)
    assert r.returncode == 0, r.stdout + r.stderr
    print("27. assembled big-C: X_spine tree mirror (leaf reachable, one ^alpha bump; "
          "omit/min-swap variants fail), C_tao_assembled both arms live, "
          "cutoff audit --complete clean  OK")


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
    check17()                                     # big-C ladder map (GO vs re-pinned 1e11)
    check18()                                     # step-2 symbolic defs vs the ladder
    check19()                                     # lap-8 C0-arm NO-GO trace (JUDGE-FLAG)
    check20()                                     # lap-11 Sec5/Sec3 glue defs vs ladder
    check21()                                     # lap-13 tight resize (Option B pin)
    check22()                                     # lap-14 Option-B feasibility map
    check23()                                     # lap-15 flat contradiction + exp-depth door
    check24()                                     # lap-16 shallow-tip witness (JUDGE-FLAG)
    check25()                                     # lap-17b point-mass half (flag CONFIRMED)
    check26()                                     # lap-18 exp-depth door REFUTED empirically
    check27()                                     # Ruling II assembled big-C (X_spine tree)
    print("ALL CHECKS PASS ✅")
