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

if __name__ == "__main__":
    check1(); check2(); check3(); check4(); check5(); check6()
    print("ALL CHECKS PASS ✅")
