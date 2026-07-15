"""
Probe the C8 truncation-excess mechanism.

Lean defs:
  pre a m   = a_{[1,m]} = a_0+...+a_{m-1}
  fnat k a  = sum_{m=0}^{k-1} 3^{k-1-m} * 2^{pre a m}
  Aff N k a = (3^k * N + fnat k a) // 2^{pre a k}          (NAT floor division)

Tao's paper uses the EXACT rational affine map Aff_a (1.3); the reindex (5.8) is EXACT
via Lemma 2.1 with the congruence (5.18)  M == F_{k}(a) mod 3^k.  The Lean `Aff` floors,
dropping that congruence.  `truncation_error_bound` claims the resulting excess
   approxMainTerm - steppedMid  =  E_N[ #{good a != valVec : Aff N k a in E'} ]
is O(log^{-c} x).  This probe measures, for a fixed odd N and length k, how many
DISTINCT tuples a (with each a_i>=1 and a_{[1,k]}=s near 2k) send Aff N k a into a
window around the true value syr^k N.  If that count is >> 1, the excess is NOT small.
"""
from itertools import product

def syr(N):
    # (3N+1)/2^v2(3N+1)
    m = 3*N+1
    while m % 2 == 0:
        m //= 2
    return m

def syr_iter(N, k):
    for _ in range(k):
        N = syr(N)
    return N

def pre(a, m):
    return sum(a[:m])

def fnat(k, a):
    return sum(3**(k-1-m) * 2**pre(a, m) for m in range(k))

def Aff(N, k, a):
    return (3**k * N + fnat(k, a)) // 2**pre(a, k)

def tuples_with_partialsums(k, smax_each=6):
    # all a in {1..smax_each}^k
    for a in product(range(1, smax_each+1), repeat=k):
        yield a

def good(a, k, thr):
    # |a_{[1,n]} - 2n| <= thr for all 1<=n<=k
    for n in range(1, k+1):
        if abs(pre(a, n) - 2*n) > thr:
            return False
    return True

for k in [5, 6, 7, 8]:
    for N in [7, 11, 27, 101, 1001]:
        if N % 2 == 0:
            continue
        true_val = syr_iter(N, k)
        vv = tuple( __import__('math').inf for _ in range(0) )  # placeholder
        # true valuation vector prefix sums:  we can compute actual valVec
        vvec = []
        M = N
        for i in range(k):
            v = 0; t = 3*M+1
            while t % 2 == 0:
                t//=2; v+=1
            vvec.append(v); M = t
        vvec = tuple(vvec)
        # window: multiplicative half-width W around true_val (proxy for E')
        W = 4.0   # generous but finite; E' is multiplicative width exp(log^0.7 x)
        lo = true_val / W
        hi = true_val * W
        thr = 3   # good-tuple threshold proxy (paper: log^{0.6} x)
        cnt = 0
        vals = set()
        collide = {}
        for a in tuples_with_partialsums(k, smax_each=5):
            if not good(a, k, thr):
                continue
            v = Aff(N, k, a)
            if lo <= v <= hi:
                cnt += 1
                vals.add(v)
                s = pre(a, k)
                collide.setdefault(s, []).append(v)
        # spread of Aff over fixed |a|=s (measure the "collapse")
        spreads = {s: (min(vs), max(vs), len(vs)) for s, vs in collide.items()}
        print(f"k={k} N={N:5d} syr^k N={true_val:12d} vvec_sum={sum(vvec)}"
              f"  #good_a_in_E'window={cnt:5d}  #distinct_Aff_vals={len(vals):4d}")
    print()

print("=== WITH the exact divisibility guard 2^{|a|} | (3^k N + fnat) (paper's exact reindex) ===")
for k in [5, 6, 7, 8]:
    for N in [7, 11, 27, 101, 1001]:
        if N % 2 == 0: continue
        true_val = syr_iter(N, k)
        W = 4.0; lo = true_val / W; hi = true_val * W; thr = 3
        cnt_all = 0; cnt_guard = 0; guard_vals = []
        for a in tuples_with_partialsums(k, smax_each=5):
            if not good(a, k, thr): continue
            num = 3**k * N + fnat(k, a)
            v = num // 2**pre(a, k)
            if lo <= v <= hi:
                cnt_all += 1
                if num % (2**pre(a, k)) == 0:   # exact divisibility (no truncation)
                    cnt_guard += 1; guard_vals.append((a, v))
        print(f"k={k} N={N:5d}  #good_in_window(trunc)={cnt_all:6d}   #good_in_window(EXACT guard)={cnt_guard}   guard_vals={[v for _,v in guard_vals][:4]}")
    print()
