import cmath, math

def syracZ_dist(n):
    N = 3**n
    P = 2*3**(n-1) if n>=1 else 1
    inv2 = pow(2,-1,N)
    invpow = [pow(inv2,s,N) for s in range(P)]
    Z = 1.0/(1-2.0**(-P))
    w = [0.0]*P
    for r in range(P):
        kfirst = r if r>=1 else P
        w[r] = 2.0**(-kfirst)*Z
    # prob[s] is a list over X of length N
    prob = [[0.0]*N for _ in range(P)]
    prob[0][0]=1.0
    for j in range(n):
        c3 = pow(3,j,N)
        new = [[0.0]*N for _ in range(P)]
        for s in range(P):
            col = prob[s]
            tot = sum(col)
            if tot==0: continue
            for delta in range(P):
                wd=w[delta]
                if wd==0: continue
                s2=(s+delta)%P
                term=(c3*invpow[s2])%N
                dst=new[s2]
                for X in range(N):
                    v=col[X]
                    if v: dst[(X+term)%N]+= wd*v
        prob=new
    p=[0.0]*N
    for s in range(P):
        for X in range(N):
            p[X]+=prob[s][X]
    return p,N

def chat_absq(p,N,xi):
    re=im=0.0
    for Y in range(N):
        ang=-2*math.pi*xi*Y/N
        re+=p[Y]*math.cos(ang); im+=p[Y]*math.sin(ang)
    return re*re+im*im

def analyze(n,m):
    p,N=syracZ_dist(n)
    K=3**(n-m)
    high=low=0.0
    for xi in range(N):
        a=chat_absq(p,N,xi)
        if xi%K==0: low+=a
        else: high+=a
    Qn=N*sum(x*x for x in p)
    pm,_=syracZ_dist(m); Qm=3**m*sum(x*x for x in pm)
    print(f"n={n} m={m}: sum_high|c|^2={high:.5e}  Qn-Qm={Qn-Qm:.5e}  Qn={Qn:.4f} Qm={Qm:.4f}  m^-1={1.0/m:.3e} m^-2={1.0/m**2:.3e}  ratio(high*m)={high*m:.3e}")

for (n,m) in [(2,1),(3,1),(4,1),(5,1),(3,2),(4,2),(5,2),(4,3),(5,3),(5,4)]:
    analyze(n,m)
