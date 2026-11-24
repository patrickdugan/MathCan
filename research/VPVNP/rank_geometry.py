"""VPVNP-02A: exact rank-stratified Walsh observer audit, stdlib only."""
from fractions import Fraction as Q
from math import prod
from pathlib import Path
import argparse
import json


def rank(a, n):
    rows = [(a >> (i*n)) & ((1 << n)-1) for i in range(n)]
    r = 0
    for j in range(n):
        p = next((i for i in range(r,n) if rows[i] >> j & 1), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        for i in range(r+1,n):
            if rows[i] >> j & 1:
                rows[i] ^= rows[r]
        r += 1
    return r


def parity(a, b):
    return (a & b).bit_count() & 1


def p_one(n,k):
    return Q(((1 << n)-(1 << (n-k)))*(1 << (n-1)), ((1 << n)-1)**2)


def p_full(n,k):
    return (1-Q((-1)**k, prod((1 << i)-1 for i in range(n-k+1,n+1))))/2


def count_rank(n,r):
    return Q(prod(((1 << n)-(1 << i))**2 for i in range(r)),
             prod((1 << r)-(1 << i) for i in range(r)))


def audit(n):
    strata = [[] for _ in range(n+1)]
    for w in range(1 << (n*n)):
        strata[rank(w,n)].append(w)
    assert all(len(ws) == count_rank(n,r) for r,ws in enumerate(strata))
    p = {k: {r: Q(sum(parity(w, sum(1 << (i*(n+1)) for i in range(k))) for w in strata[r]),len(strata[r]))
             for r in range(1,n+1)} for k in range(1,n+1)}
    h1 = all(p[k][1] > 0 and p[k][1] == p_one(n,k) for k in p)
    h2 = all(p[k][n] == p_full(n,k) for k in p)
    ratios = {k:p[k][n]/p[k][1] for k in p}
    expected = 2*(1-Q(1,1 << n))
    h3 = max(ratios.values()) == expected < n
    assert h1 and h2 and h3
    return {"n":n,"rank_counts":[len(ws) for ws in strata],
            "p_by_dual_rank":{str(k):{str(r):str(v) for r,v in row.items()} for k,row in p.items()},
            "ratios_squared":{str(k):str(v) for k,v in ratios.items()},
            "max_ratio_squared":str(max(ratios.values())),"maximizers":[k for k in p if ratios[k] == expected],
            "rank_metric_ratio_squared":n*n,"sqrt_rank_metric_ratio_squared":n,
            "constant_observer_ratio":"undefined","H1":h1,"H2":h2,"H3":h3}


def walsh_control():
    n=2
    m=1 << (n*n)
    # Fixed nonlinear integer vector observer, with a linear character coordinate.
    f=[((a & 3)==3, a.bit_count()**2, (-1)**parity(a,9)) for a in range(m)]
    norm2=lambda v:sum(x*x for x in v)
    h2=[Q(norm2([sum((-1)**parity(a,b)*f[a][j] for a in range(m)) for j in range(3)]),m*m) for b in range(m)]
    out={}
    for r in range(1,n+1):
        ws=[w for w in range(m) if rank(w,n)==r]
        direct=Q(sum(norm2([f[a^w][j]-f[a][j] for j in range(3)]) for a in range(m) for w in ws),m*len(ws))
        spectral=4*sum(h2[b]*Q(sum(parity(b,w) for w in ws),len(ws)) for b in range(1,m))
        assert direct == spectral and direct>0
        out[str(r)]={"direct_D_squared":str(direct),"spectral_D_squared":str(spectral)}
    assert all(rank(a^b,n)<=rank(a,n)+rank(b,n) for a in range(m) for b in range(m))
    return {"H4":True,"ranks":out,"rank_metric_triangle_n2":True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path)
    args=parser.parse_args()
    data={"experiment":"VPVNP-02A","method":"exact exhaustive matrix rank and dual rank character representatives","sizes":[audit(n) for n in (2,3,4)],"nonlinear_control":walsh_control(),"status":"PASS"}
    report=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if args.out:
        args.out.write_text(report,encoding='utf-8')
    else:
        print(report,end='')

if __name__=='__main__':
    main()
