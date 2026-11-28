"""VPVNP-02G: every dual matrix, exact Walsh transform and direct control."""
from math import prod
import json
from rank_geometry import rank

def fwht(indicator):
    a=indicator[:]
    h=1
    while h<len(a):
        for i in range(0,len(a),2*h):
            for j in range(i,i+h):
                x,y=a[j],a[j+h]
                a[j],a[j+h]=x+y,x-y
        h*=2
    return a

def run(n):
    m=1<<(n*n)
    q=1<<n
    ranks=[rank(b,n) for b in range(m)]
    full=[w for w in range(m) if ranks[w]==n]
    one=[w for w in range(m) if ranks[w]==1]
    full_w=fwht([int(k==n) for k in ranks])
    one_w=fwht([int(k==1) for k in ranks])
    rows=[]
    for k in range(n+1):
        denom=prod((1<<i)-1 for i in range(n-k+1,n+1))
        assert len(full)%denom==0
        rows.append(dict(k=k,dual_count=ranks.count(k),
            full_rank_signed=(-1)**k*(len(full)//denom),
            rank_one_signed=len(one)-2*(q-(1<<(n-k)))*(q//2)))
    for b,k in enumerate(ranks):
        assert full_w[b]==rows[k]['full_rank_signed'],(n,b,k)
        assert one_w[b]==rows[k]['rank_one_signed'],(n,b,k)
        if n<=3:
            assert sum(1-2*((b&w).bit_count()&1) for w in full)==full_w[b]
            assert sum(1-2*((b&w).bit_count()&1) for w in one)==one_w[b]
    return dict(n=n,matrix_count=m,rank_one_count=len(one),full_rank_count=len(full),
        rows=rows,direct_verified=n<=3)

if __name__=='__main__':
    rows=[run(n) for n in range(1,5)]
    print(json.dumps(dict(experiment='VPVNP-02G',sizes=rows,
        total_dual_matrices=sum(r['matrix_count'] for r in rows),status='PASS'),
        sort_keys=True,indent=2))
