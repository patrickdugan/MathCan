"""VPVNP-02H exact trace/prefix/tail bridge on every small full frame."""
import json
from math import prod
from frame_fiber_check import frames

def parity(x):
    return x.bit_count() & 1

def run(n,prev):
    q=1<<n
    counts=[0]*q
    prefix=[0]*(n+1)
    total=checks=0
    for cols in frames(n):
        total+=1
        diag=sum(((cols[j]>>j)&1)<<j for j in range(n))
        for m in range(q):
            counts[m]+=1-2*parity(diag&m)
        for k in range(n+1):
            mask=q-(1<<(n-k))
            sign=prod(1-2*((cols[j]>>j)&1) for j in range(n-k,n))
            assert sign==1-2*parity(diag&mask)
            checks+=1
            if n and k and all(not (x>>(n-1)&1) for x in cols[:-1]):
                assert cols[-1]>>(n-1)&1
                prefix[k]+=sign
    canonical=[]
    for k in range(n+1):
        mask=q-(1<<(n-k))
        denom=prod((1<<i)-1 for i in range(n-k+1,n+1))
        assert counts[mask]*denom==total*(-1)**k
        if n and k:
            assert prefix[k]==-(q//2)*prev[k-1]
        canonical.append(counts[mask])
    for m in range(q):
        assert counts[m]==canonical[m.bit_count()]
    return dict(n=n,frames=total,masks=q,canonical=canonical,factorChecks=checks)

if __name__=='__main__':
    rows=[]
    prev=[]
    for n in range(5):
        row=run(n,prev)
        rows.append(row)
        prev=row['canonical']
    print(json.dumps(dict(experiment='VPVNP-02H',sizes=rows,
        totalFrames=sum(r['frames'] for r in rows),
        totalMasks=sum(r['masks'] for r in rows),
        totalFactorChecks=sum(r['factorChecks'] for r in rows),
        status='PASS'),sort_keys=True,indent=2))
