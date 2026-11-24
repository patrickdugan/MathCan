"""VPVNP-02I: exact actual outer product bijection and character count."""
import json
from rank_geometry import rank
from full_walsh_audit import fwht

def run(n):
    q=1<<n
    m=1<<(n*n)
    mask=q-1
    ranks=[rank(b,n) for b in range(m)]
    actual={w for w in range(m) if ranks[w]==1}
    outer=set()
    for u in range(1,q):
        for v in range(1,q):
            w=sum(v<<(n*i) for i in range(n) if (u>>i)&1)
            assert w in actual and w not in outer
            outer.add(w)
    assert outer==actual and len(outer)==(q-1)**2
    spectrum=fwht([int(r==1) for r in ranks])
    signed=[None]*(n+1)
    kernels=0
    for b,k in enumerate(ranks):
        z=1<<(n-k)
        s=sum(1-2*((b&w).bit_count()&1) for w in outer)
        assert s==q*z-2*q+1==spectrum[b]
        assert signed[k] in (None,s)
        signed[k]=s
        rep=sum(1<<(i*(n+1)) for i in range(k))
        if n<=3 or b==rep:
            count=0
            for u in range(q):
                bt=0
                for i in range(n):
                    if (u>>i)&1:
                        bt^=(b>>(i*n))&mask
                count+=bt==0
            assert count==z
            kernels+=1
    return dict(n=n,dual=m,rankOne=len(outer),kernels=kernels,signed=signed,
        rankCounts=[ranks.count(k) for k in range(n+1)])

if __name__=='__main__':
    rows=[run(n) for n in range(5)]
    print(json.dumps(dict(experiment='VPVNP-02I',sizes=rows,
        totalDual=sum(r['dual'] for r in rows),
        totalKernelChecks=sum(r['kernels'] for r in rows),status='PASS'),sort_keys=True,indent=2))
