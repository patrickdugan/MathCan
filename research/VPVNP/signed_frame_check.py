"""VPVNP-02F exact transport for arbitrary independent coefficient normals."""
import json
from math import prod
from frame_fiber_check import frames

def parity(x):
    return x.bit_count() & 1

def independent(n,k):
    def visit(vs,span):
        if len(vs)==k:
            yield vs
            return
        for v in range(1,1<<n):
            if v not in span:
                yield from visit(vs+(v,),span|{a^v for a in span})
    yield from visit((),{0})

def run(n):
    q=1<<n
    records=[]
    for cols in frames(n):
        normals=[b for b in range(1,q) if all(not parity(b&x) for x in cols[:-1])]
        assert len(normals)==1
        records.append((cols,normals[0]))
    ic=zc=off=0
    for k in range(1,n+1):
        for vs in independent(n,k):
            a,c=vs[:-1],vs[-1]
            signed=[0]*q
            prefix=[{} for _ in range(q)]
            for cols,b in records:
                v=prod(1-2*parity(x&y) for x,y in zip(a,cols[:-1]))
                prefix[b][cols[:-1]]=v
                signed[b]+=v*(1-2*parity(c&cols[-1]))
            for b in range(1,q):
                assert signed[b]==(-(q//2)*sum(prefix[b].values()) if b==c else 0)
                off+=b!=c
            den=prod((1<<i)-1 for i in range(n-k+1,n+1))
            assert sum(signed)*den==len(records)*(-1)**k
            ic+=1
    for k in range(n):
        for a in independent(n,k):
            signed=[0]*q
            prefix=[{} for _ in range(q)]
            for cols,b in records:
                v=prod(1-2*parity(x&y) for x,y in zip(a,cols[:-1]))
                prefix[b][cols[:-1]]=v
                signed[b]+=v
            for b in range(1,q):
                assert signed[b]==q//2*sum(prefix[b].values())
            zc+=1
    return dict(n=n,frames=len(records),independent=ic,zeroFinal=zc,offFiberChecks=off)

if __name__=='__main__':
    rows=[run(n) for n in range(1,4)]
    print(json.dumps(dict(experiment='VPVNP-02F',sizes=rows,
        totals={k:sum(r[k] for r in rows) for k in ('independent','zeroFinal','offFiberChecks')},
        status='PASS'),sort_keys=True,indent=2))
