"""VPVNP-02E exhaustive independent frame-fiber oracle."""
import json
from pathlib import Path

def parity(x):
    return x.bit_count()&1

def frames(n):
    q=1<<n
    def visit(cols,span):
        if len(cols)==n:
            yield cols
            return
        for v in range(1,q):
            if v not in span:
                yield from visit(cols+(v,),span|{a^v for a in span})
    yield from visit((),{0})

def main():
    prior=[1]
    rows=[]
    for n in range(1,5):
        q=1<<n
        sums=[[0]*q for _ in range(n+1)]
        count=0
        for cols in frames(n):
            count+=1
            normals=[b for b in range(1,q) if all(not parity(b&x) for x in cols[:-1])]
            assert len(normals)==1
            b=normals[0]
            assert parity(b&cols[-1])==1
            sums[0][b]+=1
            for k in range(1,n+1):
                p=parity(sum(((cols[j]>>j)&1)<<j for j in range(k-1)) | (((cols[-1]>>(n-1))&1)<<(n-1)))
                sums[k][b]+=1-2*p
        fiber=prior[0]*(q//2)
        assert all(sums[0][b]==fiber for b in range(1,q))
        for k in range(1,n+1):
            for b in range(1,q):
                assert sums[k][b]==(-q//2*prior[k-1] if b==q//2 else 0)
        prior=list(map(sum,sums))
        assert prior[0]==count
        rows.append(dict(n=n,bases=count,normal_count=q-1,fiber_size=fiber,
                         signed_counts=prior,signed_fiber_checks=n*(q-1)))
    # Reproduce the independently registered ordered-basis DP totals.
    from basis_dp import basis_counts
    for row in rows:
        assert row['signed_counts']==basis_counts(row['n'])[0]
    print(json.dumps(dict(experiment='VPVNP-02E',sizes=rows,
        total_frames=sum(x['bases'] for x in rows),
        signed_fiber_checks=sum(x['signed_fiber_checks'] for x in rows),
        status='PASS'),sort_keys=True,indent=2))

if __name__=='__main__':
    main()
