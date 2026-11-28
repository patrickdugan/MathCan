"""VPVNP-02C exact ordered-basis dynamic program; no external packages."""
from functools import lru_cache
from fractions import Fraction as Q
from math import prod
from pathlib import Path
import json

def basis_counts(n):
    q=1<<n
    full=(1<<q)-1
    bits=[1<<i for i in range(q)]
    @lru_cache(None)
    def transitions(span):
        inside=[u for u in range(q) if span & bits[u]]
        out=[]
        for v in range(1,q):
            if span & bits[v]:
                continue
            new=span
            for u in inside:
                new |= bits[u^v]
            out.append((v,new))
        return tuple(out)
    counts=[]
    for k in range(n+1):
        states={1:1}
        for j in range(n):
            # Include the last column among the k marked diagonal coordinates.
            marked=k>0 and (j<k-1 or j==n-1)
            next_states={}
            for span,weight in states.items():
                if not weight:
                    continue
                for v,new in transitions(span):
                    sign=-1 if marked and (v>>j)&1 else 1
                    next_states[new]=next_states.get(new,0)+sign*weight
            states=next_states
        counts.append(states.get(full,0))
    return counts,transitions.cache_info().currsize

def main():
    frozen=json.loads((Path(__file__).parent/'results'/'rank_geometry.json').read_text())
    archive={d['n']:d for d in frozen['sizes']}
    rows=[]
    for n in range(1,7):
        q=1<<n
        counts,spans=basis_counts(n)
        gl=prod(q-(1<<j) for j in range(n))
        assert counts[0]==gl
        for k,count in enumerate(counts):
            closed=Q((-1)**k,prod((1<<i)-1 for i in range(n-k+1,n+1)))
            actual=Q(count,gl)
            assert actual==closed,(n,k)
            if n>1 and k:
                prev=rows[-1]
                assert actual==-Q(int(prev['signed_counts'][k-1]),int(prev['gl_order']))/(q-1)
            # Independent ordered outer-product count. Every rank-one matrix has
            # exactly one representation over F2 by two nonzero vectors.
            odd=sum((u&v&((1<<k)-1)).bit_count()&1 for u in range(1,q) for v in range(1,q))
            assert odd==(q-(1<<(n-k)))*(q//2),(n,k)
            if n in archive and k:
                old=archive[n]['p_by_dual_rank'][str(k)]
                assert Q(odd,(q-1)**2)==Q(old['1'])
                assert (1-actual)/2==Q(old[str(n)])
        rows.append({'n':n,'gl_order':str(gl),'signed_counts':list(map(str,counts)),
                     'nonterminal_span_states':spans,'all_dual_ranks':True})
    print(json.dumps({'experiment':'VPVNP-02C','sizes':rows,'status':'PASS'},sort_keys=True,indent=2))

if __name__=='__main__':
    main()
