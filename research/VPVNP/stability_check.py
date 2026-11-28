"""Replay VPVNP-02B stability from the exact registered rank tables."""
import json
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

data=json.loads((Path(__file__).parent/'results'/'rank_geometry.json').read_text())
rows=[]
for d in data['sizes']:
    n=d['n']
    C=Q(d['max_ratio_squared'])
    p=[Q(d['p_by_dual_rank'][str(k)]['1']) for k in range(1,n+1)]
    t=[Q(d['p_by_dual_rank'][str(k)][str(n)]) for k in range(1,n+1)]
    assert t[0]==C*p[0]
    assert all(t[k]<=Q(2,3)*C*p[k] for k in range(1,n))
    count=0
    for e in product(range(5),repeat=n):
        den=sum(x*y for x,y in zip(e,p))
        if not den:
            assert not any(e)
            continue
        R=sum(x*y for x,y in zip(e,t))/den
        eta=sum(x*y for x,y in zip(e[1:],p[1:]))/den
        assert R<=C*(1-eta/3)
        assert eta<=3*(1-R/C)
        count+=1
    for k in range(1,n):
        for scale in (1,10,100,1000):
            den=scale*p[0]+p[k]
            R=(scale*t[0]+t[k])/den
            eta=p[k]/den
            assert eta<=3*(1-R/C)
    rows.append({'n':n,'max_ratio_squared':str(C),'max_nonprimary_ratio_squared':str(max(t[k]/p[k] for k in range(1,n))),'nonzero_integer_weight_mixtures':count,'near_saturation_examples':4*(n-1)})
print(json.dumps({'experiment':'VPVNP-02B','sizes':rows,'status':'PASS'},sort_keys=True,indent=2))
