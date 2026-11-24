"""VPVNP-02J: direct shift energies and exact Walsh spectral identity."""
from fractions import Fraction as Q
from itertools import product
import json
from rank_geometry import rank
from full_walsh_audit import fwht

def audit(n):
    m=1<<(n*n); q=1<<n
    ranks=[rank(b,n) for b in range(m)]
    one=[w for w in range(m) if ranks[w]==1]
    full=[w for w in range(m) if ranks[w]==n]
    p=[Q(1,2)*(1-Q(x,len(one))) for x in fwht([int(k==1) for k in ranks])]
    t=[Q(1,2)*(1-Q(x,len(full))) for x in fwht([int(k==n) for k in ranks])]
    C=2*(1-Q(1,q))
    cases=[]
    def check(name,coords):
        h2=[Q(0)]*m
        for f in coords:
            for b,x in enumerate(fwht(f)):
                h2[b]+=Q(x*x,m*m)
        def direct(ws):
            return Q(sum((f[a^w]-f[a])**2 for f in coords for w in ws for a in range(m)),m*len(ws))
        a,b=direct(one),direct(full)
        aa,bb=4*sum(x*y for x,y in zip(h2,p)),4*sum(x*y for x,y in zip(h2,t))
        bad=4*sum(h2[i]*p[i] for i in range(m) if ranks[i]>=2)
        assert (a,b)==(aa,bb),name
        nonconstant=any(any(v!=f[0] for v in f) for f in coords)
        assert (a>0)==nonconstant,name
        assert b<=C*a and b+C*bad/3<=C*a,name
        if a:
            assert bad/a<=3*(1-b/a/C)
        cases.append(dict(name=name,one=str(a),full=str(b),bad=str(bad),
            ratio=str(b/a) if a else None,nonconstant=nonconstant))
    def character(b):
        return [1-2*((a&b).bit_count()&1) for a in range(m)]
    if n<=2:
        for b in range(m):
            check('character-'+str(b),[character(b)])
            if ranks[b]==1:
                assert Q(cases[-1]['ratio'])==C
        for mask in range(1,m):
            check('coordinate-mask-'+str(mask),[[int(a&mask==mask) for a in range(m)]])
    if n>=2:
        check('nonlinear-vector',[[int(a&3==3) for a in range(m)],
            [a.bit_count()**2 for a in range(m)],character(1)])
    for k in (1,2,4,16):
        if n>=2:
            f=character(1);g=character((1<<0)|(1<<(n+1)))
            check('spectral-mixture-'+str(k),[[k*x+y for x,y in zip(f,g)],character(0)])
    check('constant-vector',[[3]*m,[-2]*m])
    return dict(n=n,cases=len(cases),sharp=str(C),results=cases)
if __name__=='__main__':
    rows=[audit(n) for n in (1,2,3)]
    print(json.dumps(dict(experiment='VPVNP-02J',sizes=rows,total_cases=sum(r['cases'] for r in rows),
        status='PASS'),sort_keys=True,indent=2))
