"""AHR-06: mixed-edge local return probability expansion for simple even cycles."""
from itertools import product
import numpy as np
from scipy.linalg import expm
from pathlib import Path
import json
import math


def H(d,V,w,phase):
    n=1<<d
    h=np.diag(V).astype(complex)
    for (a,b),j in w.items():
        h[a,b]=j*np.exp(1j*phase[(a,b)])
        h[b,a]=np.conj(h[a,b])
    return h


def edges_cycle(c):
    return [tuple(sorted((a,b))) for a,b in zip(c,c[1:]+c[:1])]


def flux(c,ph):
    return sum((1 if a<b else -1)*ph[tuple(sorted((a,b)))] for a,b in zip(c,c[1:]+c[:1]))


def mixed_return(d,c,V,w,ph,t):
    es=edges_cycle(c); L=len(es); x=c[0]
    val=0.
    for choices in product((0,1),repeat=L):
        ww=w.copy()
        for e,bit in zip(es,choices):ww[e]=w[e]*bit
        U=expm(-1j*t*H(d,V,ww,ph))
        val += (-1)**(L-sum(choices))*abs(U[x,x])**2
    return float(val)


def graph(d,rng):
    V=rng.normal(size=1<<d)
    w={(x,x|(1<<i)):float(rng.uniform(.6,1.2)) for x in range(1<<d) for i in range(d) if not x>>i&1}
    a={e:float(rng.uniform(-1.2,1.2)) for e in w}
    return V,w,a


def main():
    rng=np.random.default_rng(20261123)
    examples=[]
    for d,c in [(2,[0,1,3,2]),(3,[0,1,3,7,6,4])]:
        V,w,ph=graph(d,rng)
        L=len(c)
        W=float(np.prod([w[e] for e in edges_cycle(c)]))
        phi=flux(c,ph)
        prefactor=4*((-1)**(L//2))*W*np.cos(phi)/math.factorial(L)
        assert abs(prefactor)>1e-6
        entries=[]
        for t in (.4,.3,.2):
            observed=mixed_return(d,c,V,w,ph,t)
            predicted=prefactor*t**L
            entries.append({'t':t,'observed':observed,'leading':predicted,'ratio':observed/predicted})
        assert abs(entries[-1]['ratio']-1)<.2,entries
        examples.append({'d':d,'length':L,'flux':phi,'coupling_product':W,'prefactor':prefactor,'times':entries})
    result={'status':'PASS','examples':examples}
    Path(__file__).with_name('ahr06_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
