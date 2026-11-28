"""AHR-08: intact-cube plaquette tomography oracle; NumPy/SciPy only."""
from itertools import combinations
from math import pi, log, sqrt
from pathlib import Path
import json
import numpy as np
from scipy.linalg import eigh

OFF=np.arange(4)*pi/2

def cube(d,seed):
    rng=np.random.default_rng(seed)
    primes=(2,3,5,7)
    V=np.array([sum(log(primes[k]) for k in range(d) if v>>k&1) for v in range(1<<d)])+rng.normal(0,.2,size=1<<d)
    E={(u,u^(1<<k)):(float(rng.uniform(.7,1.3)),float(rng.uniform(-1.2,1.2))) for u in range(1<<d) for k in range(d) if not u>>k&1}
    return V,E

def face(E,e,j):
    u,v=e; x=u^(1<<j);y=v^(1<<j)
    def angle(a,b):return E[(a,b)][1] if a<b else -E[(b,a)][1]
    F=sum(angle(a,b) for a,b in ((x,u),(u,v),(v,y),(y,x)))
    W=np.prod([E[tuple(sorted((a,b)))][0] for a,b in ((x,u),(u,v),(v,y),(y,x))])
    return x,float(F),float(W)

def signal(g,x,e,t,gauge=None):
    V,E=g; out=[]
    for delta in OFF:
        H=np.diag(V).astype(complex)
        for (u,v),(w,a) in E.items():
            if gauge is not None:a+=gauge[u]-gauge[v]
            z=w*np.exp(1j*(a+(delta if (u,v)==e else 0)))
            H[u,v]=z;H[v,u]=np.conj(z)
        vals,U=eigh(H)
        out.append(abs(np.dot(abs(U[x])**2,np.exp(-1j*t*vals)))**2)
    return complex(np.dot(out,np.exp(-1j*OFF))/2)

def q(g,x,e,W,t):return 6*signal(g,x,e,t)/(W*t**4)

def cover(g):
    E=g[1]; faces=set(); cmap={}
    for e in E:
        i=(e[0]^e[1]).bit_length()-1; cmap[e]=set()
        for j in range(3):
            if j!=i:
                u,v=e; f=frozenset((u,v,u^(1<<j),v^(1<<j)))
                faces.add(f);cmap[e].add(f)
    for k in range(1,len(E)+1):
        for group in combinations(E,k):
            if set().union(*(cmap[e] for e in group))==faces:return list(group),len(faces)

def main():
    cases=[]
    for d,seed in ((3,20261123),(3,20261124),(4,20261125)):
        g=cube(d,seed)
        gauge=np.random.default_rng(seed+37).normal(size=1<<d)
        e=(0,1);x,F,W=face(g[1],e,1)
        assert abs(signal(g,x,e,.67)-signal(g,x,e,.67,gauge))<2e-13
        t=.4; target=np.exp(1j*F)
        raw=q(g,x,e,W,t); rich=2*q(g,x,e,W,t/sqrt(2))-raw
        assert abs(rich-target)<abs(raw-target)/3
        pairs=0
        for edge in g[1]:
            axis=(edge[0]^edge[1]).bit_length()-1
            for j in range(d):
                if j==axis:continue
                start,f,w=face(g[1],edge,j)
                assert abs(q(g,start,edge,w,.2)-np.exp(1j*f))<.5
                pairs+=1
        cases.append(dict(d=d,seed=seed,all_edge_face_assignments=pairs,
            raw_complex_error=float(abs(raw-target)),richardson_complex_error=float(abs(rich-target)),
            raw_angle_error_rad=float(np.angle(raw*np.exp(-1j*F))),
            richardson_angle_error_rad=float(np.angle(rich*np.exp(-1j*F)))))
    g=cube(3,20261123)
    selected,nfaces=cover(g)
    assert len(selected)==3 and nfaces==6
    assert selected==[(0,1),(2,6),(5,7)]
    def Fij(i,j,fix):
        third={(0,1):2,(0,2):1,(1,2):0}[(i,j)]
        base=fix<<third
        return face(g[1],(base,base^(1<<i)),j)[1]
    B=(Fij(1,2,1)-Fij(1,2,0))-(Fij(0,2,1)-Fij(0,2,0))+(Fij(0,1,1)-Fij(0,1,0))
    assert abs((B+pi)%(2*pi)-pi)<1e-12
    e=(0,1); t=.15
    expected=sum(w*np.exp(1j*f) for j in (1,2) for x,f,w in [face(g[1],e,j)])
    wrong=6*signal(g,0,e,t)/t**4
    assert abs(wrong-expected)<.3
    result=dict(status='PASS',cases=cases,min_controlled_edges=3,
        controlled_edges=[list(e) for e in selected],faces=6,circuits_four_phase=24,
        wrong_corner_complex_error=float(abs(wrong-expected)),
        note='Numerical exact-matrix evaluation; no hardware observations')
    Path(__file__).with_name('ahr08_ci_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
