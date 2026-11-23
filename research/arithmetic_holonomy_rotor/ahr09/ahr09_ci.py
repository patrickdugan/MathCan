"""AHR-09: integer cube cochains, tree-gauge inverse, Bianchi projection."""
from pathlib import Path
import json
import numpy as np
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ

D=3
EDGES=sorted((u,u^(1<<k)) for u in range(8) for k in range(D) if not u>>k&1)
INDEX={e:i for i,e in enumerate(EDGES)}
FACES=sorted((i,j,u) for i in range(D) for j in range(i+1,D) for u in range(8) if not u>>i&1 and not u>>j&1)
TREE=[(0,1),(0,2),(0,4),(1,3),(1,5),(2,6),(3,7)]
CHORDS=[e for e in EDGES if e not in TREE]

def wrap(a):return (np.asarray(a)+np.pi)%(2*np.pi)-np.pi

def chain():
    d0=sp.zeros(12,8);d1=sp.zeros(6,12)
    for k,(u,v) in enumerate(EDGES):d0[k,u]=-1;d0[k,v]=1
    for k,(i,j,u) in enumerate(FACES):
        route=[u,u^(1<<i),u^(1<<i)^(1<<j),u^(1<<j),u]
        for a,b in zip(route,route[1:]):
            d1[k,INDEX[tuple(sorted((a,b)))]]+=1 if a<b else -1
    B=sp.Matrix([[-1,1,1,-1,-1,1]])
    return d0,d1,B

def tree_gauge(A):
    adjacency={v:[] for v in range(8)}
    for a,b in TREE:
        angle=A[INDEX[(a,b)]]
        adjacency[a].append((b,angle))
        adjacency[b].append((a,-angle))
    g={0:0.};stack=[0]
    while stack:
        u=stack.pop()
        for v,theta in adjacency[u]:
            if v not in g:g[v]=g[u]+theta;stack.append(v)
    assert len(g)==8
    return np.array([g[i] for i in range(8)])

def main():
    d0,d1,B=chain()
    assert d1*d0==sp.zeros(6,8)
    assert B*d1==sp.zeros(1,12)
    ranks=[int(x.rank()) for x in (d0,d1,B)]
    assert ranks==[7,5,1]
    diagonal=[int(smith_normal_form(d1,domain=ZZ)[k,k]) for k in range(6)]
    assert diagonal[:5]==[1]*5 and diagonal[5]==0
    chordcols=[INDEX[e] for e in CHORDS]
    M=d1[:,chordcols]
    assert M[:5,:].det() in (sp.Integer(1),sp.Integer(-1))
    Dfloat=np.array(d1.tolist(),float)
    Bvec=np.array(B.tolist(),float).reshape(6)
    rng=np.random.default_rng(20261123)
    maxreconstruction=0.
    for _ in range(100):
        original=rng.uniform(-np.pi,np.pi,size=12)
        curvature=Dfloat@original
        transformed=original.copy();g=tree_gauge(original)
        for k,(u,v) in enumerate(EDGES):transformed[k]+=g[u]-g[v]
        assert max(abs(transformed[INDEX[e]]) for e in TREE)<1e-12
        chords=np.linalg.solve(np.array(M[:5,:].tolist(),float),curvature[:5])
        diff=wrap(chords-transformed[chordcols])
        maxreconstruction=max(maxreconstruction,float(max(abs(diff))))
        assert max(abs(diff))<1e-11
    N=20000;sigma=.08
    true_edges=rng.uniform(-.25,.25,size=12)
    true_flux=Dfloat@true_edges
    raw=true_flux[None,:]+rng.normal(0,sigma,size=(N,6))
    residual=wrap(raw@Bvec)
    projected=raw-residual[:,None]*Bvec[None,:]/float(Bvec@Bvec)
    assert max(abs(wrap(projected@Bvec)))<1e-11
    mse_raw=float(np.mean(np.sum((raw-true_flux)**2,axis=1)))
    mse_projected=float(np.mean(np.sum((projected-true_flux)**2,axis=1)))
    ratio=mse_projected/mse_raw
    assert .81<ratio<.85
    result=dict(status='PASS',ranks=ranks,smith_diagonal=diagonal,
        max_chord_error=maxreconstruction,noise_sigma=sigma,noise_draws=N,
        mse_raw=mse_raw,mse_projected=mse_projected,mse_ratio=ratio,
        theoretical_ratio=5/6,independent_flux_dof=5,
        note='Exact integer algebra and simulated Gaussian noise, no QPU')
    Path(__file__).with_name('ahr09_ci_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
