"""Independent fit control for an axis-aligned cross-polytope."""
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from scheduler import Chords, greedy, minimax
import random,json

def fit(points,scales):
    # ||(x-c)/s||_1 <= lambda; rounded center gives an exact upper witness.
    m,d=len(points),len(scales); n=d+m*d+1
    obj=np.zeros(n);obj[-1]=1
    A=[]; B=[]
    for j,p in enumerate(points):
        for i,(x,s) in enumerate(zip(p,scales)):
            for sign in [-1,1]:
                row=np.zeros(n);row[i]=sign/s;row[d+j*d+i]=-1
                A.append(row);B.append(sign*x/s)
        row=np.zeros(n);row[d+j*d:d+(j+1)*d]=1;row[-1]=-1
        A.append(row);B.append(0)
    r=linprog(obj,A_ub=A,b_ub=B,bounds=[(None,None)]*d+[(0,None)]*(m*d+1),method='highs')
    if not r.success: raise RuntimeError(r.message)
    c=[F(round(x*10**8),10**8) for x in r.x[:d]]
    upper=max(sum(abs(x-y)/s for x,y,s in zip(p,c,scales)) for p in points)
    lower=max(sum(F(abs(x-y),2*s) for x,y,s in zip(p,q,scales)) for p in points for q in points)
    assert lower<=upper
    return lower,upper

def run():
    rows=[]
    for d in (3,8,16):
        scales=[120*(i+1) for i in range(d)]
        V=[tuple(sign*scales[i] if j==i else 0 for j in range(d)) for i in range(d) for sign in (-1,1)]
        C=Chords(V,128)
        for seed in (11,23,37):
            rng=random.Random(seed);edges=[]
            for j in range(64):
                i=rng.randrange(d);step=rng.choice([12,24,36,48,60]);sign=rng.choice([-1,1]);edges.append(tuple(sign*step if l==i else 0 for l in range(d)))
            points=[(0,)*d]
            for dx in edges:points.append(tuple(a+b for a,b in zip(points[-1],dx)))
            cost=[C.solve(dx)[2] for dx in edges];cuts=greedy(cost,F(1,2));k=len(cuts)-1
            methods={'gauge':cuts,'euclidean':minimax([sum(abs(x) for x in dx) for dx in edges],k),'fixed':[j*64//k for j in range(k+1)]}
            for name,cut in methods.items():
                row=dict(d=d,seed=seed,method=name,charts=k,direct_pass=0,direct_impossible=0,unresolved=0,recovered=0)
                for a,b in zip(cut,cut[1:]):
                    lo,hi=fit(points[a:b+1],scales)
                    if hi<=F(1,2):
                        row['direct_pass']+=1
                        row['recovered']+=int(sum(cost[a:b])>F(1,2))
                    elif lo>F(1,2):row['direct_impossible']+=1
                    else:row['unresolved']+=1
                rows.append(row)
    print(json.dumps(rows,indent=2))
if __name__=='__main__':run()
