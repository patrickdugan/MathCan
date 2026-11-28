from fractions import Fraction as F
from itertools import accumulate
from functools import lru_cache
from operator import index
import numpy as np
from scipy.optimize import linprog
from sympy import Matrix

class Chords:
    """Integer polytope; numerical LP proposes, rational arithmetic certifies."""
    def __init__(self, vertices, cache_entries=0):
        self.V = tuple(tuple(index(x) for x in v) for v in vertices)
        if not self.V or not self.V[0] or any(len(v)!=len(self.V[0]) for v in self.V):
            raise ValueError('invalid vertices')
        self.n, self.d = len(self.V), len(self.V[0])
        M = Matrix([[v[j]-self.V[0][j] for v in self.V[1:]] for j in range(self.d)])
        _, piv = M.rref()
        if len(piv) != self.d:
            raise ValueError('polytope must be full dimensional')
        self.ids = [i+1 for i in piv]
        self.inv = [[F(x) for x in row] for row in M[:,list(piv)].inv().tolist()]
        X = np.asarray(self.V, dtype=float).T
        self.eq = np.vstack([np.hstack([X,-X]), np.r_[np.ones(self.n),-np.ones(self.n)]])
        self.obj = np.r_[np.ones(self.n),np.zeros(self.n)]
        self._cached = lru_cache(maxsize=cache_entries)(self._solve)

    def solve(self, dx):
        dx = tuple(index(x) for x in dx)
        if len(dx)!=self.d: raise ValueError('invalid chord dimension')
        return self._cached(dx)

    def image(self, p):
        return tuple(sum(w*v[j] for w,v in zip(p,self.V)) for j in range(self.d))

    def _solve(self, dx):
        n = self.n
        r = linprog(self.obj,A_eq=self.eq,b_eq=[*dx,0],bounds=(0,None),method='highs')
        if not r.success:
            raise RuntimeError(r.message)
        p,q = ([F(max(0,round(float(z)*10**9)),10**9) for z in row] for row in (r.x[:n],r.x[n:]))
        # Equal mass by padding at the anchor, then repair the exact residual.
        p[0] += max(F(0),sum(q)-sum(p))
        q[0] += max(F(0),sum(p)-sum(q))
        res = [a-b+c for a,b,c in zip(dx,self.image(p),self.image(q))]
        for i,row in zip(self.ids,self.inv):
            z = sum(a*b for a,b in zip(row,res))
            if z >= 0: p[i]+=z; q[0]+=z
            else: q[i]-=z; p[0]-=z
        if min(p+q)<0 or sum(p)!=sum(q) or tuple(a-b for a,b in zip(self.image(p),self.image(q)))!=dx:
            raise ArithmeticError('invalid witness')
        return tuple(p),tuple(q),sum(p)

    def chart(self, points, chords, start, end, lam):
        """Shared-endpoint interval [start,end], exact coefficient certificate."""
        A=sum((c[2] for c in chords[start:end]),F(0))
        if A>lam or lam<=0: raise ValueError('chart budget exceeded')
        weights=[sum((c[1][i] for c in chords[start:end]),F(0)) for i in range(self.n)]
        weights[0]+=lam-A
        v=tuple(x-y for x,y in zip(points[start],self.image(weights)))
        for j in range(start,end+1):
            if min(weights)<0 or sum(weights)!=lam or tuple(x-y for x,y in zip(points[j],v))!=self.image(weights):
                raise ArithmeticError('invalid chart')
            if j<end:
                p,q,_=chords[j]; weights=[w+a-b for w,a,b in zip(weights,p,q)]
        return v,A

def greedy(costs, budget):
    if budget<=0 or any(c<0 or c>budget for c in costs): raise ValueError('uncoverable edge')
    cuts=[0]; acc=0
    for i,c in enumerate(costs):
        if acc+c>budget: cuts.append(i); acc=0
        acc+=c
    cuts.append(len(costs))
    return cuts

def minimax(costs,k):
    """Optimal fixed-count contiguous partition for the given additive cost."""
    n=len(costs)
    if not 1<=k<=n or any(c<0 for c in costs): raise ValueError('invalid partition')
    pref=list(accumulate(costs,initial=0)); dp={(0,0):(0,[])}
    for j in range(1,k+1):
        for b in range(j,n-(k-j)+1):
            dp[j,b]=min((max(dp[j-1,a][0],pref[b]-pref[a]),dp[j-1,a][1]+[b]) for a in range(j-1,b) if (j-1,a) in dp)
    return [0]+dp[k,n][1]

def readout_lower(vertices,v,lam,a,b=0):
    return b+sum(x*y for x,y in zip(a,v))+lam*min(sum(x*y for x,y in zip(a,w)) for w in vertices)
