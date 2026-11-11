"""Finite Gaussian gauge-quotient relative entropy, exact rational arithmetic.

TOE-01 mathematical research inspired by the TOE interview catalog. This is a
classical finite-graph model; it does not derive a physical gravity equation.
"""
from dataclasses import dataclass
from fractions import Fraction as F


def q(x):
    return x if isinstance(x, F) else F(x)


def transpose(a):
    return [list(col) for col in zip(*a)] if a else []


def matmul(a, b):
    return [[sum((x*y for x,y in zip(row,col)), F(0)) for col in zip(*b)] for row in a]


def matvec(a,v):
    return [sum((x*y for x,y in zip(row,v)), F(0)) for row in a]


def dot(a,b):
    return sum((x*y for x,y in zip(a,b)), F(0))


def kernel(a,ncols):
    """Exact nullspace basis of a matrix (rows of A, ncols coordinates)."""
    m=[list(map(q,row)) for row in a]
    if any(len(row)!=ncols for row in m):
        raise ValueError("ragged matrix")
    pivots=[]; i=0
    for j in range(ncols):
        k=next((r for r in range(i,len(m)) if m[r][j]),None)
        if k is None: continue
        m[i],m[k]=m[k],m[i]
        pivot=m[i][j]
        m[i]=[v/pivot for v in m[i]]
        for r in range(len(m)):
            if r!=i and m[r][j]:
                mult=m[r][j]
                m[r]=[x-mult*y for x,y in zip(m[r],m[i])]
        pivots.append(j);i+=1
        if i==len(m):break
    out=[]
    for j in range(ncols):
        if j in pivots: continue
        v=[F(0)]*ncols;v[j]=F(1)
        for row,col in enumerate(pivots):
            v[col]=-m[row][j]
        out.append(v)
    return out


def solve(a,b):
    n=len(a)
    if len(b)!=n or any(len(row)!=n for row in a):
        raise ValueError("square system required")
    m=[list(map(q,row))+[q(b[i])] for i,row in enumerate(a)]
    for i in range(n):
        pivot=next((r for r in range(i,n) if m[r][i]),None)
        if pivot is None:raise ValueError("singular covariance")
        m[i],m[pivot]=m[pivot],m[i]
        d=m[i][i];m[i]=[x/d for x in m[i]]
        for r in range(n):
            if r!=i:
                f=m[r][i];m[r]=[x-f*y for x,y in zip(m[r],m[i])]
    return [row[-1] for row in m]


def quotient_action(signal,nuisance,covariance):
    """Minimum 1/2 (signal - nuisance*theta)^T cov^-1 (...).

    Uses a nullspace of nuisance^T to compute the exact Gaussian KL
    quotient. Covariance is assumed symmetric positive definite.
    """
    n=len(signal)
    if not n or len(nuisance)!=n or len(covariance)!=n:
        raise ValueError("observation dimensions")
    k=len(nuisance[0])
    if any(len(row)!=k for row in nuisance) or any(len(row)!=n for row in covariance):
        raise ValueError("matrix dimensions")
    c=kernel(transpose(nuisance) if k else [],n)
    if not c:return F(0)
    cov=matmul(matmul(c,covariance),transpose(c))
    residual=matvec(c,list(map(q,signal)))
    return dot(residual,solve(cov,residual))/2


@dataclass(frozen=True)
class Graph:
    vertices:int
    edges:tuple[tuple[int,int],...]

    def __post_init__(self):
        if self.vertices<1 or not self.edges:raise ValueError("finite graph required")
        if any(u==v or min(u,v)<0 or max(u,v)>=self.vertices for u,v in self.edges):
            raise ValueError("invalid edge")
        visited={0}
        while True:
            before=len(visited)
            for u,v in self.edges:
                if u in visited or v in visited: visited.update((u,v))
            if len(visited)==before:break
        if len(visited)!=self.vertices:raise ValueError("connected graph required")

    def incidence(self):
        return [[F((v==j)-(u==j)) for j in range(1,self.vertices)]
                for u,v in self.edges]


def action(graph,quotes,variances):
    m=len(graph.edges)
    if len(quotes)!=m or len(variances)!=m:raise ValueError("shape mismatch")
    if any(q(v)<=0 for v in variances):raise ValueError("positive variances")
    cov=[[q(variances[i]) if i==j else F(0) for j in range(m)] for i in range(m)]
    return quotient_action(quotes,graph.incidence(),cov)


def coarse_action(graph,quotes,variances,observations):
    m=len(graph.edges)
    if not observations or any(len(row)!=m for row in observations):
        raise ValueError("channel shape")
    a=[list(map(q,row)) for row in observations]
    if kernel(transpose(a),len(a)):
        raise ValueError("observation rows must be independent")
    cov=[[sum((a[i][k]*q(variances[k])*a[j][k] for k in range(m)),F(0))
          for j in range(len(a))] for i in range(len(a))]
    return quotient_action(matvec(a,quotes),matmul(a,graph.incidence()),cov)


def gradients(graph,potential):
    if len(potential)!=graph.vertices:raise ValueError("missing vertex")
    return [q(potential[v])-q(potential[u]) for u,v in graph.edges]


def rational_detailed_balance(graph,forward,backward):
    """Exact Kolmogorov cycle criterion for paired positive transition rates."""
    if len(forward)!=len(graph.edges) or len(backward)!=len(graph.edges):
        raise ValueError("rate dimensions")
    if any(q(a)<=0 or q(b)<=0 for a,b in zip(forward,backward)):
        raise ValueError("positive rates")
    p={0:F(1)}
    while True:
        before=len(p)
        for (u,v),a,b in zip(graph.edges,forward,backward):
            ratio=q(a)/q(b)
            if u in p and v not in p:p[v]=p[u]*ratio
            elif v in p and u not in p:p[u]=p[v]/ratio
        if len(p)==before:break
    if len(p)!=graph.vertices:raise AssertionError("graph disconnected")
    if any(p[u]*q(a)!=p[v]*q(b) for (u,v),a,b in zip(graph.edges,forward,backward)):
        return None
    total=sum(p.values(),F(0))
    return tuple(p[v]/total for v in range(graph.vertices))
