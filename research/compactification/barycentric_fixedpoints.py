"""NRF-02D: independent exact-rational positive-matrix and soft-routing oracle."""
from dataclasses import dataclass
from fractions import Fraction as Q

@dataclass(frozen=True)
class MixingEdge:
    name: str
    source: str
    target: str
    rate: Q
    probability: Q

def incoming_comparison(vertices:tuple[str,...],
                        edges:tuple[MixingEdge,...])->tuple[tuple[Q,...],...]:
    """M[v,u]=sum pi[v,e]*r[e] for e:u->v, stochastic incoming rows."""
    if not vertices or len(vertices)!=len(set(vertices)):
        raise ValueError("nonempty distinct vertices required")
    n=len(vertices); index={v:i for i,v in enumerate(vertices)}
    matrix=[[Q(0) for _ in vertices] for _ in vertices]
    mass=[Q(0)]*n; seen=set()
    for e in edges:
        if e.name in seen or e.source not in index or e.target not in index:
            raise ValueError("duplicate edge or bad endpoint")
        seen.add(e.name)
        if e.rate<0 or e.probability<0:
            raise ValueError("negative rate or probability")
        v,u=index[e.target],index[e.source]
        mass[v]+=e.probability
        matrix[v][u]+=e.rate*e.probability
    if any(p!=1 for p in mass):
        raise ValueError("all incoming rows must have unit probability")
    return tuple(tuple(row) for row in matrix)

def exact_positive_resolvent(matrix:tuple[tuple[Q,...],...])->tuple[tuple[Q,...],Q]:
    """Exact (I-M)w=1 with Mw<w, a rational certificate for rho(M)<1."""
    n=len(matrix)
    if n==0 or any(len(row)!=n for row in matrix):
        raise ValueError("square nonempty matrix required")
    if any(value<0 for row in matrix for value in row):
        raise ValueError("nonnegative comparison matrix required")
    augmented=[[Q(i==j)-matrix[i][j] for j in range(n)]+[Q(1)]
               for i in range(n)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if augmented[i][j]!=0),None)
        if pivot is None:
            raise ValueError("singular resolvent")
        augmented[j],augmented[pivot]=augmented[pivot],augmented[j]
        divisor=augmented[j][j]
        augmented[j]=[x/divisor for x in augmented[j]]
        for i in range(n):
            if i==j: continue
            factor=augmented[i][j]
            augmented[i]=[x-factor*y for x,y in zip(augmented[i],augmented[j])]
    weights=tuple(row[-1] for row in augmented)
    if any(w<=0 for w in weights):
        raise ValueError("nonpositive resolvent witness")
    ratios=[]
    for row,w in zip(matrix,weights):
        mw=sum((a*x for a,x in zip(row,weights)),Q(0))
        if mw>=w:
            raise ValueError("not strictly subcritical")
        ratios.append(mw/w)
    alpha=max(ratios)
    if not Q(0)<=alpha<Q(1):
        raise AssertionError("bad Perron upper bound")
    return weights,alpha

def smooth_mixture_bound(r_high:Q,r_low:Q,max_high_prob:Q,
                         probability_l1_lip:Q,diameter_upper:Q)->Q:
    """Contraction estimate including route variability as D*TV."""
    if not 0<=r_low<=r_high or not 0<=max_high_prob<=1:
        raise ValueError("bad rates or probability")
    if probability_l1_lip<0 or diameter_upper<0:
        raise ValueError("negative geometry")
    return (max_high_prob*r_high+(1-max_high_prob)*r_low
            +diameter_upper*probability_l1_lip/2)

def two_by_two_subcritical_criterion(a:Q,b:Q,c:Q,d:Q)->bool:
    """Exact 2x2 Perron condition for nonnegative comparison matrices."""
    if any(x<0 for x in (a,b,c,d)):
        raise ValueError("nonnegative entries required")
    return a<1 and d<1 and b*c<(1-a)*(1-d)
