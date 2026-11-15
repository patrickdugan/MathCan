"""OLM-13: exact Sudoku intercalate invariant and factorization/gauge oracles."""
from fractions import Fraction as Q
from itertools import combinations


def canonical_grid():
    return tuple(1+(3*(r%3)+r//3+c)%9 for r in range(9) for c in range(9))


def intercalates(grid):
    """Count alternating 2x2 submatrices with two distinct digit symbols."""
    if len(grid)!=81 or any(not isinstance(v,int) or not 1<=v<=9 for v in grid):
        raise ValueError('filled 9x9 digit grid required')
    total=0
    for r,s in combinations(range(9),2):
        for c,d in combinations(range(9),2):
            if grid[9*r+c]==grid[9*s+d] and grid[9*r+d]==grid[9*s+c] and grid[9*r+c]!=grid[9*r+d]:
                total+=1
    return total


def transform(grid,rows,cols,digits,transpose=False):
    if (sorted(rows)!=list(range(9)) or sorted(cols)!=list(range(9))
        or sorted(digits)!=list(range(1,10))):
        raise ValueError('permutation of rows, columns and digits required')
    relabel=dict(zip(range(1,10),digits))
    res=[relabel[grid[9*rows[r]+cols[c]]] for r in range(9) for c in range(9)]
    return tuple(res[c*9+r] for r in range(9) for c in range(9)) if transpose else tuple(res)


def matmul(a,b):
    if not a or not b or not a[0] or len(a[0])!=len(b) or any(len(row)!=len(a[0]) for row in a) or any(len(row)!=len(b[0]) for row in b):
        raise ValueError('rectangular matrix shapes required')
    return tuple(tuple(sum((Q(x)*Q(y) for x,y in zip(row,col)),Q(0)) for col in zip(*b)) for row in a)


def wd_cross_talk(W,D):
    return matmul(W,D)


def strict_cones(K):
    if not K or any(len(row)!=len(K) for row in K):
        raise ValueError('square feature cross-talk matrix required')
    return tuple(t for t in range(len(K)) if K[t][t]>0 and all(K[t][t]>K[j][t] for j in range(len(K)) if j!=t))


def permutation_gauge(W,D,P):
    """P is a tuple mapping output feature index to old feature index."""
    m=len(W)
    if sorted(P)!=list(range(m)) or len(D[0])!=m:
        raise ValueError('invalid feature permutation')
    return tuple(W[j] for j in P),tuple(tuple(row[j] for j in P) for row in D)


def reconstruction_counterexamples():
    W0=((Q(1),),(Q(1),));D0=((Q(1),Q(0)),)
    W1=((Q(1),),(Q(-1),));D1=((Q(1,2),Q(-1,2)),)
    assert matmul(D0,W0)==matmul(D1,W1)==((Q(1),),)
    assert len(strict_cones(wd_cross_talk(W0,D0)))==0
    assert len(strict_cones(wd_cross_talk(W1,D1)))==2
    return {'exact_reconstruction':'identity',
            'first_factorization_strict_cone_count':0,
            'second_factorization_strict_cone_count':2}


def centered_covariance(X,Y):
    if not X or len(X)!=len(Y) or any(len(x)!=len(X[0]) for x in X) or any(len(y)!=len(Y[0]) for y in Y):
        raise ValueError('matched rectangular binary activation matrices needed')
    n=len(X)
    a=len(X[0]);b=len(Y[0])
    if not a or not b:raise ValueError('empty features')
    sx=[sum(Q(row[j]) for row in X) for j in range(a)]
    sy=[sum(Q(row[j]) for row in Y) for j in range(b)]
    return tuple(tuple(sum((Q(X[i][u])*Q(Y[i][v]) for i in range(n)),Q(0))-sx[u]*sy[v]/n for v in range(b)) for u in range(a))




def conditioned_covariance(X,Y,groups):
    """Exactly center within supplied token position/symbol categories.

    The data are paired observations, with group labels FIXED from public
    observed input metadata. Conditional independence implies expected
    covariance zero in every group, even with feature frequency imbalances.
    """
    n=len(X)
    if n==0 or len(Y)!=n or len(groups)!=n:
        raise ValueError('paired observations and matching group roster required')
    if any(len(row)!=len(X[0]) for row in X) or any(
        len(row)!=len(Y[0]) for row in Y):
        raise ValueError('rectangular features required')
    d1=len(X[0]);d2=len(Y[0])
    if not d1 or not d2:
        raise ValueError('empty feature dimension')
    bins={}
    for j,label in enumerate(groups):
        bins.setdefault(label,[]).append(j)
    out=[[Q(0) for _ in range(d2)] for _ in range(d1)]
    for _,indices in sorted(bins.items(),key=lambda x:str(x[0])):
        if len(indices)<2:continue
        k=len(indices)
        sa=[sum((Q(X[i][a]) for i in indices),Q(0)) for a in range(d1)]
        sb=[sum((Q(Y[i][b]) for i in indices),Q(0)) for b in range(d2)]
        for a in range(d1):
            for b in range(d2):
                out[a][b]+=sum((Q(X[i][a])*Q(Y[i][b]) for i in indices),Q(0))-sa[a]*sb[b]/k
    return tuple(tuple(row) for row in out)

if __name__=='__main__':
    import json
    print(json.dumps({'canonical_intercalates':intercalates(canonical_grid()),
                      'factorization':reconstruction_counterexamples()},indent=2))
