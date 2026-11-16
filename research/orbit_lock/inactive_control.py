"""OLM-17 exact-rational feasibility and residual oracle.

All matrix arithmetic is over Fraction. Returned residual and norm quantities
are squared rationals, avoiding unverified floating-point square roots.
"""
from fractions import Fraction as Q


def f(x):
    return x if isinstance(x,Q) else Q(x)


def V(seq):
    return tuple(f(x) for x in seq)


def dot(x,y):
    if len(x)!=len(y):
        raise ValueError("dimension mismatch")
    return sum((a*b for a,b in zip(x,y)),Q(0))


def norm2(x):
    return dot(x,x)


def mv(rows,x):
    return tuple(dot(row,x) for row in rows)


def rank(rows,n=None):
    if not rows:
        return 0
    if n is None:
        n=len(rows[0])
    a=[list(V(r)) for r in rows]
    if any(len(r)!=n for r in a):
        raise ValueError("inconsistent row size")
    piv=0
    for c in range(n):
        pivot=next((i for i in range(piv,len(a)) if a[i][c]),None)
        if pivot is None:
            continue
        a[piv],a[pivot]=a[pivot],a[piv]
        t=a[piv][c];a[piv]=[x/t for x in a[piv]]
        for j in range(len(a)):
            if j!=piv:
                t=a[j][c]
                a[j]=[x-t*y for x,y in zip(a[j],a[piv])]
        piv+=1
        if piv==len(a):
            break
    return piv


def solve(matrix,rhs):
    n=len(rhs)
    if len(matrix)!=n or any(len(r)!=n for r in matrix):
        raise ValueError("square system required")
    a=[list(V(r))+[f(rhs[i])] for i,r in enumerate(matrix)]
    for c in range(n):
        k=next((i for i in range(c,n) if a[i][c]),None)
        if k is None:
            raise ValueError("dependent equations")
        a[c],a[k]=a[k],a[c]
        t=a[c][c];a[c]=[x/t for x in a[c]]
        for i in range(n):
            if i!=c:
                t=a[i][c]
                a[i]=[x-t*y for x,y in zip(a[i],a[c])]
    return tuple(r[-1] for r in a)


def nullspace(rows,n):
    """Rational basis of ker A, even for redundant rows."""
    if not rows:
        return tuple(tuple(Q(int(i==j)) for i in range(n)) for j in range(n))
    a=[list(V(r)) for r in rows]
    if any(len(r)!=n for r in a):
        raise ValueError("invalid row size")
    pivots=[];t=0
    for c in range(n):
        k=next((i for i in range(t,len(a)) if a[i][c]),None)
        if k is None:
            continue
        a[t],a[k]=a[k],a[t]
        v=a[t][c];a[t]=[x/v for x in a[t]]
        for i in range(len(a)):
            if i!=t:
                v=a[i][c]
                a[i]=[x-v*y for x,y in zip(a[i],a[t])]
        pivots.append(c);t+=1
        if t==len(a):break
    out=[]
    for free in range(n):
        if free in pivots:
            continue
        x=[Q(0)]*n;x[free]=Q(1)
        for row,col in enumerate(pivots):
            x[col]=-a[row][free]
        out.append(tuple(x))
    return tuple(out)


def independent_vectors(vectors):
    selected=[]
    for x in vectors:
        if rank(selected+[x])>len(selected):
            selected.append(x)
    return selected


def residual_floor_sq(A,B,delta):
    """Distance squared from Bdelta to B(ker A), exact rational."""
    d=len(delta)
    T=nullspace(A,d)
    b=mv(B,delta)
    columns=independent_vectors([mv(B,t) for t in T])
    if not columns:
        return norm2(b)
    gram=[[dot(x,y) for y in columns] for x in columns]
    lam=solve(gram,[dot(x,b) for x in columns])
    residual=tuple(b[i]-sum((lam[j]*columns[j][i]
                          for j in range(len(columns))),Q(0))
                   for i in range(len(b)))
    return norm2(residual)


def exact_matched_sham(A,B,delta):
    """Find min-norm exact tangent+inactive matching and equal-norm feasibility."""
    d=len(delta)
    rows=tuple(V(x) for x in A)+tuple(V(x) for x in B)
    targets=(Q(0),)*len(A)+mv(B,delta)
    E=[]; y=[]
    for row,target in zip(rows,targets):
        if rank(E+[row],d)>len(E):
            E.append(row);y.append(target)
    if E:
        gram=[[dot(a,b) for b in E] for a in E]
        multipliers=solve(gram,y)
        s=tuple(sum((multipliers[j]*E[j][i] for j in range(len(E))),Q(0))
                for i in range(d))
    else:
        s=(Q(0),)*d
    if mv(rows,s)!=targets:
        return {"exact":False,"sham":None,"minimum_sqnorm":None,
                "equal_dose_exact":False,"nullity":d-rank(rows,d)}
    s2=norm2(s);r2=norm2(delta)
    nullity=d-rank(rows,d)
    return {"exact":True,"sham":s,"minimum_sqnorm":s2,
            "equal_dose_exact":bool(r2==s2 or (r2>s2 and nullity>0)),
            "nullity":nullity}


def e(i,d):
    return tuple(Q(int(j==i)) for j in range(d))


def low_dimensional_witnesses():
    d=5
    A=tuple(e(i,d) for i in range(4))
    delta=e(3,d)
    I=tuple(e(i,d) for i in range(d))
    conflated=(tuple(a+b for a,b in zip(e(3,d),e(4,d))),)
    silent=(e(4,d),)
    return {
      "full_B_floor_sq":residual_floor_sq(A,I,delta),
      "full_B_exact":exact_matched_sham(A,I,delta)["exact"],
      "conflated_B_floor_sq":residual_floor_sq(A,conflated,delta),
      "conflated_B_match":exact_matched_sham(A,conflated,delta),
      "silent_B_match":exact_matched_sham(A,silent,delta),
      "extra_dimension_B_match":exact_matched_sham(
          tuple(e(i,6) for i in range(4)),(e(4,6),),e(3,6)),
    }


if __name__=="__main__":
    for k,v in low_dimensional_witnesses().items():
        print(k,v)
